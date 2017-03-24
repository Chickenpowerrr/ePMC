/****************************************************************************

    ePMC - an extensible probabilistic model checker
    Copyright (C) 2017

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.

*****************************************************************************/

package epmc.multiobjective;

import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import epmc.algorithms.UtilAlgorithms;
import epmc.algorithms.explicit.ComponentsExplicit;
import epmc.algorithms.explicit.EndComponents;
import epmc.automaton.Automaton;
import epmc.automaton.AutomatonProduct;
import epmc.automaton.AutomatonProductLabel;
import epmc.automaton.AutomatonRabin;
import epmc.automaton.AutomatonRabinLabel;
import epmc.automaton.ProductGraphExplicit;
import epmc.automaton.UtilAutomaton;
import epmc.error.EPMCException;
import epmc.expression.Expression;
import epmc.expression.standard.ExpressionLiteral;
import epmc.expression.standard.ExpressionMultiObjective;
import epmc.expression.standard.ExpressionQuantifier;
import epmc.expression.standard.ExpressionReward;
import epmc.expression.standard.RewardSpecification;
import epmc.graph.CommonProperties;
import epmc.graph.GraphBuilderExplicit;
import epmc.graph.explicit.EdgeProperty;
import epmc.graph.explicit.EdgePropertyApply;
import epmc.graph.explicit.EdgePropertyConstant;
import epmc.graph.explicit.GraphExplicit;
import epmc.graph.explicit.GraphExplicitSparseAlternate;
import epmc.graph.explicit.GraphExplicitWrapper;
import epmc.graph.explicit.NodeProperty;
import epmc.graph.explicit.NodePropertyApply;
import epmc.graph.explicit.NodePropertyConstant;
import epmc.graph.explicit.StateSetExplicit;
import epmc.graphsolver.iterative.OptionsGraphSolverIterative;
import epmc.modelchecker.ModelChecker;
import epmc.options.Options;
import epmc.util.BitSet;
import epmc.util.UtilBitSet;
import epmc.value.ContextValue;
import epmc.value.OperatorAddInverse;
import epmc.value.Type;
import epmc.value.TypeDouble;
import epmc.value.TypeWeight;
import epmc.value.TypeWeightTransition;
import epmc.value.Value;
import epmc.value.ValueAlgebra;
import gnu.trove.map.hash.THashMap;

final class ProductBuilder {
    private AutomatonProduct automatonProduct;
	private StateSetExplicit initialStates;
    private BitSet[][] stable;
    private BitSet[][] accepting;
    private int numAutomata;
	private ExpressionMultiObjective property;
	private GraphExplicit graph;
	private BitSet invertedRewards;

	ProductBuilder() {
	}
	
	ProductBuilder setProperty(ExpressionMultiObjective property) {
		this.property = property;
		return this;
	}
	
	ProductBuilder setModelChecker(ModelChecker modelChecker) {
        return this;
	}
	
	ProductBuilder setGraph(GraphExplicit graph) {
		this.graph = graph;
		initialStates = graph.newInitialStateSet();
		return this;
	}
	
	ProductBuilder setInvertedRewards(BitSet invertedRewards) {
		this.invertedRewards = invertedRewards;
		return this;
	}
	
	Product build() throws EPMCException {
    	assert initialStates != null;
        GraphExplicit prodWrapper = computeProductGraph(initialStates);
        GraphBuilderExplicit builder = new GraphBuilderExplicit();
        builder.setInputGraph(prodWrapper);
        builder.addDerivedGraphProperties(prodWrapper.getGraphProperties());
        builder.addDerivedNodeProperty(CommonProperties.STATE);
        builder.addDerivedEdgeProperty(CommonProperties.WEIGHT);
        Options options = getOptions();
        Type typeWeight = TypeWeightTransition.get(getContextValue());
        boolean useNative = options.getBoolean(OptionsGraphSolverIterative.GRAPHSOLVER_ITERATIVE_NATIVE)
                && TypeDouble.isDouble(typeWeight);
        builder.setReorder();
        builder.setForNative(useNative);
        builder.build();
        GraphExplicit iterGraph = builder.getOutputGraph();
        MultiObjectiveIterationRewards rewards = computeRewards(builder);
        return new Product(iterGraph, rewards, numAutomata);
	}
	
	private GraphExplicit computeProductGraph(StateSetExplicit initialStates) throws EPMCException {
        Set<Expression> expressionsSet = new HashSet<>();
        for (Expression objective : property.getOperands()) {
        	ExpressionQuantifier objectiveQuantifier = (ExpressionQuantifier) objective;
            Expression quantified = objectiveQuantifier.getQuantified();
            if (quantified instanceof ExpressionReward) {
            	// TODO
            } else {
            	Set<Expression> inners = UtilLTL.collectLTLInner(quantified);
            	expressionsSet.addAll(inners);
            }
        }
        Expression[] expressions = expressionsSet.toArray(new Expression[expressionsSet.size()]);
        List<Automaton> automata = new ArrayList<>();
        for (Expression objective : property.getOperands()) {
        	ExpressionQuantifier objectiveQuantifier = (ExpressionQuantifier) objective;
            Expression quantified = objectiveQuantifier.getQuantified();
            if (quantified instanceof ExpressionReward) {
                quantified = ExpressionLiteral.getFalse(initialStates.getContextValue());
            }
            AutomatonRabin automaton = UtilAutomaton.newAutomatonRabin(initialStates.getContextValue(), quantified, expressions);
            automata.add(automaton);
        }
        automatonProduct = new AutomatonProduct(initialStates.getContextValue(), automata);
        numAutomata = automatonProduct.getNumComponents();
        List<Object> prodNodeProperties = new ArrayList<>();
        prodNodeProperties.add(CommonProperties.STATE);
        prodNodeProperties.add(CommonProperties.PLAYER);
        List<Object> prodEdgeProperties = new ArrayList<>();
        prodEdgeProperties.add(CommonProperties.WEIGHT);
        for (Expression objective : property.getOperands()) {
        	ExpressionQuantifier objectiveQuantifier = (ExpressionQuantifier) objective;
            Expression quantified = objectiveQuantifier.getQuantified();
            if (quantified instanceof ExpressionReward) {
                RewardSpecification rewardStructure = ((ExpressionReward) quantified).getReward();
                prodNodeProperties.add(rewardStructure);
                prodEdgeProperties.add(rewardStructure);
            }
        }
        ProductGraphExplicit product = new ProductGraphExplicit.Builder()
        		.setModel(graph)
        		.setModelInitialNodes(initialStates.getStatesExplicit())
        		.setAutomaton(automatonProduct)
        		.setAutomatonInitialState(automatonProduct.getInitState())
        		.addGraphProperties(graph.getGraphProperties())
        		.addNodeProperties(prodNodeProperties)
        		.addEdgeProperties(prodEdgeProperties)
        		.build();
        
        GraphExplicitWrapper prodWrapper = new GraphExplicitWrapper(product);
        prodWrapper.addDerivedGraphProperties(product.getGraphProperties());
        prodWrapper.addDerivedNodeProperty(CommonProperties.STATE);
        prodWrapper.addDerivedNodeProperty(CommonProperties.PLAYER);
        prodWrapper.addDerivedNodeProperty(CommonProperties.AUTOMATON_LABEL);
        prodWrapper.addDerivedEdgeProperty(CommonProperties.WEIGHT);
        
        for (Expression objective : property.getOperands()) {
        	ExpressionQuantifier objectiveQuantifier = (ExpressionQuantifier) objective;
            Expression quantified = objectiveQuantifier.getQuantified();
            if (quantified instanceof ExpressionReward) {
                RewardSpecification rewardStructure = ((ExpressionReward) quantified).getReward();
                prodWrapper.addDerivedNodeProperty(rewardStructure);
                prodWrapper.addDerivedEdgeProperty(rewardStructure);
            }
        }

        prodWrapper.explore();
        return prodWrapper;
	}
	
    private MultiObjectiveIterationRewards computeRewards(GraphBuilderExplicit builder)
    		throws EPMCException {
    	GraphExplicit prodWrapper = builder.getInputGraph();
        NodeProperty[] stateRewards = new NodeProperty[property.getOperands().size()];
        EdgeProperty[] transRewards = new EdgeProperty[property.getOperands().size()];
        EdgeProperty weights = prodWrapper.getEdgeProperty(CommonProperties.WEIGHT);
        Value weight = weights.getType().newValue();
        int propNr = 0;
        Value zero = TypeWeight.get(getContextValue()).getZero();
        for (Expression objective : property.getOperands()) {
        	ExpressionQuantifier objectiveQuantifier = (ExpressionQuantifier) objective;
            Expression quantified = objectiveQuantifier.getQuantified();
            if (quantified instanceof ExpressionReward) {
                RewardSpecification rewardStructure = ((ExpressionReward) quantified).getReward();
                stateRewards[propNr] = prodWrapper.getNodeProperty(rewardStructure);
                transRewards[propNr] = prodWrapper.getEdgeProperty(rewardStructure);
            } else {
                stateRewards[propNr] = new NodePropertyConstant(prodWrapper, zero);
                transRewards[propNr] = new EdgePropertyConstant(prodWrapper, zero);
            }
            if (invertedRewards.get(propNr)) {
                stateRewards[propNr] = new NodePropertyApply(prodWrapper, getContextValue().getOperator(OperatorAddInverse.IDENTIFIER), stateRewards[propNr]);
                transRewards[propNr] = new EdgePropertyApply(prodWrapper, getContextValue().getOperator(OperatorAddInverse.IDENTIFIER), transRewards[propNr]);
            }
            propNr++;
        }

        Map<BitSet,BitSet> resultMap = computeCombinations(builder);
        GraphExplicitSparseAlternate iterGraph = (GraphExplicitSparseAlternate) builder.getOutputGraph();
        
        MultiObjectiveIterationRewards result = new MultiObjectiveIterationRewards(iterGraph, numAutomata);
        int numStates = iterGraph.computeNumStates();
        BitSet empty = UtilBitSet.newBitSetUnbounded();
        for (int iterState = 0; iterState < numStates; iterState++) {
            int state = builder.outputToInputNode(iterState);
            if (iterState < 0 || iterState >= numStates) {
                continue;
            }
            prodWrapper.queryNode(state);
            boolean found = false;
            for (Entry<BitSet, BitSet> entry : resultMap.entrySet()) {
                BitSet combination = entry.getKey();
                BitSet states = entry.getValue();
                if (states.get(state)) {
                    result.addCombination(combination);
                    found = true;
                }
            }
            if (!found) {
                result.addCombination(empty);
            }
            ValueAlgebra stateReward = newValueWeight();
            ValueAlgebra transReward = newValueWeight();
            iterGraph.queryNode(iterState);
            int numSucc = iterGraph.getNumSuccessors();
            for (int obj = 0; obj < numAutomata; obj++) {
                stateReward.set(zero);
                NodeProperty stateRewardProp = stateRewards[obj];
                stateReward.set(stateRewardProp.get());
                EdgeProperty edgeRewardProp = transRewards[obj];
                for (int succNr = 0; succNr < numSucc; succNr++) {
                	// TODO HACK
                	int old = prodWrapper.getQueriedNode();
                    transReward.set(stateReward);
                    transReward.add(transReward, edgeRewardProp.get(succNr));
                    int succ = prodWrapper.getSuccessorNode(succNr);
                    prodWrapper.queryNode(succ);
                    transReward.add(transReward, edgeRewardProp.get(0));
                    result.setReward(transReward, succNr, obj);
                    prodWrapper.queryNode(old);
                }
            }
            result.finishState();
        }
        return result;
    }
    
    private Map<BitSet,BitSet> computeCombinations(GraphBuilderExplicit builder) throws EPMCException {
        computeStableAccepting(builder.getInputGraph());
        Map<BitSet,BitSet> todoMap = new THashMap<>();
        Map<BitSet,BitSet> resultMap = new THashMap<>();
        
        Deque<BitSet> todo = new LinkedList<>();
        BitSet initBitSet = UtilBitSet.newBitSetUnbounded();
        for (int prop = 0; prop < numAutomata; prop++) {
            initBitSet.set(prop);
        }
        todo.add(initBitSet);
        GraphExplicit prodWrapper = builder.getInputGraph();
        BitSet todoBS = UtilBitSet.newBitSetUnbounded();
        todoBS.set(0, prodWrapper.getNumNodes());
        todoMap.put(initBitSet, todoBS);
        while (!todo.isEmpty()) {
            BitSet combination = todo.getLast();
            todo.removeLast();
            BitSet states = todoMap.get(combination);
            todoMap.remove(combination);
            BitSet accepting = computeAccepting(builder.getInputGraph(), states, combination);
            resultMap.put(combination, accepting);
            for (int prop = combination.nextSetBit(0); prop >= 0;
                    prop = combination.nextSetBit(prop+1)) {
                combination.set(prop, false);
                if (!resultMap.containsKey(combination)
                        && !todoMap.containsKey(combination)
                        && !combination.isEmpty()) {
                    todo.addFirst(combination.clone());
                    BitSet remaining = states.clone();
                    remaining.andNot(accepting);
                    assert remaining != null;
                    todoMap.put(combination.clone(), remaining);
                }
                combination.set(prop, true);
            }
        }
        return resultMap;
    }
    
	private void computeStableAccepting(GraphExplicit prodWrapper) throws EPMCException {
		NodeProperty automatonLabel = prodWrapper.getNodeProperty(CommonProperties.AUTOMATON_LABEL);
        stable = new BitSet[automatonProduct.getNumComponents()][];
        accepting = new BitSet[automatonProduct.getNumComponents()][];
        int automatonNr = 0;
        for (Automaton automaton : automatonProduct.getAutomata()) {
            AutomatonRabin automatonRabin = (AutomatonRabin) automaton;
            BitSet[] automatonStable = new BitSet[automatonRabin.getNumPairs()];
            BitSet[] automatonAccepting = new BitSet[automatonRabin.getNumPairs()];
            for (int label = 0; label < automatonRabin.getNumPairs(); label++) {
                BitSet labelStableBitSet = UtilBitSet.newBitSetUnbounded();
                BitSet labelAcceptingBitSet = UtilBitSet.newBitSetUnbounded();
                assert prodWrapper != null;
                for (int node = 0; node < prodWrapper.getNumNodes(); node++) {
                    prodWrapper.queryNode(node);
                    AutomatonProductLabel prodLabel = automatonLabel.getObject();
                    AutomatonRabinLabel rabinLabel = (AutomatonRabinLabel) automaton.numberToLabel(prodLabel.get(automatonNr));
                    labelStableBitSet.set(node, rabinLabel.getStable().get(label));
                    labelAcceptingBitSet.set(node, rabinLabel.getAccepting().get(label));
                }
                automatonStable[label] = labelStableBitSet;
                automatonAccepting[label] = labelAcceptingBitSet;
            }
            stable[automatonNr] = automatonStable;
            accepting[automatonNr] = automatonAccepting;
            automatonNr++;
        }
    }

    private BitSet computeAccepting(GraphExplicit prodWrapper, BitSet states, BitSet properties)
            throws EPMCException {
        assert states != null;
        assert properties != null;
        int numCombinations = 1;
        for (int prop = properties.nextSetBit(0); prop >= 0;
                prop = properties.nextSetBit(prop+1)) {
            AutomatonRabin automaton = (AutomatonRabin) automatonProduct.getAutomaton(prop);
            numCombinations *= automaton.getNumPairs();
        }
        
        BitSet result = UtilBitSet.newBitSetUnbounded();
        BitSet stable = UtilBitSet.newBitSetUnbounded();
        for (int combNumber = 0; combNumber < numCombinations; combNumber++) {
            stable.clear();
            stable.or(states);
            int numberPart = combNumber;
            for (int prop = properties.nextSetBit(0); prop >= 0;
                    prop = properties.nextSetBit(prop+1)) {
                AutomatonRabin automaton = (AutomatonRabin) automatonProduct.getAutomaton(prop);
                int labelNr = numberPart % automaton.getNumPairs();
                numberPart /= automaton.getNumPairs();
                stable.and(this.stable[prop][labelNr]);
            }
            ComponentsExplicit components = UtilAlgorithms.newComponentsExplicit();
            components.removeLeavingAttr(prodWrapper, stable);
            EndComponents endComponents = components.maximalEndComponents(prodWrapper, stable);
            for (BitSet mec = endComponents.next(); mec != null; mec = endComponents.next()) {
                numberPart = combNumber;
                boolean allThere = true;
                for (int prop = properties.nextSetBit(0); prop >= 0;
                        prop = properties.nextSetBit(prop+1)) {
                    AutomatonRabin automaton = (AutomatonRabin) automatonProduct.getAutomaton(prop);
                    int labelNr = numberPart % automaton.getNumPairs();
                    numberPart /= automaton.getNumPairs();
                    boolean mecAccepting = false;
                    BitSet accBS = this.accepting[prop][labelNr];
                    for (int mecBit = mec.nextSetBit(0); mecBit >= 0;
                            mecBit = mec.nextSetBit(mecBit+1)) {
                        if (accBS.get(mecBit)) {
                            mecAccepting = true;
                            break;
                        }
                    }
                    if (!mecAccepting) {
                        allThere = false;
                        break;
                    }
                }
                if (allThere) {
                    result.or(mec);
                }
            }
        }
//        result = ComponentsExplicit.reachMaxOne(prodWrapper, result);
        return result;
    }
    
    private ContextValue getContextValue() {
    	return automatonProduct.getContextValue();
    }
    
    private Options getOptions() {
    	return initialStates.getContextValue().getOptions();
    }
    
    private ValueAlgebra newValueWeight() {
    	return TypeWeight.get(getContextValue()).newValue();
    }
}
