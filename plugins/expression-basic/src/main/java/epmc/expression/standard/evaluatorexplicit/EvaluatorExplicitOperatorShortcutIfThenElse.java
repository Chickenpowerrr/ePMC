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

package epmc.expression.standard.evaluatorexplicit;

import java.util.Map;

import epmc.value.ContextValue;
import epmc.value.OperatorEvaluator;
import epmc.expression.Expression;
import epmc.expression.evaluatorexplicit.EvaluatorExplicit;
import epmc.expression.standard.ExpressionOperator;
import epmc.expression.standard.evaluatorexplicit.UtilEvaluatorExplicit.EvaluatorCacheEntry;
import epmc.expressionevaluator.ExpressionToType;
import epmc.value.Type;
import epmc.value.Value;
import epmc.value.operator.OperatorIte;
import epmc.value.operator.OperatorSet;

public final class EvaluatorExplicitOperatorShortcutIfThenElse implements EvaluatorExplicit, EvaluatorExplicitBoolean {
    public final static class Builder implements EvaluatorExplicit.Builder {
        private Expression[] variables;
        private Expression expression;
        private Map<EvaluatorCacheEntry, EvaluatorExplicit> cache;
        private ExpressionToType expressionToType;

        @Override
        public String getIdentifier() {
            return IDENTIFIER;
        }

        @Override
        public Builder setVariables(Expression[] variables) {
            this.variables = variables;
            return this;
        }

        private Expression[] getVariables() {
            return variables;
        }

        @Override
        public Builder setExpression(Expression expression) {
            this.expression = expression;
            return this;
        }

        private Expression getExpression() {
            return expression;
        }

        @Override
        public Builder setCache(Map<EvaluatorCacheEntry, EvaluatorExplicit> cache) {
            this.cache = cache;
            return this;
        }

        private Map<EvaluatorCacheEntry, EvaluatorExplicit> getCache() {
            return cache;
        }

        @Override
        public boolean canHandle() {
            assert expression != null;
            if (!(expression instanceof ExpressionOperator)) {
                return false;
            }
            ExpressionOperator expressionOperator = ExpressionOperator.asOperator(expression);
            if (!expressionOperator.getOperator().equals(OperatorIte.ITE)) {
                return false;
            }
            for (Expression variable : variables) {
                if (expression.equals(variable)) {
                    return false;
                }
            }
            return true;
        }

        @Override
        public EvaluatorExplicit build() {
            return new EvaluatorExplicitOperatorShortcutIfThenElse(this);
        }

        @Override
        public EvaluatorExplicit.Builder setExpressionToType(
                ExpressionToType expressionToType) {
            this.expressionToType = expressionToType;
            return this;
        }

        private ExpressionToType getExpressionToType() {
            return expressionToType;
        }
    }

    public final static String IDENTIFIER = "operator-shortcut-if-then-else";

    private final Expression[] variables;
    private final ExpressionOperator expression;
    private final EvaluatorExplicit[] operands;
    private final Value[] operandValues;
    private final Value result;
    private final OperatorEvaluator setThen;
    private final OperatorEvaluator setElse;

    private EvaluatorExplicitOperatorShortcutIfThenElse(Builder builder) {
        assert builder != null;
        assert builder.getExpression() != null;
        assert builder.getVariables() != null;
        expression = (ExpressionOperator) builder.getExpression();
        variables = builder.getVariables();
        operands = new EvaluatorExplicit[expression.getOperands().size()];
        operandValues = new Value[expression.getOperands().size()];
        Type[] types = new Type[expression.getOperands().size()];
        int opNr = 0;
        for (Expression operand : expression.getOperands()) {
            operands[opNr] = UtilEvaluatorExplicit.newEvaluator(null, operand, variables, builder.getCache(), builder.getExpressionToType());
            operandValues[opNr] = operands[opNr].getResultValue();
            types[opNr] = operands[opNr].getResultValue().getType();
            opNr++;
        }
        OperatorEvaluator evaluator = ContextValue.get().getEvaluator(expression.getOperator(), types);
        result = evaluator.resultType().newValue();
        setThen = ContextValue.get().getEvaluator(OperatorSet.SET, types[1], evaluator.resultType());
        setElse = ContextValue.get().getEvaluator(OperatorSet.SET, types[2], evaluator.resultType());
    }

    @Override
    public String getIdentifier() {
        return IDENTIFIER;
    }

    @Override
    public Expression getExpression() {
        return expression;
    }

    @Override
    public Value evaluate(Value... values) {
        assert values != null;
        for (Value variable : values) {
            assert variable != null;
        }
        if (((EvaluatorExplicitBoolean) operands[0]).evaluateBoolean(values)) {
            EvaluatorExplicit thenOp = operands[1];
            thenOp.evaluate(values);
            setThen.apply(result, thenOp.getResultValue());
        } else {
            EvaluatorExplicit elseOp = operands[2];
            elseOp.evaluate(values);
            setElse.apply(result, elseOp.getResultValue());
        }
        return result;
    }

    @Override
    public Value getResultValue() {
        return result;
    }

    @Override
    public boolean evaluateBoolean(Value... values) {
        for (Value variable : values) {
            assert variable != null;
        }
        if (((EvaluatorExplicitBoolean) operands[0]).evaluateBoolean(values)) {
            return ((EvaluatorExplicitBoolean) operands[1]).evaluateBoolean(values);
        } else {
            return ((EvaluatorExplicitBoolean) operands[2]).evaluateBoolean(values);
        }
    }
}
