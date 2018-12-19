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

package epmc.operator;

import javax.json.Json;
import javax.json.JsonObjectBuilder;
import javax.json.JsonValue;

import epmc.expression.standard.ExpressionOperator;
import epmc.jani.exporter.operatorprocessor.OperatorProcessor;
import epmc.jani.exporter.options.OptionsJANIExporter;
import epmc.jani.exporter.processor.ProcessorRegistrar;
import epmc.jani.model.UtilModelParser;
import epmc.options.Options;

/**
 * @author Andrea Turrini
 *
 */
public class JANIExporter_OperatorIffProcessor implements OperatorProcessor {
    private final static String OP = "op";
    private final static String IMPLIES = "⇒";
    private final static String LEFT = "left";
    private final static String RIGHT = "right";
    private final static String AND = "∧";
    private final static String OR = "∨";
    private final static String NOT = "¬";
    private final static String EXP = "exp";
    
    private ExpressionOperator expressionOperator = null;
    
    @Override
    public OperatorProcessor setExpressionOperator(ExpressionOperator expressionOperator) {
        assert expressionOperator != null;
        assert expressionOperator.getOperator().equals(OperatorIff.IFF);
    
        this.expressionOperator = expressionOperator;

        return this;
    }

    @Override
    public JsonValue toJSON() {
        assert expressionOperator != null;
        
        JsonObjectBuilder builder = Json.createObjectBuilder();

        if (Options.get().getBoolean(OptionsJANIExporter.JANI_EXPORTER_USE_DERIVED_OPERATORS)) {
            builder.add(OP, AND);

            JsonObjectBuilder builderImplies = Json.createObjectBuilder();
            builderImplies.add(OP, IMPLIES);
            builderImplies.add(LEFT, ProcessorRegistrar.getProcessor(expressionOperator.getOperand1())
                    .toJSON());
            builderImplies.add(RIGHT, ProcessorRegistrar.getProcessor(expressionOperator.getOperand2())
                    .toJSON());
            
            builder.add(LEFT, builderImplies.build());

            builderImplies = Json.createObjectBuilder();
            builderImplies.add(OP, IMPLIES);
            builderImplies.add(LEFT, ProcessorRegistrar.getProcessor(expressionOperator.getOperand2())
                    .toJSON());
            builderImplies.add(RIGHT, ProcessorRegistrar.getProcessor(expressionOperator.getOperand1())
                    .toJSON());
            
            builder.add(RIGHT, builderImplies.build());
        } else {
            JsonObjectBuilder builderOr = Json.createObjectBuilder();
            builderOr.add(OP, OR);
            builderOr.add(LEFT, ProcessorRegistrar.getProcessor(expressionOperator.getOperand1())
                    .toJSON());
            builderOr.add(RIGHT, ProcessorRegistrar.getProcessor(expressionOperator.getOperand2())
                    .toJSON());
            
            JsonObjectBuilder builderNot = Json.createObjectBuilder();
            builderNot.add(OP, NOT);
            builderNot.add(EXP, builderOr.build());
            
            JsonObjectBuilder builderAnd = Json.createObjectBuilder();
            builderAnd.add(OP, AND);
            builderAnd.add(LEFT, ProcessorRegistrar.getProcessor(expressionOperator.getOperand1())
                    .toJSON());
            builderAnd.add(RIGHT, ProcessorRegistrar.getProcessor(expressionOperator.getOperand2())
                    .toJSON());

            builder.add(OP, OR);
            builder.add(LEFT, builderNot.build());
            builder.add(RIGHT, builderAnd.build());
        }
        
        UtilModelParser.addPositional(builder, expressionOperator.getPositional());
        
        return builder.build();
    }
}    
