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

package epmc.jani.model;

import javax.json.Json;
import javax.json.JsonObjectBuilder;
import javax.json.JsonValue;

import epmc.jani.exporter.processor.JANIProcessor;

public class JANIExporter_ActionProcessor implements JANIProcessor {
    /** Identifies the name of a given action. */
    private static final String NAME = "name";
    private static final String COMMENT = "comment";

    private Action action = null;

    @Override
    public JANIProcessor setElement(Object component) {
        assert component != null;
        assert component instanceof Action; 

        action = (Action) component;
        return this;
    }

    @Override
    public JsonValue toJSON() {
        assert action != null;

        JsonObjectBuilder builder = Json.createObjectBuilder();

        builder.add(NAME, action.getName());
        
        String comment = action.getComment();
        if (comment != null) {
            builder.add(COMMENT, comment);
        }
        
        return builder.build();
    }
}
