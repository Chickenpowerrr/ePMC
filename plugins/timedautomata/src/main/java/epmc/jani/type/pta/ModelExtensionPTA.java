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

package epmc.jani.type.pta;

import javax.json.JsonObjectBuilder;
import javax.json.JsonValue;

import epmc.error.EPMCException;
import epmc.graph.Semantics;
import epmc.graph.SemanticsPTA;
import epmc.jani.model.Edge;
import epmc.jani.model.JANINode;
import epmc.jani.model.ModelExtensionSemantics;
import epmc.jani.model.ModelJANI;
import epmc.time.UtilTime;

public final class ModelExtensionPTA implements ModelExtensionSemantics {
	public final static String IDENTIFIER = "pta";
	private JANINode node;

	@Override
	public String getIdentifier() {
		return IDENTIFIER;
	}

	@Override
	public void setModel(ModelJANI model) throws EPMCException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setNode(JANINode node) throws EPMCException {
		this.node = node;
	}

	@Override
	public void setJsonValue(JsonValue value) throws EPMCException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void parseBefore() throws EPMCException {
		if (node instanceof ModelJANI) {
			ModelJANI model = (ModelJANI) node;
			UtilTime.addClockType(model);
		}

		// TODO Auto-generated method stub
		
	}

	@Override
	public void parseAfter() throws EPMCException {
		if (node instanceof Edge) {
			Edge edge = (Edge) node;
		}
	}

	@Override
	public void generate(JsonObjectBuilder generate) throws EPMCException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public Semantics getSemantics() {
		return SemanticsPTA.PTA;
	}
}
