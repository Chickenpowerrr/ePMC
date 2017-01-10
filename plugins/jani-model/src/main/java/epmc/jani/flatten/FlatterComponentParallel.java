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

package epmc.jani.flatten;

import epmc.error.EPMCException;
import epmc.jani.model.component.Component;
import epmc.jani.model.component.ComponentAutomaton;
import epmc.jani.model.component.ComponentParallel;

public final class FlatterComponentParallel implements FlatterComponent {
	private Component component;

	@Override
	public void setComponent(Component component) {
		this.component = component;
	}

	@Override
	public boolean canHandle() {
		if (!(component instanceof ComponentParallel)) {
			return false;
		}
		return true;
	}

	@Override
	public ComponentAutomaton flatten() throws EPMCException {
		ComponentParallel componentParallel = (ComponentParallel) component;
		
		
		return (ComponentAutomaton) component;
	}

}
