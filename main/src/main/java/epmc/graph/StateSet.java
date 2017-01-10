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

package epmc.graph;

import java.io.Closeable;

import epmc.error.EPMCException;
import epmc.value.ContextValue;

//TODO complete documentation

public interface StateSet extends Closeable, Cloneable {

    ContextValue getContextValue();

    int size();
 
    @Override
    void close();

    boolean isSubsetOf(StateSet states) throws EPMCException;
    
    StateSet clone();

    default boolean isEmpty() {
        return size() == 0;
    }
}