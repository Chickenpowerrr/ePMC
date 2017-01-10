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

package epmc.value;

import epmc.value.ContextValue;
import epmc.value.Type;

public interface TypeWeight extends TypeAlgebra {
    static TypeWeight get(ContextValue context) {
        assert context != null;
        return context.getType(TypeWeight.class);
    }
    
    static void set(TypeWeight type) {
        assert type != null;
        ContextValue context = type.getContext();
        context.setType(TypeWeight.class, context.makeUnique(type));
    }
    
    static boolean isWeight(Type type) {
        return type instanceof TypeWeight;
    }
    
    static TypeWeight asWeight(Type type) {
    	if (isWeight(type)) {
    		return (TypeWeight) type;
    	} else {
    		return null;
    	}
    }
    
    ValueAlgebra getPosInf();

    ValueAlgebra getNegInf();
    
    ValueAlgebra getZero();
    
    ValueAlgebra getOne();
    
    @Override
    ValueAlgebra newValue();
}