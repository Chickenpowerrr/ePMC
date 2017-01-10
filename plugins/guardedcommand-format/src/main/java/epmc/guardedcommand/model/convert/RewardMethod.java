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

package epmc.guardedcommand.model.convert;

/**
 * Method to integrate rewards into JANI model converted from GuardedCommand.
 * 
 * @author Ernst Moritz Hahn
 */
public enum RewardMethod {
	/** Integrate reward assignments into existing automata. */
	INTEGRATE,
	/** Create new automaton to integrate rewards into model. */
	EXTERNAL,
	/** Do not convert rewards. */
	NONE
}