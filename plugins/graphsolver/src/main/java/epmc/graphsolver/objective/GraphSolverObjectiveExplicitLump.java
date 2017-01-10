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

package epmc.graphsolver.objective;

import epmc.graph.explicit.GraphExplicit;
import epmc.value.ValueArray;

public final class GraphSolverObjectiveExplicitLump implements GraphSolverObjectiveExplicit {
    private GraphExplicit graph;
    private int[] partition;

    @Override
    public void setGraph(GraphExplicit graph) {
        this.graph = graph;
    }

    @Override
    public GraphExplicit getGraph() {
        return graph;
    }

    @Override
    public void setResult(ValueArray result) {
    }

    @Override
    public ValueArray getResult() {
        return null;
    }
    
    public void setPartition(int[] partition) {
        this.partition = partition;
    }
    
    public int[] getPartition() {
        return partition;
    }
}
