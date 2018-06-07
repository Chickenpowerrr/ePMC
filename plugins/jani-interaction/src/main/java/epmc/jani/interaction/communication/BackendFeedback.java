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

package epmc.jani.interaction.communication;

/**
 * Interface with which the backend sends messages.
 * 
 * @author Ernst Moritz Hahn
 */
public interface BackendFeedback {
    /**
     * Send message.
     * The client parameter decides where the message should be send to.
     * The second parameter contains the actual message, which should be
     * parsable as a JSON object.
     * 
     * 
     * @param client to which instance to send message
     * @param message message to send to client
     */
    void sendToClient(Object client, String message);

    /**
     * Log off the client with the given identifier.
     * 
     * @param who client to log off
     */
    void logOff(Object who);
}
