
import java.util.*;
import java.net.*;
import java.io.*;

public class ChatServer {

	private static final Room lobby = new Room(null);

	private static class User {

		public final String identifier;
		public Room current = lobby;

		public User(final String identifier) {
			this.identifier = identifier;
			current.users.add(this);
		}

		public void hasSaid(final User user, final String message) {

		}

		public void hasQuit(final User user) {

		}

		public void wentUnder(final User user, final String name) {

		}

		public void cameFromAbove(final User user) {

		}

		public void cameFromBelow(final User user, final String name) {

		}

		public void subroomRemoved(final String name) {

		}

		public void subroomCreated(final User user, final String name) {

		}
	}

	private static class Context {

		public final Room parent;
		public final String name;

		public Context(final Room parent, final String name) {
			this.parent = parent;
			this.name = name;
		}
	}

	private static class Room {

		public final Context context;

		public final List<User> users = new ArrayList<User>();
		public final Map<String, Room> subrooms = new HashMap<String, Room>();

		public Room(final Context context) {
			this.context = context;
		}

		public boolean empty() {
			return users.size() == 0 && subrooms.size() == 0;
		}

	}

	private static final void createSubroom(final User user, final String name) {
		final Room subroom = new Room(new Context(user.current, name));

		user.current.subrooms.put(name, subroom);
		user.current.users.remove(user);
		subroom.users.add(user);

		user.current = subroom;
	}

	private static final void exitRoom(final User user) {
		user.current.users.remove(user);

		if(user.current.context == null) return; // terminate user

		final Room previous = user.current;
		user.current = previous.context.parent;
		final String name = previous.context.name;

		if(previous.empty()) {
			user.current.subrooms.remove(previous);

			for(final User one : user.current.users)
				one.subroomRemoved(name);

		}
	}
}