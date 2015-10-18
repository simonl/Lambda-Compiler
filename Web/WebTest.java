
import java.net.*;
import java.io.*;
import java.util.*;

public final class WebTest {



	public static final <A, B> void serve(final Func<A, B> logic, final Reader<A> reader, final Writer<B> writer) throws IOException {

		final ServerSocket serverLoop = startServer();

		while(true) {

			final Client<A, B> client = connect(serverLoop.accept(), reader, writer);

			try {

				while(true)
					client.send(logic.apply(client.receive()));

			} catch(final EOFException e) {

				System.out.println("End of connection\n");

			}
		}
	}

	public static final <A, B> Server<A, B> connect(final Socket server, final Writer<A> writer, final Reader<B> reader) throws IOException {

		final DataOutputStream toServer = new DataOutputStream(server.getOutputStream());
		final DataInputStream fromServer = new DataInputStream(server.getInputStream());

		return new Server<A, B>() {

			public B send(final A data) throws IOException {

				writer.write(data, toServer);
				return reader.read(fromServer);

			}

			public void terminate() throws IOException {
				server.close();
			}
		};
	}

	public static final <A, B> Client<A, B> connect(final Socket client, final Reader<A> reader, final Writer<B> writer) throws IOException {

		final DataOutputStream toClient = new DataOutputStream(client.getOutputStream());
		final DataInputStream fromClient = new DataInputStream(client.getInputStream());

		return new Client<A, B>() {

			public A receive() throws IOException {
				return reader.read(fromClient);
			}

			public void send(final B data) throws IOException {
				writer.write(data, toClient);
			}
		};
	}

	public static final ServerSocket startServer() throws IOException {

		return new ServerSocket(8001);

	}

	public static final Socket startClient() throws IOException {

		return new Socket(InetAddress.getLocalHost(), 8001);

	}
}