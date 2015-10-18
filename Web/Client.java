
import java.io.*;

public interface Client<A, B> {

	public A receive() throws IOException;
	public void send(final B data) throws IOException;

}