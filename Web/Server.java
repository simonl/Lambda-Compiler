
import java.io.*;

public interface Server<A, B> {
	public B send(final A data) throws IOException;
	public void terminate() throws IOException;
}