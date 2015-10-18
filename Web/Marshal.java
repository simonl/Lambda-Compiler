
import java.io.*;

public interface Serializer<A> {
	public void write(final A value, final DataOutputStream out) throws IOException;
	public A read(final DataInputStream in) throws IOException;
}