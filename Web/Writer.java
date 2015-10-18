
import java.io.*;

public interface Writer<A> {
	public void write(final A value, final DataOutputStream out) throws IOException;
}