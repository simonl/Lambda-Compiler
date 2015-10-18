
 import java.io.*;

 public interface Reader<A> {
 	public A read(final DataInputStream in) throws IOException;
}