
import java.io.*;

public final class TypeUtil {



	/*

	Type
		= Variable String
		| Arrow Type Type
		| Forall String Type

	write [Type] (Variable name = (0 :) . write [String] name
	write [Type] (Arrow left right = (1 :) . write [Type] left . write [Type] right
	write [Type] (Forall name body = (2 :) . write [String] name . write [Type] body

	read [Type] = do
		tag <- read [Byte]
		case tag of
			0 -> Variable <$> read [String]
			1 -> Arrow <$> read [Type] <*> read [Type]
			2 -> Forall <$> read [String] <*> read [Type]

	*/


	public static abstract class Type {
		public abstract void serialize(final DataOutputStream out) throws IOException;
	}


	public static final Serializer<Type> serializer = new Serializer<Type>() {

		public void write(final Type data, final DataOutputStream out) throws IOException {
			data.serialize(out);
		}

		public Type read(final DataInputStream in) throws IOException {
			switch(in.readByte()) {
				case 0 : {
					final String name = in.readUTF();
					return variable(name);
				}
				case 1 : {
					final Type left = read(in);
					final Type right = read(in);

					return arrow(left, right);
				}
				case 2 : {
					final String name = in.readUTF();
					final Type body = read(in);
					return forall(name, body);
				}
				default :
					throw new IllegalArgumentException("Invalid serialized data!");
			}
		}
	};


	public static final Type variable(final String name) {

		return new Type() {

			public void serialize(final DataOutputStream out) throws IOException {
				out.writeByte(0);
				out.writeUTF(name);
			}

			public String toString() {
				return name;
			}
		};
	}

	public static final Type arrow(final Type left, final Type right) {

		return new Type() {

			public void serialize(final DataOutputStream out) throws IOException {
				out.writeByte(1);
				left.serialize(out);
				right.serialize(out);
			}

			public String toString() {
				return "(" + left.toString() + " -> " + right.toString() + ")";
			}
		};
	}

	public static final Type forall(final String name, final Type body) {
		return new Type() {

			public void serialize(final DataOutputStream out) throws IOException {
				out.writeByte(2);
				out.writeUTF(name);
				body.serialize(out);
			}


			public String toString() {
				return "(forall " + name + ". " + body + ")";
			}
		};
	}
}



