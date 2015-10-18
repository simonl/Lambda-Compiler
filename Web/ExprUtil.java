
import java.io.*;
import java.util.*;

public final class ExprUtil {

	/*

		Expr
			= Variable String
			| Lambda String Type Expr
			| TypeLambda String Expr
			| Apply Expr Expr
			| TypeApply Expr Type

		write [Expr] (Variable name) = (0 :) . write [String] name
		write [Expr] (Lambda name annot body) = (1 :) . write [String] name . write [Type] annot . write [Expr] body
		write [Expr] (TypeLambda name body) = (2 :) . write [String] name . write [Expr] body
		write [Expr] (Apply func arg) = (3 :) . write [Expr] func . write [Expr] arg
		write [Expr] (TypeApply func arg) = (4 :) . write [Expr] func . write [Type] arg

		read [Expr] = do
			tag <- read [Byte]
			case tag of
				0 -> Variable <$> read [String]
				1 -> Lambda <$> read [String] <*> read [Type] <*> read [Expr]
				2 -> TypeLambda <$> read [String] <*> read [Expr]
				3 -> Apply <$> read [Expr] <*> read [Expr]
				4 -> TypeApply <$> read [Expr] <*> read [Type]

		typeOf (Variable name) = do
			ctx <- ask
			return ctx[name]
		typeOf (Lambda name annot body) = Arrow annot <$> local (insert name annot) (typeOf body)
		typeOf (TypeLambda name body) = Forall name <$> local (map (alpha name)) (typeOf body)
		typeOf (Apply func arg) = do
			Arrow a b <- typeOf func
			c <- typeOf arg
			guard (a == c)
			return b
		typeOf (TypeApply func arg) = do
			Forall name body <- typeOf func
			return (beta arg name body)

	*/

 	public static interface Expr {
 		public void serialize(final DataOutputStream out) throws IOException;
 		public TypeUtil.Type typeOf(final Map<String, TypeUtil.Type> context);
 	}

	public static final Serializer<Expr> serializer = new Serializer<Expr>() {

		public void write(final Expr data, final DataOutputStream out) throws IOException {
			data.serialize(out);
		}

		public Expr read(final DataInputStream in) throws IOException {

			switch(in.readByte()) {
				case 0 : {
					final String name = in.readUTF();
					return variable(name);
				}
				case 1 : {
					final String name = in.readUTF();
					final TypeUtil.Type annotation = TypeUtil.serializer.read(in);
					final Expr body = read(in);
					return lambda(name, annotation, body);
				}
				case 2 : {
					final String name = in.readUTF();
					final Expr body = read(in);
					return typeLambda(name, body);
				}
				case 3 : {
					final Expr func = read(in);
					final Expr arg = read(in);
					return apply(func, arg);
				}
				case 4 : {
					final Expr func = read(in);
					final TypeUtil.Type arg = TypeUtil.serializer.read(in);
					return typeApply(func, arg);
				}
				default :
					throw new IllegalArgumentException("Invalid serialized data!");
			}
		}
	};

	public static final TypeUtil.Type typeOf(final Expr expr) {
		return expr.typeOf(new HashMap<String, TypeUtil.Type>());
	}

	public static Expr variable(final String name) {

		return new Expr() {

			public void serialize(final DataOutputStream out) throws IOException {
				out.writeByte(0);
				out.writeUTF(name);
			}

			public TypeUtil.Type typeOf(final Map<String, TypeUtil.Type> context) {
				return context.get(name);
			}

			public String toString() {
				return name;
			}
		};
	}

	public static Expr lambda(final String name, final TypeUtil.Type annotation, final Expr body) {

		return new Expr() {

			public void serialize(final DataOutputStream out) throws IOException {
				out.writeByte(1);
				out.writeUTF(name);
				annotation.serialize(out);
				body.serialize(out);
			}


			public TypeUtil.Type typeOf(final Map<String, TypeUtil.Type> context) {
				context.put(name, annotation);

				return TypeUtil.arrow(annotation, body.typeOf(context));
			}

			public String toString() {
				return "(lambda " + name + " : " + annotation + ". " + body + ")";
			}
		};
	}

	public static Expr typeLambda(final String name, final Expr body) {

		return new Expr() {

			public void serialize(final DataOutputStream out) throws IOException {
				out.writeByte(2);
				out.writeUTF(name);
				body.serialize(out);
			}

			public TypeUtil.Type typeOf(final Map<String, TypeUtil.Type> context) {
				return TypeUtil.forall(name, body.typeOf(context));
			}

			public String toString() {
				return "(Tlambda " + name + ". " + body + ")";
			}
		};
	}

	public static Expr apply(final Expr func, final Expr arg) {

		return new Expr() {

			public void serialize(final DataOutputStream out) throws IOException {
				out.writeByte(3);
				func.serialize(out);
				arg.serialize(out);
			}

			public TypeUtil.Type typeOf(final Map<String, TypeUtil.Type> context) {
				throw new RuntimeException();
			}

			public String toString() {
				return "(" + func + " " + arg + ")";
			}
		};
	}

	public static Expr typeApply(final Expr func, final TypeUtil.Type arg) {

		return new Expr() {

			public void serialize(final DataOutputStream out) throws IOException {
				out.writeByte(4);
				func.serialize(out);
				arg.serialize(out);
			}

			public TypeUtil.Type typeOf(final Map<String, TypeUtil.Type> context) {
				throw new RuntimeException();
			}

			public String toString() {
				return "(" + func + " " + arg + ")";
			}
		};
	}
}