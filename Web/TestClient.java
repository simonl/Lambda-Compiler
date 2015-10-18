
import java.io.*;
import java.net.*;

public class TestClient {

	public static final void main(final String... args) throws IOException {

		final Server<ExprUtil.Expr, TypeUtil.Type> typecheckerServer = WebTest.connect(WebTest.startClient(), ExprUtil.serializer, TypeUtil.serializer);

		// Lam a. lam x:a. x
		final ExprUtil.Expr expr = ExprUtil.typeLambda("a", ExprUtil.lambda("x", TypeUtil.variable("a"), ExprUtil.variable("x")));

		// For a. a -> a
		final TypeUtil.Type type = typecheckerServer.send(expr);

		// lam x:a. x
		final ExprUtil.Expr wrong =  ExprUtil.lambda("x", TypeUtil.variable("a"), ExprUtil.variable("x"));

		// a -> a
		final TypeUtil.Type wrongType = typecheckerServer.send(wrong);

		typecheckerServer.terminate();
	}
}