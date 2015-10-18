
import java.io.*;

public class TestServer {

	public static final void main(final String... args) throws IOException {

		WebTest.serve(typecheck(), ExprUtil.serializer, TypeUtil.serializer);

	}

	public static final Func<ExprUtil.Expr, TypeUtil.Type> typecheck() {

		return new Func<ExprUtil.Expr, TypeUtil.Type>() {

			public TypeUtil.Type apply(final ExprUtil.Expr expr) {
				return ExprUtil.typeOf(expr);
			}
		};
	}
}