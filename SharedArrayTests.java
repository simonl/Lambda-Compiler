public final class SharedArrayTests {

	public static interface Array {
		public Object get(final int index);
		public Array set(final int index, final Object value);
	}

	public static interface Ref<T> {
		public T get();
		public void set(final T value);
	}

	public static interface Func<A, B> {
		public B apply(final A value);
	}

	public static final <T> Ref<T> ref(final T value) {
		return new Ref<T>() {
			private T state = value;

			public T get() {
				return this.state;
			}

			public void set(final T value) {
				this.state = value;
			}
		};
	}

	public static final <B> Func<Array, B> lend(final Func<Array, B> function) {
		return new Func<Array, B>() {
			public B apply(final Array array) {
				final LentArray lent = new LentArray(array);
				final B result = function.apply(lent);
				lent.invalidate();
				return result;
			}
		};
	}

	public static final class LentArray implements Array {

		private final Ref<Boolean> valid;
		private final Array wrapped;

		public LentArray(final Array wrapped) {
			this(ref(true), wrapped);
		}

		private LentArray(final Ref<Boolean> valid, final Array wrapped) {
			this.valid = valid;
			this.wrapped = wrapped;
		}

		public Object get(final int index) {
			if(!valid.get()) throw new IllegalStateException();

			return wrapped.get(index);
		}

		public LentArray set(final int index, final Object value) {
			if(!valid.get()) throw new IllegalStateException();

			return new LentArray(valid, wrapped.set(index, value));
		}

		public void invalidate() {
			valid.set(false);
		}
	}

	public static final class SharedArray implements Array {
		private int refcount = 0;
		private final Object[] array;

		public SharedArray(final int length) {
			this(new Object[length]);
		}

		private SharedArray(final Object[] array) {
			this.array = array;
		}

		public Object get(final int index) {
			return array[index];
		}

		public SharedArray set(final int index, final Object value) {
			if(refcount == 0) {
				array[index] = value;
				return this;
			} else {
				final Object[] copy = new Object[array.length];

				for(int i = 0; i < array.length; i++)
					copy[i] = array[i];

				return new SharedArray(copy);
			}
		}

		public void obtain() {
			this.refcount++;
		}

		public void release() {
			this.refcount--;
		}
	}
}