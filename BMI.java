import java.util.*;

public class BMI {

	private static enum Units { METRIC, IMPERIAL };

	private static final Scanner input = new Scanner(System.in);

	public static void main(final String... args) {

		System.out.println("Welcome to BMI calculator!\n");

		do {
			System.out.println("Your BMI is: " + inputBMI() + "\n");
		} while(inputContinue());
	}

	private static double inputBMI() {

		final Units units = inputUnits();

		switch(units) {
			case METRIC:
				return metric();
			case IMPERIAL:
				return imperial();
			default:
				throw new IllegalStateException("Cannot happen");
		}

	}

	private static double metric() {
		final double weight = metricWeight();
		final double height = metricHeight();

		return weight / height / height;
	}

	private static double imperial() {
		final double weight = imperialWeight();
		final double height = imperialHeight();

		return 703 * weight / height / height;
	}

	private static double metricWeight() {
		return inputValue("weight", "kg", 10, 300);
	}

	private static double metricHeight() {
		return inputValue("height", "m", 0.5, 3);
	}

	private static double imperialWeight() {
		return inputValue("weight", "lb", 22, 660);
	}

	private static double imperialHeight() {
		return inputValue("height", "inch", 20, 120);
	}

	private static Units inputUnits() {
		System.out.println("\nChoose your units: metric | imperial");

		do {
			System.out.print("> ");
			final String units = input.nextLine();

			if(units.equals("metric")) {
				return Units.METRIC;
			} else if(units.equals("imperial")) {
				return Units.IMPERIAL;
			}

		} while(true);
	}

	private static double inputValue(final String quantity, final String unit, final double min, final double max) {
		System.out.println("Enter your " + quantity + ": " + min + "-" + max + " " + unit);

		do {

			try {

				System.out.print("> ");
				final double value = Double.parseDouble(input.nextLine());

				if(min <= value && value <= max)
					return value;

			} catch(final InputMismatchException e) {

			}

		} while(true);
	}

	private static boolean inputContinue() {
		System.out.println("Calculate another BMI? yes | no");

		do {

			System.out.print("> ");
			final String line = input.nextLine();

			if(line.equals("yes")) {
				return true;
			} else if(line.equals("no")) {
				return false;
			}

		} while(true);

	}
}