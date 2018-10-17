package junit.framework;

/**
 * Thrown when an assert equals for Strings failed.
 *
 * Inspired by a patch from Alex Chaffee mailto:alex@purpletech.com
 */
public class ComparisonFailure extends AssertionFailedError {
    private /*@ spec_public @*/ static final int MAX_CONTEXT_LENGTH = 20;
    private /*@ spec_public @*/ static final long serialVersionUID = 1L;

    private /*@ spec_public @*/ String fExpected;
    private /*@ spec_public @*/ String fActual;
    
    //@ invariant this.MAX_CONTEXT_LENGTH == 20;
    //@ invariant this.serialVersionUID == 1L;
    
    /**
     * Constructs a comparison failure.
     *
     * @param message the identifying message or null
     * @param expected the expected string value
     * @param actual the actual string value
     */
    //@ requires expected != null;
    //@ requires actual != null;
    //@ ensures this.fExpected == expected;
    //@ ensures this.fActual == actual;
    public ComparisonFailure(String message, String expected, String actual) {
        super(message);
        fExpected = expected;
        fActual = actual;
    }

    /**
     * Returns "..." in place of common prefix and "..." in
     * place of common suffix between expected and actual.
     *
     * @see Throwable#getMessage()
     */
    //@ also ensures \result != null;
    @Override
    public String getMessage() {
        return new ComparisonCompactor(MAX_CONTEXT_LENGTH, fExpected, fActual).compact(super.getMessage());
    }

    /**
     * Gets the actual string value
     *
     * @return the actual string value
     */
    //@ ensures \result == this.fActual;
    public String getActual() {
        return fActual;
    }

    /**
     * Gets the expected string value
     *
     * @return the expected string value
     */
    //@ ensures \result == this.fExpected;
    public String getExpected() {
        return fExpected;
    }
}