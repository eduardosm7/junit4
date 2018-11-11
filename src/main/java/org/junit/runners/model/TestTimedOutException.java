package org.junit.runners.model;

import java.util.concurrent.TimeUnit;

/**
 * Exception thrown when a test fails on timeout.
 * 
 * @since 4.12
 * 
 */
public class TestTimedOutException extends Exception {

    private /*@ spec_public @*/ static final long serialVersionUID = 31935685163547539L;

    private /*@ spec_public @*/ final TimeUnit timeUnit;
    private /*@ spec_public @*/ final long timeout;

    //@ invariant this.serialVersionUID == 31935685163547539L;

    /**
     * Creates exception with a standard message "test timed out after [timeout] [timeUnit]"
     * 
     * @param timeout the amount of time passed before the test was interrupted
     * @param timeUnit the time unit for the timeout value
     */
    //@ ensures this.timeout == timeout;
    //@ ensures this.timeUnit == timeUnit;
    public TestTimedOutException(long timeout, TimeUnit timeUnit) {
        super(String.format("test timed out after %d %s", 
                timeout, timeUnit.name().toLowerCase()));
        this.timeUnit = timeUnit;
        this.timeout = timeout;
    }

    /**
     * Gets the time passed before the test was interrupted
     */
    //@ ensures \result == this.timeout;
    public long getTimeout() {
        return timeout;
    }

    /**
     * Gets the time unit for the timeout value
     */
    //@ ensures \result == this.timeUnit;
    public TimeUnit getTimeUnit() {
        return timeUnit;
    }
}
