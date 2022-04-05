package be.unamur.info.algo2.freyr;

import lombok.Data;
import lombok.extern.slf4j.Slf4j;

/**
 * An object representing an algorithm test data suite.
 *
 * @author Hadrien BAILLY
 */
@Slf4j
@Data
public class FreyrSeries {
    int count;
    FreyrData[] tests;

    /**
     * A constructor to generate the suite from a single string with line feeds.
     *
     * @param series the test suite in a single block.
     */
    public FreyrSeries(final String series) {
        this(series.split("\r\n|\n"));
    }

    /**
     * A constructor to generate the test suite from tuples of lines.
     *
     * @param series the test suite split in lines.
     */
    public FreyrSeries(final String[] series) {
        try {
            final int count = Integer.parseInt(series[0]);
            log.info("File contains {} tests", count);
            this.count = count;
            if (series.length != 2 * count + 1) {
                throw new IllegalArgumentException("File size does not match test count (found [" + (series.length / 2 - 1) + "], expected [" + count + "])");
            }
            if (this.count > 0) {
                this.tests = getFreyrData(series);
            } else {
                this.tests = null;
                log.error("No test found!");
            }
        } catch (ArrayIndexOutOfBoundsException e) {
            throw new IllegalArgumentException("Failed to read test count.", e);
        } catch (NumberFormatException e) {
            throw new IllegalArgumentException("Cannot parse test count.", e);
        }
    }

    /**
     * A method to extract the test data from the test suite.
     *
     * @param series the test suite split in lines.
     * @return an array of test data corresponding to the test suite.
     */
    private FreyrData[] getFreyrData(final String[] series) {
        FreyrData[] data = new FreyrData[this.count];
        for (int i = 1; i <= this.count; i++) {
            log.info("Processing test {}", i);
            try {
                final String[] header = series[2 * i - 1].split(" ");
                try {
                    final int grabs = Integer.parseInt(header[0]);
                    final int runs = Integer.parseInt(header[1]);
                    try {
                        final String unparsedTree = series[2 * i];
                        data[i - 1] = new FreyrData(i, unparsedTree, grabs, runs);
                    } catch (ArrayIndexOutOfBoundsException e) {
                        throw new IllegalArgumentException("Failed to read test [" + i + "] data.");
                    }
                } catch (ArrayIndexOutOfBoundsException e) {
                    throw new IllegalArgumentException("Failed to read test [" + i + "] parameter.");
                } catch (NumberFormatException e) {
                    throw new IllegalArgumentException("Cannot parse test " + i + " parameters [" + series[2 * i - 1] + "].");
                }
            } catch (ArrayIndexOutOfBoundsException e) {
                throw new IllegalArgumentException("Failed to read test [" + i + "] headers.");
            }
        }
        return data;
    }

    /**
     * A method to call all results from the test suite using the greedy algorithm.
     *
     * @return a String array containing the result of each test, or null if there was any exception raised.
     */
    public String[] getSimpleResults() {
        try {
            String[] results = new String[count];
            for (int i = 0; i < count; i++) {
                results[i] = String.valueOf(tests[i].getSimpleAnswer());
            }
            return results;
        } catch (RuntimeException e) {
            log.error("Failed to process test results", e);
            return null;
        }
    }
    /**
     * A method to call all results from the test suite using the naive algorithm.
     *
     * @return a String array containing the result of each test, or null if there was any exception raised.
     */
    public String[] getComplexResults() {
        try {
            String[] results = new String[count];
            for (int i = 0; i < count; i++) {
                results[i] = String.valueOf(tests[i].getComplexAnswer());
            }
            return results;
        } catch (RuntimeException e) {
            log.error("Failed to process test results", e);
            return null;
        }
    }

}
