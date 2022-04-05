package be.unamur.info.algo2;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.junit.rules.TestRule;
import org.junit.rules.TestWatcher;
import org.junit.runner.Description;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;

import static org.hamcrest.MatcherAssert.assertThat;

public class Algo2Problem2Test {

    private static final Logger LOG = LoggerFactory.getLogger(Algo2Problem2Test.class);

    private String getFileText(String input) throws IOException {
        return new String(Files.readAllBytes(Paths.get(input)));
    }

    @Rule
    public TemporaryFolder testFolder = new TemporaryFolder(); // Create a temporary folder for outputs deleted after tests

    @Rule
    public TestRule watcher = new TestWatcher() { // Prints message on logger before each test
        @Override
        protected void starting(Description description) {
            LOG.info(String.format("Starting test: %s()...",
                    description.getMethodName()));
        }
    ;
    };

    @Test
    public void test_problem_2() throws Exception{
        Main main = new Main();
        String input = "src/test/resources/problem2/ProgrammationDynamique_3.2.txt";
        String[] result = main.problem_2(getFileText(input));
        String[] s_result = {"11", "1", "4", "0"}; //String[] s_result = {"11", "1", "9", "0"};
        assertThat("Testing size array", result.length == 4);
        assertThat("Testing value[0]", result[0].equals(s_result[0]));
        assertThat("Testing value[1]", result[1].equals(s_result[1]));
        assertThat("Testing value[2]", result[2].equals(s_result[2]));
        assertThat("Testing value[3]", result[3].equals(s_result[3]));
    }

    @Test
    public void test_problem_2_naive() throws Exception{
        Main main = new Main();
        String input = "src/test/resources/problem2/ProgrammationDynamique_3.2.txt";
        String[] result = main.problem_2_naive(getFileText(input));
        String[] s_result = {"11", "1", "4", "0"}; //String[] s_result = {"11", "1", "9", "0"};
        assertThat("Testing size array", result.length == 4);
        assertThat("Testing value[0]", result[0].equals(s_result[0]));
        assertThat("Testing value[1]", result[1].equals(s_result[1]));
        assertThat("Testing value[2]", result[2].equals(s_result[2]));
        assertThat("Testing value[3]", result[3].equals(s_result[3]));
    }
}