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

import static be.unamur.info.algo2.Main.problem_3;
import static be.unamur.info.algo2.Main.problem_3_naive;
import static org.hamcrest.MatcherAssert.assertThat;

public class Algo2Problem3Test {

    private static final Logger LOG = LoggerFactory.getLogger(Algo2Problem3Test.class);

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
    };

    @Test
    public void test_problem_3() throws Exception{
        String input = "src/test/resources/problem3/ProgrammationGlouton_4.2.txt";
        String[] result = problem_3(getFileText(input));
        String[] s_result = {"3", "1", "1", "0"};
        assertThat("Testing size array", result.length == 4);
        assertThat("Testing value[0]", result[0].equals(s_result[0]));
        assertThat("Testing value[1]", result[1].equals(s_result[1]));
        assertThat("Testing value[2]", result[2].equals(s_result[2]));
        assertThat("Testing value[3]", result[3].equals(s_result[3]));
    }

    @Test
    public void test_problem_3_naive() throws Exception{
        String input = "src/test/resources/problem3/ProgrammationGlouton_4.2.txt";
        String[] result = problem_3_naive(getFileText(input));
        String[] s_result = {"3", "1", "1", "0"};
        assertThat("Testing size array", result.length == 4);
        assertThat("Testing value[0]", result[0].equals(s_result[0]));
        assertThat("Testing value[1]", result[1].equals(s_result[1]));
        assertThat("Testing value[2]", result[2].equals(s_result[2]));
        assertThat("Testing value[3]", result[3].equals(s_result[3]));
    }
}