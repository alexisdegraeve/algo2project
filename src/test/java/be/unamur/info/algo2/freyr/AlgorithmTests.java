package be.unamur.info.algo2.freyr;


import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Unit tests to secure the algorithm results
 *
 * @author Hadrien BAILLY
 */
public class AlgorithmTests {

    @Test
    public void given_big_tree_infixe_assert_that_answer_is_correct_test() {
        final String BIG_FUCKNG_TREE = "0{1{2{3{4,5{6{7,8{9{10,11,12,13{14},15}}},16,17{18}}},19},20{21,22{23{24{25,26{27}}},28{29{30,31,32{33{34},35}}},36,37{38{39,40{41{42{43},44}},45},46{47,48{49{50,51}}}},}52{53}}}}";
        final int SIZE = 54;
        final int PATH = 4;

        assertEquals(8, new FreyrData(1, BIG_FUCKNG_TREE, SIZE, PATH).getComplexAnswer());
        assertEquals(8, new FreyrData(1, BIG_FUCKNG_TREE, SIZE, PATH).getSimpleAnswer());
    }

    @Test
    public void given_big_tree_sorted_assert_that_answer_is_correct_test() {
        final String BIG_FUCKNG_TREE = "(1,{(2,{(3,{(5,{(10),(11,{(17,{(24),(25,{(37,{(43),(44),(45),(46,{(53)}),(47)})})}),(18),(19,{(26)})})}),(6)}),(4,{(7),(8,{(12,{(20,{(27),(28,{(38)})})}),(13,{(21,{(29),(30),(31,{(39,{(48)}),(40)})})}),(14),(15,{(22,{(32),(33,{(41,{(49,{(54)}),(50)})}),(34)}),(23,{(35),(36,{(42,{(51),(52)})})})})}),(9,{(16)})})})})";
        final int SIZE = 54;
        final int PATH = 4;

        assertEquals(8, new FreyrData(1, BIG_FUCKNG_TREE, SIZE, PATH).getComplexAnswer());
        assertEquals(8, new FreyrData(1, BIG_FUCKNG_TREE, SIZE, PATH).getSimpleAnswer());
    }

    @Test
    public void given_competing_tree_1_assert_that_answer_is_correct_test() {
        //@formatter:off
        final String TREE = "1,{2,{3,{4}},5{6,{7}}}";
        final int    SIZE = 7;
        final int    PATH = 4;
        //@formatter:on

        assertEquals(1, new FreyrData(1, TREE, SIZE, PATH).getComplexAnswer());
        assertEquals(1, new FreyrData(1, TREE, SIZE, PATH).getSimpleAnswer());
    }

    @Test
    public void given_competing_tree_2_assert_that_answer_is_correct_test() {
        //@formatter:off
        final String TREE = "1,{2,{3,{4,{5}},5{6,{7,{8,{9}}}}}}";
        final int    SIZE = 10;
        final int    PATH = 4;
        //@formatter:on

        assertEquals(2, new FreyrData(1, TREE, SIZE, PATH).getComplexAnswer());
        assertEquals(2, new FreyrData(1, TREE, SIZE, PATH).getSimpleAnswer());
    }

    @Test
    public void given_competing_tree_3_assert_that_answer_is_correct_test() {
        //@formatter:off
        final String TREE = "1,{2,{3,{4}},5}";
        final int    SIZE = 5;
        final int    PATH = 4;
        //@formatter:on

        assertEquals(1, new FreyrData(1, TREE, SIZE, PATH).getComplexAnswer());
        assertEquals(1, new FreyrData(1, TREE, SIZE, PATH).getSimpleAnswer());
    }

    @Test
    public void given_competing_tree_4_assert_that_answer_is_correct_test() {
        //@formatter:off
        final String TREE = "1,{2,{3,{4},6},5}";
        final int    SIZE = 6;
        final int    PATH = 4;
        //@formatter:on

        assertEquals(1, new FreyrData(1, TREE, SIZE, PATH).getComplexAnswer());
        assertEquals(1, new FreyrData(1, TREE, SIZE, PATH).getSimpleAnswer());
    }

    @Test
    public void given_random_tree_1_assert_that_answer_is_correct_test() {
        //@formatter:off
        final String TREE = "(1, {(2, {(5),(6)}), (3, {(7),(8),(9)}), (4)})";
        final int    SIZE = 9;
        final int    PATH = 2;
        //@formatter:on

        assertEquals(3, new FreyrData(1, TREE, SIZE, PATH).getComplexAnswer());
        assertEquals(3, new FreyrData(1, TREE, SIZE, PATH).getSimpleAnswer());
    }

    @Test
    public void given_random_tree_2_assert_that_answer_is_correct_test() {
        //@formatter:off
        final String TREE = "(5, {(1, {(8),(6)}), (4, {(9)}) })";
        final int    SIZE = 6;
        final int    PATH = 3;
        //@formatter:on

        assertEquals(1, new FreyrData(1, TREE, SIZE, PATH).getComplexAnswer());
        assertEquals(1, new FreyrData(1, TREE, SIZE, PATH).getSimpleAnswer());
    }

    @Test
    public void given_random_tree_3_assert_that_answer_is_correct_test() {
        //@formatter:off
        final String TREE = "(1, {(2, {(3),(6)}), (4, {(9)}) })";
        final int    SIZE = 6;
        final int    PATH = 3;
        //@formatter:on

        assertEquals(1, new FreyrData(1, TREE, SIZE, PATH).getComplexAnswer());
        assertEquals(1, new FreyrData(1, TREE, SIZE, PATH).getSimpleAnswer());
    }

    @Test
    public void given_simple_tree_1_assert_that_answer_is_correct_test() {
        //@formatter:off
        final String TREE = "(1,{(2),(3)}";
        final int    SIZE = 3;
        final int    PATH = 3;
        //@formatter:on

        assertEquals(0, new FreyrData(1, TREE, SIZE, PATH).getComplexAnswer());
        assertEquals(0, new FreyrData(1, TREE, SIZE, PATH).getSimpleAnswer());
    }

    @Test
    public void given_simple_tree_2_assert_that_answer_is_correct_test() {
        //@formatter:off
        final String TREE = "(1,{(2,{(3,{(4)})})})";
        final int    SIZE = 4;
        final int    PATH = 4;
        //@formatter:on

        assertEquals(1, new FreyrData(1, TREE, SIZE, PATH).getComplexAnswer());
        assertEquals(1, new FreyrData(1, TREE, SIZE, PATH).getSimpleAnswer());
    }

    @Test
    public void given_simple_tree_3_assert_that_answer_is_correct_test() {
        //@formatter:off
        final String TREE = "1,{2,{3,{4,{5,{6,{7,{8}}}}}}}";
        final int    SIZE = 8;
        final int    PATH = 4;
        //@formatter:on

        assertEquals(2, new FreyrData(1, TREE, SIZE, PATH).getComplexAnswer());
        assertEquals(2, new FreyrData(1, TREE, SIZE, PATH).getSimpleAnswer());
    }

    @Test
    public void given_unique_tree_1_assert_that_answer_is_correct_test() {
        //@formatter:off
        final String TREE = "(1)";
        final int    SIZE = 1;
        final int    PATH = 5;
        //@formatter:on

        assertEquals(0, new FreyrData(1, TREE, SIZE, PATH).getComplexAnswer());
        assertEquals(0, new FreyrData(1, TREE, SIZE, PATH).getSimpleAnswer());
    }

    @Test
    public void given_unique_tree_2_assert_that_answer_is_correct_test() {
        //@formatter:off
        final String TREE = "(1)";
        final int    SIZE = 1;
        final int    PATH = 1;
        //@formatter:on

        assertEquals(1, new FreyrData(1, TREE, SIZE, PATH).getComplexAnswer());
        assertEquals(1, new FreyrData(1, TREE, SIZE, PATH).getSimpleAnswer());
    }
}
