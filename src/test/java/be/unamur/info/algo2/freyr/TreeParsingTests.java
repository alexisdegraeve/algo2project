package be.unamur.info.algo2.freyr;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import java.util.Arrays;
import java.util.Objects;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests to secure the tree parsing strategy
 *
 * @author Hadrien BAILLY
 */
public class TreeParsingTests {

    private static final String BIG_FUCKNG_TREE = "0{1{2{3{4,5{6{7,8{9{10,11,12,13{14},15}}},16,17{18}}},19},20{21,22{23{24{25,26{27}}},28{29{30,31,32{33{34},35}}},36,37{38{39,40{41{42{43},44}},45},46{47,48{49{50,51}}}},}52{53}}}}";
    private static final int SIZE = 54;
    private static final int PATH = 4;
    private static final FreyrTree TREE = new FreyrData(1, BIG_FUCKNG_TREE, SIZE, PATH).getTree();

    @BeforeAll
    public static void showTree() {
        TREE.display();
    }

    @Test
    public void given_big_tree_parsing_assert_all_nodes_depth_matches_ascendants() {
        assertEquals(0, Arrays.stream(TREE.getNodes()).filter(node -> node.getDepth() != node.getAscendants().size()).count());
    }

    @Test
    public void given_big_tree_parsing_assert_that_leaves_have_no_children() {
        assertEquals(0, Arrays.stream(TREE.getNodes()).filter(node -> node.isCandidate() && node.hasChildren()).count());
    }

    @Test
    public void given_big_tree_parsing_assert_that_number_of_token_is_valid() {
        assertEquals(0, Arrays.stream(TREE.getNodes()).filter(Objects::isNull).count());
    }

    @Test
    public void given_big_tree_parsing_assert_that_only_root_has_null_parent() {
        assertNull(TREE.getRoot().getParent());
        assertEquals(1, Arrays.stream(TREE.getNodes()).filter(FreyrNode::isRoot).count());
    }

    @Test
    public void given_number_of_grabs_higher_than_expected_then_throws_illegalArgumentException() {
        final String sapling = "(1,{(2),(3)}";
        final int expectedTokens = 2;

        assertThrows(IllegalArgumentException.class, () -> new FreyrData(1, sapling, expectedTokens, 2));
    }

    @Test
    public void given_number_of_grabs_lower_than_expected_then_throws_illegalArgumentException() {
        final String sapling = "(1,{(2),(3)}";
        final int expectedTokens = 4;

        assertThrows(IllegalArgumentException.class, () -> new FreyrData(1, sapling, expectedTokens, 2));
    }
}
