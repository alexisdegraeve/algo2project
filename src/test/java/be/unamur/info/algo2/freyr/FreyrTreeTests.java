package be.unamur.info.algo2.freyr;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests to secure the tree parsing strategy
 *
 * @author Hadrien BAILLY
 */
public class FreyrTreeTests {

    private static final String BIG_FUCKNG_TREE = "0{1{2{3{4,5{6{7,8{9{10,11,12,13{14},15}}},16,17{18}}},19},20{21,22{23{24{25,26{27}}},28{29{30,31,32{33{34},35}}},36,37{38{39,40{41{42{43},44}},45},46{47,48{49{50,51}}}},}52{53}}}}";
    private static final int SIZE = 54;
    private static final int PATH = 4;
    private static final FreyrTree TREE = new FreyrData(1, BIG_FUCKNG_TREE, SIZE, PATH).getTree();

    @BeforeAll
    public static void showTree() {
        TREE.display();
    }

    @Test
    public void given_empty_tree_assert_is_invalid() {
        assertThrows(RuntimeException.class,()->new FreyrData(1, "", 0, 0));
    }

    @Test
    public void given_invalid_upstreampath_in_big_tree_assert_throws_illegalArgumentException() {
        assertEquals(Optional.empty(), TREE.getNodeAt(52).getPathTo(53));
    }

    @Test
    public void given_negative_grabs_assert_throws_illegalArgumentException() {
        assertThrows(IllegalArgumentException.class, () -> new FreyrData(1, "1", -1, 1));
    }

    @Test
    public void given_null_tree_assert_throws_illegalArgumentException() {
        assertThrows(IllegalArgumentException.class, () -> new FreyrData(1, null, 1, 1));
    }

    @Test
    public void given_null_upstreampath_in_big_tree_assert_upstreampath_equals_zero() {
        //noinspection OptionalGetWithoutIsPresent
        assertEquals(0, TREE.getNodeAt(52).getPathTo(52).get().length());
    }

    @Test
    public void given_upstreampath_in_big_tree_assert_depth_equals_upstreampath() {
        //noinspection OptionalGetWithoutIsPresent
        assertEquals(TREE.getNodeAt(52).getDepth(), TREE.getNodeAt(52).getPathTo(0).get().length()
        );
    }
}
