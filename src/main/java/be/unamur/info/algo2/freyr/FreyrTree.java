package be.unamur.info.algo2.freyr;

import lombok.Builder;
import lombok.Data;
import lombok.extern.slf4j.Slf4j;

import java.util.Arrays;
import java.util.Comparator;
import java.util.Objects;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * @author Hadrien BAILLY
 */
@Slf4j
@Data
@Builder(builderClassName = "Builder", toBuilder = true)
public class FreyrTree {

    private FreyrNode[] nodes;
    private int depth;

    /**
     * Check if the {@link #nodes current tree} is rooted, i.e. that <br>
     * - there is only one root (node without parent).<br>
     * - there is no cycle in the tree (nodes that are both ascendant and descendant to any other node).<br>
     * - there is no duplicates in the tree (nodes that share the same integer value).<br>
     *
     * @return true if the tree is rooted, false otherwise
     */
    public boolean isRooted() {
        return nodes != null && isFull() && !isSplit() && !isCyclic() && !containsDuplicateNodes();
    }

    /**
     * Check if the {@link #nodes current tree} contains any null entry.
     *
     * @return true if a null entry was found, false otherwise.
     */
    public boolean isFull() {
        return nodes != null && Arrays.stream(nodes).noneMatch(Objects::isNull);
    }

    /**
     * Check if the {@link #nodes current tree} is a single tree, i.e. if there is only one root up to which all nodes refer.
     *
     * @return true if more than one root was found, false otherwise.
     */
    public boolean isSplit() {
        return nodes != null && Arrays.stream(nodes).filter(FreyrNode::isRoot).count() > 1;
    }

    /**
     * Check if any of the subtrees in {@link #nodes current tree} is cyclic.
     *
     * @return true if any node is both ascendant and descendant to any other node, false otherwise.
     */
    public boolean isCyclic() {
        return nodes != null && Arrays.stream(nodes).anyMatch(FreyrNode::isCyclic);
    }

    /**
     * Check if the {@link #nodes current tree} contains duplicate nodes, i.e. distinct nodes with the same value.
     *
     * @return true if any node can be paired by value to any other node, false otherwise.
     */
    public boolean containsDuplicateNodes() {
        return nodes != null && Arrays.stream(nodes)
              .collect(Collectors.groupingBy(FreyrNode::getValue, Collectors.counting()))
              .values().stream().anyMatch(k -> k > 1);
    }

    /**
     * Retrieve any root node in the {@link #nodes current tree}, i.e. a node that has no parent.
     *
     * @return the first root found in the tree.
     */
    public FreyrNode getRoot() {
        return Arrays.stream(nodes)
              .filter(FreyrNode::isRoot)
              .findFirst()
              .orElseThrow(() -> new IllegalStateException("Cannot find root of tree!"));
    }

    /**
     * Retrieve a node identified its value from the tree.
     *
     * @param value the value of the node to find.
     * @return any node that matches the value, otherwise return empty.
     */
    public Optional<FreyrNode> getNodeByValue(final int value) {
        return Arrays.stream(nodes).filter(node -> node.getValue() == value).findAny();
    }

    /**
     * Retrieve a node from the tree by its physical location.
     *
     * @param index the integer value pointing to the location of the node.
     * @return the node at specified index.
     * @throws IllegalArgumentException if the index is out of bounds.
     */
    public FreyrNode getNodeAt(final int index) {
        if (index >= 0 && index < getSize()) {
            return nodes[index];
        } else {
            throw new IllegalArgumentException("Index is not contained in tree size.");
        }
    }

    /**
     * A simple method to return the size of the tree.
     *
     * @return the length of the table containing the nodes.
     */
    public int getSize() {
        return nodes.length;
    }

    /**
     * A simple method to sort the tree, using the Comparable Interface and a Mergesort implementation.
     */
    public void sort() {
        log.info("Sorting tree...");
        Arrays.sort(nodes);
        log.info("Tree successfully sorted.");
        display();
    }

    /**
     * A simple method to display the tree in a table-fashion, with complimentary details.
     */
    public void display() {
        final int size = nodes.length;

        System.out.print("\nIndex    ");
        for (int i = 0; i < size; i++) {
            System.out.printf("%3d", i);
        }
        System.out.print("\nValue    ");
        for (final FreyrNode node : nodes) {
            System.out.printf("%3d", node.getValue());
        }
        System.out.print("\nOrder    ");
        for (final FreyrNode node : nodes) {
            System.out.printf("%3d", node.getOrder());
        }
        System.out.print("\nParent   ");
        for (final FreyrNode node : nodes) {
            System.out.printf("%3d", node.getParent() == null ? 0 : node.getParent().getValue());
        }
        System.out.print("\nChildren ");
        for (final FreyrNode node : nodes) {
            System.out.printf("%3d", node.getChildren().size());
        }
        System.out.print("\nDepth    ");
        for (final FreyrNode node : nodes) {
            System.out.printf("%3d", node.getDepth());
        }
        System.out.print("\nHeight   ");
        for (final FreyrNode node : nodes) {
            System.out.printf("%3d", node.getHeight());
        }
        System.out.print("\nLeaf     ");
        for (final FreyrNode node : nodes) {
            System.out.printf("%3d", node.isCandidate() ? 1 : 0);
        }
        System.out.println("\n");
    }

    /**
     * A simple method to sort the tree by level.
     */
    public void sortByLevel() {
        log.info("Sorting tree by level...");
        Arrays.sort(nodes, Comparator.comparing(FreyrNode::getHeight));
    }

    /**
     * A simple method to sort the tree by value.
     */
    public void sortByValue() {
        log.info("Sorting tree by value...");
        Arrays.sort(nodes, Comparator.comparing(FreyrNode::getValue));
    }
}
