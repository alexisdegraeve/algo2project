package be.unamur.info.algo2.freyr;

import lombok.Data;
import lombok.extern.slf4j.Slf4j;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * @author Hadrien BAILLY
 */
@Slf4j
@Data
public class FreyrPath {
    /**
     * A sequence of nodes composing the path.<br>
     * Nodes are expected to be sequential, i.e. to have max. one parent or one child in the path.
     */
    List<FreyrNode> nodes = new ArrayList<>();

    /**
     * A default constructor that starts a new path with no node.
     */
    public FreyrPath() {
    }

    /**
     * A constructor that initiate a path from the parameter node.
     *
     * @param startPoint the node to start the path with.
     */
    public FreyrPath(final FreyrNode startPoint) {
        append(startPoint);
    }

    /**
     * Add a node to the end of the path.
     *
     * @param node the node to append to this path.
     * @throws IllegalArgumentException if the path is not empty and the passed node is not parent to the last node in the path.
     */
    public void append(final FreyrNode node) {
        if (getEndingNode().isPresent() &&
              !getEndingNode().get().getParent().equals(node)) {
            throw new IllegalArgumentException("Current node [" + node.getValue() + "] is not the parent of the last node node on the path");
        }
        nodes.add(node);
    }

    /**
     * Get the last node on the path if it exists.
     *
     * @return the last node if it exists, otherwise an empty optional.
     */
    public Optional<FreyrNode> getEndingNode() {
        if (isEmpty()) {
            return Optional.empty();
        } else {
            return Optional.ofNullable(nodes.get(nodes.size() - 1));
        }
    }

    /**
     * Check if the current path contains any node.
     *
     * @return true if the list of node is empty, false otherwise.
     */
    public boolean isEmpty() {
        return nodes.isEmpty();
    }

    /**
     * Check if the current path is similar to another path.
     *
     * @param path the path to compare with.
     * @return true if both paths contain nodes and share the same ending node, false otherwise.
     */
    public boolean isSimilarTo(final FreyrPath path) {
        final Optional<FreyrNode> thisEnding = getEndingNode();
        final Optional<FreyrNode> otherEnding = path.getEndingNode();

        return (thisEnding.isPresent() && otherEnding.isPresent()) &&
              thisEnding.get().equals(otherEnding.get());
    }

    /**
     * Check if the current path is distinct from another path.
     *
     * @param path the path to compare with.
     * @return false if both paths contain nodes and share at least one node, true otherwise.
     */
    public boolean isDistinct(final FreyrPath path) {
        return !isCrossing(path);
    }

    /**
     * Check if the current path is crossing another path.
     *
     * @param path the path to compare with.
     * @return true if both paths contain nodes and share at least one node.
     */
    public boolean isCrossing(final FreyrPath path) {
        if (this.isEmpty() || path.isEmpty()) {
            return false;
        }
        for (FreyrNode node : nodes) {
            if (path.getNodes().contains(node)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Check if the current path has the length required.
     *
     * @param k the length to enquiry.
     * @return true if the path length matches the enquiry length.
     */
    public boolean hasLength(final int k) {
        return length() == k;
    }

    /**
     * Get the current length of the path.
     *
     * @return an integer equal to the number of nodes on the path.
     */
    public int length() {
        return nodes.size();
    }

    /**
     * Append a path to the current path.
     *
     * @param path the path to append to this path.
     * @throws IllegalArgumentException if the parameter path starting node and this ending node exists
     *                                  but the starting node is not parent to the ending node of the path.
     */
    public void append(final FreyrPath path) {
        final Optional<FreyrNode> thisEnding = getEndingNode();
        if (thisEnding.isPresent()) {
            final Optional<FreyrNode> otherStarting = path.getStartingNode();
            if (otherStarting.isPresent()) {
                if (!thisEnding.get().getParent().equals(otherStarting.get())) {
                    throw new IllegalArgumentException("The starting node of the path [" + otherStarting.get().getValue() + "] is not the parent of the last node node on the path");
                }
            }
        }
        nodes.addAll(path.getNodes());
    }

    /**
     * Get the first  node on the path if it exists.
     *
     * @return the first node if it exists, otherwise an optional empty.
     */
    public Optional<FreyrNode> getStartingNode() {
        if (!isEmpty()) {
            return Optional.ofNullable(nodes.get(0));
        } else {
            return Optional.empty();
        }
    }

    /**
     * Start a new path starting from the parameter node.
     *
     * @param node the node to restart the path to and append with the current path.
     * @throws IllegalArgumentException if the node is not a child of the current path starting node.
     */
    public void prepend(final FreyrNode node) {
        final Optional<FreyrNode> thisStarting = getStartingNode();
        if (thisStarting.isPresent() && !node.getParent().equals(thisStarting.get())) {
            throw new IllegalArgumentException("The passed node [" + thisStarting.get().getValue() + "] is not a child of the path current starting node");
        }
        final List<FreyrNode> newPath = new ArrayList<>();
        newPath.add(node);
        newPath.addAll(nodes);
        nodes = newPath;
    }

    /**
     * Start a new path starting from the parameter node.
     *
     * @param path the path to restart the path to and append with the current path.
     * @throws IllegalArgumentException if both the path ending node and the current path starting node exist
     *                                  and the path ending node is not a child of the current starting node.
     */
    public void prepend(final FreyrPath path) {
        final Optional<FreyrNode> thisStarting = getStartingNode();
        if (thisStarting.isPresent()) {
            final Optional<FreyrNode> otherEnding = path.getEndingNode();
            if (otherEnding.isPresent()) {
                if (!otherEnding.get().getParent().equals(thisStarting.get())) {
                    throw new IllegalArgumentException("The passed path starting node [" + thisStarting.get().getValue() + "] is not a child of the path current starting node");
                }
            }
        }
        final List<FreyrNode> newPath = new ArrayList<>();
        newPath.addAll(path.getNodes());
        newPath.addAll(nodes);
        nodes = newPath;
    }

}
