package be.unamur.info.algo2.freyr;

import lombok.Getter;
import lombok.Setter;
import lombok.extern.slf4j.Slf4j;

import java.util.HashSet;
import java.util.Optional;
import java.util.Set;

/**
 * An object representing a node with an integer value in an rooted tree.
 *
 * @author Hadrien BAILLY
 */
@Slf4j
@Getter
@Setter
public class FreyrNode implements Comparable<FreyrNode> {
    /**
     * An integer value representing the order of reading of the tree.<br>
     * The root reads 0, the latest node reads is the biggest value.
     */
    private int order;
    /**
     * The integer value of the node, as parsed from the tree.
     * This is only a descriptor: if two nodes have the same value, they will be different nodes regardless.
     */
    private int value;
    /**
     * A pointer to the parent node, since there is only one parent possible per node in a rooted tree.
     */
    private FreyrNode parent;
    /**
     * A list containing pointers to the children nodes.
     */
    private Set<FreyrNode> children;
    /**
     * A boolean value stating if the current node is terminal (used to prune the tree in the complex solution).
     */
    private boolean candidate;

    public FreyrNode(final int order, final int value, final FreyrNode parent) {
        this.order = order;
        this.value = value;
        this.parent = parent;
        this.candidate = true;
        this.children = new HashSet<>();
    }

    /**
     * Add a node as child to another node in the tree.
     *
     * @param node the node to attach to the current node.
     */
    public void addChild(final FreyrNode node) {
        children.add(node);
    }

    @Override
    public int compareTo(final FreyrNode o) {
        return order - o.order;
    }

    /**
     * Retrieve the length of the path to a specified node.
     *
     * @param node the value of the node to find.
     * @return an int
     */
    public int getDistanceOf(final int node) {
        final Optional<FreyrPath> upstreamPathTo = getPathTo(node);
        if (upstreamPathTo.isPresent()) {
            return upstreamPathTo.get().length();
        } else {
            throw new IllegalArgumentException("[" + node + "] is not an ascendant to [" + value + "]");
        }
    }

    /**
     * Retrieve the length of the path to a specified node.
     *
     * @param node the value of the node to find.
     * @return an int
     */
    public int getDistanceOf(final FreyrNode node) {
        final Optional<FreyrPath> upstreamPathTo = getPathTo(node);
        if (upstreamPathTo.isPresent()) {
            return upstreamPathTo.get().length();
        } else {
            throw new IllegalArgumentException("[" + node.getValue() + "] is not an ascendant to [" + value + "]");
        }
    }

    /**
     * Get a set with all the ascendants of the current node, starting from its parent.<br>
     * Starts a recursive call to process all ascendants.
     *
     * @return a set of nodes that have the current node as one of their descendant.
     */
    public Set<FreyrNode> getAscendants() {
        return getAscendants(new HashSet<>());
    }

    /**
     * Get a set with all the ascendants of the current node, starting from its parent.
     *
     * @param ascendants the list of ascendants already collected.
     * @return a set of nodes that have the current node as one of their descendant.
     */
    public Set<FreyrNode> getAscendants(final Set<FreyrNode> ascendants) {
        log.trace("Observing node [{}]", value);
        if (!isRoot()) {
            if (!ascendants.contains(parent)) {
                ascendants.add(parent);
                ascendants.addAll(parent.getAscendants(ascendants));
            }
        }
        return ascendants;
    }

    /**
     * Get a set with all the descendants of the current node, starting from its children.<br>
     * Starts a recursive call to process all descendants.
     *
     * @return a set of nodes that have the current node as one of their ascendants.
     */
    public Set<FreyrNode> getDescendants() {
        return getDescendants(new HashSet<>());
    }

    /**
     * Get a set with all the descendants of the current node, starting from its children.<br>
     *
     * @param descendants the list of descendants already collected.
     * @return a set of nodes that have the current node as one of their ascendants.
     */
    private Set<FreyrNode> getDescendants(final Set<FreyrNode> descendants) {
        for (FreyrNode child : children) {
            if (!descendants.contains(child)) {
                descendants.add(child);
                if (child.hasChildren()) {
                    final Set<FreyrNode> grandchildren = child.getChildren();
                    for (FreyrNode grandchild : grandchildren) {
                        if (!descendants.contains(grandchild)) {
                            descendants.addAll(grandchild.getDescendants(descendants));
                        }
                    }
                }
            }
        }
        return descendants;
    }

    /**
     * Compute the height of the current node as compared with the deepest node in the tree.
     *
     * @return The maximum depth of the tree minus the depth of the current node.
     */
    public int getHeight() {
        return getMaxDepth() - getDepth();
    }

    /**
     * Get the absolute maximum depth from the current tree leaves.<br>
     *
     * @return the depth from the descendant with highest depth value.
     */
    public int getMaxDepth() {
        return getDescendants().stream()
              .filter(FreyrNode::isLeaf)
              .map(FreyrNode::getDepth)
              .max(Integer::compareTo)
              .orElse(getDepth());
    }

    /**
     * Get the absolute minimum depth from the current tree leaves.<br>
     *
     * @return the depth from the descendant with smallest depth value.
     */
    public int getMinDepth() {
        return getDescendants().stream()
              .filter(FreyrNode::isLeaf)
              .map(FreyrNode::getDepth)
              .min(Integer::compareTo)
              .orElse(getDepth());
    }

    /**
     * Get the depth of the current node in the tree, according to its number of ascendants.
     *
     * @return the depth of the current node, starting at 0 for the root.
     */
    public int getDepth() {
        return getAscendants().size();
    }

    /**
     * Calculate the relative maximal depth of the current node.
     *
     * @return the maximal depth of the current node leaves.
     */
    public int getRelativeMaxDepth() {
        return getMaxDepth() - getDepth();
    }

    /**
     * Calculate the relative minimal depth of the current node.
     *
     * @return the minimal depth of the current node leaves.
     */
    public int getRelativeMinDepth() {
        return getMinDepth() - getDepth();
    }

    /**
     * Get all nodes from the tree that share the same parent with the current node.
     *
     * @return a list of nodes with the same parent, or an empty list if the current node is root.
     */
    public Set<FreyrNode> getSiblings() {
        // Check if current node has parent
        if (!isRoot()) {
            // If yes, then get parent children
            final Set<FreyrNode> children = parent.getChildren();
            // And remove current node to get only siblings
            children.remove(this);
            // Return siblings
            return children;
        } else {
            // Else, return empty siblings
            return new HashSet<>();
        }
    }

    /**
     * Check if the current node is a root, i.e. that it has no parent and is thus the start of a tree.
     *
     * @return true if the current node has no parent, false otherwise.
     */
    public boolean isRoot() {
        return parent == null;
    }

    /**
     * Get a node sequence denoting the path from this node to its ascendant.
     *
     * @param ascendant the value of ascendant node to the current node up to which make a path.
     * @return a sequence of nodes containing all ascendants to, and including, ascendant if applicable.
     */
    public Optional<FreyrPath> getPathTo(final int ascendant) {
        final FreyrPath upstreamPath = new FreyrPath();
        log.debug("Tracing path to node [{}]", ascendant);
        if (value != ascendant && !isRoot()) {
            if (getAscendants().stream().anyMatch(node -> node.getValue() == ascendant)) {
                upstreamPath.append(parent);
                parent.getPathTo(ascendant).ifPresent(upstreamPath::append);
            } else {
                return Optional.empty();
            }
        }
        return Optional.of(upstreamPath);
    }

    /**
     * Get a node sequence denoting the path from this node to its ascendant.
     *
     * @param ascendant the ascendant node to the current node up to which make a path.
     * @return a sequence of nodes containing all ascendants to, and including, ascendant if applicable.
     */
    public Optional<FreyrPath> getPathTo(final FreyrNode ascendant) {
        final FreyrPath upstreamPath = new FreyrPath();
        if (value != ascendant.getValue() && !isRoot()) {
            if (getAscendants().stream().anyMatch(node -> node == ascendant)) {
                upstreamPath.append(parent);
                parent.getPathTo(ascendant).ifPresent(upstreamPath::append);
            } else {
                return Optional.empty();
            }
        }
        return Optional.of(upstreamPath);
    }

    /**
     * Check if the current node is competing with the other node.
     *
     * @param competitor the node to check for competition for a path.
     * @param k          the path length to check for competition.
     * @return true if both nodes have a possible path of k and have a least one node in common, false otherwise.
     */
    public boolean isCompetingWith(final FreyrNode competitor, final int k) {
        final Optional<FreyrPath> thisPath = this.getPathOf(k);
        final Optional<FreyrPath> competitorPath = competitor.getPathOf(k);
        return thisPath.isPresent() && competitorPath.isPresent() &&
              thisPath.get().isCrossing(competitorPath.get());
    }

    /**
     * Get a continuous node sequence of given length among the ascendants of the current node, starting from the current node.
     *
     * @param k the length of the sequence.
     * @return a k-length node sequence if any.
     */
    public Optional<FreyrPath> getPathOf(final int k) {
        final FreyrPath path = new FreyrPath();
        for (FreyrNode node = this; node != null && path.length() < k; node = node.getParent()) {
            path.append(node);
        }
        if (path.hasLength(k)) {
            return Optional.of(path);
        } else {
            return Optional.empty();
        }
    }

    /**
     * Check if the current node is a valid starter for a continuous sequence of nodes of given length.
     *
     * @param k the length of the sequence.
     * @return true if a path can be drawn, false otherwise.
     */
    public boolean isStarterForPathOf(final int k) {
        return getPathOf(k).isPresent();
    }

    /**
     * Check if the current node is competing with another node for a path.
     *
     * @param node the node to test against.
     * @param k    the length of the path to use for testing.
     * @return true if both nodes are valid starts for paths of k and share at least one node in their path, false otherwise.
     */
    public boolean competesWithNodeForPathOf(final FreyrNode node, final int k) {
        final Optional<FreyrPath> thisPath = this.getPathOf(k);
        final Optional<FreyrPath> withPath = node.getPathOf(k);
        if (thisPath.isPresent() && withPath.isPresent()) {
            return thisPath.get().isCrossing(withPath.get());
        }
        return false;
    }

    /**
     * Check if the current node is a leaf, i.e. that it is a terminal node without any child (thus the end of a branch of the tree).
     *
     * @return true if the current node has no children whatsoever, false otherwise.
     */
    public boolean isLeaf() {
        return !hasChildren();
    }

    /**
     * Check if the current node has any child.
     *
     * @return true if the node has 1 or more children.
     */
    public boolean hasChildren() {
        return children != null && children.size() > 0;
    }

    /**
     * Check if the current node is involved in a cycle (aka being both descendant and ascendant to another node).<br>
     * Starts a recursive call to process all children.
     *
     * @return true if any descendant has this node as descendants, false otherwise.
     */
    public boolean isCyclic() {
        // Starts recursive call
        return isCyclic(new HashSet<>());
    }

    /**
     * Check if the current node is involved in a cycle (aka being both descendant and ascendant to another node).
     *
     * @param visitedNodes the list of nodes previously visited and checked for cycles.
     * @return true if the current node or any of its children was already visited.
     */
    public boolean isCyclic(final Set<FreyrNode> visitedNodes) {
        // Check if current node was already visited
        if (visitedNodes.contains(this)) {
            // If yes, then a cycle was found;
            return true;
        } else {
            // Else, mark node as visited and proceed recursively
            visitedNodes.add(this);
            // If any child raises true, then return true, false otherwise
            return getChildren().stream().anyMatch(node -> node.isCyclic(visitedNodes));
        }
    }

    /**
     * Return the number of nodes present in the current tree.
     *
     * @return the count of descendants.
     */
    public int size() {
        return getDescendants().size();
    }

    public void display(final FreyrNode node) {
        System.out.print("\nValue    ");
        System.out.printf("%3d", node.getValue());

        System.out.print("\nOrder    ");
        System.out.printf("%3d", node.getOrder());

        System.out.print("\nParent   ");
        System.out.printf("%3d", node.getParent() == null ? 0 : node.getParent().getValue());

        System.out.print("\nChildren ");
        System.out.printf("%3d", node.getChildren().size());

        System.out.print("\nDepth    ");
        System.out.printf("%3d", node.getDepth());

        System.out.print("\nHeight   ");
        System.out.printf("%3d", node.getHeight());

        System.out.print("\nLeaf     ");
        System.out.printf("%3d", node.isCandidate() ? 1 : 0);

        System.out.println("\n");
    }
}
