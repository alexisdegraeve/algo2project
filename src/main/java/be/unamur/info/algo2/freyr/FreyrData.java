package be.unamur.info.algo2.freyr;

import lombok.Data;
import lombok.extern.slf4j.Slf4j;

import java.util.HashSet;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;

/**
 * An object representing a single test data from an Algorithm test data suite.
 *
 * @author Hadrien BAILLY
 */
@Slf4j
@Data
public class FreyrData {
    /**
     * Le numéro du test
     */
    private final int index;
    /**
     * Le nombre de prises présentes dans l'arbre (aka noeud)
     */
    private final int grabs;
    /**
     * La taille des pistes pour la recherche
     */
    private final int runs;
    /**
     * L'arbre à parcourir
     */
    private final FreyrTree tree;

    /**
     * This is the test constructor method. It generates an object against which we can test the algorithmes.
     *
     * @param index the index of the test in the suite.
     * @param data  the tree data.
     * @param grabs the number of nodes in the tree.
     * @param runs  the length of k for algorithm testing.
     */
    public FreyrData(final int index, final String data, final int grabs, final int runs) {
        if (data == null) {
            throw new IllegalArgumentException("Tree data cannot be null!");
        }
        if (grabs < 0) {
            throw new IllegalArgumentException("Number of grabs must be higher than 0 [is " + grabs + "].");
        }
        if (runs <= 0) {
            throw new IllegalArgumentException("Length of runs must be higher than 0 [is " + grabs + "].");
        }
        log.info("Building test with [{}] grabs", grabs);

        log.info("Parsing data tree...");
        // La taille de l'arbre à lire
        final int length = data.length();
        // Initialisation des objets
        FreyrNode[] tree = new FreyrNode[grabs];
        // Initialisation des outils de lecture
        FreyrNode parent = null;
        int current = 0;
        boolean flushed = true;
        int nodeIndex = 0;
        int depth = 0;
        int maxDepth = 0;
        boolean rooted = false;
        // Boucle proprement dite
        for (int i = 0; i < length; i++) {
            // Lire le caractère
            final char literal = data.charAt(i);
            // Contrôler sa valeur
            if (Character.isDigit(literal)) {
                // BUILD
                // Vérifier si l'arbre a déjà une racine
                if (parent == null && rooted) {
                    throw new IllegalStateException("Attempting to build non-rooted tree!");
                }
                // Si c'est un chiffre, on construit/continue de construire le nombre
                current = current * 10 + Character.getNumericValue(literal);
                flushed = false;
            } else {
                // Sinon, on effectue des mouvements dans l'arbre
                // On vérifie tout d'abord si le nombre courant a été traité
                if (!flushed) {
                    // FLUSH
                    // Si besoin, on pousse le nombre courant dans l'arbre si besoin, càd
                    // Créer un nouveau noeud
                    final FreyrNode node = new FreyrNode(nodeIndex, current, parent);
                    // Rattacher le noeud à son parent s'il existe
                    if (parent != null) {
                        parent.addChild(node);
                    }
                    // Si l'arbre n'est pas complet
                    if (nodeIndex < grabs) {
                        // Ajouter le noeud dans l'arbre
                        tree[nodeIndex] = node;
                    }
                    // marque le nombre courant comme traité
                    flushed = true;
                    rooted = true;
                    log.trace("Flushed value [{}] at nodeIndex [{}]", current, nodeIndex);
                    // avancer dans l'arbre
                    nodeIndex++;
                    // réinitialiser le nombre
                    current = 0;
                }
                // On effectue ensuite l'opération de montée/descente de l'arbre
                // PROCESS
                if (literal == '{' && nodeIndex > 0) {
                    // Si c'est une accolade ouverte, on descend dans l'arbre
                    // On indique le parent précédent
                    parent = tree[nodeIndex - 1];
                    // On déclare le parent comme non-terminal
                    parent.setCandidate(false);
                    // On augmente la profondeur courante
                    depth++;
                    // On augmente le marqueur de profondeur maximale si nécessaire
                    if (depth > maxDepth) {
                        maxDepth++;
                    }
                    log.trace("Descending tree to [{}] at nodeIndex [{}]", parent.getValue(), parent.getOrder());
                } else if (literal == '}') {
                    // Si c'est une accolade fermée, on remonte dans l'arbre
                    // On vérifie si l'ascension est possible
                    if (parent == null) {
                        // Si non, on envoie une exception (ce n'est pas possible d'avoir un enfant sans parent)
                        throw new IllegalArgumentException("Cannot ascend tree at nodeIndex [" + nodeIndex + "]");
                    }
                    // Si oui, on diminue la profondeur courante
                    depth--;
                    log.trace("Ascending tree to [{}] at nodeIndex [{}]", parent.getValue(), parent.getOrder());
                    // On remonte le parent à son grand-parent
                    parent = parent.getParent();
                }
            }
        }
        // Tester si l'arbre est complet
        if (nodeIndex < grabs) {
            throw new IllegalArgumentException("Tree contains fewer token as expected (found [" + nodeIndex + "], expected [" + grabs + "]).");
        } else if (nodeIndex > grabs) {
            throw new IllegalArgumentException("Tree contains more token than expected (found [" + nodeIndex + "], expected [" + grabs + "]).");
        }
        // EXIT
        log.debug("Tree successfully parsed.\n");

        this.index = index;
        this.grabs = grabs;
        this.runs = runs;
        this.tree = new FreyrTree(tree, maxDepth);
    }

    /**
     * A more efficient way to process the tree, that does not require its sorting.<br>
     * Its complexity is magically O(N)!
     * Each node is only processed once : it calculates recursively the number of paths of {@link #runs k}
     * + the longest path inferior to {@link #runs k} underneath (for this is the most interesting path to use).
     *
     * @return the number of distinct paths of {@link #runs k} in the current {@link #tree}.
     */
    public int getSimpleAnswer() {
        log.info("Simply resolving test [{}]", index);
        // Préparer un compteur accessible par pointeur
        final AtomicInteger ai = new AtomicInteger(0);
        // Initialiser le parcours à la racine
        FreyrNode node = tree.getRoot();
        // Récupérer le plus grand chemins libres sous la racine, de manière récursive
        getPath(node, ai);
        log.info("Number of paths found [{}]\n", ai.get());
        // Retourner le résultat
        return ai.get();
    }

    /**
     * The recursive methode that gets the number of paths of {@link #runs k} and the longest path inferior to {@link #runs k} underneath.<br>
     * This is truly where the magic happens...
     *
     * @param node the root of the subtree to test.
     * @param ai   a shared counter that can safely be manipulated during recursion (similar to c-pointer). This value is incremented for each path of {@link #runs k} found underneath.
     * @return the longest path that is not {@link #runs k}-long. It may become {@link #runs k}-long with the current node.
     */
    /*@
      @ public normal_behavior
      @ requires 0 < p && p <Integer.MAX_VALUE;
      @ requires 0 < k && p <Integer.MAX_VALUE;
      @ requires \nonnullelements(tree);
      @ requires tree.size() == p;
      @ requires (\exists int i;0<=i && i<tree.size(); tree.getNodeAt(i).isRoot() &&
      @             !(\exists int j;0<=j && j<tree.size(); i!=j && tree.getNodeAt(j).isRoot());
      @ requires (\forall int i; 0<=i && i<tree.size(); !(\nexists int j; i<j &&  j<tree.size()
      @             tree.getNodeAt(i).getValue() == tree.getNodeAt(j).getValue());
      @
      @ ensures \result == path ==> \nonnullelements(path.getNodes())
      @ ensures \result == new FreyrData() ==> \nonnullelements(path.getNodes().isEmpty())
      @
      @ runs = \old(runs)
      @
      @ ensures ((\exists int i; 0<= i && i<this.getChildren().size(); getPath(this.getChildren().get(i),0).hasLength(runs-1)) || runs==1)
      @     ==> ai.get()== 1+(\sum int i, 0<=i && i<this.getDescendants().size() && getPath(this.descendants().get(i),0).isEmpty();1) &&
      @     path.isEmpty();
      @ ensures (!(\exists int i; 0<= i && i<this.getChildren().size(); this.getChildren().get(i).getPath().hasLength(runs-1)) && runs>1)
      @     ==> ai.get()==(\sum int i, 0<=i && i<this.getDescendants().size() && getPath(this.descendants().get(i),0).isEmpty();1) &&
      @     path.includes(this) && (\forall int i; 0<=i && i<this.getChildren().size(); path.includes(this.getChildren().get(i))
      @         ==> !(\exists int j; 0<=j && j<i; getPath(this.getChildren().get(j),0).length() > getPath(this.getChildren().get(i),0).length())
      @*/
    private FreyrPath getPath(final FreyrNode node, final AtomicInteger ai) {
        // Initialiser un nouveau chemin au noeud courant
        FreyrPath path = new FreyrPath();
        log.trace("Examining Node [{}]", node.getValue());
        // Pour chaque noeud enfant
        for (FreyrNode child : node.getChildren()) {
            // Obtenir le plus grand chemin libre en dessous
            final FreyrPath subPath = getPath(child, ai);
            // Vérifier si ce chemin fait la taille recherchée
            if (subPath.hasLength(runs)) {
                // Imprimer le chemin trouvé à l'écran
                log.info("Found path [{}]", subPath.getNodes().stream()
                      .map(FreyrNode::getValue)
                      .collect(Collectors.toList()));
                // si oui, augmenter le nombre de chemins trouvés
                ai.incrementAndGet();
            } else {
                // Sinon, vérifier si ce chemin est le plus grand possible parmi les enfants
                if (path.length() < subPath.length()) {
                    // Si oui, initialiser le chemin courant à celui-ci
                    path = subPath;
                }
            }
        }
        // Ajouter le noeud courant au chemin courant
        path.append(node);
        // Vérifier si le chemin courant fait la taille recherchée
        if (path.hasLength(runs)) {
            // Imprimer le chemin trouvé à l'écran
            log.info("Found path [{}]", path.getNodes().stream()
                  .map(FreyrNode::getValue)
                  .collect(Collectors.toList()));
            ai.incrementAndGet();
            return new FreyrPath();
        } else {
            // Retourner le plus grand chemin possible
            return path;
        }
    }

    /**
     * A very consuming answer to the test.<br>
     * Its complexity is roughly O(nLogn) for sorting the tree (mergesort) + O(n^k) for processing all nodes.<br>
     * Each leaf + each depth-nk node are read, and in its worst case there are many competing leafs requiring to process their shared ancestors several times.
     *
     * @return the number of distinct paths of {@link #runs k} in the current {@link #tree}.
     */
    /*@
      @
      @ public normal_behavior
      @ requires 0 < p && p <Integer.MAX_VALUE;
      @ requires 0 < k && p <Integer.MAX_VALUE;
      @ requires \nonnullelements(tree);
      @ requires tree.size() == p;
      @ requires (\exists int i;0<=i && i<tree.size();
                    tree.getNodeAt(i).isRoot() &&
                    !(\exists int j;0<=j && j<tree.size(); i!=j && tree.getNodeAt(j).isRoot());
      @ requires (\forall int i; 0<=i && i<tree.size();
                    !(\nexists int j; i<j &&  j<tree.size();
                        tree.getNodeAt(i).getValue() == tree.getNodeAt(j).getValue());
      @ requires (\forall int i; 0<=i && i<tree.size();tree.getNodeAt(i).isLeaf <==> tree.getNodeAt(i).isCandidate();
      @ ensures \result == i ==> i = starters.size();
      @
      @ ensures runs = \old(runs),
      @ ensures tree = \old(tree);
      @
      @ ensures (\forall int i; 0<= i && i<starters.size(); starters.get(i).isLeaf() ||
      @             (\exists int j;0<=j && j<starters.size() && i!=j; starters.get(j).getDistanceOf(starters.get(i))==k);
      @ ensures (\forall int i; 0<= i && i<starters.size(); starters.get(i).isCandidate();
      @ ensures (\forall int i, j; 0<= i && i< j && i< starters.size(); !starters.get(j).getPathOf(runs).isCrossing(starters.get(j).getPathOf(runs)));
      @ ensures (\forall int i; 0<=i && i<tree.size(); tree.getNodeAt(i).isCandidate() && !starters.contains(tree.getNodeAt(i)) ==>
      @             (\exists int j; 0<=j && j<starters.size(); tree.getNodeAt(i).getPathOf(k).isCrossing(starters.get(j).getPathOf(k)) &&
      @             starters.get(i).getDepth()<=tree.getNodeAt(i).getDepth());
      @
      @*/
    public int getComplexAnswer() {
        log.info("Elaborately resolving test [{}]", index);
        // Pré-trier l'arbre pour un parcours en largeur
        tree.sort();

        // Préparer l'ensemble F des départs non-concurrents trouvés dans l'arbre
        final Set<FreyrNode> starters = new HashSet<>();
        // Préparer un memo des noeuds utilisés
        boolean[] usedNodes = new boolean[grabs];

        // Parcourir les noeuds de manière ascendante (càd en partant des feuilles)
        for (int index = grabs - 1; index >= 0; index--) {
            // Prendre un noeud de départ
            FreyrNode node = tree.getNodeAt(index);
            log.trace("Examining node [{}] at index [{}]", node.getValue(), index);
            // Vérifier si le noeud est un candidat à commencer/poursuivre un chemin et s'il est disponible (non-utilisé)
            if (node.isCandidate() && !usedNodes[node.getOrder()] && node.getDepth() + 1 >= runs) {
                log.trace("Node is free");
                // Si oui, récupérer son chemin
                //noinspection OptionalGetWithoutIsPresent
                FreyrPath path = node.getPathOf(runs).get();
                // Vérifier si aucun noeud du chemin n'est pas déjà utilisé
                if (path.getNodes().stream().noneMatch(step -> usedNodes[step.getOrder()])) {
                    log.debug("Found path[{}]", path.getNodes().stream()
                          .map(FreyrNode::getValue)
                          .collect(Collectors.toList())
                          .toString());
                    // Pour chaque noeud sur le chemin, marquer l'indice comme occupé
                    path.getNodes().forEach(step -> usedNodes[step.getOrder()] = true);
                    // Récupérer le noeud consécutif au point d'arrivée
                    //noinspection OptionalGetWithoutIsPresent
                    final FreyrNode endPoint = path.getEndingNode().get().getParent();
                    // Vérifier s'il existe
                    if (endPoint != null) {
                        // Si oui, le marquer comme nouveau candidat
                        endPoint.setCandidate(true);
                    }
                    // Enfin, ajouter le départ à l'ensemble F
                    //noinspection OptionalGetWithoutIsPresent
                    starters.add(path.getStartingNode().get());
                }
            } else {
                log.trace("Node was used.");
            }
        }
        // Une fois que tous les noeuds candidats ont été testés, retourner le résultat
        log.info("Number of paths found [{}]\n", starters.size());
        return starters.size();
    }

}
