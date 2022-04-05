package be.unamur.info.algo2.firefighter;

/**
 *
 * Programmation Dynamique : Le pompier Namurois (Version Dynamique)
 * But : Un pompier volontaire doit trouver le maximum de personnes à sauver dans un building suivant un chemin.
 *
 * Règle: Le pompier ne peut se déplacer que vers la droite ou que vers la gauche suivant l'étage ou vers le bas.
 *        Il peut aller à droite s'il est sur un numéro d'étage pair et
 *        uniquement à gauche s'il est sur un numéro d'étage impair.
 *        Une pièce qui est bloquée est représentée par -1.
 *
 * @author  Alexis DEGRAEVE
 * @since   2020-12-10
 * @link    https://github.com/UNamurCSFaculty/2021_IHDCB331_G09
 *
 **/


/**
 * ------------------------------------------------------------------------
 * FireFigherNaive : Définition de la classe
 * ------------------------------------------------------------------------
 */

public class FireFighterDynamic {

    /* Variable pour stocker tout les buildings */
    private int[][][] allBuilding;

    /**
     * Constructeur de FireFighterNaive
     *
     * @param  files  est une chaîne de caractères qui représente le fichier en entrée.
     */
    public FireFighterDynamic(final String files) {
        allBuilding = readFile(files);
    }

    /**
     * Méthode pour parcourir tous les buildings et
     *         retourner le nombre maximum de personnes à sauver pour chaque building
     *
     * @return  un tableau de chaine de caractères (String[])
     */
    public String[] rescueAllBuildings() {
        String[] resultat = null;
        try {
            if(allBuilding != null) {
                resultat = new String[allBuilding.length];
                for (int i = 0; i < allBuilding.length; i++) {
                    int savePerson = rescuePeople(allBuilding[i]);
                    resultat[i] = String.valueOf(savePerson);
                }
            }
            return resultat;
        } catch (RuntimeException e) {
            return null;
        }
    }

    /**
     * Méthode pour lire un fichier et le stocker dans un tableau à trois dimensions.
     *         chaque building sera stocké dans un tableau à 2D.
     *         Pour le fichier en entrée qui est une chaine de caractère on split chaque élément
     *         suivant les espaces et ou enter et on le stocke dans le tableau.
     *         Il y a une gestion des exceptions si le caractère n'a pas pu être transformé en nombre,
     *              si on dépasse le nombre de colonne et ou de ligne il y a aussi une exception lancée
     *
     * @param  fileName est une chaîne de caractères qui représente le fichier en entrée.
     * @return  un tableau d'entier à trois dimensions (int[][][])
     */
    private int[][][] readFile(String fileName) {
        int[][][] fireFighter = null;
        int i = 0;
        try {
            String[] lines = fileName.split("\r\n|\n");
            if(lines.length == 0) {
                return null;
            }
            int totalArray = Integer.parseInt(lines[i]);
            if (totalArray > 0) {
                fireFighter = new int[totalArray][][];
            }
            int currentTable = 0;
            while ((currentTable < totalArray) && (i < (lines.length -1))) {
                i++;
                String[] totalRowLines = lines[i].split("\\s+");
                int totalRow =  Integer.parseInt(totalRowLines[0]);
                int totalCol =  Integer.parseInt(totalRowLines[1]);
                fireFighter[currentTable] = new int[totalRow][];
                for (int j = 0; j < totalRow; j++) {
                    i++;
                    String[] readLineTab = lines[i].split("\\s+");
                    fireFighter[currentTable][j] = new int[totalCol];
                    for (int k = 0; k < totalCol ; k++) {
                        fireFighter[currentTable][j][k] = Integer.parseInt(readLineTab[k]);
                        if(k > readLineTab.length - 1) {
                            fireFighter = null;
                            throw new ArrayIndexOutOfBoundsException(); // Trop de colonne déclarée
                        }
                    }
                    if(i > lines.length - 1) {
                        fireFighter = null;
                        throw new ArrayIndexOutOfBoundsException(); // Trop de ligne déclarée
                    }
                }
                currentTable++;
            }

            if(currentTable < totalArray) {
                throw new Exception("All the table are not assigned"); // Toutes les tables n'ont pas été assignées
            }
        }catch(final ArrayIndexOutOfBoundsException e) {
            return null;
        }
        catch (final NumberFormatException e) {
            return null;
        }
        catch (Exception e) {
            e.printStackTrace();
        }
        return fireFighter;
    }

    /**
     * Méthode pour retourner le nombre de personnes à sauver pour un building.
     *
     * @param  building est un tableau à deux dimensions qui représente le building que le pompier doit parcourir
     * @return  un entier qui est le nombre de personnes sauvées. 0 >= personne(s) sauvée(s) > maxInt(en Java)
     *
     */
    private int rescuePeople(int[][] building) {
        int posX = 0;
        int posY = 0;
        int buildingSave[][] = InitializeCountArray(building);
        int savePerson = savePeople(posX, posY, building, buildingSave);
        return savePerson;
    }

    /**
     * Méthode pour initialisé le tableau de sauvegarde qui va servir pour la version dynamique.
     *         Cette méthode retourne un tableau initialiser.
     *
     * @param  building est un tableau à deux dimensions qui représente le building que le pompier doit parcourir
     * @return  tableau à deux dimensions qui contiendra -1 pour toutes les cases du tableaux.
     *          -1  indique que la case n'a pas encore été calculée
     *
     */
    private int[][] InitializeCountArray(int[][] building) {
        int[][] buildingSave = new int[building.length][];
        for (int i = 0; i < building.length; i++) {
            buildingSave[i] = new int[building[i].length];
            for (int j = 0; j < building[i].length; j++) {
                buildingSave[i][j] = -1;
            }
        }
        return buildingSave;
    }

    //@ requires posX >= 0 && posX < building.length;
    //@ requires posY >= 0 && posY < building[0].length;
    //@ loop_invariant 0 <= i && i <= building.length ;
    //@ loop_invariant (\ forall int l; 0 <= l && l < i;
    //@                 building [l] >= -1);
    //@ loop_invariant 0 <= j && j <= buildingSave.length ;
    //@ loop_invariant (\ forall int k; 0 <= k && k < j;
    //@                 building [k] >= -1);
    //@ ensures \result >= 0;

    /**
     * Méthode principale por retourner le nombre de personnes sauvées pour un building.
     *                    La différence avec la version naive c'est qu'on check d'abord dans le tableau de sauvegarde
     *                    si la valeur a déjà été calculée pour ce chemin sinon on le calcule et on le stocke dans le
     *                    tableau ce qui évite de recalculer des totaux (personnes sauvées) déjà calculés.
     *
     *    Cas de base: Le pompier ne peut aller ni à droite ni a gauche :
     *                 Dans ce cas on retourne la valeur la case sauf si c'est -1 on retourne 0
     *    Cas Récursif:
     *               Si le pompier peut se déplacer uniquement en horizontal
     *                 Dans ce cas il se déplace en horizontal + appel récursif de la méthode
     *               Si le pompier peut se déplacer uniquement vers le bas
     *                 Dans ce cas il se déplace vers le bas + appelle récursif de la méthode
     *               Si le pompier peut se déplacer soit en horizontal ou en bas :
     *                 Dans ce cas on calcule les 2 directions et on prend le maximum de deux et on
     *                 rappelle la méthode de manière récursive.
     *
     * @param  posX  Position du pompier sur l'axe Horizontal
     *         posY Position du pompier sur l'axe Vertical
     *         building c'est un tableau à deux dimensions qui représente le building que le pompier doit parcourir
     *         buildingSave c'est un tableau qui contient déjà les chemins calculés
     * @return  un entier qui est le nombre de personnes sauver. 0 >= personne sauver > maxInt(en Java)
     *
     */
    private int savePeople(int posX, int posY, int[][] building, int[][] buildingSave) {
        // Je regarde dans le tableau buildingSave si la case a déjà été calculée ou non ?
        if (buildingSave[posX][posY] != -1) return buildingSave[posX][posY];

        // BASE Case: We can not move. We can not go to right/left or down
        if (testFin(posX, posY, building) || building[posX][posY]==-1) {
            return (building[posX][posY] == -1 || !rightDirection (posX, building.length)) ? 0 : building[posX][posY];
        }
        // Case: We can ONLY move horizontally
        else if ((isMoveHorizontalPossible(posX, posY, building)) && (!isDownMovePossible(posX, posY, building))) {
            int ancPosY = posY;
            posY = moveHorizontal(posX, posY, building);
            return (building[posX][ancPosY] == -1 ? 0 : building[posX][ancPosY]) + savePeople(posX, posY, building, buildingSave);
            // Case: We can ONLY move down
        } else if ((isDownMovePossible(posX, posY, building)) && (!isMoveHorizontalPossible(posX, posY, building))) {
            int ancPosX = posX;
            posX = moveGoesDown(posX, posY, building);
            return (building[ancPosX][posY] == -1 ? 0 : building[ancPosX][posY]) + savePeople(posX, posY, building, buildingSave);
        }

        int horizontalSave = 0;
        int downSave = 0;
        int oldPosX = posX;
        int oldPosY = posY;

        if (posY < building[0].length) {
            int backupPosY = posY;
            posY = moveHorizontal(posX, posY, building);
            horizontalSave = savePeople(posX, posY, building, buildingSave);
            posY = backupPosY;
        }

        if (posX < building.length) {
            int backupPosY = posX;
            posX = moveGoesDown(posX, posY, building);
            downSave = savePeople(posX, posY, building, buildingSave);
            posX = backupPosY;
        }

        if (horizontalSave > downSave) {
            posY = moveHorizontal(posX, posY, building);
            buildingSave[posX][posY] = horizontalSave;
        } else {
            posX = moveGoesDown(posX, posY, building);
            buildingSave[posX][posY] = downSave;
        }

        return (building[oldPosX][oldPosY] == -1 ? 0 : building[oldPosX][oldPosY]) + savePeople(posX, posY, building, buildingSave);
    }


    /**
     * Méthode pour savoir si le pompier est bloqué. Si le pompier est bloqué la méthode renvoie true ou sinon false
     *
     * @param  posX Position du pompier sur l'axe Horizontal
     *         posY Position du pompier sur l'axe Vertical
     *         building c'est un tableau à deux dimensions qui représente le building que le pompier doit parcourir
     * @return un boolean qui indique true si le pompier est bloqué ou false si le pompier n'est pas bloqué
     *
     */
    private boolean testFin(int posX, int posY, int[][] building) {
        boolean rightDirection = rightDirection( posX, building.length);
        return (((rightDirection) && (isRightMovePossible(posX, posY, building)))) ||
                ((!rightDirection) && (isLeftMovePossible(posX, posY, building))) ||
                isDownMovePossible(posX, posY, building) && (posX < building.length) ? false : true;
    }

    /**
     * Méthode pour savoir si le pompier peut se déplacer vers la droite.
     *         la méthode renvoie true si le pompier peut se déplacer vers la droite
     *                                 ou sinon false si c'est vers la gauche
     *
     * @param  posX Position du pompier sur l'axe Horizontal
     *         totalLine Nombre de ligne total du building
     *
     * @return un boolean qui indique true si le pompier peut se déplacer vers la droite
     *                             ou false si le pompier peut se déplacer que vers la gauche
     *
     */
    private boolean rightDirection(int posX, int totalLine) {
        int floor = totalLine - 1 - posX;
        return floor % 2 == 0;
    }

    /**
     * Méthode pour retourner la nouvelle position du pompier vers le bas si c'est possible
     *                                    ou sinon la valeur retournée est la même que posX en entrée
     *
     * @param  posX Position du pompier sur l'axe Horizontal
     *         posY Position du pompier sur l'axe Vertical
     *         building c'est un tableau à deux dimensions qui représente le building que le pompier doit parcourir
     *
     * @return un int qui indique la nouvelle position du pompier (en X).
     *         si la valeur retournée = posX en entrée alors la position du pompier n'a pas changé.
     *
     */
    private int moveGoesDown(int posX, int posY, int[][] building) {
        return isDownMovePossible(posX, posY, building) ? posX + 1 : posX;
    }

    /**
     * Méthode pour retourner la nouvelle position du pompier en horizontal si c'est possible
     *                                    ou sinon la valeur retournée est la même que posY en entrée
     *
     * @param  posX Position du pompier sur l'axe Horizontal
     *         posY Position du pompier sur l'axe Vertical
     *         building c'est un tableau à deux dimensions qui représente le building que le pompier doit parcourir
     *
     * @return un int qui indique la nouvelle position du pompier (en Y).
     *         si la valeur retournée = posY en entrée alors la position du pompier n'a pas changé.
     *
     */
    private int moveHorizontal(int posX, int posY, int[][] building) {
        boolean rightDirection = rightDirection( posX, building.length);
        posY = ((rightDirection) && (isRightMovePossible(posX, posY, building))) ? posY + 1 : posY;
        posY = ((!rightDirection) && (isLeftMovePossible(posX, posY, building))) ? posY - 1 : posY;
        return posY;
    }

    /**
     * Méthode pour savoir si le pompier peut se déplacer en horizontal
     *
     * @param  posX Position du pompier sur l'axe Horizontal
     *         posY Position du pompier sur l'axe Vertical
     *         building c'est un tableau à deux dimensions qui représente le building que le pompier doit parcourir
     *
     * @return un boolean si true alors le pompier peut se déplacer en horizontal
     *                    sinon alors le pompier ne peut pas se déplacer en horizontal
     *
     */
    private boolean isMoveHorizontalPossible(int posX, int posY, int[][] building) {
        boolean rightDirection = rightDirection( posX, building.length);
        return ((rightDirection) && (isRightMovePossible(posX, posY, building))) ||
                ((!rightDirection) && (isLeftMovePossible(posX, posY, building))) ? true : false;
    }

    /**
     * Méthode pour savoir si le pompier peut encore se déplacer à droite
     *
     * @param  posX Position du pompier sur l'axe Horizontal
     *         posY Position du pompier sur l'axe Vertical
     *         building c'est un tableau à deux dimensions qui représente le building que le pompier doit parcourir
     *
     * @return un boolean si true alors le pompier peut encore se déplacer à droite
     *                    sinon alors le pompier ne peut plus se déplacer vers la droite
     *
     */
    private boolean isRightMovePossible(int posX, int posY, int[][] building) {
        return (posY < (building[posX].length - 1)) && (building[posX][posY + 1] != -1) ? true : false;
    }

    /**
     * Méthode pour savoir si le pompier peut encore se déplacer à gauche
     *
     * @param  posX Position du pompier sur l'axe Horizontal
     *         posY Position du pompier sur l'axe Vertical
     *         building c'est un tableau à deux dimensions qui représente le building que le pompier doit parcourir
     *
     * @return un boolean si true alors le pompier peut encore se déplacer à gauche
     *                    sinon alors le pompier ne peut plus se déplacer vers la gauche
     *
     */
    private boolean isLeftMovePossible(int posX, int posY, int[][] building) {
        return (posY > 0) && (building[posX][posY - 1] != -1) ? true : false;
    }

    /**
     * Méthode pour savoir si le pompier peut encore se déplacer vers le bas
     *
     * @param  posX Position du pompier sur l'axe Horizontal
     *         posY Position du pompier sur l'axe Vertical
     *         building c'est un tableau à deux dimensions qui représente le building que le pompier doit parcourir
     *
     * @return un boolean si true alors le pompier peut encore se déplacer vers le bas
     *                    sinon alors le pompier ne peut plus se déplacer vers la bas
     *
     */
    private boolean isDownMovePossible(int posX, int posY, int[][] building) {
        return (posX < (building.length - 1)) && (building[posX + 1][posY] != -1) ? true : false;
    }

}
