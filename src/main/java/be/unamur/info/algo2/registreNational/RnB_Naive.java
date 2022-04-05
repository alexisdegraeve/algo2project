package be.unamur.info.algo2.registreNational;
 /**
 * @Overview
 * Divide and Conquer: Le Registre National Belge version naive
 * But : Le programme doit analyser un tableau de nom et doit en ressortir soit:
 *              -  Un nom "courant" (un nom qui est représenté plus de fois que la moitié de la taille du tableau)
 *              - null (si aucun nom n'est un nom courant
 *
 * @author  Christophe HERION
 * @since   2020-12-14
 * @link    https://github.com/UNamurCSFaculty/2021_IHDCB331_G09
 *
 **/





public class RnB_Naive {


    public RnB_Naive() {}

    public String[] readFile(String fileName) {
            String[] nomsCourant = null;

            try {
                String[] lignes = fileName.split("\r\n|\n"); // enter

                if(lignes.length == 0){
                    return null;
                }

                int nblignes = Integer.parseInt(lignes[0]);

                if(lignes.length < (nblignes * 2)+1){
                    return null;
                }



                if(nblignes <= 0) {
                    return null;
                }
                else {
                    nomsCourant = new String[nblignes];
                }



                int i = 0;
                int j = 0;

                while (i <= (lignes.length-1)) {
                    i++;
                    int nbmot = Integer.parseInt(lignes[i]);
                    if(nbmot <=0){
                        return null;
                    }

                    //Recupérer le tableau dans mots
                    i++;


                        String[] mots = lignes[i].split("\\s+"); // espace

                    if(nbmot != mots.length){
                        throw new NullPointerException();
                    }

                    String motsortie = prenomCourantNaif(mots, nbmot, mots[0], 0);
                    nomsCourant[j] = motsortie;



                    j++;

                }
            } catch(NullPointerException e) {
                return null;
            } catch (final NumberFormatException e) {
                return null;
            } catch (Exception e) {
                e.printStackTrace();
            }


        return nomsCourant;
        }


    public static String prenomCourantNaif(String[] tab, int i, String toCompare, int compteurMax){


        // String[] tab est le tableau de string reprenant les noms à tester
        // int i représente la taille du tableau, on va décrémenter i à chaque appel récursif pour analyser des sous-tableaux
        // compteur max permet de retenir l'occurence maximale que l'on retrouve dans le tableau


        String toCompareJ = new String();               // String à comparer avec toCompare
        int compteur = 0;                               // compteur pour comparer le nombre d'occurence actuel et le plus grand nombre d'occurence

        // Le cas de base
        if (i <= 0) {
            return null;
        }
        else {
            for (int j = tab.length-1; j >= 0 ; j--){                       // Boucle permettant de comparer le String actuel (toCompare) avec toutes les valeurs du tableau et qui seront stockées successivement dans toCompareJ
                toCompareJ = tab[j];                                        // Stocke succesivelent chaque valeur du tableau


                if(toCompareJ.equals(toCompare)){                           // Si les deux strings sont égaux => on incrémente compteur actuel
                    compteur ++;
                    if(compteur > compteurMax){                             // Si le compteur actuel est plus grand que le compteur max => on met à jour compteurMax
                        compteurMax = compteur;
                        if(compteurMax > tab.length/2){                     // Si le compteur max est strictement plus grand que la moitié de la taille du tableau => on retourne l'élément courant
                            return toCompare;
                        }
                    }
                }
            }
        }
        return prenomCourantNaif(tab, i-1, tab[i-1], compteurMax);                    // Appel recursif à la fonction RnB
    }
}



