package be.unamur.info.algo2.registreNational;

/**
 *
 * Divide and Conquer: Le Registre National Belge version optimale
 * But : Le programme doit analyser un tableau de nom et doit en ressortir soit:
 *              -  Un nom "courant" (un nom qui est représenté plus de fois que la moitié de la taille du tableau)
 *              - null (si aucun nom n'est un nom courant
 *
 * @author  Christophe HERION
 * @since   2020-12-14
 * @link    https://github.com/UNamurCSFaculty/2021_IHDCB331_G09
 *
 **/

public class RegistreNationalBelge_DivideAndConquer {

    public RegistreNationalBelge_DivideAndConquer() {}

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

            if(nblignes > 0) {
                nomsCourant = new String[nblignes];
            }



            int i = 0;
            int j = 0;

            while (i <= (lignes.length-1)) {
                i++;
                int nbmot = Integer.parseInt(lignes[i]);
                if (nbmot <= 0) {
                    throw new NullPointerException();
                }


                //Recupérer le tableau dans mots
                i++;
                String[] mots = lignes[i].split("\\s+"); // espace

                if(nbmot != mots.length){
                    throw new NullPointerException();
                }

                //    public static String AnalyseMots(String[] tab, int i, String toCompare, int compteurMax)
                String motsortie = RnB_Rec(mots);
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

    public static String RnB_Rec(String[] tab){

        String prenomCourant = divide(tab, 0, tab.length-1);

        return prenomCourant;

    }

    public static String divide(String[] tab, int debut, int fin){

        String gauche;
        String droite;
        int centre = (debut + fin)/2;          // (sub)table
        int occGauche = 0;             //occurence of the "left" name in a (sub)table
        int occDroite = 0;            //occurence of the "right" name in a(sub)table


        // Cas de base
        if (debut == fin){
            return tab[debut];
        }
        else{
            gauche = divide(tab, debut, centre);                     // Recherche du mot le plus fréquent dans la partie gauche du tableau (ou null)
            droite = divide(tab,centre +1,fin);               // Recherche du mot le plus fréquent dans la partie droite du tableau (ou null)
            if (gauche != null){
                occGauche = conquer(gauche, tab, debut, fin);       //Si un nom fréquent a été trouvé dans la partie gauche du (sous)tableau, on compte son nombre d'occurence dans le (sous)tableau
            }
            if (droite != null){
                occDroite = conquer(droite, tab, debut, fin);       //Si un nom fréquent a été trouvé dans la partie droite du (sous)tableau, on compte son nombre d'occurence dans le (sous)tableau//if a most frequent name has been found in the right subtable, count it's occurence in the current table
            }
        }
        if (occGauche > (fin-debut+1)/2){                           //Si le nombre d'occurence du nom dans le (sous)tableau de gauche est > à la moitié du (sous)tableau, on retourne ce nom
            return gauche;
        }
        else{
            if (occDroite > (fin-debut+1)/2){                       //Si le nombre d'occurence du nom dans le (sous)tableau de droite est > à la moitié du (sous)tableau, on retourne ce nom
                return droite;
            }
            else{
                return null;                                        //Sinon, il n'y a aucun nom fréquent => on retourne null
            }
        }
    }




    private static int conquer(String nom , String[] tab, int debut, int fin){

        /*
            Compte le nombre d'occurence d'un nom dans un (sous)tableau
         */
        int compteur = 0;
        for (int i =  debut; i <= fin; i++){
            if(nom.equals(tab[i])){
                compteur++;
            }
        }
        return compteur;
    }
}


