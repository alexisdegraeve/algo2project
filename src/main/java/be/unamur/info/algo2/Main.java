package be.unamur.info.algo2;

import be.unamur.info.algo2.firefighter.FireFighterDynamic;
import be.unamur.info.algo2.firefighter.FireFighterNaive;
import be.unamur.info.algo2.freyr.FreyrSeries;
import be.unamur.info.algo2.registreNational.RegistreNationalBelge_DivideAndConquer;
import be.unamur.info.algo2.registreNational.RnB_Naive;
import lombok.extern.slf4j.Slf4j;

@Slf4j
public class Main {

    public static String[] problem_1_naive(String s_file) {
        System.out.println("===");
        System.out.println(s_file);
        System.out.println("===");
        RnB_Naive rnbNaive =  new RnB_Naive();
        String[] s_tmp = rnbNaive.readFile(s_file); // {"Peeters", "Goossens", null, "Leclercq"};
        // String[] s_tmp = null;
        return s_tmp;
    }


    public static String[] problem_1(String s_file) {
        System.out.println("===");
        System.out.println(s_file);
        System.out.println("===");
        RegistreNationalBelge_DivideAndConquer rnbRec =  new RegistreNationalBelge_DivideAndConquer();
        String[] s_tmp = rnbRec.readFile(s_file); // {"Peeters", "Goossens", null, "Leclercq"};
        // String[] s_tmp = null;
        return s_tmp;
    }

    public static String[] problem_2_naive(String s_file) {
        System.out.println("====");
        System.out.println(s_file);
        System.out.println("====");
        String[] s_tmp = new FireFighterNaive(s_file).rescueAllBuildings();
        return s_tmp;
    }

    public static String[] problem_2(String s_file) {
        System.out.println("====");
        System.out.println(s_file);
        System.out.println("====");
        String[] s_tmp = new FireFighterDynamic(s_file).rescueAllBuildings();
        return s_tmp;
    }

    public static String[] problem_3_naive(String s_file) {
        System.out.println("===");
        System.out.println(s_file);
        System.out.println("===");
        try {
            return new FreyrSeries(s_file).getSimpleResults();
        } catch (RuntimeException e) {
            log.error("Failed to parse file", e);
            return null;
        }
    }
    
    public static String[] problem_3(String s_file) {
        System.out.println("===");
        System.out.println(s_file);
        System.out.println("===");
        try {
            return new FreyrSeries(s_file).getComplexResults();
        } catch (RuntimeException e) {
            log.error("Failed to parse file", e);
            return null;
        }
    }
}
