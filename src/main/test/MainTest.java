import conllection.ArrayListAnalyze;
import conllection.HashMapAnalyze;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class MainTest {

    public static void main(String[] args) {
//        Map<Integer , Integer> map = new HashMapAnalyze();
//        map.put(1 + (0 << 4),1);
//        map.put(1 + (1 << 4) , 2);
//
//        System.out.println(map.get(1));
//        System.out.println(map.get(17));


//        for(int i = 0 ; i < 9 ; i++){
//            System.out.println(8 & i);
//        }

        List<Integer> list = new ArrayListAnalyze<>();
        list.add(1);
        list.add(1);
        list.add(1);
        list.add(1);
        list.add(1);
        list.add(1);
        list.add(1);
        list.add(1);
        list.add(1);
        list.add(1);
        list.add(1);
        System.out.println(list.size());
        System.out.println(list.get(0));

    }
}
