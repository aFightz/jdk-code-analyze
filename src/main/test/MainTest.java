import conllection.HashMapAnalyze;

import java.util.HashMap;
import java.util.Map;

public class MainTest {

    public static void main(String[] args) {
        Map<Integer , Integer> map = new HashMapAnalyze();
        map.put(1 + (0 << 4),1);
        map.put(1 + (1 << 4) , 2);

        System.out.println(map.get(1));
//        System.out.println(map.get(17));
    }
}
