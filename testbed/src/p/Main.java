package p;

import java.util.ArrayList;
import java.util.List;

public class Main {

    public static void main(String[] args) {
        FlowHeavy h = new FlowHeavy(100);
        System.out.println("NEST:" + h.nested(6));
        System.out.println("GCD:" + FlowHeavy.gcd(48, 36));
        System.out.println("FN1:" + FlowHeavy.firstNegative(new int[]{3, 2, -5, 1}));
        System.out.println("FN2:" + FlowHeavy.firstNegative(new int[]{3, 2, 1}));
        System.out.println("C1:" + FlowHeavy.classify(50));
        System.out.println("C2:" + FlowHeavy.classify(200));
        System.out.println("C3:" + FlowHeavy.classify(-1));
        System.out.printf("SQ:%.6f%n", FlowHeavy.sumSqrt(100));
        System.out.println("FIB:" + FlowHeavy.fib(15));
        System.out.println("DIV1:" + FlowHeavy.safeDiv(10, 2));
        System.out.println("DIV0:" + FlowHeavy.safeDiv(10, 0));
        System.out.println("SW:" + FlowHeavy.sw(2) + "," + FlowHeavy.sw(9));
        System.out.println("SWS:" + FlowHeavy.sws("bb") + "," + FlowHeavy.sws("zzz"));
        System.out.println("CNT:" + FlowHeavy.counter(1001));
        System.out.println("RPT:" + h.report(7));
        System.out.println("CD:" + FlowHeavy.countdown(20));

        // lambda（lambda$ 私有合成方法含循环/分支，是平坦化目标）
        int[] acc = {0};
        Runnable r = () -> {
            for (int i = 0; i < 10; i++) {
                if (i % 2 == 0) {
                    acc[0] += i;
                }
            }
        };
        r.run();
        System.out.println("LAMBDA:" + acc[0]);

        // 匿名内部类实现接口，方法内含循环
        Calc c = new Calc() {
            @Override
            public int run(int a, int b) {
                int s = 0;
                for (int i = a; i < b; i++) {
                    if ((i & 1) == 0) {
                        s += i;
                    }
                }
                return s;
            }
        };
        System.out.println("ANON:" + c.run(1, 10));

        // 枚举遍历（values/valueOf 需保护）
        StringBuilder sb = new StringBuilder("ENUM:");
        for (Color x : Color.values()) {
            sb.append(x.name()).append('=').append(x.code()).append(' ');
        }
        System.out.println(sb.toString().trim());
        System.out.println("VOF:" + Color.valueOf("BLUE").code());

        // for-each 集合
        List<String> list = new ArrayList<String>();
        list.add("aa");
        list.add("bb");
        list.add("cc");
        StringBuilder join = new StringBuilder("LIST:");
        for (String s : list) {
            join.append(s).append('-');
        }
        System.out.println(join.toString());

        // setter 链：语句级切碎 + 业务数据密钥化状态的目标场景
        System.out.println("WIN:" + Setters.build("db", 100));
        System.out.println("WIN:" + Setters.build("z", 0));

        System.out.println("ALL_OK");
    }
}
