package p;

/**
 * 控制流重型样例：覆盖平坦化必须正确处理的全部典型结构，
 * 以及必须安全跳过的结构（try-catch / 源码 switch / synchronized / 构造器）。
 */
public class FlowHeavy {

    private final int seed;

    public FlowHeavy(int seed) {
        this.seed = seed;
    }

    // 嵌套循环 + continue + 标记 break（向后/向前后向边混合）
    public int nested(int n) {
        int sum = 0;
        outer:
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                if (i == j) {
                    continue;
                }
                if (i + j > 10) {
                    break outer;
                }
                sum += i * j;
            }
        }
        return sum + seed;
    }

    // while + 提前 return
    public static int gcd(int a, int b) {
        a = Math.abs(a);
        b = Math.abs(b);
        while (b != 0) {
            int t = a % b;
            a = b;
            b = t;
        }
        return a;
    }

    // do-while + 提前 return
    public static int firstNegative(int[] xs) {
        int i = 0;
        do {
            if (i >= xs.length) {
                return -1;
            }
            i++;
        } while (xs[i - 1] >= 0);
        return i - 1;
    }

    // 短路 && || + 三目
    public static String classify(int x) {
        String s = ((x > 0 && x < 100) || x == -1) ? "in" : "out";
        if (x % 2 == 0) {
            s = s + "-even";
        } else {
            s = s + "-odd";
        }
        return s;
    }

    // long/double 双槽位局部变量与运算
    public static double sumSqrt(int n) {
        double acc = 0;
        for (long i = 1; i <= n; i++) {
            acc += 1.0 / (i * i);
        }
        return acc;
    }

    // 递归
    public static int fib(int n) {
        if (n < 2) {
            return n;
        }
        return fib(n - 1) + fib(n - 2);
    }

    // try-catch：含异常表，必须跳过平坦化
    public static int safeDiv(int a, int b) {
        try {
            return a / b;
        } catch (ArithmeticException e) {
            return -999;
        }
    }

    // 源码 int switch：TABLESWITCH，必须跳过
    public static int sw(int x) {
        switch (x) {
            case 1:
                return 10;
            case 2:
                return 20;
            case 3:
                return 30;
            default:
                return 0;
        }
    }

    // 源码 String switch：LOOKUPSWITCH，必须跳过
    public static int sws(String s) {
        switch (s) {
            case "a":
                return 1;
            case "bb":
                return 2;
            default:
                return -1;
        }
    }

    // synchronized 块（带隐式异常表），必须跳过
    public static long counter(int n) {
        long c = 0;
        synchronized (FlowHeavy.class) {
            for (int i = 0; i < n; i++) {
                c += i;
            }
        }
        return c;
    }

    // 实例方法：this + 循环 + 分支
    public String report(int n) {
        StringBuilder sb = new StringBuilder();
        int k = 0;
        while (k < n) {
            if (k % 2 == 0) {
                sb.append('e');
            } else {
                sb.append('o');
            }
            k++;
        }
        return sb.toString();
    }

    // 无限循环 + break
    public static int countdown(int x) {
        int v = x;
        while (true) {
            if (v <= 0) {
                break;
            }
            v -= 3;
        }
        return v;
    }
}
