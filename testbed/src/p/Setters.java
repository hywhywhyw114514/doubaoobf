package p;

/**
 * 模拟截图样本：一个方法里连续 new 对象 + setTitle/setSize/
 * setVisible/setDefaultCloseOperation，参数来自运行期计算
 * （字符串拼接、int 运算、boolean 分支）。语句级平坦化后这些
 * 核心操作应分散到多个 case，且状态由真实参数值喂养。
 */
public class Setters {

    public static class Box {
        String title;
        int w;
        int h;
        int op;
        boolean vis;

        public void setTitle(String s) {
            this.title = s;
        }

        public void setSize(int width, int height) {
            this.w = width;
            this.h = height;
        }

        public void setVisible(boolean v) {
            this.vis = v;
        }

        public void setDefaultCloseOperation(int x) {
            this.op = x;
        }
    }

    public static String build(String prefix, int scale) {
        Box b = new Box();
        // 循环制造跳转，标题字符串运行期拼接（字符串加密后为解密产物）
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < 2; i++) {
            sb.append(prefix);
        }
        sb.append("-win");
        String t = sb.toString();
        b.setTitle(t);
        int width = scale * 3;
        int height = scale * 4;
        b.setSize(width, height);
        boolean visible;
        if (scale > 0) {
            visible = true;
        } else {
            visible = false;
        }
        b.setVisible(visible);
        b.setDefaultCloseOperation(scale & 7);
        return t + "|" + b.w + "," + b.h + "|" + b.vis + "|" + b.op;
    }
}
