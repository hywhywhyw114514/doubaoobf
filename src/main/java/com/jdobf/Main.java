package com.jdobf;

import com.jdobf.gui.MainFrame;

/**
 * 混淆器入口（图形界面）。
 */
public final class Main {

    private Main() {
    }

    public static void main(String[] args) {
        // 部分 Windows 环境下 D3D 加速管线会导致 Swing 窗口内容白屏不渲染，
        // 仅在用户未显式指定时关闭它（必须在 AWT 初始化前设置）。
        if (System.getProperty("sun.java2d.d3d") == null) {
            System.setProperty("sun.java2d.d3d", "false");
        }
        if (System.getProperty("sun.java2d.noddraw") == null) {
            System.setProperty("sun.java2d.noddraw", "true");
        }
        MainFrame.launch();
    }
}
