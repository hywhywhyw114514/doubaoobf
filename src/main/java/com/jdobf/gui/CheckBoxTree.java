package com.jdobf.gui;

import javax.swing.JComponent;
import javax.swing.JTree;
import javax.swing.event.MouseInputAdapter;
import javax.swing.tree.DefaultTreeCellRenderer;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreeNode;
import javax.swing.tree.TreePath;
import javax.swing.tree.TreeSelectionModel;
import java.awt.BorderLayout;
import java.awt.Component;
import java.awt.event.MouseEvent;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.List;

/**
 * 带三态复选框的树：目录支持“全选 / 部分选中 / 未选”。
 */
public class CheckBoxTree extends JTree {

    public static final int KIND_ROOT = 0;
    public static final int KIND_DIR = 1;
    public static final int KIND_CLASS = 2;
    public static final int KIND_RESOURCE = 3;

    /** null 表示半选 */
    public static final class Node extends javax.swing.tree.DefaultMutableTreeNode {
        public final String title;
        public final String path;
        public final int kind;
        public Boolean selected = Boolean.FALSE;

        Node(String title, String path, int kind) {
            this.title = title;
            this.path = path;
            this.kind = kind;
            setUserObject(title);
        }

        @SuppressWarnings({"unchecked", "rawtypes"})
        public List<Node> kids() {
            // DefaultMutableTreeNode 在插入过子节点前 children 为 null
            if (children == null) {
                return java.util.Collections.emptyList();
            }
            return (List) children;
        }
    }

    private final Node rootNode;

    public CheckBoxTree() {
        rootNode = new Node("(jar)", "", KIND_ROOT);
        setModel(new DefaultTreeModel(rootNode));
        setRootVisible(true);
        setShowsRootHandles(true);
        setToggleClickCount(0);
        getSelectionModel().setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION);
        setCellRenderer(new CheckRenderer());
        // 键盘支持：空格切换当前选中行节点的勾选状态
        javax.swing.Action toggleAction = new javax.swing.AbstractAction() {
            @Override
            public void actionPerformed(java.awt.event.ActionEvent e) {
                TreePath tp = getSelectionPath();
                if (tp != null && tp.getLastPathComponent() instanceof Node) {
                    Node n = (Node) tp.getLastPathComponent();
                    if (n.kind != KIND_RESOURCE) {
                        toggle(n);
                    }
                }
            }
        };
        getInputMap(javax.swing.JComponent.WHEN_FOCUSED)
                .put(javax.swing.KeyStroke.getKeyStroke(java.awt.event.KeyEvent.VK_SPACE, 0), "toggleCheck");
        getActionMap().put("toggleCheck", toggleAction);
        addMouseListener(new MouseInputAdapter() {
            @Override
            public void mousePressed(MouseEvent e) {
                if (e.getButton() != MouseEvent.BUTTON1) {
                    return;
                }
                int row = getRowForLocation(e.getX(), e.getY());
                if (row < 0) {
                    return;
                }
                TreePath tp = getPathForRow(row);
                Object last = tp.getLastPathComponent();
                if (last instanceof Node) {
                    Node n = (Node) last;
                    if (n.kind != KIND_RESOURCE) {
                        toggle(n);
                    }
                }
            }
        });
    }

    public Node root() {
        return rootNode;
    }

    /** 用 (path, kind) 列表重建整棵树 */
    public void rebuild(List<PathEntry> entries) {
        rootNode.removeAllChildren();
        for (PathEntry e : entries) {
            // JAR 中自带的目录条目（以 "/" 结尾）只是占位，不作为叶子节点；
            // 否则目录会先以“资源叶子”身份建节点，随后被真正的包节点复用，
            // 导致整个目录被误判为不可勾选的资源。
            if (e.path.endsWith("/")) {
                continue;
            }
            String[] parts = splitPath(e.path);
            Node parent = rootNode;
            StringBuilder current = new StringBuilder();
            for (int i = 0; i < parts.length; i++) {
                boolean leaf = i == parts.length - 1;
                if (i > 0) {
                    current.append('/');
                }
                current.append(parts[i]);
                String fullPath = current.toString();
                int kind;
                if (leaf) {
                    kind = e.isClass ? KIND_CLASS : KIND_RESOURCE;
                } else {
                    kind = KIND_DIR;
                }
                Node next = findChild(parent, fullPath);
                if (next == null) {
                    next = new Node(parts[i], leaf ? fullPath : fullPath + "/", kind);
                    insertSorted(parent, next);
                }
                parent = next;
            }
        }
        ((DefaultTreeModel) getModel()).reload();
        expandAll();
    }

    private static String[] splitPath(String path) {
        List<String> parts = new ArrayList<String>();
        for (String p : path.split("/")) {
            if (!p.isEmpty()) {
                parts.add(p);
            }
        }
        return parts.toArray(new String[0]);
    }

    private Node findChild(Node parent, String path) {
        for (Node c : parent.kids()) {
            if (c.path.equals(path) || c.path.equals(path + "/")) {
                return c;
            }
        }
        return null;
    }

    private void insertSorted(Node parent, Node child) {
        int insert = 0;
        List<Node> kids = parent.kids();
        for (int i = 0; i < kids.size(); i++) {
            Node c = kids.get(i);
            boolean cDir = c.kind == KIND_DIR || c.kind == KIND_ROOT;
            boolean nDir = child.kind == KIND_DIR;
            if (cDir == nDir) {
                if (c.title.compareToIgnoreCase(child.title) > 0) {
                    insert = i;
                    break;
                }
                insert = i + 1;
            } else if (cDir) {
                insert = i + 1;
            } else {
                insert = i;
                break;
            }
        }
        parent.insert(child, insert);
    }

    public void expandAll() {
        for (int i = 0; i < getRowCount(); i++) {
            expandRow(i);
        }
    }

    private void toggle(Node n) {
        boolean newState = !Boolean.TRUE.equals(n.selected);
        setSubtree(n, newState);
        // 逐级刷新祖先
        TreeNode p = n.getParent();
        while (p instanceof Node && p != rootNode) {
            refreshParentState((Node) p);
            p = p.getParent();
        }
        ((DefaultTreeModel) getModel()).reload();
        expandAll();
    }

    private void setSubtree(Node n, boolean selected) {
        if (n.kind != KIND_RESOURCE) {
            n.selected = selected;
        }
        for (Node c : n.kids()) {
            setSubtree(c, selected);
        }
    }

    private void refreshParentState(Node n) {
        boolean hasTrue = false;
        boolean hasFalse = false;
        for (Node c : n.kids()) {
            if (c.kind == KIND_RESOURCE) {
                continue;
            }
            if (Boolean.TRUE.equals(c.selected)) {
                hasTrue = true;
            } else {
                hasFalse = true; // false 或半选都算“不全选”
            }
        }
        if (hasTrue && !hasFalse) {
            n.selected = Boolean.TRUE;
        } else if (!hasTrue) {
            n.selected = Boolean.FALSE;
        } else {
            n.selected = null;
        }
    }

    /** 收集排除项：类内部名列表 + 目录前缀（以 / 结尾） */
    public Exclusion collectExclusions() {
        List<String> classes = new ArrayList<String>();
        List<String> packages = new ArrayList<String>();
        for (Node c : rootNode.kids()) {
            collect(c, classes, packages);
        }
        return new Exclusion(classes, packages);
    }

    private void collect(Node n, List<String> classes, List<String> packages) {
        if (n.kind == KIND_CLASS && Boolean.TRUE.equals(n.selected)) {
            classes.add(n.path);
            return;
        }
        if (n.kind == KIND_DIR) {
            if (Boolean.TRUE.equals(n.selected)) {
                packages.add(n.path);
                return;
            }
            for (Node c : n.kids()) {
                collect(c, classes, packages);
            }
        }
    }

    /** 按已有选择恢复勾选（重建树后调用） */
    public void restore(List<String> cls, List<String> pkgs) {
        restoreFrom(rootNode, cls, pkgs);
        Enumeration<TreeNode> e = rootNode.depthFirstEnumeration();
        while (e.hasMoreElements()) {
            TreeNode t = e.nextElement();
            if (t instanceof Node && t != rootNode) {
                TreeNode p = t.getParent();
                if (p instanceof Node) {
                    refreshParentState((Node) p);
                }
            }
        }
        ((DefaultTreeModel) getModel()).reload();
        expandAll();
    }

    private void restoreFrom(Node n, List<String> cls, List<String> pkgs) {
        for (Node c : n.kids()) {
            if (c.kind == KIND_CLASS && cls.contains(c.path)) {
                c.selected = Boolean.TRUE;
            } else if (c.kind == KIND_DIR && pkgs.contains(c.path)) {
                setSubtree(c, true);
            } else {
                restoreFrom(c, cls, pkgs);
            }
        }
    }

    public static final class PathEntry {
        public final String path;
        public final boolean isClass;

        public PathEntry(String path, boolean isClass) {
            this.path = path;
            this.isClass = isClass;
        }
    }

    public static final class Exclusion {
        public final List<String> classes;
        public final List<String> packages;

        public Exclusion(List<String> classes, List<String> packages) {
            this.classes = classes;
            this.packages = packages;
        }
    }

    /** 复选框渲染器：自绘三态方框 + 文本 */
    private static final class CheckRenderer extends DefaultTreeCellRenderer {
        private final TriBox box = new TriBox();
        private final javax.swing.JLabel label = new javax.swing.JLabel();
        private final javax.swing.JPanel panel = new javax.swing.JPanel(
                new java.awt.FlowLayout(java.awt.FlowLayout.LEFT, 4, 1));

        CheckRenderer() {
            panel.setOpaque(false);
            label.setOpaque(false);
            panel.add(box);
            panel.add(label);
        }

        @Override
        public Component getTreeCellRendererComponent(JTree tree, Object value, boolean sel,
                                                      boolean expanded, boolean leaf, int row,
                                                      boolean hasFocus) {
            super.getTreeCellRendererComponent(tree, value, sel, expanded, leaf, row, false);
            if (value instanceof Node) {
                Node n = (Node) value;
                label.setText(n.title);
                label.setForeground(n.kind == KIND_RESOURCE
                        ? java.awt.Color.GRAY : tree.getForeground());
                box.state = n.kind == KIND_RESOURCE ? Boolean.FALSE : n.selected;
                box.setEnabled(n.kind != KIND_RESOURCE);
                return panel;
            }
            return this;
        }
    }

    /** 三态复选框图形：未选 / 勾选 / 半选（横线），圆角抗锯齿 */
    private static final class TriBox extends JComponent {
        Boolean state = Boolean.FALSE;

        TriBox() {
            setPreferredSize(new java.awt.Dimension(15, 15));
        }

        @Override
        protected void paintComponent(java.awt.Graphics g) {
            java.awt.Graphics2D g2 = (java.awt.Graphics2D) g.create();
            g2.setRenderingHint(java.awt.RenderingHints.KEY_ANTIALIASING,
                    java.awt.RenderingHints.VALUE_ANTIALIAS_ON);
            g2.setRenderingHint(java.awt.RenderingHints.KEY_STROKE_CONTROL,
                    java.awt.RenderingHints.VALUE_STROKE_PURE);
            int s = 13;
            int x = 1, y = 1;
            boolean selected = Boolean.TRUE.equals(state);
            boolean partial = state == null;
            if (selected || partial) {
                g2.setColor(partial ? new java.awt.Color(0x9DB7E8) : new java.awt.Color(0x3B6FD4));
                g2.fillRoundRect(x, y, s, s, 5, 5);
                g2.setColor(new java.awt.Color(0x3B6FD4));
                g2.drawRoundRect(x, y, s, s, 5, 5);
                g2.setColor(java.awt.Color.WHITE);
                g2.setStroke(new java.awt.BasicStroke(1.7f, java.awt.BasicStroke.CAP_ROUND,
                        java.awt.BasicStroke.JOIN_ROUND));
                if (selected) {
                    java.awt.geom.Path2D p = new java.awt.geom.Path2D.Float();
                    p.moveTo(x + 3.2, y + 6.8);
                    p.lineTo(x + 5.6, y + 9.2);
                    p.lineTo(x + 10, y + 4.2);
                    g2.draw(p);
                } else {
                    g2.fillRoundRect(x + 3, y + 5, s - 6, 3, 2, 2);
                }
            } else {
                g2.setColor(isEnabled() ? new java.awt.Color(0x9AA4B2) : new java.awt.Color(0xC9CFD8));
                g2.drawRoundRect(x, y, s, s, 5, 5);
            }
            g2.dispose();
        }
    }
}
