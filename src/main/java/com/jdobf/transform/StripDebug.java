package com.jdobf.transform;

import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.LineNumberNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.ParameterNode;

/**
 * 剥离调试信息：SourceFile、行号表、局部变量名/类型表、局部变量注解。
 * 不改变任何可执行指令与控制流。
 */
public final class StripDebug {

    private StripDebug() {
    }

    public static void apply(ClassNode cn) {
        cn.sourceFile = null;
        cn.sourceDebug = null;
        for (MethodNode mn : cn.methods) {
            if (mn.instructions != null) {
                AbstractInsnNode insn = mn.instructions.getFirst();
                while (insn != null) {
                    AbstractInsnNode next = insn.getNext();
                    if (insn instanceof LineNumberNode) {
                        mn.instructions.remove(insn);
                    }
                    insn = next;
                }
            }
            mn.localVariables = null;
            mn.visibleLocalVariableAnnotations = null;
            mn.invisibleLocalVariableAnnotations = null;
            // parameters 的注解可能被框架使用，只去掉名字
            if (mn.parameters != null) {
                for (ParameterNode p : mn.parameters) {
                    p.name = null;
                }
            }
        }
    }
}
