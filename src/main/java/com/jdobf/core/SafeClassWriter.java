package com.jdobf.core;

import org.objectweb.asm.ClassWriter;

/**
 * 使用我们自己的 Hierarchy（jar ClassNode + 反射回退）来计算公共父类，
 * 避免 COMPUTE_FRAMES 因找不到依赖类而产生错误栈帧。
 */
public class SafeClassWriter extends ClassWriter {

    private final Hierarchy hierarchy;

    public SafeClassWriter(Hierarchy hierarchy) {
        super(ClassWriter.COMPUTE_FRAMES);
        this.hierarchy = hierarchy;
    }

    @Override
    protected String getCommonSuperClass(String type1, String type2) {
        return hierarchy.getCommonSuperClass(type1, type2);
    }
}
