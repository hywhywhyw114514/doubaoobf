/*
 * DoubaoProtect SDK
 * 在函数内成对调用标记宏，加壳时加壳器会把 Begin..End 之间的代码区域
 * 纳入虚拟化门控/变异保护。标记必须放在函数入口处（区域即函数体）。
 *
 * 示例:
 *   int secret(int x) {
 *       DoubaoProtectBeginUltra("secret");
 *       ... 业务代码 ...
 *       DoubaoProtectEnd();
 *       return y;
 *   }
 *
 * 注意：Begin/End 之间不要放提前 return（保证 End 可达）。
 */
#pragma once

#ifdef __cplusplus
extern "C" {
#endif
void DbpMarkV(void);
void DbpMarkM(void);
void DbpMarkU(void);
void DbpMarkEnd(void);
#ifdef __cplusplus
}
#endif

#define DoubaoProtectBeginVirtualization(...) DbpMarkV()
#define DoubaoProtectBeginMutation(...)       DbpMarkM()
#define DoubaoProtectBeginUltra(...)          DbpMarkU()
#define DoubaoProtectEnd()                    DbpMarkEnd()
#define DoubaoProtectBegin(...)               DbpMarkU()
