# Unit249 单行形式接口修复

本次只在新目录保存完整新源码，将第 3768 行 `apply add_le_add_left` 改为 `apply add_le_add le_rfl`。新源 SHA256 为 `8202e1075c016ea5180a40774a6e01d456399bf4d82742327cad176fcf1f899b`，240930 字节、3824 LF，UTF-8 无 BOM、仅 LF。

局部事实 `hPaymentLeOne` 的完整冻结类型保持 `payment ≤ payment1`。展开两个 payment 后，共同左前缀 A 满足 `A ≤ A`；`add_le_add le_rfl` 将目标 `A+B ≤ A+C` 归约为原有的 `B ≤ C`。其后的乘法单调性、指数单调性及由 z≥1 和 sqrt(n)≥0 得到的比较证明逐字节不变。未修改任何前提、公开类型、let、实例、选择或其他证明。

确定性脚本直接比较补丁前后的前缀/后缀和逐行差异：仅第 3768 行不同，净增 2 个 ASCII/UTF-8 字节。所有行号保持，后续字节坐标重算。28 项完整冻结事实类型均保持，其中 27 项实际显式、h248 为唯一允许推断项；155 public、159 optional、730 lexical let、8 既有 letI、同一 witness 的 2 data choices 的完整映射均复算核对。FACT 的 sourceSliceSHA256 只有 hPaymentLeOne 改变，其余 27 片段逐字节相同。

旧作者和旧独审阶段释放、freeze01/02、原失败及旧完整 coverage 均按实际哈希绑定。旧审稿结论仍为 CRITICAL_GAPS；本次不将其转记通过。未受影响完整审查按父级冻结指令复用。新源仍 sourceAccepted=false、qualified=false、kernelPending=true；等待独立差异审查和 lead 的新源服务器 native/同首个成功对象实际 TYPE/必需 VALUE/transitive AX。旧 248/236 的证明、TYPE、AX 不重放。

本上下文实际 Lean/lake/PP/AX/server/network/upload/Git/外部 publication API/children/Goal/schedule/sidebar 操作均为零；仅使用本地文本与元数据工具。requestedModel=gpt-6.1-sol，requestedEffort=xhigh；实际 model/effort/usage 不可见，全部记录为 null。
