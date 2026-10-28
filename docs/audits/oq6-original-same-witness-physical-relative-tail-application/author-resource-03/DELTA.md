# Unit249 有限定理选项修订

仅在旧第 15 行 theorem 前插入 `set_option maxHeartbeats 800000 in`，作用域仅为随后这一个定理声明。新源 SHA256 `19c3e659b538c19d7e73a55bcaec1dc6727b435665e215890cc6c219c88704a0`，240965 字节、3825 LF，UTF-8 无 BOM、仅 LF，精确命中 freeze03。

移除新插入的 35 字节行即可逐字节还原旧源 8202e107…f1f899b；全部数学声明、假设、证明逻辑、let、RHS、实例、选择以及 28 个事实片段哈希保持原样。第 15 行及之后的原坐标按实际 UTF-8 重算为 +35 字节、+1 行，列号不变。复用已封存确定性元数据函数与完整库存校验逻辑，重新核对 730 let、8 letI、28 have/完整冻结类型、155 public、159 optional、2 same-data choices；并未重新生成或重读不变数学证明。

native02 的实际 RC1/noO、26.810858 秒、默认 200000 心跳上限、3819:74 tactic/15:0 whnf 两条诊断和所有 warnings 原样保留；原加法接口错误已不存在。该失败不是内核通过，新资源选项也不构成证明检查结果。独审旧源 CORRECT 与完整旧覆盖按精确哈希复用，新选项差异仍待独立审查，随后由 lead 安排新源 native/同首个成功原对象实际 TYPE/必需 VALUE/transitive AX。

本单元没有 Lean、PP、AX、服务器、网络、上传、Git、外部 API、publication 或 children 操作。sourceAccepted=false，qualified=false，kernelPending=true；fullOQ56=OPEN。请求模型/effort 保持 gpt-6.1-sol/xhigh，实际模型/effort/usage 不可见，均记 null。
