# Unit 219：kernel004 的单个 public2 依赖 motive 修复候选

作者 `/root/bounded_centered_fixed_formal_author003`，恢复自 repair003 全零 RELEASE，配置 gpt-6.1-sol / xhigh；实际后端、实际模型、实际 effort 和 input/cachedInput/output/reasoningSubset 不可观测，均记为 null。仅在 native-repair004 写入，使用 math-theorem，未启用 math-ultra；无 Lean/AX/heavy、上传、Git/API、子代理或额外远程请求。

## 实际证据

activation004 与其 8 个绑定的 SHA256/字节数全部核验。基线为 repair003 完整 5bdec 源：187545 字节、3220 LF，SHA256 `5bdec1cb3042623828a94867b38f807774a40dc635e3809e334341fa4a5c9f6e`。kernel004 自然 RC1，只报告 public2 原行 1877 一条实际错误 `rewrite failed: motive is not type correct`；无 maxErrors 上限、无成功对象、无 AX，基线前后哈希相同。

作者完整读取了 curated 单条诊断的首 60 / 末 20 行及完整错误块 SHA、字节/行数、中段省略数量。完整错误块为 22418 字节 / 458 行，SHA256 `4a542e1563b7c3250721f1ecd6828a0c284aac33ede1b3c1ed3e99a1e09c4fc3`；中间 378 行由该完整块哈希绑定。完整 raw log 仍留服务器，本轮没有下载或补读请求。

## 错误原因与局部修复

原停止后缀积分接口的 Phi 输入是 `Path((rt+t)-t) × Path t`。上一候选直接对整个展开后的 hs 类型重写 `(rt+t)-t=rt`。实际诊断显示，其生成的 motive 同时把后缀下标改为 `_a+i`，但下标附带的 Fin 边界证明仍依赖原具体长度，导致该 motive 对任意 `_a` 不合法。这是依赖类型运输失败，不是原自然数等式或数学积分身份失败。

本候选仅在 public2 的 hpiecePositive 证明内建立局部命题 hStopped：

- 以长度 k 和等式 `hk : k = (rt+t)-t` 为参数；Phi 的局部名称 F 具有真实类型 `Path k × Path t → ℝ`，同时携带可测性、绝对值 ≤1，以及各固定后缀的前缀积分 ≤0。
- prefix/suffix 的 Fin 坐标边界证明在该参数化族内由 hk 与自然数算术共同给出，因而整个族对任意满足 hk 的 k 都有合法类型。
- 在该局部证明内部先 `subst k`，将 F、其可测性/有界性、section 积分及边界证明一起运输到原接口维度，然后原样应用 actual_backward_stopped_suffix_integral。
- 使用该已应用接口的真实积分等式和固定后缀非正积分，推出选中分片积分 ≤0。最后以 k=rt、原 Phi / hPhim / hPhib / hsection 实例化，再用原 heqf 把 Φ(prefixPart,suffixPart) 还原为 Dr-c。

因此不再对已展开且携带旧 Fin 证明的整个 hs 类型直接重写，也不需要新的全局 helper 头。hStopped 是同一个 public2 证明体内的局部命题，没有增加数学假设：hk 在实际实例由自然数等式证明；F 的各条件正是本来已有的合法 bounded-Phi 和 hsection 事实。

这项实现仍待下一实际原生编译确认；作者不把局部推导的意图作为已成功 elaboration 的证据。

## 字节与范围约束

本轮相对 5bdec 只改变 `iid_actual_all_level_h0_terminal_budget` **1 个**证明体，其他 **15 个**完整证明体逐字保留。全部 **16 个**当前冻结头逐字一致，冻结基础仍为 13 个原头、P4 事先冻结的显式类型头和 2 个事先冻结的公开导出头。5 private defs、local instance、7 imports 所在完整前缀逐字不变；P3 原有证明体局部 heartbeat 800000 完整保留。

没有新增全局声明、import、假设或数学定义。原 strict/closed selectedSuffix 边界、m0 的 NH≥1、t=0 空分片、真正 raw U/J² 的 L1 来源、合法 bounded-Phi、完整未来/最终壁及 identity 后 reveal 积分范围保持原样。没有更改其他证明或父实例拥有的 220 模块，没有回退他人改动。

逐条错误映射、当前/累计 body hash 差异和输入/源/payload 精确绑定分别见 REPAIR-ERROR-MAP、HEAD-CONSISTENCY、INPUT-SEAL、SOURCE-SEAL、PAYLOAD-SEAL。源码扫描不含 sorry/admit/axiom/unsafe/native_decide。

## 下一依赖与释放

下一依赖是父实例对本精确新源的原生检查。即使后续原生返回成功，仍需最终独立完整受影响证明/实际 TYPE 复核、已要求的 P4 修订头及两导出覆盖，以及精确源全部 actual-owned 传递 AX 凭据。仅余一条错误不构成其他结果正式资格；无上限错误标记也不保证失败依赖后的全部证明已经处理。actual-owned 数量仍未知，formalQualified=false，C2/C12 OPEN。

RELEASE 记录实际 sourceWriter/heavy/inflight/LeanAX/uploads/GitAPI/children/externalRequests 全零。本轮 final 结束作者运行，不表示后台持续；旧所有封印源、失败字节与回执均未改动。
