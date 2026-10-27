# unit232 冻结实现作者报告

状态：`COMPLETE_AUTHORED_SOURCE / NOT_LEAN_CHECKED / NOT_INDEPENDENTLY_REVIEWED / NOT_QUALIFIED`。

已在唯一授权目录内完成一个公开声明的完整证明稿，源文件为 `NormalizedUpperErrorGoodsetPayment.lean`，229 LF 行、11214B，SHA256 `c95d036b852a66fb86fdef687cdff2ab4a0e6736b45cb015f8d57d3330f1ddf8`。文件严格按冻结的 preamble + head + ` := by` + proof + closing 组装，未改冻结文本、前提、实际事件或 RHS。没有其他顶层声明、局部普通辅助定义或额外模块。

## 授权、来源与证据边界

完整读取并核对本次激活、冻结记录、parent intake，以及冻结 preamble/head/closing。初始实际 ACK 在证明写入前保存于 `RUNTIME-ACK.json`。本次只保留同一个作者角色；不是独立审稿者，没有自授合格结论。

数学来源与四个实际 API 的完整声明已在封存 Stage1 的 `SOURCE-AND-ROUTE.md` 中绑定。主要复用项是 v128 receipt 中仍保持精确源哈希的：

- `NormalizedAnalyticCostLimits.actual_normalization_sequence_limits`：直接提取真实 canonical `η` 的可测性和逐点极限。
- `NormalizedRawNumeratorBuffer.actual_normalized_raw_numerator_bad_event_limsup`：直接提取 `Wη/Vη/Dη` 收敛、原始严格余量下的最终安全、`L ⊆ Eorig ∪ Z` 和原有尾并集实测度极限。

没有重写旧归一化 producer、连续性证明、reverse Fatou、DCT 或尾测度连续性；没有使用旧 theorem 最终的 `ν.real Eorig + p0` 标量界。这些既有证明不在本次重新认证范围内，只将其精确合格接口用作依赖。

## 完整证明路线

源第 93 行的 `hDbridge` 对所有 `k,ω` 明确证明冻结 `Dη = D1 + Q` 与既有 API 的 `D1 + W - Wη + z*b*(Vη-V)` 相等。之后对可测性、真实分子坏事件、余项收敛、好集安全、尾集合和尾实测度极限的复用都通过这个桥接；没有因括号差异静默更换函数。

第 97 行调用序列 API，直接取出 `η` 可测性与坐标逐点收敛。第 102 行调用 raw-numerator API，以 `hz` 推出其所需的 `0≤z`；取出原 `Wη/Vη/Dη` 收敛和安全/覆盖/尾极限。第 108–132 行显式对齐余项与事件，给出 `Dη/Q/E` 的可测性、固定 `E2` 的可测性，以及 `Dη→D1`、`Q→0`。`Q` 的性质由 `Q=Dη-D1` 得到，不重新实现 canonical 收敛。

第 134 行只从 `z≥1` 和 `hgood` 的第三项导出 `|D2|≤1/8`，继而导出 `1+D2≥7/8` 与好集内 `b>0`。这个推导没有加入 `H` 外的正性前提。第 147 行把原有最终安全直接应用于好集前两项，再和 `Vη→V>0` 的最终正性合并。量词保持为 `∀ω∈H, eventually k`，没有提升为对整个好集同时有效的统一指标。

第 162 行取出既有尾覆盖。第 168 行利用 `hgood` 排除 `H∩Eorig` 和 `H∩Z`，把覆盖收紧为 `L ⊆ Hᶜ`；第 173 行直接得到 `ν.real L ≤ ν.real Hᶜ`。第 174 行直接复用既有 `ν.real(U N)→ν.real L`，只做 actual-event RHS 桥接。

第 185–192 行分别证明固定 `E2⊆Hᶜ` 和 `Z⊆Hᶜ`。第 193 行使用已经提取的尾极限，对任意正容差取得某个尾指标 `N`；以 `E k⊆U N` 和 `ν.real L≤ν.real Hᶜ` 得到最终实际事件概率界。第 207 行使用概率测度的一般 `[0,1]` 界；第 209–223 行以非负下界提供 limsup 所需的 coboundedness，再从每个正容差最终界去掉容差。付款始终是一份 `ν.real Hᶜ`；固定第二事件和零能量事件各自另外给出同样的单独界，未声称三项概率之和有单倍付款。

第 224 行按冻结的 16 个顶层结论顺序组装全部结果。源中没有未填证明分支或目标性质回调。

## 冻结结论逐项覆盖

| 冻结项 | 实现中的提供者 |
|---|---|
| C01 `η` 可测 | `hηm`，序列 API 直接投影 |
| C02 `Q/Dη/E` 可测 | `hQm/hDηm/hEm`，实际 RHS 桥接 |
| C03 固定 `E2/Z` 可测 | `hE2m` 与 raw API 的 `hZm` |
| C04 坐标 `η→ξ` | 序列 API 的 `hηpoint` |
| C05 `Wη→W` | raw API 的 `hWpoint` |
| C06 `Vη→V` | raw API 的 `hVpoint` |
| C07 `Q→0` | `hQpoint`，由已提取 `Dη→D1` 相减 |
| C08 `Dη→D1` | `hDpoint`，raw API 及显式桥接 |
| C09 好集内 `1+D2≥7/8`、`b>0` | `hD2good` |
| C10 好集内逐样本最终正能量和分子安全 | `hsafe`，原安全 API 与 `Vη` 极限 |
| C11 固定 `E2⊆Hᶜ` | `hE2sub` |
| C12 `Z⊆Hᶜ` | `hZsub` |
| C13 固定第二事件概率界 | `measureReal_mono hE2sub` |
| C14 原零能量事件概率界 | `measureReal_mono hZsub` |
| C15 任意正容差最终概率界 | `heventual`，复用尾极限及收紧覆盖 |
| C16 精确 limsup 好集付款 | `hlimsup` |

## 普通数据、证明绑定与范围

声明头仍是 1 个类型参数、2 个显式实例、9 个 ordinary 参数、15 个 Prop 参数，共 27 个绑定；11 个 typed lets 的完整类型和 RHS 不变。证明体内重现同样的 11 个已冻结 lets，再且仅再引入已获准的三个普通对象：

- `Eorig : Set Ω := {ω | z*|D1 ω| > V ω/8}`。
- `U : ℕ → Set Ω := fun N => ⋃k, ⋃(_ : N≤k), E k`。
- `L : Set Ω := ⋂N, U N`。

其余 `have`、`rcases` 输出均是等式、可测性、收敛、包含、序关系或事件性等 Prop 证明绑定，没有新实函数、代价包络、法则、数据见证、私有辅助声明或回调。`N` 仅从实际 atTop 事件性证明中取得；是冻结 parent intake 已明确允许的最终指标。未来 actual TYPE 审查仍须确认编译器真实产物和可能生成的声明，不在此预报 owner 数或 VALUE 数。

不需要全局 `1+D2>0`，不要求原空间标准 Borel、原测度无原子、独立性、四矩或混合四矩。`hH` 保留为冻结的可测好集输入；单纯尾覆盖与有限测度单调性本身不必额外消费该假设。实际 `Y` 与尺度 `ε` 是唯一传入的近似数据，`η/Vη/Dη` 极限和安全性全部为输出。

## 实际做过和未做的检查

已完成纯文本/字节层检查：严格冻结 prefix/closing、唯一公开声明、证明体 14 个 ordinary lets 恰为 11 个镜像加 3 个获准对象、没有禁止证明机制、UTF-8 无 BOM、仅 LF。输入绑定和最终 payload 哈希由清单记录。

按本次明确任务限制，Lean、服务器、网络、上传、Git/API、子实例均为 0；未读取 unit228 未合格实现或 unit231 实现/审查。没有执行旧 producer 或任何新的 kernel/AX 命令。因此这里没有机械通过结论，也没有独立正确性结论。主实例仍需对这份完整源做来源/接口接收，安排全新合格独立审查，以及按项目资源与证据规则完成新源 kernel 和同一原始对象的全部 actual TYPE/所需 VALUE/传递公理审计。

## 原始范围保留

本文件完成的是冻结的固定概率律、有限行、固定 `z≥1` 的任意合法自然数序列付款证明稿。它没有实例化原模型同一 full-observation/canonical witness，没有证明实际 F4/F5 好集集中率，没有提供连续参数 `ε↓0` 桥，没有组合 unit231 严格预算，没有应用 source upper/Shao–Zhou、CDF 或 physical T/root 结果。上述责任保持 Stage1 和 parent freeze 已注明的开放边界。

`requestedModel=gpt-6.1-sol`、`requestedEffort=xhigh`；实际未暴露的模型、努力程度和 input/cached input/output/reasoning-subset usage 统一记录为 `null`，不作订阅比例分配推测。
