# Unit249 独立完整源码审查，首次封存版本

STATUS: CRITICAL_GAPS

本报告只适用于 `OriginalSameWitnessPhysicalRelativeTailApplication.lean`，SHA256 `a81c0e0e50a16e3ee9ae06ef3d1ce8b82f4a0c6a97766320a1a529a2bfb245f5`，240928 字节，3824 LF。冻结声明 JSON 为 `1c02c82ad8077a51d1f445c0a5b0d9b9b92c3b1a512832f4dfee5d6626772e20`。审稿人与作者隔离；作者的 PROVED 自评、自己的证明说明和生成脚本均不构成结论依据。

数学推导、来源对应和冻结接口审查未发现额外数学缺口。但提交的 Lean 证明在第 3768 行有一个已由指定服务器实际报告并由本审稿人核对的接口错误。因此本版本不获源码放行，不合格，不能将其记作证明通过。

## 精确缺口

`hPaymentLeOne` 的第 3768 行为 `apply add_le_add_left`。首次指定服务器检查的完整失败 header 报告：该实际 API 的结论是 `b + a ≤ c + a`，其完整参数条件为 `Add`, `LE`, `AddRightMono`，而当前目标为 `A + B ≤ A + C`，其中

- `A = 3*exp(-boundedPolylogMomentOrder t0 n) + exp(-cg*n)`；
- `B = 4*exp(-(z*sqrt(n))/2)`；
- `C = 4*exp(-sqrt(n)/2)`。

这两个表达式不能按该次 `apply` 直接统一。错误位置为 3768:6；承重数学不等式需要使用当前实际 API 能表达的加法单调性，但本审稿人不改写证明或命题。后续乘法单调性、指数单调性及由 `z≥1`、`sqrt(n)≥0` 推出指数比较的数学路线成立，不能弥补这个尚未通过的 Lean 调用。

诊断输入为 `lead-execution-01/native-complete-diagnostic-projection.json`。其中记录 native 实际 RC1，27.502 秒，唯一 error，未产生对象；全部 owned 进程结束，source/preservation before=after，无 timeout、cleanup、ownership 问题。原 receipt SHA256 为 `8479ab299d92811f0b4ce8fd0b169fd2cadafcdaf8b67ed186e8b15ed7e163ac`；错误消息 SHA256 为 `0cdee26250cb930754b6c7f550c79f9ac5409c5eabf723efe823ff292b68030d`。这是失败证据，不是部分内核接受或剩余证明全部通过的证书。本审稿人未访问服务器、未执行 Lean。

## 完整阅读和去重边界

完整阅读了原始 `p51.md`、`p54.md`，249 全部公开声明、全部证明执行文本、全部新独特上下文及所有承重局部类型。完整阅读了冻结设计的 `API-CONTEXT.md`（714 行）及 `SOURCE-ROUTE.md`；32 个导入定义的完整参数、返回类型和 RHS 均已阅读，包括原 `n-1`、`n-2` 系数、jackknife 平方、裁剪和 Gaussian 参照尾。

源码 1–806 行逐行阅读。六个巨大复写 Prop 类型只折叠连续空白，保留符号和标识符的边界；分别严格匹配到已经完整读过的公开 head 连续子式。其全部上下文由 N00、N01、N01c、N01m、N01s、N02、N03、N04、N05、N06、N07 恢复，未用摘要替代证明：

| 实际复写类型 | 源码行 | 已读 head 对应源码行 |
| --- | --- | --- |
| hCg | 813–1519 | 38–744 |
| hModel | 1526–2231 | 39–744 |
| hRetained248 | 2244–2944 | 44–744 |
| hOldPayments248 | 2950–3200 | 494–744 |
| hOldAtN248 | 3264–3510 | 498–744 |
| hOldAtCurrent248 | 3515–3748 | 511–744 |

其余源码行及这六段之间的所有 RHS、选择、实例、引入、匹配、局部 have、证明结尾均实际阅读。h248 是唯一获准推断的 Prop；其他 27 个 have 的完整类型均与冻结库存相同，且与其实际源码坐标提取一致。所有 FACT-COORDINATES 片段 SHA256 已独立复算。

独立重数得到 155 个 public ordinary，159 行 optional ordinary 库存，730 个源码 lexical ordinary let（含 570 个类型内复写、155 个 public、5 个实际证明 let），8 个 letI（其中只有 2 个是证明中的选定模型实例），28 个 have，4 个 `Classical.choose` 和 8 个 `choose_spec`。4 次 choose 中只有 cg、m₀ 是数据；hm₀、hcg 是同一个 hModel 的证明见证。730 个 let 的完整类型和 RHS 均与冻结引用核对；8 个 letI 均核对，其中 CountablyGenerated 的隐式可测空间参数由紧邻的 selectedSpace=m₀ 解析，显式类型为库存中的 `@MeasurableSpace.CountablyGenerated Ω m₀`。无新实例。

155 个 public 类型/RHS 与源码坐标逐项核对；optional 的旧 145 行与 public 旧 145 行相同，新 10 行与 public 新 10 行相同，另 4 行是同一次结果的 cg/m₀ 与两个 payment 标量别名。两项完整 choice propositions 也与 hCg/hModel 类型相同。完整源文前导、head、结尾逐字节相同；移除新契约的兄弟合取并还原定理名，可逐字节恢复完整旧 248 head。禁用 token 为零；只有一个顶层 theorem，无新 helper、selector、Nat cutoff、structure 或公理。

作者 manifest 的 19 个 input 与 8 个 payload 绑定（共 27 项）全部独立复算通过。这是字节检查，不把作者说明或未读文件当数学审查。本审稿人的完整输入和输出绑定另见 MANIFEST.json。上述读法覆盖全部 3824 行；没有保留未读的独特证明片段。

## 来源、依赖和作用域

p51 S1 的原 centered-row 统计量、原 F、D、s 和 s=0→0 约定保持。p54 对 p51 S6 任意多项式条件 p 矩变化率的修正保持：本单位没有使用该错误速率，也不重新认证那句话。原文的外部 Shao–Zhou 随机区间/有限费用输入明确保留；此单位不宣称从零证明该输入。

精确复用已经合格的 248：qualified-evidence SHA256 `d58d36550e44bb91d9a7dd131386c1d44525764ca697999100520f7418efa690`，源 `50cc9872e1d6148e4a81f0d49da391a1b4b749b682c91b4ba347ae22bad00433`，FIRSTO `78972bd1f02cc3f8173bad9f660f6a690587182edf3fad8d9a0d38041436f92e`。原先合格的完整审查、TYPE 和 AX 证据按精确接口复用，没有重审或重跑旧证明。

236 的 qualified-evidence SHA256 `72ffd387efd4ecdbfb464d3e1d05432d871d711b56012cdb629a46eac6282deb`，源 `cb1ed434c1029e674ddff14a1be07ab55b2fb064060acbe92bea389a93f7df8f`，FIRSTO `99a8ccfe353e26adef88d524e78418952f840906bb0a63ba886156a88a53d716`。只消费其已合格公开接口；API-CONTEXT 中完整 99LF actual TYPE 与全部隐式 real 上下文已读。未重放旧 producer/proof/TYPE/AX。

新分支是旧分支之外、同一个 selected-model 结果层的兄弟合取，不在旧 guard 的前提内部。固定 rho 在最终 n 和晚出现的 w、z 之前；晚 envelope 假设不新增 Measurable w。完整 full 和 deleted sourceCost 权重、删除量、512/rho/1 参数、原 strict moment window 和外部输入量词保持。

## 全部证明义务的独立核对

1. 807–811：248 恰调用一次，且在全部 g/r/v/rho/β/cWindow 的 let 引入和 cg/m₀ 选择之前。其六个原始共同事实和同一个 existential 逐项投影，未调用独立 235/237/239 selector。
2. 812–3203：hCg、hModel、hm₀、hcg、μ₀、两个选定实例、hRetained248 和 hOldPayments248 的类型与投影一致。最终构造保留全部原 248 分支。证明见证的嵌套选择未产生另一 law/model。
3. 3204–3233：bounded_scales_pos 的最后字段给 tailScale>0，remainderWindowScale_bounds 给实际原尺度>0；236 在原 t0 给第二尺度>0。两者的 min 得 cPaid>0；同时 cPaid≤两个父尺度且≤1，无隐藏 cost-smallness 假设。
4. 3234–3251：cPaid>0 允许 sqrt((2*cPaid)^2)=2*cPaid，故辅助窗口 min(1,sqrt((2*cPaid)^2)/2)=cPaid。第二次 236 调用仅保留 n≥4 和窗口非空字段；辅助平方参数没有进入最终 R 或实际费用。
5. 3252–3262：Real 命名空间的 sqrt→atTop 与自然数到实数的 atTop 映射复合，把固定阈值 1+rho 拉回最终自然数集。四个 eventual 集相交先于 w、z 引入；guard 因而真证，未转为用户假设。
6. 3263–3752：非负 n^(1/6) 把 paid-window 中的 z 送入旧 remainder window。新 mN、P、N、ξ0、D1、L0、sourceCost0、Tphysical 的 let 与旧费用结果定义相同。第 3791 行到 guard 的 46 次 `.2` 分别跨越 39 个旧支付外层字段和 7 个物理字段；应用 guard 后 5 次 `.2` 到达最终物理 paid bounds，未误用临近 clipped bounds。
7. 3753–3763：两个 payment 别名是旧同 witness 的字面费用；236 左侧逐项恰是 2*payment1，系数 6/2/8 与 3/1/4 对应。
8. 3764–3771：payment_z≤payment1 的数学理由是 z≥1、sqrt(n)≥0 和指数单调性；但实际第 3768 行有上文唯一已知 formal API gap，故这一提交尚未完成。
9. 3772–3784：236 的费用界使用原 t0、同 cg 和实际 z。cPaid≤原吸收尺度使其适用；下损失 payment_z+payment1≤R*Ψ，上损失 3payment_z+payment1≤2*(R*Ψ) 可由两条线性不等式推出，不需要任何因子额外正性。
10. 3785–3824：原外部 SZ input 和 moment alternative 原样传入旧物理结论；最后仅加减不等式和乘法分配律，因而没有除以 Ψ、没有要求 Ψ>0、没有要求 sourceCost 小或 1-C2*sourceCost 正。R 恰为 exp(-(t0/2)*n^(1/3))；物理事件是闭的 z≤Tphysical，s=0 分支仍为 0。没有用尾原子连续性、CDF 或 root 完成声明。

## 当前裁决和后续复用

本次完整源码审查以 CRITICAL_GAPS 收束；唯一已知关键缺口为 3768:6 的形式接口。数学契约忠实、推导其余部分无新发现问题，不等于该源版本通过。sourceAccepted=false，qualified=false，kernelChecked=false，axiomAudited=false。未产生成功 FIRSTO，未收到新单位成功对象的完整 actual TYPE、必需 VALUE 或 recursive AX 材料。

按 lead 的明确新指令释放本 SOURCE 阶段角色。后续同一独立上下文可在 followup 中只审真实最小差异及受影响范围，精确复用本报告其余完整阅读，并继续审最终成功 FIRSTO 的全部实际所属 TYPE、必需 VALUE 和 transitive AX。任何额外变化都按其真实影响增加审查，绝不把本次失败证据转记通过。

requestedModel=gpt-6.1-sol；requestedEffort=xhigh。实际后端、模型、effort、input、cachedInput、output、reasoningSubset 均不可见，记 null。本审稿人实际 Lean/lake/PP/AX/server/network/upload/Git/publication/children/Goal/schedule/sidebar 操作为零。
