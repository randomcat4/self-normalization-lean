# 原文 2176–2215 到真实平方矩消费者的源合同

状态：`CANDIDATE_NOT_FROZEN / NO_IMPLEMENTATION / NO_LEAN_RUN`。作者职责限于本目录。使用 math-theorem，未启动 math-ultra 或子上下文。

本候选服务原 `C:/game/shao/current/c12/supplement.tex` 2176–2215、调节量引理 572–585 中的单项平方矩。它证明一个真实乘积概率律上的条件消费者；原始源生存界仍是明确未支付输入。预期下游是反射缺陷中的 `U_i²` 权重及随后总和/晚时刻估计，不以本消费者宣称这些后继或 C1/C2 根闭合。

## 对象与符号完全绑定

自然语言 `i = 1,…,N` 对应 `j : Fin N` 的 `i = j.val + 1`。路径 `a : Shao.Path N` 的坐标 `a j` 就是 `A_i`。使用既有真实递推

`Shao.lindleyState a 0 = 0`，
`Shao.lindleyState a (k+1) = max 0 (Shao.lindleyState a k + a[k])`。

既有 `Shao.Probability.lindleyRegulator a j = max (-(W_{i-1} + A_i)) 0`。没有另定义抽象 `U`、自由可积随机变量或任意概率核代替它。

源版的原始概率律为 `nu`，原始数据为 `Integrable z² nu`、`N * ∫z² = 1`、`∫z = 0`、`x ≥ 0`、`0 < epsilon ≤ 1/2`、`truncationBudget nu N x ≤ epsilon³/8`。实际条件律为

`rho = cond nu {z | |z| ≤ epsilon/(1+x)}`，
`P_N = Measure.pi (fun _ : Fin N => rho)`，
`mu = ∫ z ∂rho`，`m2 = ∫ z² ∂rho`，`m3 = ∫ |z|³ ∂rho`，
`V = variance id rho = m2 - mu²`，`tau = sqrt V`，`gamma = m3/V`。

`gamma` 仍是未中心化三阶绝对矩除以方差，绝不是 `E|A-mu|³/V`。未要求条件律 `rho` 的均值为零，也未要求原始律有三阶矩。实际 `P_N` 的坐标独立性与同分布直接由乘积定义支付；上游真正 iid 样本若在另一个空间中表达，可使用已接受 `iid_samplePath_map_eq_pi` 绑定到此 `P_N`，本轮不新增抽象样本包装。

## 原文逐段对应

| 源行 | 原文义务 | 候选承担的精确内容 | 状态 |
| --- | --- | --- | --- |
| 2176–2179 | `i=1`，`tau*m2 ≤ m3` | `iid_lindleyRegulator_one_second_moment`：真实负部平方积分与 `m3/sqrt V` 上界 | 待实施；不调用生存界 |
| 2180–2183 | `U_i² ≤ (A_i^-)² 1{W<A_i^-}` | `lindleyRegulator_sq_le_strict_weight`，全路径逐点结论 | 待实施 |
| 2184–2185 | `W` 与真实前缀最大值同律 | `iid_lindleyState_coordinate_map_eq_prod`，同时保留当前真实坐标 | 待实施；复用既有反转结构 |
| 2186–2198 | 原生存引理、中心三阶矩和漂移支付 | 既有 `sourceTruncation_paid_moments` 支付中心三阶可积及 `≤8m3`；既有方差和附近预算支付相关矩数据；**不由此声称生存界已支付** | 有限步定量 BE、原始概率 Spitzer 与带漂移生存生产者仍欠 |
| 2199–2203 | 真实 `P(W≤r) ≤ C min(1,(r+gamma)/(tau sqrt i))` | `lindleyPrefixSurvivalBound rho N C`，完全展开为真实乘积最大值概率 | **显式前提，不是本单元结论** |
| 2204–2208 | 真正独立性和事件积分 | 实际联合律等于 `(maxWithZero#P_{i-1}).prod rho`；`iid_lindleyRegulator_sq_disintegration` 输出两侧可积性及真实严格事件积分等式 | 待实施；不假设独立/可积 |
| 2209–2211 | 积分生存界得到 `C(m3+gamma*m2)/(tau sqrt i)` | 候选通用消费者，代入 `r=A_i^-`，保留 `j.val+1` 的精确分母 | 待实施 |
| 2214 | `gamma*m2 ≤ 2m3` | 通用版显式真实 `m2≤2V`；源版内部从已接受方差结论支付 | 源数据已足够；不新增源假设 |
| 2215 | 单项界完成 | 只得到**以真实生存界为前提**的 `max(1,3C)*m3/(sqrt V sqrt i)` | 不标记原始无条件源引理闭合 |

## 已接受接口的准确用途

1. `Shao.Basic.Lindley`：真实递推、`prefixPath`、`reversePath`，以及 `lindleyState_eq_maxWithZero_reverse_prefix`。后者是反转前缀后的逐路径恒等式；不能把原路径 `W` 直接等同于原路径前缀最大值。
2. `Shao.Probability.FiniteIID`：实际乘积坐标的 `iIndepFun_pi` 可实例化为固定有限 iid 样本；`iid_samplePath_map_eq_pi` 和固定置换律可将原始真实 iid 表达转为 `Measure.pi`，并支付逆序不变性。
3. `LindleyTelescoping`：只复用现有 `lindleyRegulator` 定义与导入的基础路径定理。该文件的调节量可测性辅助定理为 private，若不能调用，用原始递推作短归纳证明；不改该文件。
4. `SourceTruncationBridge.sourceTruncation_law_data`：支付 `rho` 概率性、真实截断支撑与一/二/三/四阶可积性。
5. `sourceTruncation_variance_bounds`：支付 `V=m2-mu²`、`0<V`、`3/4≤N*m2`、`N*mu²≤1/4`、`1/2≤N*V≤4/3`。由 `mu²≤m2/3` 或直接代数得 `m2≤2V`。
6. `SourceFourierScale.sourceTruncation_gamma_bounds`：已经输出 `sqrt(m2)*m2≤m3`、`m3>0`、`gamma>0` 等真实矩结论。源版首步可直接复用。其通用 Lyapunov 证明辅助定理 `sf_raw_lyapunov` 为 private；通用版可在本模块用同一个点态多项式不等式证明私有通用引理，不扩大/改写已接受声明。
7. `SourceTruncationBridge.sourceTruncation_paid_moments`：已有 `Integrable |z-mu|³ rho` 和中心三阶绝对矩 `≤8m3`。它供未来真正生存生产者使用，不能推出有限步概率率。

不重跑、不重新审查上述未改动接受模块。本单元独立审查只需完整覆盖新源码/声明和实际依赖接口；接受的旧证据按精确哈希复用。

## 证明路线（候选，不是已认证证明）

**A. 逐路径与可积性。** 递推得所有 `W_k≥0`。若 `W_{i-1}≥A_i^-`，则 `W_{i-1}+A_i≥0`，故 `U_i=0`；否则 `0≤U_i≤A_i^-≤|A_i|`。平方后得到声明 1，以及无条件 `U_i²≤A_i²`。真实坐标评价在乘积律下保测，所以二阶矩控制函数 `a↦(a j)²` 可积。用可测性和支配取得声明 3，也取得严格加权函数 `F` 可积。这里完全不需要生存概率界。

**B. 反转与独立性的真实联合律。** 在真正有限乘积空间上拆出前 `j.val` 个坐标与第 `j.val` 个坐标；所有未来坐标只贡献质量 1。对前缀作固定 `Fin.revPerm`，乘积律保持不变，当前坐标保持不动。用 `lindleyState_eq_maxWithZero_reverse_prefix`，输出声明 2 的精确联合像律。等式右侧的乘积形式支付 `W_{i-1}` 与 `A_i` 的独立性，不接受任意 `IndepFun W A` 作为外部输入。`j.val=0` 的前缀是真正空乘积，最大值为 0。

**C. 非负积分/Tonelli 与 Bochner 积分合法化。** 在上述联合律上取非负 Borel 函数 `H(w,z) = (z^-)² 1{w<z^-}`。先以非负扩展积分的 Tonelli 拆分；整体受当前坐标平方控制、因此有限。由有限性得到所需 Bochner 可积性；也可在已得整体可积性后用 Fubini。内层积分是 `(z^-)²` 乘 `P_{i-1}(maxWithZero<z^-)`，恰为候选 `lindleyRegulatorSquareCost`。阈值核可测性由参数积分得到。声明 4 必须先证明这些有限性，不能利用 Lean 对不可积函数的积分默认值来形式上完成等式。

**D. 第一时刻。** `W_0=0` 给 `U_1=A_1^-`。概率律下 `h3` 先支配出 `h2`，用 `MemLp`/真实方差恒等式得 `V≤m2`。令 `b=sqrt(m2)`，积分点态不等式 `3b z²≤2|z|³+b³` 得 `b*m2≤m3`。于是 `sqrt V*m2≤m3`，而 `sqrt V>0`，故 `E U_1²≤m2≤m3/sqrt V`。源版直接消费既有真实 Lyapunov 与方差数据；不另假设 Lyapunov。

**E. 后续时刻。** `j.val≥1` 时，以 `r=z^-≥0` 使用唯一未支付前提。严格事件包含于闭事件，不需无原子性。

`P(max<z^-) ≤ C*min(1,(z^-+gamma)/D) ≤ C*(z^-+gamma)/D`，

其中 `D=sqrt V * sqrt(j.val+1)>0`。真实 `gamma=m3/V≥0`。以 `0≤z^-≤|z|` 得可积支配

`(z^-)² P(max<z^-) ≤ (C/D)(|z|³+gamma*z²)`。

积分得 `E U_i²≤(C/D)(m3+gamma*m2)`。通用 `hM2` 与 `V>0` 给 `gamma*m2≤2m3`，所以后续时刻界为 `3C*m3/D`。统一第一步得到 `max(1,3C)*m3/D`。源版从已有 `sourceTruncation_law_data`、`variance_bounds` 支付通用版全部矩/概率前提，仅保留原真实生存前提。

## 生存生产者仍欠的精确接口

OQ4 现有定向清单 `drafts/oq4/source-survival-root-intake-20261023/report.md` 已明确：没有由实际源概率律、正方差、有限三阶矩直接产生原文 1100–1105 的无条件带漂移定量生存定理。

`ReflectedSurvival.iidOneSidedSurvival_of_cdf_and_two_original_sp` 保留真实 `hCDF`、正律 `hSP`、反射负律 `hSPneg`，只把它们消费成两侧概率界。当前调节量只需实际增量律的上侧最大值，故不应额外强加 `hSPneg`；单侧 `FiniteSurvivalLaplace.closedUpper_bound_of_cdf_and_original_sp` 本身仍要求实际 CDF 和正律原始 Spitzer 恒等式。其标准化零漂移 CDF 输入也尚未支付实际非零漂移源律的带漂移生存界。

未来要删除本候选的生存前提，至少必须真正支付：实际源标准化增量的定量 Berry–Esseen；实际一般概率律的原始概率 Spitzer 恒等式；带漂移的 Laplace 到有限步生存界（含阈值 0、空前缀与 `sqrt(k+1)`）；以及中心三阶矩 `≤8m3`、漂移因子统一控制到源 `gamma=m3/V` 的转换。固定时间布朗弱极限、纯布朗存在性或两侧 killed 核极限不能替代这一有限步小墙界。该生产义务不在本单元实施范围内，也不重复 OQ4 正在推进的工作。

## 边界和反例检查

- `U_i` 的支撑严格事件与生存闭事件刻意不同；允许实际增量律有原子，在 `W=A^-` 的原子上仍 `U_i=0`。
- `A_i^-=0` 时严格事件为空，成本为零；不需要除以负部或令墙严格正。
- `N=0` 的通用结论对 `Fin 0` 为空；源归一化排除它。`N=1` 无后续生存调用。
- 真实零路径上 `W=U=0`，平方支配/联合律/可积性均包括此情况。
- 方差零的通用平方可积结论仍有效；衰减界不适用。例如 `ν=δ_{-1}` 的 `U_i²=1`，若删除 `V>0`，Lean 中零分母会把目标右侧变成 0，形成假命题。源版已有正方差，因此无此漏洞。
- 源版没有将 `rho` 中心化。直接将实际 `A` 换成 `(A-mu)/tau` 会改变真实路径墙，尤其负漂移下不能用粗墙平移恢复需要的比例。
- `C` 是显式给定的常数，不宣称统一来源。`max(1,3C)` 吸收首步并允许 `C=0` 的形式边界；任何不可能的生存前提仍作为前提保留，不拿它制造源结论。

## 当前裁决与后继

数学候选状态：`INCOMPLETE`（尚未实施及独立审查；源原命题还缺生存生产者）。此处已产出完整待冻结声明和可检查路线，不是证明认证。未做本机或服务器 Lean 检查，无公理收据或 PR。

主协调者下一步可冻结本候选或指明精确声明变化。只有冻结后，此作者才可实施该消费者；最终完整独立审查必须交由另一上下文。根级接受不得把条件适配器计为源生存界或无条件二阶矩已支付。
