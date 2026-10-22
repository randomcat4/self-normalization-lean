# U16b 独立声明、来源与静态环境审查

STATUS: CORRECT

唯一审查 lease 1；仅拥有本报告与服务器 run 对应 statement-review.md。不修改 scope、实现、旧报告、共享文件或缓存，不 spawn，不运行 Lean、API probe 或构建。并非独占代码库，保留他人改动。此为尚无实现的声明门，不将静态可证性判断当作内核证明。

## 第一阶段：仅冻结 Lean 块的完整定义体和类型盲译

先仅读取 thirty-eighth-unit-scope.md 的 Lean fence，文件 SHA256 `6fd7a6124bf672404f31d658f01250987f9bcdef69020cbb47e5a388cc9527f5`；尚未读取 scope 说明、R1 来源、本次作者路线或未来实现。本阶段的独立翻译先保存。

`positiveNormalLayerTerm` 是一个实值公开定义。输入任意实数测度 mu、实数 q/ell/h/theta 和自然数 n/k，无概率、正性、格点或 n>0 门。输出依次为：实 sqrt(n)，乘 exp(−ell·h·(k+1−theta))，再乘真实 n 重同律产品 Measure.pi(Fin n→mu) 对事件 normalDeviation(q,z)=h·(k+1−theta) 的 real 质量。normalDeviation/Path 使用既有实际定义；这里是单个真实层概率的加权项，不是近似 Gaussian 或归一化条件律。任意 mu 的定义允许 .real 总化；定理必须由概率门保证有限，不能把该总化当作证明。

`exists_stage_positive_layer_tail_bound` 的完整量词为：固定真实实数概率测度 mu；固定自然阶段 J、实中心 q/a、实 ell>0；同一 mu-AE |x|≤4+sqrt(10)，同一 mu 的真实 E(normalValue)=q 与 EX=a；实际 normalVariance(mu)>0、实际 parabolaCovariance(mu).det>0；同一 mu-AE 支持于真实 stageAtom(Fin4⊕FinJ)、新增原子 addedAtom(j.val)，且每个活跃原子的 mu.real 单点质量>0。以上所有输入之后，存在一个实常数 C>0，并对自然 n 最终成立；在这个同一个 n 事件内部，对每个 theta∈闭区间[0,1]，有整个 k↦positiveNormalLayerTerm(mu,q,ell,dyadicMesh J,theta,n,k) 的真正 Summable，且对所有自然 K，真实无限尾级数 ∑'k term(K+k)≤C·exp(−ell·dyadicMesh J)^K/(1−exp(−ell·dyadicMesh J))。

C 及最终 n 阈值在全部 theta 和全部尾指标 K 之前；可依赖固定 mu/J/q/a/ell 及所给条件。Summable 不是仅写一个总化 tsum 不等式，也没有将 summability 放在结论之外当作假设。移位是 K+k，第一层位置是 h·(k+1−theta)，右侧 rho 的幂为 K。闭端 theta=1 使 k=0 的层是0；theta=0 的首层是h。J=0 仍是 h=1 的合法有限阶段。声明没有对 theta 所诱导的层加任何格点相容条件，必须使用对所有实 d 统一的真实质量界或直接处理零层质量；不能逐 theta/K 选 n 阈值。

独立可行性初判：若既有质量门给 sqrt(n)·mass(d)≤C0 对全部 d，则 ell>0、h>0 令 rho=exp(−ell h)∈(0,1)。theta≤1 给每项非负且≤C0 rho^k；因此真可和与移位几何尾界数学上合理，theta=1 为该统一上界的边界。此为仅从完整类型所作的数学推断；实际接口、真可积/有限质量、标准级数 API 与来源尚待后续核对。

本盲译先落盘，之后才读 scope/R1/实际前置及固定库。根 A/B/C/D、完整负层支配、完整 LLT 与 hW 保持 OPEN。

## 第二阶段：冻结范围、R1 对应和实际前置

盲译落盘后才读取完整 scope 和 R1。冻结 scope 两端实际 SHA256 均为 `6fd7a6124bf672404f31d658f01250987f9bcdef69020cbb47e5a388cc9527f5`。只审该冻结定义体和一个完整类型，未读未来实现或作者 API/笔记，未改冻结文本。

真实 R1 report.md SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，本次直接读第 309–365、380–444 行。第 390–392 行明确 positive layers 用标准 scalar sup_d P(M_n=d)≤C/sqrt(n) 并支持层求和；第 400–403 行真实相位网格是 h_J(ℤ−theta_nJ)，theta_nJ={nq/h_J}；第 421 行给真实似然权重 exp(−ell d)；精确“正层几何似然权重截尾”的来源是第 428–429 行。scope 把正层几何支配总括为“399–428”时，其完整文字实际上继续到429；本报告给出精确引用，不据此篡改 scope。

对真实源 theta∈[0,1) 而言，严格正层可重索引成 d=h(k+1−theta)、k≥0。当 theta=0 时，d=0 是单独的有限边界项，本定义从 d=h 开始，不重复计数。theta=1 只是所审闭区间统一包络额外保留的零层端点，不声称源的 fractional part 会等于1；它不影响真可和或几何尾界。当前定义没有 g_J(d) 或切向条件事件，因此只控制正/非负层绝对权重，不等于源(19)完整层和极限。

本次直接在指定服务器只读 actual `Shao/OQ3/NormalLayerMassBound.lean`：SHA256 `66ff4f217b57b319abb19ea7982e467e934219fadc2574a3487087e030a9e4f1`、281 行。其 `exists_stage_normal_layer_mass_bound` 完整公开接口第206–218行与本候选共同条件逐项相同，并给 ∃C0>0、最终 n、再∀d:ℝ 的真实产品层 real 质量界。它没有只给 bounded d、可达 d 或固定 d_n 的结果；无需重做 U16a 已接受的完整证明或构建。U16a 完整独立票 SHA256 `2ad0fb6fbfeb948653bc1e8cf6ac854395b896fed7fa281defcb8c29aca3cb6f` 已接受。

actual `dyadicMesh J=((2:ℝ)^J)⁻¹`（FiniteConstraints 第45行），故对所有自然 J 都严格正，J=0 时恰为1。真实 normalDeviation 是同一 Path n 的 ∑normalValue−nq，normalValue=8x−x²；未替换统计量或测度。本候选是有条件的固定实际阶段律接口，不为任意 q/a 断言概率存在。其 Measure.pi 是同一 mu 的真实 n 重产品；没有另选有限概率或独立的参数族。

## 第三阶段：完整数学、可和性与全部量词审查

从同一 U16a 接口一次性选择 C0>0 和最终 n 事件 Hn，使 Hn 内对全部实 d 有 sqrt(n)·mass(d)≤C0。C0 和这个事件不依赖 theta、k 或 K；本候选的 C 可以直接选这个 C0。设 h=dyadicMesh J>0、rho=exp(−ell h)。由 ell>0 得 −ell h<0，故 0<rho<1，特别是 |rho|<1 和 1−rho>0；右侧分母不是总化除零。

对任何 Hn 内的 n、theta∈[0,1] 和 k≥0，令 d=h(k+1−theta)。sqrt(n)≥0、exp(−ell d)>0，真实 measure.real 层质量≥0，故定义项 T(k)≥0。把 U16a 的真实任意 d 界乘 exp(−ell d)≥0，交换实乘法的结合顺序，得到 T(k)≤C0·exp(−ell d)。theta≤1 给 k+1−theta≥k；由于 h>0 且 ell>0，指数方向是 −ell d≤−ell h·k。因此 exp(−ell d)≤exp(−ell h·k)=rho^k；最终 0≤T(k)≤C0 rho^k。没有约掉 p、质量或 sqrt(n)，也不假定层质量严格正。theta 的下界保证源正层语义，但数学包络实际仅需 theta≤1，这种冗余合法。

先由 |rho|<1 得真实实几何级数 k↦rho^k 可和，常数倍 k↦C0 rho^k 亦可和；再由非负比较测试得到实际 T 的 Summable。这一步先于任何实 tsum 比较，不把 Lean 对不可和实级数返回0的总化约定当作收敛。

接着固定任意 K≥0。可用已建立的 Summable T 与自然移位同构得 k↦T(K+k) 可和，也可直接把同一逐项界用于 K+k，并用 pow_add 得 0≤T(K+k)≤(C0 rho^K)rho^k；后者的比较大项先由几何 HasSum 乘常数，真可和，于是移位小项同样真可和。两侧真实可和后，tsum 单调性给

`∑'k T(K+k) ≤ ∑'k (C0 rho^K)rho^k = (C0 rho^K)(1−rho)⁻¹ = C0 rho^K/(1−rho)`。

式中 K+k 与库常用 k+K 仅由自然数加法交换；rho^(K+k)=rho^K rho^k，K=0 的尾从原首项起，几何闭式仍正确。对于 theta=1、k=0，d=0、指数=1= rho^0；只用 U16a 给真实零层的同一界即可，既无严格正 d 的隐含前提，也不会导致 rho=1。对于 theta=0，首项的额外 rho 衰减只让上界更松，声明不要求最优常数。

n=0 时定义中 sqrt(0)=0，有限真实产品概率保证每项为0；声明只要求最终 n，因此不必输出 n=0 事件，且上述比较论证完全不除 sqrt(n)，不存在 n0 消去错误。J0、K0、theta 两闭端、任意 q/a、可达与不可达层均已涵盖。无需 theta 与 nq/h 的相位相容，因为所消费的 U16a 全部实 d 界已经含不可达层（其完整证明先证真实 ENNReal 质量零再转 real）。不得改用仅对可达层的渐近或逐 theta/K 另选 n 阈值。

最终事件内部可以任意 intro theta 后建立整个级数可和，再任意 intro K；没有把 ∀theta 或 ∀K 搬到 eventual 外，也没有依赖尾起点选 C。ell 已固定在存在 C 之前；虽 C0 可选得不依赖 ell，本声明允许 C 依赖 ell，不因此误称对 ell→0 或 J→∞ 一致的正尾界。

## 第四阶段：实际固定库、导入可见性和静态环境

所有 API 以下均从指定服务器固定 Mathlib 源码只读核对，没有 Lean/#check/probe。真实 mathlib git HEAD 为 `807d3836b165983210ee2ecf3cd28f239436949c`；lean-toolchain 文件 SHA256 `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`、lake-manifest.json SHA256 `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`，沿用既有 Lean v4.36.0-rc1 pin。当前工作树 branch `feat/oq3-positive-layer-tail`、HEAD `115ce0f27cd1c89330a232688c4ce060196d29a2`；报告绑定冻结输入及实际前置哈希，不把正在发布的其他单元状态当作本候选证明。

- `Mathlib/Analysis/SpecificLimits/Normed.lean` SHA256 `eee44dfd62feb67bdf3ccc6cf57e8e101f38a7408dbb9c6347e0978ce2010d41`，489–497 行：`hasSum_geometric_of_abs_lt_one`、`summable_geometric_of_abs_lt_one` 与 `tsum_geometric_of_abs_lt_one` 的真实门均为 |r|<1，和为 (1−r)⁻¹。这是实几何级数；本候选已由 ell,h 严格正满足门。
- `Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean` SHA256 `88ef56c969006630d0066b7af2c74e75dd060608f3c42f0ef288ad1c6da908cc`，532–537 行实际公开的 `Summable.of_nonneg_of_le {f g:β→ℝ} (hg:∀b,0≤g b) (hgf:∀b,g b≤f b) (hf:Summable f):Summable g`。虽然文件名含 ENNReal，这一 API 的参数和结论确为实数级数，不能误套 ENNReal 无条件可和。
- `Mathlib/Topology/Algebra/InfiniteSum/Order.lean` SHA256 `526aed3d15913b1d7ad9de9f28fc26ac9ab023942b0d80cbc72323a293817b01`，132–135 行 `@[to_additive]` 对 `Multipliable.tprod_le_tprod` 生成实际加法接口 `Summable.tsum_le_tsum`：逐项≤以及左右两个 Summable 后才能比较实 tsum；ℝ 的有序拓扑群门和无穷求和 filter 的 NeBot 均满足。本审查按该源码的生成语义核查，没有把 ENNReal.tsum_le_tsum 的无可和门错用到实数。
- `Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean` SHA256 `4dc1dffbdb6a0b0157e8810b20dfc0051bedf7f449b6d1fa5b8a9a47fa47f645`，220–225 行 to_additive 从 `multipliable_nat_add_iff` 生成 `summable_nat_add_iff`：Summable(k↦f(k+K))↔Summable f。它在实际拓扑交换群 ℝ 上适用；K+k 需明确交换，或使用前述直接移位比较完全绕过重索引 API。
- `Mathlib/Topology/Algebra/InfiniteSum/Ring.lean` SHA256 `bba1f8897f3b78060d4893ee3b47f8edf6f533d2adca7909305d0a42ee50c087`，37–47 行 `HasSum.mul_left`、`Summable.mul_left`，53–59 行真正带可和门的 `Summable.tsum_mul_left/right`，支持先真可和再常数因子求和。ℝ 的 T2Space 和标准求和滤子门满足。
- `Mathlib/Analysis/Complex/Exponential.lean` 实际234–235行 `Real.exp_nat_mul(x)(n):exp((n:ℝ)*x)=exp(x)^n`，306–318行实指数单调/exp_le_exp，337行 exp_lt_one_iff；实数乘法重排后，正指数权重和 rho^k 的恒等式完全吻合。没有改成 exp(−ell h)^((k+1−theta):ℝ) 等额外实幂。
- `Mathlib/MeasureTheory/Constructions/Pi.lean` SHA256 `bb89dee63d412cd1cc1f7f9fd7a81d64074139571960b2f0fcb66d8b763cd6ef`，303–313行实际有限 n 产品的 IsFiniteMeasure/IsProbabilityMeasure 实例。`Mathlib/MeasureTheory/Measure/Real.lean` SHA256 `1b9d1490fa5acbffc570eac67f465d3d6ab0520aa3e54464f7520d60d6619b8d`53行 measureReal_nonneg、65–66行有限质量下 ofReal_measureReal。因此候选结论的真实概率有限，非 top.toReal 伪零；层事件是连续有限多项式和 normalDeviation 的等位集，已有实际统计量和有限路径环境提供其标准可测性。

拟 imports 为 NormalLayerMassBound、SpecificLimits.Normed 和既有六 tactic 模块；它们各自既有 olean 均实际存在。实际只读 import 递归得到 25 份 Shao 前置（U16a 加其24份既有闭包），无缺失源码，U16a 哈希与已接受版本一致，其余既有闭包实际哈希保持一致。没有请求新缓存。

特别独立追踪了真正 public import 可见路径，而不是仅凭依赖文件存在推断：SpecificLimits.Normed → Analysis.Asymptotics.Lemmas → Analysis.Normed.Group.InfiniteSum → Topology.Algebra.InfiniteSum.ENNReal；随后经 ENNReal/NNReal.Lemmas 的 public import 可到 Ring、Order 和 NatInt。以上所需实比较/常数倍/移位 API 位于公开 section 或其 to_additive 生成的公开声明。Real.exp API 则从旧式 Shao 导入 NormalLayerConditionalLaw 后，经 CharacteristicFunction.Basic → BoundedContinuousFunctionChar → Complex.Circle → Trigonometric.Basic → SpecialFunctions.Exp → Complex.Trigonometric → Complex.Exponential 的实际公开路径可见；不是误称 SpecificLimits.Normed 单独公开导出所有指数 API。Pi 和 Measure.Real 同样沿该既有 Shao 导入的真实公开路径可见；上述 API 所在七个库模块的既有 olean 也全部实际存在。

namespace Shao.OQ3、open MeasureTheory Filter、open scoped BigOperators Matrix、noncomputable section 与实际 U16a 环境一致。完整冻结类型没有新矩阵范数、默认实 Lebesgue、未导入测度实例或隐式可积性表达式；新定义/结论只使用已导入实际统计量、Pi、real、sqrt/exp 和实 Summable/tsum。静态未发现作用域、实例、API 路径或缓存阻塞。这不是当前尚未实施单元的编译通过声明。

## 最终独立声明裁决

STATUS: CORRECT

JUSTIFICATION: 完整定义确为同一真实 n 重产品层质量的 sqrt(n)·exp(−ell d) 权重，完整类型保持一个 C>0 和同一个 eventual n 阈值在全部 theta∈[0,1] 与全部尾起点 K 之前。U16a 的真实全实 d 质量界、h>0 与 ell>0 给非负逐项几何大项；先真 Summable 再真实 tsum 比较，得到准确的 rho^K/(1−rho) 闭式且分母严格正。theta=1 的零层、theta=0 的源有限边界、J0、K0、n0 及不可达层均无缺口。对应 R1 正层 scalar 界与几何似然截尾，所需实际接口/公开导入和既有缓存已静态核对。未发现需要修改的声明、来源或静态环境问题，可进入独立实现阶段；本票不是实现或内核/Audit 验收。

非声明：没有负层 Chernoff/率二次下界、紧倾斜族统一常数、完整负层支配、完整(19)或 LLT、条件 Lévy、hW、尖点 Euler–Maclaurin、全局最小化、最优性或新颖性结论。根 A/B/C/D、完整负层支配、完整 LLT、hW 均 OPEN。没有运行任何 Lean/API probe/构建，没有编辑实现/scope/旧票/共享文件或缓存。
