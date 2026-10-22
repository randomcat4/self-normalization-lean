# U13b FundamentalFourierAsymptotic 独立声明与来源审查

STATUS: CORRECT

仅声明/source gate，尚无本单元实现。reviewer lease 1，不 spawn、不运行 Lean/API 探针、不构建、不改作者源/旧票/共享文件/缓存。本新报告及获授权远端 `runs/oq3/u13b-20261021/statement-review.md` 为唯一写入对象。

## 1. 冻结 Lean 代码块先行盲译

本节只读取 `thirtieth-unit-scope.md` 的 Lean fence，SHA256 `27228084fa1bb342c2c689af67b89ecee74d5e46c36816cab9fdb1c8597a5783`；未读 scope 说明、R1 或本轮库 API。以下三完整类型的独立数学翻译先落盘，再作来源及环境判断。无新定义。

共同记号：μ 是 ℝ 上的真实概率；Y=normalValue，S=normalVariance μ，D=det(parabolaCovariance μ)，T=transverseVariance μ，χ(t,u)=centeredNormalTangentCharacteristic μ q a t u，h_J=dyadicMesh J。记号的真实定义、默认 volume 和中心含义将在下一阶段读取实际前置核对，不仅按名字接受。

1. **`exists_centralFourierIntegral_tendsto_below`**：给 μ 概率、μ-AE `|X|≤4+sqrt10`、实 q,a 满足真实积分 EY=q、EX=a，且 S>0、D>0。对任意给定 H>0，存在一个实 δ，0<δ<H；这个 δ 在**全部**实 s 和实序列 d 之前选定。对每个 s,d，只要 d 全序列有一个统一实界（∃M，∀n，|d_n|≤M），真实 volume 下 `centralFourierIntegrand μ q a δ s d n` 的全实轴复积分趋向实高斯常数 `sqrt(2π/S)·exp(−T s²/2)` 的复嵌入。没有要求 d_n 收敛，也没有把 δ 交给 s/d 后逐个选择。
2. **`stage_fundamentalFourierIntegral_tendsto`**：μ 概率，给固定自然数 J、q,a、上述真实 AE 有界/均值/S,D 正门；另要求 μ-AE 位于真实活跃阶段点 `stageAtom(addedAtom|Fin J)` 的 Fin4⊕FinJ 像中，且这每个阶段点的真实单点质量 μ.real{x} 严格正。对每个实 s 与全序列有界 d，

   `sqrt n · ∫_{[-π/h_J,π/h_J]} exp(−i t d_n) · χ(t,s/sqrt n)^n dt`

   趋向同一 `sqrt(2π/S)·exp(−T s²/2)`。这是未乘 h_J/(2π) 的完整基本区间 Fourier 积分极限，使用真实 μ、所有 n 的表达式和自然数 atTop；类型没有 n>0 前提或对 n=0 做分母消去。J=0 包含；严格正质量只要求这个有限活跃索引，而不是全部无限 AtomicIndex。
3. **`stage_normalLayerCharacteristic_scaled_tendsto`**：同一 μ、J、q,a、支持、各活跃点严格正质量、真实均值与 S,D 正门，以及固定 s 和全序列有界 d；额外仅要求**最终** n 满足格点层相容 `d_n+nq∈h_Jℤ`。则同一 μ 的未归一化层特征积分 `sqrt n·normalLayerCharacteristic μ q a d_n s n` 趋向

   `(h_J/(2π))·sqrt(2π/S)·exp(−T s²/2)`

   的复嵌入。它不要求所有初始 n 相容、不要求层质量正、不作条件概率除法。格点归一化系数 h_J/(2π) 只在此层目标出现。目标未含条件特征函数、连续集概率收敛或 Lévy/LLT/hW 的结论。

盲译先行阶段尚未判断定理可证性、scope/source 匹配或静态导入可见性。根 A/B/C/D 保持 OPEN。

## 2. 冻结说明与真实来源

盲译落盘后才读取冻结说明、真实 R1 309–345 及实际前置。本地 scope 与远端 run/scope.md 实际 SHA256 均为 `27228084fa1bb342c2c689af67b89ecee74d5e46c36816cab9fdb1c8597a5783`。拟文件为 FundamentalFourierAsymptotic，公开 imports 为 CentralFourierIntegral、NormalLayerFourier、Mathlib.Analysis.SpecificLimits.Normed；namespace Shao.OQ3，open MeasureTheory Filter，scoped BigOperators Matrix，noncomputable。冻结对象确为零定义、三完整目标，盲译与其余说明相符。

真实 R1 原件 SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662` 已核。318–319 的 M_n、R_n，335–337 的同一 μ 中心联合特征 n 次幂，339–344 的远弧收缩/中心高斯积分，与本单元的三个目标对应。第一目标加强已有中心积分结果的半径选择；第二目标组合中心和远弧得到真实基本区间积分渐近；第三目标再经已审的精确层反演插入格距归一化。没有把第三目标误写为 R1 的完整连续集概率极限 (15)，没有把有限样本积分形式直接称为条件概率特征函数。

实际定义核对：`normalValue x=8x−x²`；`parabolaCovariance μ` 是实际 (X,X²) 协方差矩阵；S=真实 Var_μ(Y)，D=该矩阵真实行列式，transverseVariance=D/S，代表 τ² 而非 τ。实际 NormalTangentGaussian 的 `normal_tangent_covariance_det` 给 `S Var(X)−Cov(Y,X)²=D`，因此 hS、hD 与来源 (Y,X) 正定协方差一致；不是仅凭任意矩阵 det>0 声称正定。AE 紧界保证实际多项式矩真可积、L² 门真实成立，前置 U7/U12b 的方差协方差公式没有借总化 variance 规避可积。

真实 `centralFourierIntegrand` 是增长 Icc 窗口的指标乘以 `exp(−iv d_n/sqrt n) χ(v/sqrt n,s/sqrt n)^n`；真实 `normalLayerCharacteristic` 是 μ^Fin n 上的未归一化层 indicator 相位积分。第三目标 μ、q、a、d_n、s、n 与第二目标和 U13a 反演全部相同。三个目标没有引入另一组 p/q 或选择新 law；一般阶段概率 μ 的存在、均值和正协方差由显式假设提供，不是对任意 q 的概率存在性主张。

## 3. 实际前置、固定库及数学可行性

### 3.1 目标一：共同半径可以严格压在任意 H 以下

已审实际 U12f `exists_centralFourierIntegral_tendsto` 只给一个存在半径，不能从“在该窗口积分收敛”直接推出任意较小窗口也收敛。本候选明确增加一个新目标，数学上可由实际 U12e 支配与 U12f 点态结论重新建立：

从实际 `exists_centeredNormalTangentCharacteristic_scaled_domination` 取得 δ₀,c>0；其量词为 **δ₀,c 在所有 s 之前，固定 s 后 ∀ᶠn、再 ∀v**。取 δ=min(δ₀,H/2)，则 0<δ<H，且 δ≤δ₀；δ 只依赖 μ、q,a、已有矩门及 H，在所有 s/d 之前。因 sqrt n≥0，δ 窗口包含于 δ₀ 窗口，故保留同一 c 和同一固定 s 的 eventual N(s)，不对 v 或 d 重新选择阈值。

对每个 s,d：U12f `centralFourierIntegrand_integrable` 给每一 n 的真实可积和强可测；窗口内相位范数 1，U12e 给范数≤exp(−cv²)，窗口外指标为 0，同一 Gaussian 在全实轴真正可积。U12f `centralFourierIntegrand_tendsto` 对**任意正 δ**已有真实点态结论；其 d 假设正好是本目标的显式全序列界，d_n/sqrt n→0 不需 d_n 收敛，固定 v 最终落入增长窗口。于是 filter DCT 的 eventual 可测、eventual AE 支配、支配函数可积、AE 点态四门齐全；Nat atTop 有可数基。不冒称该支配对所有初始 n 都成立。

极限 integrand 为 exp(−Q(v,s)/2) 的复嵌入。实际 U12b 给真 Gaussian 可积以及积分值 `sqrt(2π/S) exp(−(D/S)s²/2)`；实到复积分线性转换与同一 volume 相容。hD 用于 U12e coercivity，hS 用于正 Gaussian 域；本目标没有隐藏对 sqrt 或逆的非零假设。共同半径量词及任意 H>0 的严格性可以真实兑现。

### 3.2 目标二：基本区间的中心与远弧组合

记 h=mesh_J=(2^J)⁻¹>0，H=π/h>0，B=[−H,H]。先用目标一选共同 0<δ<H，再取 C=[−δ,δ]⊂B。对固定 s,d 和每一 n，实际

`f_n(t)=exp(−it d_n) χ(t,(sqrt n)⁻¹s)^n`

由实际 char 对 (t,u) 连续而连续，范数有限；f_n 在真实 Lebesgue 紧 B、C 上均真正 IntegrableOn，限制到 B\C 也真可积。这些结论先于任何集合分解或换元；不是在全实轴仅用 norm≤1 假装可积。

**集合分解**：用 `setIntegral_sdiff` 对可测 C、真实 IntegrableOn B 和 C⊂B，精确取得 `∫_B f_n=∫_C f_n+∫_{B\C}f_n`。选紧远弧包络 K=[−H,−δ]∪[δ,H]，它不含 0，且 |t|≤H；B\C⊂K。此法不把 C 与闭 K 的两个共用端点双计；若实现采用两闭远弧直接相加，也必须用 Lebesgue 单点为零去掉 ±δ 的重叠。两种均可由现有 API 实现。

**带实际层相位的远弧**：hrange 与每个活跃 Fin4⊕FinJ 单点真正质量 hpos 正好满足 U12a `stage_far_arc_uniform`。其给 η>0、0<ρ<1，统一控制 K 上所有 t 以及 |u|<η 的实际 χ(t,u)。固定 s 后 `(sqrt n)⁻¹s→0`，从而最终 |u_n|<η，阈值在全部 t 外；d 仅进入 norm=1 的相位，不能改变此界。显式重做

`‖f_n(t)‖=‖χ(t,u_n)‖^n≤ρ^n`（t∈B\C）

再用真实有限体积积分估计得到 `‖∫_{B\C} f_n‖≤volume.real(B\C)ρ^n`。不能从 U12a **无层相位的积分**界推出此界，也不能声称 `‖∫phase·g‖≤‖∫g‖`；这里需要、且可得到的是共同 pointwise χ 界。B\C 的有限体积由其包含于紧 B 获得，真实可积另已成立。

因 0<ρ<1，固定库给 nρ^n→0 与 ρ^n→0；0≤sqrt n≤n+1，故 sqrt n·ρ^n→0。乘固定有限体积，再取复值 norm 夹逼，得到**缩放后**远弧趋 0。只给“ρ^n→0”而忽略 sqrt n 不是充分验证；本候选所需加强已有缓存支持。

**真实中心换元**：只在最终 n≥1 后取 b=sqrt n>0，所以 b≠0。增长窗口上的真实 U12f integrand 为 f_n(v/b)，其区间为 [−δb,δb]。固定库的实变量/复值 `intervalIntegral.integral_comp_div` 精确给

`∫_{[−δb,δb]} f_n(v/b) dv = b • ∫_{[−δ,δ]} f_n(t)dt`。

以 Icc→Ioc 的 AE 等式和端点有序性转为有向积分，消 b 的步骤使用 b≠0；复值实数 smul 正是 `(sqrt n:ℂ)` 的乘法。左侧正是全实轴 indicator 的 centralFourierIntegrand 积分，且相位是 −v d_n/b、切向频率仍为 s/b。没有把换元 Jacobian 倒置成 1/b，也没有丢掉相位或误将 χ 频率改成 s。先有真可积，再用现有换元公式，不以其对总化积分也成立作为积分存在性的理由。

于是目标一的中心极限加缩放远弧 0，正好得到目标二没有 h/(2π) 的常数。目标二未要求 hlayer 是正确的：此时只讨论实际 Fourier 积分，任意 bounded d 的相位均合法，尚不把它解释成层概率。

### 3.3 目标三：最终相容层与精确归一化

由真实 hrange 在 μ-AE 事件上取 stageAtom，然后实际 U8 `stageAtom_normalValue_lattice` 给 Y(x)∈h_Jℤ；不需对无限未来零权点假设正质量。h_J>0 包括 J=0。将 `hlayer` 的 eventual n 与该固定单坐标 hgrid 配合，逐个最终 n 使用 U13a `normal_layer_Fourier_identity`，得到真实同一层 integral 恰为 `(h_J/(2π))∫_B f_n`。U13a 先证明真实有限概率产品联合可积后才 Fubini 的门已经完整独立审查，本候选没有另外假定未经证明的样本积分换序。

只需 eventual 相等即可传递 Tendsto，无需所有初始 n 层相容；再乘固定正 h_J/(2π)，与 sqrt n 的复标量交换得到目标三的精确常数。S>0 下该常数等于来源的 `h_J/(sqrt(2π) sqrt S)·exp(−τ²s²/2)`；冻结式保持原始 h/(2π) 来源，不额外依赖根式化简。没有以层质量为分母、没有使用正层概率、没有偷加入“所有 n 可达”或把相容当作实际可达。

### 3.4 边界、同一参数及范围

J=0：实际 mesh0=1，活跃点只有 Fin4 基点，Y 整数且实际 U12a 基本区间端点仍严格收缩，候选全部适用；没有 J>0 隐藏门。hpos 只在有限活跃支撑上，正确保留 U12a 最大性所需的实际正单点条件，不能用只非负的任意有限 law 替代。hrange/hpos 之外还明确给 hb、真实均值、hS/hD，没有从有限支持或任意 det>0 猜测这些条件。

n=0：sqrt0、其逆和所有积分定义均总化但实际紧区间函数连续可积；幂 0 为 1。第二/第三序列在 n=0 的缩放因子是 0，极限不受有限初项影响。所需 sqrt 消去只在最终 n≥1，绝不把 n=0 的换元写成可逆缩放。hd 是**全序列有界**的显式输入，不把来源 O(1) 的有限初项补界隐藏进类型；不要求 d_n 收敛或单调。层相位对所有 d 的模长 1；d 的界真正用于中心点态相位趋 1。

μ、q,a、J 在所有 n 中固定，所有 char、矩、中心、支持、正单点门与层积分均针对该同一 μ。后续若实例化实际 finiteMass，须从此前同源有限概率/中心/正活跃原子结论提供这些门；本候选没有重新选择一族 law，也没有直接声称任意非负 finiteMass 都有最大格距。

## 4. 环境与交付绑定

静态只读实际服务器 source/API/cache；没有运行 Lean、#check、API 探针或任何构建。本单元尚无 implementation 或 author receipt/Audit，本票不把声明可行性当作成功 elaboration/内核证明。

拟 imports 的真实可见链独立按 public imports 核验：

- CentralFourierIntegral → DominatedConvergence → IntervalIntegral.Basic → Bochner.ContinuousLinearMap → Bochner.Set，故 filter DCT、区间换元与 setIntegral_sdiff 均可见。
- NormalLayerFourier → FiniteFarArc → Lebesgue.Basic，故 ℝ 的 actual volume、单点零和有限区间体积实例可见；各目标 Fourier 积分还显式标出 `(volume : Measure ℝ)`。
- Analysis.SpecificLimits.Normed → SpecificLimits.Basic，故 nρ^n 与 ρ^n 衰减接口均可见。namespace/open/scoped 与三个冻结类型所用 Filter、BigOperators、Matrix 对应，无新 norm 或 MeasureSpace 实例歧义。

实际缓存只读确认存在：SpecificLimits.Normed.olean 276240 bytes；DominatedConvergence.olean 134976；IntervalIntegral.Basic.olean 565224；Bochner.Set.olean 430504；CentralFourierIntegral.olean 185848；NormalLayerFourier.olean 592824。未写缓存。

| 固定库实际 API | 核对内容 | 源 SHA256 |
|---|---|---|
| DominatedConvergence:68–75 `tendsto_integral_filter_of_dominated_convergence` | countably generated filter、eventual AEStronglyMeasurable、eventual AE 界、真实可积 bound、AE 点态四门，允许只最终支配 | `56394aacfe591230d26a1d93641f2a1d3e3a3eae4fcfe772775533a1da295833` |
| IntervalIntegral.Basic:942–944 `intervalIntegral.integral_comp_div` | c≠0；实变量复值 Bochner 积分，右端 c•integral，不是 c⁻¹；Icc/Ioc 转换及实 smul 可用 | `bf8558a4cb789e3505cfb08a6712ce83017719be2523e862d5e52f082433814c` |
| Bochner.Set:96–98 `setIntegral_sdiff`；609–611 `norm_setIntegral_le_of_norm_le_const` | 可测中心、真 IntegrableOn 外区间、子集关系；有限体积及真实 pointwise bound | `e4d90b9fde463a9123e1ac3321ce25c0714e19ce92e172f297e062d9de16be75` |
| SpecificLimits.Normed:215–217 `tendsto_self_mul_const_pow_of_lt_one` | 0≤ρ<1 → nρ^n→0；不是只给未缩放 ρ^n→0 | `eee44dfd62feb67bdf3ccc6cf57e8e101f38a7408dbb9c6347e0978ce2010d41` |
| SpecificLimits.Basic:189–198 `tendsto_pow_atTop_nhds_zero_of_lt_one` | 0≤ρ<1 → ρ^n→0，配合上一条和 sqrt n≤n+1 | `7a5d61c23552efa7618812a47172581188948b067b59ec581f18e517b819c969` |

没有误把 VectorMeasure 中的同名积分 API 当成这里的普通复值 Bochner API；上表实际查的是 MeasureTheory.Integral 相应源。

沿已独立审查的实际 import 链识别承重前置，本次重读了上文使用的真实定义、完整签名和中心 DCT/远弧/Gaussian 关键证明；下表各源的本地实际 hash 与远端工作树逐项相同：

| 实际项目前置 | SHA256 |
|---|---|
| CentralFourierIntegral | `4999d8148c1ee1ba50f61d6d19c40aed239cd001d76ee71f133d1a064c668a93` |
| NormalLayerFourier | `063b6c5ce50e6c5ee33b53301cdfcd36a63a4ea06f9c3de729756513ca736fa3` |
| NormalTangentDomination | `b65b9f5a9d67e42e611a3841563ac07004e796415c3e5b74f177a8ca80e48e90` |
| NormalTangentPowerLimit | `819bd0e801eb0b9adce0fbdbcd6ced6441b04787eb0501b811721933db0e9457` |
| NormalTangentGaussian | `d2c55bf4d7a371c9b43cd3c75eab8ece8b3c7caa21aa4827bf19c24b4c7cac39` |
| RegularCovariance | `0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853` |
| FiniteFarArc | `3a0b05d0789e53320009a44499c9c40d0fb3d892427085052c65c04456b6cf71` |
| FiniteNormalSpan | `0374da4860edf8af8bbbb9172e4e93bfe9b6c37ac57672b85a4f58392475b7de` |

实际 lean-toolchain 为 `leanprover/lean4:v4.36.0-rc1`；manifest mathlib rev 与真实 mathlib git HEAD 均为 `807d3836b165983210ee2ecf3cd28f239436949c`。这些是静态文件/git 读取，不是任何新目标检查的成功凭据。本票不读取未来作者 implementation/API/frontier notes；没有 receipt 或构建绿灯可供借用。

## JUSTIFICATION

**STATUS: CORRECT。** 三个冻结完整类型在实际前置与固定静态环境下数学上可行、来源/系数/量词正确，没有发现需要修订的声明缺口。首目标确实需要从 U12e 缩窗后重做 filter DCT，不能仅消费 U12f 的一个存在半径；第二目标有可兑现的真可积集合分解、最终正 sqrt 换元、共同远弧 pointwise 收缩和缩放幂衰减；第三目标在显式 eventual 格点相容门后消费 U13a 精确反演，保持同一 μ 与 h/(2π) 归一化。

这是**声明/source gate 准许**，尚未审查或声称存在本单元 Lean 实现、实际 target 类型输出、内核构建或作者公理门。实现仍须独立完整 proof/source/actual TYPE/机械审查。没有条件概率商、Lévy、完整混合 LLT、实际 hW 或根闭合主张；根 A/B/C/D 全部 **OPEN**。

本地交付 `drafts/oq3/u13b-statement-review.md`，授权远端 `runs/oq3/u13b-20261021/statement-review.md`；最终两端 SHA256 随交付独立核验。未改作者源、旧票、共享文件或缓存，未 spawn、运行 Lean/API 探针、构建、commit 或 PR。
