# U16a 独立声明与来源审查

STATUS: CORRECT

本票仅审冻结声明/source/environment，尚无实现。唯一审查 lease 1，仅拥有本报告和服务器对应 statement-review.md，不改 scope、源码、旧票、共享文件或缓存，不 spawn、Lean/API probe 或构建。根 A/B/C/D、layer domination/full LLT/hW 均保持 OPEN。

## 第一阶段：仅精确 Lean fence 的完整公开类型盲译

输入 thirty-seventh-unit-scope.md，SHA256 eed86bfa8689c61dcf9d3747f3f3ec3d023d77950517a473cce6073bed40c083。只提取精确代码块；零定义、两个完整公开目标。本节在读取 scope 说明、真实来源或证明路线/API 之前独立写入。

两个目标共享全部前提：mu 为实数上的真实概率测度；固定自然数阶段 J 和实中心 q,a；mu-AE |x|≤4+sqrt10；实际 normalValue 的积分=q、实际 X 的积分=a；实际 normalVariance(mu)>0，实际 parabolaCovariance(mu) 的行列式>0；mu-AE x 属于真实有限 stageAtom族 Fin4⊕FinJ 的值域，其中新增点用 addedAtom(j.val)；每个活跃索引对应真实单点的 mu.real 质量严格正。J=0 被允许（只剩四个基点），没有对全无限索引或未激活原子假定正质量。mu,J,q,a 都固定；未对紧倾斜族声称统一。

1. `exists_stage_normal_power_norm_integral_bound`：在上述完整前提下，存在一个实数 C>0，使对自然数 n 趋于无穷最终成立：sqrt(n) 乘实际实 Lebesgue 测度下、基本闭区间 [−pi/dyadicMesh J,pi/dyadicMesh J] 上的实积分，其被积函数为实际 centeredNormalTangentCharacteristic(mu,q,a,t,0) 的 n 次幂的复范数，≤C。是真正范数积分而非复积分的范数；没有层偏移 d 参数或依靠复相消的声明。所取 C/最终阈值可依赖固定 mu,J,q,a，但须在 n 外。

2. `exists_stage_normal_layer_mass_bound`：同一完整前提下，存在一个实数 C>0，使自然数 n 最终满足：对所有实数 d，sqrt(n) 乘真实 n 重同律产品 Measure.pi(Fin n→mu) 的层事件 {z:Shao.Path n | normalDeviation q z=d} 的 real 质量≤C。同一 C 和最终 n 阈值在全部实 d 之前；不要求 d 有界、收敛或满足格点条件。对离网格 d 也必须成立，不能把无法识别的复积分相消当概率零。n=0 不要求由本 eventual 声明覆盖，但证明最终除 sqrt n 时须明确进入 n>0。

待核：实际有限支持与正原子门、真实中心/协方差语义、范数积分的真可积性与 Gaussian/远弧支配、准确 sqrt n 换元、精确反演及离网格层的真实 ENNReal 零质量。此盲译不预设正确结论，也不把层上界称为完整 LLT。


## 第二阶段：冻结来源、范围和实际接口

盲译落盘后才读取完整 scope、真实 R1 和实际接口。scope 本地与指定服务器 run/u16a-20261021/scope.md 的实际 SHA256 均为 `eed86bfa8689c61dcf9d3747f3f3ec3d023d77950517a473cce6073bed40c083`。实际 R1 SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，已直接读取第 309–348、348–391、400–410 行。

R1 第 314–343 行的固定有界有限律、真实 EY=q、EX=a、正定协方差、最大格距和中心 Gaussian/远弧收缩对应候选输入；第 390–391 行明确给出正层使用的标准 scalar `sup_d P(M_n=d)≤C/sqrt n`。这里准确引用 390–391 行，而不是把它放在 390 行之前。第 357–358 行的紧倾斜参数集一致性是更强的后续目标，本声明仅对已固定 mu,J,q,a 产出 C 与阈值；不能据此证明参数族统一性。候选未声称 R1 (16)/(17)、(15) 的完整混合极限或 hW。

实际 normalValue(x)=8x−x²；normalDeviation q z=∑ normalValue(z_i)−nq；dyadicMesh J=(2^J)⁻¹>0（J=0 时为 1）。stageAtom_normalValue_lattice 和 stage_sample_normal_layer 使用的是同一实际有限 stageAtom(Fin4⊕FinJ)、同一个 addedAtom(j.val)，没有索引平移混用。实际 normalVariance 是 Var_mu(normalValue)，parabolaCovariance 是 (X,X²) 的真实方差/协方差矩阵；hb 给全部这些多项式真正 L²/可积，原已审 NormalTangentGaussian 将 (Y,X) 协方差与它绑定。hS/hD 不是任意矩阵正行列式假设；它们是实际概率协方差数据的正性门，正好可供已审 Gaussian 支配接口消费。

已从指定服务器直接读取相关完整类型、定义与真实散列：

- NormalTangentDomination.lean SHA256 `b65b9f5a9d67e42e611a3841563ac07004e796415c3e5b74f177a8ca80e48e90`，实际 scaled_domination 给 ∃delta,c>0，∀s，最终 n 后∀v，|v|≤delta sqrt n⇒‖χ(mu,q,a,(sqrt n)⁻¹v,(sqrt n)⁻¹s)^n‖≤exp(−cv²)。阈值在全部 v 外。
- FiniteFarArc.lean SHA256 `3a0b05d0789e53320009a44499c9c40d0fb3d892427085052c65c04456b6cf71`，实际 stage_far_arc_uniform 消费完全相同的 hrange/hpos 与任意紧 K、不含 0、|t|≤pi/h，给 eta>0、0<rho<1，∀t∈K、|s|<eta 时‖χ(t,s)‖<rho。闭基本区间端点允许；q,a 可任意中心。它还公开给 χ 的真实联合连续性。
- CentralFourierIntegral.lean SHA256 `4999d8148c1ee1ba50f61d6d19c40aed239cd001d76ee71f133d1a064c668a93`，实际 centralFourierIntegrand 是增长 Icc 窗口的 indicator、单位相位和实际 χ 缩放幂的乘积；centralFourierIntegrand_integrable 对任意 delta,s,d,n 真正可积。这里消费该公共可积接口，不把复积分的极限当成范数积分界。
- NormalLayerFourier.lean SHA256 `063b6c5ce50e6c5ee33b53301cdfcd36a63a4ea06f9c3de729756513ca736fa3`，实际 normal_layer_Fourier_identity 的门是 h>0、mu-AE Y∈hℤ，以及 `∃k:ℤ,d+nq=h*k`。右侧精确系数 h/(2pi)、负相位 exp(−itd)、χ(t,(sqrt n)⁻¹s)^n 的真实 Lebesgue 基本区间积分。
- NormalLayerConditionalLaw.lean SHA256 `94e2507a83dfc232280043567f6a2f07950d39da10b45699777ac1316f24281a`，公开 normalLayerCharacteristic_zero_eq_mass 对任意 n,q,a,d 给 s=0 的层特征积分等于真实 n 重产品层 real 质量的复嵌入；不是条件律零质量 Dirac 补定义。
- SampleBoundary.lean 实际 SHA256 `7660e23b71ce28ab43a4ad1d8df1862cf8a507b6bb9b41255e961f0bee0b93e2`，实际 stage_sample_normal_layer 是纯样本结论：若全部坐标属于同一阶段值域，则 ∃k，normalDeviation q z=h*k−nq。
- FiniteNormalSpan.lean 实际 SHA256 `0374da4860edf8af8bbbb9172e4e93bfe9b6c37ac57672b85a4f58392475b7de`，stageAtom_normalValue_lattice 对每个活跃索引给真实 hℤ 支撑。J=0 仍是四基点，不要求不存在的新增原子或 J>0。

这些是当前实际可用公开接口，不调用前置 private 变元替换或支撑辅助，不读取未来实现/作者 notes，也不重编旧已接受目标。

## 第三阶段：第一目标的独立数学及积分门

令 h=dyadicMesh J>0，H=pi/h>0，T=Icc(−H,H)。写 φ(t)=χ(mu,q,a,t,0)。固定 n 时 φ(t)^n 及其范数连续，故在有限 Lebesgue 区间 T 和下列可测子集上真正可积。

从实际 U12e scaled_domination 取 delta0,c>0；令 delta=min(delta0,H/2)>0，故 delta<H，中心 C0=Icc(−delta,delta) 真包含在 T。这里不假定旧 U12f 的某个存在 delta 自动小于 H，而是从实际 Gaussian 支配窗口合法缩窗。将实际支配接口取 s=0，得到一个最终阈值，在全部实 v 外；此后 |v|≤delta sqrt n 时缩放模幂≤exp(−cv²)。另外相交 n≥1，保证 sqrt n>0 及非零。

取实际可积 g_n(v)=centralFourierIntegrand(mu,q,a,delta,0,(fun _=>0),n,v)。相位此时为 1，窗外 g_n=0；norm g_n 真可积。窗内用上述支配，窗外 0≤Gaussian，故对所有 v 有 ‖g_n(v)‖≤exp(−cv²)。c>0 给真正 integrable_exp_neg_mul_sq；实积分单调性在两侧真正可积后给

`∫ℝ ‖g_n(v)‖dv ≤ G := ∫ℝ exp(−cv²)dv`，G 有限且非负。

必须重新建立以下范数的实变元替换，不能从任何复积分收敛倒推它：

`∫ℝ ‖g_n(v)‖dv = sqrt n · ∫_{−delta}^{delta} ‖φ(t)^n‖dt`。

该等式有明确可用的标准 API 路线：按 indicator 两种成员情况把 norm g_n 化为 Icc 窗口 indicator 的实函数 `f(v/sqrt n)`，其中 f(t)=‖φ(t)^n‖；以 integral_indicator 改为窗口 setIntegral，真实 Lebesgue 零端点给 Icc=Ioc；在 n≥1 下用 intervalIntegral.integral_comp_div、c=sqrt n≠0，将区间 [−delta sqrt n,delta sqrt n] 的积分精确变成 sqrt n 乘 [−delta,delta] 的积分。正 sqrt n 同时保证端点顺序与两端除法合法。函数在所有所用有限闭区间连续，故所有实积分真正可积，Jacobian 是 sqrt n 而不是其逆数。该路线不需前置 private lemma。

远区 E=T\C0 包含于紧 K=Icc(−H,−delta)∪Icc(delta,H)。delta>0 给 0∉K，K 上 |t|≤H；实际 stage_far_arc_uniform 在这些真实有限正单点门下给 eta>0、0<rho<1。取 s=0，0<eta 满足窗口，全部 t∈E 有 ‖φ(t)‖<rho，故全部 n 有 ‖φ(t)^n‖≤rho^n。E 可测且 Lebesgue 体积有限，连续范数幂在 E 真可积，实积分比较给

`∫E ‖φ(t)^n‖dt ≤ volume.real(E)·rho^n`。

0≤sqrt n≤n+1；实际 n*rho^n→0 和 rho^n→0 给 sqrt n*rho^n→0，乘固定有限 volume.real(E) 后仍趋零。因此最终缩放远区积分≤1，阈值只依赖固定 law/J 与所选 delta,rho。实际 setIntegral_sdiff 在 C0 可测、C0⊆T、f_n IntegrableOn T 下精确分解 T 的实范数积分；两部分相加给最终 sqrt n∫T‖φ^n‖≤G+1。C=G+1>0，第一目标成立。没有依赖复相消或尚未证明的紧参数一致界。

## 第四阶段：全部真实 d 的层质量与离网格情形

第一目标给 C1>0 及一个最终阈值。第二目标采用 C2=h/(2pi)·C1>0，并与 n≥1 相交；此阈值在任何 d 之前固定。对该阈值后的任意实 d，分下列两种情况，两个分支都不引入 d 相关阈值。

**格点相容 d。** hrange 与 stageAtom_normalValue_lattice 先给 mu-AE Y∈hℤ；若 ∃k，d+nq=h*k，则实际 normal_layer_Fourier_identity 可在 s=0 应用，且 normalLayerCharacteristic_zero_eq_mass 把左边识别为真正产品层质量的复嵌入。层的 real 质量非负，产品概率保证它真正有限；复嵌入范数恰是该质量。单位相位 exp(−itd) 的范数为 1，对任意实 d 均成立。χ^n 和相位连续，乘积在固定有限 T 真正可积，norm_integral_le_integral_norm 因而给

`P_mu^n(layer d) ≤ h/(2pi) · ∫T ‖φ(t)^n‖dt`。

乘非负 sqrt n，使用第一目标同一 n 事件即可得 C2。没有调用仅允许 bounded d_n 的 U13b 渐近结果来冒充所有实 d 的统一界，也没有 d 收敛/有界假设。

**离网格 d。** 若不存在上述整数 k，先在真实 ENNReal 测度层面证明零质量。每个坐标的 hrange 可经真实 finite-product 的 evaluation AE/零集 API 提升到 n 重产品；有限多个坐标的 AE 交仍为 AE。于是实际 stage_sample_normal_layer 对 AE 样本 z 给 ∃k，normalDeviation q z=h*k−nq。任何满足 normalDeviation q z=d 的样本都与离网格假设矛盾；层事件因此包含于上述 AE 支撑的真实零补集。由 measure_mono_null 得

`(Measure.pi(fun _:Fin n=>mu)) {z | normalDeviation q z=d}=0 : ℝ≥0∞`。

之后才用 real/toReal_zero 得真实 real 质量为零。没有从一个复积分等于零反推概率零，也不使用 top.toReal=0。normalDeviation 是有限和多项式，层事件闭/可测；即便直接用零集包含的单调性，也不存在可测性偷换。真实 pi 概率性覆盖 Fin n（包括空坐标集），而本最终事件中的 n≥1 已明确允许除 sqrt n。

因此同一个 N 对所有实 d 有界，正是 `∀ᶠ n, ∀ d`，而非 `∀ d, ∀ᶠ n`。J=0 的有限支持和 h=1 仍符合全部 stage/lattice/远弧接口；不存在 J>0 或所有无限原子正质量的隐藏假设。

## 第五阶段：实际固定库 API、公开路径与缓存

全部核查通过共享 server.py 只读文件/散列/导入图完成，无 Lean、API probe、构建或 cache 写入。拟环境为 NormalLayerConditionalLaw、显式 SpecificLimits.Normed 和六个既有 tactic 分模块，open MeasureTheory Filter、open scoped BigOperators Matrix。真实 Lebesgue 实测度由已有导入明确提供，积分类型里也显式写 volume:Measure ℝ。

- IntervalIntegral/Basic.lean 实际 SHA256 `bf8558a4cb789e3505cfb08a6712ce83017719be2523e862d5e52f082433814c`，942–944 行 intervalIntegral.integral_comp_div 要求 c≠0，结果是 `∫a..b f(x/c)=c•∫a/c..b/c f`；这里 c=sqrt n>0，缩放方向正确。
- Bochner/Set.lean 实际 SHA256 `e4d90b9fde463a9123e1ac3321ce25c0714e19ce92e172f297e062d9de16be75`，96–98 行 setIntegral_sdiff 要求被减集可测、原集上真可积及包含；181–183 行 integral_indicator；699–700 行 integral_Icc_eq_integral_Ioc 要求 NullSingletonClass（真实 Lebesgue 满足），允许零端点转换。没有把 Icc/Ioc 忽略成无条件逐点相等。
- Gaussian/GaussianIntegral.lean 实际 SHA256 `4378f161cf5d482be77941cc9aea0195d2e83fe54eeb51b2ab33db1a318ccb9c`，115–117 行 integrable_exp_neg_mul_sq 要求真实 c>0，确给 Lebesgue 上 exp(−cv²) 真可积。
- SpecificLimits/Normed.lean 实际 SHA256 `eee44dfd62feb67bdf3ccc6cf57e8e101f38a7408dbb9c6347e0978ce2010d41`，215–217 行 tendsto_self_mul_const_pow_of_lt_one 要求 0≤rho<1，结论为 n*rho^n→0；相应 rho^n→0 也已存在于该实际文件，无新极限定理依赖。
- Constructions/Pi.lean 实际 SHA256 `bb89dee63d412cd1cc1f7f9fd7a81d64074139571960b2f0fcb66d8b763cd6ef`，360–369 行 pi_eval_preimage_null 提升单坐标真实零集，402–407 行 measurePreserving_eval 对真实概率边际给 evaluation 的测度保持。SampleBoundary 的实际已审 AE 消费也使用 Measure.tendsto_eval_ae_ae；有限交的 Countable/Fin n 门合法。零层可用该实际零集 API 与 measure_mono_null 建立，毋须新支持假设。
- IntegrableOn.lean 实际 SHA256 `d1108ec5e836af0af6bc62c8ad5dd94a371dbc8df3e51698049d51221b3663c2`，171–176 行实际有界可积接口；公开 LocallyIntegrable.lean591–597 行 Continuous(On).integrableOn_Icc 对真实局部有限 Lebesgue 区间给所需可积性。连续相位/幂/范数及 norm_integral_le_integral_norm 沿既有实际 Bochner 导入可见，已接受旧 Fourier 单元消费过同一基础语义。

实际导入图已静态遍历核对：NormalLayerConditionalLaw→FundamentalFourierAsymptotic→CentralFourierIntegral→DominatedConvergence→IntervalIntegral.Basic；CharacteristicFunction.Basic→FourierTransform→Bochner.Set→LocallyIntegrable/IntegrableOn；CentralFourierIntegral→NormalTangentPowerLimit→NormalTangentMoments→NormalTangentGaussian→GaussianIntegral；NormalLayerFourier→SampleBoundary→FiniteIID→Independence.Basic→Constructions.Pi。故以上是当前公开可见接口，非只在某个未导入文件猜名字。

实际缓存存在：IntervalIntegral.Basic.olean 565224 字节、Bochner.Set.olean 430504、GaussianIntegral.olean 41920、SpecificLimits.Normed.olean 276240、Constructions.Pi.olean 393456、Measure.Lebesgue.Basic.olean 153848；相关项目 NormalLayerConditionalLaw 349432、CentralFourierIntegral 185848、FiniteFarArc 503008、NormalTangentDomination 772576、NormalLayerFourier 592824、SampleBoundary 594096、FiniteNormalSpan 306624 字节。没有新缓存或目标编译要求。

另从 actual NormalLayerConditionalLaw 的 Shao imports 独立递归枚举当前拟导入闭包，恰为 24 个项目模块；每份实际源码 hash 与 run/prerequisite-hashes.json 完全一致，24 个已有项目 olean 全部存在。该静态清单文件 SHA256 `02d39eeb7a2c4535ad1bc80e7591ebfaf85eb34313a33b60e24cca9340032878`，根导入 NormalLayerConditionalLaw 仍为冻结 `94e2507a83dfc232280043567f6a2f07950d39da10b45699777ac1316f24281a`。未重新构建任何前置。

实际 lean-toolchain 为 `leanprover/lean4:v4.36.0-rc1`，文件 SHA256 `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`；lake-manifest.json SHA256 `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`；Mathlib manifest rev 与实际 git HEAD 均为 `807d3836b165983210ee2ecf3cd28f239436949c`。这仅绑定静态声明环境，非尚无实现的 kernel 成功声明。本轮没有读取未来实现或 receipt。

## 最终声明/source 裁决

STATUS: CORRECT

JUSTIFICATION: 两个精确冻结类型在固定真实有限阶段 law 下成立。实际 Gaussian 支配及闭基本区间远弧收缩足以直接控制真范数积分，正 sqrt n 的实变元替换与 setIntegral 分解可由现有公开 API 完成；真实精确反演的单位相位给格点层界，离网格层可先在 ENNReal 测度上证零再转 real。同一最终 n 阈值真正先于全部实 d，J=0/n 最终正性/真实中心与协方差门均保持，未发现声明、来源或静态环境关键缺口。

仅批准声明进入实现，未证明它已经通过 Lean 内核。C 与阈值可依赖固定 mu/J/q/a；不升级为紧倾斜族统一常数，不证明 R1 (16)/(17)、负层 Chernoff、完整层支配、完整混合 LLT、hW、最优性/新颖性或根闭合。根 A/B/C/D、layer domination/full LLT/hW 全部保持 OPEN。
