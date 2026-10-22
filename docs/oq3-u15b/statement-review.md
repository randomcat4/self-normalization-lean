# U15b 独立声明与来源审查

STATUS: CORRECT

本票仅审查冻结声明/source gate，尚无实现。唯一审查 lease 1；仅拥有本报告及服务器对应 statement-review.md，不改实现、scope、旧票、共享文件或缓存，不 spawn、Lean/API probe 或构建。所有根 A/B/C/D 保持 OPEN。

## 第一阶段：仅冻结 Lean fence 的三个完整类型盲译

输入 thirty-fifth-unit-scope.md，SHA256 36f3ecf090914d74c55a194809e68580643faf3da7ae7bb02f9252281319a322。只提取精确 Lean 代码块，零定义；此阶段在阅读 scope 解释、R2 原文、实际前置或库接口之前独立翻译并先落盘。

1. `prod_measure_domination (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (m : ℝ≥0) (hdom : (m : ℝ≥0∞) • mu ≤ nu)`：任意两个真实实数概率测度和任意有限非负实常数 m，若 m 倍 mu 在测度序上≤nu，则 m² 倍真正同律乘积 mu⊗mu≤nu⊗nu。标量先由 NNReal 转为 ENNReal 再平方，m=0 包含；须核乘积测度单调性/标量转换的真实 SFinite 门。

2. `cosine_pair_integral_domination (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (m : ℝ≥0) (hdom : (m : ℝ≥0∞) • mu ≤ nu) (u v : ℝ)`：在同一组测度、m 和支配前提下，对任意实频率 u,v，以真实 mu⊗mu 及 nu⊗nu 积分同一个二样本核 K(x,y)=1−cos((x−y)(u+v(x+y)))，断言 m 的实数值平方乘参考积分≤新积分。没有给频率或原子界，故须由实际余弦的非负有界性建立真正可积；实数 m² 的转换须与第一目标 ENNReal 平方相符。

3. `quadratic_tilted_cosine_pair_domination (mu : Measure ℝ) [IsProbabilityMeasure mu] (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L) (hb : ∀ᵐ x ∂mu, |x| ≤ M) (u0 v0 u v : ℝ) (hu : |u - u0| ≤ L) (hv : |v - v0| ≤ L) (s t : ℝ)`：先共同固定真实概率基准 mu、M≥0、L≥0 和 AE 支撑界，再对全部四个参考/新倾斜系数及任意频率 s,t，使用同一二样本核 K_st，exp(−4L(M+M²)) 乘真正参考二次势倾斜律的同律二重积积分≤真正新倾斜律二重积积分。共同常数在全部倾斜系数和频率外，M=0、L=0 均包括。未附加 tilt 概率实例，故须真正从有界支持推出其指数可积性与概率性再调用前项。

这三个目标只到测度和明确非负余弦核积分的支配；没有将核积分宣称为已经证明的特征函数模平方差，也没有 WC 或根 C 闭合。此阶段尚未作批准结论；待核库实际乘积/标量/积分门及 source fit。


## 第二阶段：冻结范围、真实前置与 R2 来源

盲译先落盘后才读取完整 scope、实际 U15a 源码及 R2。scope 两端实际 SHA256 均为 `36f3ecf090914d74c55a194809e68580643faf3da7ae7bb02f9252281319a322`。实际 `C:/game/shao/current/oq3/proofs/r2/report.md` SHA256 `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55`，已直接读取第 343–373 行。

R2 第 349 行 (20) 给真实正密度下界，第 355–356 行 (21) 是真正二重积下的 1−cos 特征恒等式，第 362–363 行 (22) 使用平方因子 m²。候选抽取的是 (20) 到非负二样本积分比较的标准测度机制，不直接证明 (21) 的特征函数识别。核的相位严格满足

`(x−y)(u+v(x+y))=u(x−y)+v(x²−y²)`，

因此与源中 W=(X,X²) 的差频率相同，不是错用任意二维支撑或把二次系数多乘一倍。第三目标把频率改名为 s,t，而 u0,v0,u,v 保持倾斜系数身份，没有量词或变量混淆。

唯一 Shao 前置为已完整独立审查且已被 lead 接受的实际 `TiltedMeasureDomination.lean`，本地与服务器 SHA256 均为 `5445a68da1ac8302f174bfe2144eb8271a0af740fd6b91a87355abb41fed739b`，105 行；该模块没有 Shao 项目前置。实际核对其三个公开完整类型及实现语义：有界支持给每个二次指数真正 Integrable，hf/hg 与概率 NeZero 给正归一化，实际 withDensity 比较给 exp(−2L(M+M²)) 的测度支配。这里不重做已接受旧门或重编旧目标。

source 第 366–373 行的 WC、标准化和无界限制均没有被候选偷含。共同盒宽 M,L 是显式输入，从任意紧参数集选出 L 仍为后继步骤。当前缺失的根公共特征函数恒等式源码/olean 不是导入或数学前提；本单元不复制它们，不以该缺失恒等式已证明为依据，也不宣称 root C 已闭合。

## 第三阶段：三个完整目标的独立数学与边界审查

### 目标一：真实产品与平方标量

记 a=(m:ℝ≥0∞)。m 是 NNReal，所以 a 有限，m=0 保留。真实概率测度 mu、nu 有有限性及 SFinite；a•mu 也 SFinite，有限 NNReal 标量还给有限测度。在这种真实 SFinite 门下，实际乘积标量恒等式给

`(a•mu).prod(a•mu)=a•(mu.prod(a•mu))=a•(a•mu.prod mu)=a²•mu.prod mu`。

Measure.prod_mono 把 hdom 用在两个坐标，得到左侧产品≤nu.prod nu。它要求上方第二边际 SFinite，nu 的真实概率实例提供；标量重写时右边际 a•mu 需要的 SFinite 也真实存在，而不是把库中非 SFinite 时的 prod=0 总化分支当作真正产品。NNReal finite 与必要 SFinite 门均足够，不需要 m>0 或先由质量比较证明 m≤1。m=0 时左边是零测度，结论成立，不允许在证明中消去 m。

### 目标二：先真可积再真实积分序

对任意固定 u,v，K(x,y)=1−cos((x−y)(u+v(x+y))) 是实二元多项式复合余弦所得连续函数。标准实余弦界 −1≤cos≤1 给全局 0≤K≤2，所以 ‖K‖=K≤2。mu.prod mu 与 nu.prod nu 都是真正概率测度，因而各自有限；连续性给两边 AE 强可测，Integrable.of_bound 给两边真正 Integrable。没有要求支持紧、有界或离散，也没有把频率范围藏进界。

令 lambda=a²•mu.prod mu。由目标一 lambda≤nu.prod nu。lambda 亦有限（a² 为 NNReal 平方的有限嵌入），K 对 lambda 真可积也可由常数 2 的同一有限测度门得到。实际 integral_mono_measure 消费 lambda≤nu.prod nu、K 在上方测度 AE 非负及 Integrable K(nu.prod nu)，遂给

`∫K d lambda≤∫K d(nu.prod nu)`。

实际 integral_smul_measure 把左侧改写为 (a²).toReal·∫K d(mu.prod mu)。ENNReal.toReal_pow 与 coe_toReal 正确给 (a²).toReal=(m:ℝ)²。这里 a²≠∞，可按 NNReal coe_pow 或有限性直接核对；没有把 top.toReal=0 当有限系数。m=0 时该因子为零，而上方积分由真实非负性≥0；不消 m 或 m²。这个目标是真实已可积的单次产品积分比较，无须 Fubini 换序，也无须先证明特征函数恒等式。

### 目标三：同一实际倾斜概率与 exp(−4B)

令 B=L(M+M²)≥0。必须先分别调用实际 U15a `quadratic_exp_integrable_of_ae_abs_le`，对同一 mu、同一 hb 得到参考和新二次指数 Integrable；随后以实际 `isProbabilityMeasure_tilted` 给两个倾斜律的真实概率实例。基准 mu 概率提供 NeZero，因此该实例化不循环。不能仅凭 `mu.tilted` 的名字推断概率，因为库中不可积 tilted 为零。

U15a 的实际 `quadratic_tilted_measure_domination` 提供参考律乘 ofReal(exp(−2B))≤新律。取有限 NNReal m=⟨exp(−2B),exp_nonneg⟩，其 ENNReal 嵌入等于上述 ofReal，故真实满足目标二的 hdom。再在任意频率 s,t 应用目标二，所得系数

`(m:ℝ)²=exp(−2B)²=exp((−2B)+(−2B))=exp(−4B)`。

这一指数平方来自真实 exp_add/幂恒等式，不是近似、不是 exp(−2B) 被误当平方因子，也未把 m 与 m² 混用。

M,L 及 B 在全部四个倾斜系数和频率 s,t 前固定；原 U15a 只消费参数差 hu/hv，所得 m 不含这些参数。M=0 或 L=0 时 B=0、m=1，倾斜势在同一支持上 AE 一致，产品积分比较仍合法。无需除 M/L、缩成严格正半径或引入频率相关常数。

## 第四阶段：实际固定库名称、公开路径与缓存

全程通过共享 server.py 对指定服务器只读查看实际源/公开 import 图/文件存在性；未 Lean、API probe、构建、cache 写入或原始日志下载。本轮尚无实现或 receipt 作为数学依据。

1. `Mathlib/MeasureTheory/Measure/Prod.lean` 实际 SHA256 `007561e86f53a65ad411fcbd20d05df9e922f01c5a93eff0f9de26ac49f12ca3`。165–167 行进入 namespace MeasureTheory.Measure；172 行实际 prod 在第二边际非 SFinite 时用零测度总化，故本票明确检查 SFinite。224 行一般产品段的 hν:SFinite ν；427–432 行实际 `MeasureTheory.Measure.prod_mono` 通过 omit hν 只保留上方第二边际 SFinite ν' 的门；877–881 行 `MeasureTheory.Measure.prod_smul_left` 的右边际 SFinite 门来自该段环境。315–329 行实际产品有限性与产品概率实例均存在，真实消费两个边际的相应实例。

2. `Mathlib/MeasureTheory/Measure/WithDensity.lean` 实际 SHA256 `cb47f52f610d82f9ad76e1146e551839d4b762f7157800d12a16b0d2e618e6d3`。684–688 行实际 SFinite(c•mu) 实例；710 行该 Prod 段明确要求 SFinite ν；753–759 行 `MeasureTheory.Measure.prod_smul_right` 可把右边际标量移出产品。这里两个 prod_smul 名称确实属于 Measure 命名空间；它们与 U15a 的全局 MeasureTheory.withDensity_mono/withDensity_smul' 不应混淆。实际 WithDensity 由 U15a→Tilted→RadonNikodym→Lebesgue→Function.AEEqOfLIntegral 的公开链可见，不依赖猜测的 namespace。

3. `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` 实际 SHA256 `66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670`，scope 已直接导入。621–629 行实际 integral_mono_measure 的门是测度序、对上方测度 AE 非负、对上方测度真正 Integrable；本候选可全部提供。1047–1055 行 integral_smul_measure 的实际结果为 c.toReal •积分（库也总化处理 c=∞），本候选通过 NNReal 嵌入明确排除无穷标量，而非依赖它的退化分支。

4. `Mathlib/Basic/ENNReal/Basic.lean` 实际 SHA256 `f7fe64f0d1865209e4d2be2fd98e3bc5edf9af508dd665f0311e6396f8d513a2`：292 行 coe_toReal，411 行 coe_pow。`Mathlib/Basic/ENNReal/Real.lean` 实际 SHA256 `da5573e6bb7b196bd109724302c3db8eda3a3efab72c8db958ce2ddbf643cecf`：343–344 行 toReal_pow。实际 ENNReal 有限标量的 real conversion 与目标第二条相符。Measure.Typeclasses.Finite.lean 102–103 行有限 NNReal 标量保持有限测度，110–113 行相应标量塔实例存在。

5. `Mathlib/Analysis/Complex/Trigonometric.lean` 实际 SHA256 `f6f2c2bb6da4d7dac960bef8d07dc2e337c474b417726c1fd15e30c6b74caafb`，686–693 行 Real.cos_le_one、Real.neg_one_le_cos 真正给任意实相位的两侧界。它由 U15a 的 Exp 明确 public import 进入。`Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean` 实际 SHA256 `85fc5b104bd61801d259dda6cf837892c30bc4b44a1b23688398476941770cf7`，99–100 行 Real.continuous_cos；静态遍历实际 public import 图确认它经 Tilted→RadonNikodym→Bochner.ContinuousLinearMap→Bochner.Set→LocallyIntegrable→IntegrableOn→LpSpace/Indicator、Basic→LpSeminorm/ChebyshevMarkov、Basic、Defs→Pow/NNReal、Real、Complex→Complex/Log、Arg→Trigonometric/Angle→Trigonometric/Basic 可见。没有仅凭 cos 定义存在就假定连续性已导入。

6. 真正有界可积使用已经核对的 IntegrableOn.lean 171–172 行 Integrable.of_bound 和连续实函数的 AEStronglyMeasurable 接口，均由上述真实公开链可见。倾斜律概率实例的实际 hf/NeZero 门已在 U15a 源和 Tilted.lean126–135 行直接核对。

指定服务器实际缓存存在：Prod.olean 342936 字节、WithDensity.olean 147376、Bochner.Basic.olean 688952、Tilted.olean 78048、Trigonometric.Basic.olean 277584；实际 U15a olean 231752 字节。六个明确 tactic 分模块缓存也存在：FieldSimp 1681840、Ring 1648、Positivity 1832、Linarith 2536、FunProp 2488、NormNum 2496 字节。没有新 cache 需求或对缺失根模块的复制依赖。

实际 pins：lean-toolchain 内容 `leanprover/lean4:v4.36.0-rc1`，文件 SHA256 `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`；lake-manifest.json SHA256 `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`。Mathlib manifest rev 和实际 git HEAD 均为 `807d3836b165983210ee2ecf3cd28f239436949c`。这些是静态环境核查，非本单元编译通过声明。

## 最终声明/source 裁决

STATUS: CORRECT

JUSTIFICATION: 三个完整冻结类型的数学量词和系数正确；真正 SFinite 产品的两个标量给 m²，真实连续非负≤2的余弦核在两边产品概率下可积，测度序和有限标量积分转换给第二结论；实际 U15a 的可积门先建立两倾斜概率后给共同 exp(−4B) 实例。m=0、M=0、L=0 均合法，常数在所有倾斜参数与频率前固定。实际公开库接口与缓存足以支持上述路线，未发现声明级、来源级或静态环境关键缺口。

本票仅批准声明进入实现，不声称三个目标已经由 Lean 内核验证。该单元是来源 (20)–(22) 中标准非负积分传递的充分机制；尚未证明该积分等于特征函数模平方差，不证明 WC、除二常数传递、标准化、任意紧参数盒宽选择、最优常数、新颖性、LLT、hW 或根 C/其他根闭合。根 A/B/C/D 全部保持 OPEN。
