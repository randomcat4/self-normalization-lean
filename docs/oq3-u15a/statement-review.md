# U15a 独立声明与来源审查

STATUS: CORRECT

本票仅审查冻结声明/source/environment，尚无实现。审查者仅拥有本报告与指定服务器 statement-review.md，不改源、scope、旧票、共享文件或缓存，不 spawn、不运行 Lean/API 探针或构建。根 A/B/C/D 均为 OPEN。

## 第一阶段：仅冻结 Lean 代码块的完整类型盲译

输入 thirty-fourth-unit-scope.md，SHA256 efc6102ad3b91d3122455157faf0564f066a796eaf7ac02ddc0c9a0f52a800c2。只提取代码块，未读取 scope 说明、R2 原文、库接口或作者路线。零定义，三个完整目标；以下数学翻译先落盘。

1. `quadratic_exp_integrable_of_ae_abs_le (mu : Measure ℝ) [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M) (hb : ∀ᵐ x ∂mu, |x| ≤ M) (u v : ℝ)`：对任意实数上的真实概率测度 mu，先给定 M≥0 且 mu-几乎处处 |x|≤M，则对任意实参数 u,v，实函数 x↦exp(u x+v x²) 对同一 mu 真正可积。没有关于 u,v 的有界性限制，也没有把默认总化积分当作可积性；M=0 包含在内。

2. `tilted_measure_domination_of_abs_sub_le (mu : Measure ℝ) [IsProbabilityMeasure mu] (f g : ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hf : Integrable (fun x => Real.exp (f x)) mu) (hg : Integrable (fun x => Real.exp (g x)) mu) (hfg : ∀ᵐ x ∂mu, |g x - f x| ≤ B)`：对同一概率测度、任意实势函数 f,g 和 B≥0，显式要求 exp∘f、exp∘g 都真正可积；若两势之差在 mu-几乎处处绝对值≤B，则 exp(−2B) 的有限 ENNReal.ofReal 倍数乘以真实 mu.tilted f，在测度序上≤真实 mu.tilted g。测度序意为所有可测事件的质量支配，方向是参考 f 被统一正数压低后≤新 g。f,g 没有额外全局可测假设；须核显式可积门是否已经足够。B=0 包含在内。

3. `quadratic_tilted_measure_domination (mu : Measure ℝ) [IsProbabilityMeasure mu] (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L) (hb : ∀ᵐ x ∂mu, |x| ≤ M) (u0 v0 u v : ℝ) (hu : |u - u0| ≤ L) (hv : |v - v0| ≤ L)`：先固定同一概率测度、共同 M≥0、L≥0 与其 AE 支撑门，再对全部参考/新系数 u0,v0,u,v，只要两个系数差分别≤L，就有 exp(−2L(M+M²)) 的有限正 ENNReal 倍数乘以参考二次势倾斜测度≤新二次势倾斜测度。M,L 在全部四个系数外；目标未附加积分假设，故必须由同一 AE 紧界真实推出两边指数可积和正归一化。M=0 或 L=0 不能被证明中隐式排除。

待独立核查：实际 tilted 的不可积分支；真实正归一化、AE 密度比较和有限标量顺序；全局可测性与 AE 可测性门；实际缓存导入；与源 R2 充分测度估计的对应范围。不把该票预设为平方间隙、WC 或根闭合。


## 第二阶段：冻结 scope 与真实来源对应

盲译落盘后才读取完整 scope 和来源。scope 本地及指定服务器 run/u15a-20261021/scope.md 的实际 SHA256 均为 `efc6102ad3b91d3122455157faf0564f066a796eaf7ac02ddc0c9a0f52a800c2`。实际来源 `C:/game/shao/current/oq3/proofs/r2/report.md` SHA256 为 `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55`；已直接读取第 343–373 行，并核读其第 38–43 行的基础定义。

R2 第 41–42 行实际定义 W=(X,X²)、K(theta)=log E exp(theta·W)、dP_theta=exp(theta·W−K(theta))dP。因此本候选在实 X 的实际分布 mu 上使用 ux+vx²，确为同一二次指数族的原始坐标表达，而非替换成任意二维向量。第 345–352 行用有界 X 和紧参数邻域得与 theta 无关的正密度下界 (20)；本候选以明确共同盒宽 L 与 AE 支撑界 M，给出充分的测度序形式 m·P_theta0≤P_theta，其中 m=exp(−2L(M+M²))>0。并不主张已经形式化任何 Radon–Nikodym 导数等式。

第 354–363 行的两样本特征函数恒等式及 m² 缺口，第 366–369 行的 WC 传递和协方差标准化，均不在这三个目标中。由任意紧参数集合选出共同 L 的拓扑步骤也不在目标中；这里已经显式假设共同 L。R2 第 371–373 行警告无界 X 时 (20) 一般不成立，本候选真实保留 AE 有界支持门，未将高斯阻尼或有限矩偷换成它。无最优性或新颖性主张。

scope 拟导入 Tilted、Exp 和六个明确 tactic 模块，namespace Shao.OQ3、open MeasureTheory。没有任何 Shao 项目前置；当前旧堆叠是否接通其他公共特征函数模块与本单元无关，不复制它们，也不把未来的 m²/WC 结论当作已审依赖。

## 第三阶段：独立数学与端点审查

### 目标一：真实指数可积

对固定任意 u,v，令 C=exp(|u|M+|v|M²)，这是有限正实数。x↦exp(ux+vx²) 在整个实线上连续，所以对实际 Borel 实空间是 AEStronglyMeasurable。仅在 hb 给出的同一 mu-AE 集合上进行估计：由 |x|≤M 和 M≥0 得 x²≤M²；于是

`ux+vx² ≤ |u||x|+|v|x² ≤ |u|M+|v|M²`。

指数保序，且其范数等于自身，故真实范数 AE≤C。mu 是概率测度，所以有限；实际 Integrable.of_bound 的全部门（AE 强可测、有限测度、AE 范数常数界）因此满足。没有先用 tilted 的名字假设概率，也没有用总化积分替代可积性。M=0 时 hb 强制 x=0 AE，函数为 1 AE；没有除 M，端点合法。任意 u,v 的量词与这个逐函数可积结论相容，不要求同一个 C 同时界住全部 u,v。

### 目标二：正归一化与真实测度下界

记 Zf=∫exp(f)dmu、Zg=∫exp(g)dmu。hf,hg 是真实 Integrable，不只是积分写法；概率给 mu≠0，故实际 integral_exp_pos 分别给 Zf>0、Zg>0。它们是有限实数归一化，不能通过 integral_undef 或 ENNReal.top.toReal 得出。

在 hfg 的同一 AE 集合上，f−B≤g≤f+B。记 b=exp(B)>0、a=exp(−B)>0、c=exp(−2B)>0，则

`a exp(f) ≤ exp(g) ≤ b exp(f)`。

上界的右函数由 hf 乘常数而真正可积，左函数由 hg 可积；在真实可积门下用 integral_mono_ae 与 integral_const_mul 得 Zg≤bZf。利用所有正分母，可按以下不含可疑倒数序的交叉乘检查：

`c exp(f(x)) Zg ≤ c exp(f(x)) b Zf = a exp(f(x)) Zf ≤ exp(g(x)) Zf`。

因此 AE 有 c·exp(f(x))/Zf≤exp(g(x))/Zg。恒等式 cb=a 来自指数加法 −2B+B=−B，符号正确。归一化损失是两次 B，故目标指数 −2B 的方向正确。

实际 tilted 的定义是 `mu.withDensity (fun x => ENNReal.ofReal (exp(f x)/Zf))`。将上述真实 AE 不等式作 ENNReal.ofReal 后，使用 c≥0 的 ofReal_mul，将左密度改写为 ENNReal.ofReal c 与参考密度的点乘；withDensity_mono 将 AE 比较提升到真正测度序。再使用 withDensity_smul'，其有限标量门由 `ENNReal.ofReal c≠∞` 满足，即得到目标左边的测度标量乘法。没有假定未经证明的 RN 导数或拿有界权重比较充当测度比较。

f,g 不要求全局可测不是漏洞：hf,hg 已给指数函数的 AE 强可测性及积分；withDensity_mono 的实际前提仅是密度 AE 比较，withDensity_smul' 在有限标量下也不需密度的全局可测性。整个论证不需要将 AE 可测升级为全局可测，也不需要在未知可测函数上套全局 measurable 版本。B=0 时 AE 势相同、c=1，结论仍有效；hB 保证 c≤1，符合概率测度支配。因 hf,hg 和 mu≠0，两边实际 tilted 也可由 isProbabilityMeasure_tilted 得到概率性，但本目标仅要求测度序。

### 目标三：真正共同 M,L 与全部参数

设 f(x)=u0 x+v0 x²、g(x)=u x+v x²。先由目标一对同一 mu、同一 hb 分别得到 exp f 和 exp g 真正可积；这一步不借用尚未证明的倾斜概率。令 B=L(M+M²)≥0。在同一 hb-AE 集合上，精确势差和三角不等式给

`|g−f|=|(u−u0)x+(v−v0)x²|`

`≤|u−u0||x|+|v−v0|x²≤L|x|+Lx²≤L(M+M²)`。

使用 |x²|=x²、|x|≤M⇒x²≤M² 及 L≥0 的乘法方向；故目标二真实适用，得到实际候选的系数。M,L 在全部 u0,v0,u,v 外已固定，B 及 c 也在全部参数外；不把每个参数自己的归一化或 sup 偷放进 c。无需基准 u0,v0 的绝对界，因参数差的作用在两个归一化间取消。M=0 或 L=0 都给 B=0、c=1，没有除 M/L/B 或要求它们严格为正；共同支持上的二次势一致，结论正确。

## 第四阶段：指定服务器的实际 API、公开导入与缓存

仅通过共享 server.py 只读查看固定库源、散列、导入图和已有缓存文件；未运行 Lean、#check/API 探针、目标/Audit 构建或缓存写入。本轮没有实现或 receipt 可作为证明。

1. `Mathlib/MeasureTheory/Measure/Tilted.lean` 实际 SHA256 `355cce542b03dd9130d9511f80ae803cc11a12ba9e6a947e68402b124be2165f`。第 42–43 行是上文实际 withDensity 定义；46–48 行 tilted_of_not_integrable 明确指数不可积时为零测度；51–54 行还处理势的非 AE 可测分支，不能只凭函数叫 tilted 就判概率。126–135 行 isProbabilityMeasure_tilted 的真实门为 NeZero mu 与 exp f 的 Integrable，其证明实际调用 integral_exp_pos。候选 hf/hg 与第一目标正好排除了坏分支。

2. `Mathlib/MeasureTheory/Measure/WithDensity.lean` 实际 SHA256 `cb47f52f610d82f9ad76e1146e551839d4b762f7157800d12a16b0d2e618e6d3`。102–107 行 withDensity_mono 只要求 f≤ᵐ[mu]g；137–142 行 withDensity_smul' 要求有限标量 r≠∞，允许密度本身未全局可测。本候选的 r 为有限 ofReal(exp(−2B))，完全满足。不能误用 130–135 行那个额外要求 Measurable f 的 withDensity_smul 替换之。

3. `Mathlib/MeasureTheory/Integral/IntegrableOn.lean` 实际 SHA256 `d1108ec5e836af0af6bc62c8ad5dd94a371dbc8df3e51698049d51221b3663c2`，171–172 行 Integrable.of_bound 的真实类型要求 IsFiniteMeasure、AEStronglyMeasurable 与 AE 范数≤常数；三门在目标一均可真实提供。

4. `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` 实际 SHA256 `66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670`：288–290 行 integral_const_mul；662–667 行 integral_mono_ae 显式要求两边 Integrable；792–798 行 integral_exp_pos 的门是 NeZero mu 与 Integrable exp f。本候选既不从虚假的总化积分推出正性，也不在未知可积时作积分单调比较。

5. `Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean` 实际 SHA256 `00ef2a106c0ae4032944cec021ad58d04c370cc9b84547bed95462ca5205e25b`，87–88 行 IsProbabilityMeasure.neZero 提供归一化正性所需 NeZero 实例。`Function/StronglyMeasurable/AEStronglyMeasurable.lean` 240–243 行实际 `_root_.Continuous.aestronglyMeasurable` 要求 OpensMeasurableSpace、PseudoMetrizableSpace 和 SecondCountableTopologyEither，实际实数 Borel 空间均满足；`Analysis/SpecialFunctions/Exp.lean` 153–154 行 Real.continuous_exp 已公开可见。

6. `Mathlib/Analysis/SpecialFunctions/Exp.lean` 实际 SHA256 `1dcb27b9ea4dbfea015fd97196f0cb6ac294633be79590dba8af8685d11b03e8`。`Mathlib/Basic/ENNReal/Basic.lean` 实际 SHA256 `f7fe64f0d1865209e4d2be2fd98e3bc5edf9af508dd665f0311e6396f8d513a2`，347 行 ofReal_ne_top 为所有实数提供有限标量门；`Mathlib/Basic/ENNReal/Real.lean` 实际 SHA256 `da5573e6bb7b196bd109724302c3db8eda3a3efab72c8db958ce2ddbf643cecf`，297–303 行 ofReal_mul/ofReal_mul' 真实保留一个因子非负的条件。这里取的因子是正指数，合法。未使用任何 top.toReal。

实际 public import 图已直接遍历核对（不是 Lean probe）：

- Tilted→Decomposition.RadonNikodym→Decomposition.Lebesgue→Function.AEEqOfLIntegral→WithDensity。
- Tilted→Decomposition.RadonNikodym→Integral.Bochner.ContinuousLinearMap→Integral.Bochner.Set→Function.LocallyIntegrable→Integral.IntegrableOn。
- 同一前缀到 Bochner.Set→Bochner.SumMeasure→Bochner.Basic，因此 integral_exp_pos 与积分单调接口公开可见。
- IntegrableOn 公开链继续通向 L1Space.Integrable→L1Space.HasFiniteIntegral→StronglyMeasurable.AEStronglyMeasurable，真实连续函数可测接口公开可见；概率类型类经 IntegrableOn→LpSpace.Indicator→Measure.Real→Typeclasses.Probability 公开可见。
- Exp 的公开链经 SpecificLimits.Normed→Asymptotics.Lemmas→Normed.Group.InfiniteSum→Topology.Algebra.InfiniteSum.ENNReal→Basic.Real.ENatENNReal→Basic.ENNReal.Basic，提供有限 ofReal 门；另一条链经 Normed.MulAction→Basic.ENNReal.Action→Basic.ENNReal.Operations→Basic.ENNReal.Real，提供 ofReal_mul。

实际已有缓存存在：Tilted.olean 78048 字节，WithDensity.olean 147376 字节，Exp.olean 113760 字节；六个明确 tactic 模块 FieldSimp 1681840、Ring 1648、Positivity 1832、Linarith 2536、FunProp 2488、NormNum 2496 字节。无需缺失的其他根公共源码/olean，也未请求或写入新 cache。

实际 pins：lean-toolchain 为 `leanprover/lean4:v4.36.0-rc1`，文件 SHA256 `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`；lake-manifest.json SHA256 `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`。Mathlib manifest rev 与实际 git HEAD 均为 `807d3836b165983210ee2ecf3cd28f239436949c`。以上为静态声明环境绑定，非尚不存在实现的编译成功主张。

## 最终声明/source 裁决

STATUS: CORRECT

JUSTIFICATION: 三个精确冻结类型在真实概率测度、真实指数可积性和 AE 支撑/势差门下均成立；归一化严格为正，exp(−2B) 的方向与常数正确，有限 ENNReal 标量可通过实际 withDensity 接口提升到真实测度序。第三目标的共同常数真正先于全部参数，M=0/L=0 保留。实际公开导入路径及已有缓存提供必要接口，未发现声明级、来源级或静态环境关键缺口。

本票仅批准实现这些声明，不声称它们已经通过 Lean 内核。来源归属为 R2 式 (20) 的标准充分测度形式，不证明 RN 导数识别、两样本式 (21)、平方缺口式 (22)、WC 常数、协方差标准化、任意紧参数集盒宽选择、无界版本、最优性或新颖性。根 A/B/C/D 全部保持 OPEN。
