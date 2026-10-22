# U13c NormalLayerConditionalLaw 独立声明与来源审查

STATUS: CORRECT

仅声明/source gate，尚无实现。独立 reviewer lease 1；只拥有本新报告与授权 run/statement-review.md，不改源/旧票/公共文件或缓存，不 spawn、不运行 Lean/API 探针、不构建或 commit。本节先仅读冻结 Lean fence，先落盘，再看 scope 说明、R1、实际前置与固定库。

## 1. 冻结定义体与五完整类型的先行盲译

冻结 `thirty-first-unit-scope.md` SHA256 `57acd814b3ca02b4b8a53fd7c155d0f78ec96519242bf46dba820e75bd6071a8`。暂记 λ_n=Measure.pi(μ|Fin n)，E(q,d,n)={z:Path n | normalDeviation q z=d}，T_a,n(z)=(Σz_i−na)/sqrt n，L_n(s)=normalLayerCharacteristic μ q a d s n。真实定义/统计量及 charFun 约定将在后续独立核对，不仅凭名字接受。

1. **公开定义 `normalLayerConditionalLaw μ q a d n`**：若实际 λ_n(E)=0，返回 ℝ 上的 Dirac δ₀；否则先对真实样本概率 λ_n 以 E 作 `ProbabilityTheory.cond`，再经实际切向统计量 T_a,n 推送到 ℝ。定义本身允许任意 μ:Measure ℝ，不含 μ 概率门；各定理再明确要求 μ 为概率。它是总化的真实条件后推送构造，零质量时有显式替代分支，不把除零条件测度假装成概率。
2. **`normalLayerCharacteristic_zero_eq_mass`**：μ 概率时，对任意 q,a,d:ℝ 与 n:ℕ，未归一化层积分在 s=0 恰等于真实 λ_n 的层质量 `.real E` 的复嵌入。零层质量和 n=0 包括，不要求层可达或均值成立。
3. **`normalLayerConditionalLaw_isProbabilityMeasure`**：μ 概率时，对任意 q,a,d,n，定义出的真实 ℝ 测度是概率；结论包括零质量层和全部初始 n，因此需要核显式 Dirac 分支及非零条件测度推送。
4. **`charFun_normalLayerConditionalLaw`**：μ 概率且真实 λ_n(E)≠0 时，对任意实 s，实际条件后切向律的特征函数值等于 L_n(s)/L_n(0)。hpos 的字面是 ENNReal 层质量非零，并未直接给 `.real` 正性；有限性、实质量非零和分母非零必须由实际概率门补全。无 n>0 或全局矩假设。
5. **`eventually_stage_normalLayer_mass_pos`**：固定 μ 概率、J,q,a；μ-AE |X|≤4+sqrt10，真实 EY=q、EX=a，实际 normalVariance>0、parabolaCovariance.det>0；AE 支持在活跃 stageAtom(Fin4⊕FinJ) 像中且每个点真实单点正质量。对全序列有界实 d，只需最终 d_n+nq∈mesh_Jℤ，即得最终真实样本层质量 λ_n.real E(q,d_n,n)>0。不是仅给复积分非零，也不是假设所有层实际可达。
6. **`stage_normalLayerConditionalLaw_charFun_tendsto`**：与上一项完全相同的固定 μ/J/q/a 和真概率/矩/支持/正单点门，另给固定实 s、bounded d 和最终格点相容。结论为真实 `charFun(normalLayerConditionalLaw μ q a d_n n)(s)` 在 n→∞ 时趋向 `Complex.exp(−transverseVariance μ·s²/2)`（指数为实数嵌入）。同一 law、q,a,d_n 和 T_a,n 必须贯穿；没有声明测度弱收敛、连续集概率极限、Lévy 或完整 LLT。

盲译阶段未判断静态环境、归一化公式或极限可证性。公开结构是一实际定义、五目标。根 A/B/C/D 保持 OPEN。

## 2. 来源与实际前置对应

盲译落盘后读取冻结说明。拟 imports 为 `Shao.OQ3.FundamentalFourierAsymptotic`、`Mathlib.Probability.ConditionalProbability`、`Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic`；namespace Shao.OQ3，open MeasureTheory Filter，scoped BigOperators Matrix，noncomputable。实际库 `charFun` 位于 **MeasureTheory**，与拟 open 对应；`ProbabilityTheory.cond` 在定义内已完整限定，不缺 open ProbabilityTheory。本地冻结 scope 与真实 run/scope.md 的 SHA256 均为 `57acd814b3ca02b4b8a53fd7c155d0f78ec96519242bf46dba820e75bd6071a8`，一公开定义体与五完整类型如盲译。

真实 R1 report.md SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662` 已核。318–319 为同一 μ 的 M_n=ΣY_i−nq 与 R_n=ΣX_i−na；332–337 讨论 R_n/sqrt n 的条件特征函数，339–343 给同一协方差的 Gaussian 计算。本单元接此前未归一化层积分的极限，补上实际条件概率和特征函数比值。R1:344 的 Lévy/连续集概率结论仍未形式化，本票不将特征函数点态收敛直接计作 (15)。

实际 U13a 源 `NormalLayerFourier.lean` 两定义重核：L_n(s)=∫_{λ_n}1_{M_q=d}exp(i·s(Σz_i−na)/sqrt n)，是真实 n 重乘积样本、同一 q/a 和实际层；不是抽象数列。实际 U13b `stage_normalLayerCharacteristic_scaled_tendsto` 给同一 μ/J/q/a/d、bounded d 与 eventual 格点相容门下的 sqrt n L_n(s) 极限；零频率 s=0 时系数 A_J=(h_J/(2π))sqrt(2π/S)>0。U7 实际定义 S=Var_μ(Y)、transverseVariance=det(parabolaCovariance μ)/S；U12b 真实协方差行列式恒等式将后者绑定到 (Y,X)，它是 τ² 而非 τ。hS、hD 和同一概率/紧界保证正域及真实矩/L²，不用 totalized variance 替代可积。

公开定义只要求 Measure μ 是合法总化定义；五个定理均另加 μ 概率。一般 q,a 仅在前三个目标作代数中心，不要求均值，数学上正确；后两个极限目标完整保留真实均值门。μ/J/q/a 在全部 n 之前固定，未按 n 改 law 或改中心，也没有宣称任意 q 下都存在满足这些条件的概率。

## 3. 条件测度、真可积与极限的数学审查

### 3.1 可测层、真实统计量和零质量定义

Path n 是 Fin n→ℝ，实际 M_q(z)=Σ(8z_i−z_i²)−nq 是有限坐标多项式，连续，所以 E={M_q=d} 是闭/可测事件。T_a,n(z)=(Σz_i−na)/sqrt n 对每个固定 n 都连续；即使 n=0，分母只是按域总化的固定常数，T_0 为 0，不需消分母证明可测。这提供对 λ_n、其限制以及 cond 的实际 AEMeasurable 推送门。

λ_n 是真实有限产品概率，故每个层质量 c_n=λ_n(E)≤1、c_n≠∞。若 c_n=0，新定义明确返回真实 δ₀ 概率；若 c_n≠0，实际 `ProbabilityTheory.cond λ_n E=(c_n)⁻¹•λ_n.restrict E`。有限非零 c_n 使 cond 总质量严格归一为 1，再经**实际可测 T_a,n**推送，得到真实切向条件律概率。这验证第二目标对全部 n，而不是误把库中零质量 cond 当作概率。

固定库的 `cond_isProbabilityMeasure` 自身只要求有限 measure 和层质量非零，并不要求事件可测；本构造仍有独立真实可测 E，用于确切条件事件及 indicator/restricted integral 对应。另一个值得明确的实际语义是：本 pin 的 `Measure.map` 对非 AEMeasurable 函数有库内 fallback Dirac，概率 map instance 因而是无条件的。**这里 T_a,n 真连续/可测，所以实际 map 确为 T 的推送，不触发那个 fallback。** 后续实现必须在推送积分步骤真正给出该可测性，不能只凭 map 的概率 instance 冒称统计量分布。本候选的 T 已有足够结构提供此门，不需修改声明。

### 3.2 零频率等于真实实质量（首目标）

s=0 时实际指数为 exp(0)=1，含 sqrt0 的总化除法也给 0；L_n(0)=∫1_E·1 dλ_n。可测 E 的 `integral_indicator` 与真实常数限制积分给 `(c_n.toReal:ℂ)`，即声明的 λ_n.real E 复嵌入。真实可积由 U13a `normalLayerIntegrand_integrable` 给出，也可由产品概率上的可测 indicator 和 norm≤1 建立；不以总化积分猜测存在。c_n=0 时等式确实为 0。

### 3.3 条件 charFun 的真实比值（第三目标）

设 hpos:c_n≠0。有限概率还给 c_n≠∞，故 p_n=c_n.toReal>0，p_n≠0；据首目标 L_n(0)=(p_n:ℂ)≠0。不要把 hpos 的 ENNReal 非零直接误当作 toReal 非零而漏掉非无穷门。

实际 `charFun_apply_real` 用**正相位** `exp(s*x*I)`。统计量 T 的相位 f_s(z)=exp(i s T_a,n(z)) 连续且 norm=1，所以对 λ_n、λ_n.restrict E、cond λ_n E 均真正可积；对推送条件概率上的单变量指数也真正可积。所有这些来自有限 measure/概率和可测范数 1，不要求 T 有期望或任意全局矩。U13a 还已给原样本层 indicator 相位真可积。

先用实际 T 可测和连续指数的强可测性给真实 map 积分换元，再展开 cond，得到

`charFun(map T (cond λ_n E))(s)`
`=∫exp(i s T) dcond`
`=((c_n)⁻¹).toReal • ∫_E exp(i s T)dλ_n`
`=(p_n⁻¹:ℂ)·L_n(s)=L_n(s)/L_n(0)`。

其中 restriction/indicator 由可测 E 对应；实际积分中 `s*T=s*(Σz_i−na)/sqrt n` 是乘法/除法恒等式，含 n=0 也不需消 sqrt。`ENNReal.toReal_inv` 精确给倒数转换；c_n≠0 还使其 ENNReal inverse≠∞，c_n≠∞ 使 normalizer 真非零。最后实 smul 到复乘法和复分母消去均有 p_n≠0 依据。不是把条件 restriction 与未归一化 L_n(s) 混为一物，也不是由总化复除法“证明”条件律。

### 3.4 最终正层质量（第四目标）

使用已完整独立审查 U13b 的 s=0 结论，令 A_J=(h_J/(2π))sqrt(2π/S)。mesh_J=(2^J)⁻¹>0、π>0、S>0，所以 A_J>0，有限且复嵌入非零。首目标识别 L_n(0)=(p_n:ℂ)，通过复实部连续映射得到真实实序列 `sqrt n·p_n→A_J`。正极限的开邻域给最终严格 `sqrt n·p_n>0`；sqrt n≥0、p_n≥0，故最终 p_n>0。不是从格点相容直接推正质量，也不是只得到复积分非零。

整条推理仅使用 U13b、首目标和概率有限性；不依赖待证条件特征极限，因此无循环。hlayer 只需要 eventual，U13b 已给相同量词；不能升级到所有初始 n。正质量结果不依赖 s，这正好允许之后所有固定频率使用同一真实条件律。

### 3.5 同一缩放因子比值与 Gaussian 极限（第五目标）

U13b 对该同一 μ/J/q/a/d 给 `sqrt n L_n(s)→A_J exp(−τ²s²/2)`，s=0 给 `sqrt n L_n(0)→A_J`；A_J≠0，实际复数 Tendsto.div 可用。该商趋向 exp(−τ²s²/2) 的复嵌入，它与目标的 `Complex.exp ((−τ²s²/2:ℝ):ℂ)` 由真实 `Complex.ofReal_exp` 一致。

将第四目标的 p_n>0、μ 概率带来的 c_n 有限非零、首目标的 L_n(0)≠0，与 eventual n≥1 合取。此时 b=sqrt n>0，b 的复嵌入非零，第三目标给 actual charFun=L_n(s)/L_n(0)，而 `(b L_n(s))/(b L_n(0))=L_n(s)/L_n(0)` 在这些真实非零门后合法消去。相同 b 对分子分母，未跨 law 或改变 q/a；有限坏初项只用 eventual equality 转移 Tendsto。原定义的 Dirac 零质量分支在这个尾部确实不再触发。

因此目标五的声明足够，没有遗漏条件质量、sqrt 非零或分母极限非零门；它们可从前面目标及明确假设派生。目标依赖顺序为：首/次目标 → 比值；首目标+U13b → 最终正质量；比值+最终正质量+U13b 两个缩放极限 → 最终 charFun 极限。没有由待证收敛反推分母正性的循环。

### 3.6 边界与范围

n=0 时 Path0 的唯一空样本真实产品质量 1，M=R=0，T=0；d=0 时条件后推送为 δ₀，d≠0 时显式零质量分支仍为 δ₀。全部 n 概率与一般正质量比值目标都有效；极限证明中消 sqrt 仅在 eventual n≥1。J=0 时真实 stage 只有 Fin4，mesh0=1，继承 U13b 包括此情形；无隐藏 J>0。

hd 是显式全序列实界，未暗中补来源 O(1) 的有限初项，也未要求 d_n 收敛或单调。所有 μ/J/q/a/d 在 n 外固定；源有限律实例仍须供给其真实支持、活跃正单点、均值与矩门，本候选不替任何 law 偷供概率存在性。两个极限仅到真实概率特征函数点态 Gaussian 收敛；没有测度弱收敛、连续集概率、Lévy、完整混合 LLT、hW 或根闭合。

## 4. 固定 API、环境与哈希绑定

通过共享 server.py 只读真实固定源码与缓存，没有 Lean/#check/API 探针或构建：

| 固定库实际 API / 位置 | 本次核实的语义 | 源 SHA256 |
|---|---|---|
| Probability/ConditionalProbability:68–76,153–164 | cond 在 ProbabilityTheory，真实 inverse•restrict；有限非零条件质量给真正概率 | `4245cc130e59294fadd87a6b011273c010bf3a21fd3395b8a3fe0f8a749f3f8c` |
| Measure/CharacteristicFunction/Basic:91,129–135 | charFun 在 MeasureTheory；ℝ 上 actual exp(s*x*I) 正相位积分 | `3f90bba2eb49b295a4dd7bb80f5434f66c31ebdd2801a0bc82e5c9476c9b54e4` |
| Integral/Bochner/Basic:1047–1048,1076–1085 | measure 标量 integral 转 c.toReal•integral；真实 integral_map 要 T 的 AEMeasurable 和被积函数在 map 下 AEStronglyMeasurable，这里均由真实连续性给出 | `66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670` |
| Basic/ENNReal/Real:133–134 | c≠0 且 c≠∞ 才给 toReal c>0 | `da5573e6bb7b196bd109724302c3db8eda3a3efab72c8db958ce2ddbf643cecf` |
| Basic/ENNReal/Basic:323–324 | toReal c≠0 ↔ c≠0 且 c≠∞，防止漏有限门 | `f7fe64f0d1865209e4d2be2fd98e3bc5edf9af508dd665f0311e6396f8d513a2` |
| Basic/ENNReal/Inv:975–979 | 实际 toReal_inv 与 toReal_div，倒数位置正确 | `f06e93ae82105c5c03585c2d11377b94aac119b7fdbcaf34a7a333aa27c53f36` |
| Measure/Map:99–114 | map 的真实 AEMeasurable 分支与非可测 fallback 已核；实际 T 连续保证前者 | `7bae8f174146d4ef4055f79757c2a0a3af6a9090dda3d28ea17fbd54540e9593` |
| Measure/Typeclasses/Probability:124–141 | map 概率 instance 及 measurable map iff；本构造同时满足真实统计量推送门 | `00ef2a106c0ae4032944cec021ad58d04c370cc9b84547bed95462ca5205e25b` |

由拟 imports 的实际 public 导入链独立静态核验，Bochner.Basic 的积分缩放/推送、IntegrableOn 的有限有界相位真可积、ENNReal.Inv/相关 toReal 门、Probability instances 与 real Lebesgue/实数标准内积均可见。`charFun` 无需额外 ProbabilityTheory open；只在 cond theorem 调用处可用完整 namespace。旧实际样本概率、可测层和 Fin n 乘积环境经 FundamentalFourierAsymptotic→NormalLayerFourier/FinitePath/FiniteIID 可见。没有新增矩阵范数或 MeasureSpace 选择歧义。

实际缓存 `.olean` 已只读确认：ConditionalProbability 150160 bytes，CharacteristicFunction.Basic 341832 bytes。这里无需 LevyConvergence 或测度弱收敛缓存，未请求/写入任何新缓存。已有完整独立 CORRECT 的承重前置当前本地/服务器真源逐项 hash 一致：

| 实际前置 | SHA256 |
|---|---|
| FundamentalFourierAsymptotic.lean | `aab18e9f073a18a87d42f0edd3e37a95da58cacf5b9635e4a64c887d340765b1` |
| NormalLayerFourier.lean | `063b6c5ce50e6c5ee33b53301cdfcd36a63a4ea06f9c3de729756513ca736fa3` |
| RegularCovariance.lean | `0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853` |

实际 lean-toolchain `leanprover/lean4:v4.36.0-rc1`；manifest mathlib rev 与真实 mathlib git HEAD 同为 `807d3836b165983210ee2ecf3cd28f239436949c`。本轮仅静态审查，未声称候选目标已 elaborated/内核通过，也没有尚不存在的作者 receipt/Audit 可作证明。

## JUSTIFICATION

**STATUS: CORRECT。** 一个实际条件律定义体和五个完整类型在现有固定环境下数学可行、来源与量词一致；未发现须修改的声明或环境缺口。真实层/统计量可测，零质量 δ₀ 分支保证每个 n 的概率；正质量分支确为 normalized restriction 后的实际切向推送，charFun 比值有真实可积、ENNReal finite/nonzero、toReal inverse 与复分母门。U13b 的 s0 正实领先常数可非循环地推出最终真实正层质量；同一 sqrt n 在最终正质量且 n≥1 后合法从两个真实缩放层积分之商消去，给同一条件 law 的 Gaussian charFun 极限。

这是独立**声明/source gate**准许，尚未审查或计入任何本单元实现/实际 TYPE/作者内核门。后续实现必须接受完整独立证明审查，尤其实际 T 可测以确保 map 真推送、相位先真可积、有限非零质量与最终分母门均需落实。未主张 Lévy、弱收敛、完整 (15)/混合 LLT、实际 hW 或根闭合；根 A/B/C/D 全部 **OPEN**。

交付本地 `drafts/oq3/u13c-statement-review.md` 与授权服务器 `runs/oq3/u13c-20261021/statement-review.md`；两端最终 SHA256 随交付独立核验。只写本报告，未修改作者源/旧票/共享文件/缓存，未 spawn、运行 Lean/API 探针、构建或 commit。
