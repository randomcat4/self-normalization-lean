# U15b 完整独立证明、来源与类型审查

STATUS: CORRECT

审查者复用唯一 lease 1，仅拥有本报告及指定服务器对应 proof-review.md，不改源码、scope、旧票、共享文件或缓存，不 spawn。承认此前声明上下文存在；本阶段仍先仅提取 actual 三个完整公开类型，独立重新盲译并先落盘，尚未读取本次证明或机械证据。

## 第一阶段：actual 三个完整公开类型盲译

实际输入 drafts/oq3/ProductMeasureDomination.lean，SHA256 9f05af79e47b9f778cbce7a0d19c0addea6d457eab5f088a69bf372f660c5a3f，81 行。零公开定义。本阶段只读提取后的三个实际公开完整类型。

1. `prod_measure_domination (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (m : ℝ≥0) (hdom : (m : ℝ≥0∞) • mu ≤ nu)`：两个真实实数概率测度、有限非负 NNReal 常数 m；若其 ENNReal 嵌入乘 mu≤nu，则该嵌入的平方乘真正同律乘积 mu.prod mu≤nu.prod nu。m=0 包含，不能隐式消去。产品及标量恒等式必须有真实 SFinite 门。

2. `cosine_pair_integral_domination (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (m : ℝ≥0) (hdom : (m : ℝ≥0∞) • mu ≤ nu) (u v : ℝ)`：同一真实测度支配下，对任意实频率 u,v，(m:ℝ)² 乘 mu 二重积下 K_uv(x,y)=1−cos((x−y)(u+v(x+y))) 的真实实积分≤nu 二重积下相同核的积分。频率任意；可积性没有列为假设，须由真实概率和非负有界余弦核建立。有限 ENNReal 平方转到实数平方必须一致。

3. `quadratic_tilted_cosine_pair_domination (mu : Measure ℝ) [IsProbabilityMeasure mu] (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L) (hb : ∀ᵐ x ∂mu, |x| ≤ M) (u0 v0 u v : ℝ) (hu : |u - u0| ≤ L) (hv : |v - v0| ≤ L) (s t : ℝ)`：共同 M,L 及 AE 支撑门先于全部倾斜系数与任意频率 s,t；真实参考二次势倾斜律的同律二重积 K_st 积分乘 exp(−4L(M+M²))≤真实新倾斜律同核积分。没有预置两个 tilted 的概率实例或指数可积假设，因此须先由真实有界支持门得到它们。M=0、L=0 均允许，因子只依赖共同 M,L。

本盲译先落盘。后续按 scope/R2→全部实际证明/private/locals/固定库→全部 actual TYPE→作者 receipt/机械证据的顺序独立核查。根 A/B/C/D 均保持 OPEN；不把余弦核积分默认识别为已经证明的特征函数缺口或 WC。


## 第二阶段：冻结范围与真实来源

盲译先落盘后才读取冻结 scope、已接受 statement-review、实际 81 行实现及 R2 第 343–373 行。scope SHA256 `36f3ecf090914d74c55a194809e68580643faf3da7ae7bb02f9252281319a322`，statement-review SHA256 `b28ebc81871ad03444c7d55860dad814b0cd670eac949421381fd1ca6ab88457`；实际 R2 SHA256 `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55`。三个实际公开完整类型去空白与冻结 Lean 块逐字相同，无定义/假设/积分对象改变。

实际源码第 13 行显式 `open scoped ENNReal NNReal`，为既有 NNReal/ENNReal 记号打开作用域；imports 不变，实际类型仍是原冻结意图的非负有限实数和扩展非负实数，未将 m 改成任意可能无穷的 ENNReal。这一解析环境补充在本票如实记录，不追改冻结 scope 或旧票。

R2 第 349 行 (20) 给同一族的正测度密度下界，第 355–356 行 (21) 给二样本余弦表达，第 362–363 行 (22) 使用平方因子。此模块只证明中间真实测度与明确非负积分的传递，未证明余弦积分等于特征函数模平方缺口。其相位 `(x−y)(u+v(x+y))=u(x−y)+v(x²−y²)` 与原 W=(X,X²) 的差相符；第三目标的 s,t 是频率而非倾斜系数，不混淆。

唯一项目承重前置为已完整独立接受的实际 U15a `TiltedMeasureDomination.lean`，指定服务器实际 SHA256 `5445a68da1ac8302f174bfe2144eb8271a0af740fd6b91a87355abb41fed739b`。已直接读取其三个实际公开类型并核消费语义：同一 AE 支撑给任意二次指数真可积，正归一化后提供 exp(−2L(M+M²)) 的真实测度支配。其本身无 Shao 前置。本次不重做或重编已接受 U15a。

## 第三阶段：全部实际证明、private 与局部辅助

本节数学判断在读取 Audit TYPE 和机械证据前完成并落盘。

### 第 16–21 行：真正产品与标量平方

`Measure.prod_mono hdom hdom` 在两个坐标同时使用实际支配，得到 `(a•mu).prod(a•mu)≤nu.prod nu`，a=(m:ENNReal)。其上方右边际 nu 是真实概率，故 SFinite；下方标量右边际也有 SFinite(a•mu) 实例。随后 `Measure.prod_smul_left`、`Measure.prod_smul_right`、smul_smul、pow_two 把左侧精确化为 a²•mu.prod mu。两个 prod_smul 的真实名称确在 MeasureTheory.Measure 命名空间，不与全局 withDensity API 混淆。所有右边际 SFinite 门均具备，没有借产品在非 SFinite 时总化为零来冒充真实产品。m 为 NNReal，有限且可为零；证明不取消 m，没有隐藏 m>0。

### 第 23–30 行：唯一 authored private theorem

`cosine_pair_integrable` 针对任意真实概率 mu 与任意 u,v。K_uv 是连续实多项式复合 cos，故对真实产品 Borel 测度 AE 强可测；mu.prod mu 是真实概率，因而有限。Integrable.of_bound 取常数 2，在所有 z 而不只是 AE 小区域上，利用 cos≤1 给 K≥0，把 ‖K‖ 改成 K，再用 cos≥−1 得 K≤2。因此是真可积性，不是对无限 Lebesgue 体积套常数界，也不需要支撑界或频率窗口。

### 第 32–45 行：三处可积门、测度序与实系数

先 `hI_mu := cosine_pair_integrable mu u v`，再显式以 finite scalar 门 `((m:ENNReal)^2≠∞)` 得 `_hI_scaled := hI_mu.smul_measure ...`。该有限性由 NNReal 嵌入及其平方真实保证，m=0 也成立；不是 top.toReal 的零值退化。随后 `hI_nu` 对目标产品建立真实可积。虽然 integral_mono_measure 的实际类型仅要求上方可积，这里参考/标量参考的可积性仍在比较前明确建立，未遗漏含义。

hnonneg 是同一 nu.prod nu 上 K≥0，来自全局 cos≤1。integral_mono_measure 真实消费 prod_measure_domination、hnonneg、hI_nu，故左侧是有限标量参考测度上的真实积分。最后 simpa 仅使用 integral_smul_measure、ENNReal.toReal_pow、ENNReal.coe_toReal、smul_eq_mul，把它变为 `(m:ℝ)²∫K d(mu.prod mu)`。系数有限且实嵌入正确，无全局可测假设缺口，也未在未知可积时使用总化积分比较。

m=0 时左积分和系数均零，右积分实际非负；不消 m 或 m²。任意 u,v 的核由统一全局界 2 控制，无频率依赖的概率或可积前提。

### 第 47–78 行：真实两个倾斜概率与共同指数平方

局部 mu0、mu1 是同一基准 mu 的实际参考/新二次势 tilted。第 60–63 行两个普通 let 的值都是 `isProbabilityMeasure_tilted (quadratic_exp_integrable_of_ae_abs_le ...)`：先以同一 M,hM,hb 得指数真可积，再由基准 mu 的概率 NeZero 建立对应真实倾斜概率。这两个 let 仅向后续提供已证明的局部概率实例，不循环依赖产品结论，也未假定库中不可积 tilted=0 的分支为概率。

B=L(M+M²) 只依赖先固定的共同 M,L；m 是 NNReal.mk(exp(−2B),exp_nonneg)。实际 hm 用 `ENNReal.ofReal_eq_coe_nnreal`，精确识别正指数的 ofReal 与此 m 的嵌入，未错用反向 cast 或 toReal。hdom 在该识别后直接消费已独立接受的实际 U15a 测度支配，参考/新势、参数次序、hu/hv 全部相同。

真实两个概率实例已建立后，才调用 cosine_pair_integral_domination mu0 mu1 m hdom s t。hsquare 展开 NNReal 的实数值并用 pow_two、exp_add 和 ring 得 `(m:ℝ)²=exp(−4B)`；不是以 exp(−2B) 代替平方因子。最终 B 的定义展开与目标原式一致。

M,L 及 B、m 在所有 u0,v0,u,v 和 s,t 外固定，常数不依赖任何倾斜参数或频率。M=0 或 L=0 给 B=0、m=1，原支持上势 AE 一致，全部真实概率/可积步骤及结果有效；没有除 M/L 或加严格正前提。模块未引用公共特征函数恒等式或把所得积分擅自升级为 WC。

## 第四阶段：所消费的固定库实际语义

所有以下核对只读指定服务器源码，未 Lean/API probe：

- `Measure/Prod.lean` SHA256 `007561e86f53a65ad411fcbd20d05df9e922f01c5a93eff0f9de26ac49f12ca3`：172–175 行真实产品定义的 SFinite/非 SFinite 分支；224 行一般产品环境的 SFinite 右边际；427–432 行 Measure.prod_mono 要求上方右边际 SFinite；315–329 行产品有限/概率实例；877–881 行 Measure.prod_smul_left。代码具备所有必要门。
- `Measure/WithDensity.lean` SHA256 `cb47f52f610d82f9ad76e1146e551839d4b762f7157800d12a16b0d2e618e6d3`：684–688 行标量保持 SFinite，710 行 Prod 段环境右边际 SFinite，753–759 行 Measure.prod_smul_right。U15a 的 Tilted 真实公开导入链提供这些实例和名称。
- `Integral/Bochner/Basic.lean` SHA256 `66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670`：621–629 行 integral_mono_measure 要求测度序、上方 AE 非负和上方 Integrable；1047–1055 行 integral_smul_measure 的结果系数确为 ENNReal.toReal。`Function/L1Space/Integrable.lean` 314–317 行 Integrable.smul_measure 的门确为 c≠∞，已由代码显式提供。
- `Basic/ENNReal/Basic.lean` SHA256 `f7fe64f0d1865209e4d2be2fd98e3bc5edf9af508dd665f0311e6396f8d513a2`：265–267 行 ofReal_eq_coe_nnreal 恰识别 NNReal.mk x h；292 行 coe_toReal；411 行 coe_pow。`Basic/ENNReal/Real.lean` SHA256 `da5573e6bb7b196bd109724302c3db8eda3a3efab72c8db958ce2ddbf643cecf`，343–344 行 toReal_pow；本模块全部系数有限，未使用 top.toReal。
- `Analysis/Complex/Trigonometric.lean` SHA256 `f6f2c2bb6da4d7dac960bef8d07dc2e337c474b417726c1fd15e30c6b74caafb`：686–693 行 Real.cos_le_one、neg_one_le_cos。`Analysis/SpecialFunctions/Trigonometric/Basic.lean` SHA256 `85fc5b104bd61801d259dda6cf837892c30bc4b44a1b23688398476941770cf7`，99–100 行 Real.continuous_cos；真实 public 路径已在声明门静态核对，当前导入未改。
- 实际 Tilted.lean126–136 行 isProbabilityMeasure_tilted 要求 NeZero mu 与真正 Integrable(exp f)；此处两个 let 的证明先完整供给。U15a 的已审实际定理类型、正归一化与有限 ofReal 测度语义已按实际源核对。

全部 81 行实现、唯一 authored private 及全部局部辅助均已独立检查。数学阶段结论 CORRECT；随后才读取全部 actual TYPE，再读作者 receipt 与机械事实。


## 第五阶段：全部 4 个 actual owned TYPE

数学阶段先落盘后，仅过滤读取实际服务器 Audit.log 的 DECL/TYPE 及全部缩进续行，未提前读取 AXIOMS、PASS 或收据。实际清单为以下 4 项，均逐一核读而非只看计数：

1. `_private.Shao.OQ3.ProductMeasureDomination.0.Shao.OQ3.cosine_pair_integrable`：第 2–3 行完整类型，∀真实概率 mu、∀u,v:ℝ，实际 K_uv 对 mu.prod mu Integrable。没有支撑、频率或特征函数假设；恰对应已审私有有界积分引理。
2. `Shao.OQ3.cosine_pair_integral_domination`：第 6–11 行完整类型。mu、nu 均真实概率，m 的实际类型 NNReal，hdom 是 ENNReal 标量测度支配；随后∀u,v，实数嵌入 m 的平方乘参考真实产品积分≤目标产品积分。打印的 ↑m 在测度上下文与实积分上下文中分别为预期 ENNReal/Real 嵌入，并未把类型改成无穷标量。
3. `Shao.OQ3.prod_measure_domination`：第 14–15 行完整类型，两真实概率测度、m:NNReal、hdom 后得 ENNReal m² 标量的真实产品序。完整门与 actual/frozen 类型相同，没有多余 m>0 或不同参考测度。
4. `Shao.OQ3.quadratic_tilted_cosine_pair_domination`：实际第 18–44 行所有长续行完整读取。共同 M,L、hM/hL、同一 mu-AE 支撑门在∀u0,v0,u,v之前，hu/hv 后是∀s,t；系数精确 exp(−4L(M+M²))。左右参考/新实际 mu.tilted 的同律二重积与核的完整括号及相位全部一致，没有漏掉任一边际、换频率或增加隐藏可积假设。

真实 4 owned 项恰为 3 public theorem +1 private theorem，无 owned 定义或额外 generated 项。全部 actual TYPE 与数学语义/冻结目标吻合，类型阶段结论 CORRECT。随后才读作者 receipt/机械证据。


## 第六阶段：作者收据及真实机械证据最后绑定

全部实际数学和 TYPE 审查完成并落盘后才读取作者 receipt、Audit 源/AXIOMS/PASS、实际 build 日志和 pins。没有以作者绿灯代替独立证明判断。

- 本地 U15b-receipt.json 与实际 run/receipt.json SHA256 均为 `50313d3dfbdc1db61487557d1e42a0bd7a1effaa2ffdf428617c979d71c43316`。status 明确为 AUTHOR_KERNEL_AND_AXIOM_CHECKED_AWAITING_INDEPENDENT_PROOF_REVIEW；nonclaims 的终审 pending、未 commit/PR 限定在 author-check time，历史语义正确。implementation_environment_note 如实记录 open scoped ENNReal NNReal 与完整冻结类型未变。
- 本地 actual draft、实际 worktree/Shao/OQ3/ProductMeasureDomination.lean 及 run/ProductMeasureDomination.lean 三者 SHA256 均为 `9f05af79e47b9f778cbce7a0d19c0addea6d457eab5f088a69bf372f660c5a3f`，81 行、3847 字节。实际 run/scope.md SHA256 `36f3ecf090914d74c55a194809e68580643faf3da7ae7bb02f9252281319a322`；statement-review.md SHA256 `b28ebc81871ad03444c7d55860dad814b0cd670eac949421381fd1ca6ab88457`，均与本地冻结值一致。完整公开签名去空白比较由本审查独立执行为相同。
- 实际 build-03.log 为 0 字节，SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`。作者既有 receipt 记录命令 `lake env lean -o .lake/build/lib/lean/Shao/OQ3/ProductMeasureDomination.olean Shao/OQ3/ProductMeasureDomination.lean` 的 exit_code=0；本审查核对真实现存日志与产物而未重新执行命令，不将空日志自身当成独立 exit-code 证明。
- 实际 olean 存在，149352 字节，SHA256 `591df05b40c066845b825be9ed405503929a6c8ff04aec5f57d37e4381c2ed28`。
- 实际 Audit.lean 1544 字节，SHA256 `11fd0bb6fb13b7b04af99458e5df1cb1f1374825ce49388f1f953dbf9bbeed5d`，已完整读取代码。它先检查三个冻结名称存在且为 theorem，枚举三个公开 stem 的全部后代和整个 `_private.Shao.OQ3.ProductMeasureDomination` 前缀，拒绝 isAxiom，再对每个常量 collectAxioms 的所有传递依赖叶逐一核白名单 propext、Classical.choice、Quot.sound。结合完整源码只有 3 public+1 private、无额外定义或声明，该覆盖与实际 owned inventory 相符。
- 实际 Audit.log 2419 字节，SHA256 `76f52ba9fb9e7be93b8946d04a3659399b121c102f5c80af23e27aabd970e9a6`。全部 TYPE 已在前阶段逐项完整读取；本阶段又实际核四条 AXIOMS 均为白名单，无 sorryAx 或其他项目公理。末尾真实记录 `U15B_FROZEN_THEOREMS 3`、`U15B_ALL_THEOREMS 4`、`U15B_ALL_DECLARATIONS 4`、`U15B_AXIOM_GATE PASS`。作者 Audit exit_code=0 记录与真实源/log hash 一致，未重跑 Audit。
- 已从实际源递归独立枚举 Shao 导入闭包，恰为唯一 `Shao/OQ3/TiltedMeasureDomination.lean`，SHA256 `5445a68da1ac8302f174bfe2144eb8271a0af740fd6b91a87355abb41fed739b`；其本身无 Shao 导入。实际闭包与 receipt 的 imported_project_sources_sha256 和 run/prerequisite-hashes.json 完全相同，没有遗漏项目承重前置或消费缺失公共特征模块。
- 实际 lean-toolchain 内容 `leanprover/lean4:v4.36.0-rc1`，文件 SHA256 `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`；lake-manifest.json SHA256 `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`。Mathlib manifest rev 与实际 package git HEAD 均为 `807d3836b165983210ee2ecf3cd28f239436949c`，未跑 Lean/Lake 版本探针或编译。
- 观察时实际 branch `feat/oq3-product-measure-domination`，HEAD `54b4ad89cefaeeb9cfdbb8c14f6263218a4eb1f4`，git status 仅 `?? Shao/OQ3/ProductMeasureDomination.lean`。这是此次审查时点绑定，不限制 lead 随后获准的提交。独立实际源扫描无 CR、尾空白、sorry/admit/axiom/unsafe/implemented_by/extern。

本轮只通过共享 server.py 只读核查源、既有产物/日志的指定内容及散列；未改源码/scope/旧票/公共文件/缓存，未 spawn、Lean/API probe、重编成功 target/Audit 或下载完整原始日志。本审查唯一写入为本报告及授权服务器报告副本，不执行 commit/PR。

## 最终完整独立裁决

STATUS: CORRECT

JUSTIFICATION: 三个 actual 完整类型与冻结声明一致，R2 来源定位准确；全部 81 行实际证明、唯一 private 及所有局部辅助均独立审查。真正 SFinite 产品的标量重写给 m²；真实非负≤2余弦核可积，参考/有限标量参考/目标可积在积分序前实际建立，有限 toReal 系数正确；真实 U15a 指数可积先于两个倾斜概率实例，再给同一共同 exp(−4B) 系数。m=0/M=0/L=0 和全部参数/频率量词均合法。全部 4 actual TYPE、唯一项目依赖、真实源码/pins/既有 kernel 与传递公理审计一致。因此本票是完整独立 proof/source/type/机械绑定后的 CORRECT，区别于作者先行门与仅声明批准。

结论仅为标准充分的产品测度及真实余弦核积分支配，不识别特征函数模平方差，不证明 WC/除二常数/标准化、任意紧参数盒宽选择、无界扩展、最优常数、新颖性、KL、Lévy、LLT、hW 或根 C/其他根闭合。根 A/B/C/D 全部保持 OPEN。
