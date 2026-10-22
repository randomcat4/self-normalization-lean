# U15a 完整独立证明、来源与类型审查

STATUS: CORRECT

审查者沿用唯一 lease 1，仅拥有本报告及指定服务器对应 proof-review.md，不修改实现、scope、旧票、公共文件或缓存，不 spawn。既有声明审查上下文存在；本阶段仍先仅提取 actual 三个公开完整类型，重新独立盲译并先落盘，尚未读取本次实现证明或机械证据。

## 第一阶段：actual 三个完整公开类型盲译

输入实际 drafts/oq3/TiltedMeasureDomination.lean，SHA256 5445a68da1ac8302f174bfe2144eb8271a0af740fd6b91a87355abb41fed739b，105 行。零公开定义，本阶段只读取提取后的三个完整公开类型。

1. `quadratic_exp_integrable_of_ae_abs_le (mu : Measure ℝ) [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M) (hb : ∀ᵐ x ∂mu, |x| ≤ M) (u v : ℝ)`：任意实数上的真实概率测度 mu，给定 M≥0 和同一 mu 的 AE 支撑界 |x|≤M 后，对全部任意实系数 u,v，函数 exp(ux+vx²) 真正可积于 mu。M=0 包含；没有从总化积分或倾斜名称替代 Integrable。

2. `tilted_measure_domination_of_abs_sub_le (mu : Measure ℝ) [IsProbabilityMeasure mu] (f g : ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hf : Integrable (fun x => Real.exp (f x)) mu) (hg : Integrable (fun x => Real.exp (g x)) mu) (hfg : ∀ᵐ x ∂mu, |g x - f x| ≤ B)`：对同一概率测度、任意实势 f,g 和 B≥0，若 exp f、exp g 真可积，且势差的绝对值在同一 mu-AE 集合上≤B，则真实测度序满足 ofReal(exp(−2B))·mu.tilted f≤mu.tilted g。f,g 不假定全局可测，须核真实 AE/可积门是否已足够。标量是有限的 ENNReal.ofReal，B=0 包含。

3. `quadratic_tilted_measure_domination (mu : Measure ℝ) [IsProbabilityMeasure mu] (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L) (hb : ∀ᵐ x ∂mu, |x| ≤ M) (u0 v0 u v : ℝ) (hu : |u - u0| ≤ L) (hv : |v - v0| ≤ L)`：先共同固定 mu、M≥0、L≥0 与 AE 支撑门，再对任意四个参考/新实系数，只要两个系数差分别≤L，参考二次势倾斜测度乘固定正有限系数 ofReal(exp(−2L(M+M²))) 后≤新二次势倾斜测度。共同 M,L 及系数均在四个参数外。结论没有指数可积假设，故证明须由同一 hb 推导，而不能默认两个 tilted 是概率。M=0、L=0 均保留。

此盲译已先落盘。后续按 scope/R2→全部实际证明/private/locals/固定库→全部 actual TYPE→receipt/机械顺序审查。根 A/B/C/D 全部保持 OPEN。


## 第二阶段：冻结范围与真实来源

盲译先落盘后才读取完整 scope、此前声明票、实际 105 行实现及真实 R2。三个 actual 公开完整类型与 scope 去空白逐字相同；无公开定义或假设变化。scope SHA256 `efc6102ad3b91d3122455157faf0564f066a796eaf7ac02ddc0c9a0f52a800c2`；此前 statement-review SHA256 `aec1995f372c93fccf1108e5b37fe87623102b55dc7d8e8f00fc74d90431223d`；实际 R2 `C:/game/shao/current/oq3/proofs/r2/report.md` SHA256 `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55`。

直接读取 R2 第 38–43、343–373 行：基础族是 W=(X,X²)、K(theta)=log E exp(theta·W)、dP_theta=exp(theta·W−K(theta))dP；本单元的同一 mu 上二次势正是原始坐标表达。第 345–352 行式 (20) 要求共同正密度下界，本单元提供其充分的实际测度序形式，常数 exp(−2L(M+M²))。它没有定义 RN 导数，也不自动完成第 354–363 行两样本/平方缺口、后面的 WC 或紧参数盒宽选择。R2 明确警告无界 X 时 (20) 一般为假；实际代码保留 AE 支撑界，未用高斯阻尼或有限矩取代它。

实际源码导入 Tilted、Exp 和六个明确 tactic 模块，没有任何 Shao 项目导入。所有结论直接针对库中真正 mu.tilted，未复制根公共模块、替换成自定义倾斜律或引入尚未证实的概率/RN 假设。

## 第三阶段：全部实际证明、private 与局部辅助

以下数学审查在读取 actual Audit TYPE 与作者机械证据前完成并落盘。

### 第 14–15 行：唯一 authored private theorem

`square_le_of_abs_le (x M : ℝ) (hx : |x|≤M) : x²≤M²` 使用 pow_le_pow_left₀：较小底数 |x|≥0，底数序正是 hx，再以 sq_abs 化简。它虽无独立 hM 参数，但 hx 已强制 M≥|x|≥0；不需要偷偷假设 M>0，M=0 合法。

### 第 17–34 行：真实指数可积

`_hC` 显式记录 |u|M+|v|M²≥0，分别用 hM 和平方非负性，事实真实。Integrable.of_bound 的常数是有限正数 C=exp(|u|M+|v|M²)，不是对全实线声称该函数有界。函数全局连续，fun_prop 所要求的 AE 强可测性真实成立；mu 概率给有限测度。在 hb 的同一 mu-AE 集合上，代码先使用正指数的范数等于自身，再以指数保序比较实势：

`ux+vx²≤|ux|+|vx²|=|u||x|+|v|x²≤|u|M+|v|M²`。

后一步实际使用 private square bound，乘法因子 |u|、|v| 均非负。因而真正 AE 范数界完成后才得到 Integrable；没有对无限体积全实线作常数可积性误用，也没有先凭 tilted 名称断言概率。M=0 时 x=0 AE、指数为 1 AE；u,v 任意且未被偷偷加界。此处逐 u,v 的可积 bound 可依赖 u,v，后面的统一测度因子则不会依赖它。

### 第 36–57 行：真实归一化与指数上界

局部 Zf、Zg 是 exp f、exp g 对同一 mu 的实际 Bochner 实积分。hZf、hZg 分别调用 integral_exp_pos hf/hg；mu 的真实概率实例给 NeZero mu，因此两者严格正，不来自总化积分的默认值。`_hscale` 利用 hB≥0 显式记录 exp(−2B)≤1，正确且未要求 B>0。

hu 在 hfg 的同一 AE 集合上，由 g−f≤B 得 g≤B+f，再用指数加法与保序给 exp g≤exp B·exp f。hupper 调用 `integral_mono_ae hg (hf.const_mul (exp B)) hu`，两边真正可积都已提供；再用 integral_const_mul 才得到 Zg≤exp B·Zf。没有在未知可积时用积分单调性。局部 hc 为 exp(−2B)exp B=exp(−B)，以指数加法和 −2B+B=−B 的精确 ring 恒等式证明。

### 第 58–79 行：实际 AE 密度比较提升为测度序

代码先展开真正 `Measure.tilted` 的 withDensity 定义。实际使用的名称是全局 `MeasureTheory.withDensity_smul'` 和 `MeasureTheory.withDensity_mono`（由 open MeasureTheory 可见），不是不存在的 `MeasureTheory.Measure.withDensity_mono` / `Measure.withDensity_smul'`。scope 中对 Measure.withDensity_mono 的口语式简称不能作为实际完整 namespace；旧 scope/声明票不追改，本票如实记载固定库与成功实现使用的真正名称。

withDensity_smul' 的关键门是标量≠∞；实际提供 ENNReal.ofReal_ne_top，因此可把左边 scalar·mu.withDensity 反向改写为 mu.withDensity(pointwise scalar·density)，无需 f/g 全局可测。withDensity_mono 随后要求同一 mu 下 AE 点乘密度比较。代码 filter_upwards hfg 后，实际目标是

`ofReal(exp(−2B))·ofReal(exp f/Zf)≤ofReal(exp g/Zg)`。

反向 ofReal_mul 使用严格正 exp(−2B) 的非负性；ofReal_le_ofReal 把真实实数序提升到 ENNReal，未用 toReal 或任何无穷值转换。hx 的下半部 −B≤g−f 给 hlower：exp(−B)exp f≤exp g。

用 mul_div_assoc 后，div_le_div_iff₀ 真实消费两个正分母 hZf,hZg，将目标交叉乘为

`[exp(−2B)exp f]Zg≤exp g·Zf`。

左边先以 hupper 放大 Zg，其乘法系数非负；结合 hc 精确成为 `[exp(−B)exp f]Zf`；再用 hlower 乘 Zf≥0 完成。方向与 −2B 常数正确。hfg 同时用于全局积分上界与此处 AE 下界，没有换成不同基准测度的 AE 门。

hf/hg 不要求 f/g 全局可测并非漏洞：它们已提供指数的真实可积及 AE 强可测性；库 withDensity_mono 只要求 AE 密度序，有限标量版本 withDensity_smul' 也不要求密度全局可测。真实 tilted 的不可积时零测度分支已由 hf/hg 排除。B=0 时全部步骤仍成立、因子为 1，无除 B 操作。

### 第 81–102 行：共同二次参数盒

实际 apply 目标二时 B=L(M+M²)≥0 由 hL,hM 与平方非负性提供；f 与 g 分别为实际参考/新二次势。先两次调用目标一，真实得到同一 mu 上两个指数的 Integrable，再审 AE 势差。

在同一个 hb-AE 集合上，ring 给精确差 `(u−u0)x+(v−v0)x²`；abs_add_le、abs_mul 和 |x²|=x² 给三角上界。两次实际 mul_le_mul 的前提分别为 hu、hx、|x|≥0、L≥0，以及 hv、private square bound、x²≥0、L≥0，故上界为 LM+LM²=L(M+M²)。没有把乘法符号或两个系数位置颠倒。M,L 在全部 u0,v0,u,v 之前固定；最终系数只含共同 M,L，没有隐藏的每参数常数。基准参数的绝对大小无需额外限制。

M=0 或 L=0 给 B=0，未被 positivity 误要求严格正，也未除它们。两个边界下相应势在同一支持上 AE 一致，测度下界以因子 1 合法成立。没有平方缺口、特征函数或根 C 结论被夹带进 apply。

## 第四阶段：所消费的实际固定库语义

指定服务器只读源码核对下列实际接口，未运行 Lean/probe：

- Tilted.lean SHA256 `355cce542b03dd9130d9511f80ae803cc11a12ba9e6a947e68402b124be2165f`，42–43 行确为 mu.withDensity(ofReal(exp f/∫exp f))；46–54 行不可积/非 AE 可测分支为零测度；126–136 行真实概率性需要 NeZero 与 exp 可积。源码没有未经证明地使用其概率性来倒推可积性。
- WithDensity.lean SHA256 `cb47f52f610d82f9ad76e1146e551839d4b762f7157800d12a16b0d2e618e6d3`，32 行 namespace MeasureTheory，102–107 行全局 withDensity_mono 的门仅 f≤ᵐg；137–142 行全局 withDensity_smul' 的门为 r≠∞。实际代码名字与门均吻合。
- IntegrableOn.lean SHA256 `d1108ec5e836af0af6bc62c8ad5dd94a371dbc8df3e51698049d51221b3663c2`，171–172 行 Integrable.of_bound 需要 IsFiniteMeasure、AEStronglyMeasurable、真实 AE 范数 bound。Real 的实际 Borel/第二可数结构与连续指数多项式满足可测门。
- Bochner/Basic.lean SHA256 `66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670`，662–667 行 integral_mono_ae 要求两函数 Integrable，代码明确提供；288–293 行积分常数乘法接口；792–798 行 integral_exp_pos 要求 NeZero 与真实 exp Integrable。L1Space/Integrable.lean 1028–1030 行 Integrable.const_mul 确实从 Integrable f 得到 Integrable(c·f)，适用于 hupper。
- Basic/ENNReal/Real.lean SHA256 `da5573e6bb7b196bd109724302c3db8eda3a3efab72c8db958ce2ddbf643cecf`，297–303 行 ofReal_mul/ofReal_mul' 保留非负因子门；Basic/ENNReal/Basic.lean SHA256 `f7fe64f0d1865209e4d2be2fd98e3bc5edf9af508dd665f0311e6396f8d513a2`，347 行 ofReal_ne_top 无额外有限性假设。这里始终真实有限 ofReal 标量，未涉及 top.toReal。
- Analysis/Complex/Exponential.lean SHA256 `35d9f9e6abaf24d09a25cb1eeefbfc4180c3fe18de4d47362704c2f9f6601146`，212 行 Real.exp_add，284 行 exp_pos，317–318 行 exp_le_exp，340–341 行 exp_le_one_iff。代码使用的每个指数符号方向正确。

声明阶段已直接核对的公开 import 链向上述 IntegrableOn、Bochner.Basic、WithDensity、概率 NeZero 实例和连续函数 AE 强可测接口开放；本次实现未改变导入、定义或类型，仅实际使用正确全局 namespace。全部 105 行实现、唯一 authored private 及所有局部 have 已独立检查，数学阶段结论 CORRECT。随后才核 actual TYPE，再读机械证据。


## 第五阶段：全部 4 个 actual owned TYPE

数学阶段先落盘后，仅过滤读取指定服务器现有 Audit.log 的 DECL/TYPE 和全部缩进续行；尚未读取 AXIOMS/PASS/build/receipt。实际枚举恰为以下 4 项，而不是从预期数量推断：

1. `Shao.OQ3.tilted_measure_domination_of_abs_sub_le`：完整读取第 2–6 行。∀真实 mu:Measure ℝ，[IsProbabilityMeasure mu]，∀f,g:ℝ→ℝ、B:ℝ，0≤B→Integrable(exp f)mu→Integrable(exp g)mu→(mu-AE |g−f|≤B)→ofReal(exp(−2B))·mu.tilted f≤mu.tilted g。两个真实可积门保留，无额外全局可测假设，方向与冻结类型相同。
2. `Shao.OQ3.quadratic_tilted_measure_domination`：完整读取第 9–17 行全部长续行。mu 概率、共同 M,L 及非负性和 hb 均在 ∀u0,v0,u,v 之前；hu/hv 分别对应两个系数差，系数实际是 exp(−2(L(M+M²)))。两边仍是真实二次势 mu.tilted。没有参数依赖的替代常数或额外可积前提，M=0/L=0 允许。
3. `_private.Shao.OQ3.TiltedMeasureDomination.0.Shao.OQ3.square_le_of_abs_le`：∀x,M:ℝ，|x|≤M→x²≤M²。确是唯一 authored private 结论；类型无隐藏 hM>0，hx 已足以保证平方比较。已与第 14–15 行实际证明核对。
4. `Shao.OQ3.quadratic_exp_integrable_of_ae_abs_le`：完整读取第 23–24 行。mu 概率、M≥0、mu-AE |x|≤M，随后∀u,v:ℝ，实际 exp 二次势 Integrable mu。与冻结目标相同，是真可积而不是单一积分值。

实际 4 项全部 theorem：3 public +1 private，无 owned 定义，无额外 generated 常量或隐藏生成接口。本次未用计数替代类型阅读；每项完整类型及续行均实际核对，类型阶段结论 CORRECT。之后才开始读取作者收据和机械证据。


## 第六阶段：作者收据与真实机械证据最后绑定

完成并落盘数学及全部实际 TYPE 审查后，才读取作者收据、Audit 源与 AXIOMS/PASS、现有构建日志和实际 pins。作者绿灯不是上述独立判断的依据。

- 本地 U15a-receipt.json 与实际服务器 run/receipt.json SHA256 均为 `f0d3369168bb5b97111a56a79a1342be5de9b7597040783e496b59ebf345d820`。status 为 AUTHOR_KERNEL_AND_AXIOM_CHECKED_AWAITING_INDEPENDENT_PROOF_REVIEW；nonclaims 的终审 pending、未 commit/PR 均明确限定在 author-check time，符合实际历史时点。
- 本地 draft、实际 worktree/Shao/OQ3/TiltedMeasureDomination.lean 和 run/TiltedMeasureDomination.lean 三者 SHA256 均为 `5445a68da1ac8302f174bfe2144eb8271a0af740fd6b91a87355abb41fed739b`；105 行、4754 字节。实际 run/scope.md SHA256 `efc6102ad3b91d3122455157faf0564f066a796eaf7ac02ddc0c9a0f52a800c2`；run/statement-review.md SHA256 `aec1995f372c93fccf1108e5b37fe87623102b55dc7d8e8f00fc74d90431223d`，与本地冻结值一致。三个完整签名去空白匹配已独立核对，不是仅引用收据的 PASS。
- 实际 build-02.log 为 0 字节，SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`。既有收据记录命令 `lake env lean -o .lake/build/lib/lean/Shao/OQ3/TiltedMeasureDomination.olean Shao/OQ3/TiltedMeasureDomination.lean` 的 exit_code=0。此处核对现存日志与产物，不重复构建；空日志本身未被误称为独立的 exit-code 证明。
- 实际目标 olean 存在，231752 字节，SHA256 `f8cc665a94eedcef80779b4611a152577a8712b909528cad0f1d1da78e5b2ace`。
- 实际 Audit.lean 为 1560 字节，SHA256 `48ef7dc7da61314accfa85cc7393b204f703bc7c119a6778ade48f4cbb8f40b5`，已完整读取代码。它先验证三个冻结名称存在且为 theorem，覆盖全部三个公开 stem 后代与整个 `_private.Shao.OQ3.TiltedMeasureDomination` 前缀；拒绝 isAxiom，并对每项 Lean.collectAxioms 的传递叶逐一限制在 propext、Classical.choice、Quot.sound。结合实际完整源码仅 3 public+1 private、无定义/额外公理的声明清单，该覆盖与真实 owned inventory 完全一致。
- 实际 Audit.log 为 1599 字节，SHA256 `cd48f458145e754d243b2207a8905f6a3c693402306622abd274c8f20ec47e7d`。本阶段实际读取四条 AXIOMS，均只有 propext、Classical.choice、Quot.sound，没有 sorryAx 或额外项目公理；实际末行 `U15A_FROZEN_THEOREMS 3`、`U15A_ALL_THEOREMS 4`、`U15A_ALL_DECLARATIONS 4`、`U15A_AXIOM_GATE PASS`。作者 Audit exit_code=0 记录与实际源/log hash 相同；未重跑 Audit。
- 已独立扫描实际 import 声明：没有 Shao.* 导入，故整个项目源码前置闭包为空；与 receipt 的 imported_project_sources_sha256={} 相同。本单元无需且未消费缺失的其他公共特征函数源码/olean。真实 Mathlib 接口、其归一化/可积语义和固定源码 hash 已在第四阶段核对。
- 实际 lean-toolchain 内容为 `leanprover/lean4:v4.36.0-rc1`，文件 SHA256 `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`；lake-manifest.json SHA256 `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`。manifest 中 Mathlib rev 与实际 package git HEAD 均为 `807d3836b165983210ee2ecf3cd28f239436949c`；没有运行版本探针或构建。
- 观察时实际 branch `feat/oq3-tilted-measure-domination`，HEAD `4f183919def05aa69082a0fe0584bf023f5bb507`，git status 仅 `?? Shao/OQ3/TiltedMeasureDomination.lean`。此为审查时点绑定，不妨碍 lead 随后获准提交。实际源码无 CR、无尾空白，独立禁止项扫描无 sorry/admit/axiom/unsafe/implemented_by/extern。

全程只通过共享 server.py 只读服务器源、既有产物和散列；没有 Lean/API probe、重编成功 target/Audit、cache 写入、spawn、source/scope/旧票/共享文件改动或完整原始日志下载。本轮仅写本报告与授权的服务器报告副本，不执行 commit/PR。

## 最终完整独立裁决

STATUS: CORRECT

JUSTIFICATION: 实际三完整公开类型与冻结声明严格一致，来源准确对应 R2 式 (20) 的标准充分测度下界。全部 105 行证明、唯一 private square bound 与所有局部辅助已逐步独立审查；真实可积门先于积分比较，hf/hg 与概率 NeZero 给真正严格正归一化，同一 AE 势差的上下指数比较和两个正分母交叉乘方向正确，有限 ofReal 标量通过实际全局 withDensity 接口形成真实测度序。共同 M,L 与 M=0/L=0 均真实保留。全部 4 actual TYPE、零项目依赖闭包、实际源码/版本/既有 kernel 和传递公理证据均核对一致。本票因此是完整独立 proof/source/type/机械绑定的 CORRECT，区别于作者先行门及仅声明批准。

本单元未证明 RN 导数识别、两样本恒等式、平方特征缺口、WC 传递/标准化、任意紧参数集盒宽选择、无界扩展、KL/global-minimizer、最优性、新颖性、LLT、hW 或任何根闭合。根 A/B/C/D 全部保持 OPEN。
