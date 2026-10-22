# 实际 Ξ 的一、二阶 u 导数：独立完整证明审查

STATUS: CORRECT

JUSTIFICATION: 已对原文语义、固定完整声明、实际新源码的全部定义与证明体、两次积分求导的所有前提、标准嵌套导数连接及真实矩预算作独立完整审查；并核对服务器实际编译、完整展开类型、13 个所属常量和 268 个导入项目常量的传递公理证据。未发现关键缺口。结论精确绑定作者提交 `82f477c88b63ca3b6a5d2371a9ef24e1a584ee8a` 及下列源码哈希。此前曾在本报告记为 INCOMPLETE 等待证据；最终证据已到齐，全部缺口已经核对消除。root 整合仍是后续独立步骤。

审查者：`/root/xi_derivative_proof_review`。本审查者是新鲜独立完整证明审查者，既非作者，也非此前声明审查者。已读 `AGENTS.md`、`SERVER.md`、实际位于 `coordination/TEAM.md` 的团队约束及 math-theorem 技能与所需参考文档。仅拥有本报告与 `proof-review.json`；没有修改生产源码、固定声明、作者回执或共享库；没有运行 Lean/Lake，没有创建子实例。

## 被审对象与原文身份

| 对象 | SHA256 / 固定身份 |
|---|---|
| 实际新源码 `QuadraticFullNoiseDerivatives.lean`，171 LF 行 | `25f432d891b1c2a115b5ca91b1fb89fc888d52bf28547c3606f022f7d30ddcf5` |
| 已声明审查的 proposal v2 | `46bfabdcdfc54701b3303c8ae1cc9e8ae6297794807af8dd201a4018d5581795` |
| source-map | `3a7af71ae90ad61a3d5ee37ba3ee28de89160c73e167a14486a5fd5aa42020b9` |
| root freeze.json | `cfdbb84ee7d8786325c79c11ba2b543994e513c10dd04dbc8263b58dcdcf321e` |
| 原 `supplement.tex` | `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd` |
| 原 `main.tex` | `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06` |
| 既有实际完整噪声 `QuadraticFullNoise.lean` | `a280ff36549f2c59356fd4fa89b3e442eece91f2a0e3bb4eea553d3605e1a116` |
| v40 既有验收回执 | `2ef611852d796dd446c21479c2f023d320a7333eddd75863d059f65db3d76108` |

以上文件哈希由本审查者直接重算。基线为 v40 accepted `dc1604d8e9c88781166a0c797f45b84ff013673a`、main `5591a25ddc767e6edfd618a88855075c2af7e375`。新源码所导入的八个 Shao 模块递归闭包逐文件重算哈希，全部与 v40 回执 `source_files_sha256` 一致；没有将旧工作树误当基线。具体八个模块与哈希见 JSON。

原文对应已直接阅读：`main.tex` LF650–679 给出方差偏置对、三角弦、两组 Fin8 独立弦族和独立平滑偶标量，LF665–666 定义真实 Z、Y，LF677 定义 `Ξ(u,v)=E exp(iuZ+ivY)`。`supplement.tex` LF486–498 给出真实完整噪声的支撑和 `E|Z|≤67γ/3`、`EZ²≤70hγ/3`；LF2595–2605 的 (b) 要求整个实平面上的两阶 u 导数界；LF3355–3356 以两个真实矩界完成该项。新代码补足原文略写的积分下求导，不把 (a)/(c)/(d) 或其他下游结论包含在认证范围。

## 固定声明、量词与实际对象

本审查者独立提取源码 `:= by` 之前的两个完整公开签名，与 freeze.json 的完整原文逐字比较。header 相同；两签名分别 SHA256 `aecfe0491042bf5322b18ff10304b33d85bb9714f3dbd55dd5cc288d872db54c` 与 `8baaf861356f752e4a97d573feeb82abdd894a56e104e7365729f852ce2d5b4d`，均与冻结值完全相同。文本公开面恰为两个 theorem、零个 public def，另有一个 private def 和九个 private lemma。没有隐藏 section 变量。

两声明共同输入恰为：真实 `ν : Measure ℝ`、`IsProbabilityMeasure ν`、`Integrable |a|³ ν`、真实 `variance id ν > 0`、实数 `h>0`、`ν` 下 AE `|a|≤h`、以及真实 `γ=(∫|a|³ dν)/(variance id ν)≤2h`，最后任意 `u0 v0 : ℝ`。没有源律中心化、频率非零、锥条件、额外独立性、可微性、候选导数身份或待证界作为输入。这里 variance 没有换成未中心化二阶矩，γ 也不是自由可调参数。

第一声明在源码 LF100–140 给出四项：真实特征函数的 `HasDerivAt`；真实标准一阶 `deriv` 函数的 `HasDerivAt`；实际一阶标准导数的积分身份；实际二阶嵌套标准导数的积分身份。两个局部 let 积分分别为

\[
d_1=\int iz_1\exp(i(u_0z_1+v_0z_2))\,d\mu,
\qquad d_2=\int -z_1^2\exp(i(u_0z_1+v_0z_2))\,d\mu,
\quad \mu=\operatorname{quadraticFullNoiseLaw}\nu.
\]

它们不是新公开定义或假定函数。第二声明 LF142–169 给出 `‖Ξ_u‖≤(67/3)γ` 与 `‖Ξ_uu‖≤(70/3)hγ`，数值除法明确为实数除法。

实际 Ξ 身份直接由既有源 LF13–31核对：两 Fin8 家族取积测度，连同固定 `sourceScalarLaw` 取积，再由 LF20–27 的真实 `quadraticFullNoiseMap` 推前；第一坐标是两组弦和的差加真实 γ 倍标量，第二坐标是两组 Y 的和。`quadraticFullNoiseChar` 正是该律下正号复相位积分。private `noisePhase` 仅为相同被积函数的定义缩写，不引入替代概率律或自由乘子。

## 全部新增证明节点逐项审读

| 源 LF | 节点 | 证明核对 |
|---|---|---|
| 9–10 | private `noisePhase` | 定义精确为 `exp(((u*z1+v*z2 : ℝ):ℂ)*I)`，与实际 Ξ 定义同形。 |
| 12–14 | `noisePhase_norm` | 实相位嵌入复数后乘 I 的实部为零，`norm_exp` 给出 exp(0)=1；对每个 z、u、v，无 AE 或符号限制。 |
| 16–19 | `firstPhase_norm` | 复范数乘法、`‖I‖=1`、实数复嵌入范数为绝对值，结果恰为 `|z1|`。 |
| 21–24 | `secondPhase_norm` | 负号范数无影响，`z1²≥0` 消除绝对值，结果恰为 `z1²`，没有把平方换成第一矩。 |
| 26–32 | `noisePhase_integrable` | 概率测度保证常数 1 可积；相位由连续表达式给出 AE 强可测，范数恒 1；`Integrable.mono'` 的两个前提全部提供。 |
| 34–39 | `firstPhase_integrable` | 只需真实 `Integrable |z1|`；连续复乘子及相位可测，范数等于 dominator。无多余概率/中心化输入。 |
| 41–46 | `secondPhase_integrable` | 同理只需真实 `Integrable z1²`；可测与范数支配均逐点成立。 |
| 48–57 | `noisePhase_hasDerivAt` | 实仿射相位导数为 z1；`.ofReal_comp`、`.mul_const I`、`.cexp` 给出 `exp(iθ)*(z1*I)`；`push_cast` 与交换环恒等式化成 `I*z1*exp(iθ)`，相位号和强转正确。 |
| 59–73 | `noiseIntegral_hasDerivAt` | 第一轮支配积分求导；七个条件全部覆盖，见下一节。API 取第二返回分量得真正积分函数的 HasDerivAt。 |
| 75–98 | `firstIntegral_hasDerivAt` | 第二轮支配积分求导；逐点导数由前节点常数乘 `I*z1` 得到，使用 `I*I=-1` 化成 `-z1² exp(iθ)`，没有更高矩输入。 |
| 100–140 | `quadraticFullNoiseChar_derivatives` | 真实律概率性取既有 law_data 的第三项；矩提取恰为第2、4项。LF128 声明 `hfirst (r : ℝ)`，因而 LF139 是所有 r 上的标准 deriv 身份。`congr_of_eventuallyEq` 正向把加权积分导数转移到真实 `deriv` 函数；最后四项分别由两 HasDerivAt 与其 `.deriv` 构造。 |
| 142–169 | `quadraticFullNoiseChar_derivative_bounds` | 取矩接口第2、4、5、8项；先用已证明标准积分身份改写，再用可积 dominator 和逐点范数界作 `norm_integral_le_of_norm_le`，最后传递真实矩预算。两个常数和 Z/Y 分量均无错位。 |

第一阶函数与实际 Ξ 之间依靠定义展开相等；这是既有 `quadraticFullNoiseChar` 与 private `noisePhase` 同一表达式的 definitional equality，不是调用者提供的识别假设。第二阶的识别在 LF138–139 使用对所有 r 的 `.deriv` 等式，因而产生目标点邻域内的 `EventuallyEq`；不是只在 u0 一个点相等，也不是只证明候选 d1 函数的导数。

## 两次支配积分求导的全部条件

服务器钉死 Mathlib `ParametricIntegral.lean` LF284–289 的实际 API 已只读核对。均取实参数、复值、`α=ℝ×ℝ`、同一测度 μ，`s=Set.univ`。

| API 条件 | 第一轮 LF64–73 | 第二轮 LF81–98 |
|---|---|---|
| `s∈𝓝 u` | univ 属于任意点邻域 | 相同 |
| 邻域最终 `AEStronglyMeasurable (F r)` | 每个 r 的相位可积性取 `.aestronglyMeasurable` | 每个 r 的一阶加权相位可积性取同分量 |
| `Integrable (F u)` | 概率律下相位被 1 支配 | 一阶相位被真实可积 `|z1|` 支配 |
| `AEStronglyMeasurable (F' u)` | `firstPhase_integrable` 提供 | `secondPhase_integrable` 提供 |
| `∀ᵐ z,∀r∈univ, ‖F' r z‖≤bound z` | 由每个 z、r 的范数恒等式，bound=`|z1|` | 同理，bound=`z1²` |
| dominator 可积 | 真实矩接口第2项 h1 | 真实矩接口第4项 h2 |
| `∀ᵐ z,∀r∈univ, HasDerivAt (F · z) (F' r z) r` | 逐点相位导数对所有 z、r 成立 | 逐点常数乘导数与 `I²=-1` 对所有 z、r 成立 |

AE 外层与全邻域内层量词顺序正确；代码用 `Eventually.of_forall` 从更强的逐点事实建立该顺序，没有交换异常零集与频率量词。第二轮基础函数可积性和导数可测性都在调用前显式建立，不依赖“Bochner 积分默认值”等退化行为。

独立只读核对的其他实际 API：`RealDeriv.lean` LF103–106 的 `.ofReal_comp`；`ExpDeriv.lean` LF133–135 的 `.cexp`；`Deriv/Basic.lean` LF436–437 的 `.deriv`、LF607–609 的 `.congr_of_eventuallyEq`；`L1Space/Integrable.lean` LF104–106 的 `.mono'`；`Bochner/Basic.lean` LF983–987 的积分范数比较。具体文件哈希见 JSON。首次只读脚本在已读四个接口后因远端无 rg 退出1；没有进行 Lean 或写入，随后只对未读的 `.cexp`/`.mono'` 精确文件取证成功，没有重跑既有成功的 Lean 检查。

## 实际矩接口、常数与边界

既有 `quadraticFullNoise_support_moments` LF275–291 的八项合取依次为：实际 AE 支撑、`Integrable |Z|`、`Integrable |Y|`、`Integrable Z²`、`E|Z|` 界、`E|Y|` 界、实际 Z² 独立分解、`EZ²` 界。新第一证明取第2、4项；新界证明取第2、4、5、8项，均准确。

已审读既有真实律与矩预算的承重证明体：概率性来自实际推前；支撑证明给出 Z 有界与 Z²可积；一阶预算是16个弦的 `(4/3)γ` 加标量至多 γ，等于 `(67/3)γ`；二阶预算使用实际中心弦/独立积的方差分解 `16 E[Z1²]+γ² E[V0²]`，再接弦 `(4/3)hγ`、`E[V0²]≤1`、`γ≥0` 和 `γ≤2h`，得到 `(70/3)hγ`。弦的均值零来自三角变量对称性，并非要求 ν 中心化。既有 `SourceFullNoiseBridge.lean` 的源条件律 rho 在 LF37–58 得到完整输入；原始 ν 的均值条件没有被错误转化成 rho 中心化要求。

u0、v0 完全任意；无频率除法、非零条件、截断或锥假设，坐标轴与原点均覆盖。证明仅对实 u 求复值导数，不声称复频率导数、v 导数或更高正则性。hV>0 与 h>0 按冻结契约保留；不存在把方差零情形硬塞入任意 γ 的处理。两界正好来自实际矩，没有较粗支撑界代替精确常数。

## 服务器实际证据绑定

本审查者在指定服务器工作树做第三次、纯只读取证，远端退出码0、stderr空，未运行 Lean。实际 `git rev-parse` 得到 head `82f477c88b63ca3b6a5d2371a9ef24e1a584ee8a`、parent `dc1604d8e9c88781166a0c797f45b84ff013673a`、branch `author/c12-xi-derivatives-v41`；该提交唯一变更路径正是目标新模块，tracked diff 为空。直接读取提交 Git blob 重算 SHA256，与本地、服务器当前源及 attempt01/02 源快照全部同为 `25f432…ddcf5`、7762字节。八个前驱在服务器逐一与父提交 blob 字节比较相等，并与本地 v40 receipt 哈希匹配。

固定实际环境：`leanprover/lean4:v4.36.0-rc1`；已有服务器版本输出为 Lean 4.36.0-rc1、commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`；本审查者直接确认 Mathlib HEAD `807d3836b165983210ee2ecf3cd28f239436949c`、manifest SHA256 `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`。两次重型运行的 preflight 均显示自身 CPU10–13、外部 PID143204 为 CPU0–9，且当时无其他 Lean/Lake 进程。

| 实际服务器门 | 命令与结果 | 完整日志 SHA256 |
|---|---|---|
| 首次实际目标编译 | `lake env lean -j4 -M8192 -DautoImplicit=false -o .lake/build/lib/lean/Shao/Probability/QuadraticFullNoiseDerivatives.olean Shao/Probability/QuadraticFullNoiseDerivatives.lean`；exit0，6.921437秒，maxRSS3409012KiB | `51c34acb1f50fb265f877743d9162c7f2932ba37876f417a582cf8bfb5f175e7` |
| 完整实际所属/传递审计及实际类型输出 | `lake env lean -j4 -M8192 -DautoImplicit=false logs/c12-xi-derivatives/Audit.lean`；exit0，6.546821秒，maxRSS3758452KiB | `e1fb7fb6019851a11d88311ee4268c870bfa5924a32f0590e1df965aa3c2d48d` |

编译对象实际 SHA256 `71717c930b11f7ac25242cb9ae49191e615b829b14e9dcdba7c822db9efe6648`、358208字节，本审查者直接在服务器重算，与作者 metadata/receipt 一致。实际编译日志只有既有 Mathlib local-changes 提示；审计日志包含13项 TARGET_DECL、正确总数、完整实际类型边界标记，以及两个公开定理各自的标准三公理输出。本审查者没有重复成功的编译或审计。

作者首次 runner 因缺 `/usr/bin/time` 在 Lean 启动前失败；实际读到 `lean_started=false`、空日志哈希及保存的错误记录。这不等于 Lean 失败后修补证明，不能记为额外一次 Lean 运行。另有作者已披露的只读 untracked/cache 路径误枚举；其有界事件记录和服务器原始元数据哈希已匹配，记录为0共享写入/0缓存写入/0额外编译。本审查未再次枚举缓存，也不据固定 Mathlib HEAD 声称共享源工作树 clean。

## 实际类型与所属/private/generated 全清单

`actual-public-types.txt` 的500行完整 pp.all 输出已逐段审读，SHA256 `a31bf56ee3c08a71b0862d05e2c1b7cbb682d6bb86dbd71520b2025cedbec2d4`，与服务器同名产物一致。第一类型 LF2–52 的全部 binders 恰为固定输入；LF53–93 的两个 let 积分使用同一实际律和正号实相位，第二乘子为负实平方的复嵌入；LF94–340 是预期四项合取，第二 HasDerivAt 和第四身份均为标准嵌套 `deriv`。第二类型 LF341–403 保留同一输入和真实 γ；LF404–499 的两个不等式明确是复范数、实数 `67/3`、实数 `70/3` 及后者乘 hγ。所有实标量与复空间实例在 pp.all 中具体展开，没有额外调用者提供的范数空间实例、隐含中心化、频率限制或可微前提。

审计程序 `Audit.lean` SHA256 `54a6ac03ba7ba90ac4eae3a7182d241d9494900dce522740477940f1cb191eb3` 已完整阅读。它遍历实际环境全部 constants，先用 `env.getModuleIdxFor?` 取得真实 owner；对所有 Shao-owner 常量逐项 `Lean.collectAxioms`（递归包含其 Mathlib 依赖），拒绝任何白名单外公理，再以目标 owner 选所属项。它没有按名称前缀或仅 public theorem 限缩目标所属范围。

实际目标13项中，两个公开项为本报告上述完整名称；其余项统一真实前缀为 `_private.Shao.Probability.QuadraticFullNoiseDerivatives.0.Shao.Probability.`，完整后缀与 kind 如下：

| 后缀 | kind | 来源对应 |
|---|---|---|
| `noisePhase` | definition | LF9–10 private 定义 |
| `noisePhase.eq_1` | theorem | 该定义自动生成的展开方程，计入所属及公理审计 |
| `noisePhase_norm` | theorem | LF12–14 |
| `firstPhase_norm` | theorem | LF16–19 |
| `secondPhase_norm` | theorem | LF21–24 |
| `noisePhase_integrable` | theorem | LF26–32 |
| `firstPhase_integrable` | theorem | LF34–39 |
| `secondPhase_integrable` | theorem | LF41–46 |
| `noisePhase_hasDerivAt` | theorem | LF48–57 |
| `noiseIntegral_hasDerivAt` | theorem | LF59–73 |
| `firstIntegral_hasDerivAt` | theorem | LF75–98 |

这正是12 theorem/1 definition，包括2 public theorem、9显式 private theorem、1自动生成方程；零 public definition。13项唯一、与完整268项清单中目标 owner 的精确筛选逐项相等，没有漏项或额外公开项。自动生成方程对应已审的同一相位定义，不引入额外数学假设。

268个实际导入项目常量名称全部唯一；对每一行实际验证 owner、kind、全部 axioms 数组，无白名单外项。按 owner 计数为：FinitePath67、FiniteIID8、QuadraticCharacteristic30、LowFrequencyDamping30、QuadraticChordNoise55、QuadraticChordMoments20、SourceScalarNoise16、QuadraticFullNoise29、目标模块13；恰是本报告独立解析的9模块导入闭包。总 kind 为236 theorem/32 definition。实际公理并集仅为 `propext`、`Classical.choice`、`Quot.sound`；没有 sorryAx、新 axiom 或其他传递公理。源文本独立扫描也没有 sorry/admit/axiom/unsafe/native_decide。

`owned-audit.json` 完整清单 SHA256 `37f92624dc286b9469f06db5d6d63542ada6c60d1cf7f325781bb3250108d2df`；作者 MD 收据 SHA256 `b813c2a2c851827bb4de622e63fb1c955d0c0960bc3874677687e0e19f1e9b5e`，JSON 收据 `83084da3496a431b08256443758aaa9cda4897f9a6ae3bf731586a2a69a56ed2`；`evidence-hashes.json` 为 `5792d80667b04450b319a764f65a80ed1f2ef8ec36fea28447a0121c22ecafe8`。所有本地现存证据的哈希与 manifest、作者 receipt 对应条目一致；服务器20个固定证据文件的实际哈希亦全部逐项匹配。完整原始日志留服务器，没有下载缓存或原始大元数据。

## 最终裁决与停止

精确两个公开定理的全文源语义、冻结声明、全部证明和实际服务器证据审查：CORRECT。机械层状态：`LEAN_FULLY_CHECKED`，仅指这个冻结二定理模块；本审查者复核实际证据而未独立重跑 Lean。关键数学缺口、证据缺口：均无。只拥有本 MD/JSON 审查产物，完成后 STOP。

本节点仅覆盖 `h:supp:highderivatives(b)` 的实际 Ξ 两阶 u 导数、两个积分身份与精确全局界。锥内 (a)、高频 (c)/(d)、乘积求导、反演、去平滑、C1/C2 原根均不在本次闭合声明内；不作新颖性结论。
