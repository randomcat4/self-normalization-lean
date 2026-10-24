# SourceDesmoothing 独立完整终审

STATUS: **CORRECT**

本裁决仅覆盖冻结的八个公开头及其完整证明。第五头是带显式 PB、END、SM 输入的实际固定截断律去平滑消费者；三项生产义务仍为 **OPEN**。本报告不接受或合并提交，不扩大 C1/C2、OQ3、OQ4、OQ56 原根组的闭合范围。

审查者 `/root/common_desmoothing_full_review`，全新独立上下文，实际 `gpt-6.1-sol` / `xhigh`，非作者。按 math-theorem 执行，没有子代理。作者完成并释放写权后开始审查；只写本报告、同名 JSON、coverage JSON 和 `drafts/c12-desmoothing-review/`。没有修改冻结源码、旧证据、共享配置或缓存，没有运行 Lean、构建、公理审计、旧 producer，也没有 PR 或合并操作。

## 精确绑定与覆盖

审查的唯一新文件为 `Shao/Probability/SourceDesmoothing.lean`，本地完整副本 `drafts/c12-desmoothing/SourceDesmoothing.lean`，833 行、42090 字节，UTF-8、LF、无 BOM。

| 项目 | 精确值 |
|---|---|
| 远程工作树 | `/root/rivermind-data/shao-lean-20261021/workspaces/common-short-kernel-v51` |
| 分支 | `feat/common-desmoothing` |
| commit | `5e9c349425c4829e6ab35f18189636018e2b07a7` |
| tree | `a433e760b12c0080184e806d944414c411a31d1d` |
| parent | `cd317e79f91d65a428b465f52e4dea27cb48167c` |
| 源码 SHA256 | `8947e669f554a7d4aaefe04250a90b4deed2ec909da260f13ac5f58925790240` |
| 首次整源成功保留对象 SHA256 | `ae8e9426e44823c222ac026cf63508ddf9693c14b34c420e985db726a0eed967` |
| 完整实际类型 JSON SHA256 | `4abd937d63d889fb749e56d462190066efd7daf76ca341e047a4cfe1972a9549` |
| 唯一所属项审计日志 SHA256 | `4d7fbd836062066c1d9498ad167aa8abf46aed59390f7f261cf799cc17102283` |

完整读取 `AUTHOR_HANDOFF.md`、`author-handoff.json`、冻结文件、八头候选及全部证明候选第 1–11 节。冻结 SHA256 为 `d12b3ce0786141e9ae0efd0f8f4f3fe7d32a2984b81f4ac562f84bdb2d2fc244`；八头候选为 `fb0680612f3957d8e94d15b3461edeeeca6f96a98523ca728ad3c6aaf6955163`；证明候选为 `bdf00ff830aaf40679e8f4b8e43a5a19bf61d11897eec1339a0ffa64fbd535da`；作者交接 JSON 为 `3a25ff577d8f2537952c8947ddf1eb0ab0c2ead336e8ce515031d69323024db4`。八个完整公开头逐字匹配冻结候选，包含每个量词、假设和局部字面值。候选开头的历史未选定提示由后来的根冻结文件取代，不改变候选字节或数学内容。

全部新源码的陈述及证明已逐段读完。24/24 实际所属常量的完整实际类型与逐项传递公理已全部读取：8 公开项、16 生成项，24 项均为 theorem；0 definition、0 新增源码 private helper。所属项按实际模块归属枚举，包含外命名空间 `Shao.upperCrossing.congr_simp`，没有以名称前缀缩减范围。

大类型采用无损字面因子化：完整读了 `drafts/c12-desmoothing-review/factors.txt` 的 32 个因子和 `type-00.txt` 至 `type-23.txt` 全部有序残差。反向展开每个因子后，24 项均与原 `actual_type` UTF-8 字节逐字相同；并在服务器只读解析原审计日志，24 个名字及类型全部与本地完整类型一致。因子化是阅读表示，没有省略命题内容。覆盖清单逐项给出名字、类型哈希、AX、公私/生成分类、数学审查范围和精确类型位置。

局部绑定计数直接从新源码导出：**82 个 `let`/`letI` 出现，78 个普通 `let` 与 4 个 `letI`**；其中公开陈述 35 个普通 `let`，证明 43 个普通 `let` 加 4 个 `letI`。每个字面值已随完整源码读取；`local-inspection.json` 保存全部完整绑定文本、位置和哈希，未把 proof-local 实例隐藏在定义数为零的统计中。

## 原文与旧接口

原文 `C:/game/shao/current/c12/main.tex` SHA256 为 `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`，supplement 为 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`。完整阅读本次依赖的主文 184–196、301–329、372–558、610–667、762–858，以及补充材料 216–239、1034–1067、3851–3909；核对严格 CDF、真实预算、同一固定 cutoff、条件均值可不为零、噪声构造、局部窗口、收缩及 Q=0 修正。

消费的旧接口完整头和所属作用域已读：GaussianTail 的 density/tail 定义、basic、derivatives、local comparison；TruncationIntegrals 的实际 budget 定义、nonneg、local comparison；TruncationRegularity 的连续、正性、归一化二阶矩极限；SourceTruncationBridge 的完整 law_data；SourceClockBridge 的完整 conditioned_sample；SourceFourierScale 的完整 gamma_bounds；SourceNoiseSandwich 的完整 actual_noise_cdf_sandwich；SourceNoiseCost 的完整 weighted_cost；MeasurablePath 的 prefixSum/maxWithZero/upperCrossing 可测性。均核对了 namespace、显式/隐式参数、局部变量、所需实例和打开的 scope，没有把自然语言摘要当作完整接口。

实际定义链也已读：`Path`、`prefixSum`、`energy`、`upperMax`、`maxWithZero`、`upperCrossing`、`truncationF`、`truncationBudget`、normal density/tail；完整 `quadraticFullNoiseLaw` 的 map/input law、两个 Fin8 chord family、biased pair、triangle law、scalar bump/density/law；`sourceKernelCutoff` 的字面 bump 和 `sourceFourierTest` 的严格绝对值指标。噪声仍是同一条件律下原来的完整噪声，测试仍是原 cutoff 测试。`maxWithZero_eq`、`upperMax_eq_zero_of_energy_eq_zero`、`energy_nonneg` 等完整旧接口保持原含义。

旧证明、内核与 AX 按已合格精确版本复用。30 组激活图源/对象在服务器重哈希全部不变，本地 library 对应 30 源全部匹配。新增四个只读引用是 SourceNoiseCost、SourceNoiseSandwich 各自的 source 与 object 链接，均解析到 `workspaces/integration-bearing-v64/` 的相应路径；四个目标哈希与激活图、各自合格凭据一致。目标文件本身权限为 0644，只读约束来自所有权；没有把符号链接误称为操作系统级不可写冻结。新 SourceDesmoothing 源与对象为 0444。

SourceNoiseCost 的合格源/对象分别为 `531e2ab17798c7ba7db49d19bd08af7cc1c7cf5ae29b0d23af4873fe30dcda20` / `3a083bfb23605cfffc4118ecaeefd5d544b2db18e18defc73ca614d2facd925b`；SourceNoiseSandwich 为 `f972d6271477f37751d8b5b1bfcf74ef55348d00426e8a83b21942f3fd332d79` / `71cc730b05fbd4582076af890a4405ab48cabaa98b05e9d41f34a1116fc7ca91`。两份 root-qualification 及其独立完整审查 MD/JSON/coverage 哈希均匹配；v64 PASS 凭据保留相同源与固定版本。未重新审查不变旧证明或重跑它们。

## 八项数学裁决

1. **sourceReferenceG_local_lipschitz，15–76 行：CORRECT。** 令非截断 H(u)=1−2T(u)，用 T(0)=1/2 证明零延拓 G(u)=H(max(u,0))。两个截断点都留在 `[max(0,x−h),x+h]`，h=1/(1+x)。直接密度公式及 x²−u²≤4 给出 φ(u)≤exp(2)φ(x)；对 H 用区间导数界，再用 max 的收缩性。没有对零延拓在零点求导；s、t 为负、为零或跨零均覆盖。输出常数恰为 2exp(2)φ(x)。

2. **sourceNoise_markov_at_mean_multiple，78–122 行：CORRECT。** d 非负。d=0 时由非负可积函数零积分得到 delta=0 几乎处处，真实严格事件 `{Kd<delta}` 为零测，a=theta=0。只有 d>0 分支比较可积的常数指标 a·1_A 与 delta，再以 K>0 化简。未除以零均值；delta=a 的原子位于好事件。P 为概率测度、delta 可测可积及非负均是冻结条件。

3. **sourceWeight_nearby_bound，124–152 行：CORRECT。** 真实预算的邻域上界和真实正态尾局部上界相乘，所有乘法因子非负，得到 w(t)≤8exp(2)w(x)。`exp(1)<3` 的 Mathlib 定理给出 exp(2)≤9，故 8exp(2)≤72≤1600≤L。原 budget×tail 完整保留，没有替换成 p 阶矩代理或假设原律三阶矩。

4. **sourceSignedCDF_convolution_lower，154–271 行：CORRECT。** F 单调因此可测，且 [0,1] 有界，故 F(Tz) 可积。实际被积分的下包络为 q−Bw−ga−1_A(q+r)−g·delta，其中 q=|E(x)|/p、r=Hw/p、A={a<delta}；它只含常数、可测指标和 delta。好事件 delta≤a 上，s=1、s=−1 分别使用单调性的两个方向，得到相同有符号下界；坏事件使用 PB、局部 E 包络及 G 的 Lipschitz 界。包络的额外非正项合法弱化点态界。指标积分恰为 theta(q+r)，整理后恰得冻结的 `(1−theta)|E(x)|−theta Hw` 系数。**没有积分 E 或要求 E 可测**；b 无符号前提也没有在抽象证明中被私自使用。

5. **sourceTruncation_weighted_desmoothing_from_interfaces，273–667 行：CORRECT，条件消费者。**
   - 归一化 n·∫z²=1 推出 n>0、原二阶积分>0，因此真实 w>0。原 product law 的坐标独立/同分布事实应用于同一个闭 cutoff 事件 N，给出 p≥7/8；p≤1 来自原 P0 的概率性。条件 rho、P 及完整 noise 的概率实例均由完整旧接口构造。
   - 仅在同一 nu,n,x,epsilon 调用实际噪声 sandwich、gamma bounds 和 weighted cost。delta 可测可积、0≤delta≤400h、d≤400gamma≤1600R(0)，故 a<x/4、gamma<x/(4K)。`epsilonGeometry` 与 L≥1600 给出 a+delta≤1/[4(1+x)] 几乎处处。Markov 的 theta≤1/K 直接包含 d=0 分支。
   - s 按 E(x) 符号选择，y=x+sa 保证 y>0、gamma≤y、y≤1+x 和 SM 的半窗口；y±delta 都在完整 PB/END 窗口。先对 prefixSum 应用真实 endpoint 双 sandwich，再由 END、G 的实际 Lipschitz 得到 `|Jend(y)−G(y)|≤Ce·w+g·d+b`，由显式 SM 得到 Jmax 对 G 的界。对 maxWithZero 应用同一真实 sandwich，其绝对值因非负性恰好去掉。
   - s=1 使用下 sandwich，s=−1 把上 sandwich 乘以 −1；常数积分和符号完整保留。第四头以 H=L·M 直接实例化。实现的完整成本为 **g(a+2d)+2b≤c(K+2)D·w**，由 a=Kd、g=cφ、b+φd≤D·w、b≥0 和 c≥1 支付；没有漏掉第二个 b 或第二个 d。
   - 设 T0=B+Ce+Cs+c(K+2)D≥0。p>0 先去掉除法，再以 p≤1 缩小 pT0w。由 theta≤1/K 得 `(K−1)|E(x)|≤(KT0+LM)w`，K−1>0 且 w>0，所以除法合法，产生精确 **K/(K−1)** 与 **L/(K−1)**。L/(K−1)≤1/4 仅在 M≥0 下乘到 M；最终 M/4 真实成立。
   - 原律 hmean=0 保留，**没有条件均值零假设**。hRcube、hReta 两个原预算逐字保留；heta0 与 hReta 在这个已给 SM 的消费者中分析上未使用，不被谎称用于产生 SM。没有原律三阶矩、指数矩、对称、无原子或样本正能量假设。

6. **sourceWeight_enlarged_domain_compact，669–731 行：CORRECT。** I 是 `[0,H]` 与非负半轴内 budget 的闭次水平集的并，故闭。R(t)/(1+t)²→1 及 rhoStar>0 给出有限上界 `max H (max T (2rhoStar+2))`，下界为 0，所以紧。0∈I；由归一化推出的严格 budget 正性、真实 tail 正性及连续性得 w 在 I 连续且逐点正。紧非空域的真实最小值给出 m>0。域是主文 I 的通用 H 参数适配，覆盖全域；没有要求更高原律矩。

7. **sourceWeight_compact_supremum_absorption，733–784 行：CORRECT。** I 空时 ratios 空，另以 0 给出有界性；I 非空时由 w 的正最小值 m 和 |E|≤1 得 ratios≤1/m。`insert 0 ratios` 始终非空且有上界，故 M≥0，每个正点比值≤M。ratios 非空时比值非负，准确证明 M=sSup ratios；不把 real sSup 空集的默认值偷用成有序完备性。I 非空但无正点同样由插入零覆盖。对 C≥0，假设每个正点比值≤C+M/4 后连同插入零得到 M≤C+M/4，再得 M≤4C/3。未要求 E 连续、可测或 E/w 达到最大值。

8. **sourcePositiveCDF_weak_tail_error_identity，786–831 行：CORRECT。** 逐样本证明真实正能量严格 CDF 事件等于原 weak upperCrossing 的补集。若 Q>0 且 t>0，maxWithZero=max(0,upperMax) 与原上界完全对应；若 Q=0，全部坐标为零且 upperMax=0，补 crossing 的严格事件不发生。墙上原子保留在 weak crossing，排除于 strict CDF。使用原 crossing 可测性取补概率，再仅以 T(t)>0 整理绝对值比值。没有用连续性近似、丢弃 Q=0 或把 t=0 的 weak 事件改成零延拓。

## 生成项与信任边界

实际生成的 16 项逐项完整类型和 AX 均已检查，详见 coverage：第五头的 `_proof_1` 为 n 的自然数零/正分支逻辑，`_proof_2` 为在原预算与归一化条件下的条件 product-law 概率实例，`_proof_3` 为原 product-law 概率实例；`_simp_3`、`_simp_4` 是交集/原像成员等价，`_simp_5`–`_simp_7` 是字面 2、3、4 非零化简，`_simp_8` 是无零因子乘积非零，`_simp_9` 是 reduced monoid 中非零幂化简，`_simp_10` 是 group-with-zero 的非零整数幂化简，`_simp_11` 是特征零下自然数加一非零。第六头 `_simp_1`–`_simp_3` 是并集、Icc、Ici 成员展开。外命名空间 `Shao.upperCrossing.congr_simp` 是阈值相等带来的原 crossing 集合相等。它们均与已读新源码中的相应证明/生成操作一致，没有额外数学前提潜入公开头，也不是新增公理或 definition value。

审计脚本完整读取，SHA256 `25969a68a34443ce1acb85aacdcefadcb3ff35e6e2fa132670d7cb42e8383fe9`。它导入保留模块，以 `env.getModuleIdxFor?` 覆盖所有实际所属项；对每项使用传递 `Lean.collectAxioms`，白名单严格为 **propext、Classical.choice、Quot.sound**。全类型使用 pp.all/deepTerms/proofs、pp.maxSteps=10000000；若有 definition 则会打印完整值并因冻结为零定义而拒绝。实际 24 项 AX 集合逐项均在白名单内，definition 数为零。

真实 U+22EF、U+2026、ASCII 三点在原审计日志与全部实际类型中各为 0；源码 `sorry/admit/axiom/unsafe/native_decide` token 扫描各为 0。省略符扫描不是仅搜索反斜杠转义文本。首次只读日志解析器误把可换行 AX header 限为单行，仅读到 13 项；放宽解析后读齐 24 项并逐字匹配。这是阅读解析修正，**没有 Lean、审计或 producer 重跑**，原始成功日志不变。

## 复用的服务器凭据

首个 WHOLE 八头成功为 check007，原生 `check007.rc=0`；同次命令带 `-o` 保存上述对象，源码归档 `check007.lean` 哈希等于新源码。check001–006 原生 rc 均为 1，失败分母保留；check004 是首个 whole 尝试。check007 日志 SHA256 为 `3452d6d581cb7ca4cdbcb4b836e2e345b64e9f266c7eec5c614fd4fb584936a4`，服务器只读扫描 error: 为 0。首次完整成功后 producer 重跑为 0。

唯一实际所属项审计原生 `owned-audit.rc=0`，审计尝试 1、成功 1、导入失败 0、重跑 0；审计 JSON SHA256 为 `c2c1ad6c22d8f546b05576c8084143cad8a269a846e510656c2a0469a35160b1`。原生 rc、日志哈希、完整类型、源和对象已由独立只读 server 访问重新绑定。commit 中新源 blob 也逐字等于当前只读源，不只核对工作区文件。

固定版本：`leanprover/lean4:v4.36.0-rc1`；mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。原命令使用 root-heavy.lock、CPU10–13、`-M8192 -j4`，autoImplicit=false；没有本地 Lean。复用精确 source/object 所绑定的内核及传递 AX 成功，不声称本审查重新执行它们。原始大日志和二进制仍只在服务器。

## 尚未闭合的原文生产范围与释放

PB 仍需原 maximum 的 Gaussian 加权截断 pullback；END 仍需原 endpoint 相对误差、标记删除尾代价及 Q=0 修正，补充材料明确的 Shao–Zhou (2016) Theorems 2.1–2.2 外部归属保留；SM 仍需**同一个 rho/noise/cutoff** 的完整 y 范围 smoothed max/end 比较。本文没有从无权 bad-cutoff 概率或条件 bad clock 推出原法则 Gaussian 加权代价，也没有用命名接口抵付生产义务。

候选第 9 节指出 existential bounded threshold 不能直接支付 literal growing epsilon 的兼容关系。注册表现有后续固定 witness 候选是独立推进中的工作；本裁决不采纳它，也不改变本次八个头。实际公共 SM producer、D1/D2、PB、END 等尚需各自合格证据后才能组装原根。正确性裁决是八头解析辅助结果完整，不是研究新颖性或根定理完成裁决。

审查工作已完成，无在途 server、工具、Git 或写入操作；释放本审查全部报告/草稿写权。根协调者应完整读取本报告一次并自行决定资格及后续源依赖。本审查不自我验收、不提交 PR、不合并。

用量：实际模型/effort 如上；input、cached input、output、reasoning subset 均未由工具公开，记录为 null，不推断订阅百分比分摊。
