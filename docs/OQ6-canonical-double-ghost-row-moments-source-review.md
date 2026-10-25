# Unit188 独立完整源码审查（源码阶段）

STATUS: MATHEMATICAL_ARGUMENT_CORRECT_FORMAL_IMPLEMENTATION_INCOMPLETE

本审查上下文为 `/root/oq56_row188_final_review01`，不是候选作者，也未修改候选、冻结文件或其他所有者文件。已独立读完精确候选的全部 533 行、作者 proofnotes 和阶段一完整推导；已读 p44 全文、p51 全文及 p54 全文以核实实际原题范围、修正和外部归属。已将实际源码的每个声明、数据初始化式、局部捕获和实际使用的接口逐段与冻结及主源对应。结论是：本精确候选的数学推导及源到陈述翻译未发现关键缺口；父级随后提供的首次实际 Lean 检查已明确失败（下述 native01），当前形式实现不完整；成功内核、实际 private/generated 所属发现、完整 TYPE/FULLVALUE 和递归公理证据仍欠。因此 `qualified=false`、`actualOwned=UNKNOWN`，不作本单元机器通过或最终接受声明。

候选：`drafts/oq56/unit188/author-01/stage2/CanonicalDoubleGhostRowMoments.lean`，SHA256 `1ac138362cf5c4c9068abc601fef9823008abee789f9b241e374a99565b83fd3`，36974 字节、533 LF、0 CR、无 BOM、严格 UTF-8。声明数由完整源码实际导出为 5 def、5 theorem；没有源码级 private/helper 声明。最后一项不能代替实际 generated/private owner 发现。

## 精确输入、冻结及独立性

冻结基础为 `ecf9c44c5ac8e86d8975436aeac63c0e1c033637ff7b542f36c2317de89f5f0c`，阶段二七项数据修订为 `c02f833669acef915a26a47b8771d37b0b0ff6b7e48f011fcb08b22c8111201f`，实施激活为 `127719376ec417740739ad30b7b9fb6171fd11e2dee7479a4aaa54fa2ecf692d`。逐行独立比较了完整前缀、后缀、10 个冻结头、5 个全局定义原值及全部 53 个实际 let/letI 的类型和原值；46 原值和 7 事先批准的新值全部一一匹配，无新增数据或实例。30 个冻结嵌入表达式是声明或定义中的实际函数表达式及重复积分位置，随完整冻结头/全局定义和实际源码逐项审读，未由计数或静态布尔代替。

独立字节验证还重新计算作者 manifest、input-hashes、RELEASE0 所引用的全部 45 条本地文件绑定，哈希和提供的长度全部相符。作者 manifest `7688307ca47da967e545ca70c81e75b12abda37a1f4ccf1a3819f47d2f9cfbf6`、input-hashes `3a9a3d3cacfd51a93977319bd84135953922faa0eb907336b77a754731237b8f`、作者 release `9c11a196b6888b61d9b44ee378b2c197127310b3b54a7068e278a848da830e57`均精确相符。源码 forbidden-token 扫描未发现 sorry、admit、新 axiom、unsafe 或 native_decide。

保留的 `source-byte-validation.json` 是首次本地静态比较记录，其中一个失败来自审查脚本把头内 `(Ω := Ω)` 的命名实参误作声明体分隔符；候选没有该缺陷。`source-byte-validation-v2.json` 改用完整冻结声明行比较，10/10 全部相符，源字节未变。该修正没有运行 Lean 或重放任何旧检查。

作者已 DONE_RELEASE0。审查员只写本目录，未编写/修补证明，未调用 Lean、服务器、网络、Git、上传或缓存，也未创建 child。实际模型/努力和 token 类别不由当前上下文暴露：请求设置为 gpt-6.1-sol/xhigh，实际及 input/cached-input/output/reasoning-subset 均记 null，不推测。

## 原题到陈述

p44 §1 式(1)–(4) 的目标是原行向量 ψ_i=Σ_{j≠i}r(x_i,x_j) 的真实欧氏范数 q 矩。源码第 19–27 行明确采用 M=ν^n、P=(ν.prod ν)^n、真实配对映射、WithLp 2 的 EuclideanSpace、四角 ghostMatrix 乘全一向量及 S=Σ_i(w(z_i.1)+w(z_i.2))²。第 450 行最终声明恰为实际 M 下 ‖ψ‖^q 可积及 A^(1/q)≤2√q B^(1/q)，其中 A=∫‖ψ‖^q、B=∫S^q。

显式输入是任意 n∈ℕ、任意仅带可测结构的 Ω、真实概率 ν、产品可测且产品 L1 的 r、两个 AE 规范边际、实 q≥2、AE 非负 w、产品 AE 包络及实际 P 下 S^q 的 Integrable。没有 w 可测、Ω 拓扑/标准 Borel/可数性/DecidableEq、逐点规范性、核对角限制、矩阵律或最终矩界输入。p44 以对称典范核叙述；这里显式保留两条 AE 边际而可允许非对称 r，数学推导不依赖对称性。原始对称情形满足该接口；没有把任意非对称核的一侧规范性误说成足够。

本单元不闭合 p44 标量式(5)、尾式(7)–(9)、DC、整个 OQ56 或 C2/C12。p51 S7/S18 所用原非线性基核行集中保持归属 Shao–Zhou Lemma 6.1；p54 将条件标准化 p 矩从任意多项式速率修正为收敛/统一有界，及其反例和严格余量的实际大余项编码付款均保持原范围，不被 188 代替。124 统一机制不是前置；没有新颖性声明。

## 全部证明的独立审读

1. 第 29–38 行：splitEquiv 的方向由有限积与乘积的真实保测主源给出，再取 MeasurableEquiv 的保测逆；pairSamples 是该逆的定义展开。两侧均为实际样本积测度，概率足以支付 SigmaFinite，无 MeasureTransport 或 map 等式假设。

2. 第 40–188 行：M 上坐标 eval 的真实边际与 iIndepFun_pi 给 i≠j 时 (x_i,x_j) 的实际联合律；P 上配对 eval 独立性经 fst/snd 复合，再用真实边际得到四个 corner 映射的保测性。每次联合律均携带异索引证据，没有将独立性误作观测值不等。各角的 r L1 从真实产品 L1 拉回，对角分支恒零；有限和得到 original/ghost 各坐标 L1。有限标准基恒等式 v=Σ_i v_i e_i 在真欧氏空间中逐坐标证明，再把标量 L1 提升为完整 Bochner L1，没有默认不可积积分值冒充均值。

3. 第 162–250 行：hr1 的两侧 Fubini 切片与 hcR/hcL 相交得到 good；通过准保测 eval 和有限 ae_all_iff，仅对 M-a.e. x 得到所有坐标 good。固定该 x 后，常项、两个单鬼切片和异索引双鬼项均先证实际 L1，再交换积分。good 的左/右截面和零均值取投影的位置分别正确：r(y_i,x_j) 消费 x_j 的左截面，r(x_i,y_j) 消费 x_i 的右截面，双鬼项经联合律和产品 Fubini 为零。逐项→逐坐标→有限基展开，得到完整向量 ∫_y ghostRows(pairSamples(x,y))=originalRows(x)，同时保留真实截面 Integrable，结论保持 AE x。

4. 第 252–287 行：b=1/q 正且≤1。inversePower(t)=t^b 在闭凸非负半线凹且连续；powerNorm=‖G‖^q 非负且实际 L1，inversePower∘powerNorm=‖G‖ 的 L1 来自 hG.norm。ConcaveOn.le_map_integral 的概率、闭集、连续、AE 值域和两项 L1 全部在源码支付。先获得标量 Jensen，再与 Bochner 范数积分界组合，最后取 q 幂得到向量 q 矩 Jensen。所有 rpow 互逆仅用非负底数和 q>0，包括零。

5. 第 291–318 行：确定性 have 普遍量化 D,W,u 及所需假设；有限列范数的三角不等式、|u_j|≤1、实有限 Cauchy 和 186 能量界给 ‖D u‖≤√n·S。它不是未证明的结论性输入。唯一内部新数据 columnNorms(j)=‖column n D j‖ 处于该子证明的 D/W/u 祖先下，仅实际捕获 n,D；此时尚未引入后面 S,K 等 sibling 数据。

6. 第 319–360 行：S 是平方和故逐点非负，不需要 hW。recoverPower(t)=(max(t,0))^(1/q) 连续，逐点 recoverPower(S^q)=S。由 hS 的 AE 强可测性及连续复合恢复 S 的 AE 强可测性，再用 S≤1+S^q 与概率空间上的真实 L1 得 S L1。这里没有从某个默认积分为零推出可积性，也未暗加 w 可测。该已支付的 S L1 不被误说成外部假设；后续 q 可积支配直接使用更强的实际 hS。

7. 第 361–418 行：187 的 AE 包络将上述 √n 确定性界应用于全一或固定符号路径。187 提供真实范数 Measurable；连续实幂提供 q 次幂 Measurable，hS 提供 (√n)^q S^q 的真实 L1。Integrable.mono' 的范数支配因实幂非负而合法，因此每个固定符号 q 次幂和全一 q 次幂实际 L1。hF1Meas 的全称消去只用 Fin n→Bool 非空（任意 n 均有常值 Bool 函数），没有引入样本选择器或 n>0。

8. 第 403–448 行：按 187 实际导出的 norm-law，用标量连续函数 t↦t^q 与 integral_map_of_stronglyMeasurable 把真实推前等式换成固定符号下真实积分相等。先支付每项 L1 再交换有限 cube 求和与积分，Bool 路径数 2^n 抵消 cubeMean 的逆因子。随后只在 AE 包络上消费 186 的精确 (cubeMean)^(1/q)≤2√q·S；cubeMean 非负，升 q 幂得 cubeMean≤(2√q)^q S^q，再积分。√n 仅服务 L1 支配，不进入最终常数。

9. 第 450–529 行：真实 pairSamples 保测把鬼 q L1 拉回 M.prod M。Fubini 给 innerQ L1 及 AE q 可积截面；与 canonical_ghost_mean 的 AE 向量截面事件相交。第 477 行 sectionGhost 在该 AE x 和 hx/hxq 下定义，再调用本单元已证明 Jensen，得到 rowQ≤innerQ。rowQ 可测来自原向量 L1 与连续实幂，先由支配获得实际 rowQ L1，再用积分单调性、产品 Fubini 和 map 等式连接到鬼矩界。A,B,K 逐项非负，对 A≤K^q B 取正 1/q 幂并使用非负乘积幂与互逆，最终常数恰为 2√q。

## 数据、匿名表达式和作用域

已从完整源码自行数出全部 53 个命名局部数据，并与 actual-scopes 的源行、类型、原值对应；该文件只是索引，未把作者的 checked 布尔当证明。所有声明完整 telescope 及匿名 lambda/积分中的实质表达式均随源码审读。53 个显式局部值与冻结相符，两个 sectionGhost 分别在第 191 行 AE-good x 和第 477 行 AE-mean/q-L1 x 的祖先下。good 中四个 b 是 a 下的四个独立 sibling 作用域，互不泄漏。每个 instMM 的两个坐标测度 lambda 是 sibling，不是嵌套。basisVector 的 i→k、entry/coefficient families 的 i→j→x/y/z、signedPower 的 s→z、cubePower 的 z→s 及 innerQ 的 x→积分 y 均保持真实左到右嵌套。初始化式不看自己、前向数据或 sibling 局部参数。

ordinary Prop 型 have、滤过的 AE 假设、Finset 求和证据和分支 hij 等只支付证明义务，不增加数据或数学前提。九个 IsProbabilityMeasure letI 均为冻结的实际有限积/乘积概率实例；没有新可测空间、拓扑或非法自定义实例。实际 elaboration 捕获和任何 generated/private 常量仍必须在后续全 owner TYPE/FULLVALUE 阶段审读，本阶段不作推断。

## 实际消费的生产者与主源 API

复用 185/186/187 已资格化旧证明及原服务器证据；本审查没有重新审旧证明或重跑检查。逐字读完 188 直接消费的 17 个生产者实际完整 TYPE 和 11 个非定理 FULLVALUE，再与各单元原 actual-owned-metadata 的同名项做精确文本比较，17/17 TYPE、11/11 VALUE 完全相等，源和资格绑定亦相等。186 是 `07520a5e75c82565c542a3596f87755153234aece93f86f1a5517cedb13249ce`，187 是最终 repair01 `1e5a32ccdc30b8c70b7bc12add060392a0c90aa59d615d4d0e683c5ab1c34baf`；未使用失败旧 187。185 的直接祖先定义 cubeMean/signPath/signValue/energy 也来自其资格化 repair03。三个资格文件哈希分别为 `7b87ea13149166c7eff3d3c8f88477d35981d789c10dbbe2e295190e8526c3bd`、`bf0054b92c4b4bedd65361870bf99d2e74fd9331a121c40a37724a3266e4eeae`、`9bb3fb91a6ead38dac8b90cca10a2c7b26e87efd26de645db791402496688c4f`。细目在 producer-interface-validation.json。

直接读了 interface-calls 中 15 个 core 主源完整头及其全部 raw ambient blocks、11 个复用主源完整声明及实际活跃原始作用域、4 个阶段二补充头、6 个实幂代数头、4 个 WithLp/PiLp 坐标头，并对应到 533 行中的实际调用。概率与有限性支付 Pi 保测、坐标边缘、iIndepFun 和联合 map-product；SFinite、实/欧氏 CompleteSpace 与 NormedSpace 支付切片/Fubini/Bochner 和 Jensen；所有积分交换都有先行实际 L1。MeasurePreserving.integral_comp 需 embedding 的旧批准接口并未误用，当前使用真实 integral_map 或 integral_map_of_stronglyMeasurable。

特别核对完整实幂连续主源前 294 行和后续环境边界：Real.continuous_rpow_const 是 Real namespace 中的全实 unary 连续头，参数仅 q≥0；后面另一个泛域 α 的拓扑变量不能向前污染它。对 Continuous.comp_aestronglyMeasurable 读了完整原文件前 238 行：第 233–235 行头/体直接把连续 β→γ 与 AE 强可测 α→β 复合；活跃 TopologicalSpace 只在 β、γ。188 实际 β=γ=ℝ，α 是原/配对样本空间，无 TopologicalSpace α、第二可数或伪可度量假设。第 237 行后相邻定理的额外条件不属于本接口。该直接绑定在候选草拟后、首次机器门前补齐；不伪称早于草拟。补包哈希分别 `8b2c42b5093fcbad457c18d030d33a0d84e6f0f61ea7663c1870df0839737e4a`、`9848ec8edd79392db2f85f487cdc3e269d5bd9d7eed4cc551b77491a3c973d3c`，直接绑定 `549f243fdd42e0af3c5112111e127cb5a8072b5f12da60bfa8e2d7d5dd1d8ab9`。

## 边界、未付证据和下一步

n=0 的样本积仍为概率，Finset 空和为零，Bool 立方有唯一空函数；没有选择空索引或除以 n。n=1 的行/矩阵均由对角分支归零，异索引步骤只在 hij 证据下使用。零 S、零矩阵能量、零 B 时所有操作保留非负实幂等式，不作除法。重复观测值、原子法则及 r(a,a) 任意都允许；产品 AE 包络只经合法异索引角映射拉回，未限制到对角。

完整数学论证未发现语义缺口，但当前 Lean 实现有 19 个实际未闭合 elaboration 错误，必须修复后再核。尚欠且绝不以静态检查代替的是：父级同一精确源哈希的实际服务器内核退出码与对象；从真实源/owner map 得到的全部 owner（含 private/generated、不得 namespace 过滤）；逐项完整 TYPE、所有非定理 FULLVALUE 与递归 collectAxioms 的白名单证据及覆盖/保存结果。后续应由本同一独立上下文完整审读全部改变的证明，并读取成功机器包核对全部新实际项；不要再派第二个完整旧证明审查。若机器自然失败，失败回执保留，任何后续修复必须按实际变更范围独立复核。

源码阶段至此完成，进入 SOURCE_REVIEW_DONE_RELEASE0。C2/C12/OQ56 保持 OPEN，OQ3 保持 PAUSED_BY_USER。本 release 结束当前普通执行回合，不宣称后台持续运行；机器补充须由父级明确继续同一上下文。
## 封包前收到的首次实际机器失败

父级提供 `lead-execution-01/author-kernel-01-affected-diagnostics.json`，已重新核 SHA256 `3a5274fe3d1664a29cc29dbd1eaaab019e0397261aab140f921a5bd98e4c0073`（65463 字节），其 input 精确绑定旧 1ac13836 源，原 receipt SHA256 `8248076afbb6ae1f277f8a96a1198ebd7e54b96b0e1a816560c58f6161531677`。实际自然 RC1，7.028312226757407 秒，19 errors/12 warnings、未超时、无对象、整个 owned process group 已结束。11179 条 protected FULLFP 前后保持，gitExact/preservationEqual 为真；这些是失败检查的保存证据，不是内核通过。

错误源码行是 96/103/110/117、131/171/202/216、263/265/276/287、343/354/356、377/391/436/529。前两组涉及 eta 展开、函数空间加减/积分表达式；后续大组涉及显式 Real.rpow 与 pinned `^` API 的表示连接。它们令当前完整 Lean 证明未成立，不能把数学读审通过改写成形式检查通过。警告包括冻结的 Prop 型 letI 偏好和未用 simp 参数，不得为消除警告而擅改冻结值。

独立读取钉死 `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`（源 SHA256 `f8a26d662fb7966fa5b45aef95c8d7cf0383c9921fa3e9ee1cd2c41561e9fbfd`）前 170 行：第 34–35 行定义 rpow，第 37 行 Pow ℝ ℝ 实例，第 39–40 行完整桥接为 `@[simp] theorem rpow_eq_pow (x y : ℝ) : rpow x y = x ^ y := rfl`，活跃环境为 noncomputable section / namespace Real / `{x y z : ℝ}`。主源包为 `next-source/oq6-finite-quadratic-sign-chaos-189/complete-real-rpow-primary-source.json`，SHA256 `a6394e9305eabd601fca0c6dd3e257d80d03d0ef25bc10abeb46ca57cfde23f5`。因此桥接没有额外数学前提或零值风险；旧候选未显式完成这些 pinned API 连接，实际修复必须审读而不能猜为通过。

父级已将原作者恢复到独占 `author-01/stage2/repair-01/`，四个受影响 proof owner 为 canonical_ghost_mean、norm_integral_rpow_le_integral、ghost_row_qmoment_bound、canonical_row_qmoment_bound。审查员不写该修复，不并行修代码、不重跑失败检查。旧 1ac 源与本源码阶段证据保留。最终资格继续为 false，actualOwned 继续 UNKNOWN。
