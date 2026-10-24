# SourceScalarInitialBudget / PR312 独立完整最终审查

**STATUS: CORRECT**

审查者 `/root/scalar_initial_budget_final_review` 为本模块非作者的新上下文。结论覆盖两条冻结公开定理、九条源码私有定理及其十六条实际生成定理，严格绑定以下最终源、原成功对象及原 check16。未发现关键数学缺口、量词缩小、额外矩条件、未支付零能量事件或错误的物理概率识别。本报告是独立审查；Root 最终资格和集成另行记录。

## 精确对象与证据

- PR：https://github.com/randomcat4/shao-lean/pull/312；只读 GitHub 核对仍 OPEN、唯一新增 `Shao/Probability/SourceScalarInitialBudget.lean`。
- head `68a96dcca006f656f8c9bbb67ca1038b9b5d1d56`；tree `8eea7964444132c7bafe4abdf4b4e693c8b3432d`。服务器工作树干净；相对作者冻结基线只新增该模块。
- 新源 976 行、52151 字节，UTF-8 无 BOM、LF；SHA256 `2731effd3fbb3487bef30090699d675ce387d0258ad5a93800e9ba324330a459`。本地、服务器工作源、原 source16 快照及 Git blob 相同。
- 原对象 `/root/rivermind-data/shao-lean-20261021/outputs/common-scalar-initial-budget-v79/producer16.olean`，SHA256 `84842cb7b9f3d085891172bd3fa1ba80c5e4ed8e37f2a4b885d3d6ba86af4d28`；审计实际导入的安装对象与之相同。
- 作者 final-receipt SHA256 `60b3fb7e9423d14acd0a854905324a6cc6afd9ee23868529af1ef9d441e0d551`；作者 RELEASE SHA256 `4e0d44e9e44b66484ab9bab004149d47d160d3a72b1d349ace6061f07cf03c1a`。其全部 42 个 sealed 文件逐项核对字节数与哈希通过。
- 完整实际类型导出 60675 字节，SHA256 `7068be345c89f4f74b5b3b1734ace9e523374539d05493cde31e8d1657cef5c2`；原 all-owned 审计 JSON SHA256 `2d26c545d81af955db1e32a1c4a885e4416a7e3f986921616e6133d413db0c37`。

## 实际审查覆盖

完整阅读新源 1–976 行，包括以下全部源码陈述、证明分支、局部函数和 let/letI 值。独立解析得到 11 个源码定理、85 个 let/letI 绑定起始项；此计数不替代对全部 have/set/内部证明值的全文阅读。公开两头的全部量词和 literal lets 与冻结文件逐字相同。

| 源声明 | 完整源范围 | 审查结果 |
|---|---:|---|
| sib_gaussian_cubic_tail_weight | 19–64 | Gaussian 三次尾权 |
| sib_normalized_zero_energy | 66–89 | 真正 iid 原零能量 16R |
| sib_raw_conditional_weak_tail | 91–242 | 真条件律、原 bad crossing、两个符号 |
| sib_normalized_positive_tail_budget | 244–414 | Q0 扣除、小预算和范围外延伸 |
| sib_normalized_closed_cdf_budget | 416–509 | 所有实阈值及原子 |
| finite_second_scalar_closed_cdf_budget | 511–595 | 原有限二阶矩 law 正缩放搬回 |
| sib_analytic_profile_properties | 597–627 | g 反单调、[0,1] |
| sib_analytic_raw_profile_identity | 629–665 | 原能量/原终点逐路径 physical 值 |
| sib_analytic_profile_gaussian_integral | 667–746 | 真 Gaussian 密度积分 |
| sib_signed_cdf_transfer | 748–812 | 负号开闭互补、原子保留 |
| finite_second_analytic_initial_host_gap | 814–974 | 可积性、外层 Q0、strict host gap |

逐个完整阅读了 27 个原服务器实际所属 TYPE 的未省略原文本，包含显式 typeclass/instance 和依赖 let 值；读取范围完整覆盖类型文件 1–865 行。没有用结构摘要替代长类型，也没有使用重复项字典压缩。类型块无省略符，逐块 hash 与 actual-owner-index 对齐；再从原审计日志完整多行 metadata/TYPE 块独立匹配全部 27 项。初次只读日志提取的单行正则仅识别 15 项，已用多行解析恢复全部 27 项并逐项确认类型 hash；这是读取恢复，未重跑审计。

actual-owner inventory 由 `env.getModuleIdxFor?` 对目标模块精确选取，没有公共名或 namespace 过滤。逐名 kind 确认为 27 theorem、0 definition/opaque/其他非定理值，即 2 public + 9 source private + 16 generated。完整非定理值覆盖为空是实际 inventory 的结果，并非从源码没有 def 推测。逐名 canonical name、完整类型 hash、源证明块、类别及递归公理记录见同名 JSON。

十六个生成项也全部完整读型并映射到所属源码证明：raw conditional 的 `_simp_1/2` 是有限交集/原像成员展开；positive tail 的 `_simp_1/2/4/5/6/7/8/9/10` 是并集、反身序、2/3/4 非零、乘积非零、自然/整数幂非零、n+1 非零；closed CDF 的 `_simp_1/2` 是补集成员与 not-lt；signed CDF 的 `_simp_1/2` 是 Iic/Ici 成员；公开 host gap 的 `_simp_1` 是 not-le。它们没有增加概率、矩或目标结论前提。源码证明完整阅读；不打印或模型读取巨大 theorem 机器证书值，原对象及全部递归 collectAxioms 绑定照常保留。

## 数学核对

### Gaussian 权与真实条件单侧尾

19–64 行只对固定标准 Gaussian 使用三阶绝对矩可积。令 m 为该矩，B=8(1+m)>0。0≤t≤1 用尾概率≤1和 (1+t)^3≤8；t>1 对 Ioi t 的指示函数积分得到 t^3 Psi(t)≤m，再用 (1+t)^3≤8t^3。没有为原 law 增加三阶矩条件。

66–89 行把原已合格 iid 零能量 producer 实例化为真正 pi nu 坐标族，证明 iIndepFun、IdentDistrib 和二阶矩正性。由 n E Z²=1，producer 中 sqrt(n E Z²)=1，map id 恢复同一 nu，故费用确切为 16 truncationBudget nu n 0。

91–242 行固定 e=1/800、K=4/e²+12/e+16、Cw=(2²⁰+2¹⁸)sqrt(2pi)，并先于 law/n/t 选择 Cb 与 C=Cw K+(1+Cb)/e³。rho 确为 cond nu {|z|≤e/(1+t)}，P 为它的真正 product law。er_source_endpoint_inputs 的 x=t、近邻距离 0、small R、原二阶矩归一化与原中心化均实际满足。输出的 z 明确保留条件均值项 n|E_rho Z|、二阶矩偏差及条件三阶矩，没有把 rho 再次假定为中心化。

两个有界单侧乘法闭尾均使用同一 rho、h、t、z，小量 z≤1/1000 和 thinness t h≤1/800 均由真实输入提供。sourceTruncation_conditioned_sample 对同一 cutoff N 给 cond P0 N=P、p=P0(N)≥7/8、1-p≤r/e³；证明保留 p，并通过条件概率乘法及事件分割得到 P0(E)=p P(E)+P0(E∩Nᶜ)。后续估计用 0≤p≤1；p≥7/8 随真实条件样本资格保留，未被当作 p=1。

原坏事件费用实际使用 OriginalCDFPullback 的绝对端点分支，两个符号的 s S 均≤|S|，所以 E_s∩Nᶜ 包含于已付原事件。三角不等式确实支付条件误差、(1-p)Psi 和坏事件，得到 C r(t) Psi(t)。没有从最大值 CDF 反推端点 CDF，没有把目标尾界留作前提。

### Q0、所有正阈值与原子

244–335 行在 t>0 时精确证明 raw 乘法闭事件 E=F∪Z、F∩Z=∅，其中 F={t≤sW}、Z={Q=0}。Q=0 时 S=W=0，因此 E 成立而 F 不成立。由此支付 |P(F)-Psi|≤|P(E)-Psi|+P(Z)，没有丢掉零能量闭边界。利用 r(t)≤(1+t)^3R 与 Gaussian 权得到局部 D R，D=A B+16。

337–414 行常数 C=8/delta+D+B/delta+1 在 nu/n/t 之前，delta=e³/8。R≥delta/8 用差≤1。0<R<delta/8 时，R>0 由有限正二阶矩和 n>0 证明；在 [0,delta/R] 用介值定理选 L，使 (1+L)^3R=delta，并从小 R 推出 L>1。0<t≤L 的 smallness 逐点证明；t>L 用真实 F 尾事件单调性和 Psi 单调性，把两者各自控制在 (D+B/delta)R。这里没有对大阈值调用未经证明的小预算定理，也没有把未知目标概率作为外部假设。

416–509 行对 v<0 使用 s=-1、t=-v 的闭尾。对 v≥0 使用 t_k=v+1/(k+1)>0；E_k={t_k≤W} 递增，且其并集精确为 {v<W}。概率递增连续性和 Gaussian 尾连续性给严格尾界，再用可测的精确补集 {W≤v}。因此 v=0、正/负阈值以及原分布在任意阈值处的原子都完整覆盖；没有假设原 law 无原子或对称。

### 原 law、同一尺度和预算

511–595 行仅输入原有限二阶矩、均值 0、正二阶矩及 n>0。sigma=sqrt(E X²)>0，c=sigma sqrt n>0，nu=map(z/c)mu；map 积分和原二阶矩可积证明 nu 的有限二阶矩、零均值与 n E_nu Z²=1。坐标正缩放 A 推前 pi mu 为 pi nu。

逐路径通过 energy_smul、prefixSum_smul 与正平方根证明 W(Aa)=W(a)。Q=0 两边明确为零；Q>0 才约分。头中的 normalizedLaw 和 R 与证明中 nu、truncationBudget nu n 0 定义相同。不存在错用 sqrt n、sigma²、改变中心或改变原零能量定义的步骤。

### 解析初值、符号和真正积分

597–665 行 g(w)=if w<x then 1-exp(-2x(x-w)) else 0 在 x>0 下反单调且取值 [0,1]。在 endpoint=wall 的等号处走 else=0。逐路径 physical 等式对任意 s 都成立：Q>0 时 q=sqrt Q>0，sS/q<x 等价于 sS<xq，指数经 q²=Q 变成 -2(xq)(xq-sS)/Q；端点在墙上或外侧时两个定义均为零。Q≤0 的外层分支直接一致；energy 非负确保应用范围。没有把一个实际桥路径概率展开为显式公式。

667–746 行先用有界反单调可测性证明 Gaussian 下 g 可积。标准密度 phi 满足 phi(w) exp(-2x(x-w))=phi(w-2x)，由指数配方逐点证明；截断积分差的两个被积函数都实际可积。平移不变性把第二个 Iio x 积分变成 Iio(-x) 的 phi 积分，结合真实 Gaussian 密度表示和 Psi 对称性得到积分 1-2Psi(x)。这是实际积分计算，无未证积分假设，也没有调用实际 Brownian 反射识别。

748–812 行 s=1 直接推前；s=-1 时精确使用 {-W≤v}={W≥-v} 与 Iio(-v) 的补集。lower_set_discrepancy 从已给 closed CDF 控制开 lower set，Gaussian neg-map 对称性匹配基准；未把原 Iio 偷换成 Iic。这保证第二头对两个符号使用同一个已实付 scalar CDF。

814–974 行首先实际实例化新第一头产生 hCDF，再以 signed CDF 和已接受反单调 [0,1] 期望比较得 |E g(sW)-(1-2Psi(x))|≤CS R。V 可测且 [0,1]，故在真实原 pi mu 下可积。原 Q0 producer 的 scale=sqrt(n E X²) 经平方根乘法严格等于 sigma sqrt n，因此这次仍为同一 R。

外层 guard 费用明确通过点值等式 g(sW)=V+1_Z g(0) 积分支付，0≤g(0)≤1 给 |E g(sW)-EV|≤P(Z)≤16R。没有默认 g(0)=0；当 x>0 时它确实非零。PR303 的原实际 maxWithZero 闭 crossing 事件与此头相同，0<x≤1、同一符号及归一化都对齐。strict survival 为该闭事件的精确补集，包括墙等号和 Q0。三角不等式给最终 C=CH+CS+16；两个常数均先于 law/n/x/s。PR303 只在这里支付 host，不承担 scalar 证明。

## 旧依赖的精确复用

13 个必要完整消费头/定义值已全部阅读，并逐字核对到原源指定起始行与提取 hash；候选 source_inputs 的 46 个源文件哈希/字节数均核对。旧证明只复用已有合格完整独审与原内核/AX 证据，没有重新审查整个旧模块或重编旧 producer。

EndpointRelativeError 根资格 SHA256 `d8b92394cf4dfaae38b7dd43121567a0cbde56294221b5efe72d43f3037834bd`，旧完整 coverage SHA256 `9da3847bddd5b8f23314dfd54b33eccc399a6b54a42ad2e960e2e04f6e81539b`。其 source `e9624ff50b79c8e41b749e4b6851870129797a38c692b809a90e81cda8699223`、original object `d151025f575332bba21c3fe1dbf50bc30fca5715dce069692c515d2f32398804` 均冻结。

此次唯一 private 消费为 Root 明确授权的三名，三者旧实际 TYPE、源码证明块与旧全证明/AX 覆盖均逐名绑定：

- `_private.Shao.Probability.EndpointRelativeError.0.Shao.Probability.er_source_endpoint_inputs`：旧 actual index 2，type SHA256 `347891b61c96f6097ea4f1b3392d81c3ae87eec2806a6f85441ac401f3fae2f5`。
- `_private.Shao.Probability.EndpointRelativeError.0.Shao.Probability.er_reflected_weak_tail`：旧 actual index 45，type SHA256 `b5a26f7ef7e60ff224eb5a43cac765c8b23bf21883aa85e287f690bd516f87d1`。
- `_private.Shao.Probability.EndpointRelativeError.0.Shao.Probability.er_bounded_weak_tail`：旧 actual index 46，type SHA256 `31cce1edc2dd441a2f4d8e1ece95ae0813f037e2e3963ecbed01b9cf0d526623`。

129、146、153 行的内置 by_elab 直接返回 `Lean.mkConst (Lean.Name.num <private-module-prefix> 0 ++ <user-name>)`。这里 0 是 numeric Name 分量，和字符串 dotted 名称的解析不同。三个原常量表达式的实参、完整输入类型及结果已逐项核对；原成功 kernel 正常检查应用。它们不生成公有 adapter、改变旧定理、引入新非定理 owner 或绕过内核。

PR303 根资格 SHA256 `8e01a77733d3786183c0d36220bb9fcaf10880ef6e61fe9ea63185a701fbce44`，source `4b653cba9a9f427cd1086a153e702d7d09f684814919f0a46cfff17da335d190`、object `6b28b4f93b43ac3077989dacf8f52677557db9cae07033def1103a5dc306c2bd`。原 Q0 source `9e4380fc2e70a64b6ff7661f5f34cde9c18c1e5537e24b4165faeb46c74aee45`、object `2dbf2e7971700bc33e8fbc80c5146c7ad8ef6c9a5ee2da13dc2f7d082f3d90e5`。服务器实际消费的这些对象均独立 hash 匹配；其它已接受的 CDF transfer、Normalization、Gaussian completion 和截断接口按 source-bound 资格复用。

## 声明冻结与真实操作先后

公开冻结文件 SHA256 `473550c16a18295b51c99e4aef859ff3a49b48a4d06084cbf3958af6991032cb`；freeze MD `1166156b9c053e61c9d144b7c43ba13f23747b4413e3cc7ad1212704ae467f8d`；activation `9b2a84f9e0f0a6ca130585392cb26097556253d07d580a0664be79899dd563fc`。公开两头及私有九头均从实际源独立提取完整头并与冻结字节对齐，未改假设、let 值或量词。

私有冻结 provenance SHA256 `9307db8c216b8d4f8242fe49e827fe2e9953a5a8a1da10840a78b848f544f40b`。独立读取原 rollout 的稳定前缀 22460451 字节/7103 行，SHA256 `422f1ff2d1dbbde21679f6f914f72308129a8c718a30d75301e4d0f7f1dcd122`。按每条已索引 byte offset/length 验证原 raw JSONL 行 hash、event ID、FileChange 完成状态、原 content hash 及开始/完成时间；九名均满足冻结完成时间严格早于首次 body 开始时间。未用 mtime，未重新生成历史事件，未复制整个会话。

四批完整头事件为原行 6602、6801、6955、7073；对应首次 body 分别为 6618、6818/6895、6987/7020、7103。完整逐名时序、原始 offset/hash 和最终 header hash 在 JSON 与 local-verification.json 保留。positive-tail 首次 body 的历史原 hash 与最终修复 body 不同，按原事件核对历史首次值，不错误要求初稿等于最终证明；冻结头始终相同，最终完整源独立审查。

## 原服务器核验和资源

只读核对原成功 check16：原 kernel16.rc=0、audit16.rc=0，原 kernel 日志 0 errors/44 linter warnings。读取原 rollout 第 7252 行的真实已完成命令，确认同一 root-heavy.lock 内先编译完整冻结源到 producer16，再复制该原对象供 all-owned audit 导入，且前后源 hash 断言相同。两次 native Lean 命令均 -M8192 -j4、CPU10–13；并非把两个互不相干的成功收据拼接。

原审计遍历全部实际目标 owner、递归 collectAxioms，并拒绝白名单以外公理。27 项全为 theorem；每项实际公理均属于 `propext, Classical.choice, Quot.sound`。完整源没有 sorry/admit/新 axiom/unsafe/native_decide。精确版本为 Lean 4.36.0-rc1、mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，package view 为 shared-v34。

64 个原服务器证据文件/消费对象按已有绑定只读 hash 通过，包括历史失败和成功 partial；完整成功资格仅给 check16。partial05/13 不冒充最终整源资格；check14 失败与其 host metadata 错误保留。Git 发布超时不是证明结果，当前 PR/head/blob 已独立观察，不作不确定重推。

本审查新增 Lean=0、AX=0、producer 重编=0；未修改生产源、旧证据、其他线、缓存或集成树。没有新子上下文、sidebar、Goal 或自动化；OQ3 保持用户暂停。最后服务器目标进程观察为空，target in-flight=0；所有本审查工具调用已结束。

## 原文忠实性与边界

完整阅读了原只读 c12 supplement 3933–4027 的输入归属和 cn:zero/hostcompact/scalar/hostgap，以及 main 1107–1158 的相关装配边界。第一头兑现 cn:scalar 的有限二阶矩 iid、零能量置零统计量、全实 closed CDF 与普适 CR；证明路线使用已合格单侧尾链，没有输入原文 10.2/25 精确常数。Pinelis 引述 Shao 的归属保留，没有新颖性或精确常数复现声明。

第二头兑现 0<x≤1 的两个符号 strict survival 对显式解析初值的实际原 law 期望差，并提供可积性和物理 Gaussian completion 逐路径值。它没有证明任意 BridgeNoise 或实际 Brownian bridge 的全函数半线反射公式；该实际路径概率识别不能由此处一维 Gaussian 积分计算替代。实际 Brownian 半线识别、实际 interval 概率识别/全 smallTaylor 及原 C1/C2 完整装配仍 OPEN。其它原根范围不扩大，OQ3 不唤醒。

## 交付与释放

逐名 TYPE/proof/AX coverage、各绑定、读取范围和独立确定性核对见 `coordination/common-scalar-initial-budget-full-review.json`。审查指定模型/effort 为 gpt-6.1-sol/xhigh；本上下文不可见实际运行遥测，actual model/effort 与 input/cached input/output/reasoning-subset 使用量均记 null，不据推测填数或折算订阅比例。

本目标审查写权与执行权在最终 `drafts/c12-scalar-initial-budget-final-review/RELEASE.json` 封存后 RELEASED_TO_ROOT，0 in-flight。Root 可据本完整审查和原 check16 作 source-bound 资格判断；不需要为上下文变化重跑已成功证明或旧 AX。
