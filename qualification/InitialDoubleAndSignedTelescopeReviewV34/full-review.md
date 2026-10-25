# 189–191 独立完整源码数学审查（静态阶段）

STATUS: CORRECT

机器证据状态：PENDING_SERVER_KERNEL_TYPES_ALL_OWNED_AXIOMS。formalQualification=false。C2/C12 仍为 OPEN。

本结论仅表示：对下列冻结字节的全部新声明、透明值及完整证明作独立源码到数学陈述审查后，未发现数学关键缺口或题意替换。没有运行 Lean/lake，没有观察新模块的实际声明环境、完整展开类型或递归公理集合，不能由此宣称源码已经通过 Lean、所有公理合规或模块已获形式资格。静态结论与机器证据必须合并后才可授予该资格。

## 身份、边界与输入

审查者为 fresh canonical role `/root/initial_double_signed_complete_source_review`；请求配置 gpt-6.1-sol / xhigh；实际后端、模型、effort、input/cachedInput/output/reasoningSubset usage 都不可观察，分别为 null。父上下文是作者／集成者，本上下文只审查，未修改任何候选源、冻结文件、旧库或共享协调文件，也未开启子上下文。

实际运行 ACK 已先发送并写入 `runtime-ack.json`。读取 brief 后完整读取 math-theorem 的 SKILL、prompt-library、openai-workflow、lean-verification；更具体的 heavy0、服务器独占执行及本审查范围约束优先。另读取 SERVER 与 TEAM 的相关状态及用户给出的现行 AGENTS。

17 个输入绑定全部逐字节 SHA256／长度 PASS；`input-validation.json` 保留路径及结果。三个完整文件逐行读取：

| 单元 | 源文件 | 行／字节 | SHA256 |
|---|---|---:|---|
| 189 | InitialDoubleCompletionKernel.lean | 826／38310 | 826f8a4d10c44727380e58a40e2af878f123763debaf4bc762ccab439f726814 |
| 190 | InitialDoubleCompletionBudget.lean | 743／37123 | c923fe29c04418935766f1a6213077f2850ab784027702fdef2f9048876c3728 |
| 191 | ActualSignedDoubleTelescope.lean | 437／23850 | 044b87e87bdca7db5d69e949a7737d334a5dbab95d2bb000337fc2dfbb3f6536 |

合计 2006 行、99283 字节。三份源码为 UTF-8 无 BOM／LF。37 个源码级声明／值全部与相应预先冻结文本的数学 token 相符：189 为 1 def＋14 private theorem＋1 public theorem；190 为 2 def＋10 private theorem＋1 public theorem；191 为 1 local instance＋5 def＋2 public theorem。此为源码级计数，不能替代实际 Lean environment owner 数。逐项完整 head/value、位置及冻结来源在 `new-source-coverage.json`。新源码禁止 token 只读扫描结果为 0 hits；这不代替最终递归公理审计。

一次上传的既有收据也完整读取：18 transferred-file bindings PASS、三个 object 均不存在、LeanAX=0。它的 SHA256 为 427369cd9b52658b9a0ba4eb13a64764c8be0ce179934a02b921dacbc06ad0fd；本上下文没有再次上传或执行门禁。

## 原题语义及旧证据消费

完整读取两个 theory 目录保存的原始 source excerpts，包括 supplement 3934–3965、4699–4749、4752–4775，main 884–940、980–1032、1271–1304。原始文件没有修改。初始双弱击中事件是在同一个标准桥上分别存在上、下击中时间；不要求两个时间相同，也不把两事件独立化。有限样本部分保留实际 Q、W、iid 法、EX=0、EX²=1、x≥1 与 b≤1/2。

完整消费 46 个旧项目声明头与 75 个相关透明值；这些块覆盖 31 个物理源码文件。逐块路径、行号、完整文本、上下文和文件哈希分别写在 `consumed-project-heads.json`、`consumed-project-values.json`。全部 31 文件与已接受 `library/verification/receipt-v90.json` 的 exact-source map 一致，见 `old-source-reuse-bindings.json`，无缺项、无不同哈希。v90 receipt 为 PASS，固定 Lean 4.36.0-rc1／mathlib 807d3836b165983210ee2ecf3cd28f239436949c，并保留标准公理白名单 propext、Classical.choice、Quot.sound。旧证明仅复用，没有委派或实施一次新的完整旧证明审查。

这里的旧块包含：完整 bridgePath／strictUpper／strictLower／strictInterval 与三 completion；bridgeNoise／bridgeLaw 与同端点联合分布头；完整 imageA／imageB／spatialTailBlock／candidate values；normalizedEndpoint、truncationF／budget 与其完整所需不等式头；标量 closed-CDF producer；sourceAlive／sourceValue／completionExt 的每个历史及零能量分支；真实 uniformPermutationLaw／revealLaw；实际剩余平方和、补偿系数、small/large selected remainders、投影增量、三域导数和全部消费的 integrability／telescope／sign 完整合同。

本审查也核对三个已独立审查的理论接受记录的精确哈希：c9bfb585f771aec9859328d2f26925f0eb46ce04c9ec779db76a51e25d9b26b1、e90ae242ff0ab866669a096b628a9af934b217653cbb0fa59466868cef414200、6f862528cd5b128e390e164f349af7cea5cb24d1b6e56736cd4a4cfcb53aa722。它们提供既有数学背景，没有代替本轮对新 Lean 证明的完整阅读。

固定版本的原生接口也作服务器只读源码核对；实际 mathlib Git HEAD 正是上述 807d3836。新取的完整接口与原生 def 文本在 `native-source-heads-complete.json`、`native-generated-discovery.json`、`native-generated-contracts.json`；已有 exact native excerpts 的哈希另列在 coverage 中。数学承重接口包括 eVariationOn 的真实 supremum 定义、sum_le、mono、共同端点 union、BoundedVariationOn.dist_le、continuous_tsum、几何级数、measureReal 的包含排除与 AE congruence、HasLaw.measureReal_eq、map/integrability、product indicator integral、bounded multiplication、norm integral bound 及真实 gaussianPDFReal 值。

HasSum.tendsto_sum_nat、Summable.sum_le_tsum、Equiv.sum_comp 是当前源码中由 to_additive 生成的名字；完整读取其 HasProd.tendsto_prod_nat、Multipliable.prod_le_tprod、Equiv.prod_comp 生成头和属性，确认本轮使用的参数顺序与数学合同。没有把静态生成规则推断冒充本轮观察到的 elaborated type。最终实际环境与类型仍 pending。

## 单元 189：完整桥双击中核

**定义及前缀私有证明，15–73 行。** doubleCompletion 是严格上生存事件与严格下生存事件的补集之交在同一 nu 下的概率。包含排除确为 1-U-L+I；measurableSet 条件完整；概率界由概率测度得 0≤f≤1；可测性通过共同参数映射及三个 completion 的已接受可测性取得。没有更换为两次独立桥抽样。

**外部／内部 images，75–185 行。** 当 w≥x 时，上生存集由终点条件为空，下反射给 exp(-2x(x+w))；w≤-x 对称处理，包含 equality wall。内部 |w|<x 同时满足两半线反射及 killed-sine/image identification 的严格端点前提。原生 imageB 的 m=0,-1 正好消去两个最近反射项；imageA 的 ±1 保留；tail 的整数索引 n+2、-(n+2)、n+1、-(n+2) 逐一展开正确，得到两组 ±线性指数，未跳过负指标或整个 infinite tail。

**变差基础私有证明，187–285 行。** monotone／antitone 证明直接对 eVariationOn 的真实单调序列求和；符号选择正确，有限和望远镜后仅用 0≤f≤C。variation_add 用实数三角不等式；neg 等距；pointwise_limit 对每一个有限 partition 先取极限再用共同上界，未把逐点收敛错误提升成一致收敛。

**几何界私有证明，287–356 行。** k≥1、|v|≤x 给四个 image 的 exp(-4kx²) 上界；x≥1 给 0<r=exp(-4x²)≤1/2。u_n=2r^(n+2)+2r^(n+1) 可和且总和 (2r²+2r)/(1-r)≤6r；2r 加任意 prefix≤8r。所有分母的正性均有证明。

**公开证明，358–825 行。** 钳制 c(w)=max(-x,min(x,w)) 连续、单调且落在 [-x,x]。四类 A,D,J,K 为 exp(-(a+b c(w)))；按 b 的符号证明各自单调、非负、振幅与变差界。T_n 的 norm 和变差共同由 u_n 控制，故全实轴函数 F 的 series 连续，prefix 有共同 8r 变差与绝对值预算，极限保持这些预算。

关键墙恒等式按原生分组而非未经证明的另一重排建立。s_k=exp(-4k(2k+1)x²)，在 +x 有 A_k=s_k、K_k=s_k、D_(n+2)=J_(n+1)、D_1=r，因此 T_n=s_(n+2)-s_(n+1)，S_N(x)=r+s_(N+1)。s_(N+1)≤r^(N+1)→0，故 F(x)=r；±指标交换给 F(-x)=r。这里既没有把有限 prefix 错写成 r，也没有删去端点残项。

全局修正 L(w)=r-exp(-2x(x-min(w,-x)))、R(w)=r-exp(-2x(x+max(w,x))) 均在 [0,r]，分别反单调／单调，变差各≤r；内区为零。逐分支证明实际 f=F-L-R，且包含两面墙的 equality。于是连续、0≤f≤8r、TV(f)≤8r+r+r=10r。两侧无穷远极限分别由精确 exterior reflection 指数趋零取得。完整公开冻结结论全部覆盖，未以有限恒等式代替整个核。

结论：CORRECT（静态数学及源码语义）。

## 单元 190：仅有限二阶矩的真实初始预算

**两个值，16–24 行。** initialDoubleObservable 在实际 energy=0 时恰为 1，否则为同一个桥的 f(W)。brownianInitialDouble 使用提供的同一个 B，分别 ∃t 的 x≤B_t 与 B_t≤-x；终点闭切口 B_1≤v 在公开结论保持原样。

**antitone bounded transfer，26–55 行。** 先从有界可测性证明两个真实积分都存在；M=0 独立处理；M>0 对 f/M 调用旧 closed-CDF antitone_unit_expectation_error，再恢复 M。没有使用未证明的 CDF-to-expectation 假设。

**Jordan 分解，57–175 行。** 前缀 P(w)、后缀 Q(w)、总变差 T 都有限；原生 union 在共同 w 上给 T=P+Q。左尾 0 给 |f(w)|≤P(w)，右尾 0 给 |f(w)|≤Q(w)；两者缺一不可。共同端点 union 又给 |f(a)-f(b)|≤Q(a)-Q(b)。u=(Q+f)/2、v=(Q-f)/2 都反单调且落在 [0,V/2]，f=u-v。各自真实可积，积分相减合法，总误差≤V delta。该论证保留任意点跳跃值；不要求 f 连续、比较分布无原子或忽略截止点。

**闭切口，177–226 行。** g(w)=f(w)1_{w≤v} 的每一步变差由原 f 步差加一个从 M 跌到 0 的单调阶跃步差控制。最多一次 crossing，包括精确 cutoff equality，额外费用≤M。以后取 M=8r，得到 18r，而非在原子处删掉 f(v)。

**support split，228–345 行。** 所用点态不等式 y²≤h²1_{y≠0}+F(y)/h，分别覆盖 y=0、|y|≤h 与 |y|>h，精确 equality 在前一分支。normalizedLaw 是 z/sqrt(n) 的真实 map；n>0 给 sqrt(n)>0，实际 second moment 恰满足 n∫z²dnu=1。Y=(1+x)X/sqrt(n) 的 F 被 Y² 控制，故可积，n EF(Y)=b。取 h=2b/(1+x)²∈(0,1]，积分支撑分裂给
(1+x)²≤n h² pi+b/h，b/h=(1+x)²/2，
从而 n pi≥(1+x)^6/(8b²)。b>0 由真实正二阶矩的 truncationBudget_pos 给出；未假设全三阶矩或借用不适用的 Hölder 截断。

**actual zero energy，347–384 行。** Q=0 等同所有 iid 坐标均为 0；对真实 pi-product measure，概率正好 rho{0}^n=(1-pi)^n≤exp(-n pi)。保留所有 zero atoms 的质量，得到指数预算，未把 Q 替换成确定方差。

**Gaussian 两个数值引理，386–461 行。** s=1+x≥2、0<b≤1/2 给 x²/2+s/b≤s^6/(8b²)。exp(-s/b)≤b/s，由 exp≥1+t 与正分母严格推得。当前 gaussianPDFReal 实值为 (sqrt(2pi))^-1 exp(-x²/2)，与旧合格 Mills 下界 density/(1+x)≤Psi(x) 组合得 exp(-s^6/(8b²))≤sqrt(2pi)bPsi(x)。另由 1+x≤exp(7x²/2) 得 r≤sqrt(2pi)Psi(x)。没有换阈值或使用另一个尾函数。

**实际 Brownian 积分识别，463–547 行。** D 是 BridgeNoise×R 中两个 strict survival 补集的交；参数 joint openness 给 D 可测。产品指示函数先有真实可积性，再通过 Fubini 得 sections 积分。ae_bridgeNoise_eq 在同一 AE 集上同时对所有 BridgeTime 成立，故 bridgePath(0,1,B1,g)=B_t 可同时用于两个存在时间事件；not_forall/not_lt 精确产生弱击中。bridge_endpoint_hasLaw 的完整头给实际同桥与终点的 product law，未把 independence 当成新前提。切口集合 D∩{w≤v} 可测，其 section 保留等号；事件本身即使只有完成测度意义下的 AE 识别，measureReal_congr 足够且不要求 B 逐点全可测。

**公开组合，549–740 行。** C=(18 Cs+1)sqrt(2pi) 在 rho、n、B、x、v 之前选择。Cs 来自旧 finite_second_scalar_closed_cdf_budget 的真实结论，EX²=1 将其 sigma 化为 1；normalizedLaw 完全一致。R0=budget(nu,n,0)≤budget(nu,n,x)=b，closed CDF 对应真实 map W P。kernel 提供 f 的连续性、两尾、10r 变差与8r振幅；无切口／闭切口分别使用10r／18r。

在 E={Q=0} 上，Z 与 f(W) 可相差接近 1。因此代码 661–671 行从两值都在 [0,1] 证明 norm 差≤1_E，并支付完整 P(E)。这是原始 proof 中“P(Q=0)×sup j”不足之处的明确修正，未改原假设或 observable；报告不能还原成错误的较小费用。hpaid 的积分线性每一次都消费真正的 integrability，之后用上面零能量与 Gaussian 预算闭合常数。截止后的 Zg 也在 [0,1]，仅在 Q=0 可与 g(W) 不同，故同一完整修正适用。两尾 g 在 -∞ 跟随 f、+∞ 最终为零。两个结论的可积性和误差都覆盖。

结论：CORRECT（静态数学及源码语义）；标量估计继续按原文明确归属于 Shao 的截断估计／Pinelis2011 转述，不宣称本单元原创证明了该外部结果。

## 单元 191：实际历史标志与带符号望远镜

**局部实例和五个值，19–50 行。** LabelPerm 使用与旧 revealLaw 完全一致的离散可测空间 ⊤。三个域值都来自同一个 sourceValue 与 Q；double value 为1-U-L+I；retained组合为 I-U-L，separated组合为 U+L-I。sourceRemainder 的实际更新 (y+b,T-b²,z) 和系数 b-b²(z-y)/T 未换成确定方差。doubleCrossingEvent 包含0≤r≤n的两个弱 crossing。

**boundary：52–275 行。** inclusion-exclusion 在同一桥样本上应用。reorder 保留总 endpoint 与 energy，故实际 wall 相同。sourceAlive.interval 当且仅当上下两域都 alive，因而相应 E_I=E_U∩E_L。

Q=0 时所有 sourceValue=0，实际 double value 各秩为1；实际 wall=0、prefix0=0，两个弱 crossing 都发生，rank0的 observable 也为1。Q>0时，每个 r≤n 的真实 remainingEnergy 非负；若为0，remaining_population_geometry 给 remainingSum=0，所以 y_r=z。此可达条件正是 eventCompletionKernel_data 识别 completionExt 与真实桥事件的前提。由此每个 sourceValue 真是带完整历史／终点标志的同桥 E_J 概率，double value 在[0,1]，不是仅对有限series或猜测的任意 kernel 作概率解释。

rank0 处理所有外端点：若 bridge survival 本身非空，其首尾条件迫使 sourceAlive成立；否则 E_J与S_J同为空。正缩放 c=sqrt(Q) 将实际 wall、energy、endpoint分别变成 x、1、W，三个域使用相同缩放和 Q，故 rank0 精确等于190.observable。这里没有忽略 Q=0，也没有假设 endpoint 在墙内。

rankn 的 remainingEnergy=0、可达 y_n=z；completionExt 的可达末端值给各域 sourceValue 等于严格 survival 的指示。否定严格 survival 正好是原样的弱 crossing（包含 equality）；intervalAlive 等同两个alive，逐布尔情形给 double crossing 的指示。所有历史 flags 都从完整先前路径产生，未只看当前一次 crossing。

**stopped telescope：277–435 行。** 输入 B 的真实上下反射生成 HalflineReflectionIdentities；actual_source_interval_differentiable 对所有必要正时间、内端点供给实际 regularity。hData 对 .upper/.lower/.interval 分别消费完整旧 kernel-data heads，得到实际 derivative family 的 measurability、KernelBounds4 和真实 HasDerivAt，不把 caller-supplied target identities 或 global interval differentiability 当假设。

F、G、nu、H、P、revealLaw 在三个域完全相同。nu 的 reveal-stop合同给nu≤n，hcap给同一个energyCutoff。source_stopped_integrability 供给 A、I、R 的真实可积性，source_parts_measurable_integrable 供给 retained/separated sums 的真实可积性；有界可测 m 通过当前 Integrable.bdd_mul 的正确左乘顺序处理。没有只证明裸补偿系数 L1 就把整个余项当可积。

source_selected_remainder_decomposition 逐秩在 actual selected event 下分解 R=LS+OS；大 crossing、等号、死历史、外端点和零未来分支都由未改动的旧实际 values 保留。每域 masked stopped telescope 后，真正可积的 LS、OS 允许分开积分。source_separated_overshoot_sign_domination 以同一个实际 G 和 HasDerivAt族给所有 a,sigma,r 的 O_D=O_U+O_L-O_I≥0，无域间独立假设。

Z=(A_I-I_I)-(A_U-I_U)-(A_L-I_L)，L=LS_I-LS_U-LS_L，O=OS_U+OS_L-OS_I 的点态代数和真正积分线性给 ∫Z=∫L-∫O。任意 |m|≤1 的 signed mask 都保持该等式；hminv 是冻结原题的保留条件，旧积分恒等式实际可更强而不需要它，不构成暗中新增前提。只有最后 hm0:∀a,0≤m a 才把 O_D≥0 升为 ∫O≥0，推出 ∫Z≤∫L。没有将 signed mask 的贡献误称非正。

结论：CORRECT（静态数学及源码语义）。这仅关闭 frozen boundary 与 signed finite stopped identity 的数学证明范围；未闭合 retained budget、终端替换、残差比较或 C2 根定理。

## 真实失败、未执行证据与续接

只读辅助检查有三种实际技术失败，均保留并精确区分于数学结果：

1. 原生接口第一次发现脚本在服务器调用 rg，FileNotFoundError，rc1。已保存 `native-source-read-raw.json`；无 Lean／源写入效果。随后仅改为已有 grep 完成同一只读发现，attempt2/3 原收据保留。
2. 本地解析旧 native excerpt 时，对数组误取 stdout，出现两条 ConvertFrom-Json 空输入错误；之后用数组／对象类型判别修正，读取成功。这个失败既没有修改输入，也不产生“接口不存在”的结论。
3. 本地一次 PowerShell foreach 后直接接管道产生 ParserError，整条未执行；随后将结果先收集成数组再输出成功。最终 forbidden scan 实际0 hits，理论接受哈希实际PASS。没有把未执行那条当成功检查。

此外，head抽取初版会在 theorem target 内 let 的 :=／参数默认值处截断，或对直接 term proof 向后多读。最终重新用括号层级与 target-let识别，保存完整46 heads；所有承重 heads 已人工完整读取。早期原生搜索返回几个同名异命名空间（BoxIntegral、VectorMeasure等）块；它们保留为原始发现，实际消费限定为 MeasureTheory Bochner／Prod 等在报告列明的路径。缺失搜索名中的非限定拼写已由 Measure.isProbabilityMeasure_map_iff、HasLaw.measureReal_eq 及 to_additive完整生成头解决，不能据此推断数学缺口。

本轮没有 Lean/lake/AX command、没有机器门禁、没有实际types输出、没有新对象。所有 static pass、旧source reuse、native read receipt 都不能充作这些未执行证据。资格证据要按 exact-source packet 继续：

- 先验证这17输入和3新源哈希未变，以及本目录封存与release未变；
- 在中央有效分配的C12 heavy phase、原c12-heavy.lock与当前CPU／内存规则下，按已有审核模板产生每个新模块的target内核通过收据；
- 观察各模块实际完整elaborated declaration types及全部defining-module owned constants清单（含private、生成项、defs、instance／proof helpers）；
- 对全部owned names递归collectAxioms，严格验证只含propext、Classical.choice、Quot.sound；
- 核对公开4 targets、8 defs＋1 local instance以及所有真实新增owner的类型／值与本轮完整源码覆盖一致；计数从实际owner map派生；
- 若出现编译／审计失败，原失败保留，修复必须保持冻结声明与假设；新proof字节只使实际受影响部分审查失效。对差异部分补独立阅读与针对性门禁，复用未变源码与已接受旧证据，不自动重审本轮2006行或所有旧模块。

现有审计源码／CHECK-PLAN只属于准备材料，没有执行就仍pending。静态阶段已完成并释放本目录writer；没有保持一个等待heavy名额的隐形运行状态。下一个精确依赖是189的实际target kernel/types/all-owned-recursiveAX，然后190，再191或父按同一依赖关系安排。C2/C12 OPEN，未声称原始根组完成。

