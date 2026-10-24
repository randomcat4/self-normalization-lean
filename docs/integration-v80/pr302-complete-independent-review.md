# SourceActualIntervalProfileBudget / PR302 独立完整终审

STATUS: CORRECT

本结论仅适用于 SHA256 `58eef62954931c95be1228accb921de6db3092a4d681184d6e1fef4ab2d20ef6` 的完整 389 行新源和下列精确编译对象。已完整审查源到冻结声明、两份全部证明、全部 11 个实际所属 TYPE、2 个完整非定理 VALUE 和 11 个逐名递归 AX 结果。没有发现关键数学、编码或当前证据缺口。这里接受的是带显式真实解析前提的 canonical iid population × 同一独立均匀排列消费者；所有原研究根仍 OPEN。

## 身份、独立性与范围

审查者 `/root/actual_interval_profile_budget_final_review` 是 fresh、非作者上下文；作者是 `/root/permutation_reveal_candidate`。本审查按 math-theorem 完成，没有使用 math-ultra、子代理或自行修改证明。已读 AGENTS.md、SERVER.md、streamlined-acceptance-current.md、所需 math-theorem 角色/Lean 规范及当前协调字段。当前 root 为 `01a16be2-3e35-7e13-97d3-7b11b603dead`，接受基线为 v79/main `927797d9d551e4b57e58abfaba7c7604f0cbcca4`，OQ3 为 PAUSED_BY_USER。

唯一写域是本报告 MD/JSON 和 `drafts/c12-actual-interval-profile-budget-final-review/`。没有生产源、旧报告、旧收据、旧 RELEASE、版本、缓存或共享实现改动。作者 RELEASE 已逐字节绑定，writer/execution 已释放且 inflight=[]。审查者未执行任何 Lean、AX、build、cache 或合并命令；原有精确成功证据予以复用。

请求配置为 gpt-6.1-sol/xhigh/fresh。实际 model/effort 以及 input、cached input、output、reasoning subset 无可观测遥测，均记 null；没有推算订阅比例。

## 精确绑定与现有服务器证据

| 工件 | SHA256 / Git 标识 |
| --- | --- |
| 新源，23149 bytes / 389 lines | `58eef62954931c95be1228accb921de6db3092a4d681184d6e1fef4ab2d20ef6` |
| 原成功 attempt007.olean，1043592 bytes | `e20a2a3de177ff66618c294b219643a1f041e7ccb7a22f703e026fe33af97dbc` |
| 作者 receipt.json | `fc142130971e4029706c1ba033f9eec5a6dc8d601ad95759caf8c624e8887a0a` |
| 作者 RELEASE.json | `f315167436bf742816d28a3e645df4c9a44d90388bf60a31115305f60f48c7ff` |
| 全部实际 TYPE/VALUE，113902 bytes / 1578 lines | `c4551c76888e6a1be085a6d168c6754c7522bbf0ed70ac68419d076bf521b404` |
| 全 owner 审计 JSON | `4ae823b1a352c3bf3002f2fafa2771bc26a8fb0a8e26db0fb128bfe230637ab0` |
| 原 kernel log，24448 bytes | `4f4074628c28ffe30c763dc5308887063b241f61ffa2b2791b8f0a449822400c` |
| 原 AX log，114130 bytes | `53fdd600d2a14ef3fe9dcef06a806449d2882a4e928cacc5ba1f06e7479f7f8d` |
| 冻结说明 | `d5dae4b138889228cbb13b138ff641bd44e9f84e6be7e925ac19154828b80e8b` |
| 完整 frozen.lean.txt | `666816d6d810046a805c8dee1c6ac1d26d1a03389d301bbc0ddcc16bfd4027ac` |
| 作者 activation | `e2f85df4ac1ca983a9a54ebe1869d633128b4745d619722b5c4d8a1b75066663` |
| PR302 head | `54b993d28eca8c6b405efe278d9991b65cd3d1f1` |
| PR302 tree / blob | `de6796d8d138b2a90183c9e46d099e6a491a565d` / `2fd44a88490d111f386c4424f9915e3a492e9957` |

通过既有 transport_client broker 对原工作树与输出目录作只读校验。服务器源、输出目录源、Git blob 均给同一源哈希；工作树安装对象与原 attempt007.olean 精确同哈希；工作树干净，父提交差异只有新源。作者 receipt 的整模块 kernel rc=0、全 owner audit rc=0 与保留成功日志/原对象一致。原 kernel log 没有 error 行；警告不构成新失败。没有把“日志无错误”单独当作退出码证据。

实际 TYPE/VALUE 文件恰是原 AX log 从首个 TARGET_DECL 开始、到 AUDITED_TARGET_CONSTANTS 之前的连续原始字节切片，前缀166 bytes，切片113902 bytes；尾标记精确为 `11 PUBLIC 2 THEOREMS 9 DEFINITIONS 2`。不存在打印省略标记。审计代码实际按 `env.getModuleIdxFor?` 的 owner 选择，再对每个常量调用递归 `Lean.collectAxioms`；没有按命名空间前缀遗漏 C2 生成等式。

钉定版本是 `leanprover/lean4:v4.36.0-rc1`、mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，packages 解析到 shared-v34/packages。五个直接 dependency 绑定以及九个 qualified import 源/对象/安装对象全匹配。另对实际消费的16个源核对本地只读 library 与服务器实际源；四个 Probability producer 和三个新 C2 producer 的已合格源/对象也匹配。全部相关旧完整审查哈希匹配，复用其资格，不重审旧证明。

一次只读路径探针先假定早期工作树直接含 IntervalGaussianLocal 源，因该源实际位于既有 qualified source view 而返回 FileNotFoundError；失败已保留，随后依据 actual-import-bindings 解析正确只读路径。它没有启动 Lean、产生写入或发现数学缺口。完整原始日志和二进制留在服务器。

## 冻结与声明忠实性

独立重新抽取比较 `labelPermMeasurableSpace` 完整实例值、`intervalDerivative` 完整定义值以及两个完整 theorem 头，四项与冻结逐字一致。九个 literal lets 为 sigmaSq、scale、normalizedLaw、R、h、P、nu、L、O，未换值或改序。源仅有上述四个显式顶层声明，没有新 private helper。UTF-8 无 BOM、LF only；无 sorry/admit/new axiom/unsafe/native_decide。

正式证明新增的唯一 import 是已接受的 `Shao.C2.InteriorDerivativeMeasurability`；本次 root 任务明确确认该 import-only 补充已获授权，作者 supplement 也保留此项。它不改变头、定义、实例、lets 或前提。已完整读消费的 `measurable_interiorSpatialDerivative` 头及 interiorSpatialDerivative、spatialDerivative 的完整值，并核对其源 `195abc4d757432aab3e44971c0a4710cd43259c71e785bb9f96f4ea4814a2ca8`、对象 `47072a5f3fcf46e07efd37b37e0f73d4a0c2b55bd38d81f47670da0a6f3f22a6`。候选说明中的差商路线在正式证明中由该已合格 producer 支付，连接通过实际函数完整定义的点态相等完成。没有增加 hGmeas，也没有借用 image candidate 的正则性。

原文只读范围已实际读取：main.tex 869–955、981–1038、1077–1109，supplement.tex 4360–4400、4534–4600，并核对实际概率、projection、Gaussian profile、cutoff 和 iid reveal 接口。原文的严格生存、同一 raw wall/endpoint/tail square sum、独立均匀标签揭示、保留项与负 overshoot 都有对应，第三矩或自然 iid 停时均不是隐含条件。

## 第一公开定理的全部证明，源27–76

1. 源39–46：固定正 T，sourceIntervalCompletion_pos 给对所有 s 的函数相等，而非只在 y 的同值。故 hRegular 转成 actual intervalCompletion 在 y 的可微性，HasDerivAt 的导数正是该实际概率的 deriv。
2. 源47–62：消费已合格的联合可测 producer。其 guard 为 T>0、|y|<w、|z|<w；由 |y|≥0 直接推出 w>0，恰与新定义四条件 guard 等价。guard 真时 eventCompletionKernel.interval 的完整值就是 intervalCompletion，spatialDerivative 的完整值就是对它的 y 导数；guard 假时两函数都零。故得到全参数空间的 Borel 可测性，不限于 live 区，也不增加联合连续、版本选择或 hGmeas 前提。
3. 源63–73：C=4 非负；completion 在[0,1]由真实事件概率的已接受 API 支付。Interior.interval 的两不等式与绝对值条件等价。反射输入在当前正墙/正时间下分别供给所有 s<w 与 -w<s 的真正半线恒等式，终点由 hz 的相应分量供给；interval_deriv_bound_of_reflection 给精确 `4/sqrt T*(1+|z-y|/sqrt T)`，与 masked actual derivative 在当前 guard 同值。
4. 源74–76：正 live 区直接使用同一个实际可微性证明的 HasDerivAt，并展开实际导数值。因此最后结论是实际概率的导数合同，并非任意 G 槽位。正墙/正时间/内部之外只声称定义总化与可测性，没有跨墙可微性。

第一头仅依赖声明中的 Q 概率性、真实 hReflection 与真实 hRegular；这些解析事实本身仍未支付。

## 第二公开定理的全部证明，源79–386

### 量词、退化和可积性，源117–181

先从已合格 iid Gaussian 总预算取普适 CG>0，置 K=2*Csmall+40>0，选 C=K*CG。选择在 Q、rho、n、x 之前，允许依赖已先固定的 Csmall；没有将目标 Gaussian 比较或目标 CR 界放进前提。二阶矩/正二阶矩的原几何 API 给 R>0、h>0。cutoff 的逐排列可测性直接由真实 energyCutoff producer 给出，其定义仍为首次严格剩余能量<h。

x=0 分支使用 sourceAlive 对 k=0 的严格生存条件；prefixSum_zero=0 而 actualWall=0，因此矛盾。L/O 在所有 population、seed、rank 都为0，包括原子、raw Q=0 和 n=1。源139–150 同时支付联合可测性、真正 Bochner 可积性、有限和可积性及积分界，没有调用只适用于 x>0 的 Gaussian 预算。

x>0 分支使用第一头的真实 KernelBounds4 和实际导数联合可测性，直接满足 source_parts_measurable_integrable 的全部条件。该 accepted API 供给每排列/秩的 L/O 可测性及 revealLaw 下各秩真正可积性；有限离散种子提升为联合可测性。实际 TYPE 中新 local⊤ 与 revealLaw 所绑定的 imported⊤ 都是同一离散可测空间的定义展开，不存在新的兼容性前提。用 max(-O,0)=(|O|-O)/2 的两个符号分支得到负部可积，再对 |L| 和有限 ranks 求和；不是把积分默认值当可积性。

### 真实 Gaussian law 与总预算，源182–221

wallSigns.interval 精确为{1,-1}。已合格 early/late/total producer 在同一 h、R、rho、n、x、closed=false 上给总 G 可积及积分≤CG*R；有限2矩是唯一矩条件。fixed_gaussian_weight_measurable_bound 与 head/tail 坐标的可测合成给 G 全局可测。

P 是实际 iid product。坐标 X_i 的分布由 product evaluation 给出，独立性由 iIndepFun_pi 给出。iid_randomPermutation_map_eq_pi 对 population × 独立 uniformPermutationLaw 证明整个 reordered path 的推前恰为 P。hMap 由该定理推得，不是额外假设；IdentDistrib.comp、integrable_iff 和 integral_eq 搬运同一个 G 的可积性与积分。未用固定排列代替实际随机排列，也未断言原自然 iid 滤过停时。

### 逐实际秩 adapter 的所有分支，源222–369

令 w=x√energy(a)、y=实际 reordered prefix、T=实际 remainingEnergy、z=同一 raw 终和、b=实际下一标签。inactive 分支的源 guard 使 L=O=0，而右侧真实 rankGaussianWeight 非负。active 分支严格保留 r<κ、raw energy>0、全部 k≤r 的严格生存、终端严格内部及 T>0。由这些条件和已接受几何实际推得 w>0、|y|<w、|z|<w、T≥h>0、b²≤T；future T-b²=0→y+b=z 由 actual_reveal_zero_future_reachable 推得，没有重新假设可达性。

源243–268 的 hExt 对所有 Y,S 成立。S>0 且内点时双方是实际 intervalCompletion；Y 外域或在墙上时 exterior API 与源 guard 均给0；S=0 时双方恰在 Y=z 且内部取1；S<0 时双方均0。hDer 仍用正 T 上的全函数相等和第一头 HasDerivAt.deriv。于是 localRemainder 对所有 beta 逐点等于实际 C2 sourceRemainder，没有替换 completion 或导数对象。

源269–310 的穷尽分支与实际 source retained/overshoot 值一致：大步 b²>T/2 保留原 remainder 且 O=0；小步内部 projection=b，同样 O=0；小步上退出含等号投影 p=w-y；小步下退出含等号投影 p=-w-y。上退出实际值为 `-(b-p)*(1-(b+p)*(z-y)/T)*FY`，与 upperOvershoot 展开相等。下退出使用 C2 的 B=-b、u=w+y、e=y-z、G=-FY，展开仍得到完全相同的源表达式；源291–295 的 ring 仅支付这个符号代数，没有丢失外部负号。两侧都采取 upper-first；在实际正墙内点不可能同时跨两墙。墙等号有 b=p，所以 O=0。取 max(-O,0) 精确匹配 negativeOvershoot，而没有把可能为负的区间 O 当作非负删除。

源311–315 对 qualified actual_interval_local_gaussian_bound 的全部条件逐项实付。hReflection 被特化到所有未来正 S、对应半线内部 Y；hSmall 仍对所有 beta，要求 beta²≤T/2 和 |y+beta|≤w，正是投影到闭墙未来点所需合同。其右侧只是非 Gaussian intervalIncrementProfile；没有把目标 q³D³intervalEnvelope 或积分预算作为输入。

源316–355 以排列保能量/终和及 gaussian_weight_source_state 识别真实 rank Gaussian 权重。严格 prefix 生存通过 head 的 maxWithZero（含 k=0）分别给 s=1、-1 的 closed=false guard；保留 T≥h 的闭等号。两个 wallEnvelope 完整展开恰是{1,-1}的两个指数，tail first mark 正是同一 b，tail 和正是 z-y，T 同一。终端条件只在应用合法 local bound 后从右侧删除。源356–363 因而得到实际 `|L|+max(-O,0)≤K*rankGaussianWeight`；不存在独立抽样、mark 更换或目标比较假设。

### 求和与积分，源370–386

Fin n 与 range n 由 Fin.sum_univ_eq_sum_range 精确重索引。逐秩不等式求和给 K*G(reorder)。两侧真正可积已分别在 hSi 与 hReorderedGi 中支付，所以 integral_mono 合法；再用同一个 IdentDistrib 的 integral_eq，最后用 CG*R 的已合格 iid 总预算及 K≥0 得 C*R。没有只对期望等式声称逐样本相等，也没有依靠不可积实积分的零默认值。

## 全部实际所属声明的逐名语义评价

以下行号指113902-byte实际 TYPE/VALUE文件。每一项实际递归 AX 都恰为 `[propext, Classical.choice, Quot.sound]`；11项均已读，均为白名单，无 sorryAx 或新公理。

| 实际所属常量 | TYPE / VALUE 行 | 完整语义评价 |
| --- | --- | --- |
| Shao.C2.ProjectionOvershoot.projectionOvershoot.eq_1 | TYPE4–10 | 对所有实 B,u,T,e,G 展开 projectionOvershoot 为 -(B-u)*projectionFactor*G；与实际消费定义完全相同，无正性或非零分母新前提，是生成定义等式。 |
| Shao.C2.IntervalGaussianLargeStep.intervalEnvelope.eq_1 | TYPE14–24 | 对所有 a,y,T,z,b 展开为 wallEnvelope(a-y,|b|,z-y,T)+wallEnvelope(a+y,|b|,y-z,T)，上下墙和 lower 的相反位移均正确。 |
| Shao.Probability.SourceActualIntervalProfileBudget.labelPermMeasurableSpace | TYPE28；VALUE30–53 | 对每个 n 返回 LabelPerm n 上 MeasurableSpace 的 ⊤；完整 lattice 展开未改变离散含义，不含额外参数或假设。 |
| Shao.Probability.SourceActualIntervalProfileBudget.iid_actual_interval_retained_negative_budget | TYPE57–614 | 全部量词与9个实际 let 均保持冻结；Csmall 先固定、C 位于 Q/rho/n/x 前；真实反射/regularity/all-beta closed-future smallTaylor 为唯一解析前提；结论包括实际 κ 可测、真实 L/O 联合可测及 Bochner 可积、联合非负有限和可积及 CR。实际测度确为 P×uniform labels。 |
| Shao.Probability.SourceActualIntervalProfileBudget.intervalDerivative | TYPE618–705；VALUE707–910 | Q 只为实际 BridgeNoise 测度；完整 guard 恰为正墙/正时间/当前及终端严格内部，真支对实际 eventCompletionKernel.interval 取 y 导数，假支0。没有 image candidate、任意 G 或附加隐参。 |
| Shao.Probability.SourceActualIntervalProfileBudget.iid_actual_interval_retained_negative_budget._simp_2 | TYPE914–919 | 泛型 singleton membership 命题等于 b=a；仅生成的 Finset 化简等式，不加强预算或概率假设。 |
| Shao.Probability.SourceActualIntervalProfileBudget.actual_interval_kernel_data | TYPE923–1246 | 实际 Q 概率性、hReflection、实际 sourceCompletion interior hRegular 精确如冻；结论为整个 ℝ⁴ 的 Borel 可测、实际 KernelBounds4、正 live 区真正 HasDerivAt，无 hGmeas。 |
| Shao.Probability.SourceActualIntervalProfileBudget.intervalDerivative.eq_1 | TYPE1250–1452 | 对所有 Q,p 给完整上述四条件 guard 的定义等式；deriv 自变量是 y 坐标，墙/时间/终点坐标保持不动，假支0。 |
| Shao.C2.ProjectionOvershoot.projectionFactor.eq_1 | TYPE1456–1463 | 对所有 B,u,T,e 给 1-(B+u)*e/T；不引入 T≠0 假设，恰是已接受全实数总化定义。 |
| Shao.C2.CompletedIntervalDerivative.spatialDerivative.eq_1 | TYPE1467–1567 | 对所有真实 BridgeNoise 测度及 a,y,T,z，spatialDerivative 是实际 intervalCompletion 对 u 的导数在 y 的值；没有 image 或概率识别替代。 |
| Shao.Probability.SourceActualIntervalProfileBudget.iid_actual_interval_retained_negative_budget._simp_1 | TYPE1571–1578 | 对任意带 DecidableEq 的 α，a∈insert b s 命题等于 a=b∨a∈s；完整泛型类型与实际 signs 化简一致，无数学预算内容。 |

四个 C2 命名空间等式由本模块消费/展开 imported definitions 时生成，实际 owner 是本模块，故全部计入此次9个 theorem；其定义生产者的已合格证明和 AX 不重播。统计为2个源公开定理、7个生成 theorem、1个显式源 definition、1个 local instance、0个新显式 private helper，共11 owner / 2 values。

## 边界、限制与裁决

T=h 被 cutoff 的严格 `<h` 定义保留；b²=T/2 属于小步；上下墙相等是退出且 overshoot 因 b=p 归零。未来 T-b²=0 的内点可达通过 raw 尾平方和接口证明；全部 Y,S 的 extension 相等也包含0及负 S。n=1 仍在 n>0 的完整 producer 范围内，未暗加 n≥4。raw 总能量0、终点在墙上/外、之前已碰任一墙和 r≥n 的源项均为0；x=0 的 prefix0 严格生存不可能已独立支付。重复标签值、零坐标、原子或离散 rho 没有被剔除。仅要求有限二阶矩、中心化、正二阶矩；没有第三/四阶矩、无原子、支持有界、自然停时、目标 pushforward 或目标 CR 假设。

真实 hReflection、真实 hRegular、真实 all-beta/闭未来端点非 Gaussian hSmall 仍 OPEN。本模块不证明 image series 与实际 killed 概率相等，不支付 time/mixed/PDE/小时间解析，不证明 initial G、原 Ω 上 interval family 或完整 C1/C2 研究根。原文范围和外部已接受 producer 归属保留；不作新颖性或原根闭合主张。

最终：精确新模块的声明忠实、全部新证明完整、实际 owner/types/values/递归 AX 覆盖完整，CORRECT。可以供 root 在核对本次不可变 reviewer RELEASE 后复用作为独立完整资格；合并与进一步 integration gate 仍由 root 执行。

本次证据文件：`drafts/c12-actual-interval-profile-budget-final-review/local-byte-verification.json`、`server-readonly-verification.json`、`consumed-seams-verification.json`，以及同目录 ACK/checkpoint/RELEASE。原 source、原 author receipt/release 与旧资格全部保持原字节。
