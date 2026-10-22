# PR166 / U21b — root 新鲜独立完整验收

STATUS: CORRECT

裁决范围为冻结提交 `b3362fcb26bda08f5027ef3118ad6c759f0f5138` 的 `Shao/OQ3/AffineWeakCramer.lean` 全部152行、两个公开定理、一个私有定理、全部三个实际所属常量的完整类型及传递公理，并核验既有服务器机械证据。没有发现关键证明缺口或冻结签名漂移。本票不把仿射频率输入误认为已经生产了实际协方差白化，也不关闭原 OQ3 B/C/D。

本实例没有参与作者实现，未运行 Lean、Audit、构建或 smoke，未重复未改变的成功检查；只读原文、冻结源、作者历史及服务器原始证据。没有修改作者文件、源文件、分支、缓存或 pins；只写本报告及同名 JSON。root 之后仍须单独完成整合入口、统一编译、公理与公开覆盖门。

## 1. 冻结对象与版本绑定

- PR：[166](https://github.com/randomcat4/shao-lean/pull/166)。共享 broker 上经认证 GitHub API 独立只读核到：OPEN、base `main`、1提交、6文件、head 精确为上述冻结值。
- 实际 `git show`：parent `59a531b89eff7c11e4fc53583067f2cd3b53a517`；tree `d4a2705431957ca64cf0a6a58f3b7dd4765c97d5`。
- 唯一新增生产源：`Shao/OQ3/AffineWeakCramer.lean`，152行／7064字节，SHA256 `29457076f283c08b093949d3c12cfb020ea0bb496e51573ad74554114e94031f`。本地完整已读源、冻结 Git blob 和服务器 `source-02.lean` 三端一致。
- 另五文件精确为 `docs/oq3-u21b/{Audit.lean,author-receipt.json,proof-review.md,scope.md,statement-review.md}`，没有其他生产源改动。
- 按 `drafts/oq3/u21b-pr-handoff.json` 定向读取完整 scope71行、声明审查190行、证明审查220行、源152行、actual TYPE44行、Audit45行、receipt168行及历史记录。旧审查最前的 IN_PROGRESS 是保留的盲审历史前缀，终票是 CORRECT；没有以标题或终票标签代替本次逐义核查。

| 冻结／证据对象 | SHA256 |
|---|---|
| scope.md | `57f5eaf02d4c5b36aded5bff04b33ea57cd85d36dc4b671baac619cfebee101e` |
| statement-review.md | `438875ec0b679168bae3761b76bebee8b2b12cb77e9a207090d9f125559539f4` |
| proof-review.md | `f554f4331bedd26dc516ca724464c971934ed88f52d0cdc249aed08039161ce5` |
| author-receipt.json / receipt.json | `87de03a6e6b99ed859d27d477f82e77fdcc4606482823a05f45053540ca06c2a` |
| actual-types.txt | `789a5fdadeb50018647116edb6d0b00b66340cd80ea0f09f46684214483a624d` |
| Audit.lean | `eb5bc1e56cf9e48989ae351eb385a230e9478053a5fb625d69ca0ed2bbeb65cd` |
| audit.log | `1605c616e189b0895c48f300c5c0591dfc25b0a52c10852aa805058e22839f69` |
| audit-receipt.json | `1dedec18ec65bf3488d4de2f7b448ddbfe86a081605811e7711988b84124719b` |
| build-history.json | `1056de7986908c2c7a0e18ee0723712743a9a61c6824d3ccdad4608d7115b581` |

本地新产物哈希、冻结 Git blob 原始字节哈希、服务器 run 原始字节哈希逐项吻合；原始长日志留在服务器，不下载日志归档。

## 2. 原文 → 冻结声明 → 实际类型

完整读了只读原文 `C:/game/shao/current/oq3/proofs/r2/report.md`（523行／20102字节，SHA256 `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55`）、`repair01.md`（SHA256 `9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd`）及 root-contract 的相关完整接口。

R2 §1 的 W=(X,X²)、真实倾斜 Pθ、实际 Δ(θ) 与谱界(2)，以及 §2 的 Yθ=Δ(θ)^(-1/2)(W−m(θ))，把本节点需要消除的义务明确限定为：真实仿射推送的特征相位、转置频率、同指数与统一常数。§5(20)–(22)先生产未标准化族的 WC，再说协方差标准化按(2)改变常数。repair01 §1 仍要求真实单位协方差族、统一矩与统一 WC；它没有豁免实际白化对象或谱门。其 Song/Edgeworth、胞和、Laplace、far-field 部分均不由本模块证明。

逐白空归一化比较两个完整公开 source TYPE 与 scope 的完整 Lean fence，均相等；四个 imports 和 namespace/open/scoped/noncomputable 环境不变。实际 owner TYPE 的44行全读，包含 universe、全部续行、全部 caller 前提及五个依赖 let，没有省略可能改变语义的量词。

第一公开定理 `Shao.OQ3.affine_parabola_characteristic_factor` 对任意实测度 μ、任意实2×2矩阵 A、任意 b∈ℝ²和任意实频率 u=(ξ,η)，固定

`Y(x)=A((x,x²)−b)`，`ν=μ.map Y`，`uA=Aᵀu=(ξA00+ηA10, ξA01+ηA11)`，

并固定 φ 为 ν 上的真实复特征积分。输出完整复等式

`φ=exp(−i (uA·b)) ψμ(uA)`，以及 `‖φ‖=‖ψμ(uA)‖`。

没有 μ 概率／有限性／矩可积、A 可逆／对称、b 是均值等隐藏前提。

第二公开定理 `Shao.OQ3.uniform_weakCramer_of_affine_frequency_bounds` 对任意类型索引及集合 K，显式输入 K 内 μp 真概率、共同 L/U/c>0、β≥0、R≥0、全部频率的欧氏双界 `Lρ≤ρ(Apᵀu)≤Uρ`，以及同一原律的原始 WC。输出的 `Yp`、`νp`、`Φp` 全部由同一个 μp/Ap/bp 的 lets 固定，精确常数为

`cA=c U^(−β)>0`，`RA=R/L≥0`，

以及每个 p∈K 的真实 νp 概率性和全部 `ρ>RA` 上的 WC。cA、RA 和 β 固定在所有 p/频率之外，无 n 依赖。hWC 没有预先假设 Φp 的目标界；hfreq 没有隐藏在结论中被冒充为已生产对象。

## 3. 完整源码证明核查

源码13–22的唯一私有 theorem 先对 `Fin 2 → ℝ` 使用逐坐标连续性；`Matrix.mulVec` 按第 i 行的有限 dotProduct 展开，`Fin.sum_univ_two` 化为两个实多项式。故得到全部二维 Y 连续，适用于任意 A/b；没有用错误的单坐标替代向量或借用未证明的矩阵可逆性。

源码24–69的第一公开证明给 Y 连续可测和复相位 f 连续／AE强可测，再用真实 `MeasureTheory.integral_map`。独立只读固定 Mathlib 的 Bochner/Basic.lean1065–1086，核到该 API 只要求 AEMeasurable Y 和 AEStronglyMeasurable f；下层证明对不可积分支用 integrable_map_measure 与 integral_undef 同步两侧，没有有限测度或概率输入。因此任意无限 μ 时该定理是合法的总化 Bochner 积分恒等式；它没有额外宣称相位真可积。

源码51–57逐点展开两行矩阵乘法，得到

`ξY0+ηY1=ξA x+ηA x²−(ξA b0+ηA b1)`。

此处转置方向和负常数相位精确，非对称 A 下也成立。随后 Complex.exp_add 作用于逐点复指数，未对未证明可积的函数滥用 integral_add。固定 Bochner/Basic.lean288–290 的 integral_const_mul 对任意复函数无额外可积门；提出常数后 rfl 回到实际 JointNonlattice.lean 的 jointPhase/jointCharacteristic 定义。单位实相位的复指数模为1，所以完整复等式再给模等式；没有除以可能为零的特征积分。

源码71–118的第二公开证明在固定 p∈K 后才引入 hprob p hp；同一实际 Yp 连续可测，并以这个 AEMeasurable 证据调用 `Measure.isProbabilityMeasure_map_iff`。固定 Probability.lean139–141确实接收该门。库的 map 概率 instance 本身存在不可测兜底分支，但此证明已经排除这种分支解释，故 νp 是真正可测推送。其模1连续相位在真概率 νp 下也真正可积；不靠第一定理的不可积总化来伪造概率特征对象。

源码119–148设 `r=√(ξ²+η²)`、`rA=√(ξA²+ηA²)`，全程使用字面欧氏半径，未误用 Fin2 函数空间默认 max 范数。由 R≥0、L>0 得 RA≥0；`RA<r` 给 r>0，正 L 跨乘给 `R<Lr≤rA`，因此 `rA>R≥0`。原律 hWC 在变换频率上的严格外区条件得到完整满足。

上界 `rA≤Ur` 配合 `−β≤0`，按实际 Pow/Real.lean565–569 的 rpow_le_rpow_of_nonpos，在已证 rA>0 时给

`(Ur)^(−β)≤rA^(−β)`。

Pow/Real.lean476–483的 mul_rpow 需要两底数非负，本证明已有 U>0、r>0。由此

`cA r^(−β)=c (Ur)^(−β)≤c rA^(−β)`，

故 `1−c rA^(−β)≤1−cA r^(−β)`。结合第一定理对同一 μp/Ap/bp 的模身份与 hWC，精确得到目标。L用于阈值 R/L，U用于系数 cU^(−β)，负幂和减法不等式没有反向。

K可空时标量结论仍于 intro p 前证明；β=0保留等号边界，cA=c；R=0仍只对严格正频率取负幂。bp任意且不影响常数；p不被积分，因此没有索引可测性／拓扑／联合可测性门。第一定理覆盖零／奇异／非对称 A及零频率；第二定理非空K时的正L全频率下界本身排除频率坍缩。没有暗增 β>0、R>0或K非空。

## 4. 实际所属、公理与既有机械记录

完整读了服务器50行 audit.log 的全部 DECL/TYPE/AXIOMS 与 footer，并与本地44行 TYPE选块及完整源码核对。Audit 以 `env.getModuleIdxFor?` 和 `env.header.moduleNames` 精确匹配模块所属，不靠名字前缀；遍历全部所属常量并对每项用 Lean.collectAxioms，拒绝新 axiom 和白名单外传递公理。

| 全部实际所属常量 | 分类 | 传递公理 |
|---|---|---|
| `Shao.OQ3.affine_parabola_characteristic_factor` | public theorem | propext, Classical.choice, Quot.sound |
| `Shao.OQ3.uniform_weakCramer_of_affine_frequency_bounds` | public theorem | propext, Classical.choice, Quot.sound |
| `_private.Shao.OQ3.AffineWeakCramer.0.Shao.OQ3.affine_parabola_continuous` | private theorem | propext, Classical.choice, Quot.sound |

实际总数3owned／3THM=2public+1private，0定义、0生成定理。全部三项完整实际 TYPE 与对应源命题一致。冻结生产源全文的独立扫描没有 sorry/admit/axiom/unsafe/native_decide/implemented_by/set_option；Audit 的 pp.deepTerms和pp.maxSteps只控制打印，没有放宽证明。没有隐藏结论假设或自由替代分布。

| 完整检查历史 | 退出码／耗时 | 原始日志哈希 |
|---|---|---|
| complete01，源SHA `3560ac9a6c8328ca820598d12f069a0e59231beaf304dcd9cfbe622e8150c0a4`，147行／6938B | 1／4.568715s | `a6cd1baf0a2360fab88d296bcab6456f18e281db07ad4f91c18058cfdaf4bce1` |
| complete02，当前冻结全源152行／7064B，首次完整严格成功 | 0／4.342666s | `bddb54e999a437adc9529359b169faa1c4c76ebefb1cfed82f19734330a66b8b` |
| 首次 actual module-owner Audit | 0／5.045017s | `1605c616e189b0895c48f300c5c0591dfc25b0a52c10852aa805058e22839f69` |

实际读取两份完整日志并对两个完整 source 快照作只读 diff：01只在 mul_rpow 的隐含实指数 rewrite 匹配及未关闭匿名section报错；02只把该公式写成显式 typed hm 并补 end，所有公开TYPE/imports/前提不变。保留01失败原字节；02日志352字节、8行，仍有源码114行的一条 `letI` 样式warning，无error。不能报零warning或空日志。首Audit footer是0 frozen DEF／2 frozen THM／3 all THM／3 all DECL／PASS。

既有命令使用服务器CPU14–17、Lean4.36.0-rc1、Mathlib807d3836b165983210ee2ecf3cd28f239436949c、native8192MiB/j4/autoImplicit=false。本实例只读查询限制在CPU10–13，没有启动Lean/重跑成功source或Audit，也没有触及受保护CPU0–9/80GiB工作负载。这里复用的是哈希绑定的既有模块机械通过，未声称本实例新做了整库机械认证。

## 5. v39父版本在v41整合环境中的兼容性

从冻结Git源码导入头独立做小型 Shao-only DFS，实际链精确为：AffineWeakCramer→JointNonlattice→AtomProjection→SummableAtoms→SourceStarter→FiniteConstraints。除新模块外只有这五个已接受项目依赖。

在共享Git对象库只读比较 parent59a531 与 root提供的v41 accepted `ece32b1691a5d24a1f8114f6e6a32cbcb0613529`：这五个实际依赖的 path-limited diff 为空；lean-toolchain/lake-manifest/lakefile元数据diff也为空。没有重扫全Mathlib图、重新哈希所有旧源／旧对象或重复smoke。当前root main为 `35f4d3216bb608f5b9e7462810665ff50976cadb`，其v41收据已正式接受；此PR从v39已接受父版本新建的事实没有改变其实际依赖语义，不构成要求作者迁移、重写历史或打断后继工作的理由。

## 6. 已消除义务与仍未支付义务

本节点实际完成 R2 §2／§5 的仿射一步：同一样本统计量和真实像律、完整负平移相位、Aᵀ频率、同β与共同精确 `cA=cU^(−β)`／`RA=R/L`，并输出像律真概率。直接消费者为已验收PR159紧倾斜族未标准化WC之后的实际协方差标准化；本模块自身不引入PR159叶依赖，也不声称已完成消费者装配。

以下仍是明确未付义务，不是本票发现的冻结证明缺口：

1. 将Ap绑定实际倾斜律的协方差逆平方根或证明等价的实际白化；将bp绑定所需实际均值。
2. 从实际covariance谱界(2)生产共同L/U及频率双界；本源的hfreq仍是caller输入。
3. 生产真实标准化族均值0、covariance I、统一自然阶／8+δ矩，以及紧倾斜族实际谱生产者；U21c是后继工作，不纳入PR166接受范围。
4. hWC仍是同一原始μp的输入，完整C须与已接受真实紧倾斜producer相连；不推出一般无界倾斜自动稳定。
5. 根B的均值逆／完整Fourier与Edgeworth接口、曲边界胞估计和求和、Laplace、真实远域概率及最终误差组装；根D的完整严格性见证亦未由本节点闭合。

原A已于v40 CLOSED；本scope冻结时A OPEN的旧文字保留为历史，不倒改，也不覆盖当前状态。原B/C/D仍OPEN。本票没有新颖性、β=2/5端点、最优常数或随x变化一致性的认证。

最终裁决：CORRECT；critical_gaps=[]。可将精确冻结PR166交root组装门。作者首失败、完整类型、公理记录、原收据与源哈希保持原样。完成后STOP。
