# v40 OQ3 正则性／紧倾斜稳定性独立验收

STATUS: CORRECT

critical_gaps: []

本票仅绑定 PR159 与 PR163 的下列 exact heads。完整逐行阅读两份新生产源码、原来源、实际 public/private/generated TYPE 和关键依赖后，未发现关键缺口；不是凭作者既有 CORRECT 或编译成功作数学裁决。根协调已完成的 v40 统一机械门另行绑定，本审查没有运行 Lean、Audit、probe、构建、缓存扫描或重复旧成功门。

## 1. 精确版本、所有权与公开范围

| PR | exact head | 新生产源码／SHA256 | 公开／全部所属 |
| --- | --- | --- | --- |
| 159 | `53694dec89a2834522e48ab36954fc4528cfee06` | `Shao/OQ3/CompactTiltWeakCramer.lean`；`87d4560d0a896d7094e17153b2286408b509b605719977ee443cd688ba8b5544`；94 行／4473B | 1 public THM；1 owned THM；0 DEF/private/generated |
| 163 | `d4a9ffc332fe8247b121dc3298c322c52ac1d26b` | `Shao/OQ3/SourceSmoothMeanMap.lean`；`d376655f6d53c7e7204f375a2dfc4a4fde1e2af43496186d14fc2660434d9681`；237 行／11797B | 1 public THM；21 owned＝5 private DEF＋6 private THM＋1 public THM＋9 generated THM；共16 THM |

通过指定服务器 `tools/server.py` 只读对两个 exact git objects 执行 `git show <head>:<source>` 后计算 SHA256，与本地两份草稿的实际字节相同；`git show --stat` 证实各为六文件一提交。冻结 PR 表与各 `u21a/u20e-pr-verification.json` 的 headRefOid 精确一致。该版本核对不冒充重新查询当前 GitHub 状态；发布时记录均为 OPEN。

唯一写入所有权为本目录 `oq3-regular-review.md` 和 `oq3-regular-review.json`。没有改作者模块、scope、receipt、旧票、根入口、版本锁或其他工作者文件；没有 merge、另建分支、spawn、分线构建或进程／资源变更。外部 CPU0–9／80GiB 工作负载未被操作。原 A/PR161 属另一独立验收，不由本票关闭或重新审定。

## 2. 来源与原目标

直接实读只读来源 `C:/game/shao/current/oq3/proofs/r2/report.md` 全文，尤其38–60的真实 `K/tilt/mean`、§2标准化要求和343–369的有界倾斜稳定性。R2 SHA为 `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55`。另读 R1 137–159 的实际逆倾斜 P 和 `drafts/oq3/root-contract.md` 的定义域、真实均值图、根 B/C 范围。R1 SHA为 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。

PR159 对应 R2(20)同一紧族密度／测度下界、(22)全频平方模缺口和精确正常数 `m²c/2` 的族 WC。R2(21)二样本余弦等式是来源的一条路线；本证明用真实测度分解产生更强的模收缩，足够推出实际(22)，没有把该等式或目标结论改成输入。

PR163 对应同一有界源 P 的实际 log-partition 与倾斜均值的全参数正则性。它填补点态梯度／Hessian不能直接推出邻域光滑性的缺口；不将该源律结果偷换成根 B 的一般无界概率律结果，也未输出均值逆。

## 3. PR159 完整数学及 TYPE 审查

公开名：`Shao.OQ3.exists_compact_tilted_weakCramer_bound`。完整源码17–37及实际29行 TYPE同时保留：一个真实概率 mu、AE `|x|≤M`、`M≥0`、任意紧 K、固定参考 `(u0,v0)`、`c>0` 和参考倾斜律的单点 hWC。没有 caller 族概率、族测度下界、平方缺口或整个族 WC 假设。

单个 m 在全部 `p∈K` 和所有频率之外一次选择，同时满足 `0<m≤1`、`m²c/2>0`，并用于三个输出。频率半径始终为真实欧氏 `sqrt(xi²+eta²)`；没有以 Prod 的 max 范数替换。beta、R在代数传递中任意，应用原标准 WC 时仍须保留原 `beta,c,R>0`，本票不声称非正 beta/R 属原修复条件。

38–59：从已接受 `exists_compact_quadratic_tilted_domination` 取 m0，令 `m=min m0 1`。ofReal单调性产生同一 `m•mu0≤m0•mu0≤mup`。参考及目标的两个真实 `IsProbabilityMeasure` 实例在 proof44/56由有界二次指数真可积生产，非公开 TYPE 中额外的 caller letI。

关键依赖已实读：`TiltedMeasureDomination.lean` 用 AE 指数差界 B，先以真可积／概率给 `Zf,Zg>0`、`Zg≤exp(B)Zf`，再得实际 `exp(-2B)•mu.tilted f≤mu.tilted g`；二次版以 `B=L(M+M²)` 控制。`CompactTiltDomination.lean` 从紧 K 选同一有限 L并给 `m0=exp(-2B)>0`，包括空 K。`CharacteristicMeasureDomination.lean` 把 `m•mu0≤mup` 分解为残余正测度 rho质量 `1-m`，对模1且真可积的 jointPhase 积分，推出 `b≤1-m(1-a)`。`JointNonlattice.lean` 的 jointCharacteristic 确为同 mu 下 `exp(i(xi*x+eta*x²))` 真积分，并有 `0≤a≤1`。

60–76：设 `a=|phi0|`、`b=|phip|`、`A=1-m(1-a)`。`0≤b≤A`保证合法平方 `b²≤A²`。源中的精确代数恒等式

`1-A²-m²(1-a²)=2m(1-m)(1-a)≥0`

给 `m²(1-a²)≤1-b²`，覆盖全部实频率。没有对可为负的上界随意平方，也没有混用 m 与 m0。

77–91：`rho=rpow(sqrt(xi²+eta²),-beta)≥0`，`c*rho≤1-a`。由 `0<m≤1` 有 `m²/2≤m`；与更强的模收缩相乘给 `b≤1-(m²c/2)rho`。`m²c/2>0`已由真实 m、c正性独立生产。相同 beta和R保留；参数／频率／n都未进入常数的选择。

边界核查：K可空、参考点不必在K、M=0及退化law均保留；若参考hWC在某情形不可满足，只是该输入条件无实例，不是额外结论。完整actual owner Audit只有上述一个声明，实际公理恰 `[propext, Classical.choice, Quot.sound]`；无隐藏private或generated。

## 4. PR163 完整数学审查

公开名：`Shao.OQ3.source_log_partition_and_tilted_mean_smooth`。147–167的唯一公开TYPE只有同一权 w的逐项非负和真 `HasSum w 1`。固定 `P=originalMeasure sourceEll w`；Z、K、tilt、mean全部由该同P定义，theta遍历整个 `Fin 2→ℝ`。没有 caller P概率、正Z、可积、手给mean、可微或正则性前提。

实读依赖 `InverseTilt.lean`、`AtomicMeasure.lean` 和所需 `SummableAtoms/FiniteConstraints`：atomicMeasure为同 w的加权Dirac和，质量1由hw/hs得到；所有 fixedAtom统一 `|x|≤4+sqrt10`，逆倾斜指数真可积，故originalMeasure是真概率，并经绝对连续保留同AE界。这是同P的实际有界性，不是关于另一存在律的条件。`sourceEll`为源的 `log(31/30)`；本光滑结论不需要其符号、q或四矩约束，允许退化非负权。

19–35的五private DEF实际值均已读：coordinate为坐标CLM，M_k=真实 `∫x^k exp(theta0*x+theta1*x²)dmu`，momentSlope为 `M_(k+1)pr0+M_(k+2)pr1`，normalizedMoment为 `M_k/M0`，partitionGradient为两归一化矩的投影和。均非额外假设。

37–47：真概率及固定AE紧支撑下，连续函数有界且可积，给所有自然k／所有theta的真实加权矩可积。k=0和 `integral_exp_pos`给 `M0>0`；没有使用不可积积分总化0。

49–95：对每个k和theta构造被积F及真实CLM导数F'。参数theta1求导产生x²，故两个指数为k+1及k+2；不是对样本x求导的2x。F'在 `closedBall(theta,1)×[-B,B]` 联合连续，有限维闭球与固定区间的积紧，产生同一operator norm界C。AE样本之后覆盖整个参数ball的量词正确；C可依赖k／中心，未伪称全参数统一数值界。

已在固定Mathlib实读 `hasFDerivAt_integral_of_dominated_of_fderiv_le`（ParametricIntegral206–212）的全部门：真实参数邻域、邻域F可测、中心F可积、中心F'可测、AE样本后整个邻域共同可积范数主控及真实点态Fréchet导数。源码逐项提供这些门，再用k+1/k+2真可积拆CLM积分，得到实际momentSlope。没有跨模块调用其他源private名字。

97–107：M0严格正后使用真实log链式法则，得到全theta的log-partition导数为归一化矩CLM。109–127：归纳命题为 `∀j, M_j为C^n`，n=0由全点Fréchet导数给连续；n+1时IH同时覆盖j+1及j+2，固定CLM的smul/add给真实导数函数C^n，再用自然n版 `contDiff_succ_iff_hasFDerivAt`。不存在更高j同阶结论的循环假设。

固定Mathlib `ContDiff/Defs.lean`1114的 `contDiff_infty`恰为全部有限自然阶；1171–1173为上述自然n criterion。源码 `open scoped ContDiff`已显式开启；actual TYPE打印是 `ContDiff ℝ (↑⊤)`，即内ENat top嵌入WithTop ENat的C∞。外top的解析ω没有出现，也没有被接受为结论。

129–145：对任意mu/k/theta，`integral_tilted`和 `integral_div`给normalizedMoment等于实际tilt的x^k积分。此helper本身是总化积分恒等式，故无概率前提并非漏洞；最终调用时同P的真加权可积／正M0已独立生产。192–203对全部theta把mean的两个真实坐标绑定M1/M0、M2/M0，再证明整个函数相等。没有只在鞍点匹配值后迁移光滑性。

169–191与204–218：P概率及AE界产生正Z、完整函数 `M0=Z`；正分母下合法使用ContDiff.log/div，再以全函数身份和pi坐标光滑得到literal K和actual mean的C∞。CLM外延展开smulRight后，两坐标顺序与W=(X,X²)相同。

219–234：每theta的exp真可积独立于mean身份得到；`isProbabilityMeasure_tilted`消费该真可积和P非零，真实tilt绝对连续继承同AE界，再给tilt下x、x²真Integrable。虽然源码先构造无条件积分身份、后填公开概率合取，这些分析门并未循环依赖mean光滑。最后把同theta的真实梯度CLM改写到literal K，交付全部theta的 `HasFDerivAt K`。

## 5. PR163 全部21 actual TYPE覆盖

实际证据为服务器 `runs/oq3/u20e-20261021/actual-types.txt` 全80行（SHA `4e80fb2465482828b07bdf24345eb874cff74d5f314b86bed19f1d9f0188afae`）及audit.log全106行。私有名字共同前缀 `_private.Shao.OQ3.SourceSmoothMeanMap.0.Shao.OQ3.`；下表不是按名字猜类型，所有续行均已读。

| owner后缀／公开名 | TYPE行 | 实际内容 |
| --- | --- | --- |
| momentSlope.eq_1 | 1–5 | 全mu/k/theta展开M_(k+1)、M_(k+2)两CLM投影和 |
| normalizedMoment.eq_1 | 6–8 | 全mu/k/theta展开M_k/M0 |
| weightedMoment_hasFDerivAt | 9–12 | 真概率＋AE固定界后的全k/theta真实Fréchet导数 |
| logPartition_hasFDerivAt | 13–17 | 同概率／AE门后的全theta真实log导数 |
| normalizedMoment_tilt | 18–20 | 全mu/k/theta的真实tilted积分恒等式 |
| weightedMoment.eq_1 | 21–23 | 原始加权exp积分定义展开 |
| weightedMoment._proof_1 | 24–25 | `NeZero (1+1)`，Fin2索引数值实例 |
| weighted_integrable | 26–30 | 真概率／AE门后的全k/theta真Integrable |
| momentSlope._proof_1 | 31–32 | `ContinuousAdd ℝ` |
| momentSlope._proof_2 | 33–34 | `SMulCommClass ℝ ℝ ℝ` |
| weightedMoment_contDiff | 35–37 | 真概率／AE门后的全部k真正C∞ |
| Shao.OQ3.source_log_partition_and_tilted_mean_smooth | 38–58 | 同w/P的全部概率、正Z、可积、literal K／actual mean C∞和全theta梯度 |
| normalizedMoment | 59–60 | private DEF类型：mu,k,theta→实数 |
| momentSlope | 61–62 | private DEF类型：mu,k,theta→真实CLM |
| momentSlope._proof_3 | 63–64 | `ContinuousConstSMul ℝ ℝ` |
| partition_pos | 65–67 | 真概率／AE门后的M0严格正 |
| coordinate | 68–69 | private DEF类型：Fin2→坐标CLM |
| coordinate.eq_1 | 70–71 | 任意i展开为ContinuousLinearMap.proj i |
| partitionGradient | 72–73 | private DEF类型：mu/theta→真实CLM |
| weightedMoment | 74–75 | private DEF类型：mu,k,theta→真实加权积分 |
| partitionGradient.eq_1 | 76–80 | 全mu/theta展开两normalized矩投影和 |

五eq_1是五DEF的实际body展开；四结构生成项是闭合的标准实／Fin2结构命题，不包含law、正则性或目标假设。`weightedMoment._proof_1`实际仅用propext，其余20项为标准三公理。owner Audit以 `getModuleIdxFor?`和精确moduleName枚举，不靠namespace前缀；21项均已覆盖，未漏private/自动实例。整个传递公理集合包含于 `propext, Classical.choice, Quot.sound`，无sorryAx或新axiom。

## 6. 历史与既有机器证据

PR163旧v1 scope SHA `439e2740c2968acda75ceb7b980a27554e6d72a498e1268913c78ea00e3300da` 与202行CRITICAL GAPS票 SHA `20484a5393042bacdb8606c839cddda9deb3fce56f6ae9d4fc2beb306546bc47`仍原字节保留，已实际核hash。其历史缺口是冻结header缺显式ContDiff作用域；那次未运行Lean，不能改称观察到编译失败或数学反例。

v2 scope SHA `f2daa316ffcbb81fd564f4bdc51f5e991818af98449bb4b3ca8a83609f3d3c8e`，168行声明终票 SHA `1c0fa34ab1c2bcdbf34c3f85e1b4b42bffa3b85710584cf77a7901596910ac35`。四imports和完整公开TYPE保留，显式header增加ContDiff；当前237行最终实现准确按该v2审查，不把v2通过倒写成v1通过。完整335行旧独立proof票 SHA `56a87199c98b53c92f1c918b9b63aceb1d45f8f168638b04a64600608afff1e1`仅作完成后的对照，非本票数学裁决依据。

PR159首完整build01 exit0，非空712B、2条实例风格warning；首actual-owner Audit exit0、1声明／1THM。receipt SHA `0dd2ebbd4c2273f60b697c61550d5d870910bd08c65c4a4ad17c571d72339aae`。其通用signature标签提probability letI，本票按实际TYPE澄清：公开是caller mu概率和let mu0，两个倾斜letI在proof中。

PR163 v2完整build01为233行失败，实读原日志三个error是hZ整函数匹配及两个Fin2坐标simp匹配；完整build02为当前237行首次exit0、非空5349B、16条style warnings。它增加M0=Z全函数identity并修两处simp，未改公开TYPE或分析前提。首owner Audit exit0、21声明／16THM。receipt SHA `4141009f96510b7fc8e915bf9a7dd8976bd282126d36934a8de9aece87e62cfc`。历史失败保留，没有称partial success或空log。

根协调提供的 `coordination/integration-v40/gate-result.json`已只读绑定：status PASS，严格编译、public manifest、全传递公理、所有所属声明、模块覆盖、diff检查全部exit0。其frozen_sources字典中两新源SHA精确等于本票；实际Mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，固定Lean4.36.0-rc1。全库281模块／1882 public／3190含生成namespace THM／5507 owned；复用277旧源、1054旧对象不变。本票只复用该统一机器门，不声称亲自运行。

本轮只读辅助检索曾因服务器未装rg退出127，随后用只读Python读取固定库；另一次日志读取大小写写成audit.log而PR159实际是Audit.log，已据目录纠正并完整读实际日志。均非Lean门失败，未写任何服务器文件、未重放构建。没有重复旧源／对象／cache／pins检查。

## 7. 最终承重与未闭合范围

PR159真实消除紧有界倾斜族的同m测度下界、全频平方缺口、同beta／同R和正 `m²c/2`统一WC。PR163真实消除同源有界P的全部参数加权矩求导、literal K与actual mean全有限阶连续可微及全theta真实梯度身份。两模块各新增1公开定理，总2；本票无新public定义。

仍OPEN：一般紧族的实际仿射／协方差标准化、统一范数频率比较及调整后的WC常数／半径、一般根C完整适配；根B无界一般律的完整假设图、均值邻域逆、统一谱／标准化矩、Edgeworth外部定理逐条件落实、格胞振荡与求和、曲边界Laplace、远区概率和最终相对误差。仅证明sourceP光滑不能替代这些一般接口。PR163不输出解析ω、实际局部逆或全theta正定协方差；本票不扩张原A/D或随x变化一致性／beta端点／最优性声明。

FINAL STATUS: CORRECT — 两个exact heads及完整源码数学／实际TYPE／关键依赖／来源忠实性通过；critical_gaps为空，统一v40机械门PASS已绑定。原B/C范围未闭合。
