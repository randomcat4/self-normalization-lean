# SourceActualIntervalInitialCDF 独立完整最终审查

STATUS: CORRECT

本结论只认证冻结的新模块 `Shao.Probability.SourceActualIntervalInitialCDF`：实际原 AE iid 家族的 interval rank0 初值、全点归一化身份、真实可积性，以及同一 Brownian law 的初值 marginal／闭端点 joint 绝对误差。没有发现关键数学、翻译、证明或证据缺口。C12、OQ3、OQ56 原根不因本单元关闭；OQ3 保持用户暂停，OQ4 仅保留另行接受的原范围。

## 独立性与完整阅读

审查者是 `/root/actual_interval_initial_cdf_final_review`，独立于作者 `/root/true_energy_strip_author`，按 Root 指派使用 fresh gpt-6.1-sol / xhigh、math-theorem。未使用 math-ultra、未创建其他代理／聊天、未改生产源或共享实现。唯一写域是本报告目录。原作者证明候选与生产证明是被审查对象，不作为正确性的投票或代替本次推理。

已经完整阅读：新正式源的全部243行（包括唯一公开头和全部证明）；冻结声明全部内容；实际 `all-owned-types.txt` 全808行／60929字节／5个完整TYPE，分四个无遗漏连续片段读取；全部非定理VALUE清单（实际0）；393行完整 consumed interfaces（25个既有完整头、28个必要既有定义值）；183行数学证明候选、51行范围说明、source-mapping；以下原文锚点；实际所有权和自动方程来源；完整新审计程序与成功收据。未抽样、未只看公开声明、未按命名空间丢弃owner。

遥测不可获得，input、cachedInput、output、reasoningSubset 分列为null；未估算订阅百分比。模型／effort 按本次指定配置记录，未把不可得遥测捏造成计数。

## 精确版本与冻结顺序

| 项目 | 核实值 |
|---|---|
| PR | https://github.com/randomcat4/shao-lean/pull/318 |
| 冻结head | `bcb95ef995dba1e161d64f33c82f644f5d3b66db` |
| 冻结tree | `6e59afbeaaddacf1386a18e7b208af067febc5bd` |
| 全源，243行／12929B | `fe46483816c5314c459bc77e313b902d933c96a717bb1dea22e883951594fd29` |
| 冻结声明文件 | `5cf4afbb2e74a4f90b8fe49e4aa32f9a10f3cb9807e6fc265c19f2db3d6db59a` |
| Root冻结说明 | `f67d927cd11117978808cd7ed351d1b6c7005aff693d4b3f7bae5d2b2af08108` |
| 逐字公开头 | `53f7c2722dee75189034d0ea85c02f96426ca38fa3740be0aa0e9c8368ae26eb` |
| activation | `55fdbd8e348d5f7bbf9b9b34b765628b09d1e672a7be9e664f7534d397328e6f` |
| 原作者RELEASE | `a10029818fa6d8e0ca98371295f0c9f3899be0f6937a1266c9af9e5796897cb9` |
| 原作者final-receipt | `46305e759787ccdf02f2bad7418f7895e63d27080f1beb627d2e2347ab5884b5` |

独立脚本从实际源提取 theorem 头，与冻结文件直接逐字比较，含全部10个literal lets，完全相同；也与作者comparison文件相符。只有1个公开theorem；0源码definition、0源码instance、0全局private helper。proof-local haves不被误算成全局声明。实际源为UTF-8无BOM、LF，未归一化／改写已冻字节。

Root activation 的时间为2026-10-24 17:05:02.904737 UTC，明确绑定先行冻结和完整声明／候选读取。服务器 source01 17:11:14、最终source02 17:11:54、原成功object 17:11:59、AX JSON 17:12:04、server-final-receipt 17:13:13，均在activation之后。现存冻结／activation／原对象链满足声明先于正式实现，未以最终证明倒填冻结。

作者RELEASE明确释放目标写权／执行权／生产元数据写权，并声明实际在途0。其24个绑定文件加RELEASE本身共25份，逐一哈希和长度核验通过。本次只读服务器观测（2026-10-24 17:24:17.678805 UTC）看到目标Lean／Lake进程0、worktree干净，head及Git中的源与磁盘源一致；没有复活原writer或执行原check。

## 原文到本声明的范围

只读原文为 `C:/game/shao/current/c12/main.tex` SHA `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06` 与 `supplement.tex` SHA `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`。本次完整读了main870–907、1039–1076、1131–1142，supplement3957–4027、4704–4750。

main870–907规定真实桥生存completion、raw端点、真实剩余平方和、严格墙及Q=0 guard，随后以真实标签排列定义V_r。新声明使用现有 `sourceValue .interval (eventCompletionKernel .interval Q)` 的r=0实际值，对每一个排列逐点识别，既不是任意有界核，也不是有限代数身份冒充路径根定理。

main1039–1076的Lemma cn:initial要求 `g_x(w)=P(sup|G_t+tw|<x)`、V0=1_{Q>0}g_x(W)，以及marginal和 `1_{W≤v}` joint 的CR误差。新头的Q固定为实际 `bridgeLaw B PB`，单位桥 `intervalCompletion Q x 0 1 W` 正是这个g_x；Brownian目标joint字面交同一B的 `B 1≤v`。旧已资格的all-time AE连续桥身份保证原Brownian路径事件与实际连续桥事件吻合；紧区间连续路径取最大值，故全时严格界与sup严格界在相应AE连续路径上等价。原W的阈值原子保留为≤，没有换成开端点或只给weighted marginal。

supplement3957–4027的Q0和全实scalarCDF接口在本单元分别由已资格299、312实际支付，头里没有CDF误差、初值误差、目标概率或CR预算前提。main1131–1142只是本初值的后续消费位置，不被计为本单元已完成。supplement4704–4750中仅“every x>0的absolute interval marginal／terminal-half-line”范围由本结果覆盖；稀有双击j_x的指数／相对预算未覆盖。声明加强至x≥0，零墙分支成立，未改变正墙原范围。

本结果不认证killed density比值的解析表示、image／sine／Poisson、PDE、Taylor、overshoot、mask telescope或最终路径最大值比较装配；没有重证既有CDF／affine／反射生产者，没有新增外部概率定理，没有改源文或其p54等历史修复。

## 唯一公开头：量词和10个literal lets

C在Ω、ΩB、Brownian B/PB、原mu/rho、n、X、x、v、sigma之前存在；证明实际取 `2*Cs+16`，Cs来自312的全局绝对常数。n>0、概率测度、AE可测、iIndepFun、共同raw law、中心化、有限正二阶矩完整保留。未加原空间完备、处处可测、无原子、对称、高阶矩、支撑或任意mask因子化假设。

| literal let | 完整语义审查 |
|---|---|
| population | 原 `samplePath X`，没有换用修改过的可测版本。 |
| rawEnergy | 原所有Xi平方和；不是nσ²。 |
| rawTerminal | 原所有Xi和；不是归一化或截断和。 |
| W | population的原 `normalizedEndpoint`，Q0取0。 |
| sigmaSq | 原rho的真实二阶矩。 |
| scale | `sqrt((n:ℝ)*sigmaSq)`，正方差/n>0下为正。 |
| normalizedLaw | 原rho经z/scale的map，是normalized increment law，不是W的law。 |
| R | 上述law的实际truncationBudget n 0；原R_n(0)。 |
| Q | 同一B/PB的 `bridgeLaw`，没有任意替代bridge measure。 |
| V0 | 每个真实标签排列的原interval sourceValue，恰在rank0。 |

公开实际TYPE已从完整pp.all输出读完，含两个任意宇宙、全部实例参数、所有let的实际值、全点omega身份、forall sigma、两条真实Integrable、两条绝对误差和forall v。它与表面头一致，无隐藏弱化或额外目标前提。

## 全部243行证明覆盖及数学推理

| 新源行 | 完整覆盖、推理与裁决 |
|---|---|
| 1–18 | imports／opens／选项／namespace已读；无逻辑逃逸或新假设。 |
| 19–65 | 完整冻结头及10lets逐字／实际TYPE匹配；上节已逐项审查。 |
| 66–81 | 从312取Cs>0，先选C=2Cs+16；P为rho的Fin n产品律，Q由hB给概率律。sqrt乘法使用n≥0得到scale=sqrt(sigmaSq)*sqrt n。真实F非负给R≥0，故δ=CsR≥0。没有随机对象进入C。 |
| 82–94 | 坐标AE可测给population AE可测。`map_fun_eq_pi_map hX`和每坐标IdentDistrib.map_eq给population_*mu=P，组成与P下id的IdentDistrib。仅对Borel路径集用measure_mem_eq并取toReal，足够传递Q0；未要求原Omega处处可测或完备。 |
| 95–112 | 299对当前原AE家族给mu(rawEnergy=0)≤16R；energy零事件Borel，hTransfer将同一质量转为P(energy=0)。312对原rho/n给所有实v的closedCDF界CsR，精确sqrt相等把其normalizedLaw与本R识别。没有从最大值界倒推CDF，也没有将normalized endpoint law错充increment law。 |
| 113–128 | energy(samplePath)=rawEnergy为定义等式；prefixSum_length给rawTerminal。正能量用旧正分支，非正能量结合energy≥0得到energy=0再用旧零分支；因此原Omega每一点，包括AE异常点，都满足头的原状态身份。 |
| 129–141 | 任意a/sigma的alive分支：rank0仅含k=0，prefixSum_zero给起点0严格在真实墙内，其上界给wall>0。终点Interior由alive给出，remainingEnergy=q、remaining prefix=0，completionExt正墙／起点／终点／q>0各guard成立，展开真实eventCompletionKernel后恰是rawInitial。 |
| 142–163 | dead分支sourceValue=0。q≤0时rawInitial的同一guard直接为0；q>0时，若真实strictInterval有g，则bridgePath_endpoints给终点Interior和起点Interior，k≤0强制k=0，构造sourceAlive反驳dead，因此真实事件为空，Q.real∅=0。这同时覆盖墙等号、外部端点、x=0，不假设桥生存正概率。 |
| 164–169 | 已资格measurable_rawInitial对当前概率Q可用（概率推出SFinite）。hPair与该实际可测函数复合，得到原rawInitial(population)与canonical rawInitial的IdentDistrib；不是任意mask传递。 |
| 170–185 | 在Borel Path上取q=energy、W=normalizedEndpoint，满足旧consumer的q可测、非负及W AE可测。代δ=CsR与hCDF得marginal≤2CsR+P(Q0)。旧rawInitial_eq_normalized逐点识别guarded integrand，再用已付Q0≤16R和实数代数得≤(2Cs+16)R。目标是同一B/PB全时严格生存。 |
| 186–210 | 同一旧joint consumer对每实v给包含同一B1≤v的目标。逐点if交换用split_ifs，两个guard的任意真假都覆盖，再funext作为函数等式改写积分。仅一次支付P(Q0)，所以相同C有效；未丢掉W=v原子，未假设W/q独立。 |
| 211–225 | forall sigma用hInitial组成全点hVeq；既有rawInitial_eq_normalized给第二条全点身份。canonical integrable_rawInitial_and_joint的marginal由IdentDistrib.integrable_iff真实传回；integral_eq精确传回marginal，再用hMarginal。积分总化不充当可积性证明。 |
| 226–241 | F明确为canonical `if normalizedEndpoint≤v then rawInitial else0`，闭阈值集可测和rawInitial可测给F可测。hPair.comp hF正好得到原W mask的同分布。旧joint真实可积性经integrable_iff传回，再用integral_eq及hJoint；所有v均覆盖。 |
| 242–243 | 终止namespace已读；无额外隐藏声明。 |

承重的数学约化因此是：原联合law→canonical全实CDF误差δ和真实Q0成本→两个已接受actual Brownian initial消费者→原实际rank0 integrands及其可积性。这不是把待证目标重命名为未付引理。R在有限二阶矩下具有真实有限积分含义：F(z)=z²min(|z|,1)≤z²、scale>0，normalized law的平方可积；证明所用非负界和上游预算均保持该实际R。

边界专审：n=1保留，n=0由域排除；Q0没有被删除；非正q不作除法推理，q>0才使用旧正尺度接口；x=0时sourceAlive严格起点guard失败且Brownian目标含绝对值<0因而空；任意大x和任意实v使用同一C；终点恰在±wall被strict bridge杀死；W=v被closed mask计入；原重复样本、任意原子和AE异常点不影响全点身份／精确同分布传递。

## 全部实际owner的TYPE／VALUE／AX逐项覆盖

所有权选择来自env.getModuleIdxFor?，不是名字前缀；目标模块实际拥有5个theorem、0definition／opaque／其他非定理。下列TYPE范围指哈希绑定的808行导出，已经全部逐字读完（含BridgeNoise的连续函数子类型、两个端点等于0的约束及可测实例），未截断。

| 实际owner | 完整TYPE范围 | 定义／数学核对与裁决 |
|---|---|---|
| `Shao.Probability.SourcePermutationReveal.eventCompletionKernel.eq_1` | 3–104 | forall任意P:Measure BridgeNoise，无概率前提；upper分支等于p↦upperCompletion P p.1 p.2.1 p.2.2.1 p.2.2.2。与实际旧definition第一分支全值一致。CORRECT。 |
| `Shao.Probability.SourcePermutationReveal.eventCompletionKernel.eq_3` | 108–209 | forall任意P；interval分支等于p↦intervalCompletion P同四坐标。与旧definition第三分支全值一致，正是hInitial展开所需。CORRECT。 |
| `Shao.C2.RawInitialCompletion.rawInitial.eq_1` | 213–312 | forall任意ν、实x、隐式n、路径z；等于if0<energy z then intervalCompletion ν (x√energy z) 0 (energy z) (prefixSum z n) else0。真实q>0 guard及raw墙/端点全部保留。与旧definition完整值一致。CORRECT。 |
| `Shao.Probability.SourcePermutationReveal.eventCompletionKernel.eq_2` | 316–417 | forall任意P；lower分支等于p↦lowerCompletion P同四坐标。与旧definition第二分支全值一致。CORRECT。 |
| `Shao.Probability.SourceActualIntervalInitialCDF.original_iid_actual_interval_initial_cdf_budget` | 421–808 | 完整公开实际TYPE、全部10literal lets及全源证明已覆盖；全点身份／可积性／两Brownian误差均按冻结量词成立。CORRECT。 |

四自动theorem由新证明局部展开旧eventCompletionKernel／rawInitial时惰性生成，虽然名称落在旧命名空间，实际owner仍是本模块。已完整读旧definition实际源：SourcePermutationReveal SHA `eb8ca14665fddaa34b063f3d53a42333db4dcf813c635e4978751b5251287b5a` 的全部eventCompletionKernel分支及相关sourceAlive/sourceValue/completionExt/remainingEnergy值；RawInitialCompletion SHA `cd96e18d97fcb4d146f9ab26f9b4134d9f916dcccf437f11050b2b13ec3e5cae` 的完整rawInitial值。没有重审这些已接受旧文件的完整证明。

`generated-owner-source-map.json` SHA `7c59fc234abb4e6c50176b53f37012770b34aaee6b6fab5915f315acaf4c390b` 与实际名称／类型／上述来源一致。0个非定理值不是省略：VALUE清单SHA `b8133e0ab92847de4ecb637a375aab5f5878135a393881e451dcc983b02160ad` 明确为空，实际env扫描也给0。每一个实际owner的递归公理集均恰为 `propext, Classical.choice, Quot.sound`，没有额外公理；owner index SHA `4a9d50eec6911ebb1bfa3f737b527b429ae8ff754e61a86d2bdf48befc8884c4` 和审计JSON相互精确一致。

## 旧资格的精确复用及接口交互

393行接口摘录SHA `8dfe91cf20a8ca90e6ed34fedbc6d4bc6ee1601ffe6ca34cccd217e03ef677f7` 已完整阅读，并独立逐个确认25个头／28个值都是其hash绑定源的literal子串。24项source-inputs文件均核实原哈希，没有把摘要当完整接口。

312 scalarCDF资格SHA `de65a181861d5ba016636bc1cee91f64df9fd42cf1ce4a32f03ccabe755f9c36`：源 `2731effd3fbb3487bef30090699d675ce387d0258ad5a93800e9ba324330a459`，原producer16对象 `84842cb7b9f3d085891172bd3fa1ba80c5e4ed8e37f2a4b885d3d6ba86af4d28`；299 Q0资格SHA `dea6c4d5d11ba106989978cbf18112d88347b7bfeca6a541eeb1feadb8bb6c8c`：源 `9e4380fc2e70a64b6ff7661f5f34cde9c18c1e5537e24b4165faeb46c74aee45`，原attempt003对象 `2dbf2e7971700bc33e8fbc80c5146c7ad8ef6c9a5ee2da13dc2f7d082f3d90e5`。Root资格绑定的完整独立review、作者／审查者RELEASE、serverBinding、ownerMap哈希均核实；本轮不重读它们的全部旧证明，不重编／重AX。

旧C2实际生产者沿Root PR257资格复用：BrownianBridgeLaw、BridgeEndpointIndependence、InitialBrownianIdentity、EndpointCDFTransfer、InitialCompletionError；沿PR264资格复用CompletionScaling、RawInitialCompletion。每个实际源哈希、独立完整review哈希、作者receipt哈希都与Root资格逐项核实，当前导入object也逐一服务器核实同原哈希。完整名单见local-binding与server-binding；旧审查信用未被新报告替代或重计。

接口交互已另作数学检查：InitialCompletionError要求q处处可测，因此只在canonical Path调用；原Omega仅AE可测通过指定rawInitial及其closed endpoint函数的IdentDistrib传递。Brownian tuple-law的完整头绑定同一个 `(bridgeNoise B, B1)`，产品律是Q×标准高斯；两个actual Brownian概率由同一tuple身份供给。正尺度定理只在q>0用；真正guarded rawInitial同时覆盖q=0；sourceAlive的额外端点／起点guard由真实桥端点证明与raw completion相容。没有任意mask因子化、额外独立性或陈述循环。

## 内核、同次原对象与递归公理收据

唯一成功整源为check02：kernel rc0，原producer02.olean SHA `7df7b8749eb0e46fbd15799247e783ed381a03069ce1c2c2a6b1e90fd1f8284d`，同次导入原成功对象的all-owned audit rc0。check02 JSON SHA `42eafe68e49d1788feee14e43a64d6e4fc53f5bf2070c69ffc06a8d3e26a9338`；kernel日志SHA `49f2c60ebfc0e285fbf0ad6ba59fef19aee77ee97723a260ac056b616babc1bb`；AX JSON SHA `11791cbe098e4c0f0bbb5b77a42c220c3b3e4fdaad53b728cd2ed372462cf9a3`；完整TYPE导出SHA `9846715ec35c30658a15660c10be89578c0455ce34eb4de17d92dde791cb465c`。服务器源、快照、Git源、installed object和原producer均精确相等。

已完整审查 `owned-audit02.lean`：它遍历env全部constants，按实际module owner选择，遍历每个owner递归collectAxioms并拒绝非白名单项；打印每个完整TYPE（pp.all/deepTerms/proofs和充足maxSteps），对每个非theorem打印完整VALUE或报错；要求唯一指定公开theorem存在，统计所有owner，不按namespace过滤。完整脚本SHA `c68c41fee1b18cc784682ca77df3d376189a7e2251c16ba5a06adc8b56934901`。额外只读核验将原audit日志5个完整TYPE重新抽取，与已读all-owned-types逐字一致，且无省略／截断标记。

钉死工具链 `leanprover/lean4:v4.36.0-rc1`；实际mathlib HEAD和lake manifest rev均为 `807d3836b165983210ee2ecf3cd28f239436949c`。成功日志只有旧if_pos/if_neg弃用、unused binder及已知mathlib工作树脏状态的warning，没有错误；其实际commit、旧合格object和本成功object均已绑定，未因warning改动已接受源或重跑成功检查。

check01是不同源SHA `45091f86baca9a765fc0829ff2b733d5c00a1ed6b4fbf21d778870bd00eb3b6c` 的rc1；原失败source/log/rc/receipt/audit脚本仍在服务器，五份哈希和长度均核实。最终check02对joint integrand用funext后的函数等式rw，数学内容与冻结头不变。失败证据没有清除，也没有以失败check作为成功证据。

本次新Lean命令0、新AX命令0、旧producer重编0、成功check重播0；服务器只读两次元数据/哈希观测。原成功机械证据按精确源复用，可在本完整语义与证明审查后用于该叶模块的LEAN_FULLY_CHECKED认证；不是全项目／原研究根完成声明。

## 交付和剩余范围

完整逐项结果、所有精确绑定、5个actual TYPE／0个VALUE／5套递归AX及独立性覆盖保存在同目录 `full-review.json`；`local-binding.json` 保存83个独立本地哈希绑定和53项literal接口核对；`server-binding.json` 保存29项远端源／对象／收据绑定与零目标执行观测；`server-metadata.json` 保存钉死版本、冻结前后时间和原audit TYPE完整性核验。没有未付的新数学上游；本模块可交Root做精确范围验收／集成。后续仍是其他owner的实际killed interval解析识别、Taylor／telescope及最终装配。审查写权与实际执行零在途的明确释放见同目录RELEASE，报告发布后不再修改绑定文件。
