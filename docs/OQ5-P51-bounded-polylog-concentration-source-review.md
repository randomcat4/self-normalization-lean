# unit195 独立完整源文、陈述与证明审阅

STATUS: CRITICAL_GAPS

GAPS:

1. 精确源码第 83 行 D03.hLifted 的 `add_le_add_right hInner c` 实际产生 `c+A≤c+(B+C)`，目标为 `A+c≤(B+C)+c`。二者数学上由加法交换律相等，但当前逐字 proof term 没有执行此交换，服务器报告真实类型不匹配。必须修复这一普通 Prop 证明体，不能把本版当作已完整实现。
2. 第 186–187 行 D05.hR0 的 `simpa only [boundedLogCutoffHeight] using Real.rpow_nonneg ...` 保留了库结论的 Pow 记号，而展开定义的目标为显式 Real.rpow；在实际透明性/简化规则下没有闭合。必须补充准确记号桥或等价的显式类型转换，不能把二者在数学上等值当作现有 simpa 已成功。

JUSTIFICATION: 已对精确源码 `95eea1690b4d10a2794eff9595b3c4f7a85c473a715aee961249a8770e1548f7` 的完整 205 行、唯一数据定义和全部四个证明逐字审阅。五个冻结命题、原文对应及完整数学推导没有缺失前提或数学反例；上述两处为精确实现的真实闭合缺口，故本源码的完整实现判为 INCOMPLETE，数学推导判为 CORRECT。两处都可只修普通 Prop 证明而不改变五个头、唯一 RHS、36 个数据表达式、23 个 Prop 类型及其捕获/作用域。`qualified=false`、`actualOwned=UNKNOWN`；本版首次 native 已明确失败，不存在待确认的成功对象。

本审阅使用 math-theorem，未启用 math-ultra。审阅者为 fresh 角色 `/root/oq56_polylog195_final_review`，独立于作者 `/root/oq56_polylog195_stage1`；没有参与五个声明或证明的实施，没有改动作者、生产者、原文或其他 owner 的任何字节。请求模型为 gpt-6.1-sol、推理强度 xhigh；工具未暴露实际模型/强度内省和四分项 token 用量，分别如实记为 UNKNOWN 与 null。实际运行确认已先写入 RUNTIME-ACK.json。

## 精确对象与审阅边界

目标文件是 `drafts/oq56/unit195/author-01/stage2/BoundedPolylogConcentration.lean`，11553 字节、205 个 LF、UTF-8/BOM0、无 CR；模块 `Shao.OQ5.P51.BoundedPolylogConcentration`，导出 namespace 为 `Shao.OQ5.P51`，没有额外文件名 namespace。实施前父冻结 SHA256 为 `374eb47684b73f8125339925ec2cfdebc4c044c1b044c380e89cc375514088ae`，作者 manifest 为 `f424125f08bd526f572cc5c56d4ce3c7fc3c819c589217c169630a1b9c99c1f1`，作者 RELEASE0 为 `30c14878b5af4119d657b422bf9df6080872b5acaee601ba54e6eaae655bba3d`。声明数为五：一个 def、四个 theorem；这不是 unit195 实际生成所属名称的计数。

已完整读取 p44.md、p51.md、p54.md，而非只读作者摘要。p51 原始 197–204 行的 S16 原字节与绑定 SHA256 `96920f428b8fc09788a6388103cefe398e3ec739129a5922b984babd09e99359` 一致。p44 式(9)解释有限窗口的有界背景矩尺度；193 已承担其概率推导。195 的新数学工作是失败事件并集与 194 窗口的衔接，不能把它再描述成新鬼样本或矩证明。

完整读过父冻结中的五个头、唯一 RHS、12 项时序上下文与两项闭合、36 个直接表达式及其完整类型/初值/捕获/λ 绑定范围、23 个普通 Prop 中间量的完整类型/捕获/作用域，以及两个 eventual 证明回调的完整类型和嵌套模型量词。对作者字节映射的本地复核只用于字节归属与接口对应；数学结论来自下面逐证明推导，未用静态通过替代证明审阅。

## 原统计量和已合格依赖的真实接口

已完整读取并逐项匹配生产者的 15 个真实 TYPE（371 行）与 12 个非定理 FULLVALUE（88 行），同时核对结构化名称 components、levels、constantKind、bodyExpressionPresent 及原已合格递归 AX 白名单。193 主定理 TYPE 的 293 行已完整读取，未只依赖其简写声明。全部选中项与原 actual-owned-metadata.json 的真实条目逐字段相等，非定理 value 也完全相等；未重新审查旧生产者证明或运行旧 Lean/AX。

193 资格证据 SHA256 `67be197dee36351145b6afd54c46f33e74c21ef82cabe811c595cef951e24c27`，来源 `43367b3ce14f174a8c8e3db4152e3db3b553ab0dbc9c4521565a1db8ddac1b14`，原对象 `3b646bdd08cf72556ac49ffd27072cb78a06adbeb0d278cd592e608ff01706bd`。194 资格证据 SHA256 `6bdb7c8adf5f0d30e562b692df92730ece9d5a5d5e0c10fdeb296e56b1aca492`，来源 `1d2ad2ca13be7c987c8e0520c5687dba60669af0db6e0dd01edcbc3105043b7e`，原对象 `68f0e1dd8c2c92ed591b9e22e2c4471aed457b1a80c089133dffad97cbd26ffe`。原 188/190 统计量的 enclosing qualified 记录、实际元数据与对象也逐项绑定。

逐项接口解释如下。

- `tailScale : ℝ → ℝ` 的完整值只通过 M 访问 `squareTailScale`、`scalarTailScale`、`rowTailScale`。其数学值为 max(e(M+1), max(8e(4M+8), 8e²(4M+8)²))，不依赖 R、n、q、Ω、ν、r 或 w。M≥0 时该尺度为正，但新并集推导没有偷偷额外要求尺度正性。
- `squareSum n w x` 的完整值是 ∑ᵢ w(xᵢ)²，指数为自然数 2。
- `sampleLaw n ν` 的完整值是 Fin n 坐标上的乘积测度 `Measure.pi (fun _ => ν)`，域上仅使用给定的 mΩ；原 iid 样本法则已由此编码。
- `originalUpper n r x` 是以索引 i<j 取项的双重有限和；`originalRows n r x` 是 EuclideanSpace ℝ (Fin n) 中逐行 ∑ⱼ if i=j then 0 else r(xᵢ,xⱼ)。范数平方正是原行能量。这里去掉的是同一索引项；i≠j 而 xᵢ=xⱼ 时仍保留 r(o,o)，没有 zeroDiag 或观测互异条件。
- 193 的 `canonical_bounded_product_tails` 接收与 D03 完全相同的 n/实际概率模型和全部资格条件；其结果为五重右结合合取。最后一项真实就是三个严格失败集的 real 测度之和 ≤3 exp(-q)，准确投影 `h193.2.2.2.2`。行能量的单项更强尾界是 exp(-(2*q))，本单元未误把它当成主接口前提或改写其事件。
- 194 的三个真实定义分别为 `C * Real.rpow (Real.log (n:ℝ)) a`、`t0 * Real.rpow (n:ℝ) (1/3:ℝ)`、`Real.rpow (A * Real.log (n:ℝ) / tau) (1/alpha:ℝ)`。两个真实窗口类型都先固定实参数及符号条件，再给 eventual n 上的 `1<n ∧ 2≤q_n ∧ 2R_n²q_n≤n`；没有模型、M 或统计结论作为窗口前提。

原 188 资格引用本地 source path，而消费绑定引用同字节服务器 physical_path；已按准确来源 SHA256+bytes 比较，并保留原对象的完整 fingerprint 相等。它不是数学变化或字节变化。早期 metadata 容器中的 qualified=false 标志属于资格产生前的保存状态；enclosing exact qualified 记录绑定同 source/object/metadata，没有将此叶标志用作 unit195 机器资格。

## D01 与 D02：严格失败集和补集

源码 17–23 行的唯一 RHS 精确为 `(E_Q ∪ E_F) ∪ E_L`：

E_Q={x | CT(M)n<Qw(x)}；E_F={x | CT(M)nq<|F(x)|}；E_L={x | CT(M)n²q<‖rows(x)‖²}。

括号、实数乘法次序、自然数平方和严格关系全部与冻结一致，没有新增事件定义、数据 let、选择器或 representative。

D02 头为 25–31 行，完整证明为 31–33 行（proof SHA256 `ba6158a18318f666c6754a743abc18af227d1cb3957122c5dbe43e5f3c220997`）。展开 D01 和集合成员后，左边是 `¬((A∨B)∨C)`。两次 not_or 得 `(¬A∧¬B)∧¬C`；实数线性序的 not_lt 将每个 `¬(T<S)` 精确改为 `S≤T`；and_assoc 给目标右结合的三个非严格上界。此为完全点态等价，不需要测度、可测性、正性或任何统计资格。n=0/1、任意实 M/q 也合法。每一阈值等号样本都留在好事件，任意等号原子不会被舍弃。

## D03：有限窗口联合失败概率

D03 头为 35–53 行，完整证明为 53–94 行（proof SHA256 `1ed5848fffe45d68f0b428c87d7e905927db517ff6e67fe25409a69346097e4e`）。全部 24 项上下文保持原 193 的资格强度：n、任意 Ω:Type u、其可测空间、实际概率法则 ν、实核与包络、R/M 非负、r 产品可测与可积、左右 a.e. 典范、w a.e. 非负且≤R、w² 可积且积分≤M、ν×ν a.e. 乘积包络、q≥2、逐点对称、2R²q≤n。

实际显式调用次序为 `n ν r w R M q hR0 hM0 hr hr1 hcR hcL hW hWR hSq hSqBound hEnv hq hsym hWindow`；Ω/mΩ/hν 从同一上下文推入。`h193` 的完整真实类型覆盖全部输入，`hSum` 只取最后一项。

完整数学证明链为：第一次原始 `measureReal_union_le` 取 E_Q、E_F，得 μ.real(E_Q∪E_F)≤μ.real(E_Q)+μ.real(E_F)。第二次取 E_Q∪E_F、E_L，得 μ.real((E_Q∪E_F)∪E_L)≤μ.real(E_Q∪E_F)+μ.real(E_L)。在第一式两边右加同一 μ.real(E_L)，即可由 `hOuter.trans hLifted` 得三项和界，再由 `hUnionSum.trans hSum` 得 ≤3 exp(-q)。不过第 83 行当前选用的库 term 实际是左加 c，需要加法交换律转换，未逐字实现目标 hLifted。父候选 `by linarith only [hInner]` 在数学上只使用此线性不等式、消去相同 c，充分且没有添加前提；其实际 Lean 闭合仍须新源检查。唯一 D01 定义透明展开后左端正是目标事件；无需交换并集括号或乘法结构。

已读取原固定 Mathlib `Measure/Real.lean` 137–144 行完整原始声明和证明、该位置之前全部八项时序 scope 原文；raw 签名只有两个集合显式参数，隐含 α、MeasurableSpace α、μ。其证明分别处理 μ(union)=∞ 与有限情形，没有 MeasurableSet 或有限测度前提。195 没有调用补集测度等式，也未为 w、失败事件、Ω 添加可测性/拓扑/完备性。对这里的实际概率乘积法则，所给 `.real` 失败测度上界正是所需“除失败事件外”含义。

n=0/1 等退化域完全沿用 193 的实际条件和已合格结论；195 的并集及实数不等式推导没有新的除法、正样本数或非退化前提，不会把局部窗口包装成所有 n 无条件结论。

## D04：统一的一般多对数 eventual 结论

D04 头为 96–115 行，完整证明为 115–147 行（proof SHA256 `96554a79e4875cf2ba3b19bd85deff992ee662af767c60060831174786e7dbbe`）。外层固定 C,a,t0,M，条件 C≥0、a≥0、t0>0、M≥0 与冻结完全相同。先以 `C a t0 hC ha ht0` 调用真实 194 窗口，再应用 Eventually.mono；回调先绑定 n、窗口证明 hp，模型参数尚未引入。

由 hp.1 的 1<n 作自然数到实数严格序转换得到 1<(n:ℝ)。`le_of_lt` 满足原始 `Real.log_nonneg` 的唯一显式前提 1≤n，因此 log(n)≥0。原始 `Real.rpow_nonneg` 的显式顺序为非负基底证明、实指数 a，给 `(log n)^a≥0`；与 hC 相乘并展开真实 boundedPolylogHeight，得到 R_n≥0。hp.2.1 与 hp.2.2 分别就是 q_n≥2 与有限窗口。

之后才引入任意 Ω、mΩ、ν、hν、r、w 和所有实际资格证明，以 R=boundedPolylogHeight C a n、q=boundedPolylogMomentOrder t0 n，逐项调用 D03。每个参数的类型与实参位置匹配，hM0 保持外层固定输入，hWR 使用同一个 R_n。源码 hWR 的观测名是 o:Ω，所以外层 a:ℝ 仍是真实多对数指数，未发生 shadow 或假设类型变化。

因此所证明量词确为 `fixed parameters/signs; ∀ᶠ n, ∀ actual model and paid eligibility, bound`。窗口先于任何 Ω/ν/r/w，连 M 也不进入 194 窗口；同一 eventual 起点适用于所固定 universe u 内所有模型，允许模型随 n 变化。没有把“每模型各自最终”偷换成统一最终，也没有选择 N 或模型族。C=0、a=0、M=0 全保留；t0=0 被显式排除。小 n 仅由 eventual 窗口排除，未尝试在那里证明 log 正性。

## D05：实际对数截断 eventual 结论

D05 头为 149–169 行，完整证明为 169–202 行（proof SHA256 `d7ae4258f57a523db2c02565db30f81d11467c02337d2f25383d064a85a2272b`）。固定 A,tau,alpha,t0>0 和 M≥0，按 `A tau alpha t0 hA htau halpha ht0` 调用 194 的真实 cutoff 窗口。与 D04 一样先取得 n/hp、后引入所有模型。

hp.1 给 log(n)≥0；`mul_nonneg (le_of_lt hA) hlog0`、再 `div_nonneg ... (le_of_lt htau)` 给真实 cutoff 基底 A log(n)/tau≥0。`Real.rpow_nonneg hBase0 (1/alpha:ℝ)` 在数学上精确产生该基底、该实指数的非负性，展开真实 boundedLogCutoffHeight 后应得 R_n≥0；但当前 simpa only 未把 Pow 记号转为显式 rpow，实际未闭合。补齐这项记号等值后，hp.2.1、hp.2.2 与全部模型资格恰好满足 D03，得到与目标一致的 3 exp(-q_n)。

实指数 1/alpha 和 1/3 与自然数平方严格区分；没有向上取整、额外 α≤2、数据分支或选择。这里 α>0 保证固定高度是多对数，195 只消费 194 的准确窗口，并未改变任意原 DC 核的适用指数。实际截断核的重新典范化、统一 M 和乘积包络仍必须由相应构造支付；D05 把这些作为明确资格前提，没有替它们证明。

## 原始库 scope、局部量与边界攻击

三个新主要库材料的完整 raw 声明和完整时序 scope 共 29 行全部逐字读取，并与三个原固定 fullFile 的原文切片逐项相等。Pow/Real.lean 162–165 行的 rpow_nonneg 原始 x 为隐式实数，hx 和 y 为显式，37 行的 Pow ℝ ℝ instance 已在其 scope 中；Log/Basic.lean 212–214 行的 log_nonneg 只有 hx 显式，x 来自 `variable {x y:ℝ}`。log 文件 55 行 `set_option ... in` 属于其单个命令，不被误认为 195 的新全局透明性设置。三个 raw 声明均无 Ω 的拓扑或其他统计条件。

36 项直接表达式的完整类型、初值、捕获与 λ 范围都与冻结匹配。两个 height/moment sequence 及两个结果/窗口谓词的表达式只通过既有 n 绑定或 eventual 宏形成；不是新 let 函数。D05.rpowAtN 的表达式在透明 cutoff 定义展开和原始 rpow_nonneg 的结论中完整确定，允许复用这一冻结定义。作者 static-map-attempt01 曾错误要求该展开值逐字出现在源码，修正 reader 后源 SHA 未变；此失败仅为静态映射失败，保留且没有当作证明成功或失败。

23 个普通 Prop 中间量（D03 七个、D04 八个、D05 八个）已完整检查类型和全部实际初始化证明；两个回调的 n/hp、后续模型量词和 proof-only 捕获完整。没有数据 let、新 instance、choice、N selector、proof-supporting data choice、递归数据值或数据分支；所有局部中间步骤只产生 Prop 证明。冻结捕获表中“194 pending”的历史描述保留原字节，当前实际调用资格由 exact 194 overlay 补齐，不构成新增前提。

特别检查了阈值等号原子、不同索引的重复观测、核实际对角、a.e. 与逐点条件的区别、M=0/C=0/a=0、n=0/1、自然数与实数指数、统一 n 窗口。所有这些情形都由真实定义及冻结前提原样保留。没有把典范性或包络加强到逐点，没有加入 measurable w、nonatomic、独立的核/包络、额外高阶矩或 Ω 标准 Borel 条件。

## 归属与未覆盖的原目标

195 与 D02 合用，准确给 S16 的三项同时控制以及失败概率 ≤3 exp(-t0 n^(1/3))，且 CT 只依赖统一 M。它没有使用 V、D、真实 centered-row Studentizer 或除以 V 的表达式，没有证明 S17 几何、S15 的实际大余项付款、p54 F4 的严格 1/8 余量、编码 upper 极限或相对正态尾。

p54 已修正 p51 S6 的过强 p 矩变化率：条件标准化 p 矩只要求趋近和统一有界，不要求任意多项式变化速度。原固定法则反例及严格余量付款仍完整保留。SZ Lemma6.1 的 DC 结构与已发表外部归属亦保留；195 没有把它归为新证明。124 统一机制不作为前置。原 C1 immutablev85 完成；C2/C12/OQ56 OPEN，OQ3 仍由用户暂停。未做新颖性或根定理完成声明。

## 首次 native 失败及最小修复判断

父提供的精确 affected-diagnostics.json 已完整读取并核对本地 SHA256 `b85a77a23b76c17b7c7f5902e848aea7c856eee7927801a2db33ca9b8d4d302f`。该诊断绑定同一 `95eea169...` source、原 native receipt `cffd74e020fa3fd98b99c644df61008a40e6c32075fdc54c0d06bb0cf39acf5f`，实际 RC1、4.900466473773122 秒、两 error、13 warning、object=null、ownLean=[]；11812 项保护 fingerprint 前后相等，已结束且未分派下一调用。这里是父提供并由我本地审阅的机器诊断，不是本角色执行了服务器命令。

两项错误确实只是上述两个证明体的表示/组合闭合问题，未揭示冻结命题为假、数据值不一致或额外数学假设。第一处右加相同实数是普通线性推理；第二处原固定 Pow/Real.lean 的 39–40 行为 `@[simp] theorem rpow_eq_pow (x y : ℝ) : rpow x y = x ^ y := rfl`。已完整读取这一 raw 声明以及 194 的 parent-freeze-delta01-primary-rpow-notation.json 中完整 scope/instance，并逐行核对同固定 fullFile；它是 rfl 记号等式，没有额外前提。父在新 195 修复前冻结这一仅记号 primary delta，随后在 hR0 的 simpa only 加入该桥，数学上足够且不改变 cutoff 初值。这里评价的是最小候选修复的数学充分性；修复源字节、受影响的两个完整 proof body、精确 delta 和新机器结果仍须另行审阅。

第 32 行废弃命名警告和 D04 的 12 个 unused binder 警告不构成冻结条件被删去；本审阅没有要求清理它们或改动未受影响证明。

## 证据状态和同审阅者续接条件

本阶段确实只发生本地文件读取、散列/切片/字典接口比较和本审阅目录写入：Lean/AX/server/network/Git/API/uploads/cache/children 均为 0。独立本地绑定记录共有 176 项确定性核对、54 个本地文件绑定、78 个源码字节区间，全部通过；这些计数不代表 Lean 所属声明数，也不替代上面的完整数学审阅。

unit195 先须由同作者在新授权范围完成上述两项修复。正式合格仍待父提供：修复后精确同源 native 成功；同一个首次成功原始 .olean 的全 module-index 所属名称枚举；所有实际 TYPE，全部非定理 FULLVALUE，bodyExpressionPresent、levels、components、递归 AX 与白名单；source/object/receipt 的 SHA256、字节和对象 provenance。必须覆盖实际产生的辅助声明和所有所属非定理，不能只审五个源码头或 theorem 叶。

同一审阅者可在此完整 SOURCE 证据基础上续接两项修复的受影响范围审阅，再审机器资格证据，无需重新完整审读旧 producer proof、未变证明或重放旧 checks。若另有数学陈述/证明变化，只重审实际受影响范围。当前 SOURCE_REVIEW_COMPLETE_WITH_TWO_IMPLEMENTATION_GAPS，qualified=false，actualOwned=UNKNOWN；已记录精确下一依赖并释放本阶段 writer/execution/child 全部权限，没有不明在途请求。
