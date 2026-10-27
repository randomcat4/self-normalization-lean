STATUS: CORRECT

独立最终审阅者253，实际角色 /root/oq4_row_window_final_review，gpt-6.1-sol / xhigh。数学作者249与实现作者252均与本审阅者分离。本报告认定下列精确源码完整证明了冻结的共同三阶绝对矩界、真实变化行律、小边界比值、闭区间一致误差与真实误差集合上确界三个公开结论。没有发现关键缺口。该认定不替代 lane lead 的资格登记或 Root 的全项目集成；原固定律 OQ4 v79 的既有完成状态不变，不由本报告重复计数。其他项目根组不在本报告结论内；不作新颖性或历史首次声明。

**精确审阅对象与冻结边界。** 最终源码是 `C:/game/shao lean/drafts/oq4/row-window-v1/attempt002/Source.lean`，SHA256 `5b659ffc0235172c64b391e22947552f1e99c31b8559a422d0e9e58adc663285`，22720 字节、444 LF、无 CR、严格 UTF-8 无 BOM。冻结文件 SHA256 `f96d192cf69289c6c0923f4cfc349ca7497b56605166dfd9a1f43f9a8d2cfca9`，178 LF；lead freeze `e24e5f364de4f2e095dd2129b8ecb4e2d2f95ed1fcc228255803bf227dcfd759`；完整值库存 `e73a81ff952bba993ae834aae286efa4679eac7e6c895301831ef84d1940ce43`；D 资格激活 `8b1c8bb6cd40265b1f8949a768a951a8d10899e08085de0b4e2eb9348f42d777`。独立的纯文本重建逐字移除十个定理证明体后，恰好恢复冻结文件全部字节，包含注释、12 个导入、2 个选项、uB 宇宙、可测空间变量前导和唯一透明定义的完整值。没有附加顶层实例、辅助声明、选项、导入或前提。

实际公开定理为 `varying_row_studentized_small_boundary_ratio_tendsto`（源码第197行）、`varying_row_closed_window_eventually`（第297行）和 `varying_row_closed_window_sSup_tendsto`（第408行）。另一个公开常量是透明定义 `actualWindowErrors`（第27行）。完整数学包的 problem、assumptions、十节 proof、完整 proposed-interface 与 provenance 均已阅读；proof SHA256 `c85313fcaca935b7a73a377c9cb21d4a5097513ac62232e2f59979bbd3ccc8da`。数学包全部38项输入绑定和其密封清单逐项核对通过，没有源文件漂移。历史数学包中 D formal pending 的文字是封包时状态；实际实现之前的激活文件明确绑定后来已经合格的 D，未把历史候选状态冒充现状，也未改写历史证据。

**题意、量词和实际概率。** 每行 νSeq j 是真实 ℝ 概率测度，实际行样本为 `Measure.pi (fun _ : Fin (nSeq j) => νSeq j)`。公开假设保留逐行三阶绝对矩可积、均值0、二阶矩1和同一个实数 M 的三阶绝对矩上界。未添加 M>0；已接受的生产者在相同假设下使用。nSeq 只趋于无穷，没有 Monotone 或 StrictMono 假设；行律无需收敛、对称、密度、非格点、四阶矩、指数矩或有界支持。小边界与窗口下端点只最终为正、趋于0，并满足乘以真实实数幂 n^(1/6) 趋于无穷；没有 Antitone 假设。ε 在最终行索引之前选取，同一行索引之后对闭区间的所有 x 同时成立。

分子始终是 literal `closedStrip (x * sqrt (energy v))` 的真实有限乘积测度概率；closedStrip 的完整值是所有 k≤n 的弱前缀不等式，包含 k=0 和 k=n。energy 的完整值是坐标平方和。没有除以随机 Q、条件化掉 Q=0，或用自由概率变量替代事件。Brownian 分母的完整值是同一实际 P 下 `{ω | U B P hB ω ≤ x}` 的真实概率，hB 是给定实际 Brownian 运动证据。ΩB : Type uB 独立于有限实数路径空间，无样本耦合假设。已阅读 U、traceSup、pathSup、probability、prefixSum、Path、energy、closedStrip 所需完整源值与对应已接受的语义接口；U 是现有 Brownian 上确界的可测版本，其几乎处处等价接口保持原样。

旧 `OriginalWindowProduct.windowValues` 的 Ioo(a n)1 与旧有限事件表示已作明确区分。本次唯一新值是以 ν,n,a 为有限参数的实际绝对相对误差在 Icc a 1 上的像集。它不是旧开区间值的改名，也不修改早期行或输入任何窗口结论。公开 sSup 直接作用于该精确集合。

**完整证明审查。** 七个冻结私有证明和三个公开证明已逐体阅读，承重步骤如下。

1. 第37行 `scale_identities` 在 n>0、x>0 后使用正实数底数的 rpow 乘法／加法，严格得到 H=x√n=q n^(1/3)、n/H²=1/x²、n/H³=1/q³，其中 q=x n^(1/6)。`(1 : ℝ)/6` 是实数除法。平方根平方、q³ 和 H³ 的恒等式均正确，所有消去因子已证明非零，没有把 n=0 纳入这些消去。
2. 第73行 `small_boundary_scales` 从 hn 得最终 n≥1，与最终 x>0 相交。n^(1/3)≥1 使 H≥q，因此 H→∞；x 从右趋0给 1/x→∞，平方给 n/H²→∞；q→∞给 q⁻³→0，精确恒等式转移为 n/H³→0。三组尺度全部建立，没有由一个尺度猜测其余尺度。最终相等只改证明，保留所有早期序列值。
3. 第123行事件等式在 n>0 时只消去 √n，适用于每个实数 x。等式两侧壁高完全相同，因此零能量路径和所有弱端点逐点保留。n=0 仅不用于这个等式；最终 hn 支付所需正长度尾部。
4. 第134行私有 K 适配只在证明体内令 ht j=if 0<h j then h j else 1。ht 全部为正且与 h 最终相等；三个尺度沿这个相等转移，应用的是实际共同 M 变化行 K。再按完整 farMainTerm 与 λ 的真实值改写指数，关联乘除而不擅自消去 h。公开声明没有增加全部行正高度假设。attempt002 的两个 congrArg 正确处理二次／三次商的最终相等传递。
5. 第180行实际 firstTerm 比值使用 Brownian epsilon-delta 生产者，在最终0<x<δ上给精确相对误差控制。firstTerm 完整值为 (4/π)exp(-(π²/8)/x²)，严格正。其概率参数与最终分母一致，没有抽象参照分布替换。
6. 第197行小边界公开结论把真实变化行 D 的 R/G→1 与 K 的 G/m→1 相乘。K 的比值最终正而 m 始终正，因而真实 strip 概率 G 最终正后才消去。n>0、x>0 尾部上的事件等式和精确 m=g 恒等式给 p/g→1；再除以实际 F/g→1。最后用 g>0、实际 Brownian F(x)>0 把商代数恢复为 p/F。未将总除法中的早期零分母擅自消去，没有遗漏指数常数或退化能量原子。
7. 第276行 `bad_closed_window_subsequence` 从真实 frequently bad 与最终 a>0 的交集提取 strictly increasing m；每个 m_k 都有实际坏点。再由 [0,1] 紧致性取严格递增 φ，κ=m∘φ 保持严格递增且共尾；所有选取点对每个 k 都保留正性、属于 Icc(a_(κk))1 和误差≥ε。不是只抽取一条本来已被假设收敛的半序列。
8. 第297行否定最终全 x 结论后，确实得到 frequently 存在坏 x 的正确否定量词。κ→∞ 使 n、a 的极限及 hslow 都能重索引；逐行 hprob、h3、hmean、hsecond、hM 全部逐一传递，M 不变。c=0 分支以 x≥a 和 n^(1/6)≥0 支付重索引小边界增长，再调用新小边界定理。c≠0 且 c∈[0,1] 推出 c>0，调用合格的变化行移动正边界 A。c=1 完全包含。两支均使实际相对比值趋1，最终误差<ε与每个选取点的≥ε矛盾，闭区间两端 x=a_j 与 x=1 均未丢失。
9. 第363行有限行 `actualWindowErrors_spec` 在真实有限概率 ν、任意 n（含0）、0<a≤1 下证明四个性质。x=a 给真实非空；measureReal_mono 对全集和乘积概率给0≤p≤1，不需要额外事件可测假设；F(a)>0、F 单调与 F(x)>0 给0≤p(x)/F(x)≤1/F(a)，三角不等式给误差≤1+1/F(a)。因此集合真实有上界；条件完备性给 IsLUB，非空成员非负给 sSup≥0。没有把空集或无界集合的默认 sSup 当作概率上确界。
10. 第408行最终 sSup 结论先从 a→0 与最终 a>0 得0<a≤1尾部，再以 ε/2 应用统一闭窗口结论。每个实际像集成员≤ε/2，所以由非空的 csSup_le 得 sSup≤ε/2，结合已证明非负性，距离0小于ε。早期 a>1（可能空集）、a≤0、n=0 都保留在公开定义中；极限只使用合法最终尾部，没有对公开值作静默截断或有限前缀替换。

**旧生产者证据的精确复用。** A/B/C/D 全部既有资格收据的 source、freeze、leadFreeze、机器收据、独立完整审查报告和收据均按实际格式逐项绑定。A 的旧资格模式本就用 zeroHeavyInflight 字段，没有单独 runtimeRelease 字段；核验使用原有字段，不制造缺失收据。四份独立旧审查状态均为 CORRECT，未再次阅读其完整证明或重跑生产者／单叶 AX。

D source `6fe1d6b705355f2389ccb0f8efd3a26371135d5416d758d186623543b5babbbd` 与资格 `cdffc232dd81f0802cb9a99bb1b3195a167e8f97fd3c8dd7c731f741208f882a`、reviewer251 证据完全匹配。C 资格 `6aeecb404fd52e7f8c522ab32d9264cd30f8ede163438d44929f78642efc61a4` 与原 source e87292...、reviewer248 精确证据复用。A source08a140...、reviewer243、资格66e8f8...；B source17691c...、资格df5bb8...均按原机器／独立收据复用。实际 K、Brownian positivity/monotonicity、firstTerm 源与旧接受链核对。直接消费的全部20项项目接口 TYPE 和8项非定理 FULL VALUE 已完整阅读，并与源含义、调用点假设和真实概率对象对应；没有将固定律极限逐行套用为变化律极限。

88 个实际导入模块的每个源码 SHA256 和每个原对象 stat 均绑定到 `consumed-source-object-bindings.json`（SHA256 `902e0506f70ae86ec0635289e36fd6edbfdb4f3752933ddb075a30ff8141cde6`）。其中79项与 D 已合格映射的 source hash、resolved path、device/inode/size/mtime 完全相同，4项由精确单模块资格绑定，5项由已接受188的原始链绑定。缺省未记录的历史 stat 字段没有捏造；仅核对原链实际记录的字段。独立服务端核验确认88个实际导入对象当前 stat 仍等于成功机器审计时记录；未读取、哈希、复制或下载任何这些旧对象。

**实际所属声明、完整类型与值。** 本次不是按 namespace 预选声明。保存的 native unfiltered environmentDifference、moduleOwnership、stage2 三个全集在分类前完全一致，实际33项：32定理、1定义；公开4项=3公开定理+actualWindowErrors，显式私有7项，生成定理22项。所有声明的模块归属均为本模块。必须保留两个外观属旧 namespace 的新生成定理：`Shao.OQ4.RandomDenominatorFarTail.farMainTerm.eq_1` 与 `Shao.Probability.BrownianSup.firstTerm.eq_1`。其完整 TYPE 是上述已接受透明值的精确展开等式，在本次实际88导入基线中不存在而由本模块生成，来源明确；本模块完整内核检查没有名字冲突。本报告不声称已替代 Root 的全项目导入交互检查，Root 正常聚合需保留它们。

已知全项目集成重叠必须单列：lead 的纯保存文本观察 `drafts/oq4/resumption-20261027/E-generated-name-prior-log-observation.json` 绑定 Root 已接受v123 的 theorem-audit.log SHA256 `658f964c64622edca471873556b1b36bc4af055f8adf63523d9c4773b1e1ff2d`，两条完整 DECL 名称确实均已存在。因此本地33实际所属不等于Root33个全新名称；仅据这两处已知重叠，预期至多31个净新增。该观察提供精确既有名称，不提供旧完整 TYPE／proof value，故本报告不以“都是展开等式”代替全项目同名导入兼容性检查。两项在E的完整TYPE和值来源已明确，本地实际导入基线内完整内核检查成功；在已接受Root全项目中的同名定义兼容仍由正常聚合检查裁定。全部33项本地覆盖保留，不删除或改名这两个生成项，也不改共享原定义、已成功E源码或重跑旧AX。

已完整阅读所有33个实际 TYPE（902 LF）和唯一实际非定理 FULL VALUE（22 LF）。非定理数量从实际环境分类得到，再与冻结库存比较，未预设生成声明只有定理。完整可读投影 `owned-interface.txt` SHA256 `bada6223e754c594216ba65b32960b9cf164bf8e19c5a591bc272277070a59b3`、结构化全部 TYPE/VALUE SHA256 `2126548469f518667a34ab22d4a3c689973bf3e1fc833ed6e5ecac76e6b741b1` 已核对。

阅读采用明确无损方法：`type-value-reading.txt` 只把字面完全相同的完整表达式和9段完全相同的长子串放入字典，所有不同 binder、let、实例、目标上下文均保留；每个表达式经逐字逆替换回转为原始完整 unelided 文本。字典完整原文、所有非重复上下文及全部值均已阅读；不声称对相同重复字节逐次重读。每个新 TYPE／值与旧直接接口的哈希、行数和重复来源在独立 ledger 中逐项列出。最终所有 ledger 条目均标记覆盖完成。该方法不省略语义，不是结构摘要。

**独立保存图核验与原始机器结果。** 复用成熟的保存文本核验器，只适配本 E 的路径、精确 hash 和实际33项库存。于原OQ4锁、CPU48–51下独立读取保存的 audit-native.json 和完整文本依赖图，未启动 Lean、parser、native 公理走查或旧证明检查。核验包括：原 successful Source+audit suffix 恰等于实际检查的 private Combined；内核跳过选项为 false、trustLevel1025、autoImplicit false；owned records 与 native 全量记录逐字一致；全部新完整 TYPE/VALUE 与输出文件相同；直接旧接口集合等于所有 owned TYPE/VALUE 直接引用减 owned 集；每个闭包节点都存在，类型和值引用完整且值在要求的 definition/opaque/theorem 节点可用；不存在 unsafe/partial。

每个33根均分别沿 TYPE 和 VALUE 引用递归，包含所有定理证明值和 opaque 值。递归所得公理集合逐根等于原 native collectAxioms，也等于封包的 per-root 投影，不只比较整个模块并集。所有根可达节点的并集恰为完整65860节点图；其中项目依赖2023项、83个闭包项目模块。每根公理仅属于 `{propext, Classical.choice, Quot.sound}`，完整闭包并集正好为三项。无 sorryAx 或额外 axiom。逐根可达数量和公理结果在独立 saved-graph-verification.json 和 receipt 中完整保留。

实际服务端成功是一次完整新源码 native+所有 actual owned 审计，PID1360004，自然 RC0、reaped、未超时，20.655646728351712秒；固定 Lean4.36.0-rc1、mathlib807d3836b165983210ee2ecf3cd28f239436949c、shared-v34 原环境、-M8192 -j4。审阅者另以小型只读文字核验确认工具链/manifest pin、成功源码／实际 Combined hash、原失败收据／无对象、没有 error 的成功 stdout 和15个保留 warning。attempt001 自然 RC1／无对象作为失败分母保留；只修了两个最终相等 beta-redex 传递，未改任何冻结声明或旧模块。没有以失败中的 sorryAx 当作通过。

首成功对象只继承作者首次唯一 content hash：`69bca6683a3bccf8ada44232461e43c3b1e86e58bbb561b5c44e7c4c570c7839`，716984字节，device64947/inode21761280/mtime_ns1793063044990718671。完整路径由 execution-receipt 绑定。本审阅者只核 stat，不读取、哈希、复制或下载该对象。独立服务端图核验和最终小型元数据核验均确认原对象 stat 稳定。

**封包、运行与释放。** 作者252最终 `author-packet-manifest.json` SHA256 `d2573905a1211db523107be8a1b571c13d047e2415cd5fcd084dc7f8dceac8a9` 的42项载荷和19项compact exports全部逐字哈希核对。最终 checkpoint SHA256 `041730bdd199fb295d42f670e944788ff56bb9c4220abf70d4a1f9899d8227db` 及实际 runtime release `c44532e2ec3f072c3e65d394ad6ad74091aa7a3e669e3b3b7754a3136a6acedc` 均为 writer/heavy/inflight/pendingTool/pendingWrite/pendingExternal/pendingUncertainWrites/children=0；作者已明确释放源码写入权限。保存图检查时实际无 own Lean PID；最终独立元数据检查再次实际无 own Lean，源码和 Combined 未变，原锁成功立即取得且调用结束释放，首对象 stat 稳定。没有待回收或不确定写入请求。检查只在实际检查期间持锁，不干预其他线。

独立检查观察 cgroup memory.current 约166GiB，低于180GiB聚合阈值；本审阅使用CPU48–51，未变更外部任务、缓存、资源分配或其他线进程。本审阅者只写 `drafts/oq4/row-window-final-review-v1/`。一次本地核验器对A旧资格文件假设存在runtimeRelease而产生 KeyError，已按真实历史模式的zeroHeavyInflight修复并保留说明；这不影响源码或机器证据，没有因此重复通过的保存图核验。

最终独立结论为 CORRECT，critical gaps 空。独立源码／完整数学／全部实际 TYPE和值／源到声明语义／完整递归公理证据覆盖已完成。本审阅者释放所有 writer、heavy、inflight、pending、uncertain 与 child 状态为0。实际模型/effort明确记录；输入、缓存输入、输出和推理子集计数分别 unavailable/unknown，不估算订阅百分比。
