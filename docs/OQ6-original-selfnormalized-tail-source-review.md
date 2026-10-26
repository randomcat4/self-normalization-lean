# Unit202 独立完整 SOURCE 与证明审阅

STATUS: SOURCE_CORRECT

QUALIFIED: false

ACTUAL_OWNED: UNKNOWN

本结论仅针对精确源码 `OriginalSelfNormalizedTail.lean`，SHA256 `cfa791fd240ee560b2a876ea69a64e46c7c84735c935e1380446025e69a9e61a`，3989B、79LF。已独立完整读取原始 p51、完整声明冻结、规范数据合同、实际源码及证明，并核对所有消费到的完整 actual TYPE 和非定理 FULLVALUE。未发现关键数学缺口。该源码还没有在本审阅上下文收到 unit202 的首成功内核、首原始对象或全 owned 审计证据，因此本报告不声称 Lean elaboration、kernel、实际 owned 数量或机械资格通过。

审阅人与作者分离；只写 `drafts/oq56/unit202/final-review-01/`。没有修改源码、旧报告、冻结、作者封存、共享库或受保护来源。服务器、Lean、AX、上传、Git、API、child 调用全部为0。配置指定 gpt-6.1-sol/xhigh；实际模型、实际推理档位及 input/cachedInput/output/reasoningSubset 四类用量均不可独立观测，记录为 null。

## 1. 审阅对象与字节绑定

父冻结 `parent-freeze-v1.json` 的 SHA256 为 `408d765c4a63ba137d452b8d83aba26c4044d9b59297000d43a2a496b38b9324`。规范合同 `parent-frozen-data-contract-v1.json` 的 SHA256 为 `59a694f4deba587f3f8dca7e42a522d13149db2bc97c2b89cab0bfb0e33a91bf`。唯一完整 theorem head 为687B，SHA256 `2e0d3d2e7cb0d5323198e82c8d26d824f842f80fb5943a288a794e8acde34f15`。我从实际源码重新提取整个头并逐字比对，而非接受作者的布尔自检字段。

五项 imports、命名空间、`autoImplicit false`、单个 theorem、六个别名初始化、唯一局部概率实例及十四个局部 Prop 头全部与事前冻结吻合。源码没有额外全局 definition、instance 或 theorem；没有 sorry、admit、新 axiom、unsafe 或 native_decide。源码为 UTF-8、无 BOM、仅 LF，并有末尾 LF。作者封存的9个 payload、manifest 及 RELEASE0 已独立散列核对；释放状态所有字段均为0。作者实际 RELEASE0 hash 是 `de26fe681ca561c05edec2a78396370ec6d895cad3893757487688b49cb26a30`。

`BINDING-VALIDATION.json` 记录本地确定性核对的207项 PASS 及完整112项文件绑定记录。其作用是绑定和定位，不能替代本报告的数学判断，也不是一次 Lean 检查。第一次校验的两个失败判断和一次缺失本地 lean-toolchain 的只读查找保存在 `FAILURES.json` 与 `BINDING-VALIDATION-first-01.json`；没有删除或改写旧来源。

## 2. 原始来源到冻结陈述

已完整读只读 `C:/game/shao/current/oq56/inputs02/p51.md`，实际 SHA256 `96920f428b8fc09788a6388103cefe398e3ec739129a5922b984babd09e99359`。p51 S1 定义 W=n^(-1/2)Σg_i、V²=n^(-1)Σg_i²；S10 的好事件包含 |W|≤√y n^(1/4)(4+V)，S11 为其失败概率中的大投影部分支付4exp(-y√n/2)。

unit202 的声明精确证明原样本分量：任意 n∈ℕ、任意可测空间 Ω、概率法则 μ、可测 g∈L²(μ)、∫g=0、∫g²=1、任意实 t≥1，有限 iid 样本法则 M 下严格事件

    t(√(Σ_i g(x_i)²)+4√n) < |Σ_i g(x_i)|

的实质量至多4exp(-t²/2)。sampleLaw 的实际 RHS 是 `Measure.pi` 的常值 μ 家族，故它确为 iid 样本法则；sampleSum、sampleEnergy 的实际 RHS 分别是上述有限和与平方和，没有另一种 Studentizer、删一系数或隐含中心化。

当 n>0 且取 V≥0 时，上述事件除以√n后正是 |W|>t(V+4)。之后选 t=√y n^(1/4) 才会得到 S11 所需指数；在 p51 的 n≥4、y≥1 范围，此 t≥1。该参数特化、平方根与 W/V 代数等价、低能量付款和 G_y 并事件尚未在 unit202 声明或证明中实现。我没有把这个完整原样本分量扩称为完整 S11 或根目标完成。

该分量本身不需要 p51 其余余项核 r、标准 Borel、n≥4 或更高矩条件，所以冻结声明保留任意可测 Ω、所有 n，具有合理且经过消费接口核对的更大适用范围。可测 g 使实际事件由有限和、平方、sqrt 和绝对值组成，语义上是可测事件；代码的质量桥使用任意集合 API，因此无须额外添加 A 可测的局部命题。

外部归因保留为 p51 所注明的 Shao–Zhou (2016)(92) 上尾路线及 Jing–Shao–Wang (2003) Lemma6.4 背景。本审阅未重新读取 JSW 全文，不据此声称其全文已核对或提出新颖性结论。p54 修复和124非前置保留；原 C1 immutablev85 complete、C2/C12/OQ56及S11 OPEN、OQ3 PAUSED_BY_USER 的范围不变。

## 3. 所消费旧资格和完整接口

依照精确证据复用规则，没有重新审旧完整 proof 或重放其 kernel/leaf AX。独立读取并比对6个 current qualified-evidence、各自 source/O/metadata 和相关独立资格文件的精确本地散列；读取所有14个消费 actual TYPE 和全部9个消费 definition FULLVALUE，并直接与原 metadata 同名记录逐字比较。六个来源与原对象在 qualification、metadata 和消费包三方一致，所有消费条目的递归 AX 都在 propext、Classical.choice、Quot.sound 内。

| 单元 | 本单元消费的实际内容 | 作用 |
|---|---|---|
|188|sampleLaw TYPE/FULLVALUE、pairSamples TYPE/FULLVALUE、pairSamples_measurePreserving 完整 TYPE|iid 原法则、坐标配对映射、M×M到P的保测性|
|199|pairedDifference、pairedTailEvent TYPE/FULLVALUE；measurableSet_pairedTailEvent、paired_selfnormalized_tail 完整 TYPE|配对严格尾事件可测及2exp界|
|200|sampleSum、sampleEnergy、goodEvent TYPE/FULLVALUE；original_ghost_good_event 完整 TYPE|鬼样本弱约束及B实质量≥1/2|
|201|ghost_good_vector_tail_comparison 完整 TYPE|所有实向量、所有n、t≥1的逐点严格比较|
|187|pairedLaw TYPE/FULLVALUE|常值 μ.prod μ 的有限坐标乘积法则数据闭包|
|198|scalarEnergy TYPE/FULLVALUE|有限实向量平方和数据闭包|

188/199/200/201 的 source hash 分别为 `0b7f38c8840ffefb15fc9185c8f54c2c6907da96cc49bd5e7ee3c5ed512250fc`、`23d5e22f5bd8669f8e7d41afec78cf1b5bcf8150052ec666fc2bfbac507a7d8b`、`fc4127fadfab83ff08605b50b0cfa0525084201b7a5b78293d42d9826d82e83a`、`45119bf03fae2df0fac15f380b6283b131dafd6cb00646de55e30c0bf4e5ed35`。对应原始 O hash 分别为 `039bdc5ca03a7505762d852b8e6464c7f88de90c5b68914e6aaf6e6cb3a50d85`、`da3d2658aabde869760cf289534d016fe65529a3e5ad43293e22a5e11aac92e2`、`399266357b6bb5c62696d2b2c0f45284f4ac415f477115066592e18f49926541`、`07f7f83e68a4bbc1976521fe7e0a7d7cc3be651848742e38a1d94be70352fd7b`。187/198的完整绑定和所有消费 TYPE/value hash 载于本次 BINDING-VALIDATION。这里记录的是旧已接受精确证据复用，没有新的服务器现状观测。

## 4. 主源完整前缀和两处纠正

以钉死 Lean `leanprover/lean4:v4.36.0-rc1`、mathlib `807d3836b165983210ee2ecf3cd28f239436949c` 为上下文，完整读保存的 Real、Prod、Pi、Probability、MeasurePreserving 相关 chronological prefix。已将它们与原完整主源包的实际字符串和 source hash 对照，而非从 locator、短摘录或某次使用猜测 section variable。

`measureReal_prod_prod` 位于 MeasureTheory.Measure 内但用 root namespace 导出，其真实持续条件是右侧 `[SFinite ν]`；没有 A 或 B 可测条件，也没有沿用已关闭 section 的额外条件。这里 μ=ν=M；概率实例给有限性，继承的标准有限/SFinite支持使右侧条件成立。Prod 的有限乘积实例自行重新绑定两个可测空间与两个有限测度；它不要求额外保留外层参数或新的概率假设。

`MeasurePreserving` 的真实字段是 `Measurable F` 和 `Measure.map F (M.prod M)=P`。实际选择的 `map_measureReal_apply` 是 Measurable 版本，完整头为

    theorem map_measureReal_apply [MeasurableSpace β] {f : α → β} (hf : Measurable f)
        {s : Set β} (hs : MeasurableSet s) : (μ.map f).real s = μ.real (f ⁻¹' s)

其完整头 hash `dd3d17d057e0265937d499c3ff7bbdf4617606cac0c2075b7ddc50f30e56b074` 与原 Real 第84–85行一致。旧 Stage1 所选的 `_of_aemeasurable` 较长名称不是此头；我没有复用那个错误判断。

`measureReal_mono` 的完整头包含默认参数内部的 `:=`：

    @[gcongr] theorem measureReal_mono (h : s₁ ⊆ s₂) (h₂ : μ s₂ ≠ ∞ := by finiteness) :
        μ.real s₁ ≤ μ.real s₂

完整头 hash `001df2731ed046a784360de2810ecde04baf56ce16cb2b3cbbdef3a78ba39435` 与原 Real 第88–89行一致。它的真实上集有限性义务没有被截短头遮蔽；在这里由 M.prod M 有限给出。两项 corrected 完整声明 block 和此前全部 raw prefix 的 hash/bytes 都已独立比对。规范合同把三处原像的 U+2032 改为 Lean U+0027，仅为事前语法规范化，actual hAB/hpreimage/hmono 逐字符合规范合同。

Pi 的已保存“prefix”文本实际是完整 raw pre-header prefix加完整 instance head后附一个 LF；原主源在该头后以空格和 `:=` 继续，所以不能把此文件连末尾规范 LF声称为原文件字面初始字节。这是本次过严格 startswith 测试识别出的封装边界。已分别核对 exact raw prefix hash `483549f83047ea10fc6d2ee02f423fc2713067a9a2504372a17217627bfb804a`、完整 head hash `1db958de2a220b7107c95bd020aed96d010aed6023b8238f4a4a5dff6cc0153e` 和完整主源 hash，没有缺失变量或条件。完整上下文明确只需 Fintype ι、可测空间族和每坐标概率；Encodable section 已关闭，Fin0也被覆盖。未改动历史封存文本。

## 5. 所有六个别名、局部实例和数学闭包

M和P仅命名已有法则，捕获 n、Ω、mΩ、μ；A仅命名冻结目标谓词，捕获 n、g、t及其类型；B命名200 goodEvent；D命名199 pairedTailEvent；F命名188 pairSamples。它们均无选择、见证提取、采样、新归一化或新增数学对象。hMProbability在展开M和sampleLaw后使用既有 pi 概率实例；它是已给 μ 概率性质的证明，不是新前提，且只作用于 theorem body。

已逐项独立核对作者 map中的8组 source-visible closure、13组 inherited/structural closure和17组匿名命题组合；详细逐项结论在 SOURCE-COVERAGE。它们包括 hgmean 的恒等复合 integrand、hgsecond 的平方 integrand、全局/A重复事件谓词、两条 a_p/b_p lambda、M/P的常值法则族、F的坐标对、sampleSum/sampleEnergy的求和坐标函数、B/D既有谓词、pairedDifference和scalarEnergy组合、点态差及差平方、preimage谓词与hpreimage证明中的实质量求值等式替换上下文。

特别地，p只是hAB内任意产品点，hp只是其属于A×B的局部命题；两个i分别由各自lambda绑定。p/hp/i都不逃逸到theorem假设、别名或其他证明。组合 `fun i => g(p.1 i)-g(p.2 i)` 及其平方仅是已冻结 F/pairedDifference/scalarEnergy/a_p/b_p 的 delta/beta/投影归约，没有新数据声明。goodEvent actual FULLVALUE 的 `_proof_1/_proof_2` 是OfNat实例中的证明字段；它们由精确200资格覆盖，不是隐藏的函数、样本或额外假设。

## 6. 十四项局部命题和完整证明

| 源行 | 命题 | 独立核对的理由 |
|---|---|---|
|38–40|hB|200实际完整TYPE的全部hg/hg2/hgmean/hgsecond条件精确满足；得到B可测与M.real B≥1/2的完整合取。只消费其第二字段，没有消费200T01。|
|41–42|hD|199实际TYPE对任意n、Ω和t给pairedTailEvent可测，唯一函数条件是hg。D只是该事件别名。|
|43–44|hF|188保测TYPE的原测度为sampleLaw.prod sampleLaw，目标为pairedLaw，映射为pairSamples；分别与M/P/F定义相同。|
|45–49|hAB|p=(x,y)任意；hp.1、hp.2.1、hp.2.2经下述完整归约分别精确满足201的ha/hbSum/hbSq；201结论精确归约为F p∈D。|
|50–51|hrectangle|固定主源任意集合矩形实质量公式，所有measurable-space及SFinite M支持满足；没有要求A可测。|
|52–54|hpreimage|先取真实map实质量公式的对称，右边是((M.prod M).map F).real D；只用hF.map_eq向P改写，方向和目标完全匹配。|
|55–56|hmono|hAB提供包含；上集F⁻¹'D在有限M.prod M下质量非∞，满足完整默认参数；无可测性遗漏。|
|57–58|ht0|t≥1直接给t≥0，没有增加t>1。|
|59–60|hpaired|199实际TYPE仅需μ概率、hg、t≥0；P/D原法则和严格事件都一致，得到2exp(-t²/2)。|
|61–66|hproduct|四个calc命题依次用hrectangle.symm、hmono、hpreimage、hpaired；等式/不等式传递正确，得到ab≤2e。|
|67–68|hA0|实质量非负主源不需集合可测或有限；这里给a≥0。|
|69–70|hBdiff|从hB.2作实数减法得b−1/2≥0。|
|71–72|hmul0|由两因子非负得a(b−1/2)≥0。|
|73–74|hfinal|前式展开给a/2≤ab，与ab≤2e相合得a≤4e；nlinarith只须此实数多项式事实。|

hAB的关键定义转换逐步如下。设 a_i=g(p.1 i)、b_i=g(p.2 i)。hp.1经A、sampleEnergy、sampleSum变成

    t(√Σa_i²+4√n) < |Σa_i|.

hp.2经B、goodEvent变成 `|Σb_i|≤2√n ∧ Σb_i²≤4n`，故其两个投影匹配201的两个弱条件。201的实际结论是

    t√(Σ_i(a_i-b_i)²) < |Σ_i(a_i-b_i)|.

F p i按pairSamples的FULLVALUE归约为(p.1 i,p.2 i)；pairedDifference n g (F p) i再按其FULLVALUE归约为a_i−b_i；scalarEnergy按其FULLVALUE归约为上述差平方和。D谓词实际就是t乘该sqrt严格小于该差和绝对值。故Set.prod、Set.preimage、Set.ofPred、delta、beta和产品投影归约已足够匹配`exact`；无需Σa−Σb的分配恒等式、函数外延、样本选择或额外有限和引理。数值OfNat证明字段的差异属证明无关性，不改变数值。

最终`exact hfinal`只需展开M和A便是全局冻结目标。在最后算术中没有除以b、n或能量，也没有使用exp正性；若令e为任意实数，同样的a≥0、b≥1/2、ab≤2e仍足够得a≤4e。证明因此不藏有额外严格正性条件。

## 7. 边界与结论强度

所有n保留：n=0时平方和、和、√n都为0，严格A为0<0而为空；既有201和有限pi概率实例同样允许Fin0，代码没有要求n>0。t=1原样保留。A和D都保持严格不等号，B保持两个弱不等号；原子法则和阈值等号没有经过连续尾概率或无原子论证删除。原能量或配对能量为0时仍以sqrt表达，不作除法或条件化。Ω任意可测空间，μ任意概率，只有声明给定的可测/L²/均值0/二阶矩1条件；没有标准Borel、L⁴、指数矩或无原子假设。

这是一条将现有资格188/199/200/201相接的完整原样本上尾组件证明。数学论证和冻结声明匹配；SOURCE_CORRECT不宣称该组件有新颖性，也不宣称完整S11、C2/C12/OQ56根结论已完成。

## 8. 后续精确机器证据门

本次实际运行止于本地SOURCE审阅；actualOwned仍为UNKNOWN。父级若提供相同源码的首次成功native、首原始O、same-original-O的所有actual owned完整TYPE、所有非定理FULLVALUE、递归AX及source/object/owner绑定，我可以在同一独立上下文组合最终结论。后续不得以namespace前缀过滤遗漏private/generated/foreign actual owners，也不得以本静态清单猜测actual owned数量。

最终机器组合须确认实际Lean退出码、自然结束/无超时、原源码和原O同一性、所有实际名字/宇宙/类型/非定理值、实际声明与冻结的忠实性、所有递归AX仅在标准白名单内，以及未改变的精确旧producer证据复用。native警告、失败尝试或strict-wrapper历史状态应按真实结果保留；不得把dispatch、静态校验或SOURCE_CORRECT当作机器通过。只有收到并独立覆盖这些实际证据后，才能给CORRECT/QUALIFIED。
