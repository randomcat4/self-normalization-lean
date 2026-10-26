# 单元201独立最终 SOURCE 审阅

STATUS: SOURCE_CORRECT

本裁决只覆盖精确源码的原始含义、冻结声明、完整证明及源码可见数据/类型/作用域。qualified=false；actualOwned=UNKNOWN；actualTYPE=UNKNOWN；服务器 native/同首次原对象 TYPE、非定理 VALUE、全部所属传递 AX 门尚未在本审阅中执行。本报告用途是父级 native 后 same-first-O machine composition，不能单独充当机械合格证。

## 独立性与精确版本

审阅者是全新上下文 /root/oq56_ghostcmp201_final_review，收到配置为 gpt-6.1-sol/xhigh；实际模型、努力与四类 token 遥测未暴露，均记 null。未参与201 Stage1/Stage2实现或声明冻结；未改动作者、冻结、旧证据或共享实现。只写 final-review-01。未建立子实例，未执行 Lean、AX、服务器、SSH、上传、Git、网络/API 或发布。

有效 OQ56 父 owner 为01a17665-2e41-7ed1-9911-57f16fe889fa；已读独立激活文件、当前 AGENTS/streamlined acceptance、SERVER 与 TEAM 的所需段及 REGISTRY 该 lane 字段。作者 RELEASE0 六项 writer/execution/heavy/inflight/pendingExternal/children 均0，且绑定 manifest/DONE/runtimeACK 的散列匹配。本审阅不恢复旧 owner，也不占 heavy 槽。

本轮唯一被审源码：drafts/oq56/unit201/author-01/stage2/OriginalGhostComparison.lean，SHA256 ae0c788f6d25b698d617140fe81a8487d73295ed352a08a1ed10f14dd6dfc777，11526B/254LF/0CR/无BOM。父 freeze SHA256 a030bc1fc9135636ed5f6f7d48ae5685a87e0008f8aa36d775b2a3950597a33b；事前 overlay 文件实际名为 parent-metadata-overlay01-tactic-imports.json，SHA256 1dab014276f0594c99bccf5ee4d4b8b4fa93af7cf987b195e822ebbf3eaa04e5。只增加已经事前授权的 Mathlib.Tactic.Linarith、Mathlib.Tactic.Ring 两条 import。

T01完整头散列 e9b21814e524fecb0eab10953a385e41549a8aa88b68e2eb2760cd96058b0a79；T02完整头散列6349206513ad78a0a2a2f80973425d99d818e47f25efed6cea35e41389e1075b。两个头与父冻结逐字相同；有效完整前缀与 closure 逐字匹配。T01/T02完整证明体分别为dcec151df4c6070725f7928cce948e89f6efecb88c4115a755e4316da1637842、6d935e6b6445cdc6f65e5a09ebecffe1205254d62e4cf20308c360cb8f646adf。

## 原源与陈述忠实性

已完整读取 Stage1 derivation.md、p51.md及Stage1 source-to-statement/assumptions/downstream/provenance，未把其自述结论当独立证据。p51 SHA256 96920f428b8fc09788a6388103cefe398e3ec739129a5922b984babd09e99359，17326B。其 S10/S11 是实际 W/V/Gy 的概率上尾接口，p51自身仍标 UNCERTIFIED_REPAIR_CANDIDATE；本源只证明双样本 A×B⊆D 的确定性向量核心。

T01量词是任意 n:ℕ、a b:Fin n→ℝ，没有额外前提；目标是 sqrt(Σ(a−b)²)≤sqrt(Σa²)+sqrt(Σb²)。T02另取任意 t:ℝ，并精确保留 ht:1≤t、ha:t(sqrt(Σa²)+4sqrt(n:ℝ))<|Σa|、hbSum:|Σb|≤2sqrt(n:ℝ)、hbSq:Σb²≤4(n:ℝ)。目标严格为 t sqrt(Σ(a−b)²)<|Σ(a−b)|。没有增加 n>0、非负坐标、能量正、t>1、连续律或概率假设，也没有将结论弱化。

未来代入 a_i=g(x_i)、b_i=g(y_i) 确实产生所需点态包含关系，但本源没有定义或证明 sampleLaw、A/B/D 的可测性、矩形概率、pairSamples传输、199/200合成或实际 W/V/Gy 规范化。p51根S11及C2/C12/OQ56保持OPEN；原C1 immutablev85完整状态不因本单元变化；OQ3仍PAUSED_BY_USER。保留 Shao–Zhou(2016)(92) 和其路线对 Jing–Shao–Wang(2003)Lemma6.4 的外部归因；未声称读到不可得JSW全文或证明新颖性。

## T01：完整证明检查（源码14–154行）

令 Qa=Σa_i²、Qb=Σb_i²、R=Σ(a_i−b_i)²、C=Σa_i b_i，ra=√Qa、rb=√Qb、rR=√R，L=Σ_iΣ_j(a_i b_j−a_j b_i)²，M=ra rb，U=ra+rb。源码19–29行的10个let均是冻结的确定性实表达式；其完整初始化、直接/传递捕获和范围逐项列于 SOURCE-COVERAGE.json。

30–40行的局部 hSquareOrder 对所有 x,y:ℝ、x,y≥0、x²≤y²给x≤y。肯定分支直接返回；否定分支由x>y≥0得到x>0、x+y>0，故(x−y)(x+y)>0，而原x²≤y²与恒等式(x−y)(x+y)=x²−y²矛盾。全部 x,y 只绑定在本局部∀命题的证明中，未成为新外部参数或所选数据。hx虽未被否定分支使用，不影响命题正确性。

41–53行分别逐项使用实平方非负与有限非负求和，证明Qa,Qb,R,L≥0，包括空和。54–83行三条双和恒等式逐项核对：Σ_iΣ_j a_i²b_j²=QaQb；Σ_iΣ_j a_j²b_i²=QbQa（只在固定i,j项内交换乘法）；Σ_iΣ_j 2(a_i b_i)(a_j b_j)=2C²。Fintype.sum_mul_sum 的方向在前两项用对称式，在第三项将右侧乘积展开；Finset.mul_sum 两层分配常数2。不存在交换无限和或额外收敛前提。

84–106行逐项多项式恒等式为(a_i b_j−a_j b_i)²=a_i²b_j²+a_j²b_i²−2(a_i b_i)(a_j b_j)。先在j、再在i的同一Fin n完整范围取和，sum_add/sub_distrib分离三项，再代入上述三条恒等式，得到 L=2(QaQb−C²)。由L≥0得到107–108行C²≤QaQb。常数2为正的实数，未除以n或能量。

109–122行在已经证明的非负输入上逐个用Real.sq_sqrt给ra²=Qa、rb²=Qb、rR²=R；sqrt_nonneg给各根非负，因而M≥0且M²=QaQb。123–127行不直接实现Stage1的|C|路线，而在−C≥0时对−C与M用同一个平方序事实，由C²≤M²推出−C≤M；在¬(0≤−C)时有−C<0≤M。这个确定性的证明变体得到同一所需结论，不改任何声明、数据或假设。

128–140行以固定坐标的(a_i−b_i)²=a_i²+b_i²−2a_i b_i及有限分配律得到R=Qa+Qb−2C。141–149行U≥0且U²=Qa+Qb+2M。由−C≤M得150–151行R≤U²。152–154行把目标改写为rR≤U，使用rR,U≥0及rR²=R≤U²的平方序事实，闭合T01。源证明没有把Cauchy–Schwarz、Minkowski或目标当假设，也没有未证私有全局引理。

## T02：完整证明检查（源码156–252行）

165–176行的12个let分别为N=(n:ℝ)、Sa=Σa、Sb=Σb、Sd=Σ(a−b)、Qa/Qb/R、ra/rb/rR、rN=√N、r4N=√(4N)。它们全部精确复用冻结初始化。177–187行第二个 hSquareOrder 完整复现上述独立平方序证明，x,y作用域只在该局部证明内。

188–203行由自然数转换得N≥0，并获得rN≥0、rN²=N、Qb≥0、rb≥0、rb²=Qb、4N≥0、2rN≥0、r4N≥0、r4N²=4N。204–207行调用钉死Real.sqrt_eq_iff_eq_sq的第二方向；其前提正是4N≥0与2rN≥0，剩余等式4N=(2rN)²由rN²=N得到。故r4N=2rN，不使用错误的无条件抽根规则。

208–214行用原hbSq得到Qb≤4N；非负rb与r4N平方比较给rb≤r4N=2rN。215行仅由ht推出t≥0。216/217行ha/hbSum只做let定义展开后的同义绑定。

218–220行sum_sub_distrib精确给Sd=Sa−Sb。221–224行对Sa=(Sa−Sb)+Sb使用abs_add_le得到|Sa|≤|Sa−Sb|+|Sb|，与hbSum合成225–226行|Sa|−2rN≤|Sa−Sb|。没有把绝对值差改成有符号差，也没有丢掉负Sa/Sb情形。

227–229行把原严格ha的两边减去同一2rN，代数展开得到t ra+(4t−2)rN<|Sa|−2rN。230–234行由t≥1得2t≤4t−2，再仅在rN≥0的前提下乘rN；235–237行加上同一t ra，得到t(ra+2rN)≤t ra+(4t−2)rN。238–240行从rb≤2rN加ra、乘非负t，得到t(ra+rb)≤t(ra+2rN)。241–244行使用本源已完整证明的T01并乘t≥0，得到t rR≤t(ra+rb)。

245–252行最终完整链为

    t rR ≤ t(ra+rb) ≤ t(ra+2rN)
          ≤ t ra+(4t−2)rN < |Sa|−2rN
          ≤ |Sa−Sb| = |Sd|.

唯一承担最终严格性的外部输入是ha；所有其余步骤允许等号。链中没有缺少符号条件、倒转不等号、改变阈值或循环调用T02。

## 退化、等号、原子和作用域

- n=0时所有有限和和N均0，T01为0≤0；T02的ha为0<0，原前提不可能同时成立。源码没有人为加n>0。
- Qa=0时有限非负平方和迫使a逐点0，ha左边非负而右边0；Qb=0时b逐点0，整个证明仍成立；R=0时a=b、Sd=0，完整链表明原四前提不可能同时成立。这些边界解释没有成为新假设，也不需要源码额外拆分或除法。
- t=1时2t=4t−2，仍保留ha的严格性。hbSum/hbSq的等号原子全部包含；ha阈值等号按冻结严格<排除。负坐标、C的两种符号和零根均覆盖。
- 本结论是逐向量、逐样本的代数比较，不使用尾概率连续、a.e.选择或无原子条件。因此离散分布、重复样本、阈值原子不会产生未覆盖的概率极限步骤。
- 全部和在标准Finset.univ:Finset(Fin n)上。内层j只绑定于固定外层i的双和/对应pointwise证明，不能逃逸。x,y只在两处∀命题证明内部；7条intro中其余5条仅引入sum_congr要求的Fin n索引及univ成员证明。没有存在到数据消除、新instance、classical命令、selector或隐藏函数参数。

## 全量数据、Prop、匿名闭包与数字覆盖

从原源码独立扫描并逐项对照，而不是复制作者总数，得到2全局theorem、22实数let（T01 10/T02 12）、59显式局部Prop头（T01 27/T02 32，其中2处bullet前缀）、3个by_cases/6分支、10处显式lambda（4数据函数/6Prop证明函数）、44处∑隐式函数、7条intro。源码可见全局def/abbrev/opaque/instance/私有辅助声明均0；这不是未来actualOwned计数。

已逐个读取59个完整类型、22个完整初始化与捕获、10显式lambda完整类型/结果/初始化/捕获、44隐式sum函数完整初始化/类型/捕获和全部分支上下文。ordinary Prop仅含普通实数等式、不等式和上述∀平方序事实，不藏数据/instance见证。line52外层Prop lambda不自由捕获内层j；line53内层闭包捕获固定外i。已有两项metadata修复失败账（.2被误判为实数、外层误捕获j）完整保留，当前源码及映射已一致，未据此改动证明。

数字从源码独立派生为138个数学数字位置：76个ℝ字面量与62个ℕ平方幂；所有实数0/1/2/4及平方幂2均显式注型。206行.2是Iff方向投影而非数学实常数，独立分类1处。自然数n仅通过显式实转换进入尺度。完整位置与原numeric-map相同。

SOURCE-COVERAGE.json保留每项完整头/类型/初始化/作用域/捕获和来源范围。源码只完整语义读取一次；source-map/proof-bodies内完全相同的重复raw用精确切片/散列回读复用，没有谎称重复原文再次逐字独立阅读。131个显式lossless源码span及完整254行索引无差错回读；两个proof-bodies逐字/散列一致。Stage1 25项封存payload、Stage2 18项封存payload、16个immutable输入的散列与字节均匹配。

## 钉死库接口与证据边界

钉死Lean为leanprover/lean4:v4.36.0-rc1，mathlib为807d3836b165983210ee2ecf3cd28f239436949c，仅阅读已有pin与原源包，没有探测或安装本机Lean。已重建并校验6份完整主源散列；完整读取每份所需的最大原始连续前缀（连同所用声明）：Ring/Finset 1–68、Group/Finset/Basic 1–311、Group/Finset/Defs 1–679、Order/Group/Finset 1–160、Real/Sqrt 1–183、Unbundled/Abs 1–127。15条选定接口各自严格位于属性/头之前的全部prefix与块SHA/字节均匹配。

核对了Finset.sum的标准数据初始化及sum_congr、sum_add_distrib、sum_sub_distrib、sum_nonneg、mul_sum、Fintype.sum_mul_sum的实数特化；sum_mul是包内辅助接口，本源不直接调用。to_additive条目保留原始乘法头、属性、真实section作用域与实加法特化；未把生成泛型签名冒充已反射actualTYPE。Basic的bij节已关闭；Defs的BigOperators/CommMonoid/Opposite节已关闭；Ring中AddCommMonoidWithOne已关闭；不让过期局部classical/section变量泄漏。有限索引、实有序环及现存实加法次序实例满足各调用条件。

Real.sqrt/NNReal.sqrt完整现存noncomputable初始化已读；sqrt_nonneg、sq_sqrt、sqrt_eq_iff_eq_sq只在其真实实数变量与非负前提下使用。Abs的Group节在三角不等式前关闭，abs_add_le来自CommGroup+MulLeftMono下的to_additive源；实数特化的两个显式参数与源码调用相符。其余sq_nonneg、乘法单调性、序传递、加法抵消等普通实算术调用的条件在上述逐步证明中逐项满足。

本源没有旧项目形式依赖，唯一项目调用是T02调用同源T01。没有要求重编任何已接受producer或旧leaf AX。未新增或放宽公理白名单；本轮静态禁止词扫描无sorry/admit/new axiom/unsafe/native_decide。未来父级必须在同一精确新源首次成功原对象上检查全部实际所属TYPE、每个非定理VALUE及递归AX，白名单仍为propext、Classical.choice、Quot.sound；未来生成名/实际公理范围目前未知。

## 裁决与下一门

没有发现关键数学缺口或声明/假设漂移，故精确SOURCE裁决为SOURCE_CORRECT，gaps=[]。该结论不等于Lean执行通过，也不等于原S11或任何开放根已完成。下一精确依赖由父级在既有OQ56资源/锁/phase内执行201精确源首次native；若通过，将本完整独立SOURCE审阅与same-first-O的全实际TYPE/非定理VALUE/传递AX证据合成。只有实际变更的源码/未覆盖机器差量需要后续审阅；不重演已接受旧单元。最终RELEASE0终结本审阅writer/execution/child权限，不提供持续后台执行机制。

本审阅封存元数据曾有一次本地JavaScript解析错误（未加引号的数字开头属性名），整格在执行前被拒绝，无作者源码或冻结输入效果；只修复未执行的元数据构造。实际错误及修复边界已封存于failures.json，不计为Lean/数学失败。
