# Unit165 独立完整终审

STATUS: CORRECT。此结论覆盖冻结的一个公开定理、全部一个实际所属定理的数学语义、完整证明和完整实际类型，以及精确源码的原始服务端内核与传递公理证据。未发现关键缺口。本报告仍需父实例按封存字节作资格确认；评审者不代替父实例验收、发布或合并。

## 精确范围与角色

评审者为全新独立上下文 `/root/auxiliary_cutoff_payment_final_review`，不是作者。按明确派发配置使用 gpt-6.1-sol/xhigh；没有切换模型，底层后端与分项用量遥测不可见，均如实记为null。仅写本评审目录，未修改任何形式源码、原始证据或共享文件；服务器只读，Lean/公理审计执行及成功重放均为0。作者RELEASE已释放写入和执行权限，0在途。本单元外的161、163未验证消费者不在本轮验收范围。

## 冻结陈述及原文对应

模块 `Shao.C2.AuxiliarySourceCutoffPayment` 的冻结SHA256为 `3e3eae27819c9b09e0b821ad91fd7cc1c776afcfc8bfb93b8d718c8c43f5e792`；源码SHA256为 `aba1f5bfded1baf75673d3c9cedd3278f9e028e8a874dd5af218b6a3dbcfab16`。完整导入、设置、命名空间和声明头在实现前冻结；剥离证明后的源码与冻结文本逐字相同。没有新私有头、生成头或全局非定理值。

记M=β²(1+x)^6、H=KM、m=Nat.ceil H。定理全称量化实数β,L,rhoStar,K,s,x和自然数t,n，假设β≥1、L≥0、rhoStar>0、s≥0、x≥1、K≥8000000(1+L)²、K≥2(768/rhoStar)²、m≤t、n=t或n=t−1、st≤Lx²。结论严格为m≥4、n>0、t/2≤n、sn≤Lx²以及4000000(1+L)²M≤n和(768/rhoStar)²M≤n。未将所需秩、漂移、预算或尾界作为输入结论假设。

已完整阅读只读supplement.tex4945–4995及5070–5145相关上下文；其SHA256为b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd。4984明确定义H=Kβ²(1+x)^6与m=ceilH；5094–5111以t≥m、l=t或t−1、st≤Lx²并在L后增大K取得小参数和自身C1预算，5110明确l≥t/2且m≥4；5122使用l/β²≥K(1+x)^6/2；5133要求sqrtK≥800sqrt8 L。形式化采用更显式充分的K下界，不声称这是原文最优常数。8000000(1+L)²≥5120000L²，故其选择也与5133允许的一次增大K一致。K的两个阈值只依赖L和rhoStar，可在β、x、s、t,n等后续选择之前统一取最大值；形式定理是这个选择的全称条件式支付接口，不伪称已形式化存在性选择或全部剩余尾估计。

main.tex的SHA256为beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06；145–170、175–190的原始iid、真实Q、正二阶矩及2<p≤3范围已核对。unit165是纯数值辅助层，β≥1是显式假设，并不额外要求原始律有限三阶矩。本项目辅助预处理律可用有限三阶矩；原始有限二阶/有限p阶范围没有被修改。原始C1已于v85完成，C2/C12仍开放；OQ3仍由用户暂停。

本定理没有给出原文m≤2H≤原始总长/4、随机截止存在性、真实稀有后缀估计、低能概率、C2或C12根范围闭合。它只支付所陈述的确定性长度和数值秩；该限定与作者source-and-proof.md及freeze-record.json一致。

## 完整数学证明核查

- 源码23–34：令M=β²(1+x)^6。β≥1给β²≥1；x≥1给1+x≥1，由非负底数幂单调性得(1+x)^6≥1。β²≥0与幂减1≥0的乘积非负给M≥β²≥1，故M≥0。无除法或符号取消。
- 源码35–40：L≥0及L²≥0给(1+L)²=L²+2L+1≥1，故hKDrift给K≥8000000>0。K(M−1)≥0，结合H=KM得到H≥K≥4。
- 源码41–46：Nat.le_ceil H精确为H≤(Nat.ceil H:ℝ)，合并4≤H并以exact_mod_cast得4≤m。hCutoff给4≤t，因而1≤t，实数强制转换仍≥4。Nat.ceil_le.mp hCutoff的方向为m≤t推出H≤(t:ℝ)，没有把上取整误当向下取整，也没有额外非负前提。
- 源码47–59：hLength逐一分支。n=t时t≥4给t/2≤n；n=t−1时先有1≤t，Nat.cast_sub hT1将自然数截断减法正确转换为实数t−1，t≥4保证t/2≤t−1。两分支都给n≤t；t≥4与n≥t/2给n>0，再由实数转换回自然数。没有t=0或t=1漏支。
- 源码60–61：由n≤t与s≥0正向乘得sn≤st≤Lx²。s=0与时间等号都合法，无除以s或L。
- 源码62–66：hKDrift乘M≥0得8000000(1+L)²M≤KM=H≤t；n≥t/2等价于t≤2n，故4000000(1+L)²M≤n。乘法结合按实际左结合因子展开；nlinarith仅执行这些多项式关系，未取消可能为0的M。
- 源码67–71：hKBudget乘M≥0得2(768/rhoStar)²M≤H≤t≤2n，故(768/rhoStar)²M≤n。这里不除以rhoStar，也不需要由平方反推符号；hRho保留原文C1合法参数。
- 源码72–74：按冻结六重合取原顺序返回hm4、hn、hNLower、hTimeN、hDriftPay、hBudgetPay。局部let H/M完全展开到冻结表达式，无额外全局定义、存在量词或隐藏前提。

以上是独立逐步数学核查，而不是从编译PASS推断正确。完整74行生产源码已读，含所有局部辅助事实和两个长度分支。不存在只证明有限样例、暗改量词或用结论等价前提替代实际来源参数的情况。

## 边界与接口

- β=1、L=0、x=1均由弱不等式直接覆盖；没有借助严格边界。K取两条下界的最大值允许等号，K>0由漂移下界得到。
- s=0时hTime和hTimeN直接成立；时间st=Lx²等号保留。t=m与n=t或n=t−1均允许；n为自然数而非人为提供的正实数。
- 局部长短分支的最小算术检查t=4,n=3给2≤3和3>0；实际全组K/β/x前提迫使t远大于4，故这只是对分支证明的边界核对，不伪称t=4满足完整前提。
- rhoStar>0任意接近0时只使允许的K阈值增大，未额外假定rhoStar≤1/16。该上界属于后续C1概率消费者，unit165只支付数值秩，不负责其全部前提。
- 自然上取整使用真实Real FloorRing.toFloorSemiring，H已证明正，因而与原文整数上取整一致；没有负数截断差异。
- 未消去β、L、s、x、M、K或rhoStar的可能零值来证明不合法等价；唯一实数/自然数减法转换先支付1≤t。


新增原生导入Mathlib.Algebra.Order.Floor.Semiring的实际文件与钉住mathlib提交807d3836b165983210ee2ecf3cd28f239436949c逐字一致：Semiring.lean SHA256 7c0fa92ce68350dc4e97bac5ba8cadc3d2c4da70f36eb6c42d5647176d587f68，public import的Defs.lean SHA256 58450c1ab0d8bb32bc03dadc047190856f73c66f4f36a7392e9f4a842c75de2f。已阅读实际接口与所需上下文：Nat.le_ceil (a:R) : a≤(Nat.ceil a:R)；Nat.ceil_le : Nat.ceil a≤n ↔ a≤(n:R)。后者在Defs.lean156，前者在Semiring.lean179。`.mp hCutoff`方向完全正确。Real的FloorRing转FloorSemiring实例确实以整数ceil.toNat定义；其Galois连接给上述接口。未把同名Int.ceil_le误作Nat.ceil_le。

新Semiring原生对象SHA256为211f87bcff12008465b7c009199d5bd9045dc4ef8ef1ca1b5b1973c6975bf9a7，其现存修改时间早于attempt001命令文件。生产命令是lake env lean而非构建或取缓存，使用既有只读shared-v34对象；本轮没有包、缓存、环境或版本写入。

已读取158的两个完整源声明头、159的三个完整源声明头以及163当前冻结完整头，只评估新支付接口的匹配。158所需4000000(1+L)²β²(1+x)^6≤n和sn≤Lx²被本结论原样支付；159所需(768/rhoStar)²β²(1+x)^6≤n和n>0也被原样支付，β非负由β≥1取得。163冻结头的两条rank与时间条件逐字相同，令β为真实三阶绝对矩后可消费；这不是对163尚未通过证明的验收。后续rhoStar≤1/16、律、可积性、归一化等前提仍须由消费者另付。unit165只导入164来携带已有上下文，没有调用其新标记删除定理，也没有依赖161/163的未验证对象。

## 实际所属完整类型和值

原始OwnedAudit从env.constants.toList遍历，以env.getModuleIdxFor?及env.header.moduleNames判定真实模块归属；不按命名空间、公开名单或作者估计过滤。实际报告只有
`Shao.C2.AuxiliarySourceCutoffPayment.auxiliary_original_cutoff_rank_payment`，kind=theorem，公开数1、实际所属数1、实际定理数1、私有/生成额外所属数0、全局非定理值数0。

完整actual-owned-types.txt为10571字节、148行，已逐行阅读。其前六个数据绑定均为Real；β,L,rhoStar,s,x及K两阈值均为相应Real序关系；t,n确为Nat；hCutoff调用Real.semiring/Real.partialOrder与FloorRing.toFloorSemiring的真实Nat.ceil；hLength第二分支确为Nat的截断减法t−1。hTime及后五项数值比较都显式使用Real的Nat.cast，m≥4与n>0保持Nat序。所有2和6次幂的指数是Nat，除法为Real除法，六项合取顺序与冻结陈述完全一致。无额外实例、依赖let、错误数域、缺失量词或被省略的类型条件。pp.all导出无省略号、元变量或sorryAx。完整类型原文保留在full-review.json对应唯一owner记录中，并按SHA256 975ecf97db690543522d707ad790d9400a6619376e379ac2dc1f14506799e979绑定。

actual-definition-values.txt严格0字节，SHA256 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855，与0全局非定理值和1个实际theorem的完整归属图一致；没有缺读其他种类值。原audit日志由10571字节完整类型和225字节警告/汇总/成功后缀组成，共10796字节，导出逐字一致。

## 内核、公理及证据

原始attempt001命令、生产source.lean、kernel.log、OwnedAudit.lean、owned-audit.log/json、完整类型/空值、冻结文件、来源说明、receipt和RELEASE全部按收据SHA256核对；当前WT源码、输出对象及WT实际导入对象一致。对象SHA256为2ef0ee97e31fceaa3bb618fc8dbebb65e3341ba29137000e24fdfd8381340bdd；receipt SHA256为98d7a4d2b5acb2b367f885d9d3b2720afeab742aea9466f063b6d37700fdb74e。全部13个收据依赖源码和既有资格对象绑定已核对。初次只读观察共47个精确远端绑定全部匹配；封存前另作同一集合及新增原生接口的最终只读绑定。

完整阅读OwnedAudit.lean及finish-receipt.py。审计对每一个真实owner调用Lean.collectAxioms，并在任何非白名单公理出现时失败。沿用旧合格证据中已完整核查的递归collector实现与实际owner接口语义；本轮又将当前钉住工具链的CollectAxioms.lean源SHA256 b39bd22253a76816ee6d24284e69674d0b491be343fd71f9ee9376833d1485f6以及Environment.lean源SHA256 e7b97a029388b84c3f69c58e8df9e30064415e34a863781e1843e8c6c15e0e8f逐字绑定。递归遍历类型与值/证明依赖而非只查直接公理；本owner结果精确为propext、Classical.choice、Quot.sound。源码禁用词sorry/admit/axiom/unsafe/native_decide均未出现。

finish-receipt.py从原始日志按TARGET_DECL/DEFINITION_VALUE导出完整类型和值，检查完整无省略、1/1/0/1计数、成功标记和唯一attempt001；比较原始快照与当前源、输出对象与导入对象，剥离证明比较全部冻结上下文，再更新对应unit165模块、对象、命令和依赖清单。虽复用旧收据结构，本轮已核实所有实际字段及原始文件，未接受遗留模板计数。没有失败内核尝试，只有attempt001。kernelExit=0、auditExit=0。kernel日志的unused hRho警告真实保留；它说明本纯数值证明未需该正性条件，并不改变原文C1参数要求。mathlib repository local changes通用警告也保留；本次实际新增消费原生文件均已与钉住Git源码逐字核对。

工具链为leanprover/lean4:v4.36.0-rc1，mathlib为807d3836b165983210ee2ecf3cd28f239436949c，包视图为shared-v34。原命令使用CPU14–17、c12-heavy.lock、-M8192 -j4，符合资源约束。原receipt所记author/c12-auxiliary-centered-v71与headaef587dd277f159314297cef02b352057d7102ec是当时事实；当前只读观察为author/c12-own-c1-budget-v71、HEAD123547c9275f119c38975c95cd2dbc61d8bdf551。源码/对象/冻结证据未变，旧收据不因后续发布换支而改写。观察时无目标Lean/lake进程。

旧150–160/162/164合格评审及其父资格记录按各自封存哈希复用，未再审或重放旧证明。最新160/162/164父资格SHA256为f2aa5279ec91684de2bc70f8ca61be2f2b73b3a45873fcb090f629bd7de4f447；158/159父资格SHA256为674872c472c907628c5f6e9ad3439fc633349e135b10e381380c2e760d8647b6。其他前序绑定列在JSON和只读观察中。未把接受旧接口当作自动接受新增消费者。

## 结论、价值和释放

unit165在其精确冻结范围内CORRECT，证明完整，语义与实际类型一致，来源参数顺序和辅助律范围保持，原始服务端内核及全实际owner传递公理证据可信可复用。它是来源数值支付辅助引理，不主张研究新颖性或独立论文贡献。没有实际稀有后缀或C2/C12根闭合结论。

query-mistakes.json保留本轮只读查询的截断、异构JSON模式误读和原生接口定位修正；均无源码/服务器写入或Lean执行。父实例应完整阅读本报告、核对封存哈希并作资格确认，随后继续真正来源消费者。writer-release.json最后写入后本目录全部评审工件不可修改；评审写入与执行释放，0在途。本普通回合结束不充当持续运行机制。
