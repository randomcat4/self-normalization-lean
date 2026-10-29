# unit280 完整冻结实现：作者报告

状态：AUTHOR_COMPLETE_NOT_SOURCE_ACCEPTED_NOT_KERNEL_CHECKED。已实施完整8个冻结声明，其中2个固定定义、6个完整候选proof（5公开、1私有）。未运行 Lean、AX、编译、工具链探测、前缀或任何服务器命令；不能把本文或文本 guard 当成类型检查/内核通过或独立审查。

唯一写域：C:/game/shao lean/drafts/oq56/unit280/author-01。实施授权为 implementation-ACTIVATION.json 95121b6490458f065f920a5915f47cc38b1b37c5faba8fa327eeb51daeb1a31e /14883B，冻结记录 bcd298af759372f157cf955d255c4eb967c45e206a069073e1922e0058c14f5e /6889B。首写前57输入与ACT共58绑定逐项SHA/bytes相符。请求gpt-6.1-sol/xhigh；actual backend/model/effort及input/cachedInput/output/reasoningSubset用量未暴露，全部null。

## 1. 完整交付与字节组装

完整源码 AlmostSureBackgroundPerturbation.lean：SHA256 653589d66e7eabc454f6476509d4029c5772fd31483e6ce49bafb2328bc2246c，7371B，162LF。完整冻结HEAD流39LF，固定裸RHS流19LF，完整6proof流81LF。上述源级声明数不是未来Lean实际owner/generated常量数；后者尚未审计，不能预填。

源码由冻结PRE+LF、按冻结顺序逐项HEAD+RHS或HEAD+PROOF+LF、冻结CLOSE精确串接。每个HEAD、两项RHS、PRE、CLOSE在源码中的UTF8字节切片与冻结component逐项相同。两个def的HEAD已经含outer :=，直接接原裸RHS；没有插入第二个separator。六个theorem的proof component从 := by 开始，未改数学HEAD。DECLARATION-BYTE-MAP.json记录每项的零基字节区间、所属源行、完整component哈希与计数。对应单项HEAD/RHS/PROOF文件、ALLHEAD、ALLPROOF、FIXED-RHS、PRE/CLOSE均已给出。

声明顺序是D01 sampleEnvelopeEvent、D02 sampleBackgroundBounds、T01 coordinatePair_measurePreserving、T02 ae_sampleEnvelopeEvent、T03 measurableSet_sampleEnvelopeEvent、T04 sampleEnvelopeEvent_probability_one、T05 backgroundBounds_of_mem_sampleEnvelopeEvent、T06 ae_sampleBackgroundBounds。无额外声明、前提或新helper；局部have仅在原6proof内。T01为唯一private源定理。

## 2. 来源忠实性与共同对象

复用已完整读取的p41/p51与父设计280。p41 §2(4)-(5)要在真实iid样本上应用乘积包络，但总体PE只在μ.prod μ几乎处处成立。本单元把这项AE前提绑定到真实Pₙ=Measure.pi(fun _:Fin n=>μ)的同一事件，再消费278的有限代数结论。原条件投影/均值方差等概率依赖没有因此闭合。

D01原样固定E={x|(∀i,0≤w(xᵢ))∧(∀i j,i≠j→|r(xᵢ,xⱼ)|≤w(xᵢ)w(xⱼ))}。这里Ω为任意可测空间、μ为概率测度，n任意自然数。i≠j是指标条件；从不假设xᵢ≠xⱼ、非原子、可测单点、标准Borel、对角r=0或点态对称。残差原对角值与重复观测均被保留。

D02原样固定事件内的∀v:Fin n→ℝ ∀B:Finset(Fin n)结论包。真实有限数组是rₓ(i,j)=r(xᵢ,xⱼ)、wₓ(i)=w(xᵢ)，v完全任意。来源g的实际取值只需实例化v(i)=g(xᵢ)，不引入Eg=0/Eg²=1/g可测等无关假设。

## 3. 六项完整证明路线与实际调用

T01（源43–59行）先对Ω恒等函数使用钉死iIndepFun_pi，得Pₙ下所有求值eᵢ(x)=xᵢ相互独立。以hij:i≠j取出两坐标独立，并给map_prod_eq_prod_map_map提供两个measurable_pi_apply的AEMeasurable。Pₙ的概率测度实例给该接口所需有限测度。联合推前先等于两个边缘的乘积；分别用measurePreserving_eval.map_eq把两个边缘改成μ。两个求值取有序对可测，合成实际MeasurePreserving pair Pₙ (μ.prod μ)。没有以“独立”一句话替代推前等式，也没有调用其他模块的private/local hPair。

T02（源61–86行）把hw分别用单坐标求值保持测度的QuasiMeasurePreserving.ae拉回，得到每个i的AE权重非负。对每个i,j，若i≠j，用T01的同一AE拉回接口取得实际r样本包络；若¬(i≠j)，蕴含逐点为真，Filter.Eventually.of_forall封闭该分支，完全不约束r(xᵢ,xᵢ)。Filter.eventually_all先合取有限坐标，再两层合取有限有序指标对。最后filter_upwards在同一个x上合并hWAll/hRAll，恰好构成D01。基础AE定理没有r/w可测性隐藏参数；QMP.ae接受任意Prop的AE事实，不自动宣称该Prop对应集合在原σ域可测。

T03（源88–107行）明确且仅使用冻结的Measurable(uncurry r)与Measurable w。E被展开为坐标非负条件与不同索引包络条件的交。Set.ofPred_forall把全称条件写成iInter；对蕴含的证明索引再作一次iInter。每个权重集合由measurableSet_le const (hw.comp eval)可测；每个残差集合由可测坐标对复合uncurry r、取绝对值，再与两个坐标权重乘积比较而可测。Fin n及命题证明索引满足相应Countable要求；等索引时蕴含的索引空，得到全空间。没有要求Ω相等关系/对角集合单独可测。该实现使用已接受SparseBalancedEvent中同版Set.ofPred_forall/iInter语法作为API示例，没有消费它的数学结论或重审其旧证明。

T04（源109–123行）先调用T03给出真实E可测，再用钉死MeasureTheory.mem_ae_iff_prob_eq_one将T02的E∈ae(Pₙ)转换成Pₙ(E)=1。此接口完整上下文为任意可测空间与[IsProbabilityMeasure μ]；Pₙ的实例由有限产品概率测度提供。第二个结论展开Measure.real并把hE代入，使用ENNReal.toReal_one得到Pₙ.real(E)=1。AE与可测性分别支付；没有把AE直接当可测集合。额外完整来源HEAD/上下文及其Mathlib pin记录于SUPPLIER-COVERAGE.json。

T05（源125–147行）首先在给定x∈E时展开D01，取得逐点hxW/hxR，然后才unfold D02并引入任意v和B。第一项精确调用278.anomaly_pair_envelope_bound B rₓ wₓ hxW hxR，给|F_A|≤ℓ²/2，不要求n≥4或B非空。给定hn:4≤n后，在每个i∈B调用278.adjustedRow_sub_backgroundRow_bound B v rₓ wₓ hn hxW hxR i hi，给原n−2分母的行差。进一步给定hm:3≤cardB后，调用278.background_centered_norm_perturbation B v rₓ wₓ hn hm hxW hxR，给系数1中心化范数界。所有参数、量词、原始n分母及半系数逐字匹配已读的实际完整TYPE；不复制旧有限证明。

T06（源149–158行）在T02的同一个AE样本x上附加T05，返回x∈E∧sampleBackgroundBounds n r w x。全部v/B在固定x∈E后点态量化，没有对不可数v作AE交，也没有先固定B后偷换为全体B。任意全样本选择器S可逐点取B=S(x)；这不声称S、g、所选统计量或其事件可测，也不证明任何选择后条件分布或尾概率。

## 4. 边界逐项核对

n=0/1仍有合法Pₙ与共同事件；有限AE合取允许空指标族。不同索引映射即使产生相同观测值也由实际μ.prod μ推前控制，不需删去重复样本或改残差对角值。原w≥1若AE给出可显式推出hw，本实现没有擅自升级为处处。

D02第一项对全部n/B有效。行差只在n≥4且i∈B时结论化；范数项另外保留card B≥3。B=∅时行条件空、范数前提不成立，半系数界仍有效；B=univ时A空、ℓ=0，得到零扰动。Q_b=0、s_B=0、Q_w=0均不导致新除法：范数差只用非负平方根，未除以Studentizer或能量。

行分母固定((n:ℝ)-2)，背景Studentizer沿278对应缩放核h_B=g+g′+((cardB−2)/(n−2))r。未把分母改为cardB−2。有限cardB≥3不冒称物理m=3统计量推广；未qualified279的B→Fin(cardB)物理重标号不作为供应。三个被消费的界无需对称；没有增加无消费者需要的278 T10完整分子恒等式。

## 5. 精确供应与证据复用

SUPPLIER-COVERAGE.json绑定精确278 qualified-evidence a5f3c16017165189da76dd7691b9ff10c3200eba203541dce25fe21a017054c1 /18854B、源码8481562684fc7a3c5455e8ab99d6f85b15f4778860fa414da93099b83b4adcb8 /30148B、首次原对象fbd3913b99528f0e63e8301180570ff9c7c0b95af37a4eff6509e9e52003149c /1519024B。原完整独立审查/native03 RC0/同原对象AX RC0及strictWrapperSuccess=false/16warnings的诚实记录均复用，没有重跑或改写。

完整12个actual TYPE（3个消费定理+9个定义）和9个非定理完整VALUE阅读覆盖来自已绑定旧证据；新author目录保存这些未省略文本的字节副本。7组原钉死Mathlib HEAD/context证据也原字节复用。新查的mem_ae_iff_prob_eq_one只为T04提供完整实际API，不引入数学前提。附加本地API读取有独立SHA/bytes记录，没有网络获取或工具链探测。

## 6. 实施状态、历史与后续门

仅本author-01写域新增文件。原proposal-01整树（含其初LAST后六文件追加现场）、新syntax proposal、freeze、library和其他owner目录全只读；没有删除、回写或追认旧scope的noWriteAfter。当前实现遵守新的冻结字节，历史修订不再影响数学签名。

纯文本guard只核源文件UTF8无BOM、LF/单末LF、冻结component切片/顺序/完整重建、8声明/6proof计数、2def唯一outer:=、禁用标记及所有交付绑定。它不证明Lean可解析、可定型或内核通过。新来源独立SOURCE/语义审查、未来服务器native与所有实际owner TYPE/VALUE/传递公理审计均尚未发生；不能预填accepted/qualified或新actual-owner数。

所有来源边界保持：条件真第一投影、核均值/方差、r_R典范化误差、p41(3)几何、交互集中、rareblock积分及大K/Q付款、外部hSZ/hSZC、PE-L/NR/DC、无条件PE-R/完整OQ56/root仍OPEN。原α_p=2(p−2)/(2p−1)范围不变；276任意α条件全窗不能偷换成原无条件结论。

本作者在封存后释放全部active及dormant写入/执行/发布/子上下文权限，不保留后台继续、排队任务或活跃等待。后续只有父级在实际新授权下安排独立审查/服务器阶段。本文不是持久继续机制。
