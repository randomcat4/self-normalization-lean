# unit280 repair01：仅 T03 类型推断修复作者报告

状态：COMPLETE_AFFECTED_PROOF_REPAIR_NOT_SOURCE_ACCEPTED_NOT_KERNEL_CHECKED。完整8声明/6proof源码已重组；本次只改T03的完整proof。没有运行Lean、AX、编译、probe、SSH或网络。新SOURCE审查与native02由父级另行安排，当前不能宣称修复已通过机械验证。

唯一新写域为C:/game/shao lean/drafts/oq56/unit280/author-repair-01。ACT为86b91ec20f236b6ca05a632052b7406735dacde8b8fbb6f6130c60d46f73d2f5 /32471B；136输入与ACT共137绑定首写前全部SHA/bytes相符。ACT的PREPARED_NOT_DISPATCHED是历史准备标签，本次父级显式消息激活SAME作者。请求gpt-6.1-sol/xhigh；工具未暴露actual backend/model/effort或input/cachedInput/output/reasoningSubset，用null记录。

## 原失败与精确修复原因

原完整源码SHA653589d66e7eabc454f6476509d4029c5772fd31483e6ce49bafb2328bc2246c /7371B/162LF保留不变。native01自然结束actualRC1、未超时、owned group全部结束，preservation exact、无对象；唯一归一化错误在原T03源码L106C20，Measurable.comp hr接收的pair-measurability实参未能统一为预期的Measurable ?m.115。原收据bb0fc3f0555a3ff1dac81335e0f67461a70aa617fb413dafe2e548489cf877ea /39685668B及本地完整诊断继续只读保留，没有把旧RC1改写成成功或重放不确定命令。

本次读取了已有本地钉死API包。Measurable.prodMk与measurable_pi_apply的完整HEAD来自Mathlib.MeasureTheory.MeasurableSpace.Constructions，源SHA03bdd1fd16c69f61acf8ae50d684f54c9b565d03c6fa880fc338fcbd3bbebadb。Measurable.comp确切HEAD为：protected theorem Measurable.comp {g : β → γ} {f : α → β} (hg : Measurable g) (hf : Measurable f) : Measurable (g ∘ f)。其Defs源SHA为bbb025056bb49e962516e9d495bbda6356251a19fde31544d820ecbe50894ecf。实际包哈希、来源与使用位置均在API-AND-EVIDENCE-REUSE.json；Mathlib pin仍为807d3836b165983210ee2ecf3cd28f239436949c。

## T03 的完整局部路线

保持原classical和整个事件/有限交结构。首先在T03内部引入hpair(i j:Fin n)，其完整类型显式固定为Measurable(fun x:Fin n→Ω =>(x i,x j))，由两个已可测坐标的prodMk直接给出。它固定样本函数域与Ω×Ω值域。

再引入hrx(i j:Fin n)，完整类型显式固定为Measurable(fun x:Fin n→Ω =>r(x i)(x j))。调用实际Measurable.comp时显式传g:=Function.uncurry r、f:=fun x:Fin n→Ω =>(x i,x j)，再传原hr及hpair i j。函数复合经β/δ化简就是r(x i)(x j)，不依赖对可测空间、乘积域或结果函数的未定元猜测。

最后引入hwx(i:Fin n)，完整类型显式固定为Measurable(fun x:Fin n→Ω =>w(x i))，使用原hw与坐标可测性。原权重交集中的比较改用hwx i；原pair包络交集中的比较改用(hrx i j).abs与(hwxi).mul(hwxj)。Set.ofPred_forall、MeasurableSet.iInter、指标i≠j的证明索引交及两个主集合的交全部保持原数学路线。

三个have都在T03 proof内，不新增顶层声明，不改变任何冻结类型、条件、定义或共同事件。完整新T03 proof为24LF，保存在T03-measurableSet_sampleEnvelopeEvent-PROOF.txt。没有新增r/w可测前提：使用的仍是T03冻结HEAD已有hr:Measurable(uncurry r)、hw:Measurable w。Ω仍任意可测空间；没有标准Borel、非原子、可测单点/对角、对称或对角r=0条件。

## 完整源码与字节变更边界

新完整源码AlmostSureBackgroundPerturbation.lean：SHA879eddc9a21eb422412cb70ec99ee34524ec821e67e4aac2c3fc074b758c5572 /7679B/170LF。新旧源码仅有一个连续变更区间，即原T03 proof的bodyStartByte0至bodyEndByte0Exclusive；该区间前缀、后缀逐字相同。新源码也按冻结PRE、8HEAD、2固定RHS、6proof与CLOSE重新构造并与单区间替换结果字节相同。相对旧稿仅增加308B/8LF。

8HEAD、2固定RHS、PRE/CLOSE全部逐字沿原freeze bcd298af759372f157cf955d255c4eb967c45e206a069073e1922e0058c14f5e /6889B。两个def HEAD各自带唯一outer :=，裸RHS仍直接拼接，没有新增separator。其余T01/T02/T04/T05/T06共5proof、60LF逐字相同，未重新著作、审查或检查。原T03 proof16LF只读保留。

完整源级计数：8声明、2定义、6theorem（5公开/1私有）、HEAD39LF、固定RHS19LF、proof component共84LF（新T03 24LF+其余60LF）、ALLPROOF聚合流89LF（含5个分隔空行）。未来实际owner/generated常量与传递AX数量仍未产生，不把源级计数当作实际owner计数。

每项UTF8字节区间、HEAD/body哈希与源行见DECLARATION-BYTE-MAP.json；单一变更区间、前缀/后缀哈希及5份未变proof见EXACT-AFFECTED-DIFF.json。完整source/ALLHEAD/ALLPROOF/FIXED-RHS/PRE/CLOSE和逐项component均已交付。

## 证据复用、边界与后续门

原完整来源阅读、冻结语义与不受影响的5proof SOURCE证据直接复用。T05及其精确qualified278 T12/T13/T19消费完全不变，原12完整TYPE/9非定理VALUE覆盖与原O/独立审查收据保留，不重审旧整篇证明或运行producer/leafAX。279不被用作供应。

T02仍只从总体hw/hr的AE事实产生一个Pₙ满测事件；T03仅为原E证明可测；T04两种概率一、T05半系数/原n−2/中心化系数1、T06事件内forallvforallB都未改。不同索引与重复观测的区别、任意残差对角、小n/空B/零能量边界、sample-selected B不自动可测的限制均维持。

本次纯文本guard核验单区间替换、全部冻结component/5proof字节相等、8声明无额外顶层项、2def唯一outer:=、完整source重建、UTF8无BOM/LF单末LF及禁止标记。它不是Lean解析/类型/内核通过，也不是独立SOURCE审查。新T03的受影响SOURCE及new native02仍待父级；旧失败和未变证据按精确哈希复用。

条件真投影/均值方差、交互集中、rareblock、原无条件PE-R/PE-L与完整root范围均保持OPEN，原αp及来源量词不变。没有做资源/日程/Goal或任何发布动作。

原source、SOURCE、失败、proposal/partial历史、freeze、library和其他owner均只读。封存后本次author-repair-01的全部active与dormant权限释放，六零、queued0、activeWaitfalse；不保留后台作者或等待执行。
