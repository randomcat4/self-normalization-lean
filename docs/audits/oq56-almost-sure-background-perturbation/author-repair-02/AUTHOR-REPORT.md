# unit280 repair02：T03 的范数转绝对值可测性修复

状态：COMPLETE_AFFECTED_PROOF_REPAIR_NOT_SOURCE_ACCEPTED_NOT_KERNEL_CHECKED。完整8声明/6proof新源码已交付，只修改T03完整proof。未执行新Lean、AX、编译、probe、SSH、网络、上传或发布；新native03及受影响SOURCE审查均待父级。

唯一写域为C:/game/shao lean/drafts/oq56/unit280/author-repair-02。repair02 ACT b00a67faf597d22d7daf733d3c3daa3bcc16dcf52ab55719583b62113f50cc95 /45677B与195输入共196绑定在首写前逐项SHA/bytes相符。请求gpt-6.1-sol/xhigh；actual backend/model/effort与input/cachedInput/output/reasoningSubset未由工具暴露，均null。所有旧source、SOURCE、失败收据/输入、freeze、其他owner均只读。

## 1. 已观察的两次失败与诊断提取

native01 actualRC1、noO、owned group自然全部结束、preservation exact，唯一错误为原T03L106的pair/Measurable.comp推断。原source653589d66e7eabc454f6476509d4029c5772fd31483e6ce49bafb2328bc2246c /7371B/162LF及收据bb0fc3f0555a3ff1dac81335e0f67461a70aa617fb413dafe2e548489cf877ea /39685668B保留。

repair01以显式hpair/hrx/hwx解决该推断；native02仍自然结束actualRC1、noO、allowned ended、preservation exact，当前唯一错误变为T03L115C35的lean.invalidField abs。原repair01源码879eddc9a21eb422412cb70ec99ee34524ec821e67e4aac2c3fc074b758c5572 /7679B/170LF及收据4678b78d355265bab0b96a1c111b5443d36ffdfcc8d4a378a943c733408c5814 /39749816B保留，不能把pair推断消失写成整个native成功。

native02的完整原stdout为a1e0712d4fb2104a2af97ca53e7760976c1c3c0d7dc980a9d83ffd27b2354414 /336B。v1归一化列表为空是提取器只接受bare error:导致的parser gap；v2包含Lean诊断代码lean.invalidField，完整错误只此一项，unparsedPrefix为空。v1、v2、原stdout和server receipt均保留，oldReceiptRewrites=0。本作者没有修改诊断提取器或原收据。

## 2. 实际钉死 API 与同版已接受调用

父级已完成的只读主源查询由native02-affected-abs-norm-primary-api.json cea7d15c24f35aa32df0dd0eb66ef217ea5a343ae5344ff46cf712e4dbba9321 /3746B绑定。实际Mathlib Metric.lean源SHA66e4b70ad7283f621495ad96d0329ba095bb71081a1c72a9bd25bee8f73e361e /10439B，235–243行的完整上下文是[MeasurableSpace α] [NormedAddCommGroup α] [OpensMeasurableSpace α] [MeasurableSpace β]；公开接口为Measurable.norm {f:β→α} (hf:Measurable f) : Measurable(fun a=>norm(f a))。

这里将α取ℝ、β取真实样本域Fin n→Ω、f取x↦r(xᵢ,xⱼ)。范数群与OpensMeasurableSpace要求仅落在标准ℝ值域；样本域只需既有Π可测空间，不要求Ω带拓扑、范数、标准Borel或非原子。原T03显式Measurable(uncurry r)/Measurable w两个前提保持。

已接受local callsite OriginalClippedStatisticMeasurable.lean SHA052fb7eb6bb1d17218bf47c6c4f5b6715561da68b022bdacf6835fee5d667103 /15983B第88–90行，恰以simpa only [Real.norm_eq_abs] using hf.norm把实值可测范数转成绝对值可测。完整接口上下文、specialization及该调用片段均保存于API-BINDINGS.json。此次没有联网、读取未绑定远端状态或运行API探针。

## 3. 完整 T03 proof 的唯一修订

保留repair01所有hpair、hrx、hwx与显式comp f/g类型实例化。只在hrx之后插入局部hrabs(i j:Fin n)，完整类型固定为Measurable(fun x:Fin n→Ω =>|r(xᵢ)(xⱼ)|)。证明先取(hrx i j).norm，随后以Real.norm_eq_abs作唯一simp，将结论化为原绝对值函数。

原包络有限交比较中的唯一表达式由(hrx i j).abs换成(hrabs i j)，右侧(hwxi).mul(hwxj)、坐标非负集合、主集合交、Set.ofPred_forall、iInter及i≠j命题证明索引交完全保持。没有改变E的绝对值谓词，更没有用范数谓词替换冻结声明。插入hrabs与替换最终调用的逆补丁逐字还原repair01完整T03 proof；因此不是其他T03路线的重写。

hrabs只是T03内部have，不新增顶层helper、前提、import、PRE、设置或定义。完整新T03 proof27LF，在独立文件T03-measurableSet_sampleEnvelopeEvent-PROOF.txt交付。T03的HEAD仍逐字冻结；其可测性证明与T02的AE前提区分不变。

## 4. 完整源码、组件与精确变更边界

完整新源码AlmostSureBackgroundPerturbation.lean：SHA563829d9aff516f085f33cfd197500464af53932bbcecb21065245f2349679f3 /7826B/173LF。相对repair01增加147B/3LF，仅一个连续T03 proof区间发生改变；区间前、后缀分别字节相同。单区间替换所得源码与冻结PRE+LF、逐项HEAD+(RHS或PROOF)+LF、冻结CLOSE的完整重构结果字节相同。

全部8HEAD、2固定RHS、PRE/CLOSE保持freeze bcd298af759372f157cf955d255c4eb967c45e206a069073e1922e0058c14f5e /6889B的原字节；两个def HEAD各承担唯一outer :=，裸RHS直接拼接。T01/T02/T04/T05/T06共5proof/60LF也保持原字节，未重复审查、实施或检查。

当前源级计数8声明、2定义、6theorem（5公开/1私有）；HEAD39LF、固定RHS19LF、proof components87LF（新T03 27LF+其余60LF）、ALLPROOF聚合流92LF（含5个分隔空行）。这些不是未来actual-owner/generated常量或AX计数；新actual TYPE/VALUE/AX尚未产生。

完整source、8HEAD/2RHS/6PROOF单项文件、ALLHEAD/ALLPROOF/FIXED-RHS、PRE/CLOSE已给出。DECLARATION-BYTE-MAP.json绑定每个UTF8字节区间与行号；EXACT-AFFECTED-DIFF.json记录唯一补丁、逆补丁、原/新T03及未变5proof哈希、两次失败和诊断提取历史。

## 5. 数学范围与复用证据

T01实际pair map、T02共同AE事件、T04两种概率1、T05精确qualified278 T12/T13/T19有限界和T06同一E内forallvforallB均不变。仍使用任意可测Ω/概率μ/真实Fin n iid样本，区分i≠j与观测值互异，保留任意对角与重复观测。

原SOURCE、12个完整实际supplier TYPE/9个完整非定理VALUE覆盖、精确278原O/独立审查/机器证据与未变5proof来源证据复用，不重新审查旧整篇证明、重跑producer或leafAX，不消费279。受影响的新T03完整27LF仍需父级安排同一独立审查者审阅；本作者自查不是独审。

半系数absFA、原n−2分母、中心化系数1、n≥4/cardB≥3边界、空B/小n/零能量与任意sample-selected B不自动可测的限制维持。条件真投影/均值方差、交互集中、rareblock、原无条件PE-R/PE-L及root保持OPEN，原αp范围不变。

## 6. 状态与释放

本地guard只核冻结/未变proof字节、完整source重构、唯一T03变化、禁止标记及UTF8无BOM/LF单末LF，不能证明Lean可解析、定型或内核通过。本次没有新native/AX/编译/服务器执行，也没有新的成功对象；sourceAccepted/kernelChecked/qualified均false。前两次RC1与各自无对象状态保持真实，不补写成功。

封存后author-repair-02全部active与dormant权限释放；六零、dormant0、queued0、activeWaitfalse，不保留后台作者。后续受影响SOURCE/native03由父级在相应授权下执行，本作者不继续写旧scope。
