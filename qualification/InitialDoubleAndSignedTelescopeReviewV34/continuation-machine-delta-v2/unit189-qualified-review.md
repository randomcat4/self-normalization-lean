# 单元189：证明差异与实际机器证据续接审查

STATUS: CORRECT
QUALIFICATION: QUALIFIED_EXACT_SOURCE_UNIT189

本资格只绑定 InitialDoubleCompletionKernel.lean 的 f695b419dad97a83bf73c98fba8d68b457afbfad190cc1e0fe6f4a8a2655e58c，39053字节／835行，以及本报告所列内核对象、公理审计、完整实际类型与定义值。190、191没有因此获得机器资格。C2/C12仍为OPEN。

## 保留的完整审查与差异边界

原 full-review.md（2cabd00b6cfde27c55587c684c890d9905ed2455b840ebda8839a079d169c3fe）、full-review.json、21payload SEAL（5b81bed5a13bb5c4a0f6f000f363ecc50023f9a683b51f0fc56222b712627c32）、RELEASE（ad8f144b0aaa05f958f87fe931064a43f706ce30f0db017836b0e4abbccc5c5c）均未改动，重新核对21payload PASS。父的 parent-static-intake.json 已在任何候选修改前完整消费原11906字符报告并验证原17输入。本轮按授权只写 continuation-machine-delta-v2；没有重做未变2006行源码或已接受旧证明审查。

源链逐字节绑定：

- kernel001：826f8a4d10c44727380e58a40e2af878f123763debaf4bc762ccab439f726814。
- kernel002：2f38639174a6a70086c4a6d1dbac35986ce1beed3ac849c9764ac1114b3b460a。
- kernel003：e1249233779c39fd8c1bbd3c6be7373fc85eac2d0af0913539af85ada44653d2。
- kernel004／当前冻结复核源：f695b419dad97a83bf73c98fba8d68b457afbfad190cc1e0fe6f4a8a2655e58c。

重新生成的三份相邻统一差分与保存的 repair002／003／004 diff 完全相同。16个声明头、完整开头context、唯一doubleCompletion透明值与kernel001逐字相同；无新增全局helper。变动仅在5个private证明和1个public证明，另外9个private证明逐字相同。证明作者002已经zero-writer释放，003／004由父作者修改；本独立角色未修改候选。

## 逐项证明差异审查

1. doubleCompletion_eq：使用反向 Set.compl_eq_univ_sdiff，将univ\A还原为Aᶜ；Set.mem_sdiff替换旧membership别名。包含排除的同桥事件、测度及结论没有改变。实际生成_simp_2、4、5、6完整类型也分别是univ差集补集、差集membership、交集membership、补集membership，不是目标额外假设。
2. doubleCompletion_exterior：sub_eq_add_neg统一负端点代数；原w≤-x分支仍含墙等号和同一反射指数，证明意义相同。
3. variation_add_le：abs_add_le是本版本三角不等式的实际生成名；证明仍逐partition使用|a+b|≤|a|+|b|，没有削弱总变差目标。
4. variation_le_of_pointwise_limit：tendsto_finsetSum带显式Finset.range n，正好把每个edist的极限提升到有限partition和；没有引入一致收敛假设。
5. initial_geometric_series_budget：add_le_add le_rfl hfinite明确保持左侧2r，避免函数参数推断歧义；级数、prefix与6r／8r预算未变。
6. actual_initial_double_completion_kernel：明确change实指数及外层函数形状、显式传入hsub／variation_add_le函数和集合、嵌套add_le_add的le_rfl，均只固定原有同一函数／不等式的 elaboration。负号代数和三角不等式名称同步更新。003先将r^k按hexp还原为指数再做neg_mul规范化；移除no-progress dsimp只因前一操作已展开局部let，不删除数学步骤；monotoneOn／antitoneOn显式传Set.univ。004仅为min／max中未改变的第二参数标注(-x≤-x)或(x≤x)，固定类型推断。原全像tail、墙上S_N=r+s_(N+1)、全局F-L-R、两个tail及10r变差结论完整保留。

固定原生证据完整消费 repair002-native-readonly-002.json：Set.lean哈希9da12d237105504533571f9ebbe30ba15821d532854523e73b36c3345961461d；Unbundled/Abs.lean哈希574421adeb1391adcc9008c7e4a7981b2b444416f5d63ecf3ec48a4454851463；Topology/Algebra/Monoid.lean哈希b92c681b0f32e9a46b0959f845ee21f67a64af2ede2f1d8b34098371250410e6。完整生成头给abs_add_le及tendsto_finsetSum的正确数学接口。当前kernel004实际成功进一步排除了这些调用未被接受的疑虑。

结论：六个变动证明的独立差异审查CORRECT；与原完整source→statement审查复用部分拼接后，对kernel004精确源的全部作者源码审查覆盖完整。没有改变任何冻结数学假设、量词、definition value、版本选项或原题范围。

## 实际机器收据与全所属声明

kernel004-exit.json实际kernelExit=0，sourceSHA256与sourceAfterSHA256都为f695...，sourceUnchanged=true，08:32:08–08:32:24Z；对象为c60a4c694fb78cf0d31fcd5b5a4b3d2734958bd124d9c59d67f1016ba2bed93b。object-copy-map.json对同一对象进入实际worktree import路径验证true。189-kernel004-dispatch-intent.json绑定同一源及已有C12/OQ56 phase、c12-heavy.lock、CPU44–47、native-M8192-j4，没有新门禁包装或重放旧成功检查。

audit-exit.json实际exitCode=0，source为同一f695...，对象也是c60...。实际执行的OwnedAudit.lean哈希3dbbd9434ae26954f508d3b718c6e4a03e3af9c3b2eda295ec1323d18dcc75bc，完整读取其选择逻辑：用env.getModuleIdxFor?得到defining-module owner，筛选owner==target；没有按名称前缀筛选。每个实际constant调用Lean.collectAxioms递归收集并拒绝白名单外公理；public target数必须为1。owned-audit.json的实际哈希等于audit-exit所记ownedReceiptSHA256=2b3adb7ba6fb49e46c01489a4f7f714921d06042e34d105eafc111db5ae4afdd。

实际owner map为24项：23 theorem、1 definition、1个冻结public target。它由14个作者private theorem、1个作者public theorem、1个def以及8个实际生成theorem组成。完整type header名字集合与owner map逐名唯一相等，未遗漏private、generated或foreign namespace项。每一项的递归公理集合都只含propext、Classical.choice、Quot.sound的子集；没有新公理、sorryAx或其他例外。对象／审计／源／日志／ownedreceipt的交叉绑定已全部验证。

日志有mathlib repository localchanges警告及未使用／不可达tactic等linter警告；收据仍为自然rc0，未以警告当失败，也未因此重跑。固定view与未变旧依赖证据沿用原完整审查和项目既有接受链；这里不宣称工作区clean。旧kernel001／002／003的失败保留为失败历史，未被本次成功覆盖或冒称成功。

## 完整实际类型、唯一实际值与无损覆盖

原始actual-types-values.txt是完整119516字节payload，哈希c627875a673faedaea3018f6c852bd28b8f161e185ab0b81c080eebab190a236；来源audit日志哈希fbbd19bc9cb7499aa548bb1622c423883fdc9b052e0a6a037c99780c4b7393e0，与audit-exit一致。原byte offset index的25块长度、边界与SHA256全部重新验证。24个ACTUAL_TYPE、1个DEFINITION_VALUE均完整读取，无截断符号。

为避免反复展示相同的拓扑／可测实例和数值实例，生成16个精确重复子表达式字典，完整读完字典的7718字符及所有25个压缩块的26549字符。每条字典展开保存全部原生显式表达式，变量与universe参数没有摘要替换。独立保存原空白位置表，展开再插回空白后，原始119516字节完全相同，SHA256仍为c627...。这不是只读类型摘要：全部实际表达式均由压缩块＋完整字典覆盖。可复验材料为189-full-types-lossless-dictionary.json、189-full-types-lossless-blocks.json、189-full-types-lossless-whitespace.json、189-lossless-roundtrip-validation.json。

逐块核对结果：

- 14个作者private的实际TYPE逐项与原冻结head一致，包括全无限tail、所有概率／Brownian／x及w前提、变差与可测性；无暗加目标假设。
- 唯一public实际TYPE恰为原冻结的任意Brownian实现、x≥1、f=同一bridgeLaw下doubleCompletion、r=exp(-4x²)，以及Continuous、0≤f≤8r、TV≤10r、两无穷远tail的完整合取。
- 唯一def实际TYPE是任意Measure BridgeNoise→x→w→Real，没有额外IsProbabilityMeasure参数；完整VALUE确为同一个nu的strictUpper(x,0,1,w)补集与strictLower(x,0,1,w)补集之交的real measure。实际BridgeNoise可测实例完整展开为连续路径子类型及两个零端点，与原旧值一致。
- 四个_simp_生成项的完整TYPE是上述集合逻辑等式；三个_proof_生成项的完整TYPE分别是对n的1≤n+2、1≤n+1以及1≤1否定导致False，都是实际自然数辅助命题。类型没有承重数学结论被改写的余地。
- Shao.C2.IntervalImageSpatialConvergence.spatialTailBlock.eq_1虽然名称属于旧命名空间，实际owner明确是本模块，所以纳入24项。它的完整TYPE为对所有j,a,z,T,y,n展开spatialTailBlock的四个iteratedDeriv项，整数指标精确为n+2、-(n+2)、n+1、-(n+2)，与已完整审过的旧透明def完全相同。旧def源码哈希从原consumed-project-values绑定继续保留；本轮不重审其旧证明。这个新生成equation theorem的实际递归公理同样白名单PASS。

## 190／191的有限续接状态

已在精确历史快照上独立核对190从c923...到68363...的一行abs_add→abs_add_le，数学上保持原三角不等式；该68363候选的kernel001随后自然rc1、无对象，它不是当前最终候选，也没有资格。没有将正在修改的190 current文件当冻结输入。后来的repair002候选另需最终source binding与实际机器收据，不能由本次API差异阅读直接晋级。

191从044b...到cb53...的一行Set.univ_diff→反向Set.compl_eq_univ_sdiff在保存的原始快照上精确重建并匹配通知哈希；它保持概率包含排除的集合等式。此仅关闭已通知的一行证明差异审查，191完整机器资格仍pending。

本独立角色本轮没有Lean／AX执行、候选修改、上传、发布或代理。请求配置继续为gpt-6.1-sol/xhigh；实际后端／模型／effort与input、cachedInput、output、reasoningSubset各自不可观察，仍分别null。189可按本包独立接受；后续190／191继续同packet补实际type/value/all-owned-axiom及其真正变动证明，复用未变完整阅读。C2/C12仍OPEN。

