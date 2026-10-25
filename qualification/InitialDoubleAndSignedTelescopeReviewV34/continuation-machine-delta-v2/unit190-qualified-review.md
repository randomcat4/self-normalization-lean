# 单元190：证明差异与实际机器证据续接审查

STATUS: CORRECT
QUALIFICATION: QUALIFIED_EXACT_SOURCE_UNIT190

精确源为a967e7a8afaab71cba0258ad41277606371696ac144829769088a8bfc5a1498f，37994字节／756行。资格只覆盖original_finite_second_initial_double_completion_budget及其本模块全部实际所属声明。它依赖已在本目录单独获资格的189精确源f695...／对象c60...。191仍待最终源码和机器证据，C2/C12仍OPEN。

## 原完整审查复用与实际差异

原完整full-review.md、json、21payload SEAL与RELEASE保持原字节，重新哈希PASS；UNIT189-SEAL及其全部payload也重新验证未变。不重新审查已完整读过而未变的新证明块或已接受旧证明。

对保存的原始c923fe29c04418935766f1a6213077f2850ab784027702fdef2f9048876c3728与最终a967...重新生成统一差分，和delta-from-static-reviewed-source.diff完全一致。13个源码级声明、11个theorem head、2个完整def value及开头context均逐字不变。改变恰为下列4个proof，另外7个theorem proof逐字不变，无新增全局helper或假设。

1. vanishing_bv_antitone_decomposition：把Iic／Ici共同端点的membership证据显式写为simp only [mem_Iic/mem_Ici,le_refl]，包括union的IsGreatest／IsLeast以及dist_le的端点。它们只是w≤w，不改变两尾零条件、prefix／suffix变差或半TV范围。所有Jordan公式和真实可积性保持原样。
2. normalized_nonzero_support_lower_bound：显式建立hfm:Continuous(fun z=>truncationF((1+x)*z))，使用已有continuous_truncationF与连续线性函数复合，再传给integral_map。它没有假定所需measurability，而是从旧合格透明核和已证明连续性提供。删除的rfl由实际rw的定义化简已完成。hi的change仅展开既有Y²及h²I+F(Y)/h的积分形状；两侧真实integrability仍由原hY2、hI和hF支付，不改变pointwise support split、b、h或n*pi下界。
3. actual_brownian_initial_double_integrals：用hsection的congrArg明确得到相同集合的real measure相等；闭切口部分显式change经beta展开的section表达式后进行原有w≤v分支。两个事件仍用同一个B、同一个bridgeLaw，末端仍是B1≤v，没有换成独立事件、严格切口或抹去原子。
4. original_finite_second_initial_double_completion_budget：单列hEI给真实one-indicator积分等于P.real E，再在已由真实integrability允许的integral_sub和norm转绝对值后使用；从而完整支付P(Q=0)。abs_add_le取代该版本不适用的旧abs_add名称，表达同一三角不等式。R0≤b、10r／18r变差、恒定C的先后量词、两个目标误差以及所有原假设不变。

完整差异阅读结论CORRECT。旧完整source→statement审查覆盖未变部分，本轮覆盖真实差异和相互作用，因此最终a967源的完整作者数学审查已闭合。历史68363候选及其kernel001自然rc1、后续修复失败均是保留的失败历史，不能替代这次最终收据；没有重放旧成功检查。

## 精确机器与所属声明证据

kernel004-exit.json记录实际kernelExit=0，08:40:44–08:40:56Z；sourceSHA256和sourceAfterSHA256都是a967...、sourceUnchanged=true。对象为75b3b13956b8141fa027e906d398c4aac0ff6a78a9ca1b1a41d9ea6901cf4438；object-copy-map对该对象进入同一worktree标准import路径验证true。

audit-exit.json实际exitCode=0，源仍a967...，对象仍75b...。完整读取实际OwnedAudit.lean，哈希1c6532b4119b92151248a20dd172c9f65e92301d327afc1482f4730aced411e4；它按实际defining-module owner选择全部constant，对每项调用递归Lean.collectAxioms并拒绝白名单外项。owned-audit.json实际哈希22e3c24414d004e830b9b19146e7575bdf1b5577a167ae23c732b220e55cbfc8与audit-exit相等。

实际所属声明为27项：25 theorem、2 definition、1冻结public target。13个作者源码声明之外有14个实际生成theorem；完整TYPE header的27个名字逐一唯一，并与完整owner map集合相等。每项递归公理都是propext、Classical.choice、Quot.sound的子集。没有遗漏private／generated，没有namespace前缀过滤，也没有把描述计数当实际owner计数。

## 全部完整实际TYPE／VALUE

actual-types-values.txt为69198字节，哈希d63c6832d336f8099e7026aa6b5acb131a307bd7f0843fd88c9e3546beed636e；原日志哈希a8bac88bd3e29bd6977044fd90232415da15b5b97cacf961f93423bc22f34c45与audit-exit相同。原index的29个block边界、长度及SHA256全部重新验证；27个ACTUAL_TYPE、2个DEFINITION_VALUE完整读取，无省略符或截断。

本轮使用17项精确重复子表达式字典；完整读过字典3691字符与29块压缩表达式29535字符。保留原空白表，字典全部展开并复原空白后与原69198字节完全相等，SHA仍d63...。每个universe、显式instance、量词、分支和逻辑连接均保留，没有用类型摘要代替阅读。材料为190-full-types-lossless-dictionary.json、190-full-types-lossless-blocks.json、190-full-types-lossless-whitespace.json与190-lossless-roundtrip-validation.json；逐block/source合同覆盖在unit190-all-owned-type-value-coverage.json。

实际类型／值核验的关键结果：

- 10个private及1个public TYPE与各自冻结head完全一致。support bound和zero-energy指数保持真实归一化map z/sqrt(n)、b=truncationBudget及原有限square前提；没有暗加full third moment、bounded support、symmetry或atomlessness。
- public TYPE保持存在正C在rho、n、Ω、B、x、v之前；rho为概率测度、n>0、真实平方可积、均值0、EX²=1，B为调用者给出的同一IsBrownianReal实现，x≥1且b≤1/2。它同时给Z的真实可积性和初始双弱击中比较，并对每个v给if W≤v then Z else0的真实可积性及真实事件brownianInitialDouble∩{B1≤v}的误差；两误差都是C*b*standardNormalTail x。
- initialDoubleObservable的完整实际VALUE明确是energy a=0时1，否则同一nu的189.doubleCompletion在normalizedEndpoint处求值；没有把零能量分支改为0或小sup。
- brownianInitialDouble的完整实际VALUE是在同一omega和同一B上分别量化两个存在时间：∃t,x≤B_t，以及∃t,B_t≤-x。它没有将两个时间强制相等，也没有引入另一随机桥。其生成eq_1完整TYPE精确展开同一值；_proof_1的完整TYPE仅是BridgeTime t的非负坐标，用于NNReal时间转换。
- 其余生成项的完整TYPE分别为union／Iic／Ici／univ、preimage／intersection／complement／empty的membership等式，not_forall与not_lt的真实逻辑转换，反身≤为True，以及实际energy=0当且仅当所有坐标为0。它们与原证明所用的原子、弱切口和零能量语义一致，没有额外承重结论。

## 当前边界

189与190现在都只有各自精确源的资格；不由初始double预算推断整个C2或C12完成。191的cb53单行原生API差异已在历史快照上审查，但首个kernel001实际rc1、无对象；父正在修复，不能读moving current作最终候选，也不能向其授予机器资格。

本独立角色无候选修改、Lean／AX执行、上传、发布或子代理。配置请求gpt-6.1-sol/xhigh；实际backend／model／effort及input、cachedInput、output、reasoningSubset各自未知null。接下来只对191最终精确差异及其完整实际owner/type/value/axiom收据续接，继续复用全部未变完整审查。

