# PR306 独立完整最终审查

STATUS: CORRECT

本结论只适用于 `Shao.Probability.SourceOriginalIIDIntervalBudget` 的精确 138 行源版本，SHA256 `d9e1614dad773d65e6caaccc495d911e12210ca661f4139991b97719635f6947`，及原成功对象 `1c5fa0cbe5855226b3a4174c7372ba6934a52627fc2c9f2d66694a6559cd8ef6`。唯一新公开定理完整证明了冻结的原 AE iid 家族、同一独立均匀标签种子的实际区间 retained 与负 small overshoot 联合预算。没有关键数学或证据缺口；本审查不执行合并或代替 Root 资格授予。

审查者为 fresh 非作者 `/root/original_iid_interval_budget_final_review`，作者为 `/root/permutation_reveal_candidate`。遵循 math-theorem、AGENTS、SERVER 和 streamlined acceptance；未使用 math-ultra、未派子代理。调度要求 gpt-6.1-sol/xhigh/fresh；运行时实际模型/effort 和分项 usage 不由工具暴露，JSON 对这些不可见值分别保留 null，不估算订阅百分比。

## 精确范围与冻结

完整读过：候选 `source-scope.md`、`proof-candidate.md`、`candidate-declarations.lean.txt`、`downstream-interface-gap.md`；冻结 MD 与完整冻结 Lean 文本；新源全部 138 行和全部证明；实际导出全部 613 行（50519 bytes）的两个 TYPE、一个完整非定理 VALUE 和逐名递归 AX。另读取原 `main.tex` 869–1101 与 `supplement.tex` 4534–4600 相关语义，以及实际消费定义/头；旧合格证明按原资格复用。

冻结文件 SHA `bf47307a753c8c347cd0b6e4068b3c05589b8c43b97af18afd9082deb31cf0b9`，冻结 MD SHA `66c4837372cdad9e63b5d91b67ada147b649dc5231d0e4ae683793868a618cff`，激活 SHA `6580421a7ebcd96cf9e51fbcb4bd950c186a4e0fb9e451f5c7090c72c9e50c0c`。从 local instance 到完整公共头的字节段完全相等（仅去除段外首尾空白；段 SHA `946c9cd8dd72a6e93cab6cd400651fbf1a8066cc9188400a3d5ab6f01a20253c`）。12 个完整 literal lets 依次为 population、rawEnergy、rawTerminal、sigmaSq、scale、normalizedLaw、R、h、nu、jointLaw、L、O；没有新 source defs/private/global helper。新源为 UTF-8 无 BOM、LF-only、7749 bytes；禁用 token 检查为空。

## 逐名声明、值与公理评价

1. `Shao.Probability.SourceOriginalIIDIntervalBudget.labelPermMeasurableSpace`：source 17；actual export 1–29（TYPE 在 4，VALUE 在 6–29）。完整类型是 `(n : Nat) → MeasurableSpace (LabelPerm n)`；完整展开值为可测空间完备格的 Top，恰是冻结的 `⊤`。它使有限排列种子取全部集合可测，与既有 uniformPermutationLaw/revealLaw 的实际可测结构定义相容；未给任意 Ω 增加结构。递归公理精确为 propext、Classical.choice、Quot.sound，合格。

2. `Shao.Probability.SourceOriginalIIDIntervalBudget.original_iid_actual_interval_retained_negative_budget`：source 19–135；actual export 30–613（TYPE 从 33 至末尾），全部阅读。实际 elaborated TYPE 保留任意 universe 的 Ω 和任意 MeasurableSpace，只要求 X_i 对 mu AE 可测；实际 iid、共同原 rho、有限二阶矩、中心化、正二阶矩、原噪声概率测度和全部解析前提均与冻结一致。Csmall 在先，同一个正 C 在 Ω/mu/rho/Q/n/X/x 之前；不依赖这些后量词。actual TYPE 的全部 12 lets、六部分结论及实数 Bochner Integrable/积分均与源一致。递归公理精确为 propext、Classical.choice、Quot.sound，合格。

owner-index 审计扫描精确模块的所有常量，包括 private/generated；实际只有上述 2 名（1 theorem、1 local-instance definition）。没有被遗漏的新生成常量、其他非定理值或新公理。实际类型和值导出没有省略标记。

## 全部证明与 source-to-statement 核对

- 72–79：先从精确 canonical producer 固定 C，再引入所有原空间及原样本，因而普适常数量词顺序正确；hReflection/hRegular/hSmall 原字面传递，没有偷加目标预算、pushforward、可积性或高矩前提。
- 80–92：P 为原 rho 的有限乘积；lambda 为真实 uniformPermutationLaw；Phi(omega,sigma)=(samplePath X omega,sigma)。它保留未重排的完整人口及同一个 seed。population 的 AE 可测由逐坐标 AE 可测和有限乘积可测结构给出，不选择 everywhere 可测版本，不要求 Ω 完备。
- 93–105：rawEnergy 等式定义相等，rawTerminal 由 prefixSum_length；两者对每个 omega 成立。`iIndepFun.map_fun_eq_pi_map` 的实际已钉死库头接受 AE 可测，结合每个 IdentDistrib.map_eq 导出人口推前等于 P。没有把 iid 排列路径的边缘律冒充人口和 seed 的联合律。
- 106–113：AE prodMap 给 Phi AE 可测；`Measure.map_prod_map_of_aemeasurable` 的实际头对右因子只要求 SFinite，这里真实 uniform 概率测度满足。由已证人口 law 和 id 的推前得到 `map Phi jointLaw = P.prod lambda = revealLaw P`，方向经 he.symm 正确，再构造完整 IdentDistrib。无目标 law 前提。
- 114–118：调用 PR302 的完整 canonical 头，使用相同 rho/n/variance/normalization/R/h/x，以及相同实际 eventCompletionKernel、intervalDerivative 和 energyCutoff。其全局可测 cutoff 经 population AE 复合给逐 seed 的原 cutoff AE 可测；没有自然 iid 滤过停时声明。
- 119–130：S0 的可测性由有限和、abs、neg、max 组成。对全部自然数 r，L/O 与 L0/O0 经 Phi 的复合逐点定义相等；IdentDistrib.comp 同时给原 joint AE 可测性和真正 Bochner integrability。`integrable_iff.mpr` 的方向是从已合格 canonical integrability 搬回原 jointLaw，没有用不积函数的默认零积分逃避预算。
- 131–135：同一 S0 复合给联合非负有限和的真正 Integrable；integral_eq 给精确积分相等，再接既有 canonical CR。不是仅给边缘概率或形式积分数值。

原文 retained 与 negative overshoot 两个目标由更强的联合非负和预算覆盖。原总能量、终和、真实随机墙、剩余平方和、原 κ、活跃/terminal 指标和投影分支全都在逐点复合中原样保留；没有替换成代理状态、确定方差或改变样本的零集值。

边界核对：n>0 只排除 n=0，n=1 的 range n 只含 r=0；r≥n 的源 L/O 原定义为零。x=0 时 sourceAlive.interval 包括 prefix 0 的严格壁检查，故对全部样本 L/O 恒零；这不等于原 positive-prefix CDF 事件恒零。原 raw energy=0 由 sourceAlive 的正能量 guard 归零。墙相等和 terminal 原子仍受严格 interior 条件处理；相等小步 b²=T/2、选中 T=h、未来 T-b²=0 的 totalized completion 均保留原源值。重复数值不合并 Fin n 标签，seed 未被替换或条件化。噪声测度 Q 的实际解析前提保留 all-beta、闭未来墙 `|y+beta|≤w`，并非 Gaussian surrogate。

## 已合格依赖与证据绑定

PR302 Root 资格文件 SHA `6324851d1dabbfbcb6ba48dbc79251cf9a9fccbaef841b33c6c7df4669dd7ab8`，对精确 source `58eef62954931c95be1228accb921de6db3092a4d681184d6e1fef4ab2d20ef6` / original object `e20a2a3de177ff66618c294b219643a1f041e7ccb7a22f703e026fe33af97dbc` 允许 source-bound consumption。其 source、owner map、MD/JSON 完整独审、作者 receipt/RELEASE、审查 RELEASE 和原服务器绑定共 8 个直接哈希均匹配。本次完整核消费头、intervalDerivative 的总化完整值与新接口的相互作用，不另审旧证明或重编旧 producer。intervalDerivative 正是 interior guard 内实际 eventCompletionKernel 的 spatial deriv，guard 外零；新源使用同一个值。旧 SourceOriginalIIDHalflineBudget 的双半线资格不被借用为本 interval/O 结论。

服务器只读核验了源、Git blob、已安装对象、原 attempt001.olean、原 kernel/audit log 哈希、所有 receipt 指定 artifact 及原导入对象。安装对象精确解析到原 attempt001.olean；PR302 导入对象精确解析到原 attempt007.olean。全部实际 TYPE/VALUE 导出 50519 bytes 与原 owned-audit.log 从 TARGET_DECL 到 AUDITED_TARGET_CONSTANTS 前的完整字节段完全相同。原成功 kernel rc0、原全 owner/transitive AX rc0 由精确作者 receipt 和对应原工件复用；审查新 Lean/AX/producer 编译均为 0。只读搜索遇到一次服务器 rg 不存在，已保留该观察失败并以 Python 搜索完成；这没有启动 Lean 或改动任何源。

Lean pin `leanprover/lean4:v4.36.0-rc1`；manifest 与实际 mathlib HEAD 同为 `807d3836b165983210ee2ecf3cd28f239436949c`；shared-v34 packages 解析、Mathlib Prod 源和对象哈希与 receipt 一致。未下载二进制、cache 或完整原日志，未写生产源或旧证据。

作者 receipt SHA `202684bf17a5c310f2816a4f508f1cea5a22638e44aa27e6597e10dd701e2868`、作者 RELEASE SHA `e03669b3ed77e5a9be84f3c8a9c198f0acd131424f2e1a1aec33e0e871280f41` 与本地/服务器完全一致，作者写权和执行权已释放、inflight 空。owned JSON SHA `2cdcca4276d1c6098a16236231389f86d3e48f521e409e29d362e5d393c31719`；完整 TYPE/VALUE SHA `44c49d33efc29d1299508e841401b71b7c71c239af46d864eb1814c556394852`。

Git head `44c707277c8edb5adcebadae6b988bf8b92e726e` / tree `f6662f808c4ef43d789f2187aa09d20548c5fb6e` / blob `d30d9a22d9c81d506d32260ea494e291456088e2`，worktree clean。GitHub 只读 API 确认 PR306 仍 draft/open/unmerged，head 完全相同，base main `927797d9d551e4b57e58abfaba7c7604f0cbcca4`，1 commit / 唯一新源 / +138 -0。未合并。

## 结论边界

这是完整、正确且 source-faithful 的原概率空间消费者；机械检查复用精确服务器 L2/L3 原证据，且本次自然语言到 Lean 的忠实性已审。没有新颖性主张，也没有对原论文全部根定理作完整证明声明。真实 hReflection、hRegular、all-beta/闭未来非 Gaussian hSmall 仍为 OPEN 上游；initial G、terminal E、物理 Brownian/image 概率识别及全部原 C12/OQ3/OQ4/OQ56 根仍 OPEN，OQ3 保持 PAUSED_BY_USER。有限局部预算不能替代这些未付依赖。

下一处理是由 Root 基于本精确独审和原收据作 source-bound 资格/集成判断，并继续既有实际 E/G/解析依赖；本审查者无后续生产或合并权。最终 reviewer RELEASE 将绑定本 MD/JSON、源、原对象、作者 receipt/RELEASE 和只读验证证据，审查写/执行权随之释放，0 inflight。
