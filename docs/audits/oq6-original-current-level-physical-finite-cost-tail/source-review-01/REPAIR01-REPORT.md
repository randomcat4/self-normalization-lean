# 261 repair01 受影响证明独立复核

结论：`CORRECT`，`sourceAccepted=true`、`qualified=false`、`machinePending=true`。本次只复核修复增量，复用本同一独立上下文已完整读取的旧 432 行源码与证明。未发现新增数学缺口；未声称新候选已通过 Lean。

当前精确源码 SHA256 `986ab611625c416e1b9c0e65f2603965aa034c89c502caa927a96b1418c8e766`，25460 字节、433 LF；PROOF 为 `733d1040ec2fc956d4a327f991568fd9ce5a037726a2acd31997afa0af135e31`，19457 字节、322 LF。旧完整审阅报告仍为 `887919dc4a32eec57ec478f4ec4a6bd274c055ac697831a35e1f61bce170a6c4`，未改写。旧 native01 实际自然 RC1、无对象、五项诊断及原始失败源码都保留。

已实际读取完整 NORMALIZED-DIFF、修复激活、失败诊断、作者 release／manifest，以及当前源码 105–125、285–315、350–376、423–433 行的全部相关上下文；另读既有承载用例 WeightedCostClipping 257–285 与 NormalizedAnalyticCostLimits 270–310。作者说明不作为独立判断依据。

1. 新 293／296 行（旧 292／295）分别保持 t↦t.2.1、t↦t.2.2 两个连续坐标投影及其完整目标 `Measurable[borel (ℝ×ℝ×ℝ), borel ℝ]`。把 `.measurable` 改成 `.borel_measurable` 直接使用连续映射对定义域／值域 Borel σ 代数的可测性，避免要求自动综合的 Prod.instMeasurableSpace 与显式 borel(ℝ×ℝ×ℝ) 定义相等。没有改为更粗可测空间或新增乘积等式假设。259 原 hFullFactor／hDeletedFactor 的值域本来就是显式 borel 三元组，修复后的两次 `.comp` 因而保持完整与真实删点标量因子的原类型。被删坐标仍排除在 `{j // j≠i}` 域外。已有合格源码 WeightedCostClipping 278–280 同样在显式 Borel 两端使用该接口。此处确认数学与接口选择；其实际 elaboration 仍由新 native 决定。

2. 新 366 行（旧 365）只把 `nlinarith [sq_nonneg (z*η k i x-1)]` 缩为 `nlinarith only [...]`。目标仍是 t−t²/2≤1/2；精确代数为 t−t²/2=1/2−(t−1)²/2，而输入正是 (t−1)²≥0。只用这一个原有恒真不等式已足够，不依赖大环境中无关事实。受限求解没有新增公理或前提；Sη≤n/2、exp(Sη)≤exp(n/2)、完整 Iη 的积分可积性及正性均保持此前已审逻辑。

3. 新 110 行在 `:= by` 内添加唯一 `set_option maxHeartbeats 800000 in`，其后原证明体统一增加两个 ASCII 空格。已读激活 dfb4cd9f 的明确授权上限 800000；这个设置仅作用证明块内的 elaboration 预算，不改定理头、全局／声明选项、任何数学前提或内核规则。原始冻结前文仍只包含 autoImplicit=false；新的执行 OS CPU、-M8192-j4、wall300 和锁要求不由本次源码改变。这里未执行新检查，不判断 800000 是否足够。

独立字节复建已通过：删掉新 PROOF 的第 2 行；对第 3–322 行每个非空行恰去两个开头 ASCII 空格；其余行保留；归一化后的差异恰为上述三条一行变化。反向恢复这三条得到旧 PROOF 的 f3897252… 全部字节，再与相同冻结片段拼接得到旧完整源码 1ae7e408… 全部字节。新的冻结拼接同样逐字节精确。因此旧完整审阅中关于唯一见证、原 h/μ、量词、三个窗口、原矩条件、真删点 full-Iη 费用、原始 P maplaw、四项独立费用／移动费用最终界、下2／上4 payment、显式广 L² hSZ 及无正下因子假设的三次替换全部可精确复用，没有覆盖断层，也没有重复整份旧审阅。

REPAIR01-CHECK.json 自行推导并核验作者 manifest／输入列表中的 25 个唯一直接文件绑定，全部匹配；该数字仅对应本检查的明确文件集合，不照抄父实例不同集合的计数。新的全部源码为严格 UTF-8 无 BOM、无 CR、单一末尾 LF；声明数量仍为一个源码 theorem；没有 sorry/admit/axiom/unsafe/native_decide/extern。实际拥有者及生成名计数仍待机器证据，不用源码数量代替。

当前覆盖是“原完整独立 SOURCE 审阅＋精确复建＋全部修复增量审阅”。实际新源码全部 TYPE／必要 VALUE／首个原始对象／递归 AX 尚未提供，故不做机器资格化、不写 FINALWRITE、继续保留独占审阅权限。旧 259／260 证明和检查精确复用。ExternalSZ、CDF、relative-tail、DC、fullOQ56、root 均保持 OPEN。实际模型／后端／推理强度和分项用量未暴露，保持 null；请求值为 gpt-6.1-sol／xhigh。
