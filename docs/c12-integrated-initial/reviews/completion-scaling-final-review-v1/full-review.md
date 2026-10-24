# CompletionScaling 与 RawInitialCompletion 独立完整终审

STATUS: CORRECT

本裁决只认证两个精确冻结版本的局部数学结果。独立审查者为 `/root/completion_scaling_final_review`，使用新上下文 `gpt-6.1-sol/xhigh`，未参与命题、源实现或证明修订，只在本报告目录写入审查工件。已使用 math-theorem 与 chinese-output-style；未使用 math-ultra、子代理或第二次 Lean 检查。

## 1. 认证版本与机械证据

| 模块 | 源 SHA256 | 冻结文件 SHA256 | 成功对象 SHA256 | 收据 SHA256 |
|---|---|---|---|---|
| Shao.C2.CompletionScaling | `064a96e4dc1bc0c8a7fc317a6fecb50d59c819ecf381107625514cf59560ad92` | `2ce7970fde23314357e7b24dd7e049cc05e16b56b0705315539c1fd14913dc97` | `0ef77682133eceab5bc90504fa0b816378c034854f8703653cfc9e5c104f6445` | `a76d0883c787bceff6c5a0b7d9b7bb573e1c22a6c8c9a5633fe476d757f71267` |
| Shao.C2.RawInitialCompletion | `cd96e18d97fcb4d146f9ab26f9b4134d9f916dcccf437f11050b2b13ec3e5cae` | `f535d1dcfdad4a2843c5e84588a09bda7e7293224a7a1b4b274dc1fc9ccfa326` | `b1e26be2b56b5992a836cae8abcbd68ff76866efde8403e05beec52ab7a93c32` | `9e9377334d0abe55b522be081466e383330b9e261f7cfa07867f0de95494e92f` |

全部 12 个公开定理的完整头及 `rawInitial` 的完整定义头和值，与给定的预先冻结接口去除空白后的令牌完全相同。唯一额外执行选项是 `measurable_rawInitial` 局部的 `maxHeartbeats 1000000`；它未改变逻辑命题、定义或内核。两份最终源均为无 BOM 的 UTF-8、LF 行尾，未含 sorry、admit、新 axiom、unsafe、native_decide。

通过既有 `tools/server.py` 对远程现存证据进行只读核验，主绑定 36 项、补充绑定 4 项，均成功。读取了已成功内核日志及全部实际所属类型/定义值与原公理日志的连续逐块对应关系。CompletionScaling 成功 attempt002，RawInitialCompletion 成功 attempt003；两者原内核及所属常量递归公理审计退出码均为 0。没有重新编译新单元、旧生产模块或运行新的 Lean 公理审计。

服务器工作树为 `/root/rivermind-data/shao-lean-20261021/workspaces/c12-bridge-domination-v71`，分支 `author/c12-integrated-telescope-v71`，核得 HEAD `6fcd7beb1e4fcc586c32b205956b576952799962`。固定工具链 `leanprover/lean4:v4.36.0-rc1`、mathlib `807d3836b165983210ee2ecf3cd28f239436949c`、既有 `shared-v34/packages` 接口不变。成功日志的警告只涉及既有包工作树变更提示、未使用参数/化简项及弃用名称；未出现内核错误。不存在新增数学信任前提。

需要保留路径差异：Scaling 的成功对象、类型、值及成功日志位于工作树的 `outputs/c12-completion-scaling-v71`；它的 OwnedAudit、JSON 与失败 attempt001 位于根目录的同名 outputs。RawInitialCompletion 的全部收据路径位于根 `outputs/c12-raw-initial-completion-v71`。本次按每项收据的绝对路径核验，没有假设统一输出根。

## 2. 全实际所属范围与阅读方法

| 单元 | 公开源定理 | 实际定理 | 实际非定理 | 完整实际类型 | 完整非定理值 |
|---|---:|---:|---:|---:|---:|
| CompletionScaling | 5 | 19 | 0 | 19 | 0 |
| RawInitialCompletion | 7 | 7 | 1 | 8 | 1 |
| 合计 | 12 | 26 | 1 | 27 | 1 |

已完整阅读两个生产源的所有证明、全部冻结头、27 个完整实际类型和 `rawInitial` 的完整实际透明值。实际所属按 `env.getModuleIdxFor?` 选择，未按名称前缀筛选。特别是 `Shao.C2.BridgeDomination.strictInterval.eq_1` 的名字虽在旧命名空间，实际属于 CompletionScaling，已计入它的 19 项。Scaling 的另外 13 个生成化简定理及 5 个公开定理全部覆盖；Raw 单元实际只有 7 个公开定理与 1 个定义，没有遗漏的私有/生成值。JSON 中逐项列出所有实际名称、类型哈希、值哈希及具体覆盖理由。

对重复的长类型采用 TEAM 允许的既有无损字典方法：完整阅读 73 项原样括号子表达式字典一次，再完整阅读所有非重复的编码上下文。没有省略绑定变量、实例、let、条件或结论。恢复后逐字节等于原始文件/完整依赖块。新类型原长分别 42786 与 76973 字节，Raw 唯一值 6968 字节，Scaling 值文件为空。另完整阅读直接消费的 18 个旧实际声明类型和 13 个透明定义值，检查与新调用的参数、可测空间及结论相互作用；不重新审判旧证明。阅读清单和字节恢复证据见 `lossless-reading-manifest.json`。

两个 OwnedAudit 源均已完整阅读：遍历环境全部常量，按实际模块所有者选择，包括私有/生成声明，对每项调用递归 `Lean.collectAxioms`，只允许 `propext`、`Classical.choice`、`Quot.sound`；公开目标必须为定理且计数吻合。日志全块与 JSON 名称集合和数量相同。全部 27 项递归公理通过白名单。

## 3. CompletionScaling：逐证明与边界审查

**bridgePath_scale。** 已消费旧 `BridgeTime`、`BridgeNoise` 和 `bridgePath` 的完整实际类型和值：时间域是 `[0,1]`，噪声是两端为零的实连续映射，路径逐点为 `(1-t)y + tz + sqrt(T)g(t)`。`Real.sqrt_mul (sq_nonneg c)` 与正尺度下的 `Real.sqrt_sq hc.le` 给出 `sqrt(c²T)=c sqrt(T)`。外延后只剩相同连续映射上的实环恒等式。没有改时间、改噪声、替换终点或调用噪声分布的尺度不变性。冻结的 `hT : 0≤T` 保留；该证明中它未使用属于可接受的更保守接口，不是隐藏前提。

**upperCompletion_scale。** 完整消费 `strictUpper` 与 `upperCompletion` 的值：前者对所有 `t∈[0,1]` 要求路径 `<a`，后者为该事件的测度实值。证明先建立 `c*u<c*v ↔ u<v`，逆向用非负乘法保持 `v≤u` 与严格不等式矛盾，正向用 `c>0`。代入路径尺度后所有时刻的严格上墙条件完全等价，因此事件相等，任意同一测度的实值相等。ν 不要求是概率或有限测度；此处只使用同一集合的测度相等，即使 `.real` 对无限测度取零也没有错误推断。

**lowerCompletion_scale。** 旧值确为 `-a<path`。经 `-(c*a)=c*(-a)` 后使用同一正乘法消去，保持下墙方向，未把下墙误写为上墙或漏掉负号。

**intervalCompletion_scale。** 旧值确为同一参数的严格上下事件之交。两项均在同一 g、同一时刻域、同一 `c>0` 下消去因子。包含所有端点、墙上等号及任意墙宽；没有由概率相等倒推集合相等。生成的 `strictInterval.eq_1` 完整类型正是该定义等式。

**initial_raw_completion_eq_normalized。** 明确需要 `Q>0`，故 `sqrt(Q)>0`、`sqrt(Q)^2=Q`，且 `sqrt(Q)*(S/sqrt(Q))=S`。在区间尺度定理中选 `c=sqrt(Q), y=0,T=1,z=S/sqrt(Q)`，得原墙宽 `x sqrt(Q)`、原剩余能量 Q、原终点 S 的区间完成值与标准化 `x,0,1,S/sqrt(Q)` 相同。最终交换乘法仅为参数正规化，未取消 Q>0。

全部 14 个生成声明逐项核对：三个交集成员命题的命题等式、三个分配负号的乘法等式、三个显式 NeZero 下数码 2/3/4 非零命题、无零因子下非零积、IsReduced/MonoidWithZero 下非零自然幂、GroupWithZero 下非零整数幂、CharZero/AddMonoidWithOne 下自然数转换加一非零，以及区间定义等式。所有泛型类、绑定变量与实际结论均完整，无局部隐含的目标新公理。

边界：`c=0` 与负尺度不在冻结结论中；`T=0` 时只认证自然线性路径的代数尺度恒等。它没有认证任意不同端点零能量的源终端完成约定，也没有把半直线在 `a=0` 的自然事件替换为原文规定的全部完成值为零。

## 4. RawInitialCompletion：逐证明与消费关系

**rawInitial 定义。** 完整实际值为 `if 0<energy z then intervalCompletion ν (x*sqrt(energy z)) 0 (energy z) (prefixSum z n) else 0`。实际有限路径为 `Fin n→ℝ`，Q 是实际平方和，S 是实际末项前缀和；未换成确定性方差。零能量分支显式为零。n=0 也定义良好。

**rawInitial_eq_normalized。** 正能量分支应用上一单元的精确初始尺度定理，再消费既有 `normalizedEndpoint_of_energy_pos`，得到 S/sqrt(Q)。非正分支两边相同为零，不需要额外样本假设。这里 Q 实际非负，所以非正分支在应用中正是 Q=0；无需偷偷从标准化定义的约定推出原始分支。没有将 Q=0 的标准化桥值本身误当作零。

**measurable_rawInitial。** 已读全部实际 `CompletionParameters` 值，其准确积结构为 `ℝ×(ℝ×(ℝ×ℝ))`，顺序是墙宽、y、T、z。参数映射准确为 `(x sqrt(Q),(0,(Q,S)))`，由实际有限路径能量墙、能量和前缀和的可测性构造，未错放元组。消费的全参数区间可测性要求 `SFinite ν`，新定理完整保留该假设。正能量集合由实可测函数严格比较可测；在它上与零函数作分段。证明没有依赖误差结论或从不可数可测交直接推出可测性。局部心跳增额只让既有可测空间实例约化完成。

**rawInitial_bounds。** 正分支准确取旧 `completion_bounds` 最后两项区间值的 `[0,1]` 界；零分支为 0。ν 的概率测度假设保留。未错误消费上/下单侧界。

**integrable_rawInitial_and_joint。** 原始值函数可测，端点掩码 `{normalizedEndpoint≤v}` 也可测，闭端点的判定分支未改变。两个函数分别具有点态范数界 1，P 是概率测度，故以可积常数 1 作强可测支配得到各自的原始积分可积性。没有只检查两个积分差可积，也没有由总和/差的可积性反推出两边。

**raw_initial_marginal_error_of_cdf。** 直接对每个样本用完整逐点恒等，精确消费已合格 `finite_initial_marginal_error_of_cdf`。n、P 的概率性、Brownian 类型及 hB、δ≥0、所有 u 的闭 CDF 误差前提完整不变。结果为原始初始值期望与整段布朗运动严格区间事件概率的误差 `≤4δ`。没有把任意噪声法误认成 Brownian 桥法。

**raw_initial_joint_error_of_cdf。** 辅助 he 只交换两个 if 的嵌套位置：正能量 guard 与闭端点 guard，共四个真值分支；零分支均为 0。然后精确消费已合格 finite joint 头。积分侧仍是 `normalizedEndpoint≤v`，Brownian 侧仍是 `B 1≤v`，不排除 v 上原子。两个积分函数的相等是逐点恒等。

**iid_raw_initial_errors_of_truncated_scalar_input。** 完整消费既有截断标量预算的 iid 定理，ν 为概率法、n>0、仅平方可积、均值 0 与 n 倍二阶矩等于 1 全部保留。`hScalar` 仍为显式外部前提，准确系数是 `(51/5)scalarGamma2+25 scalarGamma3`。已读两个 gamma 完整值，切分是 `|z|>1/2` 的平方尾与 `|z|≤1/2` 的三次截断值；没有要求全局三阶矩。结果原始 marginal/joint 各 `≤200*truncationBudget ν n 0`，只经相同两个逐点改写继承。没有证明、消去或把外部 Pinelis/Shao 前提变成新 axiom；也没有在此证明原文独立的 16R 零能量论证。

## 5. 原文忠实性、既有证据复用与整合风险

完整读取只读原文 `main.tex 871–956,1038–1076` 与 `supplement.tex 4192–4252`。原文把完成核解释为严格桥生存，并在实际过程采用墙 `a=x sqrt(Q)`、状态 `S_r`、剩余平方和 `Q-Q_r`、原末端 `S_n`；初始值是 `1_{Q>0}g_x(W)`。这两单元准确填补该初始原始参数到标准化参数的同噪声恒等与可测可积消费链。有限实连续桥在紧时间域上全时刻严格绝对值 `<x` 与严格最大值 `<x` 相同，故本次初始事件与原文语义一致。

对 x>0、Q>0，初始 y=0 在墙内；末端位于或超出墙时，噪声在 t=1 为零，严格事件自动为空，符合 exterior-endpoint 杀死约定。对 x≤0，区间事件已在 t=0 为空；Raw 的 Q=0 特殊分支仍显式为零。上述是初始区间情形，不能扩展为所有半直线/所有 T=0 参数的原文特殊约定。

复用并核验以下合格旧源、对象、收据与完整独审覆盖：BridgeDomination 的审查 `568c781dac68a0ecb79e401897d30ceaa70dead2966fa77f47f9972406b29ed2`；FiniteInitialCompletion 与 TruncatedScalarBudget 的审查 `07b8c3ed3f4fb9d888944688e12aca069a0dc3bf70a3e52ea4e71ee3c897dac5`；CompletionMeasurability 的审查 `6f2a03f8ce7c54772ca4fd966558bbd986b26471a6401741b0eada31e7e08ff7`；BrownianBridgeLaw 的审查 `7eb667d7e53782be5eee0aff695d1965acda9d7db8d8a931c8e74d37760d5461`。只读消费接口与透明值，没有重审旧证明或重编旧模块。原核心有限路径、归一化、路径可测性及预算定义的本地只读源与远程实际消费源一致。

两新模块导入单向、没有循环，使用同一 BridgeNoise 子类型与其连续映射 Borel 可测结构、同一实际 Path n 产品可测结构。Raw 的 SFinite 可测性与概率测度下的有界性适配；全部消耗头的量词、参数顺序和结论完整吻合。生成 `strictInterval.eq_1` 的实际模块归属需要在未来整合时继续以精确源/对象/实际所有者图为准，不能按命名空间估计计数。本次证据中不存在未覆盖的数学交互风险。

这不是 killed/free 热核商识别、PDE、实际解析导数界、完整停止 V/FY、前缀 live/crossing-kill 过程、终端/overshoot 包络、重排 iid 法则转移或完整 C1/C2 原根闭合。没有新颖性主张。全部原研究根继续 OPEN。

## 6. 失败保存、可追溯性与释放

Scaling attempt001 的未解尺度事件目标与最后零乘法化简不匹配日志及源已绑定保存；attempt002 为唯一接受的精确成功版本。Raw attempt001 元组注解类型错误，attempt002 在 `measurable_rawInitial` 达到确定性 200000 心跳上限并导致下游未知常量；两次失败源与日志保留。attempt002→003 的唯一源差是上述局部心跳选项，成功版本的所有冻结头/值保持不变。失败没有被当作证明结果或掩盖。

本审查目录的第一次本地哈希整理遇到旧 BridgeDomination 收据使用 `SHA256` 而非新格式 `sha256` 的字段差异，在发起服务器请求前停止；已作只读接口兼容并保存说明，未改变旧收据或数学工件。补充元数据读取曾访问旧报告不存在的字段，亦为只读查询，没有数学证据副作用。

已核 C12 激活所有者 `01a16c4c-25a6-7740-a10e-12635a13edae` 与协调者 `01a16be2-3e35-7e13-97d3-7b11b603dead`，用户暂停的 OQ3 未恢复。审查者未执行重型命令，未持有 c12-heavy.lock。报告完成时本上下文写入权与执行权明确释放，在途操作为零；释放的是本审查者，不是 C12 lead。lead 可消费两精确版本的合格工件，继续实际停止完成过程/解析导数及终端约定等下一源依赖。

输入、缓存输入、输出及推理子集用量不可见，均记录 null；不把令牌数或购买积分估计转换为订阅百分比。
