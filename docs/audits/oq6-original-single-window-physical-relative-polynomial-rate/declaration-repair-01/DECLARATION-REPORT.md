# Unit263 声明显式化提案 01

状态：PROPOSAL_ONLY / ROOT_CAUSE_UNLOCATED / NOT_MECHANICALLY_CHECKED。

本提案只把冻结 HEAD 末段的三处推断写成已接受 262 实际 TYPE 中的明确项。数学前提、量词顺序、所有 let 的定义内容、原始概率空间、统计量、常数、窗口和物理零约定均保留。它是一个可供 lead 选择、冻结和独立受影响声明评审的候选，不是已证实的故障修复。具体逃逸自由变量尚未映射到用户变量；本轮没有运行 Lean、取得对象或获得新的独立评审。

作者角色为 `/root/oq56_unit263_declaration_repair01`，只写本目录。冻结片段、当前/旧作者文件、所有评审和 accepted262 都只读；未改变 canonical，未写新的完整 Lean 源或证明体。使用 math-theorem、中文输出与 Windows UTF-8 规范。请求配置为 fresh `gpt-6.1-sol` / `xhigh`；实际模型、后端、力度及各类 token 数未暴露，均保留 null。

## 实际输入和证据边界

首先读取并验证 activation `d8de84e2a88da02de51513a53413c0b8b6761d427e3043e7c681b88b2fcd11df` / 3775 B，随后逐一读取全部 13 个绑定文件的原始字节，SHA256/bytes 全部一致。READ_ACK 已在开始语义分析前写入；它诚实记录当时语义阅读仍在进行。之后完整读了冻结 HEAD/PREAMBLE/CLOSING/freeze JSON、当前 233-LF 源和其中完整 163-LF 证明、LASTFINALWRITE、全部三份声明/SOURCE/repair01 报告、directIO04 规范化诊断、qualified262 packet 和 accepted262 完整源。当前证明单独 fragment 与完整源的精确组装另由 STATIC-CHECKS 检查。

为解释声明而额外读取：native01 紧凑诊断、native02 返回描述、诊断01/02/03 的本地结果/相关入口源码，以及 directIO04 实际本地诊断源；accepted262 metadata 中 public theorem 的原始 TYPE 第318–336、400–403行；既存 Measure.real 原始接口取证包中完整定义和前置 scope；只读 hSZ 定义及原始统计量定义。新增路径/hash/bytes、确切阅读范围都列在 STATIC-CHECKS 和 MANIFEST。没有把 accepted262 的旧证明重新审判或重跑，其 qualified kernel/全部实际 TYPE/AX 证据照原样复用。

SERVER.md、TEAM 当前所有权摘要、当前 AGENTS 相关方向及 REGISTRY 所需选择字段均只读；没有把动态协调文件当作本提案的不可变数学输入。当前本任务仍是纯本地声明提案，不因此取得 lane、cache、integration、服务器或发布权限。pin 只读为 `leanprover/lean4:v4.36.0-rc1`；没有本地工具链探测。

## 已观测到的失败说明什么

原 native01 在 `42c35fd1…` 源上正常 RC1，声明行14:8 报 `unknown free variable _fvar.1226`，无对象。native02 对 `4ac45376…` 的返回描述仍为正常 RC1；其 stdout 的 SHA256/113 B 与 native01 完全相同。当前 repair01 仅把 hUpstream/dsimp/rcases 改为 direct obtain，不能据此认定声明问题得到处理。

最新 directIO04 规范化结果 `3c8d8255…` 记录正常 RC1，模块入口 `OQ56_MODULE_ENTERED` 已执行，第一条证明入口 `OQ56_PROOF_ENTERED` 没有执行；唯一源错误在诊断声明行17:8，为 `_fvar.1385`。canonical 保持 `4ac45376…` / 12552 B，无对象，所有 owned 进程结束且保护集相等。这些是上级已保存的服务器事实，本作者只核对本地绑定，不声称自己重新观察了远端进程。

前三次 logging 诊断不能反推精确断点。诊断03 的本地源码还含 `liftIO <| IO.eprintln`；上级任务明确指出相应名称错误，所以它不提供可靠证明入口证据。directIO04 才使用直接 IO 并明确区分模块与证明入口。`_fvar.1226` 与 `_fvar.1385` 是内部标识，不是可以按数字反推的 Ω、n、mN、β 或 hWindow；插入诊断本身会改变编号。

因此现有证据支持把下一步定位在声明/进入证明前的目标展开，而不支持继续盲改证明体；它没有识别具体坏表达式，没有证明 Lean 编译器存在缺陷，也没有构成定理为假的证据。即使本候选通过声明入口，仍需另行检查后续证明、全部实际声明类型及公理。

## accepted262 提供的精确参照

262 qualified packet 为 `f9a5d090b4f40039a77fa63469a2b9b3d2fd82d77bb618cbf084f64ab71d241d`，accepted 源为 `0b83abc73b1284fd49142b1cd8a4e407e22181b01150b0d910dd79454ffa0d10` / 18602 B，first original O 为 `72e2f82802a60be52d70b07a90bf16aa4b4d6fe0e19466d29b375d43d6b895fe`。本轮未重跑它们。

绑定 metadata `10031d2c49edd3db4a90d17243dc1e932ce0b44a4033ecee9e381ac1f3ab3ca1` 中 public theorem 的 TYPE 第318–336行仍保留 mN/P/D1/physical 的 let spine，并明确显示下列项；第400–403行保留最后一个项。以下只是已读原始表达式的易读记法，精确原文位置由静态记录绑定：

```lean
let mN := @MeasurableSpace.pi (Fin n) (fun _ => Ω) (fun _ => mΩ)
let P : @Measure (Fin n → Ω) mN :=
  @Measure.pi (Fin n) (fun _ => Ω)
    (@inferInstance (Fintype (Fin n)) (Fin.fintype n))
    (fun _ => mΩ) (fun _ => μ)
let physical := fun ζ =>
  @ite ℝ (Real.sqrt (centeredSq n g r ζ) = 0)
    (Real.decidableEq (Real.sqrt (centeredSq n g r ζ)) 0) 0
    ((projectionW n g ζ + D1 ζ) / Real.sqrt (centeredSq n g r ζ))
@Measure.real (Fin n → Ω) mN P {ζ | z ≤ physical ζ}
```

既存原始接口取证同时给出：

```lean
protected def Measure.real {α : Type*} {m : MeasurableSpace α}
    (μ : Measure α) (s : Set α) : ℝ := (μ s).toReal
```

这里 m 是普通隐式参数，不是新的 `[MeasurableSpace α]` 类参数；把 `P.real` 的展开解释成新增可测空间的类搜索是不准确的。它的 m 由 P 的类型推断。mN 本身仍是原有 let 值，并不变成实例 binder。另一方面 `if` 确实要合成 `Decidable`，`inferInstance : Fintype (Fin n)` 确实触发类型类合成；accepted TYPE 已给出这两个结果的具体参照。

262 和 263 中这个有限样本 suffix 的原始写法基本相同。262 通过说明这段表面语法本身并非普遍不可用，却不能保证不同外层 binder/let/合取结构中的 elaboration 行为相同，也不能单凭这一差异定位根因。没有从“262 成功、263 失败”推出某一特定实例一定逃逸。

## 合成候选及三个独立最小改动

`HEAD-PROPOSAL.txt` 是 E123 合成候选，SHA256 `be9dbe4419b940e63ea98666a7e101b851f56301fd10a6d968e5499f44c4c210` / 3005 B / 56 LF。它只有下列三处变化。这里的“最小”指每个原子只显式化一个既有推断节点；由于坏表达式未定位，不能声称三项合成是唯一或已证实的最少行修复。它以一个很小的局部 suffix patch 消除三个明确可见的推断入口，同时保留单项 patch 供 lead 选择。

1. E1/FINTYPE：只把 `(inferInstance : Fintype (Fin n))` 换成 `(Fin.fintype n)`。accepted262 TYPE 正是 inferInstance 包装的该实例。删除的是透明 inferInstance 调用，不是 n 的任意性，不增设 `Fintype` 前提，也不要求 n>0。
2. E2/DECIDABLE：只把 physical 的 `if` 写成 `@ite ℝ`，把其判定器写成 `Real.decidableEq (Real.sqrt (centeredSq n g r ζ)) 0`。两个分支分别仍为 0 和原分式。特意使用 accepted262 TYPE 实际出现的 `Real.decidableEq`，没有换成另一个尚需论证定义等同性的经典判定器。
3. E3/MEASURE-REAL：只把 `P.real event` 写成 `@Measure.real (Fin n → Ω) mN P event`。它显式指定原有隐式类型和原有可测空间，不改变 measure、事件、概率取实数方式或尾事件的弱不等式。

E123 不改 PREAMBLE：`PREAMBLE-PROPOSAL.txt` 与旧 483 B 前置片段字节完全相同，SHA256 仍为 `731fd4119088bdc37fecfa1de86bc0197ffef728f4f62d4121686ff08645eccc`。原 import、autoImplicit、universe、open/scoped、namespace/noncomputable 都保留；没有加大资源设置、换工具链、定义辅助命题或引入新实例。旧 closing 也完全复用，未生成新 closing 文件。

`HEAD-DIFF.patch`/`HEAD-REVERSE-DIFF.patch` 分别精确连接旧完整 HEAD 与 E123。`HEAD-ATOM-FINTYPE.patch`、`HEAD-ATOM-DECIDABLE.patch`、`HEAD-ATOM-MEASURE-REAL.patch` 各自均以同一旧完整 HEAD 为起点，仅作对应单项改动，不能按三个虚拟目标路径理解成三个已存在的 Lean 源。其完整目标 HEAD 可由 patch 唯一复原，静态检查记录了目标 hash/bytes/LF。没有任何一个候选被自动选中或实施。

| 候选 | 完整目标 HEAD SHA256 | Bytes/LF |
| --- | --- | --- |
| E1 only | `7c024f25d30e1cf5295da9c05600ec81c1fdbe8a5f248941924712c047d9b56b` | 2911/55 |
| E2 only | `19e73e7cd6e3dc19db3e6023112eb2e908908e1a51fe76ea91e9823ada7b2681` | 2996/56 |
| E3 only | `0e28c1211278c26a566f2256cfbdfa75286130ba51fb78f1f9a2cbe95f22b9c3` | 2956/55 |
| E123 | `be9dbe4419b940e63ea98666a7e101b851f56301fd10a6d968e5499f44c4c210` | 3005/56 |

这四个明确候选均没有证明体。它们在数学意义上是原声明的原样表达；E1 的透明包装消除、E3 的隐式实参显式化，以及 E2 对已接受相同判定器的明确应用，都应归约到相同相关项。但本轮没有机械验证原始 263 header 实际选到的每个实例，也没有获得原/新 header 的内核定义等同性证书。不能把“参照精确、静态等价理由完整”写成已 elaborated 或已 kernel checked。

## 完整量词、let 和实例依赖对照

下表左右均指旧声明和 E123；“不变”是源码/符号对照，不是一次新的 Lean elaboration 断言。

| 顺序与节点 | 原始依赖和作用域 | 候选对照 |
| --- | --- | --- |
| universe u，隐式 Ω，实例 mΩ | Ω 任意 Type u；没有标准 Borel、可数生成、无原子假设 | 全部不变 |
| μ 及概率实例，h | μ 仍是 mΩ 上的同一个原 law；h 为同一 Ω×Ω 实核 | 全部不变；概率实例不移动 |
| hh, hh2, hhsymm | 原乘积可测结构上的 Measurable/MemLp2 和逐点对称性 | 全部 binder/type/顺序不变 |
| hcenter,hprojectionsecond | 原 μ.prod μ 中心化；原投影二阶矩恰为1 | 全部不变；不新增平方可积/混合四阶矩 |
| let g | 依赖 Ω,mΩ,μ,h；仍为原核对第二个变量的 Bochner 积分 | 名字、位置、定义不变 |
| let r | 依赖 h,g；h(o,y)-g(o)-g(y) | 不变 |
| let v，let rho | v 依赖原 μ,mΩ,r 的原乘积积分；rho=sqrt(v) | 不变；不新加 v>0 |
| ∀ p,hp2,hp3,hgp | p 固定于 (2,3]；hgp 依赖同一 g,p,mΩ,μ | 仍在 ∃c 和 eventually n 之前 |
| ∀ cSZ,C1,C2,C3,C4,hSZ | hSZ 仍为同 universe u 上原完整外部 ScalarShaoZhouFiniteCostTailInput；只依赖这五常数，无本轮证明/归属转移 | 类型文本与次序不变；不内部化或削弱 packet |
| ∀ Cenv,aenv,t0,Menv 和四个符号证明 | 仍 Cenv,aenv,Menv≥0，t0>0 | 全部位于 ∃c 之前且不变 |
| let β | 原 μ 下 |g|^p 的实积分；依赖 g,p,mΩ,μ | 定义与顺序不变；不加入 β>0 或 β≥1 前提 |
| let K0 | 固定 `64*exp(1/2)^4*(1+4*512)` | 完全文字不变 |
| let Ktail | 固定 `8*(1+C1+C2+C3+C4)*exp(C3)*(1+K0)` | 完全文字不变；不放大常数 |
| ∃c，0<c，0<Ktail | c 仅在上述参数已经固定后选择；不能依赖后置 n,w,z | quantifier、两个正性结论及顺序不变 |
| eventually n in atTop | n 是 Nat；同一最终阈值在所有当前 w,z 之前 | 不变；不换成逐 w 或逐 z 的最终阈值 |
| 4≤n 与非空数值窗口 | `1≤c*β^(-1/p)*n^((p-2)/(2p))` 仍为结论 | 合取及每个数字/指数不变；不改为前提 |
| ∀w,hW,hWR,hSq,hSqBound,hEnv | w 可以随 n 改变；a.e.非负、原 polylog 高度、平方可积/≤Menv、原 residual 产品包络全部保留 | 所有 binder 原样；hEnv 使用原 μ.prod μ |
| ∀z,hz,hWindow | z≥1；唯一公共上界仍用同一 c,β,p,n | 没有新增或删除任何窗口；闭端点保留 |
| let mN | 依赖 n,Ω,mΩ；原 `MeasurableSpace.pi` | 定义/位置不变；没有 letI 或新实例 binder |
| let P | 同一 n-fold μ；原显式 pi 参数族 mΩ、μ | 仅 E1 明写 `Fin.fintype n`；不涉及概率/σ有限新前提 |
| let D1 | 依赖 n,r；同一 residualStatisticD | 定义不变，无归一化替代 |
| let physical | 依赖 n,g,r,D1,ζ；sqrt(centeredSq)=0 时恰为0，其余为原 `(projectionW+D1)/sqrt(centeredSq)` | 仅 E2 显式写相等判定；两分支、等号和所有统计量不变 |
| 原 closed tail 实质量 | event={ζ | z≤physical ζ}；P 的可测空间是 mN | 仅 E3 显式提供 Ω^n,mN；不是切换 law |
| 最终率 | 精确 Ktail、β、p、rho、n,z 及两个加项 | 每个系数、幂、根号、符号均不变 |

所有原 let 仍是定义，不变成任意独立参数；没有为了简化展开把 g/r/β/P/physical 广义化成输入。全部 named hypothesis binder 也保留，即使结论中没有直接出现其名字。旧证明的首组 intro 对应的 g/r/v/rho/p/packet/envelope/β/K0/Ktail 顺序未改。未来若实现者发现需要调整证明语法，那属于另行授权后的实现；本提案不预先写该修复。

## 自由变量诊断假设与判别限度

H1：`inferInstance` 生成或读取的实例项与当前 n/let context 关联，后续关闭 binder 时发生未解决依赖；E1 去掉这处合成调用。n 的有限类型实例实际仅依赖 n，accepted262 给出的结果是 Fin.fintype n。现有诊断没有把逃逸 fvar 识别成这个实例或 n，所以 H1 只是候选。

H2：physical 的 `if` 在嵌套 let/forall 下合成 Decidable 时，相关表达式捕获了 g/r/n/ζ 的局部项；E2 明确应用 accepted262 实际判定器，减少推断所需的中间项。它不改变零分母事件，不把 `sqrt(centeredSq)=0` 偷换成 `centeredSq=0`，不假定分母非零。没有证据排除其他根因，也没有证明原合成项确实错误。

H3：dot notation/隐式参数推断给 Measure.real 的 m 实参留下了对本地 mN 的延迟关联；E3 直接给出 mN。此处不是 typeclass 搜索：假设针对的是隐式实参的展开/作用域。显式项依然合法地在 mN 的 let 体内使用它；没有把 mN 提到作用域外。若错误发生在更早 β、hgp、hSZ 或外层目标 let，则 E3 无法覆盖。

这三项假设没有排他性，也没有确证概率排序。推荐 lead 按本次实际需要选择一个最小原子或 E123 后先冻结并取得独立受影响声明审查；不要把四个变体自动排成四次 native 重试队列。若 E123 获准后的单次受控声明检查仍在 proof-entry 之前失败，应停止同类盲试并取得更细的声明展开证据。

最小仍缺的诊断信息是：在相同 pinned 环境下，异常对应的真实 fvarId→局部声明名/类型/let值映射，以及声明目标从哪一段开始首次失败。lead 可在既有 no-O 诊断方式中对完整封闭命题项逐段记录展开边界：原 law/前提和 g/r/v/rho；固定 p/packet/envelope 和 β/K0/Ktail；最后存在量词/eventually 的终端 mN/P/physical/event。只看声明行定位或更换 logging 文字不提供这个映射。这里提出的是后续诊断需求，不是本作者授权的调用，不附带占位证明，也不要求重建旧 producer 或重审 accepted262。

## 静态验收与下一授权边界

STATIC-CHECKS 实际重新验证 activation 和全部13绑定；当前旧源的冻结片段+完整旧证明组装；候选三个唯一替换及反向恢复；双向合成 patch 和三个单项 patch 的完整内存应用；不变前缀/量词-let map；head 单 theorem/无 proof delimiter；preamble 字节不变；UTF-8 无BOM、CR0、单终LF；无 sorry/admit/新axiom/unsafe/native_decide。每项是文本与字节证据，不是 Lean 内核结论。没有写候选完整 .lean、没有改变原 proof fragment，没有执行任何 Lean/AX/version/help/smoke、服务器、网络、Git/API、发布、children、Goals 或 schedule。

之后顺序必须是 lead 选择完整候选→冻结新的精确 HEAD/PREAMBLE 绑定→独立评审受影响声明及等价性→lead 另行授权实现；本提案作者不能自行跃迁到实现或检查。后续机械成功也只能在精确 source/O/全部实际TYPE-VALUE/递归AX及独立最终证据齐备后记录 qualification。旧失败、旧冻结和旧 SOURCE 评审保持原字节，成功不可回写成旧尝试已通过。

外部 broader-L2 hSZ 仍是明确条件输入。原 p54 只保留定性条件矩收敛及最终一致界，未加入任意多项式条件收敛率。原 bounded-polylog 产品包络、z≥1、原物理统计量和闭窗目标不变；compact CDF/atoms、DC、unbounded conditioning、p54 uniform conditional consumers、external SZ、full OQ56/root 仍 OPEN。263 仍未 qualified，本提案没有数学完成声明。

PROPOSAL-READY 最后写，记录本轮提案已停止：writers/heavy/inflight/pendingExternal/uncertain/children 均0。作者角色可只读等待 lead 明确后续激活；本文件和 READY 不授予 implementation。
