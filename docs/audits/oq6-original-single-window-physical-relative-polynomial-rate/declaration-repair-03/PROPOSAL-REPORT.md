# Unit263 声明修复03提案：在最终命题项使用标准局部收束

STATUS: PROPOSAL_ONLY_AWAIT_LEAD_FREEZE

本提案只把 freeze02 HEAD 最后三行表示的同一个不等式命题 S 包裹为 `show Prop from by exact (S)`，其余53行逐字不变。完整候选 HEAD 已写入 PROPOSAL-HEAD.txt；没有组装或写出任何完整 Lean 源或证明。提案作者没有运行 Lean、AX、工具链探测或服务器操作，未取得新对象、实际 TYPE 或定义等同性证书。当前只提出标准生产语法候选，不能声称该写法已修复展开或 unit263 已 qualified。

## 输入、权限与实际读取

首先完整读取并核验 declaration-repair03-ACTIVATION.json：SHA256 `55c1eb90a83a291771ededaccb78c075daee5cd3d24582a102dfa0ab696100f5`，5372B。其17个输入均通过实际 SHA256 和字节数核验，并已完整读入：四个 freeze02片段/元数据、当前全源、完整 PROOF、旧作者 LASTFINALWRITE、四份独立语义报告、native03规范化记录、诊断05/06完整源与规范化记录、05的g映射。READ_ACK.json先记录实际开始与已核验绑定，完成读取后更新为17项全文读取完成；没有把尚未阅读的文件提前标成已读。

当前全源是 `3098a452f91dfc6bf81a4aab900cfad169d7e3fe6d2d37b8ac5959179e8b317c`，12628B/234LF；原完整 PROOF 是 `243399dc1432d9bdca85b93d28f0d4626a4f644c110c107d370943094c40733b`，9072B/163LF。两者在本轮只读。freeze02 HEAD 是 `be9dbe4419b940e63ea98666a7e101b851f56301fd10a6d968e5499f44c4c210`，3005B/56LF。前置483B/13LF和关闭68B/2LF片段也只读。

旧作者 LASTFINALWRITE `767582e0959460a0a7781d15afa28148b23185a7ba6cea0714a2bfcebd8d377a` 明确释放全部旧作者写入、执行、子代理和发布权，writers/heavy/inflight/pendingExternal/uncertain/children为0。当前角色为新声明提案作者，唯一写区是本目录；不是独立评审者，不能为自己的提案签发独立接受，也没有实现授权。其他协作者的目录、数学源与证据不作修改。

旧独立完整审查并集精确保留：SOURCE-REPORT `1e32c3626d4fd883407ea2a5397e2f376316d1eeaaba2f789c8200947a7ae3c3`、REPAIR01-REPORT `7833a3f4eb8b71a166a3759d20f81b0e1a23b1f0081709560ac343f807105270`、DECLARATION02-REPORT `91baf64576f58a3ede5e6f18fe95be5710330df9798413af24b9590dee664b36`、SOURCE02-REPORT `88845c7645a9c632e8a8511cbbfb1c7134ee55651bba4695165f97b72579d3d3`。它们对当前3098源的完整 SOURCE/证明覆盖保持原意。本报告只给出新声明写法的作者解释，不把这些旧接受自动扩展为新语法已被独立接受或机器通过。

## 已知故障与诊断能支持的范围

native03的精确3098源实际RC1，错误位于声明14:8，unknown free variable `_fvar.1226`，没有对象，所有所属进程已结束，保护字节保持相等。前两次失败按激活所述保留；本角色没有重新执行或另行读取其原始大回执。

诊断05在13个选定term边界调用标准 elabTerm，并检查当时局部类型、值和结果表达式中的可见自由变量。所有边界均记录完成，missingReferenceObservations为空，最终仍RC1且没有 PROOF_ENTERED。其错误显示 `_fvar.16399`。精确g映射文件说明 pinned PrettyPrinter 使用 `fvarId.name.replacePrefix _uniq _fvar`，因此该显示名对应实际局部 `_uniq.16399`，其用户名是 let-bound g。这个映射定位了失败报告中的局部变量；它不能单凭自身断定哪个term产生了未决约束。

诊断06的关键额外行为是在每个被包裹term的 elabTerm之后调用 synthesizeSyntheticMVarsNoPostponing，再实例化并返回同一表达式。它实际RC0、sourceErrors为空、记录 PROOF_ENTERED，完整原证明运行结束；这是无-o诊断，不是正式源的对象/AX资格包。该差异支持“未决隐式约束的求解时机及局部let作用域”这一修复方向，但还不能证明唯一根因或 Lean 编译器缺陷。

领队随后以任务内消息补充：诊断07只在gInit强制求解仍自然RC1、没有proofentry，正式3098字节不变；给出receipt短前缀2abc19c7。该补充不是本轮17项已核验输入中的完整回执，本报告明确按领队提供的观察引用，不假装已核验其完整hash/字节。它排除了“只收束g初始积分值已经足够”的候选。

随后收到并完整读取、实际核验新增08规范化文件：`lead-execution-01/diagnostic-header-term-no-o-08-normalized.json`，SHA256 `d7223175f9329034dec598dde223b941ddab5750cc24790055d4c8a78693ccd4`，2041B。它作为原17项以外的补充输入绑定到manifest/checkpoint；原激活与已完成READ_ACK自此保持原字节。领队说明08唯一强制位置是terminalProp；规范化记录绑定服务器原receipt `716c460f451ba82130497cc0e91ce7073c7de0b3abc34088a79c4af7edb6dbe7` /31532252B/mtime_ns1793235308625950218，实际RC0、7.716101575642824秒、13个header term完成、terminalProp的SYNTH_BEGIN/DONE及PROOF_ENTERED、errors空。31个warning保留，strictWrapperSuccess=false、no_o=true、canonicalObjectAbsent=true、qualified=false；afterRecordsDerived30566、allOwnedEnded/beforeAfterExact/preservationEqual均true。canonical仍为原3098/12628B。

因此“只在最终命题边界强制求解足以令这份无-o诊断成功”已有精确补充证据；不是本作者新执行结果，也不证明标准wrapper已运行成功。没有据此声称编译器bug、确定未决约束的唯一内部产生位置、正式源有对象或机器资格已闭合。

因此本轮选择一个有针对性的最终命题边界提案，避免在g/r/β/physical等处叠加未经定位的改法，也不建立盲目重试队列。最终项的局部上下文仍包含所有原let和量词变量，适合在返回整个header之前完成该项需要的合成。标准 exact 的具体效果仍必须由 pinned服务器对精确候选检查；这里不声称它与自定义诊断中的强制合成在全部内部细节上完全相同。

## 唯一提案与精确改动

用 S 表示原 HEAD54-56的完整不等式命题。唯一替换是将该末项写为：

```lean
        (show Prop from by
          exact
            (|@Measure.real (Fin n → Ω) mN P {ζ : Fin n → Ω | z ≤ physical ζ} / Shao.standardNormalTail z - 1| ≤
              Ktail * (β * Real.rpow (1 + z) p * Real.rpow (n : ℝ) (-((p - 2) / 2)) +
                (1 + rho) * (1 + z) ^ 3 / Real.sqrt (n : ℝ))))
```

`show Prop from` 明确这是一个取值于 Prop 的项；其内部 tactic goal 是 Prop，exact交付的项就是原不等式S。本地 `by` 用来构造声明的命题项，不是为原数学结论提供一个新证明体。完整 theorem 的 `:= by` 和9072B PROOF不在本提案文件中。没有新导入、辅助声明、宏、elaborator、IO、日志、全局选项、实例或定理。

PROPOSAL-HEAD.txt为SHA256 `3c95d7ec4d27d37712930ecba1739606da14d2642dc7c6633452c61678a06d8c`，3063B/58LF。旧HEAD1-53等于新HEAD1-53；旧54-56的完整S经标准wrapper与缩进变为新54-58。净增58B/2LF。唯一子串替换和反向替换均精确重建相应完整HEAD，详见STATIC-CHECKS.json。没有改写S的运算、实参、括号的数学结合关系或任一符号。

## 数学与预期定义等价性

S本来就是关系 `abs (...) ≤ (...)`，类型为Prop。标准 `show Prop from ...`只给出已经成立的类型注解；`by exact (S)`在类型Prop的目标中交付S本身。若 pinned展开按此标准含义成功，得到的末项就是同一个S，而不是S的证明、S与另一命题的等价证明、对S的弱化或另一个条件命题。无需propext、函数外延、等式运输、类型转换定理或新增公理来解释这个改写。

这里的“定义等价”是透明标准语法展开的预期项级说明。失败的原3098声明没有可用的成功实际TYPE；本轮也没有运行新HEAD，因此没有取得原失败表达式与候选实际展开项之间的机械定义等同性证书。只有后续精确源检查及实际TYPE审查可以确认所有推断节点实际落在预期项上。若某个待定实例在新边界产生差异或失败，必须按具体诊断处理，不可用这份作者说明覆盖它。

对外层依赖表达式可写成原来的嵌套上下文 C[S]：原let/forall/exists/eventually结构是C，提案只将最后S写成上述透明wrapper。C的每个binder、let值、依赖顺序和局部作用域都逐字不动。在wrapper确实展开到S的前提下，C[wrapper(S)]与C[S]逐项定义等价；不存在量词交换或在定义相等之外使用数学推理的步骤。原证明入口依次 intro g/r/v/rho、p及其条件、外部packet、固定包络参数、β/K0/Ktail，保持相同；最终同一unit262结论仍应与同一S连接。实际证明兼容性仍待正式检查。

逐项保持的完整数学接口如下：

| 接口 | 提案保留内容与依赖 |
| --- | --- |
| 原模型 | 任意Ω:Type u、同一个mΩ、原μ及IsProbabilityMeasure、原h；hh的乘积可测性、hh2的原L2条件、hhsymm、hcenter、hprojectionsecond恰为1全部逐字不动。没有标准Borel、可数生成、无原子或额外矩条件。 |
| 原派生量 | g仍是原投影积分；r仍是h-g-g；v仍是同一μ.prod μ上的r平方积分；rho仍是sqrt v。这些都是原let值，不是新增任意参数。未移动g或其定义。 |
| p与外部结果 | 固定2<p≤3、同一hgp可积条件、cSZ/C1-C4和同一ScalarShaoZhouFiniteCostTailInput.{u}先于存在c。没有证明或无条件化外部SZ。 |
| 固定包络参数 | Cenv/aenv/t0/Menv及非负/正性条件仍全部先于c和最终n。c允许依赖这些固定数据，不能依赖后来选择的n、w、z。 |
| 真实β | β仍逐字是原μ下积分∫|g|^p，不换成上界、截断矩或任意β。没有新增β>0、β≥1假设；β>0仍由原证明内部使用投影二阶矩=1推出。 |
| 同一常数 | K0与Ktail逐字符不动，尤其8、64、512、exp C3和各C之和保持原式。结论仍为同一Ktail正性与同一Ktail乘率项，没有放大常数。 |
| 量词与一致性 | ∃c>0及Ktail>0之后才是eventually n；n≥4和数值窗口非空是结论；对每个最终n才∀w、原五项w/包络条件、∀z≥1及唯一闭hWindow。统一最终阈值不改成逐w/z阈值。 |
| 单一窗口 | 原闭上界z≤c·β^(-1/p)·n^((p-2)/(2p))逐字保留。没有把四个内部辅助窗口放回公共假设。p=3、弱上端点和β<1分支都保持原先接受的数学处理。 |
| 样本law | 同一Fin n、mN、明确Fin.fintype n、同一坐标mΩ和原μ的Measure.pi、原Measure.real的mN/P实参及弱闭上尾事件全部不动。 |
| 原物理统计量 | D1=residualStatisticD n r；分子projectionW+D1，分母sqrt(centeredSq n g r ζ)；分母等于0时physical=0。同一个Real.decidableEq、两个分支及判定命题逐字保留。没有新增非零Studentizer条件，也没有替换统计量或零事件。 |
| 率与结论 | 同一标准正态上尾作分母、减1、绝对值、β·(1+z)^p·n^(-((p-2)/2))及(1+rho)(1+z)^3/sqrt n逐字保留。包装的是整个同一个≤命题。 |

原完整证明的承重部分仍由精确旧证据复用：β内部正性；q=(p-2)/(2p)满足0<q≤1/6；cMoment与cOther构成同一固定c；正β实幂消去在β<1仍成立；n^q趋于无穷给出最终数值非空；同一qualified unit262在原参数下给出统一事件；n≥4及实幂比较推出四个非矩窗口与正β矩窗口；最终取同一物理比率界的第二分量。本提案不改其任何行，也不重新对上游producer进行机器审计。

## 适用范围、后续门与实际状态

范围仍是原p51 S19 bounded-polylog乘积包络、z≥1、原真实物理上尾、固定正β逆幂单窗口分支，明确条件于更广L2的scalar hSZ packet。p54仍保留定性条件矩收敛与最终一致界的修正，不引入任意多项式条件收敛率。compact CDF/atoms、DC、unbounded conditioning、p54 uniform conditional consumers、外部SZ本身、full OQ56/root均保持OPEN。

领队可结合已成功的terminalProp单边界诊断选择并冻结精确HEAD，再安排独立受影响声明审查。只有新的精确冻结激活到达，本作者才可承担同作者实施，把冻结片段与逐字原PROOF组装；当前绝不提前写全源或证明。正式服务器native成功后仍须同一first original O的全部实际TYPE、所需非定理VALUE和递归AX，并由独立评审完成最终精确检查。诊断RC0与本地静态字节检查都不替代这些门。

本轮没有自定义生产elaborator、sorry/admit/new axiom/unsafe/native_decide，没有Lean/AX/本地或服务器工具链探测、网络、Git/API、发布、Goal、schedule或子代理。请求模型/力度为gpt-6.1-sol/xhigh；实际模型、后端、力度和输入/缓存输入/输出/推理子集计数没有暴露，均为null。最终READY-CHECKPOINT记录writer/heavy/inflight/pendingExternal/uncertain/children实际六零，保留proposal→implementation同作者角色；不签发旧式全权释放，只读等待lead精确冻结。
