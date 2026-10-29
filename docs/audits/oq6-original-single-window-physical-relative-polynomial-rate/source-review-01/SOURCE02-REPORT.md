# Unit263 SOURCE02 精确组装与覆盖并集审查

STATUS: CORRECT

JUSTIFICATION：新完整234-LF源是已接受freeze02声明与原9072B/163-LF证明的精确拼接。全部证明字节、前置片段和closing不变；唯一变化是已独立接受的E123声明显式化。旧whole SOURCE、repair01受影响证明审查、DECLARATION02声明审查，加本次精确分段与接口连接审查，完整覆盖当前234-LF源，未发现新的数学或source-to-statement相容性缺口。本结论仅为SOURCE接受，不是新候选已展开、编译、取得对象或修复unknown-fvar故障的证据；unit263仍未qualified。

评审者是同一保留上下文 `/root/oq56_unit263_review`。本轮只核组装、完整覆盖并集与受影响接口连接，没有重复整份旧证明或262已合格TYPE/核/AX判断，没有编写数学source或作者文件。保留最终review权，不签发FINALWRITE或权限释放。

## 激活、输入与实际阅读

首先读取SOURCE02激活 `47b3926d0eac609a0f4b883fdc9471423cf85aaa2035e17b491ed95ed9c4c916` /3882B，14个精确输入hash/bytes均通过。实质审查前封存SOURCE02-READ_ACK `c16029d81a687ebf2664fec3f3b8b00731e3347da62844a2cc2ebedf2d96c08a` /5041B。

完整8269B实施报告、两份完整源正反patch及当前新源1-79、169-184、224-234行的声明、证明入口、上游调用和最终连接实际读入。旧whole/repair01/DECLARATION02完整独立审查仍在本 SAME 上下文中，相关封存报告精确hash重新核对；不把这种有精确映射的复用称为第二次全文证明审判。当前完整163-LF证明文件的每个字节通过直接同一性检查；未声称本阶段又逐字语义重读其所有不变证明内容。

新源为 `author-repair-02/OriginalSingleWindowPhysicalRelativePolynomialRate.lean`，`3098a452f91dfc6bf81a4aab900cfad169d7e3fe6d2d37b8ac5959179e8b317c` /12628B/234LF。新PROOF为 `243399dc1432d9bdca85b93d28f0d4626a4f644c110c107d370943094c40733b` /9072B/163LF，与原repair01 PROOF完全相同。

作者完整实施报告为 `ea6be4289806bcb300b4f34b1218433e558d3ca4fec97d36935dc21360e0dfc9`；manifest为 `837d61cbe6f181d1e8d442d74d337eaa5c631a80797ad40e5080f865f55d6318`；最后作者释放为 `767582e0959460a0a7781d15afa28148b23185a7ba6cea0714a2bfcebd8d377a` /5646B。作者全部writer/execution/child/publication权已释放，顶层writers/heavy/inflight/uncertain/pendingExternal/children均0。manifest的26个唯一被引用本地绑定独立核对通过；加manifest本身为27，与实际集合相符。

## 独立精确分段检查

我独立用freeze02三个片段与完整旧证明重建新全源，并用原head与同一证明重建原4ac45376全源，两者均精确相等。直接对新源原始字节切片，与各精确片段原始字节比较，得到：

| 新源区段 | 新源行 | 零起点字节区间，左闭右开 | 精确片段SHA256 |
| --- | --- | --- | --- |
| PREAMBLE，483B | 1-13 | [0,483) | `731fd4119088bdc37fecfa1de86bc0197ffef728f4f62d4121686ff08645eccc` |
| freeze02 HEAD，3005B | 14-69 | [483,3488) | `be9dbe4419b940e63ea98666a7e101b851f56301fd10a6d968e5499f44c4c210` |
| 原完整PROOF，9072B | 70-232 | [3488,12560) | `243399dc1432d9bdca85b93d28f0d4626a4f644c110c107d370943094c40733b` |
| CLOSING，68B | 233-234 | [12560,12628) | `ac44bc9366e95880ea35f4b4ea2b2467167f933360b2339c2c7` |

因此证明分隔符仍由原PROOF提供，原证明完整位于新70-232行；没有在head与proof之间插入新命令、辅助声明或注释，也没有改写证明入口或尾部。新源较原233-LF/12552B的唯一总长度变化是head增加76B/1LF。

完整源的三个精确替换独立正反重建通过。两份完整源unified patch也从实际旧/新行序列独立再生成，与给定字节完全一致。旧1-59等于新1-59，旧61-63等于新61-63，旧67-233等于新68-234。所有改变都在声明中；patch中原证明第一行仅作上下文，证明本身没有变化。

SOURCE02-CHECK `887273388bac2b92b473eaefd28eba328f214d211cf01aa5aff3f8edbae866a7` /3742B封存上述原始字节、完整拼接及行映射检查。首次本地分段核对因PowerShell路径表达式分组错误，在写检查文件前停止；未修改source。修正为具名分段记录后，仅重做受影响的本地静态核对并全部通过。该本地失败和恢复事实保留在CHECK中，不冒充数学或Lean结果。

## 新声明与原证明的连接

原proof入口仍依次引入g/r/v/rho、固定p及其条件、外部packet、envelope参数、beta/K0/Ktail。E123没有更改这些外层let/forall的数量、依赖或顺序，也没有新增证明入口需要引入的假设。原proof的beta正性、固定c构造、rpow消去、eventually数值非空、统一n后才引入w/z及全部窗口推导，完整原字节保留；其原独立正确性审查继续适用。

三个显式化仅发生在最终统计量目标的局部mN/P/physical/event suffix。DECLARATION02已经完整接受：Fin.fintype n是原有限索引实例的明确项；Real.decidableEq判定同一sqrt(centeredSq)=0命题，两个分支仍为0及原分式；Measure.real显式给出原普通隐式mN，保留同一P和弱闭上尾事件。没有改变measure、Studentizer、Ktail、z窗口或任何数学前提。

我在新源实际入口和最终使用处检查这些连接。新173-175行仍是已接受的direct obtain及同一qualified262调用/原参数，新177-180行仍在引入w/z前交合原上游最终事件与数值非空事件。新229-232行仍按原顺序传递w及包络条件、z>=1、四个内部窗口、固定p/hgp/完整hSZ，再传正beta矩窗口，取同一结果的第二分量。

该最终分量的有限样本P、physical和Measure.real目标与所选E123表达同一数学项。DECLARATION02已只读核过qualified262公开实际TYPE中相同Fin.fintype、Real.decidableEq和显式mN的Measure.real片段；本轮复用该精确接口判断，不重复262整TYPE/证明/机器审查。透明inferInstance包装消除和普通隐式参数显式化没有新增数学接口要求。

这里接受的是source-to-statement组装相容性。旧263 header本身的成功展开项尚不存在，本阶段没有对新完整目标做Lean定义等同性检查。因此不能由“声明数学等价”或“原proof逐字不变”推断编译已通过；若后续出现实际elaboration相容性问题，必须按具体诊断处理，不能把本静态审查当作已运行的内核结果。

## 当前234行的完整独立覆盖并集

| 当前区段 | 覆盖来源及精确连接 |
| --- | --- |
| 1-13 PREAMBLE | 旧whole SOURCE已读并接受；本轮确认483B字节不变 |
| 14-69完整新HEAD | DECLARATION02完整56-LF语义/实例/等价性审查；本轮确认精确冻结片段及proof连接 |
| 70-232完整163-LF PROOF | 旧whole SOURCE加repair01受影响审查覆盖原完整证明；本轮确认9072B全部逐字不变，行号整体+1 |
| 233-234 CLOSING | 旧whole SOURCE已覆盖；本轮确认68B字节不变及关闭位置 |

并集的三份原独立报告分别是：whole SOURCE `1e32c3626d4fd883407ea2a5397e2f376316d1eeaaba2f789c8200947a7ae3c3`；repair01 `7833a3f4eb8b71a166a3759d20f81b0e1a23b1f0081709560ac343f807105270`；DECLARATION02 `91baf64576f58a3ede5e6f18fe95be5710330df9798413af24b9590dee664b36`。加本次精确组装、全字节映射和受影响连接审查，完整覆盖当前源每一行与所有实际改变，而不是把几份旧报告未经映射自动冠为新源通过。

所有原概率假设、p/external packet/envelope在存在c与eventually n之前的顺序、内部beta正性、beta<1消去、p=3/闭端点、四个其他窗口加矩窗口、最终非空数值窗口结论，均保持原已接受数学scope。原物理零约定、Ktail和率项保持冻结内容。单个源码theorem及proof-local maxHeartbeats800000不变，未新增helper；静态sorry/admit/axiom/unsafe/native_decide/omega匹配均0。完整新源与proof是严格UTF-8无BOM、CR0/LF、单终LF。

## 机器、权限与scope边界

本绑定材料中的新候选尚无已接受的native/原始对象/actual-owned机器审查包。unknown-free-variable的具体header故障点仍未知，本轮不证明E123修复成功。旧4ac45376源码和全部失败/诊断证据原字节保留。unit264的任何独立机器进展不属于本263证据，不为此候选提供资格。

本次SOURCE02接受后，后续仍需lead在服务器对精确新源进行新的source-bound native；仅成功时才使用同一first original O审计全部实际TYPE、所需非定理VALUE和每个owner的递归AX，并由本保留独立上下文完成最终审查。实际owner数量不能由一个源码theorem推断。此前262 qualified kernel/TYPE/AX复用，不重跑旧producer或leaf审计。当前machinePending=true、qualified=false。

原bounded-polylog产品包络、z>=1、原物理统计量、外部broader-L2 hSZ的明确条件归属及p54定性条件矩修正均保留。compact CDF/atoms、DC、unbounded conditioning、p54 uniform conditional consumers、external SZ、full OQ56/root仍OPEN。

本轮仅本地读、hash、精确字节/文本核对和评审证据写入，无数学source或作者文件修改、Lean/AX/server/network/Git/API/publication/children、Goal或schedule。请求仍为同一gpt-6.1-sol/xhigh上下文；实际model/backend/effort及input/cached-input/output/reasoning-subset用量未暴露，保持null。SOURCE02-MANIFEST封存证据，唯一CHECKPOINT-SOURCE02最后写，记录评审已停六零且retain final；不签发FINALWRITE，也不把可变checkpoint的hash放入不可变manifest。
