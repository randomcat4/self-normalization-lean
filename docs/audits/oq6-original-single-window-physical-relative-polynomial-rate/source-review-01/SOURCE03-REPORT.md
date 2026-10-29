# Unit263 SOURCE03 完整源覆盖并集与组装相容性

STATUS: CORRECT

JUSTIFICATION：完整新236行源已实际读入，精确等于freeze03 PREAMBLE +已独立接受的58行HEAD +原9072B/163行完整PROOF +原CLOSING。全部证明字节不变，唯一源差异是完整末项S的标准Prop包装。声明03的数学语义、原证明入口及最终结论的连接得到独立审查；旧完整SOURCE覆盖并集加本次精确组装与连接检查，完整覆盖当前源。未发现新的数学或source-to-statement缺口，接受SOURCE03。此为SOURCE接受，标准生产源尚无本阶段已接受的native、原始对象、actual TYPE/VALUE或递归AX证据；不继承诊断08的RC0，unit263仍未qualified。

评审者为SAME retained `/root/oq56_unit263_review`。本轮按明确扩展在同一turn接续声明与全源审查，没有修改数学源、证明、作者目录或旧证据。旧163行证明的数学正确性复用本人既有完整覆盖，不重新对相同旧证明或262 producer TYPE/核/AX作一轮独立判定。保留最终独立审查权，不签LASTFINALWRITE。

## 精确扩展、作者权限与实际阅读

完整读取并核验扩展 `ce63e9c70c206e3c1dd078362def68c0b809ba6276c90b4aac422906c17b887f` /4161B及其11个精确输入。实际SOURCE03-READ_ACK为 `ba5f1cca39df2693ba913eb3f50d04bd8760c972cf9dd3e7a35a8e4d871e942c` /4355B，在本阶段实质组装审查前封存。完整236-LF新源、完整8483B实施报告及两份完整源patch实际读入；implementation03激活、SPLICE/STATIC、manifest和作者LAST均完整解析。

新源为 `author-repair-03/OriginalSingleWindowPhysicalRelativePolynomialRate.lean`，`8dc80cf0296cdfa160f57af5618de17bbf45b8fea792a7500249c283acbaf56a` /12686B/236LF。原完整PROOF和新PROOF均为 `243399dc1432d9bdca85b93d28f0d4626a4f644c110c107d370943094c40733b` /9072B/163LF。

实施权限来自明确激活 `06157a7b5465d41d2d4ab6209f80276b804024f980c85ff22451fbf88a577a49` /4144B，只授权SAME作者在freeze03之后纯字节拼接；不把冻结/旧ACK签发时的未授权字段回写。作者完整实施报告为 `b8396b6d49712ef4fb15cbcaf179ac06640df7829194ef84519951e7cd68f0b0` /8483B；manifest为 `f28e67b2f245c0857863b45d7acf176afb0dcc997feb8fff38dc7ef40838adcb` /8183B。独立递归核对其20个唯一被引用本地绑定，加manifest本身为21个，全部hash/bytes通过。

作者LAST `457060fdecf6576099678c09774027c7a5801f1e04de7e253b1f91d0e13d110b` /6264B顶层allAuthorAuthorityReleased、writer/execution/child/publication释放字段为true，authorRoleRetained=false，writers/heavy/inflight/uncertain/pendingExternal/children均0。本报告据精确LAST记录其释放，不声称本评审另行观察了远端进程。

## 原始字节与完整差异的独立检查

独立用四个冻结/原证明输入重建新完整源；也用旧freeze02 HEAD和同一PROOF重建旧3098完整源，两者均精确相等。对新源原始字节直接切片，与对应输入原始字节比较，全部通过：

| 区段 | 当前源行 | 原始字节区间，零起点左闭右开 | 完整SHA256 |
| --- | --- | --- | --- |
| PREAMBLE，483B | 1-13 | [0,483) | `731fd4119088bdc37fecfa1de86bc0197ffef728f4f62d4121686ff08645eccc` |
| HEAD，3063B/58LF | 14-71 | [483,3546) | `3c95d7ec4d27d37712930ecba1739606da14d2642dc7c6633452c61678a06d8c` |
| 原完整PROOF，9072B/163LF | 72-234 | [3546,12618) | `243399dc1432d9bdca85b93d28f0d4626a4f644c110c107d370943094c40733b` |
| CLOSING，68B/2LF | 235-236 | [12618,12686) | `ac44bc9366e95880ea35f4b4ea2b2467167f933360b233a6c346673b2339c2c7` |

上述closing的完整64位SHA256由实际68B文件计算并保存在SOURCE03-CHECK/JSON元数据。已封存DECLARATION03报告prose中的closing hash显示截短；原报告保持 `90fae46e2733b98e55b371793184fbe2da9cfed62930bff5556b57f4bf8df599` /11942B不重写。freeze03、原始68B、完整JSON绑定和本次完整指纹一致。该显示澄清不涉及数学、声明、proof或历史字节改变，也不触发重审旧证明。

新旧完整源的精确映射是：旧1-66等于新1-66；旧67-69的同一S成为新67-71标准wrapper；旧70-234等于新72-236。后者包含完整原PROOF和CLOSING，逐字相同。总差为+58B/+2LF，改变完全止于主证明分隔符之前。

我独立执行唯一末项替换及其反向，分别精确重建新/旧完整源。另从实际新旧行序列再生成两份完整unified patch，与给定1021B patch逐字一致；用独立内存hunk读取器核对起点、上下文、删除项和旧/新计数后实际应用，正向精确得到新全源，反向精确恢复旧全源。没有调用Git/外部patch工具，没有仅以文本相似性替代补丁应用。

SOURCE03-CHECK为 `485583b366c52a04ae1f5b26d859554dd813f64597b3a52ff316716d441731fb` /3337B，封存完整四段切片、旧/新组装、逐字proof同一性、双向重建/补丁再生成/实际应用及派生计数。

## 声明与原证明的相容性

DECLARATION03完整审查已接受58行HEAD：旧HEAD前53行逐字不变，完整原末项S从新wrapper逐字恢复。内部 `show Prop from by exact(S)` 的目标是Prop，交付的是S本身，不是S的证明。它不把主定理目标弱化为Prop，不增加S假设，不引入数学运输或公理；主定理仍需要原PROOF证明同一个嵌套上下文中的S。

当前完整源将该HEAD准确放在14-71行，原PROOF的 `:= by`仍从72行开始。完整proof与旧版相同，因此75-76行的intro顺序仍为g/r/v/rho、固定p及其条件、完整外部packet、包络参数、beta/K0/Ktail。终端wrapper没有添加这些外层之前的新forall/let，没有移动g或改变真实beta积分，也没有使c或最终阈值依赖后来选择的w/z。

当前175-177行仍是同一direct obtain、同一qualified262 theorem和原mu/h/原假设实参；179-182行仍先交合统一最终事件和数值非空，再引入w/z。当前231-234行仍按原顺序传递原w及包络条件、z>=1、四个内部窗口、固定p/hgp/外部packet，再传正beta矩窗口并取结果第二分量。这个第二分量仍是包装内部逐字同一的S。

标准透明展开按预期返回S时，原proof与新最终目标无需新的数学等式运输即可连接。此为完整SOURCE的数学接口相容性接受，不是已经对新源运行的Lean定义等同性检查。生产wrapper具体求解时机、全部实际展开项和生成owner仍需正式新源机器证据。若出现实际elaboration问题，必须按具体诊断处理，不能用本报告覆盖失败。

所有原假设、真实beta、共同c/Ktail、单一闭窗口、p/external packet/envelope在存在c及最终n之前的顺序、原physical零分母约定与完整率项保持冻结内容。原beta内部正性、beta<1消去、p=3/闭端点、全部四个其他窗口及矩窗口、最终数值窗口非空的证明内容无一字节改变；其完整数学正确性沿用本人旧已接受覆盖。

## 当前236行的完整独立覆盖并集

| 当前区段 | 覆盖来源与本轮连接 |
| --- | --- |
| 1-13 PREAMBLE | 原完整SOURCE覆盖复用；本轮483B切片、导入/选项/namespace精确同一 |
| 14-71完整新HEAD | 本轮同上下文DECLARATION03完整58行语义/预期定义等价审查；本SOURCE03核精确冻结片段及入口/末端连接 |
| 72-234完整163行PROOF | 旧whole SOURCE与repair01覆盖、DECLARATION02/SOURCE02连接判断沿用；本轮完整新源实际阅读及9072B逐字同一映射 |
| 235-236 CLOSING | 原完整SOURCE覆盖复用；本轮68B完整指纹及结束位置精确核对 |

关键旧封存报告包括whole SOURCE `1e32c3626d4fd883407ea2a5397e2f376316d1eeaaba2f789c8200947a7ae3c3`、repair01 `7833a3f4eb8b71a166a3759d20f81b0e1a23b1f0081709560ac343f807105270`、DECLARATION02 `91baf64576f58a3ede5e6f18fe95be5710330df9798413af24b9590dee664b36`及SOURCE02 `88845c7645a9c632e8a8511cbbfb1c7134ee55651bba4695165f97b72579d3d3`。DECLARATION03 `90fae46e2733b98e55b371793184fbe2da9cfed62930bff5556b57f4bf8df599`与本轮精确映射/连接审查补齐唯一新变化。

这给出当前236行每个字节和全部受影响数学依赖的完整并集覆盖，不是将若干旧报告不经映射自动称为新源通过。旧262 qualified source/first O/全部TYPE/核/递归AX保持原证据复用，没有重复旧producer或leaf检查。

## 静态证据与未完成机器阶段

当前源有一个源码public theorem，一个主proof分隔符；header中新增的是一个标准Prop项by。原proof-local maxHeartbeats800000唯一设置及autoImplicit等选项不变。sorry/admit/axiom/unsafe/native_decide/omega静态匹配均0，没有生产诊断elaborator/macro/IO/日志或新helper。所有所读源、proof、冻结片段和patch均严格UTF-8无BOM、CR0/LF、单终LF。

诊断08的RC0/PROOF_ENTERED/no-error来自特定无-o强制terminalProp诊断，strict-wrapper false及31 warnings原样保留；它没有运行本8dc80cf0生产源，没有生产O，不为本SOURCE03提供机器pass。旧失败、3098 canonical与相关诊断记录保持原字节。没有断言唯一根因或编译器bug。

本次SOURCE接受后，正式native必须绑定精确8dc80cf0源；成功时才审同一first original O及全部actual-owned TYPE、所需非定理VALUE和每个owner递归AX。实际owner数量与种类不从一个源码theorem推断，header内by若产生辅助声明也必须纳入。标准公理白名单仍为propext、Classical.choice、Quot.sound。当前actual TYPE/对象/AX审查均pending，qualified=false。

原p51 S19 bounded-polylog产品包络、z>=1、原真实物理闭上尾、固定正beta逆幂单窗口scope保留，明确条件于更广L2 scalar hSZ packet。p54仍仅定性条件矩收敛与最终一致界，不加入任意多项式条件收敛率。compact CDF/atoms、DC、unbounded conditioning、p54 uniform conditional consumers、外部SZ本身、full OQ56/root均OPEN。

本轮无数学source/作者文件修改、Lean/AX/服务器/网络/Git/API/发布/children、Goal或schedule。请求仍是同一gpt-6.1-sol/xhigh；实际model/backend/effort和input/cached-input/output/reasoning-subset计数未暴露，保持null。最终CHECKPOINT-SOURCE03最后写，记录实际六零闲置和最终独立审查权保留；不签LASTFINALWRITE，不把可变检查点hash绑入不可变manifest。
