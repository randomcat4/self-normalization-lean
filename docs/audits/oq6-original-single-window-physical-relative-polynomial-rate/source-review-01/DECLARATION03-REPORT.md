# Unit263 声明03：完整末项 Prop 包装的独立审查

STATUS: CORRECT

JUSTIFICATION：完整旧56行和新58行HEAD已实际读入，前53行逐字不变，原最后三行完整不等式命题S可从新包装逐字恢复。标准 `show Prop from by exact (S)` 在目标类型Prop中交付原命题S本身，保持原目标命题和全部外层依赖，不是S的证明，也没有替代主定理的原证明。新写法与原命题具有清楚的预期项级定义等价性，原证明入口和最终结论的数学接口保持相容，未发现关键数学缺口。本结论只接受声明写法；标准生产包装尚无本阶段已接受的编译、实际TYPE或机械定义等同性证书，更不是unit263已经qualified。

评审者是SAME retained `/root/oq56_unit263_review`。旧whole/repair01/DECLARATION02/SOURCE02的完整独立覆盖并集在同一上下文中保留，精确hash复用；不重复旧163行证明或262 producer的整TYPE、证明、核/AX审查。本轮无数学源或作者文件修改，只写本评审目录的DECLARATION03-*证据。保留最终独立审查权，不签LASTFINALWRITE。

## 激活与实际材料

首先完整读取激活 `8b36f63ce870e7e6508c7828ff9b4d0b96d2bd14f3931ccbe2e6282765643c43` /4746B，16个输入逐一核验hash/bytes。实际READ_ACK在实质审查前封存为 `e0605e190fcfb24ce4217d7e8903a611ff2388e15c6190f3229ba0c36415624f` /5666B。完整旧/新HEAD、13行PREAMBLE、新freeze JSON、13173B提案报告和2041B诊断08规范化记录均实际读入；STATIC-CHECKS、manifest和READY完整解析。提案manifest的23个唯一被引用本地文件hash/bytes独立通过。

freeze03是 `16f62b0698b7c621e90c944434b2bc010c40c894e68b1cbb7cfb5bc1ba4c9a73` /2197B；新HEAD是 `3c95d7ec4d27d37712930ecba1739606da14d2642dc7c6633452c61678a06d8c` /3063B/58LF。旧freeze02 HEAD是 `be9dbe4419b940e63ea98666a7e101b851f56301fd10a6d968e5499f44c4c210` /3005B/56LF。PREAMBLE仍是 `731fd4119088bdc37fecfa1de86bc0197ffef728f4f62d4121686ff08645eccc` /483B/13LF；CLOSING仍是 `ac44bc9366e95880ea35f4b4ea2b2467167f933360b2339c2c7` /68B/2LF。原完整证明仍为 `243399dc1432d9bdca85b93d28f0d4626a4f644c110c107d370943094c40733b` /9072B/163LF。

提案报告为 `21d5d1e59ec347fe440160be23a60c9b4ed0df323eb3788714fe1b476282ae3c`；其READY `9ed7b4de27c54e3c00fa2ff2506c37d1b9c884c8c63c9131bd2d9761fd70d337`记录作者停写六零，保留proposal到implementation的同作者角色。该停写不被误称全权释放。原3098源和9072B证明只读绑定不变。

## 标准包装的精确逻辑含义

设Gamma为原全部局部let/量词上下文，S为旧HEAD54-56的完整末项不等式。在Gamma中S的类型是Prop。新项 `show Prop from ...` 给内部项指定的预期类型恰为Prop；内部 `by` 的目标也是Prop。`exact (S)`交付的是具有该类型的原命题项S，因此包装的预期结果就是S。

这与提供一个 `h : S` 完全不同。包装没有证明S，没有从Prop的可构造性推出S为真，没有把主定理目标换成“存在某个命题”，也没有增加一个S假设。主定理仍以原嵌套上下文中的S为最终待证结论，仍需原9072B证明体。这里没有sorry、额外公理、propext步骤、等式运输或把目标改成True。之所以能作此判断，不是因为包装在一般情况下“看起来无害”，而是因为内部exact的实参已精确恢复为原完整S。

新HEAD前53行仍是同一个外层上下文C，唯一改写为C[wrapper(S)]。标准show/类型注解和exact若按预期成功展开，wrapper(S)交付S，故整个C[wrapper(S)]与C[S]逐项定义等价。这里没有交换量词、移动let、增加函数参数或运用新的数学引理。标准语法可能改变约束何时收束；这属于待实际验证的展开行为，而不是数学命题变化。

必须区分预期定义等价与已取得的内核证书。原3098目标以unknown-fvar失败，没有可用的成功实际TYPE；本阶段也没有运行新标准包装。因此我没有机械确认两个成功展开项的定义等同性，没有确认所有推断节点实际生成的最终项，也没有由标准语法推断机器一定成功。后续必须读取精确新源的实际TYPE和所有实际owned声明，确认没有目标替换、未解决作用域、隐藏新假设或遗漏所需非定理VALUE。

## 原数学接口逐项保持

前53行的直接字节同一性覆盖原Omega/mOmega/mu及概率实例、原可测对称L2核、中心化和投影二阶矩恰为1；覆盖所有g/r/v/rho定义、固定p及hgp、完整外部hSZ packet和固定envelope参数；也覆盖真实beta积分、K0/Ktail、共同c、全部窗口与原物理定义。末项S的独立反向提取则覆盖完整真实概率比率和两个率项。

| 接口 | 本次核对结果 |
| --- | --- |
| 原law与假设 | 任意Omega、原mOmega/mu及概率实例、hh/hh2/hhsymm/hcenter/hprojectionsecond全不变；无标准Borel、无原子、额外矩或非零Studentizer条件 |
| 原派生量 | g仍是原投影积分，r仍是h-g-g，v仍是原产品测度的r平方积分，rho仍是sqrt v；均为原let，不是新增任意参数 |
| p与外部packet | 2<p<=3、原hgp、cSZ/C1-C4和同一个更广L2 hSZ条件输入仍在存在c之前；外部结果未被无条件化 |
| 真实beta与同一常数 | beta仍为原mu下积分|g|^p，未换成上界/任意beta，未增加beta>0或beta>=1假设；K0/Ktail全部系数及exp项不变 |
| 共同c与最终一致性 | 存在c及正性之后才eventually n，随后才forall w/z；n>=4及数值窗口非空仍是结论，最终阈值不依当前w/z选择 |
| 唯一闭窗口 | z>=1及z<=c beta^(-1/p)n^((p-2)/(2p))原样，四个辅助窗口未回到公共前提；p=3、闭端点和beta<1的原处理保留 |
| 真实有限样本law | mN、Fin.fintype n、原mu的Measure.pi、原D1及显式Measure.real(mN,P,event)不变，没有替代概率模型 |
| 真实物理零约定 | 同一个sqrt(centeredSq)=0判定、Real.decidableEq及physical=0分支；其余为原(projectionW+D1)/sqrt(centeredSq)，没有换Studentizer |
| 完整目标S | 原弱闭上尾事件、标准正态尾除法、减1、绝对值、<=、共同Ktail及完整两项率均从包装逐字恢复 |

旧完整SOURCE并集已接受的beta内部正性、q范围、固定c构造、正beta幂消去、全部内部窗口、最终数值非空和同一unit262应用的数学论证仍适用。本声明不修改该证明的任一字节，也不重复审判其证明内容。

## 与原证明入口和末端的连接

新包装只位于原终端S处。原proof开头依次intro g/r/v/rho、固定p及其条件、外部packet、envelope参数、beta/K0/Ktail的结构和作用域完全没有变化。没有新增需要intro的forall或let，也没有把某个局部值提到作用域外。

原proof最终同一qualified262调用与正beta矩窗口返回的第二分量仍是同一个S。包装的预期透明展开不要求新增数学运输、修改窗口常数或改变这次上游调用。旧DECLARATION02和SOURCE02对同一mN/P/physical/Measure.real接口的已接受判断精确复用，不重新读取262全部实际TYPE或执行producer/AX。此处接受的是声明层的数学连接；正式新完整SOURCE的精确拼接与实际elaboration连接须在其具体绑定到达后完成，不由本声明报告自动宣告。

## 精确文本检查

独立核对旧/新HEAD的前53行逐字一致。以旧54-56行的完整S生成唯一标准包装后，精确重建新58行HEAD；反向替换精确恢复旧完整HEAD。进一步从新56-58行移除新增包装括号和相应缩进，恢复的完整三行S与旧末项逐字相同。没有仅按字符数量或关键词近似判断等价。

DECLARATION03-CHECK `b6fe751a60893831f36e0a64be322add76f1828f263a6715fa1a6417ef19dff2` /2389B记录这些独立检查，以及原preamble/closing/9072B证明的精确绑定。新HEAD有一个theorem和一个标准局部by，主定理证明分隔符 `:= by` 数量为0。没有自定义elaborator/macro、IO、日志、全局选项、辅助声明或新实例，禁止的sorry/admit/axiom/unsafe/native_decide匹配为0。所读片段为严格UTF-8无BOM、CR0/LF和单终LF。

首次本地静态脚本因短函数名与PowerShell的ls别名冲突，在写检查文件前停止；没有源或证据文件写入。改为专用TextLines03名称后，只重做受影响静态项并通过；失败恢复事实保留在CHECK中。它不是Lean或数学失败。按冻结片段加原证明计算的未来组装大小为12686B/236LF；这是计算值，不是已经读取或接受的新全源。

## 诊断证据的实际边界

本轮完整读取08规范化记录 `d7223175f9329034dec598dde223b941ddab5750cc24790055d4c8a78693ccd4` /2041B，其绑定receipt为 `716c460f451ba82130497cc0e91ce7073c7de0b3abc34088a79c4af7edb6dbe7` /31532252B。08仅在terminalProp强制合成，记录实际RC0、7.716101575642824秒、13个选定header term完成、terminalProp SYNTH_BEGIN/DONE和PROOF_ENTERED，errors为空。31个warnings、strictWrapperSuccess=false、no_o=true、canonicalObjectAbsent=true、qualified=false均原样保留。它没有生产原始对象，也不是标准show/exact候选的运行。

05规范化材料和1280B g映射的精确绑定经manifest核对；本轮完整读g映射，选读解析05/06的实际RC、sourceErrors、missingReferenceObservations及无对象/未qualified字段。05为RC1、可见missingReferenceObservations空，错误显示_fvar.16399；映射定位到let-bound g，但不能定位未决约束的产生项。06全部选定term及时强制合成后RC0、sourceErrors空，仍是无对象诊断。07仅gInit合成仍RC1/no-proof-entry按lead提供的实际观察保留；本次没有声称读取其完整原回执。

这些事实支持在终端命题边界尝试局部收束的有针对性方向；它们不证明标准show/exact与诊断中的强制合成在所有展开细节相同，也不确立唯一根因或编译器bug。尤其不能由08诊断RC0改写标准wrapper为“已编译通过”，不能把旧失败或strict-wrapper false回写为成功。

## 后续权限、机器门与范围

本任务激活与ACK签发时声明尚未接受、未授权实施。之后lead明确告知已在同一freeze03后对SAME作者签发06157a7b/4144B纯字节拼接激活，写独立author-repair-03并保留9072B证明；这一后续授权作为过程消息保留，不覆盖旧ACK或freeze历史字段，也不另设冻结后拼接的等待门。本声明报告本身不新增执行权。新完整SOURCE只有在精确source/manifest/LAST扩展绑定到达并接受组装/覆盖并集后，才可标注SOURCE接受；正式服务器源/Lean仍以该门为前提。

标准wrapper的生产展开、实际TYPE、first original O、全部actual-owned TYPE/所需VALUE/递归AX仍待后续证据。可能生成的实际owner数量或种类不能由源码只有一个theorem推断；必须实际枚举和覆盖。unit263仍未qualified。旧全部源码、失败、诊断和已接受证据原字节保留。

范围仍是原p51 S19 bounded-polylog产品包络、z>=1、真实物理闭上尾、固定正beta逆幂单窗口，明确条件于更广L2 scalar hSZ输入。p54仍仅保留定性条件矩收敛及最终一致界，不增加任意多项式条件收敛率。compact CDF/atoms、DC、unbounded conditioning、p54 uniform conditional consumers、外部SZ本身、full OQ56/root均OPEN。

本轮只有本地读/hash/精确重建与评审证据写入，无数学source、作者文件、Lean/AX/server/network/Git/API/publication/children、Goal或schedule操作。请求仍为SAME retained gpt-6.1-sol/xhigh；实际model/backend/effort及input/cached-input/output/reasoning-subset未暴露，保留null。结束检查点将记录实际六零闲置及最终独立评审权保留，不签LASTFINALWRITE，不将可变checkpoint的hash放进不可变manifest。
