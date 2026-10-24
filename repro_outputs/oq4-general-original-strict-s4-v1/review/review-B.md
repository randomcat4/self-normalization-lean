# B：RademacherOriginalStrictS4 独立完整终审

STATUS: CORRECT

审稿人为 context217，fresh gpt-6.1-sol / xhigh，独立于B作者（OQ4负责人）和A作者216。B的完整最终源、首次成功对象、kernel/owned-AX收据及明确停止释放到位后才开始证明审查。完整读187行实现、三个实际native完整类型、唯一非定理的完整值及全部21个直接项目接口类型/非定理值。A已完成的报告与收据保持原字节，B仅复用其精确源版本的资格和消费接口，不重复A证明全文审查。

精确源为 attempt002/Source.lean，SHA256 `4374e07fbb24f9223543abd6c6bb35fc4e19796b290740946303725bc9ab389a`，8688 bytes /187 LF，无CR/BOM；冻结为 `8a6293eb072e81b11e43a26f90a90e9e0bc890960507b457b285a9bb753c4f61`。前导、全部三个声明、唯一sourceQ完整定义值逐一匹配冻结，未增加头或改变数学假设。attempt001的失败与body-delta保留；唯一修复是在 n=0 分支重写前加入 Nat.cast_zero 化简，不改变类型、定义或结论。

## 原文和陈述忠实性

本批次的原 spectrum01.md 已全文阅读，直接范围仍是第4节固定 Rademacher 严格边界。sourceQ 的分子是原样本空间 μ 下的真实事件概率：对每个1≤r≤n，|Σ_{i<r} X(i+1)| < (h/√n)√sourceEnergy(n,X)。已阅读 sourceStrictEvent 的实际完整值，以及 sourceEnergy=energy(sourcePath)、sourcePath(i)=X(i+1)、energy(v)=Σ_i v_i² 的定义；并非把随机能量改为一个自由标量。分母是给定B/P/hB的实际布朗上确界弱概率，阈值h/√n。X0完全未使用。

ΩX和ΩB分别量化在独立宇宙uX、uB，没有隐含相同空间或耦合。原空间只要求概率测度、正下标族iIndepFun和IdentDistrib到固定±1各半律；没有新增全体普通Measurable、完备性、矩或独立于B等假设。IdentDistrib所带的几乎处处可测条件由已合格传输定理处理。

## source_strict_probability 全量词证明

先对任意n和s=h/√n应用已合格的 OriginalStrictBoundary.source_strict_probability，将原空间真实能量事件概率变为规范有限向量自归一化事件概率。接口完整类型与当前原对象绑定均已核对；旧证明资格复用，不重新审旧proof。

n=0分支没有除以√n的合法性要求。两个事件都只量化正前缀1≤r≤0，故为univ，zero_time完整接口分别返回严格事件概率1与自归一化事件概率1。两个投影使用位置正确，Nat.cast_zero补充化简只使现有等式可重写。没有误将r=0加入严格条件，也没有把“最大值取0”与空正前缀条件混淆。

n≠0分支推出n>0及√n≠0。actual_path_support的完整类型在同一个满测集上给出所有坐标±1、整数前缀、energy=n、V=√n；当前证明只消费其最后一项。对该满测集中的v，(h/√n)V(v)=h 对所有实h均成立，包括h≤0。因而两个规范事件的谓词在该满测集相等；用measure_congr获得ENNReal测度相等，再由congrArg ENNReal.toReal得到真实概率相等。没有断言事件在全空间相同，也没有把原空间任意样本的能量逐点替换成n。该定理确实覆盖全部自然n与全部实h。

## original_strict_S4 的两类事件与四个极限

对精确A声明传入同样的h→∞、n/h²→∞和n/h³最终固定正上界，取出规范真实概率共同正尾部、修正对数误差和标准化比值极限。B的hsource对每个n,h精确成立，故hQ逐k给sourceQ=canonicalQ，即使早期分母为零，实数总定义的除法两边仍相同。

确定阈值原事件的概率等式hdet仅在h>0尾部调用已合格 source_ceil_boundary_bridge；h→∞确实给出此尾部。该接口返回的μ.real(sourceDeterministicStrictEvent)=strictP是第三项，当前 .2.2.1 投影正确。未把非整数前提或全局h>0补入命题。

source的两个极限由逐k精确hQ经congrArg及Tendsto.congr'传递。确定事件/实际布朗分母与sourceQ在hdet尾部相等，故另外两个极限由最终相等传递；方向均正确，使用的修正仍是A的(π²/4)(n/h³)(ceilh−h)。最后在hpos与hdet的交尾部，同时导出两个真实原事件概率、实际布朗分母、sourceQ、确定事件比值五项正性。没有把结论正性作为输入，也没有声称有限早期比值正。所有声明保持原冻结量词，未见关键缺口。

## 全部实际声明、图与首次成功证据

实际owned恰为三个公开声明：sourceQ、source_strict_probability、original_strict_S4；1 definition /2 theorem，private0/generated0/source-instance0。三个完整native类型及唯一完整定义值都已阅读并与源义核对。18份compact文件的长度及SHA256独立逐字节验证；source+换行+audit suffix也精确等于Combined。A的三个消费接口（strict_S4_EVENTUAL、Q、correction）的native完整类型/定义值与A已经审阅的native记录字节一致。

一次服务器只读已保存audit-native.json并独立遍历全type AND value图：未过滤environment difference、实际模块ownership、stage2集合均恰为owned3。由这三根可达全部61238个保存节点，没有缺失或无关节点；实际图归属重算project declarations672、modules33、imported project modules101。外来直接type/value引用集合恰为176条，其中21条项目接口，完整native owned投影与本地文件的canonical JSON哈希一致。

逐个owned根独立遍历axiom-kind依赖，三个根均恰为propext、Classical.choice、Quot.sound，并与其保存collectAxioms输出一致；全图无unsafe/partial及其他axiom。source无sorry/admit/新增axiom/unsafe/native_decide。saved audit SHA256为 `323d960dd11ae2e2eaec4bee736beb2e258cd486a9a3af3b4dad8bdae9881e18`。

复用首次成功实际Lean PID866706：exit0、17.341595547273755秒、未超时、已回收；autoImplicit=false、skipKernelTC=false、trustLevel1025，固定项目Lean v4.36.0-rc1及既有mathlib版本。执行收据SHA256 `798828732bf07087d1cc59b289d76203161effaf19ff3ecd3cc09eaf4f20e396`；Combined `87ae959f93314506b47f83630263faa38e8176f3ad1c7c4b433dea9967ae50d1`；首次对象 `962351411a1fccf993d9c093511455e4c4919f843f8f50073297608ed334a0aa`。当前对象stat与首次完全相同：device64947/inode4981243/size148112/mtime_ns1792823930760507357；当前实际编译Combined文本哈希相同。

全部101个已保存项目对象的resolved路径及stat均与当前一致；只做stat，没有读或重hash旧binary。直接A原对象仍为device64947/inode4981026/size1542640/mtime_ns1792823065034903399，同一source935753f4/Combinedb73f07c2/对象254979a4，准确接上本审稿已完成A收据3c1d605d…。OriginalStrictBoundary旧对象及RealStrictBoundary旧对象分别与已合格211/214证据的精确stat一致。旧证明资格按用户规则复用，没有追加旧producer编译或旧证明完整重审。

本审稿对B新Lean/parser/build/nativewalk均0，旧对象内容读取/重hash/旧producer重编均0；仅保存JSON图遍历、当前新Combined文本哈希和对象stat只读核验。两次本地只读元数据脚本遇到dict/list投影形状差异，修正索引后通过；未触及输入或生成Lean执行，不是数学/内核失败。原作者的attempt001真实失败另行完整保留。

认证范围是固定Rademacher律、给定实际布朗运动下，原AE iid正下标真实能量及确定有限和两个严格事件的上述一般序列S4。没有认证一般增量律、严格临界整列相位/极限点集，也没有关闭原OQ4或其他原根。全部原根仍OPEN；新颖性/会议价值不在本次终审范围。
