# 单元191：最终证明差异与完整实际机器证据审查

STATUS: CORRECT
QUALIFICATION: QUALIFIED_EXACT_SOURCE_UNIT191

本资格仅绑定ActualSignedDoubleTelescope.lean的a05fc009d513978b9605af7ca384579c0a409db49cd68a7b3940685b12ac45d0，24641字节／448行，及本报告绑定的内核对象、32项实际所属声明的完整TYPE、8个完整定义VALUE与递归公理。189、190沿用已经接受且未变的独立资格包；C2/C12仍OPEN。

## 原证据保留及本轮边界

原始完整静态审查的21payload、SEAL、RELEASE重新哈希PASS，字节未变。continuation-machine-delta-v2的26个through190 sealed payload、SEAL-through190（ef96f46d19ded71d584c056b3442e8add33cf43b7de6dee93cc861ced3fa61a0）、RELEASE-through190（27fa96c508a866047e087801716fd59f25fcec6fb4e611c66701d612b2f024eb）也全部原字节。没有重新阅读或重审已经完成的189／190实际类型和旧合格证明。本轮只写新的continuation-machine-delta-v3目录。

源链为原完整审过的044b87e87bdca7db5d69e949a7737d334a5dbab95d2bb000337fc2dfbb3f6536，经已保存cb53d8448cd97af9f82694bd4f0966e5df2e0e0236838008a8788d90f9a6f743，得到最终a05f...。分别重新生成原始→最终及cb53→最终的统一差分，均与保存的完整delta-from-static-reviewed-source.diff及repair002-proof-delta.diff逐字相同。原始开头context、局部labelPermMeasurableSpace实例、5个完整def value、2个public theorem head均逐字不变；源码级计数为7个命名def/theorem加1个局部实例。改变仅在2个public proof，未增加假设或全局helper。

## 两个证明的实际差异及相互作用

actual_double_value_boundary：

- 包含排除中把已失效的Set.univ_diff名称改为反向Set.compl_eq_univ_sdiff，仍是univ\U=Uᶜ，没有改上／下事件或测度。
- Q=0的两个rank0弱crossing见证增加he，即已经在原证明中建立的energy(reorder a sigma)=energy a。它只把重排后的actualWall还原到同一实际能量0；r=0、prefix=0、wall=0，两个弱不等式含等号，double value仍为1。
- endpoint hEnds的半线分支显式展开Interior；缩放hScale的三个分支显式展开eventCompletionKernel；terminal hUp／hLo显式展开Interior及局部w，并用原hs重排总和等式。这些都是同一个冻结透明定义的展开，未改严格生存、真实终点、sqrt(Q)缩放或剩余能量。
- 原reachable T=0证明、全历史flags、同一个Q下E_I=E_U∩E_L、每个r≤n的概率范围、rank0等于190.observable、rankn等于实际重排样本双弱crossing均保持原样。没有以当前一次crossing替换历史事件。

actual_double_stopped_telescope：

- 在原hZfun／hLfun／hOfun重写后显式change为逐点函数的三个积分；对嵌套integral_sub给显式f／g lambda。
- Z的f正是(A_I-I_I)-(A_U-I_U)，g正是(A_L-I_L)；L的f正是LS_I-LS_U，g为LS_L；O的f正是OS_U+OS_L，g为OS_I。全部符号及同一mu不变。
- 每次integral_sub依旧消费先前已经取得的真实hInt／hLSi／hOSi integrability；没有用裸补偿系数的L1替代余项可积性，也没有删除积分存在条件。
- 三个同nu的已证明域telescope仍通过同一linarith组合成∫Z=∫L-∫O。任意signed bounded mask保留等式；最后只有hm0:∀a,0≤m a才得到∫O≥0及∫Z≤∫L。原同桥实际导数族、KernelBounds4、实际Brownian反射与interval regularity输入的生成方式均未改变。

完整差异审查结论CORRECT。和原完整source→statement审查的未变阅读合并后，最终a05f源码的全部数学证明／语义覆盖完整；没有重审未变旧证明，也没有 silently strengthen assumptions。

## 实际内核、对象及完整owner审计

kernel002-exit.json记录自然kernelExit=0，08:47:19–08:47:26Z；sourceSHA256与sourceAfterSHA256同为a05f...，sourceUnchanged=true。对象SHA256为24b3dfe0313560ab730f6fe8383b26bfdf445090469d33959761a47b13506622，object-copy-map对同一对象进入本worktree标准import路径验证true。

audit-exit.json记录实际exitCode=0，08:48:08–08:48:14Z，源及对象完全相同。实际OwnedAudit.lean哈希4297805c36368ead6633c666c889d99ff558ce8864f1a992253fab6c697d6a29，已完整读取。脚本通过env.getModuleIdxFor?选取实际defining-module owner==目标模块的全部constant，没有按namespace前缀筛选；每项调用递归Lean.collectAxioms，遇到白名单外项即失败；两个冻结public target必须实际找到且为theorem。

owned-audit.json实际哈希386acd82ac6ff765931ba716008d344d4274381ab93eac0d87d82349e9b15ac8，与audit-exit一致。实际32owner=24theorem+8definition，public2；完整TYPE的32个唯一名字与owner map精确集合相等。所有所属声明递归公理仅为propext、Classical.choice、Quot.sound的子集，部分匹配分派生成项为空公理集。没有忽略private、generated、local instance或foreign namespace。

另核对restart/191-kernel002-response.json、191-audit001-response.json的外层exit_code都为0，首个实际收据JSON与上述下载收据逐字段一致。实际raw类型日志哈希6f965b7a1c5ba1811e2d11103e1842333e9a32658391175610230c634a73bb12、源、对象、audit源码和owned receipt均交叉绑定一致。

cb53候选的kernel001实际kernelExit=1、source before/after未变、object=null，原失败另行保留，不作为成功或不确定inflight处理。父修复脚本曾出现预期匹配数1、实际2的本地断言；按保存的repair002-parent-candidate.json，该断言前未写源，原snapshot保留。最终源与两份完整差分及kernel002／audit001是独立确证的后继。

post-machine-zero-observation.json实际观察时间08:54:33Z，ownNative=[]且c12LockFree=true。该观察仅说明完成后的实际零检查／锁释放，不是数学证明；本审查没有新开检查或占用heavy slot。

## 全部32完整实际TYPE和8完整VALUE

actual-types-values.txt完整137879字节，SHA256为4d42cb182c0a99a66d6569dcddaf61854ff402715a9429932b79670a64960183。原index从raw log字节150至138029，40个连续block（32TYPE、8VALUE）的边界、长度及SHA256全部重新验证；没有省略或截断符。

采用14个精确重复子表达式字典。完整读完字典6646字符及40个压缩block的32909字符；另保留原空白表。字典展开并复原空白后与原137879字节完全相同，SHA仍4d42...。全部universe、实例、量词、分支和实际表达式均保留；类型／值摘要没有充当阅读覆盖。可复验文件为191-full-types-values-lossless-dictionary.json、191-full-types-values-lossless-blocks.json、191-full-types-values-lossless-whitespace.json和191-lossless-roundtrip-validation.json。逐项40块的完整阅读／来源合同在unit191-all-owned-type-value-coverage.json。

两条public完整实际TYPE：

- boundary保留任意桥概率测度Q、x>0、有限path及排列；对每个r≤n给0≤actualDoubleValue≤1，rank0精确等于190.initialDoubleObservable，rankn精确等于reorder a sigma落入实际doubleCrossingEvent的指示。
- stopped telescope保留调用者实际IsBrownianReal B PB、任意概率law P、x>0、H>0、同一个可测reveal stopping rank nu及其真实energyCutoff上界、可测permutation-invariant |m|≤1。Q精确等于bridgeLaw B PB；Z、L、O精确保持冻结点态值。结论含O_D逐点非负、Z/L/O三者真正Integrable、积分等式，以及仅在m≥0时的单向不等式。没有暗加iid、moments、额外Brownian比较或kernel target假设。

八个完整实际非theorem VALUE：

1. labelPermMeasurableSpace为MeasurableSpace(LabelPerm n)的实际Top.top，完整展开的complete lattice实例也已阅读；与真实revealLaw所用旧离散⊤实例定义相同，不改变产品测度。
2. actualDoubleValue恰为同Q的1-sourceValue.upper-sourceValue.lower+sourceValue.interval。
3. actualDoubleRetained恰为同Q、同a/x/nu/r/sigma的interval-upper-lower真实retained组合。
4. actualDoubleSeparated恰为同一参数的upper+lower-interval真实separated组合。
5. doubleCrossingEvent为两个分别存在rank r≤n的弱上／下crossing，保留r=0和等号。
6. actualDerivativeFamily的upper／lower分支分别是已接受实际halflineDerivative；interval分支是同Q的intervalDerivative。
7. 实际生成actualDerivativeFamily.match_1为依MonitoredDomain.casesOn的完整依赖分派，将三个Unit→motive分支按upper／lower／interval逐一取值。
8. private生成match_1.splitter的完整VALUE就是该match_1，TYPE的motive、J及三个分支参数全部覆盖。它不是漏掉的目标数学假设。

其余实际theorem：

- 三个private match_1.eq_1／2／3完整TYPE精确给三个分派分支，公理集为空。
- actualDoubleValue／Retained／Separated三个eq_1完整TYPE精确展开各自已冻结值。
- 13个_simp_完整TYPE覆盖集合差／交／补／空集／univ及反身≤，以及2、3、4、非零乘积、自然幂／整数幂和CharZero的非零化简。抽象类型类前提在各helper TYPE中全部保留；public TYPE没有新增这些数学前提。
- 三个foreign namespace实际所属theorem完整纳入：190.initialDoubleObservable.eq_1精确展开energy0=1否则同Q kernel(W)；SourceSeparatedOvershoot.retainedSum.eq_1和separatedSum.eq_1分别精确展开range n下的实际sourceRetainedRemainder／sourceSeparatedOvershoot。它们都由191模块实际拥有，所以没有因命名空间不同漏审。旧透明值绑定继续来自原完整阅读／190资格包；本轮仅核对这三个新生成TYPE的实际含义，不重新审查190已经完成的类型或旧证明。

## 190报告封存前的精确3字节说明

父已读190报告7454字节版本；最终封存的是7451字节。唯一修改在一条VALUE说明中：

旧：“在同一omega和同一B上的两个独立存在时间量词”
新：“在同一omega和同一B上分别量化两个存在时间”

目的是避免“独立”被读作概率独立。两个∃t、同一B、同一omega、弱不等式及后续整句均未变；没有修改源码、证明、假设、收据或资格结论。这一措辞修改发生在UNIT190-SEAL之前；原v2 sealed report之后未动。

从最终文件逆向应用这唯一替换可精确复原7454字节，SHA256为1cab1ae9088731b88313c65f0cbf1850a87a37eea1efb2606158d88f7dc9697c；最终7451字节SHA256为01128791ffa7096d40fc6f34d924d1ee3c19c7018ceef9ec631879346d24ee6f。190-report-three-byte-preseal-wording-delta.json保存旧／新完整行和可复验结果，父只需补读该句差异。

## 失败账与最终边界

本轮两个本地辅助请求有已保留技术失败：一次PowerShell foreach接管道的ParserError、一次Python dict关键字以数字开头的SyntaxError；二者都在执行前发生，未写候选或输入。修正后完整读取与逐项确定性验证实际PASS。它们不属于Lean证明结果，记录于inspection-failures.json。

本角色本轮没有Lean／AX命令、候选源修改、上传、发布、代理或资源变更。请求配置仍gpt-6.1-sol/xhigh；实际backend／model／effort及input、cachedInput、output、reasoningSubset各自不可观察，分别null。

189(f695...)、190(a967...)及191(a05f...)现在各有精确源独立审查和对应机器资格，本包不宣称原始C2/C12根定理完成，也不扩大有限stopped identity及initial budget的原始范围。保存本包封存后，释放审查目录writer／inflight至0；不存在等待中的检查或隐形持续进程。
