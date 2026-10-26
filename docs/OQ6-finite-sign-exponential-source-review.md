# Unit 198 — complete independent SOURCE review

STATUS: CORRECT
QUALIFIED: false
PHASE: SOURCE complete; successful native object / actual owned declarations / recursive AX pending.

本结论只覆盖下面精确版本的源码、数学证明与源到陈述忠实性。审查员是新鲜独立的 final-review 角色，不是作者或实现者；没有修订源码或冻结前提，没有运行 Lean/AX、服务器、SSH、网络、Git/API、上传或子代理。请求模型/努力为 gpt-6.1-sol / xhigh；实际运行模型和努力无法自省，均为 UNKNOWN；输入、缓存输入、输出、推理子集 token 计数均为 null。

精确源码：`drafts/oq56/unit198/author-01/stage2/FiniteSignExponential.lean`，SHA256 `501c39f8edddc811560f6cec2f72b44ebb4849d572203127e0bcae024f0ba029`，9990 bytes，236 LF，0 CR，UTF-8 严格解码，BOM0。逐行完整阅读 L1–236，包括所有三个完整证明，而非仅 diff 或哈希。声明冻结：`parent-freeze-v1.json` SHA256 `1220e9b124d0809f67aee51f9410bf84ec7e6e3d01f9df16aea5dfe37a71de76`，101290 bytes，发生于实现之前。固定 Lean `leanprover/lean4:v4.36.0-rc1`，mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。

## 冻结、原始范围与实际陈述

L1–12 的三个 import、autoImplicit false、namespace、noncomputable section、BigOperators 和唯一项目 open 均按冻结顺序；L234、236 完整闭合。不存在新 universe、环境变量、全局/局部 instance、attribute、classical 命令、choice/selector。导入的实数运算与有限类型使用既有实例；没有预先假定新的目标公理。禁止的 sorry/admit/axiom/unsafe/native_decide 均未出现。实际生成常量和实际 transitive axioms 尚不能从此源码观察断言。

五个完整头和两个定义 RHS 与父冻结逐字相同：D01 L15–17 为所有 Fin n 坐标的 `sum signValue(s i)*a i`；D02 L20–22 为未归一化平方能量 `sum (a i)^2`；T01 L25–30 为完整布尔立方的指数平均精确因子化；T02 L57–61 对任意实数 lambda 给出精确 `lambda^2*Q/2` 指数；T03 L81–86 仅要求 t>=0，事件为严格 `t*sqrt(Q)<abs(Z)`，上界精确 `2*exp(-t^2/2)`。n 没有正性前提，a 没有有界或归一化前提，T01/T02 没有 lambda 非负前提。全局定义无未绑定的环境数据。

原始 p51 全文及相关 S1、S10–S11 已读（只读 SHA256 `96920f428b8fc09788a6388103cefe398e3ec739129a5922b984babd09e99359`）。S11 的实际 W/V/Gy 上投影支付需要 `4*exp(-y*sqrt(n)/2)`，198 是严格上游的确定性有限符号工具，并不单独证明该 iid 概率支付。Stage1 的完整 derivation、problem、assumptions、hazards 和 source-provenance 已读：独立鬼样本、固定逐坐标交换、产品律传输、积分及实际 W/V 归一化是后续199的剩余工作；不存在用此 prose 作为198新前提的做法。196 的 projection 定义、197 的余项支付均不是198的形式依赖；source import 直接项目依赖只有合格185。

p54 全文已读，条件标准化 p 矩仅保留统一有界/收敛，不能重用 p51 S6 的任意多项式速率句；严格1/8实际余量、实际坏事件、原子边界及 DC 结构/外部 SZ Lemma6.1 的限制均保持。Shao–Zhou2016 equation92 对 Jing–Shao–Wang2003 Lemma6.4 的既有归因保留；没有直接读取 JSW lemma，保留 UNKNOWN，不能认证其额外细节。198 的有限证明不将这个未直接取得的论文文本作为 Lean 假设，也不主张新颖性。原 C1 immutablev85 complete；C2/C12/OQ56 OPEN；OQ3 PAUSED_BY_USER；124统一机制不是前提。

## T01 完整证明：L31–54

令 h(i,b)=exp(lambda*signValue(b)*a_i)，类型 Fin n→Bool→Real，捕获仅 n,a,lambda。L33–43 的完整全称等式对固定 s 展开 scalarSignSum，将 lambda 分配入有限和，再用 exp_sum 得到指数乘积；每项只使用乘法结合/交换的 ring 恒等式。L44–47 按既有 signValue true=1 / false=-1 精确求两点 Bool 和，顺序为 exp(lambda*a_i)+exp(-(lambda*a_i))。L48–54 展开 cubeMean 为 `(2^n)^(-1)*sum_s`，使用 Fintype.prod_sum 的逆向等式把完整函数空间的 sum-prod 改成 prod-sum，再把产品分母合为2^n。最终 div_eq_mul_inv 与 mul_comm 精确恢复两侧乘法顺序，没有取消可能为零的量。

n=0 时同一有限恒等式给唯一空符号向量、空和0、空积1和平均权重1，所以没有遗漏该分支，也无需额外正性假设。该因子分解是完整有限枚举的代数事实；没有把概率独立性额外当作输入。

## T02 完整证明：L62–78

先用 T01，将每个 `(exp x+exp(-x))/2` 按原始 Real.cosh_eq 改为 cosh x。L67–72 以 Finset.prod_le_prod₀ 比较有限乘积，其两个全部条件均在代码中给出：源因子由 cosh_eq 和 exp 正性得到非负；逐因子上界直接为锁定 Real.cosh_le_exp_half_sq(lambda*a_i)。不需要 lambda 或 a_i 的符号条件。L73–75 以 exp_sum 的对称式把指数积合为 exp(sum ((lambda*a_i)^2)/2)，L76–78 以 mul_pow、有限乘法分配与 sum_div 化为 exp(lambda^2*scalarEnergy/2)。分母2为 Real，平方指数2为 Nat，无常数损失或用 Hilbert 常数替换尖锐1/2。

这一推导同样覆盖 lambda=0、lambda<0 及 n=0。T03 的第二次母函数调用确实可使用 -lambda，未假定符号对称性定理。

## T03 完整证明：L87–232

I 是严格事件的 Real 0/1 指示函数；Q 是同一 scalarEnergy。L91–93 的平方和非负保证 Q>=0。L94 按 Q=0 分支，而非删去零能量样本。

Q=0 分支 L95–126：aSq(i)=a_i^2 是既定非负有限族。L96–111 从零总和及 single_le_sum 得到每个平方<=0，再与平方非负结合得到平方=0，使用 sq_eq_zero_iff 得 a_i=0。L112–115 因而每个 signed sum=0。L116–121 显式证明 t*sqrt(Q)>=0，并用严格 `<` 使 I(s)=0；L122–126 平均为0，目标右侧非负。n=0 必处于此分支，亦被覆盖。若事件改为非严格，Q=0、所有a=0、较大t时左侧将为1而右侧趋0；当前代码保留严格边界，没有该反例。

Q≠0 分支 L127–232：由 Q>=0 得 Q>0 后才令 r=sqrt(Q)，并于 L130–132 证明 r>0。随后 u=t*r、lambda=t/r、minusLambda=-lambda、weight=exp(-lambda*u)，及 Eplus/Eminus/dominator 的全部类型和初始化与冻结相同。除法只出现在此正能量分支；`r≠0` 在 L210、214 由 hrPositive 明确提供。

L144–156 给 lambda>=0、weight及两指数非负。L157–185 的点态比较对同一固定 s 完整分支：事件真时由 `u<abs(Z)` 分成 u<Z 或 u<-Z。正支的指数参数为 lambda*(Z-u)>=0，负支为 lambda*(-Z-u)>=0；代码中 nlinarith 仅展开这些非负乘积。对应的 `weight*Eplus` 或 `weight*Eminus` 至少为1，加上另一非负项得到指标<=dominator。事件假时指标0，由两个乘积非负闭合。hPos/hNeg 是析取的 Prop 消去，不是选择一个数据向量或事件可测选择器。

L186–197 对正权的完整 cubeMean 求有限和：sum_le_sum 给单调性，sum_add_distrib 和 mul_sum 给固定权线性；没有积分、条件概率或期望交换的未证明前提。L198–204 将 T02 分别用于 lambda 与 minusLambda；后者由负号平方精确归于同一指数。L205–218 的三项代数是 r^2=Q、lambda*u=t^2、lambda^2*Q=t^2，得到 -lambda*u+lambda^2*Q/2=-t^2/2。L219–232 将两次母函数上界乘同一个非负 weight、相加，再使用 two_mul 和 exp_add 合成精确目标。

t=0 时 lambda=0 合法，点态 dominator 为2，最后右侧为2；代码从未使用 t>0。r>0 用途只在消分母，Q=0 分支没有除法。正、负 signed sum、等于阈值、空维数、零系数和所有退化情况均在现有量词下闭合。

## 所有数据、匿名表达式、完整 Prop 类型和作用域

12个具名非Prop初始化逐一读过并按源偏移验证：T01.h L31–32；T03.I L87–89；Q L90；aSq L95（仅零能量分支至L126）；r L129；u L133；lambda L134；minusLambda L135；weight L136；Eplus L137–138；Eminus L139–140；dominator L141–143。r、u、lambda、minusLambda、weight、Eplus、Eminus、dominator 八项只在 Q≠0 分支；r 后先证明正性才出现 u/lambda。不存在跨分支泄漏或预见未来数据。具名 data 全部类型、初始化与直接捕获符合父冻结。

其余8项为 T01.E、factor、summand，T02.E、arg、coshFactor、exponent、expFactor：分别作为声明中的匿名函数、有限积体、mul_sum/exp_sum 的匿名有限族或锁定 primary 的实参数使用，均只捕获冻结 n,a,lambda。没有额外命名/未命名的选择结果、随机参数、数据函数、集合、实例或新时间作用域。两个全局函数的所有 lambda、sum/product binder 类型与完全初始化也均已检查。

32个完整具类型 Prop helper 全部已按源码读入。其完整类型在 COVERAGE.json 中逐项保留，实际词法范围在同文件明列。T01 hPoint/hBool；T03 hQnonneg、hSqSum、hSqNonneg、haZero、hSquareLe、hSquareZero、hSignedZero、hIZero、hThreshold、hMeanZero、hQpos、hrPositive、hLambdaNonneg、hWeightNonneg、hEplusNonneg、hEminusNonneg、hPoint、hAbs、两支各自 hArg/hOne、hAverage、hDominatorAverage、hPlus、hMinus、hRSq、hLambdaU、hLambdaSquare、hExponent 均是类型明确的等式/不等式/全称 Prop，没有以 Prop 包装数据选择。局部 intro 的 i/s 和有限成员 hi/hj/hs、析取及 by_cases 的全部上下文均按其实际分支检查；不把完整声明末尾一律当作每个局部 proof 的作用域。

78个源数值 token 的每一个字节/字符/行列位置均独立核对：76个数学显式标型数字，其中24为 Nat、52为 Real；另外两个 `congr 1` 是 Nat tactic 配置。冻结主声明10项恰为3 Nat/7 Real。平方均为 Nat2，指数分母、权重基数和双侧系数为 Real2；所有指示函数0/1及正性零为 Real。注释编号和常量名后缀不计作数学数值。没有由隐式整数除法或误定型引起的陈述变化。

未发现作者 actual-scopes、numeric-source-map 或 typed-prop-helpers 的数学误标；无需新增数学/data delta，也无需为本次 SOURCE 判定添加 metadata overlay。全局块 sourceSpan 合法含尾部两LF而 canonical fullSourceDeclaration 已 rstrip；Prop helper span 从行首缩进开始而 canonical completeTypedPropHeader 去了外侧缩进。这是原始span与canonical字段的边界约定，只有先核 raw字节/字符/行后才可按约定规范外侧空白；不能改旧源码或旧证据来消除此差异。

## 已有185和固定 primary 的完整相关接口

已逐项完整读取并对原 actual-owned-metadata 逐字段比对185的5条选择接口：cubeMean._proof_1、signValue.eq_1、cubeMean、cubeMean.eq_1、signValue。合计26行完整 TYPE 和两个非定理18行完整 FULLVALUE；bodyExpressionPresent 均真、所有 name components 为实际记录、levelParams 空，递归 AX 在既有白名单内。signValue 的值准确为 Bool true=Real1、false=-Real1；cubeMean 的值准确为 Real `(2^n)^(-1)` 乘 Fin n→Bool 全函数空间有限和，Pi Fintype 明确枚举每一坐标。_proof_1 仅为 Real2所需 Nat.AtLeastTwo 的生成证明，没有额外数学数据。原185源 SHA256 `f5e4f873f4e6a2b10dfad014a2e3ac0341fb277bf970a206091342c95121350a`，qualified-evidence和actual metadata哈希均再次核对。只复用这些已合格接口；没有重审未变185 Hilbert证明或请求旧kernel/AX重跑。

完整阅读 Series.lean 的163行及 cosh定义原文件1002行（最后split空行不计额外源行），并核其选定原始声明、源文件hash和完整前缀。其余固定sqrt/exp的10项原始完整声明及各自全部时序结构命令均读过并核前缀hash。Series 的 SinCos 两个 `set_option ... in` 只作用各自声明，没有泄漏到 SinhCosh/Real。cosh_eq 是后一个 Real namespace 下的实数公式，Complex变量上下文已闭合。sqrt也是后一个Real namespace，NNReal上下文已闭合；exp接口的Real与Complex上下文严格区分。

Fintype.prod_sum 的完整原始dependent-family头及实际前缀已读，特化为 Fin n / Bool / Real，前置已闭合的section变量不变成目标额外前提。END Fintype L311、Nat L313、vars L314是头之后的上下文，不是prod_sum活动前缀。Fintype.sum_bool来自完整prod_bool头的 `@[to_additive]`，即 AddCommMonoid 下 sum f=f true+f false；其后L48/50/52也不算头的前缀。另完整读过相关固定 Finset.prod_le_prod₀ 头、原始proof和 CommMonoidWithZero/Preorder/ZeroLEOneClass/PosMulMono活动scope，当前实数实例满足全部条件。这里的 primary 证据是原始锁定源码和完整类型头，实际primary TYPE探测仍为 UNKNOWN_NOT_PROBED，不虚构运行结果。

## 静态证据、失败历史与未完机器层

独立 STATIC-VERIFICATION-V2.json 为714项PASS：保留第一静态比较中已通过的659项，仅修复32项helper canonical外侧缩进的比较规则并增补全局块/当前源/finite primary核对。它覆盖127个实际source span（5global+12data+32Prop+78numeric）、55输入绑定、Stage2 manifest19绑定、Stage1有效seal29绑定。第一次静态文件保留32项FAIL；它们是审查脚本把行首span与无外侧缩进canonical头直接相比的错误，raw字节/字符/行/prefix当时均已PASS；V2把两份完整字符串附入，未改源码或作者metadata。另一次本地 Python 命令仅返回未安装的App alias提示，脚本未开始，无源或结果写入；完整事实保存在 LOCAL-TOOL-FAILURE-01.json。均非 Lean/数学失败，不作为成功gate。

Stage1 PowerShell H/h别名导致的空manifest、伪PASS与提前RELEASE0全部明确无效，保留历史，只承认seal-repair-01/manifest（SHA256 `9f29ab3217da02ac74456a082b5c8054190b094b6dbc0b8e5fcaced8305e25d0`）及其真实零释放。Stage2 static-failure-01 的漏匹配 `· let aSq`（11而非12）已读，失败及部分maps保留；其后mapper补全，源501c没有改变。作者最终manifest19、DONE及RELEASE0均已独立核验。父后续source-span只读提取失败及成功intake也按其边界记录保留；父的PASS不是本独立数学裁决的替代品。

父在本次SOURCE封存前实际完成首次服务器native，有限诊断 `author-kernel-01-affected-diagnostics.json` SHA256 `0b13cd3ace0dc80c67ddefd8828efa4d5092530ca69ef3a7a2b32dd6e9f5413b`，3367 bytes。已完整读取这个有界诊断和其中307B完整stdout：RC1、2.913246963秒，唯一错误位于L1，是共享固定cache中 `Mathlib/Analysis/SpecialFunctions/Trigonometric/Series.olean` 不存在；没有进入198证明正文，object=null、actualOwned UNKNOWN、无AX，12242个保护项before/after exact。服务器原receipt的记录hash为 `fa91470bd3261a22bd075c71a4f914a8e92c43acdf9b96f8b515471daccb59d7`（11476215B）；本角色没有读取整份大型raw receipt，也不以该摘要冒充成功机器认证。父诊断提取第一次误用 BoundedRemainderPayments 路径的 FileNotFoundError 也已读，未解释为新的Lean失败或source变更。

因此 SOURCE 没有关键数学缺口，五个完整冻结声明及这份完整证明在源码数学层面 CORRECT。最终 qualified 必须保持 false。后续由同一独立审查角色读取父提供的FIRST successful originalO全模块idx实际所属常量，逐一完整TYPE、每非定理FULLVALUE、private/generated/外来归属、body/namecomponents/levels和递归AX、native/audit收据，再判断qualified；不得前缀过滤、以public5代替实际全集、模拟AX或把这次缺依赖RC1当作证明通过。若后续改proof，仅使受影响证据失效，必须精确绑定新版本；本报告仅适用于501c当前源。

补充行政失败记录：首次封包格式检查把保留的 Python-not-found 诊断（LOCAL-TOOL-FAILURE-01.json 的 Windows CRLF）也纳入全体无CR断言而中止，尚未写 DONE/RELEASE0/manifest。LOCAL-SEAL-FAILURE-01.json 记录该事实；原诊断字节保留，最终manifest逐文件明列CR数。Lean源仍为原9990B/236LF/CR0，审查正文及新JSON为UTF8/LF。此失败不改变源码结论或机器未完成状态。
