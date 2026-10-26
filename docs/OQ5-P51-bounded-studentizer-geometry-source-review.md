# unit196 完整独立源码审查：原居中 Studentizer 的有限几何

STATUS: CRITICAL_GAPS

本结论针对精确源 `843626299442d229a46db6c462474a046b02b90ed9a522be1848917b66cca002`（32746 字节、735 LF）。**全部冻结陈述及其数学推导经完整独立阅读为正确；这份 Lean 实现尚有三个实际编译错误，不能接纳为已完成的形式证明。** 缺口限定在 D16 与 D22 的证明实现。未发现数学反例、偷偷增加的前提或未冻结的承重数据。最终资格为 `qualified=false`、`actualOwned=UNKNOWN`。

## 审查身份、读取与证据边界

审查实例 `/root/oq56_studentizer196_final_review` 与作者 `/root/oq56_studentizer196_stage1` 分离。父实例为 OQ56 lead `01a16c48-9017-7d50-8123-83c72763be0f`，不是共享 Root。仅本 `final-review-01/` 为审查者写入范围。已先实际写入 RUNTIME-ACK；请求模型/强度为 gpt-6.1-sol/xhigh，实际自省均 UNKNOWN，input/cached-input/output/reasoning-subset 均 null。

已读取工作区 AGENTS.md、SERVER.md 和 TEAM 的所有权相关内容，使用 math-theorem 与中文输出技能。本实例不执行 Lean、公理审计、服务器、网络、Git/API、上传或缓存操作，不创建子实例。当前 phase25 的执行权限由父实例持有；本实例 heavy=0。未更改任何作者、冻结、原始来源、library 或共享协调文件。

实际完整阅读：

- 新源全部 L1—735，按 L1—250、251—500、501—735 连续读取；11 个完整证明 D12—D22 均独立核对，而非仅凭计数或作者摘要。
- F196 的全部 22 声明头、11 RHS、原作用域契约、overlay、D13 delta，及完整推导、problem、assumptions、provenance、selected-original-source、producer-bindings、primary-declarations 的所需数学与接口内容。
- 原始只读 p51 全文，特别是 L18—39 的 S1、L129—147 的 G_y、L197—211 的 S16—S17；选定 p44 片段和完整 p54，核对适用范围与修正归属。
- 188 originalRows 与 190 originalUpper 的全部实际 TYPE、全部 FULLVALUE（分别 12/6 行）、结构化名、层级参数、body-present 与旧传递公理字段；九个旧有限接口的完整源码头/RHS及词法环境。
- 七个固定 Mathlib 主要声明的完整原源码块与导入/作用域/实例环境；完整固定 Init/Classical.lean，特别完整 propDecidable、em、choose、choose_spec、indefiniteDescription 支撑链。未把 choice-support 的 Prop 证明当作普通 Prop 豁免。
- 首次实际 native 的诊断包 `author-kernel-01-affected-diagnostics.json`，SHA `1dca23b30d3af55030384593c72e6e05eb02e9fe6c27b55d17d899486d4b750e`，35789 字节；完整 stdout/stderr 和三个错误的实际目标均已读取。

独立本地确定性核对是 690/690 PASS，66 个唯一的精确本地文件绑定、285 个实际源字节段、11 个完整证明体。它们由本审查脚本重新派生；没有复制父 intake 的 928 个计数。该核对只证明字节、契约与记录对应，不冒充内核或公理结论。普通 Prop 的 144 个表头记录由 136 普通记录加 8 泛型记录组成；字节段保留缩进/尾空格，`fullWrittenSourceHeader` 保留已知 trim 惯例，没有为此改写源码。

## 实际对象与原文的逐点绑定

记 N=(n:ℝ)、g_i=g(x_i)、r_ij=r(x_i,x_j)、S=Σg_i、Q=Σg_i²。实际 originalUpper 是 Σ_iΣ_j 1_{i<j}r_ij；实际 originalRows 的 i 坐标是 Σ_j(if i=j then 0 else r_ij)，通过 `WithLp.toLp 2` 放进 EuclideanSpace ℝ (Fin n)。二者均排除**索引**对角；若 i≠j 但 x_i=x_j，r(x_i,x_j) 原值仍参与。这与原文 F、ψ_i 完全一致。

D01—D11 依次给 H_ij=g_i+g_j+r_ij、E=Q/N、V=√E、W=S/√N、D=F/[√N(N−1)]、u_i=ψ_i/(N−2)、J=Σu_i²、s²=jackknifeSq(H)/4、V=0 时取0的 d、原 G_y 与 C(K)=200(1+K+√K)。全部 RHS 与冻结文本相同。没有改成自由标量、未中心化行平方或另一核。g/r 是传入的实际函数，有限代数对任意这样的函数成立；概率投影、典范性、可测性、iid/矩资格没有被冒称为本单元结论。

九个旧接口的实际源码语义完整匹配调用：P35.mean=N⁻¹Σ、center=z_i−mean z、unorderedPairSum 为严格上三角和、pairCount=N(N−1)/2、pairCount_eq_choose，以及仅需逐点矩阵对称的 offDiagonalSum_eq_two_unordered；FiniteRows 的 uStatistic 为 choose 的逆乘严格上三角和，rowMean 为 (N−1)⁻¹ 的擦除行和，jackknifeSq 为 4(N−1)/(N−2)² 乘 Σ(rowMean−uStatistic)²。四份旧模块源哈希匹配 Root v105 接受映射。旧九接口反射打印仍为 UNKNOWN，按父的明确实质决定复用已资格源码；没有伪造打印或重复审查旧证明/旧 LeafAX。新消费端的完整实际 TYPE/FULLVALUE/AX 仍须后续取得。

## 全部11个证明的数学审查

| 声明与源行 | 独立核对的完整论证及结论 | 当前形式实现状态 |
|---|---|---|
| D12 projectionV_sq，L108—115 | Σg_i²≥0、N≥0，故 Q/N≥0；对实际 √(Q/N) 用平方根平方。n=0 时总除法给0，等式仍真。 | 数学正确；本次无该处错误，仍无模块对象资格。 |
| D13 residualU_eq_erased_row，L119—136 | 展开实际188初始化，以 Fin 索引 i 的 `ite` 零项作 sum_erase；剩余 j≠i 的项准确为 r_ij，再除同一 N−2。没有用 r 对称性或观测互异性。 | 数学正确；本次无该处错误。 |
| D14 residualEnergyJ_eq_rows_norm_sq_div，L140—147 | 逐项 (ψ_i/(N−2))²=ψ_i²/(N−2)²，再把共同分母移出和，以欧氏实际坐标范数平方等式替换 Σψ_i²。分母0时两边均0。 | 数学正确；本次无该处错误。 |
| D15 sampled_uStatistic_formula，L151—204 | 实际擦除行和=(N−2)g_i+S+ψ_i；r 对称给 Σψ_i=2F，H 对称给二倍严格上三角和。合计总行和=2(N−1)S+2F，故上三角=(N−1)S+F。原 choose 归一化得 U=2S/N+2F/[N(N−1)]。n≥4 提供所有非零分母。 | 数学正确；本次无该处错误。 |
| D16 sampled_centered_row_formula，L208—248 | Σu_i=2F/(N−2)。将实际 rowMean 公式减去 D15 的实际 U，得到 (N−2)/(N−1)·P(g+u)_i；全部索引、均值及同一样本保留。 | 数学正确；L247 的实际 rewrite 失败，见下文缺口1。 |
| D17 centeredSq_eq_center_sum，L252—266 | 将 D16 代入原 4(N−1)/(N−2)²·Σ(rowMean−U)²，最后除4；系数准确化为 1/(N−1)。未假设 s>0。 | 数学正确；该处无独立错误，不据此声称其对失败上游已有合格对象。 |
| D18 centeredDelta_eq_zero_of_projectionV_eq_zero，L270—275 | 显式 D09 `ite` 在 hV 下选择原来的0分支。没有由此推导零V上的源比值恒等式。 | 数学正确；本次无该处错误。 |
| D19 centered_denominator_identity，L279—337 | 完整展开任意有限 z 的 Σ(Pz)²=Σz²−(Σz)²/N；P(g+u)=Pg+Pu，平方和产生2ΣPg·Pu。D12给Q=NV²，√N平方给 W²=S²/N。D17减V²后，(N−1)(s²−V²)=V²−W²+2ΣPg·Pu+Σ(Pu)²，除正的 (N−1)V² 得 S1。 | 数学正确；本次无该处错误。 |
| D20 centered_geometry，L341—432 | 方差展开给 A=Σ(Pg)²≤NV²、B=Σ(Pu)²≤J。对任意 a,b，完整双和 Σ_ij(a_ib_j−a_jb_i)²=2(Σa_i²)(Σb_i²)−2(Σa_ib_i)²≥0；故 C²≤AB≤NV²J。V、√N、√J 均非负，比较非负平方得到 |C|≤√N·V·√J。没有未付款的外部 Cauchy 接口。 | 数学正确；本次无该处错误。 |
| D21 projectionGood_bounds，L436—480 | 实际 G_y 给 V²≥1/2、V≥0，推出 V>0、V≥1/2，故 4+V≤9V。b=√y·√(√N)≥0、b²=y√N，平方 |W|≤9bV 并除 V²>0 得 W²/V²≤81y√N。未把 V≥1/2 错用成 V²≥1/2。 | 数学正确；本次无该处错误。 |
| D22 bounded_studentizer_geometry，L484—731 | 逐项从同一个 hF、hRows、G_y 推出 J、D/V、显式 d 界和 C(K) 界；完整算术及边界见下一段。 | 数学正确；L658 与 L730 有实际实现缺口，见缺口2/3。 |

D22 的每个常数独立核对如下。N≥4 给 N²≤4(N−2)²、N/(N−1)≤2、(N−1)≥N/2；V≥1/2 给 1/V≤2，而 G_y 直接给 V²≥1/2。于是

\[
J=\|\psi\|^2/(N-2)^2\le4Kq,
\qquad |D|/V\le(Kq)/\sqrt N\,[N/(N-1)](1/V)\le4Kq/\sqrt N.
\]

由 J≥0、K≥0、q≥0，比较非负平方得 √J/√N≤2√K√(q/N)，这一步不要求 Kq>0。S1 的绝对值分子上界为 V²+W²+2√N·V·√J+J。除同一个正分母后，四项分别满足

\[
\frac1{N-1}\le\frac{2y}{\sqrt N},\quad
\frac{W^2}{(N-1)V^2}\le\frac{162y}{\sqrt N},\quad
\frac{2\sqrt N V\sqrt J}{(N-1)V^2}\le16\sqrt K\sqrt{q/N},\quad
\frac J{(N-1)V^2}\le16Kq/N.
\]

第二项准确使用81乘2；交叉项准确使用2·[N/(N−1)]·(1/V)·(√J/√N)，合计2·2·2·2=16。最后一项用 N≤4(N−1)V²；该不等式来自 (N−1)≥N/2 与 V²≥1/2，故无倒数方向错误。相加给164/16/16。C(K)=200(1+K+√K) 分别大于164、16√K、16K，三个被乘量 y/√N、√(q/N)、q/N 非负，故逐项相加即为最后上界。四个输出的右结合顺序为 J、D/V、显式 d、C(K) d，未变更。

## 已实际证实的三个实现缺口

1. **D16 L247，rewrite 未完成。** 实际目标仍含 `(fun j => g (x j) + residualU n r x j) i`。目标尚未进行这里所需的 β 规约，`rw [..., residualU_eq_erased_row]` 未找到 residualU 模式。数学上它等于 g_i+u_i；形式实现需要先把这层函数应用规约，再进行原来的改写。现有源码在此失败，不能称 D16 已有完整 Lean 证明。
2. **D22 L658，所引用 `abs_add` 不存在。** 相同证明块还在 L662、L667 使用同名调用。这里需要真实的绝对值三角不等式接口；目标数学关系本身正确。不能把未知标识符当成已有主要定理的成功调用。
3. **D22 L730，最后 nlinarith 失败。** 实际 ht1/ht3 的左边为 `164*(y/√N)`、`16*K*(q/N)`，而当前目标保留 `(164*y)/√N`、`(16*K*q)/N`。普通数学中这些逐项相等；当前 tactic 未把所需除法表示统一为同一个原子，未完成目标。须显式完成这些环/除法恒等变换并相加，不能从正确系数比较直接推断这份代码已完成。

以上来自已结束的首次实际 native：RC1、9.417453039437532 秒、3 errors、22 warnings、object=null、ownLean=[]。受保护11966项的 before/after 及 preservation 字段为 true。诊断中的 mathlib local-changes 警告原样保留；本审查不据警告改动缓存，也不把失败运行视为公理资格。原始服务器 receipt 的绑定 SHA 为 `435082aa3c484dfcace917384d16f1d0429e5307f1291728303a02a3dbdd1853`；本地保留的是父给出的精确受影响诊断包，没有复制全日志/缓存。

没有发现第四个数学或冻结风险；这不等于预言修复后一定编译。作者需按父事前窄冻结修复，后续仍需真实新源内核结果。

## 契约、作用域和边界攻击

22 头/11 RHS 保持；12 项按顺序的环境帧、universe u、autoImplicit=false、BigOperators、两个精确 open 和 namespace/section 闭合保持。11 个全局值完整类型与初值均读过。D10 的 x 在 Set 谓词内绑定，不是自由的顶部参数；overlay 已先行纠正。NNReal.sqrt 接收 Real.toNNReal 的 NNReal 值，再强制转换到实数，未误把 NNReal 域当作 ℝ。

16 个匿名数据形状均已核对完整初值、类型和捕获：样本矩阵；投影平方/和项；u 与 u²项；同样本好集合谓词；erase r 行项；g 向量；g+u 向量；其居中平方；Pg²；Pu²；Pg·Pu；Lagrange 双和平方；旧 offDiagonal API 的实际 r 样本矩阵参数；D13 的实际原行坐标 `@ite` 求和参数。最后一个在 delta01 先于源码生成冻结，使用原188的 `instDecidableEqFin n i j`。没有将 i/j 与观测值相等混淆。泛型 hvariance/hcs/hpoint 及各 hrow/hlinear 是完整读取的普通 Prop 辅助事实，其普通证明泛化不创建新承重数据或选择器。

64 个承重数值位置、两套显式 `ite` 的条件/判定器/实数分支均核对。D09 仅使用固定 core `Classical.propDecidable`，其选择支撑链完整可见，依赖既有白名单基础公理；没有新公理或新选择器。D13 的 Fin 判定不是新增经典选择。源码无 sorry/admit/axiom/unsafe/native_decide；这只是直接源码扫描，新增全部所属声明的递归公理审计尚无成功对象可做。

退化与边界逐项检查：

- n=0/1/2 的定义按实数总除法存在；D12—D14 不会暗用 n≥4。n=0 时 Fin n 无元素、Q=0；n=1 的残差行为空；n=2 的 u 分母0使 u、J及D14右侧均0。有限几何 D15—D17/D19—D22 的适用域明确 n≥4。
- V=0 只由 D18 返回总化0；D19 明确要求 V>0，D22 由同一个 G_y 推出 V>0。不存在零V上的全局S1声明。
- s=0 未在任何主定理中被排除或循环假设为不可能。此时 d 在 V>0 下可为−1，几何证明仍按实际 s² 运算；要在以后的小窗口排除它仍须源付款，196没有提前声称。
- K=0 或 q=0 时 hRows 迫使 J=0，hF给F=0；平方比较全过程只用非负性，无除 K、q、J 的步骤。n≥4时 √N>0，√K/√(q/N) 可以为0。
- 重复观测、非零核函数 r(a,a)、负的 g/r、所有阈值等号保留。hsym 是原文允许的对称性，没有额外反对称/迹零或互异样本假设。
- y≥1 是显式前提，四次根使用 √(√N)，其平方准确为√N。没有隐藏 q 整数、q≥2、y窗口或渐近 n₀。

## 适用范围与后续接纳

本结果在数学上完整支付原 S1 与有界乘积情形 S16两项实际样本界到 S17 的有限几何。它不导入195，不证明195的概率集中、Qw界或197的窗口/并集付款；没有把 S15 的概率和替成并集概率，也没有声称已得到 p54 的严格1/8余量。p54 的统一 p 矩修正、Shao–Zhou Lemma6.1 的结构条件和外部归属均保持。有限辅助恒等式没有新颖性主张，不构成原研究根闭合。C1 immutablev85 complete；C2/C12/OQ56 OPEN；OQ3 PAUSED_BY_USER；124不是前置。

本 SOURCE 回合在此完成并 allzero 释放。其可复用覆盖为：精确8436版本全部735行、22头11RHS及11完整proof的数学/源忠实性审查；精确缺口如上。父事前窄修复后，同一独立实例只需要完整续审实际改变的 D16/D22 两个证明、精确diff/冻结绑定及新机器包；其余9完整证明可按精确未变哈希复用，不能因编译接续或上下文阶段变化自动重审。

最终升级为 qualified 必须有修复后确切源的成功服务器内核，以及同一**首次成功原始对象**所生成的无过滤所属名索引、全部实际 TYPE、全部非定理 FULLVALUE、完整结构化名/层级/body 与递归传递公理证据，白名单仅 propext/Classical.choice/Quot.sound；并由本独立审查者实际读完、比较。当前三个失败诊断没有原始O或AX，本报告没有伪造这些内容。
