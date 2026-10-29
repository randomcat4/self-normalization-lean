# Unit277：有限异常块优化的声明提案

状态：**PROPOSAL_ONLY / NOT_FROZEN / NOT_IMPLEMENTED / NOT_QUALIFIED / NOT_KERNEL_CHECKED**。本件是来源绑定的数学设计与完整推导方案，不是 Lean 证明体，也不是独立资格审查。唯一可写目录为本 proposal-01；父协调器拥有声明冻结、元数据和服务器执行权。本轮不依赖 unit276 的未合格正文。

## 结论与最小建议

建议新模块 Shao/OQ6/FiniteExceptionalBlockOptimization.lean 只包含五个定理声明：三个私有承重助手 H01/H02/H04，两个公开实质结果 H03/H05；不增加定义。全部精确 HEAD 与完整前置语境在 PROPOSED-HEADS.json，顺序在 PROPOSED-DECLARATION-ORDER.json。父级必须另行冻结这些字节，之后才可实现证明。

H03 给出任意有限实向量、任意非空背景 B、任意实偏移 c 的优化界，并从真实背景能量 Qb>0 推出全体中心化能量 Q>0。H05 把它直接用于原始 centered-row 统计量 T=(W+D)/s，保留 s=0 时 T=0 的约定。源式 (3) 的系数 n-1、n、k/m 全部保留。

本轮不把式 (4)–(5) 放入拟冻结声明：它们需要另一组块内/交互和及背景重标号接口，而不是式 (3) 的证明依赖。下文完整记录它们的下一接口。

## 授权、读取与已有供应检查

授权 proposal-ACTIVATION.json 的 SHA256 为 5bfebd2326bacbd32645ad62bccd29572fcad647a8292a78b09a6e01a3a7ef67，4491B。所有六个绑定输入的 SHA256 与字节数均已复核一致。完整读取 p41 第1–449行、p51 第1–355行、两份下一依赖说明；读取 BoundedStudentizerGeometry 与 FiniteRows 的相关全部定义/公开 HEAD，及下列直接 bearing definitions。READ_ACK.json 记录实际运行响应。

使用 math-theorem 及其 prompt-library/openai-workflow/lean-verification 参考规则；本轮严格服从任务的“先提案、另行冻结、禁止实现/Lean”边界。未执行技能的工具链探测，因为项目和本任务明文禁止作者本轮探测或运行 Lean。已读适用根/库 AGENTS、SERVER、TEAM 所选所有权字段、当前 REGISTRY compact 状态。当前 OQ56 所有者是 01a1822b-1815-7f21-a1af-2e0b15ee67a5；不接管父级、共享区或任何其他作者。

占位检索范围是只读 library/Shao 的定向文件名与关键字，随后仅看相关候选 HEAD：
- P51/BoundedStudentizerGeometry：residualU、centeredSq、residualU_eq_erased_row、sampled_uStatistic_formula、sampled_centered_row_formula、centeredSq_eq_center_sum，以及邻近 geometry HEAD。
- OQ6/FiniteRows：原 unordered-pair uStatistic、rowMean、jackknifeSq、其非负性与行恒等式。
- P35/RowIdentity：mean、center、unorderedPairSum 及 offDiagonalSum_eq_two_unordered。
- P35/ConditionalStudentizer、ConditionalNumerator：公开结果是特定 p35 条件模型的可积性/矩/方差/费用，不是任意 b 的异常块优化；内部 center_energy_le 也是全能量上界，并且 private。
- P45/BalancedBlock：公开行公式要求秩一特征和 BalancedTarget/平衡条件；不是任意对称残差/任意背景的式 (3)。
- OQ6/OriginalExceptionalTailAbsorption：公开结论吸收已明确的指数失败项；没有任意有限块几何结论。
- OQ6/OriginalPhysicalClippedTailTransfer：确认现有 physical 使用原 s=0=>0 与 (projectionW+residualStatisticD)/s 的相同表达式。

有界检索未发现已公开的精确 H03/H05 供应者；这是所查 curated snapshot 中的定向结果，不是关于所有文件、Mathlib 或外部文献的不存在证明。已有 mean/center、原行恒等式应复用，不能重写为新“原创”结果。本提案不作数学新颖性、优先权或外部文献全覆盖主张。

## 数学对象和全部前提

H03 中 n 为自然数且 n≥2，b:Fin n→ℝ，B 是 Fin n 的有限子集且非空，c 是任意实数。令
- A=univ\B；m=card B、k=card A 是自然数，M、K、N 分别是 m、k、n 的实数转换；
- M>0、K≥0、N=M+K>0，k=n-m 由有限集合基数恒等式推出，目标中使用 card A 以避免自然数截断减法；
- μB=(∑B b)/M，q=Qb=∑B(b-μB)^2，唯一能量前提是 q>0；
- μA=(∑A b)/K，K=0 时按实数除法的总定义为0；
- QA=∑A(b-μA)^2≥0，y=μA-μB；
- Q=∑all(center b)^2，center 正是已有 P35.center，均值是原全体算术均值；
- a=μB-c，X=∑all b-Nc=Na+Ky；
- T=0 若 Q=0，否则 T=√((N-1)/N) X/√Q。

H03 不假设全局均值为零、b 非负、c 非负、异常块非空或 a≥0；也不假设所需的几何界、尾概率或费用。Q>0 是结论，不能被作为隐藏前提。n≥2 用来使 N-1>0，明确避免负比例因子。

H05 中 Ω:Type u 为任意类型，不需要可测结构。g:Ω→ℝ、r:Ω→Ω→ℝ、x:Fin n→Ω，r 对所有 a,b 对称；n≥4、card B≥3，另有实际 b 的 Qb>0。无概率、分布、均值、矩、包络、独立性、截断、α、p 或相对尾假设。点态对称性是已接受有限行 API 的参数，并与来源中对称核的设定一致。

H05 明示使用 p51 S1 与已接受 P51 供应者的 n≥4 范围。p41 的文字 m≥3 本身也允许 n=3；本次实际统计量 wrapper 不宣称覆盖 n=3。抽象 H03 已覆盖 n=3 的向量几何。若父级要单独接纳实际 n=3 端点，需要冻结相应 ≥3 原行桥接，不能从本 HEAD 静默推出。PE-R 是充分大 n 的目标，因此该明确范围不损失其未来渐近消费。

## 完整闭合推导方案

以下是数学推导和之后的实现计划，没有形式证明体。

H01 的精确恒等式为
    Q = q + QA + (M K/N)y².
按 B、A 分割全部和；每块内部离均值之和为0。全体均值满足
    bar b=(M μB+K μA)/N.
分别展开每块相对于 bar b 的平方和，线性交叉项消失，剩余块均值项化成 MK/N·(μA-μB)²。这给出 H01。K=0 时 A为空、所有 A 和及 QA 为0，B=univ，公式直接为 Q=q；不在 K=0 分支约去 K。M>0 来自 hB，N>0 来自 hn。之后使用 q>0、QA≥0 和 MK/N≥0，获得
    Q ≥ D0 := q+(KM/N)y² ≥ q >0.

H02 完全是标量配方。令 a+=max(a,0)，Z=Na++Ky，X=Na+Ky。N>0 给 X≤Z。对 Z≥0，可由 max(X,0)≤Z 平方；对 Z<0，X<0，max(X,0)=0。因此无论 Z 符号，
    max(X,0)² ≤ Z².
令 C=N(a+)²/q+K/M。准确配方恒等式是
    N C [q+(KM/N)y²] - (Na++Ky)²
      = (N K/(M q)) [q-M a+ y]² ≥0.
这里只约去正的 N、M、q，未约去 K，也不要求 y≥0 或 N=M+K。由此得到精确 H02。a=0、a<0 和 K=0 自动涵盖；不用把正部替换成绝对值或假设分子为正。

H03 应先建立实际基数关系与 X=Na+Ky，调用 H01/H02。由于 C≥0，
    max(X,0)² ≤ N C D0 ≤ N C Q.
既已由 q>0 推出 Q>0，就可合法消去零分支、使用 √Q>0 和 (√Q)²=Q。N≥2 给 √((N-1)/N)>0，正部与正的乘除因子相容：
    max(T,0)² = ((N-1)/N) max(X,0)²/Q
               ≤ (N-1)[N(a+)²/q+K/M].
这完成包含真实 Q 正性在内的 H03。所有 sqrt 正性/平方消去在实数非负依据齐全以后执行。

H04 的原统计量桥接只使用已有公开有限行事实。设
    ψ_i=∑_{j≠i}r(x_i,x_j),
    F=∑_{i<j}r(x_i,x_j),
    b_i=g(x_i)+ψ_i/(N-2),
    c=F/[(N-1)(N-2)].
residualU_eq_erased_row 和对称核的双计数给 ∑ψ=2F，因而
    ∑b = ∑g+2F/(N-2),
    ∑b-Nc = ∑g+F/(N-1),
    W+D = (∑b-Nc)/√N.
centeredSq_eq_center_sum 给 s²=Q/(N-1)，其中 s=√centeredSq≥0。Q≥0、N-1>0 保证 s=0 当且仅当 Q=0。非零分支 s=√Q/√(N-1)，直接得到
    (W+D)/s = √((N-1)/N)(∑b-Nc)/√Q.
零分支两侧均按定义为0。因此 H04 是包括零分母语义在内的全样本恒等式，不只是在一个好事件成立。

H05 对实际 b,c 调用 H03，使用 H04 把 T 还原到现有物理统计量，且由 Q>0 和 s²=Q/(N-1) 推出 s>0。这一步没有使用 unit276 或任何条件背景概率结论。

H01/H02 是本单元为闭合代数所需的两类新工具；H04 是避免重用一个未证明物理统计量同义定义的承重桥。它们建议保持 private。已有公开供应的 proof/AX 资格本轮不重复审查。实现时可在这些冻结定理体内部建立展开与正性事实；不授权未列出的顶层声明。

## 退化边界与优化含义

- k=0：B=univ、Q=q，T 的正部平方恰为 N(N-1)(a+)²/q，源右端 k/m=0。不能定义“非空异常均值”后忘记该分支。H01 的空集总定义和 H02 的 K=0 配方都对此有效。
- a=0：只剩 (n-1)k/m 的上界。k>0 时该界通常是异常共同值趋无穷时的上确界，q>0 的有限 y 一般不取等。没有假定 a≠0。
- a<0：把 a 换成正部0只增加原分子；不声称负分子平方也受同一个界。关键是 max(T,0)，不能删掉正部。
- a>0、k>0：当异常块全部 b_i=μB+q/(M a)，即 QA=0 且 y=q/(M a) 时，两处不等式可同时取等，得到来源所给的优化配置。此为抽象向量松弛的尖锐性说明，不是实际总体中任意 g/r 配置可实现的结论。
- Qb=0：本单元明确排除，与 p41(3) 一致。全样本 T 的零约定仍由 H04 保留；不能由此省掉未来低能量/零分母事件的概率支付。
- 相同观测、非零 r 的对角值：求和均排除同一索引的对角；没有把观测取值相同与索引相同混淆，也不要求 r(o,o)=0。
- 任何卡数减1/减2因子均写为实数转换之后的减法，不使用 Nat 的截断减法。目标中 k 直接是补集基数。

## 原始来源到候选 HEAD 的忠实性表（MFT）

| 原始来源 | 保留对象/主张 | 提案接口/边界 |
|---|---|---|
| p41:65–70 | B=Aᶜ、m≥3、μB、Qb、a0=μB-F/[(n-1)(n-2)] | H05 的实际 b、card B≥3、hQb 与 let c；H03 的抽象 c 可任意 |
| p41:73–80，式(3) | (T_n^+)²≤(n-1){n(a0^+)²/Qb+k/m} | H03/H05 精确保留正部、系数、真实 Qb 与补集 card；Q/s 正性为结论 |
| p41:80 | 全能量下界与异常块均值优化 | H01 精确方差分解和 H02 标量配方，不把全能量下界当前提 |
| p41:82 | 冻结残差时对异常 g 的虚拟松弛；不要求实际 g/r 可独立变化 | H03 对任意确定向量成立；H05 仅代入同一实际 b、F，不添加独立性 |
| p51:18–29 | 原 n≥4，ψ/(n-2)，W、D、s，R_h=2s，T=(W+D)/s，s=0=>0 | H04/H05 使用原 P51 定义，不替换 Studentizer；n≥4 是明示范围 |
| p41:84–120，式(4)–(5) | 背景核、分子和范数扰动 | 不在本 HEADpack，见下一精确接口；不假装本单元已闭合背景比较或稀有块积分 |
| p41:25–40 | PE-R 指数 α_p=2(p-2)/(2p-1) 与原渐近尾范围 | 本单元纯有限代数，不声明任意 α>0 的无条件 PE-R，也不以当前条件276替代它 |

具体地，令 H_ij=g_i+g_j+r_ij，q_i 为原去对角行均值、U 为原 unordered-pair uStatistic。已有 sampled_centered_row_formula 给
    q_i-U=(N-2)/(N-1)·(P_n b)_i.
所以
    R_h²=[4(N-1)/(N-2)²]∑(q_i-U)²=4Q/(N-1),
    R_h=2s=2‖P_n b‖/√(N-1).
这与来源要求的原 centered-row jackknife 完全相同。H05 没有把分母换成未中心化行平方，也没有丢掉 2 或 n-2。

## 单独记录的下一有限接口：式 (4)–(5)

这些是供父级选择下个源绑定单元的数学接口，不是本轮额外冻结 HEAD，也不授权实现。

共同数据：n≥4、B⊂Fin n、m=card B≥3、A=univ\B、k=card A；N,M,K 为对应实数；g_i 任意实数，r_ij=r_ji；F_A、F_B 为各块 i<j 的残差和，C_AB=∑a∈A∑i∈B r_ai，F=F_A+F_B+C_AB，b 与 a0 仍按原 n 构造。

(4) 精确分子接口：
    b_i^0 = g_i + [∑j∈B,j≠i r_ij]/(N-2), i∈B,
    λ=(M-2)/(N-2)∈[0,1],
    h_B(i,j)=g_i+g_j+λr_ij,
    N_B = [∑B g + (M-2)F_B/((N-2)(M-1))]/√M.
应证明（没有概率假设）
    √N a0 = √(N/M) N_B + Δ,
    Δ=√N{ K F_B/[(N-2)(N-1)(M-1)]
         +(K-1)C_AB/[M(N-1)(N-2)]
         -F_A/[(N-1)(N-2)] }.
这里 K-1 必须是实数减法，k=0 时等于-1，不能误写成 Nat k-1 的转换。推导的中间实际恒等式是
    ∑B ψ_i=2F_B+C_AB,
    μB=[∑B g+(2F_B+C_AB)/(N-2)]/M.
背景 adjusted row 的残差系数仍为 λ/(M-2)=1/(N-2)，不能换成原统计量 n-1 系数或遗漏 λ。若要调用现有以 Fin m 为域的背景统计量，需要另行冻结 B 的保序重标号/和及能量传输接口；本单元不引入该重标号。

(5) 确定性包络接口：
另外给 w_i≥0 且对 i≠j 有 |r_ij|≤w_iw_j。令 ℓ=∑A w_i，Qw=∑B w_i²，
    μ0=(∑B b_i^0)/M,
    Q0=∑B(b_i^0-μ0)²,
    sB=√(Q0/(M-1)).
应证明
    |F_A|≤ℓ²/2,
    |√Qb-√(M-1)sB|≤ℓ√Qw/(N-2).
后一式的直接承重界是
    b_i-b_i^0=(∑a∈A r_ia)/(N-2),
    |∑a∈A r_ia|≤ℓw_i,
加上背景中心化投影的范数收缩与反三角不等式。即使 ℓ=0、Qw=0、k=0 或 Qb/Q0=0，平方根范数形式仍有定义，不能额外假设它们为正。

来源 PE 是 μ⊗μ 几乎处处的包络；未来把该确定性接口用于样本时，要显式给出有限个去对角样本对同时满足包络的几乎处处提升。不能把源 a.e. 包络静默改成全体观测点的全称事实。

接下来仍缺 p41 §5 中条件于全部异常观测的交互和控制，以及 §6 的带指数权稀有块积分和真实窗口吸收。式(3)单独不提供这些概率界。不得将目标相对支付/CDF 结论作为新的公开假设来制造“消费完成”。

## 实现与复核计划、状态

父级如接受该提案，先冻结 PROPOSED-HEADS.json 中所有五个精确声明及前置语境，再由授权作者实现。同一新源版本完成后，另用独立新上下文做完整 source-to-statement/proof 审查；由父级依当前资源/锁与服务器原始工具链跑完整源 native 和同一 first original object 的 all-actual-owner TYPE/VALUE/递归 AX。只容许 propext、Classical.choice、Quot.sound。这里描述的是未来验收路径，本轮没有派发它们。

预期 Lean 路线只用有限和展开、实数域代数、非负平方、卡数分割、sqrt 正性与已有原行定理；没有确需服务器 Mathlib 查文之处，因此本轮 SSH 次数为0。具体 tactic/API 名称尚未内核验证，不把一个候选 proof plan 写成检查成功。已有原模块不重编译、不重审旧 proof、不重跑旧 AX。

本轮产出仅为这些提案文件：HEADpack、声明顺序、本文、READ_ACK、STATIC-CHECKS、MANIFEST 与唯一 LASTFINALWRITE。STATIC 只核对字节/结构/作用域，不是数学资格或 Lean 检查。实际 backend/model/effort 与各类 token usage 未暴露，记录为 null；配置要求仍是 gpt-6.1-sol/xhigh。

本轮没有 Lean/AX、上传、服务器写入、Git/API 发布、资源变更、子上下文、Goal、自动化或侧栏新会话。完成后释放本提案角色的全部受派写入/执行/子任务/等待权限；父级可据具体 HEADpack 做下一次冻结。原始 μ 全尾、NR/PE/DC/OQ56/root 均不因此关闭。

