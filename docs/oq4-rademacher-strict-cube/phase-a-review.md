# 严格完美立方子列：第一阶段独立最终源码审查

STATUS: CORRECT

审查者：115，fresh 独立最终源码语义审查。第一阶段已完成并停止。此结论限于指定最终源码、冻结数学目标和冻结公共声明的完整数学及 Lean 源码语义；没有执行 Lean、服务器、Git、实际声明清单或递归公理检查，也没有用机械收据替代证明审查。原 OQ4 总根保持 OPEN，rawleaf 增量为 0。

## 1. 隔离、版本和完整读取账

先全文读取了 AGENTS.md、SERVER.md、coordination/TEAM.md，以及 math-theorem/SKILL.md 和 prompt-library、openai-workflow、lean-verification 三份参考。只读下表许可输入及父后续许可的两个公共可测性头；未读作者收据、编译结果、其他审查推理、旧 review、额外状态文件或上游实现证明。未运行 Lean、服务器或 Git，未转写或修改 Source。唯一写入目录是 drafts/oq4/strict-cube-complete-review-v2/。

下表字节范围均为完整文件的半开区间 [0, bytes)。逐行读取没有截断；随后对冻结公共声明及最终源码全文作了轻量文本比较。哈希均在本轮从实际文件重新计算。

| 输入 | bytes / 全文行范围 / 实际显示分块 | SHA256 |
|---|---|---|
| frozen-rademacher-strict-cube-v1.md | 7454 / 1–116 / 1–116 | aa5cfc0f508ffb7a3b2cf88cb5a7ae1955e10f364ca73278003305b8f73457fd |
| rademacher-strict-cube/proof.md | 25549 / 1–507 / 1–175, 176–350, 351–507 | cc1e280efaefcd4d8fc20473001508096bd20114c8ad2a652dc5c239c1edb328 |
| frozen-rademacher-strict-cube-formal-statements-v1.lean.txt | 9971 / 1–226 / 1–120, 121–226 | 432a8c9b26f4119d3635f04a6c9bd3013c29dffd5e6b627e11b17614d4bf4a65 |
| rademacher-strict-cube-implementation-v1/Source.lean.txt | 37685 / 1–835 / 1–170, 171–340, 341–510, 511–680, 681–835 | 5802fb4b5403ec27ed2df3ed1a53160e10885cc29056e65aa3e453591f9d4ef5 |
| strict-cube-upstream-public-interface-v1.json | 6769 / 1–140 / 1–140 | 6637957b3921f575a1cdbe63681fe18e9433c583c97d708bd7d6392c7a81ae22 |
| frozen-rademacher-s4-formal-statements-v1.lean.txt | 16426 / 1–378 / 1–170, 171–378 | 0c4af1e038d7290b08daf6da9578519be7ffc913611f91fca2b833129d5fe6f1 |
| frozen-rademacher-s5-formal-statements-v1.lean.txt | 24193 / 1–471 / 1–170, 171–355, 356–471 | 1b1ad31b8147cb142f7c5bca262903abe11428cc186e93b967a5adaeb01dd6a4 |
| strict-cube-additional-public-headers-v1.json | 1020 / 1–33 / 1–33 | f5c9000e5de236a94b1c0fb87342d699f98b647971b047f2a723e8f4c604b963 |

最后一份由父在本轮明确释放，只含 Shao.measurable_prefixSum、Shao.measurable_sqrt_energy 的参数上下文与完整类型，没有证明体。S4/S5 文件是 interface JSON 指向并允许全文读取的声明冻结，所有上游证明体均为占位，未读实现。

静态声明比较：删除注释、折叠空白后，13 个透明定义的完整定义体与冻结稿逐一相等，12 个公共定理的全部头部逐一相等，各出现一次；最终源码共有 23 个 private lemma。源码未发现 sorry、admit、axiom、unsafe 或 native_decide 词项。这是文本检查，不是内核证书。

## 2. 数学目标、类型和对象忠实性

13 个定义覆盖如下，每项均与冻结定义相同，未添加额外输入条件：

| 定义 | Source 行 | 核对结果 |
|---|---:|---|
| strictEvent | 33–34 | 对所有自然 r，只要求 1≤r≤N 时严格小于任意实 h；不误含 r=0。 |
| strictP | 36–37 | 实际 S5.pathLaw 的 real 事件概率，没有谱量替代。 |
| strictSelfNormalizedEvent | 39–41 | 同一前缀和，真实 S5.V，严格阈值 s*V。 |
| k | 44 | 自然数 j+2，包含 j=0。 |
| n | 46 | 先作自然数立方 k^3，再在实式中转换。 |
| x | 48 | k/sqrt(n)，未换自由尺度。 |
| a | 50 | π²/4。 |
| b | 53–56 | 任意实际概率空间及 IsBrownianReal 的同一 BrownianSup.probability。 |
| strictRatio | 58–61 | 同一 n、k、x 下实际严格分子除 b(x)。 |
| weakRatio | 63–66 | 同一 n、k、x 下已证 S5.p 除 b(x)。 |
| sourceRatio | 68–72 | 实际严格自归一化事件的概率除同一 b(x)。 |
| mainRate | 74 | 实数转换后的 n/k²。 |
| CommonTailAt | 77–99 | 只含共同尾段的正性及真实对数/比值恒等式，均是结论。 |

所有公开 Brownian 结果保持任意 Ω、可测空间、概率测度 P、B 与 hB 的量词。没有增加路径与 Brownian 的耦合、独立性、Brownian 正性、部分和整数性、能量身份、目标极限或更强指数余项作为假设。S4/S5 的公有类型与本模块所用的实际概率、尺度及第一项对象相符。

## 3. 十二个公共证明逐项审查

| 公共定理 | Source 行 | 完整证明的独立核对 |
|---|---:|---|
| actual_path_support | 165–193 | 消费允许的 S5.actual_path_energy 输出：实际 pathLaw 的概率性、同一共同满测集上的逐坐标 ±1、真实能量与 V。pathLaw 的 Pi 等式由透明定义给出。对同一 v，确定 z_i=if v_i=1 then 1 else -1，并用有限和换实数转换证明每个前缀和为整数；未增加支撑或能量假设。 |
| measurable_events | 195–232 | 对全部 N、任意实 h,s，把三个事件写成自然数指标的可数交；无效指标条件给全集，有效指标由可测前缀和、绝对值及真实 sqrt(energy) 的常数倍给出可测比较。补充两公共头恰好提供所需函数。 |
| zero_time | 234–253 | 1≤r 与 r≤0 矛盾，所以任意 h,s 的两个严格事件均为全集；实际 pathLaw 0 的概率性使两 real 概率为 1，没有偷加 h>0。 |
| integer_boundary_bridge | 257–306 | K≥2 保证 Nat 减法实数转换等于 K-1。实际弱 p 的事件等式由透明定义给出。共同满测集的整数部分和用于整数离散性：abs(z)<K 当且仅当 abs(z)≤K-1。r=0 单独以空和和非负 Nat 阈值处理；最终由事件 a.e. 相等和 measure_congr 取 toReal。所有 N 包括 0 均覆盖。 |
| cube_geometry | 309–350 | 严增性经精确 cubeSeq(j+1) 身份调用已证 S5 立方几何。逐 j 的 k≥2、n≥8、正平方根、平方身份、自然立方实转换、x>0、x sqrt(n)=k 均有证明。S5 的正时间尺度身份及 c=1 的透明 rpow 定义给 x=n^(-1/6)。n/k²=k 与 k→∞、x=1/sqrt(k)→0 完整衔接。 |
| weak_cube_shift | 353–379 | n 等于 S5.shift cubeSeq 1，并逐 j 等于 cubeSeq(j+1)。高度、尺度、实际 Brownian 分母、弱概率和 Q 逐项对齐；不是只匹配相位极限。 |
| strict_source_bridge | 383–420 | 在实际共同满测集上 V=sqrt(n)，乘以固定 x 得 k，因而严格自归一化事件与 strictEvent a.e. 相等。事件可测、real 概率相等及 sourceRatio=strictRatio 均对每个 j 成立。除法为全定义实除法，无须预先假设 b(x)>0。 |
| common_positive_tail | 738–771 | 从实际 Brownian 正性定理得到分母尾正；从已经独立证明的严格/弱倍率正极限得到倍率尾正，再反推出两个实际分子尾正。取这三项 eventually 的共同尾段；对数恒等式使用已导出的非零性，全部 11 个 CommonTailAt 分量覆盖。这里不与 F3 循环依赖。 |
| F3_STRICT | 773–779 | 包装完整 strict_limit_data：实际相邻弱 Q→exp(a)，实际 Brownian 移位比→exp(-a)，事件桥把乘积最终等同严格倍率，故极限为 1；在极限 1 处的 log 连续性给 log→0。 |
| F3_WEAK | 781–786 | 包装完整 weak_limit_data，只用 S5_CUBE 中 c=1、相位 1、固定移位 1 的 PhaseLimits，以及全指标 weak_cube_shift。得到 exp(a) 与 a，未调用变动 c_j 的 S5。 |
| F4_ADJACENT | 789–817 | 先取共同正尾。弱/严格倍率相除的分母极限为 1，且在同一尾段等于同一 n_j 的弱/严格概率商；对数差也在同一尾段等于两个倍率对数之差。分别取极限得到 exp(a)、a。 |
| F4_NORMALIZED | 819–831 | mainRate→∞ 故其倒数→0。严格与弱 log 已有有限极限 0、a，分别乘该倒数，按实除法定义得到两个归一化极限 0。 |

S5.actual_path_energy 是已许可、针对实际 Pi 律的已证结论，而非本模块的自由前提；本模块由其共同逐坐标支撑重新构造整数前缀和。由公开的 strict_source_bridge 可把 F3_STRICT 和相应尾段恒等式逐 j 转回原严格自归一化概率；没有另换事件。

## 4. 二十三个私有证明逐项审查

| 私有引理 | Source 行 | 检查结论 |
|---|---:|---|
| cube_index_eq | 108–111 | 展开自然立方及 cubeSeq，j+1+1=j+2，精确全指标相等。 |
| cube_mono | 113–116 | 严增 shift j+1 输入 S5_CUBE_GEOMETRY 的 StrictMono。 |
| cube_height_eq | 118–122 | S5 几何在 j+1 的高度等于 j+2，使用精确 cube_index_eq。 |
| cube_scale_eq | 124–134 | n_j>0 给 1≤n_j；S5.positive_time 在 c=1 输出 x=height/sqrt(N)，与真实 k、n 对齐。 |
| k_tendsto_atTop | 136–141 | j+2 自然严格递增及自然实数转换趋于正无穷。 |
| h_tendsto_atTop | 143–147 | j+1 的同一发散论证。 |
| x_inv_sqrt | 149–158 | sqrt(k³)=k sqrt(k)，k>0 保证平方根取正及所有消去；得 x=(sqrt k)^(-1)。 |
| x_tendsto_zero | 160–163 | sqrt(k)→∞，取倒数→0，并用全指标 x_inv_sqrt 替换。 |
| eventually_positive_of_limit | 423–430 | 正极限 L 的 L/2 邻域使 f>L/2>0，未假设 f 先正。 |
| y_geometry | 432–444 | h=j+1>0，n>0，y=h/sqrt(n)>0，y≤x，k=h+1，N=k³。 |
| y_tendsto_zero | 446–448 | 0≤y≤x 且 x→0 的夹逼。 |
| h_reciprocal_limit | 450–452 | h→∞ 的倒数极限。 |
| adjacent_scale_limits | 454–509 | k/h=1+1/h→1，N/h³=(k/h)³→1；因 1≤h、k=h+1 得 k/h≤2，故全指标 N/h³≤8；N/h²≥k→∞。 |
| adjacent_log_data | 511–555 | S4_ALL 的所有入参已逐项核实，见下节；S4 输出 log Q-w→0 与 w=a*N/h³→a 相加，得 log Q→a，并从 S4.ProbabilityLegal 输出 Q 尾正。 |
| adjacent_ratio_limit | 557–564 | 连续 exp 作用于 log Q 极限，再用 Q 尾正下 exp(log Q)=Q。 |
| brownian_normalized_limit | 566–582 | 对任意全指标正且趋零的 z，逐 epsilon 使用实际 Brownian 第一项定理，再将 z 放入 (0,δ)，得实际 T(z)→1。 |
| brownian_positive_tail | 584–596 | 对同类 z，实际 Brownian 正性定理和 z→0 给 b(z) 尾正，未升级到所有正 z 的正性。 |
| inverse_square_shift | 598–610 | 所有 j 上 h>0、k>0、sqrt(N)²=N；确证 1/y²-1/x²=2+3/h+1/h²。没有遗漏常数 2。 |
| inverse_square_shift_limit | 612–624 | h^(-1)→0，平方及线性组合得差值→2。 |
| firstTerm_ratio | 626–634 | 展开同一 g，系数 4/π 非零，exp 分母非零；g(u)/g(v)=exp[-(π²/8)(1/u²-1/v²)]。全定义实除法使该恒等式甚至可对任意 u,v 表述。 |
| brownian_shift_limit | 636–674 | T(y)/T(x)→1；前项比→exp(-a)。在 b(x)>0 的已证尾段，g(x),g(y)>0，代数消去精确得到实际 b(y)/b(x)。 |
| weak_limit_data | 676–698 | 仅取 S5_CUBE 的 cubeSeq 相位 1、移位 1；抽取 log Q 与 Q 两个正确的 PhaseLimits 分量，以全指标弱倍率身份转移。 |
| strict_limit_data | 700–736 | 对 b(x)、b(y) 的共同正尾，格点桥和 k-1=j+1 把实际 Q(n,h)*b(y)/b(x) 等同 strictRatio。两个极限相消为 1，再从 log 在 1 处连续得到 log 极限 0。 |

## 5. S4、S5、Brownian 承重调用核对

S4_ALL 具体取 m_j=j+1、n_j=(j+2)^3、h_j=(j+1:ℝ)。m_j≥1，下界是等号，h_j<m_j+1 在每个 j 成立，包括 j=0 的 h=1；h→∞、N/h²→∞ 和固定 M=8、K_M=0 的三阶尺度上界均由本源码证明。未把最终正性放进调用假设。S4Outputs 中实际抽取的是第八个极限 log Q-w→0，及输出正尾的 ProbabilityLegal；w 的公开定义桥确为 a*(N/h³)*(H-h)，而 H-h=1，故 w→a。源码没有把弱相位误置为零。

S5_CUBE 只用于真实弱倍率以及精确立方几何。PhaseOutputs 的 shift 参数固定为自然数 1，源序列和本序列逐项相等；原先 cubeSeq 的第一个值 1 被固定移位到本序列的首值 8，这正是冻结的 n_0，未删改本序列任何早期项。公开 PositiveTime 的第十一个分量提供 x=height/sqrt(N)，c=1 的透明定义进一步给精确 rpow，所有前提 0<c 和 1≤n 都在源码中证明。

实际 Brownian 调用只用 actual_brownian_firstTerm、actual_brownian_eventually_positive，且始终传入同一 B,P,hB。它们的输入范围是 0<z<δ；源码分别证明 x,y 全指标正、趋零，才取得共同尾段。第一项是 g(z)=(4/π)exp[-(π²/8)/z²]。精确差值

  1/y_j² - 1/x_j² = 2 + 3/(j+1) + 1/(j+1)² → 2

给 g(y)/g(x)→exp(-π²/4)=exp(-a)。因此相邻弱倍率 exp(a) 与分母移位 exp(-a) 在严格倍率中相消。没有把 b(y) 未经计算替换为 b(x)，也没有使用强于公开第一项等价的速率。最终严格 log 极限使用连续性，虽与匿名数学证明显式拆分两个 log 的组织方式不同，结论及必要非零条件都完整。

## 6. 边界、依赖和裁决

- N=0：任意实 h,s 的严格事件为全集，概率为 1；真实能量和 V 为 0 由许可的 S5 输出保持。格点桥的弱阈值为自然 K-1≥1，所以 r=0 的弱条件成立，桥不遗漏 N=0。
- 最小阈值 K=2：整数离散桥给 abs(prefix)<2 当且仅当 abs(prefix)≤1。子列 j=0 时 k=2、n=8、h=1，所有代数和 S4 弱格假设合法；尾正结论不被误写成所有 j 的输入。
- 严格/弱边界：严格事件 r=1,…,N 与弱事件 r=0,…,N 的差异只在零前缀条件，源码单独处理。没有主张任意实阈值的 ceil 分类。
- 真实概率：S5.pathLaw 明确为实际 Measure.pi；S5.p 的定义桥和源码透明约化将它固定为同一 closedStrip 概率；V 始终是 sqrt(energy)。事件 a.e. 恒等式在取 real 概率之前成立。
- 共同尾段：所有需要普通除法、普通概率 log 的恒等式都由输出的同一尾段保证。全定义 real 商和 Real.log 在早期项保留原值，极限只使用合法的最终相等。
- 依赖无循环：几何与事件桥先完成；相邻 S4、Brownian 移位和 S5 弱极限先给 F3 的私有数据；共同正尾再由极限产生；F4 使用共同正尾。没有拿 common_positive_tail 去证明其依赖的倍率极限。
- 原始范围：仅固定 Rademacher 律与固定完美立方子列；没有新证明一般 OQ4、任意 c 的 strict 相位、任意实阈值分类、统一有限 O(n/h³) 或精细立方根率。

未发现 CRITICAL GAPS。匿名数学证明 F1–F4 完整，最终源码逐项忠实表达冻结声明，全部 13 定义、12 公共证明、23 私有证明已实际完整审阅。

尚未覆盖且本阶段禁止执行：实际所有 owned 声明及递归公理审计、实际导入对象/唯一 olean/版本比对、Lean 内核检查及父整合门。这些不是本报告已经完成的项目。本审查不据此宣称 LEAN_FULLY_CHECKED，不代替第二阶段授权。

STOP：等待父审读及单独释放；不启动第二阶段。
