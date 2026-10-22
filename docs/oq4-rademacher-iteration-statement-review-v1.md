# OQ4 Rademacher 真实迭代叶：来源到冻结声明语义审阅 v1

STATUS: CORRECT
REVIEW_SCOPE: SOURCE_TO_FROZEN_STATEMENT_ONLY
PROOF_REVIEW: NOT_PERFORMED
LEAN_CHECK: NOT_RUN
SPECTRUM_STATUS: OPEN
ROOT_STATUS: OPEN

## 裁决

冻结版忠实保留固定 Rademacher 分布、弱边界、有限整数状态、整数起点及包含零步的全部有限时间量词；目标明确绑定现有真实 killedIterKernel 与其真实积分。它只冻结原有限谱链中“整数状态保持 → 已认证主一步对可以逐层使用 → 主余弦加权积分有限幂”的薄连接叶，没有把主模态身份冒称完整 S1 生存概率式，也没有以较弱结果替代原 S1 后宣布关闭。就本次来源到冻结声明的审阅范围，无需修订冻结假设或结论。

本结论不认证尚未提交的数学证明、Lean 实现或 PR72 的证明体。当前没有 RademacherIteration 作者稿/实现进入本次审阅；CORRECT 仅为这一冻结声明的来源忠实性、接口绑定与量词边界裁决。

## 输入锁与可见范围

所有散列均实际按字节重新计算，路径中的 library 是只读 v30 快照。

| 对象 | 字节数 | SHA256 |
|---|---:|---|
| C:/game/shao/current/oq4/c01/spectrum01.md | 4306 | b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b |
| C:/game/shao lean/drafts/oq4/frozen-rademacher-iteration-v1.md | 5464 | 15851002ccadaa118035107c8b9b8266dd825fdebdf36728f3ac7a97f7330b80 |
| C:/game/shao lean/library/Shao/OQ4/KilledIteration.lean | 9162 | 03b97e5708ffa552cfa4eccec5cf3c042da9805f9ab69561f4cb3e2701a690b5 |
| C:/game/shao lean/library/Shao/OQ4/KilledKernel.lean | 5403 | f90c1996f4c220473371b0f5ea3c74a7b8287e8f997f1a2cd3f0831cd6bd626f |
| /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/Shao/OQ4/RademacherCosine.lean | 8414 | c0ba478f9ed6b5aa75d7010d70835b37065a92e9878c65b086d3c3ff24e7f861 |

已读 AGENTS.md、SERVER.md、coordination/TEAM.md 及 math-theorem 必要规则。数学输入限于上述固定原文、冻结声明和必要现有定义/定理签名；PR72 文件通过服务器只读提取定义与签名，排除证明体。未读 intake、其他 review、author checkpoint、匿名证明或未认证实现；未运行 Lean、重计算、Git 或缓存操作。冻结声明第7行提到的 intake 不构成本报告证据。

## 逐条来源映射

下表“原文”行号对应 spectrum01.md，“冻结”行号对应所锁定冻结文件；接口行号对应上表实际文件。

| 来源与数学含义 | 冻结落点 | 真实接口绑定与审阅结果 |
|---|---|---|
| 原文5–7：固定对称 ±1 分布；不是任意增量分布 | 冻结13 | RademacherCosine 的 halfENNReal 15、law 18–19、law_isProbabilityMeasure 28 固定实际测度。没有把分布替换成外部核假设。 |
| 原文11–13：h≥1，m=floor(h)，实际整数状态为 −m,…,m，吸收点 ±(m+1) | 冻结13–15、38 | m:ℕ、1≤m、m≤h<m+1 恰好表达此分支。integer_closed_iff 40–42 将实际整数 cast 的弱区间条件与整数界相连；killedKernel_row 62–68 是真实两邻点截断行。 |
| 原文13、21：有限状态核为邻接矩阵的一半，并有一步特征向量身份 | 冻结19–25、32 | killedKernel 25–26 是真实平移核对闭区间的 restrict；killedIterKernel 19 是此核的幂。冻结要求真实迭代测度 a.e. 落在 G_m，而非另造矩阵后只证其自身闭性。 |
| 原文15–21：j=1 时 θ₁=π/(2H)，v₁(s)=sin(θ₁(s+H))=cos(θ₁s) | 冻结13、27–32 | angle 34、rho 37 与此主模态相同；killedKernel_integral_principal 150–154 在相同 m、h、整数 r 及两侧界下返回真实一步积分身份。 |
| 原文24、33：每个整数 n≥0，零步按空路径解释 | 冻结15、25、34 | killedIterKernel_zero 29 明确为起点 Dirac；killedAction_zero 118 为原函数值。冻结没有漏掉 n=0 或把其起点提前杀死。 |
| 原文27–30：S1 是起点0的无权生存概率及全部所需模态的有限和 | 冻结34、42 | 当前只给 r=0 时主余弦积分为 ρ^n。killedMass 26–27 才是单位函数的 killedAction，killedMass_eq_real 82–83 才连接总质量；冻结没有把余弦测试函数换成单位函数。 |
| 原文20–23、34、36–56：正交、范数、全部模态、cot 有限和、零/负谱及奇偶项 | 冻结42 | 全部继续 OPEN。只选 j=1 是明确的依赖拆分，不是原完整谱陈述的等价替代。 |
| 原文33：0≤h<1 的正步零生存分支；原文58–81、110–119：渐近比较与弱/严格端点差异 | 冻结38–42 | m=0 分支独立保留 OPEN；S2–S4 与端点分类继续 OPEN。当前弱闭边界没有改成严格边界。 |

## 真实接口与尚需实现的连接

1. **固定对象没有游移。** law 是 ENNReal 权重 1/2 的两个真实 Dirac 测度之和，并有内部概率实例。angle m=π/(2((m:ℝ)+1))，rho m=cos(angle m)。冻结没有加入额外核、归一化参数或生存质量为正的前提。

2. **G_m 是需要新叶提供的真实状态连接。** G_m 由有限整数闭区间经 Int.cast 的像组成，要求有限及 Borel 可测，语义精确。现有 killedIterKernel_ae_support_pos 56–57 及 killedIterKernel_ae_support 66–67 只给实区间支持，不能代替“w 是合法整数 cast”的新结论。冻结第23行明确拒绝这种替代。killedKernel_row 的保留原子正是 r±1 的整数 cast，因而声明与真实核行相接。

3. **有限性和核可测性由现有对象承担。** killedIterKernel 的类型已经是 Kernel ℝ ℝ；killedIterKernel_isFiniteKernel 46 与 mass_le_one 32–33 提供有限次概率核所需的有限性和子概率总质量界。G_m 的有限/可测声明仍是本叶目标，不能因为已有实区间支持而省略。

4. **真实可积性不是隐藏假设。** killedAction_integrable 72–73 对可测、全局有界的实函数给出每个真实迭代测度上的 Integrable；余弦连续、绝对值至多1，适用所有 n 和起点。killedAction 22–23 定义上就是该真实积分。冻结同时要求可积和积分等式，避免将不可积 Bochner 积分的默认值当作结论。

5. **一步到有限幂有现成真实组合接口，但仍须证明新目标。** killedAction_semigroup 135–137 将 m+n 步动作绑定真实核组合，killedAction_iterated_integrable 129–131 提供相应迭代可积性，killedAction_smul 156–159 提供标量线性接口。这些签名支持冻结所要求的语义连接；它们本身并未宣告主余弦有限幂已证明。任何作者稿仍须把 G_m 上的一步主对通过真实组合及 a.e. 身份传递，不可拿自定义数列的递推代替。

6. **一步前提与后续使用点吻合。** PR72 的 Kcos_principal 123–126 和 killedKernel_integral_principal 150–154 均保留 1≤m、m≤h<m+1、r:ℤ、−m≤r≤m。冻结第32行要求在真实迭代测度的 G_m 支持上逐点选回这样的整数起点；没有将一步定理扩大为整个实区间的身份。

## 必要边界核对

- **零步与起点。** 全部 n:ℕ 包括0，r 必须在 I_m 内。若删掉 r 的界而仍要求零步支持在 G_m，r=m+1 的起点 Dirac 就不满足结论。冻结明确保留这一条件；正步核对目标位置的截断不意味着零步已截断起点。

- **弱边界与吸收点。** h=m 时 ±m 属于闭区间，仍保留；从 r=m 向 m+1 的那一半原子退出，向 m−1 的那一半保留。故该行总质量为1/2，不得重新归一化为1。冻结第38行“有限次概率核”须按同句的子概率、总质量不必为1及既有 ≤1 接口理解；它没有增加 IsMarkovKernel 或总质量等于1的要求。

- **不能延伸到非整数点。** 以 m=1、h=1、z=1/2 为边界见证：真实一步只保留 z−1=−1/2，因此主余弦积分为 (1/2)cos(π/8)，而拟错误延伸的右侧为 cos(π/4)cos(π/8)，两者不同。冻结对整数起点和 G_m 支持的限制是承重条件；其他 coset 不能沿用同一吸收点和频率。

- **零测度与可积语言。** 子概率核可能存在质量损失；零测度情形的 a.e. 支持和积分仍按原定义成立，不需要正质量或条件化。冻结没有通过额外正性条件排除此类情形。

- **m=0 与未来零模态。** 当前 1≤m 维持 PR72 非退化主对范围。原文0≤h<1分支没有由本叶关闭；未来完整谱含零特征值时，n=0 仍须按完整有限式处理，不能因当前 rho>0 而删掉未来的零模态零次幂项。

- **加权积分不能变成生存概率。** 例如 m=h=1、r=0、n=1 时，真实核总质量为1，而主余弦加权积分为 cos(π/4)。所以本叶的 ρ^n 不能直接充当 S1 的 p(n,h)，也不能直接给出 4/π 系数。冻结第42行明确阻止这一越界。

## 原文与本叶的作用域差异

原文的主要有限目标是起点0的完整 S1 生存概率展开，之后还有 S2–S4 渐近、负主模态奇偶项和弱/严格端点差异。本冻结叶只提取其中主模态的真实有限幂，并显式新增“真实迭代核保持有限整数状态”这一形式接口义务。它不主张证明原文全部谱结论，也不把仅有主模态的结果称为完整有限谱。

冻结将辅助起点推广到全部 r∈I_m；这与原文有限矩阵逐行的状态空间相容，且正好覆盖 PR72 的认证一步签名，但原文概率记号 p(n,h) 的起点仍是0。该辅助推广不赋予任意实起点完整核谱，也没有把 r=0 的主模态权重恢复为无权概率。

明确继续 OPEN：其他实起点状态类、m=0独立零分支、有限正弦族全部模态、零/负模态、正交与完备、单位函数展开、cot有限和、完整S1、4/π系数、S2–S4及弱/严格端点分类，以及完整 Spectrum/OQ4 根。冻结中对已有一般 kernel/path-law 桥的说明只是依赖归属，本次没有重新认证该桥。

## 审阅结论与后续门

CORRECT：可以在完全不改冻结 law、事件、端点、起点类或量词的条件下，进入这一指定连接叶的独立数学证明工作。后续匿名数学审阅、Lean 实施及完整接口/公理认证仍须分别完成；本报告不替代任何后续门，也不释放 canonical 写窗口。

DONE
