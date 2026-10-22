# OQ4 原 S5：实际临界倍率与弱格点相位冻结声明 v1

STATUS: FROZEN_DECLARATIONS_PENDING_SOURCE_REVIEW
TASK_MODE: DECLARATION_FREEZE
UNIT_KIND: DERIVED_PROBABILITY_PHASE_ASSEMBLY
NEW_RAW_LEAF_INCREMENT: 0
SOURCE_RAW_DENOMINATOR_DELTA: 0
PROOF_STATUS: NONE
LEAN_STATUS: NONE
IMPLEMENTATION_AUTHORIZATION: NONE
ACTUAL_BROWNIAN_INTERFACE_OWNER: ROOT
ACTUAL_BROWNIAN_INTERFACE_STATUS: PENDING
ACTUAL_S4_S5_SPECTRUM_OQ4_ROOT_STATUS: OPEN
FREEZE_OWNER: OQ4_LEAD
FREEZE_SCOPE: FULL_SECTIONS_3_TO_8
CANDIDATE_SHA256: e95deeca42c49f88c4e3a2ee9f4c2f1f436fe0ce34dc4bd89a5f6f13335e431a
FIXED_S4_SHA256: 144e3c290ca60c174ceec0cc85b41519a82faf0eb55c09a1c54e61e1d097e00a
SOURCE_REVIEW_STATUS: PENDING
MATHEMATICAL_REVIEW_STATUS: NONE

lead 全文读入原候选后采纳全部对象、量词、域、输出、实际事件桥和同相位极限点范围；原候选保持不可变。本冻结只更新元数据、文档自称并锁定同一实际 S4 文件及哈希，不增删数学前提或输出。精细立方根余项未纳入；原 OQ4 根仍 OPEN。

本文件冻结完整待证声明，不给证明。只处理固定 Rademacher 弱事件实际概率，不得改成一个具有相位极限的自由数列、代用尾函数或 strict 事件。所有精确桥、最终合法性、极限和子列属性均在结论侧，不作为补充前提。

## 1. 原始目标、剩余关键义务与消费者

原始目标是 spectrum01.md 第85–104行：在临界 x_N=c*N^(-1/6) 下，实际弱事件倍率的相位由 δ_c(N) 决定，c=1 的立方子列和立方减一子列给两个不同端点；一般固定 c>0 的完整极限点集是 [1,exp(π²/(4c³))]，全列没有单一极限。

既有 CP0–CP3 只给真实高度/取整后的确定性相位与严格自然数子列。剩余承重义务是正时间的 x=h/√N 与实际事件桥、最终胞元经 S4 尾桥的消费、同一相位上的实际概率误差消失，以及沿 CP 的同一 σ 转移得到完整倍率区间。

本模块消除的是“确定性 CP 相位→实际概率 S5”这条缺边；直接消费者就是第6–8节的实际端点/内部相位/完整倍率极限点和全列不收敛。本冻结声明不再新建根、舍入、尺度或相位辅助模块，不把纯 CP 输出重复登记成新原始叶。

## 2. 来源与固定依赖

原 C:/game/shao/current/oq4/c01/spectrum01.md，SHA256 b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b，4306B，commit 35d4580b61e22e7145f47730045a09874ef93259：第5–7行固定 Rademacher/V_N=√N；第11–12行固定弱胞元；第85–90行给 c=1 实际倍率；第93–100行给三个相位族、无整列极限与恰好区间；第101–104行给全部固定 c>0 及舍入子列。

固定上游：

- C:/game/shao lean/drafts/oq4/frozen-rademacher-critical-phase-v1.md，SHA256 4e8be7821b842a1fe7a6a143f9705fa476b05615e122fdd621d4cb1c5c88c1ce，8147B。只消费其同一 CP0–CP3 定义与输出，不读证明或私有草稿。
- 固定 C:/game/shao lean/drafts/oq4/frozen-rademacher-s4-probability-assembly-v1.md，SHA256 144e3c290ca60c174ceec0cc85b41519a82faf0eb55c09a1c54e61e1d097e00a / 11831B，第3–7节同一实际 p/K/b_U、S4-MAIN、S4-ERR 及 S4-EVENTUAL。它是本 S5 唯一锁定的实际 S4 上游，来源、数学和形式认证仍须分别完成。不得将本文件写成“假设任意概率比满足 S4”的替代定理。
- 固定 actualS3：frozen-rademacher-s3-brownian-assembly-v1.md，19f162418e88f7b3ddea57e1c735404f94fd3e50fbd471bfd937eaf93424a71c/14243B；固定 DA1：frozen-rademacher-lattice-shift-v1.md，9cf9dba01aa9582ceb8e4d30af06c4778b8b367b61e61562dfc42c7ffb0e2b56/6067B；固定 DA2：frozen-rademacher-scale-assembly-v1.md，9e7f840f25038e4ef55ba561eaca112802a6b373849722898f6d6a550ca9e946/5248B。它们只经同一实际 S4 传递，不重做、不重计。
- 固定 actualS2：frozen-rademacher-s2-assembly-v1.md，c59971859b432bf312d5c1d65ca82d0a02254c06d4d56833322364f87f69146e/8318B，只经 actualS3/S4 传递其真实对象和概率输出。

原 frozen01.md，ea50b9fe0d742cbc9481fb126476ae2a788c7b0ec42d4e60636d757baf7cbc5a/1491B，第3、9行只提供同一实际 U 和首项等价的原输入。root 的实际 B/U/P_B/事件概率/首项 tail 正式接口仍 pending。不能借原 spectrum 第61行更强 Brownian O 率，也不另设任意 F 或自由尾渐近。

## 3. 全部量词、固定实际对象与零时间

量化每个固定 c:ℝ，唯一参数条件为 0<c。c 不依赖 N、子列索引、相位或 ε；不要求对全部 c 有统一收敛门槛。

对每个 N:ℕ，R_N:=(N:ℝ)。逐字沿用 CP 定义

r(N):=Real.rpow R_N ((1:ℝ)/3)，
h_c(N):=c*r(N)，
m_c(N):=Nat.floor(h_c(N))，
H_c(N):=(m_c(N):ℝ)+1，
δ_c(N):=H_c(N)−h_c(N)，
q_c:=π²/(4*c³)，
E_c(N):=q_c*δ_c(N)，
F_c(N):=Real.exp(E_c(N))。

r、h、m、H、δ、E、F 都不是自由函数；q_c>0，F_c(N)>0 的合法性在结论侧。CP 中的 F_c 是上述显式指数因子，绝不是 Brownian 尾函数。

再固定

x_c(N):=c*Real.rpow R_N (−((1:ℝ)/6))。

−1/6 和 1/3 均为实数除法；不使用整数除法，不把 rpow 立方根换自由根序列，不将负指数写成自然幂。

固定 ν_R=RademacherCosine.law=(1/2:ℝ≥0∞)•Measure.dirac(1:ℝ)+(1/2:ℝ≥0∞)•Measure.dirac(−1:ℝ) 及其实际概率实例，

p(N,h):=(Measure.pi(fun _:Fin N=>ν_R)).real(@Shao.closedStrip N h)，
K(N,h):=@Shao.OQ4.killedMass ν_R law_isProbabilityMeasure h N 0，
U:=sup_{0≤t≤1}|B_t|，b_U(x):=P_B(U≤x)。

定义实际倍率总项

Q_c(N):=p(N,h_c(N))/b_U(x_c(N))，
QK_c(N):=K(N,h_c(N))/b_U(x_c(N))。

若形式层用实数全域除法或 Real.log(Q_c(N)) 写总序列，必须同时交付下节最终严格正性；不能把早期分母为0或 log 总函数值解释成合法概率对数。本冻结声明不需要也不假设 b_U(0) 的值。

N=0 保留为原时间序列的一项：CP 固定 r(0)=h_c(0)=0；原 source 第33行空路径 p(0,0)=1 的约定不改变。x_c(0) 的形式 rpow 值不承担源文正时间 x=N^(-1/6) 的含义；本冻结声明不在 N=0 处声明 x=h/√N、正尺度恒等式或概率对数。对可能存在的早期 0<h_c(N)<1 项，实际弱事件仍是同一个 p，原低阈值分支不被 S1/主胞元谱表达替换；这些项不被删成新的概率模型。

## 4. S5-DOM：正时间精确桥与最终 S4 可用性

对每个固定 c>0，以下均为待证输出。

对全部 N≥1：

R_N>0，sqrt(R_N)>0，r(N)>0，h_c(N)>0，x_c(N)>0，

h_c(N)³=c³*R_N，
R_N/h_c(N)³=1/c³，
x_c(N)=h_c(N)/Real.sqrt(R_N)，
x_c(N)*Real.sqrt(R_N)=h_c(N)。

后一精确桥须实际核对 sqrt 与 Real.rpow 指数规则及所有正底数条件，不能只凭指数形式相加。

源文 P(M_N≤x_c(N)V_N) 的实际事件识别也在输出侧：在同一产品空间上，V_N(a):=sqrt(∑i:Fin N,(a i)²) 满足 V_N=sqrt(R_N) 几乎处处，且实际弱前缀事件 ∀k≤N, |prefixSum a k|≤x_c(N)*V_N(a) 的概率恰为 p(N,h_c(N))。这里 V 只是源文能量在固定 Rademacher 产品路径上的显示表达；若形式层复用已有能量定义，须核对透明等式。不能在最终定理中自由假设 V_N=√N，不能把源文自归一化事件改为其他 law 或其他阈值。该桥只服务原85–90行实际事件，不新开一般能量模块。

须消费 CP0，给出一个固定 N_cell(c)≥1，使全部 N≥N_cell 有

h_c(N)≥1，1≤m_c(N)，(m_c(N):ℝ)≤h_c(N)<H_c(N)，
H_c(N)=h_c(N)+δ_c(N)，0<δ_c(N)≤1；
h_c(N) 为整数时 δ_c(N)=1。

同时 h_c(N)→+∞、R_N/h_c(N)²→+∞，第三尺度在每个 N≥1 精确为 1/c³。不得把这些“最终”条件改成全 N 前提，不要求所有 N 都有 m_c(N)≥1。

消费 S4-EVENTUAL 时必须实际使用同一移位尾序列：对固定 J≥N_cell，取

tilde n_j:=j+J，
tilde m_j:=m_c(j+J)，
tilde h_j:=h_c(j+J)。

对全部 j 它们满足 fixed actualS3/DA2 的原全 j 胞元条件和 S4 原三项尺度；随后将 p、K、x、b_U、δ 和全部极限通过同一索引移位返回原 N 序列。若对某个 CP 子列应用 S4，也只能使用相同 σ 的共同截尾。不得无说明把上游 all-k 接口读成 eventual-k 接口。

最终还须存在 N_pos(c)≥N_cell，使全部 N≥N_pos 有

p(N,h_c(N))=K(N,h_c(N))>0，
b_U(x_c(N))>0，
Q_c(N)=QK_c(N)>0。

并输出 x_c(N) 从正侧趋0。所有实际概率对数及后面的 log 极限都在该同一正性尾段解释；不要求早期或全正 x 的 Brownian 全局正性。

## 5. S5-MAIN：实际倍率的唯一相位输出

对每个固定 c>0，以第4节同一合法尾段解释，须有

Real.log(Q_c(N))−E_c(N)→0，

其中系数恰为 q_c=π²/(4c³)，δ_c 是弱事件的 H_c−h_c。将 Q_c 换 QK_c 是由实际相等得到的同一输出。

准确量词：对每个 ε>0，存在 N_ε≥N_pos(c)，使全部自然 N≥N_ε 显示概率对数均合法且 |Real.log(Q_c(N))−q_c*δ_c(N)|<ε。不提供任意误差函数，不附加强 Brownian 收敛率。

同时列入两个透明的派生便利消费输出：

Q_c(N)/F_c(N)→1，
Q_c(N)−F_c(N)→0，

及 QK_c 的同一结论。前者是相对于同一显式 exp 因子的误差趋零，后者是绝对差趋零。它们的证明仍须消费 CP 弱相位尾界 0<δ_c≤1 对 F_c 的固定 c 有界性；不能以绝对差的结论反过来假设 F 自由有界。两输出不另计原始叶或贡献，唯一用途是将 CP0–CP3 的同一 F 相位转移为实际倍率及完整极限点。

## 6. S5-CUBE：c=1 的实际端点与源文内部相位

逐字使用 CP1 的自然数子列

σ_1(j):=(j+1)³，
σ_0(j):=(j+2)³−1。

它们须保留严格递增、自然数截断减法合法性及全部弱胞元合法的 CP 输出；不得把全部自然 N 误写成完美立方时间。

对同一 σ_1，交付 δ_1(σ_1(j))=1（全部 j），以及真实概率尾段上的

Real.log(Q_1(σ_1(j)))→π²/4，
Q_1(σ_1(j))=QK_1(σ_1(j))→exp(π²/4)。

对同一 σ_0，交付 δ_1(σ_0(j))→0，以及

Real.log(Q_1(σ_0(j)))→0，
Q_1(σ_0(j))=QK_1(σ_0(j))→1。

概率相等和对数合法性仅在同一实际正性尾段声明，不能由 CP 的确定性合法性替代。

源文97–98行的 c=1 内部相位，消费下节 c=1 时的同一 nearest-tie-up σ_α，交付倍率→exp(π²*(1−α)/4)。原文 O(k⁻²)、O(k⁻⁵) 的精细立方根余项不在本冻结声明；CP 已明确只承诺所需相位极限，不重开精细余项模块。

## 7. S5-PHASE：一般固定 c 的同一 CP 舍入子列

对子列只允许严格递增 σ:ℕ→ℕ；全部极限以自然数 j→∞。量化每个固定 c>0，逐字沿用 CP2 的

t_c(k):=((k:ℝ)/c)³，
a_c(k):=Nat.ceil(t_c(k))，
b_c(k):=Nat.ceil(t_c(k))−1。

须使用 CP2 提供的一组固定见证 K_a(c)、K_b(c)（K_b≥1），使

σ_a(j):=a_c(j+K_a)，σ_b(j):=b_c(j+K_b)

各自严格递增，全部 j 为正时间且处于同一弱胞元合法域；保留自然数减法的前置合法性。它们不必在未经截尾的初始 k 上严格递增。

沿 CP2 的同一 σ_a，δ_c→1、E_c→q_c、F_c→exp(q_c)，并须交付实际

Real.log(Q_c(σ_a(j)))→q_c，
Q_c(σ_a(j))=QK_c(σ_a(j))→exp(q_c)。

沿同一 σ_b，δ_c→0、E_c→0、F_c→1，并须交付实际

Real.log(Q_c(σ_b(j)))→0，
Q_c(σ_b(j))=QK_c(σ_b(j))→1。

再量化每个固定 α:ℝ，0<α<1。使用同一 CP2 定义

t_c,α(k):=(((k:ℝ)+α)/c)³，
v_c,α(k):=Nat.floor(t_c,α(k)+(1:ℝ)/2)。

半整数并列固定向上舍入，不额外要求任意 nearest 选择。使用 CP2 的固定 K_c,α，令 σ_α(j):=v_c,α(j+K_c,α)，保留其严格递增、全部合法及 δ_c(σ_α(j))→1−α、E_c→q_c(1−α)、F_c→exp(q_c(1−α))；再交付同一 σ_α 上

Real.log(Q_c(σ_α(j)))→q_c*(1−α)，
Q_c(σ_α(j))=QK_c(σ_α(j))→exp(q_c*(1−α))。

上述 Q=QK 均指最终相等，实际 log 均要求最终正性。任何为了概率正性追加的截尾必须是同一个固定 j 移位，并同步作用于 CP 的 δ/E/F 和 p/K/b_U；不允许先独立选择一个“有目标概率极限”的新 σ，再把它称为 CP 相位实现。

也须给出统一的同相位消费形式：对任意 d∈[0,1]，使用 CP3 同一条严格递增且全部弱胞元合法的 σ_d，同时满足

δ_c(σ_d(j))→d，
E_c(σ_d(j))→q_c*d，
F_c(σ_d(j))→exp(q_c*d)，
Real.log(Q_c(σ_d(j)))→q_c*d，
Q_c(σ_d(j))=QK_c(σ_d(j))→exp(q_c*d)。

d=1、0 分别直接消费上述 σ_a、σ_b；0<d<1 直接消费 α=1−d 的 σ_α，不另造相位模块或自由 ratio 相位定理。每条子列须实际是自然数时间，严格递增并最终合法。

## 8. S5-CLUSTER：完整实际倍率极限点集与无整列极限

沿用 CP 的精确定义

Cluster(z):={L:ℝ | ∃σ:ℕ→ℕ, StrictMono σ ∧ z(σ(j))→L}。

对每个固定 c>0，要求完整双向集合等式

Cluster(Q_c)=Cluster(QK_c)=[1,exp(q_c)]。

必须同时覆盖两方向：
- 任意严格递增 τ 上，若实际 Q_c(τ(j)) 有有限实极限 L，则 L∈[1,exp(q_c)]；不能只检查 CP 构造的几个子列。τ 最终处于正时间/合法/实际正性域须由 StrictMono 与固定尾域输出承接。
- 区间中每个值都由第7节与 CP3 同一相位的自然数严格子列实现；不得只列两端点或只给包含关系。若使用额外共同截尾，全部相位及概率量同步移位。

于是 Q_c 和 QK_c 的全自然时间列都不存在单一有限实极限；须给 q_c>0 及两个实际不同端点极限的合法消费。c=1 恰得 [1,exp(π²/4)] 及源文93行；全部固定 c>0 恰得第101–104行。没有一般 c 下必须存在 h_c(N) 精确为整数的前提，弱相位0只是极限点。

## 9. 源语义差异、门与未完成项

本冻结声明新增原始叶和总分母增量均0；它是既有原 S4/S5 概率义务的派生装配，不把 CP0–CP3、DA1/DA2 或每个输出编号重计为原始叶。

明确辅助范围为：正时间 sqrt/rpow 精确桥、原自归一化实际事件识别、最终胞元的统一尾桥、倍率相对于显式 F 的相对/绝对误差、CP 截尾子列的严格递增及完整 Cluster 定义。源文未逐项列出这些技术输出；它们各自直接服务实际 S5，不作为自由新前提。nearest 的并列规则遵从固定 CP，精细立方根 O 率未采纳。

仍未完成：固定实际 S4 的全部门、actualS3 的正式接线、实际 U1/S2、root 的实际 B/U/可测事件概率/首项 tail、CP 的形式认证以及本冻结声明自身独立来源/数学/形式门。调度中的 CORRECT、PR 或私有草稿不构成本文件认证依据。共享二维能量9/10任务不被本冻结声明消费，也不因本固定 Rademacher 事件桥被关闭。

只处理弱事件；strict 的整数 δ=0、其他 cosets、变化的 c、一般分布、uniform-x OQ4、强 Brownian O 率、完整 Spectrum/OQ4 根均排除。本轮 proofNONE、LeanNONE，无实现授权；关键链仍 OPEN。
