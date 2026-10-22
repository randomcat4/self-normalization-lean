# 固定实际 S3/DA1/DA2 下的 S4 概率装配：匿名数学证明

STATUS: PROVED
RELATIVE_TO: FIXED_ACTUAL_S3_DA1_DA2
FROZEN_TARGET: frozen-rademacher-s4-probability-assembly-v1.md，完整第3–7节
NEW_RAW_LEAF_INCREMENT: 0
SOURCE_RAW_DENOMINATOR_DELTA: 0
LEAN_STATUS: NOT_RUN_BY_EXPLICIT_SCOPE
FORMAL_IMPLEMENTATION: HOLD
FRESH_INDEPENDENT_MATHEMATICAL_REVIEW: REQUIRED
ACTUAL_B_U_TAIL_FORMAL_INTERFACE: ROOT_PENDING
ORIGINAL_OQ4_ROOT: OPEN

本文的 PROVED 精确表示：把获准的三个固定实际数学接口 actualS3、DA1、DA2 按其冻结声明的全部输出消费后，目标 S4 第3–7节全部成立。它不是对这些上游的重新证明或形式认证，也不是用任意函数、任意概率模型、自由余项或额外正性假设得到的条件模板。实际共享 B/U、事件概率桥及首项 tail 的正式接口仍归 root 且 pending，实际 U1/S2/actualS3 的形式接线未因本文关闭。本文无 Lean、服务器、网络、Git、数值实验或子代理。

引用简记：S4 为本次目标冻结；S3 为 frozen-rademacher-s3-brownian-assembly-v1.md；DA1 为 frozen-rademacher-lattice-shift-v1.md；DA2 为 frozen-rademacher-scale-assembly-v1.md。引用“§”均指相应文件的节号，不指未读证明。六份数学输入的字节身份及本角色曝光范围见同目录 input-exposure.md。

## 1. 先做量词与边界攻击

(1) 弱胞元端点。由 1≤m、m≤h<m+1 和 H=m+1，得到 h≥1、H≥2、0<H−h≤1；h=m 时 H−h=1。胞元上端没有包含，故这里不能出现 δ=0 的整数 strict 端点。后文只用 0<δ≤1，不假定 δ 有统一正下界；δ 可以任意靠近0。

(2) 小 m、零时间与奇偶。m=1、m=2、h=m 仍在 DA1 的全域量词内。n=0 也在 DA1 和 S3 §2 固定有限身份内；S3 保留 p(0,h)=K(0,h)=1、实际中心项及自然幂约定。本文不对早期零时间写普通的 h/√N。尺度 N/h²→+∞ 只推出最终正时间，不推出全部 n>0。既不选奇偶子列，也不要求单调性。

(3) 常数与序列。DA1 的存在常数在所有有限 m,h,n、任何三序列、任何 M 及任何 ε 之前选择；它不可能在后文偷偷变成逐序列或逐项常数。对于一个给定的 S4-ALL 三序列，第三尺度的 M>0 和 K_M 只选一次，并在全部 ε 之前固定；M 不随 k 或 ε 变化。证明对任意这样的见证均有效。

(4) 最终胞元。原序列早期可有 m=0、h<1、n=0。固定 K_0≥K_cell 后，对每个 j，j+K_0≥K_cell，因此同一组三条移位序列全部合法；不需要修改任何早期实际概率。第8节给出正反两个方向的自然阈值变换，而不是把全 k 上游改写成 eventual 版本。

(5) 次临界。N/h³→0 能推出一个固定的最终正上界，例如 M=1；它不是缺少第三尺度的反例。没有任何一步需要 N/h⁴→0 作为额外前提，该结论由固定 DA2 输出。

这些纯逻辑检查没有给出满足全部冻结前提的反例。以下完成端到端推导；不改变冻结对象或前提。

## 2. 首先且仅一次固定全域 DA1 常数

在引入任何有限参数和三序列之前，由固定 DA1 §4 取一个见证 C_DA>0，使

| Cdet(m,n,h) − w(m,n,h) |
≤ C_DA * (N/h⁴ + 1/H(m)²)                                           (2.1)

对全部 m∈ℕ、m≥1、m≤h<m+1、全部 n∈ℕ 成立，其中 N=(n:ℝ)，且此处 Cdet、w 按第3节真实表达式展开。DA1 §4 的存在量词确实在所有这些有限参数之前；故从现在起同一个 C_DA 也在任何序列、M 和尾部移位之前固定。后文不再从 DA1 选择新见证，不使用 DA1 内部 C_log 作为自由输入。

这一步只消费固定 DA1 的同域结论，并不证明或宣布其 Lean 认证。可以把本文量词读为：先存在这个满足 DA1 全有限域界的 C_DA，然后对每一个冻结目标允许的三序列，以该 C_DA 交付全部 S4 输出。

## 3. 实际对象逐项相容，不增设等值前提

所有对象均采用 S4 §3 和 S3 §2–4 的同一固定定义。以下是消费固定接口时的逐字识别或已在 S3 输出中的透明定义等式，不是另加的假设。

| 对象 | 识别依据与本稿消费方式 |
| --- | --- |
| ν_R 与其概率律见证 | 两者都是 Shao.OQ4.RademacherCosine.law 及实际 law_isProbabilityMeasure；没有另选分布。 |
| p(n,h) | 两者都是 Fin n→ℝ 上同一 Measure.pi 的 real(@Shao.closedStrip n h)，即从0出发、全部 k≤n 的前缀和满足绝对值≤h 的实际弱事件。不能按谱和重定义。 |
| K(n,h) | 两者都是 @Shao.OQ4.killedMass ν_R law_isProbabilityMeasure h n 0；起点、自然时间和阈值均相同。S3 §2 的有限身份给 p=K，包括 n=0。 |
| B、U、b_U | 两者都是原冻结题同一实际 Brownian 基准，U=sup_{0≤t≤1}|B_t|，b_U(x)=P_B(U≤x)。比较边际概率不需要新增耦合或独立性。 |
| N、H、u | N 是同一 n 的实数强制转换，H=(m:ℝ)+1，u=π/(4H)。DA1 §2、DA2 §2、S3 §2 与 S4 §3 的式子完全相同。 |
| a | S3 §2 已输出 Pair.amplitude m=(1/H)*cos(u)/sin(u)=Scalar.a m；代入 DA1 §2、DA2 §2 的式子即为同一 a，不要求用户另证一条等值前提。 |
| rho | S3 §2 已输出 Pair.rho m=cos(π/(2H))=Scalar.rho m；与 DA1/DA2 的固定式相同。自然幂 rho^n 保留。 |
| λ、δ | λ=π²/8 在所有接口相同；δ=H−h 由 m,h 决定，不独立量化。DA1/DA2 的合法性输出给 h=m 时 δ=1。 |
| A、D、g、T_U | A=a*rho^n，D=p/A；g(x)=(4/π)*exp(−λ/x²)，T_U(x)=b_U(x)/g(x)，均逐字使用 S3 §2、4 的实际定义。 |
| Cdet、w | Cdet=λ*N/h²+N*log(rho)+log(π*a/4)，w=(π²/4)*(N/h³)*δ。Cdet 就是 S3 §7–8 的 C；Cdet−w 就是 DA1 §4 绝对值中的同一个表达式。 |

由固定 DA1 §3、DA2.0 及 S3 §2、5 的合法性，全部合法有限胞元上 h>0、H>0、sin(u)>0、a>0、0<rho<1、π*a/4>0、A>0；h,H 的所用幂分母均不为0。这些均是固定接口结论，未变为最终定理的新前提。确定性 Cdet、w 在全域包括 n=0 合法；实际概率 log 和含 √N 的普通商另待共同尾段。

## 4. S4-ALL 的尺度与共同合法尾段

任取满足 S4 §4 全 k 胞元和三项尺度的 m_、n_、h_。在本节至第7节固定这三序列。把其第三尺度中的 M>0、K_M 一次固定。记 N_k、H_k、δ_k、a_k、rho_k 均为第3节同一定义；不新增正性或收敛假设。

由第3节的相容性，固定 DA2 §2 的对象和全 k 域逐项满足，其 §3 的三项尺度正是本题三项尺度。因此消费 DA2.0–DA2.3，得到：

- 全 k 的弱胞元合法性以及 h_k≥1、H_k≥2、H_k=h_k+δ_k、0<δ_k≤1，整数 h_k=m_k 时 δ_k=1；
- H_k→+∞，H_k/h_k→1，N_k/H_k²→+∞；
- 自然阈值 K_T、K_+，其后分别 H_k²≤N_k 和 n_k>0；
- N_k/h_k⁴→0、1/H_k²→0，以及 DA2.2 中其余有界性和三次幂替换输出；
- Cdet_k−w_k→0，正是 DA2.3 的固定表达式。

后一条可直接消费；第6节还用同一 DA1 常数与前两项余项尺度给出显式 ε 装配，确保 S4-ERR 的 O 系数没有丢失。没有将 N/h⁴→0 或 H²≤N 反加为前提。

现在 H→∞、N/H²→∞ 和全 k 胞元满足固定 S3 §5 的全部条件，且不需要任何三次幂额外假设来调用 S3。消费 S3-DOM（§6）、S3-ALG（§7）、S3-MAIN（§8），取得其阈值 K_time^3、K_pos^3、正侧 x→0、真实正性、精确 log 桥及中心化极限。

取

K_time := max(K_T, K_+, K_time^3)，
K_pos  := max(K_time, K_pos^3, K_M)。                              (4.1)

这些是有限多个自然数的最大值。若 k≥K_time，则 n_k≥1（自然数 n_k>0 等价于 1≤n_k）、N_k>0、√N_k>0、H_k²≤N_k；此时才以普通实数除法定义

x_k=h_k/√N_k。

由 h_k≥1 和 √N_k>0 得 x_k>0。S3-DOM 给：对每个 d>0，有自然阈值 K_x^3(d)，其后 0<x_k<d；取 max(K_time,K_x^3(d)) 即为本稿正侧趋零阈值。

若 k≥K_pos，S3 的实际输出给

p_k=p(n_k,h_k)=K(n_k,h_k)=K_k>0，
D_k>0，b_k=b_U(x_k)>0，T_U(x_k)>0。

故 Q_k=p_k/b_k=K_k/b_k>0。定义相同与正性输出来自同一次实际 S3 消费。所有以下普通概率对数与概率商均只在 k≥K_pos 使用。S4-DOM 的全部要求至此成立。

## 5. 同一个实际 η3 与精确对数桥

在上述共同尾段，记

L_k:=log(p_k/b_U(x_k))，
η3_k:=L_k−Cdet_k。                                                (5.1)

这没有选择一个新余项；它就是 S3-MAIN 的实际中心化表达式。由 S3-ALG，

η3_k = log(D_k)−log(T_U(x_k))，                                  (5.2)

且 S3-MAIN 给 η3_k→0，并带有最终合法性阈值。为明确检验式子确为同一表达式，尾段 A_k、p_k、b_k、D_k、g(x_k)、T_U(x_k)、a_k、rho_k 均正，故合法地有

log(D_k)=log(p_k)−log(a_k)−N_k*log(rho_k)，
log(T_U(x_k))=log(b_k)−log(g(x_k))。

S3 §7 的正时间平方根桥给 x_k²=h_k²/N_k、1/x_k²=N_k/h_k²，故

log(g(x_k))=log(4/π)−λ*N_k/h_k²，
log(a_k)−log(4/π)=log(π*a_k/4)。

相减正好得到 (5.2)；这里 log(rho_k^n_k)=N_k*log(rho_k) 使用自然幂与同一实数强制转换的已给桥，没有改用独立实时间或实数幂。原 h_k 的分母保留，没有替成 H_k。

S3-DOM 还给实际 D_k→1、log(D_k)→0 和实际 T_U(x_k)→1。log 在1附近连续且 T_U 最终正，故 log(T_U(x_k))→0；这也从 (5.2) 验证 η3→0。这里只用实际 Brownian 首项等价的 S3 输出，不使用 spectrum01 原文的强指数 O 率。η3 是显示的真实 log 比差，不是可自由给定的趋零 e。

对 K，有限身份 p_k=K_k 和 b_k>0 给

log(K_k/b_k)=L_k，
log(K_k/b_k)−Cdet_k=η3_k，
K_k/A_k=D_k。                                                     (5.3)

所以不存在另一套 K 余项或另一个概率极限过程。

## 6. S4-ERR 与 S4-MAIN 同时闭合

对每个 k≥K_pos，直接由 (5.1) 得精确拆分

L_k−w_k=(Cdet_k−w_k)+η3_k，
(L_k−w_k)−η3_k=Cdet_k−w_k。                                     (6.1)

全 k 胞元均合法，故对该 k 用一开始固定的 DA1 见证 (2.1)，得到

| (L_k−w_k)−η3_k |
≤ C_DA*(N_k/h_k⁴+1/H_k²)。                                      (6.2)

这就是完整 S4-ERR：C_DA 对所有有限参数和所有序列同一个，o(1) 则精确绑定 (5.1)–(5.2) 的 actualS3 η3。即使 n_k=0 的早期项存在，DA1 界本身仍覆盖；本文仅不在那里作 Brownian log 比解释。由 (5.3)，对 K 的拆分与界逐字相同且采用同一个 C_DA、η3。

给出 S4-MAIN 的共同 ε 阈值。任给 ε>0，因 C_DA>0，数 ε/(4C_DA)>0。由 DA2.2，存在自然阈值 L_4、L_H，使

k≥L_4 ⇒ N_k/h_k⁴<ε/(4C_DA)，
k≥L_H ⇒ 1/H_k²<ε/(4C_DA)。

两项均非负，故可用趋零的绝对值定义取得这些严格不等式。由实际 η3→0，有自然阈值 L_η≥K_pos，使 k≥L_η 时 |η3_k|<ε/2，并且实际 log 合法。取

K_ε:=max(K_pos,L_4,L_H,L_η)。                                    (6.3)

每个 k≥K_ε 都满足

|L_k−w_k|
≤ C_DA*(N_k/h_k⁴+1/H_k²)+|η3_k|
< ε/2+ε/2=ε。

由 (5.3) 同样得到实际 K 版本。K_ε≥K_pos，全部概率 log 自变量和分母真实为正，故这正是冻结 S4-MAIN 的完整 ε 量词，而非一个使用总函数 log(0) 的形式结论。这里没有声明 w_k 收敛，也没有给 η3 统一速率或对所有序列统一的尾部阈值。

## 7. S4-SUB：从次临界实际导出 M，再由 log 返回倍率

现在只给定同一全 k 弱胞元、h_k→∞、N_k/h_k²→∞，并给定次临界 r_k:=N_k/h_k³→0；不另给 M。因为 h_k>0、N_k≥0，所以全 k 有 r_k≥0。由趋零定义，取自然 K_r(1)，使其后 |r_k|<1。于是第三尺度的合法见证可取固定 M=1>0、K_M=K_r(1)，其后 r_k≤1。这一见证在本次 S4-ALL 消费前固定，且不依赖后续 ε；C_DA 更早已全局固定。

因此第4–6节全部适用，包括实际最终正性和 L_k−w_k→0。令 c=π²/4>0。全 k 的 δ 界给

0≤w_k=c*r_k*δ_k≤c*r_k。                                         (7.1)

任给 ε>0，取第6节 MAIN 在 ε/2 下的阈值 K_MAIN(ε/2)，再由 r→0 取 K_r(ε/(2c))。在

K_log(ε):=max(K_pos,K_MAIN(ε/2),K_r(ε/(2c)))                      (7.2)

之后，|L_k−w_k|<ε/2 且 0≤w_k<ε/2，故 |L_k|<ε。于是实际 log(p_k/b_k)→0。此处 δ 可以任取全部弱相位，包括整数时 δ=1；未额外固定相位。

由 k≥K_pos 时 Q_k=p_k/b_k>0，普通实指数与对数的反函数身份给

exp(L_k)=exp(log(Q_k))=Q_k。                                    (7.3)

标准实分析事实：对 |t|<1，均值定理和 exp 在 [−1,1] 上的导数界给 |exp(t)−1|≤exp(1)*|t|。给定任意倍率误差 ε>0，令

τ:=min(1, ε/(2*exp(1)))>0。

取自然阈值 max(K_pos,K_log(τ))，则 |L_k|<τ≤1，结合 (7.3) 得

|p_k/b_k−1|=|exp(L_k)−1|
≤exp(1)*|L_k|<exp(1)*τ≤ε/2<ε。

因此 p_k/b_U(x_k)→1。由 p_k=K_k，K_k/b_U(x_k)→1 是同一实际商的精确身份，不需新的收敛证明或新的正性前提。完整 S4-SUB 得证。这没有推出 x 上的 supremum 收敛或一般分布 OQ4。

## 8. S4-EVENTUAL：任意固定移位、所有项相容与原索引返回

现取 S4 §7 的任意三序列，仅假设存在 K_cell，使每个 k≥K_cell 都有原全胞元条件，并保留原三尺度。取任意固定自然数 K_0≥K_cell；以下证明对每个这样的 K_0 均成立，不依赖选取最小 K_cell，也不要求单调。

### 8.1 全 j 合法与逐阈值尺度保持

同时定义

tilde m_j=m_(j+K_0)，tilde n_j=n_(j+K_0)，tilde h_j=h_(j+K_0)。

对每个 j≥0，j+K_0≥K_cell，故这三条同一移位序列对全部 j 满足 1≤tilde m_j、tilde m_j≤tilde h_j<tilde m_j+1。于是可原样调用上游全 j actualS3/DA2；并非把它们的前提减弱为最终合法。

对任意自然阈值 L，定义 σ(L):=L dotminus K_0，其中 dotminus 是自然数截断减法。若 j≥σ(L)，则 j+K_0≥L：当 L≤K_0 时由 j+K_0≥K_0≥L；当 K_0<L 时，L=K_0+(L dotminus K_0)，由加法保序得到结论。这覆盖所有自然数端点，不用可能为负的自然数索引。

对 h→∞ 的每个实阈值 A，取原尺度的自然阈值 L_h(A)，其后 h_k>A。于是 j≥σ(L_h(A)) 时 tilde h_j>A。对 N/h²→∞ 的每个实阈值 B，取原阈值 L_t(B)；j≥σ(L_t(B)) 时 tilde N_j/tilde h_j²>B。若这些尺度先以全域 Real 商记号表达，至少在原索引 k≥K_cell 后 h_k≥1，故上述商与普通实商相等；可把原阈值先取 max(K_cell,L_t(B))。本段未使用非法有限前缀上的除零形式值。

原第三尺度的一对 M>0、K_M 一次固定。j≥σ(K_M) 时 j+K_0≥K_M，且移位胞元全部合法，所以

tilde N_j/tilde h_j³=N_(j+K_0)/h_(j+K_0)³≤M。

因此可用同一正 M、移位阈值 tilde K_M=σ(K_M)；若要把合法性显式并入原阈值，使用 σ(max(K_M,K_cell)) 也成立。固定 C_DA 在第2节已经先于原序列和 K_0 选定，移位不触发重新取常数。

若原序列另满足次临界 N/h³→0，则对每个 ε>0，取原自然阈值 L_r(ε) 并以 max(K_cell,L_r(ε)) 加入合法性；j≥σ(max(K_cell,L_r(ε))) 给 |tilde N_j/tilde h_j³|<ε。故次临界尺度同样沿本次移位保持。若次临界场景没有另给第三尺度，原尾部 r≥0，取 M=1 和 max(K_cell,L_r(1)) 即可先导出它；不是额外假设。

### 8.2 全部实际对象的同一索引等式

对以上合法移位三序列，用第4–7节得到 tilde K_time、tilde K_pos 和各误差阈值。各对象的定义及第3节相容性逐项给下列等式；绝不改换 Brownian 或 Rademacher 模型。

| 移位对象 | 精确原索引表达式与合法性 |
| --- | --- |
| tilde N_j、tilde H_j、tilde u_j | N_(j+K_0)、H_(j+K_0)、u_(j+K_0)；自然时间强制转换和 m+1 的逐字代入，对全部 j 成立。 |
| tilde a_j、tilde rho_j、tilde A_j | a_(j+K_0)、rho_(j+K_0)、A_(j+K_0)；相同透明定义和自然幂，全部 j 合法且 A>0。 |
| tilde δ_j | H_(j+K_0)−h_(j+K_0)=δ_(j+K_0)，全部 j 合法，仍保留整数弱端点 δ=1。 |
| tilde p_j | p(tilde n_j,tilde h_j)=p(n_(j+K_0),h_(j+K_0))=p_(j+K_0)，因为同一函数的自变量逐字相等。 |
| tilde K_j | K(tilde n_j,tilde h_j)=K(n_(j+K_0),h_(j+K_0))=K_(j+K_0)，同一杀死质量定义、同一起点0。 |
| tilde λ | λ=π²/8，不移换常数。 |
| tilde x_j、tilde b_j | j≥tilde K_time 时 N_(j+K_0)>0，同一正平方根给 tilde x_j=x_(j+K_0)；从而 tilde b_j=b_U(x_(j+K_0))=b_(j+K_0)。 |
| tilde Cdet_j、tilde w_j | Cdet_(j+K_0)、w_(j+K_0)，由同一 H、h、N、a、rho、δ 的显示表达式代入，全部 j 的移位胞元上确定性项合法。 |
| tilde D_j | tilde p_j/(tilde a_j*tilde rho_j^tilde n_j)=D_(j+K_0)，全部 j 分母正；最终 D>0 取自实际 S3。 |
| g(tilde x_j)、T_U(tilde x_j) | 在正时间尾部为 g(x_(j+K_0))、T_U(x_(j+K_0))，同一实际 b_U 与同一确定性 g；在 tilde K_pos 后都正。 |
| tilde L_j、tilde η3_j | j≥tilde K_pos 时为 L_(j+K_0)、η3_(j+K_0)，因为实际 p/b、Cdet 已逐项相等；同一 η3=logD−logT_U 桥也逐项相等。 |

这里 p、K 两行在全部 j（包括 tilde n_j=0）都是同一实际有限概率的代入；没有制造“合法前缀概率”。原始索引 k<K_0 的 p(n_k,h_k)、K(n_k,h_k) 保持冻结定义且不被赋成任何替代值。

### 8.3 从移位结论返回原序列的自然阈值

先给返回规则。若某移位结论对全部 j≥J 成立，则取原索引阈值 L:=K_0+J。对任意 k≥L，有 k≥K_0，令 j:=k dotminus K_0。自然数截断减法在此无截断损失：j+K_0=k。由 k≥K_0+J 得 j≥J。因此可用第8.2节的逐项等式把移位结论返回同一原概率量。

具体取原 K_time^orig:=K_0+tilde K_time、K_pos^orig:=K_0+tilde K_pos。后者≥前者且≥K_cell。由返回规则和对象表，原序列在其后有 n≥1、N>0、√N>0、H²≤N、x>0、p=K>0、b_U(x)>0、D>0、T_U(x)>0、Q>0。全 k 合法性不在原序列非法前缀上声明。

S4-DOM 的两个发散输出逐阈值返回：给定实 A，移位 H→∞ 给自然 J_H(A)，以 max(K_cell,K_0+J_H(A)) 为原阈值；给定实 B，移位 N/H²→∞ 给 J_t(B)，以 max(K_cell,K_0+J_t(B)) 为原阈值。给定 d>0，正侧 x→0 的原阈值取 max(K_pos^orig,K_0+J_x(d))。给定 ε>0，N/h⁴→0、1/H²→0 的原阈值分别取 max(K_cell,K_0+J_4(ε))、max(K_cell,K_0+J_Herr(ε))；其后 h,H 正，故这些是普通合法商的相同极限。需要 H/h→1 或 DA2 的其他便利输出时，也按相应 ε 的同一返回规则获得；未借单调性。

S4-MAIN：给定 ε>0，取移位第6节的 tilde K_ε≥tilde K_pos，令

K_ε^orig:=max(K_cell,K_pos^orig,K_0+tilde K_ε)。                 (8.1)

若 k≥K_ε^orig，则 j=k dotminus K_0≥tilde K_ε，实际 log 合法，且

|log(p_k/b_U(x_k))−w_k|
=|log(tilde p_j/b_U(tilde x_j))−tilde w_j|<ε。

同一等式经 p=K 给 K 版本。S4-ERR 在全部 k≥K_pos^orig 由第8.2节代回移位 (5.2)、(6.1)、(6.2)，得到同一实际 η3 和同一 C_DA 的精确拆分与界。对 η3→0 的每个 ε>0，原阈值取 max(K_pos^orig,K_0+tilde L_η(ε))；没有另取 e 或 C。

S4-SUB：若原次临界，则第8.1节已证明移位次临界并导出所需 M。给定 ε>0，原 log 误差阈值取 max(K_pos^orig,K_0+tilde K_log(ε))；原倍率误差阈值取 max(K_pos^orig,K_0+tilde K_ratio(ε))。返回规则和对象等式分别给原实际 log→0、p/b→1、K/b→1，并保留共同正性。每个阈值都是明确自然数；使用的减法仅为已证明合法的截断减法。

上述论证对任意固定 K_0≥K_cell 有效。若只需原序列存在一个阈值，可取其中任意一个 K_0；本文同时保留冻结要求的任意 K_0 性质。故 S4-EVENTUAL 的全部尾桥成立，不改变任何原 h 或实际事件。

## 9. 全项形式记号与普通尾段公式的最终相等

本文的实际概率比较、普通含 √N 的除法及概率 log 均在上面共同正时间和正性尾段解释。没有定义非法前缀上的新概率或新 Brownian 尾函数。

若将冻结目标的全项写法用于形式极限，可逐字以 Real 的总函数 sqrt、除法、log 记

xhat_k:=h_k/Real.sqrt(N_k)，
Lhat_k:=Real.log(p_k/b_U(xhat_k))，
ηhat3_k:=Lhat_k−Cdet_hat_k，
Dhat_k:=p_k/(a_k*rho_k^n_k)，
That_k:=b_U(xhat_k)/((4/π)*Real.exp(−λ/xhat_k²))，

并对 Cdet_hat、what、其他确定性商采用相同显示式的总函数语法。全胞元情况在 k≥K_pos，最终胞元情况在 k≥K_pos^orig，已经证明 h,H,N,√N、a,rho,A、g、p,b,D,T_U 及全部 log 自变量/分母具备所需正性；在那里逐字有

xhat=x，Lhat=L，Cdet_hat=Cdet，what=w，
ηhat3=η3，Dhat=D，That=T_U(x)。                                  (9.1)

概率商的总函数项也与普通 Q 精确相等。对于只含 h,H 的确定性商，其 equality 更早在合法胞元尾部成立。式 (9.1) 是明确的 eventual 等式，所以这些总项与本文普通尾段公式具有相同极限；每个 ε 阈值均可再与相应 K_pos 取 max。早期可能出现的 Real.log(0)、除零或总函数 sqrt 值从未被当成真实概率解释、正性依据或极限证明步骤；本文不使用 b_U(0) 的任何信息。

## 10. 依赖账、承重义务和未完成门

| 标签 | 依赖或产出 | 精确范围 |
| --- | --- | --- |
| KNOWN | 实数/自然数次序、正数商与幂、有限 max；自然数 dotminus 的两分支性质；正数 log/exp 反函数身份、log 在1连续、exp 均值定理界。 | 普通代数与实分析，不含概率、谱或 Brownian 新输入。 |
| FIXED_INPUT | S3 §2–4 的实际对象/透明定义、§6 DOM、§7 ALG、§8 MAIN。 | 同一 p、K、a/rho、实际 b_U、D/T_U 与实际 η3；全 k 胞元和两尺度下的固定实际输出。未读取其证明。 |
| FIXED_INPUT | DA1 §3–4 合法性及先于全部有限参数的全域常数界。 | 固定 m≥1、弱胞元、全部 n≥0；无自由误差函数或逐序列常数。未读取其证明。 |
| FIXED_INPUT | DA2.0–DA2.4。 | 同一确定性对象、全 k 胞元及原三项尺度；特别消费 DA2.1–DA2.3。DA2.4 可另验证次临界中心项；本文以 δ 尾界直接证明实际次临界消费者。未读取其证明。 |
| FIXED_INPUT | 授权原谱来源 S4 段与 frozen01 的同一 U/首项等价。 | 仅定位来源、目标和固定实际接口；强 Brownian 指数 O 不消费。 |
| PROVED_HERE | 第3节定义相容消费、第4–6节 S4-DOM/MAIN/ERR。 | 同一个全域 C_DA、同一个 actualS3 η3、全部弱整数端点与早期 n=0 保留。 |
| PROVED_HERE | 第7节实际 S4-SUB。 | 从次临界推出固定最终 M；经 δ 界与合法 exp/log 得实际 p/b 和 K/b 趋1。 |
| PROVED_HERE | 第8–9节 S4-EVENTUAL 与形式全项桥。 | 任意 K_0≥K_cell、同一 j+K_0 的全部对象相等、逐阈值尺度保持、自然阈值返回；原非法有限前缀概率原样保留。 |
| OPEN | root 的实际 B/U、可测版本/事件概率桥、首项 tail 公开正式接口，及实际上游 U1/S2/S3/DA1/DA2 的形式接线与各自认证门。 | 本文不发明名称、实现或公理，不把固定接口消费改称上游已 Lean 认证。 |
| OPEN | 本稿全新独立数学审查、目标来源门及后续形式门。 | 本稿为匿名作者产物，无自行独审通过宣称；形式状态 HOLD。 |
| OPEN | 实际 S5、strict、其他 cosets、一般分布、均匀 x 窗口、完整 Spectrum/OQ4 根。 | 本稿不关闭或替代这些目标，不读取未授权下游。 |

原始目标：spectrum01 的 (S4)，即实际弱事件概率相对同一 Brownian 基准的 log 比，化为 π²Nδ/(4h³)+O(N/h⁴+H⁻²)+o(1)，以及其第80–81行次临界实际倍率结论。剩余承重义务是固定 S3/DA1/DA2 的同一对象和表达式拼接、真实 log 最终合法性、唯一绑定的 O+o，以及最终胞元的忠实尾桥。本文第3–9节逐项消除这些装配义务。

直接消费者有两个：第7节已经完成的实际次临界 p/b、K/b→1；以及将来实际 S5 固定临界相位/倍率极限点任务对 S4-EVENTUAL 的消费。后者在其自身任务中核验尺度和相位后才能使用本文输出，本文不证明 S5。全链新增 raw 叶为0，原始来源总分母变化为0。PROVED 仅相对于 FIXED_ACTUAL_S3_DA1_DA2；共享实际 Brownian 正式接口与原 OQ4 根仍 pending/open。
