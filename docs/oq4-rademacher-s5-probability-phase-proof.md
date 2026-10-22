# OQ4 S5：固定实际 S4 与 CP 输入下的匿名相对证明

STATUS: PROVED_RELATIVE_FIXED_ACTUAL_S4_AND_CP
FORMAL_STATUS: HOLD
FRESH_INDEPENDENT_REVIEW: PENDING
NEW_RAW_LEAF_INCREMENT: 0
SOURCE_RAW_DENOMINATOR_DELTA: 0
UPSTREAM_FORMALLY_CERTIFIED: NOT_CLAIMED
ORIGINAL_SPECTRUM_OQ4_ROOT: OPEN

本稿的结论是唯一锁定的实际 S4 与 CP0–CP3 输出蕴含冻结 S5 第3–8节的全部输出。所消费的 S4 仍指其指定的真实产品概率 p、同一个 killedMass K、原 Brownian b_U；没有把它换成任意满足某个渐近式的数列假设。固定上游、root 的实际 B/U/事件概率/tail 以及全部正式接口的认证不由本稿完成。本文不证明或修改任何上游。

## 1. 固定输入、量词与先行边界攻击

数学输入只含以下五份文件。A 是待证目标，B、C 是本稿的唯一固定数学接口，D、E 固定来源语义。

| 标号 | 文件 | SHA256 | 字节 |
| --- | --- | --- | ---: |
| A | drafts/oq4/frozen-rademacher-s5-probability-phase-v1.md | b79dd1cb131277acab9f156668ed1fde8aafa9c6632b821951719617b701b04d | 15006 |
| B | drafts/oq4/frozen-rademacher-s4-probability-assembly-v1.md | 144e3c290ca60c174ceec0cc85b41519a82faf0eb55c09a1c54e61e1d097e00a | 11831 |
| C | drafts/oq4/frozen-rademacher-critical-phase-v1.md | 4e8be7821b842a1fe7a6a143f9705fa476b05615e122fdd621d4cb1c5c88c1ce | 8147 |
| D | C:/game/shao/current/oq4/c01/spectrum01.md | b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b | 4306 |
| E | C:/game/shao/current/oq4/frozen01.md | ea50b9fe0d742cbc9481fb126476ae2a788c7b0ec42d4e60636d757baf7cbc5a | 1491 |

前三个路径相对于 C:/game/shao lean。B 的第3、4、7节及 C 的 CP0–CP3 作为锁定的相对输入；引用它们的输出不表示已认证其证明。D 的强 Brownian O 率和精细立方根 O 率均不使用。E 中原实际 U 的身份保持不变。

先作以下逻辑攻击，再展开证明。

1. c 必须一次固定且严格正。若让 c 随 N 变化，第三尺度不再是同一个常数，本稿的固定 F 界也不能据此取得；该扩张不在 A 中。本稿所有阈值均允许依赖这个固定 c，不声称对 c 一致。
2. N=0 不可代入正底数 rpow/sqrt 的指数法则；早期 h<1 不可代入主胞元。下面只在 N≥1 证明精确正尺度桥，只在共同合法尾段使用 S4 和概率对数，原有限前缀不改。
3. 弱事件整数高度的 δ 是1，而非0。ceil(t)−1 的自然数减法必须先有 ceil(t)≥1；k=0 不能被误当成严格位于 t 下方。下面沿用 CP 的合法固定截尾。
4. CP 给的是确定性相位，并不给概率正性。下面从 B 的同一实际输出取得一个 N_pos(c)，由严格递增性把这个尾域带到每条原 CP 子列。
5. 仅有 Q/F→1 一般不能推出 Q−F→0。下面先由 CP0 的 0<δ≤1 证明固定 c 的 F 界，再推出绝对差。
6. 只列 CP 端点不足以证明完整 Cluster。下面分别证明任意严格递增 τ 的包含关系，以及每一个 L 的同一 CP3 实现。
7. 原 V_N 的身份不能被当成额外前提。下面从 ν_R 的两点支持、各坐标柱集和有限共同满测集证明 V_N=√N 几乎处处，再识别真实事件。

这些攻击在冻结范围内没有给出反例，也没有留下额外接口前提。后文逐项闭合上述风险。

## 2. 对象固定

任取一个 c∈ℝ，0<c，以下一直固定它。对 N∈ℕ 写 R_N=(N:ℝ)，并逐字使用 A §3/C §2 的定义：

\[
r_N=\operatorname{rpow}(R_N,1/3),\quad h_N=cr_N,\quad
m_N=\operatorname{Nat.floor}(h_N),\quad H_N=(m_N:\mathbb R)+1,
\]
\[
\delta_N=H_N-h_N,\quad q=\frac{\pi^2}{4c^3},\quad
E_N=q\delta_N,\quad F_N=\exp(E_N),\quad
x_N=c\,\operatorname{rpow}(R_N,-1/6).
\]

这里所有分数指数都是实数分数。ν_R、其概率实例及实际对象固定为 A §3/B §3 中的

\[
\nu_R=\tfrac12\delta_1+\tfrac12\delta_{-1},\qquad
\mu_N=\operatorname{Measure.pi}(i:\operatorname{Fin}N\mapsto\nu_R),
\]
\[
p(N,h)=\mu_N.\mathrm{real}(\operatorname{closedStrip}(N,h)),\qquad
K(N,h)=\operatorname{killedMass}(\nu_R,h,N,0),
\]
\[
U=\sup_{0\le t\le1}|B_t|,\qquad b_U(x)=P_B(U\le x),
\]
\[
Q_N=\frac{p(N,h_N)}{b_U(x_N)},\qquad
QK_N=\frac{K(N,h_N)}{b_U(x_N)}.
\]

closedStrip 按 B §3 的透明语义，是从0出发的全部 k≤N 前缀和绝对值≤h 的弱事件。p 不按任何谱表达式重定义。B、U、P_B 不变，也不要求与 μ_N 的随机游走耦合。q>0：c³>0、4c³>0、π²>0；并且 exp 的严格正性给全部 N 的 F_N>0。这一点不需要概率对数合法。

## 3. S5-DOM 的全部正时间精确桥

本节使用 A §3 的定义和 C-CP0；所有指数计算只在 N≥1 时进行。

固定 N≥1，则 R=R_N>0。令 ℓ=log R。正底数实幂的公式是 R^a=exp(aℓ)。因此 r_N=exp(ℓ/3)>0，x_N=c exp(−ℓ/6)>0，h_N=c exp(ℓ/3)>0。

令 s=exp(ℓ/2)>0。由指数加法和 exp(log R)=R，

\[
s^2=\exp(\ell)=R.
\]

s 是 R 的非负平方根，故 s=√R，特别 √R>0。这实际核验了 sqrt 与 rpow(R,1/2) 的等式，而没有把 sqrt 直接当成形式指数。再有

\[
r_N^3=\exp(\ell)=R,\qquad
h_N^3=c^3R,\qquad
\frac{R}{h_N^3}=\frac{R}{c^3R}=\frac1{c^3}.
\]

最后一个约分使用 R>0、c³>0，分母均不为0。它也与 C-CP0 的同一立方恒等式完全一致。又由同一正底数规则，

\[
x_N\sqrt R
=c\exp(-\ell/6)\exp(\ell/2)
=c\exp(\ell/3)=h_N.
\]

由于 √R>0，可除以它得到 x_N=h_N/√R。由这些正量，还得到供极限使用的精确式

\[
x_N^2=\frac{h_N^2}{R},\qquad
\frac{R}{h_N^2}=\frac{r_N}{c^2}>0.
\]

C-CP0 给一个固定 N_cell=N_cell(c)≥1，使所有 N≥N_cell 同时满足

\[
h_N\ge1,\quad 1\le m_N,\quad
(m_N:\mathbb R)\le h_N<H_N,\quad
H_N=h_N+\delta_N,\quad0<\delta_N\le1.
\]

在这些 N 上，若 h_N 为整数则 δ_N=1。C-CP0 同时给 h_N→+∞ 与 R_N/h_N²→+∞。第三尺度在每个 N≥1 已精确等于 1/c³，故可用的同一固定正界为 M=1/c³；不能把它只写成一个随 N 变化的界。

x_N 从正侧趋0也可直接核验。任给 ε>0，由 R_N/h_N²→+∞，最终有 R_N/h_N²>1/ε²；同时取 N≥1。正量取倒数给 0<x_N²=h_N²/R_N<ε²，再由 x_N>0、ε>0 得 0<x_N<ε。这只用原第二尺度，没有假设全正 x 的 Brownian 正性。由第三尺度与 h_N→∞，还可导出 R_N/h_N⁴=(1/c³)/h_N→0；这是推论，不是替代 B 的原三尺度前提。

## 4. 固定产品律下的能量与原实际事件

本节只用 A §3–4/B §3 给出的实际 law、产品测度与弱前缀事件语义，以及有限乘积测度的定义。

设 A_R={−1,1}。该集合可测，两点 Dirac 质量的显示公式给

\[
\nu_R(A_R)=\tfrac12+\tfrac12=1,\qquad
\nu_R(A_R^c)=0,\qquad \nu_R(\mathbb R)=1.
\]

对每个 i∈Fin N，令 C_i={a∈Path N:a_i∈A_R}。其补集是第 i 坐标取 A_R^c、其他坐标取 ℝ 的有限乘积柱集。因此有限产品测度的矩形公式给

\[
\mu_N(C_i^c)=\nu_R(A_R^c)
\prod_{\ell\ne i}\nu_R(\mathbb R)=0.
\]

N=1 时右边余下的乘积是1；没有使用坐标以外的随机性。令

\[
\Omega_N=\bigcap_{i\in\operatorname{Fin}N}C_i.
\]

Fin N 有限，故 Ω_N^c 是有限个零测柱集的并，μ_N(Ω_N^c)=0，μ_N(Ω_N)=1。N=0 时该交集为空交，即整个空路径空间，也有质量1。这里构造的是所有坐标共同成立的一个满测集，并非只给每个坐标分别的 a.e. 结论。

对 a∈Ω_N，每个 a_i 是1或−1，所以 a_i²=1。于是

\[
\sum_{i:\operatorname{Fin}N}a_i^2
=\sum_{i:\operatorname{Fin}N}1=R_N,\qquad
V_N(a):=\sqrt{\sum_i a_i^2}=\sqrt{R_N}.
\]

这证明了指定 V_N=√R_N 的 μ_N-几乎处处等式；没有在最终定理中新增一个能量身份假设。

为核对事件概率，令 S_k(a) 是实际前缀和，S_0=0。固定 N≥1，定义

\[
\mathcal E_N=\{a:\forall k\le N,\ |S_k(a)|\le x_NV_N(a)\},
\quad
\mathcal C_N=\{a:\forall k\le N,\ |S_k(a)|\le h_N\}.
\]

每个前缀和是有限坐标和；V_N 是有限平方和再取 sqrt，均为连续函数。上面两个集合是有限个连续不等式的交，故可测。在 Ω_N 上，第3节的桥给

\[
x_NV_N(a)=x_N\sqrt{R_N}=h_N,
\]

所以两个事件的指标完全相同；其对称差包含在 Ω_N^c 中，质量为0。μ_N 是概率测度，因此相等的有限 ENNReal 质量取实部仍相等，得到

\[
\mu_N.\mathrm{real}(\mathcal E_N)
=\mu_N.\mathrm{real}(\mathcal C_N)=p(N,h_N).
\]

\(\mathcal C_N\) 正是 B §3 指定的 closedStrip，未更换 law、阈值或事件。对 N≥1，源文 M_N 是 k=1,…,N 的有限最大值，故 M_N≤x_NV_N 等价于这些 k 的全部不等式。加入 k=0 也不改变事件，因为 x_N>0、V_N≥0，所以 0≤x_NV_N；对 h_N 同样有 h_N>0。由此原 D §3 的自归一化弱事件概率恰为 p(N,h_N)。

早期 0<h_N<1 的正时间项也服从这同一事件识别：在 Ω_N 上 |S_1|=1>h_N，故实际两个弱事件的概率都为0，没有调用主胞元谱公式。N=0 时 r_0=h_0=0，V_0=0，原空路径事件和 closedStrip(0,0) 的概率为1。本文保留这一项，不在那里断言 x=h/√N，不使用 b_U(0)，也不解释该项的概率对数。若正式层复用别名形式的能量，所需透明等式正是本节显示的有限平方和定义；它的正式接线仍在 HOLD 范围。

## 5. 按 S4-EVENTUAL 使用同一移位，再返回原索引

依赖为 B §3、S4-ALL/S4-MAIN (§4)、S4-EVENTUAL (§7)，以及第3节/C-CP0。此处展示实际移位的全部条件，未将 B §4 的 all-j 前提改成 eventual-j。

先固定 J=N_cell；以下检验对任何固定 J≥N_cell 都成立。设

\[
\widetilde n_j=j+J,\quad
\widetilde m_j=m_{j+J},\quad
\widetilde h_j=h_{j+J},\quad
\widetilde R_j=(j+J:\mathbb R).
\]

每个 j 都有 j+J≥J≥N_cell≥1。由第3节，每个 j 同时满足

\[
1\le\widetilde m_j,\qquad
(\widetilde m_j:\mathbb R)\le\widetilde h_j
<(\widetilde m_j:\mathbb R)+1.
\]

这正是 B §7 要求移位后 fixed actualS3/DA2 具有的原全 j 弱胞元条件。原两项发散尺度沿 j↦j+J 保持：对每个实阈值，若原尺度在 N≥A 后超过它，则 j≥A 后的 j+J≥A 也超过它。第三尺度对所有 j 精确为

\[
\widetilde R_j/\widetilde h_j^3=1/c^3=M>0.
\]

故三个原尺度均已验证，M 不变，其最终界阈值甚至可取0。这不是额外增加的第四尺度假设。

由于 p、K 和所有高度函数是固定实际函数，逐项有

\[
\widetilde p_j=p(j+J,h_{j+J}),\quad
\widetilde K_j=K(j+J,h_{j+J}),\quad
\widetilde H_j=H_{j+J},\quad
\widetilde\delta_j=\delta_{j+J}.
\]

每个 j 都是正时间，第3节故给

\[
\widetilde x_j=\widetilde h_j/\sqrt{\widetilde R_j}=x_{j+J},
\quad \widetilde b_j=b_U(x_{j+J}),
\quad \widetilde Q_j=Q_{j+J},\quad
\widetilde{QK}_j=QK_{j+J}.
\]

同理 \(\widetilde E_j=E_{j+J}\)、\(\widetilde F_j=F_{j+J}\)。B 的 H、δ、确定性中心项、D、T_U、η3、w 若出现，也全是在同一个 j+J 处代入原定义；没有另选尾误差或尾函数。尤其 S4 的中心相位满足每个 j 的精确等式

\[
\widetilde w_j
=\frac{\pi^2}{4}\frac{\widetilde R_j}{\widetilde h_j^3}
 \widetilde\delta_j
=\frac{\pi^2}{4c^3}\delta_{j+J}=E_{j+J}.
\]

现在消费锁定 B 对这些具体移位序列的输出。它给固定 j_time 及 j_pos≥j_time，使 j≥j_pos 时

\[
\widetilde p_j=\widetilde K_j>0,\quad
b_U(\widetilde x_j)>0,\quad
\widetilde Q_j=\widetilde{QK}_j>0.
\]

它还给正时间、sqrt 正性、\(\widetilde H_j^2\le\widetilde R_j\) 的共同尾域，及 S4-MAIN 的准确量词：对每个 ε>0，存在 j_ε≥j_pos，使所有 j≥j_ε 的显示概率对数合法，并且

\[
|\log \widetilde Q_j-\widetilde w_j|<\varepsilon.
\]

下面显式返回原 N。固定

\[
N_{\rm pos}=J+j_{\rm pos}\ge N_{\rm cell}.
\]

对每个 N≥N_pos，有 N≥J，故自然数减法 j=N−J 没有截断损失，并且 j+J=N、j≥j_pos。以上所有量的逐项等式于是同时给出

\[
p(N,h_N)=K(N,h_N)>0,\quad b_U(x_N)>0,\quad
Q_N=QK_N>0.
\]

同一返回也给原索引的正时间及 H_N²≤R_N 的最终输出。第3节已独立给 x_N 从正侧趋0，且与 B 输出的 x 完全相同。

对 ε>0，取 N_ε=J+j_ε≥N_pos。若 N≥N_ε，则 j=N−J≥j_ε，故

\[
|\log Q_N-E_N|<\varepsilon.
\]

这正是 A §5 的概率对数量词，且全部概率正性、x、b_U、δ、E、F 都经同一个索引返回。未声称 N<J 或其他非法有限前缀已经合法，也没有借 b_U(0) 或总 log/div 的形式值补洞。固定 J 后，N_pos 和所有后续阈值均是本段取得的同一组原索引阈值。

## 6. 实际相位误差、相对误差与绝对误差

依赖为第5节的同一实际 S4-MAIN 输出，以及第3节/C-CP0 的弱相位界。

只在 N≥N_pos 的实际合法尾段写

\[
e_N:=\log Q_N-E_N.
\]

它是指定概率的显示表达式，不是额外假设的自由趋零函数。第5节证明 e_N→0，并给其每个 ε 的合法共同阈值。QK_N=Q_N 在该尾段精确成立，所以用 QK 写的同一 e_N 与极限立即相等。

又因为 N_pos≥N_cell、q>0、0<δ_N≤1，有

\[
0<E_N\le q,\qquad 1<F_N\le B_c:=\exp(q).
\]

B_c 是只依赖固定 c 的有限正实常数。由 Q_N>0 可以合法使用 exp(log Q_N)=Q_N，因而在同一尾段

\[
Q_N=\exp(E_N+e_N)=F_N\exp(e_N),
\qquad Q_N/F_N=\exp(e_N).
\]

exp 在0连续，给 Q_N/F_N→1。绝对差满足

\[
|Q_N-F_N|
=F_N|\exp(e_N)-1|
\le B_c|\exp(e_N)-1|\longrightarrow0.
\]

例如对给定 ε>0，先由连续性取 θ>0，使 |u|<θ 时 |exp(u)−1|<ε/B_c，再取第5节 e_N 的 θ 阈值并与 N_pos 取最大；其后上述绝对差<ε。这样 F 的有界性确实由固定弱相位推出，而非从目标倒推。QK 的相对/绝对结论由同一个尾段相等式得到。没有给 e_N 任何强 Brownian 收敛率。

合并第4、5节，源文实际弱自归一化事件与原 Brownian 基准的倍率，在所有正时间的事件分子相等、并在 N≥N_pos 的正分母尾段恰等于 Q_N。因此本节证明的是实际倍率的 S5，而非仅有对数主率。

## 7. 严格递增子列与共同截尾规则

下面的初等索引事实用来同步所有概率与 CP 量。若 σ:ℕ→ℕ 严格递增，则 σ(j)≥j：j=0 时成立；若 σ(j)≥j，严格递增的自然数值给 σ(j+1)≥σ(j)+1≥j+1。因此 σ(j)→∞，且每个固定阈值 A 之后，j≥A 即有 σ(j)≥A。

所以任意这种 σ 上，第5、6节的全部整列最终结论均可组合到精确的原 σ：j≥N_pos 时同一位置的 p、K、x、b_U、Q、QK 已合法，且

\[
e_{\sigma(j)}\to0,\quad
(Q-F)_{\sigma(j)}\to0,\quad
(Q/F)_{\sigma(j)}\to1.
\]

若 CP 在这同一 σ 上给 δ→d、E→qd、F→exp(qd)，则尾段的精确恒等式与极限加法给

\[
\log Q_{\sigma(j)}
=E_{\sigma(j)}+e_{\sigma(j)}\to qd,
\]
\[
Q_{\sigma(j)}
=F_{\sigma(j)}+(Q-F)_{\sigma(j)}
\to\exp(qd),
\quad QK_{\sigma(j)}\to\exp(qd).
\]

概率等式 Q=QK 和对数解释只在 j≥N_pos 声明。这里没有从概率极限反向挑选 σ。

如需让一条输出子列的每个 j 都已具有概率正性，固定 T=N_pos(c)，统一定义

\[
\widehat\sigma(j)=\sigma(j+T).
\]

它仍是自然数严格递增函数，且 \(\widehat\sigma(j)\ge j+T\ge N_{\rm pos}\)。所有量使用同一个替换 σ(j)↦σ(j+T)：R、r、h、m、H、δ、E、F、x、p、K、b_U、Q、QK 及合法 e 全部同步。CP 的全部合法性保留；原 CP 极限沿这个固定 j 移位不变。反过来，原 σ 的有限前缀不影响极限，所以前述极限仍是原 σ 的极限。此 T 不依赖 ε，也不依赖 d；但不声称它关于 c 一致。后文先保留 CP 原 σ，在需要全 j 正性时仅使用这一明示的共同移位。

## 8. c=1 的实际立方端点和内部相位

本节消费 C-CP1 的原自然数子列，不重新构造：

\[
\sigma_1(j)=(j+1)^3,\qquad
\sigma_0(j)=(j+2)^3-1.
\]

对于 σ_1，k=j+1≥1，CP1 给 h_1(k³)=k、m=k、H=k+1、δ=1，全部 j 均为正时间和合法弱胞元。对于 σ_0，k=j+2≥2，故 k³≥8、k³−1≥7≥1；自然数减一等于普通整数减一，实数转换为 (k:ℝ)³−1。CP1 给 k−1<h_1(k³−1)<k、m=k−1、H=k；m 的减法也因 k≥2 而合法，δ=k−h_1(k³−1)→0。CP1 已给两条 σ 的 StrictMono；其相邻立方增量为3k²+3k+1>0，而合法的共同减一不改变大小关系。没有把全部 N 误写成立方时间。

令 q_1=π²/4。由第7节在完全相同的两条子列上得到：

| 精确 CP 子列 | δ 极限 | E 极限 | F 极限 | log Q 极限 | Q 与 QK 的共同极限 |
| --- | ---: | ---: | ---: | ---: | ---: |
| σ_1(j)=(j+1)³ | 1（全部 j 精确等于1） | q_1 | exp(q_1) | q_1 | exp(q_1) |
| σ_0(j)=(j+2)³−1 | 0 | 0 | 1 | 0 | 1 |

表中的概率等式和 log 合法性在相同的 j≥N_pos(1) 尾段成立；CP 的全 j 确定性合法性没有被误用成全 j 概率正性。

对源文的每个固定 0<α<1，取 CP2 在 c=1 给出的原 nearest-tie-up 子列

\[
\sigma_\alpha(j)=
\operatorname{Nat.floor}((j+K_{1,\alpha}+\alpha)^3+1/2).
\]

这里 j+K 的实数转换按 CP2 解释，K_{1,α} 是 CP2 的固定见证。该式就是下节通式在 c=1 的实例，半整数并列向上。其同一子列有 δ→1−α、E→q_1(1−α)、F→exp(q_1(1−α))，从第7节得到

\[
\log Q_1(\sigma_\alpha(j))\to\pi^2(1-\alpha)/4,\qquad
Q_1(\sigma_\alpha(j))=QK_1(\sigma_\alpha(j))
\to\exp(\pi^2(1-\alpha)/4).
\]

概率相等仅作最终相等解释。本节没有使用 O(k^{-2}) 或 O(k^{-5}) 的精细根展开。

## 9. 一般固定 c 的全部 CP2/CP3 同相位实际极限

一次选择 C-CP2 提供的一组固定见证 K_a(c)、K_b(c)（K_b≥1）和各固定 α 的 K_{c,α}；不随 ε 或概率结果重选。完全沿用其定义

\[
t_c(k)=((k:\mathbb R)/c)^3,\quad
a_c(k)=\operatorname{Nat.ceil}(t_c(k)),\quad
b_c(k)=\operatorname{Nat.ceil}(t_c(k))-1,
\]
\[
\sigma_a(j)=a_c(j+K_a),\qquad
\sigma_b(j)=b_c(j+K_b).
\]

CP2 的上采样误差是 0≤(a_c(k):ℝ)−t_c(k)<1，全部 k 成立。下采样仅在 k≥1 使用：此时 t_c(k)>0，ceil(t_c(k)) 是不小于这个正数的自然数，故至少为1。因此 b_c(k) 的自然数减法无截断损失，(b_c(k):ℝ)=(a_c(k):ℝ)−1，并有 CP2 的 −1≤(b_c(k):ℝ)−t_c(k)<0。σ_b 的每个输入 k=j+K_b≥1，满足该前置条件。k=0 的 b_c(0)=0 不被错误解释为 t_c(0) 下方的点。

CP2 保证这两条已固定截尾的 σ 都 StrictMono，全部 j 是正时间且处于合法弱胞元；这不要求未经截尾的 a_c、b_c 处处严格递增。它给原 σ_a 的 δ→1、E→q、F→exp(q)，及原 σ_b 的 δ→0、E→0、F→1。

再固定 0<α<1，使用且只使用 CP2 的

\[
t_{c,\alpha}(k)=(((k:\mathbb R)+\alpha)/c)^3,\quad
v_{c,\alpha}(k)=\operatorname{Nat.floor}(t_{c,\alpha}(k)+1/2),
\quad \sigma_\alpha(j)=v_{c,\alpha}(j+K_{c,\alpha}).
\]

这是确定的半整数向上舍入，未用任意 nearest 选择。CP2 给全部 k 的 |(v:ℝ)−t|≤1/2，以及这个固定截尾 σ_α 的 StrictMono、全部正时间及弱胞元合法性，和 δ→1−α、E→q(1−α)、F→exp(q(1−α))。这些是固定 CP 输出，本稿不另证明或更换其构造。

第7节逐条应用到以上精确 σ，统一给出：

| 原 CP2 子列 | δ 极限 | E 与 log Q 的共同极限 | F、Q、QK 的共同极限 |
| --- | ---: | ---: | ---: |
| σ_a | 1 | q | exp(q) |
| σ_b | 0 | 0 | 1 |
| σ_α | 1−α | q(1−α) | exp(q(1−α)) |

每一行的 Q=QK 都是最终精确相等，每个 log 都在同一实际正性尾段合法。需要额外概率截尾时，只对该行的全部量一起使用第7节的同一个 T，原 CP2 见证本身不改，也不另选概率子列。

最后固定任意 d∈[0,1]。严格按 C-CP3 的同一实现：

- d=1 取上述 σ_a；
- d=0 取上述 σ_b；
- 0<d<1 时固定 α=1−d，有 0<α<1，取上述 σ_α。

由 CP3 及本节同相位消费，这条自然数 StrictMono、全部弱胞元合法的 σ_d 同时满足

\[
\delta_c(\sigma_d(j))\to d,\quad
E_c(\sigma_d(j))\to qd,\quad
F_c(\sigma_d(j))\to\exp(qd),
\]
\[
\log Q_c(\sigma_d(j))\to qd,\quad
Q_c(\sigma_d(j))=QK_c(\sigma_d(j))\to\exp(qd).
\]

同一 j≥N_pos(c) 保证概率及 log 合法；若用 \(\widehat\sigma_d\)，上面五项及其实际 p/K/x/b_U 同时移位。一般 c 不需要存在任何正整数时间恰有整数高度，δ=0 仅作为极限出现。

## 10. 完整实际 Cluster 的两个方向

沿用 A §8/C §2 的定义：

\[
\operatorname{Cluster}(z)=
\{L\in\mathbb R:\exists\sigma:\mathbb N\to\mathbb N,\
 \operatorname{StrictMono}(\sigma),\
 z(\sigma(j))\to L\}.
\]

先观察，任意 StrictMono τ 满足 τ(j)≥j，第5节故给 j≥N_pos 时 Q_{τ(j)}=QK_{τ(j)}。两者沿每个相同 τ 的实极限存在性及极限值相同；所以 Cluster(Q)=Cluster(QK)。这一步不预设极限正性。

包含方向：设任意 StrictMono τ，并设 Q_{τ(j)}→L∈ℝ。由第6、7节，

\[
Q_{\tau(j)}-F_{\tau(j)}\to0,\qquad
1<F_{\tau(j)}\le B_c=\exp(q)
\]

在同一最终尾段成立。对任意 ε>0，最终有

\[
1-\varepsilon<Q_{\tau(j)}\le B_c+\varepsilon.
\]

极限给 1−ε≤L≤B_c+ε，令 ε 任意小，得 1≤L≤B_c。具体说若 L<1，可取 ε=(1−L)/3，结合 Q→L 与误差<ε 将同时得到 Q<1−2ε 和 Q>1−ε，矛盾；若 L>B_c，取 ε=(L−B_c)/3 则同时得到 Q>B_c+2ε 与 Q≤B_c+ε，矛盾。因此这个论证覆盖任意有限概率极限，不仅覆盖 CP 构造的子列，也没有在尚未知 L>0 前先对 L 取 log。

反向覆盖：固定任意 L∈[1,B_c]。由于 L≥1>0，普通 log L 合法；由 log 在正数上的单调性，

\[
0=\log1\le\log L\le\log(\exp q)=q.
\]

q>0，故 d=(log L)/q∈[0,1]。L=1 时 d=0，L=B_c 时 d=1；严格内部时 0<d<1，α=1−d∈(0,1)。第9节正是 CP3 对这个 d 的原 σ_d，不是从概率极限反选的新 σ。该 σ_d 有全部自然数/StrictMono/弱胞元性质，且最终全部概率及其 log 正性合法，同时给

\[
Q_c(\sigma_d(j))=QK_c(\sigma_d(j))
\longrightarrow \exp(qd)=\exp(\log L)=L.
\]

端点及每个内部值均被同一 CP 相位实现。若要求所有 j 的概率正性，用第7节固定 T 同步截尾，仍由完全相同的 CP 构造及各量的同一索引给出。于是两方向合成

\[
\boxed{\operatorname{Cluster}(Q_c)=
\operatorname{Cluster}(QK_c)=[1,\exp(q_c)].}
\]

## 11. 两个实际端点排除整列极限

由 q_c>0 和 exp 的严格递增性，exp(q_c)>exp(0)=1。第9节的 CP2 同一自然数严格子列 σ_a、σ_b 已经分别给出实际 Q 和 QK 的两个不同极限 exp(q_c)、1，且概率正性在各自同一个共同尾段合法。

若 Q_c 全自然时间列有有限实极限 L，严格递增子列的余终性使以上两个子列都趋向 L；实极限唯一性将给 L=exp(q_c)=1，矛盾。对 QK_c 用其相同两个实际子列可得同一矛盾（也可用其与 Q_c 的整列最终相等）。故两条全列都没有单一有限实极限。c=1 时区间和端点恰为 [1,exp(π²/4)]；所有固定 c>0 时恰为 A/D 指定的 [1,exp(π²/(4c³))]。

## 12. 依赖账、承重关系与门

| 分类 | 项目 | 用途与边界 |
| --- | --- | --- |
| FIXED_INPUT | A 第3–8节的全部定义、量词与目标 | 不增删目标；实际 law/event/b_U 不变 |
| FIXED_INPUT | B §3 的实际 p/K/b_U 和弱前缀事件语义 | 第2、4节的对象识别；不是自由概率函数 |
| FIXED_INPUT | B §4 的 S4-DOM、最终实际正性、S4-MAIN；B §7 S4-EVENTUAL | 第5节验证原三尺度及全 j 胞元，消费指定输出并按同一移位返回 |
| FIXED_INPUT | C-CP0 | 第3节最终胞元/发散尺度/弱相位界；第6节固定 c 的 F 界 |
| FIXED_INPUT | C-CP1 | 第8节精确立方与合法自然数减一子列 |
| FIXED_INPUT | C-CP2、CP3 | 第9、10节原舍入见证、StrictMono、同相位五量和区间全部实现 |
| FIXED_INPUT | D、E 的原实际语义 | 只用于对齐原目标、空路径、弱边界、固定 U；不用强 Brownian O 率 |
| PROVED_HERE | 正时间 sqrt/rpow/立方/第三尺度桥 | 第3节；全部正底数和除法条件已核验 |
| PROVED_HERE | Rademacher 坐标共同满测集、V_N=√N a.e.、原自归一化事件概率=p | 第4节；有限产品测度、可测事件与零测对称差均展开 |
| PROVED_HERE | 实际 S4 的合法实例与原索引返回 | 第5节；固定 J 和 N_pos，不修订上游 all-j 条件 |
| PROVED_HERE | log Q−E→0、Q/F→1、Q−F→0 及 QK 同结论 | 第5、6节；误差显式绑定实际概率，F 界从 δ 推出 |
| PROVED_HERE | 原 CP 同 σ 的全部实际端点、内部相位、所有 d | 第7–9节；共同概率正性截尾同步所有量 |
| PROVED_HERE | Cluster 的任意子列包含、每点覆盖、实际两端点及全列无有限实极限 | 第10、11节；不只证明纯 CP 结论或对数主率 |
| OPEN | B 的上游实际 U1/S2/actualS3/DA1/DA2 的全部认证门 | 本稿只经 B 消费，不打开、证明或认证其文件 |
| OPEN | root 实际 B/U、可测事件概率、首项 tail 的公开正式接口 | 仍 pending，未另设对象或添加强尾率 |
| OPEN | C 的形式认证；本稿新鲜独立数学审查与正式实现 | 本稿未运行 Lean/lake/#check，FORMAL_STATUS=HOLD |
| OPEN | 完整原 Spectrum、一般分布/均匀窗口 OQ4 根 | 保持 OPEN，本相对结论不关闭它们 |

原目标是 D 的临界真实弱事件倍率与完整相位区间。已消除的缺边是“固定实际 S4 的合法原时间消费 + 固定 CP 相位”到“同一真实概率倍率的 S5”。直接消费者是第8–11节的实际立方端点、一般 c 舍入相位、每个区间倍率值及全列不收敛；并非另起一个自由相位定理。

相对/绝对误差只是透明便利消费输出。新原始叶增量0、原始分母增量0。不纳入精细根 O(k^{-2})/O(k^{-5})、strongBrownianRate、strict、其他 cosets、变化的 c、一般分布、uniform-x OQ4 或根闭合。本文的唯一完成状态为 PROVED_RELATIVE_FIXED_ACTUAL_S4_AND_CP；等待另一个新鲜上下文对本匿名稿作独立数学审查后再决定后续门。
