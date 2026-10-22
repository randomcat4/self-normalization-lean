# S2 有限身份及双尺度汇总的匿名数学证明

STATUS: PROVED（相对于固定的实际 Pair、Scalar SCA0 与 U1 接口）。
UPSTREAM_U1_FORMAL_STATUS: PENDING。
LEAN_STATUS: NOT_RUN；本稿不是 Lean 证明或形式认证。

本文证明 frozen-rademacher-s2-assembly-v1.md 的全部 F0/T0/F1/Q1，前提、对象、量词及时间阈值均按冻结 v1。固定 U1 的形式认证仍待完成；下述相对数学证明既不证明 U1，也不以自由函数或新公理替代 U1。Pair、Scalar 的给定调度身份不作为数学论证。

## 0. 允许接口、一次性常数及证明地位

下文缩写 Pair = Shao.OQ4.RademacherSpectralPairing，Scalar = Shao.OQ4.RademacherScalarBounds。所有使用的项目声明均来自获准的 canonical-declarations 公开完整类型或透明定义；没有使用其证明体。S1 仅使用公开 cotangent 的透明定义。一般实分析中的三角恒等式、求导法则、实数中值定理以及正自变量的指数、对数法则为基础工具；需要的新估计在本文证明。

在任取任何 m、h、n 或任何序列之前，**一次性**从固定 U1 取一个见证 C_U>0，使

\[
\begin{split}
&\forall m\in\mathbb N,\quad 1\le m\ \Longrightarrow\\
&\forall h\in\mathbb R,\quad m\le h<m+1\ \Longrightarrow\\
&\forall n\in\mathbb N,\quad ((m:\mathbb R)+1)^2\le(n:\mathbb R)\ \Longrightarrow\\
&\quad |\operatorname{Pair.remainder}(m,n)|
 \le C_U\exp\!\left(-\frac{\pi^2(n:\mathbb R)}{((m:\mathbb R)+1)^2}\right).
\end{split}\tag{U}
\]

这里的 remainder 就是第2节核对的实际透明有限表达式，绝非任意 R 或任意过程的误差。C_U 不再重新选择。F0、T0 不需要 (U)；F1、Q1 消费这一个固定接口及其同一个见证。因此 PROVED 的准确含义是“相对于固定实际 U1 的数学汇总已证明”，不是“实际 U1 已形式认证”。

公开 Pair 类型核验给出的相关接口，经删除显示层面的实例参数后是：

- closedStrip_probability_eq_killedMass：对全部 m≥1、m≤h<m+1、n:ℕ，实际 Measure.pi 产品概率的 Measure.real(closedStrip n h) 等于 killedMass law law_isProbabilityMeasure h n 0。
- closedStrip_probability_normalized：在完全相同的域（n 没有正时间前提），该实际概率等于 amplitude m * (rho m)^n * (1 + epsilon m n * (Real.tan(π/(4*((m:ℝ)+1))))² + remainder m n)。
- closedStrip_probability_zero：在同一 m,h 域，零时间实际概率为1。
- killedMass_normalized：同一域、所有 n 的 killedMass 有相同归一化右侧；它与前三条相容，本文可由概率桥取得同一结论。

上述类型中没有隐藏的 p>0、n≥1、奇偶或大 m 假设。Scalar.SCA0 的唯一参数前提是1≤m；其完整类型提供 H≥2、H>0、H²>0、H⁴>0、0<u≤π/8<π/2、0<z≤π/4<π/2、sin u>0、cos u>0、cos z>0、a>0、0<rho<1、πa/4>0。本文只消费 SCA0，不消费 SCA1/SCA2 或任何私有正切/Taylor估计。

## 1. 先作边界攻击

1. **零时间中心项。** 实际 zeroMode 的透明值是
   \[
   Z_m(n)=\begin{cases}((-1)^{m/2}/H_m)\,0^n,&\operatorname{Even}(m),\\0,&\text{否则}.
   \end{cases}
   \]
   自然数幂0^0=1，所以偶 m 的 Z_m(0)=(-1)^{m/2}/H_m 非零。任何把全部 n 的中心项删去的路线立即失效。本文始终保留 Z/B，只有证出1≤n后才允许把它算成0。
2. **m=1。** 下半索引只有0，删去0后和为空；1不是偶数，故 R_1(n)=0 对全部 n 成立。零时间主对也确实恢复1：u=π/8 时
   \[
   a_1(1-q_1)=\tfrac12(\cot u-\tan u)
   =\cot(2u)=\cot(\pi/4)=1.
   \]
3. **m=2。** 下半索引仍只有0，Z_2(n)=-(1/3)0^n。因此 R_2(n)=0 只在 n≥1 成立，而
   \[
   Z_2(0)=-\tfrac13,\qquad R_2(0)=-\frac1{3a_2}\ne0.
   \]
   此时 u=π/12，a_2(1+q_2)=(1/3)(cot u+tan u)=2/(3sin(2u))=4/3；加中心项-1/3才恢复1。故不能把正时间的空尾和特化误用到零时间。
4. **奇偶。** epsilon 的实际指数是 n+m。其符号可能随 m 或 n 改变；只有绝对值恒为1。下面保留 epsilon*q 的精确符号，不把它并入 R。
5. **胞元及序列有限前缀。** h=m 是允许的弱端点，h=m+1不在域内。所有公开概率身份恰使用这同一个半开胞元。序列可能在若干早期点有 n_k=0；下面全 k 身份允许它，最终正时间另由 t_k→∞推出。

这些攻击没有给出冻结命题的反例，但排除了删中心项、删小 m、固定奇偶、或预先加正时间的简化路线。

## 2. 实际对象与全部定义桥

现在任取 m:ℕ、1≤m，h:ℝ、(m:ℝ)≤h<(m:ℝ)+1，n:ℕ。以后没有未写出的有限参数限制。记

\[
H=(m:\mathbb R)+1,\quad N=(n:\mathbb R),\quad t=N/H^2,
\quad u=\operatorname{Scalar.u}(m),\quad z=\operatorname{Scalar.z}(m).
\]

Scalar 的透明定义逐字给出

\[
\operatorname{Scalar.H}(m)=H,\quad
u=\frac\pi{4H},\quad z=\frac\pi{2H},\quad
\operatorname{Scalar.a}(m)=\frac1H\frac{\cos u}{\sin u},\quad
\operatorname{Scalar.rho}(m)=\cos z.\tag{2.1}
\]

Pair.alpha 和 Pair.beta 的完整透明值为

\[
\alpha_{m,\ell}=\frac{((2\ell+1:\mathbb N):\mathbb R)\pi}{4H},
\qquad
\beta_{m,\ell}=\frac{((2\ell+1:\mathbb N):\mathbb R)\pi}{2H}.
\]

令 ℓ=0，自然数2*0+1=1，转为实数仍为1，故直接计算出

\[
\operatorname{Pair.alpha}(m,0)=u,\qquad
\operatorname{Pair.beta}(m,0)=z.\tag{2.2}
\]

S1 获准的第341–365行定义给出 cotangent x=Real.cos x/Real.sin x。把它代入 Pair.amplitude 的透明值，再代入(2.1)，得到定义桥

\[
\begin{split}
a_m:=\operatorname{Pair.amplitude}(m)
 &=\frac1H\operatorname{S1.cotangent}\!\left(\frac\pi{4H}\right)
 =\frac1H\frac{\cos u}{\sin u}
 =\operatorname{Scalar.a}(m),\\
\rho_m:=\operatorname{Pair.rho}(m)
 &=\cos\!\left(\frac\pi{2H}\right)
 =\cos z=\operatorname{Scalar.rho}(m).
\end{split}\tag{2.3}
\]

这里没有取用额外等值前提，也没有把同名参数认作未经证明相同的对象。由 Scalar.SCA0 和(2.1)–(2.3)，H≥2、H²>0、sin u>0、cos u>0、a_m>0及0<rho_m<1。因此 cotangent u>0。对每个 n≥0，自然数幂 rho_m^n>0（n=0时等于1），故

\[
B_{mn}:=a_m\rho_m^n>0.\tag{2.4}
\]

这个结论也吻合 Pair.normalizer_pos 的已核验完整类型。

其余实际定义逐字为

\[
\varepsilon_{mn}:=\operatorname{Pair.epsilon}(m,n)=(-1:\mathbb R)^{n+m},
\quad q_m=(\operatorname{Real.tan}u)^2,
\quad L_m=\{\ell\in\{0,\ldots,m\}:2\ell<m\},
\]

\[
\begin{split}
\operatorname{normalizedTerm}(m,n,\ell)
 &=(-1)^\ell\,
 \frac{\operatorname{cotangent}(\alpha_{m,\ell})+
        \varepsilon_{mn}\operatorname{Real.tan}(\alpha_{m,\ell})}
      {\operatorname{cotangent}(u)}
 \left(\frac{\cos\beta_{m,\ell}}{\rho_m}\right)^n,\\
R_{mn}:=\operatorname{Pair.remainder}(m,n)
 &=\sum_{\ell\in L_m\setminus\{0\}}
       \operatorname{normalizedTerm}(m,n,\ell)
   +\frac{Z_m(n)}{a_m\rho_m^n}.
\end{split}\tag{2.5}
\]

L_m 是 Pair.lowerModes m，集合删除是实际 Finset.erase 0；Z 是第1节的 Pair.zeroMode。若 ℓ∈L_m，则 r=2ℓ+1为正整数且 r≤m<H，因此0<alpha<π/4、0<beta<π/2，sin alpha和cos alpha都为正。由(2.4)和cotangent u>0，(2.5)中实际使用的除数全部非零；当 n=0时，Z 的0^0仍按1计算。所有这些都是固定范围的输出，不是新输入。R 完全由(2.5)决定，后面每次写 R 都指这个函数。

固定 ν_R=RademacherCosine.law及其 law_isProbabilityMeasure，令

\[
P_n=\operatorname{Measure.pi}(\lambda\_:\operatorname{Fin}n,\nu_R),\quad
p(n,h)=P_n.\operatorname{real}(\operatorname{closedStrip}\ n\ h),
\quad K(n,h)=\operatorname{killedMass}(\nu_R,\operatorname{law\_isProbabilityMeasure},h,n,0).
\]

这就是公开 Pair 完整类型中出现的同一组项：路径类型为Fin n→ℝ，事件是Shao.closedStrip n h，起点是实数0，概率是产品测度的 Measure.real；没有用谱和重新定义 p。定义 D(m,n,h)=p(n,h)/B_mn。

## 3. F0：全部自然时间的实际身份

对第2节任取的同一 m,h,n，应用已核验的 Pair.closedStrip_probability_eq_killedMass，其三个域前提分别正是1≤m、m≤h及h<m+1，得

\[
p(n,h)=K(n,h).\tag{3.1}
\]

应用 Pair.closedStrip_probability_normalized，利用(2.1)中的u=π/(4H)以及实际定义(2.3)、(2.5)，得

\[
p(n,h)=B_{mn}\bigl(1+\varepsilon_{mn}q_m+R_{mn}\bigr).\tag{3.2}
\]

这次调用允许 n=0；没有套用正时间的余谱化简。由(2.4)，B≠0，所以在实数域中把(3.2)除以B，乘除消去实际非零因子，得到

\[
D(m,n,h)=\frac{p(n,h)}B=\frac{K(n,h)}B
       =1+\varepsilon_{mn}q_m+R_{mn}.\tag{3.3}
\]

同一次消去也给出全时间 p=B D。a>0、0<rho<1、B>0已经在(2.3)–(2.4)证明；所以F0所列全部结论成立，且没有先假定p严格为正。

n=0时，公开 Pair.closedStrip_probability_zero 在同一 m,h 前提下给 p(0,h)=1；(3.1)给K(0,h)=1。此时B_m0=a_m，(3.3)仍有全部中心项，并特别给

\[
D(m,0,h)=1/a_m,
\qquad R_{m0}=1/a_m-1-(-1)^m q_m.
\]

第1节 m=1、m=2 的计算就是(2.5)的直接代入；它们还分别与公开 remainder_one（全部n）、remainder_two_positive_time（1≤n）、remainder_two_zero（-1/(3*amplitude 2)）及 zeroMode_two_zero 的完整类型一致。因而全时间身份同时覆盖空路径、m=1、m=2及任意奇偶。

## 4. T0：在内部证明实际正切平方界

由Scalar.SCA0，0<u≤π/8。对任意实数 x∈[0,u]，有0≤x≤π/8<π/2，故cos x>0；又0≤2x≤π/4<π/2，故cos(2x)≥0。倍角恒等式给

\[
\cos^2x=\frac{1+\cos(2x)}2\ge\frac12.\tag{4.1}
\]

在该闭区间，实际 Real.tan x=sin x/cos x 连续且分母不消失；在内部利用商法则及sin²x+cos²x=1，得

\[
(\operatorname{Real.tan})'(x)
=\frac{\cos^2x+\sin^2x}{\cos^2x}
=\frac1{\cos^2x}\le2.\tag{4.2}
\]

因为u>0，对Real.tan在[0,u]使用实数中值定理，存在c∈(0,u)，使

\[
\tan u-\tan0=u/\cos^2c\le2u.
\]

tan0=0；sin u>0、cos u>0还给tan u>0。因此两个边都非负，可以平方，利用u的实际值和H>0，得到

\[
0\le q_m=(\tan u)^2\le(2u)^2
=4\left(\frac\pi{4H}\right)^2
=\frac{\pi^2}{4H^2}.\tag{4.3}
\]

这是本稿内部从实际三角函数推出的界，常数π²/4为结论侧的一个明确非最优值；没有使用Scalar私有正切/Taylor输出、自由C_tan或充分大m条件。

另一方面，对全部自然数n，绝对值与自然数幂相容，故

\[
|\varepsilon_{mn}|=|(-1)^{n+m}|=|-1|^{n+m}=1^{n+m}=1.\tag{4.4}
\]

此式含n=0，且不作任何奇偶限制。F0与T0至此均不依赖U1。

## 5. F1：原阈值下同一个绝对常数

仍对任意第2节有限参数，仅在本节加入冻结原前提H²≤N。由H≥2，H²≥4，所以N≥4>0；如果n=0则N=0矛盾，因n是自然数故1≤n。于是Z_m(n)=0可以由实际0^n计算，(2.5)仍是同一个R（不是另定义的正时间函数）。F1前提保持恰好H²≤N；没有另加n或m阈值。

在这个原阈值下，(U)适用于同一m,h,n，给

\[
|R_{mn}|\le C_U\exp(-\pi^2N/H^2).\tag{5.1}
\]

由(3.3)在实数域中精确消去1和epsilon*q，

\[
D-1-\varepsilon_{mn}q_m=R_{mn};
\quad |D-1-\varepsilon_{mn}q_m|
\le C_U\exp(-\pi^2N/H^2).\tag{5.2}
\]

又由三角不等式、(4.3)–(4.4)，

\[
\begin{split}
|D-1|&=|\varepsilon_{mn}q_m+R_{mn}|\\
&\le|\varepsilon_{mn}|\,|q_m|+|R_{mn}|\\
&=q_m+|R_{mn}|\\
&\le\frac{\pi^2}{4H^2}+C_U\exp(-\pi^2N/H^2).
\end{split}\tag{5.3}
\]

(5.1)–(5.3)同时使用第0节预先固定的唯一C_U，适用于全部m≥1、全部弱胞元h及满足原阈值的全部自然n，包括m=1、m=2和所有奇偶。K/B由(3.3)就是D，故直接使用同一个结论与常数；没有新的过程或新误差项。

## 6. Q1：只用原双尺度的任意序列

现在才任取序列m_,n_:ℕ→ℕ及h_:ℕ→ℝ，并假设对每个k有1≤m_k和m_k≤h_k<m_k+1。定义H_k、N_k、t_k、a_k、rho_k、B_k、p_k、K_k、D_k均为第2节同一实际函数在该点的取值。只额外假设H_k→+∞及t_k=N_k/H_k²→+∞，其含义是对每个实阈值各有一个自然起点，其后全都超过或等于该阈值。C_U已在任取这些序列之前固定。

### 6.1 全k身份与最终时间域

逐k应用F0，得全部k的B_k>0、p_k=K_k及(3.2)–(3.3)。没有删除任何早期n_k=0或其中的中心项。这证明Q1(1)。

对t_k→∞取实阈值1，取一个固定自然数K_time，使k≥K_time时t_k≥1。H_k²>0，所以把1≤N_k/H_k²乘以这个正数，得到

\[
H_k^2\le N_k\qquad(k\ge K_{\rm time}).\tag{6.1}
\]

再由H_k≥2得到N_k≥4；自然数n_k如果为0则其强制转换N_k为0，矛盾。因此全部该尾段1≤n_k。这证明Q1(2)，且F1在该尾段使用同一个C_U。

### 6.2 两种实际误差都趋零

置A=π²/4>0。先给出指数控制的内部证明：对s≥0，函数g(s)=exp(s)-1-s满足g(0)=0、g'(s)=exp(s)-1≥0（exp递增且exp0=1）；中值定理给g(s)≥0。因此exp(s)≥1+s>0，并由exp(-s)=1/exp(s)得

\[
0<e^{-s}\le\frac1{1+s}\quad(s\ge0).
\]

若t>0，则s=π²t>0，进一步有

\[
0<C_Ue^{-\pi^2t}\le\frac{C_U}{1+\pi^2t}
\le\frac{C_U}{\pi^2t}.\tag{6.2}
\]

任给η>0，设两个实阈值

\[
L_H(\eta)=\max\{2,4A/\eta\},\qquad
L_t(\eta)=\max\{1,4C_U/(\pi^2\eta)\}.
\]

H_k→∞给出起点J_H(η)，其后H_k≥L_H(η)。于是H_k≥2，H_k²≥H_k≥4A/η>0，故

\[
0\le A/H_k^2\le\eta/4.\tag{6.3}
\]

t_k→∞给出起点J_t(η)，其后t_k≥L_t(η)≥1>0且π²t_k≥4C_U/η；(6.2)给

\[
0<C_Ue^{-\pi^2t_k}\le\eta/4.\tag{6.4}
\]

这些起点确实只来自原双尺度前提；(6.3)–(6.4)不是额外收敛输入。例如把η换成任意给定容差，右边η/4严格小于该容差，即分别证明A/H_k²→0和C_U exp(-π²t_k)→0。(4.3)同时给0≤q_{m_k}≤A/H_k²，(U)在(6.1)尾段给|R_{m_kn_k}|≤C_U exp(-π²t_k)，所以q_{m_k}→0且R_{m_kn_k}→0也是推论。

### 6.3 归一化概率趋一

给定任意η>0，取固定自然数

\[
J_D(\eta)=\max\{K_{\rm time},J_H(\eta),J_t(\eta)\}.
\]

对所有k≥J_D(η)，(6.1)允许使用F1；再用(6.3)–(6.4)，得

\[
|D_k-1|\le A/H_k^2+C_Ue^{-\pi^2t_k}
\le\eta/2<\eta.\tag{6.5}
\]

这是D_k→1的逐容差证明。全k已有D_k=K_k/B_k，所以K_k/B_k→1。这里从来没有把实际概率p_k本身的极限写成1。这证明Q1(3)。

### 6.4 概率及归一化比值的最终正性

令K_pos=J_D(1/2)（若需统一时间尾段，它已包含K_time）。当k≥K_pos时，由(6.5)有|D_k-1|<1/2，故

\[
\tfrac12<D_k<\tfrac32.
\]

由全k的B_k>0及p_k=B_kD_k，得到p_k>0；由全k的p_k=K_k得到K_k>0。因此同一固定尾段D_k、p_k、K_k都严格为正。这证明Q1(4)；没有为了取对数预先假定正生存。

### 6.5 相对对数的收敛、精确身份及合法性

先证明所需局部对数界。若x∈(1/2,3/2)且x≠1，对log在端点x、1之间的闭区间使用中值定理。该区间完全位于(1/2,3/2)，log处处可微；存在其间的c>1/2，使

\[
\log x-\log1=(x-1)/c,
\quad |\log x|\le2|x-1|.\tag{6.6}
\]

x=1时同一不等式两边都为0。任给η>0，(6.5)可给出一个尾段，使|D_k-1|<min(1/2,η/2)；再与K_pos取最大值。这个尾段上(6.6)有定义，并给|log D_k|≤2|D_k-1|<η，故

\[
\log D_k\longrightarrow0.\tag{6.7}
\]

现在固定任意k≥K_pos。a_k>0、rho_k>0在全k成立，rho_k^{n_k}>0及B_k>0亦然；又刚证明D_k>0、p_k>0、K_k>0。因此以下每一步真实对数的乘法法则都在正自变量上使用：

\[
\begin{split}
\log p_k
 &=\log(B_kD_k)=\log B_k+\log D_k,\\
\log B_k
 &=\log(a_k\rho_k^{n_k})=\log a_k+\log(\rho_k^{n_k})
 =\log a_k+N_k\log\rho_k.
\end{split}\tag{6.8}
\]

最后一个等式使用自然数幂的实际n_k：n=0时log(rho^0)=log1=0；若log(rho^n)=(n:ℝ)log rho，则rho^{n+1}=rho^n*rho且两个因子为正，乘法法则给log(rho^{n+1})=((n:ℝ)+1)log rho。这归纳证明全部自然数指数的公式，并且N_k正是n_k的实数强制转换。

把(6.8)两式代入并在实数中减去前两项，得到所要求的同一正性尾段上的**精确等式**

\[
\boxed{\ \log p_k-\log a_k-N_k\log\rho_k=\log D_k\ }.\tag{6.9}
\]

由(6.7)和最终相等，左侧趋零。p_k=K_k使log K_k=log p_k，故K的同一表达式在同一尾段等于log D_k并趋零。有限前缀无论n_k是否为0都不影响收敛；若采用Lean的总函数Real.log，则(6.7)–(6.9)仍只在已证的正性尾段使用其真实对数规则，没有以总函数性代替概率正性。这证明Q1(5)。

## 7. 量词、依赖及未执行事项

证明中的C_U是第0节从固定实际U1取得的同一个正绝对常数，先于全部有限参数和全部序列。K_time、K_pos及各容差起点可以依赖序列或容差；没有重新选择C_U。所有m≥1、所有弱胞元h、全部自然时间及两种奇偶均已覆盖；早期n=0的身份和偶m中心项保留，F1的时间前提恰为H²≤N。

新推导的依赖账：

| 项目 | 地位与准确消费 |
| --- | --- |
| p=K、实际全时间归一化、零时间概率 | 固定Pair公开完整类型；本文逐前提核对 |
| alpha0/u、beta0/z、Pair/Scalar的a与rho、实际R显示式 | PROVED_HERE，由获准透明定义展开 |
| H/角度/标量正性 | 固定Scalar.SCA0的公开完整类型 |
| 实际tan²≤π²/(4H²)、abs epsilon=1 | PROVED_HERE，第4节 |
| 同一R在原阈值的绝对界 | 固定U1；其形式认证PENDING，不是本稿新证结果 |
| F0、F1、两种误差趋零、D→1、最终正性与精确相对log | PROVED_HERE，F1/Q1相对于固定U1 |
| 中值定理、基本求导、三角恒等式及正实数exp/log法则 | KNOWN一般实分析工具，不是新增项目假设 |

没有加入单调性、n/h³条件、奇偶匹配、Brownian、DA1/DA2、strict事件、自由实吸收位置或其他分布。本文没有读任何别人的数学证明/来源审查/作者票据/私有Source或proof，没有执行网络、出处搜索、服务器、Lean、lake、#check、Git、cache或子代理。所有shell调用的workdir均为C:/game/shao lean。没有运行或声称运行任何Lean声明；LEAN_STATUS=NOT_RUN，不能由本文关闭U1、S2形式状态或任何根状态。

精确输入SHA256、字节数与曝光范围见同目录input-exposure.json。除了公开声明账的一次标题索引（包括其中私有声明的名称元数据），语义阅读仅限所列公开类型和透明定义；没有读入这些私有项的类型或证明体。S1账只向本上下文显示341–365行，完整字节仅用于哈希。本文是数学作者产物，尚不代替全新独立验证或形式终审。
