# 零起点显式有限 S1 与低阈值分支的数学证明

STATUS: PROOF_READY
EVIDENCE: MATH_ONLY
SCOPE: 冻结接口 v1 的 C1–C5

冻结命题为 frozen-rademacher-finite-s1-v1.md，SHA256 e2e9240f739e737c83195f177dcd54707c023151cf3e4faf7f1d862e87b585fe，10956 bytes。本稿只给出 C1–C5 的数学证明。固定上游数学引理按下述原有对象和完整量词使用；这种数学引用不表示 AllModes 的 Lean 实施已经认证，也不表示本稿已经过独立数学审查或机械认证。

## 1. 对象与所用的固定数学接口

记真实概率律为

\[
\nu_R=\mathrm{RademacherCosine.law}
=\tfrac12\delta_1+\tfrac12\delta_{-1}.
\]

这里两项测度的标量是扩展非负实数中的 \(1/2\)，概率性使用该 law 已有的内部实例。以下所有实值积分和有限谱系数均在 \(\mathbb R\) 中。

对 \(n\in\mathbb N\)，令

\[
\begin{aligned}
\mathrm{Path}\ n&=\mathrm{Fin}\ n\to\mathbb R,\\
P_n&=\mathrm{Measure.pi}(\lambda i:\mathrm{Fin}\ n,\nu_R),\\
S_k(a)&=\sum_{\substack{i:\mathrm{Fin}\ n\\i.\mathrm{val}<k}}a(i),\\
A_n(h)&=\{a:\mathrm{Path}\ n:\ \forall k\le n,\ |S_k(a)|\le h\},\\
p(n,h)&=P_n.\mathrm{real}(A_n(h)).
\end{aligned}
\]

这些分别是现有 Path、prefixSum、closedStrip 和真实乘积路径概率。由于 \(S_0(a)=0\)，在 \(h\ge0\) 时，包含 \(k=0\) 的 \(A_n(h)\) 与对 \(1\le k\le n\) 要求弱生存相同。零步由这个集合直接解释，不给空集最大值另加约定。

对固定 \(h\)，简记

\[
K_h=\mathrm{killedKernel}\ \nu_R\ h,\qquad
K_{h,n}=\mathrm{killedIterKernel}\ \nu_R\ h\ n,
\]
\[
T_{h,n}f(z)=\mathrm{killedAction}\ \nu_R\ h\ n\ f\ z
=\int f(w)\,K_{h,n}(z,dw),\qquad
M_{h,n}(z)=T_{h,n}\mathbf1(z).
\]

这些是真实杀死核及其现有的幂和积分作用，且 \(M_{h,n}(z)\) 就是现有 killedMass。所用的已认证基础接口如下：

1. \(K_h(z)=(\nu_R\circ(y\mapsto z+y)^{-1})|_{[-h,h]}\)，限制后不归一化。
2. \(K_{h,n}=K_h^n\)，且 \(K_{h,0}(z)=\delta_z\)。特别地 \(K_{h,1}=K_h\)。
3. 对可测有界的实函数 \(f\)，真实半群公式的方向为
   \[
   T_{h,a+b}f(z)=T_{h,a}(T_{h,b}f)(z)
   \quad(a,b\in\mathbb N).
   \tag{1}
   \]
   现有 killedAction_measurable 与 killedAction_bound 保证 \(T_{h,b}f\) 仍可测有界；例如 \(|T_{h,b}\mathbf1(z)|\le1\)。
4. killedMass_eq_real 给出
   \[
   M_{h,n}(z)=K_{h,n}(z).\mathrm{real}(\mathbb R).
   \]
   killedMass_eq_closedStrip_probability 的完整适用条件是 \(0\le h\)，在此条件下
   \[
   M_{h,n}(0)
   =(\mathrm{Measure.pi}(\lambda i:\mathrm{Fin}\ n,\nu_R)).
       \mathrm{real}(\mathrm{closedStrip}\ h)
   =p(n,h).
   \tag{2}
   \]
   等式 (2) 对所有自然时间成立。
5. RademacherCosine.killedKernel_row 对所有 \(m\in\mathbb N\)，包括 \(m=0\)，在 \(m\le h<m+1\) 时对每个整数 \(r\) 给出真实测度行
   \[
   K_h(r)=
   \begin{cases}\tfrac12\delta_{r+1},&|r+1|\le m,\\0,&|r+1|>m\end{cases}
   +
   \begin{cases}\tfrac12\delta_{r-1},&|r-1|\le m,\\0,&|r-1|>m.\end{cases}
   \tag{3}
   \]
   整数和实数间的转换与固定签名相同。该行公式没有 \(1\le m\) 的条件。

高阈值部分固定任意 \(m\in\mathbb N\)，满足 \(1\le m\)，并记

\[
H_N=m+1,\qquad H_Z=(m:\mathbb Z)+1,\qquad H=(m:\mathbb R)+1.
\]

三者是同一数值的不同类型，特别地 \(H>0\)。另记 \(N=2m+1\)，则

\[
N=2H_N-1,\qquad (N:\mathbb R)=2H-1.
\]

有限状态和指标为

\[
I_m=\{-m,-m+1,\ldots,m\}\subset\mathbb Z,\qquad
J_m=\{1,2,\ldots,N\}\subset\mathbb N.
\]

沿用固定正弦族，不引入自由特征值：

\[
\theta_j=\frac{(j:\mathbb R)\pi}{2H},\qquad
\mu_j=\cos\theta_j,\qquad
\phi_j(w)=\sin(\theta_j(w+H)),\qquad
v_j(s)=\phi_j((s:\mathbb R)),
\]
\[
q_j=\frac1H\sum_{s\in I_m}v_j(s).
\tag{4}
\]

这里 \(\theta_j=(j:\mathbb R)\mathrm{RademacherCosine.angle}(m)\)，由已认证的 angle 定义直接得到。

所用的固定上游数学引理只有同一有限族上的下列结论：

- FiniteBasis B2：对任意 \(F:\mathbb Z\to\mathbb R\) 和 \(r\in I_m\)，
  \[
  F(r)=\sum_{j\in J_m}
  \left(\frac1H\sum_{s\in I_m}F(s)v_j(s)\right)v_j(r).
  \tag{5}
  \]
- AllModes D2 的 \(F=\mathbf1\) 结论：若 \(m\le h<m+1\)、\(r\in I_m\) 且 \(n\in\mathbb N\)，则
  \[
  M_{h,n}(r)=\sum_{j\in J_m}q_j\mu_j^n v_j(r).
  \tag{6}
  \]

它们分别来自 SHA256 为 4672baa6bc550de2a97ca9adc0730b5633f71458b2c3da8b02c2318131e05a7f 的 FiniteBasis 固定接口和 dac2fd30e7c759137e14ebd64c4d7457155a201da04a7226449304d0b4abbe10 的 AllModes 固定接口。后者的全部模态幂使用同一真实核，网格接口固定于 Iteration 的 SHA256 15851002ccadaa118035107c8b9b8266dd825fdebdf36728f3ac7a97f7330b80。本证明直接使用 (6)，不把特征关系、概率关系或任意矩阵递推作为新增前提；(6) 的零模态、负模态和 \(n=0\) 均按其原量词保留。

## 2. 全部零起点值与精确指标分割：C1、C3

首先不对 \(j\) 加奇偶限制。由 \(H>0\)，对每个 \(j\in\mathbb N\) 都有

\[
v_j(0)
=\sin(\theta_j H)
=\sin\left(\frac{(j:\mathbb R)\pi}{2H}H\right)
=\sin\frac{(j:\mathbb R)\pi}{2}.
\tag{7}
\]

现在精确分割 \(J_m\)。自然数除法给出每个 \(j\in J_m\) 唯一的表示 \(j=2u+\varepsilon\)，其中 \(\varepsilon\in\{0,1\}\)。

若 \(\varepsilon=0\)，则 \(j=2u\)。由 \(1\le j\) 得 \(1\le u\)；由 \(2u\le2m+1\) 及 \(u,m\) 为整数得 \(u\le m\)。反过来，\(1\le u\le m\) 蕴含 \(1\le2u\le2m+1\)。所以全部偶数指标恰为

\[
E_m=\{2u: u\in\{1,\ldots,m\}\}.
\tag{8}
\]

若 \(\varepsilon=1\)，则 \(j=2u+1\)。上界 \(2u+1\le2m+1\) 等价于 \(u\le m\)，也就是 \(u\in\mathrm{range}(m+1)=\{0,\ldots,m\}\)。反过来，每个这样的 \(u\) 均给出 \(1\le2u+1\le2m+1\)。所以全部奇数指标恰为

\[
O_m=\{2\ell+1:\ell\in\mathrm{range}(m+1)\}.
\tag{9}
\]

(8)、(9) 互不相交，其并为全部 \(J_m\)。两个映射都是单射，因为 \(2u=2u'\) 或 \(2\ell+1=2\ell'+1\) 分别推出 \(u=u'\) 或 \(\ell=\ell'\)。对于奇数 \(j\in J_m\)，写成唯一的 \(j=2\ell+1\) 后，

\[
j-1=2\ell,\qquad (j-1)/2=\ell
\tag{10}
\]

在自然数中也成立。因此 (9) 给出的双射的逆恰是冻结命题中的自然数函数 \((j-1)/2\)，没有在非奇数或 \(j=0\) 上使用这个逆。奇数首项、末项分别是 \(\ell=0\) 时的 \(j=1\)，和 \(\ell=m\) 时的 \(j=2m+1=2H_N-1\)。

由正弦、余弦加法公式，在 \(u\in\mathbb N\) 上归纳得到

\[
\sin(u\pi)=0,\qquad \cos(u\pi)=(-1)^u.
\tag{11}
\]

归纳起点是 \(\sin0=0,\cos0=1\)；每增加一次 \(\pi\)，正弦和余弦都改变符号。这说明 (11) 覆盖全部自然指数而没有奇偶遗漏。将 (11) 代入 (7)，对 (8) 有

\[
v_{2u}(0)=\sin(u\pi)=0,
\tag{12}
\]

对 (9) 有

\[
v_{2\ell+1}(0)
=\sin(\ell\pi+\pi/2)
=\cos(\ell\pi)
=(-1:\mathbb R)^\ell.
\tag{13}
\]

(7)、(8)–(13) 证明 C1 和 C3，包括全部 \(J_m=\{1,\ldots,2H_N-1\}\) 的起点核对和足以重编号有限和的精确双射。

## 3. 奇数模态有限正弦和：C2

固定任意 \(\ell\in\mathrm{range}(m+1)\)，令 \(j=2\ell+1\)，并设

\[
\theta=\theta_j,\qquad t=\theta/2=\frac{(j:\mathbb R)\pi}{4H}.
\]

由 \(1\le j\le2H_N-1\)、\(H>0\) 及 \(\pi>0\)，得到

\[
0<t<\frac{2H\pi}{4H}=\frac\pi2.
\tag{14}
\]

因此 \(\sin t>0\)，尤其 \(\sin t\ne0\)。以下除法全部合法，\(\cot t\) 始终指实数 \(\cos t/\sin t\)。

先把整数状态和精确重编号。对 \(s\in I_m\)，整数 \(s+H_Z\) 满足

\[
1\le s+H_Z\le2m+1=N.
\]

将此正整数看成自然数 \(k\)，便得到 \(k\in\{1,\ldots,N\}\) 且 \((k:\mathbb Z)=s+H_Z\)。反过来，对 \(1\le k\le N\)，令

\[
s=(k:\mathbb Z)-H_Z.
\]

下界 \(k\ge1\) 给 \(s\ge-m\)，上界 \(k\le2m+1\) 给 \(s\le m\)。这两个构造互逆，且转换到实数后有 \((s:\mathbb R)+H=(k:\mathbb R)\)。所以

\[
\sum_{s\in I_m}v_j(s)
=\sum_{k=1}^{N}\sin(k\theta).
\tag{15}
\]

这一步将状态集的两个实际端点 \(-m,m\) 分别送到 \(1,N\)，没有把吸收点送进求和集。

对每个整数 \(k\) 的相应实数值，余弦加法公式给出

\[
2\sin(\theta/2)\sin(k\theta)
=
\cos((k-\tfrac12)\theta)
-\cos((k+\tfrac12)\theta).
\tag{16}
\]

将 (16) 对 \(k=1,\ldots,N\) 求和。第 \(k\) 项第二个余弦正好等于第 \(k+1\) 项第一个余弦，因此有限相消后只剩首末两项：

\[
2\sin t\sum_{k=1}^{N}\sin(k\theta)
=
\cos t-\cos((N+\tfrac12)\theta).
\tag{17}
\]

因为 \((N:\mathbb R)=2H-1\) 且 \(2H\theta=(j:\mathbb R)\pi\)，有

\[
(N+\tfrac12)\theta
=(2H-\tfrac12)\theta
=j\pi-t.
\tag{18}
\]

此处 \(j=2\ell+1\) 是奇数。由 (11) 得 \(\cos(j\pi)=-1\)、\(\sin(j\pi)=0\)，再由余弦差角公式得

\[
\cos(j\pi-t)
=\cos(j\pi)\cos t+\sin(j\pi)\sin t
=-\cos t.
\tag{19}
\]

结合 (17)–(19)，

\[
2\sin t\sum_{k=1}^{N}\sin(k\theta)=2\cos t.
\]

由 (14) 可以约去非零的 \(2\sin t\)，再使用 (15)，得到

\[
\boxed{\displaystyle
\sum_{s\in I_m}v_j(s)
=\frac{\cos t}{\sin t}
=\cot\frac{(j:\mathbb R)\pi}{4H}.}
\tag{20}
\]

按 (4) 的同一计数和定义乘以 \(1/H\)，得到

\[
\boxed{\displaystyle
q_j=\frac1H\cot\frac{(j:\mathbb R)\pi}{4H}.}
\tag{21}
\]

这证明 C2。只对奇数指标使用了 (20)、(21)；偶数指标在零起点的和中由实际值 (12) 消去。

## 4. 真实乘积路径概率的完整 S1：C4

固定全部允许的 \(m,h,n\)，即

\[
m\in\mathbb N,\quad 1\le m,\quad m\le h<m+1,\quad n\in\mathbb N.
\]

于是 \(0\le h\)，并且整数 \(0\in I_m\)。在真实核上的固定 AllModes 公式 (6) 可以取 \(r=0\)，给出

\[
M_{h,n}(0)=\sum_{j\in J_m}q_j\mu_j^n v_j(0).
\tag{22}
\]

用第 2 节的不交分割重写这个同一有限和。每个偶数指标的被加项都因 (12) 等于零，包括 \(n=0\) 时；奇数部分则按 (9)、(10) 的双射逐一重编号。因此

\[
M_{h,n}(0)
=\sum_{\ell\in\mathrm{range}(m+1)}
q_{2\ell+1}\mu_{2\ell+1}^{\,n}(-1)^\ell.
\tag{23}
\]

对每一项，(21) 给出同一个 \(q_{2\ell+1}\)，而 \(\mu_{2\ell+1}\) 按定义就是相应角度的余弦。把所有项共同的实数因子 \(1/H\) 提到和外，并只在实数乘法中交换因子，得到

\[
M_{h,n}(0)
=
\frac1H\sum_{\ell\in\mathrm{range}(m+1)}
(-1:\mathbb R)^\ell
\cot\!\left(\frac{(2\ell+1:\mathbb R)\pi}{4H}\right)
\left(\cos\!\left(\frac{(2\ell+1:\mathbb R)\pi}{2H}\right)\right)^n.
\tag{24}
\]

式中的 \(2\ell+1:\mathbb R\) 表示自然数 \(2\ell+1\) 的实数转换。最后，由已经验证的 \(0\le h\)，使用真实概率桥 (2)，得到冻结命题 C4 的完整显示式：

\[
\boxed{\displaystyle
p(n,h)=\mathrm{killedMass}\ \nu_R\ h\ n\ 0
=
\frac1H\sum_{\ell\in\mathrm{range}(m+1)}
(-1:\mathbb R)^\ell
\cot\!\left(\frac{(2\ell+1:\mathbb R)\pi}{4H}\right)
\left(\cos\!\left(\frac{(2\ell+1:\mathbb R)\pi}{2H}\right)\right)^n.}
\tag{S1}
\]

这是真实 \(P_n=\mathrm{Measure.pi}(\lambda i,\nu_R)\) 对原 closedStrip 的概率等式，求和恰为 \(\ell=0,\ldots,H_N-1\)。

### 零步与零谱项

以上推导对任意自然 \(n\) 进行，没有在任何一步要求 \(n>0\)。特别地，对每一个实数 \(\mu_j\)，包括 \(\mu_j=0\)，自然数幂恒有 \(\mu_j^0=1\)。

也可直接核对 (S1) 在 \(n=0\) 的右侧：在 (5) 中取 \(F=\mathbf1\)、\(r=0\)，得到

\[
1=\sum_{j\in J_m}q_jv_j(0)
=\frac1H\sum_{\ell\in\mathrm{range}(m+1)}
(-1)^\ell
\cot\!\left(\frac{(2\ell+1:\mathbb R)\pi}{4H}\right).
\tag{25}
\]

第二个等号正是已经证明的偶数消去和奇数系数身份。因全部余弦的零次幂都是 \(1\)，(25) 就是同一个 (S1) 右侧在 \(n=0\) 时等于 \(1\)。真实核方面 \(K_{h,0}(0)=\delta_0\)，所以 \(M_{h,0}(0)=1\)，再由 (2) 得 \(p(0,h)=1\)。

中间指标 \(j=H_N=m+1\) 满足 \(\theta_j=\pi/2\)，故 \(\mu_j=0\)。若 \(m=2d\) 为偶数，则 \(H_N=2d+1\) 为奇数，该指标正是 (S1) 中的 \(\ell=d=m/2\)，其 cot 参数是 \(\pi/4\)。因为 \(\cot(\pi/4)=1\)，它在 \(n=0\) 时的贡献恰为

\[
\frac{(-1)^d}{H},
\]

并未删去；只有 \(n\ge1\) 时该项的 \(0^n\) 才等于零。若 \(m\) 为奇数，则 \(H_N\) 为偶数，该指标在 (22) 中由 \(v_j(0)=0\) 消去，适用于全部 \(n\)。两种情形都由原有精确身份处理。

对 \(j>H_N\) 且 \(j\in J_m\)，有 \(\pi/2<\theta_j<\pi\)，所以 \(\mu_j<0\)。这些指标中每一个奇数模态都保留在 (S1) 内，尤其最末的 \(j=2m+1,\ell=m\)。式中使用的是有符号的 \(\mu_j^n\)，没有将其改成绝对值幂，也没有对 \(n\) 或模态加奇偶匹配条件。

## 5. 真实低阈值分支的独立证明：C5

现在固定任意 \(h\in\mathbb R\)，满足

\[
0\le h<1.
\tag{26}
\]

本节不使用 (S1)、(20)、(21) 或 \(m=0\) 的任何全谱结论。

在真实行公式 (3) 中取 \(m=0\)、\(r=0\)。条件 \(m\le h<m+1\) 正好是 (26)，而

\[
|0+1|=|0-1|=1>0.
\]

所以两项保留条件同时为假，得到真实测度行

\[
K_h(0)=0.
\tag{27}
\]

零步仍按实际幂的定义处理：

\[
M_{h,0}(0)=\int \mathbf1(w)\,\delta_0(dw)=1.
\tag{28}
\]

对任意正自然数 \(n\)，唯一写成 \(n=1+k\)，其中 \(k\in\mathbb N\)。令 \(g=T_{h,k}\mathbf1\)。常数 \(\mathbf1\) 可测并由 \(1\) 有界；所列实际 action 接口还给出 \(g\) 可测且 \(|g|\le1\)。因此在真实半群公式 (1) 中取第一段 \(a=1\)、第二段 \(b=k\)、\(f=\mathbf1\) 完全满足条件，其方向具体为

\[
\begin{aligned}
M_{h,1+k}(0)
&=T_{h,1+k}\mathbf1(0)\\
&=T_{h,1}(T_{h,k}\mathbf1)(0)\\
&=\int g(w)\,K_{h,1}(0,dw)\\
&=\int g(w)\,K_h(0,dw)\\
&=0.
\end{aligned}
\tag{29}
\]

倒数第二步用了真实核的一次幂 \(K_{h,1}=K_h\)，最后一步用了 (27)。这正是先从零起点走一步、再作用剩余 \(k\) 步的次序；没有假定其他起点的行也为零。

由 (28)、(29)，对全部 \(n\in\mathbb N\) 有

\[
M_{h,n}(0)=
\begin{cases}
1,&n=0,\\
0,&n\ne0.
\end{cases}
\tag{30}
\]

(26) 中的非负条件满足真实路径概率桥 (2)，故对相同的所有 \(h,n\)，

\[
\boxed{\displaystyle
p(n,h)=\mathrm{killedMass}\ \nu_R\ h\ n\ 0
=\begin{cases}
1,&n=0,\\
0,&n\ne0.
\end{cases}}
\tag{31}
\]

这包括 \(h=0\) 和全部自然时间。证明只调用了允许 \(m=0\) 的真实一步行、真实幂的零步与一次幂、半群公式和非负阈值概率桥，没有扩张高阈值全谱定理的 \(1\le m\) 范围。

## 6. 全部非负阈值的覆盖与弱端点

给定任意 \(h\ge0\)，若 \(h<1\)，使用第 5 节；若 \(h\ge1\)，取自然数下取整 \(m=\lfloor h\rfloor_+\)。其标准下取整性质给出

\[
m\le h<m+1.
\]

此时 \(m\ge1\)：否则 \(m=0\) 会由右侧严格不等式推出 \(h<1\)，与 \(h\ge1\) 矛盾。因此高阈值分支的全部条件成立，第 4 节给出 (S1)。这两个分支覆盖全部 \(h\ge0\)。

若把 (24) 的有限和记作 \(F(m,n)\)，上述覆盖也可写为数学上的导出总述

\[
p(n,h)=
\begin{cases}
1,&0\le h<1,\ n=0,\\
0,&0\le h<1,\ n\ne0,\\
F(\lfloor h\rfloor_+,n),&h\ge1.
\end{cases}
\]

高阈值分支没有排除 \(h=m\)。对整数状态，已认证 integer_closed_iff 给出 \(|s|\le h\) 与 \(|s|\le m\) 等价，所以 \(\pm m\) 在弱闭区间内保留，\(\pm(m+1)\) 则因 \(h<m+1\) 被排除。真实行 (3) 在 \(r=m\) 或 \(r=-m\) 时只丢弃向外的一半质量；它并未将向内的一半重新归一化。特别地，整数 \(h=k\ge1\) 时 \(m=k\)，吸收点仍是 \(\pm(k+1)\)。

C1–C5 因而在冻结的真实 law、真实概率、相同有限指标、相同相位和范数、全部自然时间以及弱边界约定下全部得到所需数学推导。没有除以生存质量，没有加入正生存、正谱、非零谱、无周期或额外奇偶前提。证明范围止于该有限 S1 与独立低阈值分支；不包含严格事件、其他实起点类或 S2–S5。
