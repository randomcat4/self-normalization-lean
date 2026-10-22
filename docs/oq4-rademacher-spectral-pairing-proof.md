# 有限有符号谱的精确反射配对

STATUS: PROOF_READY
EVIDENCE: MATH_ONLY
INDEPENDENT_REVIEW: PENDING
S2_STATUS: OPEN
S3_S5_STATUS: OPEN
SPECTRUM_STATUS: OPEN
ROOT_STATUS: OPEN

本稿给出冻结接口 v1 的 P1、P2、定义所需正性和全部所列时间端点的完整数学推导。这里只提交匿名数学证明供新上下文验缝，不宣称独立数学审查已通过，也不宣称任何 Lean 认证。

## 1. 固定输入、量词和真实概率接口

本次读取并在证明前核对的数学输入如下。所有摘要均为 SHA256，字节数为文件原始字节数。

| 输入 | SHA256 | 字节数 |
| --- | --- | ---: |
| frozen-rademacher-spectral-pairing-v1.md | 69c5cf5822044e19520e10c4a6de4a31e0e8f43d296e477982a9c5637c85c6fb | 8661 |
| 原 spectrum01.md，commit 35d4580b61e22e7145f47730045a09874ef93259 | b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b | 4306 |
| frozen-rademacher-finite-s1-v1.md | e2e9240f739e737c83195f177dcd54707c023151cf3e4faf7f1d862e87b585fe | 10956 |

固定任意自然数 m≥1、实数 h 满足 m≤h<m+1，以及任意自然数 n。全文不对 n 加正性、奇偶性或长时间条件。写

\[
H_N=m+1,\qquad H=(m:\mathbb R)+1.
\]

当自然数指标出现在实角度或实分母中时，均取其自然嵌入实数；因此 H 正是 H_N 的实值，并非新参数。

概率对象始终是冻结接口中的同一组对象：

\[
\nu_R=\tfrac12\delta_1+\tfrac12\delta_{-1},\qquad
\mathrm{Path}\,n=\mathrm{Fin}\,n\to\mathbb R,\qquad
P_n=\mathrm{Measure.pi}(\lambda i:\mathrm{Fin}\,n,\nu_R),
\]
\[
S_k(a)=\mathrm{Shao.prefixSum}\,a\,k,\qquad
A_n(h)=\mathrm{Shao.closedStrip}\,h
 =\{a:\mathrm{Path}\,n:\ \forall k\le n,\ |S_k(a)|\le h\},
\qquad p(n,h)=P_n.\mathrm{real}(A_n(h)).
\]

这里使用固定 law 的内部概率实例。每个 S_k 是坐标的有限和，故连续；A_n(h) 是 k=0,…,n 对应的有限个闭条件的交，因而可测。由于 h≥m≥1，零时刻条件 |S_0|=0≤h 自动满足；所以这是来源中 1≤k≤n 的同一弱生存事件，包括整数端点 h=m。本文没有改变阈值或吸收位置。

直接上游数学引理是所分配的 S1 接口 C4，在上述固定对象及完全相同的 m、h、n 上给出

\[
\begin{aligned}
p(n,h)
 &=\mathrm{killedMass}\,\nu_R\,h\,n\,0\\
 &=\frac1H\sum_{\ell\in L_m}
 (-1)^\ell
 \cot\!\left(\frac{(2\ell+1)\pi}{4H}\right)
 \left(\cos\!\left(\frac{(2\ell+1)\pi}{2H}\right)\right)^n,
\qquad L_m=\{0,\ldots,m\}.
\tag{1}
\end{aligned}
\]

式 (1) 是对固定真实乘积路径概率的已有数学引理的调用，不是用右侧重新定义 p，也不是增加“某个 p 满足 S1”的自由前提。它同时提供真实 killedMass 和 Measure.pi closedStrip 概率之间的连接；本文不另造矩阵、概率律、归一化链或自由特征值。派发许可在数学层使用这个精确 C4；它尚非本稿核验过的形式认证声明，本稿也不作这种宣称。Iteration、FiniteBasis、AllModes 的内容仅通过这个固定上游引理传递。

以下证明只改写式 (1) 的同一个有限和。在需要时记

\[
r_\ell=2\ell+1,\quad
\alpha_\ell=\frac{r_\ell\pi}{4H},\quad
\beta_\ell=2\alpha_\ell=\frac{r_\ell\pi}{2H},\quad
c_\ell=\cos\beta_\ell.
\]

它们就是冻结定义的 \(\alpha_{m,\ell},\beta_{m,\ell}\)。

## 2. 完整有限索引反射与无重叠覆盖

定义冻结的下半部和反射

\[
K_m=\{\ell\in L_m:2\ell<m\},\qquad
\iota(\ell)=m-\ell.
\]

自然数减法只在 \(\ell\in L_m\)、即 \(\ell\le m\) 时使用。令 \(t=\iota(\ell)\)，则 t 为自然数、t≤m 且

\[
\ell+t=m.
\tag{2}
\]

因此 \(\iota(t)=\ell\)；反射是 L_m 上的对合，尤其是单射。

再定义

\[
U_m=\{\ell\in L_m:m<2\ell\},\qquad
C_m=\{\ell\in L_m:2\ell=m\}.
\]

对每个 \(\ell\in L_m\)，自然数序的三歧性给出 \(2\ell<m\)、\(2\ell=m\)、\(m<2\ell\) 中恰好一种，所以

\[
L_m=K_m\ \dot\cup\ C_m\ \dot\cup\ U_m.
\tag{3}
\]

这里的三个集合两两不交。若 \(\ell\in K_m\)，式 (2) 给
\(2t+2\ell=2m\)，由 \(2\ell<m\) 得 \(2t>m\)，故 t∈U_m。
反过来，若 t∈U_m，令 \(\ell=m-t\)；同样有 \(\ell+t=m\)，由
\(2t>m\) 得 \(2\ell<m\)，故 \(\ell\in K_m\) 且 t=\iota(\ell)。
于是

\[
\iota(K_m)=U_m,
\tag{4}
\]

并且限制后的反射为这两个有限集合之间的双射。

中心集合非空当且仅当 m 为偶数。具体地，若 m=2q，则唯一解是
\(\ell=q=m/2\)，且 q≤m，因而

\[
C_m=
\begin{cases}
\{m/2\},&\text{m 为偶数},\\
\varnothing,&\text{m 为奇数}.
\end{cases}
\tag{5}
\]

若存在中心指标，等式 m=2ℓ 也反过来证明 m 偶；所以 (5) 没有遗漏其他情形。这里的 m/2 是自然数除法，只在偶数分支用其精确等式 \(2(m/2)=m\)。

在原 S1 的奇数频率中，\(\ell\mapsto r_\ell=2\ell+1\) 是 L_m 到
\(\{1,3,\ldots,2m+1\}\) 的双射。对 \(\ell\in K_m\)，

\[
1\le r_\ell<H_N,\qquad
r_{\iota(\ell)}
 =2(m-\ell)+1=2H_N-r_\ell>H_N.
\tag{6}
\]

式 (6) 的反射等式由 \(\ell+\iota(\ell)=m\) 推得，没有在越界指标上使用截断减法。中心指标满足 \(r_\ell=H_N\) 当且仅当 \(2\ell=m\)；这种原 S1 的奇数中心频率仅在 m 偶数时存在。因此 (3)–(6) 正是原 S1 全部奇数指标的无重叠、无遗漏分解，不是另选一组谱指标。

特别地，对 L_m 上任意实函数 f，有限和的分割、反射的单射性及 (5) 给出

\[
\sum_{\ell\in L_m}f(\ell)
 =
 \sum_{\ell\in K_m}\bigl(f(\ell)+f(\iota(\ell))\bigr)
 +
 \begin{cases}
 f(m/2),&\text{m 为偶数},\\
 0,&\text{m 为奇数}.
 \end{cases}
\tag{7}
\]

每个非中心指标在 (7) 中恰出现一次：下半部作为第一项，上半部作为唯一反射像。

## 3. 角度范围、零谱、负谱和分母

因为 m≥1，H≥2。对所有 \(\ell\in L_m\)，

\[
1\le r_\ell\le 2m+1=2H_N-1<2H_N.
\]

乘以正数 \(\pi/(4H)\) 得

\[
0<\alpha_\ell<\frac\pi2,\qquad
0<\beta_\ell<\pi.
\tag{8}
\]

所以所有原 S1 中的 \(\sin\alpha_\ell\) 都严格为正，cot 的分母不为零。若 \(\ell\in K_m\)，由 (6) 进一步得到

\[
0<\alpha_\ell<\frac\pi4,\qquad
0<\beta_\ell<\frac\pi2.
\tag{9}
\]

故这时 \(\sin\alpha_\ell>0\)、\(\cos\alpha_\ell>0\)、\(c_\ell>0\)，配对公式中 cot 与 tan 的分母全部合法。

由 (6) 的精确频率反射，

\[
\alpha_{\iota(\ell)}=\frac\pi2-\alpha_\ell,\qquad
\beta_{\iota(\ell)}=\pi-\beta_\ell.
\]

利用正弦余弦的余角及补角恒等式，并利用已证的非零分母，得到

\[
\cot\alpha_{\iota(\ell)}=\tan\alpha_\ell,\qquad
c_{\iota(\ell)}=-c_\ell.
\tag{10}
\]

所以 K_m 的特征值全部为正，其反射像 U_m 的特征值全部为负，没有把负谱替换成绝对值。

若 m=2q，则中心指标 q 满足 \(r_q=H_N\)，从而

\[
\alpha_q=\frac\pi4,\qquad
\beta_q=\frac\pi2,\qquad
\cot\alpha_q=1,\qquad c_q=0.
\tag{11}
\]

反过来，在 (8) 的范围内 \(\cos\beta_\ell=0\) 当且仅当
\(\beta_\ell=\pi/2\)，这等价于 \(r_\ell=H_N\)、即 \(2\ell=m\)。
因此 (11) 是原 S1 奇数和中唯一可能的零谱，且其存在性恰由 m 偶决定。为区分它和完整原 j 指标的中心，直接用 S1 接口中的透明定义
\(v_j(0)=\sin((j\pi/(2H))H)=\sin(j\pi/2)\)：当 m 奇数时，中心 j=H_N 为偶数，写 j=2q 就得 \(v_j(0)=\sin(q\pi)=0\)。所以这种完整 j 中心的起点因子为零。这与“零特征值在 n=0 仍满足 \(0^0=1\)”并不矛盾：那个偶数 j 模态的消去来自起点因子，而不是时间幂。P1/P2 仍只从 C4 的奇数和开始；此处只由透明定义解释完整 j 中心和奇数中心的区别，没有额外调用 C1 的待形式认证声明。

现在定义

\[
x=\frac\pi{4H},\quad y=\frac\pi{2H}=2x,\quad
a_m=\frac1H\cot x,\quad \rho_m=\cos y,\quad
\varepsilon_m(n)=(-1)^{n+m}.
\]

由 H≥2，

\[
0<x\le\frac\pi8<\frac\pi4,\qquad
0<y\le\frac\pi4<\frac\pi2.
\tag{12}
\]

所以 H>0、\(\sin x>0\)、\(\cos x>0\)，从而 \(\cot x>0\) 且 \(a_m>0\)。
又 \(\rho_m>0\)；因为
\(1-\cos y=2\sin^2(y/2)>0\)，还得到 \(\rho_m<1\)。对任意自然数 n，正数的自然幂为正，包括 \(\rho_m^0=1\)，故

\[
0<\rho_m<1,\qquad a_m\rho_m^n>0.
\tag{13}
\]

因此 H、\(\cot x\)、\(\rho_m\)、\(a_m\rho_m^n\) 以及本文实际使用的三角分母都非零。这些事实来自冻结的 m≥1，而非额外前提。没有任何一步以 p(n,h) 作分母。

## 4. 每个反射对的有符号全时间计算

在式 (7) 中取

\[
f_n(\ell)=(-1)^\ell\cot\alpha_\ell\,c_\ell^n.
\]

固定 \(\ell\in K_m\)，令 t=\iota(\ell)。由 m=ℓ+t，

\[
(-1)^t=(-1)^\ell(-1)^m.
\tag{14}
\]

例如将 \((-1)^m=(-1)^\ell(-1)^t\) 两边乘以 \((-1)^\ell\)，并用
\((-1)^{2\ell}=1\)，便得到 (14)；不需要对负数指数作定义。对所有自然数 n，

\[
(-c_\ell)^n=(-1)^n c_\ell^n,
\tag{15}
\]

这在 n=0 时两边都为 1，在后继步由乘法立即保持，故包含所有时间。

结合 (10)、(14)、(15) 及自然数指数的加法法则，

\[
\begin{aligned}
f_n(t)
 &=(-1)^t\tan\alpha_\ell\,(-c_\ell)^n\\
 &=(-1)^\ell(-1)^m(-1)^n
      \tan\alpha_\ell\,c_\ell^n\\
 &=(-1)^\ell\varepsilon_m(n)\tan\alpha_\ell\,c_\ell^n.
\end{aligned}
\]

于是逐对精确有

\[
f_n(\ell)+f_n(\iota(\ell))
 =
 (-1)^\ell\bigl(\cot\alpha_\ell+
       \varepsilon_m(n)\tan\alpha_\ell\bigr)c_\ell^n.
\tag{16}
\]

其中符号来自原负特征值的 n 次幂，没有增加 n 与 m 或 ℓ 的奇偶匹配条件。

若 m 偶，令 q=m/2。中心项由 (11) 精确等于

\[
\frac1H f_n(q)=\frac{(-1)^q}{H}\,0^n.
\tag{17}
\]

若 m 奇，则没有中心项。故 (17) 连同空中心分支正是冻结定义

\[
Z_m(n)=
\begin{cases}
\displaystyle\frac{(-1)^{m/2}}H\,0^n,&\text{m 为偶数},\\
0,&\text{m 为奇数}.
\end{cases}
\tag{18}
\]

对 n=0，(17) 使用 \(0^0=1\)；对 n≥1 才使用 \(0^n=0\)。

将 (16) 和 (18) 代入 (7)，再代入真实概率恒等式 (1)，得到

\[
\boxed{\displaystyle
p(n,h)=\frac1H\sum_{\ell\in K_m}
 (-1)^\ell\bigl(\cot\alpha_\ell+
       \varepsilon_m(n)\tan\alpha_\ell\bigr)
 (\cos\beta_\ell)^n+Z_m(n).
}
\tag{P1}
\]

这证明了冻结 P1，并同时完成了原有限和全部指标的反射覆盖。特别地，P1 中仍然是同一 Measure.pi 的同一 closedStrip 概率。

## 5. 首正模态、最负模态与首对的精确提取

因为 m≥1，0∈K_m。首指标满足 \(\alpha_0=x\)、\(\beta_0=y\)、\(c_0=\rho_m\)，原 S1 的首模态贡献为

\[
\frac1H f_n(0)=a_m\rho_m^n.
\tag{19}
\]

其反射是 \(\iota(0)=m\)，即原最后奇数频率 \(2m+1\)。由 (10)，

\[
\cot\alpha_m=\tan x,\qquad c_m=-\rho_m.
\]

所以最负模态自身的系数与带时间贡献分别是

\[
\boxed{\displaystyle \frac{(-1)^m}{H}\tan x},
\qquad
\boxed{\displaystyle \frac{(-1)^m}{H}\tan x\,(-\rho_m)^n}.
\tag{20}
\]

这些确为原谱的两个极端：\(\beta_\ell\) 随 ℓ 严格增加，且都在 (0,π) 中；余弦在此区间严格递减。后者也可直接由
\[
\cos u-\cos v
=2\sin\frac{u+v}{2}\sin\frac{v-u}{2}>0
\quad(0<u<v<\pi)
\]
验证。因此首模态的特征值为最大值 \(\rho_m\)，末模态为最小值 \(-\rho_m\)。同一来源的完整 j=1,…,2H_N−1 余弦指标也有相同的首末端点。式 (20) 中的模态保留其负特征值和时间符号。

由 (12) 的非零分母，

\[
\frac{\tan x}{\cot x}
 =\frac{\sin^2x}{\cos^2x}=(\tan x)^2.
\tag{21}
\]

因此 \(\ell=0\) 的配对贡献精确为

\[
\begin{aligned}
\frac1H(\cot x+\varepsilon_m(n)\tan x)\rho_m^n
 &=a_m\rho_m^n
       \left(1+\varepsilon_m(n)(\tan x)^2\right).
\end{aligned}
\tag{22}
\]

式 (20) 单独除以 \(a_m\rho_m^n\) 的值恰为
\(\varepsilon_m(n)(\tan x)^2\)，因为 \((-\rho_m)^n=(-1)^n\rho_m^n\)。
故 (22) 没有把负模态错误地当成另一个正主模态，也没有丢失 n 或 m 的奇偶性。

## 6. 明确的归一化余谱和 P2

令 \(T_m=K_m\setminus\{0\}\)，即冻结的 \(K_m.\mathrm{erase}\,0\)。定义

\[
\boxed{\displaystyle
R_m(n)=
 \sum_{\ell\in T_m}
 (-1)^\ell
 \frac{\cot\alpha_\ell+\varepsilon_m(n)\tan\alpha_\ell}{\cot x}
 \left(\frac{\cos\beta_\ell}{\rho_m}\right)^n
 +\frac{Z_m(n)}{a_m\rho_m^n}.
}
\tag{23}
\]

这是只依赖于 m、n 的具体有限表达式，不是一个待选择的误差变量。所有分母由第 3 节保证非零。

为核对归一化，任取 \(\ell\in T_m\)。自然数幂的商法则给
\[
(c_\ell/\rho_m)^n=c_\ell^n/\rho_m^n.
\]
该法则在 n=0 也成立，因为 \(\rho_m\ne0\)，两边均为 1。因此，由
\(a_m=(\cot x)/H\) 和 (13)，

\[
\begin{aligned}
&a_m\rho_m^n
 \left[
 (-1)^\ell
 \frac{\cot\alpha_\ell+\varepsilon_m(n)\tan\alpha_\ell}{\cot x}
 \left(\frac{c_\ell}{\rho_m}\right)^n
 \right]\\
&\hspace{2em}
 =\frac1H(-1)^\ell
    (\cot\alpha_\ell+\varepsilon_m(n)\tan\alpha_\ell)c_\ell^n.
\end{aligned}
\tag{24}
\]

同样 \(a_m\rho_m^n[Z_m(n)/(a_m\rho_m^n)]=Z_m(n)\)。
将 (24) 对有限 T_m 求和，并使用 \(K_m=\{0\}\dot\cup T_m\)、(22) 和 P1，便得到

\[
\boxed{\displaystyle
p(n,h)=a_m\rho_m^n
 \left(1+\varepsilon_m(n)(\tan x)^2+R_m(n)\right).
}
\tag{P2}
\]

所以 P2 是同一个真实概率身份的精确主对抽取，且 (23) 正是冻结要求的余谱公式。

## 7. 正时间、零时间和全部小 m 端点

### 7.1 正时间的中心消失与余频率

若 n≥1，则存在自然数 k 使 n=k+1，因而 \(0^n=0^k\cdot0=0\)。
由 (18)，不论 m 奇偶都有 \(Z_m(n)=0\)。因此这时 (23) 恰为显示的余谱有限和，没有其他项。

每个 \(\ell\in T_m\) 都是非零自然数，所以 ℓ≥1，从而其频率

\[
r_\ell=2\ell+1\ge3,\qquad r_\ell<H_N.
\tag{25}
\]

该频率是奇数；其负谱同伴的频率是 \(2H_N-r_\ell\)，已在同一配对项中保留。由 (9) 这些下半部余频率的余弦为正；若 T_m 非空，严格的余弦单调性还给 \(0<c_\ell<\rho_m\)。这里不据此声称任何统一求和估计或渐近结论。

### 7.2 零时间的真实概率一与完整恢复

当 n=0，Path 0 为唯一空坐标路径的类型。若 k≤0，则 k=0，其 prefixSum 是空和 0。因为 h≥0，A_0(h) 是全空间；固定乘积概率测度的全空间质量为 1。因此

\[
p(0,h)=1.
\tag{26}
\]

式 (1) 对 n=0 的调用包含所有 \(c_\ell^0=1\)，特别包含中心的 \(0^0=1\)，所以由 (7)–(18) 得

\[
1=\frac1H\sum_{\ell\in K_m}
 (-1)^\ell\left(\cot\alpha_\ell+(-1)^m\tan\alpha_\ell\right)
 +Z_m(0),
\tag{27}
\]
其中
\[
Z_m(0)=
\begin{cases}
(-1)^{m/2}/H,&\text{m 偶},\\
0,&\text{m 奇}.
\end{cases}
\tag{28}
\]

式 (27) 是从真实空路径事件和同一上游 C4 得到的全量恒等式，不是通过删去中心项得到的。再应用第 6 节对 n=0 同样合法的归一化，得到

\[
1=a_m\left(1+(-1)^m(\tan x)^2+R_m(0)\right).
\tag{29}
\]

等价地，具体定义 (23) 在零时间满足

\[
R_m(0)=\frac1{a_m}-1-(-1)^m(\tan x)^2.
\tag{30}
\]

因此 P2 的完整右侧在 n=0 确实恢复 1；定义中的 \(Z_m(0)/a_m\) 没有省略。

### 7.3 m=1 和 m=2 的空尾

若 m=1，条件 \(2\ell<1\) 强制 ℓ=0，所以 \(K_1=\{0\}\)、
\(T_1=\varnothing\)。m 为奇数又给 \(Z_1(n)=0\)。故

\[
R_1(n)=0\quad\text{对所有 }n\in\mathbb N,
\tag{31}
\]
特别包含要求的全部 n≥1。

若 m=2，条件 \(2\ell<2\) 也强制 ℓ=0，所以 \(K_2=\{0\}\)、
\(T_2=\varnothing\)。此时 H=3、m/2=1，因此

\[
Z_2(n)=-\frac13\,0^n,\qquad
R_2(n)=-\frac{0^n}{3a_2\rho_2^n}.
\tag{32}
\]

于是 n≥1 时 \(R_2(n)=0\)，但

\[
Z_2(0)=-\frac13,\qquad R_2(0)=-\frac1{3a_2}.
\tag{33}
\]

这并非空尾能够删除的中心贡献。

还可直接核对这两个退化端点与 (29) 的一致性，作为一般证明后的精确特化。m=1 时 H=2、x=π/8，利用
\(\cot x-\tan x=2\cot(2x)\)，零时间的首对为

\[
\frac12(\cot(\pi/8)-\tan(\pi/8))
=\cot(\pi/4)=1.
\]

m=2 时 H=3、x=π/12，利用
\(\cot x+\tan x=1/(\sin x\cos x)=2/\sin(2x)\)，零时间的首对为

\[
\frac13(\cot(\pi/12)+\tan(\pi/12))
=\frac13\frac2{\sin(\pi/6)}=\frac43.
\]

加上 (33) 的中心项 \(-1/3\)，总和才等于 1。这些特化来自已证明的全量公式，并不替代对任意 m、n 的推导。

## 8. 引理使用、阅读边界与未覆盖范围

数学依赖账：

- FIXED_UPSTREAM_MATH_ONLY：S1 C4，使用冻结的真实 law、Path、Measure.pi、closedStrip、killedMass、同一个 m、h、n 和原有限和。它提供实际概率连接及全部 n≥0 的完整 S1；本文没有复证 S1，也没有把它变成一个任意新结构的自由假设或公理。
- TRANSPARENT_DEFINITION_USED，仅作完整 j 中心解释：S1 接口所列 v_j 的定义；本文直接化简 v_j(0)=sin(jπ/2)，并在 j 偶时得到零，不额外调用 C1。
- PROVED_HERE：K_m、反射像及中心的互不重叠覆盖；全部角度和分母范围；正负及中心谱分类；全自然时间反射符号计算；首正与最负模态和首对；明确 R_m(n) 的 P2；正时间中心消失、余频率 r≥3；零时间概率一；m=1、m=2 空尾及 m=2 零时间中心保留。
- ELEMENTARY_IDENTITIES_USED：正弦余弦余角、补角、倍角与差公式，实数域运算，自然数幂的乘法及商法则，有限和的分割和单射重编号。文中已给出涉及符号、中心和归一化的具体使用过程。

阅读边界：除第 1 节三份核验输入外，只读取工作规则 AGENTS.md、SERVER.md、coordination/TEAM.md，以及 math-theorem 技能及其 prompt-library、openai-workflow、lean-verification 规范。未读取来源语义审查报告或其推理，未读取 intake/candidate 历史、任何其他匿名证明（包括 S1 的证明）、其他 review、作者过程、未认证实施、private Source、canonical、Git 或 cache。没有读取三个传递上游接口的证明，也没有运行 Lean、构建、枚举或数值实验。唯一写入为本匿名证明文件。

范围结论：本稿仅完成固定 1≤m、m≤h<m+1、全部自然数 n 的精确有限身份及列明的定义和边界。没有加入长时间、奇偶匹配、全谱正性、正生存或非零谱条件；没有以生存概率为分母。它不处理 0≤h<1 的另支、不将 m 扩为 0、不改变弱端点、不改变起点或实 coset。统一指数余项界、H→∞ 且 n/H²→∞ 的双尺度极限、完整 S2、S3–S5、strict 事件、Spectrum 和一般 OQ4 根结论均保持 OPEN。本稿状态止于 PROOF_READY / MATH_ONLY，等待新上下文数学审查。
