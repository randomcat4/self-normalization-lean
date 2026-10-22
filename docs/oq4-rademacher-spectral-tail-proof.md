# 统一余谱指数界的完整数学证明

STATUS: PROOF_READY
RESULT: PROVED_AS_AUTHOR_CANDIDATE
CERTIFICATION: MATH_ONLY
FRESH_INDEPENDENT_REVIEW: PENDING
LEAN_STATUS: NOT_RUN
S2_STATUS: OPEN
S3_S5_STATUS: OPEN
SPECTRUM_STATUS: OPEN
ROOT_STATUS: OPEN

## 1. 冻结目标与事先固定的绝对常数

本稿仅证明冻结接口 v1 的 U1。先于选取任何 m、h、n，定义

\[
 q:=\exp(-3\pi^2/2),\qquad
 C:=\frac{2}{3(1-q)}.
 \tag{1}
\]

由于 \(\pi>0\)，有 \(0<q<1\)，故 \(C>0\)。这是一个绝对实常数，没有参数或奇偶类别的依赖。

现在任取自然数 \(m\ge1\)、实数 \(h\) 满足 \(m\le h<m+1\)，以及自然数 \(n\) 满足

\[
 H^2\le n,\qquad H:=m+1.
 \tag{2}
\]

式中及以下涉及实数运算时，将自然数嵌入实数。另记 \(H_N=m+1\) 为自然数版本，因此 \(H\) 是 \(H_N\) 的实数值，不是独立参数。我们证明同一冻结余谱满足

\[
 |R_m(n)|\le C\exp\left(-\frac{\pi^2n}{H^2}\right).
 \tag{3}
\]

h 保持任意给定格点胞元内的值，包括弱端点 h=m。固定概率对象仍为冻结接口的 Rademacher 产品律下、从 0 出发的闭条带事件概率 p(n,h)；本稿没有以谱和定义 p。

## 2. 逐项保留的余谱定义

令

\[
 x:=\frac{\pi}{4H},\qquad \theta:=2x=\frac{\pi}{2H},
 \qquad \alpha_{m,\ell}:=(2\ell+1)x,
 \qquad \beta_{m,\ell}:=(2\ell+1)\theta.
 \tag{4}
\]

使用冻结约定

\[
 \cot u:=\frac{\cos u}{\sin u},\qquad
 \tan u:=\frac{\sin u}{\cos u},\qquad
 K_m:=\{\ell\in\{0,\ldots,m\}:2\ell<m\},
\]

\[
 \varepsilon_m(n):=(-1)^{n+m},\qquad
 a_m:=H^{-1}\cot x,\qquad \rho_m:=\cos\theta,
\]

以及全时间中心项

\[
 Z_m(n):=
 \begin{cases}
 ((-1)^{m/2}/H)\,0^n,&m\text{ 为偶数},\\
 0,&m\text{ 为奇数}.
 \end{cases}
 \tag{5}
\]

这里所有幂指数均为自然数，尤其保留 \(0^0=1\)。令 \(T_m:=K_m\setminus\{0\}\)。本稿所估计的正是冻结 P2 的唯一显示表达式

\[
 R_m(n)=
 \sum_{\ell\in T_m}
 (-1)^\ell
 \frac{\cot\alpha_{m,\ell}+\varepsilon_m(n)\tan\alpha_{m,\ell}}
      {\cot x}
 \left(\frac{\cos\beta_{m,\ell}}{\rho_m}\right)^n
 +\frac{Z_m(n)}{a_m\rho_m^n}.
 \tag{6}
\]

该定义适用于全部自然时间。它在固定上游 Pair P2 中与实际概率绑定为

\[
 p(n,h)=a_m\rho_m^n
 \left(1+(-1)^{n+m}\tan^2x+R_m(n)\right).
 \tag{7}
\]

式 (7) 是被允许引用的固定上游数学接口；本稿不重新证明配对身份，也不声称它已经通过 Lean。以下所有估计直接从式 (6) 推出，不将系数界、谱比界或求和界置为外部假设。

## 3. 定义域、分母与正时间中心项

由 \(m\ge1\) 得 \(H\ge2\)，所以

\[
 0<x\le\pi/8<\pi/4,
 \qquad 0<\theta\le\pi/4<\pi/2.
 \tag{8}
\]

因此 \(\sin x>0\)、\(\cos x>0\)，\(\cot x>0\)，从而 \(a_m>0\)。又因余弦在 \([0,\pi/2]\) 严格递减，\(0<\rho_m<1\)。对每个自然数 n 都有 \(\rho_m^n>0\)，于是

\[
 a_m\rho_m^n>0.
 \tag{9}
\]

以上均由固定 m 的范围推出，未增加分母合法性前提。

由 (2) 和 \(H\ge2\) 得 \(n\ge4\)，特别地 \(n\ge1\)。因此 \(0^n=0\)，式 (5) 在 m 为偶数和奇数时均给出 \(Z_m(n)=0\)。所以在 U1 的原时间域上，式 (6) 精确化为其中的有限和：

\[
 R_m(n)=\sum_{\ell\in T_m}b_{m,n,\ell}\,s_{m,\ell}^{\,n},
 \tag{10}
\]

其中只是对原项作记号缩写

\[
 b_{m,n,\ell}:=(-1)^\ell
 \frac{\cot\alpha_{m,\ell}+\varepsilon_m(n)\tan\alpha_{m,\ell}}
      {\cot x},
 \qquad
 s_{m,\ell}:=\frac{\cos\beta_{m,\ell}}{\rho_m}.
 \tag{11}
\]

对任意 \(\ell\in T_m\)，自然数范围条件给出

\[
 1\le\ell\le m,\qquad r:=2\ell+1\ge3,
 \qquad r<H_N.
 \tag{12}
\]

最后一个严格不等式是 \(2\ell<m\) 两边加 1。将其嵌入实数，得到

\[
 0<x<\alpha_{m,\ell}=rx<\pi/4,
 \qquad
 0<\theta<\beta_{m,\ell}=r\theta<\pi/2.
 \tag{13}
\]

故本稿实际使用的各个正弦和余弦分母均为正，\(\cot\alpha_{m,\ell}>0\)、\(\tan\alpha_{m,\ell}>0\)，且 \(0<s_{m,\ell}<1\)。这里只论证配对后下半谱的角域，没有要求原始全谱为正。

## 4. 内部系数引理：全部带符号配对系数的统一界

先证明所需的正切缩放不等式。对任意 \(0<y<\pi/2\)，正切在 \([0,y]\) 上二次可微，且

\[
 (\tan u)'=\frac1{\cos^2u},\qquad
 (\tan u)''=\frac{2\sin u}{\cos^3u}\ge0
 \quad(0\le u\le y).
\]

因此正切在该闭区间上凸。对 \(0<v\le y\)，在端点 0、y 的弦上使用 \(\tan0=0\)，得到

\[
 \tan v\le\frac{v}{y}\tan y.
 \tag{14}
\]

固定 \(\ell\in T_m\)，并使用 (12) 中的 r。将 (14) 用于 \(v=x\)、\(y=rx=\alpha_{m,\ell}\)，所有条件由 (13) 保证，得到

\[
 \tan x\le\frac1r\tan\alpha_{m,\ell}.
 \tag{15}
\]

由于 \(0<\alpha_{m,\ell}<\pi/4\)，正切的正导数以及 \(\tan(\pi/4)=1\) 给出

\[
 0<\tan\alpha_{m,\ell}<1.
 \tag{16}
\]

在这里正切、余切互为倒数，所有除法分母为正。由 (15) 得

\[
 \frac{\cot\alpha_{m,\ell}}{\cot x}
 =\frac{\tan x}{\tan\alpha_{m,\ell}}
 \le\frac1r,
 \tag{17}
\]

并由 (15)、(16) 得

\[
 \frac{\tan\alpha_{m,\ell}}{\cot x}
 =\tan\alpha_{m,\ell}\tan x
 \le\frac{\tan^2\alpha_{m,\ell}}r
 \le\frac1r.
 \tag{18}
\]

自然数幂的绝对值满足

\[
 |(-1)^\ell|=1,\qquad
 |\varepsilon_m(n)|=|(-1)^{n+m}|=1.
\]

对 (11) 中的原带符号系数使用三角不等式，再用 (17)、(18)，便有

\[
 \begin{aligned}
 |b_{m,n,\ell}|
 &=\frac{|\cot\alpha_{m,\ell}
       +\varepsilon_m(n)\tan\alpha_{m,\ell}|}{\cot x}\\
 &\le\frac{\cot\alpha_{m,\ell}+\tan\alpha_{m,\ell}}{\cot x}
 \le\frac2r\le\frac23.
 \end{aligned}
 \tag{19}
\]

这证明了对固定配对系数的界，常数独立于 m、n 及 \(\varepsilon_m(n)\) 的符号；没有将带符号系数改为另一个余谱。

## 5. 内部谱比引理：原速率的精确指数上界

首先，对 \(0\le u<\pi/2\)，有

\[
 (\tan u-u)'=\frac1{\cos^2u}-1=\tan^2u\ge0,
 \qquad \tan0-0=0.
\]

所以

\[
 \tan u\ge u \quad(0\le u<\pi/2).
 \tag{20}
\]

在同一区间定义

\[
 F(u):=\log(\cos u)+u^2/2.
\]

这里 \(\cos u>0\)，对数及其导数合法。由 (20)，

\[
 F'(u)=-\tan u+u\le0.
\]

故对任意 \(0<v\le w<\pi/2\)，单调性给出

\[
 \log(\cos w)-\log(\cos v)
 \le-\frac{w^2-v^2}{2}.
 \tag{21}
\]

将 (21) 用于 \(v=\theta\)、\(w=r\theta=\beta_{m,\ell}\)，条件由 (13) 满足。因 \(\rho_m=\cos\theta>0\)，指数函数的单调性给出

\[
 0<s_{m,\ell}
 =\frac{\cos(r\theta)}{\cos\theta}
 \le\exp\left(-\frac{(r^2-1)\theta^2}{2}\right)
 =\exp\left(-\frac{\pi^2(r^2-1)}{8H^2}\right).
 \tag{22}
\]

两边均非负，故可取自然数 n 次幂。利用指数乘法公式，以及 \(t:=n/H^2\ge1\)，得到

\[
 0<s_{m,\ell}^{\,n}
 \le\exp\left(-\frac{\pi^2(r^2-1)n}{8H^2}\right)
 =\exp\left(-\frac{\pi^2(r^2-1)t}{8}\right).
 \tag{23}
\]

这给出了冻结要求的同一频率 r 的谱比界；负谱的时间符号已由原配对系数中的 \(\varepsilon_m(n)\) 完整保留。

## 6. 内部求和引理与 U1 的闭合

对 \(\ell\in T_m\)，由 \(\ell\ge1\) 可令自然数 \(k:=\ell-1\)，则

\[
 r=2k+3,\qquad r^2-1=8+(r^2-9),
 \qquad r^2-9=4k^2+12k\ge12k.
 \tag{24}
\]

由于 \(t\ge1\) 且 \(r^2-9\ge0\)，有

\[
 (r^2-9)t\ge12k.
 \tag{25}
\]

因此，使用 (1) 定义的同一 q，

\[
 \begin{aligned}
 \exp\left(-\frac{\pi^2(r^2-1)t}{8}\right)
 &=\exp(-\pi^2t)
   \exp\left(-\frac{\pi^2(r^2-9)t}{8}\right)\\
 &\le\exp(-\pi^2t)\exp(-3\pi^2k/2)
 =\exp(-\pi^2t)q^k.
 \end{aligned}
 \tag{26}
\]

将 (19)、(23)、(26) 合并，逐一控制 (10) 中的每个原项：

\[
 |b_{m,n,\ell}s_{m,\ell}^{\,n}|
 =|b_{m,n,\ell}|s_{m,\ell}^{\,n}
 \le\frac23\exp(-\pi^2t)q^{\ell-1}.
 \tag{27}
\]

这里使用了 \(s_{m,\ell}>0\)，没有把一个有符号谱幂误认成非负量。

对有限和 (10) 使用三角不等式，并注意 \(T_m\subseteq\{1,\ldots,m\}\) 及各个 \(q^{\ell-1}\ge0\)，得到

\[
 \begin{aligned}
 |R_m(n)|
 &\le\sum_{\ell\in T_m}|b_{m,n,\ell}s_{m,\ell}^{\,n}|\\
 &\le\frac23\exp(-\pi^2t)
       \sum_{\ell\in T_m}q^{\ell-1}\\
 &\le\frac23\exp(-\pi^2t)
       \sum_{\ell=1}^{m}q^{\ell-1}.
 \end{aligned}
 \tag{28}
\]

最后这个有限几何和没有任何未处理频率。直接将相邻项消去可得

\[
 (1-q)\sum_{\ell=1}^{m}q^{\ell-1}=1-q^m\le1.
\]

因为 \(1-q>0\)，所以

\[
 \sum_{\ell=1}^{m}q^{\ell-1}\le\frac1{1-q}.
 \tag{29}
\]

式 (28)、(29) 与常数定义 (1) 合并，恰得

\[
 |R_m(n)|\le\frac{2}{3(1-q)}\exp(-\pi^2t)
 =C\exp\left(-\frac{\pi^2n}{H^2}\right).
\]

这就是 (3)。常数已在任取 m、h、n 之前固定，故完整量词为

\[
 \exists C>0\;\forall m\in\mathbb N,\ m\ge1\;\forall h\in\mathbb R,
 \ m\le h<m+1\;\forall n\in\mathbb N,
 \ (m+1)^2\le n\Longrightarrow
 |R_m(n)|\le C\exp\left(-\frac{\pi^2n}{(m+1)^2}\right).
\]

U1 证明完成。

## 7. 边界与证明范围核对

1. 若 m=1，条件 \(2\ell<1\) 强制自然数 \(\ell=0\)；若 m=2，条件 \(2\ell<2\) 同样强制 \(\ell=0\)。两种情形中 \(K_m=\{0\}\)，从而 \(T_m\) 为空。U1 的时间条件仍推出 \(n\ge1\)，所以中心项也为零，\(R_m(n)=0\)，原界成立。正文的统一有限和论证已经包含这些情况。
2. 偶 m 的中心项只在本证明先推出正时间之后归零。式 (5)、(6) 的全时间定义保持原样；n=0 时 \(0^0=1\) 的中心贡献没有被删除。U1 的前提在 n=0 时不成立，因为 \(H\ge2\)。
3. 原负主模态在 (7) 中仍精确为 \((-1)^{n+m}\tan^2x\)，它始终位于 R 之外。系数估计中的绝对值仅用于原余谱有限和的三角不等式，没有改变 (7) 的精确带符号身份。
4. h 的全部给定范围未缩小；证明未要求 h 避开整数、概率为正、n 的某种奇偶性、任何更大的 H 或时间阈值。实际吸收位置仍为 H=m+1，h=m 仍为闭条带弱端点。
5. 本稿只交付 U1 的数学作者候选证明。固定 Pair 身份的实际形式声明、其传递上游认证和本稿的独立数学审查仍由相应门负责。本稿没有 Lean、Git、cache 或远端计算动作，不交付双尺度 S2 推论、S3–S5、strict、其他 coset 或一般 OQ4 root。

## 8. 输入摘要、依赖账与阅读边界

本轮实际核对以下三个许可数学文件的 SHA256 和原始字节数：

- 冻结目标：`C:/game/shao lean/drafts/oq4/frozen-rademacher-spectral-tail-v1.md`；SHA256 `b220e1ca9f89e5f9a3328131b430fb54b9656e5113b93241adbde1aad627354a`；8952 bytes。
- 原来源：`C:/game/shao/current/oq4/c01/spectrum01.md`；固定来源 commit `35d4580b61e22e7145f47730045a09874ef93259`；SHA256 `b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b`；4306 bytes。
- 直接上游接口：`C:/game/shao lean/drafts/oq4/frozen-rademacher-spectral-pairing-v1.md`；SHA256 `69c5cf5822044e19520e10c4a6de4a31e0e8f43d296e477982a9c5637c85c6fb`；8661 bytes。

三者均与派发摘要一致。除此以外，只读取工作区 AGENTS.md、SERVER.md、coordination/TEAM.md，以及 math-theorem 技能、其 prompt-library/openai-workflow/lean-verification 规范和 chinese-output-style 技能。未读取其他冻结传递接口或任何实现。未读取任何 intake/candidate、其他匿名证明（包括 S1、Pair）、来源语义/数学/形式审查推理、作者过程、新 Lean/privateSource；没有外部搜索或数值枚举。

依赖状态仅据派发信息保留：Iteration、FiniteBasis 已完整形式认证；AllModes 独审收尾但尚未宣告完整形式认证；S1、Pair 的数学审查已 CORRECT、尚未 Lean。本稿未独立认证这些状态。式 (6)、(7) 只绑定到上述固定 Pair 接口，不允许以自由新公理替换。

内部引理账：分母合法性及中心项正时间归零由第 3 节证明；带符号系数界由第 4 节证明；全部下半谱范围内的谱比指数界由第 5 节证明；全部剩余奇数频率的有限求和界由第 6 节证明。只使用普通实微积分的导数、凸性弦不等式、单调性、指数与对数法则，以及自然数有限和代数；未调用省略证明的谱尾估计。
