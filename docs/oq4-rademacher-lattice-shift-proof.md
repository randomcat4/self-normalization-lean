# 弱格点位移 DA1 的独立数学证明

STATUS: PROOF_READY
MODE: MATH_ONLY
MATHEMATICAL_RESULT: PROVED_RELATIVE_TO_FIXED_SCA0_SCA1_SCA2
INDEPENDENT_REVIEW: PENDING
FORMAL_STATUS: NOT_RUN_NOT_AUTHORIZED
NEW_RAW_LEAF_COUNT: 0

本稿只证明冻结的 DA1 及其同域合法性。上游只使用固定 Scalar 接口的 SCA0、SCA1、SCA2 精确结论；不读取其证明、实现或审查。以下常数由这一固定上游的绝对常数选定，不是 DA1 的自由假设。本文没有序列特化、概率比较或 Brownian 输入。

## 1. 固定对象、依赖与目标

数学输入限于下列三个文件，原始字节均保持不变。

| 文件 | SHA256 | 字节数 |
| --- | --- | ---: |
| drafts/oq4/frozen-rademacher-lattice-shift-v1.md | 9cf9dba01aa9582ceb8e4d30af06c4778b8b367b61e61562dfc42c7ffb0e2b56 | 6067 |
| drafts/oq4/frozen-rademacher-scalar-bounds-v1.md | 225b63ae8522a126cb5c126f83cb782b024e95f592e9e2da5f36f56e0ce21356 | 9414 |
| C:/game/shao/current/oq4/c01/spectrum01.md | b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b | 4306 |

原来源的固定提交为 35d4580b61e22e7145f47730045a09874ef93259。唯一项目数学上游是第二个文件；第三个文件用于核对真实对象和弱胞元语义，不从中默用任何未冻结的概率或渐近结论。

对自然数 m，沿用固定定义

\[
H=H(m)=(m:\mathbb R)+1,\qquad
u=u(m)=\frac{\pi}{4H},\qquad z=\frac{\pi}{2H},
\]
\[
a=a(m)=\frac1H\frac{\cos u}{\sin u},\qquad
\rho=\rho(m)=\cos z,\qquad \lambda=\frac{\pi^2}{8}.
\]

这里只是省略固定函数的参数，不把 H、u、a 或 rho 改成独立变量。所有对数均为实对数 Real.log。

固定上游 SCA0 对每个 m≥1 给出 H≥2、H>0、H²>0、H⁴>0，以及

\[
0<u\le\pi/8<\pi/2,\quad 0<z\le\pi/4<\pi/2,
\]
\[
\sin u>0,\quad \cos u>0,\quad \cos z>0,
\quad a>0,\quad 0<\rho<1,\quad \pi a/4>0.
\]

SCA1、SCA2 给出先于所有 m 选定的绝对实常数 C_a>0、C_rho>0，使每个 m≥1 满足

\[
\left|a-\frac4\pi\right|\le\frac{C_a}{H^2},
\qquad
\left|\log\rho+\frac\lambda{H^2}\right|
\le\frac{C_{\rm rho}}{H^4}. \tag{1}
\]

这正是同一固定 a、rho 和 H 的接口；没有以其他函数或自由 Taylor 条件替代它。现从该固定存在性结论先选定一次 C_a、C_rho，后文不再随 m、h、n 改选。

目标是选定绝对 C>0，使所有 m≥1、所有实数 h 满足

\[
(m:\mathbb R)\le h<(m:\mathbb R)+1,
\]

以及所有 n∈ℕ（包括零），令 N=(n:ℝ)、delta=H−h 后，有

\[
\left|
\lambda\frac N{h^2}+N\log\rho+\log\frac{\pi a}{4}
-2\lambda\frac N{h^3}\delta
\right|
\le C\left(\frac N{h^4}+\frac1{H^2}\right). \tag{2}
\]

由于 2lambda=π²/4，式 (2) 的领先位移系数与冻结 DA1 完全相同。

## 2. 同域合法性与弱胞元端点

任取 m≥1 和满足上述左闭右开条件的 h。自然数到实数的保序性给出

\[
h\ge(m:\mathbb R)\ge1>0,\qquad
H=(m:\mathbb R)+1\ge2>0.
\]

因此 h²、h³、h⁴、H²、H⁴ 都严格为正，特别全部非零。定义 delta=H−h 后，从 h<H 得 delta>0，从 h≥m 得

\[
\delta=H-h\le((m:\mathbb R)+1)-(m:\mathbb R)=1,
\qquad H=h+\delta. \tag{3}
\]

故这里总有 0<delta≤1，并且 H>h>0。若 h=(m:ℝ)，直接代入得 delta=1；右端 h=H 仍不在定义域，绝未引入 delta=0。

上游 SCA0 已对这个同一 m 给出 sin u>0、a>0、0<rho<1 和 πa/4>0。故 rho 与 πa/4 的实对数均作用于严格正实数。固定定义中的 4H、2H、H、sin u 都非零；π>0 和实数常量 2、4 的非零性也保证出现的其他显示除法有合法正分母。上述检查不添加任何自由正性假设。

## 3. 内部对数界的完整推导

本节证明所需的内部结论，而不把它当作上游输出。先令

\[
c=\cos(\pi/8),\qquad D_a=\frac{\pi C_a}{4},
\qquad C_{\log}=\frac{D_a}{c}. \tag{4}
\]

因为 0<π/8<π/2，c>0；又 cos 的值不超过 1，所以 c≤1。于是 D_a>0、C_log>0；它们已经先于 m、h、n 选定。

为明确这里使用的初等三角估计，证明如下。对 t≥0，函数 f(t)=t−sin t 满足 f(0)=0、f'(t)=1−cos t≥0，故 sin t≤t。对 0≤s≤t≤π/2，cos 的导数为 −sin，且 sin 在该区间非负，因此 cos s≥cos t。把这两个结论用于 0<u≤π/8，结合 SCA0 的 sin u>0、cos u>0，得到

\[
0<\sin u\le u,\qquad \cos u\ge c>0.
\]

定义固定表达式 q=πa/4。利用 u=π/(4H) 和 H、sin u 非零，确切有

\[
q=\frac{\pi}{4H}\frac{\cos u}{\sin u}
=\frac{u}{\sin u}\cos u
\ge\cos u\ge c. \tag{5}
\]

另一方面，π≠0 给出 (π/4)(4/π)=1，故

\[
|q-1|
=\frac\pi4\left|a-\frac4\pi\right|
\le\frac{D_a}{H^2}. \tag{6}
\]

现证明适用于这里的对数估计。若 q=1，则 |log q|=0。若 q≠1，对 log 在以 q 和 1 为端点的闭区间应用拉格朗日中值定理。由 q≥c>0、1≥c>0，整个闭区间都在正半轴，log 在其上连续并在内部可微。故存在位于 q 与 1 之间的 xi，使

\[
\log q-\log1=\frac{q-1}{\xi}.
\]

又 xi≥c>0、log1=0，所以

\[
|\log q|=\frac{|q-1|}{\xi}
\le\frac{|q-1|}{c}
\le\frac{C_{\log}}{H^2}. \tag{7}
\]

q=1 时同一个结论也成立。于是对全部 m≥1，已经内部证明

\[
\boxed{\displaystyle
\left|\log\frac{\pi a(m)}4\right|
\le\frac{C_{\log}}{H(m)^2},\qquad C_{\log}>0.} \tag{8}
\]

这里没有仅在充分大 m 时使用 q 接近 1 的论证；统一正下界 (5) 直接覆盖全部 m≥1。尤其没有把 C_log 加为自由输入，没有增加阈值 H0，也没有消费 C_tan。

## 4. 精确位移恒等式与全域二阶余项

继续使用第 2 节由固定胞元得到的 h、H、delta。定义

\[
D=\frac1{h^2}-\frac1{H^2}-\frac{2\delta}{h^3}.
\]

因 h>0、H>0，通分合法。先利用 H−h=delta，随后利用 H=h+delta，逐步得到

\[
\begin{aligned}
D
&=\frac{h(H^2-h^2)-2\delta H^2}{h^3H^2}\\
&=\frac{\delta\{h(H+h)-2H^2\}}{h^3H^2}\\
&=-\frac{\delta^2(3h+2\delta)}{h^3H^2}.
\end{aligned} \tag{9}
\]

为核对最后一步，把 H=h+delta 代入花括号即可得到

\[
h(2h+\delta)-2(h+\delta)^2=-3h\delta-2\delta^2.
\]

分母和 3h+2delta 均严格为正，故 (9) 给出

\[
|D|=\frac{\delta^2(3h+2\delta)}{h^3H^2}.
\]

所需统一估计直接来自代数：

\[
3H^2-h(3h+2\delta)
=3(h+\delta)^2-h(3h+2\delta)
=4h\delta+3\delta^2\ge0.
\]

两边除以正的 h⁴H² 并乘以 delta²≥0，可得

\[
|D|\le\frac{3\delta^2}{h^4}\le\frac3{h^4}. \tag{10}
\]

最后一步使用 0<delta≤1。式 (9) 还固定了残差的符号，故没有在估计中改变领先位移项的方向或系数。整个论证只用实际 H=m+1、delta=H−h 所满足的恒等式；它们始终不是新的自由输入。

## 5. 选定绝对常数并闭合 DA1

在尚未选取 m、h、n 之前，使用先前固定的上游常数与式 (4)，一次性定义

\[
A=C_{\rm rho}+3\lambda,\qquad B=C_{\log},
\qquad C=A+B
=C_{\rm rho}+\frac{3\pi^2}{8}
 +\frac{\pi C_a}{4\cos(\pi/8)}. \tag{11}
\]

C_rho>0、lambda>0、C_log>0，所以 A>0、B>0、C>0。这些常数只来自固定 Scalar 接口与数值常量 π，与 m、h、n、delta 以及任何序列或尺度常数无关。

现在任取目标量词范围中的 m、h、n，令 N=(n:ℝ)≥0。将 (2) 左边绝对值内部的表达式记作 E。通过加减 lambda N/H²，有精确分解

\[
\begin{aligned}
E
&=N\left(\log\rho+\frac\lambda{H^2}\right)
 +\lambda N\left(\frac1{h^2}-\frac1{H^2}
                    -\frac{2\delta}{h^3}\right)
 +\log\frac{\pi a}{4}\\
&=N\left(\log\rho+\frac\lambda{H^2}\right)
 +\lambda N D+\log\frac{\pi a}{4}.
\end{aligned} \tag{12}
\]

三角不等式、N≥0、lambda>0、SCA2 即 (1)、内部对数界 (8)、位移界 (10) 依次给出

\[
|E|
\le\frac{C_{\rm rho}N}{H^4}
  +\frac{3\lambda N}{h^4}
  +\frac{C_{\log}}{H^2}. \tag{13}
\]

因为 H>h>0，有 H⁴≥h⁴>0，因此 1/H⁴≤1/h⁴。乘以非负 C_rho N 后，式 (13) 推出

\[
|E|\le A\frac N{h^4}+B\frac1{H^2}.
\]

记 X=N/h⁴≥0、Y=1/H²>0，则

\[
(A+B)(X+Y)-(AX+BY)=AY+BX\ge0.
\]

故 |E|≤C(X+Y)。将 X、Y、C、E、delta 的定义代回，正是

\[
\boxed{\displaystyle
\left|
\frac{\pi^2}{8}\frac{(n:\mathbb R)}{h^2}
 +(n:\mathbb R)\log\rho(m)
 +\log\frac{\pi a(m)}4
 -\frac{\pi^2}{4}\frac{(n:\mathbb R)}{h^3}(H(m)-h)
\right|
\le C\left(\frac{(n:\mathbb R)}{h^4}
                   +\frac1{H(m)^2}\right).} \tag{14}
\]

常数 (11) 在 m、h、n 之前选定，因而证明了冻结的完整存在—全称量词顺序。

## 6. 边界逐项核对与证明范围

- m=1 时，H=2、h∈[1,2)、u=π/8；(5) 在 u 的右端仍成立。delta=2−h∈(0,1]，所有估计照用。
- m=2 时，H=3、h∈[2,3)、u=π/12；同样位于全部已证明区间，没有例外分支。
- 对任意 m≥1，h=m 时 delta=1。式 (9)、(10)、(12) 不要求 delta<1，完整保留弱事件的整数端点。
- h 的域始终是 [m,m+1)，未加入 h=m+1 或 delta=0，也未改用 strict 事件。
- n=0 时 N=0，E=log(πa/4)；(8) 给出 |E|≤B/H²≤C/H²。证明没有除以 N、没有假设 n>0。
- 证明不要求 h 趋于无穷、不要求 m 充分大、不要求 H≥H0，也不需要 n/h³ 有界或其他尺度条件。
- 主要误差仍为 N/h⁴+H⁻²，领先位移系数仍为 π²/4；没有把这两个误差阶或残差符号换成别的声明。

新增引理 (8)、(9)、(10) 均在本文证明。唯一项目数学依赖为固定 SCA0、SCA1、SCA2；基础使用是实数有序域运算、三角函数的基本符号及导数、实对数的导数和中值定理。没有未证明的 Taylor 输入，没有自由替代函数或新原始来源叶。

至此得到完整数学证明，状态为 PROOF_READY / MATH_ONLY，供全新独立数学审查。未执行 Lean，未读取实现或其他匿名数学稿及审查；不据此声称形式认证、canonical 写入、DA2 或实际 S3/S4 概率结论。
