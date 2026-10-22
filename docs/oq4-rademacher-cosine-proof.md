# 真实 Rademacher 弱闭一步主余弦特征对

STATUS: PROVED
FORMAL_STATUS: MATH_ONLY_NOT_COMPILED
SPECTRUM_STATUS: OPEN
ROOT_STATUS: OPEN

本文只证明冻结 `frozen-rademacher-cosine-v1.md` 的一步有限结论。冻结文件 SHA256 为 `9532d25fa6027881db213374980ef4a7273f96c3166847855d655fd18703e91c`，长度为 4709 字节。原源 `oq4/c01/spectrum01.md` 的 SHA256 为 `b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b`；本文所对应的是原 11–21 行中主余弦向量的一步递推这一严格弱组件。本稿未执行 Lean、服务器命令或数值枚举，`PROVED` 仅表示下述数学证明完成，仍待独立审查。

## 1. 固定对象及概率性

取冻结的任意参数

\[
m\in\mathbb N,\quad 1\le m,\quad h\in\mathbb R,\quad
q:=(m:\mathbb R)\le h<q+1,
\]
\[
M:=(m:\mathbb Z),\quad r\in\mathbb Z,\quad -M\le r\le M.
\]

这里 \(q,M\) 只是同一个 \(m\) 的两种数系嵌入，不是新的参数。记

\[
H=q+1,\qquad a=\frac{\pi}{2H},\qquad \rho=\cos a,
\qquad b=(1/2:\mathbb R_{\ge0}^{\infty}).
\]

在实数 Borel 空间上，令 \(\delta_t\) 为点 \(t\) 处的 Dirac 测度，并使用冻结的实际增量测度

\[
\nu_R=b\,\delta_1+b\,\delta_{-1}.
\tag{1}
\]

本文中 `halfENNReal` 仅是非负扩展实数透明记号 \(b=(1/2:\mathbb R_{\ge0}^{\infty})\)，不是新增的概率性前提。它满足 \(b<\infty\)、\(b+b=1\) 及 \(b.\mathrm{toReal}=1/2\)。对两个 Dirac 测度，\(\delta_1(\mathbb R)=\delta_{-1}(\mathbb R)=1\)，所以

\[
\nu_R(\mathbb R)=b\cdot1+b\cdot1=1.
\tag{2}
\]

因此实际的 \(\nu_R\) 是概率测度。后文所有要求 `IsProbabilityMeasure ν_R` 的实际接口，都在这里得到其条件；没有把该条件另行假设。

令

\[
C=[-h,h],\qquad z=(r:\mathbb R),\qquad
\kappa_r=\operatorname{killedKernel}\nu_R\,h\,z.
\]

使用的实际定义是平移增量测度后限制到闭区间：

\[
\kappa_r=((T_z)_*\nu_R)|_C,\qquad T_z(y)=z+y.
\tag{3}
\]

这正是 `killedKernel_apply`，不是归一化的条件存活核。

## 2. 整数状态的弱闭条件

先证明一个适用于每个整数 \(s\) 的等价式：

\[
|(s:\mathbb R)|\le h
\quad\Longleftrightarrow\quad |s|\le M.
\tag{4}
\]

若 \(|s|\le M\)，整数到实数的嵌入保序且与绝对值相容，故
\(|(s:\mathbb R)|\le q\le h\)。反之，若 \(|(s:\mathbb R)|\le h\) 而 \(|s|>M\)，则 \(\lvert s\rvert,M\) 都是整数，因而 \(|s|\ge M+1\)。嵌入实数后得到

\[
q+1\le |(s:\mathbb R)|\le h<q+1,
\]

矛盾。这证明了 (4)。等价式没有用到 \(r\) 的范围；尤其可以分别取 \(s=r+1\) 和 \(s=r-1\)。

又由绝对值的闭区间刻画，\((s:\mathbb R)\in C\) 等价于 \(|(s:\mathbb R)|\le h\)。因此 (4) 精确地把实际核的实闭条件转为冻结的整数条件，包括 \(h=q\) 时的原子边界。

## 3. 实际二点行测度

平移 \(T_z\) 连续，因而 Borel 可测。由推前的定义，对每个 Borel 集 \(A\)，

\[
((T_z)_*\nu_R)(A)
=b\,\mathbf1_A(z+1)+b\,\mathbf1_A(z-1).
\]

也就是说，作为 Borel 测度有

\[
(T_z)_*\nu_R=b\,\delta_{z+1}+b\,\delta_{z-1}.
\tag{5}
\]

限制 Dirac 测度时，直接在每个 Borel 集 \(A\) 上计算

\[
(\delta_t|_C)(A)=\delta_t(A\cap C)
=\begin{cases}\delta_t(A),&t\in C,\\0,&t\notin C.\end{cases}
\]

限制与两个测度的和及有限非负数乘相容，因此 (3)–(5)、(4) 及整数嵌入与加减法相容给出实际行等式

\[
\boxed{
\kappa_r=
\begin{cases}b\,\delta_{((r+1:\mathbb Z):\mathbb R)},&|r+1|\le M,\\0,&|r+1|>M\end{cases}
+
\begin{cases}b\,\delta_{((r-1:\mathbb Z):\mathbb R)},&|r-1|\le M,\\0,&|r-1|>M.\end{cases}}
\tag{6}
\]

这里各个 \(0\) 都是零测度，两个条件均为整数中的条件。公式 (6) 是测度等式，不只是两个支点上的函数等式。每个被排除的原子直接变成零测度，未把其质量加回其余支点。

## 4. 真正可积性及实际积分接口

设

\[
f(w)=\cos(aw),\qquad
g(y)=\begin{cases}\cos(a(z+y)),&|z+y|\le h,\\0,&|z+y|>h.\end{cases}
\tag{7}
\]

函数 \(f\) 连续，故 Borel 可测，且每个 \(w\) 都满足 \(|f(w)|\le1\)。集合 \(\{y:|z+y|\le h\}\) 是连续函数的闭子水平集，故 Borel 可测；于是 \(g\) Borel 可测并且 \(|g(y)|\le1\)。

在第 1 节已经建立 \(\nu_R\) 的概率性之后，可将实际接口 `killedKernel_integral_bounded` 用于参数 \((\nu_R,h,z,f)\)，其可测性条件由 \(f\) 连续满足，其有界性条件取 \(1\)。该接口同时供应

\[
f\in L^1(\kappa_r),\qquad g\in L^1(\nu_R),
\tag{8}
\]

和真实的 Bochner 实积分等式

\[
\int_{\mathbb R}f(w)\,d\kappa_r(w)
=\int_{\mathbb R}g(y)\,d\nu_R(y)
=\operatorname{Kcos}\nu_R\,a\,h\,z.
\tag{9}
\]

特别地，(8) 中的可积性并非借助不可积函数的默认积分值。也可从实际 `killedKernel_mass_le_one` 得 \(\kappa_r(\mathbb R)\le1\)，再用可测性和 \(|f|\le1\) 得到左侧可积性；\(\nu_R(\mathbb R)=1\) 和 \(|g|\le1\) 同样给出右侧可积性。实数值的 Borel 可测函数在此是强可测的，且其范数积分由有限质量所控制。

为了计算右侧，使用 (1) 的二点积分规则。具体而言，\(g\) 对 \(\delta_{1}\)、\(\delta_{-1}\) 及其有限倍 \(b\delta_{1}\)、\(b\delta_{-1}\) 都可积，因为这些测度有限且 \(|g|\le1\)。因此积分对两个测度相加的规则、有限非负数乘规则及 Dirac 积分规则均适用；并且 \(b.\mathrm{toReal}=1/2\)。从而

\[
\operatorname{Kcos}\nu_R\,a\,h\,z
=\frac12 g(1)+\frac12 g(-1).
\tag{10}
\]

没有在这一计算中交换无限求和、极限或积分。

## 5. 被杀项恰在主余弦的零点

由 \(-M\le r\le M\) 有 \(|r|\le M\)。对 \(s=r+1\) 或 \(s=r-1\)，整数绝对值的三角不等式给出

\[
|s|\le |r|+1\le M+1.
\tag{11}
\]

如果这样的 \(s\) 不在整数存活域，即 \(|s|>M\)，则 (11) 和整数性共同推出

\[
|s|=M+1,\qquad |(s:\mathbb R)|=H.
\tag{12}
\]

因此一步出界时不会越过 \(\pm H\) 再落到别的格点。

另一方面，\(q\ge1\) 蕴含 \(H\ge2>0\)，所以由 \(a\) 的实际定义得到

\[
aH=\frac\pi2.
\tag{13}
\]

利用余弦的偶性，如果 (12) 成立，那么

\[
\cos(a(s:\mathbb R))
=\cos(a|(s:\mathbb R)|)
=\cos(aH)=\cos(\pi/2)=0.
\tag{14}
\]

这里第一步可按 \((s:\mathbb R)\) 非负或非正两种情形直接展开绝对值，再应用 \(\cos(-u)=\cos u\)；它不需要非格点或无原子条件。

现在分别对 \(s=r+1\) 和 \(s=r-1\) 应用 (4)：若 \(|s|\le M\)，(7) 中相应的项保留其余弦值；若 \(|s|>M\)，被杀项为零，而未截断的余弦值也由 (14) 为零。故在两种情形都成立

\[
g(1)=\cos(a(z+1)),\qquad g(-1)=\cos(a(z-1)).
\tag{15}
\]

(15) 仅是冻结整数起点及其两个实际可达点上的结论；不是对任意实起点的被杀项恒等式。

## 6. 实际主特征对与参数范围

令 \(x=az\)。将 (15) 代入 (10)，再使用实数乘法分配律与余弦加减公式，得到

\[
\begin{aligned}
\operatorname{Kcos}\nu_R\,a\,h\,z
&=\frac12\bigl(\cos(x+a)+\cos(x-a)\bigr)\\
&=\frac12\bigl((\cos x\cos a-\sin x\sin a)
 +(\cos x\cos a+\sin x\sin a)\bigr)\\
&=\cos a\cos x
=\rho\cos(az).
\end{aligned}
\tag{16}
\]

由实际接口 `killedKernel_integral_cos`，其条件只有已建立的 \(\nu_R\) 概率性，而 \(a,h,z\) 均可为任意实数，故 (16) 给出

\[
\boxed{
\int_{\mathbb R}\cos(aw)\,
 d(\operatorname{killedKernel}\nu_R\,h\,(r:\mathbb R))(w)
=\rho\cos(a(r:\mathbb R)).}
\tag{17}
\]

同一等式也已经由 (9) 直接连接到 (16)；真实可积性是第 4 节单独供应的 (8)。因此 (16)–(17) 的主对象始终是实际被杀闭核，并未用一个自由余弦系数的身份替代它。

最后，由 \(\pi>0\) 和 \(H\ge2\)，

\[
0<a=\frac\pi{2H}\le\frac\pi4<\frac\pi2.
\tag{18}
\]

余弦在 \((-\pi/2,\pi/2)\) 内严格为正，故 \(\rho>0\)。又 \(0<a<\pi/2<\pi\)，所以 \(0,a\) 均属于 \([0,\pi]\)，且 \(0<a\)。余弦在该区间严格递减，故 \(\rho=\cos a<\cos0=1\)。综上

\[
\boxed{0<a<\pi/2,\qquad 0<\rho<1.}
\tag{19}
\]

这只是此冻结一步特征对的参数事实。

## 7. 边界覆盖

以下核行均直接来自 (6)，并适用于全部 \(q\le h<q+1\)。为简洁，表内 Dirac 支点均按整数到实数的嵌入解释。

| 整数起点 | 向右一步 | 向左一步 | 实际核行 |
|---|---|---|---|
| \(r=M\) | \(M+1\) 被杀，余弦为零 | \(M-1\) 保留 | \(b\delta_{M-1}\) |
| \(r=-M\) | \(-M+1\) 保留 | \(-M-1\) 被杀，余弦为零 | \(b\delta_{-M+1}\) |
| \(r=M-1\) | \(M\) 保留 | \(M-2\) 保留 | \(b\delta_M+b\delta_{M-2}\) |
| \(r=-M+1\) | \(-M+2\) 保留 | \(-M\) 保留 | \(b\delta_{-M+2}+b\delta_{-M}\) |

表中 \(M\ge1\) 确保 \(M-1\) 与 \(-M+1\) 在存活域中，也确保 \(-M\le M-2\) 与 \(-M+2\le M\)。当 \(m=1\) 时，后两行是同一个起点 \(r=0\) 的同一二点行，两种写法均为 \(b\delta_1+b\delta_{-1}\)，没有重复相加。

对于其余整数起点 \(-M<r<M\)，整数性给 \(-M+1\le r\le M-1\)，于是两个邻点均在 \([-M,M]\) 内，实际行有两个各为 \(1/2\) 的原子。该论证与端点两行合在一起覆盖所有允许的正负整数起点。

特别在 \(h=q\) 时，\(\pm q\in[-h,h]\)，所以从 \(r=M-1\) 或 \(r=-M+1\) 到达 \(\pm M\) 的原子仍保留。这是弱闭边界；而 \(\pm H\) 由 \(h<H\) 总在域外。在 \(q<h<q+1\) 时，(4) 说明整行完全不变。被杀端点行的总质量是 \(b=1/2\)，其余行总质量是 \(b+b=1\)，清楚体现质量丢失。

冻结记录的严格事件/吸收 shift 区别只作范围说明：一般实 \(h\) 的弱事件对应 \(\lfloor h\rfloor+1\)，严格事件对应 \(\lceil h\rceil\)；整数 \(h\) 时相对 \(h\) 的 shift 分别为 \(+1\) 与 \(0\)。本文不证明或使用严格事件的结论，也没有把这两个整数化参数替换成对所有实 \(h\) 固定的两个实 shift。

## 8. 依赖与条件核对

下表中 `KNOWN` 表示已经读取的实际接口或所列基础数学规则；这里没有宣称新增 Lean 代码已编译。`PROVED_HERE` 表示本文的显式推导。

| 状态 | 依赖或结论 | 本文中的条件核对 |
|---|---|---|
| KNOWN | Dirac、测度和与非负数乘的定义；\(b+b=1\)、\(b.\mathrm{toReal}=1/2\) | \(b=1/2<\infty\)，点 \(\pm1\) 属于实数 Borel 空间；用于 (2) 的是非负扩展实数质量，实积分才使用 `toReal`。 |
| KNOWN | `translationKernel_apply` 与 `killedKernel_apply` | 所需 \(\nu_R\) 概率性先由 (2) 建立；\(T_z\) 连续，\(C\) 为闭集，\(h,z\) 均为实数；用于 (3)。 |
| KNOWN | Dirac 推前及限制规则 | 在所有 Borel 集上于第 3 节逐点核验；无归一化、无隐含支撑前提。 |
| KNOWN | `killedKernel_integral_bounded`、`killedKernel_mass_le_one` | 概率性由 (2)；函数 \(f(w)=\cos(aw)\) 可测且逐点绝对值不超过 \(1\)；参数 \(h,z\) 无额外条件；供应 (8)–(9)。 |
| KNOWN | 积分对两个测度相加、有限数乘、Dirac 积分 | 第 4 节逐一给出 \(g\) 对两个 Dirac 测度及其有限倍的真实可积性；有限系数为 \(b\)，实值系数为 \(1/2\)；供应 (10)。 |
| KNOWN | `Kcos` 的真实定义；`killedKernel_integral_cos` | `KilledCosine.lean` 的定义正是 (7) 的 \(g\) 对 \(\nu_R\) 积分；后者接口只要求已建立的概率性，等式左侧正是 \(\kappa_r\) 的积分；用于 (9)、(17)。 |
| KNOWN | 整数离散序、嵌入保序并与绝对值及加减法相容 | 对整数 \(\lvert s\rvert,M\) 使用 \(\lvert s\rvert>M\Rightarrow \lvert s\rvert\ge M+1\)；在 (4)、(11)–(12) 明确应用，未对任意实数使用整数间隙。 |
| KNOWN | 余弦加减公式、偶性、\(\cos(\pi/2)=0\)、\(\pi>0\)、余弦在 \((-\pi/2,\pi/2)\) 正及在 \([0,\pi]\) 严格递减 | 加减公式对全部实数有效；\(aH=\pi/2\) 的分母非零由 \(H\ge2\) 保证；正性和严格递减的区间条件在 (18) 后逐一核对。 |
| PROVED_HERE | 实际 \(\nu_R\) 的概率性 | (1)–(2)。 |
| PROVED_HERE | 实际闭核二点行及整数条件等价 | (3)–(6)，包括 \(h=q\) 原子边界。 |
| PROVED_HERE | 主余弦的真实可积性 | (7)–(9)，没有增加可积性前提。 |
| PROVED_HERE | \(\operatorname{Kcos}\) 与真实核积分的主特征对 | (10)–(17)，关键是实际可达域外点的零值 (12)–(15)。 |
| PROVED_HERE | 冻结参数的严格范围 | (18)–(19)。 |

实际读取的两份接口文件为 `library/Shao/OQ4/KilledKernel.lean`（SHA256 `f90c1996f4c220473371b0f5ea3c74a7b8287e8f997f1a2cd3f0831cd6bd626f`）及 `library/Shao/OQ4/KilledCosine.lean`（SHA256 `054816685c54b0001d10063cabf445755e54bd33017289be6a0356a31a5b3de8`）。本文没有使用其他作者证明、迭代接口或完整谱结论。

没有加入对称性、概率性、无原子性、非格点性或非周期性作为新前提。没有放宽整数起点为任意实起点，也没有引入时间 \(n\)。本文不证明主函数迭代、生存质量渐近、完整有限谱和、负或零模态的排除、S1 完整式、S2–S4、Brownian 基准或原 OQ4 根结论；这些状态仍为 OPEN。冻结的一步有限命题没有剩余数学缺口，独立证明审查和后续 Lean 机械核验尚未进行。
