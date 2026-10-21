# 真实 Rademacher 迭代核的整数网格支持与主余弦有限幂

STATUS: PROVED
FROZEN_VERSION: frozen-rademacher-iteration-v1.md
FROZEN_SHA256: 15851002ccadaa118035107c8b9b8266dd825fdebdf36728f3ac7a97f7330b80
SPECTRUM_STATUS: OPEN
ROOT_STATUS: OPEN

本文证明冻结 v1 的全部有限结论。这里的 PROVED 表示给出完整数学证明，不表示已经通过独立审稿或新的 Lean 核验。所有核、积分和作用均绑定已有实际对象；下文的简记不定义替代核。

## 1. 对象、假设和使用的已认证接口

固定自然数 m≥1、实数 h 满足 m≤h<m+1，并固定整数 r 满足 −m≤r≤m。整数或自然数出现在实数表达式中时均使用实际的标准嵌入。令

\[
H=m+1,\qquad a=\frac{\pi}{2H},\qquad \rho=\cos a,
\qquad f(w)=\cos(aw).
\]

这些分别是 `RademacherCosine.angle m`、`RademacherCosine.rho m` 和冻结的主余弦函数。实际增量律是

\[
\nu_R=\texttt{RademacherCosine.law}
 =\tfrac12\delta_1+\tfrac12\delta_{-1},
\]

其中实际测度标量为 `halfENNReal = (1 / 2 : ENNReal)`，不是对被杀死后的行作归一化。已有实例 `RademacherCosine.law_isProbabilityMeasure` 提供 ν_R 的概率性。

记

\[
K=\texttt{killedKernel}\ \nu_R\ h,
\qquad
L_n=\texttt{killedIterKernel}\ \nu_R\ h\ n,
\qquad
\mu_{n,z}=L_n(z).
\]

透明定义和实际核接口为

\[
K(z)=\bigl(\nu_R.\operatorname{map}(y\mapsto z+y)\bigr)
           \big|_{[-h,h]},\qquad
L_n=K^n,
\tag{1}
\]

以及

\[
\texttt{killedAction}\ \nu_R\ h\ n\ u\ z
       =\int u(w)\,d\mu_{n,z}(w).
\tag{2}
\]

式 (1) 的第一项是 `killedKernel_apply`，第二项就是 `killedIterKernel` 的定义；式 (2) 就是 `killedAction` 的定义。限制的是下一位置，不预先杀死起点。

以下已认证接口按其实际陈述使用，不重新证明其已认证有限律。

* `RademacherCosine.integer_closed_iff m h hmh hhm s`：对每个整数 s，在 `hmh : (m : ℝ) ≤ h` 和 `hhm : h < (m : ℝ) + 1` 下，
  \[
  |(s:\mathbb R)|\le h\quad\Longleftrightarrow\quad
             |s|\le(m:\mathbb Z).
  \tag{3}
  \]
* `RademacherCosine.killedKernel_row m h hmh hhm s`：对每个整数 s，
  \[
  K((s:\mathbb R))
   =\begin{cases}\tfrac12\delta_{(s+1:\mathbb R)},&|s+1|\le m,\\0,&\text{否则}\end{cases}
    +\begin{cases}\tfrac12\delta_{(s-1:\mathbb R)},&|s-1|\le m,\\0,&\text{否则}.\end{cases}
  \tag{4}
  \]
  两个判断均在整数上进行。
* `RademacherCosine.killedKernel_integral_principal m hm h hmh hhm s hslo hshi`：在 `hm : 1 ≤ m` 和整数边界 `hslo : −(m : ℤ) ≤ s`、`hshi : s ≤ (m : ℤ)` 下，
  \[
  \int f(v)\,dK((s:\mathbb R))(v)=\rho f((s:\mathbb R)).
  \tag{5}
  \]
  这就是 PR72 的实际主一步对。它只在上述整数状态上使用。
* `killedIterKernel_zero ν_R h z` 给出 `L₀(z)=δ_z`。`killedIterKernel_mass_le_one ν_R h n z` 给出 `μ_{n,z}(ℝ)≤1`；已有 `killedIterKernel_isFiniteKernel` 实例因而适用。`killedKernel_mass_le_one ν_R h z` 同样给出 `K(z)(ℝ)≤1`。
* `killedAction_integrable ν_R h n z u hu hub`：若 u 可测且在整个实线上有常数绝对值上界，则 u 对 μ_{n,z} 真正可积。`killedAction_measurable` 提供作用后的可测性；`killedAction_iterated_integrable ν_R h p q z u hu hub` 提供 `killedAction ν_R h q u` 对 μ_{p,z} 的可积性。
* `killedAction_semigroup ν_R h p q z u hu hub`：在相同可测、有界条件下，
  \[
  \texttt{killedAction}\ \nu_R\ h\ (p+q)\ u\ z
  =\texttt{killedAction}\ \nu_R\ h\ p\
       (\texttt{killedAction}\ \nu_R\ h\ q\ u)\ z.
  \tag{6}
  \]

所用实际项目模块的认证源指纹为：`RademacherCosine.lean` 的 SHA256 是 `c0ba478f9ed6b5aa75d7010d70835b37065a92e9878c65b086d3c3ff24e7f861`；`KilledKernel.lean` 是 `f90c1996f4c220473371b0f5ea3c74a7b8287e8f997f1a2cd3f0831cd6bd626f`；`KilledIteration.lean` 是 `03b97e5708ffa552cfa4eccec5cf3c042da9805f9ab69561f4cb3e2701a690b5`。这里只调用上述声明和透明定义，不依赖其他待审实现。

## 2. 实际有限整数状态集

定义冻结的集合

\[
I_m=\{s\in\mathbb Z:-m\le s\le m\},\qquad
G_m=\{(s:\mathbb R):s\in I_m\}.
\tag{7}
\]

整数闭区间 I_m 有限：平移 s↦s+m 将它一一对应到整数 0,1,…,2m。因此 G_m 是有限集合在实际整数到实数嵌入下的像，有限。更具体地，

\[
G_m=\bigcup_{s\in I_m}\{(s:\mathbb R)\}.
\]

每个实数单点集闭且 Borel 可测，有限并仍 Borel 可测。所以 G_m 和它的补集 A:=ℝ\G_m 都是 Borel 集。这里没有用实区间 [−h,h] 替换整数网格。

由 (3)，每个实整数点 w=(s:ℝ) 满足

\[
w\in[-h,h]\quad\Longleftrightarrow\quad s\in I_m.
\tag{8}
\]

不过，(8) 本身还不足以证明迭代核的整数性；该部分由下面的一步原子行和真实核组合给出。

## 3. 一步核在网格上的支持

先证明对每个 w∈G_m 都有

\[
K(w)(A)=0.
\tag{9}
\]

取 (7) 给出的整数 s∈I_m，使 w=(s:ℝ)。应用实际行公式 (4)。对于其中的 `+1` 项，有两种且仅有两种情况。

若 |s+1|≤m，则 −m≤s+1≤m，所以 (s+1:ℝ)∈G_m，因而不在 A 中。该项在 A 上的质量为 `(1/2)δ_{(s+1:ℝ)}(A)=0`。若 |s+1|≤m 不成立，该项就是零测度，在 A 上同样为零。

对 `−1` 项也逐项判断：若 |s−1|≤m，则 −m≤s−1≤m，其原子位置 (s−1:ℝ) 属于 G_m，在 A 上的 Dirac 质量为零；若判断不成立，该项是零测度。将这两个零质量相加便得 (9)。此处每个被保留的原子都来自实际 `killedKernel`；没有引入有限矩阵或重新分配被杀掉的质量。

## 4. 真实迭代核的组合及所有步数的网格支持

我们现在证明，对每个 n∈ℕ（包括 n=0），

\[
\mu_{n,(r:\mathbb R)}(A)=0.
\tag{10}
\]

先明确本归纳所用的是实际核的组合。由 (1) 的实际定义 `L_n=K^n` 和核幺半群中的幂恒等式，

\[
L_{n+1}=K\circ_k L_n.
\tag{11}
\]

这里 `∘ₖ` 就是原有的核复合：Mathlib 的实际接口 `Kernel.comp_apply K L_n z` 是

\[
(K\circ_k L_n)(z)=(L_n(z)).\operatorname{bind}K.
\]

前述实际核及迭代核的有限核实例满足这里核复合接口所需的有限性条件。因此，对任意 Borel 集 B，真实核满足

\[
\mu_{n+1,z}(B)=\int_{\mathbb R}^{-}K(w)(B)\,d\mu_{n,z}(w).
\tag{12}
\]

式 (12) 是已有核复合的测度求值公式，不是给另一对象另设的递推。也可把可测函数 `1_B : ℝ → ENNReal` 代入实际 `Kernel.lintegral_comp K L_n z` 得到同一公式。由于 K 是实际可测核，B Borel，w↦K(w)(B) 是可测的非负扩展实值函数，故 (12) 的非负积分始终有定义；这里不需正质量或除以质量。

归纳的零步：已认证 `killedIterKernel_zero` 给出

\[
\mu_{0,(r:\mathbb R)}=\delta_{(r:\mathbb R)}.
\]

冻结保留的起点条件 −m≤r≤m 确保 (r:ℝ)∈G_m，故该 Dirac 在 A 上的质量为零。这证明 (10) 在 n=0 成立。零步并没有先对起点执行杀死；如果移除起点属于 I_m 的条件，区间外起点的零步 Dirac 一般不会满足 (10)。

归纳步：假设 (10) 对 n 成立。失败集合正是 A，故该假设等价于

\[
w\in G_m\quad\text{对 }\mu_{n,(r:\mathbb R)}\text{ 几乎处处成立}.
\]

在每个这样的 w 上，(9) 给出 K(w)(A)=0。因此可测非负函数 w↦K(w)(A) 对 μ_{n,(r:ℝ)} 几乎处处为零。它的非负积分为零，将 B=A、z=(r:ℝ) 代入 (12)，得到

\[
\mu_{n+1,(r:\mathbb R)}(A)
 =\int^{-}K(w)(A)\,d\mu_{n,(r:\mathbb R)}(w)=0.
\]

归纳完成，(10) 对每个自然数 n 成立。因为 A 是 G_m 的补集，(10) 同时就是冻结要求的实际支持结论

\[
\forall^{\mu_{n,(r:\mathbb R)}}_{\mathrm{a.e.}}w,\quad w\in G_m.
\tag{13}
\]

它同时证明了整数性和有限边界；仅有 |w|≤h 的连续区间支持不能替代这里的 (13)。

## 5. 每个实际迭代核下的真正可积性

函数 f(w)=cos(aw) 连续，所以 Borel 可测，而且对所有实数 w 都有 |f(w)|≤1。已认证的质量上界给出 μ_{n,z}(ℝ)≤1，从而 μ_{n,z} 是有限测度。于是

\[
\int |f(w)|\,d\mu_{n,z}(w)
 \le\int1\,d\mu_{n,z}
 =\mu_{n,z}(\mathbb R)^{\mathrm{toReal}}\le1.
\tag{14}
\]

这里先由有限测度上常函数 1 的可积性，以及 f 可测、|f|≤1，应用支配可积性定理得到 f 真正可积，再使用通常积分的单调性得到 (14)。这也精确满足 `killedAction_integrable ν_R h n z f` 的可测与全局有界两个输入。特别地，对冻结的每个 n 和 z=(r:ℝ)，目标中的积分是通常的可积实函数积分，不是不可积时的默认值。

后面还要积分一步作用后的函数。令

\[
g(w)=\int f(v)\,dK(w)(v).
\tag{15}
\]

因为 L₁=K，(2) 将它精确识别为

\[
g=\texttt{killedAction}\ \nu_R\ h\ 1\ f.
\tag{16}
\]

`killedAction_measurable` 以 f 的可测性给出 g 可测。对每个 w，K(w)(ℝ)≤1，故 f 对 K(w) 可积，并有

\[
|g(w)|\le\int|f(v)|\,dK(w)(v)
          \le K(w)(\mathbb R)^{\mathrm{toReal}}\le1.
\tag{17}
\]

所以 g 对每个有限测度 μ_{n,z} 也可积；这也由 `killedAction_iterated_integrable ν_R h n 1 z f` 直接提供。常数倍 ρf 同样对 μ_{n,z} 可积。由此，接下来使用积分的几乎处处替换、线性和半群身份时，所有有关实函数均有实际可积性。

## 6. 支持如何允许合法地迭代主一步对

在每个 w∈G_m 上，取 s∈I_m、w=(s:ℝ)。冻结的 m≥1、m≤h<m+1 和 s 的两个整数边界，正好给出 (5) 的所有输入。于是，利用 (15)，

\[
g(w)=\rho f(w)\qquad(w\in G_m).
\tag{18}
\]

这一步没有在任意实数 w∈[−h,h] 上声称特征函数身份。它只在 G_m 上由实际整数主对推出。由已经单独证明的 (13)，(18) 对每个 μ_{n,(r:ℝ)} 几乎处处成立。因此，利用第 5 节的可积性，

\[
\int g(w)\,d\mu_{n,(r:\mathbb R)}(w)
 =\int\rho f(w)\,d\mu_{n,(r:\mathbb R)}(w)
 =\rho\int f(w)\,d\mu_{n,(r:\mathbb R)}(w).
\tag{19}
\]

为把 (19) 的左边绑定到下一步的实际积分，记

\[
J_n=\int f(w)\,d\mu_{n,(r:\mathbb R)}(w)
    =\texttt{killedAction}\ \nu_R\ h\ n\ f\ (r:\mathbb R).
\]

这是实际积分的记号。将 p=n、q=1、z=(r:ℝ)、u=f 代入已经认证的真实半群公式 (6)。f 的可测性及全局界 |f|≤1 已在第 5 节验证，故该公式确实适用。再用 (16) 和 (2)，得到

\[
\begin{aligned}
J_{n+1}
 &=\texttt{killedAction}\ \nu_R\ h\ (n+1)\ f\ (r:\mathbb R)\\
 &=\texttt{killedAction}\ \nu_R\ h\ n\
       (\texttt{killedAction}\ \nu_R\ h\ 1\ f)\ (r:\mathbb R)\\
 &=\int g(w)\,d\mu_{n,(r:\mathbb R)}(w)\\
 &=\rho J_n.
\end{aligned}
\tag{20}
\]

式 (20) 的每一项都是已有 `killedAction` 或其定义给出的真实核积分。关键的第四个等号正是支持 (13)、整数一步身份 (18) 和可积性共同保证的 (19)，并非将一步身份延伸到全实数后形式套用递推。

## 7. 精确有限幂、零步和起点零的对应式

首先，由实际零步 Dirac 及 f 的可测性，

\[
J_0=\int f(w)\,d\delta_{(r:\mathbb R)}(w)
    =f((r:\mathbb R))
    =\rho^0 f((r:\mathbb R)).
\tag{21}
\]

对自然数 n 归纳。若 J_n=ρⁿf((r:ℝ))，则由 (20) 和通常的自然数幂恒等式，

\[
J_{n+1}=\rho J_n
 =\rho\bigl(\rho^n f((r:\mathbb R))\bigr)
 =\rho^{n+1}f((r:\mathbb R)).
\]

结合 (21)，对所有 n∈ℕ 得到冻结要求的精确等式

\[
\boxed{\displaystyle
\int_{\mathbb R}\cos(aw)\,
  d\bigl(\texttt{killedIterKernel}\ \nu_R\ h\ n\ (r:\mathbb R)\bigr)(w)
 =\rho^n\cos\bigl(a(r:\mathbb R)\bigr).}
\tag{22}
\]

等价的现有作用形式为

\[
\texttt{killedAction}\ \nu_R\ h\ n\
    (w\mapsto\cos(aw))\ (r:\mathbb R)
 =\rho^n\cos\bigl(a(r:\mathbb R)\bigr).
\tag{23}
\]

当 r=0 时，它满足两个整数边界，且 cos(0)=1，故 (22) 的右边就是 ρⁿ。当 n=0 时，(22) 恢复起点 Dirac 的积分；没有遗漏零步，也没有长时间前提。已有 `rho_pos m hm` 与 `rho_lt_one m hm` 说明 0<ρ<1，但本归纳没有除以 ρ、没有取对数，也没有使用任何趋近或极限论证。

## 8. 边界、退化质量与结论范围

当 h=m 时，位置 ±m 满足弱闭条件 |±m|≤h，仍在 G_m 内；位置 ±(m+1) 因 h<m+1 被杀死。因此实际吸收位置是 ±H，不能把它们改成 ±h。式 (4) 对该端点仍完全成立。例如从 r=m 出发，m+1 的原子被杀死，而 m−1∈I_m（这里用 m≥1），所以 K(m) 在全空间上的质量为 1/2。没有将剩余的一半重新归一化成概率一；这也直接说明本证明没有假定每个被杀死后的行或迭代测度总质量都为一。

所有论证均允许有限次概率测度的总质量下降。若某个相关测度为零，其对补集的质量仍为零、几乎处处命题仍成立、可积性与积分替换仍按同一测度定义成立；证明中没有正生存质量或条件化所需的除法。冻结的整数起点条件在零步得到明确使用，正步的支持来自实际核的组合，而非只来自连续区间支持。

本证明只处理整数起点所在的 coset ℤ，以及 m≥1 的正主余弦。对于非整数起点，增量仍为 ±1，但位置属于另一实数平移 coset，不能将其直接识别成 (7) 的网格，也不能在其上调用 (5) 或套用本频率。m=0 的独立零生存分支也没有在这里处理。

式 (22) 是余弦加权积分，不是单位函数的积分。它没有给出无权生存概率的完整公式，没有证明所有正弦模态、零或负特征值、正交性、完备性、单位函数展开、cot 有限和或奇偶负谱项；也没有导出 4/π 系数、完整 S1–S4、其他 coset 的完整核谱或 OQ4 根结论。这些在本叶后仍保持 OPEN。这里对正主模态 n=0 的处理，不授权在未来包含零特征值的完整谱公式中删除任何零步项。

以上证明未改变冻结的律、闭事件、起点类、整数边界或全体自然数步数量词。全部有限结论已经由实际核的网格支持、可积性与主余弦精确有限幂身份给出。
