# 实际能量倾斜的有限路径身份：匿名数学证明 v1

作者产物状态：PROVED。独立数学门：PENDING。本文件不作独立审稿裁决，也不声称已经过 Lean 检查。

对应冻结陈述：`drafts/oq4/frozen-energy-path-law-v1.md`，SHA256 `dcc050f7c229bbe6410dd5b9562bc4f349d6466b2e82ceeb70956dae7e545899`。

## 1. 对象、前提与目标

固定实数上的概率测度 ν、任意自然数 n（允许 n=0）及实数 T、h、s，满足

\[
T\ge0,\qquad h\ge1,\qquad |s|\le T,\qquad
(x\mapsto x^2)\in L^1(\nu),\qquad \int x^2\,d\nu=1.
\]

以下所有空间与测度均取既有实现的实际对象，不引入替代路径律。记

\[
\begin{aligned}
P_n&=\operatorname{Shao.Path}(n)=\operatorname{Fin}(n)\to\mathbb R,\\
\Pi_n(\rho)&=\operatorname{Measure.pi}(i\mapsto\rho),\\
A&=\operatorname{Shao.closedStrip}(h)\subset P_n,\\
Q(a)&=\operatorname{Shao.energy}(a)=\sum_{i:\operatorname{Fin}(n)}a_i^2,\\
w(x)&=\operatorname{energyWeight}(h,s,x)
     =\mathbf1_{\{|x|\le2h\}}\exp(sx^2/h^2),\\
Z&=\operatorname{energyNormalizer}(\nu,h,s)=\int w\,d\nu,\\
\mu&=\operatorname{energyTiltedLaw}(\nu,h,s)
     =\nu.\operatorname{withDensity}\bigl(x\mapsto\operatorname{ofReal}(w(x)/Z)\bigr).
\end{aligned}
\]

这里 `ofReal` 是非负实数到扩展非负实数的嵌入；下面用于密度的实函数均先证明非负。`ρ.real E` 的含义是 `(ρ E).toReal`。

以 N 表示 n 在实数中的像。要证明实际函数

\[
\Phi(a)=\begin{cases}
\exp\bigl(s(Q(a)-N)/h^2\bigr),&a\in A,\\
0,&a\notin A
\end{cases}
\tag{1}
\]

非负且在 Π_n(ν) 下真正可积，并且

\[
\int\Phi\,d\Pi_n(\nu)
=\exp(-sN/h^2)\,Z^n\,(\Pi_n(\mu)).\operatorname{real}(A).
\tag{2}
\]

还要在第 7 节给出任意可测概率空间上的有限独立同分布样本的真正可积性及同一积分身份。

由 h≥1 得 h>0、h²>0。冻结的实际一维接口 `energyWeight_measurable`、`energyWeight_nonneg`、`energyWeight_le`、`energyWeight_integrable` 供应

\[
w\text{ 可测},\qquad 0\le w(x)\le e^{4T},\qquad w\in L^1(\nu).
\tag{3}
\]

调用 `energyWeight_integrable ν T h s hT hh0 hs` 时使用 hh0:h>0。由 `energyNormalizer_bounds`（或其已证推论 `energyTiltedLaw_normalizer_pos`）和冻结前提，

\[
0<\tfrac34e^{-4T}\le Z\le e^{4T}<\infty.
\tag{4}
\]

`energyTiltedLaw_isProbabilityMeasure ν T h s hT hh hs hSq hsecond` 供应这个实际 μ 的概率性。这里没有将 Z>0 或 μ 的概率性增加为前提。ν、μ 均为概率测度，所以它们的实际有限乘积 Π_n(ν)、Π_n(μ) 均为概率测度，因而有限且 σ 有限，包括 n=0。

## 2. 事件、能量和被积函数的可测性

共享 `Shao.measurable_energy` 说明 Q 可测；它也是实际有限平方和。共享 `measurableSet_shiftedClosedSurvival n h 0` 与 `shiftedClosedSurvival_eq_closedStrip n h hh0.le` 共同说明 A 可测。这一步直接调用已有弱闭事件桥，不改变事件或重开其义务。

因此 a↦exp(s(Q(a)−N)/h²) 可测，(1) 是它在可测集合 A 上的指示函数，故 Φ 可测。指数为正，事件外为零，所以对每条路径都有 Φ(a)≥0。

## 3. 真正可积性所需的全空间有限支配

先在不使用路径换测度公式的情况下证明 Φ 可积。若 a∈A，对每个 i 调用共享定理

`Shao.abs_coordinate_le_two_mul_of_mem_closedStrip a h ha i`，

得 |a_i|≤2h。由于 h>0，平方后得 a_i²≤4h²。结合共享 `Shao.energy_nonneg` 并对有限指标求和，得到

\[
0\le Q(a)\le4Nh^2,\qquad 0\le Q(a)/h^2\le4N.
\tag{5}
\]

这个推导在 n=0 时是空和不等式。令 q=Q(a)/h²。因为 q≥0、s≤|s|≤T 且 T≥0，

\[
sq\le Tq\le4TN.
\tag{6}
\]

令 C=exp(−sN/h²)>0，M=C exp(4TN)>0。两者都是有限实数。在 A 上用指数加法式和 (6) 得

\[
\Phi(a)=C\exp(sQ(a)/h^2)\le M.
\]

在 A 外 Φ=0，所以上述界成为全路径空间上的

\[
0\le\Phi(a)=|\Phi(a)|\le
\exp(-sN/h^2)\exp(4TN)=M.
\tag{7}
\]

Π_n(ν) 是概率测度，常数 M 真正可积；Φ 可测且由 M 支配，故 Φ∈L¹(Π_n(ν))。这已经独立支付了目标被积函数的真实可积性，没有使用原律上未截断的 exp(sx²/h²) 可积性，也没有先写一个可能不可积的实积分等式。

## 4. 从实际 withDensity 与实际有限 π 推出密度

为避免假定需要证明的路径密度，先从实际构造推导非负测试公式。定义实函数和扩展非负实函数

\[
r(x)=w(x)/Z,\qquad \widehat r(x)=\operatorname{ofReal}(r(x)),
\]

以及实际路径上的有限乘积

\[
d_m(a)=\prod_{i:\operatorname{Fin}(m)}r(a_i),\qquad
D_m(a)=\prod_{i:\operatorname{Fin}(m)}\widehat r(a_i)
\quad (a\in P_m).
\tag{8}
\]

由 (3)–(4)，r 可测，0≤r(x)≤B，其中 B=e^{4T}/Z 是有限正实数。有限个坐标评价映射可测，所以 d_m、D_m 可测，且

\[
0\le d_m(a)\le B^m<\infty,\qquad
D_m(a)=\operatorname{ofReal}(d_m(a)).
\tag{9}
\]

最后一个等式是 `ofReal` 对非负有限乘积的乘法性。空乘积为 1，故 m=0 同样成立。特别地，d_m 在实际概率测度 Π_m(ν) 下真正可积。

对每个 m 证明：任意可测 F:P_m→[0,∞] 都满足

\[
\int^- F(a)\,d\Pi_m(\mu)(a)
=\int^- F(a)D_m(a)\,d\Pi_m(\nu)(a).
\tag{10}
\]

这里所有积分都是非负无穷积分，允许测试函数取 ∞，所以归纳过程中不偷用实积分存在性。

**空指标情形。** P_0 只有空路径 e。实际空乘积测度 Π_0(ν)、Π_0(μ) 均是该单点上的概率测度，故对任何 F，其非负积分均为 F(e)。又 D_0(e)=1，所以 (10) 成立，包括 F(e)=∞ 的情形。

**归纳步。** 假设 (10) 对 m 成立。令

\[
c(x,b)=\operatorname{Fin.cons}(x,b)\in P_{m+1}
\qquad(x\in\mathbb R,\ b\in P_m).
\]

这是有限坐标插入的可测映射。有限乘积实际按首坐标和尾路径拆分；现有 `path_pi_lintegral_cons` 对概率基测度 ν 及 μ 都适用。对给定可测 F:P_{m+1}→[0,∞]，每个截面 b↦F(c(x,b)) 可测。归纳假设将实际 Π_m(μ) 截面积分改写为实际 Π_m(ν) 加权积分。函数

\[
H(x,b)=F(c(x,b))D_m(b)
\]

联合可测，而 Π_m(ν) 有限，故非负参数积分

\[
G(x)=\int^- H(x,b)\,d\Pi_m(\nu)(b)
\]

可测。这是非负参数积分可测性定理的直接应用，所有测度均 σ 有限。

由 μ 的实际定义 `ν.withDensity r̂`，可测非负 G 的一维换测度公式为

\[
\int^- G\,d\mu=\int^-G(x)\widehat r(x)\,d\nu(x).
\tag{11}
\]

于是逐步得到

\[
\begin{aligned}
\int^-F\,d\Pi_{m+1}(\mu)
&=\int^-_x\int^-_b F(c(x,b))\,d\Pi_m(\mu)(b)\,d\mu(x)\\
&=\int^-_x\int^-_b F(c(x,b))D_m(b)\,d\Pi_m(\nu)(b)\,d\mu(x)\\
&=\int^-_x\left(\int^-_b F(c(x,b))D_m(b)\,d\Pi_m(\nu)(b)\right)
       \widehat r(x)\,d\nu(x)\\
&=\int^-_x\int^-_b F(c(x,b))D_m(b)\widehat r(x)
       \,d\Pi_m(\nu)(b)\,d\nu(x)\\
&=\int^-_x\int^-_b F(c(x,b))D_{m+1}(c(x,b))
       \,d\Pi_m(\nu)(b)\,d\nu(x)\\
&=\int^-_a F(a)D_{m+1}(a)\,d\Pi_{m+1}(\nu)(a).
\end{aligned}
\tag{12}
\]

第一、末步分别调用 μ、ν 的实际 `path_pi_lintegral_cons`。第二步使用归纳假设；第三步用 (11)；第四步是非负积分提出或移入常数的性质，密度常数 r̂(x) 还是有限值；第五步用有限乘积的首尾分解 D_{m+1}(c(x,b))=r̂(x)D_m(b)。这些步骤均为非负积分恒等式，没有对可能无穷的实积分作线性运算。由归纳得到所有 m 的 (10)。

特别地，对每个可测路径集合 E，将 F 取为扩展非负实数值的 1_E，得到

\[
\Pi_n(\mu)(E)=\int^-_E D_n\,d\Pi_n(\nu).
\tag{13}
\]

右侧正是 `(Π_n(ν)).withDensity D_n` 在 E 上的值。可测集合上的测度外延性因此给出已推导的真实测度等式

\[
\boxed{\ \Pi_n(\mu)=(\Pi_n(\nu)).\operatorname{withDensity}(D_n)\ }.
\tag{14}
\]

这里左侧自始至终是实际 `Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s)`；没有定义一个具有所需密度的新路径律来替换它。

## 5. 概率质量转实与归一化的有限性支付

对任意可测路径集合 E，令 g_E=1_E d_n。由 (9)，g_E 可测且 0≤g_E≤B^n，所以 g_E 在 Π_n(ν) 下真正可积。它的实积分为有限非负数，且逐点

\[
\operatorname{ofReal}(g_E)=\mathbf1_E D_n.
\]

因此非负实可积函数的实积分与非负积分转换给出

\[
\operatorname{ofReal}\left(\int g_E\,d\Pi_n(\nu)\right)
=\int^-\operatorname{ofReal}(g_E)\,d\Pi_n(\nu)
=\Pi_n(\mu)(E).
\tag{15}
\]

又 Π_n(μ) 是概率测度，故 Π_n(μ)(E)≤1<∞。对 (15) 两边取 `toReal`，使用左侧实积分非负，得到

\[
(\Pi_n(\mu)).\operatorname{real}(E)
=\int \mathbf1_E(a)d_n(a)\,d\Pi_n(\nu)(a).
\tag{16}
\]

所有转实对象均已明确有限。取 E 为全集得到 ∫d_n dΠ_n(ν)=1；这也验证了从实际一维归一化产生的 n 维密度总质量确为 1。取 E=A 则给出本题需要的真实事件质量公式。这里没有对生存概率作任何正性假设。

## 6. 仅在 A 上删除闭截断并完成积分身份

若 a∈A，共享逐坐标界已经给出 |a_i|≤2h。于是对每个 i，实际 w 定义中的闭截断分支取指数值，而不是零值。有限乘积和指数加法式给出

\[
\begin{aligned}
\prod_i w(a_i)
&=\prod_i\exp(sa_i^2/h^2)\\
&=\exp\left(\sum_i sa_i^2/h^2\right)
 =\exp(sQ(a)/h^2).
\end{aligned}
\tag{17}
\]

另一方面，由 Z>0 和有限乘积的商规则（包括空乘积），

\[
d_n(a)=\frac{\prod_i w(a_i)}{Z^n}.
\tag{18}
\]

Z^n>0，即使 n=0 也为 1。结合 (17)–(18)，在 A 上得到

\[
\Phi(a)=C\exp(sQ(a)/h^2)=C Z^n d_n(a).
\tag{19}
\]

在 A 外，Φ=0，而 1_A d_n=0。因此 (19) 的正确全空间写法是

\[
\Phi=CZ^n\,\mathbf1_A d_n.
\tag{20}
\]

(17) 从未在 A 外使用；尤其没有全空间删去 w 的截断指示。

第 3 节已经证明左侧真正可积，第 5 节已经证明右侧的事件加权密度真正可积。CZ^n 为有限实常数，故现在可以对 (20) 作真实实积分，并用 (16) 的 E=A 情形：

\[
\begin{aligned}
\int\Phi\,d\Pi_n(\nu)
&=CZ^n\int\mathbf1_A d_n\,d\Pi_n(\nu)\\
&=\exp(-sN/h^2)Z^n(\Pi_n(\mu)).\operatorname{real}(A).
\end{aligned}
\]

这正是 (2)。若 Π_n(μ)(A)=0，等式仍成立；整个证明仅使用了 Z>0，没有除以生存概率。

## 7. 沿实际有限独立同分布联合律同时转移可积性和积分

令 Ω 为任意带可测结构的类型，p 为其概率测度，X:Fin n→Ω→ℝ 满足

- 对每个 i，X_i 可测；
- `iIndepFun X p`；
- 对每个 i，`IdentDistrib (X i) (id : ℝ → ℝ) p ν`。

这些正是共享 `Shao.Probability.iid_samplePath_map_eq_pi` 的实际环境。令

\[
Y=\operatorname{Shao.Probability.samplePath}(X),\qquad
Y(\omega)_i=X_i(\omega).
\]

共享 `measurable_samplePath hX` 给 Y 可测，共享联合律定理给真实推送等式

\[
\operatorname{Measure.map}(Y,p)=\Pi_n(\nu).
\tag{21}
\]

Φ∘Y 可测且非负。为同时支付真实可积性，先对可测非负函数 a↦ofReal(|Φ(a)|) 使用推送测度的非负积分公式，得到

\[
\int^-_\omega\operatorname{ofReal}(|\Phi(Y(\omega))|)\,dp
=\int^-_a\operatorname{ofReal}(|\Phi(a)|)\,d\operatorname{map}(Y,p)
=\int^-_a\operatorname{ofReal}(|\Phi(a)|)\,d\Pi_n(\nu)<\infty.
\tag{22}
\]

最后的有限性由第 3 节的真实可积性供应；也可直接由同一常数 M 支配得到。实值可测函数具有所需的几乎处处强可测性，(22) 因而证明 Φ∘Y∈L¹(p)。这不是先使用实积分转移后补猜可积性。

现在推送测度的实积分公式适用；结合 (21) 与已经证明的 (2)，

\[
\boxed{
\int_\Omega\Phi(Y(\omega))\,dp(\omega)
=\exp(-sN/h^2)Z^n(\Pi_n(\mu)).\operatorname{real}(A).
}
\tag{23}
\]

这里没有新增“样本路径有某密度”的输入，而是直接消费已证真实 iid 联合律。事件与能量也逐点保持为原来的实际对象：

\[
\begin{aligned}
Y(\omega)\in A
&\iff \forall k\le n,\quad
 \left|\sum_{i:\operatorname{Fin}(n),\ i.\mathrm{val}<k}X_i(\omega)\right|\le h,\\
Q(Y(\omega))&=\sum_{i:\operatorname{Fin}(n)}X_i(\omega)^2.
\end{aligned}
\]

事件的原像可测，因为 A、Y 都可测；(23) 中的左侧正是此弱闭部分和事件上的实际中心能量指数积分。Ω 不需要额外的拓扑、标准 Borel 或无原子前提。

## 8. 边界、依赖与范围核对

1. **n=0。** 共享 `shiftedClosedSurvival_zero` 和 `shiftedClosedSurvival_eq_closedStrip` 给 A=P_0；空和给 Q=0，故 Φ=1。Π_0(ν)、Π_0(μ) 都是唯一空路径上的概率测度；C=1、Z^0=1、空乘积 d_0=D_0=1，两侧均为 1。归纳基与实积分证明本身均覆盖此情形。iid 转移中样本路径仍为唯一空路径，结论相同。
2. **弱闭端点及原子。** 所有条件均保持 ≤；|S_k|=h 和 |a_i|=2h 时相关闭分支仍被计入。没有借零边界质量删除任何端点，也没有假定原律无原子、非格点或有密度。
3. **s=0、T=0。** s=0 时 Φ=1_A，w=1_{|x|≤2h}，Z=ν.real{|x|≤2h}；μ 是相应归一化闭截断测度，通常不等于 ν。式 (2) 此时为 Π_n(ν).real A=Z^n Π_n(μ).real A，正由同一证明得到。T=0 强制 s=0，不涉及除以 T。
4. **h=1、零路径与 Q=0。** h=1 仍给 h>0、h²>0。证明不除以 Q，不要求正能量，不删除全零路径，也不要求方差有正下界。全零路径的指数值 exp(−sN/h²)被保留。
5. **原测度的条件。** 原二阶真可积和单位二阶矩仅通过已有一维接口供应 Z>0、μ 概率。没有补入原中心、三阶或四阶矩、支持有界、指数矩、对称性或生存概率正性。全局有界的是截断权重和带事件的 Φ，不是原律上的未截断平方指数。
6. **已知依赖（KNOWN）。** `TruncatedEnergy` 的实际权重可测／非负／有界／真可积及 normalizer 界；`EnergyTiltedLaw` 的实际定义、normalizer 正性及概率性；`Basic.FinitePath` 的真实 energy 及非负性；`Basic.ClosedSurvival` 的 closedStrip 和逐坐标界；`Probability.MeasurablePath` 的可测能量；`KilledPathLaw` 的闭事件可测桥及真实有限 π 拆分；`Probability.FiniteIID` 的可测样本路径及真实联合律；非负积分的 withDensity、参数可测性、有限乘积拆分、实／非负积分转换和推送积分定理。每次应用都在正文交付了可测性、σ 有限性或真实可积性条件。
7. **本文件新证（PROVED_HERE）。** Φ 的全空间有限支配与真可积性；实际有限 π 的密度测试公式 (10) 及测度等式 (14)；有限事件质量的真实转实公式 (16)；A 上的截断乘积计算；目标积分身份 (2)；一般 iid 环境中的真实可积性与积分身份 (22)–(23)。
8. **后置范围。** 本证明只处理冻结的式 (7) 第一叶，不消费 E2 方差窗口、θ 存在或其 log 界，不证明式 (8)–(10)、相对渐近、E4、K/Kv、随机分母或完整 E3/OQ4。那些状态不由本文件改变。

以上给出冻结结论的完整数学证明，待与作者上下文隔离的独立数学门核验。本轮没有 Lean 实现或机械认证。
