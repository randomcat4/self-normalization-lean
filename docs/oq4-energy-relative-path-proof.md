# 同一中心参数的全 n 有限乘法路径约化

STATUS: PROVED
VERIFICATION: MATH_ONLY_NOT_COMPILED

本文只证明固定冻结版本的有限结论，不声称新增 Lean 机械认证。冻结命题：`drafts/oq4/frozen-energy-relative-path-bounds-v1.md`，SHA256 `ddc8a054559f6ec4ec423e913bfd4bb8e5a1b78f26bdefc68fbc9e26c49a7660`，5139 字节。原始语义：`C:/game/shao/current/oq4/energy01.md`，sourcecommit `35d4580b61e22e7145f47730045a09874ef93259`，SHA256 `2e0387f0a35ca677853e45fff271cc2fb0e87db9ee9c6b2f00d3bcf56b51d9e6`。本文不修改上述文件或其中的前提、常数、事件、量词。

## 1. 固定对象与待证量词

先固定任意实数 M,T≥0，并固定

\[
 P=\operatorname{energyE1Constant}(T),\qquad
 C=\operatorname{energyE2Constant}(M,T),\qquad
 H=\operatorname{energyE2Threshold}(M,T).
\]

此后三个常数不依赖 ν,h,s,n 或 θ。任取实 Borel 概率测度 ν，满足

\[
 x\mapsto x^2\in L^1(\nu),\quad x\mapsto |x|^3\in L^1(\nu),\quad
 \int x^2\,d\nu=1,\quad \int x\,d\nu=0,\quad
 \beta:=\int |x|^3\,d\nu\le M.
\tag{1.1}
\]

这里的两个矩可积条件是真可积条件。原一阶矩也真可积，因为 |x|≤1+x² 且 ν 是概率测度；没有借助总定义积分把不可积均值解释成零。β≥0 来自非负函数的积分。任取 h≥H、|s|≤T。以下全部证明都在这些固定对象下进行。

使用已有实际定义：

\[
 w(x)=1_{\{|x|\le2h\}}e^{sx^2/h^2},\quad
 Z=\int w\,d\nu=\operatorname{energyNormalizer}(\nu,h,s),
\]
\[
 \mu=\operatorname{energyTiltedLaw}(\nu,h,s)
      =\nu.\operatorname{withDensity}\bigl(\operatorname{ofReal}(w/Z)\bigr),
\]
\[
 L(t)=\int e^{tx}\,d\mu
     =\operatorname{energyLinearNormalizer}(\nu,h,s,t),\quad
 \mu_t=\operatorname{energyLinearTiltLaw}(\nu,h,s,t)
      =\mu.\operatorname{withDensity}\bigl(\operatorname{ofReal}(e^{tx}/L(t))\bigr).
\tag{1.2}
\]

对每个 n∈ℕ，令 Path(n)=Fin(n)→ℝ，Πₙ(ρ)=Measure.pi(i∈Fin(n)↦ρ)，

\[
 S_k(a)=\operatorname{prefixSum}(a,k),\quad
 Q_n(a)=\operatorname{energy}(a)=\sum_{i\in\mathrm{Fin}(n)}a_i^2,
\]
\[
 A_n=\operatorname{closedStrip}(h)
     =\{a:\ \forall k\le n,\ |S_k(a)|\le h\},\qquad
 p_n=(\Pi_n(\mu)).\operatorname{real}(A_n),\quad
 r_n(t)=(\Pi_n(\mu_t)).\operatorname{real}(A_n),
\]
\[
 F_n(a)=\begin{cases}e^{s(Q_n(a)-n)/h^2},&a\in A_n,\\0,&a\notin A_n,\end{cases}
 \qquad I_n=\int F_n\,d\Pi_n(\nu).
\tag{1.3}
\]

n 在实数表达式中均指其自然数到实数的强制转换。定义恰为冻结误差

\[
 \varepsilon_2(n,h)=C/h+Cn/h^4,\qquad
 \varepsilon(n,h)=PMn/h^3+\varepsilon_2(n,h).
\tag{1.4}
\]

将证明：存在一个 θ，使完整 energyE2Conclusion(ν,M,T,h,s,θ) 成立，而且对每个 n 同时成立

\[
 e^{-C/h}L(\theta)^n r_n(\theta)\le p_n
 \le e^{C/h}L(\theta)^n r_n(\theta),
\tag{1.5}
\]
\[
 e^{-\varepsilon_2(n,h)}r_n(\theta)\le p_n
 \le e^{\varepsilon_2(n,h)}r_n(\theta),
\tag{1.6}
\]
\[
 F_n\in L^1(\Pi_n(\nu)),\qquad
 e^{-\varepsilon(n,h)}r_n(\theta)\le I_n
 \le e^{\varepsilon(n,h)}r_n(\theta).
\tag{1.7}
\]

同一个 θ 先于 n 选择。证明也给出任意满足完整 E2Conclusion 的 θ 的辅助结论，以及相同 θ 下的真实独立同分布样本版本。

## 2. 已认证接口与使用条件（全部标记 KNOWN）

本节只使用实际 Lean 源码中的已证声明，不以其匿名证明或审稿判断作为数学引理。下列命名均位于 Shao.OQ4，最后的公共映射桥位于 Shao.Probability。

**KNOWN A：常数与阈值。** `energyE1Constant_dominates T hT` 仅要求 T≥0，给出 1≤P。`energyE2Constant_dominates M T hM hT` 要求 M,T≥0，给出 1≤C。`energyE2Threshold` 按定义等于 `energyLinearCenteringThreshold`；`energyLinearCentering_height_bounds M T h hM hT hh` 要求 M,T≥0 和该中心化阈值≤h，给出 `energyLogThreshold M T≤h` 和 2≤h（并给出中心化 K 的正性及 K/h² 的正性）。因此本轮 h≥H 足够同时供应 E1 阈值、h≥1 和 h>0。取同一接口的 h=H、阈值条件为自反不等式，还得到 H≥2，故 P,C,H 均非负。此处未新增 h 的下界。

**KNOWN B：实际 E1。** `energyE1_common_bounds ν M T h s hM hT hhLog hs hSq hCube hsecond hmean hβM` 的全部输入为：ν 为概率测度，M,T≥0，`energyLogThreshold M T≤h`，|s|≤T，以及 (1.1) 中两个真可积条件、单位原点二阶矩、原均值零和 β≤M。它返回 `energyE1Conclusion ν T h s`。所用分量是 μ 为概率测度、μ 下 x,x²,|x|³ 真可积、μ 几乎处处 |x|≤2h、2≤h、1/2≤Z≤3/2，以及

\[
 |\log Z-s/h^2|\le P\beta/h^3.
\tag{2.1}
\]

其余 E1 矩界也保留为该实际结论的分量，不需要作为新前提。由 Z≥1/2 得 Z>0。

**KNOWN C：实际 E2 总入口。** `energyE2_common_bounds ν M T h s hM hT hh hs hSq hCube hsecond hmean hβM` 的全部输入为：ν 为概率测度，M,T≥0，h≥H，|s|≤T，以及 (1.1)。其结论是

\[
 \exists\theta\in\mathbb R,\quad
 \operatorname{energyE2Conclusion}(\nu,M,T,h,s,\theta).
\tag{2.2}
\]

该完整结论逐项为：

1. `energyLinearMean ν h s θ=0`；
2. μθ 是概率测度；
3. μθ 几乎处处 |x|≤2h；
4. x、x²、|x|³ 在 μθ 下分别真可积；
5. ∫x dμθ=0；
6. |θ|≤C/h²；
7. |log L(θ)|≤C/h⁴；
8. |∫x² dμθ−1|≤C/h；
9. ∫|x|³ dμθ≤C。

这正是实际定义的全部合取分量；没有只保留参数界而丢失中心律。

**KNOWN D：实际线性正性和真可积性。** 对 ν 为概率测度、T≥0、h≥1、|s|≤T、x² 在 ν 下真可积且 ∫x² dν=1，`energyLinear_integrability ν T h s hT hh1 hs hSq hsecond t` 对每个实 t 给出 μ 下 e^{tx}、xe^{tx}、x²e^{tx}、|x|³e^{tx} 真可积。相同条件下 `energyLinearNormalizer_pos ... t` 给出真实 L(t)>0，`energyLinearTiltLaw_isProbabilityMeasure ... t` 给出实际 μt 为概率测度。这里不需要额外的原ν指数矩、第四矩或有界支持；有界支持是实际 μ 的已证结论。

**KNOWN E：实际能量路径身份。** `energyPathLaw_integral ν n T h s hT hh1 hs hSq hsecond` 只要求 ν 为概率测度、n∈ℕ、T≥0、h≥1、|s|≤T、ν 下 x² 真可积及单位二阶矩。它返回 Fₙ 在 Πₙ(ν) 下真可积及精确等式

\[
 I_n=e^{-sn/h^2}Z^n p_n.
\tag{2.3}
\]

`energyPathIntegrand_measurable h s hh0` 要求 h≥0，给出 Fₙ 的可测性；`energyPathIntegrand_integrable` 的条件为 ν 概率、T≥0、h≥1、|s|≤T。所有声明包括 n=0。

**KNOWN F：实际线性路径身份与相对夹界。** `energyLinearPathLaw_integral` 与 `energyLinearPathLaw_sandwich` 的条件均为 ν 概率、n∈ℕ、T≥0、h≥1、|s|≤T、ν 下 x² 真可积及单位二阶矩；t 是任意实数。令

\[
 J_{n,t}(a)=1_{A_n}(a)e^{-tS_n(a)}
            =\operatorname{energyLinearPathIntegrand}(h,t,a).
\]

前者返回 Jₙ,ₜ 在 Πₙ(μt) 下真可积及

\[
 p_n=L(t)^n\int J_{n,t}\,d\Pi_n(\mu_t).
\tag{2.4}
\]

后者返回

\[
 L(t)^ne^{-|t|h}r_n(t)\le p_n\le L(t)^ne^{|t|h}r_n(t).
\tag{2.5}
\]

端点来自闭事件内 |Sₙ|≤h，而非样本均值或平移事件。上述命题均包括空路径。其概率与积分均是实际 Measure.pi 上的对象。

**KNOWN G：真实独立同分布映射桥。** `iid_samplePath_map_eq_pi hX hIndep hLaw` 要求任意概率空间 (Ω,p)、参考实概率律 ρ、X:Fin(n)→Ω→ℝ、逐坐标 Measurable(Xᵢ)、iIndepFun X p，以及每个坐标 `IdentDistrib (X i) id p ρ`。结论为

\[
 \operatorname{map}(\operatorname{samplePath}X,p)=\Pi_n(\rho).
\tag{2.6}
\]

`measurable_samplePath hX` 要求逐坐标可测。`energyPathLaw_integral_iid` 在 KNOWN E 的全部条件外，增加概率空间 (Ω,p) 与上述 ρ=ν 的完整独立同分布环境；它返回 Fₙ∘samplePath X 真可积以及样本积分等于 (2.3) 的右端。`energyLinearPathLaw_base_probability_iid` 在 KNOWN F 的基础条件外增加 ρ=μ 的完整独立同分布环境，返回 pₙ 等于实际样本闭事件概率。`energyLinearPathLaw_probability_iid` 对任意实 t 在相同基础条件外增加 ρ=μt 的完整独立同分布环境，返回 rₙ(t) 等于相应实际样本闭事件概率。三者都包含 n=0；不含生存条件下独立性条件。

所读四个主要已认证接口文件的固定版本为：

| 文件 | 字节数 | SHA256 |
|---|---:|---|
| energy-e1/EnergyE1Bounds.lean | 4591 | 448db6e250307358455e7c8da660ffdb094ddb5a42f0e7e81e9c08c02aa4d39d |
| energy-e2/EnergyE2Bounds.lean | 11643 | 41b7343861549f55ae86cddb514a5ed55612448b1ab0efc1e3bb580182746ca8 |
| energy-path-law/EnergyPathLaw-published.lean | 15247 | 3336b977fbe88ae4c27ff7531ffeec6e14c71508587ac2abae99bf475757a177 |
| energy-linear-path-law/EnergyLinearPathLaw.lean | 18042 | 039ad7326ea9a80e476f50bf3f46dd0078c2c61f6786f15a6d72f3ba0c227afb |

路径均相对于 `C:/game/shao lean/drafts/oq4/`。补充实际接口仅为上述 Centering、EnergyLinearTiltLaw、原截断定义与公共 FiniteIID 等所需声明；不读取其他作者的匿名数学证明或审稿推理。

## 3. 一次选择 θ，并核对全部应用条件（PROVED_HERE）

由 KNOWN A，P≥1、C≥1、H≥2，h≥H 因而 h≥2>0，并且 energyLogThreshold(M,T)≤h。因此 KNOWN B、C 的阈值均由原 h≥H 供应，所有原矩、均值、β 条件恰是 (1.1)。|s|≤T 与 ν 概率性已经固定，故无额外条件。

现在仅调用一次 KNOWN C，取得 θ 及第 2 节所列完整 E2Conclusion。固定该 θ，全文返回这一完整结论而不改变其任何分量。此时尚未引入 n，也没有根据路径事件、生存质量或样本空间选择 θ。

在余下论证中，可以直接把这个步骤替换成“给定任意满足完整 E2Conclusion 的 θ”；其余步骤完全不使用 θ 的选择方式。存在型总入口仍由刚才的一次内部调用 (2.2) 提供。

KNOWN B、D 给出实际 μ、μθ 的概率性、Z>0 和 L(θ)>0；D 的 h≥1、T≥0、|s|≤T、原二阶矩条件已逐一供应。故有限乘积 Πₙ(ν)、Πₙ(μ)、Πₙ(μθ) 都是概率测度，各实事件质量非负且有限。三种真可积矩、实际均值零、支持与同常数四界仍作为同一个 θ 的结论保留。

以下令 n 为任意自然数，记 rₙ=rₙ(θ)，并写

\[
 a=C/h,\qquad b=Cn/h^4,\qquad d=PMn/h^3.
\tag{3.1}
\]

P,C,M,n≥0 且 h>0，故 a,b,d≥0，ε₂=a+b≥0，ε=d+a+b≥0。由于 n 完全任意，后面的证明产生 ∀n，且不重新选择 θ。

## 4. 保留 Lⁿ 的端点夹界（PROVED_HERE）

E2Conclusion 给出 |θ|≤C/h²。乘以正数 h，得到

\[
 0\le |\theta|h\le (C/h^2)h=C/h=a.
\tag{4.1}
\]

在 Aₙ 上，实际 closedStrip 的末端条件（k=n）给出 |Sₙ|≤h。因此

\[
 |\theta S_n|\le |\theta|h,\qquad
 e^{-|\theta|h}\le e^{-\theta S_n}\le e^{|\theta|h}.
\tag{4.2}
\]

这一比较对 θ 的两种符号及 θ=0 均成立；它在 Aₙ 外与零指标相乘后仍成立。Jₙ,θ 真可积由 KNOWN F 供应，指标函数在概率测度上真可积，故可积分 (4.2)；这正给出实际夹界 (2.5) 的 t=θ 情形。

指数函数单调，(4.1) 给出 e^{-a}≤e^{-|θ|h} 与 e^{|θ|h}≤e^a。L(θ)ⁿ>0 且 rₙ≥0，故可把这两项分别乘以 L(θ)ⁿrₙ，并与 (2.5) 连接，得到

\[
 e^{-a}L(\theta)^nr_n\le p_n\le e^aL(\theta)^nr_n.
\tag{4.3}
\]

交换实数乘法的因子顺序后，这就是 (1.5)。此步完整保留真实 L(θ)ⁿ；从未把它替换为 1。

## 5. 用真实 log L 吸收 Lⁿ（PROVED_HERE）

由已供应的 L(θ)>0，实对数合法满足 exp(log L(θ))=L(θ)。对 n 归纳或使用指数的自然数乘法公式可得

\[
 L(\theta)^n=\bigl(e^{\log L(\theta)}\bigr)^n
             =e^{n\log L(\theta)}.
\tag{5.1}
\]

n=0 时两端都是 1，所以这里不要求 n>0。设 λ=n log L(θ)。E2Conclusion 的实际对数界给出

\[
 |\lambda|=n|\log L(\theta)|\le nC/h^4=b,
 \qquad -b\le\lambda\le b.
\tag{5.2}
\]

将 (5.1) 代入 (4.3)，再用 rₙ≥0 及指数单调性，分别得到

\[
 e^{-(a+b)}r_n\le e^{\lambda-a}r_n\le p_n,
\]
\[
 p_n\le e^{\lambda+a}r_n\le e^{a+b}r_n.
\tag{5.3}
\]

因为 ε₂=a+b，这正是 (1.6)。这里控制的是乘法上下界，而非对稀有事件没有用的绝对误差。

## 6. 原 ν 的能量加权积分及 E1 代价（PROVED_HERE）

Fₙ 是 KNOWN E 的实际 energyPathIntegrand。该接口的全部条件已在第 3 节核对，因此直接得到 Fₙ 真可积与 (2.3)。也可以独立看清真可积性的来源：h≥0 使 Aₙ 可测；Qₙ 与 Sₖ 是可测有限多项式。闭路径上每个坐标满足 |aᵢ|≤2h，故

\[
 0\le Q_n(a)\le4nh^2\quad(a\in A_n).
\]

由于 s≤|s|≤T、T≥0、h>0，所有路径上均有

\[
 0\le F_n(a)\le e^{-sn/h^2}e^{4Tn}<\infty.
\tag{6.1}
\]

在 Aₙ 外 Fₙ=0；在 Aₙ 内把指数分解后即得此界。于是 Fₙ 是概率测度 Πₙ(ν) 下的可测有界函数，是真可积，而非依赖总定义积分的假等式。(6.1) 不假设原 ν 的全局指数矩或第四矩。

由 Z>0，和 (5.1) 相同的自然数幂恒等式给出 Zⁿ=exp(n log Z)。因此必须首先保留并精确合并 (2.3) 中的实际因子：

\[
 B_n:=e^{-sn/h^2}Z^n
     =e^{-sn/h^2+n\log Z}
     =e^{n(\log Z-s/h^2)}>0.
\tag{6.2}
\]

令 δ=n(log Z−s/h²)。E1 的 (2.1)、n≥0、P≥0、β≤M 和 h³>0 给出

\[
 |\delta|=n|\log Z-s/h^2|
 \le nP\beta/h^3\le nPM/h^3=d.
\tag{6.3}
\]

第二个不等式只用非负系数 nP/h³ 乘 β≤M。由指数单调性，e^{-d}≤Bₙ≤e^d。式 (2.3) 仍精确写成 Iₙ=Bₙpₙ。因 pₙ≥0，可结合 (1.6) 得

\[
 I_n=B_np_n\ge e^{-d}p_n
      \ge e^{-d}e^{-\varepsilon_2(n,h)}r_n
      =e^{-\varepsilon(n,h)}r_n,
\]
\[
 I_n=B_np_n\le e^dp_n
      \le e^de^{\varepsilon_2(n,h)}r_n
      =e^{\varepsilon(n,h)}r_n.
\tag{6.4}
\]

这证明 (1.7)。真实 β 的 E1 误差先由 (2.1) 引入，再由 β≤M 支付 d；没有在有限 h 时令 Bₙ=1。

第 3 节的 θ 与完整 E2Conclusion 是在 n 之前取得的，而第 4–6 节对任意 n 的论证只使用固定 θ 的同一组界。故已经证明所要求的精确量词

\[
 \exists\theta,\quad
 \operatorname{energyE2Conclusion}(\nu,M,T,h,s,\theta)
 \ \land\ \forall n\in\mathbb N,\quad (1.5),(1.6),(1.7).
\tag{6.5}
\]

M,T 在 ν,h,s 之前固定，P,C,H 对整个分布类一致；未把 θ 的存在弱化为 ∀n∃θ。

## 7. 真实独立同分布样本版本（PROVED_HERE）

仍用第 3 节选定的同一个 θ。固定任意 n、任意概率空间 (Ων,pν) 与有限族 Xν:Fin(n)→Ων→ℝ，假设各坐标可测、iIndepFun Xν pν，并且逐坐标 `IdentDistrib (Xν i) id pν ν`。这正是 KNOWN G 对 ρ=ν 的全部环境条件。由 (2.6)，Yν=samplePath Xν 可测且 map(Yν,pν)=Πₙ(ν)。

Fₙ 在路径空间可测且已真可积。对可测映射的积分与可积性映射定理，联合上述实际映射等式，给出

\[
 F_n\circ Y_\nu\in L^1(p_\nu),\qquad
 \int F_n(Y_\nu(\omega))\,dp_\nu(\omega)
 =\int F_n\,d\operatorname{map}(Y_\nu,p_\nu)
 =I_n.
\tag{7.1}
\]

也可直接调用已认证 `energyPathLaw_integral_iid`：它给出同一个真可积性及样本积分等于 Bₙpₙ，再与 (2.3) 相等，得到 (7.1)。这里仅使用有限联合分布，无条件生存独立性假设。将 (7.1) 代入 (1.7)，即得到原 ν 样本的能量加权积分的同一 ε 夹界。

如果需要把 pₙ 写成真实样本概率，则另取任意概率空间 (Ωμ,pμ) 及 Y:Fin(n)→Ωμ→ℝ，要求每个坐标可测、iIndepFun Y pμ，以及逐坐标 `IdentDistrib (Y i) id pμ μ`。KNOWN G 的实际 `energyLinearPathLaw_base_probability_iid` 的 ν、T,h,s、原二阶矩条件全由第 3 节供应；样本条件恰由本段假设供应。因此

\[
 p_n=p_\mu.\operatorname{real}
      \{\omega:\operatorname{samplePath}Y(\omega)\in A_n\}.
\tag{7.2}
\]

如果需要把 rₙ 写成真实样本概率，则另取任意概率空间 (Ωθ,pθ) 及 W:Fin(n)→Ωθ→ℝ，要求每个坐标可测、iIndepFun W pθ，以及逐坐标 `IdentDistrib (W i) id pθ μθ`。实际 μθ 概率性已由 E2Conclusion（也由 KNOWN D）供应；KNOWN G 的 `energyLinearPathLaw_probability_iid` 在 t=θ 的全部基础条件已供应。因此

\[
 r_n=p_\theta.\operatorname{real}
      \{\omega:\operatorname{samplePath}W(\omega)\in A_n\}.
\tag{7.3}
\]

Aₙ 可测、samplePath 可测，故 (7.2)、(7.3) 也直接是实际映射等式对同一闭事件取质量的结果。分别或同时将 (7.2)、(7.3) 代入 (1.5)–(1.7)，就得到所需真实样本版本。三个概率空间可以互不相同；各自族只需要自己的完整独立同分布环境，不要求它们之间有耦合、共同坐标或共同随机性，也不要求一个族同时具有两个不同的边缘律。θ 不依赖这些样本空间或有限族，故同 θ 的 ∀n 量词也不变。

## 8. 边界与退化情形逐项检查

**n=0。** Path(0) 只有空函数，S₀=Q₀=0；因为 h≥2，A₀=全空间。所有有限乘积概率为 1，F₀=1，p₀=r₀=I₀=1，L(θ)⁰=Z⁰=1，B₀=1。a=C/h≥0，b=d=0，所以 ε₂(0,h)=ε(0,h)=C/h。三组结论都化为 e^{-a}≤1≤e^a。没有把冻结误差擅改成零。

**零生存质量。** 全文从未除以 pₙ 或 rₙ。如果 rₙ=0，(1.6) 的上界和 pₙ≥0 给出 pₙ=0，(2.3) 给出 Iₙ=0。如果 pₙ=0，(1.6) 的下界、e^{-ε₂}>0 和 rₙ≥0 给出 rₙ=0，仍有 Iₙ=0。这些推理只是乘法、非负性与正指数，不产生 0/0。反之 Iₙ=0 时，由 Bₙ>0 与 Iₙ=Bₙpₙ 也得 pₙ=0。

**θ=0、正负 θ。** L(0)=∫1 dμ=1，Jₙ,0=1_{Aₙ}，所有恒等式仍成立；一般情形只使用 |θ| 和 |θSₙ|，两种符号都覆盖。θ 的实际均值条件始终保留，不把任意 t 的路径身份误当成中心化存在证明。

**s=0、T=0、正负 s。** 若 s=0，Z=ν{|x|≤2h}，μ 是实际归一化截断律；Z 未必等于 1，(2.3) 仍为 Iₙ=Zⁿpₙ，而 Iₙ 此时才是原 ν 的无权闭事件概率。T=0 强制 s=0，但不消除截断及其归一化。s 的一般两种符号由 |s|≤T、实际恒等式及对数绝对误差统一处理。s≠0 时本文始终称 Iₙ 为能量加权积分，不把它误称为原 ν 的无权概率。

**闭边界与原子。** 事件全程是同一个绝对 closedStrip；用的是 |Sₙ|≤h 与每步 |aᵢ|≤2h。真实能量权的截断条件同样为 |x|≤2h。所有比较为弱不等式，因此部分和在 ±h 的原子、坐标在 ±2h 的原子、重复坐标均保留，不要求无原子、非格点或严格内点。全零路径属于闭事件，Qₙ=0 时 Fₙ=e^{-sn/h²}，上面的恒等式和界仍覆盖它。

**阈值与分布类。** h=H 完全允许；严格正性只由已证 h≥2 导出。M=0、M<1 或任何其他 M≥0 均未被替换；若某个 M 的 admissible 分布类为空，全称结论按原量词成立，不新增 M≥1。没有假设原 ν 有界支持、对称、指数矩、第四矩或任何生存正性。

## 9. 证明状态与范围

有限 (1.5)–(1.7)、完整同 θ 的 E2Conclusion、误差非负性及真实独立同分布版本均为 PROVED；全部新推导在第 3–8 节，外部依赖精确列于第 2 节，未留下 OPEN 或等价隐藏引理。本稿为数学证明，未执行 Lean、服务器、emit、Git 或缓存操作，机械状态严格为 MATH_ONLY_NOT_COMPILED。

本稿没有证明概率比值、序列或联合渐近、误差趋一、共同二维算子、E4、K/Kv 或完整 E3/OQ4 根结论；这些目标仍保持原有 OPEN 状态。本文不引入它们作为输入，也不以绝对误差替代相对乘法夹界。
