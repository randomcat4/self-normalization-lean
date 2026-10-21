# 实际线性再倾斜的有限路径反向恒等式与夹界

STATUS: PROVED
FORMAL_STATUS: MATH_ONLY_NOT_COMPILED
E3_STATUS: OPEN
ROOT_STATUS: OPEN

本文证明冻结文件 `drafts/oq4/frozen-energy-linear-path-law-v1.md` 的全部有限结论，不改定义、量词或前提。冻结文件 SHA256 为 `54678ca7adbdcfaf007f34b1637693f2b70e6e73a15d69a761bf88f52e601091`。来源为 `oq4/energy01.md` 第78–83行，sourcecommit 为 `35d4580b61e22e7145f47730045a09874ef93259`，源 SHA256 为 `2e0387f0a35ca677853e45fff271cc2fb0e87db9ee9c6b2f00d3bcf56b51d9e6`。本稿不声称相对渐近、中心化参数选择或完整 E3/OQ4。

## 1. 对象、前提与已认证接口

固定 ℝ 上的 Borel 概率测度 ν，且

\[
 x\longmapsto x^2\text{ 对 }\nu\text{ 真正可积},\qquad
 \int x^2\,d\nu=1.
\]

取任意自然数 n（包括0）及实数 T、h、s、t，满足 T≥0、h≥1、|s|≤T；t 没有限制。以下记号都是实际已有对象的缩写：

\[
 \mu=\operatorname{energyTiltedLaw}(\nu,h,s),\qquad
 \mu_t=\operatorname{energyLinearTiltLaw}(\nu,h,s,t),\qquad
 L=\operatorname{energyLinearNormalizer}(\nu,h,s,t),
\]
\[
 P=\operatorname{Measure.pi}(i\in\operatorname{Fin}n\mapsto\mu),\qquad
 Q=\operatorname{Measure.pi}(i\in\operatorname{Fin}n\mapsto\mu_t).
\]

路径空间为 `Shao.Path n = Fin n → ℝ`。令

\[
 S(a)=\operatorname{Shao.prefixSum}(a,n),\qquad
 A=\operatorname{Shao.closedStrip}(h)
   =\{a:\ \forall k\le n,\ |\operatorname{Shao.prefixSum}(a,k)|\le h\}.
\]

定义实值指示函数 I_A(a)=1（a∈A）及0（a∉A），并使用冻结函数

\[
 F_t(a)=\begin{cases}e^{-tS(a)},&a\in A,\\0,&a\notin A.\end{cases}
\]

对有限测度 ρ，`ρ.real E` 表示 `(ρ E).toReal`。

本证明使用下列已认证接口（KNOWN），它们是由上述前提获得的定理，不是本稿添加的假设：

- `energyTiltedLaw_isProbabilityMeasure ν T h s hT hh hs hSq hsecond` 给 μ 为概率测度；实际能量律具有几乎处处支持 |x|≤2h。
- `energyLinear_integrability ν T h s hT hh hs hSq hsecond t` 给 x↦e^{tx} 对 μ 真正可积；`energyLinearNormalizer_bounds` 给 e^{-2h|t|}≤L≤e^{2h|t|}，故 `energyLinearNormalizer_pos` 给 L>0。这里全实 t 的可积性来自同一 μ 的有界几乎处处支持，没有使用原 ν 的指数矩。
- 实际定义为
  \[
  L=\int e^{tx}\,d\mu,\qquad
  \mu_t=\mu.\operatorname{withDensity}(d),\qquad
  d(x)=\operatorname{ENNReal.ofReal}(e^{tx}/L).
  \]
  `energyLinear_density_measurable` 给 d 可测，`energyLinearTiltLaw_isProbabilityMeasure` 给这个实际 μ_t 为概率测度。于是 P、Q 均为有限乘积概率测度。
- `finitePi_withDensity` 的实际接口为：若 η 和 η.withDensity(d) 都是概率测度且 d:ℝ→ENNReal 可测，则对每个 n，
  \[
  \operatorname{Measure.pi}(i\mapsto\eta.\operatorname{withDensity}(d))
  =\bigl(\operatorname{Measure.pi}(i\mapsto\eta)\bigr)
     .\operatorname{withDensity}\bigl(a\mapsto\prod_i d(a_i)\bigr).
  \]
  该接口包含空乘积；此处将 η 实例化为实际 μ。
- `Shao.prefixSum_length` 给 S(a)=∑ᵢaᵢ；`Shao.Probability.measurable_samplePath` 和 `iid_samplePath_map_eq_pi` 给第6节使用的实际有限 iid 映射桥。

下文的乘积指数密度、反向权重可积性、反向恒等式、夹界与其 iid 结论均在本稿证明（PROVED_HERE）。不使用线性族的任何求导或中心化定理。

## 2. 实际有限乘积密度

因为 L>0，对所有实数 x，e^{tx}/L 是正的有限实数。因此 d 可测且逐点有限。把第1节的 `finitePi_withDensity` 用于 η=μ 和这个实际 d，并按 μ_t 的定义改写，得到实际测度等式

\[
 Q=P.\operatorname{withDensity}\left(a\mapsto\prod_{i:\operatorname{Fin}n}
       \operatorname{ENNReal.ofReal}(e^{ta_i}/L)\right).
 \tag{1}
\]

所有实因子均非负，故 ENNReal.ofReal 与这个有限乘积交换。对每条路径 a，有限乘积代数及 `prefixSum_length` 给

\[
 \prod_i\frac{e^{ta_i}}L
 =\frac{\prod_i e^{ta_i}}{L^n}
 =\frac{\exp(\sum_i ta_i)}{L^n}
 =\frac{e^{tS(a)}}{L^n}.
 \tag{2}
\]

这些等式对 n=0 同样成立：空和为0、空乘积及 L⁰ 为1。令

\[
 D(a)=\frac{e^{tS(a)}}{L^n}.
\]

因 Lⁿ>0，D 是逐点正、有限且 Borel 可测的实函数。(1)–(2) 给出

\[
 \boxed{\ Q=P.\operatorname{withDensity}
                 (a\mapsto\operatorname{ENNReal.ofReal}(D(a)))\ }.
 \tag{3}
\]

这里 Q 始终是实际 μ_t 的实际 Measure.pi；(3) 是从其构造推出的等式。特别地，对任意可测非负测试函数 G:Path n→ENNReal，withDensity 的非负积分公式给

\[
 \int^-G\,dQ
 =\int^-\operatorname{ENNReal.ofReal}(D)\,G\,dP.
 \tag{4}
\]

(4) 在 ENNReal 中成立，暂不需要作实积分转换。与 μ 相比，单步线性密度只含 e^{tx}/L，所以 (2) 对全部路径成立；没有在原 ν 到 μ 的能量密度中删除任何截断指示。

## 3. 事件可测性与反向权重的真正可积性

对每个 k，prefixSum(a,k) 是有限个坐标投影之和，因而可测。A 是 k=0,…,n 对应的有限个闭条件 |prefixSum(a,k)|≤h 的交，所以 A 可测。由此 I_A 和 F_t 都是 Borel 可测；同样可沿实际 `measurable_prefixSum` 与 `measurableSet_shiftedClosedSurvival`、`shiftedClosedSurvival_eq_closedStrip` 接口取得该结论。

写 b=|t|h≥0，c_-=e^{-b}，c_+=e^b；两者均为正的有限实数。若 a∈A，则直接取定义中的 k=n 得 |S(a)|≤h。因此

\[
 |-tS(a)|=|t|\,|S(a)|\le |t|h=b,
\]

从而 -b≤-tS(a)≤b，指数单调性给

\[
 c_-\le e^{-tS(a)}\le c_+\qquad(a\in A).
\]

在 A 外 F_t=0，所以在整个路径空间上都有

\[
 0\le c_-I_A\le F_t\le c_+I_A\le c_+.
 \tag{5}
\]

Q 是概率测度，故 |F_t|=F_t≤c_+ 是有限常数支配。可测性与此界给 ∫|F_t|dQ≤c_+<∞，因此 F_t 对实际 Q 真正可积。此外，I_A 对 P、Q 都真正可积，且可测事件指示函数的积分分别为 P.real A、Q.real A。这些结论不依赖任一生存概率的正性。

## 4. 实积分换测度与精确反向恒等式

在 A 内，由 Lⁿ>0 和指数加法公式，

\[
 D(a)F_t(a)
 =\frac{e^{tS(a)}e^{-tS(a)}}{L^n}
 =\frac{1}{L^n}.
\]

在 A 外，两边均为0。因此逐点有

\[
 H(a):=D(a)F_t(a)=\frac{1}{L^n}I_A(a).
 \tag{6}
\]

H 非负、可测，且受有限常数 1/Lⁿ 支配；因为 P 是概率测度，H 对 P 真正可积。现在将 (4) 用于可测函数 G=ENNReal.ofReal∘F_t。D、F_t 均非负，所以 ofReal 的乘法性质和 (6) 给

\[
 \int^-\operatorname{ENNReal.ofReal}(F_t)\,dQ
 =\int^-\operatorname{ENNReal.ofReal}(D F_t)\,dP
 =\int^-\operatorname{ENNReal.ofReal}(H)\,dP.
 \tag{7}
\]

第3节已经证明 F_t 在 Q 下真正可积，且刚才已证明 H 在 P 下真正可积；二者又都非负。因此各自的实积分均为有限非负数，非负积分等于该实积分的 ENNReal.ofReal。对 (7) 两边取 toReal，合法得到

\[
 \int F_t\,dQ=\int H\,dP
 =\frac{1}{L^n}\int I_A\,dP
 =\frac{P.\mathrm{real}\,A}{L^n}.
 \tag{8}
\]

这里 P(A)≤1，事件质量到实数的转换也没有无穷值。上述转换先供应了真正可积性，未使用不可积实积分的默认值。因 Lⁿ>0，将 (8) 乘以 Lⁿ 得所需的精确身份

\[
 \boxed{\ P.\mathrm{real}\,A
          =L^n\int F_t\,dQ\ }.
 \tag{9}
\]

唯一除数是已证明正的 Lⁿ；没有除以 P.real A 或 Q.real A。

## 5. 不除生存质量的有限夹界

(5) 中的 c_-I_A、F_t、c_+I_A 均对 Q 真正可积。积分单调性和指示函数积分公式给

\[
 e^{-|t|h}Q.\mathrm{real}\,A
 \le\int F_t\,dQ
 \le e^{|t|h}Q.\mathrm{real}\,A.
\]

乘以正数 Lⁿ 并代入 (9)，即得

\[
 \boxed{\ L^n e^{-|t|h}Q.\mathrm{real}\,A
       \le P.\mathrm{real}\,A
       \le L^n e^{|t|h}Q.\mathrm{real}\,A\ }.
 \tag{10}
\]

指数中的 h 来自同一事件内部的终点界 |S_n|≤h，没有用逐坐标相加的 nh 界，也没有移动绝对部分和边界。

## 6. 沿实际 iid 映射桥拉回

先说明同一个共享桥的通用使用方式。令 λ 是 ℝ 上的任意概率测度，(Ω,p) 是任意概率样本空间，X:Fin n→Ω→ℝ 满足：每个 X_i 可测、`iIndepFun X p`，且每个 X_i 与恒等函数 id:ℝ→ℝ 在 p、λ 下 `IdentDistrib`。令 Y=samplePath X，则共享接口实际给

\[
 Y\text{ 可测},\qquad
 \operatorname{Measure.map}(Y,p)
   =P_\lambda:=\operatorname{Measure.pi}(i\mapsto\lambda).
 \tag{11}
\]

若 f 是 Borel 实函数且对 P_λ 真正可积，则可测映射的可积性转移定理将 f 在 map(Y,p) 下的可积性转为 f∘Y 在 p 下的可积性；积分换元公式随后给

\[
 \int_\Omega f(Y(\omega))\,dp(\omega)
   =\int f\,d\operatorname{Measure.map}(Y,p)
   =\int f\,dP_\lambda.
 \tag{12}
\]

具体可调用与已有 EnergyPathLaw 相同的 `integrable_map_measure` 和 `integral_map`；此处所需的映射可测性和 f 的强几乎处处可测性均由上述可测性供应。对任意可测事件 E，map 的事件公式和 (11) 同时给

\[
 p\{\omega:Y(\omega)\in E\}=P_\lambda(E),\qquad
 p.\mathrm{real}\{\omega:Y(\omega)\in E\}
   =P_\lambda.\mathrm{real}\,E.
 \tag{13}
\]

现在令 λ=μ_t，其概率性质已在第1节内部供应。对任意满足上述实际 μ_t 边缘条件的 X，取 f=F_t、E=A。第3节的可测性和真正可积性经 (11)–(12) 得到

\[
 F_t\circ\operatorname{samplePath}X\text{ 对 }p\text{ 真正可积},\qquad
 \int_\Omega F_t(\operatorname{samplePath}X(\omega))\,dp(\omega)
   =\int F_t\,dQ.
 \tag{14}
\]

设 A_X={ω:samplePath X(ω)∈A}。由 (13)，p.real A_X=Q.real A。于是 (9)–(10) 给真正的样本路径结论

\[
 P.\mathrm{real}\,A
 =L^n\int_\Omega F_t(\operatorname{samplePath}X(\omega))\,dp(\omega),
 \tag{15}
\]
\[
 L^n e^{-|t|h}p.\mathrm{real}\,A_X
 \le P.\mathrm{real}\,A
 \le L^n e^{|t|h}p.\mathrm{real}\,A_X.
 \tag{16}
\]

μ 侧也使用同一个桥：取 λ=μ，对任意另一概率样本空间 (Ω₀,p₀) 和满足相同可测性、独立性、实际 μ 边缘条件的样本族 X⁰，令 A₀={ω:samplePath X⁰(ω)∈A}，则 (13) 给

\[
 p_0.\mathrm{real}\,A_0=P.\mathrm{real}\,A.
 \tag{17}
\]

将 (17) 代入 (15)–(16) 即得到两侧都以真实 iid 样本路径表述的反向身份和夹界；例如

\[
 p_0.\mathrm{real}\,A_0
 =L^n\int_\Omega F_t(\operatorname{samplePath}X(\omega))\,dp(\omega).
\]

(12) 也将 μ 侧 I_A 的真正可积性及其积分拉回。两侧样本族可处于不同空间，不需要新增耦合，也不要求同一个样本族同时具有 μ 与 μ_t 两种边缘律。独立性仅用于原无条件 iid 映射桥，没有断言生存条件下仍独立。

## 7. 边界与前提检查

当 n=0，唯一空路径的所有受监测前缀只有 S₀=0；因 h≥1，A 为全集。S=0、F_t=1、L⁰=1，P、Q 的总质量均为1。因此 (3) 的密度为1，(9) 是1=1；(10) 为 e^{-|t|h}≤1≤e^{|t|h}，由 |t|h≥0 成立。iid 桥中的空族条件为空，样本路径为常值空路径，(14)–(17) 仍成立。

当 t=0，实际定义和 μ 的概率性质给 L(0)=∫1dμ=1，且实际 μ₀=μ.withDensity(1)=μ；这也正是 `energyLinearNormalizer_zero` 和 `energyLinearTiltLaw_zero`。此时 F₀=I_A，(9) 退化为同一事件质量恒等式，(10) 的上下端均等于 P.real A。

正负 t、h=1、T=s=0 均已包含在上述全称论证中。事件始终使用弱闭条件 ≤，指数相消和事件界在端点仍是逐点等式或不等式。允许原子、全零路径、重复坐标及端点正质量，没有用无原子性、边界零质量或严格生存事件。若 Q.real A=0，(9) 与 (5) 给 P.real A=0，(10) 两端都是0；全部步骤仍合法。整个证明未新增生存概率正性。

没有新增原均值为零、三阶矩、M、K、θ、方差下界、原 ν 的有界支持、原 ν 的指数矩或 n/h 条件。实际概率与 L 的正性均由冻结前提和已有已认证 law 接口供应。以上是数学证明产物，本轮未编译 Lean、未产生正式形式认证，也未关闭完整 E3 或 OQ4。
