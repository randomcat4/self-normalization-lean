# QuadraticCharacteristic 最终独立源码语义与证明审查

STATUS: CORRECT（源码数学审查）

本报告先独立只读实际定义与七个公开签名并完成盲译，随后读取冻结 scope 和实际来源，再阅读全部 387 行实现，包括一个私有 phase 定义及十七个私有 lemma。未以原声明审查者或作者回执的成功结论代替独立数学判断。未发现声明变更、源语义偏离或证明缺口。

未运行本机或服务器 Lean，未重复目标编译、公理审计或作者 API 探针。必要接口仅通过指定服务器 broker 只读 Mathlib 源码。作者所述目标 exit 0、29 声明标准公理审计属于另行服务器证据，不是本报告自行重跑的内核认证。只新增本报告，未修改实现、scope、依赖或他人文件。

## 冻结绑定与声明一致性

- 实现：C:/game/shao lean/drafts/c12/QuadraticCharacteristic.lean，387 行。
  SHA256：8fd7815191dbd1ba9180159effe8c353d8b82d998d4d0d50bb6f957355b628f5。
- 原提案：C:/game/shao lean/drafts/c12/FourierCore-next-scope.md。
  SHA256：add680178670044bc54e90a143a1057b2d6bc74e0d08f42769480951bfe2c656。
- main.tex：C:/game/shao/current/c12/main.tex。
  SHA256：beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06。
- supplement.tex：C:/game/shao/current/c12/supplement.tex。
  SHA256：b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd。

实现和 scope 哈希本轮实际核对。一个公开定义的 body 与冻结原式相同；七个完整公开定理签名与 scope 除空白外逐字相等。排列顺序不影响接口，没有增加原变量全局三矩、均值零、方差正性、频率域或可微性前提。

## 第一阶段：全部实际公开定义与量词盲译

定义记号
\[
 \chi_\nu(u,v)=\int_{\mathbb R}e^{i(ua+va^2)}\,d\nu(a),\quad
 m=\int a\,d\nu,\quad m_3=\int|a|^3\,d\nu,\quad
 d_v(u)=\chi_\nu(u,v)-\chi_\nu(-u,v).
\]
这是同一真实 A 与 A² 的耦合相位，不是各坐标特征函数的乘积。第二项只反转 u，保留 v。

1. **quadraticChar（21–23 行）。** 对任意实测度 ν、任意实 u,v，定义上面的真实 ℂ 值 Lebesgue/Bochner 积分。定义本身不假设 ν 概率或矩；后续特征函数结论都在明确概率前提下使用，那里被积函数真正可积。
2. **norm_quadraticChar_le_one（86–88 行）。** 对任意概率 ν、任意 u,v∈ℝ，‖χ_ν(u,v)‖≤1。没有矩、均值、方差或非零频率条件。
3. **iid_quadraticChar_factor（93–104 行）。** 任意 n∈ℕ、带可测结构的 Ω、概率 μ 和 ν、函数族 X:Fin n→Ω→ℝ；要求每个 Xᵢ 可测、iIndepFun X μ、每个 Xᵢ 在 μ 下与 id 在 ν 下 IdentDistrib。对任意实 u,v，
   \[
   \int_\Omega e^{i(uS_n(X)+vQ_n(X))}\,d\mu
     =\chi_\nu(u,v)^n.
   \]
   Sₙ 是实际同一路径的总 prefixSum，Qₙ 是其真实 energy。n=0 包含在量词中；不要求原增量任何有限矩，也未断言 Sₙ 与 Qₙ 独立。
4. **quadraticChar_odd_hasDerivAt（206–212 行）。** 任意概率 ν，唯一矩输入是实际 h3：|a|³ 在 ν 下可积；任意实 u,v。dᵥ 在 u 处的真实实参数导数为
   \[
   d_v'(u)=2i\int a\cos(ua)e^{iva^2}\,d\nu.
   \]
   该结论是 HasDerivAt，不是给一个匿名导数值命名。
5. **quadraticChar_odd_deriv_hasDerivAt（217–225 行）。** 相同 ν、h3 和任意实 u,v，函数 r↦deriv dᵥ r 的真实导数为
   \[
   d_v''(u)=-2i\int a^2\sin(ua)e^{iva^2}\,d\nu.
   \]
   ν 和 v 在整个 u 求导过程中固定；没有让律随参数变化。
6. **quadraticChar_odd_remainder（281–288 行）。** 相同唯一 h3 输入，m 和 m₃ 是 ν 的实际积分；对所有实 u,v，
   \[
   \|d_v(u)-2ium\|
   \le m_3\left(\frac{|u|^3}{3}+2|u||v|\right).
   \]
   线性项符号是 +2ium，从 d 中减去；不允许把非中心律默认为 m=0。
7. **quadraticChar_odd_bound（311–317 行）。** 相同参数和前提，
   \[
   \|d_v(u)\|\le2|m||u|
       +m_3\left(\frac{|u|^3}{3}+2|u||v|\right).
   \]
8. **quadraticChar_odd_derivative_bounds（333–340 行）。** 相同参数和前提，令 d 为真实奇部函数，断言
   \[
   \|d'_v(u)-2im\|\le m_3(u^2+2|v|),\qquad
   \|d''_v(u)\|\le2m_3|u|.
   \]
   这里两次 deriv 是同一个真实函数的两次实参数导数，没有支持界、中心化、无原子、方差、T-scale 或低频 strip 前提。

所有含矩公开结论的 h3 都只针对给定 law ν；当 ν 是源实际条件增量 law P_A 时，它不要求原未截断 ξ 的全局三矩。模块本身没有证明条件 law 的矩输入，而是从既有条件矩结论实例化；没有悄悄增加原 ξ 的 M3 假设。

## 第二阶段：来源对应

main.tex:673–678 的实际 φ(u,v)=E exp(iuA+ivA²) 与定义一致。source 的两个频率作用于同一 A，不能独立平均 A 和 A²。

supplement.tex:3197–3205 的真实奇部恒等式与减线性分解，在本模块中只取实 z=u、s=0。源更大复频域 z=u−iλ、ζ=v+is 和支持相关 exp(Cλh) 因子不属于当前声明。本模块所有 norm-one 相位论证均依赖实 u,v，因此没有把实平面结果误报为完整复移位估计。

3207–3219 的源导数公式分别是 +2i E[A cos(uA)e^{ivA²}] 和 −2i E[A²sin(uA)e^{ivA²}]；本实现实际导数及符号完全一致。冻结数值常数来自全局三角/指数余项，不冒充源未指定绝对常数的最优值。公开 raw d 界及 derivative 修正界以三角不等式蕴含 2384–2392 的实平面源结论，例如统一绝对常数 C=2 足够。

2348–2351 的未来因子 φ^(n−i) 所需真实 iid 增量期望可由 iid_quadraticChar_factor 的任意未来长度实例化。但该模块不证明完整 Fourier transform、convolution、inversion 或 differentiation 公式。2477–2484 实际还调用独立 low-frequency damping 和代数 power difference；当前因子和奇部估计没有替它们提供 Gaussian 衰减。3438–3447 的 whole-power derivative table 也仍需真实个体 φ_u、φ_uu、低频控制及 T-scale 工作。

## 基础 phase、矩和 iid factor 的完整证明审查

**25–49 行**私有 phase 就是 exp(i t)，没有代理函数。连续性与 norm=1 对实 t 成立；phase_sub_one 使用真实 ‖e^{it}−1‖≤|t|。phase_odd 经 exp(s+t)=exp(s)exp(t) 和 Euler 式给
\[
 e^{i(s+t)}-e^{i(-s+t)}=2i\sin(s)e^{it}.
\]
这一步保持第二相位 t，正号方向正确，没有使用 χ(−u,v)=conj χ(u,v) 的错误关系。

**51–65 行**phase_integrable 用概率下可积常数 1 支配实际相位；weighted_integrable 对任意可积实 g，通过 norm-one phase 和真 a.e. 强可测性得到 g·e^{iva²} 可积。后者本身甚至不需要 ν 概率；实际每次使用的相位仍为实 v。

**67–84 行**moments_of_third 用概率下可积的 1+|a|³，逐点证明 |a| 与 a² 受其支配，得实际 h1、h2。没有从非可积积分的默认值推均值或二矩；所有后续线性修正和求导都获得了真可积性。

**86–91 行**norm unit bound 由 norm-one 相位和概率质量一直接给出，数学上不需要 h3。**105–124 行**iid factor 先将真实 uSₙ+vQₙ 展开成 Σᵢ(uXᵢ+vXᵢ²)，用 exp(sum)=product 后才按观测独立性 factor。每坐标是同一 Xᵢ 的耦合 phase；以 hLaw 合成该实际可测 phase，再转移各坐标 integral 到相同 ν。没有把 Xᵢ 与 Xᵢ² 当作两个独立对象。

本轮服务器只读 Probability/Independence/Integration.lean:454–463 确认 integral_fun_prod_comp 的真实要求是各 Xᵢ a.e. 可测、各 phase 在其真实 mapped marginal 下 a.e. 强可测，均由 hX 与连续 phase 提供。这里还有 norm-one 支配确保所有坐标 phase、有限乘积及样本 phase 真可积；不是借一般非可积 product integral 的全定义值制造 factorization。空 Fin 0 的真实 product、exp(0) 和概率积分都为一，故 n=0 无需特殊非空前提。

## 两次 dominated parameter integral 的真实条件

**126–136 行**odd_identity 先对两个已证明可积的真实 characteristic integrand 使用 integral_sub，再逐点 phase_odd，得到
\[
 d_v(u)=2i\int\sin(ua)e^{iva^2}\,d\nu.
\]
它在概率 ν 下不需矩，但后续矩假设足够，整个积分对象未变。

**138–156 行**分别建立 sin(ua)、a cos(ua)、a²sin(ua) 的真可积性：使用 1、|a|、a² 的实际 dominator，再配合 weighted_integrable。**158–178 行**对正弦积分求导，取 s=univ，原 integrand 对每个参数都 a.e. 强可测且在目标 u 可积，derivative integrand 也可测；所有实 r 的导函数 norm≤|a|，h1.abs 提供固定可积 dominator。点态实参数 chain rule 产生 a cos(ra)，再乘固定 e^{iva²}。

**180–204 行**对 a cos(ra) 的积分再次求导，仍用 s=univ；原 integrand 真可积，derivative integrand 是 −a²sin(ra)e^{iva²}，可测且对所有实 r 以 a² 为 norm dominator，h2 提供其真可积性。这里不需要四阶矩或对 ν 的支持作界。

本轮服务器只读 Analysis/Calculus/ParametricIntegral.lean:284–303 确认 hasDerivAt_integral_of_dominated_loc_of_deriv_le 实际要求：

- s 是 u 的邻域；
- F(r,·) 在 u 附近 a.e. 强可测，F(u,·) 真可积；
- F′(u,·) a.e. 强可测；
- 对 a.e. a、所有 r∈s，真实导函数 norm 由同一可积 bound(a) 支配；
- 对 a.e. a、所有 r∈s，实际 HasDerivAt 成立。

该 API 返回 derivative-integrand 真可积性与积分函数的 HasDerivAt。实现逐项提供全部条件，且 dominator 与 r 无关；没有用只在单点的界假装局部统一支配。此处 law ν、二次频率 v 都固定，只有线性频率 r 变化。

**206–215 行**把正弦积分的实际导数乘 2i，经对每个 r 都成立的 odd_identity 转为真实 d 的 HasDerivAt。**217–233 行**先对 a cos integral 的实际导数乘 2i，将积分负号提出，得到 −2i；再用第一条公开 HasDerivAt 在每个 r 给出的真实 deriv 值作函数相等转换。因此第二导数确是 deriv(deriv d)，不是另定义了一个形式表达式就声称为 d″。

## 余项、线性修正和全部常数

**235–265 行**分别以实际分解
\[
 \sin b\,e^{ic}-b=(\sin b-b)e^{ic}+b(e^{ic}-1),
\]
\[
 \cos b\,e^{ic}-1=(\cos b-1)e^{ic}+(e^{ic}-1)
\]
得到全实 b,c 的 bounds：
\[
 \|\sin b\,e^{ic}-b\|\le|b|^3/6+|b||c|,\qquad
 \|\cos b\,e^{ic}-1\|\le b^2/2+|c|.
\]
使用 |sin b−b|≤|b|³/6、cos≤1 与 1−b²/2≤cos b，以及真实 phase_sub_one；没有局部小频假设。

**267–279 行**integral_linear_error 在 weighted g 与 c·a 均真可积后才拆 integral_sub，并明确将真实实均值 integral_ofReal 转成复数。没有漏掉 i，或把 μ 改为预设零值。

**289–309 行**令 b=ua、c=va²。点态 sine error 恰受
\[
 (|u|^3/6+|u||v|)|a|^3
\]
支配；其积分由真实 h3 提供。奇部的整体系数 ‖2i‖=2，故余项常数精确变成 |u|³/3+2|u||v|；线性修正为 +2ium，从 d 中减去。**318–331 行**以三角不等式恢复 d 的未修正界，线性项 norm=2|m||u|，没有中心化。

**343–367 行**一阶修正以实际 d′ 公式和同一 linear integral helper，代入 cosine error：
\[
 |a|\bigl((ua)^2/2+|va^2|\bigr)
  =(u^2/2+|v|)|a|^3.
\]
乘 ‖2i‖ 得 m₃(u²+2|v|)，常数一与二均正确。**368–385 行**用实际负二阶导数公式及 |sin(ua)|≤|ua|，得到 norm integral≤|u|m₃，再乘二，精确为 2m₃|u|。负号对 norm 无影响，但实际 derivative theorem 已正确保留。

全部 integral norm bound 都有真 h3 支配；没有把某个非可积被积函数的默认积分零当作估计。所有余项使用同一固定真实 ν 及其 m₃。

## 边界、反例防线和范围

- **u=0：** d(0,v)=0、线性修正为零、余项 RHS 为零；但 d′(0,v)=2iE[a e^{iva²}] 一般不等于 2im，一阶误差确允许 2m₃|v|。d″(0,v)=0 与二阶 RHS 为零一致。
- **v=0：** 退化成真实线性特征函数奇部，保持非中心线性项与三阶 remainder；任意正负 u 都由绝对值控制。
- **任意实 v、正负频率和格点律：** 结果是多项式误差和 unit norm，没有全频 Gaussian damping。即使共振时 χ=1，声明也不矛盾。
- **ν=δ₀：** χ=1，m=m₃=0，奇部及其导数全为零；无正方差要求。ν=δ₁、v=0 时 d=2i sin u，保留 2ium 是必要的。
- **n=0：** 真总和与 energy 都为零，exp(0)=1，空乘积和 χ⁰=1；不从空 hLaw 代替显式 μ、ν 概率前提。
- **固定 v 的部分反转：** χ(−u,v) 一般不是 conj χ(u,v)。本实现以精确 phase_odd 而非错误共轭关系处理，因此没有把 v 的符号一起反转。

**最终裁决：CORRECT。** 冻结 1 定义、7 定理及所有私有证明保全了实际 source real-plane odd estimate 和真实有限 iid factor。源码未见 sorry/admit/new axiom/unsafe/native_decide 或跨模块 _private 依赖。

仍开放的依赖包括 whole-power/T-scale 表、个体 characteristic derivatives 所需后续接口、低频 variance-retention/spectral-gap 阻尼、law-adapted 高频 smoothing、复移位/倾斜域、Fourier inversion 与 derivative transport、clock 概率、严格 CDF 平滑误差和完整 C1/C2。该模块不改变原 q>0、严格 CDF 边界或零能量约定，也没有将上述目标作为假设后循环使用。
