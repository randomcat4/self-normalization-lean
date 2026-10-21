# FourierPower 独立声明与来源审查

STATUS: CORRECT（声明阶段）

本报告先独立还原五条实际拟议定理及全部边界，再核对真实来源和数学闭合链。没有候选实现可审，不宣称已完成证明代码、编译或内核/传递公理认证。未运行本机或服务器 Lean，未重复既有目标或 API 探针，也没有修改 scope、源码、共享入口或他人文件。仅新增本报告。

## 冻结材料和已接受依赖

- 提案：C:/game/shao lean/drafts/c12/FourierPower-next-scope.md。
  SHA256：a0c19a11198fa35d63cb78ea7c066f427b2d1a91fb159f5951d5a8b0a1074943。
- main.tex：C:/game/shao/current/c12/main.tex。
  SHA256：beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06。
- supplement.tex：C:/game/shao/current/c12/supplement.tex。
  SHA256：b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd。

scope 哈希本轮实际复核。所用实际 quadraticChar 及 iid_quadraticChar_factor 是此前已经独立审查的真实积分接口，未重新定义 characteristic function。

按协调者明确指示，通用有限 iid 原点二矩恒等式作为已验依赖复用。scope 所列冻结来源 SHA256 为 4b2c65ec7fb03767b6a469ef5918592c9a76e993ad95262e6a7aae6840c4520b；该恒等式涵盖任意均值、全部自然长度及 ℓ=0。公共位置迁移及兼容入口由 root 负责，本报告不要求某个 OQ5 命名空间，也不以包装状态作为数学声明缺口，不重验或重建这份已验原点二矩证明。

## 第一阶段：无新定义的五条声明实际重译

记
\[
 \chi_\nu(u,v)=\int e^{i(ua+va^2)}\,d\nu(a),\qquad
 m=\int a\,d\nu,\quad m_2=\int a^2\,d\nu,\quad V=m_2-m^2.
\]
它们都是既有操作的真实值，不是自由矩参数。所有频率 u,v 都是任意实数，law ν 在 u 变化时固定。这里总平方和 Q 与线性和 S 来自同一份样本。

### 1. iid_quadraticChar_power_hasDerivAt

任意 ℓ∈ℕ、带可测结构的 Ω、概率 μ:Measure Ω、ν:Measure ℝ、函数族 X:Fin ℓ→Ω→ℝ；要求每个 Xᵢ 可测、iIndepFun X μ、每个 Xᵢ 在 μ 下与 id 在 ν 下 IdentDistrib，以及 a↦a² 在 ν 下真正可积。对任意实 u,v，令 S=prefixSum(samplePath X)ℓ、Q=energy(samplePath X)，结论为
\[
 \frac d{dr}\chi_\nu(r,v)^\ell\big|_{r=u}
   =i\int S\,e^{i(uS+vQ)}\,d\mu
\]
的实际 HasDerivAt。没有 ℓ>0、中心化、方差正性、三矩或四矩前提。ℓ=0 也覆盖。

### 2. iid_quadraticChar_power_deriv_hasDerivAt

同一组全部参数与前提，实际函数 r↦deriv(s↦χν(s,v)^ℓ)(r) 在 u 的 HasDerivAt 值为
\[
 -\int S^2e^{i(uS+vQ)}\,d\mu.
\]
这里 S² 是真实总线性和的平方，不是 Q=∑Xᵢ²。结论是实际 power 的实际二阶实参数导数，不是给出一个未认证形式表达式。

### 3. quadraticChar_power_derivative_bounds

任意概率 ν，只输入 a² 可积；任意 ℓ∈ℕ、u,v∈ℝ。定义真实 f(r)=χν(r,v)^ℓ、m,m₂,V 后，断言
\[
 \|f'(u)\|\le\sqrt{\ell V}+\ell|m|,\qquad
 \|f''(u)\|\le\ell V+\ell^2m^2.
\]
ℓ 的乘法在实数 cast 后进行。V≥0 须从概率和实际 L2 推出，不是前提，也不要求 V>0。漂移项完整保留。

### 4. quadraticChar_power_derivative_scale_bounds

任意概率 ν、a² 可积；任意 n,ℓ∈ℕ 且 ℓ≤n；任意 θ,B∈ℝ，要求
\[
 \theta>0,\qquad \theta\le n m_2,\qquad n|m|\le B.
\]
没有单独输入 B≥0、n>0、m₂>0 或 T>0。令真实 T=ℓm₂，f(r)=χν(r,v)^ℓ，对任意实 u,v，
\[
 \|f'(u)\|\le\sqrt{1+B^2/\theta}\sqrt T,\qquad
 \|f''(u)\|\le(1+B^2/\theta)T.
\]
T 不是可自由选择的时间参数。没有上界 nm₂≤4/3，也没有任何所需 power derivative bound 作为假设。ℓ=0 允许，此时两 RHS 都为零。

### 5. quadraticChar_power_global_normalized

任意概率 ν、a² 可积；任意 n,ℓ∈ℕ 且 ℓ≤n；要求
\[
 3/4\le n m_2,\qquad n|m|\le1.
\]
再任取实 σ,u,v，并要求 |σ|=1。f(r)=χν(σr,v)^ℓ，T=ℓm₂，结论为
\[
 \|f(u)\|\le1,\qquad
 \|f'(u)\|\le2\sqrt T,\qquad
 \|f''(u)\|\le3T.
\]
σ 是实数，不是任意复 unit phase；它恰为 ±1。首导数 chain factor σ 和二阶 factor σ² 必须实际处理。没有低频 strip、cone、u≠0 或 T>0 条件。ℓ=0 时 f=1、T=0，零阶仍为一，两个导数为零。

## 第二阶段：来源绑定和尺度条件

main.tex:546–551 的真实 conditional increments iid，并明确说条件均值不必零；553–556 和 574–578 的 S、Q 与空未来和当前两个积分声明一致。622–625 的 m₂ 是原点二矩、V=τ²，而非把 m₂ 当成已中心化方差。

supplement.tex:2343–2350 定义实际 T=(n−i)m₂，future factor 为 χ^(n−i)。当前令 ℓ=n−i，0≤i≤n 给 ℓ≤n，T 逐字对应，未把它改为 ℓV 或独立于 law 的标量。

supplement.tex:3403–3417 实际证明使用
\[
 E|S_\ell-\ell m|\le\sqrt{\ell V},\qquad
 E(S_\ell-\ell m)^2=\ell V,
\]
继而支付 E|Sℓ| 的漂移 ℓ|m|，以及 ESℓ² 的漂移平方 ℓ²m²。拟议第 3 条恰保留这两个 moment-paid 式。第 1、2 条提供源“differentiate the characteristic function of (S,Q)”所省写的实际导数身份，并且只对 u 求导。

2614–2617 的 whole-plane part (d) 量化导数阶 0、1、2 和 ±u；第 5 条覆盖这三个阶数，统一常数三足够。源 525 行有真实下界 nm₂≥3/4；3398–3400、3453–3454 明确给 n|m|≤Λᵧ<η₀/2，2860–2863 固定 η₀≤1/16，所以 n|m|≤1 是源已给小漂移预算的合法放松，而非中心化假设。

源还使用 T≤4/3 和方差与 m₂ 的比较；当前第 4 条用 raw square identity 作更直接的归一化，只需下界和 full-sample drift budget，故不需要它们作为额外前提。这是数学上成立的加强，不意味着下游依赖上界的结论已经获证。

## 第三阶段：L2、真实导数与矩支付的可闭合性

### 仅二矩足以完成两次积分求导

h2 和实 id 可测给 id∈L2(ν)。经实际 IdentDistrib 运到每个 Xᵢ，有限求和给 S∈L2(μ)。概率质量一使 S、|S|、S² 都真正可积；这一步不需要独立性，仅需各坐标 L2 和真实有限和。

样本相位 F(r,ω)=exp(i(rS(ω)+vQ(ω))) 可测，norm 恒为一，因而在原概率 μ 下真正可积。对实参数 r，
\[
 \partial_rF=iS F,\qquad
 \partial_r(SF)=iS^2F.
\]
其 norm 分别由 |S|、S² 全局统一支配。Q 是真实有限路径的平方和、可测且逐点有限；对固定 v，它只在 modulus-one phase 中出现，不对 v 求导，因此不要求 Q² 可积、第三/四阶原矩或 S 与 Q 独立。

此前已独立读取的真实 dominated parameter-integral API 对一般底层类型 Ω 适用；这里原 integrability、局部强可测、目标导函数可测、固定可积 dominator 和逐点 HasDerivAt 均可由上述 L2 事实给出，取 s=univ 即可。先以已有 iid_quadraticChar_factor 对每个 r 识别实际 power，再转换导数；第二条须以第一条每个 r 的真实 deriv 身份转换后再求导，最终 i² 给负号。这是闭合论证，不假设所需 derivative bounds 或 differentiability。

law-only 结论可在真正 canonical product probability ν^ℓ 上取各坐标 eval，获得真实 iid/common law 后应用这两个身份。该构造是实际有限乘积，不是新增独立副本公理。空乘积概率也正确。

### 已验 raw square identity 的正确中心化，含 ℓ=0

复用已接受恒等式
\[
 ES_\ell^2=\ell m_2+
      \ell\,((\ell-1:\mathbb N):\mathbb R)\,m^2.
\]
从真实坐标 L1、有限积分线性和共同 law 得 ESℓ=ℓm。ℓ=0 单独以空和为零处理；ℓ>0 时才可将 ((ℓ−1:ℕ):ℝ) 改为 (ℓ:ℝ)−1。于是对所有 ℓ，整个多项式表达式等于
\[
 ES_\ell^2=\ell(m_2-m^2)+\ell^2m^2
           =\ell V+\ell^2m^2.
\]
这只是已验 identity 的代数后果，不是另建一套通用 iid 二矩证明。

id 的真实 L2 与概率给 V=E(A−m)²≥0，并可识别为实际 Mathlib variance。中心变量 Y=Sℓ−ℓm 也在 L2，展开积分得 EY²=ℓV；不能把真实原 m 假设为零。对 L2 实变量的真正 Cauchy–Schwarz 得 E|Y|≤√EY²。因此
\[
 \|f'\|\le E|S_\ell|
 \le E|S_\ell-\ell m|+\ell|m|
 \le\sqrt{\ell V}+\ell|m|,
\]
\[
 \|f''\|\le ES_\ell^2=\ell V+\ell^2m^2.
\]
所有 integral norm/linearity 均在真可积性后进行；若走 variance_nonneg/variance_eq_sub 的 Jensen 路线，也应先有这些 L2 和概率实例，不能以非可积总积分的默认值制造 moment bounds。

### θ、B、T 的支付没有缺失 n 因子

写 N=(n:ℝ)、L=(ℓ:ℝ)。h2 给 m₂≥0；θ>0 和 θ≤Nm₂ 推 N>0、m₂>0。hbias 配合 N|m|≥0 推 B≥0，故 (N|m|)²≤B²。T=Lm₂≥0。

漂移平方项可用下列全非负乘法链处理，**无需除以 ℓ 或 T**：
\[
 \theta L^2m^2
 \le\theta NLm^2
 \le(Nm_2)NLm^2
 =T(N|m|)^2
 \le TB^2.
\]
第一步用 L≤N，第二步用 θ≤Nm₂。只除以已给 θ>0，得
\[
 L^2m^2\le(B^2/\theta)T.
\]
因此包括 L=0 在内，
\[
 ES_\ell^2=LV+L^2m^2
 \le T+(B^2/\theta)T=(1+B^2/\theta)T.
\]
没有漏掉 full-sample drift 的平方或以自由时间尺度支付。

第 4 条更强的首导数常数应直接用 raw L2：
\[
 \|f'\|\le E|S_\ell|
 \le\sqrt{ES_\ell^2}
 \le\sqrt{(1+B^2/\theta)T}
 =\sqrt{1+B^2/\theta}\sqrt T.
\]
仅把第 3 条的“中心项加漂移项”分别粗界相加，通常不足以得到这一系数；提案明确选择 raw Cauchy–Schwarz，故没有此缺口。第二导数由同一 raw second moment 直接支付。

### 来源常数与 ±u chain

θ=3/4、B=1 给 1+B²/θ=7/3，故 √(7/3)≤2、7/3≤3。两者固定在阈值、law 和样本长度之前。norm χ≤1 给所有 ℓ 的 norm χ^ℓ≤1。

若 g(r)=χν(r,v)^ℓ、f(r)=g(σr)，实参数 chain rule 给 f′(u)=σg′(σu)、f″(u)=σ²g″(σu)，把实系数转成复数后 norm 因子分别为 |σ|、|σ|²。输入 |σ|=1 正好消去二者。不存在把 −u 当作“只代入数值而不改变导数方向”的问题，也不需要 σ=1 的额外限制。

## 全部边界与反例核对

- **ℓ=0：** f=χ⁰=1；真实样本 S=Q=0；两个导数身份 RHS 为零；第 3 条零界、第 4、5 条 T=0 零界均成立。零阶 bound 保持一，不靠把 T=0 的零阶表达式解释成零。
- **n=0：** 未归一化结论允许零长度。归一化中 θ≤0 与 θ>0 矛盾，故 n>0 由实际前提推出；没有先除 n 再处理。
- **m₂=0、V=0：** 原点二矩零可出现在未归一化结论；ν=δ₀ 时全部导数为零。常值非零 law 有 V=0，但导数 norm 为 ℓ|m|、ℓ²m²，已被真实漂移项保留。归一化允许 V=0，只以 m₂>0 支付。
- **B<0：** hbias 不可能满足，因左端非负；不需要额外输入 B≥0。B=0 则真实 m=0，界退化为 centered raw-square 支付。
- **任意 u,v∈ℝ：** u=0、负频率、格点共振都合法；phase norm one，所以是全平面多项式 derivative bound，不是 Gaussian 衰减。未对 v 求导，也没有复移位。
- **漂移、下界和 future-length 约束确实必要：** scope 的三类反例均可直接算出。公平 {0,√(2/n)}、ℓ=n 时 Nm₂=1，但 origin 的导数 norm 为 √(n/2)、(n+1)/2，说明不能去掉 bias budget；公平 {0,2/n} 时 N|m|=1、T=2/n，origin norm 为 1、1+1/n，说明不能去掉正 lower normalization；n=1、ν=δ₁ 而 ℓ 增大给 ℓ、ℓ² 对 T=ℓ，说明不能去掉 ℓ≤n。
- **实际条件 law：** 源 hₓ 截断 law 的 fine moment/budget 仍须由其实际来源条件提供，不能偷用粗 cutoff 1/x 的数值结论。当前定理的 ν 是固定真实 law，没有把随机保留样本无条件当 iid。

## 裁决和后续范围

**CORRECT：固定哈希提案的五条声明数学成立，真实 source part (d)、仅 L2、漂移支付、θ/B/T 归一化、±u chain 和所有零边界均正确，无需数学签名修订。**

通用二矩共享入口迁移是协调者已指定的依赖安排，不需要改动这五条声明或额外要求 OQ5 namespace。未来实现必须真实证明 S 的 L2 和两次支配积分求导，复用既有 raw-square identity 并合法处理 Nat 零边界，再完成实际 normalization 和 σ chain；当前只是可证性审查，没有候选内核证明。

完成并实例化这些定理后可提供 h:supp:powerglobal 的 whole-plane part (d) 输入；当前不闭合 3441–3459 的 Gaussian-damped odd-power table、cone 高频 product/noise derivative bound、个体 characteristic 的低频控制、支持域/复倾斜、clock 概率、Fourier inversion、严格 CDF 平滑误差或完整 C1/C2。它们没有作为本候选的假设循环使用。
