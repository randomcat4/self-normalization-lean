# QuadraticCharacteristicPower 最终独立源语义与证明审查

STATUS: CORRECT（固定真实 law 的五个全实频率有限幂定理）

本报告先核对全部实际公开声明与原冻结提案，再核来源锚点，最后完整审查 437 行实现，包括所有 23 个私有 lemma 和五个公开 theorem。未运行本机或服务器 Lean，未重复作者成功 target，未改实现、scope、依赖或他人文件。这里的 CORRECT 是独立源码数学裁决；作者服务器编译及公理门的执行事实另列，不冒充本审查自己的内核检查。

## 冻结绑定和精确范围

- 实现：C:/game/shao lean/drafts/c12/QuadraticCharacteristicPower.lean。
  SHA256：5a51275c796d3bd0cc59b496a15b21e1c6bd5afd101b72f66a4c5e83511164c8。
- 原冻结 scope：C:/game/shao lean/drafts/c12/FourierPower-next-scope.md。
  SHA256：a0c19a11198fa35d63cb78ea7c066f427b2d1a91fb159f5951d5a8b0a1074943。
- 既有独立声明审查：C:/game/shao lean/drafts/c12/FourierPower-declaration-review.md。
- 作者执行回执：C:/game/shao lean/drafts/c12/FourierPower-review-receipt.md。
  SHA256：633350be9a304b66c9f278a7820e1bc7f49f9a46a801e46bfac0956e55a4086b。
- 复用已独立接受的真实 quadraticChar、iid factor、samplePath、prefixSum、energy；QuadraticCharacteristic 源 SHA256 为 8fd7815191dbd1ba9180159effe8c353d8b82d998d4d0d50bb6f957355b628f5。
- 复用实际共享 iid 二矩入口：FiniteIIDMoments 源 SHA256 为 d2417f73424ea90a13edb10bdad267d638d66fec432c3107362a2d0246fe2bfa。本轮其最终迁移与旧兼容入口已另立 FiniteIIDMoments-shared-blind-review.md，结论 CORRECT；没有要求消费者 import OQ5，也没有重建一份 iid 原点二矩证明。

本轮实际读取并确认实现、scope、receipt 哈希匹配。将 scope 五个 lean 代码块中的完整 theorem 声明，与实现中从 theorem 名至 := by 之前的完整文本逐字比较，五条均相同。实现没有新增公共定义；显式源码包含 5 个公开 theorem、23 个 private lemma，其余审计计数可能包含生成项。

## 一、全部实际量词和零边界的独立重译

沿用已核定义 χν(u,v)=∫ exp(i(ua+va²)) dν，是真实 ν 的积分。没有另设代理 characteristic、自由矩参数或随 u 改变的 law。

前两条共同量化任意 ℓ∈ℕ、任意带可测结构的 Ω、概率 μ:Measure Ω、概率 ν:Measure ℝ 和 X:Fin ℓ→Ω→ℝ，并输入每个 Xᵢ 可测、iIndepFun X μ、每个 Xᵢ 在 μ 下与 id 在 ν 下 IdentDistrib，以及真实 ∫a² dν 可积。u,v 任意实数，固定 ν、v 后对实变量 u 求导。记

    S(ω) = prefixSum (samplePath X ω) ℓ = ∑ i : Fin ℓ, X i ω,
    Q(ω) = energy (samplePath X ω) = ∑ i : Fin ℓ, (X i ω)^2.

1. 第 125–141 行 iid_quadraticChar_power_hasDerivAt：实际 r↦χν(r,v)^ℓ 在 u 的 HasDerivAt 值为

       i * ∫ S(ω) * exp(i(u S(ω)+v Q(ω))) dμ.

2. 第 143–165 行 iid_quadraticChar_power_deriv_hasDerivAt：实际 r↦deriv(s↦χν(s,v)^ℓ)(r) 在 u 的 HasDerivAt 值为

       - ∫ S(ω)^2 * exp(i(u S(ω)+v Q(ω))) dμ.

这里第二条对第一条的实际 deriv 再求导，且权重是平方的总和 S²，包含所有交叉项；并非 Q，也不是未证明存在的形式偏导。两条均没有 ℓ>0 前提，ℓ=0 的 S=Q=0、幂为一、两个积分导数值为零。

后三条只量化真实概率 ν 和 h2:Integrable(a↦a²)ν。令

    m = ∫ a dν,  m2 = ∫ a^2 dν,  V = m2-m^2,
    f(r) = χν(r,v)^ℓ.

3. 第 358–379 行 quadraticChar_power_derivative_bounds：对任意 ℓ∈ℕ、u,v∈ℝ，

       ‖f'(u)‖ ≤ sqrt(ℓ V) + ℓ |m|,
       ‖f''(u)‖ ≤ ℓ V + ℓ^2 m^2.

   m、m2、V 均为实际 ν 的积分/差，不是额外输入。没有 m=0、V>0 或 bounded support 条件。

4. 第 381–405 行 quadraticChar_power_derivative_scale_bounds：再量化 n,ℓ∈ℕ、ℓ≤n、θ,B∈ℝ，输入 θ>0、θ≤n m2、n|m|≤B。真实 T=ℓm2，结论

       ‖f'(u)‖ ≤ sqrt(1+B^2/θ) * sqrt T,
       ‖f''(u)‖ ≤ (1+B^2/θ) * T.

   B≥0、m2≥0 等支付所需条件从输入推出，没有新增正性输入。n=0 或 m2=0 不满足正 lower normalization；ℓ=0 仍允许且 T=0。没有假设 T>0、除以 T 或除以 ℓ。

5. 第 407–435 行 quadraticChar_power_global_normalized：对 n,ℓ∈ℕ、ℓ≤n，输入 3/4≤n m2、n|m|≤1，以及任意 σ,u,v∈ℝ、|σ|=1。令 f(r)=χν(σr,v)^ℓ、T=ℓm2，结论

       ‖f(u)‖ ≤ 1,  ‖f'(u)‖ ≤ 2 sqrt T,  ‖f''(u)‖ ≤ 3 T.

   任意 u,v 包括零、负频率及共振点；σ=±1 均覆盖。没有频率区域、非零频率、正方差、上界 n m2≤4/3、三阶矩或四阶矩前提。

## 二、真实 source 的对应与没有偷换的尺度

本轮实际重新读取 supplement.tex:2614–2617、3403–3417、524–527、3398–3400、3453–3457。来源冻结为 main.tex SHA256 beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06、supplement.tex SHA256 b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd；既有声明审查已核 main:546–578 的真实固定条件增量和 S、Q、空未来定义。

supplement:3403–3417 的实际证明先用 E|Sℓ−ℓm|≤sqrt(ℓV)、E(Sℓ−ℓm)²=ℓV，再对 (Sℓ,Qℓ) 的 characteristic 求导，得到首导数的 sqrt(ℓV)+ℓ|m| 与二导数的 ℓV+ℓ²m²。当前第 1、2 条补足其真实求导身份，第 3 条保留全部漂移项。源 2616 的 whole-plane a=0,1,2 与 ±u 由第 5 条覆盖。

实际来源的 T=(n−i)m2，故 ℓ=n−i、0≤i≤n 给当前 T=ℓm2 和 ℓ≤n。没有用 ℓV 替换 T，也没有自由选择一个与 ν 无关的 T。源 525 给 n m2≥3/4；3399、3454 给 n|m|≤Λy<η0/2，既有冻结来源 η0≤1/16，故当前较弱 n|m|≤1 合法。仍须在实际源条件 law 上提供这些真实事实；本模块不假装已由粗 cutoff 1/x 的 retained-moment 定理完成 h_x 截断 law 的数值实例化。

本实现不用源的上界 n m2≤4/3 或 V 与 m2 的比较，因为 raw second moment 与 general lower normalization/bias 已足以给出更直接的常数。省略它们是成立的加强，非将 V=m2 或 m=0 默设。

## 三、逐段真实证明审查

### 1. L2、真可积与两次支配积分求导：第 18–165 行

phase_norm 对实 t 给真实 exp((t:ℂ)i) 的 norm 恰为一。law_memLp_two 由 h2 和 id 的真可测性转为 id∈L2(ν)。sum_memLp_two 用每条实际 IdentDistrib.memLp_iff 将它传给 Xᵢ，再经有限求和得到实际 S∈L2(μ)；这一步无需独立性，也没有误用单坐标二矩控制单坐标四矩。

exp_integrable 的 dominator 是概率空间上可积常数一；hS、hQ 提供真可测性。weighted_exp_integrable 对任意真可积权重 g 以 |g| 支配，使用 hg 的 AEStronglyMeasurable/ofReal 与相位可测性；不是以非可积 Bochner 积分默认值代替实际积分。

exp_hasDerivAt 通过实参数 r↦rS+vQ、复嵌入、乘 i 和真实 cexp chain 给 iS exp(i(rS+vQ))。第 71–94 行第一次 dominated derivative 取 s=univ，明确建立：每个参数相位的 AEStronglyMeasurable、基点真可积、基点导函数 AEStronglyMeasurable、对几乎处处 ω 的所有参数统一 norm 界 |Sω|、|S| 的真可积，以及逐点 HasDerivAt。L2 加概率先得到 S∈L1。积分常数 i 的移动合法。

第 96–123 行对 S exp 的第二次求导同样逐项给出真实条件，dominator 是 S²，hS2.integrable_sq 保证其可积。权重导数为 iS² exp，复实嵌入和乘法排列由 ring 对齐。这里只对 u 求导；固定 vQ 只处在 modulus-one 相位里，所以完全不要求 Q² 可积或第四矩，也未对 v 作隐藏求导。

第 125–141 行以已核 iid_quadraticChar_factor 对每个真实参数 r 将实际样本积分识别为 χν(r,v)^ℓ。第 143–165 行先对 weighted integral 乘 i 后求导，i²=−1 给正确负号；再用第一条在每个 r 的 .deriv 身份，把被求导的函数识别为实际 deriv power。不存在从 Lean 不可微时 deriv 默认零反推导数界的漏洞；前两条均先建立真实 HasDerivAt。

### 2. 真实 canonical product、绝对矩界与 scale 支付：第 167–288 行

canonical_law 通过 measurePreserving_eval 的实际 map_eq 给每个 eval 坐标的 IdentDistrib，canonical_indep 用 iIndepFun_pi；底层确是 Measure.pi(fun _:Fin ℓ=>ν)，没有任意“独立副本”假设，也没有把随机保留子集直接当成 iid。

canonical_sum_memLp 复用实际 L2 传输；canonical_sum_mean 对每一坐标先证明 L1，再用 integral_finsetSum 与真实 marginal integral_eq 得 ES=ℓm。未在积分和交换时跳过可积性。

abs_integral_le_sqrt_second 对 |Y| 的真实 L2 使用 variance_nonneg、variance_eq_sub，得到 (E|Y|)²≤EY²；配合 E|Y|≥0、sqrt(EY²)≥0 和 sqrt 的平方身份推出 E|Y|≤sqrt(EY²)。只在概率质量一和真实 L2 下使用该界。canonical_derivative_integral_bounds 将前两条实际导数身份与 unit phase 结合，得到首导数≤E|S|、二导数≤ES²；所用 norm-integral 界都有真可积的绝对值/平方 dominator。

scale_payment（239–270）是纯实代数，不假设待证 derivative 或 sum moment。记 N=(n:ℝ)、L=(ℓ:ℝ)。它先从 θ>0、θ≤N m2、N≥0 推 m2≥0，并从 N|m|≥0 与 hbias 推 B≥0，从而可以合法平方 hbias。关键实际链为

    θ N m² ≤ (N m2) N m² = m2 (N|m|)² ≤ m2 B²,
    N m² ≤ (B²/θ) m2,
    L²m² ≤ L N m² ≤ (B²/θ) Lm2.

第一链只乘非负因子，唯一除数是输入已知正的 θ；第二链用 L≤N、L≥0。最后从 L(m2−m²)+L²m² 中丢弃非正的 −Lm²，得 (1+B²/θ)T。没有漏掉 n 因子、用 B 而非 B²、除以零时间或以虚构 centered moment 支付漂移。

abs_integral_center_bound 对真 L2 Y 和实常数 c，先由逐点 |Y|≤|Y−c|+|c| 和全部真可积性得到积分三角界，再对 Y−c 使用上段 Cauchy–Schwarz。概率保证常数的积分确为常数；这里没有把非概率质量默认成一。

### 3. 真实一/二阶 chain 与复用原点二矩：第 290–356 行

power_hasDerivAt 与 power_deriv_hasDerivAt 在 canonical product 上应用前两条，只把已证 HasDerivAt 改写为其真实 deriv 值。signed_power_deriv 用实 σr 的 scomp 给一个 σ；signed_power_second_deriv 对实际首导数函数再作 chain 和常数乘法，给两个 σ。第二条在所有参数处用第一条身份改写，故 σ=−1 的首阶方向和二阶平方均正确。

canonical_sum_second 第 327–330 行直接调用共享 finite_iid_sumSquare_integral，实际坐标和的 body 通过第 331–335 行桥接到 prefixSum；没有复制通用 iid 二矩证明。对 ℓ=0 先以真实空和处理；仅 ℓ≠0 时才用 1≤ℓ 作 Nat.cast_sub。因此合法得到对所有 ℓ 的

    ES² = ℓ(m2−m²)+ℓ²m².

不是在 ℓ=0 将 ((ℓ−1:ℕ):ℝ) 错改为 ℓ−1。canonical_centered_second 用 S 的真 L2、真实均值与 raw-square identity 计算 Var(S)=ℓVarν(id)，再用 variance_eq_integral 与 law_variance_eq 得

    E(S−ℓm)² = ℓ(m2−m²) = ℓV.

law_variance_eq 已在第 26–29 行由实际 ν 的 L2 和 variance_eq_sub 给出，所以 V 是实际 variance、非负，不是额外未经证明的自由参数。源不需要假设 V>0，也未除以 V。

### 4. 最后三条公开定理：第 358–435 行

derivative_bounds 首阶将 E|S| 用中心积分界和真实 E(S−ℓm)² 支付，正确保留 ℓ|m|；二阶直接使用 ES²。没有把原点二矩和 variance 混同。

derivative_scale_bounds 没有简单将中心项和漂移项分别粗界再相加冒充更小系数，而是独立用 E|S|≤sqrt(ES²)，然后 scale_payment 和 sqrt 单调性。证明 1+B²/θ≥0 后才以 Real.sqrt_mul 分离乘积，得精确 sqrt(1+B²/θ)sqrt T。二阶使用同一真实 raw square payment。

global_normalized 代 θ=3/4、B=1，精确系数 7/3；证明 T≥0、sqrt(7/3)≤2。零阶由真实 norm_quadraticChar_le_one 再取自然幂；首阶用一个 σ norm 因子，二阶用两个，分别由 |σ|=1 消去，最后 (7/3)T≤3T 用 T≥0。三个常数 1、2、3 的量词和符号均正确。

## 四、边界和没有闭合的外部目标

- ℓ=0：真实 product 是空坐标的概率乘积，不要求选取一个不存在的坐标。S=Q=0、χ⁰=1，前两条导数为零，所有 derivative bound 为零；零阶仍是一。所有证明都包括这一分支，没有除 ℓ/T。
- n=0：前两条及未归一化矩结论合法；归一化前提 θ≤n m2 与 θ>0 矛盾，无须另添 n>0。实现未除 n，故不需要先专门建立其正性证书。
- ν=δ0 与 m2=0：未归一化定理仍成立，两个导数均零。常值非零 law 有 V=0，但真实导数大小为 ℓ|m|、ℓ²m²，已由漂移项保留。归一化允许零方差，不允许零 raw normalization。
- B<0 与输入不相容，B=0 则漂移为零；没有私自将任意 B 作非负常量。频率 u,v 均可为零或负数；实相位模长一对所有点有效，不需要非共振性。
- 该模块只证明对固定真实 ν 的全实平面多项式导数界。没有对 v 或复数参数求导，不能据此推出相应额外矩要求已满足；也没有 Gaussian 衰减、spectral gap 或高频 damping。
- 源条件 cutoff h_x 的真实 moment/bias/normalization 专门化、Gaussian-damped odd-power table、低频/高频阻尼、law-adapted cone、clock 概率、复倾斜、Fourier inversion、积分分部边界控制、严格 CDF smoothing/defect 和完整 C1/C2 仍不在本定理交付内。它们没有被循环用作本模块前提。

## 五、执行证据的身份和最终裁决

冻结作者回执记录、协调者确认：准确目标 source 的服务器编译 exit 0 且 stdout/stderr 空；五个公开签名核对成功；30 个新 public/private/generated 声明及 8 个实际项目语义依赖的传递公理门通过，白名单仅 propext、Classical.choice、Quot.sound。所列依赖恰为真实 quadraticChar、norm bound、iid factor、samplePath、prefixSum、energy、共享 finiteFeatureSum 和 raw-square theorem。没有把一个代理 phase 或自由 moment formula 作为依赖。

这些门本轮未由我复跑。我的独立证据是完整冻结源读取、精确哈希、五条签名逐字匹配、所有 23 个私有 lemma 与五个公开 proof 的数学审查、实际来源重核；本轮本地完整禁项扫描 sorry/admit/axiom/unsafe/native_decide 亦零匹配。已核固定 Mathlib dominated-integral API 和此前接受的项目依赖复用，不作无谓新 probe 或目标重编。

CORRECT：固定源 5a51275c796d3bd0cc59b496a15b21e1c6bd5afd101b72f66a4c5e83511164c8 完整实现原 scope 的五条冻结定理。真实有限 iid law、仅二矩的两次支配求导、积分 i/−1 方向、原点二矩复用、均值漂移、θ/B/T 支付、σ chain 和全部零边界均闭合，未发现源数学缺口。此裁决精确限于 h:supp:powerglobal 的固定 law 全实平面输入，不泛化为完整 Fourier 比较或 C1/C2 结论。
