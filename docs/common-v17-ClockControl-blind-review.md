# ClockControl 最终独立源语义与证明审查

STATUS: CORRECT（冻结的三个真实有界 law 时钟定理）

本轮复用此前独立声明盲译，先核对共同 binders 和全部三个公开签名，再完整审查 468 行实现及全部八个 private theorem，最后读取并核对作者执行回执。没有运行本机或服务器 Lean，没有重复通过的 target 或旧依赖，没有修改实现、scope 或他人文件。本报告是独立源码数学裁决；执行门身份单独列明，不冒充本审查自己的服务器内核检查。

## 冻结绑定与范围

- 实现：C:/game/shao lean/drafts/c12/ClockControl.lean。
  SHA256：c7782d17c1b6dec827cde84d1d44f9b6cb7a7d8dd166bee2183cac4d2dd5cdba。
- 原冻结 scope：C:/game/shao lean/drafts/c12/ClockControl-next-scope.md。
  SHA256：0f39fda02d4b854b4969601b62bf8a5cd8a75a3c17d18fcc8bf4ba6813146afb。
- 既有独立声明盲译：C:/game/shao lean/drafts/c12/ClockControl-declaration-review.md。
  SHA256：851e7809f5a1ff2ba08d2f85c2453c6cc95a1e5cfe8965b0d4ef424c7e401378。
- 作者执行回执：C:/game/shao lean/drafts/c12/ClockControl-review-receipt.md。
  SHA256：d248abb925a45c5d40586b77fb0ef56b07ac64d1f57eea9fb47d11dd9afdb586。

本轮实际读取并确认实现、scope、receipt 哈希匹配。scope 使用共享 section variables，最终实现将它们显式展开到每个 theorem：n、Ω 可测结构、μ/ν、两个概率实例、X 的顺序和隐式性均相同。机械比较这个共同 binder 块，以及随后从 hX 到完整类型末尾的文本，三条均逐字匹配。实现没有新定义，显式声明恰为三个公开 theorem 和八个 private theorem。

## 一、实际量词和事件的保全

共同量化任意 n∈ℕ、任意可测空间 Ω、实际概率 μ:Measure Ω、ν:Measure ℝ、X:Fin n→Ω→ℝ；输入每个 Xᵢ 可测、iIndepFun X μ、每个 Xᵢ 与 id 在 μ/ν 下 IdentDistrib。实 h≥0 与 ν-a.e. |a|≤h 是真实 bounded law 条件。

记 m2=∫a²dν、m3=∫|a|³dν、m4=∫a⁴dν，Q_k=prefixSquares(samplePath X)k，D_k=Q_k−(k:ℝ)m2。原增量均值未要求零，增量方差未要求正；Q 是 raw-square clock，D 只中心化 A²。

1. 第 136–212 行 iid_bounded_clock_exp_integral：对任意 k∈ℕ、k≤n、实 θ 且 |θ|h²≤1，真实 exp(θD_k) 在 μ 下可积，并有 E exp(θD_k)≤exp(2θ²(k:ℝ)m4)。θ 的两种符号和零都允许；n=0/k=0 包括。
2. 第 214–285 行 iid_bounded_clock_deviation_le：对 k≤n、δ>0、θ>0、θh²≤1，实际弱偏差事件的概率

       μ.real{δ≤|D_k|}
         ≤ [exp(2θ²(k:ℝ)m4)−1]/[cosh(θδ)−1]。

3. 第 326–466 行 iid_bounded_clock_bad_probability_le：输入 y≥2、3/4≤nm2≤4/3、(1+y)h≤1、8(1+y)²h²≤1 和 [8(1+y)²]²nm4≤1/2，结论

       μ.real{Q_(n/2)<1/16}
         + μ.real{energy(samplePath X)∉[1/4,2]}
       ≤2048 sqrt(2π) [(1+y)³nm3] standardNormalTail(y)。

n/2 是实际 Nat quotient，下取整后才 cast。首事件保持严格 <1/16，最终事件为闭区间补集，等号阈值仍在好集；偏差事件保持 δ≤|D|。m2/m3/m4 全部是实际 ν 的 raw moments，有限性由支持推出，没有另添原 ξ 全局三/四矩、均值零、MGF、clock probability 或 Gaussian approximation 结论作输入。

## 二、既有定义和 source 对应

此前声明阶段已实际核对：samplePath X ω i=X i ω；prefixSquares 是 Fin n 中 i.val<k 的 filtered raw-square sum，energy 是全 Fin n 的 raw-square sum。因此 k≤n 时前缀恰有 k 项，k=n 时等于真实最终 energy。当前实现使用这些既有对象，没有修改有限和约定。

来源冻结：main.tex SHA256 beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06；supplement.tex SHA256 b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd。既有声明审查已实际读取 main:553–556、638–640，supplement:823–858、3078–3150、3895–3907。

source h:lem:clock（836–844）确是这两个 raw-clock 坏事件，proof 3078–3150 确实先比偏差、对 B=A²−m2 建立 signed exponential，再通过 cosh minus one 保留 nm4，最后由 m4≤h_xm3 和真实 Mills lower bound 得 tail 支付。当前三条声明和实际证明都保留这条链。

此模块把真实 bounded conditional law 的数值后果列作参数。它未自动证明原 D3/h_x 预算已经蕴含这些输入；source-specific 桥在最终边界中继续保留。省去 Λ_y 中非负的漂移项是 elementary clock estimate 的合法加强，不是将原 A 均值设为零。

## 三、八个私有证明和第一条 MGF

### 真矩可积与 A² 的正确中心化：第 14–68 行

bounded_power_integrable 对任意自然数 p，用 a.e. |a|≤h 和实幂的 norm 恒等式获得 |a^p|≤h^p；在真实概率空间上用 Integrable.of_bound 得真可积。私有 lemma 不另输入 h≥0，但每个实际使用的支持点已有 0≤|a|≤h，幂单调性的符号条件就在该点成立；公开定理也保留冻结 hh。不存在对负 h、正质量支持的错误幂估计。

square_mean_bounds 以实际 integral_mono_ae 与概率一常数积分给 0≤m2≤h²。centered_square_support 由 a²,m2∈[0,h²] 给 |a²−m2|≤h² a.e.。

centered_square_moments 先建立 a²、a⁴ 真可积，再用明确多项式恒等式和各项真可积性证明 B² 真可积、EB=0、EB²=m4−m2²≤m4。这里 B=A²−m2，所需中心化与原 A 是否均值零无关；没有把 raw clock 换成 Σ(A−EA)²。

### Signed 单坐标 MGF：第 70–116 行

one_clock_exp_bound 由 |θ|h²≤1 和真实 a.e. B bound 得 |θB|≤1。第 86–90 行先以常数 exp 1 支配真实 exponential，证明真可积；第 91–110 行亦明确证明并使用 Taylor 右边每个多项式项的真可积性。

实 exp remainder 给 exp(θB)≤1+θB+2θ²B²。积分、EB=0、EB²≤m4 得 1+2θ²m4，再用 1+x≤exp x。没有把非可积总积分的默认零当成指数矩，也没有要求 θ>0；θ 负号由绝对值 range 正确控制。

### 固定前缀显式双射：第 118–134 行

prefixSquares_sum_castLE 通过 Finset.sum_bij 给出 Fin k 到 filtered Fin n 的实际 i↦i.castLE hk。证明包括映入过滤条件、castLE 注入、每个 j.val<k 的显式逆像和 summand 相等。故真正恰有 k 个坐标，并包括空 Fin 0；不是直接把 saturated prefix 的中心误写成 k m2。

### 真实 subfamily factorization 和整个积分：第 152–212 行

Y_i=X_(i.castLE hk)，B(a)=a²−m2，hD 逐点识别实际 D_k=Σ_i:Fin k B(Y_i)。第 165–170 行以真实 IdentDistrib 把 ν 下 B 支持传到 μ 下每个 Y_i。有限 ae_all 合并后，得到 |D_k|≤k h²，第 171–190 行以 exp(|θ|k h²) 为真可积常数支配整个 exponential。这一步独立于 factorization，故不是用总积分恒等式回避 integrability。

第 191–197 行从 castLE 的注入性取得实际 iIndepFun Y，坐标可测、真实 exp 可测，并用实际 independent product-integral theorem 和实际 common-law integral_eq。单坐标 exponential 真可积性已由前述 one_clock_exp_bound 建立；完整 product 也有 hD/hi 的实际 integrability 保证。

第 198–205 行逐点用 exp(sum)=product exp，将真实积分识别为同一个 ν 积分的 k 次幂。再以该积分非负性、单坐标 MGF 和实数自然幂/指数恒等式得到 exp(2θ²k m4)。没有样本依赖选取、虚构 iid、全局原变量 M4 或外加有限和矩身份。

## 四、Cosh excess 与小矩因子：第 214–285 行

实际对 +θ、−θ 分别调用第一条，两个 hθ 条件均由 θ>0 与冻结 hstep 合法转换。exp 的两种分支都真可积，才能构造 f=cosh(θD)−1 的真可积性。第 245–264 行由真实 cosh identity、积分加/除/减以及 E1=1 得

    E f≤exp(2θ²k m4)−1。

分子保留 −1。没有用 union bound 多出因子二，也没有把小因子替换成裸 exp 常数。

c=cosh(θδ)−1 的正性由 θδ>0、真实 one_lt_cosh 给出，除法前已有 hc:0<c。cosh 的绝对值单调性和 θ,δ>0 给弱偏差事件 {δ≤|D|}⊆{c≤f}。f 全局非负，hfi 已是真可积；real Markov 使用的正是它。μ 为概率，所有实 measure 的单调转换都有有限质量保障；事件本身也是可测有限多项式/连续函数的阈值集。

因此 ratio 不是零分母的约定值，不用原子消失。k=0 或 m4=0 时 numerator 仍为零，实际偏差也消失，small-moment payment 得到精确保全。

## 五、第三条的全部数值和事件步骤

### 实际四矩到 raw cube 和真实 normal tail：第 287–324 行

fourth_le_bound_mul_cube 先从 bounded third power 的 norm 得真实 |a|³ 可积，再和真四矩作 integral_mono_ae；在实际支持上 a⁴=|a|·|a|³≤h|a|³。因此 m4≤h m3 是实际积分结论，不是新增假设或对原未截断 law 偷用全局 cube。

clock_exp_le_normal_tail 对 y≥0，用已接受真实 Gaussian density 公式 c⁻¹exp(−y²/2)、c=sqrt(2π)>0 和 Mills lower bound，得到 exp(−y²/2)≤c(1+y)Tail(y)。另一方面

    (1+y)exp(−(1+y)²)
      ≤exp(y−(1+y)²)≤exp(−y²/2)。

最后以明确 1+y>0 消去共同正因子。没有使用样本 Gaussian comparison/BE 或 proxy tail；tail/density 来源是已独立接受的 GaussianTail。

### Nat 半长与正性：第 346–376 行

实际取 a=1+y≥3、θ=8a²>0；m2,m3,m4 均非负。由 a h≤1、h≥0 推 h≤1/3，再得 m2≤h²≤1/9。若 n≤6，便与 nm2≥3/4 矛盾，故推导 n≥7，而非增加新样本量前提。

hk:n/2≤n 是 Nat 真 quotient 的基本界。hk3 先在 Nat 中借助 n≥7 证明 n≤3(n/2)，随后才 exact_mod_cast 到实数；没有以实数 n/2 替代自然数 floor。因此 k=⌊n/2⌋ 的奇数分支合法，并有 k m2≥nm2/3≥1/4。

### 小 excess、正 denominator 和 2048：第 377–417 行

由 a≥3 得 e^(a²)≥4，故 cosh(a²)−1≥e^(a²)/4>0。hdev 对任意 j≤n 保留实际 nm4：从 m4≥0 和 hbudget 得 0≤2θ²j m4≤1，实 exponential-excess bound 给

    exp(2θ²j m4)−1≤4θ²n m4。

取 δ=1/8，则 θδ=a²。对第二条的真实 denominator 使用上述正下界并作正号乘法，得到每个 deviation probability≤16θ²n m4 exp(−a²)。没有把 exponential-excess 粗化成一后丢掉矩预算。

### Strict/closed 事件包含与最终付款：第 418–466 行

hsub1 用 k m2≥1/4 和 Q_k<1/16 得实际弱偏差≥1/8；hsub2 通过 prefixSquares_length 将 Q_n 精确识别为 energy，再将闭 Icc 补集分为 energy<1/4 或 energy>2，分别用 center∈[3/4,4/3] 得弱偏差≥1/8。全部为逐点包含；没有把 strict 换为 weak 后丢掉原子，也不要求 sample 有密度。

两项概率和≤32θ²n m4 exp(−a²)=2048a⁴n m4 exp(−a²)。由实际 m4≤h m3、a h≤1、所有因子非负，证明 a m4≤m3，得

    sum≤2048a³n m3 exp(−a²)
       ≤2048sqrt(2π)a³n m3 Tail(y)。

最后一乘仍明确使用非负 a³n m3，没有除 m3、n、h 或 small budget。常数、Nat casts 与 raw moments 均对应冻结声明。

## 六、全部边界与仍开放的 source 桥

- 第一条 θ=0、k=0/n=0：实际 D_0=0、empty sum/product 与 exponential integral 都为一。h=0 同样允许，两种 ν/X 支持通过真实 common law 后 a.e. 为零，界仍精确成立。
- 第二条显式 δ,θ>0，保护 cosh denominator。不能删它们：δ=0 时 k=0 的偏差事件为全空间而分式为零；θ=0 时非恒定 Bernoulli square 的偏差可有正概率而 RHS 总定义为零。
- k≤n 由显式双射使用，不能删掉。ν=δ1、n=0、k=1、h=1、θ=−1/4 时 saturated prefix 为零、D=−1；删 hk 后左 exp(1/4) 大于右 exp(1/8)。当前声明正确排除此例。
- 第三条由实际 support/normalization 推出 n≥7；n=0/h=0/m2=0 不满足 lower normalization。常值非零 law 和零 increment variance 没有被无故排除，只要所列 budgets 真满足就合法。
- 所有支持与最终好钟区间为闭边界，首坏事件严格，deviation 为弱阈值。阈值原子均由真实包含式安全处理，未改 energy convention。
- 真实源 law 是 cond ν0{|a|≤h_x}，h_x=ε/(1+x)。现模块未证明其 cutoff mass 正、真实 iid conditioned sample law 或 D3 exact normalization/small-moment budgets；它们要由相应 source-specialization bridge 提供。旧 reciprocal cutoff 参数需实际改为 (1+x)/ε 并证明 set/measure 相等，不能直接取 x。
- 仅用原 ν0 的 L2 不能替代 bounded support；全局 cube/fourth/exp-square 可能发散。当前 h3/m4 都在真实 bounded ν 下推导，没有新增原 ξ 全局矩。
- 后续 square/joint tilted laws 的 moments/normalizers 改变；必须在那个具体 law 下重证 numerical hypotheses。Q 未被改成 centered-coordinate energy，因此没有遗漏 2(EA)Σ(A−EA)+k(EA)² 的交叉项。

## 七、执行证据身份与最终裁决

协调者提供、冻结作者回执记录：准确 source target 服务器 exit 0、stdout/stderr 空；另外 fresh import 检查三 public types 并执行完整 module-ownership audit。审计用 env.getModuleIdxFor? 的真实 ownership，不仅凭名字前缀：新 ClockControl 26 个声明、GaussianTail 29、FiniteIID 8、FinitePath 67，总计 130 个项目声明均只含 propext、Classical.choice、Quot.sound。新 26 包括 3 public、8 private、15 generated；特别覆盖在本模块生成、名字却为 Shao.Probability.samplePath.eq_1 的声明，未因 prefix 筛选漏掉。

所交付依赖哈希为 FinitePath 898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb、FiniteIID d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b、GaussianTail f166fab0061199e25d0391bbde5c977905e368513a6e0e18b492877c65160922。这些已有公共语义和证明复用，不重验旧依赖。

本轮未复跑上述 target/audit，也未把回执文字当作证明。我的独立证据是完整冻结源读取、共同 binders 与三签名字节比较、全部八个 private 和三个 public proof 的实际数学核对，以及对新源完整禁项扫描；sorry/admit/axiom/unsafe/native_decide 均零匹配。源码数学观察和作者实际服务器验证分别成立，身份未混淆。

CORRECT：固定源 c7782d17c1b6dec827cde84d1d44f9b6cb7a7d8dd166bee2183cac4d2dd5cdba 完整实现三条冻结定理。真实 bounded integrability、iid prefix exponential factor、cosh minus one 的小矩支付、正分母、Nat 半长和 strict/closed 事件，以及实际 normal-tail 系数全部闭合，未发现源数学缺口。

此裁决只接受 generic bounded-law ClockControl 模块，不宣称 h_x/D3 专门化、small-y desmoothing Chebyshev、tilted-clock transport、完整原 clock/Fourier/C1/C2 或 OQ4 能量分母结论已经完成。
