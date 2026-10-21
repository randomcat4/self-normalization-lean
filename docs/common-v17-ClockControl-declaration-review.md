# ClockControl 独立声明审查

STATUS: CORRECT（声明阶段，尚无候选实现证明）

冻结 scope：C:/game/shao lean/drafts/c12/ClockControl-next-scope.md。
SHA256：0f39fda02d4b854b4969601b62bf8a5cd8a75a3c17d18fcc8bf4ba6813146afb。

本轮先仅提取共享 Lean binders 和三条 theorem 签名，独立重译实际量词，再读完整 scope 与原 source，最后核算全部积分条件、常数、边界和小矩因子。只审零定义、三定理的拟议声明及数学可闭合性，没有候选 proof 可作最终证明审查。未实施、未运行本机或服务器 Lean、未重编既有目标、未重试服务器连接；只使用本机已有源码，未改 scope、实现或他人文件。CORRECT 不表示已有内核证明或完整 D3 专门化。

## 一、全部签名的独立盲译

三条共同量化任意 n∈ℕ、任意带可测结构的 Ω、实际概率 μ:Measure Ω 和 ν:Measure ℝ、X:Fin n→Ω→ℝ，并共同输入：每个 Xᵢ 可测、iIndepFun X μ，以及每个 Xᵢ 在 μ 下与 id 在 ν 下 IdentDistrib。ν 是实际固定边际 law，μ 是真正承载该 iid 样本的概率 measure，不能将随机保留样本、原未条件化 sample 或另一个 tilted law 无条件代入。

每条均输入实 h≥0 及 ν-a.e. |a|≤h。令实际 raw moments

    m2=∫a² dν， m3=∫|a|³ dν， m4=∫a⁴ dν，
    Q_k(ω)=prefixSquares (samplePath X ω) k，
    D_k(ω)=Q_k(ω)−(k:ℝ)m2。

Q 是实际原坐标平方和，不是 variance、中心坐标平方和或代理能量。ν 的均值未要求零，也没有 V>0 条件。

1. iid_bounded_clock_exp_integral（scope 90–101）：量化 k∈ℕ、k≤n 及任意实 θ，输入 |θ|h²≤1，结论真实 exp(θD_k) 在 μ 下可积，并且

       Eμ exp(θD_k) ≤ exp(2θ²(k:ℝ)m4)。

   θ 有符号；θ=0、k=0、n=0 均允许。没有 m2/m4 可积额外假设；必须由真概率与 a.e. 有界支持推导，不能把不适当的总积分默认值作矩。

2. iid_bounded_clock_deviation_le（114–126）：量化 k∈ℕ、k≤n、δ,θ∈ℝ，输入 δ>0、θ>0、θh²≤1，给真实闭偏差事件

       μ.real{δ≤|D_k|}
         ≤ [exp(2θ²(k:ℝ)m4)−1]/[cosh(θδ)−1]。

   分母是真实 cosh excess；δθ>0 须推出它严格正。没有额外 union-bound 因子二，也没有把分子 exp(exponent)−1 改为 exp(exponent)。m4=0 或 k=0 时分子仍精确为零。

3. iid_bounded_clock_bad_probability_le（139–154）：量化实 h,y，输入 h≥0、y≥2 和上述真实 ν 支持，另输入

       3/4≤(n:ℝ)m2≤4/3，
       (1+y)h≤1，
       8(1+y)²h²≤1，
       [8(1+y)²]²(n:ℝ)m4≤1/2。

   结论为实际两个事件的实概率之和

       μ.real{Q_(n/2)<1/16}
         + μ.real{energy(samplePath X)∉[1/4,2]}
       ≤ 2048 sqrt(2π) [(1+y)³(n:ℝ)m3] standardNormalTail(y)。

   n/2 在 Nat 中作下取整；其后才作相应实数计算。首事件严格小于 1/16；末事件是闭区间 [1/4,2] 的补集，即 Q_n<1/4 或 Q_n>2，阈值原子保留在好集。右端使用已接受的真实 standard Gaussian tail，不是外加 tail proxy 或 Gaussian approximation 输入。

## 二、既有定义及真实 source 核对

实际读取 library/Shao/Basic/FinitePath.lean:27–31：

    prefixSquares a k = ∑ i∈univ.filter (i.val<k), (a i)²，
    energy a = ∑ i:Fin n, (a i)²。

同时读取 library/Shao/Probability/FiniteIID.lean:20 的 samplePath X ω i=X i ω。故前缀是严格索引 i.val<k，k≤n 时恰有 k 项，k=n 时等于真实最终 energy；超出 n 的 prefix 会饱和，因此第 1、2 条的 k≤n 是实际必要范围，不能默删。

本轮实际读取 main.tex:553–556、638–640，以及 supplement.tex:823–858、3078–3150、3895–3907。来源冻结哈希：

- main.tex：beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06。
- supplement.tex：b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd。

main:554 的 Q_i=ΣA_j²、Q_0=0 与本接口一致。supplement:836–844 的 h:lem:clock 的确是半长 raw clock 严格小于 1/16 与最终 raw clock 不在闭 [1/4,2] 的两个概率和。其证明 3078–3150 依次作阈值到偏差的包含、真实 centered-square B=A²−m2 的双向 exponential、cosh minus one 的 Markov，以及 m4≤h_xm3 和 Mills 支付；三条声明忠实分解了这条实际链。

源 3082–3099 提供尺度/Taylor 区间，3084 提供 raw normalization，3117–3126 给 θ²nm4≤1/2。当前第三条把这些真正数值后果列为输入，未假设目标 clock probability 或 MGF inequality；它不自动证明原 D3 的截断预算已经蕴含所有输入。

源 Λ_y=(1+y)n|μ_A|+(1+y)³nm3 含非负均值项。当前直接付给较小的 raw-cube 项，是由该 elementary clock proof 得出的合法加强；最终乘数、tail 都非负，专门化后可用 raw-cube 项≤Λ_y 恢复源形式。没有将 μ_A 设为零。

## 三、独立数学可闭合性：真可积与小因子

### 真有界支持与单坐标 MGF

ν 是概率、id 是 Borel、|a|≤h ν-a.e.，因此 a、a²、|a|³、a⁴ 真可积，且

    0≤m2≤h²， 0≤m3， 0≤m4≤h m3。

这些是实际积分比较；需要有限概率质量，不能对任意无限 measure 将常数 integrability 默设。由真实 IdentDistrib 将支持和相应积分输送到各 Xᵢ，在有限交集上取得全部坐标的共同 a.e. 支持；没有要求每个 ω 都满足支持。

对 B(a)=a²−m2，在支持上 B∈[−h²,h²]。真可积性允许算出 EB=0、EB²=m4−m2²≤m4。|θ|h²≤1 时 |θB|≤1，实 Taylor 不等式 exp t≤1+t+2t² 给

    E exp(θB)≤1+2θ²m4≤exp(2θ²m4)。

exp(θB) 本身由 exp(|θ|h²) a.e. 支配而真可积。符号 θ 无限制；没有在 θ<0 时错误翻转不等式。

### 固定前缀 factorization 与第一条

当 k≤n，filtered Fin n 指标集合恰有 k 项。可用显式与 Fin k 的 bijection，或 filtered-set cardinal 恒等式证明这一点。实际前缀 centered clock 是这些项 B(Xᵢ) 的和，所以 exponential 为它们的 product。

每项及有限 product 均可测且 a.e. 由有限常数支配。实际原 iIndepFun 的固定 subfamily/可测复合仍独立，故真积分分解；每一项真实 marginal expectation 满足上段 MGF 界。将非负上界取 k 次幂给 exp(2θ²k m4)。这里没有随机指标选择、条件 iid 捷径或 source-independent expectation identity 作为输入。

即使 k=0/n=0，empty product 是一、D_0=0，积分等于一，第一条边界精确成立。h=0 时 A=0 ν-a.e.，各坐标亦 μ-a.e. 零，任意 θ 都合法，结论仍是一对一。

### Cosh excess 与第二条没有丢失矩因子

分别对 ±θ 使用第一条。两种 exponential 都真可积，故其平均与减去可积常数一均真可积；概率质量一使 E1=1。用真实 cosh identity 得

    E[cosh(θD_k)−1]≤exp(2θ²k m4)−1。

左侧 integrand 逐点非负。θδ>0 给 c=cosh(θδ)−1>0；cosh 偶且在绝对值上单调，所以 {δ≤|D_k|} 上 cosh(θD_k)−1≥c。可测的真实 deviation event 由有限多项式 D_k 得到。非负真可积变量的 real Markov 正好给第二条分式，不需 atomlessness，不需分裂正/负事件作 union bound。

这个步骤保留分子 −1 是关键。m4=0 时全部真实 clock deviation 消失，分子必须零；普通 Chernoff 的裸 exp bound 并不能自动支付小截断预算。

## 四、第三条的常数、自然数半长与全部乘法条件

令 a=1+y≥3、θ=8a²>0、k=⌊n/2⌋。

### 先合法建立半长和事件包含

由 ah≤1、h≥0、a≥3，得 h≤1/3，故 m2≤h²≤1/9。配合 nm2≥3/4，得到 n≥27/4；n 是自然数，所以 n≥7。这排除 n=0/h=0/m2=0，且不需要新增前提。

自然数除法给 k≤n 且 k≥n/3；可按 n=2q+r、r∈{0,1} 证明，并在已有 n≥7 下安全处理奇数。这里 k/n 比较的 casts 必须在 Nat quotient 定义后进行，不能用实数 n/2 代替 ⌊n/2⌋。

因此 k m2≥(nm2)/3≥1/4，最终 clock 的中心 nm2∈[3/4,4/3]。逐点有

    {Q_k<1/16} ⊆ {|Q_k−k m2|≥1/8}，
    {Q_n∉[1/4,2]} ⊆ {|Q_n−n m2|≥1/8}。

第一条事实上有中心与阈值至少 3/16 的距离，第二条的两端距离至少 1/2 和 2/3；选 δ=1/8 保留充分余量。闭偏差事件包住原严格坏事件，不借助任何边界零质量假设。prefixSquares n=energy 是实际定义桥，而非额外随机变量替换。

### Cosh 余量、原点四矩及系数 2048

hstep 就是 θh²≤1，可对 j=k,n 用第二条。由 hbudget 和 m4≥0、j≤n，有

    0≤2θ²j m4≤1，
    exp(2θ²j m4)−1≤4θ²j m4≤4θ²n m4。

这里 exp excess 的线性化用真小矩预算，未把 exp(2θ²nm4) 当绝对常数后丢失 nm4。θδ=θ/8=a²≥9，e^(a²)≥4，故

    cosh(a²)−1≥e^(a²)/4>0。

每个 deviation probability≤16θ²nm4 exp(−a²)，两个概率和≤32θ²nm4 exp(−a²)。代 θ²=64a⁴ 得

    bad probability sum≤2048 a⁴nm4 exp(−a²)
      ≤2048 a³nm3 exp(−a²)。

最后一步用真 m4≤h m3、ah≤1，所有 a、n、m3、指数因子均非负；不是在没有符号条件时直接乘不等式。此处仍保留完整的 (1+y)³nm3 小量。

### 真实 Gaussian tail 的标量桥

既有 GaussianTail 的 actual Mills lower bound 在 y≥0 上为

    standardNormalTail(y)≥exp(−y²/2)/[sqrt(2π)(1+y)]。

本轮实际核对其公开声明 standardNormal_mills_bounds；复用已独立接受的标准 Gaussian density 公式和正性，未重验其证明。对 y≥0，由 1+y≤exp y 可得

    (1+y)exp(−(1+y)²)≤exp(y−(1+y)²)≤exp(−y²/2)。

故 exp(−a²)≤sqrt(2π)standardNormalTail(y)，得第三条精确常数 2048sqrt(2π)。这是两个真实标量 Gaussian 函数的比较，不是待证样本 Gaussian/BE 结论，也不循环假设 clock 或 Fourier 控制。

## 五、边界与不适当改弱条件的反例

- n=0/k=0 在前两条合法，D=0，MGF 积分一；第二条的 δ>0 使偏差事件空，分子零。第三条 normalization 已排除 n=0，且能实际推出 n≥7。
- θ=0 只在第一条允许。若第二条删 θ>0 而代 θ=0，分子分母在 Lean 中均零，RHS 变零，但例如 X 对 {0,1} 公平分布、n=k=1、δ=1/4 时实际偏差概率为一。δ=0 同样不能允许：即使 k=0，事件为全空间而分母零。
- h=0、零 law、常值非零 law、非零均值、零方差都包括在前两条。第三条可以允许常值非零 law，只要 normalization 和预算实际满足；其坏 clock 事件仍按真实 raw square 定义处理。
- k≤n 不能去掉。直接反例为 ν=δ1、n=0、k=1、h=1、θ=−1/4：空样本的实际 saturated prefix 为零，D=−1，|θ|h²≤1，但左 exp(θD)=exp(1/4)，右 exp(2θ²k m4)=exp(1/8)，不等式失败。空坐标的 measurability/independence/common-law 条件均真，故确实是缺少长度范围的反例。
- 有限原始二矩不能代替 bounded support。给 {+2^r,−2^r} 合计质量 7·2^(−3r)、r≥1，各符号均分，则总质量一，二矩为七，但绝对三矩、四矩和每个正指数平方矩都发散。这验证了必须施于真实有界条件 law，不能只用原 ξ 的 L2 就声称 MGF 真可积。
- 所有 cutoff 支持为闭条件；clock 首坏事件严格，末坏事件为闭区间补集，deviation event 为弱不等式。阈值原子被安全包含而非删除。μ.real 的概率均有限，且这些事件可测，不依赖未证明的原子消失。

## 六、与 source law、旧 retained 和其他结果的界限

源使用 η_x=cond ν0{|a|≤h_x}，h_x=ε/(1+x)，并在全坐标有界 conditioning 后取得实际 iid/common marginal。旧 retainedCutoffLaw 的 |a|≤1/r 可由 r=(1+x)/ε 精确表示，但必须实际证明集合/measure 相等、conditioning mass 正及所用 source raw moment budgets；不能直接拿 r=x 或旧粗界 nm3≤2/r³ 就宣称保留了 R_n(x) 小因子。

scope 把这条 D3 专门化明确列为未完成；所建议使用真 conditional integral、截断原始三矩和 cutoff mass lower bound 的路线与本接口相容。hbudget 是真实有界 ν 的四矩预算，不要求原 ξ 的全局三/四矩。sample μ 可以是已证明概率的真实 all-bounded conditional measure 或其 canonical product image，不能未经条件 law 桥直接保留原 μ。

later square/joint tilted laws 的支持可能仍有界，但其 m2/m3/m4 与 normalizers 改变；第三条的具体 normalization 和预算必须在那个实际 law 下重证。原增量 variance 不参与本 raw clock proof；把 Q 改为 Σ(A−EA)² 会丢失 2(EA)Σ(A−EA)+k(EA)²，当前声明没有作这种替换。

本次无需 OQ4 module、BE/CDF approximation 或 Wald/stopped-clock 结论。已接受 Gaussian tail 仅作最后 scalar Mills 桥。小 y 的 desmoothing Chebyshev、D3 exact budget transport、倾斜时钟和完整 source lemma 的实例化均不因 generic 接口而自动完成。

## 裁决

CORRECT：固定哈希的三条声明数学成立。真实有限前缀的 raw centering、signed MGF 真可积、cosh excess 正分母、四矩小因子、自然数半长、严格/闭事件包含及常数 2048sqrt(2π) 均正确，无需数学签名修订。

未来实现须真实完成 bounded moments、a.e. support/common-law transport、固定前缀 cardinal/bijection、independent product integration、cosh excess Markov、事件包含和 Gaussian scalar comparison，再接受定向服务器与传递公理门及新 proof 审查。当前只有声明审查；不声称候选 proof 已完成，也不宣称完整 clock/Fourier/C1/C2 或 OQ4 根结果闭合。
