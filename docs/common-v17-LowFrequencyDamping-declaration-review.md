# LowFrequencyDamping 独立声明审查

STATUS: CORRECT（声明阶段，尚无候选实现证明）

冻结 scope：C:/game/shao lean/drafts/c12/LowFrequencyDamping-next-scope.md。
SHA256：4e65222b68f8d3e75065b9f0064bdc0ac90dc6545289c60ab05f6e9fff78cb8a。

本轮先只提取六个 Lean 签名并独立翻译量词，再读完整 scope、来源和作者证明路线，最后独立核算常数、可积性及边界。只审零定义、六定理的拟议声明及数学可闭合性，没有候选 proof 可作最终证明审查。未实施、未运行本机或服务器 Lean、未复跑既有目标、未重试服务器连接，也未修改 scope、实现或他人文件。CORRECT 不表示已有内核证明或 source-specific 条件 law 桥已完成。

## 一、签名盲译：全部真实对象、量词和条件

六条均量化任意实际概率 ν:Measure ℝ，复用已接受的

    χν(u,v) = quadraticChar ν u v = ∫ exp(i(ua+va²)) dν。

ν 固定，u,v 是任意实参数。记 M3=∫|a|³ dν、V=variance id ν。以下 h3 都是实际 Integrable(a↦|a|³)ν，不是把总积分的某个有限默认值当成矩有限。没有一条要求原增量均值为零。

1. quadratic_pair_square_moment（scope 150–155）：仅输入 h3，结论为真实 ν.prod ν 上 (a−b)² 可积，且

       ∫(a−b)² d(ν⊗ν) = 2 V。

   不要求 V>0；常值 law、零 law 均包括。独立性来自实际 product，不是把 A 与 A² 当成独立。

2. quadratic_pair_tail_square_bound（164–173）：另量化 d∈ℝ、d>0，令严格坏集

       B_d = {d<|a| 或 d<|b|}。

   实际 masked 平方 (a−b)²1_Bd 可积，且其积分≤8M3/d。声明包含真可积结论，未预设尾矩上界。

3. quadratic_pair_retained_square_lower（179–191）：输入 h3、V>0、d>0 及实际标量预算 8M3≤dV。闭保留集

       G_d = {|a|≤d 且 |b|≤d}

   上的 masked 平方真可积，且 V≤∫(a−b)²1_Gd d(ν⊗ν)。这里不是假设 retention variance lower bound，再在后面改称已证明；输入只有实际三矩/方差预算。

4. quadraticChar_gap_identity（202–206）：只输入概率 ν 和任意 u,v∈ℝ，无任何矩条件，给

       1−‖χν(u,v)‖²
         = ∫[1−cos((a−b)(u+v(a+b)))] d(ν⊗ν)。

   这是整个耦合 phase 的真实 norm-square gap。不是错误的 χν(−u,v)=conj χν(u,v) 对称断言。

5. quadraticChar_local_gap（217–227）：输入第 3 条的 h3、V>0、d>0、8M3≤dV，再量化 u,v∈ℝ，要求

       |u|d≤1/3， 4|v|d≤|u|。

   结论 V u²/16≤1−‖χν(u,v)‖²。u=0 允许，此时 d>0 与第二条件推出 v=0；没有 u≠0 或 v≠0 前提。

6. quadraticChar_lowFrequency_damping（240–252）：输入实际 h3、V>0，定义实际 γ=M3/V，在

       |u|≤1/(128γ)， |v|≤|u|/(128γ)

   下同时给

       ‖χν(u,v)‖≤exp(−V u²/32)，
       ‖χν(−u,v)‖≤exp(−V u²/32)。

   γ 不是自由正参数，也不是 M3/m2、中心绝对三矩/V 或假设已知的 spectral scale。正方差下 M3、γ 的正性须推导；不能依赖 Lean 对零除的总定义把它默认为合法尺度。最终定理没有 d、retention、gap 或 damping 假设。

## 二、与实际来源及已有接口核对

本轮实际读取 main.tex:546–551、622–625、673–678，以及 supplement.tex:1977–1983、2371–2377、3155–3192、2477–2486、3438–3459。来源冻结哈希：

- main.tex：beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06。
- supplement.tex：b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd。

main:546–551 明确是 ξ 在 {|ξ|≤h_x} 下的真实条件增量，并明确说条件均值未必为零。main:622–623 与 supplement:1979–1981 实际定义 τ²=m2−μ²、γ=m3/τ²。因此此处 V=真实 variance、M3=原点绝对三矩和 γ=M3/V 完全对应来源，没有混淆 raw 二矩和方差，也未把原增量中心化。

supplement:2371–2377 的 h:supp:lowfreq 恰为两个低频条件下 χ(±u,v)≤exp(−cτ²u²)。3155–3192 的 proof 确实用真实同 law 独立 pair，先付坏 pair 平方矩，再由总 pair 矩 2τ²得到保留矩≥τ²，最后付小角度 cosine gap 并转为 exponential。六个拟议声明把这条链分开，最终常数 κ=1/128、c=1/32 是源“存在绝对正数”的合法具体选择。

源使用随频率变化的最小 cutoff，scope 改用固定 d=16γ。对本目标这合法：新 d 同时满足尾矩和小相位要求，不需要逐字保留 min 的构造，也不引入 v=0 时的无穷大或 u=0 时的除法。该替代不改变 law、事件边界或最终频率区域。

已有 quadraticChar 是真实 coupled quadratic phase 的积分；可直接复用，不需新 characteristic 定义。此 unit 独立于 future sample 长度，不增添有限幂、iid sample 或时钟结论。来源 2477–2486 和 3438–3459 的有限幂差/导数表还需要其余代数和导数输入，不能由本声明审查宣布整体闭合。

## 三、独立证明可闭合性和常数核算

### 真正矩可积与 pair 恒等式

概率质量一和逐点 |a|、a²≤1+|a|³ 给真实 L1 与 L2。全 pair 平方由 2a²+2b² 支配；cross product ab 的绝对积分通过两个边际真实 L1 的 product 有限，再可 Fubini/线性分解。因此

    E(A−B)² = 2 E A²−2(E A)² = 2V。

这里非中心均值的平方被真实扣除；不能写成 2m2。两类 mask 集都是 Borel，masked nonnegative square 被全 square 支配，故真可积。所有积分拆分和比较都可以先完成可积性，再使用线性/单调性。

### 严格坏集的常数八

在 B_d 上令 r=|a|、s=|b|。因为 d>0 且 max(r,s)>d，有 d≤r+s、|a−b|≤r+s，于是

    d(a−b)² ≤ (r+s)³ ≤ 4(r³+s³)。

第二步的精确余量是 4(r³+s³)−(r+s)³=3(r+s)(r−s)²≥0。坏集外左 mask 为零，右边仍非负。积分后，两个 marginal cube 各贡献 M3，故坏 pair 平方矩≤8M3/d。乘/除都只用 d>0，常数八正确，不需引入原证明中的 m2M3/d³ 或额外 Lyapunov 前提。

G_d 与 B_d 在所有实 a,b 上精确互补。因而预算 8M3≤dV 给 E[D²1_Bd]≤V，与 ED²=2V 相减得到 E[D²1_Gd]≥V。|a|=d 或 |b|=d 的原子都留在 G_d，没有丢弃或重算。

### 无矩 gap 身份与局部常数十六

令 θ(a)=ua+va²。每个 exp(iθ) 的 norm 一，其 product/conjugate 在真实概率 product 上真可积，cosine gap 则介于零与二、Borel 且真可积。真实 product integration 给

    χν(u,v) conj χν(u,v) = E exp(i(θ(A)−θ(B)))。

取实部，使用 θ(a)−θ(b)=(a−b)(u+v(a+b))，得到第 4 条。整个 θ 被 conjugate；只反转 u 而不反转 v 不等于该 conjugate，拟议结论没有犯此错误。

在 G_d 上有 |a+b|≤2d，由 4|v|d≤|u| 得

    |v(a+b)|≤|u|/2，
    |u+v(a+b)|≥|u|/2，
    |u+v(a+b)|≤3|u|/2。

又 |a−b|≤2d，故完整 phase t 的 |t|≤3d|u|≤1。实初等不等式 |t|≤1⇒1−cos t≥t²/4 成立，含 t=0；例如由 sine 余项和 half-angle identity 可得更强的 25t²/72，下界 t²/4 充分。因此在 G_d 上

    1−cos t ≥ u²(a−b)²/16。

在 G_d 外 cosine gap 非负。积分并使用已付 retained square moment≥V 得 V u²/16 的真实 gap；没有将 integrand 在坏集之外错误地取负，也不假设所需 spectral gap。

### 真实 γ 正性与最终常数

M3 非负且实际有限。若 M3=0，非负可积函数 |a|³ 的零积分推出 a=0 ν-a.e.；因此真实 variance=0，与 V>0 矛盾。故 M3>0、γ=M3/V>0，d=16γ>0。

两条最终频率条件分别给

    |u|d≤16/128=1/8≤1/3，
    4|v|d≤(64/128)|u|=|u|/2≤|u|。

并且 dV=16M3≥8M3，预算成立。应用局部 gap 得 t=Vu²/16≤1−‖χ‖²。利用 1−t≤exp(−t)，得到

    ‖χ‖²≤exp(−Vu²/16)=[exp(−Vu²/32)]²。

norm 非负，exponential 严格正，故可合法从平方界推出所需 norm 界，不需除 norm 或先假设 t<1。对 −u 应用相同定理，|−u|=|u| 且 (−u)²=u²，所以另一界成立；ν 不需要对称，μ 不需要为零。

## 四、边界、改变声明的反例与 source 专门化范围

- d=0 被第 2、3、5 条显式排除，保护其 tail payment/除法。第 1、4 条无此辅助参数。
- u=0 在最终条件中，γ>0 导致 |v|≤0，所以 v=0；χ(0,0)=1，最终右端亦一。局部版本也由 d>0 推 v=0。没有除 u/v，负 u、v 由绝对值控制。
- V=0 的常值/零 law 合法进入 pair identity、tail bound 和 gap identity；最终 ratio 定理则显式要求正方差。第 3 条正方差前提虽比仅推出非负 retained bound 所需稍强，但与来源一致，不构成错误。
- 若去掉低频域，ν 对 {−1,1} 公平分布，χ(2π,0)=1，违反任何 c>0 的 Gaussian 型 exp(−cu²) 界。
- 若去掉 quadratic strip，ν 对 {0,1} 公平分布，取 v=−u≠0，uA+vA² 恒零，χ norm 一，故正 gap 不可能。
- 若把 raw M3 换为 centered cube，ν 对 {L−1,L+1} 公平分布、L>1。其 V=1、中心 cube=1，但 M3=L³+3L；取 v=−u/(2L)，两原子的 quadratic phase 相等，χ norm 一。对于任意 κ>0，选 L≥1/(2κ)、0<u≤κ 就满足错误的 centered-gamma 域而破坏 damping。真实 raw γ 恰避免这个非中心二次相位抵消。

scope 326–391 的 h_x 与 reciprocal cutoff transport 明确标为独立未证明桥。其复用方向合法：b=(1+x)/ε 对应 1/b=h_x；必须先证明真实条件集/measure 相同、conditioning mass 正、h3 和 V>0，不能直接把 b=x 或 1+x 代入旧 retained 接口。本轮只核对该必要区别和既有公开前提，不把整条 rescaling/sample-size/variance transport 宣称已形式完成。generic h3 指真实条件 law 的三矩，不要求原 ξ 的全局三矩。

## 裁决

CORRECT：固定哈希的六条声明、实际 γ=M3/V、严格/闭边界、非中心 pair 恒等式、尾矩常数八、局部 gap 常数十六及最终 κ=1/128、c=1/32 均成立，无需数学签名修订。需要实现时逐项完成真可积/Fubini、complex gap、small-angle 和 γ 正性证明；现在尚无候选 Lean proof，因此不作最终 proof/内核裁决。

本单元只闭合可实施的固定 law 低频声明。条件 h_x 的专门化、低频有限幂导数表、高频噪声/阻尼、clock、Fourier inversion、strict-CDF smoothing 和完整 C1/C2 仍不由此报告获证。
