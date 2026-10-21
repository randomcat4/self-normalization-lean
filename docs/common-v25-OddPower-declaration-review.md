# OddPower 独立声明审查

STATUS: CORRECT（声明阶段，零定义、三个公开定理）

冻结 scope：C:/game/shao lean/drafts/c12/OddPower-next-scope.md。
SHA256：005abcc7752ff48345617c7e946dc616494907ad57637017abff82b6ef989c3d。

本轮先只提取三个拟议 theorem 签名，独立翻译实际量词、系数和自然数边界，再读完整 scope、原 source 和必要已接受公开声明，最后核算有限幂 jet、长度比例、漂移与常数。只审声明数学和 source 适用范围，没有实施，没有候选 proof 可作最终审查。未运行本机或服务器 Lean、未复跑已接受目标、未重审旧证明、未改作者文件。CORRECT 不表示已有内核证明或完整 Fourier 比较闭合。

## 一、实际声明盲译

三条共同量化真实概率 ν:Measure ℝ，输入 h3:Integrable(a↦|a|³)ν。ν、实 v 和自然幂长度在对实 first frequency 求导时均保持固定。沿用已接受

    χν(u,v)=∫exp(i(ua+va²))dν，
    μ=∫a dν， m2=∫a²dν， m3=∫|a|³dν， V=variance id ν。

μ 是实际非中心均值，m2 为 raw 二矩，m3 为 raw 绝对三矩。无一条要求 μ=0、law 对称、原 ξ 的全局三矩或 ν 的四矩。

### 1. 真实单坐标 derivative payment

quadraticChar_single_derivative_bounds（scope 140–148）只要求 ν 概率与真实 h3，u,v 任意实数。令 f(r)=χν(r,v)，结论

    ‖f'(u)−iμ‖≤m2|u|+m3|v|，
    ‖f''(u)‖≤m2。

没有 V>0、bounded support 或频率限制；原子/常值 law 和零方差都允许。deriv 是实际实参数复值导数，不是形式偏导或自由 derivative 参数。

### 2. 全自然数长度的真实幂差 jet

quadraticChar_odd_power_residual_bounds（160–190）再输入 V>0，任意 ℓ∈ℕ、u,v∈ℝ，以及真实 γ=m3/V 的闭低频条件

    |u|≤1/(128γ)， |v|≤|u|/(128γ)。

记

    q=exp(−Vu²/32)， N=(ℓ:ℝ)，
    N1=((ℓ−1:ℕ):ℝ)， N2=((ℓ−2:ℕ):ℝ)，
    a0=2|μ||u|+m3(|u|³/3+2|u||v|)，
    a1=2|μ|+m3(u²+2|v|)， a2=2m3|u|，
    L=|μ|+m2|u|+m3|v|，
    d(r)=χν(r,v)^ℓ−χν(−r,v)^ℓ。

三个结论是

    ‖d(u)‖≤N a0 q^(ℓ−1)，
    ‖d'(u)‖≤N a1 q^(ℓ−1)+N N1 L a0 q^(ℓ−2)，
    ‖d''(u)‖≤N a2 q^(ℓ−1)
        +2N N1 L a1 q^(ℓ−2)
        +N N1 m2 a0 q^(ℓ−2)
        +N N1 N2 L² a0 q^(ℓ−3)。

所有 q 的指数都在 Nat 中先作饱和减法；N1/N2 也先 Nat 减法再 cast。ℓ 是任意自然数，不要求为奇数。q 是实际正实指数，非假设的 characteristic modulus；p=χ(u,v)、r=χ(−u,v) 可以不相等，不输入任何非零条件。

### 3. ℓ≥6 的 source 形状归一化表

quadraticChar_odd_power_lowFrequency_normalized（218–245）输入 ν 概率、h3、V>0，n,ℓ∈ℕ、ℓ≤n、ℓ≥6、3/4≤nm2、n|μ|≤1、m2≤4V，以及同一实际 γ 的闭低频条件。定义

    T=ℓm2，
    A=ℓ|μ||u|+ℓm3(|u|³+|u||v|)，
    B=ℓ|μ|+ℓm3(u²+|v|)，
    R=sqrt T(1+sqrt T|u|)， E=exp(−Tu²/256)，
    d(r)=χν(r,v)^ℓ−χν(−r,v)^ℓ。

实际三行结论为

    ‖d(u)‖≤2EA，
    ‖d'(u)‖≤4E(B+RA)，
    ‖d''(u)‖≤18E[ℓm3|u|+RB+T(1+Tu²)A]。

T 仍是 raw 二矩乘长度，未换为 ℓV 或独立自由参数；E、R 均由这个同一 T 定义。n=0 与 normalized 条件不相容，但没有加额外 n>0 输入。没有 nm2 上界、T<y² 或目标 derivative bound 作为假设。

## 二、实际来源及已接受依赖

本轮实际读取 supplement.tex:2343–2401、2445–2486、3420–3459、2860–2863，并定向定位 J=8 与 L2 的实际约束。来源冻结哈希：main.tex beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06；supplement.tex b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd。

源 2343–2357 确实用 ℓ=n−i、T=ℓm2，odd Fourier factor 是 (1/2)[χ(u,v)^ℓ−χ(−u,v)^ℓ]Ξ(u,v)。当前只审 Ξ 之前的实际幂差，没有假装已给 Dℓ 连同 noise 的导数。

source 2397–2399 是真实有限 geometric polynomial identity。2477–2484 的低频 zeroth bound 以及 3441–3447 的三行 derivative table 与当前 A、B、R、T 结构一致。3431–3436 的 individual derivative estimate 恰对应第 1 条；3450–3452 的两种二阶计数恰对应第 2 条的两个 H'' 项。

source 2461–2462、3437 给 L2≥2J+4，J=8，且 T≥L2γ²、m2≤γ² 推 ℓ≥L2≥20。故当前 ℓ≥6 覆盖目标 source 长度区间，未强加 source 不具备的非空长度条件。不过从实际 source 参数形式化导出该长度，还需 genuine γ/m2 比较；这些额外 γ 结论没有被当前 SourceTruncationBridge 八条自动交付，不能把后续实例化说成已闭合。

source nm2≤4/3、nV≥1/2 蕴含 m2≤(8/3)V≤4V；source n|μ|≤Λ_y<η0/2，η0≤1/16，蕴含当前 n|μ|≤1。它们都是同一实际条件 law 的事实，非强迫 μ=0。当前归一化不需 source 的 nm2 上界或 T<y² 作为其它输入，是合法加强，不宣称那些外部条件已形式完成。

本轮仅核必要已接受 public declarations，不重验其 proof：

- QuadraticCharacteristic：8fd7815191dbd1ba9180159effe8c353d8b82d998d4d0d50bb6f957355b628f5。实际 odd_bound 提供 a0，odd_derivative_bounds 及 HasDerivAt companions 提供 a1、a2 和真实 differentiability。
- QuadraticCharacteristicPower：5a51275c796d3bd0cc59b496a15b21e1c6bd5afd101b72f66a4c5e83511164c8。singleton iid 专门化给实际 χ' 积分/χ'' differentiability；其 law-only second bound 在 ℓ=1 化成 V+μ²=m2。
- LowFrequencyDamping：ffdeace2421a3c0fdf63def48eb96b882f9dc98014e5614d226a07f87a02bb65。真实闭低频域给 χ(u,v)、χ(−u,v) 的 norm 均≤q。

这些对象全部基于同一真实 ν，没有 surrogate law、moving law、log characteristic 或目标 odd-power bounds 作依赖。

## 三、单坐标可积、方向和 jet 的独立可闭合性

概率与真实 h3 给实际 L1/L2。singleton Fin 1、X=id、μ=ν 的确是可测 iid/common-law 样本；以已接受有限幂 derivative 结果在 ℓ=1 的实际积分身份，得到

    χ'_u=i∫a exp(i(ua+va²))dν。

减去 iμ 之前，a exp、a 以及其差均真可积。实相位的全局 |exp(it)−1|≤|t| 给 pointwise

    |a||exp(i(ua+va²))−1|≤|u|a²+|v||a|³。

右边真可积，积分得到第一条；χ'' 的真实 norm≤m2 亦由已接受 power derivative 的 ℓ=1 结论给出，无需新四矩或复制 dominated-integral proof。

令 f(r)=χ(r,v)、g(r)=χ(−r,v)、δ=f−g。实际 real chain 是

    g'(u)=−χ'_u(−u,v)， g''(u)=χ''_uu(−u,v)。

因此两边 individual derivative norm 都≤L、second norm 都≤m2；δ 的实际值/一阶/二阶 norm 则由既有 odd theorems分别≤a0、a1、a2。首阶 a1 保留 2|μ|，二阶负频率的两次 chain 产生正号；没有把 χ(−u,v) 当完整 complex conjugate。

需要的是 f,g 在 u 的真实二次可微性和该点 jet bounds。q 只是在该点的 norm 上界，不需对低频不等式或 q(r) 求导；即使固定 v 使低频域不是 u 的邻域，也不影响这些全实参数函数已建立的 differentiability。这里没有从不可微时 deriv 的默认值推 bound。

## 四、finite polynomial 的全部系数与小指数

对所有实参数 r，定义真实有限和

    Hℓ(r)=Σ_{j<ℓ} f(r)^j g(r)^(ℓ−1−j)， d=δHℓ。

这由 commutative-ring geometric identity 成立，不需要除 f、g 或 f−g。对 ℓ≥1，每个 summand 恰有 ℓ−1 个 factor；零阶共有 ℓ 项，首阶总数 ℓ(ℓ−1)，二阶有一项 factor 的 second derivative 共 ℓ(ℓ−1) 项，两项 first derivative 的有序选择共 ℓ(ℓ−1)(ℓ−2) 项。因此

    ‖Hℓ‖≤N q^(ℓ−1)，
    ‖Hℓ'‖≤N N1 L q^(ℓ−2)，
    ‖Hℓ''‖≤N N1 m2 q^(ℓ−2)+N N1 N2 L² q^(ℓ−3)。

d'=δ'H+δH'，d''=δ''H+2δ'H'+δH'' 给第二条的四项，特别是 mixed term 的二、one-second term 的 m2 及 two-first term 的 L² 均正确。各 norm coefficient 非负，norm sum/product 的真实 finite bounds 可以直接用，不需随机量或 measure 交换。

- ℓ=0：d=1−1=0，H 为 empty sum，所有右项均有 N=0；q^0=1，不存在负指数。
- ℓ=1：H=1，H'=H''=0；N1=0，三个 bounds 仅剩 a0、a1、a2。
- ℓ=2：H=f+g，H''=f''+g''；one-second term仍为 2m2，N2=0 移除不可能的 two-first term。不能把它整个 H'' 错删。
- ℓ=3：最后一项保留 q^0，确实没有未被求导的剩余 factor。

当长度小于相应 derivative count，系数消失而不是把 Nat 减法改成负实数。实际 proof 需据这些边界处理 Nat casts/指数加法，不能在零长度直接替换 N1=N−1 或 N2=N−2。该数学处理可闭合，声明未隐瞒边界。

## 五、归一化付款、ℓ≥6 和最终 2/4/18

真实 V=m2−μ²、0≤V≤m2，由 h3 的 L2 和概率得到。V>0 还推出 m3>0，故 γ=m3/V>0，低频中的实除法有正号保障。由 strip 得

    m3|v|≤V|u|/128≤m2|u|/128，
    L≤|μ|+2m2|u|。

写 N=ℓ、Nn=n 的实值。由 N≤Nn、3/4≤Nn m2、Nn|μ|≤1，可以仅除已知正的常数 3/4 得

    Nn μ²≤(4/3)m2， N²μ²≤(4/3)T，
    N|μ|≤2sqrt T， NL≤2sqrt T+2T|u|=2R。

不需要除 χ、N、T 或 V；所有 sqrt-square conversion 使用 T≥0。n=0 不可能满足 normalized positive scale，ℓ≥6 亦已排除它。

对 j=1,2,3，ℓ≥6 给 Nat residual length ℓ−j≥ℓ/2。m2≤4V 因而给

    V(ℓ−j)/32≥Vℓ/64≥ℓm2/256=T/256，
    q^(ℓ−j)≤E。

这是 exponent 实值的正确方向；ℓ=6,j=3 的最差比例恰为 1/2。无需 characteristic 非零，仅用实际正 exponential 与 natural power identity。

系数直接有 Na0≤2A、Na1≤2B、Na2=2N m3|u|、N1,N2≤N。用 NL≤2R，三个 residual bounds 分别≤

    2EA，
    E(2B+4RA)，
    E[2Nm3|u|+8RB+2TA+8R²A]。

R²=T(1+sqrt T|u|)²≤2T(1+Tu²)，故

    2TA+8R²A≤18T(1+Tu²)A。

余下首两项的系数二、八也都≤18，得到第三行；第二行≤4E(B+RA)。所以 2、4、18 和 exponent 1/256 全部正确，mixed first-derivative contribution 没有遗漏。三行可统一采用 source 常数 C=18，但不是源原文给定数值或最优值。

## 六、非中心边界与未完成外部目标

- u=0 在真实 γ>0 下迫使 v=0；d(0)=d''(0)=0，但 d'(0)=2iℓμ。B 中 ℓ|μ| 不能删。例如 n=ℓ=6，ν 对 μ±s 公平分布，μ=1/6、s=1/sqrt6，满足 normalized scale/bias/variance comparison；原点 d'(0)=2i 非零。删去 B 的 drift 后 RHS 会变零。
- 负 u,v 和闭域端点均允许；全部 polynomial/chain reasoning 对原子 law 也有效。第一条允许常值 law 与 V=0，后两条则显式 V>0，不定义常值 law 的 0/0 damping 域。
- 幂差在 f=g 或某个 characteristic 值为零处依旧是 polynomial，不能使用 logarithmic differentiation 或 χ'/χ。q 总是正 exponential，也无需求倒数。
- normalized 表只声明 ℓ≥6；较小长度由完整 residual 表覆盖，未给不存在的剩余因子凭空分配统一 Gaussian fraction。
- source 的真实固定条件 law、raw moment/bias、variance comparison 和足够 future length 仍须实际实例化；当前 h3 不要求原未截断变量全局三矩。Later tilted law 或随 u 改变的 law 不在默认消费范围内。
- 本表尚未乘 (1/2)Ξ；noise derivatives、noise 构造、cone/高频阻尼、complex shifts/tilts、oscillatory inversion/区域积分、strict-CDF smoothing、clock 的 h_x 专门化和完整 C1/C2 均不由这三条声明闭合。

## 裁决

CORRECT：固定哈希的三个声明数学成立，无需签名修订。真实 χ 的单坐标 derivative、全自然长度 finite-power difference jet、Nat 0/1/2/3 边界、非中心 drift、无 characteristic 除法的路线、ℓ≥6 的 residual damping 以及最终 2/4/18、1/256 常数均正确，source 目标长度范围实际可覆盖。

未来实现必须真实完成 finite polynomial 的两次 differentiation、每个 small-exponent 分支和负频率 chain，再进行仅新 target 的服务器检查、module ownership 全新/依赖公理门、禁项与冻结 source hash，以及新的独立 proof review。本轮没有候选 Lean proof，也不以作者 API probe 作为定理验证。
