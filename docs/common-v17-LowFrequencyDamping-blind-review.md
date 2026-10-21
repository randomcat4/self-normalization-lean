# LowFrequencyDamping 最终独立源语义与证明审查

STATUS: CORRECT（固定真实 law 的六个低频定理）

本轮复用此前独立声明盲译，先逐字核对六个实际公开签名，再完整审查 414 行实现、18 个 private lemma 和一个 private phase 定义，最后读取并核对冻结作者回执。没有运行本机或服务器 Lean，没有复跑通过的 target 或旧依赖，没有修改实现、scope 或他人文件。这里的 CORRECT 是独立源码数学裁决；作者服务器检查的执行事实另列，不冒充本审查自己的内核检查。

## 冻结绑定与精确审查范围

- 实现：C:/game/shao lean/drafts/c12/LowFrequencyDamping.lean。
  SHA256：ffdeace2421a3c0fdf63def48eb96b882f9dc98014e5614d226a07f87a02bb65。
- 原冻结 scope：C:/game/shao lean/drafts/c12/LowFrequencyDamping-next-scope.md。
  SHA256：4e65222b68f8d3e75065b9f0064bdc0ac90dc6545289c60ab05f6e9fff78cb8a。
- 既有独立声明盲译：C:/game/shao lean/drafts/c12/LowFrequencyDamping-declaration-review.md。
  SHA256：e05746a95f83393ae5304bf91e97b9b9f1d6808a5ac1e7c0dd94a9569d6b994c。
- 作者执行回执：C:/game/shao lean/drafts/c12/LowFrequencyDamping-review-receipt.md。
  SHA256：3ab8db367c583333ad87bd0d9ebaeee373eaaa06ee9a01584f305e474f5b5a1f。
- 唯一项目 import 是已独立接受的 Shao.Probability.QuadraticCharacteristic，冻结源 SHA256：8fd7815191dbd1ba9180159effe8c353d8b82d998d4d0d50bb6f957355b628f5。其真实 quadraticChar 定义直接复用，没有新增公共 characteristic 或 law。

实际本地读取确认实现、scope 和 receipt 哈希均匹配。机械比较原 scope 六个 Lean 声明与实现从 theorem 名到 := by 前的完整文本，六条全部逐字相同。原 API 是零个新公共定义、六个 theorem；第 194 行 private phase 只是 literal complex exponential 的实现 helper，不改变公共 API，也不构造代理分布。

## 一、实际量词和公式保全

六条均量化真实概率 ν:Measure ℝ，χν(u,v)=∫exp(i(ua+va²))dν。除第 4 条不需矩外，使用实际 h3:Integrable(a↦|a|³)ν；记 M3=∫|a|³dν、V=variance id ν。原点三矩不是中心三矩，V 不是 raw 二矩。ν 未要求对称、原增量均值未要求零。

1. 第 58–88 行 quadratic_pair_square_moment：全 pair square 在实际 ν.prod ν 下可积，且 E(A−B)²=2V。不要求 V>0。
2. 第 137–156 行 quadratic_pair_tail_square_bound：任意实 d>0，严格坏集 B_d={d<|a|∨d<|b|} 的 masked pair square 可积，积分≤8M3/d。
3. 第 158–192 行 quadratic_pair_retained_square_lower：另输入 V>0、8M3≤dV，闭保留集 G_d={|a|≤d∧|b|≤d} 的 masked square 可积，积分≥V。retention lower bound 本身不是假设。
4. 第 233–262 行 quadraticChar_gap_identity：任意实 u,v、无矩前提，

       1−‖χν(u,v)‖²=E[1−cos((A−B)(u+v(A+B)))]。

5. 第 322–344 行 quadraticChar_local_gap：在第 3 条条件以及 |u|d≤1/3、4|v|d≤|u| 下，V u²/16≤1−‖χν(u,v)‖²。
6. 第 375–412 行 quadraticChar_lowFrequency_damping：V>0，实际 γ=M3/V，若 |u|≤1/(128γ)、|v|≤|u|/(128γ)，则同时

       ‖χν(u,v)‖≤exp(−Vu²/32)，
       ‖χν(−u,v)‖≤exp(−Vu²/32)。

所有 u,v 都是实数；零频率允许。没有新增支持、均值零、第四矩、非零频率、retained moment、cosine gap 或 damping 假设。d 只在中间定理出现，最终定理从实际矩自行构造它。

## 二、来源与已审声明一致

此前声明阶段已实际读取、独立核对 main.tex:546–551、622–625、673–678，以及 supplement.tex:1977–1983、2371–2377、3155–3192。它们的冻结哈希分别为：

- main.tex：beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06。
- supplement.tex：b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd。

main:551 明确条件增量均值未必零；main:622–623 与 supplement:1979–1981 的真实 γ 是 m3/τ²。source h:supp:lowfreq 是 2371–2377 的两个低频域下 χ(±u,v) exponential norm bound，其 proof 3155–3192 确实是独立同 law pair 的尾矩保留、真实 norm-square gap 和 small-angle payment。实现保留这条数学链，以合法的 d=16γ 替代 source 随频率取 min 的 cutoff，以 κ=1/128、c=1/32 给明确绝对常数。

这里没有把 source law h_x=ε/(1+x) 换成旧 reciprocal cutoff 1/x，也没有宣称全 source 条件 law 的输入桥已经形式完成。实现本身是对任意满足 h3 和 V>0 的固定 ν 的真实 generic 结果，不是条件 law 专门化或低频有限幂导数表。

## 三、完整证明审查

### 1. 真 L1/L2、非中心 pair moment：第 19–88 行

moments_of_third 使用概率空间的真可积 dominator 1+|a|³，并逐点分 |a|≤1 和 ≥1，建立 |a|、a² 的 norm 支配。因此获得真实 first/square integrability，没有从总积分默认值反推矩有限。

integral_fst 和 integral_snd 明确输入真实 integrability，以 ν 的概率质量一将 product marginal 积分化回原积分。pair_square_integrable 以 2(a²+b²) 支配 (a−b)²，Borel 可测性成立。

第 66–69 行由真实 L2 与 variance_eq_sub 给 V=m2−m1²。平方展开前，第 78–81 行分别证明边际平方和及 cross product 2ab 在真实 product 上可积；cross product 使用两个实际 L1 变量的 mul_prod。之后才作 integral_sub、integral_add、product factorization，得到

    E(A−B)²=2EA²−2(EA)²=2V。

非零均值项被真实扣除，不是把 ED² 错写成 2m2；没有假设原 A 为中心化 law。这里只有两份 ν.product 坐标独立，不存在 A 与 A² 的虚假独立。

### 2. Strict bad、closed good 和尾矩预算：第 90–192 行

bad_integrable 与 good_integrable 分别构造实际 Borel strict-union/closed-intersection 集，使用已证 pair-square integrability 的 indicator，再逐点识别为实际 if mask。两者真可积性先于积分拆分。

pair_tail_pointwise 的坏集分支中，d≤|a|+|b|、(a−b)²≤(|a|+|b|)²，并用

    (|a|+|b|)³≤4(|a|³+|b|³)

得到 d(a−b)²≤4(|a|³+|b|³)。只以已知 d>0 除法。坏集外左边零，右边非负；点态不等式覆盖所有 a,b，没有依赖 a.e. 边界忽略。

第 149–156 行的 integral_mono 输入双方真实 integrability；两个 marginal cube 各积分为 M3，给常数八。没有额外使用单坐标四矩或假设尾矩付款。

第 175–185 行的全 square=good square+bad square 通过完整逐点 case split 证明：若两个 |.|≤d 则两个 strict-tail 条件均假；否则线性次序的 De Morgan 给至少一个 d<|.|。因此等号原子全留在 good 集，两个集合真实互补。

随后 full moment=2V、tail≤8M3/d≤V 给 good≥V。第 187–192 行虽然绕道通过 good/V≥1，但所有除 V 的操作都显式使用输入 hV:0<V；除 d 亦使用 hd:0<d。没有零/未知号分母。

### 3. 真 complex product 和无矩 gap：第 194–262 行

private phase 逐字为 exp((t:ℂ)i)。phase_norm 给实 t 下 norm 恰一；phase_continuous 与 phase_integrable 用真实概率上的可积常数一支配；cos_pair_integrable 同样以 |cos|≤1 给实际 integrability，不需 h3。

phase_conj conjugate 的是整个 t；phase_pair 用 exp-add 和真实实数多项式恒等式给相位差

    (a−b)(u+v(a+b))。

第 238–241 行证明 conjugate phase 真可积，并与原 phase 作 mul_prod，得到真实 product integrability。conjugate 的 integrability 识别为在 (−u,−v) 的相位；没有错误地仅反转 u。

第 242–249 行用实际 product integral、integral_conj、integral_re，将真实 χν(u,v) 乘其完整 complex conjugate 的实部识别为 ‖χν(u,v)‖²。phase_pair 和 phase_re 把它化成 pair cosine integral。最后第 258–261 行在常数和 cosine 真可积、product 概率质量一已建立后才作积分相减，得 1−norm² 的真实身份。不存在非可积默认值、代理 characteristic 或 χν(−u,v)=conj χν(u,v) 假设。

### 4. 小角度与 local gap 常数：第 264–344 行

small_cos_gap 令 x=|t/2|，从 |t|≤1 推 0≤x≤1 与 x³≤x；真实 sine remainder 与三角不等式给 (5/6)x≤|sin(t/2)|。平方时显式保持两侧非负，得到 (25/36)x²≤sin²(t/2)。真实 half-angle identity 和 x²=t²/4 给

    1−cos t≥25t²/72≥t²/4。

没有除 t，故 t=0 包括在内。

retained_phase_gap 在 good 分支先证明 |a±b|≤2d。由 4|v|d≤|u| 得 |v(a+b)|≤|u|/2，因而对 w=u+v(a+b) 有

    |u|/2≤|w|≤3|u|/2。

完整 phase 的绝对值≤2d·(3|u|/2)=3d|u|≤1。正确的乘法符号和绝对值非负性均被保留。以 |w| 的真实平方下界结合 small_cos_gap 得 u²(a−b)²/16；good 外用 cos≤1 得全 gap 非负。

第 333–344 行调用前面已证 retained moment；积分比较双方真可积，正的 square 系数才可乘 retained lower bound，再以已证 norm-square identity 改写，得到 V u²/16 的 local gap。实现没有把待证 retention 或 spectral gap 作为公共/私有额外假设。

### 5. 实际 M3、γ 正性和 ±u 指数界：第 346–412 行

third_moment_pos 首先建立 M3≥0。若不正，则 M3=0；第 353–359 行使用非负真可积函数零积分的真实 a.e. 消失结论，从 |a|³=0 推 id=0 ν-a.e.。variance_congr 与常数零的实际 L2 variance formula 给 V=0，和 hV 矛盾。因此 M3>0 不是额外假设，也不是由对零除的总定义推来。

norm_le_exp_of_gap 对任意 δ≤1−‖z‖²，使用 1−δ≤exp(−δ) 以及 exp(−δ/2)²=exp(−δ)，结合 norm 非负和 exp 严格正得 norm≤exp(−δ/2)。该 helper 不需 δ>0，所有实 δ 下均合法，也没有除 norm/δ 或无根据开方。

最终实际定义 V=variance id ν、M3=∫|a|³dν、γ=M3/V、d=16γ。先由 M3>0、V>0 得 γ,d>0，才使用 le_div_iff 的频率换算和 γV=M3。两条原频率条件分别给

    |u|d≤16/128=1/8≤1/3，
    4|v|d≤64|u|/128=|u|/2≤|u|，
    dV=16M3≥8M3。

因此对 (u,v) 和 (−u,v) 分别调用真实 local_gap。第二次仅使用 |−u|=|u|、(−u)²=u²；没有用 law 的对称性或把负频率值当成原值的 conjugate。代 δ=Vu²/16 后，ring 对齐 −δ/2=−Vu²/32，两个 norm bound 同时闭合。

## 四、实际边界与未宣称的外部结论

- 严格 bad 与闭 good 对所有 d 的 indicator helper 都真可积；公开 tail/budget/gap 中需要除 d 时才显式要求 d>0。|a|=d 的原子没有被丢弃。
- u=0 的最终 domain 在 γ>0 后迫使 v=0；实现无需独立 origin 分支，因为同一 local gap/指数 lemma 已覆盖。最终右端一，χ(0,0)=1。负 u,v 均由真实绝对值控制。
- 零方差/常值 law 包括在 pair moment、tail bound、gap identity；最终 ratio theorem 和 retained/local positive-variance版本显式要求 V>0，不存在隐藏零分母。原增量即使均值非零，也保留 raw cube 和完整 quadratic phase。
- private norm-exp helper 在 δ=0 甚至 δ<0 也有效，不把其一般形式当成全频率 damping；真正正的 quadratic gap 只在已付低频域推出。
- source-specific h_x 条件 law 的概率、raw cube、正方差及旧 reciprocal-cutoff transport 仍须真实提供。当前 h3 是实际固定 ν 的三矩，不是原未截断 ξ 的全局三矩。
- 原声明审查的反例仍说明：去掉低频域，公平 {−1,1} 在 u=2π,v=0 norm 一；去掉 quadratic strip，公平 {0,1} 在 v=−u 的相位恒零；以中心 cube 替代 raw cube，平移公平 {L−1,L+1} 的 quadratic cancellation 破坏界。实现未作这些错误加强。

## 五、执行证据的身份与最终裁决

冻结作者回执经本轮实际读取并核对哈希。协调者提供、该回执记录的执行事实为：准确 source target 服务器 exit 0，stdout/stderr 空；六公开签名检查成功；包含 generated internal declarations 的 30 个新声明及 14 个实际语义依赖传递公理门通过，仅使用 propext、Classical.choice、Quot.sound。14 个依赖对应真实 quadraticChar、variance 及其 raw/AE 桥、product/conjugate/real integral、complex norm-square algebra、sine remainder/half-angle、指数标量界和零积分 a.e. lemma，与实际 proof 一致。

这些门没有由我复跑，也不作为独立数学判断的替代。我的实际独立证据为冻结源完整读取、六签名字节匹配、所有私有和公开 proof 的源数学核对、已接受项目依赖复用以及本地完整禁项扫描；sorry/admit/axiom/unsafe/native_decide 均零匹配。源码观察不是独立服务器内核回执。

CORRECT：固定源 ffdeace2421a3c0fdf63def48eb96b882f9dc98014e5614d226a07f87a02bb65 完整实现原 scope 六条冻结 theorem。真实 pair 可积性、非中心 2Var 身份、strict/closed 分割、实际 characteristic gap、small-angle 常数、M3/γ 正性、d=16γ 支付和 ±u exponent conversion 均闭合，未发现源数学缺口。

此裁决精确限于 fixed-law 低频模块。h_x 专门化、组合的低频 odd-power 导数表、高频噪声/阻尼、clock 概率、complex tilt、Fourier inversion/振荡积分、严格 CDF smoothing/defect 和完整 C1/C2 不由该模块或本报告宣称完成。
