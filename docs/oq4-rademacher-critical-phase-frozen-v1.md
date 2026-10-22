# OQ4 确定性临界弱格点相位：冻结命题 v1

STATUS: FROZEN_FOR_FRESH_SOURCE_REVIEW
DATE: 2026-10-22
OWNER: OQ4_LEAD
SCOPE: DETERMINISTIC_CRITICAL_WEAK_LATTICE_PHASE_ONLY
PROOF_STATUS: NOT_WRITTEN
LEAN_STATUS: NOT_RUN
IMPLEMENTATION_AUTHORIZATION: NONE
ACTUAL_S5_BROWNIAN_SPECTRUM_OQ4_ROOT_STATUS: OPEN

本冻结只处理原 S5 的确定性高度、格点相位和子列构造。作者不得增加、删减、弱化或重新解释前提。它不是实际概率倍率、S5 或 OQ4 root 的冻结替代品。

## 1. 来源、采纳与边界

原始来源为 C:/game/shao/current/oq4/c01/spectrum01.md，commit 35d4580b61e22e7145f47730045a09874ef93259，SHA256 b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b，4306B。第11–12行固定弱胞元；第70–81行给相位和三项尺度；第85、95–104行给临界高度、三类子列及固定 c>0 推广。第88–90、93、100–104行中的实际概率判断不作为本命题前提。

新 intake 5a4bb76763aafdb595fb555dc7a9cb6b8adc2568791af912d069fa35ff51f812/12801B 和候选 dbd95c2c4f67600146807824ee30b5ffda7cf5a0d971319c0b24bc555661ce64/11849B 原字节保留；本文件单独采纳其 CP0–CP3 确定性部分。来源未指定的 nearest 并列规则在此固定为向上舍入；不要求证明任意 nearest 选择的辅助推广。尾部重编号、严格递增及自然数减法合法性均是待证明输出，不是新增假设。

精细 O(k^(-2)) 或 O(k^(-5)) 余项不是本冻结的必需输出或自由输入。只要求以下精确恒等式、趋向零和严格子列性质。该单元是既有 Spectrum/S5 粗义务内的确定性分解；本轮不新增总义务分母、不将声明数量当原始新叶。

## 2. 固定对象与量词

固定任意 c:ℝ，唯一参数前提为 0<c。c 不随 n、k、子列索引或目标相位变化；不要求关于所有 c 的统一尾部门槛。

对每个 n:ℕ，固定透明函数

  r(n) = Real.rpow (n:ℝ) ((1:ℝ)/3)，
  h_c(n) = c*r(n)，
  m_c(n) = Nat.floor(h_c(n))，
  H_c(n) = (m_c(n):ℝ)+1，
  delta_c(n) = H_c(n)-h_c(n)。

1/3 是实数除法。r 不是自由序列或额外给定的根；其非负、立方恒等式和唯一根性质在 CP0 内实际证明。

再固定

  q_c = π²/(4*c³)，
  E_c(n) = q_c*delta_c(n)，
  F_c(n) = Real.exp(E_c(n))。

F_c 是上述唯一显式确定性函数，没有任何概率或尾函数含义。

子列一律指严格递增函数 sigma:ℕ→ℕ。所有极限以自然数指标趋向正无穷取；实序列趋向正无穷的含义为对任意实阈值最终大于它。定义

  Cluster(z) = {L:ℝ | 存在严格递增 sigma:ℕ→ℕ，z(sigma(j))→L}。

本冻结中的区间等式都指完整双向集合等式，不能只交付某些候选子列。

## 3. CP0：根、最终弱胞元和原尺度

对每个固定 c>0，证明：

1. 对全部 n:ℕ，r(n)≥0、r(n)³=(n:ℝ)，且 r(n) 是具有这些性质的唯一实数；r(0)=0、h_c(0)=0。对每个 n≥1，r(n)>0、h_c(n)>0，并有 h_c(n)³=c³*(n:ℝ) 和 (n:ℝ)/h_c(n)³=1/c³>0。
2. 存在一个固定自然 N_c≥1，使全部 n≥N_c 有 h_c(n)≥1、1≤m_c(n)、(m_c(n):ℝ)≤h_c(n)<H_c(n)、H_c(n)=h_c(n)+delta_c(n)、0<delta_c(n)≤1。若 h_c(n) 是整数，则 delta_c(n)=1。Nat.floor 与通常整数 floor 在这些非负输入上的对应必须核验。
3. h_c(n)→+∞，(n:ℝ)/h_c(n)²→+∞。第三尺度的固定正界可以取 1/c³，并在全部 n≥1 为精确恒等式；不假设额外的第四幂误差或单调性。
4. 对任何严格递增 sigma，组合后的 h_c(sigma(j))→+∞、(sigma(j):ℝ)/h_c(sigma(j))²→+∞，并最终进入同一弱胞元域；第三尺度最终精确为 1/c³。对 CP1/CP2 的构造，必须选择固定截尾使每个 j 均已合法。

不把最终弱胞元改成全 n 前提；n=0 保留为有限前缀，不能在零项使用第三尺度的正时间恒等式。

## 4. CP1：c=1 的两个精确端点子列

令 c=1。

1. 对每个自然 k≥1，n=k³ 时有 h_1(n)=k、m_1(n)=k、H_1(n)=k+1、delta_1(n)=1。sigma_1(j)=(j+1)³ 是严格递增、全部在弱胞元域的子列，并有 E_1(sigma_1(j))→π²/4、F_1(sigma_1(j))→exp(π²/4)。
2. 对每个自然 k≥2，n=k³-1 使用自然数截断减法；先证明它等于普通整数减一且 n≥1。须有 k-1<h_1(n)<k、m_1(n)=k-1、H_1(n)=k，以及 delta_1(k³-1)=k-h_1(k³-1)→0（k→∞）。sigma_0(j)=(j+2)³-1 是严格递增、全部合法的子列，且 E_1(sigma_0(j))→0、F_1(sigma_0(j))→1。

所有 k 的实数表达使用自然数到实数转换；m=k-1 中的自然数减法也须在相应域解释，不能省去下界。

## 5. CP2：任意固定 c>0 的舍入子列

对每个自然 k，定义

  t_c(k) = ((k:ℝ)/c)³，
  a_c(k) = Nat.ceil(t_c(k))，
  b_c(k) = Nat.ceil(t_c(k))-1。

证明全部 k 有 0≤(a_c(k):ℝ)-t_c(k)<1；对全部 k≥1，先证 Nat.ceil(t_c(k))≥1，再证 -1≤(b_c(k):ℝ)-t_c(k)<0。k=0 的 b_c(0)=0 不承担严格小于 t_c(0) 的错误断言。

证明存在固定 K_a,K_b:ℕ（可依赖 c，K_b≥1），使

  sigma_a(j)=a_c(j+K_a)，sigma_b(j)=b_c(j+K_b)

各自严格递增、每个 j 均在 CP0 的弱胞元合法域。对 k→∞，证明最终 k≤h_c(a_c(k))<k+1、m_c(a_c(k))=k、h_c(a_c(k))-k→0，因而 delta_c(a_c(k))→1；另证明最终 k-1<h_c(b_c(k))<k、m_c(b_c(k))=k-1、h_c(b_c(k))-k→0，因而 delta_c(b_c(k))→0。相应 E/F 子列极限分别为 q_c/exp(q_c) 和 0/1。

内部相位：另固定任意 alpha:ℝ，0<alpha<1。对每个 k:ℕ，定义

  t_c,alpha(k) = (((k:ℝ)+alpha)/c)³，
  v_c,alpha(k) = Nat.floor(t_c,alpha(k)+(1:ℝ)/2)。

这固定了半整数向上舍入规则。证明全部 k 有 |(v_c,alpha(k):ℝ)-t_c,alpha(k)|≤1/2。证明存在固定 K_c,alpha，使 sigma_alpha(j)=v_c,alpha(j+K_c,alpha) 严格递增、全部合法，并有

  h_c(v_c,alpha(k))-((k:ℝ)+alpha)→0，
  最终 k<h_c(v_c,alpha(k))<k+1、m_c(v_c,alpha(k))=k，
  delta_c(v_c,alpha(k))→1-alpha。

由同一截尾子列得到 E 极限 q_c*(1-alpha)、F 极限 exp(q_c*(1-alpha))。这些存在性和极限都是输出；不允许将有界舍入误差、最终严格递增、方向控制或 floor 稳定性另作假设。有限前缀可能有重复项，不能直接称未经截尾的 a、b、v 为严格子列。

## 6. CP3：完整极限点集与整列不收敛

对每个固定 c>0，证明

  Cluster(delta_c)=[0,1]，
  Cluster(E_c)=[0,q_c]，
  Cluster(F_c)=[1,exp(q_c)]。

具体要求：任意严格递增 sigma 上若上述任一序列有有限实极限，它属于相应闭区间；反之区间中每一个值都有严格递增子列实现。对每个 d∈[0,1]，应能用同一条全部合法的 sigma_d 同时实现 delta 极限 d、E 极限 q_c*d、F 极限 exp(q_c*d)。d=1、0 分别接 CP2 上／下采样，0<d<1 取固定 alpha=1-d。指数区间中任意一点的覆盖也须证明。

作为同一结果的推论，delta_c、E_c、F_c 的整列均无单一实极限。弱相位0是极限点，不是弱胞元合法单项值。不得假设对一般 c 存在正整数 n 使 h_c(n) 恰为整数。

## 7. 明确排除及后续门

不假设、证明或认证实际概率、Brownian、S1–S4、实际 S5、随机游走概率比、strict 完整相位集合、一般分布、其他 cosets、c≤0、变化的 c、Spectrum 或 OQ4 root。没有自由概率尾函数、Taylor 余项、DA1 或 DA2 误差假设；本单元的数学前提仅固定 c>0 和明确透明定义。

原112–116行 weak/strict 差别保持原意：整数高度的弱 delta=1，strict delta=0。CP2 的 ceil 上采样只被本冻结用于弱相位1，不能移作 strict 相位1。此处不冻结任何实际对数概率差界；n=1,h=1 的 strict 零概率说明不能把来源的渐近措辞当成全有限参数的有限对数界。

下一门：全新独立来源声明审查；通过后另派匿名数学作者，再由另一个全新上下文审查。形式实现须另行授权，当前未运行 Lean。本单元即使全部完成，也只关闭既有 S5 的确定性相位依赖；实际概率连接及全部根结论仍 OPEN。
