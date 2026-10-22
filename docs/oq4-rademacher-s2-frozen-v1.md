# OQ4 S2 有限与双尺度汇总：冻结命题 v1

STATUS: FROZEN_FOR_FRESH_SOURCE_REVIEW
DATE: 2026-10-22
OWNER: OQ4_LEAD
UNIT_KIND: DERIVED_ASSEMBLY
NEW_RAW_LEAF_INCREMENT: 0
SOURCE_RAW_DENOMINATOR_DELTA: 0
PROOF_STATUS: NOT_WRITTEN
LEAN_STATUS: NOT_RUN
IMPLEMENTATION_AUTHORIZATION: NONE
UPSTREAM_U1_FORMAL_STATUS: PENDING
S2_S3_S5_BROWNIAN_SPECTRUM_OQ4_ROOT_STATUS: OPEN

本单元仅汇总原 S2 第38–56行及其同一误差的派生消费接口，不增加原始来源叶或总分母。作者不得增加、删减、弱化或重新解释任何前提。不得把待证标量便利界、正性或实际余项界变成自由输入。

## 1. 来源与固定依赖

原始来源 C:/game/shao/current/oq4/c01/spectrum01.md，commit 35d4580b61e22e7145f47730045a09874ef93259，SHA256 b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b/4306B。第11–12行固定弱胞元，第24–34行保留零时间，第36–43行给真实谱主项与校正，第46–55行给统一余项与原时间阈值，第56行给负主模态系数的小量。

本次采纳新 intake 07e8dcf8fd74540f61c5229ae34f9f1d110c0b2c7a1c27ad421f17522205a4a6/12359B 与候选 f095ab555bfaaff667a68403a601f2f928a1153098ac9fb02167d3e5fd95881a/10239B 的 F0/T0/F1/Q1 范围，另建本冻结；两个原件不改。

固定上游为实际项目 Pair P1/P2、Scalar SCA0 和同一个明确的 U1：

- Pair 冻结69c5cf5822044e19520e10c4a6de4a31e0e8f43d296e477982a9c5637c85c6fb/8661B，公开声明账739c43160dbbe549e5a2d02e7e2b2b86e61cde7fb3bbed3481d5d035ee77242e/187627B；已完整认证 PR111，尚待 main 整合。
- Scalar 冻结225b63ae8522a126cb5c126f83cb782b024e95f592e9e2da5f36f56e0ce21356/9414B，公开声明账71f4ce77c809070b1133c0b6eaa17481b4d5129114bea03f08f52418ce7a6953/91113B；PR104 内容已在 main v31 接受。
- U1 冻结b220e1ca9f89e5f9a3328131b430fb54b9656e5113b93241adbde1aad627354a/8952B；数学已审、形式认证仍 pending。其上游是同一个实际 Pair.remainder 的绝对常数界，不能换成任意 R/F 的自由假设。

数学汇总可相对于这些固定接口证明；完整形式认证必须调用实际已认证 U1 声明，不能因本冻结的存在而称 U1 或 S2 已关闭。不得读取其他作者或审查者的推理来代替接口条件核验。

## 2. 真实对象与全部有限域

量化全部 m:ℕ，1≤m，全部 h:ℝ，(m:ℝ)≤h<(m:ℝ)+1，以及全部 n:ℕ（包含0）。令

  H_m=(m:ℝ)+1，N_n=(n:ℝ)，t_mn=N_n/H_m²，
  u_m=Scalar.u m=π/(4H_m)，z_m=Scalar.z m=π/(2H_m)，
  a_m=Pair.amplitude m，rho_m=Pair.rho m，
  eps_mn=Pair.epsilon m n=(-1:ℝ)^(n+m)，
  q_m=(Real.tan u_m)²，R_mn=Pair.remainder m n，
  B_mn=a_m*rho_m^n。

H 是同一自然数 m 的实际吸收位置，不是 h 或自由实参数。全部 m=1、m=2、整数弱边界 h=m、零时间、全部奇偶和胞元严格上端均保留。

固定 ν_R=RademacherCosine.law，即两个 ±1 Dirac 测度各乘1/2。令 P_n=Measure.pi(fun _:Fin n=>ν_R)，实际路径 Path n=Fin n→ℝ，从0出发；closedStrip n h 是全部前缀和绝对值≤h的弱事件。定义

  p(n,h)=P_n.real(closedStrip n h)，
  K(n,h)=killedMass ν_R law_isProbabilityMeasure h n 0，
  D(m,n,h)=p(n,h)/B_mn。

p 是实际产品测度事件的实值概率，不能按谱和重新定义。R 必须是 Pair.remainder 的唯一透明函数：去掉首下模态的有限 normalizedTerm 和，加精确 zeroMode/(a*rho^n)，保留偶 m、n=0 时的0^0=1。不得引入“存在误差使身份成立”的选择函数。

Pair 的 cotangent 通过已认证 S1 公开定义 fun x=>cos x/sin x 解释；S1 声明账8b604744edf2d58d5d89cf0893a02a2ccdc391520d02744d9a60c659a49a53c4/94365B 第341–365行给出其完整透明值。必须实际对接

  Pair.alpha m 0=u_m，Pair.beta m 0=z_m，
  a_m=(1/H_m)*(cos u_m/sin u_m)=Scalar.a m，
  rho_m=cos z_m=Scalar.rho m。

这些是定义相容性输出，不作为额外等值假设。Scalar SCA0 提供实际角度和正性域；不把其私有 tan/Taylor 引理或未冻结便利输出当输入。

## 3. F0：全部时间身份与归一化合法性

对第2节全部 m,h,n，输出

  a_m>0，0<rho_m<1，B_mn>0，p(n,h)=K(n,h)，
  p(n,h)=B_mn*(1+eps_mn*q_m+R_mn)，
  D(m,n,h)=K(n,h)/B_mn=1+eps_mn*q_m+R_mn。

这些来自实际 Pair 公开身份与正分母的规范化，不重做或重计 Pair。全部 n=0 时 p=K=1；中心零项不得删除。m=1 的 R 对全部 n 为0；m=2 只在 n≥1 时 R=0，n=0 的中心项和余项非零。F0 不受后续时间阈值限制，也不先假设全部有限概率严格为正。

## 4. T0：必须内部证明的标量便利界

对全部 m≥1，证明实际 q_m 满足

  0≤q_m≤π²/(4H_m²)。

对全部 n:ℕ，证明 |eps_mn|=1。明确常数 π²/4 是原第56行 O(H^(-2)) 的一个非最优全有限域便利加强，不是原文给定数值，也不是已认证 Scalar 的公开结论。本冻结把它放在结论侧；作者须从实际 Real.tan、u 和已写合法性域推出，不能用自由 C_tan、Taylor 误差或额外充分大 m 前提替代。不增加原始叶。

## 5. F1：同一绝对 U1 常数的有限概率误差

存在 C_U:ℝ，0<C_U，在全部 m,h,n 与序列之前固定，使对第2节全部有限参数，当 H_m²≤N_n 时，同一见证同时满足

  |R_mn|≤C_U*exp(-π²*N_n/H_m²)，
  |D(m,n,h)-1-eps_mn*q_m|≤C_U*exp(-π²*N_n/H_m²)，
  |D(m,n,h)-1|≤π²/(4H_m²)+C_U*exp(-π²*N_n/H_m²)。

对 K/B 使用同一 D 身份，不另造过程或常数。此处采用实际固定 U1 的一个见证，而非对每个 m、h、n、奇偶或序列选常数。阈值恰为 H²≤N，不改成更强时间、不删小 m、不把负主模态校正并入 R。该域从 m≥1 推出正时间，所以只在此才可去掉零模态中心项。U1 形式认证尚 pending，F1 不能先行冒称已获形式认证。

## 6. Q1：原双尺度的任意序列输出

任取 m_,n_:ℕ→ℕ，h_:ℕ→ℝ，对每个 k 都满足 1≤m_k 和 (m_k:ℝ)≤h_k<(m_k:ℝ)+1。所有对象严格取第2节的同一实际函数，记 H_k、N_k、t_k、a_k、rho_k、B_k、p_k、K_k、D_k。

唯一渐近前提为 H_k→+∞ 和 t_k=N_k/H_k²→+∞。即对每个实阈值 T，各有一个固定自然起点，其后相应量≥T。不加入单调性、n/h³条件、临界子列、奇偶匹配或 Brownian 前提。

证明以下全部输出：

1. 全部 k 有 B_k>0、p_k=K_k 和 F0 身份；早期 n_k=0 及中心项照样保留。
2. 存在固定 K_time，使全部 k≥K_time 有 H_k²≤N_k 且自然数 1≤n_k；F1 的同一个绝对 C_U 在该尾段适用。
3. D_k→1，等价地 K_k/B_k→1。这里 D_k 是实际 p_k/B_k，绝不把 p_k 自身的极限误写为1。
4. 存在固定 K_pos，使全部 k≥K_pos 有 D_k>0、p_k>0、K_k>0。正性是结论，不是为使用对数增加的假设。
5. 在已证正性尾段，真实相对对数满足 log(D_k)→0，并且同一尾段有精确等式

     log(p_k)-log(a_k)-N_k*log(rho_k)=log(D_k)，

   左侧因而趋零。K_k 由其与 p_k 的实际相等消费同一结论。

全部起点可依赖序列或 ε；C_U 始终与它们无关。D 的除数 B 在全部 k 正，概率对数则必须同时交付最终正性；Lean 的 Real.log 总函数不能替代这项合法性义务。

T0 的 H^(-2) 项和 F1 的指数项必须在原双尺度实际趋零；不得把这两项趋零或 D 的相对误差当额外输入。Q1 的最终正性与相对 log 是原 S2 误差的透明派生便利输出，原文未逐字另列；它们不增加原始叶。log 比较的分母只为实际谱主因子 B，没有 Brownian 概率。

## 7. 排除与下一门

不假设或认证 Brownian、S3–S5、DA1/DA2、strict 事件、其它 cosets、一般分布、完整 Spectrum 或 OQ4 root。全 k 胞元域保持原接口；若后继应用仅最终处于该域，须另行处理有限前缀，不能在本冻结里暗中免除。

本冻结不证明 U1，也不重做已接受 Pair/Scalar 源码。下一门为全新来源声明审查；通过后另派匿名数学作者与独立验证者。数学结论必须明确相对于固定 U1；形式实施及终审必须等待实际 U1 认证接口，不能引入自由尾界假设来绕过。当前没有 Lean 或实施授权，S2 及全部根状态继续 OPEN。
