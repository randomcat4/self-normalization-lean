# 原物理紧区间 CDF：P179 / PR549 unit264 原题范围审查

**裁决：给定公开的 broader scalar CDF 输入，unit264 已将实际 compact 成本/CDF 消费接回任意原可测空间、原 μ/h 的有限行物理统计量。一个正 K 同时控制全部 n≥3、x∈[0,1] 的严格/闭 CDF 和严格/闭尾，误差均为 K[β n^{−(p−2)/2}+(1+√v)n^{−1/2}]。当前范围没有未实例化的包络、低能量付款、原分母正性、原子或“另一个编码律等于原物理律”的前提。**

**这是有实质外部条件的原模型消费者闭合；broader CDF 输入的存在/证明没有由本定理交付。**它量化所有独立中心化 L² 标量族，没有 bounded ζ 假设，不能从此前 tail-only 输入、输入的 Shao–Zhou 名字或白名单 AX 推出其可用性。负阈值、更大/变化窗口、Gaussian-relative、条件族一致性、p54 的额外一致消费者、DC/full OQ56 不由本条紧区间绝对误差结论自动关闭。同批263由另一审查者处理，本报告不重复其工作。

## 1. 精确版本与复用

发布为 P179 / PR549，head abc5b2bf12577e40f2f7060a906fec8bf86e4630，tree 41509195d0a3a7f63df2de17cb7b2323beefc76a，parent 3c4d3f633480812ecf70988a93b7916aba8df6f6。PUBLICATION-COMPLETE.json 的 SHA256 为 218f8f52fb4acb08164e21e5b44e815b8e4b7a69e167b30aa2c2db941df6a432。

本次唯一新生产输入是 C:/game/shao lean/drafts/oq56/unit264/author-repair-02/OriginalPhysicalCompactCDF.lean，公开名为 Shao.OQ6.OriginalPhysicalCompactCDF.actual_original_physical_compact_cdf_tail_rpow_rate。

| 当前 unit264 工件 | SHA256 | 长度 |
| --- | --- | --- |
| 最终 repair02 源 | a2dda2b0def88529c2f2d08cb90557e79b8a3a481adefecd84ab51a629f4575f | 7825 B / 170 LF |
| qualified-evidence.json | 1885a4be457c7191b1d5e7fc507f5071508eae77229121bb73e4dc2ab32c5171 | 11606 B / 282 LF |
| source-review-01/FINAL-REPORT.md | 951835bbe43b9bf070f7897853cba40ffa26f0d241f2bb670876b346c4b16ef6 | 18006 B / 104 LF |
| source-review-01/FINAL-VERDICT.json | a6778304b9b3f2481dd062bba2f3443d2abc29d98cf653739005a6a683707d29 | 8205 B |
| source-review-01/FINAL-COVERAGE.json | 0d99905f605ec0ab9b4532d758dd5976a21f5ef660efa474a56445c4239a3797 | 113751 B |
| owner-evidence-01/actual-owned-types.txt | 3e0524e4da21edb12aaf63a721726bc193018228888ce1ba697bcd130ded8b9d | 16067 B / 229 LF |

本次完整读最终源、229 LF 实际 TYPE、完整最终独审和下述承重定义/接口；复用原独立完整 SOURCE 加两次 affected repair 的准确联合覆盖，不重新审计旧221/170或本单元完整局部证明。qualification 的20个本地引用散列/字节均相合。实际 owner 恰1个 theorem，必要非定理 VALUE 为空，SHA256 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855。

首原对象为 6fdc85b25308f8d8b1a9d9506226d8bf06660e7fe8be24707dacf98fe70aca35 / 1732656 B；既有 native03 与同首原对象 audit01a 实际 RC0/0、递归 AX 仅 propext/Classical.choice/Quot.sound。历史失败、warning 和 strict-wrapper false 继续按资格原状保留，本次没有执行任何机器门。外部 hSZC 仍是实际 TYPE 第二行的普通假设，白名单证明证据不等于证明这个假设存在。

基线选择性复用 v155 Root 原题范围验收（coordination/integration-v155/root-source-scope-acceptance.json，SHA256 8595ddf5ff19e7aa5447545c327311fa9001c1067e8e95f1ce2f4cd03a7836e6）。其当时保留的 compact/CDF 概率消费者缺口，现由264在本报告的精确条件/窗口内推进；不追改旧验收字节。

## 2. 实际陈述：一个 K、原 p 矩和四个关系

原 Ω 只需 MeasurableSpace，μ 为其概率律；h 在原 μ×μ 上联合可测、L²、逐点对称、原积分为0，实际投影二矩为1。固定真实 2<p≤3，另明确假设实际投影 p 矩可积。定义

\[
g(o)=\int h(o,y)\,d\mu(y),\quad
r(o,y)=h(o,y)-g(o)-g(y),\quad
v=\int r^2\,d(\mu\times\mu),\quad
S=1+\sqrt v,\quad\beta=\int |g|^p\,d\mu.
\]

这里用 S 表示源码中的模型常数 s，避免与前几轮样本物理分母混淆。h∈L² 保证真实 r∈L²、v 有限非负，故 S≥1；hgp 是实际 Integrable |g|^p，不是依靠 Lean 对不可积函数积分总化为0而写出的有限 β。

对样本 ξ，令 H_{ij}=h(ξ_i,ξ_j)，并使用原有限行定义

\[
U_n=\binom n2^{-1}\sum_{i<j}H_{ij},\qquad
\bar H_i=\frac1{n-1}\sum_{j\ne i}H_{ij},\qquad
R_n^2=\frac{4(n-1)}{(n-2)^2}\sum_i(\bar H_i-U_n)^2,
\]
\[
P_n=\mu^{\otimes n},\qquad
T_n=\begin{cases}\sqrt n\,U_n/\sqrt{R_n^2},&R_n^2>0,\\0,&R_n^2\le0.\end{cases}
\]

实际结论为：固定 C/hSZC、原 μ/h/p/hgp 后，**∃K>0 ∀n≥3**，T_n 在原乘积 σ 域可测，且 **∀x∈[0,1]**，以下四个绝对误差都不大于同一个

\[
\varepsilon_n=K\left(\frac{\beta}{n^{(p-2)/2}}+\frac S{\sqrt n}\right):
\]
\[
|P_n(T_n\le x)-\Phi(x)|,\quad |P_n(T_n<x)-\Phi(x)|,\quad
|P_n(x<T_n)-(1-\Phi(x))|,\quad
|P_n(x\le T_n)-(1-\Phi(x))|.
\]

K 在 n 和 x 之前选择；不是每个阈值另选常数，不是只对充分大 n 或子列成立。允许 K 依赖前置模型/输入；公开类型不声称跨任意 μ/h 的统一 K。p=3 包含，p=2 不在速率结论内；原核只需 L²，不要求整个 h 的 p 矩或残差高阶矩。当前绝对误差可在小 n 时超过1，不影响其为真实上界。

## 3. broaderCDFinput 实际假设的完整数学内容

已完整读 library/Shao/OQ6/NormalizedIntegrableCDFAssembly.lean:19–68 的 ScalarShaoZhouFiniteCostCDFInput 定义。它不是“假设目标原 T 的 CDF 结论”，而是一个普遍标量输入：

- C>1；对任意同宇宙概率空间 (ν,Ω)、任意 n≥1 和独立、可测、中心化 L² 实族 ζ_i，要求 ΣEνζ_i²=1。
- D1、D2、非负包络 A/B 均为整向量 ζ 的 Borel 函数；删一 A_i/B_i 是只看其他 ζ_j 的 Borel 函数。A/B 和删一包络逐点非负，|D1|≤A、|D2|≤B 在 ν 下几乎处处成立。
- 对编码归一化量 V=(Σζ_i²)^{1/2}，要求 V>0、1+D2>0 几乎处处；要求下述 full/deleted 测试真实可积。
- 对全部 z≥0，令

\[
L_z=\sum_iE_\nu[((1+z)\zeta_i)^2\min(|(1+z)\zeta_i|,1)],
\]
\[
\mathcal C_z=L_z+E_\nu(A+zB)
+\sum_iE_\nu\!\left[
\min\!\left(|\zeta_i|,\frac1{1+z}\right)
\bigl(|A-A_i|+z|B-B_i|\bigr)\right].
\]

输入断言

\[
\left|\nu\!\left\{\frac{\sum_i\zeta_i+D1}
{V\sqrt{1+D2}}\le z\right\}-\Phi(z)\right|\le C\mathcal C_z.
\]

定义中**没有 bounded ζ、p>2、第三矩、strict moment budget 或 z≤1 前提**；但有以上真实可测/独立/L²/删除结构、AE 分母正性与可积性门槛。成本是未倾斜的 full/deleted 期望，不是此前相对尾的指数加权比值或完整 I 的另一种归一化。输入本身只直接给闭 CDF；严格 CDF 与尾关系由消费者另外取得。

因此 hSZC 是比仅有有界观察版本或 tail-only hSZ 更广且不同的显式条件。旧相对尾输入的存在，不自动产生它；外部结果的名称也不证明其完整 L² 域已经在文献中成立。本次按给定 hSZC 接受真实消费者，继续保留该输入存在/证明及准确外部归属的义务，没有新引入外部公理。

其 V>0 门槛作用于内部标量编码族，不是对原 R_n²>0 的假设。原物理零分母由第5节的实际概率费用控制，不能用编码正分母替代。

## 4. 原有限行 T 的精确对应与任意原空间运输

前几轮记号中

\[
W=\frac{\sum_i g(\xi_i)}{\sqrt n},\quad
F=\sum_{i<j}r(\xi_i,\xi_j),\quad
D=\frac F{\sqrt n(n-1)},\quad
\sigma_n^2=\operatorname{centeredSq}(n,g,r,\xi).
\]

有两个实际来源，足以逐样本识别统计量，而非口头等同：

1. ActualUncenteredCompactCDF.lean:25 的已接受 finite_projection_residual_numerator，对 n≥3 给出 W+D=√n U_n/2；该文件:473 在真实 h=g+g+r 的同一样本核上实际调用它。originalUpper 的定义就是同一 F（CanonicalDoubleGhostScalarMoments.lean:31）。旧 p51 BoundedStudentizerGeometry.lean:151 的 sampled_uStatistic_formula 虽只声明 n≥4，**本次不把该旧前提越过到 n=3**。
2. BoundedStudentizerGeometry.lean:79 的 centeredSq 定义恰为 jackknifeSq(sampledKernel)/4；sampledKernel=g_i+g_j+r_ij=h_ij 逐点成立。FiniteRows.jackknifeSq_nonneg 在 n≥3 给 R_n²≥0，故 σ_n=√R_n²/2。

因此正分母样本上 (W+D)/σ_n=√n U_n/√R_n²；R_n²=0 时两种定义均取0。264 的物理统计量就是此前同一原 T，既不是 clipped law，也不是编码 Tη。n=3 由上述已接受 n≥3 有限行来源承重；这不将此前 n≥4 的几何/相对尾声明改写成 n≥3。

任意原可测空间的衔接也已经实际做出。264 使用 OriginalCountablyGeneratedModel.actual_normalized_original_countably_generated_model 的同一个 m0≤mΩ、μ0=trim μ；它提供 g0=g、r0=r、v0=v 和真实投影律相等。对连续 F(t)=|t|^p，通过相同投影推送律，264 证明粗空间的真实 p 矩可积且 β0=β；不是只传 L² 或把不同测度下的 β 静默换名。S0=S 还单独由 v0=v 保证。

随后只调用一次已接受 ActualPhysicalCompactCDF 的真实 compact 四关系定理。对每个 n，旧模型的 generic finite-J 观察法则给 **map(T)P_coarse=map(T)P_original**；264 对 Iic x、Iio x、Ioi x、Ici x 分别使用实际 map_apply/toReal，精确转回四个原概率。最终 TYPE 中局部名 P₀ 实际定义为原 μ^n，不是粗律。原 T 的可测性亦由同一个 id 的可测复合给出。没有向用户添加 CountablyGenerated、标准 Borel、无原子或“观察法则相等”假设，也没有额外运输误差。

## 5. compact 包络、低能量与零分母费用已经实例化

当前路径使用实际未中心化行平方 J=uncenteredSq 和中间

\[
T_*=\begin{cases}\sqrt n\,U_n/(2\sqrt J),&J>0,\\0,&J=0.\end{cases}
\]

其真实 W/D 正是第4节的 W/D。令 ψ_i=Σ_{j≠i}r(ξ_i,ξ_j)、Λ²=Σ_iψ_i²，实际 compact 包络为

\[
A=|D|,\qquad
B=4096\left(\frac S{\sqrt n}+\frac{\Lambda^2}{S n^{5/2}}\right).
\]

删一量以 eraseIncident 删除该坐标的残差，并保留原 n 的全部系数。ActualUncenteredCompactCDF.lean:218–245 与 UntiltedCompactCost 的公开消费者真实构造这些量、可积性和删除费用；它们不是等待调用者供应的 A/B。此 B 包络的是 J/V²−1 的实际 compact 修正，不是把此前中心化 current-clip 的 B_y=512ρy 当作同一成本无损替换。

在实际 G 上用 max(δ*,−1/2)，G 外置0；实际 Hcpt=G∩{δ*≥−1/2} 上该修改与原 δ*=J/V²−1 相等，故分母和 T_* 的四种比较精确一致。低能量/坏集费用由 CompactGoodEvent 的实际原模型定理给

\[
P_n(H_{\rm cpt}^c)\le e^{-c_1n}
+\frac{1/16+16384S}{\sqrt n}.
\]

PhysicalCompact.actual_physical_zero_probability_and_compact_transport 还给

\[
P_n(R_n^2=0)\le e^{-c_2n}
+\frac{1/16+16720S}{\sqrt n}.
\]

这些消费者的前提只有已给原 h/μ 的 L²、对称、中心与投影归一化；没有另需 bounded-polylog 产品包络或未付的坏集假设。这里残差用 L² 支付的是 compact 绝对误差中的 S/√n，**不是从 L² 得到普遍的残差指数尾**，与 v152 的条件式大偏差 payer 范围不冲突。

设 c_n=4(n−1)/(n−2)²、τ_n(x)=x/√(1+c_nx²)。已接受有限行转换在正 R_n² 上给 T_*=τ_n(T_n) 及严格/闭关系；[0,1] 被 τ_n 映入 [0,1]，且 |Φ(τ_n(x))−Φ(x)|≤12/n。实际 consumer 的共同前置误差为

\[
E_0=C\left[L_y+16(1+4096)(1+y)\frac S{\sqrt n}\right]
+2e^{-cn}+\frac{1/8+33104S}{\sqrt n}+\frac{12}{n},
\quad y=\tau_n(x),\ c=\min(c_1,c_2)>0.
\]

真实 |g|^p 给 L_y≤β(1+y)^p n^{−(p−2)/2}≤8β n^{−(p−2)/2}；真实 residual full/deleted 成本已经有上述 16(1+4096) 界。用 S≥1，所有 n≥3 上指数项和 1/n 均可吸收到 S/√n；已接受 rpow-rate 证明可选择一个共同 K=131112C+33117+2/c。264 直接接收这个一次选择的 K，未将“存在付款”重新留给原模型调用者。

## 6. x=0 的严格 CDF、x=1 的闭尾与原子

原子处理没有使用虚构反射包，也没有假设原尾概率随阈值连续。实际 CompactTailBounds.ambient_weighted_ae_compact_tail_bounds 从闭 CDF 输入取得严格比较时，使用 ε_k=1/(k+1)>0，令 D1_k=D1+ε_k、A_k=A+ε_k、Adelete_k=Adelete+ε_k；删除差不变，总 compact 成本只增 ε_k。闭比较事件

\[
\{W+D1+\varepsilon_k\le xVb\}
\uparrow\{W+D1<xVb\}.
\]

通过概率测度对递增可测事件的连续性和真实成本极限取得严格比较；零投影分支也同步把其约定 κ 改为 κ+ε_k。阈值 x 保持不动且始终非负，故在 **x=0** 不需使用负阈值 CDF 输入。这里使用的是合法 buffer 和从下连续的事件，不是把有原子的分布函数当作连续函数。

物理零分母也保留严格/闭的不同修正。PhysicalCompact 的实际法则在 Z±={R_n²=0, ±U_n>0} 上给

\[
P(T_n\le x)-P(T_*\le\tau_n(x))
=\begin{cases}P(Z_+),&x\ge0,\\-P(Z_-),&x<0,\end{cases}
\]
\[
P(T_n<x)-P(T_*<\tau_n(x))
=\begin{cases}P(Z_+),&x>0,\\-P(Z_-),&x\le0.\end{cases}
\]

所以 x=0 两种 CDF 的零分母贡献并未混同；二者分别由真实 P(R_n²=0) 支付。Gaussian 比较使用的是上节的连续 Φ 与 τ_n 的定量界。

最终严格上尾是 {x<T_n}={T_n≤x}^c，闭上尾是 {x≤T_n}={T_n<x}^c；对原概率测度取补集正好保留同一误差。因此 **x=1 的闭尾**直接来自 x=1 的严格 CDF，不需忽略 P(T_n=1)。四种比较共用 ε_n；普通推论是 P(T_n=x)≤2ε_n，而不是 P(T_n=x)=0。264 最后的四次 Borel 区间法则运输还精确保留了这些原子。

## 7. 本批关闭什么，仍不关闭什么

相对 v155，本条实质关闭了“条件于明确 scalar CDF 输入后，实际 compact 成本怎样进入原概率、原物理紧区间 CDF/尾”的消费者缺口；任意原可测 Ω 的约化/回运、原真实 p 矩、n≥3、四关系、真实零分母和费用吸收均已接通。不能再把这些已发表输出列为尚待提供的编码同律、包络或无原子条件。第4节有限行与投影记号的等同是所列已接受定义/恒等式的普通代数蕴含，不冒充本批另发表了一条同名 Lean 包装。

必须继续保留：

- **外部输入**：ScalarShaoZhouFiniteCostCDFInput 的完整 L² 域存在/证明和准确文献归属仍未由264交付；它与 v155 的 broader tail hSZ 是不同命题。相关 Shao–Zhou、自归一鞅/随机区间输入的原归属不被改为本单元的新结果。
- **窗口与误差种类**：本 TYPE 是 x∈[0,1] 的绝对误差，允许 h 本身无界但 L²、g 有真实 p 矩；“无界核”与“无界阈值”不能混同。负阈值、更宽紧区间、growing x、整个实线 Kolmogorov 或相对尾，不是本条公开范围。未来可对 −h 明确重用已给定理作其他组合；这不是本证明已假设一个反射 CDF 包，更不应将它引入作为 x=0 严格 CDF 的前提。
- **族的一致性**：一个固定模型的 K 不给随条件化/截断模型变化的统一 K；证据中 c 可以随模型变化。p54 条件 p 矩只有收敛/充分大 n 一致有界的修复，不因此升级成任意多项式变化率、统一条件族消费者或严格 upper-event 余量。
- **其他根范围**：同批263单窗口、更广无界包络条件化、DC、full OQ56/root 由各自精确接口和审查负责。本次不读取未发布265以后，也不从 compact CDF 消费者宣告这些范围关闭。

本次唯一写入为本报告，未修改其他文件或旧冻结证据；未执行 Lean/AX/SSH、联网、Git/API、调度或新增上下文。规定 gpt-6.1-sol/xhigh；实际 model/backend/effort、input/cached input/output/reasoning subset 均未暴露，分别为 null。

## 承重只读源码指纹

下表均位于 C:/game/shao lean/library/。读取限于本文引用的完整定义、公开承重陈述和必要消费连接；旧完整证明与机器证据按既有资格复用。

| 文件 | SHA256 |
| --- | --- |
| Shao/OQ6/NormalizedIntegrableCDFAssembly.lean | 797b0a65ef59b3d7cd9a774aaf6f9d664c1e55168614a0a97eca205ba675cfd0 |
| Shao/OQ6/OriginalCountablyGeneratedModel.lean | 8691f69ca9ab84649f92b20385c415a2129250cc8f64375d6296e2d59a381627 |
| Shao/OQ6/ActualPhysicalCompactCDF.lean | d264ae1c1f04cee3b43ec5e44829a5986574d70f30615f7bdeb1f1bfab2a14ae |
| Shao/OQ6/ActualUncenteredCompactCDF.lean | 73d65132b550dfb9f4abfb41a0a34d67f11628d0f91ece53226db9580eefc6e9 |
| Shao/OQ6/CompactTailBounds.lean | 720e06311802591f73a5abc2941afa2f9110e74bdc564bf1ebcefe7b6d5102d3 |
| Shao/OQ6/PhysicalCompact.lean | 55f09e9c4998ab239fdbfcd08a945f5a88354ae14a69f5b5e5761cc7ce2d6e5f |
| Shao/OQ6/FiniteRows.lean | bb4dc865f5ab96ce57814f0721fbd31a2885d6fce7a9facd150941c4c2f91930 |
| Shao/OQ5/P51/BoundedStudentizerGeometry.lean | bc64d3e11a64f62ad654305ce579c1779546d4df37b5593090105af910502edc |
| Shao/OQ6/CanonicalDoubleGhostScalarMoments.lean | 17790c480efcab2d11cb5d00ccd215a6853e289fb078b5b041ae3bba972ab68c |
| Shao/OQ6/UntiltedCompactCost.lean | a7ab6509e2008e568c8707d4d07b517bd94797218347589193e65f7242dca111 |
| Shao/OQ6/CompactGoodEvent.lean | 5985db59268a5566b4ea96b76d076a1c4852fdf593071a2608be2b4a0c50bb92 |
