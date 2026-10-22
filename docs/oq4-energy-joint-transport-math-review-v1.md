# OQ4 联合极限薄叶：独立数学审阅 v1

STATUS: CORRECT
GATE: MATH_ONLY
ACTIVE: false
E3_STATUS: OPEN
ROOT_STATUS: OPEN

## 审阅对象与隔离

本次为新上下文、匿名、独立数学审阅。只判断收到的证明是否完整推出冻结 v1；不以来源语义门的状态或其他审稿结论为数学依据。未修改冻结、证明或任何实现；未运行 Lean、重计算、Git 或缓存操作。所查前置为已经认证的实际有限接口，核对其透明定义与定理签名，不重新认证其证明。

| 输入 | 绝对路径 | SHA256 | 字节 |
|---|---|---|---:|
| 原文 source | C:/game/shao/current/oq4/energy01.md | 2e0387f0a35ca677853e45fff271cc2fb0e87db9ee9c6b2f00d3bcf56b51d9e6 | 5244 |
| 冻结 v1 | C:/game/shao lean/drafts/oq4/frozen-energy-joint-transport-v1.md | 415ae0a03c480d3dcc2d370662a9d4e050d941fe609821d2996c5c69ceb42fb4 | 6797 |
| 匿名 proof | C:/game/shao lean/drafts/oq4/energy-joint-transport/proof.md | 69364de066f5f008f4130f3ba8665b1455a91dc6716ad643ff234983d7daac2b | 20436 |

下文 F、P 分别指冻结与匿名证明，数字为本次输入的一基行号。报告自身的 SHA256、字节和编码检查由交付回执给出，避免把自指哈希写入正文。

## 覆盖矩阵

| 冻结义务 | 证明位置 | 独立核查结果 |
|---|---|---|
| 固定同一原律 ν、固定共同 M,T,C,H,P；保留真实原矩 | F13；P9–24 | 通过。没有换成随 j 变化的原律，也没有把倾斜矩当作原矩输入。 |
| 共同高度从 h→+∞ 内部取得 | F15,22；P107–142 | 通过。J_H 由收敛导出，未加入全序列 h≥H。 |
| θ 在所有长度、空间和样本之前选择 | F17–22,40,65；P105–142,470 | 通过。先对 (u,v) 的非空见证集作选择，所得 θ 不读取长度或样本。 |
| 同一 θ 的 E2 与全部有限长度结论 | F19–20；P113–139,211 | 通过。实际 common_bounds 的量词是 ∃θ, E2 θ ∧ ∀m, Relative θ m。 |
| 只用 h→∞、n/h³→0 | F24；P146–184 | 通过。n 可不趋于无穷；未用 n/h²→∞。 |
| e₂,e、四个指数、δ₂,δ 的真实极限与尾部非负 | F34–42；P155–184 | 通过。1/h→0，n/h⁴=(n/h³)(1/h) 最终成立，全部极限由此推出。 |
| I 的实际被积函数真正可积 | F30,44；P208–224 | 通过。是实际 Relative 结论中的 Integrable，不是总化积分的默认值。 |
| 实际乘积律与两组有限指数夹界 | F26–30,46–47；P188–224 | 通过。事件和实际律均未替换为任意实数输入。 |
| δ=exp(e)−1 同时控制上下两侧 | F49–53；P226–264 | 通过。证明了 1−exp(−a)≤exp(a)−1，保留非负 r 因子。 |
| r=0 与无条件比值的排除 | F53；P250–274,474 | 通过。r=0 强制 p=I=0，无任何除以 r 的步骤。 |
| 每个 η>0 的相对误差与 exp(±η) 尾部 | F53；P261–274 | 通过。尾部可依赖 n,η，但不依赖样本实现。 |
| L,Z 的实际尾部正性 | F61；P26–39,82,278–284 | 通过。L>0 由实际 normalizer 接口，Z≥1/2 由实际 E1 结论供应。 |
| n log L、|θ|h 以及 L^n 的极限 | F57；P286–318 | 通过。先有正底数幂恒等式，再用连续性；未使用非正数总化 log。 |
| n(log Z−s/h²) 与真实能量因子极限 | F58–61；P320–357 | 通过。保留 Pβn/h³，之后才用 β≤M；有限 j 未把该因子设为 1。 |
| 实际路径身份及终点支付 | F55–61,69；P359–380 | 通过。I=Bp 与同 θ 的线性路径身份准确；端点始终是原 closedStrip 中的 S_n。 |
| 三空间、逐行 iid 的可测性、独立性及边缘 | F63；P382–440 | 通过。分别使用三个实际边缘，不要求一个样本族同时具有不同律。 |
| 样本概率、样本能量积分的精确替换及相对界 | F63–65；P442–466 | 通过。替换的是确定实数，不声称跨空间逐点相等；不增加跨行独立或耦合。 |
| n=0、有界 n、早期零/负高度、M<1、T=0、s=0 | F69；P472–476 | 通过。均保留；s=0 仍保留实际截断归一化与 Z 幂。 |
| 弱闭端点原子、全零路径、无额外原律正则性 | F69；P84–103,474 | 通过。无删边界、密度、四阶矩、指数矩、对称或非格点假设。 |
| 范围没有扩大到完整 E3/OQ4 | F71；P478 | 通过。式(9)/(10)、K/Kv、killed 边界、E4、随机分母与完整根继续 OPEN。 |

## 实际前置接口核对

本票接受任务给定的已认证有限定理，并核查其确实是 canonical 实际对象上的声明，而非把待证结论作为输入的替身。核对的源哈希与给定版本一致：

- EnergyRelativePathBounds：7f9242f4116924f26c9c7b75313e4e37b49c13f7da4f4052e7a7585984a2b654。
- EnergyE2Bounds：41b7343861549f55ae86cddb514a5ed55612448b1ab0efc1e3bb580182746ca8。
- EnergyE1Bounds：448db6e250307358455e7c8da660ffdb094ddb5a42f0e7e81e9c08c02aa4d39d。
- EnergyLinearPathLaw：039ad7326ea9a80e476f50bf3f46dd0078c2c61f6786f15a6d72f3ba0c227afb。
- EnergyLinearTiltLaw：63cf342dcbe3cce728a42b283a539b8a56043f74a23f6f888ef94df378dcde78。

`energyE1_common_bounds` 的输入正是 ν 的概率性、M,T 非负、energyLogThreshold≤h、|s|≤T、原平方及绝对三次方可积、原均值零、原点二阶矩一、实际 β≤M。其透明 `energyE1Conclusion` 返回实际 energyTiltedLaw 的概率性、三种矩可积性、闭支持、h≥2、Z∈[1/2,3/2] 和所引 Pβ/h³ 对数界。不存在额外输入 Z>0 或已经完成的 E1 误差。

`energyE2Threshold` 透明等于 energyLinearCenteringThreshold；`energyLinearCentering_height_bounds` 在所需 M,T 与高度前提下返回 energyLogThreshold≤h 和 h≥2。`energyE2_common_bounds` 使用相同原矩前提返回存在 θ。透明 `energyE2Conclusion` 包含实际 energyLinearTiltLaw 的概率性、支持、三矩可积、真实均值零和 P44–52 的四界，故 P26–55 的引用条件完整。

`energyRelativePath_common_bounds` 的实际签名没有输入 θ、路径界、概率性或可积性结论；它在固定原矩及共同高度条件下返回 `∃θ, energyE2Conclusion ... θ ∧ ∀n, energyRelativePathConclusion ... θ n`。其透明 Relative 结论正是两组真实 Measure.pi/closedStrip 夹界以及 energyPathIntegrand 对原 ν 乘积律的 Integrable；透明 Error2/Error 与 F34–35 相同。辅助 `energyRelativePath_bounds_of_e2` 允许用已经取得的同一个 θ，并不重新选 θ。

`energyLinearNormalizer_pos` 的高度要求仅为 h≥1，另需 T≥0、|s|≤T、原平方可积与二阶矩一；这些在共同尾部均满足。energyLinearNormalizer 实际定义为对 energyTiltedLaw 的 exp(tx) 积分。两种倾斜律均为实际 withDensity 定义，未使用任意候选密度。energyWeight 采用 |x|≤2h 的闭截断，energyPathIntegrand 的实际方程采用 closedStrip 内的 exp(s(energy−n)/h²)。

`energyPathLaw_integral` 与 `energyLinearPathLaw_integral` 的签名确实返回实际可积性与 P362、P368–370 的等式；后者使用同一 θ。`energyLinearPathLaw_base_probability_iid`、`energyLinearPathLaw_probability_iid` 的样本前提正是各自可测、iIndepFun、逐坐标 IdentDistrib。`energyRelativePath_integral_iid` 另外使用已取得的 E2 结论，明确返回样本被积函数 Integrable 及与原 ν 有限乘积积分的精确相等。共同 `iid_samplePath_map_eq_pi` 无额外连续性、无原子或正生存前提，并允许 n=0。因此 P407–440 没有把需要认证的概率基础改成新假设。

## 完整推理审查

### 选择顺序与共同尾部

P113–121 对每个合法 (u,v) 使用已经认证的全长度有限定理，得到非空 G(u,v)。选择公理只对固定 ν,M,T 与该输入对选见证；随后 P124–128 在 h_j<H 时置零。这在逻辑上先于任意 n、任意状态空间及样本族。h→+∞ 的定义保证存在 J_H，使所有后续 h_j≥H。因此同一个 J_H 上 E2 及所有 m 同时成立，后取 m=n_j 合法。证明没有把每条长度序列各有 θ 的较弱结论冒充冻结要求。

### 联合尺度与真实相对误差

1/h→0 仅在最终 h>0 时证明。令 q_j=N_j/h_j³→0，则最终 N_j/h_j⁴=q_j/h_j→0，故 e₂=C/h+C N/h⁴ 与 e=PMq+e₂ 趋零。最终 h≥2，且 C,P≥1、M,N≥0，供应误差非负；指数连续性给全部 exp(±e) 与 δ 的结论。早期任意总化实值均不会改变 atTop 极限。

关键实数步骤 P226–250 完整：由 exp(−a)r≤x≤exp(a)r、a,r≥0，设 t=exp(a)≥1，得到 x−r≤(t−1)r，且 r−x≤(1−1/t)r≤(t−1)r。于是 |x−r|≤(exp(a)−1)r。下侧误差确实被同一个 δ 控制，不能只引用上侧。这一步没有除以 r；r=0 时两侧直接给 x=0。因此相对尺度在任意小生存质量及零质量时均完整保留。δ→0 与 e→0 分别供应 ηr 误差及 exp(±η) 夹逼，未以绝对差趋零或未定义的比值替代。

### 正归一化与真实能量支付

P278–284 先取得实际 L>0 与 Z≥1/2，随后才使用 exp(log x)=x。P302–314 对自然数幂的归纳包括 m=0，因而 L^n=exp(N log L) 的使用域正确。|N log L|≤C N/h⁴→0 与 |θ|h≤C/h→0 足以给 L^n→1 及终点指数两端趋一。

能量支付中，|N(log Z−s/h²)|≤Pβq≤PMq→0 使用最终 q≥0 和 β≤M；Pβ 为真实原矩系数，未提前删除。由 Z>0 可将真实 exp(−sN/h²)Z^n 精确写成 exp(N(log Z−s/h²))，因此趋一；有限层面仍保留该因子及其指数上下界。路径身份 I=Bp 与线性身份始终作用于同一 closedStrip。其 k=n 条件直接给 |θS_n|≤|θ|h，完全不需要累积均值漂移或移动边界。

### 可积性和逐行三空间转接

P214 的 Integrable 来自实际有限结论，且 F 非负；故 I 是有限实际积分。三个独立应用的 samplePath 推前等式各有自己的概率空间、可测性、iIndepFun 及指定边缘。有限连续前缀和所定义的 closedStrip 为 Borel 集，故事件概率可精确换元。原律样本积分的可积性和等式又由实际积分接口共同返回；单纯总化积分相等不是论据。

这些等式仅识别 p、r、I 三个确定实数，所以不同空间间不需要耦合。每个有效 j 可有不同状态空间和不同有限实现，分别代入即可；没有跨 j 的随机序列极限定理，也就没有跨行独立性、共同概率空间或联合可测性要求。相对误差的尾部由确定性 n,h,s,θ 和 η 决定，故统一适用于当行全部合格样本实现，不会因样本改变 θ。

### 退化情形与范围

n=0 时，正高度尾部的闭条带包含唯一空路径，有限乘积概率为一，能量及前缀和为零，I=p=r=1，所有零次幂为一；冻结误差仍可为 C/h，无需擅改为零。有界或任意变化 n 只受 n/h³→0 约束。早期 h=0、h<0 或 h<H 仅影响有限前段，证明未赋予那些序号真实概率或正底数解释。M<1 的空分布类按原全称量词处理，未补 M≥1。T=0、s=0、闭端点原子及格点律均保留；s=0 没有把实际截断律误写成 ν 或删除 Z^n。

原文 source71–83 的能量加权积分、两次精确换测度及同一绝对部分和事件在本叶保持。该结论不涉及 source85–97 的共享双变量算子/微分共轭，不使用 K 的生存正性与 n/h²→∞，也不返回 E4 条件能量结论。式(9)/(10)、K/Kv、killed 边界、反射账本、随机分母、完整 E3 与 OQ4 根均保持 OPEN。

## 缺口与最小修正

未发现数学关键缺口；不要求改动冻结前提、事件、常数、原律或量词，也无必须修订的证明步骤。

仅有非阻断排版问题：P70 用 `]` 关闭 P66 的 `\[` 数学环境；可将其改为 `\]`。这不影响本次数学判断；本票未修改匿名证明。

本票的 CORRECT 只通过数学门。当前联合极限新叶没有据本票获得 Lean 编译、传递公理审计、独立 no-o/full-source 或负责人导入复核认证；不应标记 LEAN_FULLY_CHECKED。DONE。
