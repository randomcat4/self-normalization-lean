# 原始 OQ3 D：小正参数全局极小存在与全部极小点定位的来源蕴含审查

日期：2026-10-28。独立审查者：/root/original_d_strictness_source_review。使用既有 math-theorem 角色；不使用 math-ultra。本报告仅核对 PR532 的 JU361–KD370 与原 D 的数学衔接，复用五份合格完整证明审查，不重新审查十个局部证明，不使用 KE371 或任何后续未发布结果。

**STATUS: CORRECT_FOR_SMALL_POSITIVE_GLOBAL_EXISTENCE_AND_ALL_MINIMIZER_LOCALIZATION。对同一个已经具有原 D 谱严格性的实际十六点律，本批证明了：每个充分小固定正尾参数的真实全尾域都有严格正、有限的全局最小率；所有全局极小点，以及整平面上不高于该最小率的全部点，均进入预先指定的任意均值邻域。分布在全部尾参数、邻域和样本量之前固定。**

**原 D 的完整正则唯一鞍点及尾展开应用仍未由本批合格声明闭合。已有定位结果可合法接入接受的零倾斜均值逆图，为全部极小点提供实际对偶参数、真实 Legendre 取等及正定协方差；这些不再是需要另假设的条件。仍须完成边界紧性、边界驻点关系和优化参数的负号、严格正切向曲率及唯一性。KC 的均值外间隙不等于围绕一个唯一正尾鞍点的间隙；它已足够给出固定均值图外的粗远场指数界，而更小鞍点邻域的原远场消费者仍须等待真实唯一性/分离接口。**

## 1. 精确版本与复用证据

原来源实际哈希仍为：

| 原来源 | SHA256 | 本次承重内容 |
|---|---|---|
| C:/game/shao/current/oq3/proofs/r2/report.md（R2） | 572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55 | 45–79 的正则/唯一鞍点条件，343–373 的紧倾斜，375–491 的同一抛物线见证及最后的小正参数应用断言 |
| C:/game/shao/current/oq3/proofs/r2/repair01.md（RP） | 9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd | 标准化输入，边界坐标公式 (8)–(14)，212–226 的显式实际远场条件 |

本次以已读的相关原段和之前已完整读取的 RP 为依据，不改变来源。已接受 v148 的独立原 D 谱严格性报告保持封存 SHA256 6f1ba1abd4cd5280d7eaafb1cc3bc47388ab978cf9773781e0d56c8a5d36f9ee；本报告对其后续范围作新判断，不回写旧报告。

审查对象为 [PR532](https://github.com/randomcat4/shao-lean/pull/532)：

- head：4b371480f4d9a7989d441a068320593462c188cd；tree：3fea53deb13d60fea491a6c841b55d7e97e1201a；publication-record 的 overlay parent：fab5735927722fca9dc9c82613afef6b5d1fbd51。
- 本地 packet：C:/game/shao lean/drafts/oq3/publication-u22-small-positive-global-minima/。
- publication-plan SHA256：ebb415d529022e6600a61fe26d840ff3144b9a11d4440b2490a2edcab07d8dfe；publication-record SHA256：8d0feb6144a916c32da6edc4888714d33a9354438baf39880d55ebc22ad700df。
- source-map SHA256：c8400c4e034d8143a56019ebc090fb98906556ba52e05ed68c2e9412ae0aec28；manifest SHA256：186f8ba31cb8e84f5db83e2967aae018c4f600a10b0e3f06baef2d4610be323e。

已完整读取全部十八条实际 TYPE（包括生成声明）及承重公开声明、KA 全部数据/概率证明 let、KD/JZ 的有限可行点与定位衔接。为本次语义审查，原局部证明结论直接复用合格独审；没有重新做十份完整证明审查。精确源如下，路径相对于 packet 的 Shao/OQ3/：

| 单元 / 源码 | SHA256 |
|---|---|
| JU361 SymmetricEightAtomCompactTiltWitness.lean | c0eb09893cd152f6b77b2ce69ee7228268a93adb411326206b47643f19e2fa0d |
| JV362 BoundedParabolaRectangleSeparation.lean | df78dcfa2a177d2e6a440afcfe8142da895b328fefcd44712306e90a0dbd8dcf |
| JW363 BoundedParabolaLegendreCompactSublevels.lean | 9510b16dfeafa0c257890a78520277eb8a5ad2d2a1bcc44ce75076061688fc59 |
| JX364 SymmetricEightAtomPositiveEnergySupport.lean | 3fd880eb5bd250033a78e377884b60163f494831399830d211815e9118a8f4c9 |
| JY365 BoundedParabolaTailGlobalMinimum.lean | e39dd81451cb3496ec26039721388c256ee13318a8a95193e458aaa39fb9eaa2 |
| JZ366 BoundedCenteredParabolaSmallPositiveMinimum.lean | 525bca5279e7c91b4d9abbea9ac2e0465562088fca6caf05232e8b542910a218 |
| KA367 SymmetricEightAtomSmallPositiveMinimum.lean | 8222b7afcc4418e4cb1c8269858fefec17a647a1c7784b0076cf6a2509e58b47 |
| KB368 BoundedParabolaLegendreZeroSet.lean | 9e526278b01d912ec4c981c0eb700bcd4edfc0bebc11704bf637103978f37899 |
| KC369 BoundedParabolaMeanRateGap.lean | bcf54b06a346508d69f865e4bb785c685eb7c643588cb34530e3288f628999b3 |
| KD370 BoundedCenteredParabolaMinimumLocalization.lean | d9d40d3fb394aed773e71b49740bbf26d40bd26d81c765a58383a71c38b7259f |

本地确定性核对了十份源、十份 actual-types、十份 qualification、十份 receipt、五份完整独审报告，共 45 项精确字节数/SHA256，均匹配 plan。十份资格均为 COMPLETE_QUALIFIED，parentFullReportRead/reviewerCompletedStopped 均为 true；source、actual TYPE、同一 first-original-O 绑定相符，保存的实际 all-owner AX 收据自然 RC0，递归公理只有 propext、Classical.choice、Quot.sound。没有新的 Lean/AX 或服务器观察。

复用五份独审，均位于 packet 的 docs/oq3-u22-small-positive-global-minima/：

| 报告 | 覆盖 | SHA256 |
|---|---|---|
| u22ju-proof-review.md | JU361 | a7c658c33df4e037906d6d5f0b8585c7382d950eaacc149fe3e00e363ee5905f |
| u22jv-proof-review.md | JV362/JW363 | 1bb57df191b4ff864e0bdc1a07c9e384977557456657b421ac4795ca3ac0f8fa |
| u22jx-proof-review.md | JX364/JY365 | d3a1ff82305b0683cf56e851f5bed2764549fc8062fb69ff4d616f6074a6ca3c |
| u22jz-proof-review.md | JZ366/KA367 | 73b66a8ded3723a321b0fda1c7a0463092581e600a2f6e795a5246e5067f3758 |
| u22kb-proof-review.md | KB368/KC369/KD370 | 0df98df355641d9cb78f2b842ac82ed535cee66573cc9f7da12a633a501b6995 |

关键实际类型的精确 SHA256：

| 类型文件 | SHA256 |
|---|---|
| u22ka-actual-types.txt | a398f22e064d1ed2119469ae4b8c47db6493c18ef59185cadd901e311dfe180d |
| u22kb-actual-types.txt | 2b44ed4ddef216487b7d41cadee19d06534956606bd5af6a19a758dccae0be6c |
| u22kc-actual-types.txt | 7dab67acff7fa6cb900edea3149faa76fb41b1e3263877ba8c1570c4f8bff9bf |
| u22kd-actual-types.txt | 0faa5b6c75161bc9f89579d565e6c46ac796e8aef8c3a24a59b584a9a5fc66b8 |

KA 的第三个 SOURCE let 是明确的概率证明 (symmetric_eight_atom_law_and_phase_gap a).1。实际内核 TYPE 的两个数据 let 是 A、mu；该证明值内联至 LegendreRate 的 NeZero 实参。既有 qualified KA 完整审查和哈希 81004c826f74c7157426090f8bc11ecb5ed97eb0d7c362390939a46c61f6fb55 的完整抽取结果已覆盖同一 a 的 JD 概率证明骨架。没有新增非零测度假设或第二个分布见证。本报告复用该证据，不声称模型读了 347143B 原始 AST 日志，不重新展开或执行检查。

## 2. 同一实际分布与真正全域率

固定 v148 谱严格性存在定理的一组见证 \(a\)：
\[
a_0=1,\quad0<a_0<\cdots<a_7,\qquad
\mu=\tfrac1{16}\sum_{j=0}^7(\delta_{a_j}+\delta_{-a_j}).
\]
JU 从同一 JT 见证保留所有合取，并输出任意紧倾斜族的一致性；KA 再对该同一 a、同一 A、同一 mu 添加正能量、右半轴质量、基准协方差行列式及全局极小存在。没有随 level 重选原子、权重或原律。

这里“同一”不是宣称不同存在定理中的任意两次 Classical.choose 必须定义相等。其准确数学含义是：先固定一个原谱见证，再应用普适的 JX/JZ/KB/KC/KD，即可对这个已经固定的律得出全部新结论；KA 的自身证明也确实把这一组合放在单个存在量词内。

令
\[
q_0=E_\mu X^2,\quad m_0=(0,q_0),\quad
K(s,t)=\log E_\mu e^{sX+tX^2},\qquad
I(z)=\sup_{(s,t)\in\operatorname{dom}K}\{sa+tq-K(s,t)\}.
\]
actual bivariateLegendreRate 是上述真实可积域上的 EReal 上确界，不是局部实值函数，不采用域外总化 log 积分代替真实率。JX 给出某个固定 \(B>0\)，
\[
1\le |X|\le B,\quad1\le X^2\le B^2\quad\mu\text{-a.s.},\qquad
\mu(X>0)>0.
\]
因此 \(1\le q_0\le B^2\)，所有矩存在，真实 MGF 域是全平面；JV/JW 证明
\[
z\notin[-B,B]\times[1,B^2]\Longrightarrow I(z)=+\infty,
\quad
\{z:I(z)\le L\}\text{ 对每个实 }L\text{ 紧}.
\]
此处只断言矩形外率无穷，不把矩形内每一点误称为可达或有限率。

原尾域保持
\[
D_x=\{(a,q):q>0,\ x\sqrt q\le a\}.
\]
它在整平面不是闭集；然而有限率次水平集已经满足 \(q\ge1\)，所以 JY 在紧次水平集内与连续弱尾不等式相交，获得真实紧非空集。原 \(q>0\) 和弱尾边界均被保留，未偷纳零能量点。

## 3. 小正参数下全局存在：量词与可行点都已付清

JY 的一般定理确实只在给定有限率可行点后推出全局极小，单用 JY 不能宣称原 D 见证已经存在。然而 JZ 已在零倾斜均值逆图中实际提供这个有限点：
\[
w_x=(x\sqrt{q_0},q_0)\in D_x.
\]
对全部充分小 \(x>0\)，它进入同一个零倾斜真实 Legendre 图，故 \(I(w_x)<\infty\)。这个点只作为上界测试点；没有把它声称为真正极小点，也没有假定所需鞍点。

JZ/KA 精确给出
\[
\exists\varepsilon_0\in(0,1]\ \forall x\in(0,\varepsilon_0)\quad
\exists z_x\in D_x,\quad
0\le I(z_x)<\infty,\qquad
\forall y\in D_x,\ I(z_x)\le I(y).
\]
比较量词覆盖整个原尾域，包括图外和实际率无穷的所有尾点。它不是“在图内最小”、不是预设全局最小、不是仅某个正 x 或一列 x 的存在。

KB 随后给出一个更强、与协方差无关的有界律事实：
\[
I(z)\ge0,\qquad I(z)=0\iff z=(EX,EX^2),\qquad
z\ne(EX,EX^2)\Longrightarrow I(z)>0.
\]
对当前中心律和任意 \(x>0\)，尾点满足 \(a\ge x\sqrt q>0\)，而 \(m_0\) 的首坐标为零，故每个尾点都与 \(m_0\) 不同。这将 KA 的“非负有限”强化为
\[
\lambda_x:=\min_{D_x}I=I(z_x)\in(0,\infty)
\]
对每个充分小正 x 成立。这里从 EReal 过渡到实数合法：严格大于 0 且小于 \(+\infty\) 已排除两个无穷端点。

原 D 的“任意充分小固定正 x”量词，已经在**全局极小存在和正最小率**这一子范围得到满足。x 仍是之后研究尾展开时固定的参数；这不要求误差常数随 x 一致，不包含 \(x=0\)、\(x=\varepsilon_0\) 或整个 \((0,1)\)。

## 4. KD 定位的是全部极小点，不是一个方便的选择

将 KA 的同一律代入 KD 的通用接口，所有前提都已支付：有界、中心、实际正能量下界 1，以及 \(\det\operatorname{Cov}(X,X^2)>0\)。于是得到
\[
\forall r>0\ \exists\varepsilon_r\in(0,1]\quad
\forall x\in(0,\varepsilon_r)\quad
\exists z_x\in D_x:
\quad0<I(z_x)<\infty,\quad I(z_x)=\min_{D_x}I,
\]
并且
\[
\forall y\in\mathbb R^2,\quad I(y)\le I(z_x)
\Longrightarrow d(y,m_0)<r. \tag{L}
\]
任何另一全局极小点 y 都满足率相等，故自动包含在 (L) 中。最后的 y 根本不要求属于尾域，结论比“选出的一个极小点趋近均值”更强。实际 Prod 距离为两坐标距离的最大值；按等价范数改半径即可转成通常欧氏邻域结论。

对每个小 x 定义整组 \(\mathcal M_x=\operatorname{argmin}_{D_x}I\)。它非空，且
\[
\forall r>0\ \exists\varepsilon_r>0\quad
\forall\,0<x<\varepsilon_r\ \forall z\in\mathcal M_x,\quad
d(z,m_0)<r.
\]
因此任意 \(x_k\downarrow0\) 和任意选择 \(z_k\in\mathcal M_{x_k}\) 都有 \(z_k\to m_0\)，不需要选择连续、单调或唯一的极小点分支。不能把 \(\exists\varepsilon_r\) 移到 \(\forall r\) 外面；那会错误地要求某个正 x 的极小点等于不在正尾域内的均值。

KC 给出的统一数值率间隙是
\[
\forall r>0\ \exists g_r>0\quad
\forall z,\quad d(z,m_0)\ge r\Longrightarrow I(z)\ge g_r.
\]
它以实际均值为中心，且在整个平面成立。KB 排除零率点，紧次水平集把逐点严格正提升为这个固定邻域外的统一正数。它没有提前选出任何正尾鞍点。

另一个直接的语义后果是 \(\lambda_x\to0\)（\(x\downarrow0\)）。JZ/KD 所用图内真实局部率
\[
L(w)=\theta(w)\cdot w-K(\theta(w))
\]
在 \(m_0\) 连续且 \(L(m_0)=0\)；\(w_x\to m_0\) 且 \(I(w_x)=L(w_x)\)。于是
\[
0<\lambda_x\le I(w_x)\longrightarrow0.
\]
因此本批严格正最小率不提供跨全部小正 x 的共同正下界；不存在与此极限相矛盾的“统一 \(\Lambda_0>c>0\)”结论。

## 5. 实际对偶参数、均值逆图和协方差可直接衔接

本次读取并复用的既有接受接口：

| library 下文件 | SHA256 |
|---|---|
| Shao/OQ3/OpenDomainLegendre.lean | 941c08552f300af2c85e2df7f55399b69c4468bca467fe88b8a303a6a3c74bc3 |
| Shao/Probability/BivariateLegendre.lean | d8bd5dc7099ffdbf52282ebb41ad03145a50b42547dec55bb42caacb31ed5f58 |
| Shao/OQ3/BoundedActualQuadraticExteriorExponentialBound.lean | 87a42571d3c0842e8bb86d81461e13423c5041a1b9db3a993e99176614bae0f7 |
| Shao/OQ3/BoundedActualExteriorFromUniqueMinimum.lean | f77a879d7e4b4f9b4a8ddb079db8b78bc0f3ef0243cbc6559f102ea6f2729455 |

当前律的 MGF 全域有限，基准协方差正定。故接受的 open_domain_quadratic_tilt_compact_legendre_chart 在零参数适用，产生固定均值图 e、正半径 \(\rho\) 和紧参数集 \(\Theta\)，覆盖 \(\overline B(m_0,\rho)\)。先把这个半径固定，再用 KD 取 \(\varepsilon_\rho\)。对全部充分小正 x，**每个**全局极小点 z 都在该图中，因此同一个接受接口给
\[
\theta_z=e^{-1}(z)\in\Theta,\quad
\nabla K(\theta_z)=z,\quad
I(z)=\theta_z\cdot z-K(\theta_z).
\]
这是真实全域上确界在实际参数处取到，而不是仅把局部率另命名为 I。e 的逆连续还给出所有这类 \(\theta_z\to(0,0)\)。不用预先假设极小点的对偶参数存在。

v148 已审查的有界紧倾斜 covariance/whitened-family 接口可用于同一固定 \(\Theta\)：真实 \(\Delta(\theta_z)\) 正定，谱界、标准化高阶矩和 JU 的 WC 常数在该紧参数集统一。当前律至少三个不同的抛物线点也直接排除任何非零线性/二次组合的零方差。故“只有基准 det，优化参数处协方差还是新的未知假设”并非本批加旧接口后的正确数学判断。

这不等于已经得到正尾边界鞍点：均值映射的逆解与在弯曲尾边界上满足法向/切向条件，是两种不同的条件。本节只认定已有接口的直接语义组合，不把尚未提供的边界优化证明补写成已验收 Lean 声明。

## 6. 均值外间隙已经支付什么远场，尚未支付什么

只从 KC 的式子不能直接读出围绕某个候选正尾点 \(z_x\) 的
\[
I(y)\ge\lambda_x+\eta_x
\]
在所有尾域图外点成立：当另一个同值极小点仍处于均值球内时，KC 完全允许它存在。KD 把全部极小点压进同一小球，也不排除球内有两个极小点。

但不能把本批说成“任何实际远场仍全无”。存在以下**较粗而合法的已接受接口组合**。固定 \(r>0\)，取 KC 的 \(g_r>0\)。由上节测试点连续性，进一步缩小正参数阈值使 \(\lambda_x<g_r/4\)。令闭集
\[
A_r=\{y:d(y,m_0)\ge r\}.
\]
整个 A_r 的真实率至少 \(g_r\)，严格大于 \(g_r/2\)。接受的 bounded_actual_quadratic_exterior_exponential_bound 对这个闭集和阈值 \(g_r/2\) 的全部前提已满足，因而给出固定 \(C_r>0\)，对所有 \(n\ge1\)，
\[
\mu^{\otimes n}\{\overline W_n\in A_r\}
\le C_r e^{-ng_r/2}.
\]
其对原尾域交集当然也成立，且
\[
\mu^{\otimes n}\{\overline W_n\in D_x\setminus B(m_0,r)\}
\le C_r e^{-n(\lambda_x+g_r/4)}
\]
对充分小正 x 成立。选择 \(r<\rho\) 可使这个固定均值球完全处于真实逆图内。这项结论不需要唯一性、不改变原产品律，且由现有 generic 概率上界接口直接导出；不应另立无支付的远场假设。

这仍不是 packet 声明中已经具备“任意所需小鞍点坐标邻域的原远场估计”。RP 的最终边界 Laplace 分解须围绕所选唯一极小点缩小坐标矩形，排除图内其余尾点；固定均值球之外的估计不排除球内第二个最小点。既有 bounded_actual_exterior_exponential_bound_of_unique_minimum 正是等待真实原尾域唯一性，然后输出以那个边界点为中心、带相对 \(\lambda_x+\eta_x\) 指数的原消费者。当前没有满足该接口的唯一性输入。

因此精确边界是：**固定均值图外的粗指数局部化已有数学蕴含；围绕实际唯一正尾鞍点的完整远场/局部 Laplace 分离仍未闭合。** 这项后者不是理由去重做任何旧概率生产者；承重缺口在真实边界优化与唯一性接口。

## 7. 原 D 的剩余正则条件不能由名称或库存替代

原 R2/RP 的正尾鞍点还要求
\[
z_x=(a_x,q_x),\quad a_x>0,\quad
q_x=a_x^2/x^2,\quad
s_x=-2a_xt_x/x^2,\quad t_x<0,
\]
以及
\[
\Lambda_1=
\frac{2t_x}{x^2}+
(1,2a_x/x^2)\Delta(\theta_x)^{-1}
(1,2a_x/x^2)^{\mathsf T}>0.
\]
本批直接给出的是弱尾不等式 \(a_x\ge x\sqrt{q_x}\)，没有边界相等式，未输出驻点等式、\(t_x<0\)、\(\Lambda_1>0\) 或唯一性。每点 \(\Delta>0\) 只能使上式的矩阵二次项为正，不能未经控制就抵消可能为负的 \(2t_x/x^2\)。全平面率在均值附近的凸性也不能不经论证地替代其在非线性尾域上的唯一最小点证明。

这些结论通常可沿局部边界优化继续证明；“有可能由标准分析推出”不等于本批已有其完整来源绑定证明。本报告不读取或借用 KE371 的边界紧性工作，不用之后的候选结果回填当前声明。当前仍需对同一实际律提供边界紧性及对应的源级参数符号/驻点/正切曲率与唯一性论证；不再需要重新寻找幅值、原律、有限可行点或全局极小点。

即使已给出实际对偶坐标与正定协方差，本报告也不把“存在一个有限正全局极小”改称“存在唯一全局正则鞍点”。原 D 最后一小段要进入正则有界应用类的断言，以及代入既有 B/C 固定点尾展开的完整应用，依然 OPEN。

## 8. 本次接受范围裁决

| 原 D 相关内容 | 本批及接受接口组合后的结论 |
|---|---|
| 同一实际十六点谱严格性见证、任意紧倾斜的一致 WC | 保留 v148；JU 已正式组装紧族 witness |
| 正能量下界、正右半轴质量、真实全 MGF 域及基准 det | 已闭合，无额外假设 |
| 全部充分小固定正 x 的真实全尾域全局极小存在 | 已闭合：JZ/KA，不是仅局部候选 |
| 正最小率 \(0<\lambda_x<\infty\) | 已闭合：KA 加 KB 或 KD |
| 全部极小点趋向实际均值；整个下方率次水平集定位 | 已闭合：KD；\(\varepsilon_r\) 在半径 r 之后选 |
| \(\lambda_x\to0\)、每个小参数优化点的实际对偶参数/Legendre 取等 | 由已读零倾斜图及 KD/JZ 合法推出，不需要增加数学假设 |
| 优化对偶参数处正定协方差、固定紧族矩/谱/WC | 由定位加既有接受紧倾斜接口推出 |
| 固定均值图外的粗实际指数局部化 | KC 加有限测试点连续性和既有有界概率接口已足够 |
| 原尾边界相等式、驻点关系、负二次参数、严格正切向曲率 | 本批未闭合；需要真实边界优化证明 |
| 原尾域唯一全局最小、其小鞍点邻域外的相对远场 | OPEN；不能将均值外间隙冒充此项 |
| 完整原 D 正则子类及具体见证的尾渐近应用 | OPEN，不因最小率存在而关闭 |

本报告区分数学语义组合与本批直接导出的命名 Lean 声明。全局存在、严格正最小率和全部极小点定位已有合格形式化结果；第 5–6 节的直接接口组装至多需要命名包装，不能制造新假设。剩余边界/唯一性/曲率部分则需要实质源级证明，不能仅靠一个包装声明解决。没有 x 窗口一致尾展开、\(\beta=2/5\) 端点、最弱条件或历史新颖性结论。

本次唯一写入为本报告；未执行 Lean/SSH/AX，未改生产源、REGISTRY 或旧报告，未启动子上下文。规定模型/强度 gpt-6.1-sol/xhigh；实际模型、实际强度、input_tokens、cached_input_tokens、output_tokens、reasoning_subset_tokens 未暴露，均为 null。
