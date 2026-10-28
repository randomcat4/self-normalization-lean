# 原 D 最终应用：PR535 的原来源数学蕴含审查

结论：接受 PR535 精确版本对原 D 的最后衔接。此前已接受的同一十六点对称分布，现在确实具有所有充分小正参数的实际边界鞍点、正确符号、原始切向正曲率、整个原尾域上的唯一全局率极小点、指定小鞍点邻域外的完整概率指数估计，以及修正 p54 常数的固定参数尾渐近。没有尚未实例化的远区前提，也没有把谱见证与应用见证分别存在而误合成一个见证。原 D 的存在性严格性及其正则有界应用可在数学范围上关闭；不需要再增加一条同名根包装来补数学缺口。

这里的“关闭”严格指 R2 第 6 节最后所需的一个抛物线十六点见证及其充分小固定正参数应用。它不把条件式一般修复变成对任意分布、任意正参数都成立的无条件展开，不声称变化参数窗口上的一致误差常数，也不代替 Root 的实际聚合/保留性门或此前独立的反例验收。下文给出量词和各项承重义务的具体理由。

## 1. 来源、版本与本次复用边界

本次直接核对的只读原始来源为：

| 来源 | SHA256 | 实际长度 |
| --- | --- | --- |
| C:/game/shao/current/oq3/proofs/r2/report.md（R2） | 572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55 | 20102 B / 523 LF |
| C:/game/shao/current/oq3/proofs/r2/repair01.md（RP） | 9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd | 5846 B / 226 LF |
| C:/game/shao/current/oq3/verdict.md | fd0a5732845aa96ab1725e6d1e52676502092e49d2c00225ce1fde26ac06f3b5 | 3041 B / 58 LF |

承重原文是 R2 47–79 的固定参数充分修复、343–373 的有界倾斜稳定性、375–491 的真正抛物线严格性见证和最后的小正参数应用；RP 全文已经读到，其第 1 节以 Song 的统一族输入修正旧对角论证，第 3 节确定法向/切向系数与常数，第 4 节明列远区概率条件。本次没有把 R2 原句“隐函数论给鞍点”或“有界时由紧性自动得到”当作证明。

PR535 的 head 为 4c24defa2abf2eb24a54f03a97d20b2b7be84638，tree 为 616a67d66653e8df03a624db4c2483d140866e4a，parent 为 81c2b1820fe43c38b8e2a5c82a4269c670cd2676。读取精确 packet：

    C:/game/shao lean/drafts/oq3/publication-u22-regular-unique-tail-expansion/

其 handoff SHA256 为 d1974647e173abb02ce8650e32369ecb99f5cf14bd7b7e4a57ebcde25879aee5；publication-record 为 b91f15e4250e0824eefa865711d249900ba062de2aeba5939513b0462d3c8a1f；plan 为 9b925eb76459bc2cfd228be7042fbef2bcdbd6dbd0b3c7539e9248111f38d680；packet manifest 为 c56597354d29664f59a6af526d607133a7debc72e9663e3a71adbf06ea52f1b7；changed-source/source-map 为 13ca8a1d9d64777cf7958d0301b71a09bcc0ae2aa18f37be668e185db75552ff。

本次完整读了十二条实际 TYPE，特别整读 KM/KO/KP 的实际输出、相应承重源码和三份最终独审；其余局部证明的完整独立审查按资格复用，没有另做十二份证明重审。对十二源、十二 TYPE、十二 qualification、十二 receipt、九份独审共 57 个不同文件逐项重算 SHA256/字节，全部与 manifest 相合；每条资格均为 COMPLETE_QUALIFIED、parentFullReportRead=true、reviewerCompletedStopped=true，每条实际 1 TYPE/0 非定理 VALUE，首原对象和 TYPE/source 引用与各 receipt 一致。各 receipt 的自然内核/同首原对象递归 AX 成功证据所列传递公理恰为 propext、Classical.choice、Quot.sound。本次未重跑这些检查，也未把历史 receipt 的 PENDING_FRESH_FULL_REVIEW 标签误作当前资格。

以下源均在 packet 的 Shao/OQ3/ 下，TYPE 均在 docs/oq3-u22-regular-unique-tail-expansion/ 下。

| 单元、源文件 | 完整源 SHA256 | 实际 TYPE SHA256 |
| --- | --- | --- |
| KE371 BoundedCenteredParabolaMinimumBoundary.lean | 0336d9dd800bec50c57391bfcb8ab01d61920b9391a23718c4dd11108c776b96 | 7fed8365a3a85bfb2aea75e6e4fe69524770a8312ecbe3486234da6b97f1af25 |
| KF372 BoundedCenteredParabolaBoundaryTiltSign.lean | 2a79bc75f017b19700bf8d55381e13075d3a270487f328484dde29df985d8baf | 694e7604eccf9cf60b5b198f89f2d678a516dbb06445cd5e4a054f2fdda97a54 |
| KG373 BoundedCenteredParabolaGlobalBoundaryTilt.lean | 3c2f9c6c43bf9981e813f783fc5d1110b6a3cc596e4be5271eeb22f67afe867a | 29d8c5d44a774d1aeeb06c3242edeaf06e56b3d3605de49d4846788394496e8a |
| KH374 JointEnergyCurvatureNeighborhood.lean | b29ebe1b35c27dd0f1400b9bf84ddfd1e33ade28dffd3deff758711086e21a68 | 070ba17711da6c79aa34fe1d88ce3713f553e65e47f8d428b2b6a735d3a73133 |
| KI375 ParabolaEnergyCurvatureNeighborhood.lean | b0e88e7d3e1436f64fcea19fc85c1a2c40b795b9f3ff1c4887a4a6fb27da96dc | 1641dd8cae4712dd33c8c7e659dddea0a284f4f3a7dad1e8632353a7caf68827 |
| KJ376 BoundedCenteredParabolaRateCurvature.lean | 7261bc52a019f75f98df9bbf4c9f8bfb2f81c8c391fdfdb6024456ecaaa6ed9b | 8206cc4a6af63a257704b991db146800e2c034063230df11c83bfacda769124a |
| KK377 BoundedCenteredParabolaUniqueMinimum.lean | 1ac210f88ccada9ed71df6ff6c1e857772dd4dc18976e6667d1f962cbde4c370 | 4257c69c94addca999dfd5368aa6d0d03ac401d121adc362a6658809576ac5b2 |
| KL378 ScaledTangentCurvatureNeighborhood.lean | 3ac0df885fb481485e1f711dd0ea66452cb2937597ae792acd407e8ae4cf1878 | 3d53d7c5d2f3bdee70ecb54dcaccd9d3e8ab14f754eb88ec16403f1564df37d0 |
| KM379 BoundedCenteredParabolaRegularUniqueSaddle.lean | eea615a58568c00d67b2cb9bd11e6e822a1ee0aab3e2640db13b612d5ff548af | 77a6365147689db58e5d997e287f535a8b4e97770b3ddc1c580c5b09508f055f |
| KN380 BoundedParabolaWholeTailRateGap.lean | 27bd9434219378e469494669778b622395d9dcfd4cbc822a76baf939ffed6da2 | 3b4dcd79f765cad9bdfd5614525f701c1fff539f9a5951edaaf3cc67d6112e72 |
| KO381 SymmetricEightAtomRegularUniqueSaddleWitness.lean | 0bc8ce9f01fa07359c55f54859bcef7cef03f947beb3bda00b9129136b53c18e | 3c5937f7156f7e242d96533500e6508829fb35ce520431cc0294342ff9c49a05 |
| KP382 SymmetricEightAtomCanonicalTailExpansion.lean | 122531acb80f700bc4e26781d7f09ced4d1ab335cc514dcb8d1f72fbd3acbe56 | 9b13c1174588e693894bfae618623c1c0d5c6b52d154993444a111488ffae8d4 |

资格复用的完整独审分别为 u22ke-proof-review（KE/KF）0df8def6891e92ff229c59a3e0ff875092338559c629c0e9cc72bb23bf827143；u22kg-proof-review 43d0298ac94679e858d4c9c16668bd7e3f63aa4294b9aa0168492a275b44b6f0；u22kh-proof-review 82719e53df304d015a96aa88a5791a07108adfa65f0a86c2aaf06bd4e1d61b5c；u22ki-proof-review 14279f754a40a5bd13545aa11845848fdebe50a80a47cf8810cefaf168462197；u22kj-proof-review（KJ/KK）f6870771fca4d332e71c6b867c0e8db235896c19c087fc72aa3b8b186c005ed1；u22kl378-proof-review 9094cb89cf619503fcf0dbb9a7358b34690ab65cea451d573d4833cc38c47f99；u22km379-proof-review（KM/KN）4fba8b28328208d246023f26dcca1d74f20b3f2486b0839e59d0339ad10eefe8；u22ko381-proof-review 2d1ad9bf19f59d84680dab35f59deab3a164b4ddecd304c78602ebfb5de85ade；u22kp382-proof-review 4505e6b77b898173f76957c5bb300c0f43a6681e68bbc0371f6a1dc1a3d18d4f，合计 1111 LF。

其中最终 KP 的 qualification 为 d783a4eef83f57672d4cd2a12d9133b58b73095739e2cf40c1aa4d7448035b26；receipt 为 0b578001225395ce8636767af74ed1184a8b0d2db0d902db8fa3bfec41779742；首原对象为 1b761d4c96f3f05e88a13b06d140ff5bd346fdaa82e11d270199f34626a1f378 / 921880 B。本报告只复用上述对象证据，不声称自己观察了新的服务器运行或 Root 聚合结果。

此前冻结范围报告保持原字节：v146 B/C 报告 0a1cb2b7b56accae776f214e1911ca8a5cc8acd8c35275c606be3a200ac65449；v148 严格性报告 6f1ba1abd4cd5280d7eaafb1cc3bc47388ab978cf9773781e0d56c8a5d36f9ee；v149 小正参数报告 7a73e385417415ec2e40c321bc3ec3a993f9ba996907122d5e11e3c80d04fc4d。它们当时列出的实际鞍点/曲率/唯一性/应用缺口，是本次所检验的新义务，不被追改成当时已证明。

## 2. 原 D 要求的同一见证与实际量词

令八振幅为 a:Fin 8→ℝ，A=append(a,−a)，并令

\[
\mu=\frac1{16}\sum_{k=0}^{15}\delta_{A_k},\qquad W(X)=(X,X^2).
\]

KO 的实际声明 exists_symmetric_eight_atom_regular_unique_saddle_witness 与 KP 的 exists_symmetric_eight_atom_canonical_tail_expansion 均无调用者数学前提。它们先选同一 a，给出 a(0)=1、StrictMono a、全部 a_i>0 和 A 单射。于是十六点不同，每点质量确为 1/16；这是原 R2 允许的正且对称概率的一个具体存在性子类。概率归一化、恒等函数可积及其积分为零、正右半轴质量、某个 B>0 下 1≤|X|≤B 和 1≤X²≤B² 全部已输出。

关键量词顺序为

\[
\exists a\ [\text{上述同一 }\mu\text{ 的全部谱性质}]\quad
\exists\epsilon\in(0,1]\quad
\forall x\in(0,\epsilon)\ \exists a_x,\theta_x,L_x\quad
[\text{同律正则唯一鞍点、全尾间隙及最终渐近}].
\]

a 和 μ 不随 x、邻域大小 ρ、样本数 n 或频率重选。各 x 才选 a_x、θ_x、L_x；随后对每个 ρ>0 选 δ_{x,ρ}>0；渐近常数 C_x>0、N_x≥2 又在所有 n≥N_x 之前一次选定。gap 和展开是关于同一 a_x、θ_x 的合取，不能读成两个不同鞍点的分别存在。KP 源码只从 KO 取得一次 a/μ，从当前 x 的 hregular 取得一次 a0/θ/L，然后完整保留该对象的谱/几何/远区后缀再调用 JA342；没有独立的第二次存在性选择。

声明中的概率 proof-letI 是同一 a 上已证明的 IsProbabilityMeasure μ，不是隐藏调用者前提。源内 hprob 与声明中的 JD 投影证明同一个 Prop；其证明无关性不改变 μ、倾斜积分或 Legendre 率。现有 qualified 审查已经覆盖这个交互。本次没有发现要补导出巨型 raw AST 或重新审查旧实例的具体风险。

原 D 只需要这种存在性见证，不要求列出八个可数值核算的振幅。此前 JO/JP/JT 的同一次选择已经支付线性八元组和平方差七元组的 γ=3/16 丢番图条件；本批保留由它们导出的谱结论，不需要重新选择幅值。这里不将存在性命题扩大成整个八维参数空间上新的满测分类定理。

## 3. 谱严格性仍是同一个实际抛物线分布

KP 保留原律的真实联合特征函数 ψμ(ξ,η)，并输出：

\[
\forall u\ne0,\quad |\psi_\mu(u)|<1,\qquad
\exists c>0,\ R\ge0,\quad
|u|>R\Rightarrow|\psi_\mu(u)|\le1-c|u|^{-3/8}.
\]

指数满足 0<3/8<2/5。原文若要求 R 严格正，只须将现有 R≥0 增大到 R+1。该界是完整二维径向条件，包含两个坐标轴与斜方向；没有把两个分别的一维分布界代替联合 WC。真正联合非格点并非未经证明的“高频界也覆盖低频”断言：接受的旧生产者利用 |ψ(u₀)|=1 时所有原子相位一致，从而 |ψ(ku₀)|=1 对正整数 k 成立，再令 k 越过高频阈值与 WC 矛盾。

strong Cramér 的实际否定量词为：不存在 δ>0、R≥0，使所有 |u|>R 都有 |ψμ(u)|≤1−δ。KP 同时保留更具体的任意 R∈ℝ、ε>0 都有 ξ>R，满足 |ψμ(ξ,0)−1|<ε 和 |ψμ(ξ,0)|>1−ε。因此取 R=k、ε=1/k 即得逃向无穷的近一序列；概率特征函数模恒≤1，所以

\[
\limsup_{\|u\|\to\infty}|\psi_\mu(u)|=1.
\]

这正好否定原文的 limsup<1，而非仅否定某个预先指定的 δ 或某条有限频率测试。真正联合非格点与该近共振性质同时成立；“弱非格点”不能误读成定量 WC 的定义。

若还需与原 ICM 的 Fourier 可积性比较，此同一见证确实在该条件之外。有界 W 给 ψ 全局 Lipschitz，某个有限 L>0 满足 |ψ(u)−ψ(v)|≤L‖u−v‖。取上述近共振点的彼此分离子列，使各点模>3/4；固定半径 1/(4L) 的互不相交二维球内均有 |ψ|≥1/2。因此对任何有限 r>0，∫ℝ²|ψ(u)|^r du=∞。这也是已有有界性/近共振的直接语义后果，不是新假设；单独一条轴上无穷点本身并不足以推出二维积分发散，所用固定正半径球正好补足这一点。

每个固定紧参数集 K 上，KP 仍给一个 m_K>0 和同一 R，使所有 p∈K 的实际倾斜律满足

\[
\mu_p\ge m_K\mu,\qquad
1-|\psi_{\mu_p}(u)|^2\ge m_K^2(1-|\psi_\mu(u)|^2),\qquad
|\psi_{\mu_p}(u)|\le1-\frac{m_K^2c}{2}|u|^{-3/8}.
\]

这是同一基准 μ 的真实倾斜族，不是额外谱假设。最终 KP 先在紧单点 {θ_x} 取得该实际鞍点倾斜律的 WC，再合法调用有界稳定性接口构造邻域；没有把单点集当作具有非空内部的邻域。

## 4. 实际边界、驻点和整个尾域唯一性已经付清

使用同一 μ 的真实全域 EReal 率

\[
I(a,q)=\sup_{\theta\in\operatorname{dom}K}
\{\theta_1a+\theta_2q-K(\theta)\},\qquad
D_x=\{(a,q):q>0,\ a\ge x\sqrt q\}.
\]

这里 dom K 是指数函数实际可积的参数域。有限支撑给 dom K=ℝ²，分割函数为严格正的有限指数和；没有使用不可积积分总化为零。D_x 保留弱尾边界和严格 q>0；它并不是整个 ℝ² 中的闭集，证明没有把 q=0 偷纳入尾域。

PR532 已给出小正 x 下全尾率极小存在与全部低率竞争点向实际均值 (0,EμX²) 定位。KE371 将有限的全局极小点放到真实边界；KG373 接入实际倾斜均值，KF372 才在满足其完整前提后给驻点与严格符号。KM379 的公开输入只是有界、中心、正 AE 能量下界和正基准协方差行列式；KO 将同一十六点律的 lower=1、upper=B²、mean0 与 base det>0 全部传入。这些输入已经证明，并未把待证鞍点、正曲率或唯一性当作前提。

对每个 0<x<ε，所得 w_x=(a_x,a_x²/x²) 和 θ_x=(s_x,t_x) 满足

\[
a_x>0,\quad\theta_x\in\operatorname{int}(\operatorname{dom}K),\quad
\nabla K(\theta_x)=w_x,\quad
s_x=-\frac{2a_xt_x}{x^2},\quad s_x>0,\quad t_x<0.
\]

KK377 的唯一性是对每个 y∈D_x：

\[
I(y)\le I(w_x)\Longrightarrow y=w_x,
\qquad
I(w_x)\le I(y).
\]

不是仅图内、某个子水平集内或有限率竞争者内的唯一性。其数学衔接是：此前对整个低率子水平集的定位，使全部可能的最小点位于同一个均值图小邻域；KE 把它们放到边界；KJ 给 q↦I(x√q,q) 在该共同能量区间的严格正二阶导数。两个不同能量值的最小点将违反严格凸性；能量相同的边界点本来相同。KM 调用 KK 的这种完整唯一性，把它与另一个定位构造出的实际倾斜点识别为同一 w_x。没有由局部 Hessian 正定直接跳到全局唯一性的缺口。

KM/KO/KP 直接给的是唯一的实际率极小点。若把原文“唯一鞍点”还读成自然参数本身唯一，同一有限支撑律也满足：任何非零 b 的 b₁X+b₂X² 不可能在十六个不同 X 值上恒定，否则一个非零二次多项式有超过两个根。所有倾斜原子权重严格正，故每个实 θ 的 Covθ(W) 正定。于是 K 在整个 ℝ² 严格凸，梯度严格单调、单射；产生同一 w_x 的 θ 必须是 θ_x。这里也没有第二个未付的 dual-parameter 唯一性假设。

## 5. 原始切向曲率、协方差与速率身份

只证明 q↦I(x√q,q) 的能量曲率为正，并不自动等于 RP 的 a 坐标曲率。KL378/KM379 专门支付了这一步。设均值图上的实际光滑率为 J，实际逆参数为 P，q_*=EμX²。基点的能量方向 Hessian 为

\[
D^2J(0,q_*)[(0,1),(0,1)]
=\frac{q_*}{\det\operatorname{Cov}_\mu(W)}>0.
\]

正能量下界保证 q_*>0；分子是 Covμ(W) 的 00 元 VarμX=q_*，不是能量方差。KL 的共同邻域连续性给

\[
2P_2(w)+D^2J(w)[(x,2\sqrt q),(x,2\sqrt q)]>0
\]

对所需小 |x| 和靠近实际均值的 w 同时成立。KM 的全部最小点定位确保当前 w_x 真在这个共同邻域内，P(w_x)=θ_x。由边界 a_x=x√q_x，

\[
(x,2\sqrt{q_x})=x(1,2a_x/x^2).
\]

因此上述严格正量精确等于

\[
x^2\left\{\frac{2t_x}{x^2}
+v_x^{\mathsf T}\Delta_x^{-1}v_x\right\},\qquad
v_x=(1,2a_x/x^2),\quad \Delta_x=\operatorname{Cov}_{\mu_{\theta_x}}(W).
\]

x²>0 才允许除回，得到原始

\[
\Lambda_1(x)=\frac{2t_x}{x^2}+v_x^{\mathsf T}\Delta_x^{-1}v_x>0.
\]

这不是把一个缩放后的正系数改名。KM 输出的 L_x 正是实际 Δ_x 的行映射；KP 对其四个矩阵元逐项评价，利用实际 covariance 定义中 D10=D01，调用已接受 IX339，才把 L_x.symm 的 pair 二次式识别成上式 Matrix inverse 的 dotProduct。det Δ_x>0 保护逆矩阵，既没有转置错误，也没有把协方差与其逆混用。

在 RP 坐标 r=a−a_x、z=a²/x²−q 下，法向导数 F_z(0,0)=−t_x>0，F_r(0,0)=0，而 F_rr(0,0)=Λ₁(x)>0。因此原始边界 Laplace 所需的两个不同方向条件均已成立。

KP 还用真实 MGF 内部的 attained Legendre 接口与实际两个倾斜矩身份，得到

\[
I(w_x)=(J_0(x):\mathrm{EReal}),\qquad
J_0(x)=s_xa_x+t_xa_x^2/x^2
-\log\int e^{s_xu+t_xu^2}\,d\mu(u).
\]

此前保留的 0<I(w_x)<∞ 随即给 J₀(x)>0；这不是在无穷率上使用 totalized toReal=0。KO 为 KN 使用 toReal 时也先明确排除了 ±∞。原 D 所需真实率与局部实率已经识别。

正定性并无额外未付义务。Δ_x 是真实有限二阶矩 covariance，必半正定；det>0 使它正定。有限支撑还使 K 全域光滑，均值逆图存在。缩小到包含 θ_x 的一个紧参数邻域后，协方差连续且处处正定给统一 0<λ_-≤λ_+<∞；|X|≤B 给 W 和全部倾斜矩有界，结合统一逆协方差界给标准化变量的统一 8+δ 阶矩，例如 δ=1。居中白化后的均值零、协方差单位阵和 WC 指数不变由既有 v148/B-C 接口合法实例化。缺少一个把这些已证后果再次并列的名字，不是新的数学条件。

这里 a(0)=1 是支撑尺度约定，不是声称 VarμX=1。原 D 没有要求单位方差；现有 mean0、概率质量1与 VarμX≥1 已足够。即使另需单位方差，也可按 σ=(EμX²)^{1/2}>0 作正比例变换，尾比值 S_n/V_n 不变，联合频率经可逆对角变换，真正非格点、WC 指数和 strong 失败均保持；本次结论并不依赖这项额外包装。

## 6. 全尾域细远区的率间隙与实际概率估计

KN380 本身是一个条件辅助声明；它明列实际有限中心率和全尾唯一性。不能只读到 KN 就宣称同律远区已付。KO381 明确从同一 KM 鞍点给出其全部输入，并证明对每个 ρ>0 存在 δ_{x,ρ}>0，使所有

\[
y\in D_x\setminus U_{x,\rho},\qquad
U_{x,\rho}=\{|a-a_x|\le\rho,\ |a^2/x^2-q|\le\rho\}
\]

均满足 I(y)>J₀(x)+δ_{x,ρ}。最终域不受 carrier、chart、有限率或高能量截断限制；率为 +∞ 的点也包含。小正能量 0<q<1 的点虽不在实际有限支撑均值集内，仍由真实率为 +∞ 支付，未被从公开尾域删除。KN 使用紧子水平集、包含中心的严格内矩形与其闭补集取得统一间隙，避免了从逐点严格不等式无理由推出统一 δ。

率间隙与概率远区是两个义务。本次也核到了第二个：JA342→IZ341→canonical_actual_self_normalized_tail_laplace→actual_self_normalized_tail_laplace_of_unique_minimum，针对内部实际选定的同一个小 ρ，调用已接受 actual_exterior_exponential_bound_of_unique_minimum，输出

\[
\mu^{\otimes n}\{\overline W_n\in D_x\setminus U_{x,\rho}\}
\le C_E e^{-n(J_0(x)+\eta)},\qquad n\ge1,\quad \eta,C_E>0.
\]

该调用需要的 I(w_x)=J₀ 和完整真唯一性已由当前同律输出满足。所读承重源码中没有尚待调用者提供的 hFar、整平面指数紧性或另一个分布的 LDP 输入。该实际外域证明把低能量、高能量实际正尾分别以任意指定指数率控制，中间能量夹层紧化，以有限指数测试控制；然后与当前局部窗口概率作精确分拆。对当前有界律，已有 bounded_actual_exterior_exponential_bound_of_unique_minimum 还给同一结论的有界直接接口。

因此 RP 第 4 节的显式远区概率条件确实得到实例化。尤其没有将原较大 U 的外部估计仅靠单调性转到更小矩形：缩小 U 会扩大外部事件，不能那样转移；接受的尾接口为其自身选择的小矩形重新给出完整外部估计。这消除了“只有均值图外粗远区”或“只有紧 carrier 上 gap”的具体疑虑。

## 7. 固定小正参数的最终原事件与修正常数

KP382 最后的无条件存在性后缀，对同一 μ 和每个 0<x<ε，给出

\[
v_{\mathrm{corr}}(x)=(-t_x)\sqrt{\det\Delta_x}\sqrt{\Lambda_1(x)}>0
\]

以及 ∃C_x>0 ∃N_x≥2 ∀n≥N_x：

\[
\left|
\sqrt{2\pi n}\,e^{nJ_0(x)}
\mu^{\otimes n}\!\left\{\frac{S_n}{V_n}\ge x\sqrt n\right\}
-v_{\mathrm{corr}}(x)^{-1}
\right|\le\frac{C_x}{\sqrt n}.
\]

概率严格是原 μ 的 n 重独立产品；S_n=ΣX_i，V_n=(ΣX_i²)^{1/2}，没有把分母改成样本中心方差。源事件实际使用弱不等式 ≥，零能量时比值为0；x>0、n≥2 使零能量不属于正尾，且当前 μ 还有 |X|≥1 的已证 AE 下界。正能量事件与 \overline W_n∈D_x 精确等价，没有删掉离散边界原子或条件化概率。

Λ₀=J₀=I(w_x)；法向因子是 −t_x，切向因子是 √Λ₁，covariance 因子是 √det Δ_x。这与 R2 式(1)、RP 式(10)/(14) 的修正常数完全一致，没有改回 ICM 印刷常数，没有额外 x、2 或错误的 reciprocal。因 v_corr 对固定 x 严格正，缩放绝对误差也等价于相对主项 O(n^{-1/2})。不是一个子列或有限 n 检验。

JA342 是条件式一般定理，KP 没有将它直接称为无条件应用：其实际 μ/θ、内部性、det>0、x/a_x>0、t_x<0、实际均值身份、驻点式、原律 AE 有界、0<β=3/8<2/5、实际 θ 倾斜 WC、原始 Λ₁>0 和整尾唯一性均已逐项在同一 witness 上提供。故当前具体应用的这些条件已经消去；一般定理的其他潜在应用仍须各自满足其实际前提。

## 8. 承重旧接口与外部结果归属

本次定向读取并核对的旧源码保持以下 SHA256；路径前缀为 C:/game/shao lean/library/：

| 承重旧源码 | SHA256 |
| --- | --- |
| Shao/OQ3/BoundedCanonicalActualTailScaledExpansion.lean（JA342） | 0fd9a975807b524eaeb1b308dffae928f739e91785e05b744d4ee928a44583c1 |
| Shao/OQ3/CanonicalActualTailScaledExpansion.lean（IZ341） | f41f8f56d5db27b26b03fbd983ff9a352ac3c1fffa512c9959fb362bc0677798 |
| Shao/OQ3/CanonicalActualSelfNormalizedTail.lean | 9142fca892e49cbc44b4e39ac533bb47f5bc8baf0540c8b12a959a4d3886a447 |
| Shao/OQ3/ActualSelfNormalizedTailUniqueMinimum.lean | aacc6c97a4d4e46c16b314476e7155a710d5f642fb2755f8b041b75a4bc60eb7 |
| Shao/OQ3/ActualExteriorFromUniqueMinimum.lean | c970a34a6e5dd9839c526558f931b32d6e61eeafe80e767a385198d46a17a7ba |
| Shao/OQ3/BoundedActualExteriorFromUniqueMinimum.lean | f77a879d7e4b4f9b4a8ddb079db8b78bc0f3ef0243cbc6559f102ea6f2729455 |
| Shao/OQ3/CovarianceRowInverseQuadratic.lean（IX339） | 1b4ec8feaf3445d7f7fa2508f66cae0cfcb9bb20d05389787bb860ad61fd9836 |
| Shao/OQ3/OpenDomainLegendre.lean | 941c08552f300af2c85e2df7f55399b69c4468bca467fe88b8a303a6a3c74bc3 |
| Shao/OQ3/RegularCovariance.lean | 0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853 |
| Shao/Probability/BivariateLegendre.lean | d8bd5dc7099ffdbf52282ebb41ad03145a50b42547dec55bb42caacb31ed5f58 |
| Shao/Basic/FinitePath.lean | 898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb |

对这些接受结果复用原完整独审和收据，本次只核声明适用性、实际定义及上述源语义交互。尤其没有把某个局部任意输入率函数、自由 covariance 或抽象概率替代 I、Δ_x、μ^n。OpenDomainLegendre 等旧接受对象的历史 firstOriginal provenance 若原为 UNKNOWN/null，仍保持该限制，不因本次消费升级其来源。

原 RP 采用 Song (2020) Theorem 2.1、s=8 的 uniform-in-law weak-Cramér Edgeworth 输入；它明确替换了 R2 早先从 Angst–Poly 以对角论证推统一性的路线。阈值为 0<β<2/(8−3)=2/5；h=n^{-3}，曲边界小胞振荡 O(n^{-7/2})，每胞绝对误差 O(n^{-3})，O(n²) 胞总误差 O(n^{-1}e^{-nΛ₀})，再接边界 Laplace 的相对 O(n^{-1/2})。这些原来源归属及 p54 常数修复均保留，不能把本批见证组装称为新发现了 Song 的外部定理或它的最优阈值。

本批最终实际 TYPE 没有留下“假设 Song 定理/目标 Edgeworth 展开/目标远区付款”的自由前提；其接受 producer 链和标准 AX 证据按原范围复用。来源上调用外部数学成果，与形式化接口上尚有未实例化的 caller hypothesis 是不同问题。这里未发现后者；本次也不重新认证原外部论文、新颖性或历史优先权。

## 9. 最终接受范围与真正未声称的范围

| 原 D 所需事项 | 本次范围裁决 |
| --- | --- |
| 一个实际十六点对称抛物线分布、两类同时丢番图选择 | 已接受旧 JO/JP/JT/KA 见证，当前 KO/KP 保持同一 a/μ；CLOSED |
| 真正联合非格点、WC β=3/8、任意紧倾斜稳定性、strong Cramér 失败 | 当前实际 TYPE 原样保留且与原定义/极限量词一致；CLOSED |
| 中心/有界/正右质量/概率归一化及标准化谱矩义务 | 同律直接输出或由有限支撑和既有接受接口推出；CLOSED |
| 所有充分小正 x 的实际边界鞍点、驻点关系、s>0、t<0 | KE/KF/KG/KM→KO/KP；CLOSED |
| 整个原 D_x 的唯一全局率极小，而非局部唯一 | KK/KM→KO/KP；CLOSED |
| RP 原始切向 Λ₁>0、实际逆 covariance 与有限正率身份 | KL/KM/IX/attained Legendre→KP；CLOSED |
| 每个指定 ρ 的全尾域率间隙，以及实际所选小窗口外概率指数付款 | KN→KO/KP 加既有实际外域 producer，所有输入已实例化；CLOSED |
| 同一谱见证的固定小正 x 修正尾渐近 | KP382 无条件存在性实际 TYPE；CLOSED |

因此，对 R2/RP 原 D 的存在性严格性和最后“见证落在正则有界充分修复子类”的数学主张，本次没有剩余实质缺口。局部终审中将“原 D/full OQ3 的 Root 范围验收”列在其职责之外，不是说 KP 的实际输出还缺鞍点、远区或另一个同律存在证明；本报告正补这项来源蕴含判断。若 Root 将旧反例 A、已接受 B/C 和本次 D 合并为约定的 A–D 原范围，D 不再提供额外数学障碍。本报告没有重新审查 A，也不能单凭一个正面见证替代 A 的负面结论。

仍须保留以下精确边界：

1. 结论是 ∃同一 μ ∃ε>0 ∀固定 x∈(0,ε) ∃C_x,N_x ∀n≥N_x；不是 ∃C,N 对全部小 x 统一。特别 x=x_n↓0、x_n√n→∞ 的变化窗口，或整个 [a_n,1/2] 上的正面一致展开，没有由逐 x 量词得到。x=0、x=ε、β=2/5 和退化曲率端点均不在当前结论内。
2. 原 ICM 问删除 Fourier 可积性后的无条件 O(n^{-1/2}) 主张，由独立反例 A 回答；D 说明一种严格弱于 strong Cramér 的充分修复确有实际应用。若一个统一窗口删除条件的主张包含 A 的固定 x₀，固定 x₀ 的反例已经足以否定该主张：a_n↓0 使 x₀ 最终属于窗口。这不等于证明当前正面修复在变化窗口上一致。
3. B/C 仍是一种充分条件，不是对每个原题分布均自动成立的鞍点/谱/全局条件。当前有限支撑见证已付清它们；任意新分布特别是无界律，仍须按其真实前提实例化。不能把 D 的具体无条件存在性应用扩成“所有 genuinely nonlattice 律都有该展开”。
4. 不认证最弱条件、β<2/5 的最优性、所有历史旁支问题、跨不同律仅由粗数值界控制的统一模数、可数值列出的振幅或新颖性/优先权。上述未声称事项并不是原 D 这个存在性应用的待付条件。

本次仅写本数学报告，未执行 Lean/AX/SSH、编译、联网 API、发布或新增子上下文，未修改旧冻结报告或其他人的文件。规定配置为 gpt-6.1-sol/xhigh；actual_model、actual_effort、input_tokens、cached_input_tokens、output_tokens、reasoning_subset_tokens 均为 null，本界面未暴露可核实遥测。
