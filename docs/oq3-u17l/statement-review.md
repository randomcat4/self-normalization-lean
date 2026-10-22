# U17l GaussianBoundaryLaplaceMixture 独立声明／来源／静态 API 审查

STATUS: CORRECT

## 1. 冻结完整类型的独立盲译（先行持久化）

本节只读取scope的唯一完整Lean TYPE，先于scope说明、R1／primary来源及作者路线。无新DEF，无当前实现；不把同名经典公式视作已经形式化。

```lean
theorem gaussianBoundaryWeight_neg_laplace_mixture
    (kappa x : ℝ) (hk : 0 < kappa) (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ =>
      Real.exp (-((kappa ^ 2 / 2) * (1 + t ^ 2)) * x) / (1 + t ^ 2))
      (Set.Ioi 0) ∧
    gaussianBoundaryWeight kappa (-x) = (2 / Real.pi) *
      (∫ t : ℝ in Set.Ioi 0,
        Real.exp (-((kappa ^ 2 / 2) * (1 + t ^ 2)) * x) / (1 + t ^ 2))
```

任意实κ/x固定，显式要求κ>0和x≥0。令f(t)=exp(−[(κ²/2)(1+t²)]x)/(1+t²)，结论第一项是f在真实实数半轴Ioi0上的IntegrableOn（默认实测度须核Lebesgue），第二项是既有gaussianBoundaryWeight κ (−x)精确等于(2/π)乘该同一半轴真实积分。两个结论为一个公开合取target，不是两个节点。

此类型对x=0也要求真实可积与相等；此时指数为0、f=1/(1+t²)，须给真实π/2积分使右侧为1。κ严格正，x无需严格正；不可对x0取消√x或把全半轴上的常数1假当可积。

κ/x在t积分之前固定，指数衰减率为(κ²/2)(1+t²)>0，权重分母1+t²严格正。定义gaussianBoundaryWeight的真实闭域／密度仍需随后核对，尤其−x与负号／系数2/π和κ²/2。类型没有μ/J/hcont或原模型概率门，声明只作已定义Gaussian profile的经典正混合分析接口，不证明actual source原24/25的全间隙、无条件19、Phi字面CDF、hW、generalKL或根闭合。

此独立盲译已持久化；后续来源、实际API／可积数学与最后机械核验另附。

## 2. 独立最终裁定

STATUS: CORRECT

JUSTIFICATION: 冻结完整TYPE的常数、指数符号、半轴、κ/x正域和x0边界正确；从已接受真实Gaussian密度定义出发，现成可积／Gaussian半积分／受控参数微分／FTC与均值定理API足以支持一个不借新axiom或erfc导入的完整证明。真实55项目／2905库导入图和缓存核验无缺项。此票只批准声明，不提前验收未来实现。

第1节盲译检查点为1861字节／26行，SHA908db7722b1ba13364a5ec977c9b4fdd3bc03757fedf5ffd4148f4e0195cbb64；终稿仅更新行政状态并追加下文，第1节完整TYPE与翻译原文未改。作者gaussian-laplace-mixture-next-candidate.md、cusp-positive-mixture-next-notes.md及任何其他future/implementation笔记未读；candidate-cache metadata未读。

## 3. 原target、经典来源与未闭消费者

R1只读原件C:/game/shao/current/oq3/proofs/r1/report.md，SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662。411–421定义原负曲边g/F；448–455的负半轴函数为exp(ell x)乘2标准正态尾(κ√x)，其零点平方根尖点是后续正间隙承重对象。457–481的22/24精确ζ渐近与25统一正下界均尚未由本目标证明。

本模块原target→原25的负半轴正混合分析前置。消除义务→为实际gaussianBoundaryWeight κ(−x)给准确正指数核混合身份，先证明真实IntegrableOn并保留x0。直接consumer→后续格和与连续积分差的正性／统一h√h下界；K已经把真实阶段Gaussian事件接到这个密度weight。剩余→实格和／混合积分交换的真可和／可积门、校正后的指数率正性、统一参数余量、原24精确ζ或原25统一gap本身，另有hcont/U18a、无条件15/19、字面Phi/CDF、rotation/hW/generalKL及所有根。

已实际打开并核对[NIST DLMF 7.7.1](https://dlmf.nist.gov/7.7.E1)。该经典公式的实正轴形式，以z=κ√(x/2)代入，其右端正是(2/π)∫_{t>0}exp(−(κ²/2)(1+t²)x)/(1+t²)dt，Gaussian尾对应当前真实负曲边。κ>0、x>0给非负实z，满足原公式扇形域；x0在本票下文以实际π/2积分单独核，未仅凭复argument的零点约定。

DLMF用于经典来源和系数核对，不是本项目已形式化定理，不可据此新增axiom/import一个未经证明的erfc恒等式，也没有新颖性或最优性主张。下面给出的静态完整可行性核验从现有Gaussian真实积分API出发，不依赖该外部公式作证明前提。

## 4. 实际weight与真可积门

actual GaussianBoundaryConstant.lean20–22：gaussianBoundaryWeight κ d=∫_{−(z/κ)²≤d}exp(−z²/2)/√(2π) dz，是真实默认实Lebesgue积分。公开52–56的gaussianBoundaryWeight_eq_piecewise，在κ>0后给d≥0时1、d<0时(2/√(2π))∫_{κ√(−d)}∞exp(−z²/2) dz；该已接受证明保留真实高斯可积、闭两尾、Lebesgue零端点和反射门。

本scope右侧f_{κ,x}(t)=exp(−[(κ²/2)(1+t²)]x)/(1+t²)。对全部实t，1+t²>0；κ²/2>0、x≥0使指数≤0，所以0≤f≤g(t)=(1+t²)⁻¹，且‖f‖=f。连续分子／非零分母给真实可测性。

actual ImproperIntegrals.lean274–276给g对整个实轴真Integrable，故其Ioi0 restriction真Integrable。按actual Integrable.mono'的AEStronglyMeasurable与AE范数主控门，得到本目标f对Ioi0的真IntegrableOn，包括x0。不能以f≤1代替，因为Ioi0的Lebesgue质量无限，也不能因实积分总返回某实数就倒推可积。

x0时f=g；actual integral_Ioi_inv_one_add_sq在i=0给∫Ioi0g=π/2−arctan0=π/2，乘2/π得1。左端weight κ0由真实piecewise的d0分支为1。因此初读要求的x0既有真可积，也有精确常数，而非toReal∞被压成0。

## 5. 不借外部erfc公理的实际API证明可行性

以下是独立核验的可落实论证，不是已存在的L实现；作者仍须在后续实际proof中逐门完成。

令参数b∈ℝ，ν=volume.restrict(Ioi0)，K(b,t)=exp(−(b²/2)(1+t²))/(1+t²)，以及

F(b)=(2/π)∫K(b,t)dν，
H(b)=(2/√(2π))∫_{z>b}exp(−z²/2)dz。

所有b（甚至负b）的K都被同一个真可积g(t)支配，因为b²≥0。K在t和b分别真实连续，且分母全t非零。因此每个K(b,·)真Integrable(ν)，过滤器DCT在b→任意b₀时的四门均有：eventual AEStronglyMeasurable、共同g范数界、g真Integrable、AE逐点连续。实nhds过滤器有可数基。这给F在0的真实连续性（也给全实连续性），不能用缺失主控的导数替代该步骤。

固定b₀>0，选参数邻域s=ball b₀ (b₀/2)，在积分变量t外统一选定。a∈s时b₀/2<a<3b₀/2；逐点实微分及正分母消去给

∂_a K(a,t)=−a·exp(−(a²/2)(1+t²))。

其范数为a exp(−(a²/2)(1+t²))，对全部a∈s、全部t有共同界

(3b₀/2)·exp(−(b₀²/8)t²)。

这是因为a≥b₀/2、a≤3b₀/2、t²≥0，并可丢掉额外exp(−a²/2)≤1。该Gaussian主控的参数b₀²/8严格正，所以由实际integrable_exp_neg_mul_sq真Integrable，并可限制到ν。所有导函数在t的可测性及参数邻域内的真实HasDerivAt由指数／多项式／非零常分母的链式法则成立。

actual hasDerivAt_integral_of_dominated_loc_of_deriv_le恰要求：s∈nhds b₀、eventual核可测、K(b₀)真可积、F'(b₀,·)可测、AE t后∀a∈s的共同导数范数界、主控可积、AE t后∀a∈s的真实HasDerivAt。上述是统一邻域和主控，完全符合其量词；API同时返回导函数真Integrable及积分的真实HasDerivAt。

在b>0处，实际Gaussian半积分（rate=b²/2>0）给

F'(b)=−(2b/π)exp(−b²/2)·[√(π/(b²/2))/2]
      =−(2/√(2π))exp(−b²/2)。

化简使用b>0、pi>0，所以√(b²)=b，涉及b的消去不在b0处进行。actual integral_gaussian_Ioi的公开类型虽对非正rate也给总化等式，其实现有非可积的undef分支；本次导数计算始终rate>0，必须明确同时给实际Gaussian可积，不可借该总化分支。

H的积分核exp(−z²/2)对全实轴真可积且连续。actual integral_Ioi_sub_Ioi'在真实两条尾IntegrableOn之后，将H(b)写成H(0)减(2/√(2π))乘有限primitive∫0..b；actual integral_hasDerivAt_right在IntervalIntegrable、局部强可测与连续门下给

H'(b)=−(2/√(2π))exp(−b²/2)。

同时H在0真实连续。F(0)=1由实际半轴反正切积分；H(0)=1由固定rate1/2>0的实际Gaussian半积分和√(2π)>0，故没有在b=0去除√b。

于是F−H在开放连通Ioi0上真实可微且deriv=0。actual IsOpen.is_const_of_deriv_eq_zero消费IsOpen、IsPreconnected、DifferentiableOn和EqOn(deriv,0)，给该开半轴上常值。0不在Ioi0内，不能把它冒作此API的基点：必须另用F/H在0的连续性、0属于Ioi0闭包（或一条正数趋0序列），把常值识别成F0−H0=0。故F=H于b≥0。

此证明不声称F在0可微；事实上零点的参数对称性会产生尖点，局部Gaussian导数主控不能在b₀=0按同式建立。scope并未要求这个错误前提，类型保留x0仍数学正确。

最后给定κ>0、x>0取b=κ√x>0。真实piecewise令d=−x<0，左端就是H(b)。b²=κ²x用sq_sqrt(hx)真实成立，右侧K指数可按ring精确化为scope的−((κ²/2)(1+t²))*x。x0使用第4节直接归一化，故得到冻结全部x≥0的目标。系数2/π、指数κ²/2、半轴Ioi0和weight的负位移均一一匹配。

此路线无需对二维实积分作无前提Fubini，也不需要新erfc缓存。若未来作者改走Fubini/Tonelli路线，仍需另审其真实非负／联合可积／转实门；本声明批准不预批那条尚未实现路线。

## 6. 实际主API类型／实现与边界核对

已在固定server只读下读完整相关类型及主要证明语义：

- ImproperIntegrals274–289：g真Integrable，Ioi i积分=π/2−arctan i；证明以真实可积和arctan导数／无穷远极限承重。
- GaussianIntegral115–120：正rate Gaussian真可积及Ioi0可积当且仅当rate正；289–301为实际半Gaussian积分，明确非正rate时是undef分支，本次不用该分支。
- ParametricIntegral284–302：上述邻域在AE积分变量之外、∀a∈s的统一可积导数界、真实HasDerivAt及核可测／可积门；其证明先转邻域Lipschitz主控，不是形式交换未界导数。
- Integral/IntervalIntegral/Basic1172–1180：尾积分差等于有限区间积分，真实两条IntegrableOn门必须先给。
- FundThmCalculus725–728：integral_hasDerivAt_right需要真实IntervalIntegrable、StronglyMeasurableAtFilter和ContinuousAt；931–939给连续primitive的可微性，不能仅凭文件名声称有自动导数。
- MeanValue767–771：开放preconnected集合上deriv0常值，参数点必须在该集合内。边界0的值按上节单独由连续性确定。
- DominatedConvergence68–75：过滤器DCT的eventual measurable/bound、主控Integrable、AE点态Tendsto及可数基门，在ν restricted measure场景全部明确。
- Function/L1Space/Integrable104–106：Integrable.mono'真实要求候选AEStronglyMeasurable及AE范数≤真可积实主控。

K的真实Gaussian事件↔density profile身份与原20已完整独立接受，但本L类型只消费实际gaussianBoundaryWeight定义与既有piecewise API，不调用K/相关模块中的private辅助，不把待生产hcont当本证明输入。

κ0被类型严格排除；x0、t趋∞及t0边界保留。1+t²全实正；(κ²/2)(1+t²)是严格正指数率，混合权(2/π)/(1+t²)非负且半轴总质量1。这些是标准分析含义，当前target没有另导出概率measure实例、完全单调性或实格和可和定理。

## 7. 真实来源范围与不提前闭合原25

原负半轴源函数还乘exp(ell x)；未来消费本混合身份后指数率会变成(κ²/2)(1+t²)−ell。要保证正率须真实κ²/2>ell（K阶段门可提供），而制服参数、求和积分交换及梯形正间隙仍要另证。不能因本目标的未倾斜weight核率正，就宣称所有未来ell的校正混合也正。

本票没有原24的精确ζ(−1/2)系数或原25的统一h√h下界；没有省略混合后的真实Summable／联合Integrable门。未将经典DLMF恒等式当新定理发现。原根A/B/C/D、hcont/U18a、无条件15/19、Phi字面CDF、cusp/rotation/hW/generalKL均保持OPEN。

## 8. 数学审查之后的实际闭包／公开可达／pins／缓存

拟唯一Shao导入为SourceGaussianBoundaryProfile，另三个显式Mathlib导入是Calculus.ParametricIntegral、Calculus.MeanValue、Integral.IntervalIntegral.FundThmCalculus；namespace/open/scoped Topology Interval/noncomputable上下文与scope完整TYPE相容。没有公开DEF，唯一合取target不另拆节点。

本地scope59与run scope.md均SHAa33ee77ea57ce02a2a16002e6b43dc8c3498c5689793e308e0bd1d61381b5bd1，5186字节／28行；两端GaussianBoundaryLaplaceMixture.lean均不存在，未读或宣称本target的receipt/build/Audit通过。

独立从实际imports词法剥嵌套注释／行注释／字符串递归，按module/public import与旧非module规则核公开图。实际55份Shao、2905份Mathlib源和现成olean均齐；55源对已冻结K的54前置加K本源逐hash核missing0/extra0/hashdiff0。未读取作者candidate-cache metadata，不下载或编译任何cache。

主要实际公开路径：GaussianBoundaryConstant经SourceGaussianBoundaryProfile导出其真实定义／piecewise，再导出ImproperIntegrals和GaussianIntegral；ParametricIntegral／MeanValue／FTC是本scope显式公共库导入；DCT和IntervalIntegral.Basic经ParametricIntegral公开可达；Integrable比较经ImproperIntegrals→JapaneseBracket→L1Space.Integrable公开可达。Lebesgue.Basic实例亦实际公开可见，所有IntegrableOn／setIntegral默认体积是同一真实实Lebesgue测度。

实际图不包含未来Levy/Portmanteau/Tannery；不因U18a那批51缺项等待或补写缓存。初始侦察数字与本次独立实际核验一致，但本票未把侦察metadata当证据。

2026-10-22T08:58:50.640940+00:00只读观察branch feat/oq3-gaussian-laplace-mixture，HEAD5ffdc89842f49c86102f2bcfb0826589de86f43e（K正常发布），worktree clean。K真实源22df4806e0179c5dc1ea70f759895bdd6a8610ae1f212c3e16b38d0bf6282515，7703字节／164行；GaussianBoundaryConstant c44d13d42da6711f9eec44313fb27b363513b7e75aeb83c1df79708157e65f5a，12700字节／282行，均与本地冻结字节一致。

lean-toolchain实际SHAd581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4，29字节／1行，固定leanprover/lean4:v4.36.0-rc1；lake-manifest.json SHA40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e，3541字节／117行；Mathlib HEAD807d3836b165983210ee2ecf3cd28f239436949c。

55路径→SHA按键排序紧凑JSON指纹c5e9824e79c69550d99fe0f093e19f12e85a4c0fbd7ce1fa031b0a5c18e7bb55。完整独立冻结绑定如下（未另写共享清单）：

```text
Shao/Basic/FinitePath.lean 898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb
Shao/OQ3/AtomProjection.lean 0d369052c7f87122765612efdeaca5d9ac71abca861e7785c86d1f9edcc74d22
Shao/OQ3/AtomicMeasure.lean 59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39
Shao/OQ3/AtomicProductControl.lean 6f886635f2201e04d1004a4f4b3b4058d406be3a283f716b70f1ce1cfaa5775f
Shao/OQ3/AtomicTailControl.lean ec528d9af8b475f1db8a78c93ab917d754365d280027a86be2823825b19c2f79
Shao/OQ3/BinaryEntropyBounds.lean 291cc2afc5e632ad8326b5d98ceb619b959a41bc8d49120d2a52bd1a0b213228
Shao/OQ3/CenteredLogMGF.lean 1fb9f7b4ca976c02f5f100161da811738a443d75c47c72c2e274de54d9fb90f4
Shao/OQ3/CenteredSampleTilt.lean d042af2e3ab2f38bb94b67dc53d28d335c1370fcecd8100e93a067d9ba067501
Shao/OQ3/CentralFourierIntegral.lean 4999d8148c1ee1ba50f61d6d19c40aed239cd001d76ee71f133d1a064c668a93
Shao/OQ3/CharacteristicMeasureDomination.lean ec7032919bd8d825bb8746da15e84b29c5cb59ef97858367e4d73fdf52aa9bbb
Shao/OQ3/CompactTiltDomination.lean 6f31ac2e3b2b9d9b2ef957ebe52cfe3664a86694bb396b09c1006b890cbd0623
Shao/OQ3/CompactTiltLayerMassBound.lean 5602fd17ebac0fe40fb789067cea6b9553659dad4c8965ff88aea7e106ef5cc7
Shao/OQ3/CorrectedScaleContinuity.lean b0391976b809b37b1d0d3cb591c2fc89c9291538e8bc9193db70dd2b1504a2a8
Shao/OQ3/EnergyBernoulliMGF.lean e3bb038b2b92fac9a5341b26d437eeba046a5fd954a753fe80a7058ce32432ad
Shao/OQ3/FarEnergyExponentialCover.lean 40ee1824e49f2bf38e653edfa38363774e27a7d58c3c9e1c2b97245cfc86803d
Shao/OQ3/FiniteConstraints.lean 800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0
Shao/OQ3/FiniteFarArc.lean 3a0b05d0789e53320009a44499c9c40d0fb3d892427085052c65c04456b6cf71
Shao/OQ3/FiniteNormalSpan.lean 0374da4860edf8af8bbbb9172e4e93bfe9b6c37ac57672b85a4f58392475b7de
Shao/OQ3/FiniteStageMeasure.lean 1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1
Shao/OQ3/FundamentalFourierAsymptotic.lean aab18e9f073a18a87d42f0edd3e37a95da58cacf5b9635e4a64c887d340765b1
Shao/OQ3/GaussianBoundaryConstant.lean c44d13d42da6711f9eec44313fb27b363513b7e75aeb83c1df79708157e65f5a
Shao/OQ3/GlobalNegativeLayerBound.lean 57b61e6e3bfd184586083e55633a563e4176cbfcf16def62a7d860d92b5c01d8
Shao/OQ3/InverseTilt.lean c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811
Shao/OQ3/JointNonlattice.lean 51ce939232610353215fc3b7377e19b894451a9a108125e1828bf2fe8ec81559
Shao/OQ3/LocalNegativeLayerControl.lean e94a5a8e82d2a69a946a12e16f3fb2a58b174fb036becce5632d7c600b796f01
Shao/OQ3/LocalNegativeLayerTail.lean 049361c77716896922fb1d7cd3e6abf84515b76a99103c597d8d74b63a2f1856
Shao/OQ3/LocalRateMargin.lean 5e0e4f9ebb0dc514e0b55b9ed3aa7e5a9e8b9c128fdda2edfd2257bc3ad70a77
Shao/OQ3/NegativeLayerGeometricTail.lean 8077cfb97547c4a8c5b22da6ed17a58168a6ca1f6b2654f6799292a06a8b23f4
Shao/OQ3/NormalLayerConditionalLaw.lean 94e2507a83dfc232280043567f6a2f07950d39da10b45699777ac1316f24281a
Shao/OQ3/NormalLayerFourier.lean 063b6c5ce50e6c5ee33b53301cdfcd36a63a4ea06f9c3de729756513ca736fa3
Shao/OQ3/NormalLayerMassBound.lean 66ff4f217b57b319abb19ea7982e467e934219fadc2574a3487087e030a9e4f1
Shao/OQ3/NormalTangentDomination.lean b65b9f5a9d67e42e611a3841563ac07004e796415c3e5b74f177a8ca80e48e90
Shao/OQ3/NormalTangentGaussian.lean d2c55bf4d7a371c9b43cd3c75eab8ece8b3c7caa21aa4827bf19c24b4c7cac39
Shao/OQ3/NormalTangentMoments.lean 8cee48bc8f519f72b218a2ef80685d946a6debaea8b723af38a49c5bdca12cc1
Shao/OQ3/NormalTangentPowerLimit.lean 819bd0e801eb0b9adce0fbdbcd6ced6441b04787eb0501b811721933db0e9457
Shao/OQ3/NormalTrialCost.lean 8fb184ac4cf75e4f1c64e615b5c94c1a5f16c39109709a8f5dbc7fe2c5406895
Shao/OQ3/PositiveLayerTail.lean ebcef2d9ada2df9973a16ab8f1c9806c304dbaf1d01731c9de5ffcfd9d12172a
Shao/OQ3/PositiveRate.lean 8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b
Shao/OQ3/ProductMeasureDomination.lean 9f05af79e47b9f778cbce7a0d19c0addea6d457eab5f088a69bf372f660c5a3f
Shao/OQ3/RegularCovariance.lean 0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853
Shao/OQ3/ResonanceArithmetic.lean cd21a264d637bab30fed765bdc25ed09bb4ff56f6efb9c88ee09be4ca6e1648b
Shao/OQ3/SampleBoundary.lean 7660e23b71ce28ab43a4ad1d8df1862cf8a507b6bb9b41255e961f0bee0b93e2
Shao/OQ3/SampleChangeOfMeasure.lean d6259e330afca7b95e2e206c7021a44836e32cc0add596d14a6af8bdbda25134
Shao/OQ3/SourceBinaryEntropyGap.lean f5696cc1c953b3079f0c2987a239b3d0c0003292bb3018052c80d4f1fa9254c9
Shao/OQ3/SourceEnergyGeometry.lean 3cad1d1f12583690a6acbffc749110ace2b2786831f706049583cb755ac2253a
Shao/OQ3/SourceFarWeightedTail.lean c9e4c14af297353c5358da6d3e75d72f712649e535102ba18297fc00a0e5261f
Shao/OQ3/SourceGaussianBoundaryProfile.lean 22df4806e0179c5dc1ea70f759895bdd6a8610ae1f212c3e16b38d0bf6282515
Shao/OQ3/SourceStarter.lean 0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d
Shao/OQ3/StageCurvedLayerLimit.lean 71c85b128101af074034f454f40d25405b6898624989d464a69a73cc19db4d60
Shao/OQ3/StageLayerDecomposition.lean b6204bbbc39d029e221e473c76e8ebe34a42cf4765f4c3f7ccbd657d6311a8de
Shao/OQ3/StageLayerSeriesLimit.lean 4c797f9f5f9b47c0f62764c0b62396b9679172782d144fca29a091b83a52e02d
Shao/OQ3/StageSourceNegativeTail.lean 8b2e2eee60a9725e02653b58741cd63ba497fd5e5c5baaa0dca228fbda3ea8a0
Shao/OQ3/SummableAtoms.lean 0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b
Shao/OQ3/TiltedMeasureDomination.lean 5445a68da1ac8302f174bfe2144eb8271a0af740fd6b91a87355abb41fed739b
Shao/Probability/FiniteIID.lean d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b
```

主要实际Mathlib源码SHA（相对Mathlib/）：

```text
Analysis/SpecialFunctions/ImproperIntegrals.lean 1527f79047df49f816995ad879a8cfa9e6655f8c8a2c1e0342bf780890a894e7
Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean 4378f161cf5d482be77941cc9aea0195d2e83fe54eeb51b2ab33db1a318ccb9c
Analysis/Calculus/ParametricIntegral.lean f0a3c1e155e36b41a4f8ac6cf7adc2a9116e88177726d214e75ab1ad79559739
Analysis/Calculus/MeanValue.lean 0f10e5afeb80809192b023486b09e98939d0a6bd0920ab3882bddb41a715d947
MeasureTheory/Integral/IntervalIntegral/Basic.lean bf8558a4cb789e3505cfb08a6712ce83017719be2523e862d5e52f082433814c
MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean 85ca810c4adc1236fa7d057ff48cf7ae69d2bacf1ac2413b02ba9ac530de1e0b
MeasureTheory/Integral/DominatedConvergence.lean 56394aacfe591230d26a1d93641f2a1d3e3a3eae4fcfe772775533a1da295833
MeasureTheory/Function/L1Space/Integrable.lean d80e3495465030c1accca450935e4bfafcfe31d9b695e17f23ee9cfcea537759
MeasureTheory/Measure/Lebesgue/Basic.lean 4955d3400a03ba9d525206fcf1cff8592497dfff06674ca13d68d3bdcabb964d
```

## 9. 最终边界与批准

未发现需修复的完整TYPE／来源／静态环境缺口。实现者必须真实证明Cauchy主控可积、参数邻域外置的Gaussian导数主控和主API全部门、两边实际HasDerivAt、正半轴常值后向0的连续延拓，以及x0精确归一化；声明门不提前验收这些未来证明体或公理audit。

仅写本新票及授权run副本；未改任何source/scope/receipt/旧票/shared或撤销他人修改，未spawn/commit/pub，未运行Lean/#check/probe/build/rebuild、未写cache或复制完整原始日志。所有实际远端项目命令taskset -c 14-17，只读；未用ulimit-v，未触外部CPU0–9/80GiB任务或全局资源。primary网页读取仅为经典公式来源核对。

FINAL STATUS: CORRECT
FINAL JUSTIFICATION: 冻结κ>0/x≥0的实际Gaussian负曲边与(2/π)正Laplace核混合恒等式，包括真IntegrableOn与x0，数学常数／符号／边界正确。存在满足全部真实主控／可积／可测／导数门的现成固定API证明路线，无需新axiom、erfc库或cache；55项目／2905库真实闭包和公开图／pins核验一致。批准声明实施，不关闭原24/25、hcont或任何根。


## 10. 容量中断恢复与补充公开图核验：平方根导数

恢复先只读确认本地前220行完整终稿存在，SHA d58284ad37ebee1523c862f1114d673bea0eafd1b245308b8ead243989cb4b2a，22579字节；远端statement-review.md当时不存在。本节只追加，不覆盖该完整检查点或第1节盲译历史，亦未创建新代理／改变模型或复跑成功证明。

根据lead新增明确检查项，独立读取实际Mathlib/Analysis/SpecialFunctions/Sqrt.lean68–69，真实API为：

```lean
Real.hasDerivAt_sqrt {x : ℝ} (hx : x ≠ 0) :
  HasDerivAt (Real.sqrt ·) (1 / (2 * Real.sqrt x)) x
```

实际该模块SHA38c916b763ade8ed7174488bad31aee40735d03877a1bf9e540c1cf0107ec1ab，源码／现成olean存在。它处于当前四imports的物理依赖闭包，但在按module/public import递归的公开图中不可达。因此不能以其缓存存在就声称当前scope可直接调用Real.hasDerivAt_sqrt。这是公开可见性事实，不是缺cache或target数学错误。

本票第5节的完整可行路线只对独立参数b的多项式b²核求导，完成所有b≥0的F(b)=H(b)以后才代b=κ√x；最后只需公开基础Real.sqrt的值／平方／正性恒等式。它没有对x↦κ√x求导，不消费Real.hasDerivAt_sqrt，所以当前冻结imports下此路线仍完整，声明／环境裁定维持CORRECT。

若未来实现选择在x变量上对κ√x直接求导，并消费这个具体API，则当前导入不足；最小显式环境修复是新增import Mathlib.Analysis.SpecialFunctions.Sqrt。那是该证明路线的public可见性修复，不是增删target数学假设，也不需下载cache。此票不授权静默修改scope；应透明冻结该显式import版本后核相应环境门，或采用本票已核不依赖该API的b参数路线。

本次未改scope／source／旧票或其他文件，未读作者u17l-implementation-notes.md，未运行Lean/probe或写cache。补充实际检查仍为CPU14–17只读。

FINAL STATUS: CORRECT
FINAL JUSTIFICATION: 原完整220行数学／source／API证据保持；补充确认平方根导数当前不公开可达，但本票逐门核验的独立b参数证明不需要它。原冻结target在现有imports下数学及静态环境正确；对依赖sqrt导数的替代路线已明确最小显式环境修复，不将该API误记为可见或已编译。本票仍不关闭原24/25、hcont或任何根。
