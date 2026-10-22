# U16i 独立声明、来源与静态接口审查

STATUS: CORRECT

唯一lease1，仅拥有本新报告和remote run/statement-review.md；不独占代码库，保留他人编辑。不改source/scope/receipt/旧票/shared/cache，不spawn、Lean/probe/build/commit或下载raw完整日志。第一阶段先只取冻结Lean fence唯一完整type独立盲译并持久化，当时未读scope正文/作者路线/本次actual前置。初次保存2523字节，SHA256 83ca84010cf9f525dcad2812bd6f9d9c323c721cab7460c5a9c9f8e870e5b99c；随后按下列阶段完成审查。未读后续J/energy笔记。

## 第一阶段：唯一完整type盲译，先落盘

输入forty-fifth-unit-scope.md，SHA256 `663973e1fe281e96f7480adc972ef525aa0d09bed43bc6aae32bcc1031407f80`；零公开定义、一个public theorem `exists_local_negative_layer_tail_bound`。

固定同一真实概率mu、自然J、实q/a/ell；mu-AE |x|≤4+sqrt(10)，q>0、ell≥0；同mu真实normalValue均值=q和真实x均值=a；actual normalVariance>0和actual parabolaCovariance.det>0；ell严格小于q/(32*actual transverseVariance mu)。mu-AE支持于真实Fin4⊕FinJ的stageAtom(addedAtom j.val)像，所有该活跃singleton的mu.real质量严格正。T=transverseVariance实际符号与数学意义须后核，不能先凭名字视为标准差。

在全部这些固定数据之后，存在同一delta/gamma/c/C四个严格正实数；之后Nat atTop最终所有n；之后对全部非负实k/r，同时若k/n≤delta、r/n≤delta且n*q*k/16≤r²，则sqrt(n)*exp(ell*k)乘真实原mu的n重产品.real事件质量≤C*exp(−gamma*k−c*r²/n)。事件恰normalDeviation q z=−k且r≤|∑z_i−n*a|；不是一般a下的tangentDeviation a，也未要求路径上实际偏差R/n≤delta。

量词必须是同一四常数和同一N先于全部k/r，而非逐k/r试验产生N；k/r不是整数，含0，J可0，n0不要求最终包含且不能非法除。局部条件只控制试验位置(k/n,r/n)，事件内R可任意远。ell=0保留，严格hgap应提供gamma>0的余量。真实概率/可测事件/ENNReal有限转real及sqrt/exp各因子均需实际核。

独立初判：若actual显式trial cost有给定曲尾约束下的正weight margin，真实iid事件比较与compact tilted层质量可合成目标；关键先证明z=±r/n的trial tangent系数符号，不能凭尾方向猜测。可望缩delta，使曲约束及k/n小推出|b|k≤r/2而不除k/r/b；此后事件内远R的线性下界有效。两侧事件合并在r0重叠也只需union上界。以上均待actual定义/库/统一参数与全边界核后才可裁决；当前先保存，根A/B/C/D、完整19/LLT/hW/global gap仍OPEN。

## 第二阶段：冻结类型、来源和真实承重接口

本地forty-fifth-unit-scope.md与真实remote run/scope.md实际SHA都为 `663973e1fe281e96f7480adc972ef525aa0d09bed43bc6aae32bcc1031407f80`。唯一完整type的全部真实基准门、实k/r、严格四正常数和最终n在全k/r外的量词保持；零定义。scope数学路线作为待核候选，不能视作已经证明。

真实只读R1 `C:/game/shao/current/oq3/proofs/r1/report.md` SHA `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，实际读350–389。350–365是中心二元指数倾斜和两侧事件比较；368–383为局部二次率及曲约束下weight margin；386–389给源(17)并另提出邻域外global gap。当前类型以真实显式trial cost和已接受局部余量给一个充分局部概率界，不声称trial cost=Legendre上确界、源(16)最优inf公式或邻域外global strict gap。

实际E `NormalTrialCost.lean` SHA `8fb184ac4cf75e4f1c64e615b5c94c1a5f16c39109709a8f5dbc7fe2c5406895` 的完整两定义及两个public type均读到。S=normalVariance(mu)>0，T=transverseVariance(mu)=det(parabolaCovariance)/S>0，b=Cov_mu(normalValue,id)/S；actual trial(y,z)=(y/S−b*(z−by)/T,(z−by)/T)，actual cost=v*y+s*z−actual centeredNormalLogMGF(mu,q,a,v,s)。T是τ²而非τ，因此hgap恰q/(32τ²)>ell，对应源κ²/2>ell，不漏平方或32系数。

actual E `exists_normalTrialCost_weight_margin` 在本类型同hb/q/a/ell、真实均值、正S/det和严格gap下，给共同delta0/gamma/c>0；对全部n≥1、k≥0、任意有符号实r'，只要k/n≤delta0、|r'|/n≤delta0、nqk/16≤(r')²，即有 gamma*k+c*(r')²/n≤n*actualCost(−k/n,r'/n)−ell*k。它确实同时覆盖r'=r及r'=−r，共用同gamma/c；没有额外Legendre、概率Chernoff或global producer前提。本次不重复旧proof，仅核已完整接受的实际接口/定义及消费门。

actual G `CompactTiltLayerMassBound.lean` SHA `5602fd17ebac0fe40fb789067cea6b9553659dad4c8965ff88aea7e106ef5cc7` 的完整public type恰给固定基准/有限stage上compact二次tilt族共同C0>0和eventualN，之后全部p∈K和全部实层d；不会把k误限整数。actual H `CenteredSampleTilt.lean` SHA `d042af2e3ab2f38bb94b67dc53d28d335c1370fcecd8100e93a067d9ba067501` 三个完整public type实际读过：真实sample exp可积/normalizer乘积/产品倾斜measure等式、真实中心投影tilt=quadratic tilt、明确可测E/hlower下的实际概率指数比较。H已完整独立接受终票 `7a2319b4d0d29e43a6a76d1d71bcc461f8611a7adc4b62ef1210272f0bd950ad`，G已接受终票 `95287e3a48acb54ae21d7abd3ad52657d78ad28f3c1eb84d0897f61e2eef4b18`；不把作者未来路线替代其实际语义。

## 第三阶段：共同局部半径与真实trial符号

以E选出的delta0/gamma/c为固定数据；S/T>0来自hS及hD/hS，b是同mu真实Cov(Y,X)/S，有任意实符号。hb和已接受协方差基座保证真实多项式L²及covariance语义，而不是无可积variance总化。选delta=min(delta0,min(1,q/(64*(b²+1))))>0。分母b²+1>0且q>0，故正性真实；delta≤delta0、delta≤1和delta≤q/(64*(b²+1))在全部n/k/r之前固定，不假设b≥0。

固定后续n≥1与允许k/r，n实值>0。k/n≤delta⇒k≤delta*n。因为k≥0、n>0，

`b²*k² ≤ b²*delta*n*k ≤ (q/64)*n*k = (n*q*k/16)/4 ≤ r²/4`。

中间b²*delta≤q/64来自64*(b²+1)*delta≤q和delta≥0；没有除b/k/r。两端平方的底数|b|k及r/2都非负，故|b|k≤r/2。该推导包含k0/r0/b0，不能把r>0/k>0作为隐藏门；r0时曲约束在q>0/n>0下还迫使k0，但证明不必为此除k。

令y=−k/n、z+=r/n、z−=−r/n，(v±,s±)=actual normalTrialTilt(mu,y,z±)。T>0且n>0，逐定义真实化简为s+=(r+b*k)/(n*T)、s−=(−r+b*k)/(n*T)。由−r/2≤b*k≤r/2得到s+≥0、s−≤0，r0两者可为0，非严格sign已足够。先取得该sign门才允许尾部点态比较，不能只根据“正尾/负尾”命名猜系数符号。

注意局部条件只给trial y/z±位置，未限制事件内实际R/n。因为sign已经真实证明，对所有R≥r有s+*R≥s+*r，对所有R≤−r有s−*R≥s−*(−r)，不论R多远。故不需要且不能额外加事件内|R|≤delta*n；正是这一线性比较让冻结目标的远事件版本可成立。

## 第四阶段：compact参数集和共同C/N

取固定Q=Icc(−1,1)×Icc(−1,1)，定义实际参数映射 F(y,z)=(8*v(y,z)+s(y,z),−v(y,z))，其中(v,s)=normalTrialTilt(mu,y,z)。actual定义只是固定S/T/b的连续线性/除常数运算，故F真实连续；S/T正也保证清分母时非零。Q真实compact，K=F''Q真实compact。没有试图跨模块调用E的private trial_parameter_bound，也不需要逐trial重新造紧集。

该K在n/k/r之前选择，甚至可以在delta缩小之前以整个Q选择。delta≤1和n>0、k/r≥0保证(y,z±)∈Q；两个quadratic参数p±=F(y,z±)因此属于同一个K。此时对本类型保留的同mu hb/真实均值/hS/hD/hrange/hpos调用actual G，得到同一C0>0和eventualN，先于全部p/d。不能将旧固定mu U16a逐p常数假装成这一统一结果。

最后eventual阈值只交G的同一N与n≥1；E对所有n≥1有效，没有额外依赖k/r的最终阈值。gamma/c仍为E的原来共同正数，缩delta不改变它们；输出C=2*C0>0同样在全部k/r前。所有常数可依赖固定mu/J/q/a/ell和已给门，不宣称对所有J或所有基准mu共同。

## 第五阶段：事件、真实同n概率与指数系数

记M(z)=normalDeviation q z、R(z)=∑z_i−n*a，均为真实有限路径上的连续实函数。actual centeredSampleProjection逐点有限求和/分配给v*M+s*R；R不是tangentDeviation a（该既有定义实际以n*a/4为中心），仅当source a=q/4时R才等于tangentDeviation q。冻结事件用sum−n*a，正确保留一般a。

E+={M=−k ∧ r≤R}、E−={M=−k ∧ R≤−r}及abs事件都是连续有限多项式/abs的闭Borel集。由第三阶段sign，E±上sampleProjection(q,a,v±,s±)≥L±=v±*(−k)+s±*(±r)。这个hlower是真正对所有该事件路径的输入，不只AE，不借样本仍在局部邻域。

对每支应用actual H3与该可测事件/真实hlower。H1/其已接受完整proof保证同mu任意试验参数的单点和样本exp真Integrable、真实Z/Z^n>0、single/sample tilt真概率及实际n产品倾斜measure等式；不需要small-ball来给可积。H3因此确给P_mu^n(E±)的.real≤exp(n*K(v±,s±)−L±)*P_centeredTilt±^n(E±)，所有log只在真实正Z上使用，不以不可积tilt=0或top.toReal完成。

H2在同mu/hb和相同v±/s±下把centered投影tilt实际识别为quadratic tilt p±，故这里产品law恰是G的同一个真实产品law，不是把中心改为tilt均值的另一个mu族。事件E±⊆{M=−k}，在该真实有限产品概率下measureReal_mono给E±实质量≤同层实质量；G恰对全部实d有效，选d=−k，不要求k整数或预先格点相容。tilt后中心仍按固定q定义只是层坐标，不宣称均值未变。

对n≥1的合法非零n，actual normalTrialCost定义给真实恒等式 `n*K(v±,s±)−L± = −n*normalTrialCost(mu,q,a,−k/n,±r/n)`。因为n*(−k/n)=−k、n*(±r/n)=±r，它只是非零n下的环/域代数，未识别为Legendre优化；也未丢q/a常数shift，因为K是同一个actual centeredNormalLogMGF。该等式应在未来proof先明确n实值>0后清分母，不能让n0的总化除法伪造它。

于是每支乘sqrt(n)*exp(ell*k)，都只乘非负/正量。真实G给sqrt(n)*P_quadTilt±^n(layer−k)≤C0，因此得到每支≤C0*exp(ell*k−n*Cost±)。E2对r'=±r同时有效：|r'|/n=r/n≤delta≤delta0、(r')²=r²，且所有其它同一门保留，故ell*k−n*Cost±≤−gamma*k−c*r²/n。exp单调和C0>0给两个分支各自同一C0*exp(−gamma*k−c*r²/n)。没有除sqrt(n)、事件质量、k/r/b，实际概率比较和各有限转换都在同n产品上。

abs事件包含于E+∪E−（实际上相等）：按R正负消abs可证。P_mu^n是真实概率、finite，measureReal_mono及measureReal_union_le给其质量≤两支质量之和；乘sqrt(n)*exp(ell*k)非负，合并得到同一2*C0。r0时两支在R0重叠没有问题，只用union上界，不假设不交。k=r0时两支rate均0，G层界充分；k0/r>0按同样sign和cost估计；r0/k>0在n≥1/q>0下曲约束不可能但未靠除k处理。ell0允许，严格hgap保证E的gamma/c仍正。

n0不必在最终集合内，选n≥1后所有n分母和sqrt门真实成立，冻结target只要求eventual。E±可能零概率、负层可能离格点，H/G的真有限概率与all-real d界均适用；不从.real0倒推ENNReal0，也不log事件概率。这个证明针对给定k/n、r/n局部的任意远事件尾，未将其偷换成截断事件。

## 第六阶段：actual库/作用域和静态环境

冻结imports恰NormalTrialCost、CompactTiltLayerMassBound、CenteredSampleTilt；namespace Shao.OQ3/open MeasureTheory Filter/open scoped BigOperators/noncomputable section使唯一type中的∑、atTop和actual定义均可见，没有Matrix范数/默认volume新实例门。当前没有实现或receipt/Audit，声明门只可给数学/静态API可行性，不能宣称目标已内核证明。

已实际读E全部145行（核真实定义和公开门，不重审旧接受proof）、G唯一完整public type、H全部三个完整public type及S/T真实定义；源hash如上。E2本身就给signed r的完整统一余量，G/H均不要求tilt保持均值。H的已接受真概率/归一化语义继承到这里，不以作者未来I路线或旧摘要代替。

实际Mathlib `Measure.Real.lean`88–90 measureReal_mono要求大集合质量非top（可由finite自动给），137–144 measureReal_union_le为任意集合的实质量次可加；当前基准与各tilted产品都是概率，因此这些实值恰为真正有限质量，不是靠该API在∞处的总化分支。事件可测另为H3明确提供。实际该源码SHA `1b9d1490fa5acbffc570eac67f465d3d6ab0520aa3e54464f7520d60d6619b8d`。

actual `Topology.Compactness.Compact.lean`124–125 IsCompact.image需要真实Continuous F，1071–1078 IsCompact.prod需要两factor compact，正好由两个isCompact_Icc给Q及其连续像K；未来可以展开actual trial的固定系数用连续运算证明F，不依赖某个尚未核的private定理。eventual交/ge_atTop、非负乘法、平方比较和实exp单调均在现有公开环境；关键数值64/16/32的关系已在第三阶段独立算出，不是仅信作者路线。

三项直接现成olean实际存在：NormalTrialCost 2258984字节、CompactTiltLayerMassBound 808464字节、CenteredSampleTilt 285296字节；全部actual project闭包也有现成olean。不存在新cache/root公共char源码需求，未做Lean/#check/APIprobe/build。真实server确认LocalNegativeLayerTail.lean当前不存在，未读J或未来energy笔记。

## 第七阶段：34项真实Shao闭包及pins

只读实际三个direct imports递归枚举34项（32 OQ3+2 shared），source实际SHA与现成olean均核；未把I或排队J计入：

|模块|实际服务器SHA256|
|---|---|
|Shao.Basic.FinitePath|898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb|
|AtomProjection|0d369052c7f87122765612efdeaca5d9ac71abca861e7785c86d1f9edcc74d22|
|AtomicMeasure|59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39|
|CenteredLogMGF|1fb9f7b4ca976c02f5f100161da811738a443d75c47c72c2e274de54d9fb90f4|
|CenteredSampleTilt|d042af2e3ab2f38bb94b67dc53d28d335c1370fcecd8100e93a067d9ba067501|
|CentralFourierIntegral|4999d8148c1ee1ba50f61d6d19c40aed239cd001d76ee71f133d1a064c668a93|
|CharacteristicMeasureDomination|ec7032919bd8d825bb8746da15e84b29c5cb59ef97858367e4d73fdf52aa9bbb|
|CompactTiltDomination|6f31ac2e3b2b9d9b2ef957ebe52cfe3664a86694bb396b09c1006b890cbd0623|
|CompactTiltLayerMassBound|5602fd17ebac0fe40fb789067cea6b9553659dad4c8965ff88aea7e106ef5cc7|
|FiniteConstraints|800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0|
|FiniteFarArc|3a0b05d0789e53320009a44499c9c40d0fb3d892427085052c65c04456b6cf71|
|FiniteNormalSpan|0374da4860edf8af8bbbb9172e4e93bfe9b6c37ac57672b85a4f58392475b7de|
|FiniteStageMeasure|1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1|
|FundamentalFourierAsymptotic|aab18e9f073a18a87d42f0edd3e37a95da58cacf5b9635e4a64c887d340765b1|
|InverseTilt|c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811|
|JointNonlattice|51ce939232610353215fc3b7377e19b894451a9a108125e1828bf2fe8ec81559|
|LocalRateMargin|5e0e4f9ebb0dc514e0b55b9ed3aa7e5a9e8b9c128fdda2edfd2257bc3ad70a77|
|NormalLayerConditionalLaw|94e2507a83dfc232280043567f6a2f07950d39da10b45699777ac1316f24281a|
|NormalLayerFourier|063b6c5ce50e6c5ee33b53301cdfcd36a63a4ea06f9c3de729756513ca736fa3|
|NormalLayerMassBound|66ff4f217b57b319abb19ea7982e467e934219fadc2574a3487087e030a9e4f1|
|NormalTangentDomination|b65b9f5a9d67e42e611a3841563ac07004e796415c3e5b74f177a8ca80e48e90|
|NormalTangentGaussian|d2c55bf4d7a371c9b43cd3c75eab8ece8b3c7caa21aa4827bf19c24b4c7cac39|
|NormalTangentMoments|8cee48bc8f519f72b218a2ef80685d946a6debaea8b723af38a49c5bdca12cc1|
|NormalTangentPowerLimit|819bd0e801eb0b9adce0fbdbcd6ced6441b04787eb0501b811721933db0e9457|
|NormalTrialCost|8fb184ac4cf75e4f1c64e615b5c94c1a5f16c39109709a8f5dbc7fe2c5406895|
|PositiveRate|8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b|
|ProductMeasureDomination|9f05af79e47b9f778cbce7a0d19c0addea6d457eab5f088a69bf372f660c5a3f|
|RegularCovariance|0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853|
|ResonanceArithmetic|cd21a264d637bab30fed765bdc25ed09bb4ff56f6efb9c88ee09be4ca6e1648b|
|SampleBoundary|7660e23b71ce28ab43a4ad1d8df1862cf8a507b6bb9b41255e961f0bee0b93e2|
|SourceStarter|0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d|
|SummableAtoms|0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b|
|TiltedMeasureDomination|5445a68da1ac8302f174bfe2144eb8271a0af740fd6b91a87355abb41fed739b|
|Shao.Probability.FiniteIID|d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b|

真实worktree `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`，固定toolchain leanprover/lean4:v4.36.0-rc1，lean-toolchain SHA `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`，lake-manifest SHA `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`，actual mathlib HEAD `807d3836b165983210ee2ecf3cd28f239436949c`，只读核；scope正文的G/H排队历史原样保留，不替代当前已接受的full final状态。

## 最终独立声明裁决

STATUS: CORRECT

JUSTIFICATION: 冻结唯一完整type数学成立，actual E/G/H公开接口与原始source绑定及全部量词匹配。正S/det给真实T>0，严格ell<q/(32T)给同一E weight margin；可在全部n/k/r前缩delta，严格推得|b|k≤r/2并先证两trial s的真实符号，保留k/r/b0。固定方形的actual trial→quadratic连续像给同一compact K，G的C0/N在所有trial/层外；H真iid倾斜/常数shift/明确事件比较与same μ/q/a及same n产品绑定。事件内远R无需局部约束，正确符号保证全事件hlower；n非零后actualcost精确指数恒等式、真实有限event mono/union及E双signed-r余量给同一2C0和gamma/c，r0重叠亦合法。没有Legendre身份、tilt均值保持、逐trial N偷换共同N、缺正normalizer或top-real总化漏洞；n≥1阈值、J0/allreal k/r和零事件均保留。实际34项前置/publicAPI/现成缓存与pins无声明阻塞。

这是完整独立声明/source/API门CORRECT，不是尚未存在的I实现/proof/Audit通过；未来actual proof需逐门实现这些数学/measure/可积/符号/尺度义务。本目标仍只控制给定trial k/n,r/n局部条件下的负层双侧真实事件；source a=q/4、曲边真实样本恒等式和r=sqrt(nqk/16)的后续绑定未在本单元声称。大k/n仍需global strict gap，未完成源全部(17)、完整(19)、LLT/hW/KL/WC或根闭合，无Legendre最优/最弱/最优/新颖性主张。根A/B/C/D、完整19/LLT/hW/global gap仍OPEN；J及未来energy笔记未读。所有source/scope/receipt/旧票/shared/cache未修改。
