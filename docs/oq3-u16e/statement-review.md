# U16e 独立声明、来源与静态接口审查

STATUS: CORRECT

唯一审查lease1，仅拥有本新报告与授权服务器statement-review.md；不修改scope、实现、旧票、shared或cache，不spawn、Lean/APIprobe/build或下载原始完整日志。并非独占代码库，保留他人编辑。尚无本单元实现，先仅读取冻结Lean fence两个公开定义完整体和两个完整类型，独立盲译并落盘；尚未读scope正文或作者数学路线。

## 第一阶段：两个完整定义体及两个完整类型盲译

输入forty-first-unit-scope.md，SHA256 `7fbbd6d73fb40cec315795bccf9af7655063576ffc722cf7ea5477f6abafb676`。

`normalTrialTilt(mu,y,z)`：对任意实数测度mu、实y/z，令S=actual normalVariance(mu)、T=actual transverseVariance(mu)、b=actual Cov_mu(normalValue,X)/S，返回实对 `(y/S−b*((z−by)/T), (z−by)/T)`。定义自身没有概率、可积或S/T非零门，按实除法总化；定理必须用其正性条件解释真实试验参数，不能从定义名推断实际矩阵逆。

`normalTrialCost(mu,q,a,y,z)`：同一试验参数对的第一分量乘y、第二分量乘z，再减同一mu和中心q/a下、这对参数处的actual centeredNormalLogMGF。它是显式单个线性试验值，不定义sSup、Legendre变换、最优试验或概率率函数；其实际指数可积/normalizer正性在首目标中显式输出。

`exists_normalTrialCost_cubic_lower`：给真实实数概率mu、同一hb AE有界支撑、固定q/a、真实E(normalValue)=q和EX=a，以及actual normalVariance>0与actual parabolaCovariance.det>0；之后∃D>0和radius>0，先于全部实y/z，对整个闭l1球|y|+|z|≤radius，同时输出实际trial参数对应exp投影的真Integrable、其真实积分严格正，以及profile(actual S,actual T,同mu Cov(Y,X)/S,y,z)−D(|y|+|z|)³≤actual normalTrialCost。没有q>0/ell或阶段门，两个中心始终是同一mu真实均值。

`exists_normalTrialCost_weight_margin`：同一真实概率/hb，固定q/a/ell，额外q>0、ell≥0，两个真实均值门、actual S>0、actual parabolaDet>0，严格ell<q/(32*actual transverseVariance)。之后同时∃delta/gamma/c三者严格正，先于全部自然n≥1、全部实k≥0和任意有符号r；两个比值k/n、|r|/n≤delta且nqk/16≤r²时，gamma*k+c*r²/n≤n*actual normalTrialCost(mu,q,a,−k/n,r/n)−ell*k。n为实cast除数，n0显式排除；无k/r非零门或概率尾事件输出。

独立类型初判：若实际T=det/S>0、实际Q完成平方为S(v+b*s)²+T*s²，则该trial对满足v+b*s=y/S、s=(z−by)/T；dot=2profile且Q(trial)=2profile。U16d共同logMGF上界经固定线性算子范数可给首目标的真实三次下界；再以actualcost作为U16c的generic I输入可望给次目标。必须之后核实actual T/完成平方定义、同mu绑定、清分母与参数窗口的真实量词，不能凭作者命名默认这些恒等式。

y=z0、退化方向、D的严格正见证、ell0、signed b/r、k/r零、n1和正S/T门均需检查；本段先保存，之后才source/scope/API。实际Legendre/Fenchel、概率Chernoff、紧族uniform与根A/B/C/D保持OPEN。

## 第二阶段：冻结范围、真实来源与接受凭据

盲译先落盘后才读取完整scope、R1、实际已接受源码及固定库。scope本地/远端实际SHA256均 `7fbbd6d73fb40cec315795bccf9af7655063576ffc722cf7ea5477f6abafb676`，远端scope为6270字节。拟NormalTrialCost.lean，直接imports CenteredLogMGF和LocalRateMargin；namespace Shao.OQ3、open MeasureTheory、noncomputable section。没有本单元实现、receipt或目标构建可用，本报告不将静态可行性当作内核通过。

真实R1路径 `C:/game/shao/current/oq3/proofs/r1/report.md`，SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，本次直接核350–383行。351行实际中心K_c、353–355行优化试验、370–371行inverse-covariance二次代价，以及378–383行曲边负层余量给出本单元的来源。当前显式试验法是标准充分下界路线，不声称normalTrialCost等于来源的Legendre I，不以单个试验值代替上确界或全局最优性。

本次实际承重已是lead全文接受的U16d/U16c完整独立票，分别SHA256 `7dd7ce4fe20dc562fb4dfdc95683e067164f5ec1405479d838a9682c4859308e` 和 `a536247a23c01140ca82f79bcc72156081d92106ee2feea0dbf2234cf83f8169`，指定服务器现有最终报告hash再次匹配。scope正文中“完整审查运行/尚未接受”是冻结当时的计划说明，不替换当前已接受状态；旧scope文字未被追改，也不拿作者机械绿灯充当独立前提。

## 第三阶段：实际协方差绑定与两个定义的数学含义

指定服务器actual RegularCovariance.lean SHA256 `0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853`29–30行定义 transverseVariance(mu)=parabolaCovariance(mu).det/normalVariance(mu)。所以首目标hS>0、hD>0直接给实际S>0和T>0；可用div_pos hD hS，无需基点正质量或额外原子性门。实际库名为transverseVariance_pos的现有定理166–169行另需hbase，它不适用于本声明全部mu；本审查没有漏掉该门，而明确用实际定义完成正性，故没有声明阻塞。

actual NormalTangentGaussian.lean SHA256 `d2c55bf4d7a371c9b43cd3c75eab8ece8b3c7caa21aa4827bf19c24b4c7cac39`67–75行 `normalTangentQuadratic_complete_square` 完整接口是：真实mu概率、hb和hS>0后，对任意v/s给

`Q(mu,v,s)=S*(v+b*s)^2+T*s^2`，

其中b正是同mu Cov(normalValue,X)/normalVariance、T正是上述实际transverseVariance。该定理不要求hbase/hD，但本声明额外hD恰好使T>0。其实际证明消费同mu的normal_tangent_covariance_det；hb保证所有多项式实际L²/矩可积，det关系为真正(Y,X)协方差与(X,X²)抛物线矩阵的绑定，不是任意det>0的符号替换。T是tau²而非tau。

把S,T,b固定为上述同mu量，令w=z−by、s*=w/T、v*=y/S−b*s*。这正是完整公开normalTrialTilt的两个分量，顺序和负号无误。由于S,T>0，真实清分母后有v*+b*s*=y/S，并且

`v* y+s* z=y²/S+w²/T`，
`Q(mu,v*,s*)=S*(y/S)^2+T*(w/T)^2=y²/S+w²/T`。

故两者都是2*gaussianRateProfile(S,T,b,y,z)，因此实际对偶代数式为

`v* y+s* z−Q(mu,v*,s*)/2=gaussianRateProfile(S,T,b,y,z)`。

系数1/2没有丢失，Cov的行列/normal-tangent坐标没有互换；没有除b、y、z或w，不需要它们非零。该恒等式只是实际二次型的显式线性试验值，不使用微分、最优化、Fenchel定理或全局Legendre构造。两个公开定义在任意mu上总化，但定理的真实概率/hb、中心与正S/T才允许这种解释。

## 第四阶段：首目标的完整独立可行性证明

为固定实际mu的线性trial映射，可同时选择

`L=1/S+(|b|+1)^2/T+1>0`。

令t=|y|+|z|≥0。正T下abs_div、三角不等式给|s*|≤(|b|+1)t/T；再由|v*|≤|y|/S+|b||s*|，得到

`|v*|+|s*|≤[1/S+(|b|+1)^2/T]*t≤L*t`。

S/T正性在清绝对分母时实际使用，b的任意符号只经|b|处理。L固定在全部y/z之前，且有+1保证严格正；不需要抽象算子范数、额外cache、每点选择半径或非空目标集合。

actual CenteredLogMGF.lean SHA256 `1fb9f7b4ca976c02f5f100161da811738a443d75c47c72c2e274de54d9fb90f4`56–64行完整接口已重新读取，输入正好是本声明同一个mu、hb、q/a和真实两中心；一次性给C0>0、delta0>0，对闭l1参数球内所有v/s同时输出真exp Integrable、真实normalizer Z>0和K_c≤Q/2+C0(|v|+|s|)^3。

取radius=min1(delta0/L)>0，D=C0*L³>0，均在全部y/z之前。若t≤radius，则正L给|v*|+|s*|≤L*t≤delta0，正好进入同一个U16d参数球。这一步保持实际测度、中心、trial参数和完整积分，不从固定方向窗口偷换共同半径。先消费U16d的真实可积和Z>0，normalTrialCost内的log因此是真正正normalizer的log，未利用不可积积分0或log0总化。

再用非负参数范数、L和C0把三次误差合法控制为C0(|v*|+|s*|)^3≤C0L³t³=D t³。结合已核实际对偶代数式，

`normalTrialCost=v* y+s* z−K_c(v*,s*) ≥ profile−C0(|v*|+|s*|)^3 ≥ profile−D t³`，

精确得到首目标三个分量。真实指数/积分的中心仍为同mu真实q/a；未在proof-route中把actualQ换成自由S/T/b。D/radius的严格正性也在y=z=0时保留，不需要D最小或最优。

边界：y=z=0给trial=(0,0)，真实exp=1、Z=1、log=0，cost/profile/误差均0；z=by使w=0、s*=0，仍无除w；y=0或b=0同样合法，b可负。完整退化mu一般不满足本目标hS/det>0，故不能把U16d的退化mu范围偷带过来；此处恰好只在真实可逆二次型下定义并解释trial逆。首目标q/a只需是真实均值，无q>0/ell条件，范围未擅自缩窄。

## 第五阶段：第二目标的实际接口接合和量词

actual LocalRateMargin.lean SHA256 `5e0e4f9ebb0dc514e0b55b9ed3aa7e5a9e8b9c128fdda2edfd2257bc3ad70a77`49–60行完整公开类型已重新读取。首目标第三分量给真正局部hI；将其I取为显式函数 `(fun y z => normalTrialCost mu q a y z)`，S/T/b取上述实际同mu值，D/radius取首目标见证。D>0提供U16c所需D≥0，radius>0保留；q>0、ell≥0、本目标hgap和实际S/T正性逐项匹配，没有额外Hessian/Taylor或概率率假设。

因此U16c确实适用于这个actualcost函数，产出同一delta/gamma/c>0先于全部自然n≥1、实k≥0和signed r；右侧I(−k/n,r/n)就是本公开目标的actualcost。首目标的全ball下界恰好满足U16c对全部合法点的hI，不是仅沿一个固定射线；U16c内部统一缩窗先建立l1邻域门，保证消费actualcost下界的点真实在radius内。

q/(32T)与曲边nqk/16保持原系数，T是实际tau²；n≥1保证实cast(n)>0，k不是整数限制，r可负，ell0/k0/r0/n1均为已接受U16c实际范围。第二目标并未给试验第二参数的尾部符号或真实尾概率界；即使未来要用它做单侧倾斜，仍需另证正确符号、真实iid换测度、span保持及紧族统一C/sqrt n等。把generic I在本步骤实例化为actualcost，不等于证明它是实际Legendre I或满足对所有试验参数的Fenchel性质。

## 第六阶段：实际标准API、导入和版本环境

仅指定服务器只读源码/既有缓存；无Lean/#check/APIprobe/build。实际标准API如下：Algebra.Order.Field.Basic SHA256 `fabd3062223bbdcd4efae38a4a586f88241f67da533e79ee06c56ba507c27b2d`673–674行abs_div；Algebra.Order.GroupWithZero.Basic SHA256 `28c0432242f3766a643689abd852cbf92fee391d314f76815e6977e64854103c`874–878行div_pos/div_nonneg、1128–1141行正分母的le/div/lt比较；Algebra.Order.Ring.Abs SHA256 `afad3c8ac856f0019cb16aeb194e452613aee2bfe400e82c2e2a7becd89a5abe`49行abs_mul。所有需要消去的S/T/L为真正数，1、2和自然n≥1的分母亦有明确门，不对signed b清非零或反转不等式。

这些API沿LocalRateMargin→FieldSimp/Positivity的实际公开导入路径可见，ring/field_simp/有限多项式和实幂比较的现有环境足够，不需新线性算子/矩阵逆cache。两个直接导入既有olean实际存在：CenteredLogMGF为392960字节，LocalRateMargin为982024字节。完整公开import静态递归无缺失源，实际Shao闭包12份，哈希如下：

| 实际前置模块 | SHA256 |
| --- | --- |
| CenteredLogMGF | `1fb9f7b4ca976c02f5f100161da811738a443d75c47c72c2e274de54d9fb90f4` |
| LocalRateMargin | `5e0e4f9ebb0dc514e0b55b9ed3aa7e5a9e8b9c128fdda2edfd2257bc3ad70a77` |
| NormalTangentMoments | `8cee48bc8f519f72b218a2ef80685d946a6debaea8b723af38a49c5bdca12cc1` |
| NormalTangentGaussian | `d2c55bf4d7a371c9b43cd3c75eab8ece8b3c7caa21aa4827bf19c24b4c7cac39` |
| RegularCovariance | `0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853` |
| FiniteStageMeasure | `1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1` |
| InverseTilt | `c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811` |
| AtomicMeasure | `59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39` |
| SummableAtoms | `0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b` |
| FiniteConstraints | `800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0` |
| SourceStarter | `0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d` |
| PositiveRate | `8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b` |

实际toolchain `leanprover/lean4:v4.36.0-rc1`，lean-toolchain SHA256 `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`，lake-manifest.json SHA256 `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`，manifest pin与实际mathlib HEAD均 `807d3836b165983210ee2ecf3cd28f239436949c`。两个定义/目标所需Measure、actual函数、ℝ×ℝ分量与积分记法在冻结namespace/open环境中可见，无新矩阵范数/default volume或cache义务。

## 最终独立声明裁决

STATUS: CORRECT

JUSTIFICATION: 两个完整定义和两个完整类型均与实际同mu协方差绑定、真实K_c及标准显式试验路线相符。S/T真正数、trial参数符号/顺序和实际完成平方对偶式精确；共同线性系数L把全部y/z的固定小球送进U16d共同参数球，真exp可积与Z>0保持，实际cost得到profile减三次下界。再以这个明确actual函数给U16c全部hI门，可获得先于全部n/k/r的真实曲尾权重余量，保留32/16系数、正分母及零/signed边界。已接受完整前置、实际公开API与现有缓存已核对，没有需要修订的声明、数学、来源或静态环境缺口，可进入实现；此票不是新目标内核验收。

非声明：不证明normalTrialCost等于Legendre上确界、Fenchel普遍下界或最优试验，不生产实际逆Hessian，不证明尾试验符号、实际iid倾斜换测度、紧倾斜族统一Fourier质量界、Chernoff(16)/(17)、全局唯一性/远区gap、完整(19)/LLT/hW/WC/KL或根闭合，不声称最弱/最优/新颖性。根A/B/C/D、实际Legendre与概率Chernoff、紧族uniform均保持OPEN。只写本新报告和授权副本，没有读未来实现/作者笔记，未改scope/源码/旧票/shared/cache，未spawn/Lean/probe/build。
