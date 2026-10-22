# U12e NormalTangentDomination 独立声明与来源审查

## 第一阶段：仅冻结Lean代码块的独立盲译（先落盘）

本节只读取twenty-seventh-unit-scope.md的Lean代码块，在读取scope解释、真实R1、实际前置及本次库API之前落盘。实测scope SHA256=`576ad253917355393b231302dba1aced8a1123bacb2d111f0e8eaeb6df299520`。零定义、三个完整目标；尚无实现或最终裁决。

1. exists_normalTangentQuadratic_coercive：任意实际概率mu，若真实AE支撑满足|x|≤4+sqrt10，actual normalVariance(mu)>0及actual parabolaCovariance(mu)的det>0，则存在一个正实常数c，对全部实t/s共同成立c(t²+s²)≤actual normalTangentQuadratic(mu,t,s)。c先于t/s，不能随方向选择。
2. exists_centeredNormalTangentCharacteristic_gaussian_bound：同一个实际概率mu和AE界，给定q/a为该mu下actual EY/EX，且同一mu的actual S>0、D>0，则存在两个共同正常数delta/c，对全部实t/s在两个闭区间|t|≤delta、|s|≤delta内，真实中心联合特征函数的复范数≤exp(−c(t²+s²))。delta/c先于所有t/s，不是仅沿固定方向的局部结论；中心门明确保留。
3. exists_centeredNormalTangentCharacteristic_scaled_domination：同样mu/AE界/实际两个均值及S/D正性，存在共同正delta/c，随后对每个给定实s，最终所有自然数n上，对全部实v，只要|v|≤delta sqrt(n)，就有真实中心特征函数在(tangent与normal均按sqrt(n)倒数缩放)的n次幂范数≤exp(−c v²)。eventual阈值可依赖s以及已固定mu/q/a/delta/c，但在∀v之外，不能逐v取阈值。delta/c也在∀s之外；n=0无需成立，需核最终n≥1以合法消去sqrt(n)。

待核actual Q与同一mu真实S/D/C的关系、共同强制下界、二样本真正可积与矩/中心及Fubini/实部/平方次序、局部相位统一界、从平方范数到指数界的常数与正性、缩放eventual量词和全部v统一、实际import/作用域/实例。当前仅盲译，不将此界当作幂极限、DCT、LLT或实际hW；根A/B/C/D全部OPEN。

## 第二阶段：真实来源与actual承重接口

盲译落盘后读取scope解释、R1 309–345，实测R1 SHA=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。源314–322使用一个固定有界律的真实Cov(Y,X)、EY=q、EX=a；335–343使用相同中心的联合特征函数，并在sqrt(n)尺度作Gaussian积分。本候选是该中心弧的共同模长支配前置，较源所用固定有限律推广到满足相同真实有界/非退化门的任意概率律，推广有效；没有声称已建立源341的极限展开或343的极限积分交换。

已读取实际前置源码和所用证明/定义：NormalTangentMoments SHA=`8cee48bc8f519f72b218a2ef80685d946a6debaea8b723af38a49c5bdca12cc1`，其先真可积再合法平方展开，给同一mu下Z=t(Y−q)+s(X−a)的真MemLp2、EZ=0、EZ²=actual Q；其完整独立CORRECT票已在本gate前完成。FiniteFarArc SHA=`3a0b05d0789e53320009a44499c9c40d0fb3d892427085052c65c04456b6cf71`，21–23的actual centeredNormalTangentCharacteristic正是∫exp(iZ)dmu，不是另一形式特征函数。NormalTangentGaussian SHA=`d2c55bf4d7a371c9b43cd3c75eab8ece8b3c7caa21aa4827bf19c24b4c7cac39`，19–22定义actual Q=S t²+2Cts+V s²；46–75证明同一mu的S V−C²=det(parabolaCovariance)=D和完整平方Q=S(t+(C/S)s)²+(D/S)s²。RegularCovariance SHA=`0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853`实际S=Var(Y)、矩阵为Cov(X,X²)；InverseTilt SHA=`c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811`的紧支撑连续可积接口消费真实概率/hb。没有以形式正定矩阵代替actual随机矩。

## 第三阶段：三个完整目标的独立数学可行性

记beta=4+sqrt10>0、B=8beta+beta²，则mu-AE有|X|≤beta、|Y|≤B。概率有限，所有下文连续有界函数真正可积；所有参数均为有限实数。以下是本声明gate的独立数学核对，不是未来实现或内核证明的宣告。

**目标1。** 令S=normalVariance(mu)>0、D=det(parabolaCovariance(mu))>0、C=Cov_mu(Y,X)、k=C/S、T=D/S>0，均来自同一mu。actual完整平方给Q=S(t+ks)²+T s²。逐点不等式t²+s²≤2(t+ks)²+(2k²+1)s²可由t=(t+ks)−ks及(a−b)²≤2a²+2b²取得。取kappa=min(S/2,T/(2k²+1))>0，则2kappa≤S且kappa(2k²+1)≤T，故对全部t/s共同有kappa(t²+s²)≤Q。分母2k²+1严格正；没有方向依赖常数或未经证明的谱界，也未仅凭任意矩阵det>0断言正定。

**目标2：二样本积分门。** 对任意固定t/s，Z连续，且AE有|Z|≤|t|(B+|q|)+|s|(beta+|a|)。Z、Z²真可积，U12c在实际hq/ha下给EZ=0及EZ²=Q。F=exp(iZ)连续且全局范数1，因此真Integrable F；其共轭同样真可积。在实际mu.prod mu下，两坐标各满足hb的共同AE事件可由可测支撑集合和乘积AE接口取得；mu.prod mu是真实概率。Z(first)²、Z(second)²由坐标提升真可积，Z(first)Z(second)由一维真可积与Integrable.mul_prod真可积；所以(Z(first)−Z(second))²在拆开积分之前真可积。复乘积F(first)conj(F(second))同样真可积（或直接由连续可测及范数1、有限乘积measure取得），其实部cos(Z(first)−Z(second))也真可积。

于是可在真实联合可积之后应用Fubini/乘积分解、共轭积分、实部积分，得

‖∫F dmu‖² = Re[(∫F dmu)conj(∫F dmu)] = ∫cos(Z(x)−Z(y))d(mu.prod mu)。

同时合法展开二样本平方并用质量1、EZ=0，取得∫(Z(x)−Z(y))²d(mu.prod mu)=2Q。这里平方是两个真实独立坐标下的相位差平方；没有将“单变量积分存在”直接当作联合Fubini前提。

**目标2：共同小半径与常数。** 相位差中q/a实际抵消，故乘积AE有|Z(x)−Z(y)|≤2B|t|+2beta|s|。可选delta=pi/[2(B+beta+1)]>0，则全部|t|,|s|≤delta同时保证|Z(x)−Z(y)|≤pi。真实库cos上界要求的正是这个AE门，不能全局套用。积分该不等式并用真实二样本矩，得到‖phi(t,s)‖²≤1−4Q/pi²≤exp(−4Q/pi²)≤exp(−4kappa(t²+s²)/pi²)。范数及指数均非负，以exp(u)²=exp(2u)比较平方可得‖phi(t,s)‖≤exp(−c(t²+s²))，其中c=2kappa/pi²>0。该取法同时对全部t/s成立，边界t=s=0给1≤1正确；没有丢失因子2、pi正性或平方根符号门。q/a即使没有被用于小半径，其真实均值门仍在二样本矩等式中正确消费。

**目标3。** 使用目标2同一个delta/c（先于s）。固定s后，选自然数N≥1且N>(|s|/delta)²；存在性只需实数的Archimedean性质，阈值不依赖v。所有n≥N有n>0、sqrt(n)>0、(sqrt(n))²=n及|s|/sqrt(n)≤delta。对任何|v|≤delta sqrt(n)，也有|v|/sqrt(n)≤delta，因此可同时应用目标2。复范数乘方恒等式及exp乘方给

‖phi(v/sqrt(n),s/sqrt(n))^n‖ ≤ exp(−c(v²+s²)) ≤ exp(−c v²)。

消去n时使用n>0和sqrt平方恒等式，而非对n=0作倒数推理。eventual之后仍是∀v，故增长窗口中的全部v共用同一N；这里没有逐v取阈值。delta/c对所有s共同，N可随s改变，完全吻合类型。c>0还使v↦exp(−c v²)是真正Lebesgue可积Gaussian，但本目标没有断言截断积分的DCT门或极限存在。

三个目标的协方差、矩、积分及特征函数始终采用同一mu；类型中的常数可依赖这个固定mu，其余参数在正确量词之后，不是对全部mu给统一常数。hS/hD排除退化方向；不需要有限原子严格正性、ell/q区间、格点或有限阶段额外构造。用于实际有限mu时，可消费既有同一finiteMass概率/中心及协方差正性接口，当前类型没有重新选择p/q或改成原律P。

## 第四阶段：固定库、导入与环境核对

仅在指定服务器只读现有源码/olean，未运行Lean或API探针。Mathlib实际git HEAD=`807d3836b165983210ee2ecf3cd28f239436949c`，lean-toolchain=`leanprover/lean4:v4.36.0-rc1`。实际run scope.md的SHA与本地均为`576ad253917355393b231302dba1aced8a1123bacb2d111f0e8eaeb6df299520`。

* Trigonometric.Bounds.lean SHA=`4268d20e37d4ba832714de59a8c6174e495c907512b786642c6c52b4d59a91c7`，139–147的Real.cos_le_one_sub_mul_cos_sq真实类型是|u|≤pi→cos u≤1−(2/pi²)u²，闭端点也覆盖；已有olean 44936 bytes，未构建。不能把其误读为无条件全实cos二次上界。
* Integral.Prod.lean SHA=`8ccfbcad5fffde3f8d0dfa3167b80dacfb524bc10790f1744b8b8a9b3f4c3a05`，281–289的Integrable.comp_fst/comp_snd需另一侧有限measure；300–302的Integrable.mul_prod消费两个真实一维Integrable；443–444的integral_prod及471–473的integral_integral明确消费联合Integrable；538–540提供分离乘积积分恒等式。上文已先提供真实可积，不借该恒等式的总化分支代替条件。
* Measure.Prod.lean SHA=`007561e86f53a65ad411fcbd20d05df9e922f01c5a93eff0f9de26ac49f12ca3`，327–329提供实际乘积概率实例；449–451的ae_prod_iff_ae_ae需真实MeasurableSet，当前hb/连续相位的界集合均可测。实际概率亦提供finite/SFinite门。
* Bochner.ContinuousLinearMap.lean SHA=`272fbf423443f1cd4aa032396f85a19c2f4f80b9fe9df655de16b0df655a22c3`，165–167的integral_re需要真实Integrable；174–175的integral_conj提供共轭交换。相位范数1及连续性满足实部交换所需真可积门。

拟import NormalTangentMoments、FiniteFarArc及Trigonometric.Bounds足以绑定所有三个公开类型；namespace Shao.OQ3及open MeasureTheory Filter使Measure、积分、eventually和atTop处于正确作用域。声明不含需要Matrix scoped记号的mulVec/矩阵字面量；`.det`是已有actual矩阵的投影，不需另添Matrix范数实例。随机积分均显式mu，不发生默认volume歧义。

实际import图也已只读核对：NormalTangentMoments→NormalTangentGaussian→Lebesgue.Integral→Haar.Unique→Integral.Prod，其中三个Mathlib边为public import，现成乘积积分API确实由拟导入链提供；Bochner.ContinuousLinearMap由FiniteFarArc→JointNonlattice→Convex.Integral→AEEqOfIntegral链到达；GaussianIntegral由NormalTangentGaussian直接到达。以上Prod、ContinuousLinearMap、GaussianIntegral以及三个已有project前置的olean均实测存在；FiniteFarArc另显式导入Lebesgue.Basic。无缺失CLT/Taylor缓存或新cache写入依赖；这是静态声明/环境gate，不虚称本候选已经Lean elaboration或kernel通过。

STATUS: CORRECT

JUSTIFICATION: 三个完整类型准确绑定同一实际有界概率mu的中心、协方差和特征函数。actual完整平方给共同正强制下界；真实二样本可积/AE/概率及Fubini、实部、矩门可满足，cos二次界可在一个共同正半径内合法应用并给正确Gaussian系数。sqrt尺度结论的delta/c在s外、eventual阈值在全部v外，n≥1可统一加入，因此没有量词或n0漏洞。固定导入、作用域、真实库条件及已存在cache可支持该声明，未发现需修订的来源、数学或静态环境缺口。

本票仅批准这三个声明/source与静态环境，不是未来实现、proof/type/kernel或机械审查票。未读取作者API/实现笔记或未来实现，未写Lean实现、运行Lean/API探针、重编成功项、写缓存、spawn、commit/PR。没有幂极限、截断DCT/极限积分交换、Fourier反演、层归一化、混合LLT、实际hW或根闭合主张。所有根A/B/C/D保持OPEN。
