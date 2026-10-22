# U12f CentralFourierIntegral 独立声明与来源审查

## 第一阶段：仅冻结Lean代码块盲译（先落盘）

本节仅提取twenty-eighth-unit-scope.md的Lean代码块，在读取scope解释、真实R1、本次actual前置与固定库之前落盘。实测scope SHA256=`4059b088d8038323e630d4dc8c694b0138fa22cf4caf338e26b0e7bdebaf97b2`。一定义、三个完整目标，尚无实现/最终判定。

定义centralFourierIntegrand(mu,q,a,delta,s,d,n,v)：在真实闭区间[−delta sqrt(n),delta sqrt(n)]上，是复层相位exp(−i v d(n)/sqrt(n))乘同一实际中心characteristic_mu,q,a(v/sqrt(n),s/sqrt(n))的n次幂；在区间外为复0。d为任意实序列。定义允许任意delta及n0，所有除法按Lean实/复总化定义；必须在证明中另外区分最终正n。

1. centralFourierIntegrand_integrable：任意实际概率mu及任意q/a/delta/s/d/n，整个真实截断复函数对显式实Lebesgue volume真正Integrable。无hb/均值门，也无delta正性或n正性门，需包含负delta及n0。
2. centralFourierIntegrand_tendsto：同一实际概率mu、真实AE有界支撑、q/a为actual EY/EX，另给delta>0及固定s、全序列实有界d（明确∃M,∀n,|d(n)|≤M），则每个给定实v的真实截断函数沿n趋于Complex.exp((−Q(mu,v,s)/2:ℝ):ℂ)。没有S/D/Q正性门；d无需收敛，只需其sqrt尺度相位趋0且窗口最终包含固定v。
3. exists_centralFourierIntegral_tendsto：同一概率/hb/真实两个均值及actual S>0、D>0给一个共同正delta，随后对所有固定s、所有全序列实有界d，真实显式Lebesgue积分沿n趋于实数sqrt(2pi/S)*exp(−transverseVariance(mu)*s²/2)嵌入ℂ。delta在全部s/d外；每个s/d可有自己的eventual阈值。需要以同一mu的actual Q及S/τ²解释该全Gaussian积分。

待核每项真可积、negative delta/n0边界、d(n)/sqrt(n)趋0与cutoff最终包含固定v、共同delta量词、U12e在全v外的eventual支配门、滤子版DCT真实eventual可测/AE点态与同一Gaussian真可积、实复积分转换、actual S/D/τ²及volume实例/导入。当前仅盲译，不把本声明当作格点反演、归一化、条件Lévy、LLT或实际hW；根A/B/C/D全部OPEN。

## 第二阶段：真实R1与actual承重定义

盲译落盘后读取scope解释、真实R1 309–345，实测R1 SHA=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。源315/318/335–343使用同一mu的EY=q、EX=a中心和sqrt尺度联合特征函数；324给有界层位移。定义中的负相位正是层位移Fourier因子在法向变量v/sqrt(n)下的形式。本单元只对该已缩放的中心积分作分析；其最终常数没有格距或外部反演归一化因子，不能自行认定为源15的完整概率极限。

实际前置源码本地及真实服务器hash一致：NormalTangentPowerLimit=`819bd0e801eb0b9adce0fbdbcd6ced6441b04787eb0501b811721933db0e9457`；NormalTangentDomination=`b65b9f5a9d67e42e611a3841563ac07004e796415c3e5b74f177a8ca80e48e90`；NormalTangentGaussian=`d2c55bf4d7a371c9b43cd3c75eab8ece8b3c7caa21aa4827bf19c24b4c7cac39`；FiniteFarArc=`3a0b05d0789e53320009a44499c9c40d0fb3d892427085052c65c04456b6cf71`。U12d/U12e完整独立最终票均已先完成，hash分别`96b2dfc6293e571e91a969aa7f2f07dc758989ea2fb22238f3b7cfa99f978841`、`3f20da936f2d35e0cd9558ccb0d46768dcb28e9434e0b6604031f6cc1cc479b9`；本次仍独立读取所消费的实际定义、类型及相关证明。

FiniteFarArc 21–23的actual characteristic是mu下真实∫exp(i[t(Y−q)+s(X−a)])，50–65在任意概率mu下以相位norm1、真实概率可积常数作dominated连续性证明，不需要随机矩。其factor与JointNonlattice 37–43还给范数≤1。U12d 137–192给同一mu/中心/固定v/s的真实点态幂极限，无S/D门。U12e 262–308给∃delta c>0后∀s、eventually n、∀v增长窗口内的共同exp(−c v²)界，阈值在全部v之外。U12b actual Q=Var(Y)v²+2Cov(Y,X)vs+Var(X)s²；S=normalVariance=Var(Y)，transverseVariance=D/S=τ²，非τ本身。

## 第三阶段：一定义与三个目标的独立数学核对

### 1. 每项真正Lebesgue可积，包括所有边界

对每个固定n，sqrt(n)和d(n)是固定有限实数。v↦−v d(n)/sqrt(n)即使n=0也按实除法定义为连续函数；复指数连续。actual characteristic在任意概率mu下对两个频率联合连续，因此与(v/sqrt(n),s/sqrt(n))复合、自然n次幂及相位乘积均为连续复函数。每项的外层积分是Lebesgue volume，不是随机mu积分。

闭区间I_n=[−delta sqrt(n),delta sqrt(n)]对任意delta/n都是可测紧集，真实Lebesgue体积有限。因此连续主体在I_n上真正IntegrableOn，再以可测集合indicator得到整个零延拓函数的真Integrable。也可用主体norm≤1和有限体积直接取得；不能从norm≤1就声称在无限体积全实轴上可积，真正有限支持门在此不可省。

当delta<0且n≥1时，I_n左右端点逆序，集合为空；函数为0。delta=0时是单点支持，Lebesgue-AE为0。n=0对任何delta均有I_n={0}、相位exp0=1且characteristic的0次幂为1，故函数为indicator_{0}(1)，Lebesgue积分0。没有在这些初项使用sqrt非零消去，首目标类型不需追加delta>0或n>0。

### 2. 层相位、增长cutoff与逐v点态极限

由hd取一个对所有自然n有效的有限实界M；如需正界可取|M|+1，故不依赖M原先是否严格正。最终n≥1后sqrt(n)>0且sqrt(n)→∞，于是|d(n)/sqrt(n)|≤(|M|+1)/sqrt(n)→0。对固定v，实相位−v d(n)/sqrt(n)→0；实到复嵌入及复指数连续给层相位趋1。整个论证不要求d(n)自身收敛。

delta>0给delta sqrt(n)→∞，对每个固定v最终|v|≤delta sqrt(n)，即真实indicator最终恒1。该eventual时刻可依赖v，符合点态目标。以最终相等改写截断函数，再将层相位趋1乘U12d同一mu/q/a、同一固定v/s的幂极限，得到Complex.exp((−Q(mu,v,s)/2:ℝ):ℂ)。不需S/D/Q正性，零方向和退化二次型也成立。所有n固定同一mu、q/a、s和d，没有以随n改变的概率律或中心偷换该极限。

hd是明确全序列界，不是只给eventual O(1)标签。本票没有默默形式化从源O(1)到全序列界的有限初项补界，也不要求d(n)格点可达；这些与当前条件化分析目标分开。

### 3. 共同delta、真实eventual支配、DCT及actual Gaussian常数

先从同一mu/hb/q/a/hq/ha/hS/hD实例化U12e，取得共同delta/c>0；二者先于全部s/d。给定任意s和满足hd的d后，U12e提供一个在全部v外的eventual n门。窗口内，|v|≤delta sqrt(n)，真实层相位norm恒1（对所有实相位成立），所以乘上它不改变幂的范数界；窗口外indicator为0。因此对同一个eventual n事件、全体实v，都有

‖centralFourierIntegrand(n,v)‖≤exp(−c v²)。

这是比DCT所需eventually n、AE v更强的界。它不依赖d的收敛，也不需为各v另外取支配阈值；同一delta不能随s/d重选。U12e只是eventual支配，所以不能直接填给要求∀n支配的序列版定理。本候选拟导入的真实filter版DCT恰好允许eventual界：

* 每个n真Integrable由目标1，故AEStronglyMeasurable，对eventual n当然成立。
* 同一上述eventual事件给AE v共同Gaussian界。
* c>0给v↦exp(−c v²)对真实Lebesgue volume真正Integrable。
* 目标2对每个v给真实点态Tendsto，因而满足AE v点态门。此处点态阈值可随v，而支配阈值仍在v外，两者不可混淆。
* atTop:Filter ℕ有可数基，满足filter版的IsCountablyGenerated门；复数具所需实范数空间结构。

因此真实complex积分趋于∫Complex.exp((−Q(mu,v,s)/2:ℝ):ℂ)dv。对每个实数r，Complex.exp(r:ℂ)=(Real.exp r:ℂ)；U12b的normalTangentGaussian_integrable在同一mu、hb、S>0下先保证实际实Gaussian真可积，再进行实到复积分转换。actual integral_normalTangentGaussian给

∫exp(−Q(mu,v,s)/2)dv = sqrt(2pi/S)*exp(−τ² s²/2)，τ²=actual D/S。

所以最后的实数常数嵌入ℂ与完整目标精确相符。S>0使2pi/S处于正域，hD>0使τ²>0并提供共同coercive支配；U12b单独Gaussian可积只需S>0，不应暗加其他均值或矩阵假设。本过程始终同一actual Q/协方差，不用任意形式正定矩阵替换；没有交换随机二样本积分或引入未经给出的Fubini门。

## 第四阶段：固定库与静态环境独立核对

只在指定服务器只读源码/已存在olean，无Lean、API探针或目标构建。真实run scope.md与本地均SHA=`4059b088d8038323e630d4dc8c694b0138fa22cf4caf338e26b0e7bdebaf97b2`；实际mathlib HEAD及manifest rev=`807d3836b165983210ee2ecf3cd28f239436949c`，lean-toolchain=`leanprover/lean4:v4.36.0-rc1`。

|固定库/API|实际条件与SHA256|
|---|---|
|Integral.DominatedConvergence 68–75|filter版需[l.IsCountablyGenerated]、eventual AEStronglyMeasurable、eventual AE共同bound、真实Integrable bound、AE点态Tendsto。正是本候选可给出的门；58–65的另一序列版要求全n支配，不能混用。`56394aacfe591230d26a1d93641f2a1d3e3a3eae4fcfe772775533a1da295833`|
|Function.LocallyIntegrable 582–597|ContinuousOn/Continuous在紧Icc上真IntegrableOn；真实Lebesgue在紧集有限、实/复标准拓扑与Borel门均适用。`a100190a7214f8976974c9c2856c7f411ba8e3bb46ef8bf7965fbcf1c00e649c`|
|Integral.IntegrableOn 340–350|可测s上IntegrableOn等价indicator全空间Integrable；不会省去窗口可测性。`d1108ec5e836af0af6bc62c8ad5dd94a371dbc8df3e51698049d51221b3663c2`|
|GaussianIntegral 115–117|integrable_exp_neg_mul_sq真实要求c>0。`4378f161cf5d482be77941cc9aea0195d2e83fe54eeb51b2ab33db1a318ccb9c`|
|Bochner.ContinuousLinearMap 158–163|integral_complex_ofReal将实际实Gaussian积分嵌入复数；数学论证已另先提供真可积。`272fbf423443f1cd4aa032396f85a19c2f4f80b9fe9df655de16b0df655a22c3`|
|Lebesgue.Basic 55、87、124|真实volume等于实Stieltjes恒等测度，volume Icc(a,b)=ofReal(b−a)，单点体积0，覆盖负delta/n0。`4955d3400a03ba9d525206fcf1cff8592497dfff06674ca13d68d3bdcabb964d`|
|Haar.OfBasis 309–319|实际Real.measureSpace及标准基规范Haar volume实例，非任意别的默认测度。`b243e3c02d446de7b0475db5a61405224c298ae134d4fe0e609cf55d5d874d07`|

DominatedConvergence.olean实测已存在（134976 bytes），所拟两project导入的olean及LocallyIntegrable、IntegrableOn、Lebesgue.Basic olean亦存在。真实public import图独立核：PowerLimit→FiniteFarArc→Lebesgue.Basic给实际实volume；PowerLimit→NormalTangentMoments→NormalTangentGaussian给GaussianIntegral；DominatedConvergence→IntervalIntegral.Basic→Bochner.ContinuousLinearMap→Bochner.Set→LocallyIntegrable→IntegrableOn给真实连续紧区间/indicator接口。无需新增CLT/Taylor/测度缓存。

拟namespace Shao.OQ3、open MeasureTheory Filter足以使用现有定义、显式volume、Tendsto/atTop及积分记号；三个类型无需要Matrix scoped字面量或mulVec的记号。所有外层积分显式为标准(volume:Measure ℝ)，随机characteristic内部仍是显式mu，二者没有混同。此为静态声明/环境审查，不虚称新文件已经elaboration、实现或kernel通过。

STATUS: CORRECT

JUSTIFICATION: 真实增长窗口定义与三个完整类型准确连接同一mu的点态幂极限、在全部v外的eventual共同Gaussian支配及actual Gaussian全积分。每项的连续主体在紧窗口上真可积，再经可测indicator零延拓给真Lebesgue可积，negative delta/n0边界合法；全序列有界层位移只需除sqrt后趋0，固定v最终进入窗口。共同delta先于全部s/d，固定库filter版DCT的eventual可测、共同可积bound和AE点态门均真实满足；实复积分转换及actual S/D/τ²常数正确。未发现需要修订的来源、数学、量词或静态环境缺口。

本票仅批准一定义/三个声明及来源/静态环境，尚非实现/proof/type/kernel票。未读作者未来实现/API笔记、写Lean实现、运行Lean/API探针、重编成功项、改实现/共享文件/旧票/缓存、spawn或commit/PR。未把本中心积分结果视作格点反演、格距归一化、条件Lévy、混合LLT、实际hW或对角闭合；根A/B/C/D全部OPEN。
