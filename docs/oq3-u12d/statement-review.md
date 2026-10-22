# U12d v2 NormalTangentPowerLimit 独立声明与来源审查

## 第一阶段：仅v2冻结Lean代码块盲译（先落盘）

本节仅提取twenty-sixth-unit-scope-v2.md的Lean代码块，在读取本次scope解释、真实R1、承重前置和固定库之前先落盘。实测v2scope SHA256=`39dd7f63f4b6ff42e3c45516cb6bab093e158cf388836721f178ec77a4528717`。零定义、三个完整目标，当前尚无最终判定。本票只审v2；v1没有本票审查或成功实施历史。

1. centeredNormalTangentCharacteristic_cubic_remainder：任意实际概率mu及真实AE界|x|≤4+sqrt10，q/a为该同一mu下真实EY/EX，固定任意方向v/s后，存在共同正C/delta，随后所有实u在|u|≤delta时，actual中心特征函数在(u v,u s)与复数1−Q(mu,v,s)u²/2之差的范数≤C|u|³。C/delta先于u，可以依赖已固定方向及mu/q/a；没有S/D/Q正性或单位方差归一化门，包含u=0和零方向。
2. centeredNormalTangentCharacteristic_power_tendsto：同一真实概率/AE界/真实q/a均值及任意固定v/s，无S/D/Q正性门，actual中心特征函数在(v/sqrt(n),s/sqrt(n))的n次幂沿自然n趋于复数exp(−Q(mu,v,s)/2)。n=0是序列中的合法总化值，可由最终n≥1处理，不要求逐n正sqrt。
3. finite_atomic_normal_tangent_power_tendsto：固定同一ell/q/p/r/J，若实际约束矩阵非奇异、乘p=target(q)、finiteBase各项非负且全部r非负，则对每个给定v/s，同一actual atomicMeasure(finiteMass ell p r J)的中心q、q/4特征函数sqrt尺度n次幂趋于该同一mu的exp(−Q/2)。无Summable r、ell正性、q区间、S/D/Q正性或额外概率存在性门；需真实有限HasSum及非负质量导出概率和两个实际均值。所有n使用同一mu/参数/中心。

待核固定复指数三阶余项实际范数小球门、所有多项式/余项真可积先于积分、实际中心二阶矩Q、C/delta与u的量词、n>0与sqrt除法、复序列误差相对1/n的真little-o及库幂极限完整类型、退化方向/Q0、有限零延拓J0与任意r、import/作用域/实例。当前只盲译，未读作者API/未来实现笔记，根A/B/C/D全部OPEN。

## 第二阶段：v2冻结范围、真实R1与actual定义

盲译落盘后读取v2scope解释与真实R1 309–345，实测R1 SHA=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。源315、318、335–343给同一mu的EY=q、EX=a及实际中心联合特征函数，在法向t=v/sqrt(n)、切向s/sqrt(n)尺度产生actual联合二次型。这三个声明分别提供点态三阶余项、固定方向的n次幂极限及同一有限源律的实例。R1的正定性还服务后续Gaussian积分/局部极限；本点态幂极限本身不需要正定，v2删除S/D/Q正性是数学上有效的弱化，不是复用未经核查的单位方差路线。

实际前置已只读读取，以下hash本地与真实服务器相同：NormalTangentMoments=`8cee48bc8f519f72b218a2ef80685d946a6debaea8b723af38a49c5bdca12cc1`；FiniteFarArc=`3a0b05d0789e53320009a44499c9c40d0fb3d892427085052c65c04456b6cf71`；NormalTangentGaussian=`d2c55bf4d7a371c9b43cd3c75eab8ece8b3c7caa21aa4827bf19c24b4c7cac39`；FiniteStageMeasure=`1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1`；AtomicMeasure=`59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39`。

actual Y=8x−x²，Z=centeredNormalProjection(q,a,v,s)=v(Y−q)+s(X−a)；FiniteFarArc 21–23的characteristic为∫exp(iZ)dmu。U12c在真实概率/hb/hq/ha下先建立真MemLp2和平方/交叉项可积，再给EZ=0及EZ²=actual Q；Q是同一mu的S v²+2Cov(Y,X)vs+Var(X)s²。U12c完整独立CORRECT票已完成，SHA=`d776f0a101c95cf88869b24e6df9039bdcd99edfd68a9c91d578fddfe0b7fb8f`。U12e完整最终票亦已先交付，SHA=`3f20da936f2d35e0cd9558ccb0d46768dcb28e9434e0b6604031f6cc1cc479b9`；v2拟导入不依赖U12e的正定支配结论。

## 第三阶段：三个完整类型的独立数学核对

### 1. 真AE小球、真可积及共同三阶余项

令beta=4+sqrt10、BY=8beta+beta²。hb给真实mu-AE界|X|≤beta、|Y|≤BY。固定mu/q/a/v/s后，可取

M=1+|v|(BY+|q|)+|s|(beta+|a|)>0，C=M³>0，delta=1/M>0。

真实AE有|Z|≤M。对整个闭窗口|u|≤delta共同成立‖((uZ:ℝ):ℂ)*I‖=|u||Z|≤1，因此实际Complex.exp_bound的范数小球门确实满足，而不是从“u趋0”就假定对整个支撑小。其n=3的有限多项式为1+i uZ−u²Z²/2，真实系数为4/(3!*3)=2/9；于是逐点余项范数≤(2/9)|u|³|Z|³≤M³|u|³。常数C/delta不依赖随后u；u=0也给真实零余项。

积分之前，可先逐项给真Integrable：Z及Z²来自实际有界连续投影/U12c；常数在概率有限measure下可积；它们的实到复嵌入及标量乘积可积；exp(iuZ)连续、全局范数1，真可积；因此完整多项式、差余项及其范数也真可积。随后才合法拆多项式积分及差积分。概率质量1、真实EZ=0、真实EZ²=Q使多项式积分恰为1−((Q u²/2:ℝ):ℂ)，I²=−1决定负号。对余项积分取范数后，以真实AE常数界积分得到≤C|u|³。没有用总化积分/未给可积的Taylor式冒充真实余项，也没有要求支撑在全实轴逐点有界。

这是固定方向的统一u窗口；不声称C/delta同时对全部v/s有效。零方向可取上面的M=1、C=1、delta=1，不需要C=0或除零。actual Q=EZ²≥0，但证明余项和下一幂极限均不以Q或S/D为分母，Q=0同样有效。

### 2. actual复数1/n的little-o及幂极限

令f(n)=actual characteristic_mu,q,a(v/sqrt(n),s/sqrt(n))，t0=((-Q/2:ℝ):ℂ)，u_n=(sqrt(n))⁻¹。最终n≥1，故(n:ℝ)>0、sqrt(n)>0、sqrt(n)²=n，且(n:ℂ)≠0。sqrt(n)→∞给u_n→0，因此最终|u_n|≤delta。先在这些真实正域门之后，将上一目标的余项严格改写为

‖f(n)−(1+t0/(n:ℂ))‖ ≤ C/(n sqrt(n))，即 n‖f(n)−(1+t0/(n:ℂ))‖≤C/sqrt(n)→0。

需要的是实际复little-o，不是仅一个未经比较的O(n^−3/2)标签：对任意epsilon>0，最终C/sqrt(n)≤epsilon；再用n>0除去n，得到‖error(n)‖≤epsilon/n=epsilon‖1/(n:ℂ)‖。这正是固定Asymptotics.isLittleO_iff的全部epsilon/eventual范数门，故error=o[atTop](fun n=>1/(n:ℂ))。t0/n中的符号是负Q/(2n)，不是正Q/(2n)。

实际库Complex.tendsto_pow_exp_of_isLittleO_sub_add_div只消费上述little-o，直接给f(n)^n→Complex.exp(t0)；没有隐藏t0非零、Q正、单位方差、slitPlane或各n概率门。其库证明也只在eventually n≠0后消分母。n=0在整个序列里按实/复除法及零次幂总化合法定义，但不用于推导sqrt或n的消去，有限初值不影响atTop极限。

Q=0时t0=0，仍用同一余项/little-o论证得极限exp0=1；v=s=0时actual相位恒0、characteristic=1，更直接一致。mu/q/a/v/s在取所有n之前固定，不让均值、律或方向随n变化。本目标是每个固定v/s的点态幂极限，不是对增长频率窗口的统一极限。

### 3. 同一实际有限律实例与J0

FiniteStageMeasure 18–61的actual finiteMass在同一AtomicIndex上保留finiteBase与j<J的r(j)，未来全0。hM/hc通过真实有限补偿及有限支撑HasSum证明给全部四约束；hp/hr只需非负，给整个权重非负。第0约束给真HasSum1，因此actual atomicMeasure(finiteMass ell p r J)是真实概率。U12c 104–119从同一约束取得id真可积且EX=q/4、X²真可积且EX²=q，再合法积分Y=8X−X²取得EY=q，同时有真实AE界。以这些同一mu/中心门实例化目标2即可。

任意r仅前J项参与，所有finite feature序列真可和，不要求Summable r或ell正性；J=0时新增和为空、future权重全0、finiteBase=p，概率/均值/幂极限论证不变。允许零权和退化协方差。q是给定实际可满足约束下的条件参数，未声称任意q存在合法概率；没有改选p/q、引入另一源族或混用原律P的EX=0。所有n保持同一ell/q/p/r/J和同一actual Q。

## 第四阶段：实际固定库与静态环境门

只在指定服务器只读实际源码及已有olean，未运行Lean、API探针或作者探针记录。mathlib实际git HEAD及manifest rev均=`807d3836b165983210ee2ecf3cd28f239436949c`，lean-toolchain=`leanprover/lean4:v4.36.0-rc1`。真实run scope.md与本地v2scope实测同SHA=`39dd7f63f4b6ff42e3c45516cb6bab093e158cf388836721f178ec77a4528717`。

|固定源码/API|独立核对的实际条件及SHA256|
|---|---|
|Analysis.Complex.Exponential 377–379|Complex.exp_bound要求‖z‖≤1及自然数n>0，给norm余项≤‖z‖^n*((n+1)/(n!*n))。n=3时真系数2/9。`35d9f9e6abaf24d09a25cb1eeefbfc4180c3fe18de4d47362704c2f9f6601146`|
|SpecialFunctions.Complex.LogBounds 371–380|定理完整类型为对任意t:ℂ，若(fun n=>f(n)−(1+t/n))=o[atTop](fun n=>1/(n:ℂ))则f(n)^n→exp(t)；不附加非退化或正性门。`d3711d5d5b528b8d1733d531d5ae78bc77d13a68079a7243af3251abc48380f7`|
|Analysis.Asymptotics.Defs 169–183|little-o等价每个epsilon>0最终有‖error‖≤epsilon‖比较序列‖；当前比较序列确为复数1/n。`68ef9c1b2d13f99770bcd0c679a23f078f634ea344ff914d7d634ba1682104ed`|
|Bochner.Basic 970及线性积分；Bochner.ContinuousLinearMap 163|范数积分上界、实到复积分转换可用；数学论证另先提供余项及多项式真可积，不依赖总化分支。SHA分别`66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670`、`272fbf423443f1cd4aa032396f85a19c2f4f80b9fe9df655de16b0df655a22c3`|
|Analysis.Real.Sqrt 139、177、285|sqrt在atTop趋∞；sq_sqrt需非负，sqrt_pos需严格正；最终n≥1可真实满足。`1f19e1d6722b2f51c2cd676d0b28ede856c7915ac815b597cef4b3919040c204`|

LogBounds位于`@[expose] public section`，其olean实测存在（62744 bytes）；拟导入的NormalTangentMoments/FiniteFarArc已有olean，Complex.Exponential及Asymptotics.Defs olean亦存在。独立遍历真实public import边确认Complex.Exponential经FiniteFarArc→JointNonlattice→Complex.Log→Log.Basic→Exp→Complex.Trigonometric到达；Asymptotics.Defs经LogBounds的公开Integrals.Basic链到达。故既有exp余项与little-o定义不依赖读取作者API笔记或新缓存。

namespace Shao.OQ3、open MeasureTheory Filter及open scoped Matrix满足实际积分、Tendsto/atTop和第三目标*ᵥ记号；所有随机积分显式带同一mu，默认Lebesgue不会取代它。候选不依赖CLT/Taylor额外缓存，也不依赖U12e正定性接口。本票为静态声明/环境门，未虚称这三个新目标已经Lean elaboration、实现或kernel通过。

STATUS: CORRECT

JUSTIFICATION: v2三个完整类型与真实来源的中心sqrt尺度特征幂极限相符。实际有界投影给整个统一u窗口的真AE复指数小球、真可积多项式/余项及C|u|³界；真实EZ=0/EZ²=Q给正确二阶系数。最终n>0后，三阶界满足固定库要求的实际复数1/n little-o，从而可使用任意复t的幂极限定理，Q0/零方向无需非法归一化。有限四约束与非负零延拓给同一实际概率及EX=q/4/EY=q，J0和任意r无需Summable；静态导入、作用域、实际库条件与缓存均可支持该声明。未发现需修订的数学、量词、来源或静态环境缺口。

本票仅审v2声明/source与静态环境；v1原候选未读取、修改或视为已审实现。未读取作者API/未来实现笔记，未写Lean实现、运行Lean/API探针、重编成功项、改共享文件/旧票/缓存、spawn或commit/PR。未证明积分极限交换、DCT、Fourier反演、条件Lévy、混合LLT、实际hW或对角闭合；根A/B/C/D全部OPEN。
