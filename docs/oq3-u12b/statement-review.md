# U12b NormalTangentGaussian 独立声明与来源审查

## 第一阶段：仅Lean代码块盲译（先落盘）

本节仅提取twenty-fourth-unit-scope.md的Lean代码块，在读取scope解释、R1对照及本次真实定义/API之前落盘。实测scope SHA256=`b5887ae7c85b81ef3d5acc2a82ecce83702d99f5dcc555cc08541193579756f4`。一个定义、六个完整目标，尚无实现，当前无最终裁决。

定义normalTangentQuadratic(mu,v,s)=S v²+2 C v s+A s²，其中S=actual normalVariance(mu)，C=actual Cov(normalValue,id;mu)，A=actual Var(id;mu)。不是任意抽象矩阵二次型。

1. 任意实际概率mu，若真实AE界|x|≤4+sqrt10，则C=8*parabolaCovariance(mu)00−parabolaCovariance(mu)01。需真实MemLp2支持协方差线性/对称，而非总化方差公式。
2. 同样概率与实际AE界下，S*A−C²=det(actual parabolaCovariance(mu))。这是(Y,X)协方差的真实行列式与(X,X²)矩阵的行列式相同。
3. 同样概率/AE界，再给S>0，则对全部实v/s，Q(v,s)=S*(v+(C/S)*s)²+transverseVariance(mu)*s²。transverseVariance实际定义待核；除S的非零门明确存在。
4. 同样概率/AE界、S>0及D=det(actual parabolaCovariance)>0，对每个(v,s)满足v≠0或s≠0，有Q(v,s)>0。D>0只在这项严格正性中增加。
5. 同样概率/AE界、S>0，对全部固定实s，v↦exp(−Q(v,s)/2)真正Integrable（默认实测度须核为标准Lebesgue）；没有D>0要求。
6. 同样概率/AE界、S>0和任意固定s，全实线真实积分∫exp(−Q(v,s)/2)dv=sqrt(2pi/S)*exp(−transverseVariance(mu)*s²/2)。同样没有D>0要求，需真实平移Gaussian可积后计算。

待核actual Y/Delta/S/tau²定义、MemLp2及双线性前提、变换行列式符号/完整配方、正Q条件、最后两项仅S>0的充分性、默认Lebesgue导入和真实平移Gaussian积分常数。没有Taylor/幂极限、Fourier反演、LLT或根闭合声明；根A/B/C/D仍OPEN。

## 第二阶段：真实来源与定义对应

盲译落盘后读取scope解释、实际R1 238–258及309–345，R1 SHA=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。源239–245给Delta=Cov(X,X²)、sigma²=Var(Y)、tau²=detDelta/sigma²；321–322在混合法向/切向坐标给tau²=detCov(Y,X)/sigma²。本候选第二目标连接两个真实行列式，最后目标对应341–343的Gaussian积分常数；不证明源(15)或实际对数展开/积分极限。

实际FiniteConstraints.lean SHA=`800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0`，normalValue=8x−x²。实际RegularCovariance.lean SHA=`0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853`，Delta=[[VarX,Cov(X,X²)],[同,Var(X²)]]，S=Var(normalValue)，transverseVariance=detDelta/S；其132–155行已审实际normalVariance_eq_covariance在同一概率/hb门下给S=64Delta00−16Delta01+Delta11。当前目标使用这些actual定义，未另造代数替代矩阵或把tau²误作标准差。

## 第三阶段：逐目标独立数学核对

1. hb使id与id²均真实可测且有界，概率为有限测度，故先以MemLp.of_bound建立两者MemLp2（id²的界beta²同时保证真实四阶矩）。8id也MemLp2，Y=8id−id²亦如此。实际covariance_fun_sub_left要求三份MemLp2，正好得到Cov(Y,X)=8Cov(X,X)−Cov(X²,X)；实际covariance_self与covariance_comm给8A−B，其中A=Delta00、B=Delta01。线性/对称符号、系数8和第二坐标方向正确，未把variance.toReal总化当作缺矩情况下的线性公式。
2. 记E=Delta11。由实际S=64A−16B+E及C=8A−B，S*A−C²=A*E−B²=detDelta。这里从(X,X²)到(Y,X)的线性变换[[8,−1],[1,0]]行列式为1，协方差行列式不乘64；候选没有混用VarX与VarY。
3. S>0提供S≠0；代入D=S*A−C²展开配方，S(v+(C/S)s)²+(D/S)s²=S v²+2Cvs+A s²，transverseVariance实际正是D/S。只需已有恒等式和S非零，不需额外D>0或q/a均值门。
4. D>0和S>0给tau²=D/S>0。若s≠0则配方第二项严格正、第一项非负；若s=0则hne迫使v≠0，第一项S v²严格正。这证明完整二维非零向量的Q>0，非仅det>0的未绑定抽象矩阵断言。
5. 固定任意s，以c=(C/S)s、b=S/2>0写exp(−Q(v,s)/2)=exp(−tau² s²/2)*exp(−b(v+c)²)。先用正b Gaussian定理取得真实Integrable，再由实Lebesgue平移保持Integrable，乘固定有限实指数因子仍Integrable。最后两项无需hD：即使tau²=0或仅作为有限实标量，其固定s因子始终有限；没有把二维严格正性偷偷加入一维Gaussian积分门。
6. 在真实可积已建立后，平移不变的全实线积分给∫exp(−b(v+c)²)dv=sqrt(pi/b)=sqrt(2pi/S)。乘上述常数即候选RHS。指数上的1/2、根号上的2pi/S及条件方差tau²都正确。源后续Fourier前因子h/(2pi sqrt(n))若另有真实反演才会产生h/(sqrt(2pi n)sigma)；本候选仅证明这里的Gaussian积分，不将该前因子/极限宣称已实现。

## 第四阶段：固定API、实际默认Lebesgue与可行环境

所有API仅经指定服务器固定mathlib源码只读核对，未运行本单元目标或API Lean探针。

|固定库|实际SHA256与前提|
|---|---|
|Probability/Moments/Covariance.lean|`7f261bcecb104697357f2c51f1c66154153236f3266264ba7c5dd7b8519665fd`；181–183 covariance_fun_sub_left要求有限mu及三份MemLp2，129–140给标量乘法，75–78给对称。|
|Probability/Moments/Variance.lean|`0bcf0e00025e061b358fbde009fc35cd2e6dc28749d724513d08caa76e69415e`；197–201 covariance_self要求实际AEMeasurable，hb下上述MemLp2提供。|
|Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean|`4378f161cf5d482be77941cc9aea0195d2e83fe54eeb51b2ab33db1a318ccb9c`；115–117 integrable_exp_neg_mul_sq要求b>0，210–221 integral_gaussian给sqrt(pi/b)。候选S>0保证真实可积正分支，不借b≤0的integral_undef分支。对应olean实际存在。|
|MeasureTheory/Group/Integral.lean|`63f6cbdfca7878cc6b85825ef2509a7e7ab2129cbf8430e779dd7adc25ed0066`；101–105/138–140的to_additive实际提供积分及Integrable的右加平移接口，条件是add-right invariant测度，真实实Lebesgue满足。这里核的是加法平移，不误用Haar.NormedSpace的非零标量缩放定理。|
|MeasureTheory/Measure/Lebesgue/Integral.lean|`8fa19186f554100cee2b450ba3faef3e84c0407734a3068e442093d2b9ff4ea4`；第8行public import Haar.Unique，缓存olean实际存在。|

针对此前MeasureSpace环境遗漏，这次实际追踪公开导入链，而不是仅按文件名断言：Lebesgue.Integral→Haar.Unique→Integral.DominatedConvergence→Integral.IntervalIntegral.Basic→Measure.Lebesgue.Basic→Haar.OfBasis，均为public import。GaussianIntegral也有独立公开路径经Gamma.Basic/ImproperIntegrals/JapaneseBracket到Haar.OfBasis。实际OfBasis309–319给Real.measureSpace，Basic的Real.volume_eq_stieltjes_id将其volume证明为标准实Lebesgue。故最后两声明的默认Integrable与无显式测度v积分确为同一标准Lebesgue；显式mu下的矩/协方差仍在传入概率mu上。OfBasis/Basic真实SHA分别为`b243e3c02d446de7b0475db5a61405224c298ae134d4fe0e609cf55d5d874d07`、`4955d3400a03ba9d525206fcf1cff8592497dfff06674ca13d68d3bdcabb964d`；Haar.Unique SHA=`243cfd79d72daa1fdc96ae44fbba0b0434e428df6abd0f8d1b8e3c49a72b1016`。

STATUS: CORRECT

JUSTIFICATION: 一个actual定义式及六完整类型与源真实(Y,X)协方差和Gaussian积分步骤一致。hb/probability足以先建立真实MemLp2并合法应用协方差线性，行列式恒等与完整配方正确；D>0仅为Q严格正性所需，最后两个真实平移Gaussian目标确只需S>0。正系数可积性、平移不变性、标准Lebesgue公开实例链及积分常数均已独立核对，未发现关键声明/source或环境缺口。

这是声明/source gate，尚无U12b实现或完整proof/kernel票；本次未写实现、读取作者API/未来实现笔记、运行Lean、重编成功目标、修改缓存或spawn。不使用缺失CLT/Taylor缓存，不声称特征幂极限、Fourier反演、Lévy/LLT、实际hW或根闭合。根A/B/C/D全部OPEN。
