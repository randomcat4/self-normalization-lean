# U12c NormalTangentMoments 独立声明与来源审查

## 第一阶段：仅Lean代码块盲译（先落盘）

本节仅提取twenty-fifth-unit-scope.md的Lean代码块，在读取scope解释、R1及本次实际前置源码/API之前落盘。实测scope SHA256=`56af302fa669d878206ebed0b2d59830bf528a59c76317b5c7cc9a5c559370ce`。一定义、四完整目标，尚无实现，当前无最终裁决。

定义centeredNormalProjection(q,a,v,s,x)=v(normalValue(x)−q)+s(x−a)，是实际法向/切向的实线性中心投影。

1. 对任意实际概率mu、真实AE界|x|≤4+sqrt10及全部实q/a/v/s，该投影真正MemLp2。q/a未要求均值。
2. 同样概率/AE界下，另给actual ∫normalValue dmu=q、∫id dmu=a，则全部v/s的投影真实积分=0；真实均值门显式保留。
3. 同样概率/AE界及两个实际均值等式下，全部v/s的投影平方真实积分=normalTangentQuadratic(mu,v,s)。需实际平方/交叉乘积可积，不能用总化积分代替二阶矩。
4. 对任意ell/q/p/r/J，若actual constraintMatrix(ell)非奇异、乘p等于target(q)、finiteBase各项非负及全部r各项非负，则同一actual atomicMeasure(finiteMass ell p r J)是真实概率；其EX=q/4、EY=q；对全部v/s，以同一q及a=q/4作中心的投影同时真MemLp2、均值0、平方积分=该同一mu下actual Q。类型无Summable r、ell正性或q区间要求；是给定真实概率门下的条件结论，不声称任意q存在合法p/r。

待核真实投影可测/有界和MemLp2、均值门、actual二阶矩与U12b Q、有限零延拓的真HasSum及正质量、四约束推出真实EX/EY、J0及无Summable r门、始终同一actual有限倾斜律而非另一源族或原律P。根A/B/C/D仍OPEN。

## 第二阶段：真实R1与承重定义

盲译落盘后读取scope解释、真实R1 309–345及实际前置源码，R1 SHA=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。源315、318、335–343要求实际均值中心的法向/切向投影及其联合协方差二次型；本候选只建立真实中心/矩输入，不把它们当作已证明二阶特征展开或LLT。

本审查是在U12b完整最终票已完成上传/hash交付后开启。实际NormalTangentGaussian.lean SHA=`d2c55bf4d7a371c9b43cd3c75eab8ece8b3c7caa21aa4827bf19c24b4c7cac39`，完整独立CORRECT票SHA=`73c6fc3ecd6efc91bf842865ccd9ba1f823e8c1bf42bbbe1637f7f90a47b1bb3`。其Q定义明确是S v²+2Cov(Y,X)vs+VarX s²，不是新任意矩阵。实际FiniteConstraints.lean SHA=`800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0`，Y=8x−x²、四feature=[1,x²−4x,x exp(−ellY),x²]、target=[1,0,0,q]。

实际AtomicMeasure.lean SHA=`59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39`：非负w与HasSum1给真实原子概率，atomicMeasure_ae_bounds对actual固定原子给真实AE上界，atomicMeasure_constraints从每个真实HasSum给feature真正Integrable和积分=target。实际FiniteStageMeasure.lean SHA=`1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1`：finiteMass是同一AtomicIndex上四旧质量加j<J新增质量/未来0，finiteMass_constraints只消费hM/hc、不要求r可和；finiteMass_nonneg消费hp/hr。已读实际有限支撑HasSum证明，未从总化tsum猜可和性。

## 第三阶段：四目标独立数学核对

1. beta=4+sqrt10，有界实际X给|Y|≤8beta+beta²。对任意q/a/v/s，投影是可测连续多项式，并且AE绝对值≤|v|(8beta+beta²+|q|)+|s|(beta+|a|)，是有限实常数。真实概率为有限measure，因此MemLp.of_bound给真MemLp2。亦可用已建立的Y/id MemLp2、可积常数及线性组合得到；不需q/a是均值。
2. hq/ha是实际mu下的两个真均值。上述可积性先支持∫[v(Y−q)+s(X−a)]的逐项积分及常数项；概率mass1后分别为v(q−q)+s(a−a)=0。不能删除hq/ha来声称任意中心投影均值0，当前类型已正确保留。
3. Y−q、X−a均真MemLp2，故其平方以及交叉乘积均真正Integrable；投影平方本身也真可积。合法展开平方并逐项积分，两个中心平方积分为actual VarY和VarX，中心乘积为actual Cov(Y,X)，依赖实际均值等式而非仅符号“中心”。因此得到v²VarY+2vs Cov(Y,X)+s²VarX，按实乘法交换与U12b actual Q完全一致。真实矩前提足够，未暗加D>0、S>0或非零(v,s)，包括v=s=0。
4. 对同一ell/q/p/r/J，hM/hc给全部有限约束的真HasSum；k0的feature1给HasSum(finiteMass)1。hp/hr给整个实际权重非负，因此同一atomicMeasure是真实概率。k3给E X²=q，k1给E(X²−4X)=0；实际有界X使id真正Integrable，故q−4EX=0并得EX=q/4。Y=8X−X²真正可积，再得EY=8(q/4)−q=q。然后以这个同一mu的AE界和两个实际均值实例化前三目标，全部v/s共用该有限概率律。这里是倾斜原子律pi_J，不与originalMeasure的中心化EX=0混用；不调用另一组p/q的存在性族。

有限性边界：r只通过前J项进入finiteBase和finiteMass，未来索引权重恒0，故任意r的有限feature序列都真可和，不要求Summable r或ell≥0。hr/hp仅非负已经足够，零质量/退化二阶型不影响这组矩结论。J0只剩四旧原子且同样HasSum1/约束/概率，所有结论有效。q是给定真实可满足约束下的条件参数；若q不相容，前提没有模型，不是对任意q断言存在合法概率。

## 第四阶段：实际固定库与环境门

固定服务器源码只读核对，没有运行Lean/新API探针：MeasureTheory/Function/L2Space.lean42–54明确MemLp.integrable_sq及memLp_two_iff_integrable_sq（后者需真实AEStronglyMeasurable），SHA=`c5737e32b9b1e2a6a0d04b411244ed90d0fcf25aab0449b51865d39182eb4593`。L1Space/Integrable.lean1074–1077的MemLp.integrable_mul要求HolderTriple p q 1，p=q=2满足，SHA=`d80e3495465030c1accca450935e4bfafcfe31d9b695e17f23ee9cfcea537759`。Covariance.lean44–45为actual中心乘积积分，54–65的covariance_eq_sub明确消费概率和两份MemLp2，SHA=`7f261bcecb104697357f2c51f1c66154153236f3266264ba7c5dd7b8519665fd`；Variance.lean226–228的variance_eq_sub同样需概率及MemLp2，SHA=`0bcf0e00025e061b358fbde009fc35cd2e6dc28749d724513d08caa76e69415e`。这些实际门均由上述真实有界概率/均值条件满足。

拟导入已通过完整独立审查的NormalTangentGaussian并open scoped Matrix，提供实际Q/finiteMass及矩阵记号；本候选全部积分和MemLp都显式带同一mu或实际finite原子律，没有依赖未知默认测度。其传递实际标准Lebesgue实例亦已在U12b核验，但当前随机矩不会被它替换。没有缺失CLT/Taylor缓存或共享cache写入依赖。

STATUS: CORRECT

JUSTIFICATION: 一定义与四完整类型准确绑定实际中心投影、真实可积/均值和U12b actual Q；概率有界门足够建立MemLp2、平方及交叉乘积真可积。有限四约束加非负质量给同一pi_J概率与EX=q/4/EY=q，从而全部投影结论可真实实例化；有限零延拓使Summable r、ell正性、无限严格正质量等额外门均无需添加，J0/零投影/退化情形正确。未发现声明/source或环境关键缺口。

本票仅为声明/source gate，尚无U12c实现或完整proof/kernel裁决；未写实现、读取作者API/未来实现笔记、运行Lean、重编成功项、改缓存或spawn。没有Taylor余项、n次幂极限、积分极限交换、Fourier反演、混合LLT、实际hW或根闭合主张。根A/B/C/D全部OPEN。
