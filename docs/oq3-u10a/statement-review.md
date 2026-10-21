# U10a GaussianBoundaryConstant 独立声明与来源审查

## 第一阶段：仅Lean代码块盲译（先落盘）

本节只读取twenty-second-unit-scope.md的Lean代码块，在读取其解释、R1对应行和本次固定库API之前落盘。实测scope SHA256=`e294a49d155254fb3f375e6f04251fdaa51e03143c0fde0c4471c66212c56ba2`。三个定义、五公开目标，尚无实现。本节不作最终裁决。

三个实际候选定义：

1. gaussianBoundaryWeight(kappa,d)是关于Lebesgue测度的限制积分：在所有满足−(z/kappa)²≤d的z上，积分标准高斯密度exp(−z²/2)/sqrt(2π)。定义本身任意实kappa/d总化，正高斯边界解释待kappa>0门。
2. gaussianBoundaryProfile(ell,kappa,d)=exp(−ell*d)乘上述权重。
3. boundaryKappa(q,mu)=sqrt(q)/(4sqrt(transverseVariance(mu)))；真实transverseVariance含义待对照现有定义，不把它预先当标准差。

五个完整目标：

1. 对全部kappa>0和任意实d，weight在d≥0时等于1；d<0时等于2/sqrt(2π)乘exp(−z²/2)在开半线z>kappa*sqrt(−d)上的积分。严格开端点须靠高斯无原子/单点零测度与原定义闭不等式对应。
2. 对全部ell>0、kappa>0且2ell<kappa²，profile作为实d的函数真正Integrable（默认实Lebesgue测度）。
3. 同样正域下，真实全实线积分∫profile(d)dd=kappa/(ell*sqrt(kappa²−2ell))。并非仅定义形式或总化积分；需前一目标的真实可积与适当Fubini/Tonelli依据。
4. 对任意实q>0及任意Measure ℝ的mu，只要S=actual normalVariance(mu)>0和D=det actual parabolaCovariance(mu)>0，就有boundaryKappa(q,mu)²=qS/(16D)。类型没有概率/可积假设；是否仅为已定义tau²=D/S的纯代数恒等式待核。
5. 对ell>0、q>0、S>0、D>0和actual R=S−(32ell/q)D>0，(1/sqrt(S))*∫profile(ell,boundaryKappa(q,mu),d)dd=correctedInverseScale(ell,q,mu)。类型仍对任意mu；应从这些实际正标量门导出kappa>0及2ell<kappa²，并将高斯积分常数正确化为实际校正逆尺度。

待核真实标准高斯归一化、对称两尾及开闭边界，联合/迭代积分的实际可积性，正域和常数2/4/16/32，R1(20)对应及真实S/D/transverseVariance/correctedInverseScale定义。无LLT或根闭合声明；根A/B/C/D仍OPEN。

## 第二阶段：实际来源、定义与固定库

盲译落盘后读取scope全文、真实R1 411–444及现有定义。R1实测SHA256=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`：413–421定义g(d)=1（d≥0）或2个标准高斯右尾（d<0），kappa=sqrt(q)/(4tau)，F=exp(−ell d)g；431–443的(20)恰为(1/sigma)∫F=kappa/(sigma ell sqrt(kappa²−2ell))=1/vcorr及kappa²=q sigma²/(16detDelta)。当前目标与这项完整连续高斯积分对应，不包含源(19)的有限层LLT极限。

实际RegularCovariance.lean SHA256=`0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853`，20–30行定义Delta=[[Var(X),Cov(X,X²)],[同,Var(X²)]]，S=Var(normalValue)，transverseVariance=D/S。因此transverseVariance为tau²，候选分母4sqrt(transverseVariance)确为4tau，没有误将tau²直接作标准差。实际CorrectedScaleContinuity.lean SHA256=`b0391976b809b37b1d0d3cb591c2fc89c9291538e8bc9193db70dd2b1504a2a8`，20–22行定义correctedInverseScale=(ell sqrt(S−32ell D/q))⁻¹，常数及正号与源一致。这两份是已完整独立审查的实际定义，不另造替代协方差或尺度。

指定服务器固定mathlib源码与缓存只读核对如下（未运行本单元或API Lean构建）：

|固定库源码|实测SHA256及实际接口|
|---|---|
|Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean|`4378f161cf5d482be77941cc9aea0195d2e83fe54eeb51b2ab33db1a318ccb9c`；115–117 integrable_exp_neg_mul_sq要求b>0；210–221 integral_gaussian给∫exp(−b x²)=sqrt(pi/b)。后者对b≤0的实现会用integral_undef，故本单元必须实际消费正b而不能仅套总化等式。|
|Analysis/SpecialFunctions/ImproperIntegrals.lean|`1527f79047df49f816995ad879a8cfa9e6655f8c8a2c1e0342bf780890a894e7`；77–80 integrableOn_exp_mul_Ioi要求a<0；102–107 integral_exp_mul_Ioi给右半线积分−exp(a c)/a。|
|MeasureTheory/Integral/Prod.lean|`8ccfbcad5fffde3f8d0dfa3167b80dacfb524bc10790f1744b8b8a9b3f4c3a05`；230–243 integrable_prod_iff及对称形式要求联合AEStronglyMeasurable、几乎处处切片Integrable及切片范数积分真正Integrable；443–483 integral_prod/integral_integral_swap必须先有联合Integrable。|
|MeasureTheory/Integral/Bochner/Set.lean|`e4d90b9fde463a9123e1ac3321ce25c0714e19ce92e172f297e062d9de16be75`；689–721的Iic/Iio及Ici/Ioi积分相等由端点零测或NullSingletonClass支持。实Lebesgue满足此门。|

前三项对应的指定服务器olean均实际存在。本审查没有把“缓存可导入”当作本单元已证明。

## 第三阶段：五个目标的独立数学核对

1. 标准密度phi(z)=exp(−z²/2)/sqrt(2pi)为正且真实Integrable：取高斯系数b=1/2>0，再除以sqrt(2pi)>0；固定Gaussian积分为sqrt(2pi)，所以整体积分确为1。d≥0时−(z/kappa)²≤0≤d，边界集合就是全集，含d=0。d<0时a=kappa sqrt(−d)>0，闭边界集合恰为Iic(−a)∪Ici(a)；两半线不交，真实高斯可积允许拆积分。Lebesgue反射保持及密度偶性使两项相等，端点单点零测把Ici(a)换成Ioi(a)。故目标中的2/sqrt(2pi)与开右尾均正确，未丢闭端点质量。
2. 对ell>0、kappa>0、2ell<kappa²，考虑非负联合核H(z,d)=phi(z)exp(−ell d)1{d≥−(z/kappa)²}。边界为连续实函数不等式的闭可测集合，核联合可测。固定z时下限c=−(z/kappa)²，d切片是常数乘exp(−ell d)在Ici(c)上的限制，先由ell>0的指数半线可积性及端点零测得到真实Integrable，其范数积分等于phi(z)exp(ell(z/kappa)²)/ell。该z函数恰为exp(−b z²)/(ell sqrt(2pi))，b=1/2−ell/kappa²>0，是真正Integrable的高斯。因此integrable_prod_iff可先证明联合H Integrable；没有先使用尚无可积前提的Bochner交换。联合可积的另一边缘积分正是profile，故第二公开目标真实成立。仅“每个切片可积”本身不够；这里范数边缘高斯可积亦已独立建立。
3. 在已建立的联合可积基础上Fubini换序，积分等于(1/(ell sqrt(2pi)))∫exp(−b z²)dz=sqrt(pi/b)/(ell sqrt(2pi))。b>0及kappa>0使所有根号分母正；2b=(kappa²−2ell)/kappa²，正确取正根后为kappa/(ell sqrt(kappa²−2ell))。这验证完整实线profile积分，非仅有限d或一侧积分，亦非数值近似。
4. 对任意mu，hS>0、hD>0使tau²=D/S>0，hq>0使候选kappa>0。直接平方真实定义，使用sqrt(q)²=q、sqrt(D/S)²=D/S及非零分母，得kappa²=q/(16(D/S))=qS/(16D)。这是实际已定义标量的纯代数结论，不要求mu另有概率/可积结构；签名没有错误省略概率门，也没有据此无条件宣称任意mu满足正域。
5. hR>0并结合q,D>0给kappa²−2ell=qR/(16D)>0，因此第三目标的hgap真实满足。ell、sqrt(S)、kappa、sqrt(kappa²−2ell)、sqrt(R)均严格正，不能只平方后忽略符号。用kappa²=qS/(16D)与差值恒等式，正数kappa/(sqrt(S)sqrt(kappa²−2ell))的平方为1/R，故它等于1/sqrt(R)；再除ell，恰为actual correctedInverseScale。常数16与32一致，未遗漏sigma=sqrt(S)因子。真实S/D来自当前mu，候选未另选源族p/q/r；已有U7/U11d的实际合法原子律可提供正前提，但本目标只消费它们，不扩张成普遍概率断言。

STATUS: CORRECT

JUSTIFICATION: 三个定义和五个完整目标与真实R1(20)一致；标准高斯归一化、闭边界两尾、联合可积先于Fubini、积分常数及实际协方差/方差正域均有完整数学依据。kappa使用sqrt(tau²)，由R>0推出所需高斯gap，所有平方根与逆的正分母和正根符号可落实，未发现关键声明/source缺口。

本票仅为独立声明/source gate；尚无U10a实现、目标构建或完整proof/kernel裁决，本次没有写实现、运行Lean或读取作者API/未来实现笔记。不是有限阶段LLT、源(19)全层极限、尖点Euler–Maclaurin、实际hW或最终反例；根A/B/C/D全部OPEN。
