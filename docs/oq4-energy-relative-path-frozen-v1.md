# OQ4 E3 下一有限叶：同一中心参数的全n乘法路径约化冻结 v1

STATUS: FROZEN_PENDING_STATEMENT_REVIEW
E3_STATUS: OPEN
ROOT_STATUS: OPEN

来源：固定oq4/energy01.md式7/8及第81–83行相对传输，sourcecommit35d4580b61e22e7145f47730045a09874ef93259，源SHA2562e0387f0a35ca677853e45fff271cc2fb0e87db9ee9c6b2f00d3bcf56b51d9e6。候选intake049bebe6d0551a1cf37dff4f5ebbbd7a17daae9ac83fa541169abec4a754de6c仅为侦察，不是本冻结认证。

拟新Shao/OQ4/EnergyRelativePathBounds.lean。使用既有真实energyTiltedLaw、energyLinearTiltLaw、energyNormalizer、energyLinearNormalizer、实际Measure.pi/closedStrip/energy/prefixSum与两条有限路径身份，禁止重复造假设密度/抽象概率。E2 endpoint与EnergyLinearPathLaw两前置全部final gate通过前不启动本叶作者proof或实施；当前只作源语义门。

## 对象、共同常数与冻结前提

先固定M,T≥0，P=energyE1Constant(T)，C=energyE2Constant(M,T)，H=energyE2Threshold(M,T)，这些对象仅依赖M,T。随后对全部实Borel概率ν，原square/cube真正可积、单位原点二阶∫x²dν=1、原均值∫xdν=0、实际β=∫|x|³dν≤M；对全部h≥H、|s|≤T，令

μ=energyTiltedLaw ν h s，Z=energyNormalizer ν h s，

L(t)=energyLinearNormalizer ν h s t，μ_t=energyLinearTiltLaw ν h s t。

概率性、h≥1、Z/L正性、矩与指数真可积性、E1适用阈值和各估计均由已认证接口内部供应。没有原ν有界支持、指数/第四矩、密度/对称/非格点或生存概率正性新条件。

对n∈ℕ含0，实际路径空间Path n=Fin n→ℝ，A_n=closedStrip(n:=n) h，Q_n=energy，S_n=prefixSum n，Π_n(λ)=Measure.pi(i∈Fin n↦λ)。令

p_n=(Π_n(μ)).real A_n，pθ_n=(Π_n(μ_θ)).real A_n，

I_n=∫a (if a∈A_n then exp(s*(Q_n(a)−(n:ℝ))/h²) else0)dΠ_n(ν)。

I_n是原ν下真正可积的能量加权积分，s≠0时不可误称为原ν无权生存概率。

## 全部有限结论与同θ量词

总入口必须内部调用E2，从真实ν,h,s选出同一个θ，返回该θ的完整energyE2Conclusion（真实μ_θ概率/支持/三可积矩、实际均值零与同常数四界），并且对所有n同时供应以下结论。θ在n之前选择，不能每n重新选θ，也不要求唯一性或可测/连续选择。允许任意满足实际E2估计的θ作辅助引理，但存在型源绑定入口不可删成外部θ前提。

定义透明误差

ε2(M,T,n,h)=C/h+C*(n:ℝ)/h⁴，

ε(M,T,n,h)=P*M*(n:ℝ)/h³+ε2(M,T,n,h)。

它们非负，并对所有n有：

1. 保留源L幂的有限终点夹界

exp(−C/h)*L(θ)^n*pθ_n ≤ p_n
≤ exp(C/h)*L(θ)^n*pθ_n。

2. 吸收真实L幂后的有限乘法夹界

exp(−ε2)*pθ_n ≤ p_n ≤ exp(ε2)*pθ_n。

3. 原ν能量加权积分真正可积，且

exp(−ε)*pθ_n ≤ I_n ≤ exp(ε)*pθ_n。

这些结论没有除以p_n或pθ_n。L(θ)^n=exp((n:ℝ)*log L(θ))必须由真实L>0合法推出；式7的因子必须先精确写成

exp(−s*(n:ℝ)/h²)*Z^n
=exp((n:ℝ)*(log Z−s/h²))，

再用E1实际β误差及β≤M支付P*M*n/h³，不可有限h时把该因子设为1。线性端点使用同一绝对closedStrip事件内|S_n|≤h，不能以n*mean粗移边界。

可将三组夹界合并结论，或保留必要helper。实际Lean公开声明数据最终源码测量，不把条目数机械计成独立原始目标。有限身份、可积性或E2总入口的重复调用不额外计为新原始概率义务。

## 真实iid版本

沿既有iid_samplePath_map_eq_pi，对任意概率空间及可测/iIndepFun/逐坐标IdentDistrib为原ν的有限族X，原I_n integrand(samplePath X)真正可积、实际积分等于I_n，故同一乘法夹界适用。若p_n或pθ_n写成真实样本概率，分别使用μ或同一μ_θ边缘的完整iid环境和既有map桥；可在不同概率空间，不要求新增耦合或一个样本族同时有两个边缘law，不使用生存条件下独立性。可直接复用既有正式iid路径结论，不重证共同基础。

## 边界、来源强度与排除范围

n=0时A全集，p_0=pθ_0=I_0=1；误差ε2=ε=C/h可非零，粗夹界仍合法，不擅改误差定义。θ=0、s=0、T=0、h=H、弱闭端点/截断端点原子、全零路径、零生存质量均保留。s=0时μ仍实际归一化截断，不能先把Z^n删除。M<1的分布类可空，不补M≥1。

本叶仅冻结有限共同乘法约化。原源后续联合渐近必须另保留h→∞与n/h³→0；序列极限/exp误差→1作为之后薄推论，不在本叶冒充已证。概率比值→1另需最终正性，不能在0/0处伪称相对结论。本叶不给n/h²→∞、K/Kv、条件能量E4、共同二维算子9/10、随机分母或完整E3/OQ4根；各完整根仍OPEN。

所有Lean/重计算仅指定server，作者唯一emit，独立no-o/fullsource所有getModuleIdxFor?none无namespace/name过滤、所有冻结旧OQ4实际共存，父owner+namespace/传递三公理门；禁sorry/admit/newaxiom/unsafe/native_decide。冻结后证明实例不得改前提、常数、事件或量词。canonical/正式哈希窗口由lead明确协调。
