# OQ4 E2 第五叶：同一实际线性族的共同中心参数存在冻结 v1

STATUS: FROZEN_PENDING_STATEMENT_REVIEW
E2_STATUS: OPEN
ROOT_STATUS: OPEN

来源：固定oq4/energy01.md第65行，先选K大于初始均值常数的两倍，再取共同大h，端点异号和连续性产生θ。sourcecommit35d4580b61e22e7145f47730045a09874ef93259，源SHA2562e0387f0a35ca677853e45fff271cc2fb0e87db9ee9c6b2f00d3bcf56b51d9e6。候选在translation/energy-centering-intake-v1.md独立核对；本叶只冻结θ存在范围，不冻结后续log/最终E2汇总。

拟新Shao/OQ4/EnergyLinearTiltCentering.lean，只沿既有E1、实际线性law/derivatives、有限比较第三叶及共同方差窗口第四叶。后两者最终门全通过前不写本叶数学proof或实施。本次仅源语义审查。

## 固定常数、对象与共同量词

先固定M,T≥0。P=energyE1Constant(T)，A=P M，K(M,T)=1+4A>0；H_center(M,T)=H_var(M,T,K(M,T))，H_var完整沿第四叶冻结表达式不换。

对全部ℝ Borel概率ν，原x²、|x|³真正可积、∫x²dν=1、∫x dν=0、实际β=∫|x|³dν≤M；对全部h≥H_center及|s|≤T，同时使用同一实际μ=energyTiltedLaw ν h s、L/A1/A2/B3、μ_t=energyLinearTiltLaw ν h s t和m(t)=energyLinearMean。

共同常数在ν/h/s之前固定。没有任意抽象law/mean/variance或未证端点、可微性、连续性、方差下界作为新输入。原id真正可积由矩内供，不加原support/指数/第四矩假设。

## 冻结结论

令a=K(M,T)/h²，内部推出a>0。证明真实端点m(-a)<0<m(a)，特别包含源所需弱异号。端点严格性来自K/2>A和共同窗口导数下界，不来自额外非退化假设。

由已认证导数叶连续性及区间论证，存在实θ∈[-a,a]使m(θ)=0。对同一θ，返回

|θ|≤K(M,T)/h²，

实际μ_θ为概率、ae闭支持|x|≤2h、id/平方/绝对立方真正可积，并且∫x dμ_θ=0。

概率/支持/可积性与真实一阶矩身份必须实际调用既有law接口供应；不是新数学承重节点。θ是同一L与实际密度exp(θx)/L(θ)的参数，不能用另造有零均值的law代替。

可把端点定理、存在定理和实际law结论合并/分开；最终公开Lean声明数按实现记录，不机械按段落计数。允许必要内部MVT接口，但新原始义务是端点异号与存在，不把既有供应重复记节点。

## 区间与边界义务

共同窗口的真实m'=v_t∈[1/2,2]只在[-a,a]使用。MVT/单调比较需实际证明其闭区间连续及开区间可微/导数界前提；任意中间点都须验证|t|≤K/h²。初始m(0)=∫x dμ由第一叶真实t0身份供应，|m(0)|≤A/h²从E1内部推出。不能误把原ν中心化转写成μ中心化。

K已先固定为1+4A，再代入H_var；不能随h选择。T=0、s=0、M小导致空类、h=H_center、原子及弱闭端点保持；θ可为0。没有θ唯一、可测选择、连续选择或全实参数全局严格单调断言。

本叶不证所选θ处h^-4 logL或最终共同二三阶矩估计，不关闭完整E2。该后续范围单列。E2/E3/E4/K/Kv/随机分母及完整根OPEN。

所有Lean/重计算仅指定server，作者唯一emit新目标，独立no-o/fullsource全部getModuleIdxFor?none、全旧模块实际共存，父module-owner+namespace/传递公理门；禁sorry/admit/newaxiom/unsafe/native_decide，仅标准三公理。
