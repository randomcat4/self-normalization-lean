# OQ4 E2 第六叶：所选参数log误差与完整有限E2总入口冻结 v1

STATUS: FROZEN_PENDING_STATEMENT_REVIEW
E2_STATUS: OPEN
ROOT_STATUS: OPEN

来源：固定oq4/energy01.md第45–67行式(5)(6)，尤其第66行logL和第67行最终矩界。sourcecommit35d4580b61e22e7145f47730045a09874ef93259，源SHA2562e0387f0a35ca677853e45fff271cc2fb0e87db9ee9c6b2f00d3bcf56b51d9e6。候选C2/H2经translation/energy-centering-intake-v1.md(8e0def88d233d2a9fd7fa66d426965a18e81134fa2c4b2752ba038287533fbd7)核对，但不代替本冻结或证明门。

拟新Shao/OQ4/EnergyE2Bounds.lean。依赖既有E1/真实linear law/derivatives/comparisons/variancewindow及第五叶真实中心参数存在。第五叶最终门前本叶不写作者proof或实现；当前仅语义门。E3第一叶独立推进。

## 明确常数、共同高度与实际对象

先固定M,T≥0，P=energyE1Constant(T)，A=P M，J=exp(2)，K=1+4A，B=J K(A+6)。沿第四/五叶同一原公式令

H2(M,T)=H_var(M,T,K)=H_center(M,T)，

C2(M,T)=1+K+K(A+2K)+(A+B)+J A。

常数与高度在ν/h/s之前固定，只依赖M,T；不临时按h或θ再选择。可用透明定义引用已认证K/Hcenter/A/B，不能静默换常数。

对全部ℝ Borel概率ν，原square/cube真正可积、单位二阶∫x²=1、原均值∫x=0、实际β=∫|x|³≤M；对全部h≥H2、|s|≤T，始终使用同一实际μ=energyTiltedLaw ν h s、L=energyLinearNormalizer、m=energyLinearMean、μ_t=energyLinearTiltLaw ν h s t。所有概率、L>0、矩真可积、导数与窗口数值内部供应，不作输入。

## 新分析义务：实际logL的h^-4小参数误差

先对每个|t|≤K/h²证明

|log L(t)|≤K(A+2K)/h⁴。

固定u在0与t之间，实际窗口导数m'=v_u∈[1/2,2]和实际m(0)的E1小量给

|m(u)|≤|m(0)|+2|u|≤(A+2K)/h²。

再用真正(logL)'=m、logL(0)=0及MVT（或合法等价积分）得到上式。每个区间点必须实际验证窗口域，t/u为负和等0均须覆盖。不能假设一个未证明的log积分身份/可交换性或把可微/连续/均值小量作为新增前提。

此MVT系数使用较松的2K²支付，源仅要求M,T依赖常数，不声称最优。若采用更紧等价证明可保留本明确上界，不静默改定义。

## 完整有限E2结论的汇总（不作为额外独立原始义务双计）

调用第五叶产生同一θ，返回该实际μθ的概率、ae闭支持、id/平方/绝对立方真正可积、精确∫x dμθ=0，以及同一个C2、H2下

|θ|≤C2/h²，

|log L(θ)|≤C2/h⁴，

|∫x²dμθ−1|≤C2/h，

∫|x|³dμθ≤C2。

二阶从窗口|qθ−1|≤A/h+B/h²≤(A+B)/h（h≥1），三阶从真实归一化比较rθ≤D²r≤J A，θ/log常数逐项由C2覆盖。μθ依然是既有真实密度exp(θx)/L(θ)相对μ的measure，不能另造零均值law或抽象moments。

允许透明结论predicate但只作结论，不得输入。再给固定law推论M=实际β，β≥0内部供应；仍同一law/θ/四界。实际公开Lean数按最终源记录；总入口调用各叶不再计额外原始承重义务。

## 边界与关闭范围

T=0、s=0、θ=0、h=H2、原子/弱闭端点/全零路径可用域保留，不加M≥1（小M共同类可空）。不加原bounded support/指数/第四矩/密度/对称/非格点假设。不声称θ唯一或可测选择，不输出随n的路径相对渐近。

只有所有前置与本叶最终认证后，才可称原source有限一维E2本线LEAN_FULLY_CHECKED，main整合另待root；当前E2仍OPEN。即使未来有限E2关闭，也不关闭E3路径/共同算子、E4条件能量、K/Kv、随机分母或原完整OQ4根。

所有Lean/重计算仅server，作者唯一emit、独立no-o/fullsource全部getModuleIdxFor?none、全冻结旧OQ4实际共存，父全module-owner+namespace/传递公理；禁sorry/admit/newaxiom/unsafe/native_decide，仅标准三公理。
