# OQ4 E2 第四叶：共同有限参数方差窗口冻结 v1

STATUS: FROZEN_PENDING_STATEMENT_REVIEW
E2_STATUS: OPEN
ROOT_STATUS: OPEN

来源：固定oq4/energy01.md第61–64行，特别是先固定K后共同充分大h的一致真实方差区间。sourcecommit35d4580b61e22e7145f47730045a09874ef93259，源SHA2562e0387f0a35ca677853e45fff271cc2fb0e87db9ee9c6b2f00d3bcf56b51d9e6。候选阈值经translation/energy-linear-comparison-intake-v1.md独立核对；候选核对不代替本冻结/证明门。

拟新Shao/OQ4/EnergyLinearTiltVarianceWindow.lean。依赖已认证EnergyE1Bounds、EnergyLinearTiltLaw/Derivatives以及冻结比较第三叶EnergyLinearTiltComparisons（其最终源尚在实施；未通过最终门前不实施本叶）。只用同一实际μ=energyTiltedLaw ν h s、μ_t=energyLinearTiltLaw ν h s t、L/A1/A2/B3与m(t)=energyLinearMean。

## 明确共同常数与量词

先固定M,T,K≥0，令P=energyE1Constant(T)、A=P M、J=exp(2)、B=J K(A+6)、C=A+5J K，

H_var(M,T,K)=energyLogThreshold(M,T)+8(1+A+B+C+K)。

这些是上述明确表达式，不能用未认证的存在常数替换；可用透明定义组织。K在h之前固定；阈值依赖M,T,K，不声称任意K时M,T-only。后续若先选择K(M,T)再代入才可称M,T-only。

对任意ℝ Borel概率ν，原x²、|x|³真正可积，∫x²dν=1、∫x dν=0、实际β=∫|x|³dν≤M；对全部h≥H_var、|s|≤T、|t|≤K/h²，同时返回下述结论。原id真正可积由原矩内部供应，不新增前提。

记同一实际μ下m0=∫x、u1=∫|x|、q=∫x²、r=∫|x|³；同一μ_t下q_t=∫x²、r_t=∫|x|³，m_t=m(t)=∫x dμ_t，v_t=∫(x−m_t)²dμ_t，D=exp(2h|t|)。以上只是实际对象记号，不是任意输入数值或替代测度。

## 冻结结论与内部支付

1. 内部推出h≥energyLogThreshold(M,T)、h≥2与h≥8A、8B、8C、8K；D²≤J。
2. 从E1与β≤M内部推出q≤2、u1≤3、|m0|≤1及r≤A；还须保留实际E1小量|q−1|≤A/h、|m0|≤A/h²供下一步，不把这些结论设作输入。
3. 从比较第三叶内部推出
   |q_t−q|≤B/h²，
   |q_t−1|≤A/h+B/h²≤1/4，
   |m_t|≤C/h²≤1/2。
4. 同一实际μ_t概率及id/平方/中心平方真正可积从已有真实接口供应；用真实身份v_t=q_t−m_t²推出1/2≤v_t≤2。不得把q_t称作方差或假设m_t=0。
5. 可显式返回同一m在t处的HasDerivAt m v_t及数值v_t∈[1/2,2]，导数存在及积分身份必须实际调用已认证导数叶；不能使用形式微分或额外输入可微性。此项是已有导数与本叶区间的接口汇总，不增加新的独立原始义务。

可把上述技术支付合并为少量公开定理，或仅保留必要内部helper；实际公开Lean数在最终源冻结时记录，不机械按这五条计数。不得仅把输入/输出重新包装而省去第2–4项的新数值证明。

## 禁止替代与边界

不增加原ν有界支持、指数/第四矩、对称、密度、非格点、μ已中心化或方差下界等条件。闭支持只在实际μ/μ_t下ae成立。固定K=0、T=0、s=t=0、h=H_var及零/闭端点原子均保留。M<1时符合原单位二阶的分布类可为空，不另增M≥1。所有除法分母正性由h≥2内部供应，不能除以可能为零的A/B/C/K。

本叶不选择K(M,T)，不证端点异号、θ存在/唯一、精确中心化、选θ处h^-4 logL或完整E2常数。后续中心参数仍单列。E2/E3/E4/K/Kv/随机分母及完整根OPEN。

先源语义门；比较第三叶完整最终通过后，才作者匿名数学、独立数学及实现/最终门。所有Lean/重计算只指定server；作者唯一新olean emitter，独立no-o/full-source全部getModuleIdxFor?none、全旧OQ4实际共存，父所有module-owner+namespace/传递公理审计；仅标准三公理，禁sorry/admit/newaxiom/unsafe/native_decide。
