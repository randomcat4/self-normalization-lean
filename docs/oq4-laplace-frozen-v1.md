# OQ4 正部Laplace尾积分与S1冻结 v1

源 current/oq4/b01/proof01.md §3 S1，衔接已冻结IntervalConcentration的实际标准正态CDF。该模块只用明确BE型CDF输入推出S1，不证明BE、SP或完整一侧S。

μ为任意ℝ Borel概率测度，L>0，定义A_L(μ)=∫[1−exp(−max(x,0)/L)]dμ(x)。冻结目标：

1. 被积函数真实可积，0≤A_L(μ)≤1，并证明真实尾积分恒等式
   A_L(μ)=∫_{u∈(0,∞)} (1/L)exp(−u/L) μ.real(Ioi u) du。
   右侧相对Lebesgue测度也须真实可积。尾事件严格>u，CDF对应≤u，μ允许任意原子/无界支持且无需μ矩。不能用不可积积分默认0。
2. 实际标准γ=gaussianReal 0 1、Φ=cdf γ满足Φ(0)=1/2和γ.real(Ioi 0)=1/2；不能把高斯中心质量当抽象输入。
3. q≥1自然数、C_BE≥0、1≤β≤L。若对所有实x有实际CDF前提
   |μ.real{y | y/sqrt(q)≤x}−Φ(x)|≤C_BE β/sqrt(q)，
   则A_L(μ)≥1/2−(1+C_BE)L/sqrt(q)。
   保留A_L≥0这一独立界；右侧在小q时可为负，不据此收紧前提或替换成正数。
4. ν为任意ℝ Borel概率测度，Π_q为真实q维有限乘积，以μ=(prefixSum · q)_*Π_q实际实例化，给源A_q=E[1−exp(−T_q^+/L)]的真实可积性、0≤A_q≤1及同一S1下界（产品CDF输入、q≥1、C_BE≥0和1≤β≤L完整保留）。不需要对Π_q作生存条件化，不添加矩/中心/密度/格点前提。

可用加权layer-cake或Tonelli证明尾积分，但必须证明所有可测/可积性质。父已只读确认Mathlib.MeasureTheory.Integral.Layercake缓存存在，包含lintegral_comp_eq_lintegral_meas_lt_mul；Gauss.Real已缓存且有gaussianReal_map_neg与非原子实例可供中心质量证明。具体API由作者读钉死source。

拟Shao/OQ4/LaplaceTail.lean。该单元关闭源S1解析支付和实际有限和law实例，不证明BE/SP、S2/S3、无条件S/AC/O0/R3R4、B1、长时间K/Kv、E1-E6或OQ4。所有根保持OPEN，不改既审源或公共定义。
