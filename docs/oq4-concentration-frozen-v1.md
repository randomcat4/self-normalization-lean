# OQ4 Berry–Esseen 到闭区间集中冻结 v1

源 current/oq4/b01/proof01.md §2 BE、§3 AC与β≥1。严格保留闭区间左端原子，不能用F(b)−F(a)代替P(a≤X≤b)。不引入未证BE作为公理，只把它写为实际CDF误差前提。

冻结结论：

1. 任意ℝ Borel概率测度μ、实L,ε≥0、函数G:ℝ→ℝ，若对所有x,y有|G(x)−G(y)|≤L|x−y|，且对所有x有|μ.real(Iic x)−G(x)|≤ε，则对每个a≤b有
   μ.real(Icc a b)≤L(b−a)+2ε。
   a=b必须保留，此时包含左端原子的质量界≤2ε；μ无需密度或无原子条件。
2. 实际标准正态分布γ=Mathlib gaussianReal 0 1 的Φ(x)=ProbabilityTheory.cdf γ x（等于γ.real(Iic x)）满足全实轴|Φ(x)−Φ(y)|≤|x−y|。可使用松但明确的密度≤1，不需最优1/sqrt(2π)。该项须证明实际γ/Φ，不把比较函数的Lipschitz性当作未实例化前提。
3. ν为ℝ概率测度，y²与|y|³真实可积且∫y²dν=1，则β=∫|y|³dν≥1。允许用逐点3u²≤2u³+1（u=|y|）积分证明，不假设均值、无原子或第四矩。
4. ν满足第三项，t≥1自然数，Π_t为ν的真实有限乘积，C_BE≥0。设实际标准化和的BE型误差前提
   对所有实x，|Π_t.real{a | prefixSum a t/sqrt(t)≤x}−Φ(x)|≤C_BE β/sqrt(t)。
   则对每个实a有实际闭单位区间集中
   Π_t.real{b | prefixSum b t∈[a,a+1]}≤(1+2C_BE)β/sqrt(t)。
   不假定有限样本密度、原子消失或生存条件后独立；标准化和law须从真实可测prefixSum映射构造。由t≥1供应正sqrt分母，不能把t0默认除零混进声明。

源BE本身仅在iid中心单位方差三阶矩类给出；本模块不证明该外部定理。第四项允许比源更一般的满足显示CDF前提的ν，但不能拿该条件式冒称无条件AC。第三项β≥1为独立无条件矩事实。有限样本零路径和分布原子均保留。

拟Shao/OQ4/IntervalConcentration.lean。不证明SP、一侧S、无条件AC/O0/R3R4、B1/Brownian输入、K/Kv或OQ4。标准正态用已钉死Mathlib实际定义；缺缓存只向总协调报模块，不自行改共享cache。
