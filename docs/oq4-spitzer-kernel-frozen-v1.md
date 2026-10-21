# OQ4 BE与原始SP到实际有限核吸收冻结 v1

源 b01/proof01 §3 S/AC、§5 O、§6 R3/R4、§8有限D8的已审接口组合。拟Shao/OQ4/SpitzerKernelBounds.lean，只关闭这些有限概率输入的真实供应链，不证明BE或SP本身。

ν为ℝ Borel概率测度，β=∫|y|³dν。完整前提：id、y²、|y|³真正ν可积，∫y=0、∫y²=1，M≥0、β≤M、C_BE≥0。对每个自然t≥1、每个实x，明确给ν的实际Π_t普通和归一化CDF误差≤C_BE β/sqrt(t)。明确给ν与ν⁻=map(−id)ν各自全部L>0、0<s<1的**原始**Spitzer恒等式，内容与FiniteSurvivalLaplace/ReflectedSurvival冻结一致。不得另给ν⁻-BE、S/AC/O0/R3/R4、生存后独立性、非增性、可和性或所需吸收结论作为假设。

定义数值参数

C_q=1+2C_BE，C_S=sqrt(2)exp(6+3C_BE)，
C_layer=12 C_q C_S M(1+M)，
E=π³M/48+2π C_layer(1+2M)。

冻结目标：

1. 从实际二阶/三阶矩证明β≥1，真实调用ReflectedSurvival已证明的双侧S与闭区间AC。现有Lean谓词的实际参数顺序是iidIntervalConcentration ν β C_q、iidOneSidedSurvival ν β C_S；必须供应这些现有谓词，而非另造概率接口。C_q、C_S非负且只依赖C_BE，不能标为无条件通用数值常数。
2. 对h≥3、m=floor(h²)、每个|z|≤h，内部供应KilledBlockBounds的实际块R3、R4：U_m|r_h|(z)≤E/h³及G_m(z)≤2C_S principalCosine(h,z)+(2C_S M)/h，并真实保持旧接口要求的可测/可积性。r_h、U、G、principalCosine必须是已经实现的实际核对象，不换成抽象序列；允许直接组合既审定理，不重写其证明或公共定义。
3. 再设π(1+M)≤h，自然N≥m，R=exp(π²)，并明确保留非循环smallness
   ((2C_S)R)(E R/h³)N+(2C_S M)R/h≤1/2。
   对每个|z|≤h，以H=2(1+(2C_S)R)R证明
   (a) 全部自然k≤N：0≤normalizedKernelMass ν h k z≤H；
   (b) m≤k≤N：
   |normalizedKernelCosine ν h k z−normalizedKernelCosine ν h m z|
   ≤(E R/h³)(k−m)H。
   k−m取自然差再转实数，与旧KilledBlockBounds/Absorption接口一致，保留k=m、k=0质量和闭域端点。输入中不再有S/AC/O0/R3/R4假设；仅保留明确BE、两份原始SP、矩/高度/时间/smallness。

所有数学前提、常数依赖、有限时间范围应在最终签名显式可见。该模块不证明Brownian B1、长时间极限、4/π、K/Kv、E1–E6、BE/SP或完整OQ4；全部完整根仍OPEN。不改变任何既审源或公共定义。
