# Unit218：有界中心化比较在[1/2,16]的实际装配

## 1. 冻结命题、常数和范围

从已验收的原始C1公开定理original_one_sided_relative_error_iid一次选出其数值rhoStar>0、C1>0。取

    etaF=1/100，epsilonF=min(rhoStar/27,1/8)>0。

对实际iid增量Z，设EZ=0、EZ²=1、|Z|≤B≤etaF√n/x，n≥1、1/2≤x≤16、β=E|Z|³、δ=β/√n，且δx³≤epsilonF。令D_n(x)为同一向量完整实际平方和下的两面弱乘法命中交事件，d(x)为实际Brownian两面命中交事件概率，Psi为字面标准正态尾。目标是存在数值CF>0使

    |P(D_n(x))−d(x)|≤CF δ(1+x)³Psi(x)。

同时得到实际绝对最大值与Brownian绝对最大值的绝对概率误差≤Cδ。本稿所有阈值和事件含端点原子及零能量原样归属。增量无需对称、密度或非格点性。

本稿复用unit214/215数学结论，并消费216完整物理账单、217真实h0截止terminal候选；后两者仍在独审，全部新的形式实现及资格尚未完成。它是完整数学装配候选，不是已有Lean根定理或完整所有x的P_CC。

## 2. 自己的实际预算与合法C1

有界支撑使所有三阶矩真正可积。在x≥1/2时

    (1+x)B/√n≤(1+x)/(100x)≤3/100<1。

因此在同一实际归一化律map(Z↦Z/√n)rho下，truncationF((1+x)z)从未触及截断，精确有

    R_x=δ(1+x)³，R_0=δ，h=4nR_0²=4β²=h0。

这不同于将原始law的预算下界搬到新law；此处每一项均由当前自身rho的真实积分定义。Root正在检查canonical own-law非残差分支，本稿不修改或另实现其共享producer。

又(1+x)/x≤3，故R_x≤27δx³≤rhoStar。这明确推出C1原始适用域中的“实际R_x≤rhoStar”分支，而不是把适用域当成新增分布假设。取p=3，规范产品空间的坐标可测、独立同律，二阶/三阶矩及均值/方差条件均满足公开定理的完整头。对s=±1分别得到

    |P(U_s(x))−2Psi(x)|≤C1 δ(1+x)³Psi(x)≤K1δ，
    K1=C1·17³/2。

U_s是实际正时间有符号弱命中。最后一步只用x≤16、Psi(x)≤1/2；不需要把一个law等同于其反射law。由于δ≤8epsilonF≤1，后续δ²≤δ。

## 3. 任意正阈值的实际半线初始完成

已验收finite_second_scalar_closed_cdf_budget给规范终点W=S_n/√Q（Q=0时定义0）的真实闭CDF误差≤KS R_0=KSδ。对−W也成立：可对真实反射增量律应用同一声明，其均值、方差和三阶矩预算不变；不假定rho对称。

对任意x>0定义实际半线初始函数

    g_x(w)=1−exp(−2x(x−w))，w<x；w≥x时为0。

它在[0,1]内，且精确表示为

    g_x(w)=∫_{−∞}^x 2x exp(−2x(x−t))·1_{w≤t}dt。

密度非负且总质量为1。先由有界性得到实际和Gaussian下的真正可积性；Tonelli后用闭CDF上界，得到|E g_x(sW)−E g_x(Normal)|≤KSδ。阈值原子不改变Lebesgue参数积分，未将CDF端点改成未经控制的跳值。

实际V0^s=1_{Q>0}g_x(sW)。真实布朗桥反射与端点分解给E g_x(Normal)=1−2Psi(x)。已验收original_iid_zero_energy_budget给P(Q=0)≤16R_0=16δ，所以

    |E V0^s−(1−2Psi(x))|≤(KS+16)δ。

这里没有将只允许x≤1的finite_second_analytic_initial_host_gap直接扩域；本节通过真实闭CDF、显式g_x层积分和零能量接口给出完整扩展论证。空间/能量缩放的物理g_x识别来自同一实际半线核，w<x边界处g_x=0与物理完成一致。

对实际严格半线存活A_n^s，它正是U_s(x)的字面补集，包括Q=0时严格存活失败。结合第二节合法C1，得到三域transfer所需的真正初始host gap

    |P(A_n^s)−E V0^s|≤KGδ，KG=K1+KS+16。

## 4. 同一实际截止与三域transfer的所有前提

在三个域中选择同一个ν=κ_h0，h0=4β²>0。已验收energy_cutoff_data明确给IsRevealStoppingRank(κ_h0)及cap≤κ_h0（这里相等）。这是在固定完整路径下的标签揭示停止性，不是宣称最终能量wall构成自然iid停止边界。section可测性来自有限能量比较，三个域的ν相同。

同一实际Brownian Q给半线反射、真实区间空间导数及可测性。已验收actual_halfline_kernel_data和actual_interval_kernel_data在真实BridgeIntervalImageResolved正则接口下提供Measurable FY、导数身份及统一4/√T·(1+|d|/√T)界；没有自由小Taylor或预算前提。所有sourceL/O的真正L1还可直接由这些界和T≥h0的有限rank控制获得，符合qualified source_parts_measurable_integrable的适用条件；不从目标费用反推L1。

Unit216给三域实际保留项与负区间账单B=KBδ，已包含所有rank及同一个实际cap。Unit217给三个域的实际terminal误差E=KTδ²≤KTδ；其未来supremum结论包含截止点本身。第三节给两个半线的G=KGδ。

于是精确消费已验收source_three_domain_overshoot_transfer，使用上述实际F/FY、x>0、h0、真实停止cap和实际积分预算。它给

    EΣ O_U，EΣ O_D≤B+E+G，
    |P(A_n^I)−E V0^I|≤3B+3E+2G。

最后一式取其可测、置换不变、|m|≤1的mask m=1。这里正分离overshoot账单终于被同一个真正停止telescope支付；既不依赖Root的大阈值residual正overshootproducer，也不假定正overshoot已经小。

其点wise signed组合O_U+O_D−O_I≥0保留以前已命中一壁/两壁、区间终点已出界、等号e=0及大能量步全部分支。负区间部分由216独立支付；不把O_I全称非负。完整actualDoubleRetained仍为I−U−D。

## 5. 实际区间初始与绝对最大值

已验收original_iid_actual_interval_initial_cdf_budget的公开头对所有x≥0成立。对本实际规范坐标law、同一个真实Q、R_0=δ，取其无mask边际条款，得到

    |E V0^I−P_B(所有t都满足|B_t|<x)|≤KI0δ。

它包括原始乘积律推前、真实Q_n、零能量、物理sourceValue初始值及完整终点识别；本稿不重复其已经验收的BV或scalar证明。初始值不依赖标签σ，因此其原law边际等于revealLaw期望。

与第四节相加，实际严格区间存活和Brownian严格区间存活的差≤KAδ，

    KA=3KB+3KT+2KG+KI0。

取字面补集，即实际弱绝对最大值事件与Brownian弱绝对最大值事件的差也≤KAδ。实际Q=0时所有前缀为0，弱绝对乘法事件为真、sourceAlive严格存活为假；补集恒等式依然成立，没有将该样本当成概率零。

## 6. 弱双命中与固定阈值的相对形式

实际U_+、U_-的并是弱绝对最大值事件、交正是目标弱双命中。Brownian有同样的集合恒等式；正阈值下一壁命中概率均为2Psi(x)，由反射得到d(x)=4Psi(x)−H_B(x)。用完全相同的真实容斥逐项相减，再用第二节的两个C1界和第五节的绝对最大值界，得到

    |P(D_n(x))−d(x)|≤(2K1+KA)δ=:KDδ。

所有Brownian与实际事件均为原始路径事件；两面命中可发生在不同的正时间，也不固定命中顺序。没有从某个单壁部分有限恒等式声称全根闭合。

最后1/2≤x≤16且标准正态尾严格正、单调，故

    (1+x)³Psi(x)≥Psi(16)>0。

选择CF=1+KD/Psi(16)，即得冻结的|P(D_n(x))−d(x)|≤CFδ(1+x)³Psi(x)。CF虽可很大，仍是先于law、n、x固定的数值常数；固定紧区间论证不要求最优常数，也不把它外推到x>16。

## 7. 承重结论与未闭范围

这份完整数学装配把214的真实闭strip、215已有网格精确对接、216全rank实际retained/负区间账单、217真实κ_h0终端预算和既有C1/初始/transfer接口连接成[1/2,16]的bounded-centered比较。它不需要任何自身预算的正下界，正好覆盖任意小δ的固定阈值段。

正式C2资格仍需当前候选的独立完整审查、必要Lean实现、实际TYPE/FULLVALUE和服务器kernel/all-ownedAX。P_CC还需大阈值own-law非残差及actual residual与新Root实际原律桥接；Root独占共享Probability模块及其nonresidual任务不由本稿替代。原始C1 immutablev85维持既有资格；C2/C12仍OPEN，无本地/服务器Lean、AX、上传或Git发布。
