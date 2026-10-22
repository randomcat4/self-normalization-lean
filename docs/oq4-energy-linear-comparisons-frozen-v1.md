# OQ4 E2 第三叶：实际线性倾斜的有限矩比较冻结 v1

STATUS: FROZEN_PENDING_STATEMENT_REVIEW
E2_STATUS: OPEN
ROOT_STATUS: OPEN

来源：固定 oq4/energy01.md 第61–64行的同一实际指数族与闭支持指数比较。source commit35d4580b61e22e7145f47730045a09874ef93259，源SHA2562e0387f0a35ca677853e45fff271cc2fb0e87db9ee9c6b2f00d3bcf56b51d9e6。候选独立核对见 translation/energy-linear-comparison-intake-v1.md，其结论仅为候选有效，不代替本次冻结/证明审查。

拟新 Shao/OQ4/EnergyLinearTiltComparisons.lean。只依赖实际第一叶 EnergyLinearTiltLaw（冻结源63cf342dcbe3cce728a42b283a539b8a56043f74a23f6f888ef94df378dcde78）及其原有依赖；本叶不需要导数叶。旧模块/公共文件不改。

## 固定对象与前提

ν为ℝ上的Borel概率测度，原x²、|x|³真正可积，∫x²dν=1；T≥0、h≥1、|s|≤T。沿用实际μ=energyTiltedLaw ν h s、L(t)=energyLinearNormalizer、A1(t)、A2(t)、B3(t)、实际μ_t=energyLinearTiltLaw及m(t)=energyLinearMean。所有实t均在范围。

令m0=∫x dμ，u1=∫|x|dμ，q=∫x²dμ，r=∫|x|³dμ，q_t=∫x²dμ_t，r_t=∫|x|³dμ_t，D=exp(2h|t|)。这只是同一实际测度的透明记号，不是可任意输入的数值或抽象law。

μ和μ_t概率、ae闭支持|x|≤2h、L>0及所需真实可积性，必须由冻结第一叶/N1内部供应。允许省去实际不使用的原第三矩前提形成合法加强，但不得增加原ν有界支撑、指数/第四矩、原中心、M、K、θ、已中心化或方差下界假设。

## 冻结结论：全实t的raw与normalized比较

1. |L(t)−1|≤D|t|u1。
2. |A1(t)−m0|≤D|t|q。
3. |A2(t)−q|≤D|t|r。
4. 0≤B3(t)≤Dr。
5. |m(t)−m0|≤D²|t|(q+|m0|u1)。m(t)与μ_t实际一阶矩的身份由第一叶供应。
6. |q_t−q|≤D²|t|(r+q u1)。
7. r_t≤D²r。

所有积分差/绝对值比较必须沿真正可积性执行，不能依赖总积分默认值。u1可积从μ下id真正可积内部导出。允许合并公开定理或添加必要内部helper；固定数学范围不要求机械一式一声明，公开Lean声明数待最终源冻结时按实际记录。

## 证明义务与边界

在同一μ的ae支持集上，实际证明|exp(tx)−1|≤D|t||x|；乘x和x²分别支付q和r，第三绝对矩分子由exp(tx)≤D支付。归一化须使用L≥D⁻¹>0：分子偏差与原矩乘|1−L|两项均保留，准确产生D²及q+|m0|u1、r+q u1。不能删除归一化产生的额外项。

t=0、正负t、h=1、T=0、s=0、零点/±2h闭端点原子均保留。μ/μ_t的支持不转写为原ν有界支持。

本叶不提供参数导数、共同方差窗口、端点异号、θ存在、精确中心化、所选θ处h⁻⁴ logL或最终E2共同常数。E2/E3/E4/K/Kv/随机分母及完整根仍OPEN。

先独立源语义门，再作者匿名数学证明、独立数学门、实现与独立最终门。所有Lean仅指定server，作者唯一emit新目标olean；全旧OQ4+sourcebody及最终实际共同import，独立no-o/完整source全部getModuleIdxFor?=none声明，父module-owner/传递公理门。禁止sorry/admit/newaxiom/unsafe/native_decide，仅标准三公理。
