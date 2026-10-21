STATUS: CORRECT
REVIEW_MODE: MATH_ONLY
FORMAL_STATUS: LEAN_NOT_RUN
E3_STATUS: OPEN
OQ4_STATUS: OPEN

# EnergyLinearPathLaw 匿名数学证明独立审查 v1

审查对象为冻结命题 `drafts/oq4/frozen-energy-linear-path-law-v1.md` 与匿名证明 `drafts/oq4/energy-linear-path-law/proof.md`。本审查只判断该证明是否完整推出冻结的有限结论，不修订命题或证明，也不把有限身份认证为完整 E3/OQ4。

冻结文件 SHA256：`54678ca7adbdcfaf007f34b1637693f2b70e6e73a15d69a761bf88f52e601091`；3705 字节。

匿名证明 SHA256：`6cb27fdbecad8c22a2b051a4285d55fde4f4d215b562d4f0b8270752f4618776`；12028 字节。

只读原始来源 `C:/game/shao/current/oq4/energy01.md` 的 SHA256 已核对为 `2e0387f0a35ca677853e45fff271cc2fb0e87db9ee9c6b2f00d3bcf56b51d9e6`，与给定 sourcecommit `35d4580b61e22e7145f47730045a09874ef93259` 的锁定记录一致；本轮未运行 Git。原式8位于第78–83行，审查范围为其冻结的任意实参数有限版本，不含紧随其后的相对渐近断言。

JUSTIFICATION:

1. **实际对象与接口匹配（证明第19–65行）。** 已直接核对 `energy-linear/EnergyLinearTiltLaw.lean` 第9、21行的实际 L 和 μ_t 定义，以及第70、85、102、105行的可积性、界、正性与概率接口。它们全部仅需冻结的 ν 概率、平方真可积及单位二阶矩、T≥0、h≥1、|s|≤T。另核对 `energy-law/EnergyTiltedLaw.lean` 第11、37–55、70–77行，μ 为实际归一化截断能量律，其几乎处处支持确为 |x|≤2h。全实 t 的指数可积性来自这个 μ 的支持，未要求原 ν 的指数矩或有界支持。

2. **实际有限乘积密度成立（第71–111行，式1–4）。** `energy-path-law/EnergyPathLaw.lean` 第70行的 `finitePi_withDensity` 确实以 η 和 η.withDensity(d) 均为概率、d 可测为前提；本稿以实际 η=μ、d(x)=ofReal(exp(tx)/L) 实例化，三个条件均在此前供应。L>0 保证每个实因子正且有限，故有限乘积与 ofReal 交换合法。`FinitePath.lean` 的 `prefixSum_length` 给真实 S=Σa_i，有限指数乘积恰为 exp(tS)/L^n，空乘积也包含。由此推出的 Q=P.withDensity(ofReal D) 使用实际 Measure.pi，没有引入替代路径律或密度假设。单步线性密度的基测度是 μ；原 ν→μ 的能量截断从未在全部路径上被删除。

3. **F_t 对实际 Q 真正可积（第115–136行）。** 实际 `ClosedSurvival.lean` 的 closedStrip 监测 k=0,…,n 的弱闭条件，故 A 可测且在 A 上 |S|≤h。F_t 是可测的非负实函数，且全空间有 0≤F_t≤exp(|t|h)。Q 已为概率测度，因此此处给出有限绝对积分，而不是使用不可积实积分的默认值。P、Q 下的 I_A 亦真正可积。此论证不依赖任何生存质量的正性。

4. **反向换测度无有限性缺口（第140–181行，式6–9）。** L^n>0、exp(tS)exp(-tS)=1 给逐点 DF_t=(1/L^n)I_A；A 外由 F_t=0 仍成立。右侧全空间有有限常数界，故 H=DF_t 在实际 P 下真正可积。式4先应用于可测非负测试 ofReal∘F_t，再以两边已证明的非负真可积性把非负积分转为实积分并取 toReal，得到 ∫F_t dQ=P.real A/L^n。乘以正的 L^n 即为冻结反向身份。全过程唯一除数为 L^n，未除 P.real A 或 Q.real A。

5. **夹界保持同一闭事件（第185–202行）。** 点态界 exp(-|t|h)I_A≤F_t≤exp(|t|h)I_A 的各项均在 Q 下真正可积，故积分单调性给式10。h 来自终点 S_n 的事件内界，没有换成 n h、引入累计漂移或移动绝对部分和边界。零生存质量时，F_t 的积分为零，反向身份推出 P.real A=0，夹界仍成立。

6. **真实 iid 拉回覆盖可积性、积分与概率（第206–270行）。** 已直接核对 `library/Shao/Probability/FiniteIID.lean` 第22、32行：逐坐标可测、iIndepFun、逐坐标对 id 的 IdentDistrib 与两端概率性质，恰好推出 samplePath 可测及实际 map 等于 Measure.pi。本稿第215–224行使用的可积性转移和积分换元与实际 `EnergyPathLaw.lean` 第268行以后所用接口一致；实函数的 Borel 可测性供应所需强几乎处处可测性。对 λ=μ_t，获得 F_t∘samplePath 的真可积性与积分等式；可测事件的 map 公式给真实样本生存概率。对 λ=μ 同样拉回左侧事件质量及 I_A 的可积性和积分。没有要求同一族同时具有两种边缘律，没有添加耦合，也没有把条件生存后的坐标误当独立。

7. **边界与量词完整（第274–280行）。** n=0 时 Path 0 为单点、A 全集、S=0、F_t=1、L^0=1，密度及反向身份均为1；夹界为 exp(-|t|h)≤1≤exp(|t|h)，证明明确区分了该界与身份。t=0 时实际接口给 L(0)=1、μ_0=μ，身份和两界均退化为事件质量。正负 t、h=1、T=s=0、全零路径、重复坐标、原子、端点正质量及零生存质量均由同一逐点论证覆盖。未偷增原均值为零、三阶矩、M/K/θ、方差下界、原支持或指数矩、n/h 条件。

未发现阻断冻结有限结论的关键数学缺口。已核对的 `EnergyPathLaw.lean` 字节版本 SHA256 为 `4feb2d7024c75f6cabeab4f46bf81d5430f70a5d30cc86de8dde3250b3191536`；`EnergyLinearTiltLaw.lean` 为 `63cf342dcbe3cce728a42b283a539b8a56043f74a23f6f888ef94df378dcde78`。

本轮没有读取作者 checkpoint、命题审查报告、其他数学审查报告或其他匿名证明；没有修改冻结文件、证明或 Lean 源。未运行 Lean、服务器任务或重计算，因此本裁决仅为 MATH_ONLY / LEAN_NOT_RUN。完整 E3 与 OQ4 仍为 OPEN。
