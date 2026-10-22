STATUS: CORRECT
JUSTIFICATION: 冻结 v1 的三组有限乘法夹界、误差非负性、同一 θ 的完整 E2Conclusion 与真实独立同分布样本版本，均由所给匿名证明在原前提下推出。未发现关键缺口或满足全部冻结前提的反例。

VERIFICATION: MATH_ONLY
LEAN_STATUS: LEAN_NOT_RUN
E3_STATUS: OPEN
OQ4_ROOT_STATUS: OPEN
OTHER_OPEN_ROOTS_UNCHANGED: C1/C2、OQ3、OQ6、p52/p53、RS2。

## 审查范围与输入锁定

本报告为全新隔离的独立关键缺口数学审查，只审冻结命题与所给匿名证明，并核对必要的实际已认证接口。未读取作者 checkpoint、intake、声明审查、其他数学审查推理或其他匿名证明；未修改冻结文件、证明或源文件。未使用服务器、Lean、Git 或缓存操作。本报告不认证任何新增 Lean 实现。

| 输入 | 字节数 | SHA256 |
|---|---:|---|
| drafts/oq4/frozen-energy-relative-path-bounds-v1.md | 5139 | ddc8a054559f6ec4ec423e913bfd4bb8e5a1b78f26bdefc68fbc9e26c49a7660 |
| drafts/oq4/energy-relative-path/proof.md | 19657 | 1432a8270323a3dbfe948d12573fb5bee71afdc04d31256861e691d06506d484 |

匿名证明共 375 行。下文“证明”行号均指该锁定文件。四个主要 KNOWN 接口的实际文件哈希、字节数与证明第 178–181 行逐项一致：

| 实际接口 | 字节数 | SHA256 |
|---|---:|---|
| energy-e1/EnergyE1Bounds.lean | 4591 | 448db6e250307358455e7c8da660ffdb094ddb5a42f0e7e81e9c08c02aa4d39d |
| energy-e2/EnergyE2Bounds.lean | 11643 | 41b7343861549f55ae86cddb514a5ed55612448b1ab0efc1e3bb580182746ca8 |
| energy-path-law/EnergyPathLaw-published.lean | 15247 | 3336b977fbe88ae4c27ff7531ffeec6e14c71508587ac2abae99bf475757a177 |
| energy-linear-path-law/EnergyLinearPathLaw.lean | 18042 | 039ad7326ea9a80e476f50bf3f46dd0078c2c61f6786f15a6d72f3ba0c227afb |

接口路径相对于 C:/game/shao lean/drafts/oq4/。补充只核对实际 TruncatedEnergy、EnergyTiltedLaw、EnergyLinearTiltLaw、EnergyLinearTiltCentering、公共 FiniteIID、FinitePath 与 ClosedSurvival 的所需定义或声明；未以它们的审稿材料替代接口。

## 可核验理由

1. 原对象、量词与前提忠实。证明第 10–27 行先固定 M,T≥0，再取实际实 Borel 概率 ν、真实 square/cube 可积性、单位原点二阶矩、原均值零及实际 β≤M，之后才取 h,s。P,C,H 与冻结第 13 行为同一实际定义，未依赖 ν,h,s,n。原一阶矩由 |x|≤1+x² 与概率性得到真正可积，因此均值零没有利用总定义积分的退化语义。证明第 31–61 行的 w、Z、μ、L、μ_t、closedStrip、energy、prefixSum 与实际定义一致；既未更换事件，也未改用抽象密度假设。

2. 阈值与全部 KNOWN 条件齐备。EnergyE1Bounds.lean 第 14–18 行给出 P≥1；EnergyE2Bounds.lean 第 17–21 行给出 C≥1，第 9 行定义 H 为实际中心化阈值。EnergyLinearTiltCentering.lean 第 23–29 行在恰有的 M,T≥0、H≤h 下，供应 energyLogThreshold(M,T)≤h 与 h≥2；以 h=H 还得 H≥2。故证明第 98、187–193 行确实取得 E1 阈值、h≥1、h>0，无新增高度条件。实际 E1 总入口第 42–47 行与 E2 总入口第 132–136 行的每个条件，均逐一由冻结前提供应。μ 的概率性、真正可积矩与 Z≥1/2 来自完整 E1；真实 L(t)>0 与 μ_t 概率性由 EnergyLinearTiltLaw.lean 第 51–55、70–74、102–114 行的同一基础条件供应，不要求原 ν 的指数矩、第四矩或有界支持。

3. 同一个 θ 与完整 E2 结论得到保留。证明第 189 行仅从实际 energyE2_common_bounds 选一次 θ；n 在第 195 行才作为任意自然数引入。EnergyE2Bounds.lean 第 118–129 行的完整合取包含实际 energyLinearMean=0、μ_θ 概率性、支持、三个真正可积矩、实际均值零、θ 界、log L 界及二阶/三阶矩界，与证明第 119–129 行一致。后续只使用该固定 θ 的界，证明第 312–321 行因而确实得到“存在 θ，完整 E2Conclusion 且对所有 n”的冻结量词。给定任意满足完整结论的 θ 时，同一论证也适用；它没有取代内部存在型入口。

4. 保留 L(θ)^n 的第一组夹界成立。实际 EnergyLinearPathLaw.lean 第 145–153 行直接给出 L(θ)^n exp(±|θ|h) r_n 的同事件夹界；其基础条件均已满足。ClosedSurvival.lean 第 26–27 行确实包括末端 k=n，故 |S_n|≤h。由 |θ|≤C/h² 与 h>0 得 |θ|h≤C/h。证明第 206–230 行使用指数单调性及 L(θ)^n r_n≥0，正确推出 exp(−C/h)L(θ)^n r_n≤p_n≤exp(C/h)L(θ)^n r_n。正负 θ 与 θ=0 均由绝对值界覆盖，未平移闭路径边界。

5. 吸收真实 L 幂的第二组夹界成立。证明第 234–247 行先由 L(θ)>0 合法推出 L(θ)^n=exp(n log L(θ))，再由实际 E2 对数界得到 |n log L(θ)|≤Cn/h⁴。此自然数幂等式涵盖 n=0。令 a=C/h、b=Cn/h⁴，则 λ−a≥−a−b、λ+a≤a+b；第 250–260 行乘 r_n≥0 后连接第一组界，正好得到冻结 ε2=a+b 的双边乘法界。没有把 L 幂先设成 1。

6. 原 ν 的加权积分与 E1 代价正确闭合。EnergyPathLaw-published.lean 第 230–236 行在已满足的条件下，给出真正可积性及 I_n=exp(−sn/h²)Z^n p_n。其第 149–157 行的真正可积性甚至只需概率性、T≥0、h≥1、|s|≤T。证明第 264–277 行的独立有界包络也正确：在闭路径上每个坐标 |a_i|≤2h，故 0≤Q_n≤4nh²；由 s≤T、Q_n/h²≥0、T≥0 得 F_n≤exp(−sn/h²)exp(4Tn)，两种 s 符号均成立。

   第 279–296 行先用 Z>0 精确写成 B_n=exp(n(log Z−s/h²))>0，再由 E1 的真实 β 误差得到 |n(log Z−s/h²)|≤nPβ/h³≤nPM/h³。后一替换的系数 nP/h³ 非负，β≤M 正好支付冻结 d=PMn/h³。由 exp(−d)≤B_n≤exp(d)、p_n≥0 与第二组界，第 298–310 行正确得到 ε=d+ε2 的第三组夹界。积分一直是原 ν 下的实际能量加权积分；s=0 时才专门解释为无权闭事件概率，且仍保留 Z^n。

7. 误差符号、空路径与退化情形覆盖完整。证明第 198–202 行由 P,C,M,n≥0、h>0 得 a,b,d、ε2、ε 全非负。第 359 行对 n=0 保留原误差 C/h，利用空路径空间的单点概率、A_0 全空间与 F_0=1，三组界均成立。第 361 行只用非负质量、正指数与 B_n>0，处理 p_n、r_n、I_n 为零的情形；没有除以生存质量或声称 0/0 比值。第 363–369 行的 θ=0、正负 θ、s=0、T=0、正负 s、h=H、全零路径与 M<1 空分布类均与前面推导兼容。closedStrip 与 energyWeight 都使用弱闭端点，±h 的部分和原子及 ±2h 的截断原子没有被排除。

8. 真实独立同分布版本合法且可分空间。公共 library/Shao/Probability/FiniteIID.lean 第 20–43 行的 samplePath、可测性与 iid_samplePath_map_eq_pi 所需条件，恰为逐坐标可测、iIndepFun、逐坐标 IdentDistrib 和概率性。证明第 325–337 行由该实际映射等式转移 F_n 的真正可积性与积分，也可直接使用实际 energyPathLaw_integral_iid（第 268–291 行）。第 339–355 行对 p_n 与 r_n 分别使用 μ 与 μ_θ 的完整独立同分布环境，符合实际 EnergyLinearPathLaw.lean 第 239–267 行。三个概率空间可以不同，既不要求新增耦合，也不要求一个样本族同时具有不同边缘律；没有使用生存条件下独立性。θ 在这些样本空间和有限族之前已固定。

## 结论边界

本次确认的仅是冻结 v1 的有限同 θ、全 n 乘法路径约化及其真实独立同分布传输。没有新增生存正性、Kv、原分布有界支持、指数矩或第四矩条件。证明第 375 行对比值、序列或联合极限、共同二维算子、E4、K/Kv 以及完整 E3/OQ4 根结论的排除准确；这些完整目标保持 OPEN，其余原有开放根状态不变。数学审查通过不代表新增 Lean 源文件已实现或机械门已运行。
