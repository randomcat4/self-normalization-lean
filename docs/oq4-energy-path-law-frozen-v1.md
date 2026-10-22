# OQ4 E3 第一叶：实际能量倾斜的有限路径身份冻结 v1

STATUS: FROZEN_PENDING_STATEMENT_REVIEW
E3_STATUS: OPEN
ROOT_STATUS: OPEN

来源：固定oq4/energy01.md第69–77行式(7)，sourcecommit35d4580b61e22e7145f47730045a09874ef93259，源SHA2562e0387f0a35ca677853e45fff271cc2fb0e87db9ee9c6b2f00d3bcf56b51d9e6。接口只读侦察translation/energy-e3-dependency-intake-v1.md（7446cd3a61d48bde212c6629674c9ed8e82f450d153295e680d46fb0eebec87a）是接续依据，不是证明或最终认证。

拟新Shao/OQ4/EnergyPathLaw.lean，独立于E2方差/θ/中心参数。所有实际对象消费已有共享定义，不重复证明/复制closedStrip、逐坐标界、iid joint-law或共享删除/截断桥。

## 固定对象与前提

参数顺序建议(ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) (T h s : ℝ)，hT:0≤T、hh:1≤h、hs:|s|≤T、原x²真正可积及∫x²dν=1。n允许0。原中心与第三矩不用于此有限身份，允许省去原源可用但未用的条件作合法加强。

使用实际Shao.Path n=Fin n→ℝ，Π_n(ρ)=Measure.pi(fun _ : Fin n => ρ)，实际A=Shao.closedStrip(n:=n) h，Q(a)=Shao.energy a，实际w=energyWeight h s、Z=energyNormalizer ν h s、μ=energyTiltedLaw ν h s。μ概率、Z>0及w可积必须从已冻结TruncatedEnergy/EnergyTiltedLaw内部供应，不作为新前提。T不进入law定义。

定义或透明缩写

Φ(a)=if a∈A then exp(s*(Q(a)−(n:ℝ))/h²) else 0。

## 冻结结论

1. Φ在实际Π_n(ν)下真正可积，且非负；事件与能量的可测性由既有真实接口供应。
2. 真实路径积分身份

∫a Φ(a)dΠ_n(ν)=exp(−s*(n:ℝ)/h²)*Z^n*(Π_n(μ)).real A。

3. 沿既有Probability.iid_samplePath_map_eq_pi的真实环境给iid拉回：任意概率空间(Ω,p)与可测的有限坐标X_i:Ω→ℝ，在iIndepFun和各坐标与原ν的IdentDistrib假设下，Φ(samplePath X)真正p可积，并有同一右端的积分身份。不要给新“假设path law有密度”的替代输入。精确参数形式可适配已认证iid接口，但不得弱化为不同路径事件或不同能量。

有限π密度等式或非负测试式可作为内部证明，也可公开必要辅助结论；不要求为最小范围额外泛化任意law/测试函数。最终公开Lean数按实际源记录，不机械按本段计数。

## 必须实际证明的密度与真可积性支付

必须从真实μ=ν.withDensity(ofReal(w/Z))及实际有限π构造推出其乘积密度/测试身份，不能先定义一个具所需密度的替代path law。对a∈A调用共享abs_coordinate_le_two_mul_of_mem_closedStrip，得每坐标闭截断指示为1、∏w(a_i)=exp(s*Q(a)/h²)，并严格处理归一化Z^n。

不得把上述截断删除推广成全路径空间逐点身份。在A外保留Φ=0。实际0≤Q(a)≤4*(n:ℝ)*h²给全空间有限支配

0≤Φ(a)≤exp(−s*(n:ℝ)/h²)*exp(4*T*(n:ℝ))，

Π_n(ν)概率使常数真正可积。允许等价的真实有限支配路线；不得依赖原ν的未截断二次指数可积，也不得用总实积分默认值制造等式。实际概率质量转real与实/非负积分转换均须交付有限性/真可积性。

## 边界、归属与后置范围

保留n=0：A全集、Q=0、Φ=1、空乘积/0次幂1，两边1；不能借absMax接口增加n>0。保留h=1、T=0、s=0、零路径、Q=0、弱闭端点及原子，不能假定原ν有界支持、密度、无原子、非格点、对称、指数或第四矩。s=0的μ通常仍为归一化闭截断律，不等于原ν。

共享Basic.ClosedSurvival和Probability.FiniteIID及KilledPathLaw只列已实现依赖，不开新原始义务或修改公共源。该有限身份不依赖θ、E2共同方差、K或稀有事件概率正性，不除以生存概率。

本叶不提供线性再倾斜反向式(8)、相对渐近、共同二维算子(9)/(10)、E4能量集中、K/Kv、随机分母或完整E3/OQ4。所有这些仍OPEN。

先独立源语义、作者匿名数学、独立数学，再服务器实现与最终source门。所有Lean/重计算仅指定server；作者唯一emit新目标，独立no-o/fullsource全部getModuleIdxFor?none、全旧OQ4实际共存，父module-owner+namespace/传递公理门；禁sorry/admit/newaxiom/unsafe/native_decide，仅标准三公理。
