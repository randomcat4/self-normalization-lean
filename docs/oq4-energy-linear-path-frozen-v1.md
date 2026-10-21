# OQ4 E3 第二叶：实际线性再倾斜的有限路径反向身份冻结 v1

STATUS: FROZEN_PENDING_STATEMENT_REVIEW
E3_STATUS: OPEN
ROOT_STATUS: OPEN

来源：固定oq4/energy01.md第78–83行式8及其有限夹界，sourcecommit35d4580b61e22e7145f47730045a09874ef93259，源SHA2562e0387f0a35ca677853e45fff271cc2fb0e87db9ee9c6b2f00d3bcf56b51d9e6。接口intake7446cd3a是定位依据，不是认证。

拟新Shao/OQ4/EnergyLinearPathLaw.lean。沿同一真实energyTiltedLaw、energyLinearTiltLaw及实际FinitePath/ClosedSurvival/FiniteIID对象；可复用第一EnergyPathLaw已证明的finitepi密度helper，必须实际证明/实例化，不能将密度当新前提。第一EnergyPathLaw最终门前不启动本叶作者proof/实施，当前仅源语义门。

## 对象与冻结前提

ν为ℝ Borel概率，原square真正可积、单位second；n任意自然含0，T≥0,h≥1,|s|≤T，线性参数t为任意实数。令μ=energyTiltedLaw ν h s，μ_t=energyLinearTiltLaw ν h s t，L=energyLinearNormalizer ν h s t；Π_n为实际Measure.pi，Path n=Fin n→ℝ，A=Shao.closedStrip(n:=n) h，S(a)=Shao.prefixSum a n。所有概率、L>0、指数真可积、路径事件可测性必须内部供应。无原center/cube/M/K/theta/variance/原support或指数矩新假设。

令F_t(a)=if a∈A then exp(−t*S(a)) else0。

## 冻结有限结论

1. 从实际μ_t的真实withDensity定义和有限pi构造推出Π_n(μ_t)相对Π_n(μ)的密度exp(t*S(a))/L^n，允许等价已证明非负测试公式/内部helper；不能另造具有该密度的path law或把身份设为前提。指数乘积等于终点指数，使用真实prefixSum_length。
2. F_t对实际Π_n(μ_t)真正可积，并有精确反向身份

(Π_n(μ)).real A = L^n * ∫a F_t(a)dΠ_n(μ_t)。

3. 给不除生存概率的有限夹界

L^n*exp(−|t|*h)*(Π_n(μ_t)).real A ≤ (Π_n(μ)).real A
≤ L^n*exp(|t|*h)*(Π_n(μ_t)).real A。

4. 沿既有iid_samplePath_map_eq_pi给真实iid拉回：对任意概率样本空间上可测/iIndepFun/逐坐标IdentDistrib为μ_t的有限样本，F_t(samplePath X)真正可积且积分等于上述实际product积分，因而反向身份/夹界可使用真实样本路径。μ侧概率也应可用同一现有map桥拉回，不另造iid密度假设。

可合并公开结论或保留必要helper；实际公开Lean数按最终源记录，不机械按条数计数。

## 真可积、归一化与边界

同一个A内部真实|S(a)|≤h，故exp(−|t|h)≤exp(−tS(a))≤exp(|t|h)，F_t全路径由有限常数exp(|t|h)支配；Π_n(μ_t)概率内部给真正可积。密度转换需合法处理实/非负积分及有限性；用exp(tS)*exp(−tS)=1和L^n>0消去密度时必须实际证明，而不是依赖总积分默认值。

线性密度的指数乘积身份对全部路径成立，因为基础μ已是实际能量law；不能误将原ν的能量截断指示在全部路径上删除。事件始终同一个绝对prefixSum闭事件，不用n*mean粗移边界。

n=0时A全集/S=0/F=1/L^0=1，两侧1；t=0时实际L0=1/μ0=μ，保持真实测度身份。保留正负t、h=1、T=s=0、零路径、弱闭端点和原子。允许零生存概率；本叶不除以任何生存质量，不新增其正性。

不要求t已中心化，不选择theta，不给n/h条件的相对渐近、共同二维算子9/10、E4/K/Kv/随机分母或完整根。E3仍OPEN。

所有Lean/重计算仅指定server；作者唯一emit，独立no-o/fullsource全部getModuleIdxFor?none、所有已冻结旧OQ4实际共存，父module-owner+namespace/标准三公理门；禁sorry/admit/newaxiom/unsafe/native_decide。并行实施的canonical/正式hash窗口由lead协调，scratch可并行。
