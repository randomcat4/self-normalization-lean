# OQ4 核幂与有限 iid 闭生存终点 law 冻结 v1

源 current/oq4/b01/proof01.md §1 的K_h^n1(z)=P(τ_z>n)及§6/8中被杀终点law。复用共同 Shao.Path、Shao.prefixSum、Shao.Probability.FiniteIID，以及已合入main9da55787的Shao.Basic.ClosedSurvival；不复制/改写共同定义。

ν为ℝ Borel概率测度，Π_n=Measure.pi(fun _ : Fin n => ν)，n自然数。对h,z任意实数定义局部移位生存事件

S_n(h,z)={a : Shao.Path n | 对每个自然k，1≤k≤n ⇒ |z+Shao.prefixSum a k|≤h}，

和终点E_n(z,a)=z+Shao.prefixSum a n。时0不额外杀死区间外起点，空样本S_0为全集；这与实际P^0(z)=δ_z一致。源域|z|≤h内与源严格离开τ约定完全相同，闭边界/格点原子不去除。

冻结结论：

1. S_n(h,z)为Borel可测集合，E_n(z,·)可测。实际核幂逐行精确满足测度恒等式
   killedIterKernel ν h n z = Measure.map (E_n z) (Π_n.restrict (S_n(h,z)))。
   不是仅总质量、同矩或几乎处处起点结论。对所有n,h,z成立，n0包括空有限乘积law与δ_z。
2. 对任意有界Borel实测试f，P^n(z)下f及Π_n下的截断测试
   a ↦ if a∈S_n(h,z) then f(E_n(z,a)) else 0
   都真实可积，且积分相等。取f=1得到实际killedMass ν h n z = Π_n.real(S_n(h,z))。
3. 若(Ω,μ)任意概率空间，X_i (i:Fin n)均可测、相互独立、各自law为ν（与共享FiniteIID接口相同），则同一核行等于
   Measure.map (ω↦E_n(z,samplePath X ω))
     (μ.restrict {ω | samplePath X ω∈S_n(h,z)})。
   并给出相同有界测试积分与实生存概率等式。不重新证明共享的iid_samplePath_map_eq_pi。
4. z=0且h≥0时，S_n(h,0)与共同Shao.closedStrip h逐点相同；从而Π_n及任意上述iid样本的闭strip生存概率等于killedMass ν h n 0。保留n0/h0/全零路径及整数端点。

ν无需中心、方差、矩、密度、非格点或有界支持。不得用生存条件后的错误独立性；证明应通过未条件化有限乘积拆分与真实核组合，再把共同iid联合law推送过来。所有测试函数积分须有实际可积性，不能依赖不可积默认0。

该单元关闭有限核幂与实际iid路径的law连接，不证明O0/R3/R4、Brownian近似、K/Kv、能量分母E1-E6或OQ4。拟Shao/OQ4/KilledPathLaw.lean。作者使用前先由父把已获取的共同main合入新分支；共同文件不改，不自行写缓存。
