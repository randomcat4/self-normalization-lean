# OQ3-U16g：实际紧二次倾斜族的统一全实层质量界

冻结v1，DECLARATION_REVIEW_QUEUED，尚未批准或实现。拟Shao/OQ3/CompactTiltLayerMassBound.lean。imports Shao.OQ3.CharacteristicMeasureDomination、Shao.OQ3.NormalLayerMassBound；namespace Shao.OQ3、open MeasureTheory Filter、noncomputable section。零新公开定义、一个公开目标。

来源 current/oq3/proofs/r1/report.md SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，356–360：在每个紧倾斜参数集上，法向Fourier积分有统一C/sqrt n界。本目标直接生产同一真实有限基准mu的实际compact quadratic tilt族上全部真实d的层质量界；这填补U16a只有固定mu的局限，不等于已经完成换测度Chernoff尾事件。

```lean
theorem exists_compact_tilted_normal_layer_mass_bound (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q a : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (K : Set (ℝ × ℝ)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ p ∈ K, ∀ d : ℝ,
      Real.sqrt (n : ℝ) *
        (Measure.pi (fun _ : Fin n =>
          mu.tilted (fun x : ℝ => p.1 * x + p.2 * x ^ 2))).real
          {z : Shao.Path n | normalDeviation q z = d} ≤ C
```

完整类型中的mu是真实固定概率与有限stage支撑，hq/ha是真实基准均值、S/det正性和所有stage原子正质量均是基准mu的实际门。J可以0，K可为空，d是任意实数而不缩为格点，p是整段compact参数。C严格正且eventual n阈值在全部p/d之前；不能从每个p的逐点C(p)/N(p)静默推出共同常数。

每个tilt都是实际Measure.tilted(p1*x+p2*x²)，而不是任意已假定满足质量界的family。必须先由hb、U15a actual quadratic_exp_integrable_of_ae_abs_le和isProbabilityMeasure_tilted给真概率；不可积时tilted=0的总化不能用于证明。actual tilted_absolutelyContinuous mu f给tilt≪mu，将同一个有限stage AE支撑转移到每个真实tilt；无需其真实均值仍是q/a。输出事件的normalDeviation q明确以固定基准q定义，中心改变仅改特征函数相位、法向模量不变，不能给tilted错误附加hq/ha。

U16f（当前尚未实施；须其完整独立final接受后才派本声明门）的共同m>0,m≤1 actual jointCharacteristic模量界，参考u0=v0=0。真实Measure.tilted_const mu0=mu，经已公开centeredNormalTangentCharacteristic_factor及exp纯虚相位norm1，给所有p和所有t同一比较

`norm(phi_tilt_p(t,0))≤1−m*(1−norm(phi_mu(t,0)))`。

不得改用每个tilt的协方差最小值或从未知紧性断言正下界；这里真实m由已接受compact测度下界生产者与U16f产生，不是公开前提。

基准mu已接受Gaussian bound给delta0,c0>0，|t|≤delta0时norm(phi_mu(t,0))≤exp(−c0*t²)。取H=pi/dyadicMesh J>0和delta=min(delta0,H/2)>0、delta<H。令c1=m*c0*exp(−c0*delta²)>0。标准add_one_le_exp(x)乘正exp(−x)给x exp(−x)≤1−exp(−x)；当|t|≤delta时x=c0*t²≤c0*delta²，故

`1−exp(−c0*t²)≥c0*exp(−c0*delta²)*t²`。

共同模量比较再接1−c1*t²≤exp(−c1*t²)，得全部p的同一真实中心Gaussian模界。不额外假定tilted中心或正定，也不使用复积分抵消替代范数积分。

余弧E=Icc(−H,H)\Icc(−delta,delta)包含于真实紧Kfreq=Icc(−H,−delta)∪Icc(delta,H)，0不在其中。基准mu实际stage_far_arc_uniform在hrange/hpos和基本频带门下给rho∈(0,1)；共同rho1=1−m(1−rho)严格在(0,1)，且rho1≥rho因m≤1。全部p在同一E有norm(phi_tilt_p)≤rho1，故真正范数幂积分≤volume.real(E)*rho1^n。不能以只知模1上界得到衰减，不能漏最大span门。

对每个实际tilt，unitphase真Integrable及参数连续给频率范数幂在紧区间真IntegrableOn。中央sqrt n正换元含真实Jacobian；n≥1时norm(phi(v/sqrt n)^n)≤exp(−c1*v²)，真可积Gaussian majorant给同一G=∫exp(−c1v²)；fararc的sqrt n*rho1^n→0在同一N后≤1。真实中央与sdiff积分相加，得同一C1=G+1在全部p前的完整基本区间范数积分界。旧U16a私有连续性/换元/离格点证明不可直接跨模块调用；可在本模块重新给必要标准辅助及完整来源审查，不能改冻结U16a或root公共源。

最后分任意真实d：若d+nq不在hZ，先用每个tilt真实AE stage支撑、有限product AE和stage_sample_normal_layer得实际ENNReal层质量0，再取.real；不得只证明实积分0而误当概率0。若在hZ，调用实际normal_layer_Fourier_identity与normalLayerCharacteristic_zero_eq_mass，消去单位模相位并用norm积分界得到sqrt n mass≤h/(2pi)*C1。h/(2pi)>0保证共同C>0。所有事件/函数真可测和所有积分可积在取范数与积分加减前建立，不能借实积分或ENNReal.toReal的top总化。

已实际只读核固定Tilted.lean：74–75行tilted_const在真实prob门下等于mu；280–281行tilted_absolutelyContinuous对任意mu/f给tilt≪mu；251–252行tilted_tilted要求真exp可积；未来转中心投影tilt到quadratic tilt可另由常数再倾斜恒等式完成，当前输出直接是quadratic tilt族不含那一步。其余源/实际publicAPI均在本lane已接受旧stack，无新cache/rootchar源码需求。必须在前置U16f完整接受后再核实际闭包/缓存并独立审查本完整类型；作者批准前不实施/Leanprobe。

本目标完成的是实际compact tilt族的统一法向层质量上界，尚非单侧尾的正确试验符号、真实iid倾斜换测度、负层(16)/(17)、全局远区gap、完整层和19、LLT/hW/WC/KL或根闭合。无最弱/最优/新颖性主张，根ABCD全部OPEN。不cachewrite/copyroot源码/rebase/merge，不扩大root所有权。
