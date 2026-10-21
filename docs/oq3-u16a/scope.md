# OQ3-U16a：固定有限模型的统一层质量上界

冻结 v1，DECLARATION_REVIEW_QUEUED，尚未批准或实现。拟 Shao/OQ3/NormalLayerMassBound.lean；imports Shao.OQ3.NormalLayerConditionalLaw、Mathlib.Analysis.SpecificLimits.Normed 及既有六个 tactic 分模块；namespace Shao.OQ3、open MeasureTheory Filter、open scoped BigOperators Matrix、noncomputable section。零公开定义、两个公开目标。

来源 R1 report.md SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，309–343 的中心 Gaussian/远弧模间隙，以及 349–390，尤其390之前的正层 scalar sup_d P(M_n=d)≤C/sqrt n。本单元只给固定真实有限模型、最终所有n和全部真实d的统一质量界；不声称紧倾斜参数集的一致界，更不直接证明(16)/(17)、完整层极限或hW。所有根ABCD OPEN。

```lean
theorem exists_stage_normal_power_norm_integral_bound (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q a : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      Real.sqrt (n : ℝ) *
        (∫ t : ℝ in Set.Icc (-Real.pi / dyadicMesh J) (Real.pi / dyadicMesh J),
          ‖centeredNormalTangentCharacteristic mu q a t 0 ^ n‖ ∂(volume : Measure ℝ)) ≤ C

theorem exists_stage_normal_layer_mass_bound (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q a : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ d : ℝ,
      Real.sqrt (n : ℝ) * (Measure.pi (fun _ : Fin n => mu)).real
        {z : Shao.Path n | normalDeviation q z = d} ≤ C
```

C 与最终阈值可依赖已固定的真实mu/J/q/a及其前提，但全部d在阈值之后；不能对每个d另选阈值。n0不需成立，最终可相交n≥1后使用真正正sqrt及变元替换。hD是明确保留的来源正定前提，用于消费既有二维Gaussian bound，非暗中降成退化模型。hrange/hpos是实际有限stage原子，J0允许，未预先假定终结论或未知局部概率界。

数学路线（未实现）：从真实U12e中心缩放模支配取得delta0,c>0。H=pi/h>0，delta=min(delta0,H/2)>0。对s=0，最终n且所有v在缩放窗口内的模≤exp(-cv²)。真实 centralFourierIntegrand(mu,q,a,delta,0,fun _=>0,n) 可积，其norm亦可积；窗口外为零。以真正 Integrable Gaussian majorant作 integral_mono，得到该norm积分≤G=∫exp(-cv²)，G有限非负。须独立明确验证norm的线性变元替换：该norm积分恰为sqrt n乘中心区间norm积分；不能从复积分极限倒推出绝对积分有界，也不能调用前置private引理。

远区 E=Icc(-H,H)\Icc(-delta,delta)，包含于紧K=Icc(-H,-delta)∪Icc(delta,H)。真实stage_far_arc_uniform给rho∈(0,1)，s0合法，全部t∈E模幂≤rho^n。E真有限测度且norm连续可积，远区norm积分≤volume.real E*rho^n；sqrt n*rho^n→0可由sqrt n≤n+1与两个已缓存标准幂极限作夹逼。因此最终缩放远区norm积分≤1。真实setIntegral_sdiff+实际Integrable把中心和远区相加，C=G+1>0即可，绝不靠不受控相消。

第二目标：同一mu/J的hrange经stageAtom_normalValue_lattice给AE单点正常格点，再经有限产品坐标AE给真实样本支撑。对满足d+nq∈hZ的任意d，真实normal_layer_Fourier_identity在s0给层质量的复积分；normalLayerCharacteristic_zero_eq_mass是实际概率质量，不是conditional零层补定义。所有相位因子模1，连续可积后 norm_integral_le_integral_norm 给质量≤h/(2pi)乘第一目标同一个绝对积分；固定C'=h/(2pi)*C>0统一所有d。若d+nq不在hZ，真实样本格点AE使该层测度真零，须在ENNR测度层面先证零再转.real，不能依赖top.toReal=0或假定离网层不存在。实际pi是概率，全部真实层测度有限，空层/零质量可直接保留。可用private支撑/变元替换/积分引理，不增公开目标。

静态接口依据：既有U12e NormalTangentDomination的exists_centeredNormalTangentCharacteristic_scaled_domination；U12c FiniteFarArc的stage_far_arc_uniform；U12f CentralFourierIntegral的实际可积/indicator定义；U13a Fourier实际身份；U13c零频率质量身份；SampleBoundary.stage_sample_normal_layer给真实有限样本格点。库真实 intervalIntegral.integral_comp_div、integral_indicator/Icc-Ioc转换、norm_integral_le_integral_norm、integral_mono/integral_nonneg、setIntegral_sdiff、integrable_exp_neg_mul_sq、tendsto_self_mul_const_pow_of_lt_one 均已在旧已接受实际导入/缓存中消费。实现前仍要求唯一reviewer声明/source/接口门全文批准；不新拉cache、不复制root源码、不重编译已接受模块。

本单元不把固定mu的C升级为紧倾斜族统一C，不证明局部率二次下界/全局远区间隙/负层Chernoff(16)/(17)、完整层支配、尖点EM或旋转hW。不重复已接受Fourier/LLT节点，不声称新颖性、最弱前提或根闭合。
