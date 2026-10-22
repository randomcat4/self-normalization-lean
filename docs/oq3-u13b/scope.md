# OQ3-U13b：真实基本区间Fourier渐近（冻结v1声明候选）

冻结v1，DECLARATION_REVIEW_QUEUED；尚无独立声明批准、尚无实现，不计已接受节点。拟文件Shao/OQ3/FundamentalFourierAsymptotic.lean，导入Shao.OQ3.CentralFourierIntegral、Shao.OQ3.NormalLayerFourier、Mathlib.Analysis.SpecificLimits.Normed；namespace Shao.OQ3，open MeasureTheory Filter，open scoped BigOperators Matrix，noncomputable section。在U13a完整审查报告由lead全文读取之后，由同一reviewer独立声明审查；批准前不实施。

源R1 report.md309–345，只对法向Y的格点反演。这里拟将真实中心与远弧组合，再消费U13a精确反演；仍不证明条件归一化、Levy、完整混合LLT或hW。

```lean
theorem exists_centralFourierIntegral_tendsto_below (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a : ℝ)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det) (H : ℝ) (hH : 0 < H) :
    ∃ delta : ℝ, 0 < delta ∧ delta < H ∧ ∀ (s : ℝ) (d : ℕ → ℝ),
      (∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M) →
        Tendsto (fun n : ℕ =>
          ∫ v : ℝ, centralFourierIntegrand mu q a delta s d n v ∂(volume : Measure ℝ))
          atTop (nhds (((Real.sqrt (2 * Real.pi / normalVariance mu) *
            Real.exp (-(transverseVariance mu * s ^ 2) / 2)) : ℝ) : ℂ))

theorem stage_fundamentalFourierIntegral_tendsto (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q a : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (s : ℝ) (d : ℕ → ℝ) (hd : ∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M) :
    Tendsto (fun n : ℕ => ((Real.sqrt (n : ℝ) : ℝ) : ℂ) *
      (∫ t : ℝ in Set.Icc (-Real.pi / dyadicMesh J) (Real.pi / dyadicMesh J),
        Complex.exp (((-(t * d n) : ℝ) : ℂ) * Complex.I) *
          centeredNormalTangentCharacteristic mu q a t
            ((Real.sqrt (n : ℝ))⁻¹ * s) ^ n ∂(volume : Measure ℝ)))
      atTop (nhds (((Real.sqrt (2 * Real.pi / normalVariance mu) *
        Real.exp (-(transverseVariance mu * s ^ 2) / 2)) : ℝ) : ℂ))

theorem stage_normalLayerCharacteristic_scaled_tendsto (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q a : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (s : ℝ) (d : ℕ → ℝ) (hd : ∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M)
    (hlayer : ∀ᶠ n : ℕ in atTop, ∃ k : ℤ,
      d n + (n : ℝ) * q = dyadicMesh J * (k : ℝ)) :
    Tendsto (fun n : ℕ => ((Real.sqrt (n : ℝ) : ℝ) : ℂ) *
      normalLayerCharacteristic mu q a (d n) s n)
      atTop (nhds ((((dyadicMesh J / (2 * Real.pi)) *
        (Real.sqrt (2 * Real.pi / normalVariance mu) *
          Real.exp (-(transverseVariance mu * s ^ 2) / 2))) : ℝ) : ℂ))
```

零新定义/三个冻结公开目标签名。第一目标只缩U12e支配窗口，不能从U12f存在半径直接推出更小任意半径的积分极限。第二目标中心部分对实际紧区间换元v=t sqrt(n)，先立真可积并在eventually n>0后消去sqrt；两闭远弧边界重叠只在零体积端点，可用Icc/Ioc AE等式或setIntegral_sdiff分解。U12a只供没有层相位的界，必须显式乘上模长1的实际层相位重新给积分界；共同rho/eta与sqrt(n)rho^n趋零缺一不可。固定s后才选n使s/sqrt(n)进入eta窗口。

第三目标的格点相容仅eventually，需由hrange真实导出单坐标零offset网格，再在hlayer的eventual n上用U13a反演。无格点相容时，中心形式积分的正极限不能自动解释成正层概率。系数暂留h/(2pi)乘实际Gaussian常数，保留其精确来源。任何条件概率须后续先证s0层质量eventually正再归一化，本单元不调用Levy。

已静态核cached Analysis.SpecificLimits.Normed215–217的tendsto_self_mul_const_pow_of_lt_one（0≤rho<1）以及intervalIntegral.integral_comp_div（sqrt n非零）。可用sqrt n≤n+1与两个实际幂极限夹逼远弧；集合分解可用setIntegral_sdiff，紧远弧仅用于给其子集上的共同pointwise界。本冻结对象尚未获独立声明批准，不作为完成结果。根A/B/C/D OPEN。
