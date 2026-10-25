import Shao.OQ6.ConditionalStandardizedLowEnergy

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Shao.OQ6.LogarithmicConditionalLowEnergy

noncomputable section

open MeasureTheory ProbabilityTheory

theorem actual_logarithmic_conditional_low_energy
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun z : Ω × Ω => h z.1 z.2))
    (hh2 : MemLp (fun z : Ω × Ω => h z.1 z.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ z : Ω × Ω, h z.1 z.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (w : Ω → ℝ)
    (hw : Measurable w)
    (hwone : ∀ᵐ o ∂μ, 1 ≤ w o)
    (α τ : ℝ) (hα : 0 < α) (hτ : 0 < τ)
    (hwexp : Integrable (fun o => Real.exp (τ * Real.rpow (w o) α)) μ)
    (henvelope : ∀ᵐ z : Ω × Ω ∂(μ.prod μ),
      |h z.1 z.2 - (∫ y, h z.1 y ∂μ) - (∫ y, h z.2 y ∂μ)| ≤
        w z.1 * w z.2)
    (p : ℝ) (hp : 2 < p ∧ p ≤ 3)
    (hgp : Integrable
      (fun o => Real.rpow |∫ y, h o y ∂μ| p) μ)
    (J : ℝ) (hJ : 0 ≤ J) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let β : ℝ := ∫ o, Real.rpow |g o| p ∂μ
    let q : ℝ := p / 2
    let t0 : ℝ := Real.rpow (1 / (8 * β)) (2 / (p - 2))
    let c0 : ℝ := t0 / 4
    let e : ℝ := 1 - 2 / p
    let A : ℝ := 2 * (J + 1) / e
    0 < c0 ∧
      ∃ Nlog : ℕ, 3 ≤ Nlog ∧
      ∀ n : ℕ, Nlog ≤ n →
      let Rn : ℝ := Real.rpow (A * Real.log (n : ℝ) / τ) (1 / α)
      let Cn : Set Ω := {o : Ω | w o ≤ Rn}
      let ν : Measure Ω := (μ Cn)⁻¹ • μ.restrict Cn
      IsProbabilityMeasure ν ∧
        ∀ m : ℕ, 3 ≤ m → m ≤ n → (n : ℝ) / 2 ≤ (m : ℝ) →
        let lam : ℝ := ((m : ℝ) - 2) / ((n : ℝ) - 2)
        let H : Ω → Ω → ℝ := fun o y => g o + g y + lam * r o y
        let κ : ℝ := ∫ z : Ω × Ω, H z.1 z.2 ∂(ν.prod ν)
        let G : Ω → ℝ := fun o => (∫ y, H o y ∂ν) - κ
        let σ2 : ℝ := ∫ o, G o ^ 2 ∂ν
        let σ : ℝ := Real.sqrt σ2
        let X : Ω → ℝ := fun o => G o / σ
        let Pm : Measure (Fin m → Ω) := Measure.pi (fun _ : Fin m => ν)
        let E : Set (Fin m → Ω) :=
          {o : Fin m → Ω | (∑ i : Fin m, X (o i) ^ 2) / (m : ℝ) < (1 / 2 : ℝ)}
        0 < σ ∧ IsProbabilityMeasure Pm ∧ MeasurableSet E ∧
          Pm.real E ≤ Real.exp (-(c0 / 2) * (n : ℝ)) := by
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
  let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
  let β : ℝ := ∫ o, Real.rpow |g o| p ∂μ
  let q : ℝ := p / 2
  let t0 : ℝ := Real.rpow (1 / (8 * β)) (2 / (p - 2))
  let c0 : ℝ := t0 / 4
  let e : ℝ := 1 - 2 / p
  let A : ℝ := 2 * (J + 1) / e
  change 0 < c0 ∧ _
  have h179Threshold :
    ∃ N0 : ℕ, 1 ≤ N0 ∧
      ∀ R : ℝ, (N0 : ℝ) ≤ R →
      let C : Set Ω := {o : Ω | w o ≤ R}
      let d : ℝ := μ.real C
      let ν : Measure Ω := (μ C)⁻¹ • μ.restrict C
      MeasurableSet C ∧ (1 / 2 : ℝ) ≤ d ∧
        IsProbabilityMeasure ν ∧ ν ≪ μ ∧ ν C = 1 ∧
        ∀ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 →
        let H : Ω → Ω → ℝ := fun o y => g o + g y + lam * r o y
        let κ : ℝ := ∫ z : Ω × Ω, H z.1 z.2 ∂(ν.prod ν)
        let G : Ω → ℝ := fun o => (∫ y, H o y ∂ν) - κ
        let σ2 : ℝ := ∫ o, G o ^ 2 ∂ν
        let σ : ℝ := Real.sqrt σ2
        let X : Ω → ℝ := fun o => G o / σ
        Measurable G ∧ MemLp G 2 ν ∧
          Integrable (fun o => G o ^ 2) ν ∧
          (∫ o, G o ∂ν) = 0 ∧
          (1 / 2 : ℝ) ≤ σ2 ∧ σ2 ≤ (3 / 2 : ℝ) ∧
          0 < σ ∧ σ ^ 2 = σ2 ∧
          Measurable X ∧ MemLp X (ENNReal.ofReal p) ν ∧
          MemLp X 2 ν ∧ Integrable (fun o => X o ^ 2) ν ∧
          (∫ o, X o ^ 2 ∂ν) = 1 ∧
          Integrable (fun o => Real.rpow |X o| p) ν ∧
          (∫ o, Real.rpow |X o| p ∂ν) ≤ 2 * β ∧
          (let f : Ω → ℝ := fun o => Real.exp (-t0 * X o ^ 2)
           let L : ℝ := ∫ o, f o ∂ν
           Measurable f ∧ Integrable f ν ∧ 0 ≤ L ∧
             L ≤ 1 - 3 * t0 / 4 ∧
             L ≤ Real.exp (-3 * t0 / 4) ∧
             ∀ m : ℕ,
             let Pm : Measure (Fin m → Ω) := Measure.pi (fun _ : Fin m => ν)
             let S : (Fin m → Ω) → ℝ := fun o => ∑ i : Fin m, X (o i) ^ 2
             let Fm : (Fin m → Ω) → ℝ := fun o => Real.exp (-t0 * S o)
             let εm : ℝ := Real.exp (-t0 * (m : ℝ) / 2)
             let E : Set (Fin m → Ω) := {o : Fin m → Ω | S o ≤ (m : ℝ) / 2}
             IsProbabilityMeasure Pm ∧ Measurable S ∧ MeasurableSet E ∧
               Measurable Fm ∧ Integrable Fm Pm ∧ 0 < εm ∧
               (∫ o, Fm o ∂Pm) = L ^ m ∧
               (∫ o, Fm o ∂Pm) ≤ Real.exp (-3 * t0 * (m : ℝ) / 4) ∧
               Pm.real E ≤ Real.exp (-c0 * (m : ℝ))) := by
    exact
      (Shao.OQ6.ConditionalStandardizedLowEnergy.actual_conditional_standardized_low_energy
        μ h hh hh2 hhsymm hcenter hprojectionsecond w hw hwone
        α τ hα hτ hwexp henvelope p hp hgp).2.2.2.2.2.2.2
  have hC0 : 0 < c0 := by
    exact
      (Shao.OQ6.ConditionalStandardizedLowEnergy.actual_conditional_standardized_low_energy
        μ h hh hh2 hhsymm hcenter hprojectionsecond w hw hwone
        α τ hα hτ hwexp henvelope p hp hgp).2.2.2.2.2.1
  let NL : ℕ := Classical.choose h179Threshold
  have hNL :
    1 ≤ NL ∧
      ∀ R : ℝ, (NL : ℝ) ≤ R →
      let C : Set Ω := {o : Ω | w o ≤ R}
      let d : ℝ := μ.real C
      let ν : Measure Ω := (μ C)⁻¹ • μ.restrict C
      MeasurableSet C ∧ (1 / 2 : ℝ) ≤ d ∧
        IsProbabilityMeasure ν ∧ ν ≪ μ ∧ ν C = 1 ∧
        ∀ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 →
        let H : Ω → Ω → ℝ := fun o y => g o + g y + lam * r o y
        let κ : ℝ := ∫ z : Ω × Ω, H z.1 z.2 ∂(ν.prod ν)
        let G : Ω → ℝ := fun o => (∫ y, H o y ∂ν) - κ
        let σ2 : ℝ := ∫ o, G o ^ 2 ∂ν
        let σ : ℝ := Real.sqrt σ2
        let X : Ω → ℝ := fun o => G o / σ
        Measurable G ∧ MemLp G 2 ν ∧
          Integrable (fun o => G o ^ 2) ν ∧
          (∫ o, G o ∂ν) = 0 ∧
          (1 / 2 : ℝ) ≤ σ2 ∧ σ2 ≤ (3 / 2 : ℝ) ∧
          0 < σ ∧ σ ^ 2 = σ2 ∧
          Measurable X ∧ MemLp X (ENNReal.ofReal p) ν ∧
          MemLp X 2 ν ∧ Integrable (fun o => X o ^ 2) ν ∧
          (∫ o, X o ^ 2 ∂ν) = 1 ∧
          Integrable (fun o => Real.rpow |X o| p) ν ∧
          (∫ o, Real.rpow |X o| p ∂ν) ≤ 2 * β ∧
          (let f : Ω → ℝ := fun o => Real.exp (-t0 * X o ^ 2)
           let L : ℝ := ∫ o, f o ∂ν
           Measurable f ∧ Integrable f ν ∧ 0 ≤ L ∧
             L ≤ 1 - 3 * t0 / 4 ∧
             L ≤ Real.exp (-3 * t0 / 4) ∧
             ∀ m : ℕ,
             let Pm : Measure (Fin m → Ω) := Measure.pi (fun _ : Fin m => ν)
             let S : (Fin m → Ω) → ℝ := fun o => ∑ i : Fin m, X (o i) ^ 2
             let Fm : (Fin m → Ω) → ℝ := fun o => Real.exp (-t0 * S o)
             let εm : ℝ := Real.exp (-t0 * (m : ℝ) / 2)
             let E : Set (Fin m → Ω) := {o : Fin m → Ω | S o ≤ (m : ℝ) / 2}
             IsProbabilityMeasure Pm ∧ Measurable S ∧ MeasurableSet E ∧
               Measurable Fm ∧ Integrable Fm Pm ∧ 0 < εm ∧
               (∫ o, Fm o ∂Pm) = L ^ m ∧
               (∫ o, Fm o ∂Pm) ≤ Real.exp (-3 * t0 * (m : ℝ) / 4) ∧
               Pm.real E ≤ Real.exp (-c0 * (m : ℝ))) := Classical.choose_spec h179Threshold
  have hEPos : 0 < e := by
    have hpPos : 0 < p := by linarith [hp.1]
    have hDiv : 2 / p < 1 := (div_lt_one hpPos).2 hp.1
    dsimp only [e]
    linarith
  have hAPos : 0 < A := by
    dsimp only [A]
    exact div_pos (mul_pos (by norm_num) (by linarith)) hEPos
  let T : ℝ := τ * Real.rpow (NL : ℝ) α / A
  have hTPos : 0 < T := by
    have hNLReal : (1 : ℝ) ≤ (NL : ℝ) := by exact_mod_cast hNL.1
    have hNLPos : 0 < (NL : ℝ) := by linarith
    dsimp only [T]
    exact div_pos (mul_pos hτ (Real.rpow_pos_of_pos hNLPos α)) hAPos
  let Nlog : ℕ := Nat.ceil (max (3 : ℝ) (Real.exp T))
  have hNlog : 3 ≤ Nlog := by
    have hceil : max (3 : ℝ) (Real.exp T) ≤ (Nlog : ℝ) := by
      exact Nat.le_ceil _
    have hthree : (3 : ℝ) ≤ (Nlog : ℝ) := (le_max_left _ _).trans hceil
    exact_mod_cast hthree
  refine ⟨hC0, Nlog, hNlog, ?_⟩
  intro n hn
  have hNThree : 3 ≤ n := hNlog.trans hn
  have hLogLower : T ≤ Real.log (n : ℝ) := by
    have hexpn : Real.exp T ≤ (n : ℝ) := by
      calc
        Real.exp T ≤ max (3 : ℝ) (Real.exp T) := le_max_right _ _
        _ ≤ (Nlog : ℝ) := Nat.le_ceil _
        _ ≤ (n : ℝ) := by exact_mod_cast hn
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos T) hexpn
  let Rn : ℝ := Real.rpow (A * Real.log (n : ℝ) / τ) (1 / α)
  have hRLower : (NL : ℝ) ≤ Rn := by
    have hNLReal : (1 : ℝ) ≤ (NL : ℝ) := by exact_mod_cast hNL.1
    have hNLPos : 0 < (NL : ℝ) := by linarith
    have hPowerPos : 0 < Real.rpow (NL : ℝ) α := Real.rpow_pos_of_pos hNLPos α
    have hLogPos : 0 < Real.log (n : ℝ) := hTPos.trans_le hLogLower
    have hBasePos : 0 < A * Real.log (n : ℝ) / τ :=
      div_pos (mul_pos hAPos hLogPos) hτ
    have hBaseLower : Real.rpow (NL : ℝ) α ≤ A * Real.log (n : ℝ) / τ := by
      apply (le_div_iff₀ hτ).2
      calc
        Real.rpow (NL : ℝ) α * τ = A * T := by
          dsimp only [T]
          field_simp [ne_of_gt hAPos] <;> ring
        _ ≤ A * Real.log (n : ℝ) := mul_le_mul_of_nonneg_left hLogLower hAPos.le
    have hPowOrder :
        Real.rpow (Real.rpow (NL : ℝ) α) (1 / α) ≤ Rn := by
      change ((NL : ℝ) ^ α) ^ (1 / α) ≤ (A * Real.log (n : ℝ) / τ) ^ (1 / α)
      exact Real.rpow_le_rpow hPowerPos.le hBaseLower (by positivity)
    have hPowerCancel : Real.rpow (Real.rpow (NL : ℝ) α) (1 / α) = (NL : ℝ) := by
      change ((NL : ℝ) ^ α) ^ (1 / α) = (NL : ℝ)
      rw [← Real.rpow_mul hNLPos.le]
      rw [show α * (1 / α) = (1 : ℝ) by field_simp [ne_of_gt hα]]
      exact Real.rpow_one _
    rw [hPowerCancel] at hPowOrder
    exact hPowOrder
  let Cn : Set Ω := {o : Ω | w o ≤ Rn}
  let ν : Measure Ω := (μ Cn)⁻¹ • μ.restrict Cn
  change IsProbabilityMeasure ν ∧ _
  have hνprob : IsProbabilityMeasure ν := (hNL.2 Rn hRLower).2.2.1
  refine ⟨hνprob, ?_⟩
  intro m hm hmn hhalf
  let lam : ℝ := ((m : ℝ) - 2) / ((n : ℝ) - 2)
  have hLam : 0 ≤ lam ∧ lam ≤ 1 := by
    have hnReal : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNThree
    have hmReal : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hmnReal : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have hDenPos : 0 < (n : ℝ) - 2 := by linarith
    constructor
    · dsimp only [lam]
      exact div_nonneg (by linarith) hDenPos.le
    · dsimp only [lam]
      apply (div_le_iff₀ hDenPos).2
      linarith
  let H : Ω → Ω → ℝ := fun o y => g o + g y + lam * r o y
  let κ : ℝ := ∫ z : Ω × Ω, H z.1 z.2 ∂(ν.prod ν)
  let G : Ω → ℝ := fun o => (∫ y, H o y ∂ν) - κ
  let σ2 : ℝ := ∫ o, G o ^ 2 ∂ν
  let σ : ℝ := Real.sqrt σ2
  let X : Ω → ℝ := fun o => G o / σ
  let Pm : Measure (Fin m → Ω) := Measure.pi (fun _ : Fin m => ν)
  let E : Set (Fin m → Ω) :=
    {o : Fin m → Ω | (∑ i : Fin m, X (o i) ^ 2) / (m : ℝ) < (1 / 2 : ℝ)}
  change 0 < σ ∧ IsProbabilityMeasure Pm ∧ MeasurableSet E ∧ _
  have hMPos : 0 < (m : ℝ) := by
    have hmReal : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hσpos : 0 < σ :=
    ((hNL.2 Rn hRLower).2.2.2.2.2 lam hLam).2.2.2.2.2.2.1
  have hPmprob : IsProbabilityMeasure Pm :=
    ((((hNL.2 Rn hRLower).2.2.2.2.2 lam hLam).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2).2.2.2.2.2 m).1
  have hSumMeasurable :
      Measurable (fun o : Fin m → Ω => ∑ i : Fin m, X (o i) ^ 2) :=
    ((((hNL.2 Rn hRLower).2.2.2.2.2 lam hLam).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2).2.2.2.2.2 m).2.1
  have hClosedBound :
      Pm.real {o : Fin m → Ω | (∑ i : Fin m, X (o i) ^ 2) ≤ (m : ℝ) / 2} ≤
        Real.exp (-c0 * (m : ℝ)) :=
    ((((hNL.2 Rn hRLower).2.2.2.2.2 lam hLam).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2).2.2.2.2.2 m).2.2.2.2.2.2.2.2
  have hStrictSubset :
      E ⊆ {o : Fin m → Ω | (∑ i : Fin m, X (o i) ^ 2) ≤ (m : ℝ) / 2} := by
    intro o ho
    change (∑ i : Fin m, X (o i) ^ 2) / (m : ℝ) < (1 / 2 : ℝ) at ho
    change (∑ i : Fin m, X (o i) ^ 2) ≤ (m : ℝ) / 2
    have hlt := (div_lt_iff₀ hMPos).1 ho
    linarith
  have hEmeas : MeasurableSet E := by
    exact measurableSet_lt (hSumMeasurable.div_const (m : ℝ)) measurable_const
  have hFinalExpOrder :
      Real.exp (-c0 * (m : ℝ)) ≤ Real.exp (-(c0 / 2) * (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hC0.le (sub_nonneg.mpr hhalf)]
  letI : IsProbabilityMeasure Pm := hPmprob
  refine ⟨hσpos, hPmprob, hEmeas, ?_⟩
  calc
    Pm.real E ≤
        Pm.real {o : Fin m → Ω | (∑ i : Fin m, X (o i) ^ 2) ≤ (m : ℝ) / 2} :=
      measureReal_mono hStrictSubset
    _ ≤ Real.exp (-c0 * (m : ℝ)) := hClosedBound
    _ ≤ Real.exp (-(c0 / 2) * (n : ℝ)) := hFinalExpOrder

end

end Shao.OQ6.LogarithmicConditionalLowEnergy
