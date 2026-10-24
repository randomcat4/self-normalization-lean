import Shao.OQ6.ActualPhysicalGlobalCDF
import Shao.OQ4.ReflectedSurvival

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Shao.OQ6.ActualPhysicalSignedGlobalCDF

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

universe u

theorem physical_statistic_neg
    {n : ℕ} (H : Fin n → Fin n → ℝ) (q : ℝ) :
    (if 0 < Shao.OQ6.FiniteRows.jackknifeSq (fun i j => -(H i j)) then
      q * Shao.OQ6.FiniteRows.uStatistic (fun i j => -(H i j)) /
        Real.sqrt (Shao.OQ6.FiniteRows.jackknifeSq (fun i j => -(H i j)))
    else 0) =
      -(if 0 < Shao.OQ6.FiniteRows.jackknifeSq H then
        q * Shao.OQ6.FiniteRows.uStatistic H /
          Real.sqrt (Shao.OQ6.FiniteRows.jackknifeSq H)
      else 0) := by
  classical
  have hpair :
    Shao.OQ5.P35.unorderedPairSum (fun i j => -(H i j)) =
      -(Shao.OQ5.P35.unorderedPairSum H) := by
    unfold Shao.OQ5.P35.unorderedPairSum
    calc
      (∑ i : Fin n, ∑ j : Fin n, if i < j then -(H i j) else 0) =
          ∑ i : Fin n, ∑ j : Fin n, -(if i < j then H i j else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : i < j
        · simp only [if_pos hij]
        · simp only [if_neg hij, neg_zero]
      _ = -(∑ i : Fin n, ∑ j : Fin n, if i < j then H i j else 0) := by
        simp only [Finset.sum_neg_distrib]
  have hU :
    Shao.OQ6.FiniteRows.uStatistic (fun i j => -(H i j)) =
      -(Shao.OQ6.FiniteRows.uStatistic H) := by
    unfold Shao.OQ6.FiniteRows.uStatistic
    rw [hpair, mul_neg]
  have hrow (i : Fin n) :
    Shao.OQ6.FiniteRows.rowMean (fun i j => -(H i j)) i =
      -(Shao.OQ6.FiniteRows.rowMean H i) := by
    unfold Shao.OQ6.FiniteRows.rowMean
    rw [Finset.sum_neg_distrib, mul_neg]
  have hR :
    Shao.OQ6.FiniteRows.jackknifeSq (fun i j => -(H i j)) =
      Shao.OQ6.FiniteRows.jackknifeSq H := by
    unfold Shao.OQ6.FiniteRows.jackknifeSq
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [hrow i, hU]
    ring
  simp only [hR, hU]
  by_cases hpos : 0 < Shao.OQ6.FiniteRows.jackknifeSq H
  · simp only [if_pos hpos, mul_neg, neg_div]
  · simp only [if_neg hpos, neg_zero]

theorem actual_physical_signed_global_cdf_tail_rpow_rate
    (C : ℝ)
    (hSZ : Shao.OQ6.NormalizedIntegrableCDFAssembly.ScalarShaoZhouFiniteCostCDFInput.{u} C)
    {Ω : Type u} [MeasurableSpace Ω]
    [MeasurableSpace.CountablyGenerated Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
    (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (p : ℝ) (hp2 : 2 < p) (hp3 : p ≤ 3)
    (hgp : Integrable (fun o => Real.rpow |∫ y, h o y ∂μ| p) μ) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
    let s : ℝ := 1 + Real.sqrt v
    let β : ℝ := ∫ o, Real.rpow |g o| p ∂μ
    ∃ K : ℝ, 0 < K ∧
      ∀ (n : ℕ), 3 ≤ n →
        let N : ℝ := (n : ℝ)
        let q : ℝ := Real.sqrt N
        let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
        let U : (Fin n → Ω) → ℝ := fun ξ =>
          Shao.OQ6.FiniteRows.uStatistic (fun i j => h (ξ i) (ξ j))
        let R2 : (Fin n → Ω) → ℝ := fun ξ =>
          Shao.OQ6.FiniteRows.jackknifeSq (fun i j => h (ξ i) (ξ j))
        let T : (Fin n → Ω) → ℝ := fun ξ =>
          if 0 < R2 ξ then q * U ξ / Real.sqrt (R2 ξ) else 0
        Measurable T ∧
          ∀ x : ℝ,
            let error : ℝ := K *
              (β * Real.rpow (1 + |x|) p / Real.rpow N ((p - 2) / 2) +
                (1 + |x|) * s / q + |x| ^ 3 / N)
            |P₀.real {ξ | T ξ ≤ x} - Shao.OQ4.standardNormalCDF x| ≤ error ∧
            |P₀.real {ξ | T ξ < x} - Shao.OQ4.standardNormalCDF x| ≤ error ∧
            |P₀.real {ξ | x < T ξ} -
              (1 - Shao.OQ4.standardNormalCDF x)| ≤ error ∧
            |P₀.real {ξ | x ≤ T ξ} -
              (1 - Shao.OQ4.standardNormalCDF x)| ≤ error := by
  classical
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
  let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
  let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
  let s : ℝ := 1 + Real.sqrt v
  let β : ℝ := ∫ o, Real.rpow |g o| p ∂μ
  let hminus : Ω → Ω → ℝ := fun o y => -(h o y)
  let gminus : Ω → ℝ := fun o => ∫ y, hminus o y ∂μ
  let rminus : Ω → Ω → ℝ := fun o y => hminus o y - gminus o - gminus y
  let vminus : ℝ := ∫ t : Ω × Ω, rminus t.1 t.2 ^ 2 ∂(μ.prod μ)
  let sminus : ℝ := 1 + Real.sqrt vminus
  let βminus : ℝ := ∫ o, Real.rpow |gminus o| p ∂μ
  have hhminus : Measurable (fun t : Ω × Ω => hminus t.1 t.2) := hh.neg
  have hh2minus : MemLp (fun t : Ω × Ω => hminus t.1 t.2) 2 (μ.prod μ) := hh2.neg
  have hsymmminus : ∀ o y, hminus o y = hminus y o := by
    intro o y
    exact congrArg (fun z : ℝ => -z) (hhsymm o y)
  have hcenterminus : (∫ t : Ω × Ω, hminus t.1 t.2 ∂(μ.prod μ)) = 0 := by
    change (∫ t : Ω × Ω, -(h t.1 t.2) ∂(μ.prod μ)) = 0
    rw [integral_neg, hcenter, neg_zero]
  have hgminus : ∀ o, gminus o = -(g o) := by
    intro o
    exact integral_neg (fun y => h o y)
  have hprojectionsecondminus :
      (∫ o, (∫ y, hminus o y ∂μ) ^ 2 ∂μ) = 1 := by
    change (∫ o, gminus o ^ 2 ∂μ) = 1
    simp_rw [hgminus, neg_sq]
    exact hprojectionsecond
  have hgpminus : Integrable (fun o => Real.rpow |∫ y, hminus o y ∂μ| p) μ := by
    change Integrable (fun o => Real.rpow |gminus o| p) μ
    simpa only [hgminus, abs_neg] using hgp
  have hrminus : ∀ o y, rminus o y = -(r o y) := by
    intro o y
    change -(h o y) - gminus o - gminus y = -(h o y - g o - g y)
    rw [hgminus o, hgminus y]
    ring
  have hvminus : vminus = v := by
    change (∫ t : Ω × Ω, rminus t.1 t.2 ^ 2 ∂(μ.prod μ)) =
      ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
    apply integral_congr_ae
    exact ae_of_all (μ.prod μ) (fun t => by
      change rminus t.1 t.2 ^ 2 = r t.1 t.2 ^ 2
      rw [hrminus t.1 t.2, neg_sq])
  have hsminus : sminus = s := by
    change 1 + Real.sqrt vminus = 1 + Real.sqrt v
    rw [hvminus]
  have hβminus : βminus = β := by
    change (∫ o, Real.rpow |gminus o| p ∂μ) =
      ∫ o, Real.rpow |g o| p ∂μ
    apply integral_congr_ae
    exact ae_of_all μ (fun o => by
      change Real.rpow |gminus o| p = Real.rpow |g o| p
      rw [hgminus o, abs_neg])
  obtain ⟨Kplus, hKplus, hplus⟩ := Shao.OQ6.ActualPhysicalGlobalCDF.actual_physical_global_cdf_tail_rpow_rate C hSZ μ h hh hh2 hhsymm hcenter hprojectionsecond p hp2 hp3 hgp
  obtain ⟨Kminus, hKminus, hminusBounds⟩ := Shao.OQ6.ActualPhysicalGlobalCDF.actual_physical_global_cdf_tail_rpow_rate C hSZ μ hminus hhminus hh2minus hsymmminus hcenterminus hprojectionsecondminus p hp2 hp3 hgpminus
  let K : ℝ := Kplus + Kminus
  have hK : 0 < K := add_pos hKplus hKminus
  have hKplusK : Kplus ≤ K := by
    dsimp only [K]
    linarith only [hKminus]
  have hKminusK : Kminus ≤ K := by
    dsimp only [K]
    linarith only [hKplus]
  refine ⟨K, hK, ?_⟩
  intro n hn
  let N : ℝ := (n : ℝ)
  let q : ℝ := Real.sqrt N
  let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  let U : (Fin n → Ω) → ℝ := fun ξ => Shao.OQ6.FiniteRows.uStatistic (fun i j => h (ξ i) (ξ j))
  let R2 : (Fin n → Ω) → ℝ := fun ξ => Shao.OQ6.FiniteRows.jackknifeSq (fun i j => h (ξ i) (ξ j))
  let T : (Fin n → Ω) → ℝ := fun ξ => if 0 < R2 ξ then q * U ξ / Real.sqrt (R2 ξ) else 0
  let Uminus : (Fin n → Ω) → ℝ := fun ξ => Shao.OQ6.FiniteRows.uStatistic (fun i j => hminus (ξ i) (ξ j))
  let R2minus : (Fin n → Ω) → ℝ := fun ξ => Shao.OQ6.FiniteRows.jackknifeSq (fun i j => hminus (ξ i) (ξ j))
  let Tminus : (Fin n → Ω) → ℝ := fun ξ => if 0 < R2minus ξ then q * Uminus ξ / Real.sqrt (R2minus ξ) else 0
  have hTminus (ξ : Fin n → Ω) : Tminus ξ = -(T ξ) := by
    exact physical_statistic_neg (fun i j => h (ξ i) (ξ j)) q
  have hTmeasurable : Measurable T := (hplus n hn).1
  refine ⟨hTmeasurable, ?_⟩
  intro x
  let E : ℝ := β * Real.rpow (1 + |x|) p / Real.rpow N ((p - 2) / 2) + (1 + |x|) * s / q + |x| ^ 3 / N
  let Ψ : ℝ := 1 - Shao.OQ4.standardNormalCDF x
  have hβnonneg : 0 ≤ β := by
    exact integral_nonneg (fun o => Real.rpow_nonneg (abs_nonneg (g o)) p)
  have hNnonneg : 0 ≤ N := by
    dsimp only [N]
    positivity
  have hsnonneg : 0 ≤ s :=
    add_nonneg (by norm_num) (Real.sqrt_nonneg v)
  have hEfirst :
      0 ≤ β * Real.rpow (1 + |x|) p / Real.rpow N ((p - 2) / 2) :=
    div_nonneg
      (mul_nonneg hβnonneg
        (Real.rpow_nonneg (add_nonneg (by norm_num) (abs_nonneg x)) p))
      (Real.rpow_nonneg hNnonneg ((p - 2) / 2))
  have hEsecond : 0 ≤ (1 + |x|) * s / q :=
    div_nonneg
      (mul_nonneg (add_nonneg (by norm_num) (abs_nonneg x)) hsnonneg)
      (Real.sqrt_nonneg N)
  have hEthird : 0 ≤ |x| ^ 3 / N :=
    div_nonneg (pow_nonneg (abs_nonneg x) 3) hNnonneg
  have hEnonneg : 0 ≤ E := add_nonneg (add_nonneg hEfirst hEsecond) hEthird
  change
    |P₀.real {ξ | T ξ ≤ x} - Shao.OQ4.standardNormalCDF x| ≤ K * E ∧
    |P₀.real {ξ | T ξ < x} - Shao.OQ4.standardNormalCDF x| ≤ K * E ∧
    |P₀.real {ξ | x < T ξ} - Ψ| ≤ K * E ∧
    |P₀.real {ξ | x ≤ T ξ} - Ψ| ≤ K * E
  by_cases hx : 0 ≤ x
  · have hcostplus :
        β * Real.rpow (1 + x) p / Real.rpow N ((p - 2) / 2) +
          (1 + x) * s / q + x ^ 3 / N = E := by
      dsimp only [E]
      rw [abs_of_nonneg hx]
    have hb := (hplus n hn).2 x hx
    change
      |P₀.real {ξ | T ξ ≤ x} - Shao.OQ4.standardNormalCDF x| ≤
        Kplus * (β * Real.rpow (1 + x) p / Real.rpow N ((p - 2) / 2) +
          (1 + x) * s / q + x ^ 3 / N) ∧
      |P₀.real {ξ | T ξ < x} - Shao.OQ4.standardNormalCDF x| ≤
        Kplus * (β * Real.rpow (1 + x) p / Real.rpow N ((p - 2) / 2) +
          (1 + x) * s / q + x ^ 3 / N) ∧
      |P₀.real {ξ | x < T ξ} - (1 - Shao.OQ4.standardNormalCDF x)| ≤
        Kplus * (β * Real.rpow (1 + x) p / Real.rpow N ((p - 2) / 2) +
          (1 + x) * s / q + x ^ 3 / N) ∧
      |P₀.real {ξ | x ≤ T ξ} - (1 - Shao.OQ4.standardNormalCDF x)| ≤
        Kplus * (β * Real.rpow (1 + x) p / Real.rpow N ((p - 2) / 2) +
          (1 + x) * s / q + x ^ 3 / N) at hb
    rw [hcostplus] at hb
    have hfee : Kplus * E ≤ K * E :=
      mul_le_mul_of_nonneg_right hKplusK hEnonneg
    exact ⟨hb.1.trans hfee, hb.2.1.trans hfee,
      hb.2.2.1.trans hfee, hb.2.2.2.trans hfee⟩
  · have hxneg : x < 0 := lt_of_not_ge hx
    let y : ℝ := -x
    have hy0 : 0 ≤ y := by
      dsimp only [y]
      linarith only [hxneg]
    have hyabs : y = |x| := by
      dsimp only [y]
      rw [abs_of_neg hxneg]
    have hcostminus :
        βminus * Real.rpow (1 + y) p / Real.rpow N ((p - 2) / 2) +
          (1 + y) * sminus / q + y ^ 3 / N = E := by
      dsimp only [E]
      rw [hβminus, hsminus, hyabs]
    have hb := (hminusBounds n hn).2 y hy0
    change
      |P₀.real {ξ | Tminus ξ ≤ y} - Shao.OQ4.standardNormalCDF y| ≤
        Kminus * (βminus * Real.rpow (1 + y) p / Real.rpow N ((p - 2) / 2) +
          (1 + y) * sminus / q + y ^ 3 / N) ∧
      |P₀.real {ξ | Tminus ξ < y} - Shao.OQ4.standardNormalCDF y| ≤
        Kminus * (βminus * Real.rpow (1 + y) p / Real.rpow N ((p - 2) / 2) +
          (1 + y) * sminus / q + y ^ 3 / N) ∧
      |P₀.real {ξ | y < Tminus ξ} - (1 - Shao.OQ4.standardNormalCDF y)| ≤
        Kminus * (βminus * Real.rpow (1 + y) p / Real.rpow N ((p - 2) / 2) +
          (1 + y) * sminus / q + y ^ 3 / N) ∧
      |P₀.real {ξ | y ≤ Tminus ξ} - (1 - Shao.OQ4.standardNormalCDF y)| ≤
        Kminus * (βminus * Real.rpow (1 + y) p / Real.rpow N ((p - 2) / 2) +
          (1 + y) * sminus / q + y ^ 3 / N) at hb
    rw [hcostminus] at hb
    have hfee : Kminus * E ≤ K * E :=
      mul_le_mul_of_nonneg_right hKminusK hEnonneg
    have hclosed : {ξ | T ξ ≤ x} = {ξ | y ≤ Tminus ξ} := by
      ext ξ
      simp only [Set.mem_setOf_eq, hTminus, y, neg_le_neg_iff]
    have hstrict : {ξ | T ξ < x} = {ξ | y < Tminus ξ} := by
      ext ξ
      simp only [Set.mem_setOf_eq, hTminus, y, neg_lt_neg_iff]
    have hupperStrict : {ξ | x < T ξ} = {ξ | Tminus ξ < y} := by
      ext ξ
      simp only [Set.mem_setOf_eq, hTminus, y, neg_lt_neg_iff]
    have hupperWeak : {ξ | x ≤ T ξ} = {ξ | Tminus ξ ≤ y} := by
      ext ξ
      simp only [Set.mem_setOf_eq, hTminus, y, neg_le_neg_iff]
    have hPhi : Shao.OQ4.standardNormalCDF x =
        1 - Shao.OQ4.standardNormalCDF y := by
      have hreflection := Shao.OQ4.standardNormalCDF_reflection y
      have hyneg : -y = x := by
        dsimp only [y]
        ring
      rw [hyneg] at hreflection
      exact hreflection
    have hPsi : Ψ = Shao.OQ4.standardNormalCDF y := by
      dsimp only [Ψ]
      rw [hPhi]
      ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hclosed, hPhi]
      exact hb.2.2.2.trans hfee
    · rw [hstrict, hPhi]
      exact hb.2.2.1.trans hfee
    · rw [hupperStrict, hPsi]
      exact hb.2.1.trans hfee
    · rw [hupperWeak, hPsi]
      exact hb.1.trans hfee

end

end Shao.OQ6.ActualPhysicalSignedGlobalCDF
