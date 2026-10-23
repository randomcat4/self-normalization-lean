import Shao.OQ3.PairCharacteristicQuadraticRemainder

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
noncomputable section

theorem uniform_isotropic_pair_characteristic_local_gaussian_bound
    {ι : Type*} (K : Set ι) (laws : ι → Measure (Fin 2 → ℝ))
    (hprob : ∀ p ∈ K, IsProbabilityMeasure (laws p))
    (hL2 : ∀ p ∈ K, ∀ i : Fin 2, MemLp (fun y : Fin 2 → ℝ => y i) 2 (laws p))
    (hmean : ∀ p ∈ K, ∀ i : Fin 2, (∫ y : Fin 2 → ℝ, y i ∂laws p) = 0)
    (hcov : ∀ p ∈ K, ∀ i j : Fin 2, ProbabilityTheory.covariance
      (fun y : Fin 2 → ℝ => y i) (fun y : Fin 2 → ℝ => y j) (laws p) =
        if i = j then 1 else 0)
    (hthird : ∃ C : ℝ, 0 < C ∧ ∀ p ∈ K,
      Integrable (fun y : Fin 2 → ℝ =>
        (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ 3) (laws p) ∧
      (∫ y : Fin 2 → ℝ,
        (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ 3 ∂laws p) ≤ C) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
      ∀ p ∈ K, ∀ u v : ℝ, Real.sqrt (u ^ 2 + v ^ 2) ≤ delta →
        ‖(∫ y : Fin 2 → ℝ,
          Complex.exp (((u * y 0 + v * y 1 : ℝ) : ℂ) * Complex.I) ∂laws p)‖ ≤
            Real.exp (-(u ^ 2 + v ^ 2) / 4) := by
  obtain ⟨C, hC, hthird⟩ := hthird
  let A : ℝ := Real.exp 1 + 4
  have hA : 0 < A := by dsimp [A]; positivity
  let delta : ℝ := min 1 (1 / (4 * A * C))
  have hdeltapos : 0 < delta := by
    exact lt_min (by norm_num) (one_div_pos.mpr (by positivity))
  have hdeltaone : delta ≤ 1 := min_le_left _ _
  have hdeltabound : delta ≤ 1 / (4 * A * C) := min_le_right _ _
  have hdenom : 0 < 4 * A * C := by positivity
  have hscale : (A * C) * delta ≤ 1 / 4 := by
    have h := (le_div_iff₀ hdenom).mp hdeltabound
    nlinarith
  refine ⟨delta, hdeltapos, hdeltaone, ?_⟩
  intro p hp u v hrdelta
  letI : IsProbabilityMeasure (laws p) := hprob p hp
  let r : ℝ := Real.sqrt (u ^ 2 + v ^ 2)
  let z : ℂ := ∫ y : Fin 2 → ℝ,
    Complex.exp (((u * y 0 + v * y 1 : ℝ) : ℂ) * Complex.I) ∂laws p
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr1 : r ≤ 1 := hrdelta.trans hdeltaone
  have hrsq : r ^ 2 = u ^ 2 + v ^ 2 := Real.sq_sqrt (by positivity)
  have hr2 : r ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1)]
  have hq0 : 0 ≤ 1 - r ^ 2 / 2 := by linarith
  have hqcast : (1 - ((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2) =
      ((1 - r ^ 2 / 2 : ℝ) : ℂ) := by
    rw [hrsq]
    push_cast <;> ring
  have hqnorm : ‖(1 : ℂ) - ((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2‖ = 1 - r ^ 2 / 2 := by
    rw [hqcast]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0]
  have herror : ‖z - (1 - ((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2)‖ ≤ A * r ^ 3 * C :=
    (pair_probability_characteristic_quadratic_remainder_bound
      (laws p) (hL2 p hp) (hmean p hp) (hcov p hp) (hthird p hp).1 u v).trans
        (mul_le_mul_of_nonneg_left (hthird p hp).2
          (mul_nonneg hA.le (pow_nonneg hr0 3)))
  have hAr : (A * C) * r ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_left hrdelta (mul_nonneg hA.le hC.le)).trans hscale
  have hcube : A * r ^ 3 * C ≤ r ^ 2 / 4 := by
    calc
      A * r ^ 3 * C = ((A * C) * r) * r ^ 2 := by ring
      _ ≤ (1 / 4) * r ^ 2 := mul_le_mul_of_nonneg_right hAr (sq_nonneg r)
      _ = r ^ 2 / 4 := by ring
  have hz : ‖z‖ ≤ A * r ^ 3 * C + (1 - r ^ 2 / 2) := by
    calc
      ‖z‖ = ‖(z - (1 - ((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2)) +
          (1 - ((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2)‖ := by
        congr 1
        ring
      _ ≤ ‖z - (1 - ((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2)‖ +
          ‖(1 : ℂ) - ((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2‖ := norm_add_le _ _
      _ ≤ A * r ^ 3 * C + (1 - r ^ 2 / 2) := add_le_add herror hqnorm.le
  have hzsmall : ‖z‖ ≤ 1 - r ^ 2 / 4 := by linarith
  have hexp : 1 - r ^ 2 / 4 ≤ Real.exp (-(r ^ 2) / 4) := by
    have h := Real.add_one_le_exp (-(r ^ 2) / 4)
    linarith
  exact hzsmall.trans (by simpa only [hrsq] using hexp)

end
end Shao.OQ3
