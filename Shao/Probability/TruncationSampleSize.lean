import Shao.Probability.TruncationRegularity
import Mathlib.Analysis.Real.Sqrt

/-!
# The sample-size lower bound from the genuine truncation budget

The law is a probability measure with its original normalization
`n * integral z² = 1`. The needed Lyapunov comparison is proved by integrating
a polynomial tangent inequality for the actual cutoff variable.
-/

set_option autoImplicit false

namespace Shao

open MeasureTheory

private theorem integral_sq_cube_le_abs_cube_sq
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : Ω → ℝ)
    (hg2 : Integrable (fun ω => (g ω) ^ 2) μ)
    (hg3 : Integrable (fun ω => |g ω| ^ 3) μ) :
    (∫ ω, (g ω) ^ 2 ∂μ) ^ 3 ≤ (∫ ω, |g ω| ^ 3 ∂μ) ^ 2 := by
  let A : ℝ := ∫ ω, (g ω) ^ 2 ∂μ
  let C : ℝ := ∫ ω, |g ω| ^ 3 ∂μ
  let b : ℝ := Real.sqrt A
  have hA : 0 ≤ A := integral_nonneg (fun ω => sq_nonneg (g ω))
  have hC : 0 ≤ C := integral_nonneg (fun ω => pow_nonneg (abs_nonneg (g ω)) 3)
  have hb : 0 ≤ b := Real.sqrt_nonneg A
  have hb2 : b ^ 2 = A := Real.sq_sqrt hA
  have htangent (ω : Ω) :
      (3 * b) * (g ω) ^ 2 ≤ 2 * |g ω| ^ 3 + b ^ 3 := by
    have hfactor : 0 ≤ (|g ω| - b) ^ 2 * (2 * |g ω| + b) :=
      mul_nonneg (sq_nonneg _) (by positivity)
    rw [← sq_abs (g ω)]
    nlinarith
  have hI := integral_mono (hg2.const_mul (3 * b))
    ((hg3.const_mul 2).add (integrable_const (b ^ 3))) htangent
  have hmoment : (3 * b) * A ≤ 2 * C + b ^ 3 := by
    simpa [A, C, integral_add (hg3.const_mul 2) (integrable_const (b ^ 3)),
      integral_const_mul] using hI
  have hb3 : b ^ 3 ≤ C := by
    rw [← hb2] at hmoment
    nlinarith
  change A ^ 3 ≤ C ^ 2
  calc
    A ^ 3 = (b ^ 3) ^ 2 := by rw [← hb2]; ring
    _ ≤ C ^ 2 := pow_le_pow_left₀ (pow_nonneg hb 3) hb3 2

/-- The original two-step sample-size lower bound, with no global third moment
or Lyapunov premise. The conditional moments below are genuine cutoff moments. -/
theorem truncationBudget_sample_size_lower
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (t ρ : ℝ) (ht : 0 ≤ t)
    (hR : truncationBudget ν n t ≤ ρ) (hρ : ρ ≤ 1 / 16) :
    (1 + t) ^ 6 ≤
        (1 - ρ) ^ 3 * (1 + t) ^ 6 / truncationBudget ν n t ^ 2 ∧
      (1 - ρ) ^ 3 * (1 + t) ^ 6 / truncationBudget ν n t ^ 2 ≤ (n : ℝ) := by
  let N : ℝ := n
  let a : ℝ := 1 + t
  let R : ℝ := truncationBudget ν n t
  let g : ℝ → ℝ := fun z => if |z| ≤ 1 / a then z else 0
  let A : ℝ := ∫ z, (g z) ^ 2 ∂ν
  let C : ℝ := ∫ z, |g z| ^ 3 ∂ν
  let T : ℝ := ∫ z : ℝ, if 1 / a < |z| then z ^ 2 else 0 ∂ν
  have ha : 0 < a := by dsimp [a]; linarith
  have ha1 : 1 ≤ a := by dsimp [a]; linarith
  have hn : 0 < n := by
    by_contra hnot
    have hz : n = 0 := Nat.eq_zero_of_not_pos hnot
    simp [hz] at hnorm
  have hN : 0 < N := by dsimp only [N]; exact_mod_cast hn
  have hsecond : 0 < ∫ z : ℝ, z ^ 2 ∂ν := by
    by_contra hnot
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n)
      (le_of_not_gt hnot)
    rw [hnorm] at hnonpos
    norm_num at hnonpos
  have hRpos : 0 < R := truncationBudget_pos ν n h2 hn hsecond t ht
  have hD : MeasurableSet {z : ℝ | |z| ≤ 1 / a} :=
    measurableSet_le continuous_abs.measurable measurable_const
  have hg2 : Integrable (fun z => (g z) ^ 2) ν := by
    apply (h2.indicator hD).congr
    exact ae_of_all ν (fun z => by
      simp [g, Set.indicator])
  have hg3 : Integrable (fun z => |g z| ^ 3) ν := by
    apply (integrable_truncation_small_three ν h2 a ha).congr
    exact ae_of_all ν (fun z => by
      dsimp only [g]
      split_ifs <;> simp)
  have htail : Integrable (fun z : ℝ => if 1 / a < |z| then z ^ 2 else 0) ν :=
    integrable_truncation_tail_two ν h2 a ha
  have hA : 0 ≤ A := integral_nonneg (fun z => sq_nonneg (g z))
  have hC : 0 ≤ C := integral_nonneg (fun z => pow_nonneg (abs_nonneg (g z)) 3)
  have hT : 0 ≤ T := integral_nonneg (fun z => by split_ifs <;> positivity)
  have hsplit : (∫ z : ℝ, z ^ 2 ∂ν) = A + T := by
    dsimp only [A, T]
    rw [← integral_add hg2 htail]
    apply integral_congr_ae
    exact ae_of_all ν (fun z => by
      by_cases hz : |z| ≤ 1 / a
      · simp only [g, ite_eq_left hz, ite_eq_right (not_lt.mpr hz), add_zero]
      · simp only [g, ite_eq_right hz, ite_eq_left (lt_of_not_ge hz)]
        norm_num)
  have hnormsplit : N * (A + T) = 1 := by
    rw [← hsplit]
    exact hnorm
  have hCeq : C = ∫ z : ℝ, if |z| ≤ 1 / a then |z| ^ 3 else 0 ∂ν := by
    apply integral_congr_ae
    exact ae_of_all ν (fun z => by
      dsimp only [g]
      split_ifs <;> simp)
  have hdec : R = a ^ 3 * (N * C) + a ^ 2 * (N * T) := by
    rw [hCeq]
    exact truncationBudget_decomposition ν n h2 t (by linarith)
  have hlyap : A ^ 3 ≤ C ^ 2 := integral_sq_cube_le_abs_cube_sq ν g hg2 hg3
  have hNA : 0 ≤ N * A := mul_nonneg hN.le hA
  have hNC : 0 ≤ N * C := mul_nonneg hN.le hC
  have hNT : 0 ≤ N * T := mul_nonneg hN.le hT
  have hasq : 1 ≤ a ^ 2 := by nlinarith [sq_nonneg (a - 1)]
  have hsmall0 : 0 ≤ a ^ 3 * (N * C) := mul_nonneg (pow_nonneg ha.le 3) hNC
  have htailbound : N * T ≤ R := by
    calc
      N * T = 1 * (N * T) := (one_mul _).symm
      _ ≤ a ^ 2 * (N * T) := mul_le_mul_of_nonneg_right hasq hNT
      _ ≤ R := by rw [hdec]; exact le_add_of_nonneg_left hsmall0
  have hret : 1 - ρ ≤ N * A := by
    have htailrho : N * T ≤ ρ := htailbound.trans hR
    nlinarith [hnormsplit]
  have hrho : 0 ≤ 1 - ρ := by linarith
  have hsmall : a ^ 3 * (N * C) ≤ R := by
    rw [hdec]
    exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg a) hNT)
  have hR2 : (a ^ 3 * (N * C)) ^ 2 ≤ R ^ 2 :=
    pow_le_pow_left₀ hsmall0 hsmall 2
  have hmainpoly : (1 - ρ) ^ 3 * a ^ 6 ≤ N * R ^ 2 := by
    calc
      (1 - ρ) ^ 3 * a ^ 6 = a ^ 6 * (1 - ρ) ^ 3 := mul_comm _ _
      _ ≤ a ^ 6 * (N * A) ^ 3 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hrho hret 3) (pow_nonneg ha.le 6)
      _ = (a ^ 6 * N ^ 3) * A ^ 3 := by ring
      _ ≤ (a ^ 6 * N ^ 3) * C ^ 2 := mul_le_mul_of_nonneg_left hlyap
        (mul_nonneg (pow_nonneg ha.le 6) (pow_nonneg hN.le 3))
      _ = N * (a ^ 3 * (N * C)) ^ 2 := by ring
      _ ≤ N * R ^ 2 := mul_le_mul_of_nonneg_left hR2 hN.le
  have hR2pos : 0 < R ^ 2 := sq_pos_of_pos hRpos
  have hnum : R ^ 2 ≤ (1 - ρ) ^ 3 := by
    calc
      R ^ 2 ≤ (1 / 16 : ℝ) ^ 2 := pow_le_pow_left₀ hRpos.le (hR.trans hρ) 2
      _ ≤ (15 / 16 : ℝ) ^ 3 := by norm_num
      _ ≤ (1 - ρ) ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
  change a ^ 6 ≤ (1 - ρ) ^ 3 * a ^ 6 / R ^ 2 ∧
    (1 - ρ) ^ 3 * a ^ 6 / R ^ 2 ≤ N
  constructor
  · apply (le_div_iff₀ hR2pos).mpr
    exact (mul_le_mul_of_nonneg_left hnum (pow_nonneg ha.le 6)).trans_eq (mul_comm _ _)
  · exact (div_le_iff₀ hR2pos).mpr hmainpoly

end Shao
