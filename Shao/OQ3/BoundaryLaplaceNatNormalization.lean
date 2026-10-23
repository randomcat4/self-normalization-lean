import Shao.OQ3.BoundaryLaplaceNormalization
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem boundary_laplace_source_leading_constant (det lambda Lambda1 : ℝ) :
    ((Real.sqrt det)⁻¹ * (Real.sqrt (2 * Real.pi / Lambda1) / lambda)) / (2 * Real.pi) =
      1 / (Real.sqrt (2 * Real.pi) * lambda * Real.sqrt det * Real.sqrt Lambda1) ∧
    ∀ (n : ℕ) (J0 : ℝ),
      Real.exp (-(n : ℝ) * J0) *
        (((Real.sqrt det)⁻¹ * (Real.sqrt (2 * Real.pi / Lambda1) / lambda)) / (2 * Real.pi)) /
          Real.sqrt (n : ℝ) =
        Real.exp (-(n : ℝ) * J0) /
          (Real.sqrt (2 * Real.pi * (n : ℝ)) * lambda * Real.sqrt det * Real.sqrt Lambda1)
 := by
  have hS : 0 ≤ 2 * Real.pi := mul_nonneg (by norm_num) Real.pi_pos.le
  have hbase : ((Real.sqrt det)⁻¹ * (Real.sqrt (2 * Real.pi / Lambda1) / lambda)) /
      (2 * Real.pi) = 1 / (Real.sqrt (2 * Real.pi) * lambda * Real.sqrt det * Real.sqrt Lambda1) := by
    rw [Real.sqrt_div hS]
    calc
      _ = (Real.sqrt (2 * Real.pi) / (2 * Real.pi)) /
          (Real.sqrt det * lambda * Real.sqrt Lambda1) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ = _ := by
        rw [Real.sqrt_div_self]
        simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
        ring
  refine ⟨hbase, ?_⟩
  intro n J0
  rw [hbase, Real.sqrt_mul hS]
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

theorem boundary_laplace_nat_scale (n : ℕ) (hn : 1 ≤ n) :
    let t : ℝ := (Real.sqrt (n : ℝ))⁻¹
    0 < t ∧ t ≤ 1 ∧ t ^ 2 = 1 / (n : ℝ) ∧
      1 / (2 * Real.pi * t ^ 2) = (n : ℝ) / (2 * Real.pi) ∧
      ∀ J0 C0 : ℝ,
        Real.exp (-J0 / t ^ 2) = Real.exp (-(n : ℝ) * J0) ∧
        t * Real.exp (-J0 / t ^ 2) * (C0 / (2 * Real.pi)) =
          Real.exp (-(n : ℝ) * J0) * (C0 / (2 * Real.pi)) / Real.sqrt (n : ℝ)
 := by
  let t : ℝ := (Real.sqrt (n : ℝ))⁻¹
  have hN : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) hn)
  have hN1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hN
  have hs1 : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr hN1
  have ht : 0 < t := inv_pos.mpr hs
  have ht1 : t ≤ 1 := by
    change (Real.sqrt (n : ℝ))⁻¹ ≤ 1
    rw [← one_div]
    exact (div_le_one hs).mpr hs1
  have ht2 : t ^ 2 = 1 / (n : ℝ) := by
    dsimp only [t]
    rw [inv_pow, Real.sq_sqrt hN.le, one_div]
  refine ⟨ht, ht1, ht2, ?_, ?_⟩
  · rw [ht2]
    field_simp [hN.ne', Real.pi_ne_zero] <;> ring
  · intro J0 C0
    have heq : -J0 / t ^ 2 = -(n : ℝ) * J0 := by
      rw [ht2]
      field_simp [hN.ne'] <;> ring
    refine ⟨congrArg Real.exp heq, ?_⟩
    rw [heq]
    simp only [div_eq_mul_inv]
    ring

theorem boundary_laplace_nat_normalization
    (J B : (ℝ × ℝ) → ℝ) (V : Set (ℝ × ℝ)) (J0 C0 C : ℝ)
    (hreal : ∀ t : ℝ, 0 < t → t ≤ 1 →
      let m0 : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (volume : Measure ℝ)
      let W : (ℝ × ℝ) → ℝ := fun w => B w * Real.exp (-J w / t ^ 2)
      let Ln : ℝ := (1 / (2 * Real.pi * t ^ 2)) * ∫ w : ℝ × ℝ in V, W w ∂m0
      let main : ℝ := t * Real.exp (-J0 / t ^ 2) * (C0 / (2 * Real.pi))
      IntegrableOn W V m0 ∧ 0 < main ∧ |Ln / main - 1| ≤ C * t) :
    let m0 : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (volume : Measure ℝ)
    ∀ n : ℕ, 1 ≤ n →
      let W : (ℝ × ℝ) → ℝ := fun w => B w * Real.exp (-(n : ℝ) * J w)
      let Ln : ℝ := ((n : ℝ) / (2 * Real.pi)) * ∫ w : ℝ × ℝ in V, W w ∂m0
      let main : ℝ := Real.exp (-(n : ℝ) * J0) * (C0 / (2 * Real.pi)) / Real.sqrt (n : ℝ)
      IntegrableOn W V m0 ∧ 0 < main ∧ |Ln / main - 1| ≤ C / Real.sqrt (n : ℝ) := by
  let m0 : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (volume : Measure ℝ)
  dsimp only
  intro n hn
  let t : ℝ := (Real.sqrt (n : ℝ))⁻¹
  obtain ⟨ht, ht1, _, hcoef, hform⟩ := boundary_laplace_nat_scale n hn
  let Wt : (ℝ × ℝ) → ℝ := fun w => B w * Real.exp (-J w / t ^ 2)
  let Wn : (ℝ × ℝ) → ℝ := fun w => B w * Real.exp (-(n : ℝ) * J w)
  have he (x : ℝ) : Real.exp (-x / t ^ 2) = Real.exp (-(n : ℝ) * x) := (hform x C0).1
  have hW : Wt = Wn := by
    funext w
    dsimp only [Wt, Wn]
    rw [he (J w)]
  have hcoef0 : 1 / (2 * Real.pi * t ^ 2) = (n : ℝ) / (2 * Real.pi) := hcoef
  have hmain0 : t * Real.exp (-J0 / t ^ 2) * (C0 / (2 * Real.pi)) =
      Real.exp (-(n : ℝ) * J0) * (C0 / (2 * Real.pi)) / Real.sqrt (n : ℝ) :=
    (hform J0 C0).2
  obtain ⟨hI, hP, hE⟩ := hreal t ht ht1
  have hI0 : IntegrableOn Wt V m0 := hI
  have hP0 : 0 < t * Real.exp (-J0 / t ^ 2) * (C0 / (2 * Real.pi)) := hP
  have hE0 : |((1 / (2 * Real.pi * t ^ 2)) * (∫ w : ℝ × ℝ in V, Wt w ∂m0)) /
      (t * Real.exp (-J0 / t ^ 2) * (C0 / (2 * Real.pi))) - 1| ≤ C * t := hE
  rw [hW] at hI0 hE0
  rw [hcoef0, hmain0] at hE0
  rw [hmain0] at hP0
  refine ⟨hI0, hP0, ?_⟩
  simpa only [t, div_eq_mul_inv] using hE0

end
end Shao.OQ3
