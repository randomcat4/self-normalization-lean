import Shao.OQ5.P50.ThreeStateLayer
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The actual finite three-state layer law

The source weights and matrix are those of p50 section 2, reused by p52.
This module constructs the atomic marginal and its actual product measure,
with finite integrability, exact expectations and canonical row integrals.
It makes no assertion about infinitely many layers or the full p52 model.
-/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

namespace Shao.OQ5.P50

noncomputable section

/-- The actual three-state atomic law with the existing source weights. -/
def layerMeasure (p q : ℝ) : Measure (Fin 3) :=
  Measure.sum fun a : Fin 3 => ENNReal.ofReal (layerWeight p q a) • Measure.dirac a

private theorem layerWeight_nonneg (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q ≤ 1) (a : Fin 3) :
    0 ≤ layerWeight p q a := by
  fin_cases a <;> simp [layerWeight] <;> linarith

private theorem layerWeight_sum (p q : ℝ) :
    (∑ a : Fin 3, layerWeight p q a) = 1 := by
  rw [Fin.sum_univ_three]
  simp [layerWeight]
  ring

/-- Finiteness holds even when the raw weights do not define a probability. -/
private instance layerMeasure_finite (p q : ℝ) :
    IsFiniteMeasure (layerMeasure p q) where
  measure_univ_lt_top := by
    simp [layerMeasure, Fin.sum_univ_three]

theorem layerMeasure_isProbabilityMeasure (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q ≤ 1) :
    IsProbabilityMeasure (layerMeasure p q) := by
  apply HasSum.isProbabilityMeasure_sum_dirac (layerWeight_nonneg p q hp hq hpq)
  simpa only [layerWeight_sum p q] using (hasSum_fintype (layerWeight p q))

theorem layerMeasure_singleton (p q : ℝ) (a : Fin 3) :
    layerMeasure p q {a} = ENNReal.ofReal (layerWeight p q a) :=
  Measure.sum_smul_dirac_singleton

theorem integrable_layerMeasure (p q : ℝ) (f : Fin 3 → ℝ) :
    Integrable f (layerMeasure p q) :=
  Integrable.of_finite

theorem integral_layerMeasure (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q ≤ 1) (f : Fin 3 → ℝ) :
    (∫ a, f a ∂layerMeasure p q) = ∑ a : Fin 3, layerWeight p q a * f a := by
  rw [integral_fintype (integrable_layerMeasure p q f)]
  apply Finset.sum_congr rfl
  intro a _
  rw [measureReal_def, layerMeasure_singleton,
    ENNReal.toReal_ofReal (layerWeight_nonneg p q hp hq hpq a), smul_eq_mul]

theorem integrable_layerMeasure_prod (p q : ℝ) (F : Fin 3 × Fin 3 → ℝ) :
    Integrable F ((layerMeasure p q).prod (layerMeasure p q)) :=
  Integrable.of_finite

theorem integral_layerMeasure_prod (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q ≤ 1) (F : Fin 3 × Fin 3 → ℝ) :
    (∫ z, F z ∂(layerMeasure p q).prod (layerMeasure p q)) =
      ∑ a : Fin 3, ∑ b : Fin 3,
        layerWeight p q a * layerWeight p q b * F (a, b) := by
  rw [integral_prod F (integrable_layerMeasure_prod p q F)]
  simp_rw [integral_layerMeasure p q hp hq hpq]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  exact (mul_assoc _ _ _).symm

theorem integral_layerKernel_row_zero (N : ℕ) (t p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q ≤ 1) (hqnz : q ≠ 0) (a : Fin 3) :
    (∫ b, layerKernel N t p q a b ∂layerMeasure p q) = 0 := by
  rw [integral_layerMeasure p q hp hq hpq]
  exact layerKernel_weighted_row_zero N t p q hqnz a

theorem layerKernel_memLp_two (N : ℕ) (t p q : ℝ) :
    MemLp (fun z : Fin 3 × Fin 3 => layerKernel N t p q z.1 z.2) 2
      ((layerMeasure p q).prod (layerMeasure p q)) := by
  apply (memLp_two_iff_integrable_sq
    (integrable_layerMeasure_prod p q
      (fun z => layerKernel N t p q z.1 z.2)).aestronglyMeasurable).2
  exact integrable_layerMeasure_prod p q
    (fun z => layerKernel N t p q z.1 z.2 ^ 2)

end
end Shao.OQ5.P50
