import Shao.OQ5.P35.FixedLawCoefficients
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The fixed atomic category law for p35

Source: `current/oq56/inputs02/p35.md`, §3, lines 66–99.
The measure and coefficients do not depend on the eventual sample size.
This module constructs the probability law on categories and its required first,
second and offset moments. It does not construct the continuous noise, the real
encoding law, an iid sequence or the kernel.
-/

namespace Shao.OQ5.P35

open MeasureTheory

noncomputable section

/-- The fixed category law, including its atom at category zero. -/
def categoryMeasure : Measure ℕ :=
  Measure.sum fun c : ℕ => ENNReal.ofReal (categoryMass c) • Measure.dirac c

instance categoryMeasure_isProbabilityMeasure : IsProbabilityMeasure categoryMeasure :=
  HasSum.isProbabilityMeasure_sum_dirac categoryMass_nonneg hasSum_categoryMass

@[simp] theorem categoryMeasure_singleton (c : ℕ) :
    categoryMeasure {c} = ENNReal.ofReal (categoryMass c) :=
  Measure.sum_smul_dirac_singleton

@[simp] theorem categoryMeasure_real_singleton (c : ℕ) :
    categoryMeasure.real {c} = categoryMass c := by
  rw [measureReal_def, categoryMeasure_singleton,
    ENNReal.toReal_ofReal (categoryMass_nonneg c)]

/-- Integrability is exactly summability of the mass-weighted absolute values. -/
theorem integrable_categoryMeasure_iff (f : ℕ → ℝ) :
    Integrable f categoryMeasure ↔
      Summable (fun c => categoryMass c * ‖f c‖) := by
  unfold categoryMeasure
  simpa only [id_eq, ENNReal.toReal_ofReal (categoryMass_nonneg _)] using
    (integrable_sum_dirac_iff (f := f) (x := id)
      (c := fun c => ENNReal.ofReal (categoryMass c))
      (fun _ => ENNReal.ofReal_ne_top))

/-- An integrable category observable has its usual mass-weighted expectation. -/
theorem integral_categoryMeasure (f : ℕ → ℝ) (hf : Integrable f categoryMeasure) :
    (∫ c, f c ∂categoryMeasure) = ∑' c, categoryMass c * f c := by
  have hsum : Summable (fun c : ℕ =>
      (ENNReal.ofReal (categoryMass c)).toReal * ‖f (id c)‖) := by
    simpa only [id_eq, ENNReal.toReal_ofReal (categoryMass_nonneg _)] using
      (integrable_categoryMeasure_iff f).mp hf
  simpa only [categoryMeasure, id_eq,
    ENNReal.toReal_ofReal (categoryMass_nonneg _), smul_eq_mul] using
    (integral_sum_dirac_eq_tsum (f := f) (x := id)
      (c := fun c => ENNReal.ofReal (categoryMass c))
      (fun _ => ENNReal.ofReal_ne_top) hsum)

private theorem value_nonneg (c : ℕ) : 0 ≤ categoryValue c := by
  unfold categoryValue
  split_ifs <;> positivity

theorem integrable_categoryValue : Integrable categoryValue categoryMeasure := by
  apply (integrable_categoryMeasure_iff categoryValue).mpr
  simpa only [Real.norm_eq_abs, abs_of_nonneg (value_nonneg _)] using
    hasSum_mass_value.summable

theorem integral_categoryValue :
    (∫ c, categoryValue c ∂categoryMeasure) = 1 / 511 := by
  rw [integral_categoryMeasure categoryValue integrable_categoryValue]
  exact hasSum_mass_value.tsum_eq

theorem integrable_categoryValue_sq :
    Integrable (fun c => categoryValue c ^ 2) categoryMeasure := by
  apply (integrable_categoryMeasure_iff (fun c => categoryValue c ^ 2)).mpr
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (categoryValue _))] using
    hasSum_mass_value_sq.summable

theorem integral_categoryValue_sq :
    (∫ c, categoryValue c ^ 2 ∂categoryMeasure) = 1 / 15 := by
  rw [integral_categoryMeasure (fun c => categoryValue c ^ 2) integrable_categoryValue_sq]
  exact hasSum_mass_value_sq.tsum_eq

theorem integrable_categoryOffset_pow (r : ℕ) (hr : r ≤ 3) :
    Integrable (fun c => categoryOffset c ^ r) categoryMeasure := by
  apply (integrable_categoryMeasure_iff (fun c => categoryOffset c ^ r)).mpr
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (categoryOffset_nonneg _) r)] using
    summable_mass_offset_pow r hr

end
end Shao.OQ5.P35
