import Shao.OQ5.P35.FixedCategoryLaw
import Mathlib.MeasureTheory.Measure.Real

/-!
# Exact tails of the fixed p35 category law

Source: `current/oq56/inputs02/p35.md`, §3 and §4, formulas (9)–(10).
The CDF keeps its special atom at zero; all probabilities refer to the same
fixed category measure. No conditional law or sample-size parameter is used.
-/

set_option autoImplicit false

namespace Shao.OQ5.P35

noncomputable section

open MeasureTheory
open scoped BigOperators

/-- The real probability of a category strictly below j. -/
def categoryBelowMass (j : ℕ) : ℝ := categoryMeasure.real (Set.Iio j)

theorem categoryBelowMass_zero : categoryBelowMass 0 = 0 := by
  simp [categoryBelowMass]

theorem categoryBelowMass_nonneg (j : ℕ) : 0 ≤ categoryBelowMass j :=
  measureReal_nonneg

private theorem categoryBelowMass_eq_sum (j : ℕ) :
    categoryBelowMass j = ∑ c ∈ Finset.range j, categoryMass c := by
  have hset : (Set.Iio j : Set ℕ) = (Finset.range j : Set ℕ) := by
    ext c
    simp
  unfold categoryBelowMass
  rw [hset, ← sum_measureReal_singleton]
  simp

private theorem categoryBelowMass_succ (j : ℕ) :
    categoryBelowMass (j + 1) = categoryBelowMass j + categoryMass j := by
  simp only [categoryBelowMass_eq_sum, Finset.sum_range_succ]

private theorem categoryBelowMass_succ_eq (j : ℕ) :
    categoryBelowMass (j + 1) =
      1 - (16384 / 16383 : ℝ) * (1 / 16384 : ℝ) ^ (j + 1) := by
  induction j with
  | zero => norm_num [categoryBelowMass_succ, categoryBelowMass_zero]
  | succ j ih =>
    rw [categoryBelowMass_succ, ih, categoryMass_succ, pow_succ]
    ring

theorem categoryBelowMass_eq (j : ℕ) (hj : 1 ≤ j) :
    categoryBelowMass j =
      1 - (16384 / 16383 : ℝ) * (1 / 16384 : ℝ) ^ j := by
  cases j with
  | zero => cases hj
  | succ j => exact categoryBelowMass_succ_eq j

theorem categoryMeasure_above_eq (j : ℕ) :
    categoryMeasure.real (Set.Ioi j) =
      (1 / 16383 : ℝ) * (1 / 16384 : ℝ) ^ j := by
  have hcompl : (Set.Iio (j + 1) : Set ℕ)ᶜ = Set.Ioi j := by
    ext c
    simp
  have h := measureReal_add_measureReal_compl (μ := categoryMeasure)
    (s := Set.Iio (j + 1)) (measurableSet_Iio : MeasurableSet (Set.Iio (j + 1)))
  rw [hcompl] at h
  change categoryBelowMass (j + 1) + categoryMeasure.real (Set.Ioi j) = _ at h
  rw [categoryBelowMass_succ_eq, pow_succ] at h
  norm_num at h
  linarith

theorem categoryBelowMass_bounds (j : ℕ) (hj : 1 ≤ j) :
    (16382 / 16383 : ℝ) ≤ categoryBelowMass j ∧ categoryBelowMass j < 1 := by
  constructor
  · have hset : ({0} : Set ℕ) ⊆ Set.Iio j := by
      intro c hc
      have hc0 : c = 0 := Set.mem_singleton_iff.mp hc
      subst c
      exact hj
    have h := measureReal_mono (μ := categoryMeasure) hset
    simpa [categoryBelowMass] using h
  · rw [categoryBelowMass_eq j hj]
    have hpos : 0 < (16384 / 16383 : ℝ) * (1 / 16384 : ℝ) ^ j := by positivity
    linarith

end

end Shao.OQ5.P35
