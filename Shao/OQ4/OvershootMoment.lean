import Shao.OQ4.OvershootSum
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Integrating the third-moment overshoot payment

Source: current/oq4/b01/proof01.md, Section 6, (R5)--(R6).
The full series of expected cell defects is controlled with a first and third
moment. No fourth moment, bounded support, or atomlessness is assumed.
This module does not supply the killed-kernel occupation input (O0).
-/

set_option autoImplicit false

namespace Shao.OQ4

open MeasureTheory
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
variable {U : Ω → ℝ}

/-- Every unit-cell defect is integrable under a finite first moment. -/
theorem integrable_overshootCell (hU : Integrable U μ) (j : ℕ) :
    Integrable (fun ω => overshootCell (U ω) j) μ := by
  exact ((hU.sub (integrable_const (j : ℝ))).pos_part).const_mul ((j : ℝ) + 1)

omit [IsFiniteMeasure μ] in
/-- Expected cell defects are nonnegative, including atoms at cell endpoints. -/
theorem integral_overshootCell_nonneg (j : ℕ) :
    0 ≤ ∫ ω, overshootCell (U ω) j ∂μ := by
  exact integral_nonneg (fun ω => overshootCell_nonneg (U ω) j)

/-- The finite cutoff bound after integrating R6. -/
theorem sum_integral_overshootCell_le (hU : Integrable U μ)
    (hU3 : Integrable (fun ω => U ω ^ 3) μ)
    (hU0 : ∀ᵐ ω ∂μ, 0 ≤ U ω) (L : ℕ) :
    (∑ j ∈ Finset.range L, ∫ ω, overshootCell (U ω) j ∂μ) ≤
      4 * ((∫ ω, U ω ∂μ) + ∫ ω, U ω ^ 3 ∂μ) := by
  rw [← integral_finsetSum (Finset.range L) (fun j _ => integrable_overshootCell hU j)]
  calc
    (∫ ω, ∑ j ∈ Finset.range L, overshootCell (U ω) j ∂μ)
        ≤ ∫ ω, 4 * (U ω + U ω ^ 3) ∂μ := by
      apply integral_mono_ae
        (integrable_finsetSum (Finset.range L) (fun j _ => integrable_overshootCell hU j))
        ((hU.add hU3).const_mul 4)
      exact hU0.mono (fun ω hω => overshoot_sum_le_cubic (U ω) hω L)
    _ = 4 * ((∫ ω, U ω ∂μ) + ∫ ω, U ω ^ 3 ∂μ) := by
      rw [integral_const_mul, integral_add hU hU3]

/-- The entire sequence of expected defects is summable with only a third moment. -/
theorem summable_integral_overshootCell (hU : Integrable U μ)
    (hU3 : Integrable (fun ω => U ω ^ 3) μ)
    (hU0 : ∀ᵐ ω ∂μ, 0 ≤ U ω) :
    Summable (fun j : ℕ => ∫ ω, overshootCell (U ω) j ∂μ) := by
  exact summable_of_sum_range_le (fun j => integral_overshootCell_nonneg j)
    (fun L => sum_integral_overshootCell_le hU hU3 hU0 L)

/-- R6's expected payment over all cells, uniform in every finite cutoff. -/
theorem tsum_integral_overshootCell_le (hU : Integrable U μ)
    (hU3 : Integrable (fun ω => U ω ^ 3) μ)
    (hU0 : ∀ᵐ ω ∂μ, 0 ≤ U ω) :
    (∑' j : ℕ, ∫ ω, overshootCell (U ω) j ∂μ) ≤
      4 * ((∫ ω, U ω ∂μ) + ∫ ω, U ω ^ 3 ∂μ) := by
  exact Real.tsum_le_of_sum_range_le (fun j => integral_overshootCell_nonneg j)
    (fun L => sum_integral_overshootCell_le hU hU3 hU0 L)

end Shao.OQ4
