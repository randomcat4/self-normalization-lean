import Shao.OQ3.ProductMeasureDomination
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

namespace Shao.OQ3
open MeasureTheory
open scoped ENNReal NNReal
noncomputable section

theorem exists_compact_parameter_box (K : Set (ℝ × ℝ)) (hK : IsCompact K) (u0 v0 : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ p ∈ K, |p.1 - u0| ≤ L ∧ |p.2 - v0| ≤ L := by
  have hF : Continuous (fun p : ℝ × ℝ => |p.1 - u0| + |p.2 - v0|) := by fun_prop
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro p hp
  have hsum : |p.1 - u0| + |p.2 - v0| ≤ max C 0 := by
    calc
      _ ≤ ‖|p.1 - u0| + |p.2 - v0|‖ := by
        rw [Real.norm_eq_abs]
        exact le_abs_self _
      _ ≤ C := hC p hp
      _ ≤ max C 0 := le_max_left _ _
  constructor <;> linarith [abs_nonneg (p.1 - u0), abs_nonneg (p.2 - v0)]

theorem exists_compact_quadratic_tilted_domination (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (K : Set (ℝ × ℝ)) (hK : IsCompact K) (u0 v0 : ℝ) :
    ∃ m : ℝ, 0 < m ∧ ∀ p ∈ K,
      (ENNReal.ofReal m • mu.tilted (fun x => u0 * x + v0 * x ^ 2) ≤
        mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) ∧
      ∀ s t : ℝ, m ^ 2 *
        (∫ z : ℝ × ℝ, 1 - Real.cos ((z.1 - z.2) * (s + t * (z.1 + z.2)))
          ∂(mu.tilted (fun x => u0 * x + v0 * x ^ 2)).prod
            (mu.tilted (fun x => u0 * x + v0 * x ^ 2))) ≤
        ∫ z : ℝ × ℝ, 1 - Real.cos ((z.1 - z.2) * (s + t * (z.1 + z.2)))
          ∂(mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)).prod
            (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) := by
  obtain ⟨L, hL, hbox⟩ := exists_compact_parameter_box K hK u0 v0
  let B : ℝ := L * (M + M ^ 2)
  refine ⟨Real.exp (-2 * B), Real.exp_pos _, ?_⟩
  intro p hp
  obtain ⟨hu, hv⟩ := hbox p hp
  constructor
  · exact quadratic_tilted_measure_domination mu M L hM hL hb u0 v0 p.1 p.2 hu hv
  · intro s t
    have hsquare : Real.exp (-2 * B) ^ 2 = Real.exp (-4 * B) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [hsquare]
    exact quadratic_tilted_cosine_pair_domination mu M L hM hL hb u0 v0 p.1 p.2 hu hv s t

end
end Shao.OQ3
