import Shao.OQ3.WeakCramerPairNonlattice
import Mathlib.Topology.Order.Compact

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem continuous_pair_characteristic
    (law : Measure (ℝ × ℝ)) [IsProbabilityMeasure law] :
    Continuous (fun a : ℝ × ℝ =>
      ∫ w : ℝ × ℝ,
        Complex.exp (((a.1 * w.1 + a.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂law) := by
  refine MeasureTheory.continuous_of_dominated
    (bound := fun _ : ℝ × ℝ => (1 : ℝ)) ?_ ?_ (integrable_const (1 : ℝ)) ?_
  · intro a
    exact (show Continuous (fun w : ℝ × ℝ =>
      Complex.exp (((a.1 * w.1 + a.2 * w.2 : ℝ) : ℂ) * Complex.I)) by
        fun_prop).aestronglyMeasurable
  · intro a
    exact Filter.Eventually.of_forall (fun w => (Complex.norm_exp_ofReal_mul_I _).le)
  · exact Filter.Eventually.of_forall (fun w => by fun_prop)

theorem weak_cramer_pair_compact_frequency_gap
    (law : Measure (ℝ × ℝ)) [IsProbabilityMeasure law]
    (beta c R : ℝ) (hbeta : 0 ≤ beta) (hc : 0 < c) (hR : 0 ≤ R)
    (hWC : ∀ u v : ℝ, R < Real.sqrt (u ^ 2 + v ^ 2) →
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂law)‖ ≤
          1 - c * Real.rpow (Real.sqrt (u ^ 2 + v ^ 2)) (-beta))
    (K : Set (ℝ × ℝ)) (hcompact : IsCompact K)
    (hzero : ∀ a ∈ K, a.1 ≠ 0 ∨ a.2 ≠ 0) :
    ∃ gamma : ℝ, 0 < gamma ∧ gamma < 1 ∧ ∀ a ∈ K,
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((a.1 * w.1 + a.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂law)‖ ≤ gamma := by
  by_cases hne : K.Nonempty
  · let F : (ℝ × ℝ) → ℝ := fun a =>
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((a.1 * w.1 + a.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂law)‖
    have hF : Continuous F := (continuous_pair_characteristic law).norm
    obtain ⟨a, ha, hmax⟩ := hcompact.exists_isMaxOn hne hF.continuousOn
    have hlt : F a < 1 := weak_cramer_pair_characteristic_norm_lt_one
      law beta c R hbeta hc hR hWC a.1 a.2 (hzero a ha)
    have hnonneg : 0 ≤ F a := norm_nonneg _
    refine ⟨(F a + 1) / 2, by linarith, by linarith, ?_⟩
    intro b hb
    have hle : F b ≤ F a := hmax hb
    exact hle.trans (by linarith)
  · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    intro a ha
    exact (hne ⟨a, ha⟩).elim

end
end Shao.OQ3
