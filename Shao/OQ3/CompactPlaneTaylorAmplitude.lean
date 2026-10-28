import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Shao.OQ3
open scoped Topology ContDiff
noncomputable section

theorem compact_plane_uniform_quadratic_taylor_and_amplitude
    (f A : (ℝ × ℝ) → ℝ) (U K : Set (ℝ × ℝ))
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hf : ∀ x ∈ U, ContDiffAt ℝ 2 f x)
    (hA : ∀ x ∈ U, ContDiffAt ℝ 1 A x) :
    ∃ delta C : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ x ∈ K, ∀ y : ℝ × ℝ, ‖y - x‖ ≤ delta →
        y ∈ U ∧
        |f y - f x - fderiv ℝ f x (y - x)| ≤ C * ‖y - x‖ ^ 2 ∧
        |A y - A x| ≤ C * ‖y - x‖ := by
  obtain ⟨r, hr, hrU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨s, hs, hsCompact⟩ := hK.exists_isCompact_cthickening
  let delta : ℝ := min r s
  have hdelta : 0 < delta := lt_min hr hs
  let T : Set (ℝ × ℝ) := Metric.cthickening delta K
  have hTU : T ⊆ U := (Metric.cthickening_mono (min_le_left r s) K).trans hrU
  have hCompact : IsCompact T := hsCompact.of_isClosed_subset
    Metric.isClosed_cthickening (Metric.cthickening_mono (min_le_right r s) K)
  have hContD2 : ContinuousOn (fun x => fderiv ℝ (fun z => fderiv ℝ f z) x) T := by
    intro x hx
    exact (((hf x (hTU hx)).fderiv_right (m := 1) (by norm_num)).fderiv_right
      (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hContDA : ContinuousOn (fun x => fderiv ℝ A x) T := by
    intro x hx
    exact ((hA x (hTU hx)).fderiv_right (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  obtain ⟨C1, hC1⟩ := hCompact.exists_bound_of_continuousOn
    (f := fun x : ℝ × ℝ => fderiv ℝ (fun z => fderiv ℝ f z) x) hContD2
  obtain ⟨C2, hC2⟩ := hCompact.exists_bound_of_continuousOn
    (f := fun x : ℝ × ℝ => fderiv ℝ A x) hContDA
  let C : ℝ := 1 + |C1| + |C2|
  have hC : 0 < C := by dsimp [C]; positivity
  have hC1le : C1 ≤ C := by dsimp [C]; linarith [le_abs_self C1, abs_nonneg C2]
  have hC2le : C2 ≤ C := by dsimp [C]; linarith [le_abs_self C2, abs_nonneg C1]
  have hBoundD2 (x : ℝ × ℝ) (hx : x ∈ T) :
      ‖fderiv ℝ (fun z => fderiv ℝ f z) x‖ ≤ C := (hC1 x hx).trans hC1le
  have hBoundDA (x : ℝ × ℝ) (hx : x ∈ T) : ‖fderiv ℝ A x‖ ≤ C :=
    (hC2 x hx).trans hC2le
  refine ⟨delta, C, hdelta, hC, ?_⟩
  intro x hx y hxy
  let S : Set (ℝ × ℝ) := Metric.closedBall x ‖y - x‖
  have hS : S ⊆ T := by
    intro z hz
    apply Metric.mem_cthickening_of_dist_le z x delta K hx
    have hz' : ‖z - x‖ ≤ ‖y - x‖ := by
      simpa only [S, Metric.mem_closedBall, dist_eq_norm] using hz
    rw [dist_eq_norm]
    exact hz'.trans hxy
  have hxS : x ∈ S := Metric.mem_closedBall_self (norm_nonneg _)
  have hyS : y ∈ S := by
    simp only [S, Metric.mem_closedBall, dist_eq_norm, le_refl]
  have hConvex : Convex ℝ S := convex_closedBall x _
  have hDiffF (z : ℝ × ℝ) (hz : z ∈ S) : DifferentiableAt ℝ f z :=
    (hf z (hTU (hS hz))).differentiableAt (by norm_num)
  have hDiffDF (z : ℝ × ℝ) (hz : z ∈ S) :
      DifferentiableAt ℝ (fun q => fderiv ℝ f q) z :=
    ((hf z (hTU (hS hz))).fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hDFBound (z : ℝ × ℝ) (hz : z ∈ S) :
      ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ C * ‖y - x‖ := by
    have hLip := hConvex.norm_image_sub_le_of_norm_fderiv_le hDiffDF
      (fun q hq => hBoundD2 q (hS hq)) hxS hz
    have hz' : ‖z - x‖ ≤ ‖y - x‖ := by
      simpa only [S, Metric.mem_closedBall, dist_eq_norm] using hz
    exact hLip.trans (mul_le_mul_of_nonneg_left hz' hC.le)
  have hTaylor := hConvex.norm_image_sub_le_of_norm_fderiv_le'
    hDiffF hDFBound hxS hyS
  have hAmplitude := hConvex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hA z (hTU (hS hz))).differentiableAt_one)
    (fun z hz => hBoundDA z (hS hz)) hxS hyS
  refine ⟨hTU (hS hyS), ?_, ?_⟩
  · simpa only [Real.norm_eq_abs, pow_two, mul_assoc] using hTaylor
  · simpa only [Real.norm_eq_abs] using hAmplitude

end
end Shao.OQ3
