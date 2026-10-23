import Shao.OQ3.StandardizedCellBounds
import Shao.OQ3.CellAveragedOscillation
import Shao.OQ3.StandardGaussianCellMass

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory
open scoped Topology
noncomputable section

theorem standardized_gaussian_cell_averaged_oscillation_bound
    (n : ℕ) (hn : 1 ≤ n) (theta : ℝ × ℝ)
    (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (y : ℝ × ℝ)
    (d : ℝ) (hd : 0 ≤ d) (A : Set (ℝ × ℝ))
    (hcell : ∀ w ∈ A, ‖w - y‖ ≤ d / (n : ℝ))
    (h : ℝ) (hh : 0 ≤ h) :
    let B : Set (ℝ × ℝ) := (fun w : ℝ × ℝ => Real.sqrt (n : ℝ) • E (w - y)) '' A
    let g : (ℝ × ℝ) → ℝ := fun v => Real.exp (-Real.sqrt (n : ℝ) *
      (theta.1 * (E.symm v).1 + theta.2 * (E.symm v).2))
    let kappa : ℝ := (|theta.1| + |theta.2|) * ‖(E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖
    let R : ℝ := d * ‖(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖
    let C : ℝ := Real.exp (kappa * R)
    let Φ : MeasureTheory.Measure (ℝ × ℝ) :=
      (ProbabilityTheory.gaussianReal 0 1).prod (ProbabilityTheory.gaussianReal 0 1)
    MeasureTheory.Integrable (openBallOscillation (B.indicator g) h) Φ ∧
    (∫ z, openBallOscillation (B.indicator g) h z ∂Φ) ≤
      8 * Real.sqrt (n : ℝ) * kappa * C * h *
        (R / Real.sqrt (n : ℝ) + h) ^ 2 +
      2 * C * Φ.real (Metric.cthickening h (frontier B)) := by
  let B : Set (ℝ × ℝ) := (fun w : ℝ × ℝ => Real.sqrt (n : ℝ) • E (w - y)) '' A
  let g : (ℝ × ℝ) → ℝ := fun v => Real.exp (-Real.sqrt (n : ℝ) *
    (theta.1 * (E.symm v).1 + theta.2 * (E.symm v).2))
  let kappa : ℝ := (|theta.1| + |theta.2|) * ‖(E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖
  let R : ℝ := d * ‖(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖
  let C : ℝ := Real.exp (kappa * R)
  let Φ : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)
  let L : ℝ := Real.sqrt (n : ℝ) * kappa * C
  have hkappa : 0 ≤ kappa :=
    mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (norm_nonneg _)
  have hR : 0 ≤ R := mul_nonneg hd (norm_nonneg _)
  have hC : 0 ≤ C := (Real.exp_pos _).le
  have hs : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hL : 0 ≤ L := mul_nonneg (mul_nonneg hs hkappa) hC
  have hsupport : ∀ v ∈ B, ‖v‖ ≤ R / Real.sqrt (n : ℝ) :=
    standardized_cell_support_bound n hn E y d hd A hcell
  obtain ⟨hweight, hvariation⟩ := standardized_cell_exponential_bounds n hn theta E R hR
  have hbound : ∀ v ∈ B, |g v| ≤ C := by
    intro v hv
    exact (hweight v (hsupport v hv)).2
  have hLip : ∀ u ∈ B, ∀ v ∈ B, |g u - g v| ≤ L * dist u v := by
    intro u hu v hv
    simpa only [L, dist_eq_norm] using hvariation u v (hsupport u hu) (hsupport v hv)
  obtain ⟨hint, hpoint, havg⟩ :=
    indicator_cell_averaged_oscillation_bound Φ B g C L h hC hL hh hbound hLip
  have hB : B ⊆ Metric.closedBall (0 : ℝ × ℝ) (R / Real.sqrt (n : ℝ)) := by
    intro v hv
    simpa only [Metric.mem_closedBall, dist_zero_right] using hsupport v hv
  have hnear := standard_gaussian_plane_cell_thickening_bound B
    (R / Real.sqrt (n : ℝ)) h (div_nonneg hR hs) hh hB
  have hcoeff : 0 ≤ 2 * L * h := mul_nonneg (mul_nonneg (by norm_num) hL) hh
  change Integrable (openBallOscillation (B.indicator g) h) Φ ∧
    (∫ z, openBallOscillation (B.indicator g) h z ∂Φ) ≤
      8 * Real.sqrt (n : ℝ) * kappa * C * h *
        (R / Real.sqrt (n : ℝ) + h) ^ 2 +
      2 * C * Φ.real (Metric.cthickening h (frontier B))
  refine ⟨hint, havg.trans ?_⟩
  calc
    2 * L * h * Φ.real (Metric.cthickening h B) +
        2 * C * Φ.real (Metric.cthickening h (frontier B)) ≤
      2 * L * h * (4 * (R / Real.sqrt (n : ℝ) + h) ^ 2) +
        2 * C * Φ.real (Metric.cthickening h (frontier B)) :=
      add_le_add (mul_le_mul_of_nonneg_left hnear hcoeff) le_rfl
    _ = 8 * Real.sqrt (n : ℝ) * kappa * C * h *
        (R / Real.sqrt (n : ℝ) + h) ^ 2 +
        2 * C * Φ.real (Metric.cthickening h (frontier B)) := by
      dsimp only [L]
      ring

end
end Shao.OQ3
