import Shao.OQ3.StandardizedCellBounds
import Shao.OQ3.CellBoundaryOscillation

namespace Shao.OQ3
open Classical
open scoped Topology
noncomputable section

theorem standardized_cell_pair_oscillation_bound
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
    ∀ z : ℝ × ℝ, ∀ u ∈ Metric.closedBall z h, ∀ v ∈ Metric.closedBall z h,
      |B.indicator g u - B.indicator g v| ≤
        (if (Metric.closedBall z h ∩ B).Nonempty then
          2 * Real.sqrt (n : ℝ) * kappa * C * h else 0) +
        (if (Metric.closedBall z h ∩ frontier B).Nonempty then 2 * C else 0) := by
  let B : Set (ℝ × ℝ) := (fun w : ℝ × ℝ => Real.sqrt (n : ℝ) • E (w - y)) '' A
  let g : (ℝ × ℝ) → ℝ := fun v => Real.exp (-Real.sqrt (n : ℝ) *
    (theta.1 * (E.symm v).1 + theta.2 * (E.symm v).2))
  let kappa : ℝ := (|theta.1| + |theta.2|) * ‖(E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖
  let R : ℝ := d * ‖(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖
  let C : ℝ := Real.exp (kappa * R)
  have hkappa : 0 ≤ kappa :=
    mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (norm_nonneg _)
  have hR : 0 ≤ R := mul_nonneg hd (norm_nonneg _)
  have hC : 0 ≤ C := (Real.exp_pos _).le
  have hN : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) hn)
  have hs : 0 ≤ Real.sqrt (n : ℝ) := (Real.sqrt_pos.mpr hN).le
  have hsupport : ∀ v ∈ B, ‖v‖ ≤ R / Real.sqrt (n : ℝ) :=
    standardized_cell_support_bound n hn E y d hd A hcell
  obtain ⟨hweight, hvariation⟩ := standardized_cell_exponential_bounds n hn theta E R hR
  have hbound : ∀ v ∈ B, |g v| ≤ C := by
    intro v hv
    exact (hweight v (hsupport v hv)).2
  let L : ℝ := Real.sqrt (n : ℝ) * kappa * C
  have hL : 0 ≤ L := mul_nonneg (mul_nonneg hs hkappa) hC
  have hLip : ∀ u ∈ B, ∀ v ∈ B, |g u - g v| ≤ L * dist u v := by
    intro u hu v hv
    simpa only [L, dist_eq_norm] using hvariation u v (hsupport u hu) (hsupport v hv)
  dsimp only
  intro z u hu v hv
  have ho := indicator_cell_pair_oscillation_bound B g C L h hC hL hh hbound hLip z u hu v hv
  simpa only [B, g, kappa, R, C, L, mul_assoc] using ho

end
end Shao.OQ3
