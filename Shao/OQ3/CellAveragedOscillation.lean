import Shao.OQ3.OpenBallOscillation
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace Shao.OQ3
open Classical MeasureTheory
open scoped Topology
noncomputable section

theorem indicator_cell_averaged_oscillation_bound
    (μ : MeasureTheory.Measure (ℝ × ℝ)) [MeasureTheory.IsFiniteMeasure μ]
    (A : Set (ℝ × ℝ)) (g : (ℝ × ℝ) → ℝ)
    (C L h : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hbound : ∀ u ∈ A, |g u| ≤ C)
    (hLip : ∀ u ∈ A, ∀ v ∈ A, |g u - g v| ≤ L * dist u v) :
    MeasureTheory.Integrable (openBallOscillation (A.indicator g) h) μ ∧
    (∀ z, openBallOscillation (A.indicator g) h z ≤
      (Metric.cthickening h A).indicator (fun _ => 2 * L * h) z +
      (Metric.cthickening h (frontier A)).indicator (fun _ => 2 * C) z) ∧
    (∫ z, openBallOscillation (A.indicator g) h z ∂μ) ≤
      2 * L * h * μ.real (Metric.cthickening h A) +
      2 * C * μ.real (Metric.cthickening h (frontier A)) := by
  classical
  let N : Set (ℝ × ℝ) := Metric.cthickening h A
  let E : Set (ℝ × ℝ) := Metric.cthickening h (frontier A)
  have ha : 0 ≤ 2 * L * h := mul_nonneg (mul_nonneg (by norm_num) hL) hh
  have hb : 0 ≤ 2 * C := mul_nonneg (by norm_num) hC
  have hnonneg (T : Set (ℝ × ℝ)) (K : ℝ) (hK : 0 ≤ K) (z : ℝ × ℝ) :
      0 ≤ T.indicator (fun _ => K) z := by
    by_cases hz : z ∈ T <;> simp [hz, hK]
  have hhit (T : Set (ℝ × ℝ)) (K : ℝ) (hK : 0 ≤ K) (z : ℝ × ℝ) :
      (if (Metric.closedBall z h ∩ T).Nonempty then K else 0) ≤
        (Metric.cthickening h T).indicator (fun _ => K) z := by
    by_cases hit : (Metric.closedBall z h ∩ T).Nonempty
    · obtain ⟨w, hw, hwT⟩ := hit
      have hz : z ∈ Metric.cthickening h T :=
        Metric.mem_cthickening_of_dist_le z w h T hwT
          (by simpa only [Metric.mem_closedBall, dist_comm] using hw)
      have hhits : (Metric.closedBall z h ∩ T).Nonempty := ⟨w, hw, hwT⟩
      simp [hhits, hz]
    · by_cases hz : z ∈ Metric.cthickening h T <;> simp [hit, hz, hK]
  have hind : ∀ x, |A.indicator g x| ≤ C := by
    intro x
    by_cases hx : x ∈ A
    · simpa only [Set.indicator_of_mem hx] using hbound x hx
    · rw [Set.indicator_of_notMem hx, abs_zero]
      exact hC
  have hint : Integrable (openBallOscillation (A.indicator g) h) μ :=
    open_ball_oscillation_integrable μ (A.indicator g) C h hC hind
  have hpoint (z : ℝ × ℝ) :
      openBallOscillation (A.indicator g) h z ≤
        N.indicator (fun _ => 2 * L * h) z + E.indicator (fun _ => 2 * C) z := by
    apply csSup_le ⟨0, Set.mem_insert _ _⟩
    intro r hr
    rcases Set.mem_insert_iff.mp hr with rfl | hr
    · exact add_nonneg (hnonneg N _ ha z) (hnonneg E _ hb z)
    · obtain ⟨u, hu, v, hv, rfl⟩ := hr
      have hp := indicator_cell_pair_oscillation_bound A g C L h hC hL hh hbound hLip
        z u (Metric.ball_subset_closedBall hu) v (Metric.ball_subset_closedBall hv)
      exact hp.trans (add_le_add (hhit A _ ha z) (hhit (frontier A) _ hb z))
  have hN : MeasurableSet N := Metric.isClosed_cthickening.measurableSet
  have hE : MeasurableSet E := Metric.isClosed_cthickening.measurableSet
  have hiN : Integrable (N.indicator (fun _ => 2 * L * h)) μ :=
    (integrable_const _).indicator hN
  have hiE : Integrable (E.indicator (fun _ => 2 * C)) μ :=
    (integrable_const _).indicator hE
  refine ⟨hint, hpoint, ?_⟩
  calc
    (∫ z, openBallOscillation (A.indicator g) h z ∂μ) ≤
        ∫ z, N.indicator (fun _ => 2 * L * h) z +
          E.indicator (fun _ => 2 * C) z ∂μ :=
      integral_mono hint (hiN.add hiE) hpoint
    _ = μ.real N * (2 * L * h) + μ.real E * (2 * C) := by
      rw [integral_add hiN hiE, integral_indicator_const _ hN, integral_indicator_const _ hE]
      simp only [smul_eq_mul]
    _ = 2 * L * h * μ.real (Metric.cthickening h A) +
        2 * C * μ.real (Metric.cthickening h (frontier A)) := by
      dsimp only [N, E]
      ring

end
end Shao.OQ3
