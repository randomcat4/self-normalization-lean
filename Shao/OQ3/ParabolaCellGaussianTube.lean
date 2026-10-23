import Shao.OQ3.ParabolaCellArcs
import Shao.OQ3.GaussianFiniteArcTube
import Shao.OQ3.StandardizedParabolaArcs
import Shao.OQ3.StandardizedFrontierTransport

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
noncomputable section

theorem actual_standardized_parabola_cell_frontier_tube_bound
    (n : ℕ) (hn : 1 ≤ n) (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (y : ℝ × ℝ)
    (aL aR qL qR level a0 rho : ℝ) (hrho : 0 ≤ rho)
    (hawidth : aR - aL ≤ 1 / (n : ℝ)) (hqwidth : qR - qL ≤ 1 / (n : ℝ))
    (h : ℝ) (hh : 0 < h) :
    let A : Set (ℝ × ℝ) := (Set.Ioc aL aR ×ˢ Set.Ioc qL qR) ∩
      {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
        0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
    let B : Set (ℝ × ℝ) :=
      (fun w : ℝ × ℝ => Real.sqrt (n : ℝ) • E (w - y)) '' A
    let C : ℝ := ‖(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ *
      (1 + 2 * (|a0| + rho) / level ^ 2)
    ((ProbabilityTheory.gaussianReal 0 1).prod
      (ProbabilityTheory.gaussianReal 0 1)).real (Metric.cthickening h (frontier B)) ≤
        384 * (C * h / Real.sqrt (n : ℝ) + h ^ 2) := by
  classical
  let A : Set (ℝ × ℝ) := (Set.Ioc aL aR ×ˢ Set.Ioc qL qR) ∩
    {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
      0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
  let B : Set (ℝ × ℝ) :=
    (fun w : ℝ × ℝ => Real.sqrt (n : ℝ) • E (w - y)) '' A
  let C : ℝ := ‖(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ *
    (1 + 2 * (|a0| + rho) / level ^ 2)
  change ((gaussianReal 0 1).prod (gaussianReal 0 1)).real
    (Metric.cthickening h (frontier B)) ≤ 384 * (C * h / Real.sqrt (n : ℝ) + h ^ 2)
  have hC : 0 ≤ C := by
    apply mul_nonneg (norm_nonneg _)
    exact add_nonneg (by norm_num)
      (div_nonneg (mul_nonneg (by norm_num) (add_nonneg (abs_nonneg _) hrho)) (sq_nonneg _))
  by_cases hA : A.Nonempty
  · obtain ⟨w, hw⟩ := hA
    rcases hw with ⟨⟨ha, hq⟩, hwindow⟩
    have habs := abs_le.mp hwindow.1
    have hclip : max aL (a0 - rho) ≤ min aR (a0 + rho) := by
      have hl : max aL (a0 - rho) ≤ w.1 := max_le ha.1.le (by linarith [habs.1])
      have hr : w.1 ≤ min aR (a0 + rho) := le_min ha.2 (by linarith [habs.2])
      exact hl.trans hr
    have hqorder : qL ≤ qR := hq.1.le.trans hq.2
    let L : ℝ := max aL (a0 - rho)
    let R : ℝ := min aR (a0 + rho)
    let curve : Fin 6 → ℝ → ℝ × ℝ := ![
      (fun t => (L + t * (R - L), qL)),
      (fun t => (L + t * (R - L), qR)),
      (fun t => (L, qL + t * (qR - qL))),
      (fun t => (R, qL + t * (qR - qL))),
      (fun t => (L + t * (R - L), (L + t * (R - L)) ^ 2 / level ^ 2)),
      (fun t => (L + t * (R - L), (L + t * (R - L)) ^ 2 / level ^ 2 - rho))]
    let K : NNReal := Real.toNNReal (C / Real.sqrt (n : ℝ))
    have hK : (K : ℝ) = C / Real.sqrt (n : ℝ) :=
      Real.coe_toNNReal _ (div_nonneg hC (Real.sqrt_nonneg _))
    have hcovA : frontier A ⊆ ⋃ i : Fin 6, curve i '' Set.Icc (0 : ℝ) 1 :=
      (actual_parabola_window_cell_six_compact_arcs aL aR qL qR level a0 rho).2
    have hLip : ∀ i : Fin 6, LipschitzOnWith K
        (fun t : ℝ => Real.sqrt (n : ℝ) • E (curve i t - y)) (Set.Icc (0 : ℝ) 1) :=
      actual_six_standardized_arcs_lipschitz n hn
        (E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) y aL aR qL qR level a0 rho
        hrho hclip hqorder hawidth hqwidth
    have hcover : frontier B ⊆ ⋃ i : Fin 6,
        (fun t : ℝ => Real.sqrt (n : ℝ) • E (curve i t - y)) '' Set.Icc (0 : ℝ) 1 := by
      change frontier ((fun v : ℝ × ℝ => Real.sqrt (n : ℝ) • E (v - y)) '' A) ⊆ _
      rw [standardized_frontier_image n hn E y A]
      rintro v ⟨x, hx, rfl⟩
      rcases Set.mem_iUnion.mp (hcovA hx) with ⟨i, t, ht, hti⟩
      refine Set.mem_iUnion.mpr ⟨i, ⟨t, ht, ?_⟩⟩
      exact congrArg (fun v : ℝ × ℝ => Real.sqrt (n : ℝ) • E (v - y)) hti
    have hb := standard_gaussian_plane_finite_arc_cover_tube_bound 6
      (fun i t => Real.sqrt (n : ℝ) • E (curve i t - y)) (fun _ => K)
      hLip (frontier B) hcover h hh
    calc
      _ ≤ 64 * (h * (∑ _i : Fin 6, (K : ℝ)) + (6 : ℝ) * h ^ 2) := hb
      _ = 384 * (C * h / Real.sqrt (n : ℝ) + h ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hK]
        ring
  · have hAempty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    have hB : B = ∅ := by simp only [B, hAempty, Set.image_empty]
    simp only [hB, frontier_empty, Metric.cthickening_empty, measureReal_empty]
    exact mul_nonneg (by norm_num)
      (add_nonneg (div_nonneg (mul_nonneg hC hh.le) (Real.sqrt_nonneg _)) (sq_nonneg _))

end
end Shao.OQ3

