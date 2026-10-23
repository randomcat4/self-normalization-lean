import Shao.OQ3.GaussianCurveTube

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
noncomputable section

theorem standard_gaussian_plane_finite_arc_cover_tube_bound
    (m : ℕ) (f : Fin m → ℝ → ℝ × ℝ) (K : Fin m → NNReal)
    (hf : ∀ i, LipschitzOnWith (K i) (f i) (Set.Icc (0 : ℝ) 1))
    (F : Set (ℝ × ℝ))
    (hcover : F ⊆ ⋃ i : Fin m, f i '' Set.Icc (0 : ℝ) 1)
    (h : ℝ) (hh : 0 < h) :
    ((ProbabilityTheory.gaussianReal 0 1).prod
      (ProbabilityTheory.gaussianReal 0 1)).real (Metric.cthickening h F) ≤
        64 * (h * (∑ i : Fin m, (K i : ℝ)) + (m : ℝ) * h ^ 2) := by
  classical
  let Φ : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)
  let U : Set (ℝ × ℝ) := ⋃ i : Fin m, f i '' Set.Icc (0 : ℝ) 1
  let H : Fin m → Set (ℝ × ℝ) :=
    fun i => Metric.cthickening h (f i '' Set.Icc (0 : ℝ) 1)
  have hU : IsCompact U := isCompact_iUnion fun i =>
    isCompact_Icc.image_of_continuousOn (hf i).continuousOn
  have hclosure : closure F ⊆ U := closure_minimal hcover hU.isClosed
  have hsub : Metric.cthickening h F ⊆ ⋃ i : Fin m, H i := by
    intro z hz
    rw [Metric.cthickening_eq_biUnion_closedBall F hh.le] at hz
    rcases Set.mem_iUnion.mp hz with ⟨x, hz⟩
    rcases Set.mem_iUnion.mp hz with ⟨hx, hz⟩
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hclosure hx)
    exact Set.mem_iUnion.mpr ⟨i, Metric.closedBall_subset_cthickening hxi h hz⟩
  calc
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).real (Metric.cthickening h F) ≤
        Φ.real (⋃ i : Fin m, H i) := measureReal_mono hsub (measure_ne_top Φ _)
    _ ≤ ∑ i : Fin m, Φ.real (H i) := measureReal_iUnion_fintype_le H
    _ ≤ ∑ i : Fin m, 64 * ((K i : ℝ) * h + h ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      exact standard_gaussian_plane_lipschitz_arc_tube_bound (f i) (K i) (hf i) h hh
    _ = 64 * (h * (∑ i : Fin m, (K i : ℝ)) + (m : ℝ) * h ^ 2) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end
end Shao.OQ3

