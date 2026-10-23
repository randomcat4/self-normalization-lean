import Shao.OQ3.CellBoundaryOscillation
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace Shao.OQ3
open Classical
open scoped Topology
noncomputable section

def openBallOscillation (f : (ℝ × ℝ) → ℝ) (h : ℝ) (z : ℝ × ℝ) : ℝ :=
  sSup (insert 0 {r : ℝ | ∃ u ∈ Metric.ball z h, ∃ v ∈ Metric.ball z h,
    r = |f u - f v|})

theorem open_ball_oscillation_properties
    (f : (ℝ × ℝ) → ℝ) (C h : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, |f x| ≤ C) :
    (∀ z, 0 ≤ openBallOscillation f h z ∧ openBallOscillation f h z ≤ 2 * C) ∧
    (∀ z, ∀ u ∈ Metric.ball z h, ∀ v ∈ Metric.ball z h,
      |f u - f v| ≤ openBallOscillation f h z) ∧
    (∀ t : ℝ, IsOpen {z : ℝ × ℝ | t < openBallOscillation f h z}) ∧
    Measurable (openBallOscillation f h) := by
  classical
  let S : (ℝ × ℝ) → Set ℝ := fun z =>
    insert 0 {r : ℝ | ∃ u ∈ Metric.ball z h, ∃ v ∈ Metric.ball z h,
      r = |f u - f v|}
  have hzero (z : ℝ × ℝ) : (0 : ℝ) ∈ S z := Set.mem_insert _ _
  have hupper (z : ℝ × ℝ) : ∀ r ∈ S z, r ≤ 2 * C := by
    intro r hr
    rcases Set.mem_insert_iff.mp hr with rfl | hr
    · linarith
    · rcases hr with ⟨u, hu, v, hv, rfl⟩
      calc
        |f u - f v| ≤ |f u| + |f v| := by
          simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (f u) (-f v)
        _ ≤ 2 * C := by linarith [hbound u, hbound v]
  have hbdd (z : ℝ × ℝ) : BddAbove (S z) := ⟨2 * C, hupper z⟩
  have hnonneg (z : ℝ × ℝ) : 0 ≤ openBallOscillation f h z :=
    le_csSup (hbdd z) (hzero z)
  have hsize (z : ℝ × ℝ) : openBallOscillation f h z ≤ 2 * C :=
    csSup_le ⟨0, hzero z⟩ (hupper z)
  have hpair : ∀ z, ∀ u ∈ Metric.ball z h, ∀ v ∈ Metric.ball z h,
      |f u - f v| ≤ openBallOscillation f h z := by
    intro z u hu v hv
    exact le_csSup (hbdd z) (Set.mem_insert_of_mem 0 ⟨u, hu, v, hv, rfl⟩)
  have hopen : ∀ t : ℝ, IsOpen {z : ℝ × ℝ | t < openBallOscillation f h z} := by
    intro t
    by_cases ht : t < 0
    · have heq : {z : ℝ × ℝ | t < openBallOscillation f h z} = Set.univ := by
        apply Set.eq_univ_of_forall
        intro z
        exact ht.trans_le (hnonneg z)
      rw [heq]
      exact isOpen_univ
    · have ht0 : 0 ≤ t := le_of_not_gt ht
      have heq : {z : ℝ × ℝ | t < openBallOscillation f h z} =
          ⋃ (u : ℝ × ℝ) (v : ℝ × ℝ) (_ : t < |f u - f v|),
            Metric.ball u h ∩ Metric.ball v h := by
        ext z
        constructor
        · intro hz
          obtain ⟨r, hr, htr⟩ := exists_lt_of_lt_csSup ⟨0, hzero z⟩ hz
          rcases Set.mem_insert_iff.mp hr with rfl | hr
          · exact (not_lt_of_ge ht0 htr).elim
          · rcases hr with ⟨u, hu, v, hv, rfl⟩
            refine Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr
              ⟨v, Set.mem_iUnion.mpr ⟨htr, ?_⟩⟩⟩
            constructor
            · simpa only [Metric.mem_ball, dist_comm] using hu
            · simpa only [Metric.mem_ball, dist_comm] using hv
        · intro hz
          rcases Set.mem_iUnion.mp hz with ⟨u, hz⟩
          rcases Set.mem_iUnion.mp hz with ⟨v, hz⟩
          rcases Set.mem_iUnion.mp hz with ⟨huv, hz⟩
          apply huv.trans_le
          apply hpair z u
          · simpa only [Metric.mem_ball, dist_comm] using hz.1
          · simpa only [Metric.mem_ball, dist_comm] using hz.2
      rw [heq]
      exact isOpen_iUnion fun u => isOpen_iUnion fun v =>
        isOpen_iUnion fun _ => Metric.isOpen_ball.inter Metric.isOpen_ball
  refine ⟨fun z => ⟨hnonneg z, hsize z⟩, hpair, hopen, ?_⟩
  exact measurable_of_Ioi fun t => (hopen t).measurableSet

theorem open_ball_oscillation_integrable
    (μ : MeasureTheory.Measure (ℝ × ℝ)) [MeasureTheory.IsFiniteMeasure μ]
    (f : (ℝ × ℝ) → ℝ) (C h : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, |f x| ≤ C) :
    MeasureTheory.Integrable (openBallOscillation f h) μ := by
  obtain ⟨hsize, hpair, hopen, hmeas⟩ :=
    open_ball_oscillation_properties f C h hC hbound
  apply (MeasureTheory.integrable_const (2 * C)).mono' hmeas.aestronglyMeasurable
  exact MeasureTheory.ae_of_all μ fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hsize z).1]
    exact (hsize z).2

end
end Shao.OQ3
