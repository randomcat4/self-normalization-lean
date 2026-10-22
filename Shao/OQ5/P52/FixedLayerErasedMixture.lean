import Shao.OQ5.P52.FixedLayerErasedSample

/-!
# The actual erased prefix under exact-count and rare-event conditioning

Disjoint fixed-position cells have the same full erased vector law.
Finite additivity before normalization removes the position condition
without selecting a target subset or assuming equal mixture weights.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

attribute [local instance] fixedSampleLaw_isProbabilityMeasure
attribute [local instance] fixedErasedLaw_isProbabilityMeasure

theorem fixedLayerExactEvent_probability_pos (j n K : ℕ) (hK : K ≤ n) :
    0 < fixedSampleLaw.real (fixedLayerExactEvent j n K) := by
  rw [fixedLayerExactEvent_probability j n K hK]
  apply mul_pos
  · apply mul_pos
    · exact_mod_cast Nat.choose_pos hK
    · exact pow_pos (fixedLayerP_bounds j).1 _
  · apply pow_pos
    linarith [fixedLayerP_add_Q_lt_one j]

private theorem exact_event_ne_zero (j n K : ℕ) (hK : K ≤ n) :
    fixedSampleLaw (fixedLayerExactEvent j n K) ≠ 0 := by
  intro hz
  have he : fixedSampleLaw.real (fixedLayerExactEvent j n K) = 0 := by
    change (fixedSampleLaw (fixedLayerExactEvent j n K)).toReal = 0
    rw [hz]
    rfl
  exact (ne_of_gt (fixedLayerExactEvent_probability_pos j n K hK)) he

theorem fixedLayerExactEvent_cond_isProbabilityMeasure
    (j n K : ℕ) (hK : K ≤ n) :
    IsProbabilityMeasure (ProbabilityTheory.cond fixedSampleLaw (fixedLayerExactEvent j n K)) :=
  ProbabilityTheory.cond_isProbabilityMeasure (exact_event_ne_zero j n K hK)

private theorem measurable_erased_prefix (j n : ℕ) :
    Measurable (fun ω (i : Fin n) =>
      fixedEraseLayer j (fixedSampleCoordinate i.val ω)) :=
  measurable_pi_iff.mpr (fun i =>
    (measurable_fixedEraseLayer j).comp (measurable_fixedSampleCoordinate i.val))

private theorem position_intersection_mass (j n : ℕ) (J : Finset (Fin n))
    (B : Set (Fin n → LayerObs)) (hB : MeasurableSet B) :
    fixedSampleLaw (fixedLayerPositionEvent j n J ∩
      (fun ω (i : Fin n) => fixedEraseLayer j (fixedSampleCoordinate i.val ω)) ⁻¹' B) =
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) B *
        fixedSampleLaw (fixedLayerPositionEvent j n J) := by
  have hc : (ProbabilityTheory.cond fixedSampleLaw (fixedLayerPositionEvent j n J))
      ((fun ω (i : Fin n) => fixedEraseLayer j (fixedSampleCoordinate i.val ω)) ⁻¹' B) =
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) B := by
    rw [← Measure.map_apply (measurable_erased_prefix j n) hB,
      map_fixedLayerPositionEvent_cond_erasedPrefix]
  calc
    _ = (ProbabilityTheory.cond fixedSampleLaw (fixedLayerPositionEvent j n J))
        ((fun ω (i : Fin n) => fixedEraseLayer j (fixedSampleCoordinate i.val ω)) ⁻¹' B) *
        fixedSampleLaw (fixedLayerPositionEvent j n J) :=
      (ProbabilityTheory.cond_mul_eq_inter
        (measurableSet_fixedLayerPositionEvent j n J) _ fixedSampleLaw).symm
    _ = _ := by rw [hc]

theorem map_fixedLayerExactEvent_cond_erasedPrefix
    (j n K : ℕ) (hK : K ≤ n) :
    (ProbabilityTheory.cond fixedSampleLaw (fixedLayerExactEvent j n K)).map
      (fun ω (i : Fin n) => fixedEraseLayer j (fixedSampleCoordinate i.val ω)) =
      Measure.pi (fun _ : Fin n => fixedErasedLaw j) := by
  classical
  let s := (Finset.univ : Finset (Fin n)).powersetCard K
  let F : (ℕ → LayerObs) → (Fin n → LayerObs) :=
    fun ω i => fixedEraseLayer j (fixedSampleCoordinate i.val ω)
  let ν : Measure (Fin n → LayerObs) := Measure.pi (fun _ : Fin n => fixedErasedLaw j)
  have hF : Measurable F := measurable_erased_prefix j n
  have hsumA : fixedSampleLaw (fixedLayerExactEvent j n K) =
      ∑ J ∈ s, fixedSampleLaw (fixedLayerPositionEvent j n J) := by
    rw [fixedLayerExactEvent_eq_biUnion]
    exact measure_biUnion_finset
      (fun J _ J' _ hJJ => fixedLayerPositionEvent_disjoint j n J J' hJJ)
      (fun J _ => measurableSet_fixedLayerPositionEvent j n J)
  have hmix (B : Set (Fin n → LayerObs)) (hB : MeasurableSet B) :
      fixedSampleLaw (fixedLayerExactEvent j n K ∩ F ⁻¹' B) =
        ν B * fixedSampleLaw (fixedLayerExactEvent j n K) := by
    have hinter : fixedLayerExactEvent j n K ∩ F ⁻¹' B =
        ⋃ J ∈ s, fixedLayerPositionEvent j n J ∩ F ⁻¹' B := by
      rw [fixedLayerExactEvent_eq_biUnion]
      simp only [Set.iUnion_inter, s]
    calc
      _ = ∑ J ∈ s, fixedSampleLaw (fixedLayerPositionEvent j n J ∩ F ⁻¹' B) := by
        rw [hinter]
        exact measure_biUnion_finset
          (fun J _ J' _ hJJ =>
            (fixedLayerPositionEvent_disjoint j n J J' hJJ).mono
              Set.inter_subset_left Set.inter_subset_left)
          (fun J _ => (measurableSet_fixedLayerPositionEvent j n J).inter (hF hB))
      _ = ∑ J ∈ s, ν B * fixedSampleLaw (fixedLayerPositionEvent j n J) := by
        apply Finset.sum_congr rfl
        intro J _
        exact position_intersection_mass j n J B hB
      _ = ν B * (∑ J ∈ s, fixedSampleLaw (fixedLayerPositionEvent j n J)) :=
        (Finset.mul_sum _ _ _).symm
      _ = ν B * fixedSampleLaw (fixedLayerExactEvent j n K) := by rw [hsumA]
  have hnz := exact_event_ne_zero j n K hK
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (measurable_erased_prefix j n) hB,
    ProbabilityTheory.cond_apply (measurableSet_fixedLayerExactEvent j n K)]
  change (fixedSampleLaw (fixedLayerExactEvent j n K))⁻¹ *
    fixedSampleLaw (fixedLayerExactEvent j n K ∩ F ⁻¹' B) = ν B
  rw [hmix B hB, mul_comm (ν B) (fixedSampleLaw (fixedLayerExactEvent j n K))]
  exact ENNReal.inv_mul_cancel_left hnz (measure_ne_top fixedSampleLaw _)

theorem map_fixedLayerRareEvent_cond_erasedPrefix (j : ℕ) :
    (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)).map
      (fun ω (i : Fin (fixedLayerN j)) =>
        fixedEraseLayer j (fixedSampleCoordinate i.val ω)) =
      Measure.pi (fun _ : Fin (fixedLayerN j) => fixedErasedLaw j) := by
  exact map_fixedLayerExactEvent_cond_erasedPrefix j (fixedLayerN j) 2
    (le_trans (by norm_num : 2 ≤ 8) (fixedLayerN_ge_eight j))

private theorem map_rare_cond_erased_coordinate (j : ℕ) (i : Fin (fixedLayerN j)) :
    (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)).map
      (fun ω => fixedEraseLayer j (fixedSampleCoordinate i.val ω)) = fixedErasedLaw j := by
  calc
    _ = ((ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)).map
        (fun ω (k : Fin (fixedLayerN j)) =>
          fixedEraseLayer j (fixedSampleCoordinate k.val ω))).map (Function.eval i) := by
      rw [Measure.map_map (measurable_pi_apply i) (measurable_erased_prefix j (fixedLayerN j))]
      rfl
    _ = (Measure.pi (fun _ : Fin (fixedLayerN j) => fixedErasedLaw j)).map
        (Function.eval i) := by
      rw [map_fixedLayerRareEvent_cond_erasedPrefix]
    _ = fixedErasedLaw j :=
      (measurePreserving_eval (μ := fun _ : Fin (fixedLayerN j) => fixedErasedLaw j) i).map_eq

theorem iIndepFun_fixedLayerRareEvent_cond_erasedPrefix (j : ℕ) :
    iIndepFun (fun i : Fin (fixedLayerN j) =>
      fun ω => fixedEraseLayer j (fixedSampleCoordinate i.val ω))
      (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)) := by
  let _ : IsProbabilityMeasure
      (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)) :=
    fixedLayerExactEvent_cond_isProbabilityMeasure j (fixedLayerN j) 2
      (le_trans (by norm_num : 2 ≤ 8) (fixedLayerN_ge_eight j))
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (f := fun i : Fin (fixedLayerN j) =>
      fun ω => fixedEraseLayer j (fixedSampleCoordinate i.val ω))
    (fun i => ((measurable_fixedEraseLayer j).comp
      (measurable_fixedSampleCoordinate i.val)).aemeasurable)).mpr
  simpa only [map_rare_cond_erased_coordinate] using
    map_fixedLayerRareEvent_cond_erasedPrefix j

end
end Shao.OQ5.P52
