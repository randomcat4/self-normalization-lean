import Shao.OQ5.P52.FixedLayerModel
import Shao.OQ5.P52.BackgroundMeasureBridges
import Mathlib.Probability.Independence.InfinitePi

/-!
# Actual fixed-layer erasure and conditional background preservation

The derived background retains the full noise and every other category.
Its root law is the existing fixed observation law. Series deletion and
conditional sample laws are separate prerequisites.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

attribute [local instance] fixedObservationLaw_isProbabilityMeasure

def fixedEraseLayer (j : ℕ) (o : LayerObs) : LayerObs :=
  (o.1, fun k : ℕ => if k = j then 0 else o.2 k)

def fixedErasedLaw (j : ℕ) : Measure LayerObs :=
  fixedObservationLaw.map (fixedEraseLayer j)

theorem measurable_fixedEraseLayer (j : ℕ) :
    Measurable (fixedEraseLayer j) := by
  apply measurable_fst.prodMk
  apply measurable_pi_iff.mpr
  intro k
  by_cases hk : k = j
  · simpa only [fixedEraseLayer, ite_eq_left hk] using
      (measurable_const : Measurable (fun _ : LayerObs => (0 : Fin 3)))
  · simpa only [fixedEraseLayer, ite_eq_right hk, Function.comp_def] using
      ((measurable_pi_apply k).comp measurable_snd)

theorem fixedErasedLaw_isProbabilityMeasure (j : ℕ) :
    IsProbabilityMeasure (fixedErasedLaw j) := by
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_fixedEraseLayer j).aemeasurable).mpr
      fixedObservationLaw_isProbabilityMeasure

theorem fixedObservation_category_indep_fixedEraseLayer (j : ℕ) :
    IndepFun (fun o : LayerObs => o.2 j) (fixedEraseLayer j) fixedObservationLaw := by
  classical
  let ν := Shao.OQ5.P50.layerCategoryProductLaw fixedLayerP fixedLayerQ
  let _ := Shao.OQ5.P50.layerNoiseLaw_isProbabilityMeasure
  let _ := Shao.OQ5.P50.layerCategoryProductLaw_isProbabilityMeasure
    fixedLayerP fixedLayerQ (fun k => (fixedLayerP_bounds k).1.le)
    (fun k => (fixedLayerQ_bounds k).1.le)
    (fun k => (fixedLayerP_add_Q_lt_one k).le)
  let _ : ∀ k, IsProbabilityMeasure
      (Shao.OQ5.P50.layerMeasure (fixedLayerP k) (fixedLayerQ k)) :=
    fun k => Shao.OQ5.P50.layerMeasure_isProbabilityMeasure _ _
      (fixedLayerP_bounds k).1.le (fixedLayerQ_bounds k).1.le
      (fixedLayerP_add_Q_lt_one k).le
  let S : Set ℕ := {j}
  let T : Set ℕ := {k | k ≠ j}
  let e : (ℕ → Fin 3) → (ℕ → Fin 3) :=
    fun s k => if k = j then 0 else s k
  have he : Measurable e := by
    apply measurable_pi_iff.mpr
    intro k
    by_cases hk : k = j
    · simpa only [e, ite_eq_left hk] using
        (measurable_const : Measurable (fun _ : ℕ → Fin 3 => (0 : Fin 3)))
    · simpa only [e, ite_eq_right hk] using
        (measurable_pi_apply k : Measurable (fun s : ℕ → Fin 3 => s k))
  have hcoords : iIndepFun (fun k (s : ℕ → Fin 3) => s k) ν := by
    exact iIndepFun_infinitePi (P := fun k =>
      Shao.OQ5.P50.layerMeasure (fixedLayerP k) (fixedLayerQ k))
      (X := fun _ s => s) (fun _ => measurable_id)
  have hST : Disjoint S T := by
    apply Set.disjoint_left.mpr
    intro k hk hk'
    exact hk' (by simpa only [S, Set.mem_singleton_iff] using hk)
  have htuples := iIndepFun.indepFun_set S T hST hcoords
    (fun k => measurable_pi_apply k)
  let r : (T → Fin 3) → (ℕ → Fin 3) :=
    fun t k => if hk : k = j then 0 else t ⟨k, hk⟩
  have hr : Measurable r := by
    apply measurable_pi_iff.mpr
    intro k
    by_cases hk : k = j
    · simpa only [r, dite_eq_left hk] using
        (measurable_const : Measurable (fun _ : T → Fin 3 => (0 : Fin 3)))
    · simpa only [r, dite_eq_right hk] using
        (measurable_pi_apply (⟨k, hk⟩ : T))
  have hrcomp : r ∘ (fun (s : ℕ → Fin 3) (k : T) => s k) = e := by
    funext s k
    dsimp only [Function.comp_def, r, e]
    split_ifs <;> rfl
  have hcatErase : IndepFun (fun s : ℕ → Fin 3 => s j) e ν := by
    have h := htuples.comp
      (measurable_pi_apply (⟨j, by simp only [S, Set.mem_singleton_iff]⟩ : S)) hr
    rw [hrcomp] at h
    exact h
  exact indepFun_product_noise_lift Shao.OQ5.P50.layerNoiseLaw ν
    (measurable_pi_apply j) he hcatErase

private theorem fixed_category_event_ne_zero (j : ℕ) (a : Fin 3) :
    fixedObservationLaw {o : LayerObs | o.2 j = a} ≠ 0 := by
  have hm : Measurable (fun o : LayerObs => o.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  have hw : 0 < Shao.OQ5.P50.layerWeight (fixedLayerP j) (fixedLayerQ j) a := by
    unfold Shao.OQ5.P50.layerWeight
    split_ifs
    · linarith [fixedLayerP_add_Q_lt_one j]
    · exact (fixedLayerP_bounds j).1
    · exact (fixedLayerQ_bounds j).1
  change fixedObservationLaw ((fun o : LayerObs => o.2 j) ⁻¹' {a}) ≠ 0
  rw [← Measure.map_apply hm (measurableSet_singleton a),
    map_fixedObservation_category, Shao.OQ5.P50.layerMeasure_singleton]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr hw)

theorem map_cond_fixedObservation_fixedEraseLayer (j : ℕ) (a : Fin 3) :
    (ProbabilityTheory.cond fixedObservationLaw {o : LayerObs | o.2 j = a}).map
      (fixedEraseLayer j) = fixedErasedLaw j := by
  exact map_cond_indep_eq_map
    ((measurable_pi_apply j).comp measurable_snd) (measurable_fixedEraseLayer j)
    (fixedObservation_category_indep_fixedEraseLayer j) {a} (measurableSet_singleton a)
    (fixed_category_event_ne_zero j a)

theorem fixedErasedLaw_eq_cond_zero (j : ℕ) :
    fixedErasedLaw j =
      ProbabilityTheory.cond fixedObservationLaw {o : LayerObs | o.2 j = 0} := by
  let A0 : Set LayerObs := {o | o.2 j = 0}
  have hA0 : MeasurableSet A0 :=
    ((measurable_pi_apply j).comp measurable_snd) (measurableSet_singleton 0)
  have hae : fixedEraseLayer j =ᵐ[ProbabilityTheory.cond fixedObservationLaw A0] id := by
    filter_upwards [ProbabilityTheory.ae_cond_mem hA0] with o ho
    change o.2 j = 0 at ho
    apply Prod.ext
    · rfl
    · funext k
      change (if k = j then 0 else o.2 k) = o.2 k
      split_ifs with hk
      · subst k
        exact ho.symm
      · rfl
  calc
    fixedErasedLaw j =
        (ProbabilityTheory.cond fixedObservationLaw A0).map (fixedEraseLayer j) :=
      (map_cond_fixedObservation_fixedEraseLayer j 0).symm
    _ = (ProbabilityTheory.cond fixedObservationLaw A0).map id := Measure.map_congr hae
    _ = ProbabilityTheory.cond fixedObservationLaw A0 := Measure.map_id

theorem fixedErasedLaw_absolutelyContinuous (j : ℕ) :
    fixedErasedLaw j ≪ fixedObservationLaw := by
  rw [fixedErasedLaw_eq_cond_zero]
  exact ProbabilityTheory.cond_absolutelyContinuous

end
end Shao.OQ5.P52
