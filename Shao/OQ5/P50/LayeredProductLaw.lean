import Shao.OQ5.P50.ThreeStateLaw
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory

namespace Shao.OQ5.P50

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

/-- Actual uniform law on the interval [-1,1]. -/
def layerNoiseLaw : Measure ℝ :=
  ProbabilityTheory.cond volume (Set.Icc (-1 : ℝ) 1)

/-- The full countable product of the actual three-state source marginals. -/
def layerCategoryProductLaw (p q : ℕ → ℝ) : Measure (ℕ → Fin 3) :=
  Measure.infinitePi (fun j : ℕ => layerMeasure (p j) (q j))

/-- The entire observation law, with independent G and all categorical layers. -/
def layerObservationLaw (p q : ℕ → ℝ) : Measure LayerObs :=
  layerNoiseLaw.prod (layerCategoryProductLaw p q)

theorem layerNoiseLaw_isProbabilityMeasure : IsProbabilityMeasure layerNoiseLaw := by
  unfold layerNoiseLaw
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Icc]
    norm_num
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

attribute [local instance] layerNoiseLaw_isProbabilityMeasure

theorem layerNoiseLaw_ae_mem :
    ∀ᵐ g ∂layerNoiseLaw, g ∈ Set.Icc (-1 : ℝ) 1 :=
  ProbabilityTheory.ae_cond_mem measurableSet_Icc

private theorem layerFactors_probability (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1) :
    ∀ j, IsProbabilityMeasure (layerMeasure (p j) (q j)) :=
  fun j => layerMeasure_isProbabilityMeasure (p j) (q j) (hp j) (hq j) (hpq j)

theorem layerCategoryProductLaw_isProbabilityMeasure (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1) :
    IsProbabilityMeasure (layerCategoryProductLaw p q) := by
  let _ := layerFactors_probability p q hp hq hpq
  unfold layerCategoryProductLaw
  infer_instance

theorem layerObservationLaw_isProbabilityMeasure (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1) :
    IsProbabilityMeasure (layerObservationLaw p q) := by
  let _ := layerCategoryProductLaw_isProbabilityMeasure p q hp hq hpq
  unfold layerObservationLaw
  infer_instance

theorem map_layerObservation_first (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1) :
    (layerObservationLaw p q).map Prod.fst = layerNoiseLaw := by
  let _ := layerCategoryProductLaw_isProbabilityMeasure p q hp hq hpq
  unfold layerObservationLaw
  rw [Measure.map_fst_prod]
  simp

theorem map_layerObservation_categories (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1) :
    (layerObservationLaw p q).map Prod.snd = layerCategoryProductLaw p q := by
  let _ := layerCategoryProductLaw_isProbabilityMeasure p q hp hq hpq
  unfold layerObservationLaw
  rw [Measure.map_snd_prod]
  simp

theorem map_layerObservation_category (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1) (j : ℕ) :
    (layerObservationLaw p q).map (fun o => o.2 j) = layerMeasure (p j) (q j) := by
  let _ := layerFactors_probability p q hp hq hpq
  change (layerObservationLaw p q).map ((fun s : ℕ → Fin 3 => s j) ∘ Prod.snd) = _
  rw [← Measure.map_map (measurable_pi_apply j) measurable_snd,
    map_layerObservation_categories p q hp hq hpq]
  exact Measure.infinitePi_map_eval (fun j => layerMeasure (p j) (q j)) j

theorem layerObservation_first_ae_mem (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1) :
    ∀ᵐ o ∂layerObservationLaw p q, o.1 ∈ Set.Icc (-1 : ℝ) 1 := by
  have h : ∀ᵐ g ∂(layerObservationLaw p q).map Prod.fst, g ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [map_layerObservation_first p q hp hq hpq]
    exact layerNoiseLaw_ae_mem
  exact ae_of_ae_map measurable_fst.aemeasurable h

theorem layerObservation_first_indep_categories (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1) :
    ProbabilityTheory.IndepFun Prod.fst Prod.snd (layerObservationLaw p q) := by
  let _ := layerCategoryProductLaw_isProbabilityMeasure p q hp hq hpq
  exact ProbabilityTheory.indepFun_prod measurable_id measurable_id

theorem iIndepFun_layerObservation_categories (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1) :
    ProbabilityTheory.iIndepFun (fun j (o : LayerObs) => o.2 j) (layerObservationLaw p q) := by
  let _ := layerObservationLaw_isProbabilityMeasure p q hp hq hpq
  apply (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
    (P := layerObservationLaw p q) (X := fun j (o : LayerObs) => o.2 j)
    (fun j => (measurable_pi_apply j).comp measurable_snd)).mpr
  change (layerObservationLaw p q).map Prod.snd =
    Measure.infinitePi (fun j => (layerObservationLaw p q).map (fun o : LayerObs => o.2 j))
  simp only [map_layerObservation_category p q hp hq hpq]
  exact map_layerObservation_categories p q hp hq hpq

theorem map_layerObservation_category_pair (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1)
    (i j : ℕ) (hij : i ≠ j) :
    (layerObservationLaw p q).map (fun o => (o.2 i, o.2 j)) =
      (layerMeasure (p i) (q i)).prod (layerMeasure (p j) (q j)) := by
  let _ := layerFactors_probability p q hp hq hpq
  change (layerObservationLaw p q).map
    ((fun s : ℕ → Fin 3 => (s i, s j)) ∘ Prod.snd) = _
  rw [← Measure.map_map ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
    measurable_snd, map_layerObservation_categories p q hp hq hpq]
  exact Measure.infinitePi_map_eval_prod (P := fun j => layerMeasure (p j) (q j)) hij

theorem map_layerObservation_category_restrict (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1)
    (J : Finset ℕ) :
    (layerObservationLaw p q).map (fun o (j : J) => o.2 j) =
      Measure.pi (fun j : J => layerMeasure (p j) (q j)) := by
  let _ := layerFactors_probability p q hp hq hpq
  have hrestrict : Measurable (J.restrict : (ℕ → Fin 3) → (J → Fin 3)) :=
    measurable_pi_iff.mpr (fun j => measurable_pi_apply (j : ℕ))
  change (layerObservationLaw p q).map (J.restrict ∘ Prod.snd) = _
  rw [← Measure.map_map hrestrict measurable_snd,
    map_layerObservation_categories p q hp hq hpq]
  exact Measure.infinitePi_map_restrict (μ := fun j => layerMeasure (p j) (q j)) (I := J)

end
end Shao.OQ5.P50
