import Shao.OQ5.P50.LayeredProductLaw
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory
open scoped BigOperators

namespace Shao.OQ5.P50

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

private theorem pairCategory_measurable (j : ℕ) :
    Measurable (fun z : LayerObs × LayerObs => (z.1.2 j, z.2.2 j)) :=
  ((measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)).prodMk
    ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))

private theorem pairCategory_restrict_measurable (J : Finset ℕ) :
    Measurable (fun (z : LayerObs × LayerObs) (j : J) => (z.1.2 j, z.2.2 j)) :=
  measurable_pi_iff.mpr (fun j => pairCategory_measurable j)

theorem map_layerObservation_pair_category (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1) (j : ℕ) :
    ((layerObservationLaw p q).prod (layerObservationLaw p q)).map
      (fun z : LayerObs × LayerObs => (z.1.2 j, z.2.2 j)) =
        (layerMeasure (p j) (q j)).prod (layerMeasure (p j) (q j)) := by
  let _ := layerObservationLaw_isProbabilityMeasure p q hp hq hpq
  have hm : Measurable (fun o : LayerObs => o.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  change ((layerObservationLaw p q).prod (layerObservationLaw p q)).map
    (Prod.map (fun o : LayerObs => o.2 j) (fun o : LayerObs => o.2 j)) = _
  rw [← Measure.map_prod_map _ _ hm hm, map_layerObservation_category p q hp hq hpq]

theorem map_layerObservation_pair_category_restrict (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1)
    (J : Finset ℕ) :
    ((layerObservationLaw p q).prod (layerObservationLaw p q)).map
      (fun (z : LayerObs × LayerObs) (j : J) => (z.1.2 j, z.2.2 j)) =
        Measure.pi (fun j : J =>
          (layerMeasure (p j) (q j)).prod (layerMeasure (p j) (q j))) := by
  let _ := layerObservationLaw_isProbabilityMeasure p q hp hq hpq
  let _ : ∀ j : ℕ, IsProbabilityMeasure (layerMeasure (p j) (q j)) :=
    fun j => layerMeasure_isProbabilityMeasure (p j) (q j) (hp j) (hq j) (hpq j)
  let r : LayerObs → (J → Fin 3) := fun o j => o.2 j
  let ν : J → Measure (Fin 3) := fun j => layerMeasure (p j) (q j)
  have hr : Measurable r :=
    measurable_pi_iff.mpr (fun j => (measurable_pi_apply (j : ℕ)).comp measurable_snd)
  have hrr : Measurable (Prod.map r r) :=
    (hr.comp measurable_fst).prodMk (hr.comp measurable_snd)
  have hcopy : (layerObservationLaw p q).map r = Measure.pi ν :=
    map_layerObservation_category_restrict p q hp hq hpq J
  let e := MeasurableEquiv.arrowProdEquivProdArrow (Fin 3) (Fin 3) J
  have he := MeasurePreserving.symm e
    (measurePreserving_arrowProdEquivProdArrow (Fin 3) (Fin 3) J ν ν)
  have hprod : ((layerObservationLaw p q).prod (layerObservationLaw p q)).map
      (Prod.map r r) = (Measure.pi ν).prod (Measure.pi ν) := by
    rw [← Measure.map_prod_map _ _ hr hr, hcopy]
  calc
    _ = (((layerObservationLaw p q).prod (layerObservationLaw p q)).map
        (Prod.map r r)).map e.symm := by
      rw [Measure.map_map e.symm.measurable hrr]
      rfl
    _ = ((Measure.pi ν).prod (Measure.pi ν)).map e.symm := by rw [hprod]
    _ = _ := he.map_eq

theorem iIndepFun_layerObservation_pair_categories (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1) :
    ProbabilityTheory.iIndepFun
      (fun j (z : LayerObs × LayerObs) => (z.1.2 j, z.2.2 j))
      ((layerObservationLaw p q).prod (layerObservationLaw p q)) := by
  let _ := layerObservationLaw_isProbabilityMeasure p q hp hq hpq
  apply ProbabilityTheory.iIndepFun_iff_finset.mpr
  intro J
  apply (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (μ := (layerObservationLaw p q).prod (layerObservationLaw p q))
    (f := fun (j : J) (z : LayerObs × LayerObs) => (z.1.2 j, z.2.2 j))
    (fun j => (pairCategory_measurable j).aemeasurable)).mpr
  simp only [map_layerObservation_pair_category p q hp hq hpq]
  exact map_layerObservation_pair_category_restrict p q hp hq hpq J

theorem map_layerObservation_pair_categories (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1) :
    ((layerObservationLaw p q).prod (layerObservationLaw p q)).map
      (fun (z : LayerObs × LayerObs) (j : ℕ) => (z.1.2 j, z.2.2 j)) =
        Measure.infinitePi (fun j : ℕ =>
          (layerMeasure (p j) (q j)).prod (layerMeasure (p j) (q j))) := by
  let _ := layerObservationLaw_isProbabilityMeasure p q hp hq hpq
  have h := ProbabilityTheory.iIndepFun.map_fun_eq_infinitePi_map
    (fun j => pairCategory_measurable j)
    (iIndepFun_layerObservation_pair_categories p q hp hq hpq)
  simpa only [map_layerObservation_pair_category p q hp hq hpq] using h

theorem integrable_layerObservation_pair_finiteProduct (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1)
    (J : Finset ℕ) (F : ℕ → Fin 3 × Fin 3 → ℝ) :
    Integrable (fun z : LayerObs × LayerObs =>
      ∏ j ∈ J, F j (z.1.2 j, z.2.2 j))
      ((layerObservationLaw p q).prod (layerObservationLaw p q)) := by
  let _ := layerObservationLaw_isProbabilityMeasure p q hp hq hpq
  let _ : ∀ j : ℕ, IsProbabilityMeasure (layerMeasure (p j) (q j)) :=
    fun j => layerMeasure_isProbabilityMeasure (p j) (q j) (hp j) (hq j) (hpq j)
  let Φ : (J → Fin 3 × Fin 3) → ℝ := fun x => ∏ j : J, F j (x j)
  have hI : Integrable Φ (Measure.pi (fun j : J =>
      (layerMeasure (p j) (q j)).prod (layerMeasure (p j) (q j)))) :=
    Integrable.fintype_prod (fun j => integrable_layerMeasure_prod (p j) (q j) (F j))
  have hI' : Integrable Φ (((layerObservationLaw p q).prod (layerObservationLaw p q)).map
      (fun (z : LayerObs × LayerObs) (j : J) => (z.1.2 j, z.2.2 j))) := by
    rw [map_layerObservation_pair_category_restrict p q hp hq hpq J]
    exact hI
  convert hI'.comp_measurable (pairCategory_restrict_measurable J) using 1
  ext z
  exact (Finset.prod_coe_sort J (fun j : ℕ => F j (z.1.2 j, z.2.2 j))).symm

theorem integral_layerObservation_pair_finiteProduct (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1)
    (J : Finset ℕ) (F : ℕ → Fin 3 × Fin 3 → ℝ) :
    (∫ z : LayerObs × LayerObs, ∏ j ∈ J, F j (z.1.2 j, z.2.2 j)
      ∂(layerObservationLaw p q).prod (layerObservationLaw p q)) =
        ∏ j ∈ J, ∫ s : Fin 3 × Fin 3, F j s
          ∂(layerMeasure (p j) (q j)).prod (layerMeasure (p j) (q j)) := by
  let _ := layerObservationLaw_isProbabilityMeasure p q hp hq hpq
  let _ : ∀ j : ℕ, IsProbabilityMeasure (layerMeasure (p j) (q j)) :=
    fun j => layerMeasure_isProbabilityMeasure (p j) (q j) (hp j) (hq j) (hpq j)
  let R : LayerObs × LayerObs → (J → Fin 3 × Fin 3) :=
    fun z j => (z.1.2 j, z.2.2 j)
  let Φ : (J → Fin 3 × Fin 3) → ℝ := fun x => ∏ j : J, F j (x j)
  have hI : Integrable Φ (((layerObservationLaw p q).prod (layerObservationLaw p q)).map R) := by
    rw [map_layerObservation_pair_category_restrict p q hp hq hpq J]
    exact Integrable.fintype_prod (fun j => integrable_layerMeasure_prod (p j) (q j) (F j))
  have hmap := integral_map (pairCategory_restrict_measurable J).aemeasurable
    hI.aestronglyMeasurable
  calc
    _ = ∫ z : LayerObs × LayerObs, Φ (R z)
        ∂(layerObservationLaw p q).prod (layerObservationLaw p q) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z =>
        (Finset.prod_coe_sort J (fun j : ℕ => F j (z.1.2 j, z.2.2 j))).symm)
    _ = ∫ x, Φ x ∂((layerObservationLaw p q).prod (layerObservationLaw p q)).map R := hmap.symm
    _ = ∫ x, Φ x ∂Measure.pi (fun j : J =>
        (layerMeasure (p j) (q j)).prod (layerMeasure (p j) (q j))) := by
      rw [map_layerObservation_pair_category_restrict p q hp hq hpq J]
    _ = ∏ j : J, ∫ s : Fin 3 × Fin 3, F j s
        ∂(layerMeasure (p j) (q j)).prod (layerMeasure (p j) (q j)) :=
      integral_fintype_prod_eq_prod (fun (j : J) (s : Fin 3 × Fin 3) => F j s)
    _ = _ := Finset.prod_coe_sort J (fun j : ℕ => ∫ s : Fin 3 × Fin 3, F j s
      ∂(layerMeasure (p j) (q j)).prod (layerMeasure (p j) (q j)))

end
end Shao.OQ5.P50
