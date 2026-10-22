import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Two generic measure bridges for background preservation

These structural statements retain a full independent noise coordinate and
transport an independent variable through an actual positive conditional
restriction. Actual fixed-layer erasure is a separate specialization.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace Shao.OQ5.P52

noncomputable section

theorem indepFun_product_noise_lift
    {G C A B : Type*} [MeasurableSpace G] [MeasurableSpace C]
    [MeasurableSpace A] [MeasurableSpace B]
    (γ : Measure G) (ν : Measure C)
    [IsProbabilityMeasure γ] [IsProbabilityMeasure ν]
    {X : C → A} {Y : C → B}
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y ν) :
    IndepFun (fun z : G × C => X z.2)
      (fun z : G × C => (z.1, Y z.2)) (γ.prod ν) := by
  let μX : Measure A := ν.map X
  let μY : Measure B := ν.map Y
  let r : G × (A × B) → A × (G × B) := fun z => (z.2.1, (z.1, z.2.2))
  have hr : Measurable r :=
    (measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hXYmap : ν.map (fun c => (X c, Y c)) = μX.prod μY :=
    hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable
  have hreorder : (γ.prod (μX.prod μY)).map r = μX.prod (γ.prod μY) := by
    calc
      (γ.prod (μX.prod μY)).map r =
          (((γ.prod μX).prod μY).map MeasurableEquiv.prodAssoc).map r := by
        rw [Measure.prodAssoc_prod]
      _ = (((γ.prod μX).prod μY).map (Prod.map Prod.swap id)).map
          MeasurableEquiv.prodAssoc := by
        rw [Measure.map_map hr MeasurableEquiv.prodAssoc.measurable,
          Measure.map_map MeasurableEquiv.prodAssoc.measurable
            (measurable_swap.prodMap measurable_id)]
        rfl
      _ = (((γ.prod μX).map Prod.swap).prod (μY.map id)).map
          MeasurableEquiv.prodAssoc := by
        rw [Measure.map_prod_map _ _ measurable_swap measurable_id]
      _ = ((μX.prod γ).prod μY).map MeasurableEquiv.prodAssoc := by
        rw [Measure.prod_swap, Measure.map_id]
      _ = μX.prod (γ.prod μY) := Measure.prodAssoc_prod
  have hU : (γ.prod ν).map (fun z : G × C => X z.2) = μX := by
    change (γ.prod ν).map (X ∘ Prod.snd) = _
    rw [← Measure.map_map hX measurable_snd, Measure.map_snd_prod]
    simp only [measure_univ, one_smul]
    rfl
  have hV : (γ.prod ν).map (fun z : G × C => (z.1, Y z.2)) = γ.prod μY := by
    change (γ.prod ν).map (Prod.map id Y) = _
    rw [← Measure.map_prod_map _ _ measurable_id hY, Measure.map_id]
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (f := fun z : G × C => X z.2) (g := fun z : G × C => (z.1, Y z.2))
    (hX.comp measurable_snd).aemeasurable
    (measurable_fst.prodMk (hY.comp measurable_snd)).aemeasurable).mpr
  rw [hU, hV]
  calc
    (γ.prod ν).map (fun z : G × C => (X z.2, (z.1, Y z.2))) =
        ((γ.prod ν).map (Prod.map id (fun c => (X c, Y c)))).map r := by
      rw [Measure.map_map hr (measurable_id.prodMap (hX.prodMk hY))]
      rfl
    _ = (γ.prod (μX.prod μY)).map r := by
      rw [← Measure.map_prod_map _ _ measurable_id (hX.prodMk hY),
        Measure.map_id, hXYmap]
    _ = μX.prod (γ.prod μY) := hreorder

theorem map_cond_indep_eq_map
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → A} {Y : Ω → B}
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y μ)
    (D : Set A) (hD : MeasurableSet D) (hA : μ (X ⁻¹' D) ≠ 0) :
    (ProbabilityTheory.cond μ (X ⁻¹' D)).map Y = μ.map Y := by
  apply Measure.ext
  intro S hS
  calc
    ((ProbabilityTheory.cond μ (X ⁻¹' D)).map Y) S =
        (μ (X ⁻¹' D))⁻¹ * μ (X ⁻¹' D ∩ Y ⁻¹' S) := by
      rw [Measure.map_apply hY hS, ProbabilityTheory.cond_apply (hX hD)]
    _ = (μ (X ⁻¹' D))⁻¹ * (μ (X ⁻¹' D) * μ (Y ⁻¹' S)) := by
      rw [hXY.measure_inter_preimage_eq_mul D S hD hS]
    _ = μ (Y ⁻¹' S) :=
      ENNReal.inv_mul_cancel_left hA (measure_ne_top μ _)
    _ = (μ.map Y) S := (Measure.map_apply hY hS).symm

end
end Shao.OQ5.P52
