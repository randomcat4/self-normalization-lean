import Shao.OQ5.P35.ConditionalSample
import Shao.OQ5.P35.BackgroundMoments
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Actual selected-background laws after fixing category positions

All samples remain coordinates of the single original sample law. Independence
and common laws follow from the existing conditional decoded joint map.
-/

set_option autoImplicit false

namespace Shao.OQ5.P35

noncomputable section

open MeasureTheory ProbabilityTheory

theorem map_sampleDecoded_cond_fixed (n j : ℕ) (hj : 1 ≤ j)
    (J : Finset (Fin n)) (i : Fin n) :
    Measure.map (sampleDecoded i.val) (cond sampleLaw (fixedCategoryEvent n j J)) =
      (cond categoryMeasure (categoryPatternSet j J i)).prod noiseLaw := by
  have hpair (k : Fin n) :
      IsProbabilityMeasure ((cond categoryMeasure (categoryPatternSet j J k)).prod noiseLaw) := by
    have := categoryPatternLaw_isProbability j hj J k
    infer_instance
  calc
    Measure.map (sampleDecoded i.val) (cond sampleLaw (fixedCategoryEvent n j J)) =
        Measure.map (Function.eval i)
          (Measure.map (fun ω (k : Fin n) => sampleDecoded k.val ω)
            (cond sampleLaw (fixedCategoryEvent n j J))) := by
      rw [Measure.map_map (measurable_pi_apply i)
        (Measurable.of_eval (fun k : Fin n => measurable_sampleDecoded k.val))]
      rfl
    _ = Measure.map (Function.eval i)
        (Measure.pi (fun k : Fin n =>
          (cond categoryMeasure (categoryPatternSet j J k)).prod noiseLaw)) := by
      rw [decoded_cond_fixed_joint_map n j hj J]
    _ = _ := (measurePreserving_eval
      (fun k : Fin n => (cond categoryMeasure (categoryPatternSet j J k)).prod noiseLaw) i).map_eq

theorem iIndepFun_sampleDecoded_cond_fixed (n j : ℕ) (hj : 1 ≤ j)
    (J : Finset (Fin n)) :
    iIndepFun (fun i : Fin n => sampleDecoded i.val)
      (cond sampleLaw (fixedCategoryEvent n j J)) := by
  have := fixedCategoryEvent_cond_isProbability n j hj J
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i : Fin n => (measurable_sampleDecoded i.val).aemeasurable)).mpr
  rw [decoded_cond_fixed_joint_map n j hj J]
  congr 1
  funext i
  exact (map_sampleDecoded_cond_fixed n j hj J i).symm

theorem map_selectedBackgroundDecoded
    (m n j : ℕ) (hj : 1 ≤ j) (J : Finset (Fin n))
    (e : Fin m → Fin n) (he : Function.Injective e) (hback : ∀ r, e r ∉ J) :
    Measure.map (fun ω (r : Fin m) => sampleDecoded (e r).val ω)
        (cond sampleLaw (fixedCategoryEvent n j J)) =
      Measure.pi (fun _ : Fin m => (backgroundCategoryLaw j).prod noiseLaw) := by
  have hi := (iIndepFun_sampleDecoded_cond_fixed n j hj J).precomp he
  rw [hi.map_fun_eq_pi_map
    (fun r : Fin m => (measurable_sampleDecoded (e r).val).aemeasurable)]
  congr 1
  funext r
  rw [map_sampleDecoded_cond_fixed n j hj J (e r)]
  simp only [categoryPatternSet, hback r, ite_false, backgroundCategoryLaw]

theorem iIndepFun_selectedBackgroundFeature
    (m n j : ℕ) (hj : 1 ≤ j) (J : Finset (Fin n))
    (e : Fin m → Fin n) (he : Function.Injective e) (hback : ∀ r, e r ∉ J) :
    iIndepFun (fun r : Fin m => fun ω => categoryFeature (sampleCategory (e r).val ω))
      (cond sampleLaw (fixedCategoryEvent n j J)) := by
  have _ := hback
  have hi := (iIndepFun_sampleDecoded_cond_fixed n j hj J).precomp he
  have hc := hi.comp (fun _ (x : ℕ × ℝ) => categoryFeature x.1)
    (fun _ => (measurable_of_countable categoryFeature).comp measurable_fst)
  exact hc

private theorem map_sampleCategory_cond_background
    (n j : ℕ) (hj : 1 ≤ j) (J : Finset (Fin n))
    (i : Fin n) (hi : i ∉ J) :
    Measure.map (sampleCategory i.val) (cond sampleLaw (fixedCategoryEvent n j J)) =
      backgroundCategoryLaw j := by
  have := categoryPatternLaw_isProbability j hj J i
  calc
    Measure.map (sampleCategory i.val) (cond sampleLaw (fixedCategoryEvent n j J)) =
        Measure.map Prod.fst (Measure.map (sampleDecoded i.val)
          (cond sampleLaw (fixedCategoryEvent n j J))) := by
      rw [Measure.map_map measurable_fst (measurable_sampleDecoded i.val)]
      rfl
    _ = Measure.map Prod.fst
        ((cond categoryMeasure (categoryPatternSet j J i)).prod noiseLaw) := by
      rw [map_sampleDecoded_cond_fixed n j hj J i]
    _ = backgroundCategoryLaw j := by
      rw [Measure.map_fst_prod, measure_univ, one_smul]
      simp only [categoryPatternSet, hi, ite_false, backgroundCategoryLaw]

theorem identDistrib_selectedBackgroundFeature
    (m n j : ℕ) (hj : 1 ≤ j) (J : Finset (Fin n))
    (e : Fin m → Fin n) (he : Function.Injective e) (hback : ∀ r, e r ∉ J)
    (r : Fin m) :
    IdentDistrib (fun ω => categoryFeature (sampleCategory (e r).val ω)) (id : ℝ → ℝ)
      (cond sampleLaw (fixedCategoryEvent n j J))
      (Measure.map categoryFeature (backgroundCategoryLaw j)) := by
  have _ := he
  refine ⟨((measurable_of_countable categoryFeature).comp
    (measurable_sampleCategory (e r).val)).aemeasurable, measurable_id.aemeasurable, ?_⟩
  rw [Measure.map_id]
  calc
    Measure.map (fun ω => categoryFeature (sampleCategory (e r).val ω))
        (cond sampleLaw (fixedCategoryEvent n j J)) =
        Measure.map categoryFeature (Measure.map (sampleCategory (e r).val)
          (cond sampleLaw (fixedCategoryEvent n j J))) := by
      rw [Measure.map_map (measurable_of_countable categoryFeature)
        (measurable_sampleCategory (e r).val)]
      rfl
    _ = _ := by rw [map_sampleCategory_cond_background n j hj J (e r) (hback r)]

theorem iIndepFun_selectedBackgroundOffset
    (m n j : ℕ) (hj : 1 ≤ j) (J : Finset (Fin n))
    (e : Fin m → Fin n) (he : Function.Injective e) (hback : ∀ r, e r ∉ J) :
    iIndepFun (fun r : Fin m => fun ω => categoryOffset (sampleCategory (e r).val ω))
      (cond sampleLaw (fixedCategoryEvent n j J)) := by
  have _ := hback
  have hi := (iIndepFun_sampleDecoded_cond_fixed n j hj J).precomp he
  have hc := hi.comp (fun _ (x : ℕ × ℝ) => categoryOffset x.1)
    (fun _ => (measurable_of_countable categoryOffset).comp measurable_fst)
  exact hc

theorem identDistrib_selectedBackgroundOffset
    (m n j : ℕ) (hj : 1 ≤ j) (J : Finset (Fin n))
    (e : Fin m → Fin n) (he : Function.Injective e) (hback : ∀ r, e r ∉ J)
    (r : Fin m) :
    IdentDistrib (fun ω => categoryOffset (sampleCategory (e r).val ω)) (id : ℝ → ℝ)
      (cond sampleLaw (fixedCategoryEvent n j J))
      (Measure.map categoryOffset (backgroundCategoryLaw j)) := by
  have _ := he
  refine ⟨((measurable_of_countable categoryOffset).comp
    (measurable_sampleCategory (e r).val)).aemeasurable, measurable_id.aemeasurable, ?_⟩
  rw [Measure.map_id]
  calc
    Measure.map (fun ω => categoryOffset (sampleCategory (e r).val ω))
        (cond sampleLaw (fixedCategoryEvent n j J)) =
        Measure.map categoryOffset (Measure.map (sampleCategory (e r).val)
          (cond sampleLaw (fixedCategoryEvent n j J))) := by
      rw [Measure.map_map (measurable_of_countable categoryOffset)
        (measurable_sampleCategory (e r).val)]
      rfl
    _ = _ := by rw [map_sampleCategory_cond_background n j hj J (e r) (hback r)]

theorem memLp_backgroundFeature (j : ℕ) (hj : 1 ≤ j) :
    MemLp (id : ℝ → ℝ) 2 (Measure.map categoryFeature (backgroundCategoryLaw j)) := by
  apply (memLp_map_measure_iff aestronglyMeasurable_id
    (measurable_of_countable categoryFeature).aemeasurable).mpr
  change MemLp categoryFeature 2 (backgroundCategoryLaw j)
  exact (memLp_two_iff_integrable_sq
    (measurable_of_countable categoryFeature).aestronglyMeasurable).mpr
      (integrable_backgroundCategoryFeature_sq j hj)

theorem memLp_backgroundOffset (j : ℕ) (hj : 1 ≤ j) :
    MemLp (id : ℝ → ℝ) 2 (Measure.map categoryOffset (backgroundCategoryLaw j)) := by
  apply (memLp_map_measure_iff aestronglyMeasurable_id
    (measurable_of_countable categoryOffset).aemeasurable).mpr
  change MemLp categoryOffset 2 (backgroundCategoryLaw j)
  exact (memLp_two_iff_integrable_sq
    (measurable_of_countable categoryOffset).aestronglyMeasurable).mpr
      (integrable_backgroundCategoryOffset_sq j hj)

end

end Shao.OQ5.P35
