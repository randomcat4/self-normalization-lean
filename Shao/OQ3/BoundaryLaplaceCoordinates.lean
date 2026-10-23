import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem boundary_rate_chart_measure_and_integral (a0 level : ℝ) :
    let m : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (volume : Measure ℝ)
    let G : (ℝ × ℝ) → (ℝ × ℝ) := fun w =>
      (a0 + w.1, (a0 + w.1) ^ 2 / level ^ 2 - w.2)
    MeasurePreserving G m m ∧ MeasurableEmbedding G ∧
      ∀ (s : Set (ℝ × ℝ)) (f : (ℝ × ℝ) → ℝ),
        (IntegrableOn f (G '' s) m ↔ IntegrableOn (fun w => f (G w)) s m) ∧
        (∫ w : ℝ × ℝ in G '' s, f w ∂m) = ∫ w : ℝ × ℝ in s, f (G w) ∂m
 := by
  let m : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (volume : Measure ℝ)
  let G : (ℝ × ℝ) → (ℝ × ℝ) := fun w =>
    (a0 + w.1, (a0 + w.1) ^ 2 / level ^ 2 - w.2)
  have hshift : MeasurePreserving (fun p : ℝ × ℝ => (a0 + p.1, p.2)) m m :=
    (measurePreserving_add_left (volume : Measure ℝ) a0).prod
      (MeasurePreserving.id (volume : Measure ℝ))
  have hneg : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    ⟨measurable_neg, by simpa using (Real.map_volume_mul_left (a := -1) (by norm_num))⟩
  have hflip : MeasurePreserving (fun p : ℝ × ℝ => (p.1, -p.2)) m m :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod hneg
  have hshear : MeasurePreserving
      (fun p : ℝ × ℝ => (p.1, p.1 ^ 2 / level ^ 2 + p.2)) m m := by
    refine (MeasurePreserving.id (volume : Measure ℝ)).skew_product
      (μc := (volume : Measure ℝ)) (μd := (volume : Measure ℝ))
      (g := fun a z : ℝ => a ^ 2 / level ^ 2 + z) ?_ ?_
    · exact (show Continuous (fun p : ℝ × ℝ => p.1 ^ 2 / level ^ 2 + p.2) from by fun_prop).measurable
    · exact Filter.Eventually.of_forall fun a =>
        map_add_left_eq_self (volume : Measure ℝ) (a ^ 2 / level ^ 2)
  have hMP : MeasurePreserving G m m := by
    simpa only [Function.comp_def, G, sub_eq_add_neg] using hshear.comp (hflip.comp hshift)
  let e : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
    { toFun := G
      invFun := fun w => (w.1 - a0, w.1 ^ 2 / level ^ 2 - w.2)
      left_inv := by intro w; ext <;> dsimp [G] <;> ring
      right_inv := by intro w; ext <;> dsimp [G] <;> ring
      continuous_toFun := by dsimp [G]; fun_prop
      continuous_invFun := by fun_prop }
  have hEmb : MeasurableEmbedding G := e.isClosedEmbedding.measurableEmbedding
  refine ⟨hMP, hEmb, ?_⟩
  intro s f
  exact ⟨((hMP.restrict_image_emb hEmb s).integrable_comp_emb hEmb).symm,
    hMP.setIntegral_image_emb hEmb f s⟩

theorem boundary_rate_chart_rectangle_image (a0 level rho : ℝ) :
    let G : (ℝ × ℝ) → (ℝ × ℝ) := fun w =>
      (a0 + w.1, (a0 + w.1) ^ 2 / level ^ 2 - w.2)
    G '' {w : ℝ × ℝ | |w.1| ≤ rho ∧ 0 ≤ w.2 ∧ w.2 ≤ rho} =
      {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
        w.1 ^ 2 / level ^ 2 - rho ≤ w.2 ∧ w.2 ≤ w.1 ^ 2 / level ^ 2} := by
  let G : (ℝ × ℝ) → (ℝ × ℝ) := fun w =>
    (a0 + w.1, (a0 + w.1) ^ 2 / level ^ 2 - w.2)
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa only [G, add_sub_cancel_left] using hu.1
    · change (a0 + u.1) ^ 2 / level ^ 2 - rho ≤
        (a0 + u.1) ^ 2 / level ^ 2 - u.2
      linarith [hu.2.2]
    · change (a0 + u.1) ^ 2 / level ^ 2 - u.2 ≤ (a0 + u.1) ^ 2 / level ^ 2
      linarith [hu.2.1]
  · intro hw
    refine ⟨(w.1 - a0, w.1 ^ 2 / level ^ 2 - w.2), ?_, ?_⟩
    · exact ⟨hw.1, sub_nonneg.mpr hw.2.2, by linarith [hw.2.1]⟩
    · ext <;> dsimp [G] <;> ring

end
end Shao.OQ3
