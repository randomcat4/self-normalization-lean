import Shao.Probability.FiniteIID
import Shao.C1.IntegratedPermutationTelescope
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
namespace Shao.C1.UniformPermutationIIDLaw
open MeasureTheory ProbabilityTheory
open Shao.C1.IntegratedPermutationTelescope

def reorderedSample {n : ℕ} {Ω : Type*} (X : Fin n → Ω → ℝ)
    (p : Ω × Equiv.Perm (Fin n)) : Shao.Path n := fun i => X (p.2 i) p.1

theorem measurable_reorderedSample (n : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace (Equiv.Perm (Fin n))] [MeasurableSingletonClass (Equiv.Perm (Fin n))]
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) :
    Measurable (reorderedSample X) := by
  exact measurable_from_prod_countable_left fun σ =>
    Measurable.of_eval fun i => hX (σ i)

theorem iid_reorderedSample_hasLaw (n : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace (Equiv.Perm (Fin n))] [MeasurableSingletonClass (Equiv.Perm (Fin n))]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν) :
    HasLaw (reorderedSample X) (Measure.pi (fun _ : Fin n => ν))
      (μ.prod (uniformPermutationLaw n)) := by
  classical
  let := uniformPermutationLaw_isProbability n
  have hm := measurable_reorderedSample n X hX
  refine ⟨hm.aemeasurable, ?_⟩
  ext s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply_symm (hm hs)]
  have hsection (σ : Equiv.Perm (Fin n)) :
      μ ((fun ω => (ω, σ)) ⁻¹' (reorderedSample X ⁻¹' s)) =
        (Measure.pi (fun _ : Fin n => ν)) s := by
    have hfixed := Shao.Probability.iid_samplePath_map_eq_pi
      (fun i => hX (σ i)) (hIndep.precomp σ.injective) (fun i => hLaw (σ i))
    have happ := congrArg (fun ρ : Measure (Shao.Path n) => ρ s) hfixed
    rw [Measure.map_apply (Shao.Probability.measurable_samplePath (fun i => hX (σ i))) hs]
      at happ
    exact happ
  simp only [hsection, lintegral_const, measure_univ, mul_one]

theorem iid_iterated_reordered_integral (n : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace (Equiv.Perm (Fin n))] [MeasurableSingletonClass (Equiv.Perm (Fin n))]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (F : Shao.Path n → ℝ) (hF : Measurable F)
    (hFint : Integrable F (Measure.pi (fun _ : Fin n => ν))) :
    (∫ ω, ∫ σ, F (reorderedSample X (ω, σ)) ∂(uniformPermutationLaw n) ∂μ) =
      ∫ z, F z ∂(Measure.pi (fun _ : Fin n => ν)) := by
  let := uniformPermutationLaw_isProbability n
  have hlaw := iid_reorderedSample_hasLaw n μ ν X hX hIndep hLaw
  have hint := hlaw.integrable_comp hFint
  simpa only [Function.comp_apply] using
    (integral_prod (F ∘ reorderedSample X) hint).symm.trans
      (hlaw.integral_comp hF.aestronglyMeasurable)

end Shao.C1.UniformPermutationIIDLaw
