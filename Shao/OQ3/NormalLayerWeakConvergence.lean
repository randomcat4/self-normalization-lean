import Shao.OQ3.NormalLayerConditionalLaw
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.Distributions.Gaussian.Real

namespace Shao.OQ3

open MeasureTheory Filter
open scoped Topology BigOperators

noncomputable section

theorem stage_normalLayerConditionalLaw_weak_tendsto (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q a : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (d : ℕ → ℝ) (hd : ∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M)
    (hlayer : ∀ᶠ n : ℕ in atTop, ∃ k : ℤ,
      d n + (n : ℝ) * q = dyadicMesh J * (k : ℝ)) :
    Tendsto (fun n : ℕ =>
      (⟨normalLayerConditionalLaw mu q a (d n) n,
        normalLayerConditionalLaw_isProbabilityMeasure mu q a (d n) n⟩ : ProbabilityMeasure ℝ))
      atTop (nhds (X := ProbabilityMeasure ℝ)
        (⟨ProbabilityTheory.gaussianReal 0 (Real.toNNReal (transverseVariance mu)),
          by infer_instance⟩ : ProbabilityMeasure ℝ)) := by
  have hT : 0 ≤ transverseVariance mu := (div_pos hD hS).le
  have hV : (Real.toNNReal (transverseVariance mu) : ℂ) =
      ((transverseVariance mu : ℝ) : ℂ) := by
    exact_mod_cast Real.coe_toNNReal (transverseVariance mu) hT
  refine ProbabilityMeasure.tendsto_of_tendsto_charFun
    (μ := fun n : ℕ => (⟨normalLayerConditionalLaw mu q a (d n) n,
      normalLayerConditionalLaw_isProbabilityMeasure mu q a (d n) n⟩ : ProbabilityMeasure ℝ))
    (μ₀ := (⟨ProbabilityTheory.gaussianReal 0 (Real.toNNReal (transverseVariance mu)),
      by infer_instance⟩ : ProbabilityMeasure ℝ)) ?_
  intro s
  have hGaussian : charFun
      (ProbabilityTheory.gaussianReal 0 (Real.toNNReal (transverseVariance mu))) s =
      Complex.exp ((-(transverseVariance mu * s ^ 2) / 2 : ℝ) : ℂ) := by
    rw [ProbabilityTheory.charFun_gaussianReal]
    congr 1
    rw [hV]
    push_cast
    ring
  have hchar := stage_normalLayerConditionalLaw_charFun_tendsto
    mu J q a hb hq ha hS hD hrange hpos s d hd hlayer
  simpa only [ProbabilityMeasure.coe_mk, hGaussian] using hchar

theorem stage_normalLayerConditionalLaw_real_tendsto (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q a : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (d : ℕ → ℝ) (hd : ∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M)
    (hlayer : ∀ᶠ n : ℕ in atTop, ∃ k : ℤ,
      d n + (n : ℝ) * q = dyadicMesh J * (k : ℝ))
    (A : Set ℝ)
    (hfrontier : ProbabilityTheory.gaussianReal 0 (Real.toNNReal (transverseVariance mu))
      (frontier A) = 0) :
    Tendsto (fun n : ℕ => (normalLayerConditionalLaw mu q a (d n) n).real A)
      atTop (nhds ((ProbabilityTheory.gaussianReal 0
        (Real.toNNReal (transverseVariance mu))).real A)) := by
  have hweak := stage_normalLayerConditionalLaw_weak_tendsto
    mu J q a hb hq ha hS hD hrange hpos d hd hlayer
  have hmeasure : Tendsto
      (fun n : ℕ => normalLayerConditionalLaw mu q a (d n) n A)
      atTop (nhds (ProbabilityTheory.gaussianReal 0
        (Real.toNNReal (transverseVariance mu)) A)) :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
      (μ := (⟨ProbabilityTheory.gaussianReal 0 (Real.toNNReal (transverseVariance mu)),
        by infer_instance⟩ : ProbabilityMeasure ℝ))
      (μs := fun n : ℕ => (⟨normalLayerConditionalLaw mu q a (d n) n,
        normalLayerConditionalLaw_isProbabilityMeasure mu q a (d n) n⟩ : ProbabilityMeasure ℝ))
      hweak (E := A) hfrontier
  exact (ENNReal.tendsto_toReal (measure_ne_top _ A)).comp hmeasure

end
end Shao.OQ3
