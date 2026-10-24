import Shao.C2.EndpointCDFTransfer

open scoped NNReal
noncomputable section
namespace Shao.C2.InitialCompletionError
open MeasureTheory ProbabilityTheory Set
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw Shao.C2.EndpointCDFTransfer

theorem zero_energy_removal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W Q : Ω → ℝ)
    (hW : AEMeasurable W P) (hQ : Measurable Q) (hQ0 : ∀ᵐ ω ∂P, 0 ≤ Q ω)
    (f : ℝ → ℝ) (hf : Measurable f) (hf0 : ∀ w, 0 ≤ f w) (hf1 : ∀ w, f w ≤ 1) :
    |(∫ ω, (if 0 < Q ω then f (W ω) else 0) ∂P) - ∫ ω, f (W ω) ∂P| ≤
      P.real {ω | Q ω = 0} := by
  let s : Set Ω := {ω | 0 < Q ω}
  have hs : MeasurableSet s := measurableSet_lt measurable_const hQ
  let g : Ω → ℝ := fun ω => f (W ω)
  have hg : Integrable g P := by
    refine (integrable_const (1 : ℝ)).mono' (hf.comp_aemeasurable hW).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 (W ω))]
      exact hf1 (W ω)
  have hzero : P.real sᶜ = P.real {ω | Q ω = 0} := by
    apply measureReal_congr
    filter_upwards [hQ0] with ω hω
    apply propext
    change ¬ 0 < Q ω ↔ Q ω = 0
    exact ⟨fun h => le_antisymm (le_of_not_gt h) hω, fun h => by rw [h]; exact lt_irrefl 0⟩
  have hc0 : 0 ≤ ∫ ω in sᶜ, g ω ∂P := integral_nonneg fun ω => hf0 (W ω)
  have hc1 : (∫ ω in sᶜ, g ω ∂P) ≤ P.real sᶜ := by
    calc
      _ ≤ ∫ _ in sᶜ, (1 : ℝ) ∂P := integral_mono_ae hg.integrableOn
        (integrable_const 1) (Filter.Eventually.of_forall fun ω => hf1 (W ω))
      _ = _ := by simp
  have hd : (∫ ω in s, g ω ∂P) - (∫ ω, g ω ∂P) = -(∫ ω in sᶜ, g ω ∂P) := by
    have ht := integral_add_compl hs hg
    linarith
  change |(∫ ω, s.indicator g ω ∂P) - (∫ ω, g ω ∂P)| ≤ _
  rw [integral_indicator hs, hd, abs_neg, abs_of_nonneg hc0]
  exact hc1.trans_eq hzero

theorem initial_marginal_error_of_cdf
    {Ω ΩB : Type*} [MeasurableSpace Ω] [MeasurableSpace ΩB]
    (P : Measure Ω) [IsProbabilityMeasure P] (W Q : Ω → ℝ)
    (hW : AEMeasurable W P) (hQ : Measurable Q) (hQ0 : ∀ᵐ ω ∂P, 0 ≤ Q ω)
    (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hB : IsBrownianReal B PB) (δ : ℝ) (hδ : 0 ≤ δ)
    (hCDF : ∀ x : ℝ,
      |P.real {ω | W ω ≤ x} - (gaussianReal 0 1).real (Set.Iic x)| ≤ δ)
    (a : ℝ) :
    |(∫ ω, (if 0 < Q ω then intervalCompletion (bridgeLaw B PB) a 0 1 (W ω) else 0) ∂P) -
      PB.real {ω | ∀ t : BridgeTime, |B ⟨(t : ℝ), t.property.1⟩ ω| < a}| ≤
      2 * δ + P.real {ω | Q ω = 0} := by
  let ν := bridgeLaw B PB
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_bridgeLaw B PB hB
  let μ := P.map W
  letI : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff hW).mpr inferInstance
  have hLaw : HasLaw W μ P := ⟨hW, rfl⟩
  have hCDF' (x : ℝ) : |μ.real (Set.Iic x) - (gaussianReal 0 1).real (Set.Iic x)| ≤ δ := by
    have hx := hLaw.measureReal_eq (measurableSet_Iic (a := x))
    change P.real {ω | W ω ≤ x} = μ.real (Set.Iic x) at hx
    rw [← hx]
    exact hCDF x
  have hm := InitialCompletionVariation.initial_interval_measurable ν a
  have htr := initial_completion_expectation_error ν μ (gaussianReal 0 1) δ hδ hCDF' a
  rw [integral_map hW hm.aestronglyMeasurable] at htr
  have hrem := zero_energy_removal P W Q hW hQ hQ0 _ hm
    (fun w => (completion_bounds ν a 0 1 w).2.2.2.2.1)
    (fun w => (completion_bounds ν a 0 1 w).2.2.2.2.2)
  rw [brownian_initial_marginal B PB hB a]
  have ht := abs_sub_le
    (∫ ω, (if 0 < Q ω then intervalCompletion ν a 0 1 (W ω) else 0) ∂P)
    (∫ ω, intervalCompletion ν a 0 1 (W ω) ∂P)
    (∫ w : ℝ, intervalCompletion ν a 0 1 w ∂(gaussianReal 0 1))
  exact ht.trans (by linarith)

theorem initial_joint_error_of_cdf
    {Ω ΩB : Type*} [MeasurableSpace Ω] [MeasurableSpace ΩB]
    (P : Measure Ω) [IsProbabilityMeasure P] (W Q : Ω → ℝ)
    (hW : AEMeasurable W P) (hQ : Measurable Q) (hQ0 : ∀ᵐ ω ∂P, 0 ≤ Q ω)
    (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hB : IsBrownianReal B PB) (δ : ℝ) (hδ : 0 ≤ δ)
    (hCDF : ∀ x : ℝ,
      |P.real {ω | W ω ≤ x} - (gaussianReal 0 1).real (Set.Iic x)| ≤ δ)
    (a v : ℝ) :
    |(∫ ω, (if 0 < Q ω then
        (if W ω ≤ v then intervalCompletion (bridgeLaw B PB) a 0 1 (W ω) else 0) else 0) ∂P) -
      PB.real {ω | (∀ t : BridgeTime, |B ⟨(t : ℝ), t.property.1⟩ ω| < a) ∧ B 1 ω ≤ v}| ≤
      2 * δ + P.real {ω | Q ω = 0} := by
  let ν := bridgeLaw B PB
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_bridgeLaw B PB hB
  let μ := P.map W
  letI : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff hW).mpr inferInstance
  have hLaw : HasLaw W μ P := ⟨hW, rfl⟩
  have hCDF' (x : ℝ) : |μ.real (Set.Iic x) - (gaussianReal 0 1).real (Set.Iic x)| ≤ δ := by
    have hx := hLaw.measureReal_eq (measurableSet_Iic (a := x))
    change P.real {ω | W ω ≤ x} = μ.real (Set.Iic x) at hx
    rw [← hx]
    exact hCDF x
  let f : ℝ → ℝ := fun w => if w ≤ v then intervalCompletion ν a 0 1 w else 0
  have hm : Measurable f :=
    (InitialCompletionVariation.initial_interval_measurable ν a).piecewise
      measurableSet_Iic measurable_const
  have hf0 (w : ℝ) : 0 ≤ f w := by
    dsimp [f]
    split_ifs
    · exact (completion_bounds ν a 0 1 w).2.2.2.2.1
    · exact le_rfl
  have hf1 (w : ℝ) : f w ≤ 1 := by
    dsimp [f]
    split_ifs
    · exact (completion_bounds ν a 0 1 w).2.2.2.2.2
    · norm_num
  have htr := initial_joint_expectation_error ν μ (gaussianReal 0 1) δ hδ hCDF' a v
  change |(∫ w, f w ∂μ) - ∫ w, f w ∂(gaussianReal 0 1)| ≤ 2 * δ at htr
  rw [integral_map hW hm.aestronglyMeasurable] at htr
  have hrem := zero_energy_removal P W Q hW hQ hQ0 f hm hf0 hf1
  rw [brownian_initial_joint B PB hB a v]
  have ht := abs_sub_le
    (∫ ω, (if 0 < Q ω then f (W ω) else 0) ∂P)
    (∫ ω, f (W ω) ∂P)
    (∫ w : ℝ, f w ∂(gaussianReal 0 1))
  exact ht.trans (by linarith)

end Shao.C2.InitialCompletionError
