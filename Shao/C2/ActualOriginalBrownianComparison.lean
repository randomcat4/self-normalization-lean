import Shao.C2.ActualBridgeIntervalTelescope
import Shao.Probability.SourceOriginalBrownianComparison

set_option autoImplicit false
noncomputable section
namespace Shao.C2.ActualOriginalBrownianComparison
open MeasureTheory ProbabilityTheory Shao.Probability
open Shao.Probability.SourcePermutationReveal
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.BridgeIntervalImageResolved Shao.C2.ActualBridgeIntervalTelescope
open Shao.C2.IntervalImageRevealBounds
open Shao.Probability.SourceOriginalBrownianComparison
open scoped BigOperators Classical NNReal

theorem actual_original_iid_brownian_small_window_comparison :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω ΩB : Type*} [MeasurableSpace Ω] [MeasurableSpace ΩB]
        (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
        IsBrownianReal B PB →
        ∀ (mu : Measure Ω) (rho : Measure ℝ)
          [IsProbabilityMeasure mu] [IsProbabilityMeasure rho]
          (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ),
          (∀ i, AEMeasurable (X i) mu) →
          iIndepFun X mu →
          (∀ i, IdentDistrib (X i) (id : ℝ → ℝ) mu rho) →
          Integrable (fun z : ℝ => z ^ 2) rho →
          (∫ z : ℝ, z ∂rho) = 0 → 0 < (∫ z : ℝ, z ^ 2 ∂rho) →
          let population : Ω → Shao.Path n := Shao.Probability.samplePath X
          let rawEnergy : Ω → ℝ := fun omega => ∑ i : Fin n, (X i omega) ^ 2
          let rawTerminal : Ω → ℝ := fun omega => ∑ i : Fin n, X i omega
          let M : Ω → ℝ := fun omega => Shao.absMax (population omega) hn
          let W : Ω → ℝ := fun omega => Shao.C1.normalizedEndpoint (population omega)
          let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂rho
          let scale : ℝ := Real.sqrt ((n : ℝ) * sigmaSq)
          let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / scale) rho
          let R : ℝ := Shao.truncationBudget normalizedLaw n 0
          ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
            let strictSurvival : Set Ω :=
              {omega | M omega < x * Real.sqrt (rawEnergy omega)}
            let weakCrossing : Set Ω :=
              {omega | x * Real.sqrt (rawEnergy omega) ≤ M omega}
            let brownianStrictSurvival : Set ΩB :=
              {omegaB | ∀ t : BridgeTime, |B ⟨(t : ℝ), t.property.1⟩ omegaB| < x}
            let brownianWeakCrossing : Set ΩB :=
              {omegaB | ∃ t : BridgeTime, x ≤ |B ⟨(t : ℝ), t.property.1⟩ omegaB|}
            (∀ omega : Ω,
              Shao.energy (population omega) = rawEnergy omega ∧
              Shao.prefixSum (population omega) n = rawTerminal omega ∧
              W omega = if 0 < rawEnergy omega then
                rawTerminal omega / Real.sqrt (rawEnergy omega) else 0) ∧
            AEMeasurable rawEnergy mu ∧ AEMeasurable M mu ∧ AEMeasurable W mu ∧
            |mu.real strictSurvival - PB.real brownianStrictSurvival| ≤ C * R ∧
            |mu.real weakCrossing - PB.real brownianWeakCrossing| ≤ C * R ∧
            (∀ v : ℝ,
              |mu.real (strictSurvival ∩ {omega : Ω | W omega ≤ v}) -
                PB.real (brownianStrictSurvival ∩ {omegaB : ΩB | B 1 omegaB ≤ v})| ≤ C * R ∧
              |mu.real (weakCrossing ∩ {omega : Ω | W omega ≤ v}) -
                PB.real (brownianWeakCrossing ∩ {omegaB : ΩB | B 1 omegaB ≤ v})| ≤ C * R) := by
  obtain ⟨C, hC, hmain⟩ := original_iid_actual_brownian_small_window_comparison
    compensatedProfileConstant compensatedProfileConstant_nonneg
  refine ⟨C, hC, ?_⟩
  intro Ω ΩB hΩ hΩB B PB hPB hB
  letI : IsProbabilityMeasure PB := hPB
  apply hmain B PB hB
  · intro w y T z hw hT hy hz
    exact actual_source_interval_differentiable B PB hB w y T z hw hy hz hT
  · intro w y T z beta hw hT hy hz hs hn
    simpa only [div_pow, one_pow, one_div, div_eq_mul_inv, mul_pow, one_mul, mul_assoc] using
      sourceRemainder_small_bound B PB hB w y T z beta hw hy hz hT hs hn

end Shao.C2.ActualOriginalBrownianComparison
