import Shao.C2.ActualOriginalBrownianComparison
import Shao.C2.ActualBrownianCrossingLower

set_option autoImplicit false
noncomputable section
namespace Shao.C2.ActualOriginalCompactRelative
open MeasureTheory ProbabilityTheory Shao.Probability
open Shao.C2.BridgeDomination
open Shao.C2.ActualOriginalBrownianComparison Shao.C2.ActualBrownianCrossingLower
open scoped BigOperators Classical NNReal

theorem actual_original_iid_absolute_small_window_relative :
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
            let weakCrossing : Set Ω :=
              {omega | x * Real.sqrt (rawEnergy omega) ≤ M omega}
            let H : ℝ := PB.real
              {omegaB | ∃ t : BridgeTime,
                x ≤ |B ⟨(t : ℝ), t.property.1⟩ omegaB|}
            0 < H ∧ |mu.real weakCrossing / H - 1| ≤ C * R := by
  obtain ⟨C0, hC0, hmain⟩ := actual_original_iid_brownian_small_window_comparison
  have hTail : 0 < Shao.standardNormalTail 1 := (Shao.standardNormalTail_basic.2.2.1 1).1
  refine ⟨C0 / Shao.standardNormalTail 1, div_pos hC0 hTail, ?_⟩
  intro Ω ΩB hΩ hΩB B PB hPB hB mu rho hmu hrho n hn X hX hIndep hLaw h2 hmean hsecond
    population rawEnergy rawTerminal M W sigmaSq scale normalizedLaw R x hx0 hx1 weakCrossing H
  letI : IsProbabilityMeasure PB := hPB
  letI : IsProbabilityMeasure mu := hmu
  letI : IsProbabilityMeasure rho := hrho
  have hh := hmain B PB hB mu rho n hn X hX hIndep hLaw h2 hmean hsecond x hx0 hx1
  have habs : |mu.real weakCrossing - H| ≤ C0 * R := hh.2.2.2.2.2.1
  have hLower : Shao.standardNormalTail 1 ≤ H :=
    brownian_weak_absolute_crossing_small_window_lower B PB hB x hx1
  have hH : 0 < H := hTail.trans_le hLower
  have hCR : 0 ≤ C0 * R := (abs_nonneg _).trans habs
  refine ⟨hH, ?_⟩
  calc
    |mu.real weakCrossing / H - 1| = |(mu.real weakCrossing - H) / H| := by
      rw [sub_div, div_self hH.ne']
    _ = |mu.real weakCrossing - H| / H := by rw [abs_div, abs_of_pos hH]
    _ ≤ (C0 * R) / H := div_le_div_of_nonneg_right habs hH.le
    _ ≤ (C0 * R) / Shao.standardNormalTail 1 :=
      div_le_div_of_nonneg_left hCR hTail hLower
    _ = (C0 / Shao.standardNormalTail 1) * R := by ring

end Shao.C2.ActualOriginalCompactRelative
