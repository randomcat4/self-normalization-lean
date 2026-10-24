import Shao.C2.AuxiliaryProductC1Endpoint
import Shao.C2.AuxiliaryCenteredProductLaw
import Shao.C2.AuxiliarySourceGaussian

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Shao.C2.AuxiliaryRareTiltProbability
open MeasureTheory ProbabilityTheory

theorem auxiliary_actual_rare_tilt_probability :
    ∃ C : ℝ, 0 < C ∧
      ∀ rhoStar : ℝ, 0 < rhoStar → rhoStar ≤ 1 / 16 →
        ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu],
          Integrable (fun z : ℝ => z ^ 2) nu →
          Integrable (fun z : ℝ => |z| ^ 3) nu →
          (∫ z : ℝ, z ∂nu) = 0 →
          (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
          ∀ (L s : ℝ), 0 ≤ L → 0 ≤ s →
            ∀ (n : ℕ) (x : ℝ), 1 ≤ x →
              s * (n : ℝ) ≤ L * x ^ 2 →
              4000000 * (1 + L) ^ 2 * (∫ z : ℝ, |z| ^ 3 ∂nu) ^ 2 *
                (1 + x) ^ 6 ≤ (n : ℝ) →
              (768 / rhoStar) ^ 2 * (∫ z : ℝ, |z| ^ 3 ∂nu) ^ 2 *
                (1 + x) ^ 6 ≤ (n : ℝ) →
              let rho : Measure ℝ := nu.tilted (fun z => -s * z ^ 2)
              let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
              let a : ℝ := Real.sqrt ((9 / 4) * x ^ 2 - 1)
              P.real {v : Shao.Path n | 0 < Shao.energy v ∧
                a * Real.sqrt (Shao.energy v) ≤ |Shao.prefixSum v n|} ≤
                  C * Shao.standardNormalTail ((3 / 2) * x) := by
  classical
  obtain ⟨C0, hC0, hEndpoint⟩ :=
    Shao.C2.AuxiliaryProductC1Endpoint.actual_product_absolute_endpoint_c1
  refine ⟨8 / 3 + 12 * C0, by linarith, ?_⟩
  intro rhoStar hRho0 hRho16 nu _ h2 h3 hMean hNorm L s hL hs n x hx hTime hRank hBudgetRank rho P a
  let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂nu
  let mu : ℝ := ∫ z : ℝ, z ∂rho
  let y : ℝ := a - 1 / (100 * (1 + x))
  have hBeta : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one nu h2 h3 hNorm
  have hBeta0 : 0 ≤ beta := zero_le_one.trans hBeta
  have hBetaPos : 0 < beta := lt_of_lt_of_le zero_lt_one hBeta
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  rcases Shao.C2.AuxiliarySourceParameters.auxiliary_source_mean_and_weak_event
      nu h2 h3 hMean hNorm L s hL hs n x hx hTime hRank with
    ⟨hn, _hN4, hSmall, _hDrift, hEvent⟩
  have hRho : IsProbabilityMeasure rho :=
    (Shao.C2.AuxiliaryEnergyCentered.auxiliary_energy_tilt_small_parameter
      nu h2 h3 hMean hNorm s hs hSmall).1
  letI : IsProbabilityMeasure rho := hRho
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  let chi : Measure ℝ := Measure.map (fun z : ℝ => z - mu) rho
  let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂chi
  let eta : Measure ℝ := Measure.map
    (fun z : ℝ => z / (Real.sqrt sigmaSq * Real.sqrt (n : ℝ))) chi
  let Pc : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => chi)
  rcases Shao.C2.AuxiliaryOwnC1Budget.auxiliary_centered_law_and_own_budget
      nu h2 h3 hMean hNorm s hs hSmall n hn with
    ⟨hChi, _hIdChi, hZeroChi, h2Chi, h3Chi, _hVar, hVarL, _hVarU, _hThird, hOwn⟩
  letI : IsProbabilityMeasure chi := hChi
  have hSecondChi : 0 < ∫ z : ℝ, z ^ 2 ∂chi := by linarith
  have hYBounds := Shao.C2.AuxiliarySourceEvent.auxiliary_rare_thresholds x hx
  have hy : 0 ≤ y := zero_le_one.trans hYBounds.1
  have hyx : y ≤ 2 * x := hYBounds.2.1
  have hLegal : Shao.truncationBudget eta n y ≤ rhoStar := by
    apply (hOwn y hy).trans
    apply (Shao.C2.AuxiliaryOwnC1Budget.auxiliary_own_budget_rank_payment
      beta rhoStar x y hBeta0 hRho0 hx0 hy hyx n hn hBudgetRank).trans
    linarith
  have hCenteredC1 : Pc.real {w : Shao.Path n |
      y * Real.sqrt (Shao.energy w) ≤ |Shao.prefixSum w n|} ≤
        C0 * Shao.standardNormalTail y :=
    hEndpoint rhoStar hRho0 hRho16 chi h2Chi hZeroChi hSecondChi h3Chi n hn y hy hLegal
  let B : Set (Shao.Path n) := {v |
    y * Real.sqrt (Shao.energy (fun i => v i - mu)) ≤
      |Shao.prefixSum (fun i => v i - mu) n|}
  have hCentered : P.real B ≤ C0 * Shao.standardNormalTail y := by
    change P.real {v : Shao.Path n |
      y * Real.sqrt (Shao.energy (fun i => v i - mu)) ≤
        |Shao.prefixSum (fun i => v i - mu) n|} ≤ _
    rw [(Shao.C2.AuxiliaryCenteredProductLaw.auxiliary_centered_product_law_and_endpoint
      rho n mu).2 y]
    exact hCenteredC1
  have hRadEq : 9 * x ^ 2 / 4 - 1 = (9 / 4 : ℝ) * x ^ 2 - 1 := by ring
  have hScale : 3 * x / 2 = (3 / 2 : ℝ) * x := by ring
  have hGaussian : Shao.standardNormalTail y ≤
      12 * Shao.standardNormalTail ((3 / 2) * x) := by
    have hh := Shao.C2.AuxiliarySourceGaussian.auxiliary_rare_threshold_gaussian_tail x hx
    change Shao.standardNormalTail
      (Real.sqrt (9 * x ^ 2 / 4 - 1) - 1 / (100 * (1 + x))) ≤
        12 * Shao.standardNormalTail (3 * x / 2) at hh
    simpa only [hRadEq, hScale] using hh
  have hCenteredTail : P.real B ≤ 12 * C0 * Shao.standardNormalTail ((3 / 2) * x) := by
    have hh := mul_le_mul_of_nonneg_left hGaussian hC0.le
    nlinarith
  have hsBound : s ≤ 1 / (128 * beta ^ 2) := by
    apply (le_div_iff₀ (show 0 < 128 * beta ^ 2 by positivity)).2
    nlinarith
  have hCoeff : 1024 ≤ 4000000 * (1 + L) ^ 2 := by
    nlinarith [sq_nonneg L]
  have hLowRank : 1024 * beta ^ 2 * (1 + x) ^ 6 ≤ (n : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hCoeff
      (mul_nonneg (sq_nonneg beta) (pow_nonneg (show 0 ≤ 1 + x by linarith) 6))
    nlinarith
  let A : Set (Shao.Path n) := {v | Shao.energy v ≤ (n : ℝ) / 8}
  have hLow : P.real A ≤ (8 / 3 : ℝ) * Shao.standardNormalTail ((3 / 2) * x) :=
    Shao.C2.AuxiliaryLowEnergyGaussian.auxiliary_tilted_low_energy_gaussian
      nu h2 h3 hMean hNorm s hs hsBound n x hx0 hLowRank
  have hSub : {v : Shao.Path n | 0 < Shao.energy v ∧
      a * Real.sqrt (Shao.energy v) ≤ |Shao.prefixSum v n|} ⊆ A ∪ B := by
    intro v hv
    by_cases hLowV : Shao.energy v ≤ (n : ℝ) / 8
    · exact Or.inl hLowV
    · exact Or.inr (hEvent v (le_of_lt (lt_of_not_ge hLowV)) hv.2)
  calc
    P.real {v : Shao.Path n | 0 < Shao.energy v ∧
        a * Real.sqrt (Shao.energy v) ≤ |Shao.prefixSum v n|} ≤ P.real (A ∪ B) :=
      measureReal_mono hSub
    _ ≤ P.real A + P.real B := measureReal_union_le A B
    _ ≤ (8 / 3 : ℝ) * Shao.standardNormalTail ((3 / 2) * x) +
        12 * C0 * Shao.standardNormalTail ((3 / 2) * x) := add_le_add hLow hCenteredTail
    _ = (8 / 3 + 12 * C0) * Shao.standardNormalTail ((3 / 2) * x) := by ring

end Shao.C2.AuxiliaryRareTiltProbability
