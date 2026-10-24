import Shao.C2.AuxiliaryRareTiltProbability
import Shao.C2.AuxiliarySourceCutoffPayment

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Shao.C2.AuxiliaryOriginalCutoffRare
open MeasureTheory ProbabilityTheory

theorem auxiliary_original_cutoff_rare_probability :
    ∃ C : ℝ, 0 < C ∧
      ∀ rhoStar : ℝ, 0 < rhoStar → rhoStar ≤ 1 / 16 →
        ∀ L : ℝ, 0 ≤ L →
          ∀ K : ℝ, 8000000 * (1 + L) ^ 2 ≤ K →
            2 * (768 / rhoStar) ^ 2 ≤ K →
            ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu],
              Integrable (fun z : ℝ => z ^ 2) nu →
              Integrable (fun z : ℝ => |z| ^ 3) nu →
              (∫ z : ℝ, z ∂nu) = 0 →
              (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
              ∀ s : ℝ, 0 ≤ s →
                ∀ x : ℝ, 1 ≤ x →
                  ∀ t n : ℕ,
                    Nat.ceil (K * (∫ z : ℝ, |z| ^ 3 ∂nu) ^ 2 * (1 + x) ^ 6) ≤ t →
                    (n = t ∨ n = t - 1) →
                    s * (t : ℝ) ≤ L * x ^ 2 →
                    let rho : Measure ℝ := nu.tilted (fun z => -s * z ^ 2)
                    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
                    let a : ℝ := Real.sqrt ((9 / 4) * x ^ 2 - 1)
                    P.real {v : Shao.Path n | 0 < Shao.energy v ∧
                      a * Real.sqrt (Shao.energy v) ≤ |Shao.prefixSum v n|} ≤
                        C * Shao.standardNormalTail ((3 / 2) * x) := by
  obtain ⟨C, hC, hRare⟩ :=
    Shao.C2.AuxiliaryRareTiltProbability.auxiliary_actual_rare_tilt_probability
  refine ⟨C, hC, ?_⟩
  intro rhoStar hRho0 hRho16 L hL K hKDrift hKBudget nu _ h2 h3 hMean hNorm s hs x hx t n hCutoff hLength hTime rho P a
  let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂nu
  have hBeta : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one nu h2 h3 hNorm
  rcases Shao.C2.AuxiliarySourceCutoffPayment.auxiliary_original_cutoff_rank_payment
      beta L rhoStar K s x hBeta hL hRho0 hs hx hKDrift hKBudget
      t n hCutoff hLength hTime with
    ⟨_hm4, _hn, _hHalf, hTimeN, hRank, hBudgetRank⟩
  exact hRare rhoStar hRho0 hRho16 nu h2 h3 hMean hNorm
    L s hL hs n x hx hTimeN hRank hBudgetRank

end Shao.C2.AuxiliaryOriginalCutoffRare
