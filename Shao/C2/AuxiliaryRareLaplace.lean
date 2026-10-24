import Shao.C2.AuxiliaryOriginalCutoffRare
import Shao.C2.AuxiliaryProductTiltLaw
import Shao.C2.AuxiliaryEnergyLaplace

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Shao.C2.AuxiliaryRareLaplace
open MeasureTheory ProbabilityTheory

theorem auxiliary_original_cutoff_rare_laplace :
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
                    let Praw : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
                    let a : ℝ := Real.sqrt ((9 / 4) * x ^ 2 - 1)
                    let A : Set (Shao.Path n) := {v | 0 < Shao.energy v ∧
                      a * Real.sqrt (Shao.energy v) ≤ |Shao.prefixSum v n|}
                    let W : Shao.Path n → ℝ := fun v => Real.exp (-s * Shao.energy v)
                    Integrable (A.indicator W) Praw ∧
                      (∫ v : Shao.Path n, A.indicator W v ∂Praw) ≤
                        C * Real.exp (-(7 / 8) * s * (n : ℝ)) *
                          Shao.standardNormalTail ((3 / 2) * x) := by
  obtain ⟨C, hC, hRare⟩ :=
    Shao.C2.AuxiliaryOriginalCutoffRare.auxiliary_original_cutoff_rare_probability
  refine ⟨C, hC, ?_⟩
  intro rhoStar hRho0 hRho16 L hL K hKDrift hKBudget nu _ h2 h3 hMean hNorm s hs x hx t n hCutoff hLength hTime Praw a A W
  let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂nu
  let Z : ℝ := ∫ z : ℝ, Real.exp (-s * z ^ 2) ∂nu
  let rho : Measure ℝ := nu.tilted (fun z => -s * z ^ 2)
  let Ptilt : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
  have hBeta : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one nu h2 h3 hNorm
  rcases Shao.C2.AuxiliarySourceCutoffPayment.auxiliary_original_cutoff_rank_payment
      beta L rhoStar K s x hBeta hL hRho0 hs hx hKDrift hKBudget
      t n hCutoff hLength hTime with
    ⟨_hm4, _hn, _hHalf, hTimeN, hRank, _hBudgetRank⟩
  have hSmall :=
    (Shao.C2.AuxiliarySourceParameters.auxiliary_rare_parameter_payment
      beta L s hBeta hL hs n x hx hTimeN hRank).2.2.1
  have hDecay : Z ≤ Real.exp (-(7 / 8) * s) :=
    Shao.C2.AuxiliaryEnergyLaplace.auxiliary_energy_laplace_decay
      nu h2 h3 hMean hNorm s hs (by change s * beta ^ 2 ≤ 1 / 64; linarith)
  have hZ0 : 0 ≤ Z := integral_nonneg (fun z => (Real.exp_pos _).le)
  have hPower : Z ^ n ≤ Real.exp (-(7 / 8) * s * (n : ℝ)) := by
    calc
      Z ^ n ≤ (Real.exp (-(7 / 8) * s)) ^ n := pow_le_pow_left₀ hZ0 hDecay n
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hA : MeasurableSet A := by
    exact (measurableSet_lt measurable_const Shao.measurable_energy).inter
      (measurableSet_le (measurable_const.mul Shao.measurable_sqrt_energy)
        (Shao.continuous_prefixSum n).abs.measurable)
  have hIdentity := Shao.C2.AuxiliaryProductTiltLaw.auxiliary_actual_event_laplace_identity
    nu h2 h3 hMean hNorm s hs n A hA
  change Integrable (A.indicator W) Praw ∧
    (∫ v : Shao.Path n, A.indicator W v ∂Praw) = Z ^ n * Ptilt.real A at hIdentity
  have hProbability : Ptilt.real A ≤ C * Shao.standardNormalTail ((3 / 2) * x) :=
    hRare rhoStar hRho0 hRho16 L hL K hKDrift hKBudget nu h2 h3 hMean hNorm
      s hs x hx t n hCutoff hLength hTime
  have hTail0 : 0 ≤ Shao.standardNormalTail ((3 / 2) * x) :=
    (Shao.standardNormalTail_basic.2.2.1 _).1.le
  refine ⟨hIdentity.1, ?_⟩
  rw [hIdentity.2]
  calc
    Z ^ n * Ptilt.real A ≤ Z ^ n * (C * Shao.standardNormalTail ((3 / 2) * x)) :=
      mul_le_mul_of_nonneg_left hProbability (pow_nonneg hZ0 n)
    _ ≤ Real.exp (-(7 / 8) * s * (n : ℝ)) *
        (C * Shao.standardNormalTail ((3 / 2) * x)) :=
      mul_le_mul_of_nonneg_right hPower (mul_nonneg hC.le hTail0)
    _ = C * Real.exp (-(7 / 8) * s * (n : ℝ)) *
        Shao.standardNormalTail ((3 / 2) * x) := by ring

end Shao.C2.AuxiliaryRareLaplace
