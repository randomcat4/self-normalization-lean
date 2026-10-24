import Shao.C2.CompletedIntervalUpdate

noncomputable section
namespace Shao.C2.SourceIntervalTelescope
open MeasureTheory
open Shao.C2.BridgeDomination Shao.C2.CompletionMeasurability
open Shao.C2.CompletedIntervalProcess Shao.C2.CompletedIntervalDerivative
open Shao.C2.CompletedIntervalUpdate Shao.C2.CompletedIntervalTelescope
open Shao.C1.PermutationEnergyEnvelope Shao.C1.IntegratedPermutationTelescope

def sourceStoppedStep {n : ℕ} (ν : Shao.Path n → Equiv.Perm (Fin n) → ℕ)
    (μ : Measure BridgeNoise) (x : ℝ) (z : Shao.Path n)
    (σ : Equiv.Perm (Fin n)) (r : Fin n) : ℝ := by
  classical
  exact if r.val < ν z σ then
    (if 0 < Shao.energy z ∧ strictLive x z σ r.val ∧
      |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z) then
      rawStepRemainder μ x z σ r else 0)
  else 0

theorem stopped_guarded_eq_source (n : ℕ) (μ : Measure BridgeNoise) (x H : ℝ) (hH : 0 < H)
    (ν : Shao.Path n → Equiv.Perm (Fin n) → ℕ)
    (hcutoff : ∀ (z : Shao.Path n) (σ : Equiv.Perm (Fin n)) (r : Fin n),
      r.val < ν z σ → H ≤ revealRemainingEnergy z σ r)
    (z : Shao.Path n) (σ : Equiv.Perm (Fin n)) (r : Fin n) :
    stoppedGuardedRemainder ν (fun z σ k => completedValue μ x z σ k)
      (fun z σ r => completedDerivative μ x z σ r) H z σ r =
      sourceStoppedStep ν μ x z σ r := by
  unfold stoppedGuardedRemainder sourceStoppedStep
  by_cases hr : r.val < ν z σ
  · rw [if_pos hr, if_pos hr]
    exact guarded_remainder_eq_live_rawStep n μ x z σ r H hH (hcutoff z σ r hr)
  · rw [if_neg hr, if_neg hr]

theorem source_interval_stopped_expectation_of_analytic_inputs (n : ℕ)
    [MeasurableSpace (Equiv.Perm (Fin n))]
    [MeasurableSingletonClass (Equiv.Perm (Fin n))]
    (P : Measure (Shao.Path n)) [IsProbabilityMeasure P]
    (μ : Measure BridgeNoise) [IsProbabilityMeasure μ]
    (hRegular : ∀ a y T z : ℝ, 0 < a → 0 < T → |y| < a → |z| < a →
      HasDerivAt (fun u : ℝ => intervalCompletion μ a u T z) (spatialDerivative μ a y T z) y)
    (hDerivativeMeas : Measurable (fun p : CompletionParameters =>
      spatialDerivative μ p.1 p.2.1 p.2.2.1 p.2.2.2))
    (x : ℝ) (hx : 0 < x) (H C : ℝ) (hH : 0 < H) (hC : 0 ≤ C)
    (hBound : ∀ a y T z : ℝ, 0 < a → 0 < T → |y| < a → |z| < a →
      |spatialDerivative μ a y T z| ≤ C / Real.sqrt T * (1 + |z - y| / Real.sqrt T))
    (ν : Shao.Path n → Equiv.Perm (Fin n) → ℕ)
    (hν : ∀ z σ, ν z σ ≤ n)
    (hνmeas : ∀ σ, Measurable (fun z => ν z σ))
    (hνobs : ∀ (z : Shao.Path n) (r : Fin n) (σ τ : Equiv.Perm (Fin n)),
      (∀ i : Fin n, i.val < r.val → σ i = τ i) →
        (r.val < ν z σ ↔ r.val < ν z τ))
    (hcutoff : ∀ (z : Shao.Path n) (σ : Equiv.Perm (Fin n)) (r : Fin n),
      r.val < ν z σ → H ≤ revealRemainingEnergy z σ r)
    (m : Shao.Path n → ℝ) (hmmeas : Measurable m) (hmabs : ∀ z, |m z| ≤ 1)
    (hminvariant : ∀ (z : Shao.Path n) (τ : Equiv.Perm (Fin n)),
      m (fun i => z (τ i)) = m z) :
    Integrable (fun z => ∫ σ, m z *
      (completedValue μ x z σ (ν z σ) - RawInitialCompletion.rawInitial μ x z)
        ∂(uniformPermutationLaw n)) P ∧
    Integrable (fun z => ∫ σ, m z * (∑ r : Fin n, sourceStoppedStep ν μ x z σ r)
      ∂(uniformPermutationLaw n)) P ∧
    (∫ z, ∫ σ, m z * (completedValue μ x z σ (ν z σ) - RawInitialCompletion.rawInitial μ x z)
      ∂(uniformPermutationLaw n) ∂P) =
      ∫ z, ∫ σ, m z * (∑ r : Fin n, sourceStoppedStep ν μ x z σ r)
        ∂(uniformPermutationLaw n) ∂P := by
  have h := actual_completed_interval_stopped_expectation n P μ hRegular hDerivativeMeas
    x hx H C hH hC hBound ν hν hνmeas hνobs hcutoff m hmmeas hmabs hminvariant
  dsimp only at h
  simpa only [stopped_guarded_eq_source n μ x H hH ν hcutoff] using h

end Shao.C2.SourceIntervalTelescope
