import Shao.C2.CompletedIntervalDerivative
import Shao.C1.IntegratedPermutationTelescope

noncomputable section
namespace Shao.C2.CompletedIntervalTelescope
open MeasureTheory
open Shao.C2.BridgeDomination Shao.C2.CompletionMeasurability
open Shao.C2.CompletedIntervalProcess Shao.C2.CompletedIntervalDerivative
open Shao.C1.PermutationEnergyEnvelope Shao.C1.IntegratedPermutationTelescope

theorem actual_completed_interval_stopped_expectation (n : ℕ)
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
    let V : Shao.Path n → Equiv.Perm (Fin n) → ℕ → ℝ := fun z σ k => completedValue μ x z σ k
    let FY : Shao.Path n → Equiv.Perm (Fin n) → Fin n → ℝ := fun z σ r => completedDerivative μ x z σ r
    Integrable (fun z => ∫ σ, m z *
      (V z σ (ν z σ) - RawInitialCompletion.rawInitial μ x z) ∂(uniformPermutationLaw n)) P ∧
    Integrable (fun z => ∫ σ, m z * (∑ r : Fin n, stoppedGuardedRemainder ν V FY H z σ r)
      ∂(uniformPermutationLaw n)) P ∧
    (∫ z, ∫ σ, m z * (V z σ (ν z σ) - RawInitialCompletion.rawInitial μ x z)
      ∂(uniformPermutationLaw n) ∂P) =
      ∫ z, ∫ σ, m z * (∑ r : Fin n, stoppedGuardedRemainder ν V FY H z σ r)
        ∂(uniformPermutationLaw n) ∂P := by
  dsimp only
  have h := integrated_stopped_compensation n P ν hν hνmeas hνobs
    (fun z σ k => completedValue μ x z σ k)
    (fun σ k => measurable_completedValue n μ x σ k)
    (fun z σ k => completedValue_bounds n μ x z σ k)
    (fun z σ r => completedDerivative μ x z σ r)
    (fun σ r => measurable_completedDerivative n μ hDerivativeMeas x σ r)
    (fun z r σ τ hστ => completedDerivative_reveal_observable n μ x z r σ τ hστ)
    H C hH hC hcutoff
    (fun z σ r hGuard => completedDerivative_guarded_bound n μ x hx H C hH hC hBound z σ r hGuard)
    m hmmeas hmabs hminvariant
  simpa only [completedValue_initial n μ x hx] using h

end Shao.C2.CompletedIntervalTelescope
