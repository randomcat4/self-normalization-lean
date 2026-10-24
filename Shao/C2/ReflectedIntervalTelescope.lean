import Shao.C2.SourceIntervalTelescope
import Shao.C2.IntervalDerivativeBound
import Shao.C2.InteriorDerivativeMeasurability

noncomputable section
namespace Shao.C2.ReflectedIntervalTelescope
open MeasureTheory
open Shao.C2.BridgeDomination Shao.C2.HalfLineReflectionFormula
open Shao.C2.CompletedIntervalProcess Shao.C2.CompletedIntervalDerivative
open Shao.C2.IntervalDerivativeBound Shao.C2.InteriorDerivativeMeasurability
open Shao.C2.SourceIntervalTelescope
open Shao.C1.PermutationEnergyEnvelope Shao.C1.IntegratedPermutationTelescope

theorem source_interval_stopped_expectation_of_reflection (n : ℕ)
    [MeasurableSpace (Equiv.Perm (Fin n))]
    [MeasurableSingletonClass (Equiv.Perm (Fin n))]
    (P : Measure (Shao.Path n)) [IsProbabilityMeasure P]
    (μ : Measure BridgeNoise) [IsProbabilityMeasure μ]
    (hRegular : ∀ a y T z : ℝ, 0 < a → 0 < T → |y| < a → |z| < a →
      HasDerivAt (fun u : ℝ => intervalCompletion μ a u T z) (spatialDerivative μ a y T z) y)
    (hUpper : ∀ a T z : ℝ, 0 < a → 0 < T → z < a →
      ∀ s : ℝ, s < a → upperCompletion μ a s T z = upperReflection a s T z)
    (hLower : ∀ a T z : ℝ, 0 < a → 0 < T → -a < z →
      ∀ s : ℝ, -a < s → lowerCompletion μ a s T z = lowerReflection a s T z)
    (x : ℝ) (hx : 0 < x) (H : ℝ) (hH : 0 < H)
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
  have hBound : ∀ a y T z : ℝ, 0 < a → 0 < T → |y| < a → |z| < a →
      |spatialDerivative μ a y T z| ≤ 4 / Real.sqrt T * (1 + |z - y| / Real.sqrt T) := by
    intro a y T z ha hT hy hz
    exact interval_deriv_bound_of_reflection μ a y T z hT hy hz
      (hUpper a T z ha hT (abs_lt.mp hz).2)
      (hLower a T z ha hT (abs_lt.mp hz).1)
      (hRegular a y T z ha hT hy hz).differentiableAt
  have h := integrated_stopped_compensation n P ν hν hνmeas hνobs
    (fun z σ k => completedValue μ x z σ k)
    (fun σ k => measurable_completedValue n μ x σ k)
    (fun z σ k => completedValue_bounds n μ x z σ k)
    (fun z σ r => completedDerivative μ x z σ r)
    (fun σ r => measurable_completedDerivative_of_regular n μ hRegular x σ r)
    (fun z r σ τ hστ => completedDerivative_reveal_observable n μ x z r σ τ hστ)
    H 4 hH (by norm_num) hcutoff
    (fun z σ r hGuard => completedDerivative_guarded_bound n μ x hx H 4 hH (by norm_num)
      hBound z σ r hGuard)
    m hmmeas hmabs hminvariant
  simpa only [completedValue_initial n μ x hx,
    stopped_guarded_eq_source n μ x H hH ν hcutoff] using h

end Shao.C2.ReflectedIntervalTelescope
