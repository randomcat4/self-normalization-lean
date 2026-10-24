import Shao.C2.ActualBridgeIntervalTelescope
import Shao.C2.AdaptiveRevealCutoff
import Shao.Probability.SourceActualLocalProfileBudget

set_option autoImplicit false
noncomputable section
namespace Shao.C2.ActualAdaptiveIntervalTelescope
open MeasureTheory ProbabilityTheory
open scoped NNReal Topology
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.BridgeUpperAffineIdentification Shao.C2.BridgeLowerIdentification
open Shao.C2.HalfLineReflectionFormula Shao.C2.SourceIntervalCompletion
open Shao.C2.BridgeIntervalImageResolved Shao.C2.CompletedIntervalProcess
open Shao.C2.CompletedIntervalDerivative Shao.C2.CompletedIntervalUpdate
open Shao.C2.SourceIntervalTelescope Shao.C2.ReflectedIntervalTelescope
open Shao.C1.PermutationEnergyEnvelope Shao.C1.IntegratedPermutationTelescope

open Shao.C2.ActualBridgeIntervalTelescope Shao.C2.AdaptiveRevealCutoff
open Shao.Probability.SourcePermutationReveal (LabelPerm energyCutoff IsRevealStoppingRank remainingEnergy)
open Shao.Probability.SourceActualLocalProfileBudget (actual_energy_cutoff_measurable)

theorem actual_adaptive_interval_stopped_expectation {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (W : Measure Ω) [IsProbabilityMeasure W] (hB : IsBrownianReal B W)
    (n : ℕ) [MeasurableSpace (Equiv.Perm (Fin n))]
    [MeasurableSingletonClass (Equiv.Perm (Fin n))]
    (P : Measure (Shao.Path n)) [IsProbabilityMeasure P]
    (x : ℝ) (hx : 0 < x) (H : ℝ) (hH : 0 < H)
    (ell : ℕ)
    (m : Shao.Path n → ℝ) (hmmeas : Measurable m) (hmabs : ∀ z, |m z| ≤ 1)
    (hminvariant : ∀ (z : Shao.Path n) (τ : Equiv.Perm (Fin n)),
      m (fun i => z (τ i)) = m z) :
    let ν : Shao.Path n → Equiv.Perm (Fin n) → ℕ := fun z sigma =>
      min (energyCutoff z H sigma) (n - ell)
    Integrable (fun z => ∫ σ, m z *
      (completedValue (bridgeLaw B W) x z σ (ν z σ) - RawInitialCompletion.rawInitial (bridgeLaw B W) x z)
        ∂(uniformPermutationLaw n)) P ∧
    Integrable (fun z => ∫ σ, m z * (∑ r : Fin n, sourceStoppedStep ν (bridgeLaw B W) x z σ r)
      ∂(uniformPermutationLaw n)) P ∧
    (∫ z, ∫ σ, m z * (completedValue (bridgeLaw B W) x z σ (ν z σ) - RawInitialCompletion.rawInitial (bridgeLaw B W) x z)
      ∂(uniformPermutationLaw n) ∂P) =
      ∫ z, ∫ σ, m z * (∑ r : Fin n, sourceStoppedStep ν (bridgeLaw B W) x z σ r)
        ∂(uniformPermutationLaw n) ∂P := by
  intro ν
  have hStop (z : Shao.Path n) : IsRevealStoppingRank (ν z) :=
    (adaptive_cutoff_stopping_and_le z H H hH hH le_rfl ell).1
  refine actual_source_interval_stopped_expectation B W hB n P x hx H hH ν
    (fun z sigma => (hStop z).1 sigma) ?_ ?_ ?_ m hmmeas hmabs hminvariant
  · intro sigma
    exact (actual_energy_cutoff_measurable H hH sigma).min measurable_const
  · intro z r sigma tau hprefix
    simpa only [not_le] using not_congr ((hStop z).2 r.val sigma tau hprefix)
  · intro z sigma r hr
    change H ≤ remainingEnergy z r.val sigma
    exact ((before_adaptive_cutoff_iff z H hH ell r.val r.is_lt.le sigma).mp hr).2

end Shao.C2.ActualAdaptiveIntervalTelescope
