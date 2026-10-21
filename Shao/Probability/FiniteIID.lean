import Shao.Basic.FinitePath
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib

/-!
# Finite iid samples and fixed coordinate permutations

The common real law need not be centered and no moment or atomlessness condition
is imposed. Every result includes length zero. A permutation is a fixed input;
no result here concerns a sample-dependent or conditionally random permutation.
-/

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- Regard a finite family of real random variables as one path-valued variable. -/
def samplePath (X : Fin n → Ω → ℝ) (ω : Ω) : Shao.Path n := fun i => X i ω

theorem measurable_samplePath {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) : Measurable (samplePath X) := by
  exact Measurable.of_eval hX

variable {μ : Measure Ω} {ν : Measure ℝ}
variable [hμ : IsProbabilityMeasure μ] [hν : IsProbabilityMeasure ν]

include hμ hν

/-- The joint law of a finite iid sample is its finite product law. -/
theorem iid_samplePath_map_eq_pi {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν) :
    Measure.map (samplePath X) μ = Measure.pi (fun _ : Fin n => ν) := by
  have hcoord : ∀ i, Measure.map (X i) μ = ν := by
    intro i
    simpa only [Measure.map_id] using (hLaw i).map_eq
  change Measure.map (fun ω i => X i ω) μ = _
  rw [hIndep.map_fun_eq_pi_map (fun i => (hX i).aemeasurable)]
  congr 1
  funext i
  exact hcoord i

/-- The same joint law expressed as an identically distributed pair. -/
theorem iid_samplePath_identDistrib {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν) :
    IdentDistrib (samplePath X) (id : Shao.Path n → Shao.Path n)
      μ (Measure.pi (fun _ : Fin n => ν)) := by
  refine ⟨(measurable_samplePath hX).aemeasurable, measurable_id.aemeasurable, ?_⟩
  simpa only [Measure.map_id] using iid_samplePath_map_eq_pi hX hIndep hLaw

/-- Reordering iid coordinates by any fixed permutation preserves the joint law. -/
theorem iid_samplePath_identDistrib_perm {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (σ : Equiv.Perm (Fin n)) :
    IdentDistrib (samplePath X) (samplePath (fun i => X (σ i))) μ μ := by
  refine ⟨(measurable_samplePath hX).aemeasurable,
    (measurable_samplePath (fun i => hX (σ i))).aemeasurable, ?_⟩
  rw [iid_samplePath_map_eq_pi hX hIndep hLaw,
    iid_samplePath_map_eq_pi (fun i => hX (σ i))
      (hIndep.precomp σ.injective) (fun i => hLaw (σ i))]

/-- Every measurable path observable has the same law after a fixed permutation. -/
theorem iid_observable_identDistrib_perm {β : Type*} [MeasurableSpace β]
    {X : Fin n → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (σ : Equiv.Perm (Fin n)) {F : Shao.Path n → β} (hF : Measurable F) :
    IdentDistrib (fun ω => F (samplePath X ω))
      (fun ω => F (samplePath (fun i => X (σ i)) ω)) μ μ := by
  exact (iid_samplePath_identDistrib_perm hX hIndep hLaw σ).comp hF

/-- Measurable path events have equal probabilities after a fixed permutation. -/
theorem iid_event_probability_eq_perm {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (σ : Equiv.Perm (Fin n)) {A : Set (Shao.Path n)} (hA : MeasurableSet A) :
    μ {ω | samplePath X ω ∈ A} =
      μ {ω | samplePath (fun i => X (σ i)) ω ∈ A} := by
  exact (iid_samplePath_identDistrib_perm hX hIndep hLaw σ).measure_mem_eq hA

/-- Measurable events of any measurable observable retain their probabilities. -/
theorem iid_observable_event_probability_eq_perm {β : Type*} [MeasurableSpace β]
    {X : Fin n → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (σ : Equiv.Perm (Fin n)) {F : Shao.Path n → β} (hF : Measurable F)
    {A : Set β} (hA : MeasurableSet A) :
    μ {ω | F (samplePath X ω) ∈ A} =
      μ {ω | F (samplePath (fun i => X (σ i)) ω) ∈ A} := by
  exact (iid_observable_identDistrib_perm hX hIndep hLaw σ hF).measure_mem_eq hA

end Shao.Probability
