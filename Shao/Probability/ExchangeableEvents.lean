import Shao.Probability.MeasurablePath
import Shao.Probability.FiniteIID

/-!
# Fixed-permutation probabilities for the C1 and C2 events

These are direct consumers of finite iid exchangeability and event measurability.
The events keep their genuine final energy and their original zero-energy
conventions. Thresholds are arbitrary real numbers.
-/

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} {ν : Measure ℝ}
variable [hμ : IsProbabilityMeasure μ] [hν : IsProbabilityMeasure ν]

include hμ hν

/-- C1 strict upper survival has the same probability under a fixed permutation. -/
theorem iid_upperStrictSurvival_probability_eq_perm {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (σ : Equiv.Perm (Fin n)) (hn : 0 < n) (t : ℝ) :
    μ {ω | samplePath X ω ∈ upperStrictSurvival hn t} =
      μ {ω | samplePath (fun i => X (σ i)) ω ∈ upperStrictSurvival hn t} := by
  exact iid_event_probability_eq_perm hX hIndep hLaw σ
    (measurableSet_upperStrictSurvival hn t)

/-- C1's zero-normalized upper-maximum CDF is invariant under a fixed permutation. -/
theorem iid_upperNormalizedCDF_probability_eq_perm {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (σ : Equiv.Perm (Fin n)) (hn : 0 < n) (t : ℝ) :
    μ {ω | samplePath X ω ∈ C1.upperNormalizedCDF hn t} =
      μ {ω | samplePath (fun i => X (σ i)) ω ∈ C1.upperNormalizedCDF hn t} := by
  exact iid_event_probability_eq_perm hX hIndep hLaw σ
    (C1.measurableSet_upperNormalizedCDF hn t)

/-- C2 hitting both genuine-energy walls is invariant under a fixed permutation. -/
theorem iid_doubleCrossing_probability_eq_perm {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (σ : Equiv.Perm (Fin n)) (hn : 0 < n) (x : ℝ) :
    μ {ω | samplePath X ω ∈ C2.doubleCrossing hn x} =
      μ {ω | samplePath (fun i => X (σ i)) ω ∈ C2.doubleCrossing hn x} := by
  exact iid_event_probability_eq_perm hX hIndep hLaw σ
    (C2.measurableSet_doubleCrossing hn x)

/-- Absolute crossing of the genuine-energy wall is invariant under a fixed permutation. -/
theorem iid_absoluteCrossing_probability_eq_perm {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (σ : Equiv.Perm (Fin n)) (hn : 0 < n) (x : ℝ) :
    μ {ω | samplePath X ω ∈ absoluteCrossing hn x} =
      μ {ω | samplePath (fun i => X (σ i)) ω ∈ absoluteCrossing hn x} := by
  exact iid_event_probability_eq_perm hX hIndep hLaw σ
    (measurableSet_absoluteCrossing hn x)

end Shao.Probability
