# Actual Lindley last-regulator first moment

Status: CANDIDATE_PENDING_ROOT_FREEZE. Proposed module Shao/Probability/SourceLindleyRegulatorFirstMoment.lean. Two public theorems, no new public definitions. All mathematical objects are the accepted actual Lindley recursion and its actual finite iid law.

```lean
namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem lindleyRegulator_cyclic_sum (n : ℕ) (a : Shao.Path (n + 1)) :
    (∑ j : Fin (n + 1),
      lindleyRegulator (fun k : Fin (n + 1) => a (k + j)) (Fin.last n)) =
      max (-(Shao.prefixSum a (n + 1))) 0

theorem iid_lindleyRegulator_last_first_moment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (n : ℕ) :
    let P : Measure (Shao.Path (n + 1)) := Measure.pi (fun _ : Fin (n + 1) => ν)
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let V : ℝ := variance (id : ℝ → ℝ) ν
    Integrable (fun a : Shao.Path (n + 1) => lindleyRegulator a (Fin.last n)) P ∧
      ((n + 1 : ℕ) : ℝ) *
        (∫ a : Shao.Path (n + 1), lindleyRegulator a (Fin.last n) ∂P) =
          ∫ a : Shao.Path (n + 1), max (-(Shao.prefixSum a (n + 1))) 0 ∂P ∧
      (∫ a : Shao.Path (n + 1), lindleyRegulator a (Fin.last n) ∂P) ≤
        Real.sqrt V / Real.sqrt ((n + 1 : ℕ) : ℝ) + |μ|

end Shao.Probability
```

The sample length is n+1 only to retain an actual final Fin index without adding a positive-length proof argument. Source time i=1 is n=0, and every source i>=1 is covered. No symmetry, centered-law or positive-variance premise is added. V=0 is retained. This is the actual first-moment identity and sharp source S.3.8 first bound, not the second-moment/survival bound or full regulator lemma.
