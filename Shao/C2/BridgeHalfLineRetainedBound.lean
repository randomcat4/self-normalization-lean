import Shao.C2.BridgeLowerIdentification

noncomputable section
namespace Shao.C2.BridgeHalfLineRetainedBound
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.SourceHalfLineCompletion

theorem actual_upper_retained_bound {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (a y T z b : ℝ) (ha : 0 < a) (hy : y < a) (hz : z < a) (hT : 0 < T)
    (hb : b ^ 2 ≤ T) (hzero : T - b ^ 2 = 0 → y + b = z) :
    let F := fun w S : ℝ => sourceUpperCompletion (bridgeLaw B P) a w S z
    let R := fun β : ℝ => F (y + β) (T - β ^ 2) - F y T -
      (β - β ^ 2 * (z - y) / T) * deriv (fun w => F w T) y
    |if b ^ 2 ≤ T / 2 ∧ a ≤ y + b then R (a - y) else R b| ≤
      8000100 * (|b| / Real.sqrt T) ^ 3 * (1 + |z - y| / Real.sqrt T) ^ 3 *
        Real.exp (-((max (a - y - (|b| + max (z - y) 0)) 0) ^ 2) / T) := by
  apply actual_upper_retained_bound_of_reflection (bridgeLaw B P) a y T z b ha hy hz hT hb hzero
  intro S hS w hw
  exact Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula B P hB a w S z hS hw hz

theorem actual_lower_retained_bound {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (a y T z b : ℝ) (ha : 0 < a) (hy : -a < y) (hz : -a < z) (hT : 0 < T)
    (hb : b ^ 2 ≤ T) (hzero : T - b ^ 2 = 0 → y + b = z) :
    let F := fun w S : ℝ => sourceLowerCompletion (bridgeLaw B P) a w S z
    let R := fun β : ℝ => F (y + β) (T - β ^ 2) - F y T -
      (β - β ^ 2 * (z - y) / T) * deriv (fun w => F w T) y
    |if b ^ 2 ≤ T / 2 ∧ y + b ≤ -a then R (-a - y) else R b| ≤
      8000100 * (|b| / Real.sqrt T) ^ 3 * (1 + |z - y| / Real.sqrt T) ^ 3 *
        Real.exp (-((max (a + y - (|b| + max (y - z) 0)) 0) ^ 2) / T) := by
  apply actual_lower_retained_bound_of_reflection (bridgeLaw B P) a y T z b ha hy hz hT hb hzero
  intro S hS w hw
  exact Shao.C2.BridgeLowerIdentification.bridge_lower_formula B P hB a w S z hS hw hz

end Shao.C2.BridgeHalfLineRetainedBound
