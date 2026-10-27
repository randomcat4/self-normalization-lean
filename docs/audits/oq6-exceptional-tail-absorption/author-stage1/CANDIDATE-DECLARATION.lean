import Shao.Probability.GaussianTail
import Shao.OQ5.P51.BoundedPolylogWindow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Stage1 declaration candidate only. This file deliberately contains a theorem
head without a proof body and is not a compilable production module.
No declaration is frozen by this file. The lane lead must freeze the complete
interface before any proof implementation. No new helper declaration is proposed.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace Shao.OQ6.OriginalExceptionalTailAbsorption

theorem eventually_original_exceptional_payment_absorbed
    (t0 cg : ℝ) (ht0 : 0 < t0) (hcg : 0 < cg) :
    let cWindow : ℝ := min (1 : ℝ) (Real.sqrt t0 / (2 : ℝ))
    0 < cWindow ∧
      ∀ᶠ n : ℕ in atTop,
        4 ≤ n ∧
          (1 : ℝ) ≤ cWindow * Real.rpow (n : ℝ) (1 / 6 : ℝ) ∧
          ∀ z : ℝ, (1 : ℝ) ≤ z →
            z ≤ cWindow * Real.rpow (n : ℝ) (1 / 6 : ℝ) →
            (6 : ℝ) *
                Real.exp (-Shao.OQ5.P51.boundedPolylogMomentOrder t0 n) +
              (2 : ℝ) * Real.exp (-cg * (n : ℝ)) +
              (8 : ℝ) * Real.exp (-(Real.sqrt (n : ℝ)) / (2 : ℝ)) ≤
              Real.exp (-(t0 / (2 : ℝ)) *
                Real.rpow (n : ℝ) (1 / 3 : ℝ)) *
                Shao.standardNormalTail z

-- No proof body follows: Stage1 ends at the complete proposed result type.
end Shao.OQ6.OriginalExceptionalTailAbsorption
