# Actual growing microclock reflection sum — ROOT FROZEN

Root mathematical freeze before any implementation. The complete selected single
public head, including every literal let and the true joint sample/integrals,
is copied verbatim below. No silent change to assumptions, quantifier order,
clock event, finite index set, constants or actual test/noise is authorized.
Zero new definitions. Extra PRIVATE helper THEOREMS are authorized, with all
actual private/generated types/values/axioms in the final complete review.

This freeze authorizes no worktree activation or implementation yet. Exact
SourceLocalizedMicrotimeDerivatives bdf57fc81650cf1dbb43d42d70b8d9078ac3fdb00e7637913f1e67f0b7bc1633
must first receive fresh complete independent CORRECT and root qualification.
Its author/reviewer must release before that worktree is reused. Preserve
original successful objects and source bytes; no old compile/audit replays.

Proposed future sole source is Shao/Probability/SourceGrowingMicrotimeReflection.lean,
plus drafts/c12-growing-microtime-probability-assembly/. No source exists yet.
Terminal m=0 is paid by the actual local constant before positive-clock counting;
no raw2<=gamma² or conditional-mean-zero hypothesis is added. The selected
per-index estimate uses the first derivative and true late first regulator
moment only. This is a source-proof simplification, not a stronger assumption.
The explicit prefixSquares>=1/16 indicator is retained. Downstream original
E-complement inclusion, medium/long ranges and total comparison remain unpaid.

All Lean checks must remain server-only, fixed packages/toolchain, root CPU10–13
and root-heavy.lock/-M8192/-j4. Same-o first full success, complete owned AX and
fresh complete independent review mandatory. Original C1/C2 remain OPEN.

Immutable candidate evidence hashes:
- candidate-declarations.lean.txt: 3087cd938dad36d523275931e19080ddbefcfb7f174ce3b94c3f6eeff136d720
- proof-candidate.md: 9503b39a4443c817add41b216ad0d35d3027b9b5f0e8df9cedfbec64d9ae314f
- candidate-check.md: dd7a988b16be915677d18cc9787c28a6c2fbf4a8bfdb4e00b23d23ccdb346311

## Exact selected complete declaration

```lean
import Shao.Probability.SourceLocalizedMicrotimeDerivatives
import Shao.Probability.SourceLindleyRegulatorFirstMomentSums
import Shao.Probability.LindleyTelescoping
import Shao.Probability.GaussianTail

set_option autoImplicit false
namespace Shao.Probability
open MeasureTheory ProbabilityTheory

-- Candidate only, not frozen or implemented.
theorem sourceTruncation_growing_microtime_reflection_sum :
    ∃ C : ℝ, 0 < C ∧
      ∀ L2 epsilon0 : ℝ, 0 < L2 → 0 < epsilon0 →
        epsilon0 ≤ 1 / (192 * Real.sqrt (L2 + 1)) →
        ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
          ∀ n : ℕ, Integrable (fun a : ℝ => a ^ 2) ν0 →
            (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1 →
            (∫ a : ℝ, a ∂ν0) = 0 →
            ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon →
              epsilon ≤ epsilon0 / 2 →
              Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
              ∀ y : ℝ, 2 ≤ y →
                |y - x| ≤ 1 / (2 * (1 + x)) →
                let rho := ProbabilityTheory.cond ν0
                  {a : ℝ | |a| ≤ epsilon / (1 + x)}
                let raw2 := ∫ a : ℝ, a ^ 2 ∂rho
                let m3 := ∫ a : ℝ, |a| ^ 3 ∂rho
                let V := variance (id : ℝ → ℝ) rho
                let gamma := m3 / V
                let P := Measure.pi (fun _ : Fin n => rho)
                let psi := fun p : ℝ × ℝ =>
                  ∫ z : ℝ × ℝ,
                    sourceFourierTest y (p.1 + z.1, p.2 + z.2)
                    ∂quadraticFullNoiseLaw rho
                let T := fun j : Fin n =>
                  ((n - (j.val + 1) : ℕ) : ℝ) * raw2
                let J := Finset.univ.filter (fun j : Fin n =>
                  n / 2 < j.val + 1 ∧ T j < L2 * gamma ^ 2)
                let D := fun (j : Fin n) (a : Shao.Path n) =>
                  if (1 / 16 : ℝ) ≤ Shao.prefixSquares a (j.val + 1) then
                    |lindleyDelta rho psi a j| else 0
                let Lambda :=
                  (1 + y) * (n : ℝ) * |∫ a : ℝ, a ∂rho| +
                    (1 + y) ^ 3 * (n : ℝ) * m3
                (∀ j : Fin n, Integrable (D j) P) ∧
                  (∀ j ∈ J, (∫ a : Shao.Path n, D j a ∂P) ≤
                    C / ((n : ℝ) * gamma) * Real.exp (-4 * y ^ 2)) ∧
                  (∑ j ∈ J, ∫ a : Shao.Path n, D j a ∂P) ≤
                    C * (L2 + 1) * ((n : ℝ) * m3) * Real.exp (-4 * y ^ 2) ∧
                  (∑ j ∈ J, ∫ a : Shao.Path n, D j a ∂P) ≤
                    C * (L2 + 1) * Lambda * Shao.standardNormalTail y

end Shao.Probability
```
