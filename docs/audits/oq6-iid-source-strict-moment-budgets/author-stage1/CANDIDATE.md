# Unit 230 Stage 1 candidate: genuine IID source-z strict moment budgets

Status: READY_FOR_LEAD_DECLARATION_FREEZE. This is an uncompiled declaration
candidate, not an implementation or an accepted proof. The lead owns the exact
freeze. This author has not created a Lean source file.

Proposed module: `Shao.OQ6.IIDSourceStrictMomentBudgets`.
Proposed sole public declaration:
`Shao.OQ6.IIDSourceStrictMomentBudgets.actual_iid_source_z_strict_moment_budgets`.
No conflict with that module or declaration was found in the curated library.

## Complete proposed preamble and declaration head

The fenced material intentionally stops at the complete result type. No proof
term or placeholder is supplied. The enclosing namespace and section are shown
to fix the complete preamble and name, rather than to claim a compilable file.

```lean
import Shao.OQ6.ActualPhysicalCompactCDF
import Shao.Probability.TruncationIntegrals
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false

universe u

namespace Shao.OQ6.IIDSourceStrictMomentBudgets

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

theorem actual_iid_source_z_strict_moment_budgets
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (p : ℝ) (hp2 : 2 < p) (hp3 : p ≤ 3)
    (hgp : Integrable (fun o : Ω => Real.rpow |g o| p) μ)
    (cBudget : ℝ) (hcBudget : 0 < cBudget) :
    let β : ℝ := ∫ o : Ω, Real.rpow |g o| p ∂μ
    let c : ℝ :=
      Real.rpow (min (1 / 2 : ℝ) cBudget / 2) (1 / p)
    0 ≤ β ∧
      0 < c ∧
      Real.rpow c p = min (1 / 2 : ℝ) cBudget / 2 ∧
      Real.rpow c p < min (1 / 2 : ℝ) cBudget ∧
      (∀ (n : ℕ) (_hn : 1 ≤ n) (z : ℝ) (_hz : 1 ≤ z),
        let P : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
        let N : ℝ := Real.sqrt (n : ℝ)
        let ξ : Fin n → (Fin n → Ω) → ℝ :=
          fun i ω => g (ω i) / N
        let projectionTest : (Fin n → Ω) → Fin n → ℝ :=
          fun ω i => Shao.truncationF (z * ξ i ω)
        let δ : Fin n → ℝ :=
          fun i => ∫ ω : Fin n → Ω, projectionTest ω i ∂P
        let L : ℝ := ∑ i : Fin n, δ i
        let scalarBudget : ℝ :=
          ∫ o : Ω, Shao.truncationF (z * (g o / N)) ∂μ
        IsProbabilityMeasure P ∧
          Integrable (fun o : Ω => Shao.truncationF (z * (g o / N))) μ ∧
          (∀ i : Fin n, Integrable (fun ω : Fin n → Ω =>
            projectionTest ω i) P) ∧
          (∀ i : Fin n, δ i = scalarBudget) ∧
          L = (n : ℝ) * scalarBudget ∧
          (∀ i : Fin n, L = (n : ℝ) * δ i) ∧
          (∀ i : Fin n, 0 ≤ δ i) ∧
          0 ≤ L ∧
          L ≤ β * Real.rpow z p /
            Real.rpow (n : ℝ) ((p - 2) / 2) ∧
          (β = 0 → L = 0 ∧ (∀ i : Fin n, δ i = 0)) ∧
          ((β = 0 ∨
              (0 < β ∧ z ≤ c * Real.rpow β (-1 / p) *
                Real.rpow (n : ℝ) ((p - 2) / (2 * p)))) →
            L ≤ Real.rpow c p ∧
              (∀ i : Fin n, δ i < (1 / 2 : ℝ)) ∧
              L < cBudget * z ^ 2))

end

end Shao.OQ6.IIDSourceStrictMomentBudgets
```

## Quantifier and dependency contract

The carrier is an arbitrary measurable space. The probability assumption is
explicit and provides the finite IID product law. There is no standard-Borel,
atomlessness, mean-zero, unit-second-moment, kernel, residual, clipping, CDF,
Shao-Zhou callback, sequence, or convergence premise. `hg2` is the L2 input
required by the qualified scalar API; `hgp` states genuine p-moment
integrability. No integral is used as a substitute for an integrability proof.

The constant `c` has its entire ordinary typed right-hand side in the result.
It captures exactly `p` and `cBudget`, and is chosen before the universal
`n,z`. In particular it does not capture `μ,g,β,n,z`. Its exact pth power is
half of the smaller strict allowance, so the strict inequalities do not appear
as assumptions.

The ordinary lets capture the following full dependency sets:

| Let | Type | Free data captured by the right-hand side |
| --- | --- | --- |
| `β` | `ℝ` | `Ω`, its measurable structure, `μ`, `g`, `p` |
| `c` | `ℝ` | `p`, `cBudget` |
| `P` | `Measure (Fin n → Ω)` | `Ω`, its measurable structure, `μ`, `n` |
| `N` | `ℝ` | `n` |
| `ξ` | `Fin n → (Fin n → Ω) → ℝ` | `Ω`, `n`, `g`, `N` |
| `projectionTest` | `(Fin n → Ω) → Fin n → ℝ` | `Ω`, `n`, `z`, `ξ`, qualified `Shao.truncationF` |
| `δ` | `Fin n → ℝ` | `Ω`, `n`, `P`, `projectionTest` |
| `L` | `ℝ` | `n`, `δ` |
| `scalarBudget` | `ℝ` | `Ω`, its measurable structure, `μ`, `g`, `z`, `N` |

`_hn` and `_hz` are named proof binders inside the universal statement. The
anonymous instance binders are exactly `[MeasurableSpace Ω]` and
`[IsProbabilityMeasure μ]`. Product measurability and finite-coordinate
instances are supplied by the imported standard product construction. There
are no existential witnesses, callbacks, unprinted dependent lets, or local
instance values hidden in the public head. `IsProbabilityMeasure P` is an
explicit conclusion, not an additional input.

## Boundary and source contract

For every `n ≥ 1,z ≥ 1`, the product/marginal identities and the quantitative
rate hold without a window restriction. For `β > 0`, the final implication
uses exactly the printed S19 source-z window, including its closed upper
endpoint. It then gives `L ≤ c^p`, every `δ_i < 1/2`, and `L < cBudget*z²`.
The theorem does not identify `cBudget` with a published constant.

For `β = 0`, the unconditional rate and nonnegativity force `L = 0`, and each
nonnegative summand vanishes. The zero branch therefore gives the strict
margins for every `z ≥ 1`, instead of calling the printed negative-power
window nonempty at zero. In Lean, `Real.rpow 0 (-1/p) = 0` because the exponent
is nonzero. That total convention would make the printed window impossible
when `z ≥ 1`; the explicit disjunction prevents a vacuous treatment of this
degenerate model. No positive-beta premise is added to the generic theorem.

The upper p endpoint `p = 3` is included, with its explicit third-moment
integrability. The lower endpoint `p = 2` is outside the requested S19 growing
window scope; the qualified scalar API itself permits it. For every allowed
`p`, the window exponent `(p-2)/(2*p)` is positive. The same fixed `c` works
for all `n,z`; no n-dependent constant or sufficiently-large-n premise is
introduced. For positive `β` the window is eventually nonempty as n grows.

For the standardized original projection, `∫g² = 1` excludes `β = 0`:
zero nonnegative p-moment would force `g = 0` almost everywhere and hence
`∫g² = 0`. The existing qualified conditional-standardized p-moment result
even gives `1 ≤ β` in its own stronger model. That stronger model is not
imported into this generic result and no original-root assumptions change.

The mathematical route and exact qualified scalar interface are in
`SOURCE-AND-ROUTE.md`. Lead freeze, implementation, independent final review,
server kernel and transitive-axiom receipts all remain outstanding.
