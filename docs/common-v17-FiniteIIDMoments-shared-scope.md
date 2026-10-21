# Shared finite iid second-moment module: extraction proposal

Status: PROPOSED, AWAITING COORDINATOR FREEZE. This unit changes only this
scope document. No candidate Lean implementation, compilation, cache
operation, frozen-source edit or worktree synchronization has been done.
The existing OQ56 PR18 and `lead-oq56` worktree remain untouched.

## Read-only inputs and selected packaging

The actual server source read for this proposal is

```text
workspaces/lead-oq56/Shao/OQ5/P35/FiniteIIDMoments.lean
SHA256 4b2c65ec7fb03767b6a469ef5918592c9a76e993ad95262e6a7aae6840c4520b
539 lines; namespace Shao.OQ5.P35
```

The hash was checked before reading the full numbered source. The only
OQ5 implementation imported by it is `RowIdentity.lean`, also read in full:

```text
workspaces/lead-oq56/Shao/OQ5/P35/RowIdentity.lean
SHA256 73bb0809bc6d323b31775327e468677d6320b38f8fe87363936860164f17f975
```

The consumer proposal is `drafts/c12/FourierPower-next-scope.md`, SHA256
`a0c19a11198fa35d63cb78ea7c066f427b2d1a91fb159f5951d5a8b0a1074943`.
It needs the actual raw square moment of a finite iid coordinate sum,
including length zero and nonzero mean; it must not reprove the accepted
generic iid square identity or import a specialized OQ5 theorem through a
common Probability module.

Recommended follow-up, only after the coordinator freezes this scope and
PR18 has been integrated:

1. Create `Shao/Probability/FiniteIIDMoments.lean`, namespace
   `Shao.Probability`, as the sole implementation of the existing generic
   moment proofs: 3 definitions and 6 public theorems, with their original
   assumptions and proof bodies.
2. In a new follow-up change, turn
   `Shao/OQ5/P35/FiniteIIDMoments.lean` into a compatibility entry point:
   keep its original 3 definition bodies and original 6 public theorem
   signatures; replace only theorem proofs with applications of the new
   shared theorems. Keep importing `RowIdentity` there.
3. Change no OQ5 consumer, `RowIdentity`, common root import or existing
   path definition as part of the selected extraction.

Keeping the original small definition bodies is intentional source
compatibility, not a second moment proof or a new sum convention. The
common and old functions have definitionally identical bodies after
unfolding `unorderedPairSum`; `rfl` bridges must be checked. This is safer
than replacing the old definitions with `abbrev := newName`, because an
existing consumer uses `dsimp only [finiteFeatureSum,
finitePairProductSum, ...]`. Introducing another named definition layer
could change that restricted unfolding behavior. No public equality
lemmas or new probabilistic assumptions are needed for compatibility.

## Minimal dependency closure actually observed

The original source refers to only two declarations from `RowIdentity`:

| Original use | Actual meaning | Shared replacement |
|---|---|---|
| line 31: `unorderedPairSum` | `sum i, sum j, if i<j then H i j else 0` | Inline this exact body in the shared `finitePairProductSum`. This is definitionally the same function. |
| line 471: `pairCount_eq_choose m` | `(m:real)*((m:real)-1)/2 = (m.choose 2:real)` | `(Nat.cast_choose_two ℝ m).symm`, from the actual pinned Mathlib theorem. |

No kernel, row mean, U-statistic, Studentizer, counterexample law,
projection, category or OQ5 parameter enters any generic iid proof.
`Shao.Probability.FiniteIID` is not used through any of its project
declarations in the old moment source; its relevant Mathlib imports can
instead be imported directly. Thus the selected new module can have **no
Shao project imports**, and in particular no transitive OQ5 import.

Proposed explicit imports are

```lean
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
```

`Ring` is explicitly retained because removing `RowIdentity` otherwise
removes one direct source of its tactic import. This is the intended
project dependency boundary, not a claim that every listed Mathlib import
is irredundant. The original `set_option autoImplicit false`,
`noncomputable section`, section variables, `include`/`omit` binders,
open namespaces and BigOperators scope are preserved.

For the C1/C2 raw-sum theorem alone, the strict proof closure is smaller:

```text
finiteFeatureSum
private subsetSum
private subset_sum_memLp -> subset_sum_mean -> subset_sum_second
private iid_coord_memLp, iid_coord_mean, iid_coord_second
public finite_iid_sumSquare_integral
```

Here the arrows indicate shared helper reuse, not that each preceding
helper directly calls the next. Splitting just that subset out while
leaving the other old generic proofs in OQ5 would require duplicating the
private subset proofs, exposing internal helpers as additional public API,
or substantively restructuring the old proofs. Moving the entire already
generic block avoids those costs and gives OQ56 and C1/C2 one canonical
proof implementation. This proposal therefore selects the existing whole
3-definition/6-theorem block, not a new generalized moment hierarchy.

## Exact shared definitions and public signatures

The following is the complete proposed new public interface. Only the
namespace and the expanded pair-sum body differ from the old public
objects. Assumptions are neither weakened nor strengthened.

```lean
namespace Shao.Probability

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

def finiteFeatureSum {m : ℕ} {Ω : Type*}
    (Z : Fin m → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin m, Z i ω

def finiteLeaveOwnSquareSum {m : ℕ} {Ω : Type*}
    (Z : Fin m → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin m, Z i ω ^ 2 * (finiteFeatureSum Z ω - Z i ω) ^ 2

def finitePairProductSum {m : ℕ} {Ω : Type*}
    (Z : Fin m → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin m, ∑ l : Fin m,
    if i < l then Z i ω * Z l ω else 0

variable {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} {ν : Measure ℝ}
variable {Z : Fin m → Ω → ℝ}

theorem finite_iid_leaveOwnSquare_integrable
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hZ : ∀ i, Measurable (Z i)) (hIndep : iIndepFun Z μ)
    (hLaw : ∀ i, IdentDistrib (Z i) (id : ℝ → ℝ) μ ν)
    (hν2 : MemLp (id : ℝ → ℝ) 2 ν) :
    Integrable (finiteLeaveOwnSquareSum Z) μ

theorem finite_iid_leaveOwnSquare_integral
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hZ : ∀ i, Measurable (Z i)) (hIndep : iIndepFun Z μ)
    (hLaw : ∀ i, IdentDistrib (Z i) (id : ℝ → ℝ) μ ν)
    (hν2 : MemLp (id : ℝ → ℝ) 2 ν) :
    (∫ ω, finiteLeaveOwnSquareSum Z ω ∂μ) =
      (m : ℝ) * (∫ z, z ^ 2 ∂ν) *
        (((m - 1 : ℕ) : ℝ) * (∫ z, z ^ 2 ∂ν) +
          ((m - 1 : ℕ) : ℝ) * ((m - 2 : ℕ) : ℝ) * (∫ z, z ∂ν) ^ 2)

theorem finite_iid_pairProduct_memLp_two
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hZ : ∀ i, Measurable (Z i)) (hIndep : iIndepFun Z μ)
    (hLaw : ∀ i, IdentDistrib (Z i) (id : ℝ → ℝ) μ ν)
    (hν2 : MemLp (id : ℝ → ℝ) 2 ν) :
    MemLp (finitePairProductSum Z) 2 μ

theorem finite_iid_sumSquare_integral
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hZ : ∀ i, Measurable (Z i)) (hIndep : iIndepFun Z μ)
    (hLaw : ∀ i, IdentDistrib (Z i) (id : ℝ → ℝ) μ ν)
    (hν2 : MemLp (id : ℝ → ℝ) 2 ν) :
    (∫ ω, finiteFeatureSum Z ω ^ 2 ∂μ) =
      (m : ℝ) * (∫ z, z ^ 2 ∂ν) +
        (m : ℝ) * ((m - 1 : ℕ) : ℝ) * (∫ z, z ∂ν) ^ 2

theorem finite_iid_pairProduct_integral
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hZ : ∀ i, Measurable (Z i)) (hIndep : iIndepFun Z μ)
    (hLaw : ∀ i, IdentDistrib (Z i) (id : ℝ → ℝ) μ ν)
    (hν2 : MemLp (id : ℝ → ℝ) 2 ν) :
    (∫ ω, finitePairProductSum Z ω ∂μ) =
      (m.choose 2 : ℝ) * (∫ z, z ∂ν) ^ 2

theorem finite_iid_pairProduct_variance
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hZ : ∀ i, Measurable (Z i)) (hIndep : iIndepFun Z μ)
    (hLaw : ∀ i, IdentDistrib (Z i) (id : ℝ → ℝ) μ ν)
    (hν2 : MemLp (id : ℝ → ℝ) 2 ν) :
    variance (finitePairProductSum Z) μ =
      (m.choose 2 : ℝ) * (variance (id : ℝ → ℝ) ν) ^ 2 +
        (m : ℝ) * (((m - 1 : ℕ) : ℝ) ^ 2) *
          (∫ z, z ∂ν) ^ 2 * variance (id : ℝ → ℝ) ν

end
end Shao.Probability
```

These are theorem signatures for review, not an implementation with
omitted proof placeholders. The future `.lean` file must have complete
proofs throughout.

## Private proof inventory and permitted mechanical edits

Move the following original private helpers without exposing them as new
public API:

| Original source | Helpers |
|---|---|
| 33–38 | private definitions `subsetSum`, `subsetPair` |
| 45–81 | `subset_sum_measurable`, `subset_pair_measurable`, `subset_sum_memLp`, `distinct_product_memLp`, `subset_pair_memLp` |
| 83–113 | `subset_sum_mean`, `subset_sum_second` |
| 115–160 | `subset_pair_insert`, `subset_pair_sum_indep` |
| 162–289 | `centered_pair_moments`, `subset_pair_center` |
| 302–318 | `iid_coord_memLp`, `iid_coord_mean`, `iid_coord_second` |
| 320–348 | `iid_leaveOwn_indep`, `iid_leaveOwn_term_integrable` |
| 425–512 | `iid_pair_statistics` |

There are 2 private definitions and 17 private theorems. The two private
measurability helpers have no reference elsewhere in this original file;
they are not needed for the minimal dependency closure. They may be
carried over unchanged to preserve the source block and declaration order;
this proposal does not combine extraction with a dead-code cleanup.
All remaining private helpers support the existing six public results.

The original public proofs at 351–357, 360–395, 398–404, 407–423,
515–521 and 524–533 move to the new namespace. The only intentional
proof-term change is the neutral pair-count replacement at old line 471:

```lean
have hcnt : (m : ℝ) * ((m : ℝ) - 1) / 2 = (m.choose 2 : ℝ) :=
  (Nat.cast_choose_two ℝ m).symm
```

Pinned Mathlib `Data/Nat/Choose/Cast.lean:45–47` has exactly this theorem:
`Nat.cast_choose_two (K : Type*) [DivisionRing K] [NeZero (2 : K)]
(a : ℕ) : (a.choose 2 : K) = a * (a - 1) / 2`.
This replaces the same deterministic identity, not an iid step or a new
assumption. There is no need to migrate `pairCount`, `unorderedPairSum`,
`two_mul_choose_two`, or any OQ5 row algebra to a common module.

If a missing transitive tactic import is exposed by the future standalone
check, add only its appropriate Mathlib import. Do not repair a missing
common import by importing OQ5. Any actual statement or proof-route
change beyond these packaging edits must be reported to the coordinator.

## Compatibility entry point and definitional identity checks

After PR18 integration, the compatibility module should import

```lean
import Shao.OQ5.P35.RowIdentity
import Shao.Probability.FiniteIIDMoments
```

It keeps the original namespace, original three definition bodies and
original six theorem signatures. Each public theorem is a thin wrapper
of its shared same-basename theorem. For example, in the original binder
context, the original `finite_iid_sumSquare_integral` proof is replaced by

```lean
  Shao.Probability.finite_iid_sumSquare_integral hZ hIndep hLaw hν2
```

The two sides' finite sums are definitionally equal, so no conversion of
the random variables, law or event is involved. If elaboration needs the
definitions named explicitly, a `simpa only [...] using ...` wrapper is
permitted; the theorem signature must remain exactly the original one.
Do not implement compatibility using only `open` or an unqualified
`export`: the old fully qualified declaration names must continue to
exist. Do not rewrite old consumers to use the new names as a workaround.

Separate future server examples must check, for every `m`, `Ω`, `Z`, `ω`,
the following three equalities using `rfl`:

```lean
Shao.OQ5.P35.finiteFeatureSum Z ω =
  Shao.Probability.finiteFeatureSum Z ω
Shao.OQ5.P35.finiteLeaveOwnSquareSum Z ω =
  Shao.Probability.finiteLeaveOwnSquareSum Z ω
Shao.OQ5.P35.finitePairProductSum Z ω =
  Shao.Probability.finitePairProductSum Z ω
```

Old proof objects or `.olean` binary bytes cannot be preserved after an
implementation is relocated: private fully qualified names change and
dependents must be rebuilt. The intended identity is unchanged public
types, definitionally equal finite random variables and a single shared
proof implementation, not byte-identical kernel terms or artifacts.

Actual source search found three direct importers in the inspected OQ56
tree:

```text
Shao/OQ5/P35/ConditionalStatistics.lean
Shao/OQ5/P35/ConditionalStudentizer.lean
Shao/OQ5/P35/ConditionalNumerator.lean
```

`ConditionalNumerator.lean:243–245` uses restricted `dsimp only` on the two
definitions; this motivates keeping their exact old bodies. Its private
`iid_sum_statistics` at 109–135 separately derives sum L2, mean and variance
with Mathlib APIs. That helper is **not** moved or edited in this batch.
There is no reference to the old module's mangled private declarations in
the inspected Shao source tree. Follow-up discovery of further consumers
must broaden compatibility testing, not silently drop their old names.

## C1/C2 use, actual moments and boundary preservation

For `FourierPower`, the shared sum is connected to the existing path sum
without defining another path or adding a new public convention:

```lean
-- In a consumer importing both common modules:
Shao.Probability.finiteFeatureSum X ω =
  Shao.prefixSum (Shao.Probability.samplePath X ω) ℓ
```

The future local proof is `by simp only [Shao.prefixSum_length,
Shao.Probability.samplePath, Shao.Probability.finiteFeatureSum]` for
`X : Fin ℓ → Ω → ℝ`. This is a caller-side equality proof, not a new
required public declaration. The consumer converts its exact input
`Integrable (fun a : ℝ => a^2) ν` to `MemLp id 2 ν` using the already
available `memLp_two_iff_integrable_sq` and invokes the shared theorem.

No centered sum theorem, mean-zero input, positive variance, fourth
moment, third moment or a free replacement value for the raw second
moment is introduced. Distinct-coordinate products are in L2 because of
actual independence and coordinate L2; the expressions do not require a
single-coordinate fourth moment. The leave-own expression excludes the
own coordinate before multiplying its square by the remaining-sum square.

All original zero/small-length branches are preserved, especially:

- `m=0`: the sums are the actual empty sum; all displayed identities are
  zero with the original vacuous coordinate conditions.
- `m=1`: the pair and leave-own sums vanish; the raw sum square is the
  actual single-coordinate second moment. The leave-own proof's explicit
  `m=1` branch remains before casting `m-2`.
- Natural subtraction remains `((m-1 : ℕ) : ℝ)` and
  `((m-2 : ℕ) : ℝ)` in every public statement. The original `m=0` split
  in `sumSquare` and pair variance remains before `Nat.cast_sub`.
- Means may be nonzero; raw second moments are not replaced by variance.
  Degenerate constant laws, zero variance and negative coordinate values
  remain allowed. No division by sample length or variance is added.

The finitePower scope's centered identity and first-moment payment remain
short caller-side algebra from genuine L2 integrability, finite integral
linearity and the shared raw-square identity. They are not folded into
this extraction as additional public claims.

## Future required checks and current cache evidence

No Lean command has been run for this proposal. Read-only server source
inspection confirmed `Nat.cast_choose_two` exactly as above. Read-only
artifact checks found `Mathlib.Data.Nat.Choose.Cast`, `Mathlib.Tactic.Ring`
and `Mathlib.Tactic.Linarith` already cached in the pinned server package
tree; all other imports are existing imports of the accepted module or
existing common `FiniteIID` module. No cache request is currently needed.
All future elaboration and compilation must remain on the server.

After explicit freeze and after PR18 integration, necessary checks are:

1. In the coordinator's assigned follow-up worktree, hash-bind the accepted
   original source before editing. Compile only the new shared module
   first and confirm its direct/transitive project imports contain no
   `Shao.OQ5` module. No common root entry change is needed.
2. Compile the old compatibility entry point; `#check @` all old and new
   public definitions/theorems, compare binder types and assumption lists,
   and run the three `rfl` equality examples plus the path-sum bridge.
3. Compile each direct existing importer above with unchanged source, in
   dependency order, against the replacement entry point; refresh dependent
   artifacts rather than relying on stale `.olean` files. The OQ56 lead
   and root coordinate these checks without editing `lead-oq56` in place.
   Root may run its usual broader integration gate afterward.
4. Inspect a source diff showing the original generic proof block moved
   under the new namespace, the two neutral dependency replacements, and
   thin old theorem wrappers. Review every additional import or proof
   adjustment explicitly; no second iid-moment proof should remain in OQ5.
5. Run forbidden-token scans and a fresh full new-declaration transitive
   axiom audit for the new shared namespace/private prefix and all old
   wrappers. Include generated definitions and helper declarations. Only
   `propext`, `Classical.choice`, `Quot.sound` are permitted.
6. Record new local/server source hashes, actual command exit results and
   unchanged consumer hashes, then arrange independent semantic/relocation
   review before integration. The old accepted source hash is a provenance
   input; it is not reused as the replacement entry point's new hash.

This proposal does not claim the extraction has already compiled, and
does not authorize changes to the still-frozen PR18 source or the other
lead's worktree. It closes only a shared packaging prerequisite after the
future gates pass. It proves no new Fourier derivative, conditional iid
law, Gaussian approximation, or root C1/C2/OQ56 result by itself.
