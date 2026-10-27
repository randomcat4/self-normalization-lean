# Unit233 Stage1 source and route

Status: local declaration/source/API design only; no freeze, proof body, Lean command, server action, network action, publication or delegated child. All quoted API heads are from exact local qualified snapshots bound in INPUT-BINDINGS.json. Their already accepted proofs and receipts are reused as dependencies; this document does not recertify them. No unit228/unit231 unqualified proof or review, and no unit232 implementation, was read.

Primary p54 §§1–3 and p51 S1–S8 were read in full. p54 F4/F5 is the selected mathematical scope. The p51 S6 p-moment rate sentence is superseded by p54 F1–F3; nothing in this candidate uses that false rate. The precise selected branch is p51 S16–S17 with bounded-polylog envelope, rather than DC S18. The published Shao–Zhou self-normalized input remains attributed through OriginalGoodEventProbability/OriginalNormalizedUpperTail; this unit does not claim to reprove it.

## Source-to-candidate correspondence

| Source object | Exact candidate interpretation | Boundary |
| --- | --- | --- |
| Original iid observations | `sampleLaw n μ = Measure.pi (fun _ : Fin n => μ)` | Same fixed original μ; no conditional replacement |
| Original projection | `g`, `Measurable g`, `MemLp g 2 μ`, mean 0, second moment 1 | Fixed before cg/n/z; no fourth or mixed moment |
| F and rows ψ | `originalUpper n r x`, `originalRows n r x` | Actual original residual, off-diagonal rows; r globally symmetric |
| q0 and S16 height | `boundedPolylogMomentOrder t0 n`, `boundedPolylogHeight C a n` | Fixed C/a/t0/M; qualified eventual deterministic admissibility reused |
| S10/S11 Gy | `projectionGood n g z`, via exact normalizedGoodEvent bridge | cg supplied for this μ/g only |
| Actual Cn | C2 with only F and row-norm squared bounds | Omits unused squareSum(w); full failure event still pays |
| F4 Hn,y | `H = projectionGood n g z ∩ C2` | Explicit measurable ordinary-data event; no target callbacks |
| Actual D,d,V | Existing `residualStatisticD`, `centeredDelta`, `projectionV` | Same n coefficients; actual centered row geometry |
| Retained correction | `e1 x = clippedCenteredDelta n g r C0 rho 1 x` | Clip label 1 remains distinct from z; only contraction used |
| True s | `Real.sqrt (centeredSq n g r x)` | Positive on H by actual factorization; zero event paid |
| F5 original payment | `3 exp(−q) + exp(−cg n) + 4 exp(−z sqrt n / 2)` | Actual Hᶜ, not a surrogate B-bad event |

## Planned dependency route and all new obligations

1. Extract `cg`, its positivity and the all-n/all-y complement bound once from `original_good_event_complement_bound μ g hg hg2 hgmean hgsecond`. This occurs before C/a/t0/M and before the eventual n filter. Transfer the exact event with `normalizedGoodEvent_eq_projectionGood`; no conditioning or choice of cg after z.
2. For C/a/t0/M obtain the eventual concentration theorem `eventually_boundedPolylog_product_joint_failure`, intersected with n ≥ 4. This qualified theorem already includes the moment-order ≥ 2 and bounded-height window prerequisites in its proof. No old producer build or a new caller admissibility callback is needed. After n is selected, instantiate only the genuine r/w integrability, canonicality and envelope hypotheses. The threshold is uniform in those r/w and in C0/rho/z.
3. Define the candidate's exact q/K/G/C2/H/e1 lets. Measurability is a new finite-observable obligation, not a caller premise. For i,j, `x ↦ g(x i)` is measurable by evaluation and hg; `x ↦ r(x i)(x j)` is measurable by the product of evaluations and hr. Finite sums/absolute values/squares give originalUpper, projectionEnergy, projectionW and rowSum observables. Rewrite the literal originalRows norm squared by `EuclideanSpace.real_norm_sq_eq` and its `WithLp.toLp` definition as the finite sum of rowSum squares. This avoids requiring a measurable Euclidean-space output theorem. Real sqrt is continuous on ℝ, so the literal G bound is measurable. Intersections and measurable inequality sets give H. This uses no `Measurable w`, no completion of μ and no selection of an a.e. representative of the event.
4. For every actual x ∈ H pass its two C2 bounds, its G membership, n ≥ 4, symmetry, K ≥ 0 and t0 > 0 to `bounded_remainder_small_window`. The literal K is positive by `bounded_scales_pos M hM`. That head returns V > 0, the ratio bound z|D|/V ≤ 1/8 and both d bounds ≤ 1/32. Convert only the ratio to z|D| ≤ V/8 using that same V > 0. The strict numerator bound follows because V/8 < V/4. The lower d margin follows from −|d| ≤ d and |d| ≤ 1/32; energy ≥ 1/2 is already literal G membership.
5. Instantiate `clippedCenteredDelta_bounds` at the retained clip label y = 1, using hC0/hrho and the numerical nonnegativity of 1. Its absolute contraction gives the e1 bounds after multiplication by the nonnegative z². Its last conclusion gives the retained clipped denominator's positivity on H. No budget domination or target-goodness hypothesis is added. With d ≥ −1/2 and V > 0 use `centered_studentizer_factorization` for the true sqrt(centeredSq) positivity and exact **actual-d** factorization. The result does not replace d by e1 in this equality.
6. The two zero events cannot occur in H by the two positive conclusions, so their union lies in Hᶜ pointwise. No atomlessness or tail continuity is used.
7. Let B be the exact `boundedProductFailure n r w M q`. From the literal threshold definitions, C2ᶜ ⊆ B, even though H does not test squareSum(w). Consequently Hᶜ ⊆ Gᶜ ∪ B. `measureReal_mono` and `measureReal_union_le` on the finite original product law bound the actual H complement by the sum of the qualified original-G and joint-failure bounds. Real measure here is finite; these inequalities do not require global measurability of B or w. H itself has the separately derived genuine measurable-set conclusion. Reassociate the three terms to the exact candidate RHS.

The route above describes the obligations of later implementation, not an implemented proof. New routine finite measurability/set/algebra steps remain to be constructed and checked after the parent freezes a statement. All mathematical probability/concentration inputs invoked here have explicit qualified heads below. No conclusion is introduced as a premise through a renamed lemma or callback.

## Quantifier and edge-case audit

The order is Ω/mΩ/μ/hμ/g/projection assumptions → existential cg → universally quantified concentration constants and their signs → eventual n ≥ 4 → arbitrary r/w with exact canonical product-envelope assumptions → arbitrary nonnegative clip C0/rho → z ≥ 1 in the original small window → fixed actual lets and conclusions. Thus n-dependent residual/envelope choices on the same μ/g are covered, while n-dependent μ/g are not. C0 and rho need not be identified with a model constant or residual L2 norm for this contraction-only result; a later full-model binding must supply those identifications if needed.

For n = 0,1,2,3 the ordinary definitions stay total but this theorem claims no frontier. If the legal z interval is empty at a particular n the universal window implication is vacuous; the positive window scale and eventual growth also permit nonempty intervals for large n. No extra hypothesis is introduced to force nonemptiness. M,C,a may be zero. t0 must be strictly positive. w may fail to be globally measurable; its square is integrable and the a.e. bounds are retained exactly as required by the qualified theorem. Canonicality is two separate a.e. integral equalities, integrability is on μ.prod μ, and symmetry is pointwise. No conditional expectation kernel or standard Borel assumption is added.

The exact full heads/ordinary RHS excerpts below are a dependency dictionary, not a new implementation. The generator records the source range and source-byte hash for each entry in INPUT-BINDINGS.json. The code fences preserve namespace-sensitive names; the original files provide the namespace/import context stated in each entry.

## Remaining boundaries and later gates

There is no discovered missing probability API for this fixed-law candidate. The new finite measurability construction, set inclusion, ratio-to-product conversion and scalar margin assembly still need implementation and normal independent/Lean verification; no Stage1 acceptance of a proof is claimed. There is a real missing interface for any extension claiming simultaneous uniform cg for conditional μn/gn, and a separate real budget-domination requirement for clip1 = d or physical/clipped equality. Those are excluded here. The original/trim/augmented same-witness passage, source epsilon upper-event limit, source analytic costs, fullmodel/m0/canonical-eta bindings, compact CDF/relative tail and OQ6 root closure remain later consumers.

The proposed result uses p54 only as a repaired source obligation and qualified exact APIs for the selected branch. It adds no p-moment rate, fourth/mixed-moment premise, unproved conditional-uniform low-energy theorem or surrogate replacement of the actual event payment.

## Exact dependency context

### Context for `CanonicalDoubleGhostRowMoments.lean`

The source pre-declaration namespace/open/universe/variable context is retained here. In particular FiniteRows and P35 RowIdentity have the implicit module variable `{n : ℕ}`.

```lean
set_option autoImplicit false
namespace Shao.OQ6.CanonicalDoubleGhostRowMoments
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
open Shao.OQ6.FiniteHilbertSignMoments
open Shao.OQ6.FiniteMatrixSignEnergy
open Shao.OQ6.DoubleGhostSignInvariance
```

### Context for `CanonicalDoubleGhostScalarMoments.lean`

The source pre-declaration namespace/open/universe/variable context is retained here. In particular FiniteRows and P35 RowIdentity have the implicit module variable `{n : ℕ}`.

```lean
set_option autoImplicit false
namespace Shao.OQ6.CanonicalDoubleGhostScalarMoments
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
open Shao.OQ6.FiniteHilbertSignMoments
open Shao.OQ6.FiniteMatrixSignEnergy
open Shao.OQ6.DoubleGhostSignInvariance
open Shao.OQ6.FiniteQuadraticSignChaos
open Shao.OQ6.CanonicalDoubleGhostRowMoments
```

### Context for `RowIdentity.lean`

The source pre-declaration namespace/open/universe/variable context is retained here. In particular FiniteRows and P35 RowIdentity have the implicit module variable `{n : ℕ}`.

```lean
namespace Shao.OQ5.P35
noncomputable section
open scoped BigOperators
variable {n : ℕ}
```

### Context for `FiniteRows.lean`

The source pre-declaration namespace/open/universe/variable context is retained here. In particular FiniteRows and P35 RowIdentity have the implicit module variable `{n : ℕ}`.

```lean
set_option autoImplicit false
namespace Shao.OQ6.FiniteRows
noncomputable section
open scoped BigOperators
variable {n : ℕ}
```

### Context for `BoundedPolylogWindow.lean`

The source pre-declaration namespace/open/universe/variable context is retained here. In particular FiniteRows and P35 RowIdentity have the implicit module variable `{n : ℕ}`.

```lean
set_option autoImplicit false
open Filter
open scoped Topology
namespace Shao.OQ5.P51
noncomputable section
```

### Context for `BoundedProductEnvelopeTails.lean`

The source pre-declaration namespace/open/universe/variable context is retained here. In particular FiniteRows and P35 RowIdentity have the implicit module variable `{n : ℕ}`.

```lean
set_option autoImplicit false
universe u
namespace Shao.OQ6.BoundedProductEnvelopeTails
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
open Shao.OQ6.StretchedExponentialSumMoments (coordinateSum)
open Shao.OQ6.DoubleGhostSignInvariance (pairedLaw)
open Shao.OQ6.CanonicalDoubleGhostRowMoments (pairedEnergy sampleLaw originalRows)
open Shao.OQ6.CanonicalDoubleGhostScalarMoments (originalUpper)
```

### Context for `BoundedStudentizerGeometry.lean`

The source pre-declaration namespace/open/universe/variable context is retained here. In particular FiniteRows and P35 RowIdentity have the implicit module variable `{n : ℕ}`.

```lean
set_option autoImplicit false
universe u
open scoped BigOperators
open Shao.OQ6.CanonicalDoubleGhostRowMoments (originalRows)
open Shao.OQ6.CanonicalDoubleGhostScalarMoments (originalUpper)
namespace Shao.OQ5.P51
noncomputable section
```

### Context for `BoundedRemainderPayments.lean`

The source pre-declaration namespace/open/universe/variable context is retained here. In particular FiniteRows and P35 RowIdentity have the implicit module variable `{n : ℕ}`.

```lean
set_option autoImplicit false
universe u
open Filter MeasureTheory
open scoped BigOperators ENNReal
open Shao.OQ6.BoundedProductEnvelopeTails (tailScale)
open Shao.OQ6.CanonicalDoubleGhostRowMoments (sampleLaw originalRows)
open Shao.OQ6.CanonicalDoubleGhostScalarMoments (originalUpper)
namespace Shao.OQ5.P51
noncomputable section
```

### Context for `BoundedPolylogConcentration.lean`

The source pre-declaration namespace/open/universe/variable context is retained here. In particular FiniteRows and P35 RowIdentity have the implicit module variable `{n : ℕ}`.

```lean
set_option autoImplicit false
universe u
open Filter MeasureTheory
open scoped BigOperators ENNReal
open Shao.OQ6.BoundedProductEnvelopeTails (squareSum tailScale)
open Shao.OQ6.CanonicalDoubleGhostRowMoments (sampleLaw originalRows)
open Shao.OQ6.CanonicalDoubleGhostScalarMoments (originalUpper)
namespace Shao.OQ5.P51
noncomputable section
```

### Context for `ClippedStudentizer.lean`

The source pre-declaration namespace/open/universe/variable context is retained here. In particular FiniteRows and P35 RowIdentity have the implicit module variable `{n : ℕ}`.

```lean
set_option autoImplicit false
universe u
noncomputable section
open scoped Classical
namespace Shao.OQ5.P51
```

### Context for `OriginalGhostGoodEvent.lean`

The source pre-declaration namespace/open/universe/variable context is retained here. In particular FiniteRows and P35 RowIdentity have the implicit module variable `{n : ℕ}`.

```lean
set_option autoImplicit false
namespace Shao.OQ6.OriginalGhostGoodEvent
noncomputable section
open MeasureTheory
open scoped BigOperators
```

### Context for `OriginalGoodEventProbability.lean`

The source pre-declaration namespace/open/universe/variable context is retained here. In particular FiniteRows and P35 RowIdentity have the implicit module variable `{n : ℕ}`.

```lean
set_option autoImplicit false
open scoped BigOperators
open MeasureTheory
namespace Shao.OQ6.OriginalGoodEventProbability
noncomputable section
```

### Context for `OriginalGoodEventBridge.lean`

The source pre-declaration namespace/open/universe/variable context is retained here. In particular FiniteRows and P35 RowIdentity have the implicit module variable `{n : ℕ}`.

```lean
set_option autoImplicit false
namespace Shao.OQ6.OriginalGoodEventBridge
```

## Exact dependency dictionary

The following 56 entries are exact source-derived excerpts. Definition entries retain all ordinary RHS; theorem entries retain the complete head and omit accepted proof bodies.

### Shao.OQ6.CanonicalDoubleGhostRowMoments.sampleLaw

Source: `library/Shao/OQ6/CanonicalDoubleGhostRowMoments.lean`, lines 19–19. exact definition including full ordinary RHS.

```lean
def sampleLaw (n : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω] (ν : Measure Ω) : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => ν)
```

### Shao.OQ6.CanonicalDoubleGhostRowMoments.originalRows

Source: `library/Shao/OQ6/CanonicalDoubleGhostRowMoments.lean`, lines 23–23. exact definition including full ordinary RHS.

```lean
def originalRows (n : ℕ) {Ω : Type*} (r : Ω → Ω → ℝ) (x : Fin n → Ω) : EuclideanSpace ℝ (Fin n) := WithLp.toLp (2 : ℝ≥0∞) (V := Fin n → ℝ) (fun i : Fin n => ∑ j : Fin n, if i = j then 0 else r (x i) (x j))
```

### Shao.OQ6.CanonicalDoubleGhostScalarMoments.originalUpper

Source: `library/Shao/OQ6/CanonicalDoubleGhostScalarMoments.lean`, lines 31–32. exact definition including full ordinary RHS.

```lean
def originalUpper (n : ℕ) {Ω : Type*} (r : Ω → Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j then r (x i) (x j) else 0
```

### Shao.OQ5.P35.unorderedPairSum

Source: `library/Shao/OQ5/P35/RowIdentity.lean`, lines 33–34. exact definition including full ordinary RHS.

```lean
def unorderedPairSum (H : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j then H i j else 0
```

### Shao.OQ5.P35.mean

Source: `library/Shao/OQ5/P35/RowIdentity.lean`, lines 48–48. exact definition including full ordinary RHS.

```lean
def mean (f : Fin n → ℝ) : ℝ := (n : ℝ)⁻¹ * ∑ i : Fin n, f i
```

### Shao.OQ5.P35.center

Source: `library/Shao/OQ5/P35/RowIdentity.lean`, lines 51–51. exact definition including full ordinary RHS.

```lean
def center (f : Fin n → ℝ) (i : Fin n) : ℝ := f i - mean f
```

### Shao.OQ6.FiniteRows.uStatistic

Source: `library/Shao/OQ6/FiniteRows.lean`, lines 24–25. exact definition including full ordinary RHS.

```lean
def uStatistic (H : Fin n → Fin n → ℝ) : ℝ :=
  (n.choose 2 : ℝ)⁻¹ * Shao.OQ5.P35.unorderedPairSum H
```

### Shao.OQ6.FiniteRows.rowMean

Source: `library/Shao/OQ6/FiniteRows.lean`, lines 28–29. exact definition including full ordinary RHS.

```lean
def rowMean (H : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  ((n : ℝ) - 1)⁻¹ * ∑ j ∈ Finset.univ.erase i, H i j
```

### Shao.OQ6.FiniteRows.jackknifeSq

Source: `library/Shao/OQ6/FiniteRows.lean`, lines 32–34. exact definition including full ordinary RHS.

```lean
def jackknifeSq (H : Fin n → Fin n → ℝ) : ℝ :=
  (4 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2) *
    ∑ i : Fin n, (rowMean H i - uStatistic H) ^ 2
```

### Shao.OQ5.P51.boundedPolylogHeight

Source: `library/Shao/OQ5/P51/BoundedPolylogWindow.lean`, lines 29–30. exact definition including full ordinary RHS.

```lean
def boundedPolylogHeight (C a : ℝ) (n : ℕ) : ℝ :=
  C * Real.rpow (Real.log (n : ℝ)) a
```

### Shao.OQ5.P51.boundedPolylogMomentOrder

Source: `library/Shao/OQ5/P51/BoundedPolylogWindow.lean`, lines 32–33. exact definition including full ordinary RHS.

```lean
def boundedPolylogMomentOrder (t0 : ℝ) (n : ℕ) : ℝ :=
  t0 * Real.rpow (n : ℝ) (1 / 3 : ℝ)
```

### Shao.OQ6.BoundedProductEnvelopeTails.squareSum

Source: `library/Shao/OQ6/BoundedProductEnvelopeTails.lean`, lines 29–35. exact definition including full ordinary RHS.

```lean
def squareSum
    (n : ℕ)
    {Ω : Type u}
    (w : Ω → ℝ)
    (x : Fin n → Ω) :
  ℝ :=
  ∑ i : Fin n, (w (x i)) ^ 2
```

### Shao.OQ6.BoundedProductEnvelopeTails.commonMomentScale

Source: `library/Shao/OQ6/BoundedProductEnvelopeTails.lean`, lines 37–40. exact definition including full ordinary RHS.

```lean
def commonMomentScale
    (M : ℝ) :
  ℝ :=
  64 * (M + 1)
```

### Shao.OQ6.BoundedProductEnvelopeTails.envelopeTailScale

Source: `library/Shao/OQ6/BoundedProductEnvelopeTails.lean`, lines 42–45. exact definition including full ordinary RHS.

```lean
def envelopeTailScale
    (M : ℝ) :
  ℝ :=
  4 * M + 8
```

### Shao.OQ6.BoundedProductEnvelopeTails.squareTailScale

Source: `library/Shao/OQ6/BoundedProductEnvelopeTails.lean`, lines 47–50. exact definition including full ordinary RHS.

```lean
def squareTailScale
    (M : ℝ) :
  ℝ :=
  Real.exp 1 * (M + 1)
```

### Shao.OQ6.BoundedProductEnvelopeTails.scalarTailScale

Source: `library/Shao/OQ6/BoundedProductEnvelopeTails.lean`, lines 52–55. exact definition including full ordinary RHS.

```lean
def scalarTailScale
    (M : ℝ) :
  ℝ :=
  8 * Real.exp 1 * envelopeTailScale M
```

### Shao.OQ6.BoundedProductEnvelopeTails.rowTailScale

Source: `library/Shao/OQ6/BoundedProductEnvelopeTails.lean`, lines 57–60. exact definition including full ordinary RHS.

```lean
def rowTailScale
    (M : ℝ) :
  ℝ :=
  8 * (Real.exp 1) ^ 2 * (envelopeTailScale M) ^ 2
```

### Shao.OQ6.BoundedProductEnvelopeTails.tailScale

Source: `library/Shao/OQ6/BoundedProductEnvelopeTails.lean`, lines 62–65. exact definition including full ordinary RHS.

```lean
def tailScale
    (M : ℝ) :
  ℝ :=
  max (squareTailScale M) (max (scalarTailScale M) (rowTailScale M))
```

### Shao.OQ6.BoundedProductEnvelopeTails.bounded_scales_pos

Source: `library/Shao/OQ6/BoundedProductEnvelopeTails.lean`, lines 320–325. exact theorem head; proof assignment/body excluded.

```lean
theorem bounded_scales_pos
    (M : ℝ)
    (hM0 : 0 ≤ M) :
  0 < commonMomentScale M ∧ 0 < envelopeTailScale M ∧
  0 < squareTailScale M ∧ 0 < scalarTailScale M ∧
  0 < rowTailScale M ∧ 0 < tailScale M
```

### Shao.OQ5.P51.sampledKernel

Source: `library/Shao/OQ5/P51/BoundedStudentizerGeometry.lean`, lines 30–33. exact definition including full ordinary RHS.

```lean
def sampledKernel
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (x : Fin n → Ω) : Fin n → Fin n → ℝ :=
  fun (i j : Fin n) => g (x i) + g (x j) + r (x i) (x j)
```

### Shao.OQ5.P51.projectionEnergy

Source: `library/Shao/OQ5/P51/BoundedStudentizerGeometry.lean`, lines 37–40. exact definition including full ordinary RHS.

```lean
def projectionEnergy
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  (∑ i : Fin n, (g (x i)) ^ (2 : ℕ)) / (n : ℝ)
```

### Shao.OQ5.P51.projectionV

Source: `library/Shao/OQ5/P51/BoundedStudentizerGeometry.lean`, lines 44–47. exact definition including full ordinary RHS.

```lean
def projectionV
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  Real.sqrt (projectionEnergy n g x)
```

### Shao.OQ5.P51.projectionW

Source: `library/Shao/OQ5/P51/BoundedStudentizerGeometry.lean`, lines 51–54. exact definition including full ordinary RHS.

```lean
def projectionW
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  (∑ i : Fin n, g (x i)) / Real.sqrt (n : ℝ)
```

### Shao.OQ5.P51.residualStatisticD

Source: `library/Shao/OQ5/P51/BoundedStudentizerGeometry.lean`, lines 58–61. exact definition including full ordinary RHS.

```lean
def residualStatisticD
    (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  originalUpper n r x / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
```

### Shao.OQ5.P51.residualU

Source: `library/Shao/OQ5/P51/BoundedStudentizerGeometry.lean`, lines 65–68. exact definition including full ordinary RHS.

```lean
def residualU
    (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (x : Fin n → Ω) : Fin n → ℝ :=
  fun i : Fin n => originalRows n r x i / ((n : ℝ) - 2)
```

### Shao.OQ5.P51.residualEnergyJ

Source: `library/Shao/OQ5/P51/BoundedStudentizerGeometry.lean`, lines 72–75. exact definition including full ordinary RHS.

```lean
def residualEnergyJ
    (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  ∑ i : Fin n, (residualU n r x i) ^ (2 : ℕ)
```

### Shao.OQ5.P51.centeredSq

Source: `library/Shao/OQ5/P51/BoundedStudentizerGeometry.lean`, lines 79–82. exact definition including full ordinary RHS.

```lean
def centeredSq
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  Shao.OQ6.FiniteRows.jackknifeSq (sampledKernel n g r x) / 4
```

### Shao.OQ5.P51.centeredDelta

Source: `library/Shao/OQ5/P51/BoundedStudentizerGeometry.lean`, lines 86–91. exact definition including full ordinary RHS.

```lean
def centeredDelta
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  @ite ℝ (projectionV n g x = 0)
    (Classical.propDecidable (projectionV n g x = 0))
    (0 : ℝ) (centeredSq n g r x / (projectionV n g x) ^ (2 : ℕ) - 1)
```

### Shao.OQ5.P51.projectionGood

Source: `library/Shao/OQ5/P51/BoundedStudentizerGeometry.lean`, lines 95–99. exact definition including full ordinary RHS.

```lean
def projectionGood
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (y : ℝ) : Set (Fin n → Ω) :=
  {x : Fin n → Ω | (1 / 2 : ℝ) ≤ projectionEnergy n g x ∧
    |projectionW n g x| ≤ Real.sqrt y * Real.sqrt (Real.sqrt (n : ℝ)) * (4 + projectionV n g x)}
```

### Shao.OQ5.P51.studentizerGeometryScale

Source: `library/Shao/OQ5/P51/BoundedStudentizerGeometry.lean`, lines 103–104. exact definition including full ordinary RHS.

```lean
def studentizerGeometryScale (K : ℝ) : ℝ :=
  (200 : ℝ) * (1 + K + Real.sqrt K)
```

### Shao.OQ5.P51.projectionV_sq

Source: `library/Shao/OQ5/P51/BoundedStudentizerGeometry.lean`, lines 108–111. exact theorem head; proof assignment/body excluded.

```lean
theorem projectionV_sq
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (x : Fin n → Ω) :
    (projectionV n g x) ^ (2 : ℕ) = projectionEnergy n g x
```

### Shao.OQ5.P51.residualEnergyJ_eq_rows_norm_sq_div

Source: `library/Shao/OQ5/P51/BoundedStudentizerGeometry.lean`, lines 140–144. exact theorem head; proof assignment/body excluded.

```lean
theorem residualEnergyJ_eq_rows_norm_sq_div
    (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (x : Fin n → Ω) :
    residualEnergyJ n r x =
      ‖originalRows n r x‖ ^ (2 : ℕ) / ((n : ℝ) - 2) ^ (2 : ℕ)
```

### Shao.OQ5.P51.centeredSq_eq_center_sum

Source: `library/Shao/OQ5/P51/BoundedStudentizerGeometry.lean`, lines 254–261. exact theorem head; proof assignment/body excluded.

```lean
theorem centeredSq_eq_center_sum
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (x : Fin n → Ω)
    (hsym : ∀ a b : Ω, r a b = r b a) (hn : 4 ≤ n) :
    centeredSq n g r x =
      (∑ i : Fin n,
        (Shao.OQ5.P35.center (fun j : Fin n => g (x j) + residualU n r x j) i) ^ (2 : ℕ)) /
        ((n : ℝ) - 1)
```

### Shao.OQ5.P51.centered_denominator_identity

Source: `library/Shao/OQ5/P51/BoundedStudentizerGeometry.lean`, lines 281–292. exact theorem head; proof assignment/body excluded.

```lean
theorem centered_denominator_identity
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (x : Fin n → Ω)
    (hsym : ∀ a b : Ω, r a b = r b a) (hn : 4 ≤ n)
    (hV : 0 < projectionV n g x) :
    centeredDelta n g r x =
      ((projectionV n g x) ^ (2 : ℕ) - (projectionW n g x) ^ (2 : ℕ) +
          2 * (∑ i : Fin n,
            Shao.OQ5.P35.center (fun j : Fin n => g (x j)) i *
              Shao.OQ5.P35.center (residualU n r x) i) +
          (∑ i : Fin n, (Shao.OQ5.P35.center (residualU n r x) i) ^ (2 : ℕ))) /
        (((n : ℝ) - 1) * (projectionV n g x) ^ (2 : ℕ))
```

### Shao.OQ5.P51.projectionGood_bounds

Source: `library/Shao/OQ5/P51/BoundedStudentizerGeometry.lean`, lines 438–445. exact theorem head; proof assignment/body excluded.

```lean
theorem projectionGood_bounds
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (x : Fin n → Ω) (y : ℝ)
    (hn : 4 ≤ n) (hy : (1 : ℝ) ≤ y) (hGood : x ∈ projectionGood n g y) :
    0 < projectionV n g x ∧
      (1 / 2 : ℝ) ≤ projectionV n g x ∧
      (projectionW n g x) ^ (2 : ℕ) / (projectionV n g x) ^ (2 : ℕ) ≤
        (81 : ℝ) * y * Real.sqrt (n : ℝ)
```

### Shao.OQ5.P51.bounded_studentizer_geometry

Source: `library/Shao/OQ5/P51/BoundedStudentizerGeometry.lean`, lines 486–502. exact theorem head; proof assignment/body excluded.

```lean
theorem bounded_studentizer_geometry
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (x : Fin n → Ω) (K q y : ℝ)
    (hsym : ∀ a b : Ω, r a b = r b a) (hn : 4 ≤ n)
    (hK : 0 ≤ K) (hq : 0 ≤ q) (hy : (1 : ℝ) ≤ y)
    (hF : |originalUpper n r x| ≤ K * (n : ℝ) * q)
    (hRows : ‖originalRows n r x‖ ^ (2 : ℕ) ≤ K * (n : ℝ) ^ (2 : ℕ) * q)
    (hGood : x ∈ projectionGood n g y) :
    residualEnergyJ n r x ≤ 4 * K * q ∧
      |residualStatisticD n r x| / projectionV n g x ≤
        4 * K * q / Real.sqrt (n : ℝ) ∧
      |centeredDelta n g r x| ≤
        164 * y / Real.sqrt (n : ℝ) +
          16 * Real.sqrt K * Real.sqrt (q / (n : ℝ)) + 16 * K * q / (n : ℝ) ∧
      |centeredDelta n g r x| ≤
        studentizerGeometryScale K *
          (y / Real.sqrt (n : ℝ) + Real.sqrt (q / (n : ℝ)) + q / (n : ℝ))
```

### Shao.OQ5.P51.remainderWindowScale

Source: `library/Shao/OQ5/P51/BoundedRemainderPayments.lean`, lines 19–23. exact definition including full ordinary RHS.

```lean
def remainderWindowScale (K t0 : ℝ) : ℝ :=
  min (1 : ℝ)
    (min (1 / ((32 : ℝ) * (K + 1) * (t0 + 1)))
      (1 / Real.sqrt ((32 : ℝ) * (studentizerGeometryScale K + 1) *
        (1 + Real.sqrt t0 + t0))))
```

### Shao.OQ5.P51.remainderWindowScale_bounds

Source: `library/Shao/OQ5/P51/BoundedRemainderPayments.lean`, lines 61–68. exact theorem head; proof assignment/body excluded.

```lean
theorem remainderWindowScale_bounds
    (K t0 : ℝ) (hK : 0 ≤ K) (ht0 : 0 < t0) :
    0 < remainderWindowScale K t0 ∧
      remainderWindowScale K t0 ≤ 1 ∧
      remainderWindowScale K t0 ≤ 1 / ((32 : ℝ) * (K + 1) * (t0 + 1)) ∧
      remainderWindowScale K t0 ≤
        1 / Real.sqrt ((32 : ℝ) * (studentizerGeometryScale K + 1) *
          (1 + Real.sqrt t0 + t0))
```

### Shao.OQ5.P51.bounded_remainder_small_window

Source: `library/Shao/OQ5/P51/BoundedRemainderPayments.lean`, lines 87–100. exact theorem head; proof assignment/body excluded.

```lean
theorem bounded_remainder_small_window
    (n : ℕ) {Ω : Type u} (g : Ω → ℝ) (r : Ω → Ω → ℝ)
    (x : Fin n → Ω) (K t0 y : ℝ)
    (hsym : ∀ a b : Ω, r a b = r b a) (hn : 4 ≤ n)
    (hK : 0 ≤ K) (ht0 : 0 < t0) (hy : (1 : ℝ) ≤ y)
    (hyWindow : y ≤ remainderWindowScale K t0 * Real.rpow (n : ℝ) (1 / 6 : ℝ))
    (hF : |originalUpper n r x| ≤ K * (n : ℝ) * boundedPolylogMomentOrder t0 n)
    (hRows : ‖originalRows n r x‖ ^ (2 : ℕ) ≤
      K * (n : ℝ) ^ (2 : ℕ) * boundedPolylogMomentOrder t0 n)
    (hGood : x ∈ projectionGood n g y) :
    0 < projectionV n g x ∧
      y * |residualStatisticD n r x| / projectionV n g x ≤ (1 / 8 : ℝ) ∧
      y ^ (2 : ℕ) * |centeredDelta n g r x| ≤ (1 / 32 : ℝ) ∧
      |centeredDelta n g r x| ≤ (1 / 32 : ℝ)
```

### Shao.OQ5.P51.boundedProductFailure

Source: `library/Shao/OQ5/P51/BoundedPolylogConcentration.lean`, lines 17–23. exact definition including full ordinary RHS.

```lean
def boundedProductFailure
    (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (w : Ω → ℝ) (M q : ℝ) :
    Set (Fin n → Ω) :=
  ({x : Fin n → Ω | tailScale M * (n : ℝ) < squareSum n w x} ∪
    {x : Fin n → Ω | tailScale M * (n : ℝ) * q < |originalUpper n r x|}) ∪
    {x : Fin n → Ω | tailScale M * (n : ℝ) ^ (2 : ℕ) * q < ‖originalRows n r x‖ ^ (2 : ℕ)}
```

### Shao.OQ5.P51.not_mem_boundedProductFailure_iff

Source: `library/Shao/OQ5/P51/BoundedPolylogConcentration.lean`, lines 25–31. exact theorem head; proof assignment/body excluded.

```lean
theorem not_mem_boundedProductFailure_iff
    (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (w : Ω → ℝ) (M q : ℝ) (x : Fin n → Ω) :
    x ∉ boundedProductFailure n r w M q ↔
      squareSum n w x ≤ tailScale M * (n : ℝ) ∧
      |originalUpper n r x| ≤ tailScale M * (n : ℝ) * q ∧
      ‖originalRows n r x‖ ^ (2 : ℕ) ≤ tailScale M * (n : ℝ) ^ (2 : ℕ) * q
```

### Shao.OQ5.P51.eventually_boundedPolylog_product_joint_failure

Source: `library/Shao/OQ5/P51/BoundedPolylogConcentration.lean`, lines 96–115. exact theorem head; proof assignment/body excluded.

```lean
theorem eventually_boundedPolylog_product_joint_failure
    (C a t0 M : ℝ)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (ht0 : 0 < t0) (hM0 : 0 ≤ M) :
    ∀ᶠ n : ℕ in atTop,
      ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω]
        (ν : Measure Ω) [hν : IsProbabilityMeasure ν]
        (r : Ω → Ω → ℝ) (w : Ω → ℝ)
        (hr : Measurable (Function.uncurry r))
        (hr1 : Integrable (Function.uncurry r) (ν.prod ν))
        (hcR : ∀ᵐ a : Ω ∂ν, (∫ b : Ω, r a b ∂ν) = 0)
        (hcL : ∀ᵐ b : Ω ∂ν, (∫ a : Ω, r a b ∂ν) = 0)
        (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a)
        (hWR : ∀ᵐ o : Ω ∂ν, w o ≤ boundedPolylogHeight C a n)
        (hSq : Integrable (fun a : Ω => (w a) ^ (2 : ℕ)) ν)
        (hSqBound : (∫ a : Ω, (w a) ^ (2 : ℕ) ∂ν) ≤ M)
        (hEnv : ∀ᵐ z : Ω × Ω ∂ν.prod ν, |r z.1 z.2| ≤ w z.1 * w z.2)
        (hsym : ∀ a b : Ω, r a b = r b a),
        (sampleLaw n ν).real
            (boundedProductFailure n r w M (boundedPolylogMomentOrder t0 n)) ≤
          (3 : ℝ) * Real.exp (-(boundedPolylogMomentOrder t0 n))
```

### Shao.OQ5.P51.studentizerClip

Source: `library/Shao/OQ5/P51/ClippedStudentizer.lean`, lines 12–13. exact definition including full ordinary RHS.

```lean
def studentizerClip (B d : ℝ) : ℝ :=
  max (-(min B (1 / 2 : ℝ))) (min d B)
```

### Shao.OQ5.P51.studentizerClipBudget

Source: `library/Shao/OQ5/P51/ClippedStudentizer.lean`, lines 15–18. exact definition including full ordinary RHS.

```lean
def studentizerClipBudget (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (C0 rho y : ℝ) (x : Fin n → Ω) : ℝ :=
  C0 * (((1 + rho) * y) / Real.sqrt (n : ℝ) +
    residualEnergyJ n r x / ((1 + rho) * y * Real.sqrt (n : ℝ)))
```

### Shao.OQ5.P51.clippedCenteredDelta

Source: `library/Shao/OQ5/P51/ClippedStudentizer.lean`, lines 20–25. exact definition including full ordinary RHS.

```lean
def clippedCenteredDelta (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (C0 rho y : ℝ)
    (x : Fin n → Ω) : ℝ :=
  if projectionV n g x = 0 then 0 else
    studentizerClip (studentizerClipBudget n r C0 rho y x)
      (centeredDelta n g r x)
```

### Shao.OQ5.P51.clippedCenteredStatistic

Source: `library/Shao/OQ5/P51/ClippedStudentizer.lean`, lines 27–33. exact definition including full ordinary RHS.

```lean
def clippedCenteredStatistic (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (C0 rho y : ℝ)
    (x : Fin n → Ω) : ℝ :=
  if projectionV n g x = 0 then 0 else
    (projectionW n g x + residualStatisticD n r x) /
      (projectionV n g x *
        Real.sqrt (1 + clippedCenteredDelta n g r C0 rho y x))
```

### Shao.OQ5.P51.studentizerClip_contract

Source: `library/Shao/OQ5/P51/ClippedStudentizer.lean`, lines 35–39. exact theorem head; proof assignment/body excluded.

```lean
theorem studentizerClip_contract (B d : ℝ) (hB : 0 ≤ B) :
    (1 / 2 : ℝ) ≤ 1 + studentizerClip B d ∧
    |studentizerClip B d| ≤ B ∧
    |studentizerClip B d| ≤ |d| ∧
    (-(1 / 2 : ℝ) ≤ d → |d| ≤ B → studentizerClip B d = d)
```

### Shao.OQ5.P51.studentizerClipBudget_nonneg

Source: `library/Shao/OQ5/P51/ClippedStudentizer.lean`, lines 84–87. exact theorem head; proof assignment/body excluded.

```lean
theorem studentizerClipBudget_nonneg (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (C0 rho y : ℝ) (x : Fin n → Ω)
    (hC0 : 0 ≤ C0) (hrho : 0 ≤ rho) (hy : 0 ≤ y) :
    0 ≤ studentizerClipBudget n r C0 rho y x
```

### Shao.OQ5.P51.clippedCenteredDelta_bounds

Source: `library/Shao/OQ5/P51/ClippedStudentizer.lean`, lines 109–118. exact theorem head; proof assignment/body excluded.

```lean
theorem clippedCenteredDelta_bounds (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (C0 rho y : ℝ)
    (x : Fin n → Ω) (hC0 : 0 ≤ C0) (hrho : 0 ≤ rho) (hy : 0 ≤ y) :
    (1 / 2 : ℝ) ≤ 1 + clippedCenteredDelta n g r C0 rho y x ∧
    |clippedCenteredDelta n g r C0 rho y x| ≤
      studentizerClipBudget n r C0 rho y x ∧
    |clippedCenteredDelta n g r C0 rho y x| ≤ |centeredDelta n g r x| ∧
    (0 < projectionV n g x →
      0 < projectionV n g x *
        Real.sqrt (1 + clippedCenteredDelta n g r C0 rho y x))
```

### Shao.OQ5.P51.centered_studentizer_factorization

Source: `library/Shao/OQ5/P51/ClippedStudentizer.lean`, lines 149–155. exact theorem head; proof assignment/body excluded.

```lean
theorem centered_studentizer_factorization (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (x : Fin n → Ω)
    (hV : 0 < projectionV n g x)
    (hLower : -(1 / 2 : ℝ) ≤ centeredDelta n g r x) :
    0 < Real.sqrt (centeredSq n g r x) ∧
    Real.sqrt (centeredSq n g r x) =
      projectionV n g x * Real.sqrt (1 + centeredDelta n g r x)
```

### Shao.OQ5.P51.clippedCentered_comparison_on_projectionGood

Source: `library/Shao/OQ5/P51/ClippedStudentizer.lean`, lines 184–199. exact theorem head; proof assignment/body excluded.

```lean
theorem clippedCentered_comparison_on_projectionGood (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (C0 rho y : ℝ)
    (x : Fin n → Ω) (hn : 4 ≤ n) (hy : (1 : ℝ) ≤ y)
    (hGood : x ∈ projectionGood n g y)
    (hDom : |centeredDelta n g r x| ≤ studentizerClipBudget n r C0 rho y x)
    (hLower : -(1 / 2 : ℝ) ≤ centeredDelta n g r x) :
    clippedCenteredDelta n g r C0 rho y x = centeredDelta n g r x ∧
    0 < projectionV n g x *
      Real.sqrt (1 + clippedCenteredDelta n g r C0 rho y x) ∧
    0 < Real.sqrt (centeredSq n g r x) ∧
    projectionV n g x * Real.sqrt (1 + clippedCenteredDelta n g r C0 rho y x) =
      Real.sqrt (centeredSq n g r x) ∧
    clippedCenteredStatistic n g r C0 rho y x =
      (if Real.sqrt (centeredSq n g r x) = 0 then 0 else
        (projectionW n g x + residualStatisticD n r x) /
          Real.sqrt (centeredSq n g r x))
```

### Shao.OQ6.OriginalGhostGoodEvent.sampleSum

Source: `library/Shao/OQ6/OriginalGhostGoodEvent.lean`, lines 17–19. exact definition including full ordinary RHS.

```lean
def sampleSum (n : ℕ) {Ω : Type*} (g : Ω → ℝ)
    (x : Fin n → Ω) : ℝ :=
  ∑ i : Fin n, g (x i)
```

### Shao.OQ6.OriginalGhostGoodEvent.sampleEnergy

Source: `library/Shao/OQ6/OriginalGhostGoodEvent.lean`, lines 21–23. exact definition including full ordinary RHS.

```lean
def sampleEnergy (n : ℕ) {Ω : Type*} (g : Ω → ℝ)
    (x : Fin n → Ω) : ℝ :=
  ∑ i : Fin n, (g (x i)) ^ (2 : ℕ)
```

### Shao.OQ6.OriginalGoodEventProbability.normalizedGoodEvent

Source: `library/Shao/OQ6/OriginalGoodEventProbability.lean`, lines 21–27. exact definition including full ordinary RHS.

```lean
def normalizedGoodEvent
    (n : ℕ) {Ω : Type*} (g : Ω → ℝ) (y : ℝ) : Set (Fin n → Ω) := {x : Fin n → Ω |
  (1 / 2 : ℝ) ≤ Shao.OQ6.OriginalGhostGoodEvent.sampleEnergy n g x / (n : ℝ) ∧
    |Shao.OQ6.OriginalGhostGoodEvent.sampleSum n g x / Real.sqrt (n : ℝ)| ≤
      Real.sqrt y * Real.rpow (n : ℝ) ((1 : ℝ) / 4) *
        ((4 : ℝ) + Real.sqrt
          (Shao.OQ6.OriginalGhostGoodEvent.sampleEnergy n g x / (n : ℝ)))}
```

### Shao.OQ6.OriginalGoodEventProbability.original_good_event_complement_bound

Source: `library/Shao/OQ6/OriginalGoodEventProbability.lean`, lines 29–39. exact theorem head; proof assignment/body excluded.

```lean
theorem original_good_event_complement_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgmean : (∫ o : Ω, g o ∂μ) = 0)
    (hgsecond : (∫ o : Ω, (g o) ^ (2 : ℕ) ∂μ) = 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ), 0 < n → ∀ (y : ℝ), (1 : ℝ) ≤ y →
      (Shao.OQ6.CanonicalDoubleGhostRowMoments.sampleLaw n μ).real
        (normalizedGoodEvent n g y)ᶜ ≤
          Real.exp (-c * (n : ℝ)) +
            (4 : ℝ) * Real.exp (-(y * Real.sqrt (n : ℝ)) / (2 : ℝ))
```

### Shao.OQ6.OriginalGoodEventBridge.normalizedGoodEvent_eq_projectionGood

Source: `library/Shao/OQ6/OriginalGoodEventBridge.lean`, lines 10–13. exact theorem head; proof assignment/body excluded.

```lean
theorem normalizedGoodEvent_eq_projectionGood
    (n : ℕ) {Ω : Type*} (g : Ω → ℝ) (y : ℝ) :
    Shao.OQ6.OriginalGoodEventProbability.normalizedGoodEvent n g y =
      Shao.OQ5.P51.projectionGood n g y
```

