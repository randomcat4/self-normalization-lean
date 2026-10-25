# Unit 192 static proof candidate

State: COMPLETE_STATIC_CANDIDATE_NOT_LEAN_CHECKED. All three frozen theorem
bodies are implemented. No additional global definition or theorem was added.
The sole new definition is the exact frozen `prefixAlive` value. These notes
describe the candidate; they do not supply kernel, axiom, or independent-review
qualification.

The frozen context/value/heads are those of `frozen.lean.txt`, SHA256
`199a8a03bceeb1a01e78e3a7836798e6fe46ea230108b5c2cfb128454d3423b6`.
`static-source-audit.json` records the exact candidate hash, byte/line counts,
all three head comparisons, full-prefix comparison, input binding results and
source-format/forbidden-token scan.

## Mathematical and source scope

The complete accepted mathematical route and its complete independent report
were read. The original excerpts were also read in full: supplement.tex
4778–4808, 5433–5456 and 5496–5588. The implementation targets the pointwise
classification at 5564–5587. The final frozen public head is pointwise only;
this file makes no numerical probability-bill claim or original C2/C12 closure
claim. The integrated consequence in the theory is not silently promoted to a
new formal declaration.

The reused unit191 source is the exact `actualDerivativeFamily` definition at
SHA256 `a05fc009d513978b9605af7ca384579c0a409db49cd68a7b3940685b12ac45d0`.
Its actual upper/lower branches are `halflineDerivative` and its actual interval
branch is the guarded `intervalDerivative Q`. No caller-provided derivative
oracle is introduced. Existing half-line kernel-data, actual interval regularity
and interval kernel-data contracts are used at their established interfaces.
Existing qualified theorem proofs have not been edited or rechecked.

## Whole-path reflection

The first private body defines only a local map `R` of pinned continuous paths,
whose value is minus the continuous path. Both zero endpoint proofs are given
explicitly. Continuity of the path negation and subtype projection gives its
measurability.

The two `ae_bridgeNoise_eq` sets for `B` and `-B` are intersected. On their common
full-measure set equality is proved for every bridge time simultaneously, then
lifted through continuous-map and subtype extensionality. Thus the actual
bridge random elements satisfy `R ∘ bridgeNoise B = bridgeNoise (-B)` almost
everywhere. This is stronger than a collection of one-time marginal identities.

The measurable pushforward identity gives `R_* bridgeLaw B P = bridgeLaw (-B) P`.
Full bridge-law universality, applied to `hB.neg` and `hB`, identifies the latter
law with `bridgeLaw B P`. The affine path at `(-y,-z)` with noise `R g` is
proved to be the negative of the original affine path. The interval preimage
therefore exchanges its two strict inequalities, whereas the upper preimage is
the original strict lower event. Applying the measurable pushforward formula
to these two preimages proves both frozen completion identities, for arbitrary
real `w,y,T,z` without extra positivity assumptions.

## Derived lower gradient ratio

The second private body selects the existing universal upper-ratio constant
before introducing the probability space or Brownian motion. Its lower result
uses exactly that selected constant.

The small-energy condition and `0 < u ≤ |b|`, with `u=w+y`, give `u²≤T/2` and
`u≤sqrt T`. Together with `w≥x sqrt T`, `x≥16`, and `T>0`, these prove both
strict inequalities `-w<y<w`. All reflected derivative inputs are therefore
interior. The existing actual interval spatial derivative theorem gives
reflected interval differentiability. Actual half-line kernel data, whose
reflection identities are supplied by the accepted upper/lower Brownian
formulas, give reflected upper differentiability.

Composing each reflected derivative with `s↦-s` explicitly contributes the
factor `-1`. The first private completion identities identify the resulting
functions with the original interval/lower completions. Uniqueness of derivatives
then identifies the reflected derivatives with minus the corresponding original
derivatives. The existing upper ratio at `(-y,-z,-b)` becomes the exact frozen
lower ratio. Absolute displacement, endpoint bounds and squared increments are
preserved under the reflection. No lower ratio is assumed.

## Public classification

The public proof chooses upper/lower universal witnesses before the ambient
space and uses their maximum as `C`. This retains the frozen quantifier order
and gives a positive universal constant. Its only analytic data are constructed
from the actual kernels as above. The established sign-domination theorem gives
`U≥0`, `L≥0`, and `U+L-I≥0` for the exact raw state.

The branch order and exact payments are:

1. On strict bad displacement, `-I≤max(-I,0)` pays `U+L-I` by the exact bad bill.
   The exponential term and both prior-hit terms are nonnegative. The interval
   negative part remains present.
2. If the upper prefix flag fails, the upper and interval live guards vanish,
   giving `U=I=0`; the term indexed by failure of the upper flag pays `L`.
   Failure of the lower prefix flag gives `L=I=0` and pays `U`. These flags use
   only prefixes `k≤r` and contain no terminal endpoint condition.
3. With both flags live, `r≥n`, `r≥nu sigma`, nonpositive remaining energy or
   nonpositive actual energy give three literal zero terms from source guards.
   No division or positive-wall inference is used on these zero branches.
4. On the remaining raw state define the actual next label
   `b=a(sigma ⟨r,hr⟩)`. If `b²>T/2`, the shared local small-energy guard again
   gives three literal zeros. Large-energy terms remain in the retained part of
   the existing source decomposition; this theorem only classifies separated
   terms.
5. Nonnegative prefix squares give `T≤energy a`, hence `w≥x sqrt T`. A single
   label square is bounded by actual energy, yielding `|b|≤sqrt(energy a)` and
   `|b|≤w/x`. The proof also records `|b|≤sqrt T`, which follows from the already
   active small-energy guard. This last bound gives a convenient stronger
   route to `3x sqrt T/2 < 2w-|b|` on the regular exterior branches. It adds no
   hypothesis and avoids any unstated support assumption.
6. At an interior endpoint, all three actual live guards are proved from the
   two prefix flags and strict endpoint inequalities. Actual kernel-data
   derivatives identify all three `G` values with genuine completion
   derivatives by `HasDerivAt.deriv`.
7. At an upper crossing, the lower projection is unchanged, so `L=0`. The
   established projection-control theorem is applied to both upper and
   interval domains with `eta=1`. It gives the same nonnegative excess `e`
   and coefficient `c`, with `U=-(ec)dU` and `I=-(ec)dI`. The upper ratio
   bounds `ec(dI-dU)` by its exponential multiple of `U`.
8. At a lower crossing, the upper projection is unchanged, so `U=0`. The same
   projection-control theorem at `eta=-1` gives `L=(ec)dL`, `I=(ec)dI`. The
   derived lower ratio bounds `ec(dL-dI)` by its exponential multiple of `L`.
   Weak crossing inequalities are retained throughout; an equality crossing
   has zero excess and is covered by the same formulas.
9. At neither crossing, all projections equal `b`, making all three local
   terms zero. Positive `w` excludes simultaneous upper and lower crossings.
10. If `z≤-w`, strict endpoint guards give `L=I=0`. An upper crossing would
    force `y-z≥2w-b≥2w-|b|`, contradicting regular displacement and the strict
    gap from item 5. Thus `U=0`. If `z≥w`, upper and interval guards give
    `U=I=0`; a lower crossing would force `z-y≥2w+b≥2w-|b|` and is excluded
    the same way. Equality endpoints are included in these exterior cases.

The exponential conversion uses `(x sqrt T)²≤w²` and `T>0` to prove
`x²≤w²/T`, hence `exp(-w²/T)≤exp(-x²)`. Multiplication is only by the
nonnegative excess, coefficient, or already established one-wall overshoot.
The resulting bound is precisely the frozen three-bill expression.

## Verification boundary and handoff

All author operations were static source reads/writes and deterministic local
byte/hash/structure audits. No local or server Lean/lake command, axiom command,
upload, Git operation, publication API action, or subagent dispatch occurred.
Bounded read-only native server source inspection was limited to the pinned
Mathlib derivative chain-rule source, on CPU44–47. An unavailable `rg` command
and nonexistent optional source-search directory produced ordinary read-only
inspection failures; they have no mathematical or build-result interpretation.

The requested author configuration was fresh `gpt-6.1-sol/xhigh`. The resolved
backend model/effort and input/cached-input/output/reasoning-subset counts are
not exposed and are recorded as null. No subscription usage estimate is made.

The next dependent step is the parent's exact-source server kernel and all-owned
transitive-axiom gate, followed by the required independent complete formal
source-to-statement/proof review. Any parser/elaboration issue at that first
gate is still possible because this is a static candidate. No kernel or formal
qualification is claimed here.
