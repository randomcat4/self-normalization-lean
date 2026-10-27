# Unit236 Stage1 candidate and analytic route

Status: **CANDIDATE_ROUTE_COMPLETE; NOT_FROZEN; NO_PROOF_IMPLEMENTATION**.
This is a declaration/route proposal, not a proof qualification or machine result.
The sole author scope was `drafts/oq56/unit236/author-stage1-01/**`.
The activation was read completely and matches SHA256
`e0ed6cec4d1e385b6ba0c34946b3d2c6aaac21f7616df0157dddb39e368d1880`, 5068 bytes.
All eight activation-bound mathematical inputs were rehashed and matched exactly.
Complete primary p54 and p51 were read. Accepted233/235 were consumed through
their complete public source heads/import/namespace/instance context and qualified
evidence; their old proof bodies and successful checks were not re-reviewed or replayed.

## Proposed mathematical scope

The single proposed public declaration is
`Shao.OQ6.OriginalExceptionalTailAbsorption.eventually_original_exceptional_payment_absorbed`.
Its complete literal head, without any proof body, is in `CANDIDATE-DECLARATION.lean`.
No auxiliary public/private theorem, definition, structure, instance or axiom is
proposed. The header file is intentionally not a compilable module.

For fixed real `t0 > 0` and `cg > 0`, select
`cWindow = min 1 (sqrt(t0)/2)` before the eventual natural index or real threshold.
The result includes `0 < cWindow`, eventual `n >= 4`, eventual nonemptiness
`1 <= cWindow*n^(1/6)`, and the stated inequality for **every** real `z` in that
closed window. The eventual cutoff can depend on `t0,cg` but cannot depend on `z`.
Every numeric coefficient, exponent and RHS is literal in the head; there is no
target-bound premise, callback, substituted tail, event probability or model witness.

The output is the deterministic relative bound

    6 exp(-t0 n^(1/3)) + 2 exp(-cg n) + 8 exp(-sqrt(n)/2)
      <= exp(-(t0/2) n^(1/3)) * Shao.standardNormalTail(z).

In particular, this is stronger than eventual relative polynomial smallness, but
no `n^(-J)` consumer, final relative-error scale or CDF is claimed here.
Only the lead may freeze or alter this proposed interface.

## Original source connection and exact limits of the connection

The whole p54 source is a pending repair supplement, not a stand-alone completed
probability theorem. Section2/F4 requires the actual concentrated good event,
strict numerator/denominator margins and the real retained clipping. F5/F6 pay
the actual complement and coding bad events; they do not permit replacing these
with a generic envelope event. The paragraph after F6 explicitly calls for
dividing the exponential payment by the actual Gaussian upper tail on a small
sixth-root window. Section3 keeps the compact source Theorem2.2 costs distinct.
Section1 replaces the false arbitrary-polynomial p-moment variation sentence
from p51 S6 by a bounded/convergent p-moment statement; unit236 does not use or
restore that false sentence.

The complete p51 was read, including S1's actual `T=(W+D)/s` and its zero branch,
S11's `exp(-cg*n)+4exp(-z*sqrt(n)/2)`, S15's separate true remainder events,
S16/S17's bounded-product concentration and small-window selection, S18's named
published DC dependency, S19's strict source budgets, S20--S25's signed exact
coding and deletion costs, S26/S27's compact/atom argument, and S28/S6's scope
as corrected by p54. Unit236 isolates only the deterministic tail-absorption
sentence; it does not complete those probabilistic interfaces or import their
desired conclusions as assumptions.

The qualified233 public conclusion has literal payment

    3 exp(-q) + exp(-cg233*n) + 4 exp(-z*sqrt(n)/2)

for the actual `H^c`, with `q=boundedPolylogMomentOrder t0 n`, `H=G_z intersect C2`,
and all original hypotheses/window/margins retained in the full copied head in
the inventory. The qualified235 conclusion has

    3 exp(-q) + exp(-cg235*n) + 4 exp(-sqrt(n)/2)

for actual retained-clip1-versus-physical `Eclip`, with its genuine `rho`,
`1+rho <= sqrt(n)` and original y=1 small-window premises retained.
Future addition of these two bounds uses `cg=min cg233 cg235`, with its
positivity proved from both independent witnesses. It does **not** identify
their witnesses merely because their source existential variable is named `cg`.
For `z>=1`, `sqrt(n)>=0` gives the first fast term at most
`4exp(-sqrt(n)/2)`, yielding exactly the unit236 literal three-term expression.
That future union/event-measurability/same-model application is outside this unit.

Unit236's `cWindow` must later be intersected with the actual233 remainder window
and any other source budgets; it does not itself discharge them. No common
countably-generated/canonical witness, eta encoding, target-event callback,
full source Theorem2.1/2.2 application, Shao--Zhou hypothesis, CDF, atom or
zero-denominator closure is supplied or assumed by the proposed scalar theorem.

## Actual definition dictionary and context

The bound uses the actual accepted `Shao.standardNormalTail`, not a fresh symbol
for an assumed Gaussian estimate. In accepted `GaussianTail.lean`, imports are
`Mathlib.Probability.Distributions.Gaussian.Real`, `Mathlib.Probability.CDF`,
`Mathlib.MeasureTheory.Integral.IntegralEqImproper`,
`Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`, and
`Mathlib.Analysis.Calculus.MeanValue`; context is `autoImplicit false`,
`open MeasureTheory Set Filter`, `open scoped Topology`, `namespace Shao`.
There are no section parameters or user-supplied instances in its public tail heads.
The exact definitions are:

```lean
noncomputable def standardNormalDensity (x : ℝ) : ℝ :=
  ProbabilityTheory.gaussianPDFReal 0 1 x

noncomputable def standardNormalTail (x : ℝ) : ℝ :=
  ((ProbabilityTheory.gaussianReal 0 1) (Set.Ioi x)).toReal
```

The exact bounded-polylog definition in namespace `Shao.OQ5.P51`,
`noncomputable section`, `open Filter`, `open scoped Topology`, is:

```lean
def boundedPolylogMomentOrder (t0 : ℝ) (n : ℕ) : ℝ :=
  t0 * Real.rpow (n : ℝ) (1 / 3 : ℝ)
```

`Real.rpow` is the pinned Mathlib real part of complex power:
`noncomputable def rpow (x y : ℝ) := ((x : ℂ) ^ (y : ℂ)).re`, with the
standard `Pow ℝ ℝ` instance `⟨rpow⟩`. All applications in the route have
nonnegative base, and identities requiring a positive base are restricted to
eventual `n>=4`. The candidate explicitly uses `Real.rpow` so no natural-power
overload can silently change `1/3` or `1/6` into a natural quotient.
`z^2` in the route/catalog is the ordinary natural square.

No ambient measurable space, measure, probability instance, finite index type,
universe parameter or model witness appears in the proposed theorem. Its only
explicit arguments are the two real numbers and their positivity proofs; its
only theorem-level let is the fully defined `cWindow`. The standard natural
atTop filter and fixed real field/order/power instances come from the imports.
There is no local/custom instance declaration or implicit result premise.

The full public Gaussian heads (basic/representation/Mills/ratio, also derivatives
and the two comparison heads) are copied losslessly from their accepted source
into `INTERFACE-INVENTORY.json`. Only basic and ratio are needed for this route.
The private `density_formula` is not used, exposed or assumed.

## Analytic route, with every quantitative loss exposed

The following are route obligations, not added hypotheses and not implemented
Lean lemmas. Their fully scoped typed forms and ordinary definitions are recorded
in the inventory. No further exported helper is proposed.

1. Write `x=(n:Real)`, `s=x^(1/3)`, `u=x^(1/6)` and `b=3*t0/8`.
   For `n>=4`, `x>=1`, `s>0`, `u>0`, `u^2=s`, `u<=s`,
   `s*x^(2/3)=x` and `s*u=sqrt(x)`. These follow from the exact pinned positive-base
   power-addition/multiplication identities, the sqrt/rpow identity and exponent
   monotonicity. The fractions are real throughout.

2. `cWindow>0`, `cWindow<=1` and `cWindow^2<=t0/4` use `t0>0`,
   `sqrt(t0)>0` and `(sqrt(t0))^2=t0`; the `min` never depends on `cg,n,z`.
   Since `u` tends to atTop, `cWindow*u>=1` eventually. This supplies an actual
   nonempty threshold interval, not a vacuous quantified window.

3. Since `x^(2/3)` and `u=x^(1/6)` tend to atTop, eventually
   `x^(2/3)>=t0/cg` and `u>=2*t0`. With positive `cg` and `s`, the exact identities
   in step1 imply `cg*x>=t0*s` and `sqrt(x)/2>=t0*s`. The eventual set is chosen
   before `z`; it depends only on the fixed scalar parameters. Thus the literal
   payment is at most `(6+2+8)*exp(-t0*s)=16*exp(-t0*s)`.

4. For a window point `1<=z<=cWindow*u`, nonnegativity permits squaring the
   upper bound, giving `z^2/2 <= (cWindow^2/2)*s <= (t0/8)*s`.
   Also `1+z<=1+u<=1+s`.

5. Apply public `Shao.standardNormalTail_ratio_bound` with `x=z,y=0`.
   Its hypotheses are exactly `0<=z` and `0<=0`. Public basic gives `Q(0)=1/2`.
   Hence `1/2 <= (4/3)*(1+z)*exp(z^2/2)*Q(z)`.
   All factors divided through are strictly positive (`1+z`, real exponential),
   and the ordinary exponential inverse identity yields

       Q(z) >= (3/8)*exp(-z^2/2)/(1+z)
            >= (3/8)*exp(-(t0/8)*s)/(1+s).

   This argument uses the reverse direction of the ratio comparison; it does not
   need the private density formula or a normalization value for the density.

6. The exact pinned limiting theorem
   `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero` with exponents `0` and `1`
   and positive coefficient `b=3*t0/8` yields

       (128/3)*(1+s)*exp(-b*s) -> 0.

   Compose both limits with `s(n)->atTop`, use `rpow_zero/rpow_one` and limit
   addition/constant multiplication. Therefore the displayed expression is
   eventually at most1. Factoring exponentials then gives

       16*exp(-t0*s)
         <= exp(-(t0/2)*s) * ((3/8)*exp(-(t0/8)*s)/(1+s))
         <= exp(-(t0/2)*s) * Q(z).

   The exponent bookkeeping is exact: `t0 - t0/2 - t0/8 = 3*t0/8`.
   Intersect this eventual set with the three scalar growth sets and `n>=4`.
   All estimates then hold for every window point with a single cutoff.

No counterexample or mathematical gap was found in this candidate route.
This is not an independent correctness vote: it remains a Stage1 author's
candidate for lead freeze and later complete proof/source review and server
kernel/transitive-axiom qualification.

## Pinned API catalog and provenance boundary

Lean/mathlib versions are the project pins `leanprover/lean4:v4.36.0-rc1` and
`807d3836b165983210ee2ecf3cd28f239436949c`; no local toolchain was invoked.
The complete local pinned `Pow/Asymptotics.lean` source used here is bound by
its existing manifest SHA256 `f736afe5ee0e392168895c13ce258c142fdc5d3b45ecb5d3dd12af9299a8ee42`
(19292 bytes). It has `public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal`,
`public section`, `open Real NNReal ENNReal Filter Set`, `open scoped Topology`,
and `section Limits; open Real Filter`. The following names are **global**,
not `Real.`-namespaced:

```lean
theorem tendsto_rpow_atTop {y : ℝ} (hy : 0 < y) :
  Tendsto (fun x : ℝ => x ^ y) atTop atTop

theorem tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (s : ℝ) (b : ℝ) (hb : 0 < b) :
  Tendsto (fun x : ℝ => x ^ s * Real.exp (-b * x)) atTop (𝓝 0)
```

The complete local pinned `Pow/Real.lean` source is bound by its existing manifest
SHA256 `f8a26d662fb7966fa5b45aef95c8d7cf0383c9921fa3e9ee1cd2c41561e9fbfd`
(50402 bytes, `pinnedGitBlobExact=true`). It has
`public meta import Mathlib.Data.Nat.NthRoot.Defs`,
`public import Mathlib.Analysis.SpecialFunctions.Pow.Complex`,
`@[expose] public section`, `noncomputable section`, `open Real Finset Set`,
`namespace Real`, and `variable {x y z : ℝ}`. Needed exact heads are:

```lean
theorem Real.rpow_natCast (x : ℝ) (n : ℕ) : x ^ (n : ℝ) = x ^ n
theorem Real.rpow_pos_of_pos {x : ℝ} (hx : 0 < x) (y : ℝ) : 0 < x ^ y
theorem Real.rpow_one (x : ℝ) : x ^ (1 : ℝ) = x
theorem Real.rpow_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : 0 ≤ x ^ y
theorem Real.rpow_add {x : ℝ} (hx : 0 < x) (y z : ℝ) :
  x ^ (y + z) = x ^ y * x ^ z
theorem Real.rpow_mul {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) :
  x ^ (y * z) = (x ^ y) ^ z
theorem Real.rpow_le_rpow_of_exponent_le {x y z : ℝ}
    (hx : 1 ≤ x) (hyz : y ≤ z) : x ^ y ≤ x ^ z
theorem Real.sqrt_eq_rpow (x : ℝ) : Real.sqrt x = x ^ (1 / (2 : ℝ))
```

The lead supplied the requested exact pinned primary nat-cast context before
sealing. `lead-api-reference-01/Mathlib__Order__Filter__AtTopBot__Archimedean.lean.md`
is SHA256 `ddc6a12d12faefee3dba7f13aaf338119f8dfaf8b21c3b5cc2dab5370a0f603b`,
1737 bytes. Its complete relevant contexts and lines41--57 were read. The bound
primary Mathlib source is SHA256
`0ba4137bb8d0837d43b1140379163e3cdf89e88675c26807c51f5e801ad31df3`,12631 bytes,
at the pinned commit above, with full provenance in `server-source-binding.json`.
It has public imports `Mathlib.Algebra.Order.Archimedean.Basic`,
`Mathlib.Order.Filter.AtTopBot.Group`, `Mathlib.Order.Filter.CountablyGenerated`,
ordinary import `Mathlib.Algebra.Order.Group.Basic`, `public section`,
`variable {α R : Type*}`, and `open Filter Set Function`; the growth theorem is
global. Exact relevant heads, with the ambient `R` made explicit here, are:

```lean
theorem tendsto_natCast_atTop_atTop {R : Type*}
    [Semiring R] [PartialOrder R] [IsOrderedRing R] [Archimedean R] :
  Tendsto ((↑) : ℕ → R) atTop atTop

theorem Filter.Eventually.natCast_atTop {R : Type*}
    [Semiring R] [PartialOrder R] [IsOrderedRing R] [Archimedean R]
    {p : R → Prop} (h : ∀ᶠ (x : R) in atTop, p x) :
  ∀ᶠ (n : ℕ) in atTop, p n
```

The initial primary nat-cast provenance lookup is therefore resolved before the
Stage1 seal; no missing pinned limiting API is reported. The author made no
server call or Lean check to resolve it. The existing `BoundedPolylogWindow.lean`
also uses `tendsto_natCast_atTop_atTop (R:=ℝ)` with the pinned rpow growth theorem.

## Action/resource/provenance ledger

Actual ACK was sent before source reads. Local read-only searches, byte hashes,
and owned proposal-artifact writes are the only executed actions. There was no
Lean executable call, proof implementation, server/network/transfer action,
Git/API/publication action, child, freeze, shared/other-owner/source modification,
or accepted old check replay. Heavy/inflight/pending external/children are all0.
The current Root is `01a17d3c-6dfd-7cc0-94ed-35d758a423a5`; current AGENTS
Coordinator5 and subsequent OQ3 resumption appendix were read, so older pause
and resource text is not treated as current authority. The author had heavy0
regardless of the lane's active phase.

Requested model/effort: `gpt-6.1-sol`/`xhigh`. Actual model/effort and all four usage
fields remain null because this context has no runtime exposure of those data.
Input, cached input, output and reasoning-subset usage are not inferred.
The final release binds the closed writer state; it does not grant proof authority.
