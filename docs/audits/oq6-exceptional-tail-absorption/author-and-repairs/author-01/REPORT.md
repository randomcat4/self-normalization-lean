# Unit236 complete author implementation

Status: **COMPLETE_IMPLEMENTATION_PENDING_INDEPENDENT_REVIEW_AND_SERVER_CHECK**.
The sole proposed theorem now has a complete proof body. This is an author
handoff, with no independent correctness vote and no kernel/axiom qualification.
No Lean command, server/network operation or old accepted proof/check replay was
performed by this author. All implementation and report writes are confined to
`drafts/oq56/unit236/author-01/**`.

## Authority and exact declaration

The same Stage1 author actually acknowledged Stage2 before writing proof bytes.
`RUNTIME-ACK.json` records the complete activation read, all9 immediate referenced
freeze/intake/Stage1-release/manifest fingerprints, and all15 still-exact Stage1
mathematical inputs. The implementation activation is SHA256
`adc98890cbea1eebcb140447461a35c169c6c35cbb9d1ec0a8eac4d135a84b02`,3310B;
the lead's freeze is SHA256
`26faefc94722d9d74a904c2a98abbc31b575eaa4a001c9c3c10d84e759aee074`,3024B.
The parent intake and changed frozen inventory fields were read before proof.

The exact production preamble, full literal theorem head and closing were joined
from the frozen files. Only the proof body was supplied by this author. There
was no assumption, binder, target, namespace, import or option change.

Public theorem:
`Shao.OQ6.OriginalExceptionalTailAbsorption.eventually_original_exceptional_payment_absorbed`.

Its explicit input arguments are only `(t0 cg : ℝ)`, `(ht0 : 0 < t0)` and
`(hcg : 0 < cg)`. The result's `cWindow=min 1 (sqrt(t0)/2)` is selected before
the eventual natural index, and the result contains its positivity, eventual
`n>=4`, eventual nonemptiness and the **entire closed** threshold interval
`1<=z<=cWindow*n^(1/6)`. A single eventual cutoff is used for all those `z`.

The bound is the literal fixed-scalar payment

    6 exp(-boundedPolylogMomentOrder t0 n)
      + 2 exp(-cg*n) + 8 exp(-sqrt(n)/2)
      <= exp(-(t0/2)*n^(1/3))*Shao.standardNormalTail z.

The used definition is exactly
`boundedPolylogMomentOrder t0 n = t0*Real.rpow (n:ℝ) (1/3:ℝ)`.
The tail is exactly the accepted definition
`((ProbabilityTheory.gaussianReal 0 1) (Set.Ioi z)).toReal`.
It is not an unconstrained function or a desired-bound callback.

## Full proof accounting

The source has one theorem and no added helper declaration. Its complete body
implements the following chain; every sign condition and uniformity dependency
is made explicit in source.

1. The first two proof-local scalars are the lead-approved mirror
   `cWindow=min (1:ℝ) (Real.sqrt t0/(2:ℝ))` and
   `b=3*t0/(8:ℝ)`, both before the eventual `n`. Positivity of `t0` gives
   `cWindow>0` and `b>0`. The two `min` projections give `cWindow<=1` and
   `cWindow<=sqrt(t0)/2`. The nonnegative product
   `(sqrt(t0)/2-cWindow)*(sqrt(t0)/2+cWindow)` and `sq_sqrt ht0.le`
   give `cWindow^2<=t0/4`. There is no extra numerical premise on `t0`.

2. The exact primary nat-cast limit, followed by the pinned global
   `tendsto_rpow_atTop`, gives divergence of `n^(1/3)`, `n^(1/6)` and
   `n^(2/3)` on natural atTop. The pinned global theorem
   `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero` is used at real powers0 and1
   with the fixed positive coefficient `b`. Composing with `n^(1/3)` and
   adding/multiplying those limits gives

       (128/3)*(1+n^(1/3))*exp(-b*n^(1/3)) -> 0.

   This implies an eventual `<=1` bound, without any threshold depending on `z`.

3. One `filter_upwards` intersects exactly five eventual conditions:
   `n>=4`, `n^(1/6)>=1/cWindow`, `n^(2/3)>=t0/cg`,
   `n^(1/6)>=2*t0`, and the residual factor `<=1`. Only now are the approved
   in-branch scalars introduced: `x=(n:ℝ)`, `s=x^(1/3)`, `u=x^(1/6)`.
   All natural-to-real inequalities use the `n>=4` result already in that branch.

4. For this fixed branch, positive-base real-power identities prove
   `u^2=s`, `u<=s`, `s*x^(2/3)=x` and `s*u=sqrt(x)`.
   The first growth condition gives `1<=cWindow*u`, so the final interval is
   nonempty. The next two growth conditions imply `t0*s<=cg*x` and
   `t0*s<=sqrt(x)/2`. Positivity of `s` and `cg` is supplied at each
   multiplication or division. Thus each faster exponential is no greater than
   `exp(-t0*s)`, and the three literal coefficients sum to16.

5. The proof then introduces an arbitrary real `z` with its exact closed-window
   hypotheses. The nonnegative product `(cWindow*u-z)*(cWindow*u+z)` justifies
   squaring its upper bound. Using `u^2=s` and `cWindow^2<=t0/4` gives
   `z^2/2<=(t0/8)*s`. The same window, `cWindow<=1` and `u<=s` give
   `1+z<=1+s`. Both denominators are strictly positive.

6. The **public** `Shao.standardNormalTail_ratio_bound z 0` and
   `Shao.standardNormalTail_basic.2.1` supply

       1/2 <= (4/3)*(1+z)*exp(z^2/2)*Q(z).

   Multiplying by positive `exp(-z^2/2)`, using the explicit exponential
   cancellation identity, and dividing through the positive `1+z` gives

       (3/8)*exp(-z^2/2)/(1+z) <= Q(z).

   Public basic positivity of `Q(z)` permits enlarging its denominator factor
   from `1+z` to `1+s`; exponential monotonicity permits the corresponding
   window exponent bound. Consequently

       (3/8)*exp(-(t0/8)*s)/(1+s) <= Q(z).

   The proof never accesses or restates the private density formula and never
   assumes an independent tail estimate.

7. The remaining exact identity is written as a proposition and proved in source:

       ((128/3)*(1+s)*exp(-b*s))
         * (exp(-(t0/2)*s)*((3/8)*exp(-(t0/8)*s)/(1+s)))
       = 16*exp(-t0*s).

   It uses only rearrangement, `(1+s)/(1+s)=1` with proved positivity, and
   `b+t0/2+t0/8=t0`. The already selected residual bound `<=1`, multiplied by
   the nonnegative second factor, proves absorption of `16*exp(-t0*s)`.
   Transitivity with the literal numerator bound and the actual Gaussian tail
   lower bound finishes the full uniform result.

This is a complete source implementation of the adopted analytic route. No
missing mathematical sublemma, tactic placeholder, deferred branch or target
result premise is left in source. Elaboration, kernel acceptance and actual
owned-constant discovery remain unperformed, as required by the author activation.

## Ordinary data, contexts and compatibility

There are exactly five proof-local ordinary `let` statements, with precisely the
types, RHS and scopes frozen by the lead: `cWindow`, `b`, `x`, `s`, `u`.
The result-type `cWindow` let is part of the unchanged frozen head. Every other
new local item is a proof of a proposition (`have`, `calc`, inequality,
equality, `Tendsto` or `Filter.Eventually`), including the inline scalar functions
inside those propositions. There is no ordinary function binding, helper
constant, instance, structure, witness, choice operation or callback added.
`COMPATIBILITY.json` records the exact ordinary-data map, source positions,
inline function RHS, imports/options/namespace and byte comparison results.

All powers `1/3`, `1/6` and `2/3` have explicit real types. Natural powers2 are
explicitly natural squares. No proof uses a power identity at zero or a
nonpositive base; all such identities occur after the established `n>=4`.
The only scalar premises remain the exact `ht0,hcg`; all rate/window facts are
proved conclusions. There is no new local or global instance declaration.

The ordinary algebraic function expressions in `Tendsto` propositions are inline
and fully displayed, consistent with the frozen inventory's explicit restriction
allowing inline expressions in Prop-valued `have` statements. They do not create
additional ordinary helpers. No interface amendment was needed during Stage2.

## Exact API provenance and accepted evidence reuse

The complete Stage1 catalog and its hashes remain bound. The needed primary
`Pow/Asymptotics.lean` heads are global `tendsto_rpow_atTop` and
`tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`; their file/context is the pinned
`807d3836b165983210ee2ecf3cd28f239436949c` source already cataloged in Stage1.
The primary `Pow/Real.lean` snapshot provides the real-power definition and
identities, including `Real.rpow_natCast`, `Real.rpow_add`, `Real.rpow_mul`,
`Real.rpow_le_rpow_of_exponent_le` and `Real.sqrt_eq_rpow`.

The previously requested exact primary nat-cast header and context arrived before
the Stage1 seal and are still exact. Its bound full source fingerprint is
`0ba4137bb8d0837d43b1140379163e3cdf89e88675c26807c51f5e801ad31df3`,12631B;
the complete relevant excerpt is SHA256
`ddc6a12d12faefee3dba7f13aaf338119f8dfaf8b21c3b5cc2dab5370a0f603b`,1737B.
There is no outstanding primary limiting-API provenance request.

The actual accepted Gaussian definitions and complete public heads were read in
Stage1 and reused as interfaces. The implementation invokes only public basic
and ratio results; no old Gaussian proof was re-reviewed or checked again.
Qualified233/235 supply source motivation through their exact public statements,
not a new proof dependency or desired-bound assumption. Their accepted proof,
original-object and axiom evidence remains unchanged and is not replayed here.

## Source fidelity and retained open scope

Complete primary p54 and p51 were read in Stage1 and remain exact. The implemented
scalar result supplies only the deterministic tail-relative absorption sentence
motivated by p54 Section2 and p51 S11/S15--S19. It neither restores the false
p-moment variation-rate claim from old p51 S6 nor changes the actual original
statistic or its zero-denominator branch.

A future event consumer still needs both independent233/235 witnesses, their
positive minimum `cg`, the actual common law/model/statistic data, union/payment
application and all original concentration/remainder windows. Those witnesses
are not identified merely because both source heads use the binder name `cg`.
The consumer must intersect `cWindow` with the actual source window and retain
all required budgets. No event probability, same-model construction, coding
epsilon limit, published Shao--Zhou application, CDF, atom, zero-denominator
probability, full OQ56/root completion or historical novelty is claimed here.

## Validation and release

Only deterministic local byte/structure checks are recorded: all required input
hashes, exact frozen preamble/head/closing, five allowed proof-local lets, source
declaration count, absence of prohibited proof escapes and UTF8/no-BOM/LF bytes.
These checks are not Lean or a substitute for independent mathematical review.
There is no native result, object, actual-type/value export or transitive-axiom
receipt for this author output yet.

The required next acceptance work is the lead's complete independent source-to-
statement/proof review and the exact-source designated-server kernel/actual-owner
type/value/transitive-axiom qualification. The author does not perform those
actions under this activation. Failed/accepted old receipts and all frozen bytes
remain preserved.

Requested model/effort: `gpt-6.1-sol`/`xhigh`, inherited from the explicitly created
fresh author context. Actual model/effort and input/cached-input/output/
reasoning-subset token usage are unexposed and remain null in the machine records.
The source and all payloads are bound by the manifest and final zero release.
After that seal, writer/heavy/inflight/pendingExternal/children/uncertain are0;
there is no continuing background action implied by this report or final reply.
