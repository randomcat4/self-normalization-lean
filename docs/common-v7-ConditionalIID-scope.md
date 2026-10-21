# Frozen finite conditional iid interface

Status: both signatures, names, and the conjunction output were frozen by the
root coordinator before implementation. The server-checked implementation is
`drafts/c12/ConditionalIID.lean`; its check and axiom receipt is
`drafts/c12/ConditionalIID-review-receipt.md`. No conditional-independence axiom
or additional assumption was introduced. Independent review remains separate.

## Source contract

Read-only source `current/c12/supplement.tex`, lines 170-179: fix a deterministic
deleted set `I` with positive event probability, retain its complement in the
original increasing order, and condition on the exact event `{J = I}`. The
retained coordinates are iid with the common original law conditioned on
`abs z <= 1/x`. The source already has `I.card < n`, so a coordinate remains.
Supplement SHA256:
`b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`.

Read-only `current/c12/main.tex`, label `h:eq:truncation`, lines 424-430:
the event is that every coordinate satisfies `abs xi_j <= h_x`. The conditional
law later named `P_x^*` is the original measure conditioned on this one fixed
event. The event is kept fixed as the later comparison threshold varies.
Main source SHA256:
`beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`.

The measure used throughout must be the existing normalized restriction
`ProbabilityTheory.cond mu A = (mu A)^(-1) * mu.restrict A` (measure scaling).
It must not be a new conditional-iid predicate or an assumed probability kernel.

## Fixed Mathlib evidence

Inspected source at pinned Mathlib commit
`807d3836b165983210ee2ecf3cd28f239436949c` on the designated server, using five
bounded batched source-query connections, with no builds or downloads. Relevant
existing `.olean` files for ConditionalProbability and Constructions/Pi were
present; Independence.Basic is already a dependency of the checked library.

- `Probability/ConditionalProbability.lean`: `ProbabilityTheory.cond` is
  exactly inverse event mass times the restricted measure.
- In the same file, `cond_isProbabilityMeasure` turns the
  normalized restriction of a finite measure on a nonzero event into a
  probability measure. `cond_apply` and `ae_cond_mem`
  provide the actual conditional event formula and conditional support.
- `Probability/Independence/Basic.lean:1043`: `cond_iInter` factors conditional
  intersections of coordinate events. The proof explicitly uses the normalized
  restriction, original independence, and finite products of ENNReal masses.
- `Independence/Basic.lean:1083`: `iIndepFun.cond` already proves conditional
  independence. Its arguments are measurable `Y_i`, independence of the
  coordinate pairs `(X_i,Y_i)`, nonzero probabilities of every `Y_i in B_i`,
  and measurability of the `B_i`. Its conclusion is `iIndepFun X` under the
  normalized restriction to the intersection of those coordinate events.
- `Independence/Basic.lean:669`: `iIndepFun.comp` preserves independence under
  separate measurable coordinate transformations. Apply it to `z |-> (z,z)`
  to supply the independent pairs required above; no new pair-independence
  hypothesis is needed.
- `Independence/Basic.lean:847`: `iIndepFun.map_fun_eq_pi_map` gives the actual
  finite joint pushforward measure from independent measurable coordinates.
  The converse is present at line 866.
- `MeasureTheory/Measure/Restrict.lean:332`: `Measure.restrict_map` identifies
  a restriction of a pushforward with the pushforward of a preimage restriction.
- `MeasureTheory/Measure/Map.lean:142`: `Measure.map_smul` transports the
  normalization factor. Together these prove the elementary conditional-law
  transport identity, without needing a new general conditional-probability
  framework.
- `MeasureTheory/Constructions/Pi.lean:417`: `Measure.restrict_pi_pi` restricts
  a finite product measure to a coordinate rectangle coordinatewise.
  `Measure.pi_eq` at line 279 and `Measure.pi_pi` at line 291 give the optional
  canonical-product proof route. This route is valid but not necessary because
  `iIndepFun.cond` and `cond_iInter` already close the required condition step.

## Frozen generic public theorem

Use one homogeneous measurable codomain `alpha`, arbitrary finite index type
`iota`, and no topological/standard-Borel assumption. This covers the real
finite-path application and keeps the generic conditioning statement minimal.
The finite type may be empty.

```lean
theorem indep_cond_joint_map_eq_pi
    {iota Omega alpha : Type*} [Fintype iota]
    [MeasurableSpace Omega] [MeasurableSpace alpha]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : iota -> Omega -> alpha}
    (hX : forall i, Measurable (X i))
    (hIndep : iIndepFun X mu)
    (B : iota -> Set alpha)
    (hB : forall i, MeasurableSet (B i))
    (hA : mu (Set.iInter (fun i => X i ⁻¹' B i)) ≠ 0) :
    Measure.map (fun omega i => X i omega)
        (ProbabilityTheory.cond mu (Set.iInter (fun i => X i ⁻¹' B i))) =
      Measure.pi (fun i =>
        ProbabilityTheory.cond (Measure.map (X i) mu) (B i))
```

Namespace proposal: `Shao.Probability`. The actual Lean source can use Greek
identifiers and `⋂ i, ...`; the displayed statement fixes all quantifiers and
assumptions. Since `mu` is a probability measure, `hA` is exactly positive
joint probability; no separate finite-mass or denominator-finiteness premise
is needed. Each single-coordinate marginal on the right is the actual original
pushforward of `X_i`, then conditioned on `B_i`.

The conditional measure's probability instance is derived, not assumed.
For each index `i`, the inclusion of the joint event in `X_i in B_i` implies
its event has nonzero original probability. Conditional marginal probability
instances then follow from `cond_isProbabilityMeasure`. With an empty index
type the event is universal and the conclusion is the law on the singleton
empty product, with no nonempty-index premise.

## Minimal proof route

1. Set `A = intersection_i {X_i in B_i}`. Derive `IsProbabilityMeasure (cond mu A)`
   and all nonzero coordinate conditioning probabilities from `hA`.
2. Use `hIndep.comp (fun _ z => (z,z))` with the measurable diagonal to obtain
   independence of the coordinate pairs.
3. Apply the existing `iIndepFun.cond` theorem. This proves independence of all
   `X_i` under the actual measure `cond mu A`.
4. Use `cond_iInter` with a singleton index set to prove, on each measurable
   test set, that the law of `X_i` under `cond mu A` equals its law conditioned
   only on `X_i in B_i`.
5. Rewrite the latter as `cond (mu.map (X_i)) (B_i)` using `restrict_map`,
   `map_smul`, and the ordinary pushforward event-mass formula. This elementary
   transport lemma can be private; no extra public auxiliary is required.
6. Apply `iIndepFun.map_fun_eq_pi_map` under `cond mu A` and rewrite its marginal
   measures using step 5. No iid hypothesis is used in this generic theorem.

If Lean elaboration makes the direct conditioning API cumbersome, the same
frozen conclusion has a second route: push the original independent joint law
to the product space; transport conditioning through that measurable joint map;
use `restrict_pi_pi`; check normalized rectangle masses with `pi_eq`. Changing
proof route does not permit adding hypotheses or assuming conditional independence.

## Frozen fixed retained-set iid corollary

For the paper use `s : Finset (Fin n)` as the fixed retained set, with
`hs : 0 < s.card`, and one measurable good set `B : Set R`. Set, by a local
abbreviation rather than a new global event definition,

```text
A_s = intersection_(i : Fin n) X_i^(-1)(if i in s then B else B.compl).
mu_s = ProbabilityTheory.cond mu A_s.
nu_B = ProbabilityTheory.cond nu B.
Y_r = X_(Shao.retainedIndex s r),  r : Fin s.card.
```

Frozen corollary signature:

```lean
theorem iid_retained_cond_coordinate_event
    {n : Nat} {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {nu : Measure R}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {X : Fin n -> Omega -> R}
    (hX : forall i, Measurable (X i)) (hIndep : iIndepFun X mu)
    (hLaw : forall i, IdentDistrib (X i) (id : R -> R) mu nu)
    (s : Finset (Fin n)) (hs : 0 < s.card)
    (B : Set R) (hB : MeasurableSet B)
    (hA : mu (Set.iInter (fun i =>
      X i ⁻¹' (if i ∈ s then B else Bᶜ))) ≠ 0) :
    nu B ≠ 0 ∧
    iIndepFun (fun r : Fin s.card => X (Shao.retainedIndex s r))
      (ProbabilityTheory.cond mu (Set.iInter (fun i =>
        X i ⁻¹' (if i ∈ s then B else Bᶜ)))) ∧
    forall r : Fin s.card,
      IdentDistrib (X (Shao.retainedIndex s r)) (id : R -> R)
        (ProbabilityTheory.cond mu (Set.iInter (fun i =>
          X i ⁻¹' (if i ∈ s then B else Bᶜ))))
        (ProbabilityTheory.cond nu B)
```

Here `R` in the displayed pseudocode means Lean `ℝ`; all other notation is the
ordinary Lean signature. The `nu B ≠ 0` output is derived from any retained
coordinate, its common original law, and `hA`; it is not a new premise.
The conditional probability instances follow from this output and `hA`.
Independence of `Y` follows from conditional independence of `X` and
`retainedIndex s`'s injectivity using existing `iIndepFun.precomp`.
Its coordinate laws follow from conditional marginal laws and
`retainedIndex_mem`, which picks the `B` branch of the mixed event.

The already checked `iid_samplePath_map_eq_pi` then immediately gives the
retained path's actual product law `pi (fun _ : Fin s.card => nu_B)`, because
`samplePath Y omega` is definitionally
`retainedPath (samplePath X omega) s`. No third public theorem is needed unless
the coordinator wants that equality as the sole retained-corollary output.

## Source specializations and boundaries

- Deletion source: take `B = {z | abs z <= 1/x}` and `s = I.compl`. The finite
  filter `J(omega) = {i | 1/x < abs (X_i omega)}` equals `I` exactly when every
  retained coordinate lies in `B` and every deleted coordinate lies in `B.compl`.
  This is an elementary event equality to prove when connecting the source;
  no independent law is asserted for a random or sample-chosen index set.
- Whole-sample bounded source: set every `B_i = {z | abs z <= h_x}`. The generic
  theorem covers the event `N_x` directly, including an empty family.
- If the family is empty, positive joint event probability does not imply that
  `nu B > 0`: there is no coordinate from which to infer this. Thus the generic
  joint theorem allows empty families, while the retained-iid corollary uses
  the source's already-present nonempty retained set when promising a proper
  conditional common law. This distinction must not be hidden in typeclasses.
- Threshold membership is weak (`<=`); deleted membership is its exact
  complement (`>`). There is no assumption that boundary atoms vanish.
- No centering, moments, positive energy, positivity of observations, or
  atomlessness is required. No logarithmic or tail estimates are in scope.
- The general theorem conditions on all fixed coordinate events, and the
  retained corollary on one fixed mixed event. It does not state that retaining
  threshold-selected observations is unconditionally iid.

## Freeze and verification gate

The coordinator accepted the generic arbitrary-codomain finite-index signature,
the retained corollary's conjunction output, and the theorem names before any
Lean implementation. Existing definitions and sources remain unchanged.

The assigned new probability module has passed its targeted server check and
all-declaration transitive axiom audit; see its receipt for the frozen SHA256.
A fresh independent source-to-statement/proof review is required for acceptance.
No local Lean and no cache writes were performed by this author.
