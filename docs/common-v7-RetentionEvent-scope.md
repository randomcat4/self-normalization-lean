# Frozen retention-set event bridge

Status: the root coordinator froze this exact one-definition/four-theorem API
at proposal SHA256
`b2fd6fcfdd8d28041463973fce753975e2d6483461953c8d04fff3107a26da59`
before implementation. The server-checked source is `RetentionEvent.lean` in
this directory; see `RetentionEvent-review-receipt.md`. Independent review is
separate. Frozen ConditionalIID and OrderedSelection sources are unchanged.

## Source meaning

Read-only `current/c12/supplement.tex`, lines 143-145 and 170-179, defines the
paper's `J` as the deleted/bad set `abs xi_i > 1/x`, then fixes one value `I`
with positive probability and retains its complement in increasing order.
Supplement SHA256:
`b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`.

The proposed `retentionSet` names the good/retained set, as requested for this
bridge. It must not silently be identified with the paper's deleted `J`.
For good set `B`, the paper's bad set is `retentionSet X B.compl`; its fixed
value `I` corresponds exactly to `retentionSet X B = I.compl`. The complement
identity below makes this translation explicit.

## Definitions and deterministic statements

Namespace: `Shao.Probability`. The selector and its set identities have no
measurability or probability assumptions. Length `n` may be zero.

```lean
noncomputable def retentionSet {n : Nat} {Omega : Type*}
    (X : Fin n -> Omega -> ℝ) (B : Set ℝ) (omega : Omega) : Finset (Fin n) :=
  by
    classical
    exact Finset.univ.filter (fun i => X i omega ∈ B)

theorem retentionSet_eq_event {n : Nat} {Omega : Type*}
    (X : Fin n -> Omega -> ℝ) (B : Set ℝ) (s : Finset (Fin n)) :
    {omega | retentionSet X B omega = s} =
      Set.iInter (fun i => X i ⁻¹' (if i ∈ s then B else Bᶜ))

theorem retentionSet_compl {n : Nat} {Omega : Type*}
    (X : Fin n -> Omega -> ℝ) (B : Set ℝ) (omega : Omega) :
    retentionSet X Bᶜ omega = (retentionSet X B omega)ᶜ
```

The complement is finite complement in all of `Fin n`. The selector's
membership is exactly `X_i omega in B`; its enumeration is not changed or
redefined. Existing `Shao.retainedIndex s` remains the increasing enumeration.
A membership equivalence can be private because the public task only needs
the actual fiber event identity and the complement bridge.

The event equality is pathwise equality of sets of outcomes, rather than
almost-everywhere equality, equality of probabilities, or an event inclusion.
Its proof is finite-set extensionality, splitting fixed membership `i in s`.
The complement equality is also pointwise finite-set extensionality.

## Measurability statement

```lean
theorem measurableSet_retentionSet_eq
    {n : Nat} {Omega : Type*} [MeasurableSpace Omega]
    {X : Fin n -> Omega -> ℝ} (hX : forall i, Measurable (X i))
    (B : Set ℝ) (hB : MeasurableSet B) (s : Finset (Fin n)) :
    MeasurableSet {omega | retentionSet X B omega = s}
```

Proof: rewrite by `retentionSet_eq_event`, apply measurability of a finite
intersection, and use the coordinate preimages of either `B` or `B.compl`.
No measurable-space structure on `Finset (Fin n)` is needed: this is precisely
the source's fixed fiber event, not an unnecessary finite-set-valued random
variable API.

## Fixed-fiber conditional iid statement

```lean
theorem iid_retained_cond_retentionSet_eq
    {n : Nat} {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {X : Fin n -> Omega -> ℝ}
    (hX : forall i, Measurable (X i)) (hIndep : iIndepFun X mu)
    (hLaw : forall i, IdentDistrib (X i) (id : ℝ -> ℝ) mu nu)
    (s : Finset (Fin n)) (hs : 0 < s.card)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hA : mu {omega | retentionSet X B omega = s} ≠ 0) :
    nu B ≠ 0 ∧
    iIndepFun (fun r : Fin s.card => X (Shao.retainedIndex s r))
      (ProbabilityTheory.cond mu {omega | retentionSet X B omega = s}) ∧
    forall r : Fin s.card,
      IdentDistrib (X (Shao.retainedIndex s r)) (id : ℝ -> ℝ)
        (ProbabilityTheory.cond mu {omega | retentionSet X B omega = s})
        (ProbabilityTheory.cond nu B)
```

The sole probability proof is to rewrite the actual fiber by the deterministic
event equality and apply the already frozen and checked
`iid_retained_cond_coordinate_event`. There is no new conditional-independence
assumption or re-proof of the probability foundations.

The source conditional measure is the genuine normalized restriction
`cond mu {omega | retentionSet X B omega = s}`. Its probability instance follows
from the positive fiber mass. The output `nu B != 0` gives the proper
one-coordinate conditional probability law using `cond_isProbabilityMeasure`.
The conjunction preserves both independence and all common coordinate laws.
The existing finite iid product-law theorem may then be applied to the
increasing retained path without adding another public theorem here.

## Boundaries and exclusions

- All deterministic identities and fiber measurability allow `n=0`; the
  selector and its only possible fixed value are empty, so that fiber is the
  universal event. The conditional iid corollary separately requires a
  nonempty retained set, because it also derives `nu B != 0` from an actual
  retained coordinate.
- `B` is any measurable real set. At the source threshold take
  `B = {z | abs z <= 1/x}`. Its complement is exactly
  `{z | 1/x < abs z}`, including all boundary atoms on the retained side.
- For a fixed deleted source set `I`, substitute `s=I.compl`. The complement
  identity converts the source's exact deleted-set event into this exact
  retained-set fiber. No sample-dependent permutation or random-length iid
  statement is asserted.
- No centering, moment, positive-energy, atomlessness, or positive-length
  premise is added to the selector/event identities. The corollary has only
  the fixed source-relevant `s.card > 0` restriction already shown above.
- The module does not prove a binomial law for the number deleted, conditional
  moment estimates, or the later tail bound.

## Ownership and acceptance

Implementation file: `drafts/c12/RetentionEvent.lean`, remote
`Shao/Probability/RetentionEvent.lean`, importing the existing ConditionalIID
module. Only this new module and its own scope/receipt may be edited.
No root imports, audit scripts, pins, shared caches, or other authors' sources
are changed. The targeted server-only Lean check and transitive axiom audit
including generated/private declarations have passed at the recorded frozen
source SHA256. A fresh independent review is still required for acceptance.
