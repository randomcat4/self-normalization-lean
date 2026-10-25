# Initial double completion: source-faithful formal interface plan

This is a declaration plan only. No implementation, upload, Lean/axiom command or new formal qualification is claimed. Frozen mathematical subject and complete candidate remain unchanged. Author owns only C12 source and drafts; existing Probability producers are consumed unchanged.

## Actual values to expose under Shao.C2.InitialDoubleCompletionBudget

```lean
noncomputable def initialDoubleCompletion (nu : Measure BridgeNoise) (x w : ℝ) : ℝ :=
  nu.real ((strictUpper x 0 1 w)ᶜ ∩ (strictLower x 0 1 w)ᶜ)

noncomputable def initialDoubleObservable {n : ℕ}
    (nu : Measure BridgeNoise) (x : ℝ) (a : Shao.Path n) : ℝ :=
  if Shao.energy a = 0 then 1
  else initialDoubleCompletion nu x (Shao.C1.normalizedEndpoint a)

def brownianInitialDouble {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (x : ℝ) : Set Ω :=
  {ω | (∃ t : BridgeTime, x ≤ B ⟨(t : ℝ), t.property.1⟩ ω) ∧
    (∃ t : BridgeTime, B ⟨(t : ℝ), t.property.1⟩ ω ≤ -x)}
```

These values preserve both weak walls on the same path, actual bridge law, zero-energy value1, the all-real endpoint and closed terminal cutoff. `initialDoubleCompletion` is a probability of the intersection of two complements, not `1 - intervalCompletion`, which would encode either crossing.

## Required public result shapes

1. Actual kernel continuity, pointwise nonnegativity, uniform bound8 exp(-4x²), eVariationOn over the whole line bounded by ENNReal.ofReal(10 exp(-4x²)), for each actual Brownian bridge and x>=1. Finite-interval image cancellation is an internal proof step; it does not replace a whole-line statement.
2. A single universal C>0 selected before rho,n,x,v,B and implementation spaces. For a real Borel probability rho with Integrable square, EX=0, EX²=1, n>0: normalizedLaw=map(z↦z/sqrt(n))rho; b=truncationBudget normalizedLaw n x; P=pi(rho); W=normalizedEndpoint; nu=bridgeLaw B PB; Z=initialDoubleObservable nu x. With x>=1 and b<=1/2, return genuine Integrable Z P; marginal |integral Z - PB.real(brownianInitialDouble B x)|<=C*b*standardNormalTail x; and for every v, genuine Integrable(if W<=v then Z else0) P plus the same bound against PB.real(brownianInitialDouble B x ∩ {ω | B 1 ω<=v}). No full third moment, symmetry, atomlessness, n-large condition or external BV/CDF/rare-zero payment hypothesis.

The exact Lean declarations must be frozen, including ambient imports and the above value bytes, before source implementation. This plan does not claim to be an elaborated declaration freeze. Its final statement must use native `eVariationOn`, `Measure.pi`, normalized endpoint and actual Brownian law contracts unchanged.

## Lean-facing proof architecture

- Reuse `BridgeLowerIdentification.bridge_lower_formula`, the qualified upper formula, `BrownianKilledSineIdentification.bridge_interval_eq_image`, `IntervalImageCandidateSpatial.intervalImageCandidate_eq_images` and exact `spatialTailBlock` definition. The full final kernel has two infinite tails. The m=±1 finite terms and all remaining tails must be accounted for; do not assert a formal all-integer series without paying reindexing/summability.
- Establish finite-partition variation directly on [-x,x] using geometric majorants. Uniform convergence handles interior limits; exact r_h/s_h telescoping gives both boundary values before gluing. Two exterior monotone pieces cost r each. This avoids an infinite derivative/integral interchange.
- CDF transfer can use the mathematical left-continuous BV Stieltjes lemma in the candidate, but the accepted project already provides `EndpointCDFTransfer.antitone_unit_expectation_error` for arbitrary atoms. A Jordan decomposition into scaled monotone functions would reuse that public contract and avoid introducing a new integration-by-parts library. Whichever Lean route is chosen must prove the total variation cost, preserve the closed cutoff, and not add its conclusion as an assumption.
- The original finite2 rare-zero derivation is separate: truncated second/third moments at A=sqrt(n)/(1+x), nonzero support probability, finite-support Hölder and actual iid all-zero event. None of the infinite full third moment is integrated. This can be a private helper in this C12 module; no shared Probability edits are needed.
- `bridge_endpoint_hasLaw` and ae reconstruction identify both Gaussian integrals with actual Brownian events; the marginal and terminal cutoff are different measurable sets but the same product law. No new Brownian reflection/PDE proof, no old Lean check replay.

## Source correction / exact intended scope

The supplement line “Removing Q=0 costs its probability times the supremum” is not the literal correction for Z0=1(Q>0)j(W)+1(Q=0). The correction is 1(Q=0)(1-j(0)), paid by the full rare P(Q=0) bound. This is an explicit proof-level repair under exactly the original assumptions; no original source byte is edited. The candidate also proves the terminal-closed-cutoff rare initial-double bound using the same C. Full C2 regular, postwall, rare-suffix and fixed-window assembly remain open.
