# OQ3 U22BE / unit138 — frozen exact standardized frontier transport

FROZEN before implementation. math-theorem/no math-ultra, OQ3 lead author; fresh independent full source-to-statement/proof/all owned full types/all global-local values and actual-owner recursive standard3 audit required. One public theorem/no global definitions.

Source-bound purpose: original repair uses standardized cells B=sqrt(n)*E(A-y). Actual Gaussian tube consumer must control frontier B using BA's actual frontier A cover. A continuous map alone does not transport frontiers by equality; physical normalization is a homeomorphism when n>=1 and E is a continuous linear equivalence. Prove the exact equality for arbitrary A without closed/open/measurable/atomless assumptions.

Exact planned imports: Mathlib.Analysis.SpecialFunctions.Sqrt; Mathlib.Analysis.Normed.Operator.ContinuousLinearMap; Mathlib.Topology.Homeomorph.Defs. Existing pinned mathlib objects only, no accepted OQ3 dependency/recheck. All server/resource/version rules unchanged.

Exact complete declaration:
```lean
theorem standardized_frontier_image
    (n : ℕ) (hn : 1 ≤ n) (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (y : ℝ × ℝ) (A : Set (ℝ × ℝ)) :
    frontier ((fun w : ℝ × ℝ => Real.sqrt (n : ℝ) • E (w - y)) '' A) =
      (fun w : ℝ × ℝ => Real.sqrt (n : ℝ) • E (w - y)) '' frontier A
```

All arguments universally quantified. n>=1 and the actual equivalence E are explicit; y arbitrary and A any set, including empty, nonclosed, half-open, nonmeasurable. The existing product maximum-norm topology is unchanged. E is not asserted actual covariance whitening. No probability hypothesis or conclusion, no assumed frontier identity, no sample boundary-null condition.

Proof data to be constructed locally: s=Real.sqrt(n:Real)>0; actual homeomorphism H with forward value H(w)=s•E(w-y) and inverse value H⁻¹(v)=E.symm(s⁻¹•v)+y. Left/right inverse identities use nonzero s and E's genuine inverses. Both actual maps continuous. Apply pinned Homeomorph.image_frontier to A and reverse equality. No desired identity is supplied as a premise, no new global definition or stronger unproved intermediate theorem.

OPEN: actual nonempty/empty cell Gaussian sixarc tube consumer with proved common constants, h=n^-3 and oscillation, uniform source whitening/cell geometry, anchors/disjointpartition/Edgeworth/exterior/originalB/D. Accepted fixed-lawA and boundedcompacttiltC scopes retained. No silent original physical-domain/saddle/moment/curvature/rategap/p54/WC/attribution change.

