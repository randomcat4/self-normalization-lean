# OQ3-U20b: literal standard Landau failure for the same final source law

Frozen v1 DECLARATION_REVIEW_PENDING; no implementation/source/probe/Audit/newbranch. Proposed module Shao.OQ3.SourceRemainderNotBigO. Exact imports Shao.OQ3.SourceFixedLawCounterexample and Mathlib.Analysis.Asymptotics.Defs. Namespace Shao.OQ3, open MeasureTheory, scoped Matrix Topology BigOperators, noncomputable section. Zero public definitions, one complete public target. U20a entire224line CORRECT final741362e81acd4e59a9f31e31f0505917d782911b95c000e0d95b89bf14a5211a read BEFORE acceptance/exactPR152 publication and this scope. Frozen152 head5a82f9e0587a93fc413f83f22713f7e6ec1d8ec5/treebd20d48ce804652b9a15e78e8e3d9568eb7e81ac;151a8991280/1480e29e264/1465d14dbdb/C144f69807c8 preserved.

Original target -> R1 verdict and literal O(n^-1/2) failure at(31), lines539-558; original report SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662. Eliminated remaining obligation -> actual same-final-law quantitative scaled gaps must imply failure of the STANDARD mathlib Asymptotics.IsBigO for the actual normalizedTailCoefficient remainder, not just informal prose about unboundedness. Direct consumer -> root final source counterexample can use this one witness and apply canonical rate/saddle/Hessian/geometric-constant adapters to its SAMEq/w/full4HasSum; no second opaque source law is needed. All prior source-law premises and quantitative StrictMono witnesses are retained AND a new standard Landau negation is proved, rather than silently replacing the stronger producer. Root owns canonical defs/implementation/integration; this target creates no public definitions and does not claim full rootA closure. All root A/B/C/D remain OPEN.

```lean
theorem exists_source_fixed_law_not_isBigO :
    ∃ (q : ℝ) (w : AtomicIndex → ℝ),
      1 < q ∧ q < 103 / 100 ∧ (∀ i, 0 < w i) ∧
      (∀ k : Fin 4,
        HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
          (constraintTarget q k)) ∧
      let P : Measure ℝ := originalMeasure sourceEll w
      let x0 : ℝ := Real.sqrt q / 4
      IsProbabilityMeasure P ∧
      (Integrable (fun x : ℝ => x) P ∧ (∫ x : ℝ, x ∂P) = 0) ∧
      (∀ᵐ x ∂P, 1 ≤ |x| ∧ |x| ≤ 4 + Real.sqrt 10) ∧
      0 < P.real (Set.Ioi 0) ∧
      (∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 → ‖jointCharacteristic P xi eta‖ < 1) ∧
      Filter.Tendsto (fun J => |resonanceXi J| + |resonanceEta J|)
        Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun J => ‖jointCharacteristic P (resonanceXi J) (resonanceEta J)‖)
        Filter.atTop (nhds (1 : ℝ)) ∧
      0 < x0 ∧ x0 < 1 / 2 ∧ 0 < saddleRate sourceEll q w ∧
      0 < correctedInverseScale sourceEll q (atomicMeasure w) ∧
      (∃ nseq : ℕ → ℕ, StrictMono nseq ∧
        Filter.Tendsto nseq Filter.atTop Filter.atTop ∧
        ∀ J : ℕ, 0 < nseq J ∧
          (J : ℝ) < Real.sqrt (nseq J : ℝ) *
            (normalizedTailCoefficient sourceEll q w (nseq J) -
              correctedInverseScale sourceEll q (atomicMeasure w))) ∧
      ¬ Asymptotics.IsBigO Filter.atTop
        (fun n : ℕ => normalizedTailCoefficient sourceEll q w n -
          correctedInverseScale sourceEll q (atomicMeasure w))
        (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹)
```

q/w are fixed once before P/x0, all support/probability/nonlattice/resonance/rate/scale properties, the increasing time witnesses AND the final negation. P/x0 are specified lets, not free law/threshold. The standard Asymptotics.IsBigO takes actual source remainder f(n)=normalizedTailCoefficient sourceEll q w n-c with c=correctedInverseScale sourceEll q(atomicMeasure w); no custom bigO, arbitrary coefficient sequence or manual failure input. Its norm-based bound is the usual absolute error. The comparison is inverse sqrt(n), exactly n^-1/2 at all positive natural n; atTop ignores n0, and the actual quantitative witnesses explicitly have nseqJ>0 before cancellation. The new negation is outside the nseq existence but still in this SAME q/w/P scope. Actual finite-product original-law probability and same source normalization are unchanged.

Proof route for independent checking, not added assumptions: destruct exists_source_fixed_law_counterexample ONCE. Preserve every actual output and the one nseq/StrictMono/Tendsto/positive/currentJgap. Assuming an actual standard IsBigO bound yields a real B and an eventual norm inequality by isBigO_iff (or isBigO_iff'). Pull this event back along actual nseq Tendsto. Choose natural J in that eventual tail and with B<J. Since nseqJ>0, sqrt(nseqJ)>0; use f<=absf and the norm bound, multiply by positive sqrt, then legally cancel its nonzero inverse to get sqrt(nseqJ)*f(nseqJ)<=B. Contradict the SAME witness J<sqrt(nseqJ)*f(nseqJ) and B<J. Do not assume f or C_n monotone, uniform error, raw q/n positivity without proof, or change law for the negation. A private generic contradiction helper is allowed only if main actually consumes it on this exact source witness and all actual private/generated TYPEs and transitive axioms are audited.

Pinned actual API source reads: Asymptotics/Defs.lean96 isBigO_iff,100 isBigO_iff',139 IsBigO.bound. True inverse sqrt nonnegativity and nonzero are established before cancellation. Full prospective exact2import static readiness completed2026-10-22T19:57:14.106048Z:67Shao2973Mathlib physical/public2712internal+189externalstops=2901, source/olean gaps0. Canonical67 relative-path sorted compact mapb89b6ad627672a072361be255f994133e4607630d3ec6bd9ca8e59ca2e811a04; candidateJSON542ac8b1f41a3a1ac5d0e72d2c5a5121d4349c39023b155272f75a0a33a2336e. Metadata-only66oldsource entries matchrootv37 receipt0ca757d0c30a8a0d7239de0631e018ae79aacdb8bee1faa836df7ce5cf8a8ae8, plus actual fully independently acceptedPR152 sourceSHA3d402b62362c4394eb50a6ade2f512ab90c3d19982ce19ca143c706257c5c571. This does NOT claim all67arealreadyinmain. Needed Asymptotics.Defs/AtTopBot.Basic/Tendsto/Real.Sqrt/actualSourceFixedLawCounterexample are publicly reachable. This is readiness only, not Lean or independent mathematical acceptance; reviewer must reconstruct from frozenTYPE, real R1 and actual accepted public producer, not author notes/candidate/scanner/receipt.

No implementation/source/probe/Audit/newbranch until the entire independent declaration final is read and CORRECT. Current frozen152 branch/head clean. After approval prefer a newer root-approved accepted checkpoint containing the actual67formal sources if handed off; otherwise normal NEW owned branch from exact fully independently accepted152head5a82f9e0 preserves actual source dependency without merge/reset/rebase/fetch or copying unrelated source. Its leaf PR may initially target the preserved152feature branch if152 notyetinmain; root alone later integrates/retargets. All oldfrozenheads preserved. Root BivariateLegendre proposal is not a production dependency until accepted implementation/checkpoint supplied; no competingcanonicaldefs. Server-only CPU14-17, oneheavy lane, native-M8192-j4-DautoImplicit=false, no proofsettingsweaken or successfulchecksrepeated/cachewrites; externalCPU0-9/80GiB untouched. All original roots remain OPEN.
