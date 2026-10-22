# OQ3 U17n frozen declaration — actual stage phase returns

Original target: R1 report.md486–489, the arbitrarily large returns of the fixed phase {n*q/h_J} to zero after the finite law and the same q/J have been fixed. Original source SHA256 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662. All source inputs remain read-only.

Module: Shao/OQ3/StagePhaseReturns.lean. Namespace Shao.OQ3; open Filter; scoped Topology; noncomputable section. Imports exactly:

```text
Shao.OQ3.SourceGaussianLatticeGap
Mathlib.Data.Int.Interval
Mathlib.Data.Finset.Card
Mathlib.Analysis.SpecificLimits.Basic
```

0 public definitions; exactly 1 complete conjunctive public target:

```lean
theorem exists_stage_phase_return_subsequence (J : ℕ) (q : ℝ) :
    ∃ m : ℕ → ℕ, StrictMono m ∧
      Tendsto (fun j : ℕ => Int.fract ((m j : ℝ) * q / dyadicMesh J))
        atTop (nhds 0)
```

Quantifiers are all J:ℕ, including J=0, and all real q, including rational q/h_J, irrational q/h_J, and q=0. The same q and J occur throughout the entire subsequence; no parameter is reselected with j. StrictMono is substantive: together with the actual Nat atTop API it gives arbitrarily large sample sizes. The limit is in ℝ for the actual fractional part, from its nonnegative side, not merely convergence in the circle quotient or small distance to either 0 or 1.

Eliminated obligation: construct a genuine strictly increasing natural subsequence on which the exact phase input required by the already accepted actual layer-series limit tends to 0. A proof yielding fractional parts near 1, signed integer times, a bounded set of sample sizes, only irrational q/h, or an assumed recurrence input does not satisfy this type.

Direct consumer: StageLayerSeriesLimit.normalizedTailCoefficient_stage_subsequence_tendsto (after the explicit actual hcont producer is available), followed by source(26) finite-stage witness selection using U17m's accepted uniform Gaussian lattice gap. This target does not itself select n_J with the coefficient lower bound or growth inequality. It does not produce hcont, unconditional19, recursive positive masses, or the final fixed-law remainder contradiction.

Dependencies: current M685line source d211fa4e676fbb76e81ff59008fb654c6b4fdc51c78a1bccd7adf4b1f5b419bd has complete independent CORRECT final790lines SHA0d83e7a9434d0a41845f5ca295b743042c96881b3dd898fc6a5f4e2dde2e7ef9, entirely read by lead before this scope was written. M commit527be7e8e6cffe4949f871279fa720d0d11349ea is immutable; publication is administrative and need not replace its bytes. Normal branch continuation does not authorize rebase, merge, retarget, or source drift.

Static prerequisite gate: candidate physical closure57Shao/2905Mathlib has all sources and existing oleans; actual public graph2764 includes Finset.Card, Int.Interval, Floor.Ring/Semiring, Archimedean.Basic and SpecificLimits.Basic. This is readiness, not an N proof or compile. U18a latest fresh check after M entire final at10:34:41UTC still has two missing Levy/Portmanteau roots and same51 missing compiled dependencies; root remains sole cache writer. N does not import missing DiophantineApproximation.Basic, Irrational, RingTheory.Int.Basic or DenseSubgroup.

The elementary finite pigeonhole principle, true floor/fract identities and Archimedean bounds are permitted. Any adapted library implementation must retain its actual source/license attribution and all mathematical gates; copying a theorem statement as an axiom or using a hidden admission is forbidden. Do not assume a fractional-part continuity statement at integers. The author route and future implementation notes remain off limits to the independent reviewer.

Before implementation: independently translate the complete actual frozen TYPE and persist that blind translation first, then compare R1/scope and actual public API implementations; mechanical/cache/hash evidence last. Before acceptance: independently review all proof steps, private bodies, generated declarations and all actual TYPE continuations; author checks use the first complete strict server build and full transitive axiom audit, with truthful partial history and no unnecessary repeat of successful source/Audit. Lead reads the entire final report before acceptance/publication or next declaration dispatch.

Execution: all Lean/heavy work only on designated server, taskset CPU14–17, one heavy process shared by lane/reviewer, native -M8192 -j4 -DautoImplicit=false; no ulimit-v, heartbeat/semantic weakening, new axiom, sorry/admit/unsafe/native_decide/implemented_by, cache writing, local Lean, or shared-owner edits. External CPU0–9/80GiB workload is protected. Reviewer owns only its new reports and authorized remote copies; no spawned agents or Lean/probes/rebuilds. All roots A/B/C/D remain OPEN; original24 exactζ, hcont/unconditional19, actual diagonal, hW and generalKL remain OPEN.
