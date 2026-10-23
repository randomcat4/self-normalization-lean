# Independent final review: SourceShortTimeGrid

STATUS: CORRECT

The three frozen public declarations are proved faithfully, with no changed assumptions or uncovered mathematical gap. The existing exact-source server artifacts are sufficient for this unit. A separate numeric Lean-process exit code was not retained by the original compound shell commands; this report does not equate the observed shell exit 0 with a separately observed Lean exit 0.

Reviewer: `/root/common_short_grid_review`, fresh gpt-6.1-sol / xhigh, independent of `/root/common_marked_outside_author`. This reviewer authored no theorem, proof, assumption or shared implementation. Only this report and its companion JSON are written. Math-theorem was used; math-ultra was not used. No Lean command or prior successful gate was rerun.

## Exact binding

Module: `Shao.Probability.SourceShortTimeGrid`; remote worktree `/root/rivermind-data/shao-lean-20261021/workspaces/common-cone-derivatives-v44`; commit `bf3a6fd2cf2a8f1ddab3e1dabc289e44effcc9d5`. Remote HEAD, committed source bytes, remote current source and the 345-line local `drafts/c12-cone-derivatives/short-time-grid-work.lean` agree. The source is UTF-8/LF, with zero CR bytes. All three complete source declarations match the frozen candidate after whitespace-only normalization. The forbidden-token scan finds no `sorry`, `admit`, `axiom`, `unsafe` or `native_decide`.

| Artifact | SHA256 |
| --- | --- |
| Exact source | `39484ec8a491ed78070731e94e9ad01a1b5018df46058b693b3d801dfa67fb69` |
| Target `.olean` | `a3d3b6e102fb70964f61c340d125c57f205661166004644a589b0e3fa6a761ef` |
| Complete root declaration freeze | `86258c45bc38cfa7ad141d0c79e9073e10a6f9ed73729f628c8bc093c1e1751d` |
| Complete candidate declarations | `72bdee7fd23d370a7bdc4adc717f9f8fdb62ae0db5a783994dd9903d0fd95e34` |
| Source contract | `7049483e3c6388775e287a1179cc81233777a6219e1808aa7dbb6c024fc20048` |
| Original author receipt | `533f41dc203669c3246e55304cc7d96a2417c0ed5bddf31249612e92d163ac66` |
| Complete `short-time-grid-check06.log` | `8e447583a6c18383b13648bea2f5c3bd36781ffbce4276c18ddfafb72bbc20d1` |
| Complete actual-owned type/value/axiom log | `974f7b097e8f29a1c713dd4f590b1b2005dbb1c465ea5546536f698d863f76f5` |
| Module-owned audit JSON | `22a183639a4db4ac0e9c638faaba3e67eda175024c85f4fbddf509ffb8d15911` |
| Executed owned audit source | `e60022403d0f4afd4f4c0f62fe7bcdcde3ccf808db13c46754e1eea5303b0cef` |
| Original-execution supplement | `75837047419074e6c1aa9ba9be1dbab1f36d89ec4d27abfd338c86dae98f66f4` |

Logs and the executed audit source remain in `/root/rivermind-data/shao-lean-20261021/outputs/common-cone-derivatives-v44/`; full logs were not copied into this workspace. The supplement is `coordination/integration-v51/short-grid-original-execution-supplement.json`. All hashes above were directly checked.

The project toolchain is `leanprover/lean4:v4.36.0-rc1`, with toolchain-file SHA256 `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`; the committed toolchain bytes agree. Mathlib HEAD is `807d3836b165983210ee2ecf3cd28f239436949c`. The relevant `Integrals/Basic.lean` and `Pow/Real.lean` bytes agree with that pin (SHA256 `9f989cc31de77616c518e6b435d1af387596c6c6ab317b1c4b979c5f8f73f022` and `f8a26d662fb7966fa5b45aef95c8d7cf0383c9921fa3e9ee1cd2c41561e9fbfd`). Original commands use activation before the designated worktree, CPU10–13, the shared `root-heavy.lock`, `-M8192 -j4 -DautoImplicit=false`.

## Source-to-statement review

The read-only originals were read at main LF724–745 and supplement LF624–650/LF2655–2698. Original supplement SHA256 is `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`; main SHA256 is `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`.

`sourceShortTime_R_integrals` uses the actual function R(T,y)=1+sqrt(y)T^(-1/4), genuine Lebesgue `IntegrableOn` on (0,y²), and both normalized equalities 7/3 and (15/14)y². Integrability is established before additive integral rewrites; no totalized integral of a nonintegrable function is used as an estimate.

`sourceTruncation_remainingClock_power_integral_comparison` retains the entire raw-source law, second-moment integrability, normalization, mean, cutoff and budget premises. Its rho is the actual conditioned law; m2 and gamma are its actual integrals and variance quotient. T_i is exactly the natural-subtraction clock (n-i)m2, and `range (n+1)` supplies i≤n. For integral i, `n / 2 < i` with natural division is equivalent to the original real inequality i>n/2, for even and odd n. The lower guard is nonstrict and the upper guard is strict. Replacing the supplement's upper `max(L2*gamma²,y²)` by y² is equivalent under the lower guard: when y²≤L2*gamma² both selected sets are empty. The exponent is an unrestricted real, the interval is the genuine `Icc (L2*gamma²/2) (y²)`, and the factor is exactly 2^|a|.

`sourceTruncation_shortClock_R_sums` chooses C=10 before every source law, n, cutoff, L2 or y. It pays actual m2/y²-weighted sums of R and T*R and retains the C*y² conclusion for the latter. No grid inequality, integrability, integral budget, m2 positivity or gamma comparison is supplied as a public premise.

The source uses closed-interval shorthand while claiming disjoint intervals; the proof uses (T_i-m2,T_i], which are truly disjoint. Changing finitely many endpoints preserves Lebesgue integrals. This is an endpoint convention repair, with no altered analytic hypothesis or claimed norm/probability identification.

## Complete proof coverage

All 345 lines, all eight written theorem proofs, and the mathematical content of all three generated theorem types were reviewed.

| Source lines | Verification |
| --- | --- |
| 1–26 | Imports/options are ordinary; the power integral uses r>-1 and b>0, transfers interval integrability to `Ioc` then `Ioo`, and evaluates b^(r+1)/(r+1). The square-root scaling identity uses y>0 for the real-power laws. |
| 28–84 | Powers 0, 1, -1/4 and 3/4 are genuinely integrable at zero. On positive T, T*T^(-1/4)=T^(3/4). Linear integral rules give (7/3)y² and (15/14)y⁴; division is safe because y>0. Endpoint values at zero cannot change these Lebesgue integrals. |
| 86–118 | From m>0, gamma>0, m≤gamma² and L≥2 obtain 2m≤L*gamma² and positive lower global endpoint. `rpow` is continuous on that actual Icc, including vacuous/reversed and singleton cases. Every selected window has length m>0 and lies in the global interval. |
| 119–174 | Natural subtraction is controlled by i<j≤n, yielding T_j≤T_i-m. Half-open windows are pairwise genuinely disjoint. For t in a window, 0<t≤T_i≤2t. For a≥0, monotonicity and (2t)^a=2^a*t^a prove the pointwise estimate; for a<0, decreasing powers and 2^|a|≥1 prove it. Constant-function integration gives exactly m*T_i^a. Integrability, finite-union equality, nonnegativity and enlargement are paid before summation. No nonempty-J premise is used. |
| 176–207 | The accepted variance interface gives V=m2-mu² and V>0, hence m2>0. The accepted gamma interface gives gamma>0 and m2≤gamma² for exactly the same conditioned law. These are derived from the frozen raw premises, then supplied to the private proved grid lemma. |
| 209–236 | Only the full interval down to zero needs a>-1. With |a|≤1, 2^|a|≤2. The smaller Icc is contained in `Ioc 0 y²`; integrability and nonnegativity justify enlargement, and the upper endpoint is removed by the standard null-singleton integral equality. |
| 238–308 | The four powers 0, -1/4, 1 and 3/4 satisfy both restrictions. Nonnegative sqrt(y) preserves each inequality. Finite-sum algebra and positive-T power identities give the R and TR comparisons. The exact first theorem yields bounds 14/3≤10 and (15/7)y²≤10y². |
| 310–345 | The fixed witness 10 precedes all data. Source-law positivity/comparison payments are repeated with the same hypotheses and passed to the proved private R lemma. Namespace closure adds no assumption. |

Empty selected sets, n=0 in the private grid statement, and i=n are safe: the guards require positive selected T, so T_n=0 is excluded. If y² is below/equal to either lower integration cutoff or the selected-time cutoff, the proof uses empty/singleton sets without assuming an ordered nonempty global interval. The general comparison allows every real a, including a=-1 or smaller, since that interval is bounded away from zero. Only the four integrable powers are enlarged to zero.

The exact reused interfaces were inspected without re-reviewing accepted old proofs: `SourceFourierScale.lean` source SHA256 `5f31eb92eff8ded33b91f55a59a16de4e58cdd7a9e0514d082a2c4932f5feff0`, object `181f3e96c2cde028a900a0d7c167ca7e521e1a19b28ac97427b9530e6433ab8b`; `SourceTruncationBridge.lean` source `05321c22d1b2ea178fbc116178af345f4186bfce51011c8242b4ccfd2e0dd7d1`, object `3a23c563b69b9316b50d14f3b008ad26575d4c547602f4abd13e9c1718295c7a`. Their invoked signatures have no extra grid/integral premise.

## Every actual owner and transitive axiom coverage

The executed audit selects by `env.getModuleIdxFor?`, rather than namespace spelling or the public list. It traverses every target-owned constant, including private/generated entries, applies recursive `Lean.collectAxioms` to each, rejects anything outside propext/Classical.choice/Quot.sound, and prints the complete `info.type` under `pp.all true`. Definition values would be printed separately. The actual map contains 11 constants, all theorems, 3 public, and 0 definitions/definition values; the report does not infer these counts from source keywords.

Every complete type was read from the original 95,200-byte export, including instances, universe parameters, quantifier order, real versus natural powers/division, conditioned measures, variance, sum predicates and volume restrictions. No ellipsis occurs in these actual type records. Display aliases such as `Real.measureSpace`, `Real.instPow`, `ProbabilityTheory.cond`, `IntegrableOn` and the canonical integral restrictors preserve the mathematical objects shown in the source; no parameter, quantifier or measure was omitted. Shorter later `#check` displays are redundant and were not substituted for the complete actual records.

In the following table P=`_private.Shao.Probability.SourceShortTimeGrid.0.Shao.Probability.` and S=`Shao.Probability.`. A=propext/Classical.choice/Quot.sound; B=propext/Quot.sound. Each type hash is SHA256 of the UTF-8 `ACTUAL_TYPE` payload, excluding its label and record separator, with terminal newlines normalized to exactly one LF. Full names, byte/line counts and individual verdicts are also in the companion JSON.

| Complete owner name using the prefixes above | Full type SHA256 | Axioms | Verdict |
| --- | --- | --- | --- |
| S.sourceShortTime_R_integrals | `5a1cc8c41f8dc0c5b3abff9c5b2ca2094f82c417449df2d9939a2e74f5be60c1` | A | CORRECT |
| S.sourceTruncation_shortClock_R_sums | `afc654625fb29ca8bdf5dbf54ec5eec207bc3aeeec8cf42d780feb24f702dd8a` | A | CORRECT |
| P.shortTime_grid_power._proof_1_1 | `31ecc2a487bf41860116673209f83a3d5d42af5774902508fcf8ad7b6b534c10` | B | CORRECT |
| P.shortTime_sqrt_scale | `f3c57340f87c74a6725ceb6abdf0a2e52ea217bf023b7e37413d0971377b775d` | A | CORRECT |
| P.shortTime_power_integral | `7a4f319e1975c426e2390e0152c2f4d0b715c0fd1f34c2cf9120907100004104` | A | CORRECT |
| P.shortTime_grid_power | `4ca1e016ba03f47fce4e5c11cce7c76c0d012b23ed065602ed37b86b1df811a0` | A | CORRECT |
| P.shortTime_grid_power_full | `01af0bb4726809e3f1d8ea95fba3516654ab9a10f7d4dd470ee7e0c45ad9b489` | A | CORRECT |
| S.sourceTruncation_remainingClock_power_integral_comparison | `d876861caa23fe29f44906ae72ebf45d41959586efef2395b50e74be12848624` | A | CORRECT |
| P.shortTime_grid_R | `7649e1a17f2649937b2cb4d6cd0ac6ba76b5128887a8b93dd8d08f5d066ea22e` | A | CORRECT |
| P.shortTime_grid_power._proof_1_2 | `bbdd11451f17c42b3d4952c6da14e9e14d9955cc547fcfa738dc5a30f5759f5e` | B | CORRECT |
| P.shortTime_grid_R._simp_1_1 | `b07777507c69580dfbd3ce88a5e1ce8e61c44ee6e33a2a0a4e4b9b420fae3c96` | B | CORRECT |

The two generated `_proof_1_*` types are the natural-number contradictions implementing i<n+1 => i≤n and i<j≤n => n-j+1≤n-i. The generated `_simp_1_1` is the universe-polymorphic finite-sum identity sum(a*f_i)=a*sum(f_i) in a `NonUnitalNonAssocSemiring`; it adds no analytic or probability assumption. Each was checked individually, not accepted by a public-only sweep.

## Original execution and acceptance interpretation

The reviewer directly read only the four pertinent raw session records, at command/response lines 2362/2368 and 2382/2387 of the rollout cited by the supplement. Kernel call `call_de97152c4a284c27bc519dc805e2ea72`, chunk `bb1e20`, performs the final source correction, exact source transfer, and the targeted compiler command. Its complete stdout is byte-identical to the current complete check06 log. The log contains only the three harmless style/unused-variable warnings and the pre-existing package-view warning, with no error.

Audit call `call_4d20bbd3fe4d413184f703167f797f19`, chunk `40d996`, runs the exact audit source and then returns the tail and five SHA256 values for source, object, kernel log, full actual-owned export and audit JSON. All five match the original returned hashes and current files. The complete audit reaches the all-owned PASS result, the 11/3/11/0 coverage marker, and the three public recursive axiom outputs without an error. The actual types agree with the independently read final source, including its generated declarations.

Both outer tools and combined shells returned 0. However, `; cat ...` and `; tail ... && sha256sum ...` mask a standalone Lean failure status, so `separately_captured_Lean_exit_code` is null. The unchanged author receipt's numeric `kernel_exit_code: 0` and `axiom_audit_exit_code: 0` must be interpreted through this supplement, not cited as independently captured process exits. Acceptance here rests on the original exact-source execution, complete error-free log, emitted frozen object, successful complete owned export/PASS audit, simultaneous original hash binding, and the full independent mathematical review. This is sufficient evidence for the frozen unit; a redundant Lean rerun is unwarranted.

This certifies only the three frozen analytic time/grid statements. It does not certify the five-region assembly, a kernel/probability equality, shortkernel (iii), the probability root, C1 or C2. Those original groups remain OPEN. No novelty claim is assessed or made. Review complete; the reviewer releases its slot and has no further proof task authorized.
