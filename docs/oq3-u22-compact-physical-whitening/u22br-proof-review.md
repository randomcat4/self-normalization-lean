# OQ3 U22br / BR151 independent complete final review

STATUS: CORRECT

Statement fidelity: CORRECT. Complete proof: CORRECT. Existing exact-source server kernel and whole-owner transitive-axiom evidence: CORRECT and reusable. No critical gap was found in the two frozen declarations. This is an auxiliary compact-open covariance-spectrum result; it does not close original OQ3 B/D or the actual sample Edgeworth/reconstruction/exterior obligations.

Reviewer: fresh independent NON-AUTHOR context `/root/oq3_u22br_full_review`, 2026-10-24 Asia/Singapore. Prescribed/configured dispatch: gpt-6.1-sol, xhigh, fresh context. No separate runtime billing/model attestation or input/cached-input/output/reasoning-subset usage counters are exposed inside this review; none are invented. I authored no part of the reviewed source and changed only this report. The report applies math-theorem and the project-specific streamlined acceptance/resource rules, without math-ultra, new agents, messages to other chats, Lean invocation, or repeated accepted checks.

## 1. Exact frozen version and coverage

| Artifact | SHA256 | Bytes / lines |
|---|---|---|
| `u22br-source.lean`, entire new module | `c54c920af77b529a30f737b22232cadafa221cee708f11d1e19d118a1ba313a4` | 5448 / 116 |
| `hundred-fifty-first-unit-scope.md` | `bd9ce6496275d4536062ea009c3df0407d545b5e34ea7917980c80bf42163a21` | 4951 / 38 |
| `u22br-actual-types.txt` | `35b813aa8cec674110e11cb0d770c55cb47b4dca6ef0a7753a67e7b287df9e67` | 1433 / 29 |
| `u22br-receipt.json` | `dd3698293f0655e299b7c8590c97feb260c3ade4f3cb3db270718f824ab65533` | 4730 / 113 |
| `u22br-Audit.lean` | `f4e9631f86268dca93e0cdc19bc154b01adf04a11450c104add49898b56006a7` | 2075 / 49 |

I read all 116 new source lines, the entire frozen scope, all 29 actual-type lines, and the entire owner-audit program. Both complete declaration texts, including both statement `let` values, are exact text matches to the pre-implementation freeze. The actual audit types retain every hypothesis and the full conclusion; neither type contains an omitted term or truncated family definition. Server source-02, current production source, server scope, server actual-types, server receipt and server Audit agree byte-for-byte by independently computed SHA256 with their local counterparts. These files use UTF-8, LF and no CR bytes; frozen bytes were not normalized or changed by this reviewer.

The complete actual module owner is `Shao.OQ3.CompactOpenDomainCovarianceSpectrum`. Its exact inventory is two public theorems, two actual owned constants, zero definitions, zero private theorems and zero generated theorems:

1. `Shao.OQ3.quadratic_form_bounds_of_det_trace`.
2. `Shao.OQ3.compact_open_domain_covariance_spectral_bounds`.

All local values were reviewed: first-proof `q = a*xi^2+2*b*xi*eta+d*eta^2`, `qa = d*xi^2-2*b*xi*eta+a*eta^2`, `z = xi^2+eta^2`; second statement and proof `nu p = mu.tilted (fun x => p.1*x+p.2*x^2)`, `D p = parabolaCovariance (nu p)`; `T = C2+C4+1`; and the local probability instance supplied by `hm.1 p hp`. There is no extra local measure, replacement matrix or uninspected generated definition.

## 2. Source-to-statement and quantifiers

The generic theorem quantifies over arbitrary real `a,b,d,delta,T,xi,eta`, retaining both frozen nonnegative diagonal hypotheses, positive `delta`, the determinant lower bound, positive `T`, and the trace upper bound. It proves both Rayleigh inequalities with exactly `delta/T` and `T`, for every real direction. It assumes a scalar determinant bound rather than either desired quadratic-form bound.

The actual theorem starts with one actual probability measure `mu`, any compact `Theta` contained in the interior of its true quadratic exponential-integrability domain, and pointwise strict positivity of the determinant of the actual tilted covariance on that same `Theta`. It returns positive `lo,hi` outside all parameter/direction quantifiers. Thus the constants are uniform in every `p in Theta` and every real `xi,eta`; no finite subfamily, cell, sample size, or bounded support is substituted. `Theta.Nonempty` is not a hidden requirement. No desired uniform spectrum appears as a premise.

The consumed domain definition, read completely at `BivariateLegendre.lean:20-22`, is exactly `{theta | Integrable (fun x => exp (theta.1*(W x).1+theta.2*(W x).2)) mu}`. For this theorem `W x=(x,x^2)`. Pinned Mathlib `Measure.tilted` at `MeasureTheory/Measure/Tilted.lean:38-43` is the actual `withDensity` measure with density `ENNReal.ofReal (exp (f x) / integral (exp o f))`; it is not an arbitrary law. Its totalized zero behavior outside integrability is not used here: true domain membership and the qualified compact-moment theorem supply genuine probability and integrability before moment identities are invoked.

The entire actual `parabolaCovariance` definition at `RegularCovariance.lean:20-24` was read. Its entries are `Var(X)`, `Cov(X,X^2)`, the identical `Cov(X,X^2)` again, and `Var(X^2)`. The off-diagonal equality used in the proof is therefore definitional, not an assumed matrix symmetry.

Original read-only `proofs/r2/repair01.md`, SHA256 `9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd`, was checked at its consumed uniform-input/small-cell passage, lines 1-78. Its lines 14-20 and 49-57 require actual uniformly elliptic tilted covariance for whitening and cell geometry. BR151 provides the stated conditional compact-open producer for this prerequisite. The same physical mean-chart inverse image from BQ150 can instantiate `Theta`; BR151 itself neither constructs that chart nor proves its determinant positivity. Song's external theorem remains attributed and is not imported as an axiom. Existing moment, weak-Cramer, beta-range, saddle and exterior-probability requirements remain in their original scope. The bounded C result is not expanded into an unbounded stability theorem.

## 3. Complete proof review

**Lines 1-17:** imports, namespace, scopes, noncomputable section and complete first signature match the freeze. No axiom, unsafe construction or proof-setting relaxation is introduced.

**Lines 18-30:** `z` is nonnegative and `det = a*d-b^2 >= delta > 0`. From `a>=0` and positive determinant the trace is strictly positive: if `a+d<=0`, then `d<=-a`, whence `a*d<=-a^2<=0`, contradicting `a*d>b^2>=0`. The `hid` identity expands exactly to `(a+d)q-det*z=(a*xi+b*eta)^2+(b*xi+d*eta)^2`. This yields `det*z <= (a+d)q`, and hence `q>=0`, using positive trace and `det*z>=0`. No division by a possibly zero matrix entry occurs.

**Lines 31-39:** the adjugate identity is likewise exact: `(a+d)qa-det*z=(d*xi-b*eta)^2+(-b*xi+a*eta)^2`. It gives `qa>=0` by the same positive-trace argument. The identity `q+qa=(a+d)z` then implies `q <= (a+d)z`. The method covers either sign of `b`, repeated eigenvalues and the zero direction without diagonalization or a totalized eigenvalue/inverse.

**Lines 40-49:** multiplying the determinant lower bound by nonnegative `z`, then using `hbase`, `htrace` and nonnegative `q`, gives `delta*z <= T*q`. Division uses the explicit `T>0`, so the lower bound is exactly `(delta/T)z <= q`. Multiplying the trace bound by nonnegative `z` gives the requested upper bound. The frozen `hd` is mathematically redundant in this proof and is retained unchanged; its unused-variable warning is not a gap and does not call for a cosmetic revision.

**Lines 51-74:** the second full signature and both statement families match the freeze. Proof `nu,D` are the same values. The qualified actual determinant smoothness theorem gives continuity on the true open domain; restriction by the exact subset hypothesis gives continuity on this `Theta`. `IsCompact.exists_forall_le' hc hdet` supplies one `delta>0` with `delta <= det(D p)` for every `p in Theta`. The actual pinned primary theorem explicitly handles the empty-set branch, so this step does not covertly assume nonemptiness.

**Lines 75-82:** the qualified compact-moment theorem is applied to this exact `mu,Theta,hcompact,hTheta`. Its orders 2 and 4 provide positive common `C2,C4`, actual integrability and actual integral bounds. `T=C2+C4+1>0` and `lo=delta/T>0`, `hi=T>0` are chosen before `p,xi,eta`. At each permitted `p`, the local probability instance is the genuine conclusion `hm.1 p hp`.

**Lines 83-95:** `sq_abs` converts the actual integrability and moment bound for `|X|^2` to those for `X^2`. `4=2*2`, `pow_mul` and `sq_abs` convert `|X|^4` to `(X^2)^2`. The measurable identity and measurable square supply actual almost-everywhere strong measurability, and `memLp_two_iff_integrable_sq` then supplies `MemLp X 2 (nu p)` and `MemLp (X^2) 2 (nu p)`. Thus both uses of the variance identity occur after their true probability and L2 hypotheses have been established. L2 also ensures the usual centered covariance has genuine integrable products; totalized undefined integrals are not doing mathematical work.

**Lines 96-106:** the two diagonal bounds are exactly `Var(X)=E(X^2)-(EX)^2 <= C2` and `Var(X^2)=E(X^4)-(EX^2)^2 <= C4`, with nonnegative subtracted squares. Consequently `D00+D11 <= T`. The extra 1 in `T` supplies positive slack without requiring nonemptiness or a positive variance lower bound at this step.

**Lines 107-113:** actual definitional symmetry and `Matrix.det_fin_two` turn the uniform actual determinant bound into `delta <= D00*D11-D01^2`, with no factor or sign error. Actual variance nonnegativity supplies the frozen diagonal hypotheses. The generic theorem then proves both bounds for every parameter and every direction, with the same constants already chosen. Lines 115-116 close the unnamed section and named namespace. Every source line and both complete proofs are covered.

## 4. Qualified dependencies and primary interfaces

Unchanged old proofs and old complete reports were reused, not re-proved or re-audited. I read the complete consumed declarations and their definition/statement let-values, and checked source hashes plus qualification/scope excerpts rather than rereading entire old proofs or reports:

| Dependency / qualification | Exact SHA256 |
|---|---|
| `OpenDomainCompactMoments.lean` | `19946ecf589a2012df33b34ad740b4ff30190bd84fe42662bdaa194c5c545093` |
| qualified complete F report, `u22f-proof-review.md` | `2d1ff5f523b7c7207d018dd4d5d4419c31d58de2302313e0adfa3cc1845a2eae` |
| `OpenDomainCovarianceAmplitude.lean` | `c6f20047e1ef46331b19619f05a72dd7e3ecf60bc1ffad7d2d952599ce5f8a1e` |
| qualified complete U/V report, `u22uv-proof-review.md` | `09fcc0c7b78f3ac2eec58e30142ea588303c2d07d15ec78978f8dae0ca31b2f2` |
| `RegularCovariance.lean` | `0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853` |

F's complete consumed type at lines 37-48 retains the exact `nu p = mu.tilted (p.1*X+p.2*X^2)` value and concludes `(forall theta in Theta, IsProbabilityMeasure (nu theta))` together with `forall k : Nat, exists C>0, forall theta in Theta, Integrable |X|^k (nu theta) and 0<=integral |X|^k and integral |X|^k<=C`. It supplies both integrability and boundedness, not merely a totalized moment number. U's entire consumed type at lines 9-15 is `ContDiffOn R infinity (fun p => (parabolaCovariance (mu.tilted (p.1*X+p.2*X^2))).det)` on precisely the same true open domain, under only actual base probability.

All three dependency sources were independently hashed locally and directly on the server and match the `source_files_sha256` map of accepted root v56 receipt `c01ea5fcae6b6db2a7b19d22ac585be4e0a014499de6ef324105be7168b579a4`, checked code `0187a42cf43bb24fcf263ff55a7515303cea40c3`. That receipt is PASS and preserves its inherited baseline; this review reuses its qualification rather than asserting a new audit of the whole baseline. F's complete report explicitly concludes complete source fidelity/proof/all-owner evidence CORRECT; U/V's complete report likewise explicitly covers Udet and its full module, with non-author fresh review and exact owner/axiom evidence. Their report bytes match the designated qualification hashes.

The following actual pinned Mathlib primary interfaces/definitions were read directly on the server; their applicable hypotheses match the proof:

- `Topology/Order/Compact.lean:236-243`, SHA256 `e3d3e63921f09661fc6178857a0a72f28c27d41f7810f66607f24ac5919c7001`: `IsCompact.exists_forall_le'` requires compactness, continuity on the set and pointwise strict lower bound, and returns a strictly larger common lower bound. Its proof explicitly treats `s=empty`.
- `Probability/Moments/Variance.lean:226-228`, SHA256 `0bcf0e00025e061b358fbde009fc35cd2e6dc28749d724513d08caa76e69415e`: `variance_eq_sub` requires probability and `MemLp X 2`; `variance_nonneg` at 204-205 is unconditional. Actual `evariance/variance` values at 58-64 were also read.
- `MeasureTheory/Function/L2Space.lean:52-54`, SHA256 `c5737e32b9b1e2a6a0d04b411244ed90d0fcf25aab0449b51865d39182eb4593`: `MemLp f 2 mu iff Integrable (fun x => f x^2) mu` requires `AEStronglyMeasurable f mu`, supplied for both actual polynomials.
- `LinearAlgebra/Matrix/Determinant/Basic.lean:809`, SHA256 `ebe677eb09cc7c2a51402ed26d918d01e547eb5cb00e822d6aadd63acc4ed3cd`: `det A=A00*A11-A01*A10`.
- `MeasureTheory/Measure/Tilted.lean:38-43`, SHA256 `355cce542b03dd9130d9511f80ae803cc11a12ba9e6a947e68402b124be2165f`, actual tilt definition; and `Probability/Moments/Covariance.lean:42-45`, SHA256 `7f261bcecb104697357f2c51f1c66154153236f3266264ba7c5dd7b8519665fd`, actual centered covariance definition.

## 5. Original server evidence and source history

Server worktree `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3` was directly observed on branch `feat/oq3-covariance-cell-family`, HEAD `0b64fc057c6aec5728f5917b98d725c6f69a564f`. Review reads used the established UTF-8 JSON `tools/server.py` transport, without credentials output, broker restart, cache writes or downloaded logs/binaries. Original run: `/root/rivermind-data/shao-lean-20261021/runs/oq3/u22br-20261023`.

I inspected the complete original build-history/audit records and both original build logs plus the original owner-audit log on that server. Their byte hashes, timings and exit codes agree with the exact local receipt:

| Gate | Exit / seconds | Original log SHA256 / bytes |
|---|---|---|
| attempt 1, source-01 | 1 / 7.759408311918378 | `53f2ebb57ec0d0a7753e656e467a7344993b2f736182314f260960b6fb5114dc` / 1169 |
| first complete kernel success, attempt 2 | 0 / 7.809217847883701 | `2288d6eb7613093821ef9331eee8636be8bb8d518c83d71486d7ac07aec7b801` / 860 |
| first whole-owner transitive-axiom audit | 0 / 5.903513817116618 | `a0a1177a85d6883ceea2f670d2e46affdeea4cdf71c4e4fd729af8732f7ab82b` / 1685 |

Source-01 is 5444 bytes / 115 lines, SHA256 `6dad004c31b899ad270b6b3c5eba8e8be9817fc5d22eb2afcfeee8a36ca8794b`. Its only substantive diagnostic is that `end Shao.OQ3` tried to close the still-open unnamed noncomputable section. A direct server snapshot diff shows exactly one added standalone `end` before the named namespace close. No declaration, hypothesis, let-value or proof changed. The complete successful source-02 is the frozen 5448-byte / 116-line final source. Failed evidence is preserved; it is not counted as success.

The first successful log preserves three warning groups: the inherited mathlib local-change/overlay warning, unused frozen `hd`, and the proposition-proof `letI` style suggestion. There is no error, sorry warning or altered mathematical premise. No warning-suppression option was introduced. Existing environment manifest SHA256 is `1fc78b60874c9d96adf399fc244c1063da454d2f33274423f8e1dacbd1249009`; it reuses the accepted read-only source/object view and adds this lane's new object. I checked the resolved actual view links and observed these object hashes, without recompiling them:

- F: `a91518aceb2c3e577f8342b4c2c159ba02654953f70d3d16c7967e963814d367`.
- U: `494d228652c426ebb25ac2916a3e5e240ae60cdb1c4e17f39dac3f95f0c392b2`.
- RegularCovariance, resolving to the inherited integration-bearing-v43 object: `deebeea0d55266fcb1c6872101634d9171132886b6b67a7b14960428e4e14038`.
- BR151 final object, resolving to this lane's `.lake/build/lib/lean/Shao/OQ3/CompactOpenDomainCovarianceSpectrum.olean`: `9aa16a5c872789caf89dbdbe41509b7ace449d81a8e44d8876aa02cf8a6b517a`.

The original build/audit records use CPU14-17, native memory 8192 MiB, jobs 4 and autoImplicit=false. Actual read-only pin inspection confirms `leanprover/lean4:v4.36.0-rc1` and both manifest and Mathlib Git HEAD `807d3836b165983210ee2ecf3cd28f239436949c`. No Lean/probe/build/audit or smoke command was run by this reviewer, locally or remotely. Existing successful gates alone were inspected and reused.

## 6. Whole actual ownership and transitive axioms

The entire 49-line Audit program was reviewed. It verifies both frozen names are theorems, enumerates every environment constant, selects its actual module owner through `getModuleIdxFor?` and the environment module table, rejects any owned axiom, and runs `Lean.collectAxioms` for every owned constant. It rejects every transitive axiom outside `propext`, `Classical.choice`, `Quot.sound`. It logs complete actual types and definition values where definitions exist; this is not only a namespace sweep or manually enumerated target audit.

The actual complete log contains exactly the two DECL/TYPE/KIND theorem records matching all 29 local actual-type lines. Each AXIOMS record is `[propext, Classical.choice, Quot.sound]`. Final counts are `U22BR_FROZEN_DEFINITIONS 0`, `U22BR_FROZEN_THEOREMS 2`, `U22BR_ALL_THEOREMS 2`, `U22BR_ALL_DECLARATIONS 2`, followed by `U22BR_AXIOM_GATE PASS`. Those observed counts exclude any hidden private/generated owned constant or definition in this exact source version. The source has no `sorry`, `admit`, new `axiom`, `unsafe`, `native_decide`, `implemented_by` or weakened proof setting. Both actual theorems therefore have complete standard-whitelist transitive-axiom coverage.

## 7. Final judgment and remaining scope

CORRECT for the exact frozen statement, all 116 source lines, every local/statement value, both actual owned theorems, and the original exact-source server evidence. No additional check or proof revision is required for this version. This is a standard algebra/compactness auxiliary contribution; no mathematical novelty or original-root completion is claimed.

The retained hypothesis is actual pointwise positive determinant on the same true-domain compact set. BR151 obtains uniform positive quadratic-form bounds from it and actual moments, rather than proving that determinant premise or finishing the full statistical argument. Physical sample Edgeworth approximation, exact reconstruction, exterior probability control and original B/D remain OPEN; bounded C scope and external-result attribution remain unchanged. At acceptance the coordinator can reuse this complete independent report and original receipts, checking exact hashes, interfaces, interactions and claimed scope without replaying accepted old proofs or gates.

All reviewer tool operations returned before final handoff; no background reviewer job, child context, source write or server check remains in flight. Only this report was written. After its byte/line/SHA256 self-check this assigned review stops; no next task or persistent continuation is implied.
