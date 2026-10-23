# U22by / unit158 independent complete final review

STATUS: CORRECT
SOURCE_TO_STATEMENT: CORRECT_IN_FROZEN_SCOPE
ALL_ACTUAL_OWNERS: COVERED_3_OF_3
PRECISE_GAPS: NONE_IN_FROZEN_BRIDGE_SCOPE
ROOT_CLOSURE: NOT_CLAIMED

Date: 2026-10-24, Asia/Singapore. Reviewer: fresh non-author context `/root/oq3_u22by_full_review`, prescribed gpt-6.1-sol / xhigh, with no model switch or child context. I applied math-theorem, not math-ultra. I did not author or modify the implementation, freeze, receipt, status, registry, shared code, or old evidence. This report is my only write. Token-category counters are not exposed to this context; no usage counts or subscription allocation are invented.

## 1. Verdict and exact scope

Both public theorems are mathematically correct with their complete frozen assumptions and actual elaborated types. I read all 110 new source lines, both complete authored proofs, all 50 lines of the actual-type export, the complete freeze, audit program, receipt, environment manifest and build history, and the complete saved build/audit outputs. The actual third owner outside `Shao.OQ3` is included explicitly below. All statement and proof-local let values were inspected.

The result is a conditional bridge from a genuine local identity for the actual global EReal Legendre rate and a positive normal/tangential growth estimate to a rate floor on an explicitly smaller physical window. The second theorem transfers that floor to a real-valued representation J already identified with the same actual rate on the old cap window. It does not construct these premises from the probability law, select or identify the original producer's L/e/Lambda, or transport the original Laplace/Gaussian/anchor packet to the new window.

There is no critical proof, quantifier, finite-value, metric, boundary, ownership, or exact-source evidence gap within this frozen scope. Acceptance of this bridge must retain the remaining producer and root obligations in section 9.

## 2. Exact bytes and evidence binding

Local root: `C:/game/shao lean/`. Source module: `Shao.OQ3.PhysicalWindowRateFloor`. Server run: `/root/rivermind-data/shao-lean-20261021/runs/oq3/u22by-20261023`. Server worktree: `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`.

| Artifact | Bytes / lines | SHA256 |
| --- | --- | --- |
| `drafts/oq3/u22by-source.lean` | 5162 / 110 | `7e76ddd24536a713098341d2829077ff312296fac37da25bca41a7a573d98c7e` |
| `drafts/oq3/hundred-fifty-eighth-unit-scope.md` | 6003 / 56 | `606afda3e220f5331c1d3546aeeb13c80095b587190c656743218be17cbc6e83` |
| `drafts/oq3/u22by-actual-types.txt` | 2946 / 50 | `1a815c4558fa629bddb3931a3c10a0b1c5ba09c5bb6eb862e8ad635672331e58` |
| `drafts/oq3/u22by-receipt.json` | 3814 | `8e38643d98d17e162a276c589435cb9452b4676a724fe314a94f7dc6e09e6454` |
| `drafts/oq3/u22by-Audit.lean` | 2080 | `36ae6dfef6d53390b584eaf473116953267b9cf4410e1793d1c43a4ea06a67b9` |
| `drafts/oq3/u22by-audit-environment.json` | 1091 | `a0f3ffa687675076b5981b6d9930b1d68e1982a16735d3b44a0278124d177ed4` |
| `drafts/oq3/u22by-build-history.json` | 959 | `bc009f0dba070ade5193dee45cf5e38ede5fcfd8ea854359ae0a267b45126c22` |
| Server `audit-record.json` | 498 | `8423ae0b61b834d292bebd04befd2a55030f1309a619e6e86f9b67d45bbb732e` |
| Server `build-01.log` | 133 | `fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626` |
| Server `audit.log` | 3198 | `e70d86a59908e4a11c5ea818fc0188a9c0d4a141ecb503075eee5159a1fd3155` |

I independently read and hashed the saved server artifacts. Server `source-01.lean`, `scope.md`, `actual-types.txt`, `receipt.json`, `Audit.lean`, `audit-environment.json` and `build-history.json` match their local counterparts above exactly. The current server implementation source also matches the frozen source hash. The source has 110 LF bytes, zero CR bytes and no UTF-8 BOM; no normalization or cosmetic edit was made. The entire server audit DECL/TYPE/AXIOMS/KIND block sequence is byte-for-byte equal to the 2946-byte actual-type export, so the export does not omit a declaration or a statement tail.

The receipt records branch `feat/oq3-weighted-grid-reconstruction` and historical parent `fd718003cddb5ac4458073966048c4a5bc7e25e1`. These are receipt provenance, not a claim that no later branch activity exists. The receipt remains `AUTHOR_PASS_PENDING_FRESH_COMPLETE_REVIEW`; this new report supplies the independent review without rewriting that historical receipt.

## 3. Complete statement and actual-owner coverage

The actual ownership enumeration contains exactly two public source theorems, one generated theorem, no private theorems and no definitions. The count 3 is derived from the module-owner audit and the three exported declarations, rather than a namespace-prefix scan.

| Actual owner | Complete coverage |
| --- | --- |
| `Shao.OQ3.actual_parabola_rate_floor_of_boundary_lower_bound` | Source 8-65, complete frozen and actual type, all assumptions, both statement lets, full proof and every local let |
| `Shao.OQ3.actual_parabola_analytic_rate_floor_of_boundary_lower_bound` | Source 67-107, complete frozen and actual type, all assumptions, statement V, full proof and use of the first theorem |
| `Shao.Probability.bivariateLegendreRate.congr_simp` | Entire exported equality-congruence type, transported measure instance, equality-substitution semantics, source-bound kernel and recursive axiom evidence |

The first theorem quantifies a real probability measure mu, unrestricted real `level,a0`, strictly positive `cap,delta,c`, and an arbitrary real-valued F on pairs. It requires the exact eventual equality

`I(a0+u.1, (a0+u.1)^2/level^2-u.2) = (F u : EReal)`

in the full pair neighborhood of `(0,0)`, and the single uniform closed-rectangle estimate

`forall r z, |r| <= delta -> 0 <= z -> z <= delta -> c*(z+r^2) <= F(r,z)-F(0,0)`.

Its statement lets are exactly `I = bivariateLegendreRate mu (fun x => (x,x^2))` and

`V eta = {w | |w.1-a0| <= eta AND 0 <= w.1^2/level^2-w.2 AND w.1^2/level^2-w.2 <= eta}`.

It concludes the actual center equality `I(center) = (F(0,0) : EReal)` and one eta, chosen before every physical point, with `0<eta`, `eta<=cap`, `eta<=delta`, and for every `w in V eta` both the finite identity `I w = (F(w.1-a0,w.1^2/level^2-w.2) : EReal)` and `I(center)<=I w`. The actual type preserves every conjunct, including both radius bounds and the finite equality.

The second theorem repeats exactly the same mu/level/a0/cap/delta/c/F/heq/hgrowth inputs. It adds an arbitrary real-valued J and equality of that same actual I with `(J w : EReal)` at every point of the literal old closed cap window. Its sole statement let V is exactly the same window function. It concludes one positive eta bounded by both cap and delta, followed by the universal floor `J(center)<=J w` on V eta. There is no extra analyticity or measurability assumption hidden behind the theorem name, and the theorem does not establish analyticity of an arbitrary input J.

The generated owner's full type is:

```text
forall {Omega : Type u} [MeasurableSpace Omega]
  (mu mu1 : Measure Omega) (e_mu : mu = mu1) [NeZero mu]
  (W W1 : Omega -> Real x Real),
  W = W1 -> forall (z z1 : Real x Real),
  z = z1 -> bivariateLegendreRate mu W z = bivariateLegendreRate mu1 W1 z1.
```

This is equality congruence for the measure, statistic and evaluation point. The nonzero instance for mu1 is transported along `e_mu`; it does not assert nonzeroness or equality of unrelated measures. Eliminating the three equalities leaves reflexivity, with proof irrelevance for transported typeclass evidence. It adds no floor, finiteness or probabilistic assumption. Its generated proof is included in the exact-source kernel/all-owned recursive-axiom receipt. It was not excluded because its name is outside the OQ3 namespace. There are 0/0 owned definition bodies to inspect; this does not exempt the statement or proof lets inspected here.

## 4. Full proof audit, first theorem

Source 1-7 imports only the qualified T module, opens the stated namespaces/scopes and a noncomputable section. Source 8-25 agrees with the frozen declaration; no assumption, domain, quantifier or conclusion has changed. Source 26-27 unfolds only statement lets. The proof-local I at 28-29 is the identical global rate, not a proxy or a new optimization problem.

At 30, `Metric.eventually_nhds_iff` gives an epsilon strictly greater than zero and a predicate valid at every pair of distance strictly less than epsilon from `(0,0)`. At 31-33 the center itself has distance zero, so `heq` gives the finite center identity. Only adding/subtracting zero is simplified. The proof does not infer a neighborhood property from an almost-everywhere identity or from a punctured neighborhood.

At 34-40 the witness is exactly `eta = min cap (min delta (eps/2))`. The three positive inputs cap, delta and eps/2 establish eta>0. The min inequalities separately establish eta<=cap, eta<=delta and eta<=eps/2. Since eps>0, eta<eps. The order of choices is correct: a single eta is fixed before introducing w. The public statement exposes its required positive shrinking bounds; it does not claim a supplied numerical epsilon or an unchanged old window.

At 41-46 the inverse physical coordinates are exactly `r=w.1-a0`, `z=w.1^2/level^2-w.2`. Literal membership in V eta yields `|r|<=eta`, `0<=z` and `z<=eta`, including the horizontal and normal closed endpoints. At 47-49 the default metric on an ordinary real pair is the maximum of the coordinate distances, not the Euclidean square-root distance. Thus

`dist((r,z),(0,0)) = max(|r|,|z|) = max(|r|,z) < eps`.

Each coordinate is at most eta and eta<eps, so even the closed physical boundary lies strictly inside the open epsilon ball. No missing sqrt(2) factor, unwarranted open-to-closed extension, sign loss or coordinate norm substitution occurs.

At 50-57 `hlocal` applies to these exact coordinates. The reconstruction identity is `G(r,z)=w`: `a0+(w.1-a0)=w.1`, and the second component subtracts `w.1^2/level^2-w.2` from the same quotient. The `ring` step is a polynomial cancellation around that quotient. It divides by no unknown quantity and requires no `level != 0`; real division is total in Lean, and this identity remains valid at level=0. Physical consumers may retain positive level, but it was not silently assumed by this generic bridge. Rewriting G gives the stated finite actual-rate identity at w.

At 58-61, eta<=delta transfers the exact closed coordinate bounds into hgrowth. Because `c>0`, `z>=0` and `r^2>=0`, `c*(z+r^2)>=0`. Combining this with hgrowth gives `F(0,0)<=F(r,z)`. This uses the supplied quantitative phase-growth fact, rather than a compact-minimum assertion, cellwise anchor minimality, or the desired physical floor as an extra premise. Strict positivity of c is stronger than what this short order step alone needs, but it is explicitly frozen and matches T's output; it has not been introduced during the proof.

At 62-65, both actual EReal rates are rewritten to real coercions and `EReal.coe_le_coe_iff.mpr` transports the real inequality. There is no `toReal` operation that could discard infinity. F is real-valued, so the identities prove the center and all points of this smaller window are finite actual-rate values. Source 66 is blank. The full first proof is covered.

## 5. Full proof audit, second theorem

Source 67-86 is the frozen transfer statement, including its complete old-cap hJ and both eta bounds. At 87-90 the first theorem is applied to the identical arguments mu/level/a0/cap/delta/c/F/heq/hgrowth. The returned eta, positivity and cap/delta bounds are retained without replacing the measure, center, coordinates or window.

At 91-93 the physical center belongs to the old cap window because both its tangent displacement and normal deficit are exactly zero, with `0<=cap`. Hence hJ supplies the actual I(center)=J(center) equality. At 94-99, if w belongs to V eta then each upper bound transfers by eta<=cap and normal nonnegativity is unchanged. This proves literal V eta subset V cap and licenses hJ at w. The proof does not apply the old-window identity outside its domain.

At 100-106 the actual I-floor from the first theorem is placed between the two actual I=J identities. This produces the inequality between real coercions of J(center) and J(w). At 107 `EReal.coe_le_coe_iff.mp` gives exactly the real J-floor. The different arbitrary representations F and J never need to be identified as functions or to share an inverse-chart extension: their true-rate equalities at the relevant center and point suffice. Source 108-110 closes the section/namespace and contains no extra declarations. The full second proof is covered.

## 6. Qualified old interface, original source meaning and limits

I consumed the complete public T declaration, source lines 1-62, and the complete 61-line actual T type with all let values, while reusing its old proofs/checks. The read-only local and current server T source both have hash `426d3b0713595bea5fbb4205b550f2e20e6a7f9f4aea1c555bd847cdb060dcc4`. The exact independent qualification is `drafts/oq3/u22st-proof-review.md`, SHA256 `9dd3afba4c9d742aea2c2772c014a679c7caa022179e2df3c50ff27ec006b205`. Its qualification and selected coverage/scope fields identify a fresh non-author gpt-6.1-sol/xhigh review of all 105 T source lines, complete type/let values and actual proof, with CORRECT T_ACTUAL/BATCH_INTERFACE verdicts. The actual T type export is SHA256 `3b6d30a8aedec5b12feaeaf625df8609bb9ac74683bdc6c90dcd63722b6d86d3`. No complete old proof or complete old report was reread, and no old check was replayed.

T's full input contract is the real probability measure mu; theta in the interior of its true parabola exponential-integrability domain; nonzero determinant of the actual tilted parabola covariance; positive level and a0; negative theta.2; actual tilted first/second moments equal to `(a0,a0^2/level^2)`; and the exact saddle equation `theta.1=-2*a0*theta.2/level^2`.

All T let values were checked: Omega is that true domain's interior; nu(p) is the actual quadratic exponential tilt of mu; means(p) is its actual first/second integral pair; K(p) is the logarithm of the original exponential integral; D is the actual covariance of nu(theta); pr0/pr1 are coordinate continuous linear projections; row0=`D00*pr0+D01*pr1`; row1=`D01*pr0+D11*pr1`; B(u)=`(u.1,2*a0/level^2*u.1-u.2)`. T chooses L/e with the exact row-map/means equalities, theta/source and means(theta)/target membership, and source subset Omega. Its J(z)=`e.symm(z).1*z.1+e.symm(z).2*z.2-K(e.symm(z))`; G(r,z)=`(a0+r,(a0+r)^2/level^2-z)`; F=J composed with G; v=`(1,2*a0/level^2)`; Lambda1=`2*theta.2/level^2+(L.symm v).1+(2*a0/level^2)*(L.symm v).2`.

For that same choice, T exports positive `-theta.2`, genuine smoothness/first derivative/full second-derivative identities, an eventual equality of the actual global EReal rate at G(w) with F(w), the complete cubic/mixed/quadratic remainder estimate, and, conditionally on `0<Lambda1`, positive delta,c with exactly the hgrowth rectangle estimate used here. T does not derive Lambda1 positivity merely from determinant nonzero. BY neither invokes this producer nor substitutes a different L or claims to have met its conditions: it accepts the actual eventual identity and growth facts explicitly as its reusable bridge inputs. Their compatibility with T is exact at the interface level, but specializing them to the original physical producer is still work to perform.

I also read the reconstruction intake's relevant source-bound obstruction: finite active-cell cardinality and each cell's anchor minimum do not imply a common exponential-rate floor. BY supplies the missing order bridge once the genuine same-law local identity/growth inputs are supplied and the window is explicitly reduced. It does not pretend the cardinality bound alone supplies this fact.

The actual I used in both public statements is the original `Shao.Probability.bivariateLegendreRate`: the EReal supremum over the entire genuine exponential-integrability subtype, with the genuine logarithmic MGF. I inspected these definitions in `library/Shao/Probability/BivariateLegendre.lean`; local/server/root-v58 map source hash is `d8bd5dc7099ffdbf52282ebb41ad03145a50b42547dec55bb42caacb31ed5f58`. There is no compact-dual truncation, arbitrary rate proxy, toReal replacement, finite enumeration of dual tests or altered law. Probability supplies the required NeZero instance, without a new assumption.

## 7. Pinned interfaces and environment provenance

The historical root-v58 receipt is still exactly SHA256 `253f5cce5c2503ded6a632585e4a93184b7284ea89fdc25d9a6ec65470e96025`, status PASS, checked code `88ae3c04be8f09ce57ec6d5334fb33b2632d2f3d`, tree `af49372ca63b0fba481d10acfb0c98159cd58ee8`. Its source map binds T and BivariateLegendre to the hashes above. The historical recorded v58 main is `cae262e8330f9d96ce77cf67af821f454d451773`. The current registry/TEAM reports v59; I treated that as a notice, not a reason to rerun old gates or rewrite the historical receipt.

The server toolchain pin and lakefile remain `leanprover/lean4:v4.36.0-rc1`, mathlib `807d3836b165983210ee2ecf3cd28f239436949c`, and `autoImplicit=false`. A read-only mathlib HEAD observation matches that commit. Direct pinned source excerpts checked are `Metric.eventually_nhds_iff` at `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean:781-783`, `Prod.dist_eq` and the max-distance instance at `Mathlib/Topology/MetricSpace/Pseudo/Constructions.lean:176-185`, and `EReal.coe_le_coe_iff` at `Mathlib/Data/EReal/Basic.lean:55-56`. These are precisely the topological, metric and EReal-order interfaces used in the new proofs; no online secondary source or uncertain recalled API was needed.

The reused accepted-source-view resolves T's object to the lane's own `.lake/build/lib/lean/Shao/OQ3/OpenDomainBoundaryLowerBound.olean`, SHA256 `6be9582aee39433d33a46a52fef52cdeea79c7c0e6a63a271ff131d4e6cf1cea`, matching its old qualification. BY resolves to the lane's own `PhysicalWindowRateFloor.olean`, SHA256 `371ab5a8acf8834d889c3059e015cfa11b334b4e9ca97e2d75c1f9e87e6e1614`. The BivariateLegendre view object resolves to the accepted integration-bearing-v43 object, SHA256 `0379679ed486ae83d6e50e68a24bd3a5520f2f06025dae6439b5a4b6a8ba6e25`. These were targeted read-only observations, not a cache rebuild or a new environment gate.

## 8. Saved kernel, all-owned transitive axioms and warnings

There is one source-bound complete author build attempt, attempt 1, exit 0, 5.344711644575 seconds, on the exact final 110-line source. The build history records COMPLETE_SUCCESS, two public targets, CPU14-17, native M8192, j4 and autoImplicit=false. There is no failed source attempt or omitted retry in the supplied history. I did not rerun it.

The saved first ownership audit has exit 0, 6.493779886513948 seconds, with the same source/resources/options. Its program checks each frozen target exists and is a theorem, then enumerates actual module ownership using `env.getModuleIdxFor?`, rather than assuming a namespace prefix. For every owned declaration it rejects new axioms, calls recursive `Lean.collectAxioms`, rejects any dependency outside `propext`, `Classical.choice`, `Quot.sound`, and logs the full actual type. The logged totals are frozen definitions=0, frozen source theorems=2, all theorems=3, all declarations=3, AXIOM_GATE PASS. Every one of the three actual owners, including `Shao.Probability.bivariateLegendreRate.congr_simp`, logs exactly `[propext, Classical.choice, Quot.sound]`. Thus private/generated or transitive dependencies are not silently excluded.

The exact saved build warning is:

```text
warning: mathlib: repository has local changes:
  /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3/.lake/packages/mathlib
```

The same known Lake overlay warning appears before the saved audit output. It is retained as a warning with the archived hashes; neither saved output contains a source error. I made no cosmetic source/package edit to remove it and did not repeat a successful gate. The new source scan contains no sorry, admit, axiom declaration, unsafe, native_decide or implemented_by token. The absence of those tokens supplements the complete proof review and recursive axiom evidence; it is not used as their replacement.

All my server activity was read-only saved-evidence/source/object inspection. I ran no Lean command, build, proof/audit replay, local Lean installation, cache hydration, shared-cache write, Git mutation or heavy computation. I read the workspace ownership/takeover/server instructions and current active OQ3 lease: old writer released, current successor activated, lane child ceiling one. This reviewer owns only this report and does not take implementation ownership or infer runtime from an ACTIVE registry entry.

## 9. Remaining scope and final acceptance statement

The following remain open and are not defects in the frozen generic bridge:

- Instantiate the lower-bound producer with the original actual law, actual covariance-row L and retained same positive Lambda1; bind any independently chosen L/e witnesses as required rather than assuming them identical.
- Bind the old physical analytic J and cap to that same actual-law rate identity, choose the new eta explicitly, and preserve or rebuild all shrunken-window Theta, anchor, Gaussian and Laplace facts with their correct witnesses.
- Establish the quantitative weighted reconstruction error with the genuine common exponential factor, then the actual Song Edgeworth formal result and exterior control needed by the original probability statements.

No original B/D or full OQ3 root is closed here. Corrected fixed-law A, bounded compact-tilt C, p54 repairs, the strict weak-Cramer threshold and external-result attribution remain in their recorded scopes. No new novelty or whole-problem claim is certified by this elementary bridge review.

Final decision: CORRECT for both exact public declarations and the complete actual owned module at source SHA256 `7e76ddd24536a713098341d2829077ff312296fac37da25bca41a7a573d98c7e`, with exact-source saved kernel/all-owned transitive-axiom evidence and no critical gap in the frozen scope. Coverage is 110/110 new source lines, 2/2 public authored proofs, 3/3 actual owned complete types, 0/0 owned definition values, and every statement/proof-local let value. Accept only this scope and retain the explicit remaining dependencies above.
