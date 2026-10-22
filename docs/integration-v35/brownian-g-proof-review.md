# Independent Brownian B2 node G proof review

STATUS: CORRECT

STATEMENT_AND_ORIGINAL_SEMANTICS: CORRECT

FORMAL_EVIDENCE: Existing successful strict source/object and complete owned-declaration axiom gates inspected and rehashed; no Lean rerun in this review.

This is a fresh never-author review by `root/brownian_g_proof_review`. I read all 525 lines / 22786 bytes of the exact candidate, including every private proof, and checked its complete path from the actual finite Rademacher product to the actual Brownian grid probabilities and then to B1's continuous-time probability. I did not author, repair or edit any implementation. No critical mathematical or statement-fidelity gap was found. No fix is required for the reviewed node.

Acceptance is confined to the exact frozen G source/object identified below. Full Brownian B2 remains OPEN until S and all independent acceptance and root integration gates close. This report does not certify an exact Brownian spectral series, canonical Brownian existence, or the full original OQ4 self-normalized uniform relative-error theorem.

## Frozen inputs and identity

Read `AGENTS.md`, `SERVER.md`, `coordination/TEAM.md`, and math-theorem's skill, prompt-library, openai-workflow and lean-verification references. The original `C:/game/shao/current/oq4/frozen01.md:3,7–9` specifies the actual standard Brownian supremum on [0,1] and its first term. The reviewed paper route and declaration proposal supply the permitted intermediate G statements; the earlier CORRECT route review is not substituted for this source review.

| Artifact | SHA256 |
|---|---|
| `coordination/shared-bearing-v34/brownian-b2-frozen-v1.md` | `b1a1c447eb2354f627807f6dafe56e1c3d71184d107aa94152dc5d2b82bf20fb` |
| `drafts/shared-brownian/survival-route/proof-route-v1.md` | `596ba300939b539e470e8d3a48b294d090e0a8a1e26c143abf0ba7b6c7c4ff16` |
| `drafts/shared-brownian/survival-route/lean-interface-and-api-v1.md` | `d929bd9e124348b8a1705e25079653be33c51472bcd7fe7f40f6f6e1bff9b90b` |
| G source `Shao/Probability/BrownianGridBridge.lean` | `98741686b236686ea72d9d6b9c44dced7b6f1036528942bb7bf69154972bd5e9` |
| G emitted `.olean` | `fa4e0ffe41fe390ff80aa1b9b97c19eae3391f448e992015eb46309ecae31d58` |
| Certified B1 source `Shao/Probability/BrownianSup.lean` | `f7f86bd8db582d9a4e53241f9cfc8384f86ee33765a40c5541a15b6f0c22a718` |
| B1 emitted `.olean` | `8a3072bc84c46e050f77f2dac29b3d2ebff1102bd4623ed38178101f05bea68c` |
| Final M source `Shao/Probability/RademacherGrid.lean` | `abb08df1b17a154ab6a8a8c59fda06eadec6a44009c89d02c8f2aeedbd4acaac` |
| M emitted `.olean` | `a7e40944ff983751d3c2bdead76e6672dbdc27b74ef1f42883d50ac0d38afe73` |

G's local and remote source bytes agree. The worktree is `/root/rivermind-data/shao-lean-20261021/workspaces/shared-brownian-v34`. Its source and emitted object are regular files in that worktree, as are the actual M and B1 source/object dependencies. The M/B1 object hashes agree with their existing receipts. B1's independent CORRECT review is `proof-review-brownian-b1.md/json` at the same source hash. G uses M's actual definitions, rather than assuming M's comparison conclusion or a replacement distribution.

## Exact public interface and source fidelity

G lines 19–29 define precisely the frozen three objects: `gridTime d j = j/d` in nonnegative reals; the event requiring `|B_(j/d)| ≤ x` for every natural j≤d; and its actual `P.real` probability. Lines 436–439 prove the frozen fixed-grid convergence with only B/P, the probability instance, actual `IsBrownianReal B P`, d>0 and x>0. Lines 511–513 prove the frozen dyadic convergence for every real x to the certified B1 `probability B P hB x`. There are exactly these two source-public theorems and these three source-public definitions. Making `gridTime` noncomputable does not alter its expression or scope.

B1 lines 53–54 define the literal weak strip for all t∈[0,1]. B1 lines 121–148 identify its real measure with the probability of the measurable version of the actual path supremum. G finishes through this exact `probability_eq_fullStrip`, rather than introducing another probability function. The arbitrary measurable sample space and given B remain quantified. There is no desired grid convergence, Brownian small-ball estimate, path-modulus estimate, functional CLT, supremum-no-atom premise, extra iid sequence, strengthened Brownian predicate, or conditional first-term wrapper.

## Complete mathematical proof audit

1. **Actual product and scalar inputs (G 31–112).** M 24–35 defines `radMeasure n` as the Fin n product of the actual two-atom law and defines the literal coarse prefix event. `Shao/Basic/FinitePath.lean:18,23–24` is `Fin n → ℝ` with the sum of coordinates of index <k, and `RademacherCosine.lean:15–30` is the two half-weighted atoms at ±1 with total mass one. G's private probability instance unfolds that same product. G 49–70 proves mean zero and second moment one by integrating the two atoms, paying the single-law CLT's actual integral hypotheses. The integrability argument is valid for this finite atomic measure.

2. **Block characteristic function and normalization (G 36–42,72–112).** `finProdFinEquiv (i,k)` flattens to k+m*i, so the d blocks are the literal consecutive disjoint blocks of the original dm coordinates. G computes the joint characteristic function directly under `radMeasure (d*m)`: the inner product is a sum of independent weighted coordinate projections; evaluation has exactly the Rademacher law; regrouping the product gives d powers, each of exponent m. The factor at coordinate i is `φ(t_i/(sqrt(d)*sqrt(m)))^m`. No law replacement or unproved independence of block sums occurs.

3. **Actual Brownian target and finite-dimensional Lévy (G 114–132,164–221).** The code uses raw actual Brownian increments Δ_i=B_((i+1)/d)−B_(i/d), and scales the Rademacher block vector by 1/sqrt(d). This is algebraically equivalent to the paper route's standard-normal block vectors followed by a cumulative map scaled by 1/sqrt(d). G 117–132 pays the monotone-time hypothesis of the actual finite independent-increments API. G 164–198 proves variance exactly 1/d and the characteristic function `exp(-((t_i/sqrt(d))²)/2)`. The square-root identity uses nonnegativity of natural casts and contains no missing factor d. At fixed t, the proved single-law characteristic-function CLT supplies each factor limit; the finite product gives the joint limit. All finite vectors are a.e. measurable. Lévy at G 203 applies to EuclideanSpace on Fin d, explicitly permitting the sample spaces `Path (d*m)` to vary with m.

4. **Cumulative map and exact endpoint identities (G 223–325).** The map sums the first i+1 coordinates and is continuous. G 239–275 proves its image is the literal prefix sum at (i+1)m divided by sqrt(dm). The identity `sqrt(dm)=sqrt(d)*sqrt(m)` and the flattened-index inequality are proved in source. Every block endpoint through dm is present; the zero prefix is subsequently added by the event adapter. At m=0 there is no element of Fin m, so the relevant finite identities remain total; no positive-denominator event equivalence is claimed there. G 277–311 proves the finite telescoping identity for every k≤d, including k=0 and k=d. G 313–325 uses the single a.e. equality B_0=0 to replace every Brownian cumulative vector by its actual positive-time endpoint vector. No family of uncountably many a.e. equalities is formed.

5. **Closed weak cube and null frontier (G 327–396).** The cube is the finite intersection `|v_i|≤x`, proved closed. A frontier point is in the closed cube; if no coordinate equals ±x, all inequalities are strict, placing it in the open finite intersection and contradicting frontier membership. This proves the needed frontier containment, including the degenerate x cases of this helper. For each coordinate, (i+1)/d>0 follows from d>0 and i+1≥1. `hasLaw_eval` and the Gaussian singleton theorem therefore give zero mass to both coordinate levels. Pullback of the finite union and measure monotonicity establish the actual endpoint law's null frontier. This uses only endpoint atomlessness at positive times, not atomlessness of a path supremum or a boundary-crossing result.

6. **Passage to the actual coarse and grid event probabilities (G 398–458).** For d,m>0 the factor sqrt(dm) is strictly positive, so dividing the weak bound is reversible with no sign change. The Rademacher cube event equals `coarseStrip`, including j=0 through S_0=0. The Brownian cube event equals the grid event a.e. through B_0=0, with x>0 paying the zero-time inequality. The positive-time coordinates i+1 cover j=1,...,d exactly. Portmanteau applies to the proved null frontier. All probabilities are finite; continuity of ENNReal.toReal gives the real-probability limit. The final source adapter explicitly restricts to eventual m≥1 (G 453), so the initial m=0 term is harmless. The public theorem claims neither d=0 nor x≤0, exactly as frozen.

7. **Dyadic refinement and dense approximation (G 134–160,479–509).** Every coarse dyadic time j/2^r is exactly (2j)/2^(r+1), with index within the finer grid, proving antitonicity in the correct direction. At r=0 the grid has d=1 and includes times 0 and 1; no omitted initial grid or division by zero arises. The floor approximant `floor(t*2^r)/2^r` tends to t for each nonnegative t by the inspected floor-limit theorem. For t≤1 its index is ≤2^r, including t=1 exactly. G 491 restricts once to `hB.cont`; for every path in that same a.e. set it proves both event inclusions for every t∈[0,1]. Continuity of that path's absolute value and closedness of the weak inequality give the reverse inclusion. It does not intersect an uncountable family of a.e. statements.

8. **All-real-x probability limit (G 461–477,511–523).** Each grid event is a finite intersection of coordinate weak bounds and is null measurable using only the supplied coordinate a.e. measurability. Probability continuity from above requires those null-measurability proofs, antitonicity, and one finite stage; all are supplied. The a.e. dyadic-intersection/fullStrip identity identifies the limit measure; finite-measure toReal conversion and B1 identify the exact final probability. The argument is valid for x=0 and x<0 without any strict-wall or no-atom limit step. For x<0, the j=0 absolute-value constraint already makes every grid and full strip empty. No part of this proof asserts or needs probability continuity as a function of x.

These stages close exactly the two mathematical obligations assigned to G. They leave the separate finite spectral envelope, ordered m/d/epsilon transfer and final x↓0 limit to S, as the frozen dependency plan requires.

## Inspected external API hypotheses and actual bindings

I independently read the actual bound Mathlib source at the pinned commit `807d3836b165983210ee2ecf3cd28f239436949c`:

| Source location | Requirement checked |
|---|---|
| `Probability/CentralLimitTheorem.lean:51–67` | Single-law characteristic-function powers need a probability measure, a.e. measurability, mean zero and second moment one; no infinite iid sequence. |
| `MeasureTheory/Measure/LevyConvergence.lean:39–40,222–238` | Finite-dimensional real inner-product Borel target; a family of sample spaces indexed by n; source/limit a.e. measurability and characteristic-function convergence. |
| `MeasureTheory/Function/ConvergenceInDistribution.lean:64–70,104–112,136–148` | Actual pushforward probability measures, valid a.e. congruence, and continuous mapping theorem with the needed Borel structure. |
| `Probability/BrownianMotion/Basic.lean:75–108,168–184,302–304` | Actual FDD law, coordinate a.e. measurability, Gaussian eval and difference laws, B_0=0 a.e., independent increments, one a.e. continuous-path set. |
| `Probability/Independence/Process/HasIndepIncrements/Basic.lean:57–59` | Monotone Fin(d+1) time vector yields the d successive increments. |
| `Probability/Independence/CharacteristicFunction.lean:195–204,225–229` | Finite independent-sum/product formulas and the exact toLp joint vector, with a.e. measurability. |
| `Probability/Distributions/Gaussian/Real.lean:233–236,481–485` | Singleton nullity requires nonzero variance; Gaussian characteristic function has the expected variance coefficient and sign. |
| `MeasureTheory/Measure/Portmanteau.lean:334–341` | Weak convergence of probability measures plus null frontier yields ENNReal event-measure convergence. |
| `MeasureTheory/Measure/Continuity.lean:220–227` | Null measurable decreasing events and a finite stage give measure continuity from above. |
| `Analysis/SpecificLimits/Basic.lean:723–735` | `floor(a*x)/x→a` at positive infinity for a≥0, matching the explicit dyadic approximation. |

The worktree's `.lake/packages` resolves to `/root/rivermind-data/shao-lean-20261021/cache-overlays/shared-v34/packages`; actual Mathlib object files are in its mathlib build directory. The inspected Mathlib sources resolve to the shared pinned source checkout and are byte-equal to its files. The actual `.git/HEAD` reference file resolves to `refs/heads/pinned`, whose contents are the expected commit. The worktree `lean-toolchain`, lakefile and manifest all pin Lean `v4.36.0-rc1` / this exact Mathlib revision. No version or cache state was changed. The preexisting Lake repository-change warning corresponds to this root-prepared private overlay, not a Lean source diagnostic.

## Strict source/object and complete axiom evidence

The existing remote receipt records exit 0 for:

```text
taskset -c 10-13 lake env lean -M8192 -j4 -DautoImplicit=false -DwarningAsError=true -o .lake/build/lib/lean/Shao/Probability/BrownianGridBridge.olean Shao/Probability/BrownianGridBridge.lean
taskset -c 10-13 lake env lean -M8192 -j4 -DautoImplicit=false -DwarningAsError=true repro_outputs/node-g/audit.lean
```

I inspected/rehashed the actual strict log, emitted object, import-audit source, complete audit log, author receipt, proof map and checkpoint. I did not rerun either command. The strict source log contains only the known Lake overlay warning, with no Lean source warning/error. The imported-object audit selects every environment constant whose module owner is exactly `Shao.Probability.BrownianGridBridge` and runs `Lean.collectAxioms` on each, rather than selecting only public names. It separately confirms both public names are theorem declarations.

All 78 multiline `OWNED_DECL ... AXIOMS [...]` records were parsed, with 78 unique names, 67 private names and 36 names containing generated-proof/simp/equation markers. The log reports 68 theorem constants and 2 frozen public theorem declarations. All 42 explicit source declarations (37 private, including the private instance; 31 explicit theorem declarations, 29 private) have matching owned audit records. No explicit declaration is missing. Every parsed transitive axiom set is a subset of `{propext, Classical.choice, Quot.sound}`; there are no exceptions. Both public `#print axioms` outputs agree. The complete source scan finds no `sorry`, `admit`, `axiom`, `unsafe` or `native_decide`.

| Existing evidence | Bytes | SHA256 |
|---|---:|---|
| `repro_outputs/node-g/candidate-07-strict.log` | 144 | `1fe2df6249264854f739bdebcb7ee2e4b82cecb8c6bf75ce9f40ca36badcecc1` |
| `repro_outputs/node-g/audit.lean` | 1770 | `98770ad79528f0723a97f959283c2496fb01b7b4a9df1885e7f321fe5da47765` |
| `repro_outputs/node-g/audit-final.log` | 12109 | `954989ddb5b87bbdc0e330ed3099ad2fda479f1c4aa97d67b4dd7f360e92d0f2` |
| `repro_outputs/node-g/author-receipt.json` | 2882 | `49ab9721d320694b92980f9a1e38a22b3b6473c0f4596cb52c5efc1b4f29cb11` |

## Decision and release

CORRECT for the exact frozen G node. Required fixes: none. Statement fidelity and complete source proof both pass; existing strict source/object and full owned/private/generated transitive-axiom evidence pass at the recorded hashes. Root still owns integration and final whole-B2 acceptance.

All remote review commands were bounded, read-only Python/source/log metadata reads via the existing `tools/server.py`, under CPU10–13 affinity. No Lean execution, source edit, Git operation, cache mutation or process-management action ran. A final read-only `/proc/143204/status` observation showed the external user's python3 process still allowed CPU0–9. Its 80 GiB allowance was not changed. Only this Markdown report and its JSON companion were written locally. Reviewer work is complete; release this slot.
