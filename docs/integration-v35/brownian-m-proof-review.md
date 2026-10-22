# Brownian B2 node M independent full proof review

STATUS: **CORRECT**

Fresh reviewer: `/root/brownian_m_proof_review`. This reviewer has not authored or repaired M. I reviewed all 347 source lines, every private proof, the complete new polynomial route, the frozen public interface, and the pre-existing server evidence. This accepts **node M only**. Brownian B2, the G/S nodes, and the actual Brownian first-term target remain **OPEN**.

## Exact scope and identity

The freeze [brownian-b2-frozen-v1.md](<C:/game/shao lean/coordination/shared-bearing-v34/brownian-b2-frozen-v1.md>) has SHA256 `b1a1c447eb2354f627807f6dafe56e1c3d71184d107aa94152dc5d2b82bf20fb`. Its lines 8–15 freeze the reviewed statements and definitions, module ownership, unchanged assumptions, and the complete-private-proof requirement.

The specification is [lean-interface-and-api-v1.md](<C:/game/shao lean/drafts/shared-brownian/survival-route/lean-interface-and-api-v1.md>), SHA256 `d929bd9e124348b8a1705e25079653be33c51472bcd7fe7f40f6f6e1bff9b90b`. Its four definition bodies (lines 19–30) and both theorem signatures (lines 48–58) independently compare exactly to the implementation after whitespace removal only. I also read the original full mathematical route (`596ba300939b539e470e8d3a48b294d090e0a8a1e26c143abf0ba7b6c7c4ff16`) for the consumer context. The old reflection proof's prior acceptance is not used to certify the new proof.

The reviewed [RademacherGrid.lean](<C:/game/shao lean/drafts/shared-brownian/node-m/RademacherGrid.lean>) is exactly 14,366 bytes, 347 lines, SHA256 `abb08df1b17a154ab6a8a8c59fda06eadec6a44009c89d02c8f2aeedbd4acaac`. The identical remote source is `/root/rivermind-data/shao-lean-20261021/workspaces/shared-brownian-v34/Shao/Probability/RademacherGrid.lean`. The existing emitted object is 1,061,168 bytes, SHA256 `a7e40944ff983751d3c2bdead76e6672dbdc27b74ef1f42883d50ac0d38afe73`.

There are precisely four public definitions (`radMeasure`, `radSurvival`, `coarseStrip`, `coarseProbability`) and two public theorems. No extra public mathematical interface, desired probability premise, CLT/modulus premise, or forbidden proof token occurs. In particular `hx : 0 ≤ x` remains present despite being unused by this stronger proof.

## Full source-to-mathematics review

1. **Actual objects and probability (source lines 20–39).** `Path n` is literally `Fin n → ℝ` (accepted `FinitePath.lean:18`); `prefixSum` is the sum of coordinates with index below k (`:23–24`). `radMeasure` is the literal finite Pi of the accepted law `(1/2) • dirac 1 + (1/2) • dirac (-1)` (`RademacherCosine.lean:15–30`), whose probability instance is proved. `closedStrip` monitors every k≤n, including zero and n, using weak walls (`ClosedSurvival.lean:26–27`). The coarse event includes all j≤d, hence both endpoints. These definitions do not replace actual path probabilities with abstract functions.

2. **Exact law splitting (source lines 41–93).** The prepend map is measurable coordinate by coordinate. `radMeasure_succ` proves equality of measures on every measurable rectangle via `Measure.pi_eq`: the first factor is evaluated using the two actual Dirac atoms; all remaining factors are exactly the tail product. No sign-support assertion or uniform-string model is silently assumed. `radMeasure_real_succ` then proves the real-probability half-sum for each measurable event. Finiteness of the probability measures and half weights explicitly justifies `ENNReal.toReal_add` and the map-evaluation steps.

3. **Prefixes and strict crossing (source lines 95–111).** `prefix_cons` proves `S_(k+1)(cons z w)=z+S_k(w)`. The crossing event is exactly `∃ k≤n, a<|s+S_k|`, including the current state and the terminal index. Its measurability follows from measurable finite prefix sums and a countable union with the k≤n condition. No wall atom is discarded.

4. **Potential, nonnegativity, and moment content (source lines 113–131; new route lines 19–33).** For natural r,
   `V_r(s)=s⁴+6rs²+3r²−2r ≥ s⁴ ≥ 0`.
   At r=0 the extra term is zero. For r≥1, `6rs²≥0` and `r(3r−2)≥0`. The source proves this with a separate zero/successor split. Expanding the two polynomials gives
   `(V_r(s+1)+V_r(s−1))/2=V_(r+1)(s)`.
   Indeed averaging `(s±1)^4` gives `s⁴+6s²+1`, and averaging `(s±1)^2` gives `s²+1`. Together with the exact product splitting and base `V_0(s)=s⁴`, this is also a complete inductive mathematical proof that V is the expected terminal fourth power. In particular its value at zero is `3r²−2r`. The implementation needs only the proved polynomial recursion and domination, so it has no unproved separate moment premise.

5. **Complete first-crossing recursion (source lines 133–172; new route lines 35–48).** The induction proves `a⁴ μ_r(C_r(s))≤V_r(s)` for every real state s and a>0. If `a<|s|`, prefix zero already crosses, so the event is universal and its cost is bounded by `a⁴≤s⁴≤V_r(s)`. Otherwise zero does not cross. After a first coordinate z, the source proves the exact preimage identity `C_(r+1)(s)∘cons z=C_r(s+z)`, using successor/zero cases for the crossing index. The two induction hypotheses at s+1 and s−1, the exact half-sum law, and the polynomial recursion complete the step. At r=0, the crossing/noncrossing cases are respectively universal/empty. This is a complete finite sign-tree first-crossing proof; it does not require a missing selector, reflection involution, stopping time, or optional-stopping theorem. Equality `|s|=a` belongs to the noncrossing branch, exactly as strict crossing requires.

6. **Public maximal inequality (source lines 174–183).** Set s=0 and obtain `a⁴ P(crossing)≤3m²−2m`. Positivity a>0 licenses division by a⁴. Natural m≥0 gives `3m²−2m≤6m²`, yielding the exact frozen bound. At m=0, the only prefix is zero, so the crossing event is empty and both sides of the claimed bound are zero. No positivity assumption on m is added.

7. **Actual block law (source lines 185–222).** The coordinate family under the actual Pi law is independent. Precomposition with an injective selector preserves that independence; each selected coordinate's push-forward is literally the same Rademacher law by `measurePreserving_eval`. The accepted `iid_samplePath_map_eq_pi` (`FiniteIID.lean:32–43`) therefore identifies the whole selected path law with `radMeasure m`. The selector `i↦jm+i` is proved in range and injective for every j:Fin d. This is equality of actual block push-forward measures. Cross-block independence is unnecessary for the later union bound.

8. **All block prefixes and union bound (source lines 224–274).** `prefix_step` proves the one-coordinate prefix identity by equality of finite index sets. `prefix_block` proves
   `S_(jm+k)=S_(jm)+S_k(block_j)`
   by induction for every k≤m, including k=0 and k=m. The bad event is the union over every j:Fin d of that block's strict crossing event. Push-forward evaluation uses the proved measurability and exact block law. Summing the maximal bound yields `P(bad)≤d·6m²/a⁴`.

9. **Weak event containment and endpoints (source lines 276–314).** Restricting a full strip to j·m≤d·m gives the first containment. For the other, if a coarse path is outside the bad-block event, every block prefix is ≤ε√(dm), since bad crossing is strict. For each k<dm, m>0 gives `j=floor(k/m)<d`, r=k mod m≤m, and `jm+r=k`. The block prefix identity and triangle inequality give `|S_k|≤(x+ε)√(dm)`. The remaining k=dm is treated explicitly using the terminal coarse endpoint and ε√(dm)≥0. Thus no prefix, endpoint, or equality at the wall is lost.

10. **Frozen coarse conclusion and exact scalar factor (source lines 316–344).** Real-measure monotonicity and the finite union bound apply to the containments under the same `radMeasure (d*m)`. From d,m>0 and ε>0, a=ε√(dm)>0. The source proves `(√(dm))⁴=d²m²` and cancels only nonzero d,m,ε to get
    `d·6m²/(ε√(dm))⁴=6/(d ε⁴)`.
    Both frozen inequalities, all binders, normalization √(dm), and the x+ε weak strip match exactly. In particular x=0 is covered.

The new [proof-route.md](<C:/game/shao lean/drafts/shared-brownian/node-m/proof-route.md>), SHA256 `db23c62d1c0cbbf2599f31b242852f72bf19af3b8e296f61d39b14d595da3cce`, is complete and corresponds to the implementation. Replacing an optional reflection construction with this finite polynomial induction does not change any frozen declaration or mathematical assumption.

## Existing server evidence and full audit

I performed only read-only server inspection through the existing shared `tools/server.py` connection, with new inspection commands pinned to CPU10–13. I did **not** rerun Lean, emit an object, modify source/Git/cache state, or change any process. Local writes are only these two review files.

The author receipt hashes to `8fffc6c4264eb41b5e0e3d41203ec6109aa528fe77919ab7b73705070b347a6b`. Local `server-result.json` and remote `repro_outputs/node-m/result.json` are byte-identical, SHA256 `f074e3acf5cf507b9cf776c22707957ac801904e41c4271699152739615d8e7f`. Remote source, emitted object, audit source, and both successful logs have exactly the frozen hashes and byte sizes. The recorded final target command emits the exact object path using `lake env lean -j4 -M8192 -DautoImplicit=false -o .../RademacherGrid.olean Shao/Probability/RademacherGrid.lean`; the existing check/audit receipts record exit 0.

| Existing remote artifact | SHA256 | Read-only verification |
|---|---|---|
| `check-07-full-emit.log` | `46e78e30895ed4435daf0bf5d0a7a6ae124773e6bfb2f676ab1297c154cb2288` | 2,752 bytes / 48 lines; no error or proof-stub line |
| `audit.lean` | `9f24c6e4884c462bb09984af60b1c35a908208cdc38474c58ab7f40aa69a071d` | 2,364 bytes; imports emitted M object and audits ownership/transitive axioms |
| `audit-01.log` | `df370eee6250261bf593e131cbaef12d058bdfa983c2e30226838fef46d9adc1` | 55,462 bytes / 908 lines; complete final counters and both explicit axiom printouts |

The audit source [audit.lean](<C:/game/shao lean/drafts/shared-brownian/node-m/audit.lean:21>) enumerates **all** environment constants, uses `env.getModuleIdxFor?` and the actual module header to establish ownership, and calls `Lean.collectAxioms` on every declaration owned by any actual imported Shao module (lines 21–40). This includes private/generated constants whose names do not begin with the public namespace. It rejects any axiom outside `propext`, `Classical.choice`, `Quot.sound` and asserts public-interface coverage (lines 41–49).

I parsed every complete record, including wrapped axiom lists. There are **349 distinct dependency records**, across exactly **13 project modules**, and **57 distinct M-owned records**. The M-owned set is exactly the target-owned subset of those dependency records, and exactly matches the 57-name receipt inventory. All 57 records pass the same whitelist. The successful footer reports 47 theorem constants, the exact two public theorems, and four public definitions (`audit-01.log:902–906`); both explicit target axiom outputs are whitelist-only (`:907–908`). All 349 transitive records pass, with no disallowed axiom or missing module binding.

| Actual imported Shao module | Constants audited |
|---|---:|
| `Shao.Basic.ClosedSurvival` | 20 |
| `Shao.Basic.Events` | 23 |
| `Shao.Basic.FinitePath` | 67 |
| `Shao.Basic.OrderedSelection` | 31 |
| `Shao.C1.Normalization` | 25 |
| `Shao.C2.TwoSided` | 11 |
| `Shao.OQ4.CosineCoefficients` | 11 |
| `Shao.OQ4.KilledCosine` | 9 |
| `Shao.OQ4.KilledKernel` | 15 |
| `Shao.OQ4.RademacherCosine` | 34 |
| `Shao.Probability.FiniteIID` | 8 |
| `Shao.Probability.MeasurablePath` | 38 |
| `Shao.Probability.RademacherGrid` | 57 |

All **26 source/object hashes and sizes** in the 13 project-module bindings match the existing remote files. The 12 imported pre-M sources also exactly match the read-only accepted v33 local library copies. Source/object/log modification times are consistent with source freeze, final object emission, then the importing audit. No hash was accepted solely from the printed author summary.

The toolchain file and manifest specify Lean `leanprover/lean4:v4.36.0-rc1` and Mathlib `807d3836b165983210ee2ecf3cd28f239436949c`; the actual Mathlib HEAD matches. The build's repository-local-changes warning is retained, as are all earlier diagnostic logs. The missing/type-changed status observation was specifically from `/root/rivermind-data/shao-lean-20261021/workspaces/shared-brownian-v34/.lake/packages/mathlib`, which resolves to the private overlay `/root/rivermind-data/shao-lean-20261021/cache-overlays/shared-v34/packages/mathlib`. That overlay's `.git` and `Mathlib` entries resolve into `/root/rivermind-data/shao-lean-20261021/lean/.lake/packages/mathlib`; symlink layout explains the overlay type-change reporting. I did not inspect the original shared checkout's status in that check and make no missing/changed-file claim about it. The relevant inspected Pi, independence, and real-measure source contents each byte-match their pinned Git blob. This path-precision clarification changes neither the mathematical verdict nor the checked hashes. The final target warnings concern unused variables/tactics, deprecated aliases, and redundant simplification; they do not report target or audit errors.

Protected PID143204 was observed as `python3` with `Cpus_allowed_list: 0-9`. Nothing was terminated, repinned, reniced, or resource-limited.

## Acceptance boundary

No critical gap was found in the exact M statements, definitions, new mathematical proof, private Lean proofs, or the frozen existing server evidence. **Node M is CORRECT at the exact source/object hashes above.** The stronger polynomial estimate is a valid implementation of the public 6m² bound, and the coarse estimate has the exact 6/(dε⁴) constant.

This module proves only finite Rademacher maximal and coarse-grid comparisons. It does not itself prove a Brownian CLT bridge, a dense Brownian grid limit, a spectral envelope, or the actual Brownian first term. **B2, G, S, and the full first-term target remain OPEN.** This review closes no additional original root. Integration must preserve the reviewed bytes and complete its separately required gates.
