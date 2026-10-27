# Unit223 native001 proof repair plan

Status: PLAN_ONLY, NOT_IMPLEMENTED, UNELABORATED. The current source remains exact SHA256 `88b7164a43fe06a7e41fe83b593bd4a5a5b517af897bfe7d27cf98648e46ad3d`, 10989B/226LF. PROPOSED-FULL-SOURCE.txt is a materialized candidate text for parent inspection/freeze; no repaired Lean file has been created and no old author source has been edited.

The authoritative native001 diagnostic projection v2 records the SAME single failed server attempt: RC1, 6.6097067426890135 seconds, six errors, one warning, no object, all-owned ended, before/after exact, preservation true and no own Lean process. V1's four-error count omitted two error(lean.invalidField) records and remains superseded evidence, not a second check. The 15,782,759-byte original receipt remains on the server and was not transferred or replayed.

| Native001 observation | Exact proposed action | Classification |
|---|---|---|
| Lines115/118/121: simplification retains the constant-zero tilted product instead of P | Replace the three bare `tilted_zero` simp entries with explicit `MeasureTheory.tilted_const` | Observed law-identity representation mismatch |
| Line133: no `MemLp.div_const` field for hF2 | Apply public `hF2.mul_const` to the reciprocal of the SAME original denominator, and add `div_eq_mul_inv` to the existing full-D simplifier | Observed missing field; arithmetic normal form |
| Line136: the same nonexistent field on `hF2.sub (hpsi2 i)` | Apply public `MemLp.mul_const` to the SAME reciprocal before congruence | Observed missing field |
| Line137: no goals after the preceding failure | Retain the complete congruence proof after repairing the preceding public call | Observed cascade, not an independent mathematical gap |
| New `mul_const` congruence left side is multiplication by the reciprocal | Match that literal product in the existing `change`, then rewrite `← div_eq_mul_inv` before unchanged `congr 1`/incident identity/linarith | Inferred necessary downstream join, not a separately observed native failure |

The stored pinned Tilted API shows that the probability-law `tilted_zero` is a legitimate identity for a zero function. I do not identify it with the distinct zero-base-measure lemma. The actual native simplifier nevertheless left `fun xi => 0`. The accepted explicit `MeasureTheory.tilted_const` usage matches that displayed constant lambda directly and retains the same original probability instance. There is no new law, normalization, instance or hypothesis.

The existing pinned local LpSeminorm/SMul API excerpt explicitly gives both `MemLp.const_mul` and `MemLp.mul_const`. The plan chooses RIGHT multiplication because division is already `a*b^(-1)`: it avoids an extra commutation step. The multiplier is the literal real expression `(N*((n:Real)-1))^(-1)`, with existing captures N,n; it is not a new ordinary value or local let. The identity `div_eq_mul_inv` is unconditional and adds no nonzero-denominator premise. The original n>=4 and all original coefficients are unchanged.

No derived proposition, lambda, helper, ordinary value, instance, witness, selector or premise is added. All existing affected proposition types and capture sets remain the same. DATA-AND-CAPTURE-MAP.json records the five affected existing facts, exact scalar/law/congruence joins and the unchanged scoped hIncident. LOCATORS.json preserves case-sensitive names, all target lambdas, and explicit checks for absent funext and bullet-have forms. The entire source suffix beginning at hJI is byte-identical to native001.

The existing line90 derived Prop `letI` warning is retained, with no linter suppression. The independent complete CORRECT_SOURCE review of native001 remains bound; this plan requests only affected repair review after the parent freezes and activates this exact target. Source-level argument and public API evidence do not predict a kernel pass. Any additional elaboration failure must be preserved and handled as a new affected failure.

The old n^2 coarse-budget recovery and current (n-2)^2 J/Jdel/B1/B1del formulas are untouched. C0=0 and rho=0 remain included. p51 stays UNCERTIFIED_REPAIR_CANDIDATE; p54 repairs and external Shao-Zhou2016 attribution remain. No deleted-M_epsilon, S25 analytic limit, CDF, S11/generalS15/DC/OQ56/root closure is claimed, and OQ3 stays user-paused.

No Lean/compiler/server/network/transfer/Git/API/publication/child operation occurred in this plan. The next dependency is parent inspection and exact repair-target freeze, then separate SAME-author implementation authorization. A final answer does not provide continued execution. Actual model/effort and unexposed usage are null.
