# Unit 230 repair01: four real-power rewrite spelling bridges

Status: COMPLETE_AFFECTED_REPAIR_READY_FOR_DELTA_REVIEW_AND_NEW_NATIVE.
No new Lean or axiom check has been performed by this author.

The complete repaired source is `IIDSourceStrictMomentBudgets.lean`, SHA256
`4905904cb5e8f37f1731c92da9e504e614e8dc7734a5de3f124ab2bceff55c36`,
10716 bytes / 245 LF / zero CR / UTF-8 without BOM.

The original 10511-byte source
`68dec15cc392157d84d3bf8d6dd8193668182458f6734daadbf668b19f2144b7`
and native001 failure evidence remain exact. The complete normalized
diagnostics report four errors, zero warnings, natural RC1 in 5.657673314
seconds, no original object, no remaining owned Lean process, and equality
of all 19057 protected records. These are observations from the existing lead
receipt; this author did not repeat the check or contact the server.

## Exact changed proof scope

Exactly four new lines were inserted; no original line was removed or
replaced. Removing those four insertions reconstructs the old source bytes
exactly. `EXACT-DELTA.json` records each insertion and its old/new line map.

| Original failing line | New bridge line | Affected local proof | Repair |
| --- | --- | --- | --- |
| 83 | 83 | `hcpower` | Convert the explicit nested `Real.rpow` goal to HPow spelling before reversing `Real.rpow_mul`. |
| 190 | 191 | `hβpower` | Apply the same spelling bridge before the negative-beta-exponent multiplication identity. |
| 197 | 199 | `hnpower` | Apply the same spelling bridge before the n-exponent multiplication identity. |
| 208 | 211 | product equality inside `hWindowPower` | Convert the goal and four directly used proposition facts to the same HPow spelling before `Real.mul_rpow` and the two helper rewrites. |

The first three insertions are `simp only [Real.rpow_eq_pow]`. The fourth is
`simp only [Real.rpow_eq_pow] at hβrootNonneg hnrootNonneg hβpower hnpower ⊢`.
The latter also bridges the nonnegativity facts that determine the bases of
the product lemma, and the two equalities consumed after product expansion.
Thus the inserted normalization is consistent across both sides of the
rewrites; no new ordinary value is introduced.

The diagnostics show a syntactic mismatch between explicit `Real.rpow` goals
and HPow-spelled patterns. `Real.rpow_eq_pow` states the equality of those two
spellings. The repair preserves the same nonnegative bases, real exponents,
positive-denominator hypotheses, exponent cancellations and conclusions.
It changes no mathematical assumption or source interpretation.

## Compatibility and evidence limits

The exact frozen 557-byte preamble and 2097-byte declaration head remain the
prefix; the exact 48-byte closing remains the suffix. Every ordinary typed
let is unchanged: nine in the head, nine proof repeats, and the approved
local f. Its type/right-hand side/captures/scope remain frozen. There is still
one top-level theorem and no new global helper, ordinary parameter, local
instance or premise. The beta-zero and positive-beta closed-window branches,
constant order and literal source-z argument are unchanged.

All writes are confined to `unit230/author-01/repair-01/**`. The original
source, implementation packet, Stage1 packet and all receipts were retained;
no other-owner implementation or shared file changed. Units228/229 were not
read, imported, renamed, retried or used. The repair introduces no new
dependency or cache requirement.

Only local byte/hash/format/frozen-inventory and exact-delta checks were
performed. No Lean/server/network/transfer/Git/API/children operation occurred.
The changed proof requires the same independent reviewer's affected-delta
inspection and a new exact-source native check. No new success, object,
axiom receipt or independent review verdict is claimed here, and no duplicate
review or replay of unaffected old modules is requested.

The requested model/effort remain gpt-6.1-sol/xhigh in the same authorized
author context. Actual exposed model/effort and token counters are unavailable
and recorded as null. The author releases this repair writer slot with zero
heavy, in-flight, pending, uncertain or delegated work.
