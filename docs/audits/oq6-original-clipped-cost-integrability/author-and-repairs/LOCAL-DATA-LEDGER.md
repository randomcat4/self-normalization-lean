# Complete local data and proof-scope ledger

Status: complete author source, uncompiled and not independently reviewed. Exact source blocks and full public-producer proposition types are retained in LOCAL-DATA-INVENTORY.json. These are source representations, not actual kernel TYPE records.

The exact frozen17head values and8proof-local ordinary values are unchanged modulo proof-body whitespace. No additional nonProp value/helper/selector/witness/measurable-space instance is introduced. The one explicit IsProbabilityMeasure P instance is a frozen derived Prop instance. All other canonical instances come from the frozen original context.

| Ordinary proof data | Complete type | Captures | Source start |
|---|---|---|---|
| F | `(Fin n → Ω) → ℝ` | Ω, n, r | 72 |
| psi | `(Fin n → Ω) → Fin n → ℝ` | Ω, n, r | 74 |
| LambdaSq | `(Fin n → Ω) → ℝ` | Ω, n, psi | 78 |
| LambdaDelSq | `(Fin n → Ω) → Fin n → ℝ` | Ω, n, r | 80 |
| sigma | `ℝ` | rho | 85 |
| base | `ℝ` | sigma, N | 86 |
| K | `ℝ` | sigma, n, N | 87 |
| BcoarseDel | `(Fin n → Ω) → Fin n → ℝ` | Ω, n, base, LambdaDelSq, K | 88 |

Every proposition proof is recorded with its complete declared result type, source block and exact scoped locator. hmodel/hobs/hcoarse inferred types are expanded from the exact complete public head, including every imported typed let/RHS, with x=0,z=0,C0=1 as applicable. hIncident is a proposition inside hDdel2 and captures that block's i and sample xi; it is not a global helper or untyped new ordinary value. Case-sensitive hF2/hFtilt2/hD2/hDdel2 and B1/B1del/BcoarseDel names are distinct.

All standalone fun lines, every fun occurrence, and every intro are inventoried; there is no funext command and no bullet-have declaration in this source. The scanner supports those forms explicitly so their absence is not a regex omission. Implicit integral/finite-sum lambdas, Prop-valued predicate functions, original instances and producer let-capture maps are retained or explicitly referenced. A/Adelete/B/Bdelete are the original exact functions, not chosen surrogates.

No existential E from qualified220 is selected: only its measurability proposition projections are used. No private producer helper is called. The finite affine and congruence families occur solely inside derived proposition proofs; they introduce no additional ordinary local let or hidden premise. The new source does not claim deleted coding envelopes or the S25 limit.
