# Unit283 proposed assembly contract

STATUS: PROPOSAL_ONLY. The parent owns declaration freeze. This packet creates no implementation or execution authority.

Proposed module: `Shao.OQ5.P41.FixedMaskJointBlockFubini`.
Proposed later filename: `FixedMaskJointBlockFubini.lean`.

Assemble PRE.txt verbatim, then each declaration in ORDER.txt, then CLOSE.txt verbatim. For each D declaration concatenate its literal complete HEAD ending in the outer `:=` with its bare fixed RHS file. For each T declaration the HEAD stops at the complete target: no proof separator or theorem body is present. A separately authorized later implementation may append a theorem proof only after the parent freezes the packet. No theorem proof, executable Lean module, wrapper, check, or new shared implementation is included here.

The three fixed definitions preserve all observations. `splitSample` has background as its first coordinate and the entire complementary anomalous vector as its second. `joinSample` reconstructs each original coordinate using the same arbitrary fixed eB/eA. `backgroundSection` fixes the entire anomalous vector a. The complement is literally `(Bᶜ : Finset (Fin n))`; eA cannot enumerate a proper subblock or use a fresh independent sample. There is no sample-dependent enumeration.

T01/T02 are inverse contracts, T03/T04 measurability contracts, and T05/T06 are section contracts. T06 has a generic SFinite measure premise on the background-vector measure; this is a standard integration interface, not a new hypothesis on the original observation law. T07 is the actual positive-mask joint conditional law. It must reuse the public `Shao.Probability.indep_cond_joint_map_eq_pi` and existing coordinate evaluation facts; do not reprove old coordinate conditioning. Its only positivity premise is actual full-mask mass nonzero. In a nonempty block its coordinate positivity follows from that premise; an empty block introduces no positivity premise.

T08 is the primary, unconditional weighted restriction identity. T09 evaluates its arbitrary measurable joint event and uses the anomaly-outer/background-inner product measure formula. T10 transports an arbitrary measurable original-coordinate event through the inverse reconstruction. T11 transports a measurable original almost-everywhere predicate to anomaly-a.e. background-a.e. sections, with actual full-mask positivity. T11 deliberately does not return a statement for every anomalous vector. All new dependency edges occur earlier in ORDER.txt.

The weight in T08/T09/T10 is the actual original product mask mass. Existing281 `fixedMask_measure` supplies its exact expression `(μ C)^B.card * (μ Cᶜ)^(n-B.card)` without a new theorem. In a zero-mask branch the restricted measure is zero; no cancellation or division by that mask is permitted. Normalized one-coordinate restrictions appear only in the product laws and are genuine cond values even at zero coordinate mass. Empty finite products retain their unit mass. No assumptions `0 < μ C`, `0 < μ Cᶜ`, `0 < B.card`, `0 < (Bᶜ).card`, or `0 < n` may be introduced.

Primary p41/p51 and qualified279/281 exact source and machine interface evidence are reused. Full old theorem proof review and old Lean/AX execution are not replayed. The parent may obtain missing read-only pinned primary API text; any such supplemental input must be separately hash-bound before use. A missing API name is not filled by guessing. Static checks are text/hash/format checks only and confer no elaboration or mathematical certificate.

Any later change to PRE/CLOSE, a HEAD, fixed RHS, guard, universe, instance, quantifier, dependency, event order, complement, weight, or integration order requires parent intake and a new freeze. Sources must remain UTF-8 without BOM, LF, and one final newline. Existing owners, source references, curated library, Probability/shared modules and all old evidence remain read-only.

The scope is finite probability transport. Subsequent consumers must use the original physical event with its existing n-2 scale, m>=4 domain, sB=0 convention and closed threshold. No interaction Bernstein estimate, actual interaction mean/variance/boundedness, Delta absorption, low-sB payment, Mills bound, anomaly exponential integration, all-mask sum, or unconditional PE-R/PE-L/NR/DC/OQ56/root closure is asserted.
