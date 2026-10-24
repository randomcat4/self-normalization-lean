# Independent complete final reviews

These are the complete independent exact-source reviews. The lead has read both full reports, verified all bound hashes and actual-owner coverage, and qualified the exact sources. No old result was recompiled or re-reviewed to publish this milestone. The reviewer verdicts concern the local analytic modules; all original roots remain OPEN.

# Unit 142 complete independent final review

STATUS: CORRECT

The exact `WeightedDeletionMoments.lean` source SHA256 `16bf3df8202d9303e2aab275f401b02824fda2f113e8d86fef83f45db8399cd3`, together with original object SHA256 `513cd06e19116576e3651750d845435a5e3adf036c95d983c2330718d6f63f51`, has a complete independent source-to-statement/proof review and complete actual-owned type/value/recursive-axiom review. No critical mathematical, premise-fidelity, or evidence-coverage gap was found. This verdict is for the exact local analytic theorem and its private/generated declarations. All root groups remain OPEN.

## Complete source/proof review

Coverage: SOURCE_REVIEW_COMPLETE and ACTUAL_OBJECT_REVIEW_COMPLETE. The earlier checkpoint is retained separately as historical progress evidence.

Reviewer: `/root/oq56_weighted142_final_review`, fresh independent context; prescribed gpt-6.1-sol / xhigh. Source author and lead repair author are separate contexts. Actual token telemetry is unavailable: input, cached input, output and reasoning-subset counts remain UNKNOWN.

Exact candidate: `drafts/oq56/unit142/author-01/full02/WeightedDeletionMoments.lean`, SHA256 `16bf3df8202d9303e2aab275f401b02824fda2f113e8d86fef83f45db8399cd3`, 75057 bytes, 1551 lines, UTF-8 LF. The entire file, including all proof bodies, was read in contiguous line ranges 1–249, 250–546, 547–820, 821–1025, 1026–1281 and 1282–1551. All nine source lexical headers were compared to their frozen headers, including all lets; each matched exactly after LF reading. All fourteen imports match frozen-import-addendum-v3.json. There are eight private and one public lexical theorems, and no lexical top-level definitions. These lexical counts do not establish the actual generated/owned declaration count.

## Source coverage ledger

| Source declaration | Lines completely read | Mathematical check |
|---|---:|---|
| wd_insert_fubini | 31–147 | Explicit insertion and inverse measurable equivalence; product rectangle measure calculation splits singleton i from its complement; integrable pullback precedes signed Fubini. No injectivity or observation coding assumption. |
| wd_deleted_row_reindex | 149–247 | Bijective coordinate reindex is measure preserving; erased sums exclude the diagonal; the incident-deleted i row vanishes; complements retain all other rows. No symmetry assumption used. |
| wd_product_row_second | 250–365 | Every coordinate is L2; diagonal products pull back the second moment; distinct coordinates use product independence; integrability precedes finite-sum integral exchanges. Cardinal N(N−1) handles empty and singleton index types. |
| wd_conditional_row_moments | 367–469 | Uses CanonicalTilt.section_contraction in the original μ-AE direction; under ρ, row mean squared is at most ε²R and row energy at most KR. Counts n−1 complement coordinates and n−2 off-diagonal companions; explicit n=1 boundary. R is measurable, nonnegative and L1 under μ. |
| wd_deleted_row_moment | 471–545 | Applies qualified all-size unit139 row_square_sum_moment at n−1, with unchanged L,K,ε and r, then reindexes. Includes original n=3/deleted size2 without invoking an n−1 window or an n≥3-only specialization. |
| wd_vector_integral_cauchy | 547–598 | Componentwise L2 products are L1; integral Cauchy–Schwarz followed by finite vector Cauchy–Schwarz yields the bound. No independence between U and V is assumed or required. |
| wd_mixed_row_cross_bounds | 600–1023 | Uses μ×ρ^(n−1) sections, the qualified cap–sqrt-energy bound, deleted-row moment, and vector Cauchy–Schwarz. The hlift construction establishes joint L1 from integrable section norm bounds before signed Fubini; no R², higher kernel moment or g²R moment. Exact pointwise identities and measurable transport return the estimates under H. |
| wd_scalar_deletion_bounds | 1026–1280 | All denominator/square-root positivity follows from n≥3; binomial identities and bounds are proved; a√n=x and nε²=4C²x² are exact. The numeric factors 4√2,16,24 follow from nonnegative multiplication and stated polynomial bounds. No division by s or x. |
| actual_quadratic_weighted_deletion_bounds | 1282–1548 | Consumes the actual h-derived g,r tilt interface; pointwise signed row-square identity and D1 difference use symmetry with the original √n(n−1) denominator. Unit141 transport retains exp(deleted sum)/m^n and m⁻¹≤2, not a renormalized partial law. Nonnegative integrals justify the factor-two comparison and summation over n. |

## Consumption interfaces completely read

- Unit139 `full_raw_contracts`: unordered_pair_sum_second_moment and row_square_sum_moment. In particular the row interface permits every natural size, not only size at least three.
- Unit140 `full_raw_contracts`: actual_quadratic_source_moments, with all let definitions, g/r regularity, μ-AE canonical rows, normalized density bounds/mass, residual second moment bound and actual full-tilt moment conclusions.
- Unit141 `full_raw_contracts`: finite_observation_partial_tilt_transport and actual_quadratic_partial_source_transport, including the complete signed/absolute/capped transport and original m^n normalization.
- Read-only `library/Shao/OQ6/CanonicalTilt.lean` section_contraction full public header at lines 294–330.
- Read-only ResidualDeletion eraseIncident and rowSum definitions plus full consumed rowSum_eraseIncident, unorderedPairSum_sub_eraseIncident and rowSqSum_sub_eraseIncident headers.
- Exact qualified CappedSectionEnergy source public header through line25. The source SHA256 3804881d178f23cf5059cb698a9a4a9657b8bfaf82e79ef2db272dafe8b73ed5 and independent review SHA256 98fea1b34856314bede26902e84c256f2936c98228d5a21b176736f90d1914bb were locally rehashed and match capped-qualified-evidence.json. Its accepted proof/object qualification is reused, not re-reviewed or re-executed.

## Original-source fidelity

Read original immutable p39 Section4 lines109–157, covering (8)–(14); p37 equations (1)/(17) and their observation-law interpretation; p38 lines41–74 with original-n deleted coefficients; scope01.md; and the full p54 repair note. The candidate proves the local weighted deletion part of p39 (11)–(13), with explicit constants and integrability, under the same finite second kernel moment and normalized actual projection. It does not prove the entire analytic budget (14), the probability engine, RS1/RS2, the physical Studentizer, any original root theorem or novelty. The source partial factor m⁻¹ is retained exactly. All roots remain OPEN.

The argument works at x=0, permits atoms and arbitrary exceptional μ-null rows, and does not discard zero-energy sections. The cap is min(|ag|,1); the proof needs only EμR≤s². Private s=0 cases use no division by s. Public s=1+sqrt(v) is at least one. No high moment, pointwise domination, density/nonlattice assumption or zero-Studentizer exclusion is introduced. p54's corrected uniform-moment and atom-safe probability payment obligations remain outside this unit; nothing here restores the false p-moment rate or claims a tail-continuity argument.

No source-level critical gap found. The complete parent-supplied packet has now been read, including all fifteen actual types, zero non-theorem values and all thirty-seven recursive AX entries; the detailed object ledger follows. No local/server Lean, audit rerun, source edit, network or spawned context has occurred.


## Exact mechanical evidence reused

The final source is 75057 bytes and the original object is 6260960 bytes. The parent-supplied source-bound producer receipt is SHA256 `3ab33c5a1755096b4a7786ca5c674bf9aca564211b95b4bd655d8029b73b95ca`, with direct exit 0. The producer compact file is SHA256 `18a88c58a059ad77865e37771b8f9f506d2fae07140fede6c0736512a96a036c`. Its 31 warning entries were read: deprecated spellings, style suggestions, unused assumptions/simp arguments, and the established Lake repository-local-changes notice. They contain no error diagnostic. Its strict wrapper success is FALSE and remains recorded as FALSE. The producer compact's exact protected-record field is 1842; this report does not substitute an informal descriptive count for that field.

The sole imported-object audit receipt is SHA256 `715fdf466967e5160569ec5ca197dddd139d2d4e0d0e9644649f955ffa3d7bb7`, direct exit 0; its compact SHA256 is `82a2a7121fd0c07d914dc4bbc678d9378da4e5ae1874fb6051b0b9b8a8af5abf`. The exact source/object binding matches the producer. Both exact before/after protected-record counts are 1846; all are preserved and all owned execution groups ended. The audit's strict wrapper success is FALSE because of the same 134-byte Lake notice, whose SHA256 is `11ec49f9906e54894a8ffa4551c841fd9873cf63f295722c88755032b40c3cbf`. This is not described as a strict-wrapper pass.

The audit template was fully read. It enumerates every constant whose module owner equals the public theorem's actual imported module owner, rather than filtering by a public namespace or source declaration list. It emits full `info.type`, all non-theorem definition/opaque values when present, the recursive `Lean.collectAxioms` result, and each constant kind/body-presence flag. The checker rejects any axiom outside propext, Classical.choice and Quot.sound. No source-proof re-elaboration is part of this imported-object audit.

The local metadata `lead-execution-01/weighted-owned-metadata-01.txt` was independently rehashed: SHA256 `1616090504b2789deae42785e9571e62f7518118ac49f668e009e556ee9f7fa3`, 161119 bytes, 2151 lines. I read every line, including every repeated expanded type instance, in the contiguous ranges 1–200, 201–412, 413–580, 581–808, 809–1043, 1044–1262, 1263–1463, 1464–1610, 1611–1748, 1749–1950 and 1951–2151. No dictionary substitution or omitted repeated type was used. The full inventory agrees with the audit compact, has fifteen unique names and fifteen TYPE blocks, contains no abbreviated-ellipsis marker, and ends with `OQ56_OWNED_COUNT 15`.

No Lean compilation, audit rerun, server/SSH/network access, mathematical source change or subagent delegation was performed by this reviewer. `weighted-ALL-LEAN-STOP.json` SHA256 `ed38bf52f071e62b92054759405a0b96d3f130facf3ff47daff62b305c34b946` remains binding; all further unit142 Lean is PERMANENT_STOP.

## Complete actual-owner coverage ledger

For every row below, the entire stated TYPE range and the preceding JSON/AX entry were read. Every declaration is `thmInfo`, `isTheorem=true`, and has a body expression. There are zero non-theorem declarations/values, so no VALUE body was omitted. Axiom lists below are the complete recursive lists for each owner; they sum to 37 occurrences. Names are printed in full to make coverage unambiguous.

| Actual owner | Metadata TYPE lines | Complete recursive axioms | Type/semantic check |
|---|---:|---|---|
| `_private.Shao.OQ6.WeightedDeletionMoments.0.Shao.OQ6.WeightedDeletionMoments.wd_insert_fubini._simp_1_3` | 2–4 | propext | Generated equality of universal-set membership with True; fully read. |
| `_private.Shao.OQ6.WeightedDeletionMoments.0.Shao.OQ6.WeightedDeletionMoments.wd_insert_fubini._simp_1_2` | 6–13 | propext | Generated dependent-pi-set membership equality with its full coordinate-membership proposition; fully read. |
| `_private.Shao.OQ6.WeightedDeletionMoments.0.Shao.OQ6.WeightedDeletionMoments.wd_mixed_row_cross_bounds` | 15–399 | propext, Classical.choice, Quot.sound | All assumptions, lets H/cap/E/rows/cross/Bdel and all integrability/bound conclusions agree with frozen Group C. No additional independence, moment or AE hypothesis. |
| `_private.Shao.OQ6.WeightedDeletionMoments.0.Shao.OQ6.WeightedDeletionMoments.wd_mixed_row_cross_bounds._simp_1_1` | 401–411 | propext, Classical.choice, Quot.sound | Generated real rpow-half equals sqrt type, with all arithmetic instances read. |
| `_private.Shao.OQ6.WeightedDeletionMoments.0.Shao.OQ6.WeightedDeletionMoments.wd_product_row_second` | 413–579 | propext, Classical.choice, Quot.sound | Full type over arbitrary finite J agrees with frozen Group B, including real-cast cardinal N(N−1), L2, both L1 statements and exact second-moment identities. |
| `_private.Shao.OQ6.WeightedDeletionMoments.0.Shao.OQ6.WeightedDeletionMoments.wd_scalar_deletion_bounds` | 581–807 | propext, Classical.choice, Quot.sound | Full type agrees with frozen Group D: C≥1, s≥0, n≥3, x≥0, a/K/ε/Bdel and all three numerical conclusions. |
| `_private.Shao.OQ6.WeightedDeletionMoments.0.Shao.OQ6.WeightedDeletionMoments.wd_deleted_row_moment` | 809–1042 | propext, Classical.choice, Quot.sound | Full all-n type, supplied complement equivalence, unchanged original tilt, row L2/M L1 and exact binomial bound agree with Group B. No hidden deleted-size≥3 hypothesis. |
| `_private.Shao.OQ6.WeightedDeletionMoments.0.Shao.OQ6.WeightedDeletionMoments.wd_deleted_row_reindex` | 1044–1244 | propext, Classical.choice, Quot.sound | Entire expanded complement/reindex measure-preserving type and both deterministic row-square identities agree with Group A. |
| `_private.Shao.OQ6.WeightedDeletionMoments.0.Shao.OQ6.WeightedDeletionMoments.wd_insert_fubini._simp_1_1` | 1246–1249 | propext | Generated preimage-membership equality; fully read. |
| `_private.Shao.OQ6.WeightedDeletionMoments.0.Shao.OQ6.WeightedDeletionMoments.wd_vector_integral_cauchy._simp_1_1` | 1251–1261 | propext, Classical.choice, Quot.sound | Second, separately owned rpow-half equals sqrt type; independently fully read despite repetition. |
| `_private.Shao.OQ6.WeightedDeletionMoments.0.Shao.OQ6.WeightedDeletionMoments.wd_vector_integral_cauchy` | 1263–1381 | propext, Classical.choice, Quot.sound | Entire type contains only component L2 assumptions on arbitrary U,V and agrees with Group C. No component-independence premise appears. |
| `_private.Shao.OQ6.WeightedDeletionMoments.0.Shao.OQ6.WeightedDeletionMoments.wd_insert_fubini` | 1383–1462 | propext, Classical.choice, Quot.sound | Entire μ×P insertion map, H and signed Fubini type agree with Group A, for every integrable f. |
| `_private.Shao.OQ6.WeightedDeletionMoments.0.Shao.OQ6.WeightedDeletionMoments.wd_conditional_row_moments` | 1464–1747 | propext, Classical.choice, Quot.sound | Entire type agrees with Group B and places its row conclusions directly under μ-AE. R is only L1 with its first integral bounded by s². |
| `Shao.OQ6.WeightedDeletionMoments.actual_quadratic_weighted_deletion_bounds` | 1749–2139 | propext, Classical.choice, Quot.sound | All assumptions and every actual h-derived let match the frozen public header; full m^n, original D1 denominators, signed identity, all three L1 conclusions and bounds retain their exact meanings. |
| `_private.Shao.OQ6.WeightedDeletionMoments.0.Shao.OQ6.WeightedDeletionMoments.wd_insert_fubini._simp_1_4` | 2141–2150 | propext | Generated product-set membership equality with its two component conditions; fully read. |

Thus the actual owned inventory is 15 theorems = 9 lexical source theorems + 6 generated theorems; 0 non-theorem values; 37 recursive AX occurrences, all within the exact whitelist. Four generated insertion simplifications use only propext; the other eleven declarations each use the three whitelisted axioms. No new axiom, sorryAx, unsafe/native_decide source escape or uncovered actual declaration was found.

## Mathematical justification and scope

Set N=n−1. On the original μ-AE good rows, CanonicalTilt gives a ρ-row second moment at most KR(o) and squared row mean at most ε²R(o). Independent tilted complement coordinates therefore give E(S²|o)≤N(K+(n−2)ε²)R(o) and E(A|o)≤NKR(o). The deleted vector T is a function of the complement and its L2 energy has bound Bdel obtained from the all-size unit139 interface at size n−1, using the same a-derived density. For original n=3 this is size two, which the interface explicitly covers.

Vector Cauchy–Schwarz gives E(|dot| |o)≤sqrt(NK Bdel)sqrt(R(o)); it permits dependence of the vectors r(o,Yj) and T(Y)j. The qualified capped-energy interface gives Eμ[cap sqrt(R)]≤a s from Eg²=1 and EμR≤s². The proof constructs joint L1 via section-norm bounds before invoking Fubini. In particular it never requires E(R²), E(g²R), fourth kernel moments or reverse transfer of a ρ-AE statement to μ.

Under insertion, S=ψi and cross=2 dot. Symmetry yields the exact original-length identity Λ²−Λdel²=ψi²+cross+Σj≠i rij², with the sign and every row retained. Dropping cap≤1 only on the two square terms, while retaining cap on the cross term, yields the private lambda bound. The exact original D1 difference is ψi/[sqrt(n)(n−1)]. The unit141 transport then gives each weighted original-law integral as m⁻¹ times the mixed-law integral. Since m⁻¹≤2, summing n identical numerical bounds and applying Group D gives precisely the public constants. Neither the partial density nor D1 is silently recomputed at n−1.

At x=0 cap is identically zero and none of these arguments divides by x. The private s=0 case also involves no division by s. Arbitrary atoms, diagonal values and μ-null bad sections are allowed; finite sums exclude self-edges and all integrated section facts are used in their stated AE direction. The original public s is 1+sqrt(v)≥1.

The result is a faithful local analytic formalization of p39's weighted deletion calculations (11)–(13), using the actual tilt and preserving p37(1)/(17)'s original full normalization. It does not close all of p39(14), any ordinary-measure bad event, RS1/RS2, the observation-space probability engine, physical Studentizer positivity, HG, an original OQ5/OQ6 root group, or C1/C2. It introduces no higher projection moment or pointwise kernel domination. p54's corrections and its atom-safe upper-tail payment remain intact and outside this unit. Probability-engine attribution remains with the named Shao–Zhou source, and novelty/priority is not certified here.

Qualified final review is complete for this exact source/object. No source repairs or premise changes are requested. No further mathematical review is needed merely because the unchanged artifact reaches integration; only an actual changed mathematical delta, uncovered interaction, or evidence gap would require new review coverage.


---

# Complete independent final review: unit142b CappedSectionEnergy

STATUS: CORRECT

QUALIFICATION: complete independent source-to-statement/proof and actual
owned-object type/value/recursive-axiom review, for the exact helper source
SHA256 `3804881d178f23cf5059cb698a9a4a9657b8bfaf82e79ef2db272dafe8b73ed5`
and original object SHA256
`88b2325773ef41d7256dbbd827eb13470dcac5c7a82337f50a14d498e184542c`.
This is helper-only qualification, not qualification of the complete weighted
unit142 theorem or closure of an original research root. All original roots
remain OPEN.

## Independence and method

Reviewer: `/root/oq56_capped142_review`. The initial author was
`/root/oq56_capped142_author`; the parent lead made the affected API repair.
This reviewer authored neither version, made no source edits, and did not
change a frozen premise or statement. Only the assigned review directory was
written. The math-theorem skill and current streamlined acceptance rule were
used; math-ultra was not used. Prescribed model/effort is gpt-6.1-sol/xhigh.
Actual model/effort and separate input, cached-input, output and reasoning-
subset token counts are UNKNOWN because the tool interface does not expose
them. No subscription percentage is inferred.

I completely read the final 90-line source proof, the frozen prelude and full
theorem type, all 8635 bytes of actual imported-object metadata, both complete
owned types with explicit instances and lets, and the audit source. There was
no type dictionary or omission of repeated subexpressions in this small
packet. Both actual owners are theorems; there are zero non-theorem values to
read. Compiled theorem proof values were not dumped or requested: all source
proof steps were read, and the exact successful object was audited recursively.

No Lean, server, SSH, network, local Lean probe, or repeated compiler/audit
command was run by this reviewer. The exact successful producer and imported
object audit are reused, as authorized. No accepted old proof body was
re-reviewed or changed.

## Exact source, freeze and server bindings

Final source:
`drafts/oq56/unit142/lead-execution-01/CappedSectionEnergy-repair02.lean`.
Local SHA256 was independently recomputed as
`3804881d178f23cf5059cb698a9a4a9657b8bfaf82e79ef2db272dafe8b73ed5`.
It is 3920 bytes, UTF-8 without BOM, with zero CR bytes and 90 LF bytes.
Its source declares exactly one theorem and no other top-level declaration.
The prohibited sorry/admit/axiom/unsafe/native_decide mechanisms are absent.

Freeze: `drafts/oq56/unit142/frozen-capped-energy-v1.md`, independently
recomputed SHA256
`605e497986dc39cff144677aa9870b7c8e3828a81dfc7bd8c33306f536443e85`.
The exact prelude and complete header before `:= by` match the frozen code
prefix after LF normalization, 762 characters on each side. This includes
every binder, premise, the result-level cap let and both conclusion clauses.
No premise/type change was made by the repair.

The source-bound producer compact record
`lead-execution-01/capped-producer-compact.json`, local SHA256
`177fac51af79eceaa28fa3e27a084750a2845ed89ff8c84652ba5c1c3636daba`,
binds:

- Server source: `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/Shao/OQ6/CappedSectionEnergy.lean`,
  same final source SHA256 and 3920 bytes.
- Original object: `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/.lake/build/lib/lean/Shao/OQ6/CappedSectionEnergy.olean`,
  SHA256 `88b2325773ef41d7256dbbd827eb13470dcac5c7a82337f50a14d498e184542c`,
  104512 bytes.
- Producer receipt: server `work/oq56/successor-unit142-01/CappedSectionEnergy/author-02/receipt.json`,
  SHA256 `4a1cf13311767380e32ecb580a5e32e8feb303eabcd09d68f6f6bba719bd09df`.
- Direct compiler exit 0; 1819 protected records preserved; owned execution
  group ended; further producer Lean is permanently stopped.

The imported-object audit compact record
`lead-execution-01/capped-owned-audit-compact-v1.json`, local SHA256
`26086aef36fd98117d86b5e4788252c21bd16224492125d3a9ddeb785e8c2875`,
binds the same final source and original object, direct audit exit 0, and
server receipt SHA256
`02208fa185156d328f38a6f2379eddd16add3adfca9d467ac057970dc7fc437d`.
It records 1822 protected records preserved, execution group ended, and
permanent stop of further cap Lean. These different protected-record counts
refer to the producer and later audit stages, respectively.

Both compact records have `strictWrapperSuccess=false`. Their direct exits
are zero, and their identified sole wrapper issue is the exact established
Lake package-local-changes notice, not a source error or diagnostic. The
producer compact binds stderr SHA256
`11ec49f9906e54894a8ffa4551c841fd9873cf63f295722c88755032b40c3cbf`.
The parent identifies this as the established 134-byte notice and reports no
source stdout/diagnostics. I distinguish that notice and strict-wrapper
flag from the successful direct kernel/audit exits; I do not relabel the
wrapper itself as successful.

Receipt-reuse boundary: the large original receipts and binary object remain
at their recorded server paths. I reviewed the supplied compact bindings and
the complete local metadata and recomputed local source/freeze/packet hashes;
I did not independently transfer or rehash those remote receipts or the
remote binary. This is deliberate reuse of the exact source-bound successful
artifacts, not a claim of a second server run.

The original source SHA256
`440a76f2144eca9d9f99687ec3bb474ca72fe7fa74bfd9c42660e53660671409`
and its failed elaboration remain preserved. The original failure is not
retroactively accepted. The final repair changes only measurable absolute
value via norm (final lines29-31), and the explicit pointwise goal conversion
before the absolute-value rewrite (final lines55-56). Both repaired source
steps were read in full and are mathematically valid. The earlier static
report remains an accurate CRITICAL_GAPS record for the original bytes.

## Frozen statement and actual imported types

`capped_sqrt_energy_bound` quantifies over arbitrary `Omega : Type u_1` with
only a measurable-space instance, a probability measure mu, measurable L2
real g with integral g^2=1, measurable nonnegative integrable R, s>=0 with
integral R<=s^2, and a>=0. With cap(o)=min(|a*g(o)|,1), it proves genuine
integrability of cap*sqrt(R) and its integral bound a*s.

The full actual type was read from `capped-owned-metadata.txt`, whose local
SHA256 is
`2d3e3414de458a709b8d25057e5b20d0a0c2109dac1ccbf2fb24e5931b10540e`.
Its explicit instances are the standard Real measurable, normed, ordered,
ring, and integral structures. Its L2 exponent is the ENNReal numeral 2;
the normalization and bound use real integrals and natural square powers.
No extra class, hidden domain restriction, weakened quantifier, alternate
measure, or different function enters. The type retains the literal cap let
(printed as `have cap ...;`) and the two-part And conclusion under the same
mu. The right-hand side is literally a*s. It matches the frozen full type.

The second actual owned type is
`Shao.OQ6.CappedSectionEnergy.capped_sqrt_energy_bound._simp_1_1`:
for every real x, real `x ^ (1 / 2)` equals `Real.sqrt x`. I read the entire
explicit type, including Real rpow, the real division 1/2 and all numeral
instances. This generated theorem is the simplification identity used for
the square-root/rpow conversion in final lines67-68. It has no extra premise,
and does not introduce an assumed helper, definition or axiom. Both actual
records have kind `thmInfo` and a present body expression; the main theorem
has universe parameter u_1 and the generated real identity has none.

## Complete final proof review

All theorem-local claims are covered below; no step needs a premise beyond
the frozen statement.

- Lines26-28 introduce the same cap let and unfold the result-level let by
  definitional equality.
- Lines29-31 show a*g measurable, then obtain the measurable cap using the
  measurable norm, Real.norm_eq_abs and min with 1. This resolves the old
  missing Measurable.abs API without changing the mathematical function.
- Lines32-37 show cap>=0 and cap<=a*|g|. The latter is min<=its first input
  and |a*g|=a*|g| under a>=0.
- Lines38-43 prove measurable sqrt(R), its square=R pointwise using R>=0,
  and sqrt(R)-L2 using the genuine integrability of R. No squared energy
  integral or exceptional-section integrability is postulated.
- Lines44-47 obtain |g|-L2, integrability of |g|*sqrt(R) by L2-L2 Holder,
  and integrability of the constant multiple a*(|g|*sqrt(R)).
- Lines48-51 multiply the pointwise cap inequality by the nonnegative square
  root, yielding the exact majorant after multiplication reassociation.
- Lines52-57 prove the claimed capped product integrable by domination with
  that already integrable majorant. Line55 explicitly changes the local norm
  goal into |cap(o)*sqrt(R(o))|<=a*(|g(o)|*sqrt(R(o))); nonnegativity then
  removes its absolute value. This resolves the old elaboration obstruction
  without assuming the desired integrability.
- Lines58-68 apply the standard integral norm Holder inequality at conjugate
  exponents 2,2 to g and sqrt(R). Norm=signed-real absolute value, squared
  absolute value=square, and the rpow/square-root identity convert it into
  integral |g|*sqrt(R) <= sqrt(integral g^2)*sqrt(integral sqrt(R)^2).
  Both required L2 premises have already been paid.
- Lines69-72 bound sqrt(integral R) by sqrt(s^2)=s using the frozen integral
  budget, monotonicity of sqrt and s>=0.
- Lines73-79 substitute integral g^2=1 and sqrt(R)^2=R, giving the actual
  integral |g|*sqrt(R)<=s.
- Lines80-86 combine the integrability conclusion with integral monotonicity,
  constant extraction, and multiplication of that budget by a>=0. This proves
  precisely the frozen conjunction. Lines88-90 close only the section and
  namespace.

The argument covers a=0, s=0 and pointwise zeros of g or R without division,
strict positivity, discarded atoms or tail-continuity assumptions. Globally
g=0 is already excluded by the stated unit second moment, not by a hidden
proof assumption. Arbitrary measurable and atomic probability spaces are
allowed; no topology, coding, standard-Borel structure, countable generation
or injectivity of a projection is added.

## Original source correspondence and use boundary

I read the full original p39 source in the preceding independent static phase,
and its complete source/statement correspondence remains applicable after the
two API-only changes. Binding:
`C:/game/shao/current/oq56/inputs02/p39.md`, SHA256
`251249839300f1c15b0c05cdb407167c7ab9f9a8b294e25747a3e1ef57d338a4`.
The exact source step is section4 lines141-145 below (11), also reused in the
cross-term argument at line151: the capped projection weight times the square
root of conditional residual energy costs at most the projection scale times
the residual scale. This helper proves that step by ordinary Cauchy--Schwarz.

For the intended application, R(o) is literally integral r(o,y)^2 dmu(y).
Only its first integral is needed. The accepted actual140 interface supplies
the same g/r/v/s definitions, measurable g, g-L2, integral g^2=1,
product-measurable residual-L2, mu-AE canonicality and v<=s^2 with s>=1.
The accepted CanonicalTilt.section_contraction interface supplies measurable
and integrable R, integral R=v, its budget and the mu-AE good sections.
Pointwise R>=0 follows from the integral of a square, including totalized
exceptional sections, without asserting all sections L2. The final142 range
x>=0,n>=3 makes a=x/sqrt(n)>=0. These are derived interfaces, not new final
premises. No residual fourth moment, R-L2, integrability of g^2*R, mixed high
moment, projection MGF or independence between g and R is used.

The accepted dependency interfaces, not old proof bodies, were read in full
in the static phase: ActualQuadraticTiltMoments SHA256
`f4772e78008aad28d89f99a6c52e63ba15329fab40c1b66fb41dc2ed3b249d10`
and CanonicalTilt SHA256
`6d7709cf90b9e746251155221788e634e3ded8ede2700cc34bdf86355165fa23`.
The full final142 public freeze, including every let, was read for scope,
SHA256 `f5a6e2a2b0ebac80cf8962cfb32c7742c53831b42dd4784ac61419a877f95ee7`.
The final142 implementation must still make the actual application and pay
its conditional/deleted row estimates, partial-tilt normalizer, integrability
and numerical-constant assembly; this helper does not certify those steps.

The full scope01 and p54 boundaries were also read in the static phase and
remain preserved. Their source SHA256 values are respectively
`5c8653d566857492d8c4f3da43ddd8f2b84a33f107132d3e61322735c2143052`
and `e03649e1324def02de3ff234bcc94c9e1cb643e074a324e1817ef940f5e01c43`.
No arbitrary polynomial rate for conditional p-moments, replacement of actual
large-remainder events by envelope events, continuity at atoms or missing
mixed fourth moment is imported. No probability-limit/engine step occurs in
this helper. Shao--Zhou attribution is retained; no novelty or historical
firstness claim follows from this elementary helper. All original OQ6/RS2/p53
and other research roots remain OPEN.

## Complete actual-owner and recursive-axiom coverage

Audit source: `lead-execution-01/capped-owned-audit.lean`, local SHA256
`bc5ecf45bbad6e556eb3d7249f43a8cce0d08b17befe417aeb5c7b6293f741bd`.
It imports the exact produced module and locates its module owner by the main
theorem anchor. It scans the complete environment and selects constants by
actual module index; it does not filter by namespace or printed-name prefix.
For every actual owner it calls recursive `Lean.collectAxioms`, rejects any
entry outside the whitelist, prints its full type with pp.all, identifies
its kind, and prints required definition/opaque values when present. Thus
private/generated owners could not be silently omitted by a name filter.

The complete local metadata independently parses to exactly two JSON owner
records, two full TYPE blocks, zero non-theorem records and zero VALUE blocks;
its terminal count is also two. No ellipsis/metavariable/sorry marker occurs.
The two names and theorem kinds match the compact inventory. Both full types
were actually read as described above; the non-theorem value obligation is
vacuous because neither actual owner is a definition or opaque constant.

Recursive axiom lists, fully read for each owner:

| Actual owner | Kind | Recursive axioms |
| --- | --- | --- |
| capped_sqrt_energy_bound._simp_1_1 | thmInfo | propext, Classical.choice, Quot.sound |
| capped_sqrt_energy_bound | thmInfo | propext, Classical.choice, Quot.sound |

There are six axiom-list occurrences in total, three distinct standard
axioms, and no non-whitelisted dependency or newly introduced axiom. These
counts are derived from the exact metadata, not copied from an older unit.
Body presence is recorded for both theorem owners. The full production source
proof plus exact-source original object binding and recursive audit supply
the required proof/object evidence without expanding tactic-generated proof
values.

CRITICAL_GAPS: none in the final exact helper version. It is qualified for
reuse at the two hashes stated above; any mathematical source change would
invalidate the affected review/check evidence. This report does not authorize
a new compiler run or claim that the strict wrappers returned success.
