# Unit145 C — final independent qualification

STATUS: CORRECT

QUALIFICATION: QUALIFIED_EXACT_SOURCE_COMPLETE

The current exact module `Shao.OQ6.UntiltedCompactCost`, with its sole public theorem `actual_quadratic_compact_source_cost`, is qualified. The complete original C proof/source-fidelity review and already reviewed split delta are reused; all eight subsequently affected proof ranges and every actual new owned type/axiom have now been completely reviewed. There is no uncovered source, type, required non-theorem value or transitive-axiom scope in this C module. This is an analytic compact-cost qualification, not an original OQ56/C12 root closure.

## Exact qualification binding

| Item | Exact SHA256 / scope |
|---|---|
| Current source | `a7ab6509e2008e568c8707d4d07b517bd94797218347589193e65f7242dca111`, 21450 bytes/388 LF lines |
| Current object | `643acbb122ef62fec01dc715cdf347f5c19c8e377e3548aceee4862c4ab210ff`, 2066272 bytes |
| Frozen module split | `fd6b4bbabdf97e370d3c8fdd5367f73d8e0f50f6f872a764a1e579236766cc51` |
| C frozen raw header | `a2c268c6b6997e378c2cee68e8b649a2e0881c0f01b7f9d690f5c59b55291719`, all24 lets |
| Complete original proof/source review reused | `c5d35edab9dfc4ee8518666328cbd07274446997c83784438cbdb44f1e5c523a` |
| Independent split/public-row API delta review reused | `6a3ab79d62b94e9934c917594f1d656104054c6dfa80314fe02a6c769a346bc5` |
| Current aggregate eight-range delta | `130c42e0565c05c49b4cecde09459b66a6265a6e1261b52e2f2d0b5b0bf15578` |
| Parent producer/audit intake | `2f9f49f57c4fb1df0b1c0c3ce0a069a673a6ba64b72a1012cb70e86e6ab00761` |
| Actual owned metadata | `e28cd7f5e543cf50153825a45b31c96fc4d2621af73911f8fe2eb139524af623`, 46676 bytes |

The current local source is `lead-repair-cost-cache-03/UntiltedCompactCost.lean`. Its complete seventeen-import/context prefix and complete C raw header are byte-identical to the split freeze. There is one source-public theorem, zero source-private declarations, zero new definitions and no private/mangled cross-module helper call. The theorem's mathematical assumptions and all24 typed definition values are unchanged.

## Complete current source coverage through exact reuse and delta

The same independent reviewer originally read every original C proof line and the complete immutable p37/p38/p39/p54/scope01 sources. That source-to-statement review remains bound to the exact original proof. The separately reviewed split candidate `2f87e56b9f3ce6b6ccce53e41cd60e827f65e2862ae0f8a60a8501b390a57b09` preserves it except for the previously reviewed public density-one row-energy specialization. Foundation is already qualified; no Foundation or139–144 proof/check replay was performed.

All three subsequent author repair sources and their complete provenance were inspected at the affected scope. Their exact byte chain is:

    2f87e56b… → 122c7dad… → 72bfb46a… → a7ab6509…

Independent whole-file replay verifies each stage against its before/after hashes, and independent aggregate forward and reverse replay verifies the final file against the eight exact changed ranges. Every old/new range text matches its stated line slice. All other source lines, including the header/context and unchanged proof steps, are exact. Thus the current388-line proof/source coverage is complete through the original full review, the split review and the present affected-range review; a second complete old-proof review was neither necessary nor performed. `source-delta-coverage.json` binds every current source line by SHA256 and distinguishes newly read affected lines from exact reused lines.

### Eight affected proof findings

1. **Lines171–173, projection L2 normalization.** The unavailable `MemLp.div_const` call is replaced by multiplication by `q⁻¹`, followed by multiplication by1+z. These ordinary scalar multiplications preserve the already available coordinate L2 fact under the original product measure. `div_eq_mul_inv` and `Function.comp_apply` identify the resulting function with exactly `(1+z)*(g(ξ_i)/q)`. This is definitional/scalar normalization, not an additional moment premise or changed projection. The subsequent projection-test L1 domination and projection bound consume exactly the same hproj2 type.

2. **Line238, binomial bound.** The bounded arithmetic uses only N≥3, `N(N−1)=2*choose(n,2)` and nonnegativity of `(N−2)²`. The desired difference satisfies `2*((N−1)²−choose(n,2))=(N−2)²+(N−2)≥0`. Thus the same `choose(n,2)≤(N−1)²` bound is proved, without introducing a new fact or changing the constant.

3. **Line246, row-energy polynomial bound.** After the unchanged binomial rewrite the target is `N(N−1)≤N²`, equivalent to N≥0. Restricting arithmetic to hN0 proves exactly that inequality and avoids irrelevant context expansion.

4. **Lines301–302, magnitude integral normalization.** Moving `integral_div` from a single rewrite occurrence into `simp only` normalizes both relevant division integrals. The preceding raw energy L1 fact still justifies integral addition; the original probability law gives mass1 for the constant term. The equality remains `EB=C0*(s/q+(EΛsq)/K)` with K=sN²q, without changing any denominator or integrability premise.

5. **Line304, correct addition side.** `add_le_add (le_refl (s/q))` applies the divided energy upper bound to the second summand, preserving the common first summand. Multiplication by C0 uses the existing C0≥0. This yields exactly the intended B magnitude bound; the earlier API-side error is corrected without a mathematical change.

6. **Line316, cap measurability normalization.** Adding `Function.comp_apply` unfolds the pointwise coordinate composition in the already measurable absolute projection, division by q, and minimum with the fixed cutoff. The cap remains literally `min(|g_i|/sqrt(n),1/(1+z))`; no zero cap, indicator or alternate law is substituted.

7. **Line382, final coefficient inequality.** The restricted arithmetic uses only C0≥0,z≥0 and C0z≥0. The coefficient difference is `16(1+C0)(1+z)−(3+6C0z)=13+16C0+16z+10C0z≥0`. The prior steps separately use s≥0 and q>0. No stronger constant or range assumption is hidden in the tactic restriction.

8. **Line384, total source cost.** `add_le_add (le_refl Lcompact) hres` adds the same Lcompact to the residual inequality on the correct side. It proves the frozen `sourceCost≤Lcompact+16(1+C0)(1+z)s/q` conclusion directly, without changing the definition of sourceCost or dropping its projection term.

All affected normalization, algebra and arithmetic are correct. The final successful kernel check independently closes the pinned-API/elaboration uncertainty that was explicitly pending in prior stages. Earlier failed candidates/receipts remain historical evidence; the missing root import was an execution-availability issue and is not used as a mathematical premise or result.

## Literal actual type/value/axiom coverage

The complete current metadata was read, including every entry field, all nine full type strings, every name component/universe/kind/body-presence field and every axiom list. All512 TYPE lines were literally emitted and read with entry-local line numbers: source type1–413, then all99 lines of the eight generated types. No type was summarized, truncated, pattern-inferred or accepted from a descriptive count. Recorded type SHA256, UTF-8 byte count and line count were independently recomputed for every entry and all matched. `actual-owned-coverage.json` contains512 individual line hashes and complete coverage flags.

The actual inventory derives nine unique `thmInfo` constants, all with proof expressions: one source theorem and eight generated theorems. There are zero actual non-theorem constants and therefore zero required FULLVALUE payloads or lines. `non-theorem-value-inventory.json` records the explicit empty inventory. This zero is established by inspecting all nine actual kinds/isTheorem flags and the audit's value-emission logic, not by treating an absent value field as evidence that a definition has been checked.

### Actual public C type

The source type has SHA256 `c270b2a43d2c66bc6a3f61c1e8729bc8d9b6131509a17b27781206977b2a2b71`, 32040 bytes/413 lines. Its complete expanded binders retain only the frozen measurable symmetric pair-L2 centered h, unit actual projection second moment, n≥3,z≥0,C0≥0 and the probability-space instances. There is no new h moment, RS/window/scale condition, mixed moment, atom restriction or zero-energy exclusion.

All24 actual let values agree with the frozen meanings: actual projection/residual/v/s; original μ^n; the literal truncation test and retained Lcompact; the literal compact cap; original and erased pair sums/rows/energies; unchanged original-n numerator denominators; A/Adel and B/Bdel with the same deterministic term and sN²sqrt(N) denominator; deletedTest, residualCost and sourceCost. The complete final conjunction preserves every raw Integrable family, the exact iid Lcompact identity, 0≤Lcompact≤(1+z)², and both unconditional analytic cost bounds. In particular, the final constant is exactly16(1+C0)(1+z)s/sqrt(n).

### Actual generated types and all axioms

Every generated item is under the actual C theorem, not Foundation. The complete generated statements were read with all stated algebraic hypotheses. Their order and line coverage are:

| Actual suffix | TYPE lines | Complete statement meaning | Transitive axioms |
|---|---:|---|---|
| source C | 413 | Complete frozen actual-kernel compact-cost type | propext, Classical.choice, Quot.sound |
| `_simp_1_6` | 24 | Natural power of nonzero a is nonzero under the stated reduced monoid-with-zero hypotheses | propext |
| `_simp_1_2` | 7 | `2=0` equals False under its NeZero instance | propext |
| `_simp_1_5` | 8 | Product of two nonzero elements is nonzero under NoZeroDivisors | propext |
| `_simp_1_1` | 10 | Real exponent1/2 equals Real.sqrt for every real input | propext, Classical.choice, Quot.sound |
| `_simp_1_8` | 16 | cast(n)+1 is nonzero under the stated CharZero additive structure | propext |
| `_simp_1_7` | 20 | Integer power of nonzero a is nonzero in a group with zero | propext, Classical.choice, Quot.sound |
| `_simp_1_4` | 7 | The corresponding NeZero fact for4 | propext |
| `_simp_1_3` | 7 | The corresponding NeZero fact for3 | propext |

All nine axiom lists were read completely. They contain15 occurrences, with distinct set exactly `{propext, Classical.choice, Quot.sound}`. No sorryAx, new/custom axiom, unsafe escape or desired-cost hypothesis occurs. All source and generated items are covered; no definition/opaque body is outstanding.

## Actual owner selection and source-bound server receipts

The complete2739-byte/62-line audit source was read at `lead-repair-cost-cache-01/actual-compact-source-cost-owned-audit.lean`, SHA256 `988b36a29edcb730d3b82fd5a4ea23de4ee50260e1b1ea468a6729dbf4cf4d3c`. It imports the current cost object and obtains `getModuleIdxFor?` from the new C theorem, then selects every constant with exactly that module index. It neither filters by namespace/name nor treats Foundation's identical namespace as ownership. The already accepted Foundation has another module index and is correctly excluded. The audit prints every full type with pp.all, gathers each transitive `Lean.collectAxioms` list, rejects non-whitelist axioms, and prints full definition/opaque values when such constants exist.

The existing receipt/config read-only binding `audit-source-binding-existing-receipt.json`, SHA256 `274fcde7dd4d4841c2622b6ed4311128e066ec907c5649bd68c361542fc1cfe8`, confirms that this exact audit source equals the original config source, saved input copy, and both before/after protected physical fingerprints. It binds config `a7fa8b15daeba603fedf4b318db063928034fd0aaf7b4d0460727f53fc121afa` to the same audit receipt and exact owned source/object. It records actual audit mode, no `-o`, own-object import, full SHA/bytes/ns source/object checks, CPU22–25, M8192/j4, direct0, preservation and ended status. Supplying this missing source-provenance extraction required no new Lean check or old proof review.

The kernel projection `523d6114e1733b70916f0b2cfb0eb6d90efab4b1becd8a95927732ec18de8a15` binds the exact current source/object to producer receipt `3822fd32de3a171020e0ef8b1fb080cbf377bd65e7eb708627cc9b1ad59a49eb`: actual direct0 in13.453898957s, all2915 protected physical records preserved, execution ended and no errors. The complete2195-byte stdout text in the projection was read and independently reproduces SHA `deecef0d727677b62948e9ab6132b15350593e08adc9e2473bc1eb63a88e5710`. Its11 actual warning headings are style/deprecation/linter diagnostics. The known134-byte Lake notice is retained at SHA `11ec49f9906e54894a8ffa4551c841fd9873cf63f295722c88755032b40c3cbf`.

The audit projection `578ede2a58594c7519e735c8151c22feb0875ab93d16d61aec0d787b9114b915` binds the same source/object and full metadata to receipt `8b4c109305c8c112a2f7e7ed493b7109824a6b5a006b2bf69107a823d1917e01`: actual direct0 in5.178615753s, no `-o`, all2925 protected records preserved, execution ended and no errors. Metadata's receipt binding matches; its original41991-byte stdout is bound by SHA `a50c25fd9b3d26227fcae830eab0323be04ebcaab547bf0f11679293aa629818`.

Both strict-wrapper-success fields remain false and are disclosed; they are not mislabeled as strict success or empty diagnostics. The project accepts the actual direct0, exact object/source, preservation and complete audit results with these known nonfatal warnings. No warning cleanup or unchanged check replay was done. The reviewer performed no fresh server/network/object probe, compilation, cache action or binary/log download; the saved exact source-bound receipts were reused.

## Source fidelity, scope and release

The complete original source-to-statement review is retained: this is precisely p37(2)'s original-product-law continuous-weight compact analytic cost. The actual cap remains nonzero at z=0, L1 remains in Lcompact, deletion keeps the original n coefficients, actual s=1+sqrt(v) is positive, and all L1 obligations are real conclusions. The previously reviewed argument needs no E[g²R], ER², higher kernel moment or independence between dependent conditional vectors. n=3, z=0, C0=0, v=0, null sections and cutoff atoms remain covered.

The result does not pay actual numerator/denominator bad-event probabilities, H/G failure concentration, physical Studentizer-zero probability, clipping/physical transfer, threshold/coding limits or the named Shao–Zhou probability theorem. p54's fixed-p uniform-moment repair, strict margins and atom-safe argument remain unchanged, as does external-result attribution. No priority, original OQ56 root closure or C12 closure is claimed.

Current root state is preserved specifically: OQ56 and C12 remain OPEN; OQ3 remains PAUSED_BY_USER; the separate limited original-OQ4 accepted scope at9fd4cd61 is preserved and is not overwritten by historical all-open wording. This review changes only the acceptance of the current C analytic module.

Only this new `stage4-cost-final/` directory was written. Author/reviewer separation is preserved: the parent authored the repairs, and this same independent reviewer did not modify a proof. Reviewer Lean/server/network/Git/cache/API/installation/child/chat/goal/automation actions are all zero. Requested model/effort is gpt-6.1-sol/xhigh; actual model/effort and separate input/cached-input/output/reasoning-subset counts are not exposed and remain null.

Final state: QUALIFIED_EXACT_SOURCE_COMPLETE for sourcea7ab6509…/object643acbb1…. All required current C coverage is complete, with no remaining review gap. Writer/execution release is exact, zero in flight. The lane coordinator may consume this qualification and the saved producer/audit receipts at integration; no unchanged old-unit or Foundation replay is requested.
