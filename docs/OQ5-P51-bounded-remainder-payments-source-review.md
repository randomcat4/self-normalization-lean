# Unit 197 independent SOURCE review

STATUS: CORRECT

This is a complete independent source-to-statement, assumptions, and proof review of the source below. It is **SOURCE_ONLY_NOT_QUALIFIED**: unit197 `qualified=false`, `actualOwned=UNKNOWN`. No unit197 kernel, original-object, actual-owned declaration, or axiom pass is asserted. Mathematical correctness of the five source proofs is separate from the pending machine qualification.

Reviewer: `/root/oq56_remainder197_final_review`, fresh context distinct from the author `/root/oq56_remainder197_stage1`. Parent is OQ56 lead `01a16c48-9017-7d50-8123-83c72763be0f`, not the Root coordinator. Prescribed model/effort: `gpt-6.1-sol/xhigh`; actual introspection UNKNOWN. Input/cached-input/output/reasoning-subset usage are all null. Writes are confined to this review directory. Lean/AX/server/network/Git/API/upload/cache/child calls: zero.

Source: `drafts/oq56/unit197/author-01/stage2/BoundedRemainderPayments.lean`, SHA256 `c0102fa13835fb22b01148e42d66cf8ff5704d682b9a6142eb508d7172d95cc9`, 28173 bytes, 523 LF, CR0/BOM0. Author manifest `b4750d4cb78a674182fe9278d8ef733e1b4cae68191625e24019e60d61e2bf1a` and RELEASE0 `6f6f760586bfdb681bba883f556d15a6b79da2f8aa3cc43b72c5198524d62b4a` were checked. The original 13 Stage2 payloads and 15 Stage1 payloads are preserved. The complete source and all five proof bodies were read, including every ordinary typed Prop helper and every branch; exact duplicate views were checked against their byte spans.

## Scope and frozen interface

The mathematical freeze is `parent-freeze-v1.json`, SHA256 `d67253825646f92c3c681181d84466ded3cfccc8f81eba0c98e0d4229aaaee6b`, 107211 bytes. Its complete 11 heads, six global RHSs, 13 chronological frame commands, two closures, 19 anonymous expression shapes, two local probability-instance initializers and all source digit positions agree with this source. Freeze preceded implementation. Neither this reviewer nor the later annotation repair changes a mathematical assumption, declaration, initializer, proof, or source byte.

The original p51 (355 lines), p54 (86 lines) and p44 (180 lines) were read completely from their read-only source inputs. Their exact hashes are respectively `96920f428b8fc09788a6388103cefe398e3ec739129a5922b984babd09e99359`, `e03649e1324def02de3ff234bcc94c9e1cb643e074a324e1817ef940f5e01c43`, and `3d6a674252a81b7ca051fd54aa0a621511ebce94af2f0bdf9b4eca8715bc5239`. The claim reviewed is precisely p51 S15's last three payments in the bounded-product branch, obtained from S16 and actual centered-jackknife S17 geometry. It is not the missing S11 payment for the complement of Gy, the entire S15 estimate, the signed-coding or compact-tail engine, the DC branch S18, or a root completion. p51's candidate label and p54's correction of the excessive conditional p-moment-rate claim remain intact. Published Shao–Zhou inputs retain their attribution.

## Definitions D01–D06: CORRECT

Lines19–23 define a total real constant

`c = min(1, min(1/[32(K+1)(t0+1)], 1/sqrt(32(Cg+1)(1+sqrt(t0)+t0))))`,

where the existing actual `Cg = studentizerGeometryScale K = 200(1+K+sqrt K)`. No hidden local alias or selector is introduced in Lean. Definitions D02–D04 (lines26–44) are exactly the strict events `{d < -1/2} ∩ Gy`, `{V/4 < y|D|} ∩ Gy`, `{1/4 < y²|d|} ∩ Gy`. The second event has the original absolute value on D; the first event deliberately has signed d. D05 (lines47–51) fixes `(E1 ∪ E2) ∪ E3`. D06 (lines54–58) fixes `(μ.real E1 + μ.real E2) + μ.real E3`, rather than a union probability. Their general functions g,r and total definitions are consistent with the frozen statement.

## D07, lines61–84: CORRECT

K≥0 and t0>0 imply Cg≥0, K+1>0, t0+1>0 and A=1+sqrt(t0)+t0>0. Thus both denominators 32(K+1)(t0+1) and sqrt(32(Cg+1)A) are strictly positive. Each of the three terms in the nested minimum is positive. `lt_min`, `one_div_pos`, and the two nested `min_le_right` projections give exactly c>0 and its three upper bounds. The proof establishes positivity rather than assuming it, and remains valid at K=0. The nonlinear arithmetic after unfolding Cg only uses its explicit existing RHS and sqrt K≥0.

## D08, lines87–324: CORRECT

All premises are the frozen pointwise ones: n≥4, K≥0, t0>0, y≥1, y≤c n^(1/6), symmetry of r, the same actual |F|≤Knq and row-norm²≤Kn²q bounds, and membership in the actual Gy. There is no probability or desired-small-remainder premise. The parameter q is the actual old definition `boundedPolylogMomentOrder t0 n = t0 * Real.rpow (n:ℝ) (1/3:ℝ)`.

For explanatory algebra only, write N=(n:ℝ), a=N^(1/6), b=N^(1/3), q=t0 b. The implementation creates none of these as new data. Lines107–139 prove N≥4>0, sqrt N>0, a,b>0, b≥1, a²=b, a⁶=N, b³=N and a³=sqrt N. The last identity uses a complete Prop-only uniqueness fact: two nonnegative reals with equal squares are equal, by `(s-t)(s+t)=0`. Both factors' branches are handled. Thus no sign ambiguity is hidden in taking square roots. The real exponents 1/6,1/3 are explicitly real; the powers 2,3,6 here are Nat powers. `rpow_eq_pow` only bridges existing notation, `rpow_natCast` converts Nat powers, and `rpow_mul` is used under N≥0. There is no use of a real-power identity on a negative base.

Lines140–164 establish q≥0, q/N=t0/b², and sqrt(q/N)=sqrt(t0)/b. The division identity uses N≠0 and b²≠0. The square-root equality compares two nonnegative sides, squares both using q/N≥0 and t0≥0, and applies the same uniqueness fact. It does not assume an unrestricted square-root multiplication or division formula.

Lines165–182 import D07 and actual qualified196 bounds. V>0 is obtained first from `projectionGood_bounds`. The old `bounded_studentizer_geometry` is then used twice with q≥0, n≥4, y≥1 and exactly the supplied F/row/Gy premises: its second conjunct gives |D|/V≤4Kq/sqrt N and its fourth gives |d|≤Cg(y/sqrt N+sqrt(q/N)+q/N). The source's `.2.1` and `.2.2.2` projections match the fully read actual conjunction type. There is no circular denominator-positivity assumption.

For the numerator (lines183–205), multiply by y≥0 and use a²=b and a³=sqrt N to get

`y|D|/V ≤ 4 K t0 (y/a) ≤ 4 K t0 c`.

From c·32(K+1)(t0+1)≤1 and c((K+1)(t0+1)−Kt0)≥0 one obtains 4Kt0c≤1/8. The source's explicit polynomial certificates suffice; it never cancels K, so K=0 is covered.

For the denominator (lines206–271), nonnegative squaring/cubing of y≤ca gives y²≤c²b and y³≤c³sqrt N. Consequently

`y³/sqrt N ≤ c³`,
`y² sqrt(q/N) ≤ c² sqrt(t0)`,
`y² q/N ≤ c² t0 / b ≤ c² t0`.

All three divisions use previously proved strict positivity, and the last comparison uses b≥1 and c²t0≥0. Since 0<c≤1, c³≤c². After expanding the three terms, the bound is `y²*(y/sqrt N+sqrt(q/N)+q/N) ≤ c² A`.

Lines272–301 square the nonnegative inequality c sqrt(32(Cg+1)A)≤1, giving `32(Cg+1)c²A≤1`. The explicitly supplied nonnegativity c²A≥0 gives `Cg c² A≤1/32`. Multiplication of the old |d| bound by y²≥0 is valid; multiplying the three-term estimate by Cg≥0 yields y²|d|≤1/32. Finally y≥1 gives y²≥1, so |d|≤y²|d|≤1/32. Lines323–324 return exactly all four required conclusions: V>0, numerator ratio≤1/8, scaled absolute d≤1/32, absolute d≤1/32.

These estimates are finite inequalities throughout n≥4. No little-o statement, additional asymptotic threshold, square-root branch choice, or hidden stronger hypothesis is substituted for the complete proof.

## D09, lines327–393: CORRECT

The actual193 `bounded_scales_pos` has six right-associated positive constants; its final `.2.2.2.2.2` is indeed tailScale M>0. With K equal to that same tailScale, qualified195's `not_mem_boundedProductFailure_iff` turns nonmembership into the exact Qw/F/row nonstrict bounds. The proof uses the actual F and row bounds in D08; the first Qw bound can remain unused without changing the failure event. The parameterized local fact hSmall returns only a conjunction in Prop, not a selected sample or data object.

For any x in E1 outside that failure event, Gy and hSmall imply |d|≤1/32 while `neg_abs_le d` gives d≥−|d|≥−1/32. This contradicts the original strict d<−1/2. For E2, hSmall gives V>0 and y|D|/V≤1/8; multiplying by positive V yields y|D|≤V/8<V/4, contradicting E2's strict comparison. For E3, y²|d|≤1/32 contradicts 1/4<y²|d|. The three `Classical.byContradiction` uses return proofs of membership only. They do not introduce data choice, any extra local instance, or a source assumption. Splitting the fixed union as `(hx | hx) | hx` gives the fourth inclusion into the very same failure set.

Original strict boundaries and absolute values are preserved. Equality atoms in the old concentration good bounds or the bad-event thresholds require no probability-zero or continuity assumption; the explicit numerical margins separate them.

## D10, lines396–456: CORRECT

All old finite-probability eligibility remains present: probability ν; R,M≥0; product measurability and integrability of r; both a.e. canonical integral conditions; a.e. 0≤w≤R; integrability and M-bound of w²; a.e. product envelope; q≥2; symmetry; 2R²q≤n. The new n≥4, t0>0, y≥1 and small-window conditions are explicit. The old `canonical_bounded_product_joint_failure` is called with q exactly q0, with all arguments in the complete actual type's order. It supplies the failure probability ≤3 exp(−q0); this conclusion has not been relisted as a premise.

The frozen local instance `instSample` is the existing finite Pi probability instance specialized to constant ν on Fin n. It follows from the already bound IsProbabilityMeasure ν and adds no model qualification. The read-only full actual `sampleLaw` RHS is that same `Measure.pi` law. `MeasureTheory.measureReal_mono` requires the target measure to be finite and has a default `by finiteness` proof; that is justified by this probability instance. It has no measurability premise on E1/E2/E3 or their union. Thus arbitrary g in this local payment statement is valid: arbitrary sets are measured by the measure's underlying outer measure, and finite-measure `toReal` monotonicity applies. No hidden measurable-g assumption or proof of S11 is obtained from that fact.

Four exact inclusions give three individual bounds and the direct union bound, all with factor3. The arithmetic sum of the three real inequalities gives factor9 for D06. No disjointness or independence of bad events is used. In particular the factor3 union bound is not mislabeled as the factor9 S15 sum payment.

## D11, lines459–520: CORRECT

The quantifier order is preserved: fixed C,a,t0,M and signs, then eventual n, then all Ω/mΩ/ν/hν/g/r/w/eligibility and y/window inputs. The proof intersects only `eventually n≥4` with the old qualified195 eventual joint-failure theorem; it introduces no threshold selector or model-dependent choice. The old eventual actual type has precisely its model eligibility universally quantified after n, and hAll is called with those same inputs. It supplies the exact same failure bound. The same probability-instance specialization, four inclusions and finite outer-measure monotonicity then apply at the chosen n, and the sum is9 while the union is3. C,a only control the old polylog height; the c window depends solely on tailScale M,t0. Functions and laws may vary with n under this formulation. No hWindow or hq proof missing from D10 is assumed here: the already qualified eventual producer directly supplies the probability conclusion.

## Complete data, helper and source-interface review

All 78 complete typed Prop headers and their complete source proof context were read. Parameterized `hNonnegSquareUnique` and `hSmall` have proposition-valued results. No new named real/function let, choice, selected data branch, global instance, or extra anonymous data expression was found. The two `letI instSample` occurrences are the only new source local instances and exactly match the prior contract. The 19 shapes consist of the three global set predicates, existing uncurry/section/square/constant-marginal forms and six existing implicit Pi family specializations. Binder a:Ω in an integral does not capture outer real exponent a in D11; ν,mΩ,hν are inherited from the exact model telescope. The source's sole universe u, autoImplicit=false, namespace, noncomputable section, opens/imports and closures match the frozen chronological frame.

`resolved-helper-scopes.json` records all 78 headers and exact proof/availability ranges. In particular hZero is local to hNonnegSquareUnique through line106; hLeft0,hRight0,hLeftSq,hRightSq are local to hsRatio through line164; hBounds is local to hSmall through line358. The other six helpers in inclusion-proof branches end at368,379,387 as appropriate. No inner proof variable or sample escapes its own branch. Ordinary complete Prop-only facts and proof branches use the project exemption correctly.

The complete selected actual interfaces of qualified188,190,193,194,195 and196 were read, including all32 TYPEs (502 lines), all24 non-theorem FULLVALUEs (218 lines), name components, universe levels, body presence and recursive axiom lists. Their selected blocks equal the direct actual metadata exactly. This reuses the old qualified independent reviews and source-bound original-object/kernel/AX receipts; it does not rereview old complete proofs or rerun old compilation/audits. The 196 compatibility overlay is `603ea9daf35ffed1396b8616e0eff242f353c3efee8641fd9afb659ab7b4c91d`; its15 selected entries are the11 actual definitions plus D12/D18/D21/D22. Qualified196 source is `bc64d3e11a64f62ad654305ce579c1779546d4df37b5593090105af910502edc`, first successful original O `372a857054f7f77a5502fb8b5631c780b55fb0694db7ebc5a6789b9161bf8be3`, qualification `612a44bc0a5fb74bfbdda2af2c9cc4e286592c86cf4033f2ebb2e204796fdb95`. Qualified195 source is `3f3d699297f33685dad57eed265727d538dac2ff5812966dc97093f6b0f5f169`, original O `dceb8eac886963e6d2e6f9816af61dc1918ffb7f6bdeb320ea280b12d1bb9353`, qualification `9e9f993f33102eb83c9a1a3d2a6e8c12269937b63b8077d4ca641e43025715bb`.

Actual188 originalRows erases only index i=j; actual190 originalUpper retains all i<j pairs. Repeated observations x i=x j for i≠j are retained. No r(o,o)=0, atomless law, independent g/w, standard-Borel space, higher g moment, or mixed fourth moment is added. The sampledKernel diagonal remains unchanged in196; the original centered finite-row construction supplies its own index-diagonal treatment. The actual193 constants confirm rowTailScale=8 exp(1)²(4M+8)², whereas 64(M+1) is commonMomentScale. The sealed expository correction preserves the formal tailScale max chain.

The22 selected pinned Mathlib raw declarations were read with complete imports, prefixes and65 chronological scope rows, followed by all5 supplemental existing contexts. Exact raw-file/slice hashes were checked against preserved full raw files. Real rpow notation, NNReal/Real sqrt domain, measureReal_mono's target-finiteness requirement, Pi initialization and both Pi finite/probability instances match the uses above. The supplemental MeasureSpace/finite-volume instances impose no new MeasureSpace requirement on this source. All selected old recursive axiom lists stay within propext, Classical.choice, Quot.sound. That does not certify new unit197-generated declarations, whose actual inventory is still unknown.

## Independently found annotation defects and explicit resolution

The original numeric annotation counted8 digits in `z.1`/`z.2` at lines409/473 as real literals. They are Prod projection-field syntax; their selected terms have type Ω from z:Ω×Ω. The exact byte offsets are21118,21122,21133,21141,25065,25069,25080,25088. The correct interpretation is86 arithmetic literals=12 Nat+74 Real, plus8 separate syntax-field positions, retaining all original94 source digit positions. The additional262 proof-literal positions were individually verified; none is field syntax. The four hsRatio inner helper scope descriptions were also overbroad; the six explicit nested-scope entries are now bounded exactly (including previously qualitative hZero/hBounds descriptions).

Parent wrote `parent-metadata-overlay01-field-syntax-and-nested-prop-scopes.json`, SHA256 `2cbf0b6fdfb094d94d1d7aafb46ff6df151dc3656d5c47b57f46e99fc2ac1496`, 62714 bytes, before any197 server gate. I independently fully confirmed all8 corrected syntax entries, unchanged86 numeric rows,6 local proof boundaries and source hashes. The exact half-open scope ends, including each source LF, are hZero line106/byte4585; the four hsRatio facts line164/byte7713; hBounds line358/byte18887. The overlay explicitly supersedes only affected annotations/claims in the old freeze, maps and parent intake; their original bytes remain preserved. It adds no new mathematical data, premise, choice, selector, instance or proof change. These annotation gaps are resolved for this effective SOURCE review; they are not silently ignored or confused with a mathematical proof repair.

Parent then wrote `parent-metadata-overlay02-complete-nested-branch-scopes.json`, SHA256 `2db2e85d44251a7439e6304a580b876f49213893414abdd613f5b43abf19a8f9`, 20469 bytes, also before first native. I fully read and independently confirmed all12 effective nested/branch records: the additional six branch facts end at line368/byte19326, line379/byte19860, line387/byte20200. Overlay02 explicitly supersedes the overbroad all-other-scope assertion in Overlay01 for these branch facts. Both overlays and old originals are preserved, source and mathematics unchanged.

Independent deterministic readback has2130 effective checks with zero failures and157 exact local bindings. Two preliminary reviewer-comparator conventions were preserved as diagnostic files: the source header span includes one ASCII space before `:=`, while completeTypedHeader canonically omits it; lexical-scope endpoints include the terminal LF. Their initial overly strict comparisons were corrected and all affected bytes independently rechecked. These diagnostics did not run Lean or mutate source/parent evidence. Static readback supplements, but does not constitute, the mathematical reasoning in this report.

## Boundary cases and remaining qualification gap

D01–D06 remain total at n=0,1,2 (and3) under the imported total real divisions/powers/sqrt. No old source denominator identity is claimed there: D08–D10 explicitly require n≥4 and D11 intersects that eventual condition. At n=0 projectionEnergy=V=0 and Gy is empty; there is also no legal y≥1 window. At V=0 the actual196 d branch is0; Gy excludes V=0 by projectionEnergy≥1/2 and the actual V² identity. All divisions in the substantive geometric argument occur after positivity is proved. K=0, y=1 and threshold equalities are explicitly covered. No loss of repeated samples, diagonal index distinction, signed d, absolute D, or equality atoms occurs.

There is no remaining critical mathematical gap in the reviewed exact source and its frozen intended scope. There remains a mandatory **unit197 machine-evidence gap**: a designated-server successful native check on this exact c010 source, followed by a SAME FIRST successful original-object audit of every actual module-index-owned declaration without namespace/prefix filtering, complete TYPEs, every non-theorem FULLVALUE, name components/levels/body flags, and recursive axioms. Actual owner counts must be derived from that object, never guessed here. On receipt, this same independent context must review those exact artifacts in a new actual-machine subdirectory. If first native fails or a proof changes, preserve failures and rereview only the affected complete changed proof/evidence; unchanged accepted old producers need no replay.

Original C1 immutablev85 stays complete; C2/C12/OQ56 remain OPEN; OQ3 remains PAUSED_BY_USER; p54 repairs and external attribution are preserved; unified124 is not a prerequisite. The next mathematical dependency after this limited payment unit remains actual Gy-complement S11, including its self-normalized exponential upper-W tail. This report does not close it.
