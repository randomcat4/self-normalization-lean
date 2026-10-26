# Independent complete SOURCE and mathematical proof review — unit 194

STATUS: CORRECT

SOURCE_REVIEW_COMPLETE: true

QUALIFIED: false

ACTUAL_OWNED: UNKNOWN

The frozen source has a complete, mathematically correct proof of the four stated deterministic results. I found no critical mathematical gap, changed assumption, circular premise, unplanned data value, or source-to-statement scope expansion. This is the independent complete SOURCE verdict. It is not a Lean acceptance or a final machine qualification: the exact-source native receipt and the same-original-object complete owner/type/value/component/recursive-axiom packet have not yet been supplied to this reviewer.

Reviewer: `/root/oq56_polylog194_final_review`, a fresh context separate from the author role `/root/oq56_polylog194_stage1`. Parent is the OQ56 lane lead `01a16c48-9017-7d50-8123-83c72763be0f`, not the shared root coordinator. Requested model/effort are `gpt-6.1-sol` / `xhigh`; actual runtime introspection is `UNKNOWN_TOOL_NOT_EXPOSED`. This review writes only `drafts/oq56/unit194/final-review-01/`. Reviewer Lean, remote, network, Git/API, upload, cache, heavy, and child execution are all zero.

## Exact source and authority

The source reviewed completely is `drafts/oq56/unit194/author-01/stage2/BoundedPolylogWindow.lean`, SHA256 `416a3f8e7f41341a36fc5fea6923308cd09d96a195192f1d4ef7e247d72f520a`, 9692 bytes, 215 LF characters, strict UTF-8, CR0 and BOM0. All 215 lines, including nine imports, commands, three definitions, all four theorem statements and proof bodies, and both closing scopes, were read. The production module is `Shao.OQ5.P51.BoundedPolylogWindow`; its declared namespace is `Shao.OQ5.P51`. The seven explicit names omit the file basename. A future actual-owner discovery must use the compiled module index, not a namespace filter containing `BoundedPolylogWindow`.

The parent freeze is `next-source/oq6-bounded-polylog-window-194/parent-freeze-v1.json`, SHA256 `fc1612a0ca066c74edea4ec41716583fe635fbc5c103cf03540dabe3a9435278`. I read all seven exact ordered declarations, all three full right-hand sides and types, the complete 14937-byte ordered local-data/scope contract (SHA256 `93304586b1b46677cb7f21a5814890febf8615d526c7bbf0b2b0410c3c2880be`), assumptions, frozen theorem, and complete mathematical derivation. Independent source extraction matches every declaration and every definition RHS after whitespace normalization. The nine imports also match in order. No re-freeze is required by this source.

The effective primary evidence is the original immutable candidate plus the metadata-only repair overlay SHA256 `23e3d3f5dc9eda22bd92c381b4dbdd059fc7166cec0f416dfd40fb3884cd22db` and the corrected selected-declaration file SHA256 `ec26479d7c0256b95e781c6c4dc1f25402adf22b8aee97b3b0daa377b4cc242e`. I did not treat the original malformed 36-row metadata as 36 declarations. The corrected denominator is exactly 32 complete selected raw declarations, 146 chronological scope rows and six global-instance rows. I read all of these rows and independently compared all 184 rows against their exact raw slices in the two full pinned packets. All slices and all nine contained file byte hashes agree. The packets are SHA256 `fa40811a001b5ed199b4338031681de84d9cb3862a1f2b7126427c7c241cf4db` and `ade2e9a0f33fb87d9d03e7a901382ae61bf1572fa0237d744ce5f0065de0b52b`, at Mathlib `807d3836b165983210ee2ecf3cd28f239436949c`, Lean `leanprover/lean4:v4.36.0-rc1`. This is raw-source evidence, not an elaborated TYPE print.

`INDEPENDENT-STATIC-BINDING.json` records the independent exact-byte and slice checks, declaration extraction, complete written types of all 29 `have`s, and import comparison. Its result is static correspondence only; the mathematical judgement here was made by reading and checking the proofs, not inferred from those comparisons.

Current authority is phase `C12_OQ56_21`, ledger SHA256 `b827695f18d3d96805f0577b9c8759a66be0b71640dcc107910384ea7723cb44`: Root0/C121/OQ561, at most two project heavy commands. The OQ56 parent retains CPU52–55 and its original lock; this reviewer has heavy0. The historical phase16 field nested in the OQ56 registry entry is not the current phase authority. Existing old ACK/format provenance, frozen bytes and accepted receipts were preserved.

## Original-source fidelity

I read the complete original p44, p51 and p54 files, not just the target excerpt. Their verified SHA256 values are respectively `3d6a674252a81b7ca051fd54aa0a621511ebce94af2f0bdf9b4eca8715bc5239`, `96920f428b8fc09788a6388103cefe398e3ec739129a5922b984babd09e99359`, and `e03649e1324def02de3ff234bcc94c9e1cb643e074a324e1817ef940f5e01c43`.

The original p51 lines197–204 need the deterministic condition that a fixed polylogarithmic height satisfies `R_n² q_0=o(n)` for `q_0=t_0 n^(1/3)`. This unit exports the explicit quotient limit and the useful eventual inequalities `1<n`, `2≤q_0`, and `2 R_n² q_0≤n`, first for the exact height `C (log n)^a` and then for the actual cutoff `(A log n/tau)^(1/alpha)`. All coefficients and exponents are fixed real parameters. The generic hypotheses are exactly `C≥0`, `a≥0`, `t0>0`; the specialization has exactly `A,tau,alpha,t0>0`.

No statement assumes a desired window, a rate bound for the ratio, a random concentration event, or any statistical premise. No theorem permits the fixed coefficients to vary with `n`. The exact polylogarithmic form and the actual cutoff are what is established; the source does not export a separate theorem for every abstract function merely bounded by a polylogarithm.

This is only the deterministic admissibility prerequisite. It neither proves the probability estimates in S16 nor the actual denominator geometry in S17. It does not establish the original OQ56 root or any new novelty claim. p44's ghost-sample/moment argument remains a distinct obligation; the published Shao–Zhou Lemma6.1 input remains externally attributed. The p54 repair of the false arbitrary polynomial conditional p-moment rate remains in force and is neither consumed nor claimed proved here. There is no DC 2/5 expansion or mechanism124 prerequisite. Original C1 immutablev85 remains complete, C2/C12/OQ56 remain OPEN, and OQ3 remains separately PAUSED_BY_USER.

## Complete proof review, lines1–215

Lines1–27 import only the nine frozen Mathlib modules, set `autoImplicit false`, open `Filter` and the `Topology` scope, enter `Shao.OQ5.P51` and a noncomputable section. There are no project imports. Lines29–33 define the exact total real sequences `R_n=C*Real.rpow(log(n:ℝ),a)` and `q_n=t0*Real.rpow(n:ℝ,1/3)`. They introduce no hypotheses, branches, selected witness or local instance.

**Generic ratio, lines35–92.** The statement includes the complete natural domain and all six ordered parameter/proof binders. Lines41–44 apply the root theorem `isLittleO_log_rpow_rpow_atTop` with the explicit real exponent `2*a` and the strictly positive exponent `2/3`. This theorem allows every fixed real log exponent; using `a≥0` is not necessary for this step and does not add a premise. Lines45–48 restrict the real little-o relation along the natural cast. The standard real semiring/order/strict ordered-ring/Archimedean instances meet its hypotheses. Lines49–52 use the quotient consequence in the normed division ring ℝ. Thus `(log(n:ℝ))^(2*a)/(n:ℝ)^(2/3)` tends to zero along all naturals.

Lines53–57 multiply this limit by the fixed real scalar `C^2*t0` in the raw theorem's scalar-then-proof argument order. The target limit is zero since this scalar times zero is zero. No positive scalar condition is needed. Lines58–91 prove the exact eventual identity between the requested ratio and that scaled quotient. The proof restricts to the eventual set `1<n`; the natural-to-real cast gives `1<(n:ℝ)`, then `0<(n:ℝ)` and `0<log(n:ℝ)`. All sign-sensitive formulas are used inside this scope.

Lines68–72 use `rpow_mul_natCast` at the natural number2 to identify `((log n)^a)^2` with `(log n)^(a*2)`, then commutative real arithmetic gives exponent `2*a`. There is no confusion between the outer natural square and an arbitrary real power. Lines73–84 first use `rpow_sub` with a strictly positive natural cast to show `n^(1/3)/n = n^(1/3-1)`, normalize the exponent to `-(2/3)`, and use `rpow_neg` with a nonnegative base to obtain `1/n^(2/3)`. Lines85–91 expand only the exact two definitions and use valid field/ring reassociations. These prove

`R_n^2*q_n/n = (C^2*t0)*((log n)^(2*a)/n^(2/3))`

on the stated eventual set. Line92 transports the scaled limit in the correct equality direction using `heq.symm`. The proof does not cancel a zero denominator at finite indices and does not assume the conclusion.

**Generic eventual window, lines94–141.** Lines101–104 use the preceding theorem with exactly `C,a,t0,hC,ha,ht0`. Lines105–109 scale by2, with associativity identifying the exact twice-ratio. Lines110–118 scale that limit by−1 and use the raw-written `eventually_const_lt` with the proof `−1<0` first and the negative-ratio limit second. The resulting eventual inequality is `−1<−(2 R_n^2 q_n/n)`. Lines119–123 correctly turn it into `2 R_n^2 q_n/n<1` by real linear arithmetic. This requires no nonnegativity hypothesis on that ratio. The generated dual declaration `eventually_lt_const` is not consumed.

Lines124–127 compose `tendsto_rpow_atTop` at the positive exponent1/3 with the natural-cast limit. Lines128–130 take the fixed real threshold `2/t0` using the limit-proof-then-threshold order of `eventually_ge_atTop`. The finite intersection in lines131–133 binds only an arbitrary natural input and Prop hypotheses. In lines134–138, clearing the strictly positive `t0` in `2/t0≤n^(1/3)` gives `2≤n^(1/3)*t0=t0*n^(1/3)=q_n`. Lines139–141 recover positivity of the natural-cast denominator from `1<n`; clearing that positive denominator in the strict upper ratio gives `2 R_n^2 q_n<n`, which implies the required weak inequality. Every conjunct follows from a proved eventual statement. There is no chosen threshold N and no circular window premise.

**Actual cutoff definition and ratio, lines143–175.** The total definition is exactly `Real.rpow (A*log(n:ℝ)/tau) (1/alpha:ℝ)`. Lines153–155 prove nonnegativity of the direct generic coefficient `(A/tau)^(1/alpha)` by strictly positive base and of the direct exponent `1/alpha` by `alpha>0`. Lines156–162 apply the generic ratio theorem with these two explicit real expressions, `t0`, and the ordered proof arguments. There is no separate chosen coefficient or implicit extra parameter.

Lines163–172 prove the actual height's eventual equality to that exact generic height. On `1<n`, `A/tau>0` and `log n>0`; field reassociation identifies the original base with `(A/tau)*log n`. `mul_rpow` is applied with the two required nonnegative-base proofs in their written order, at the exponent `1/alpha`. The full parameter and hypothesis captures match the freeze. Lines173–175 transport the limit across this eventual equality. Rewriting uses the actual-height-to-generic-height equality, and yields the requested function equality regardless of congruence orientation. No equality is asserted outside its proved eventual sign domain.

**Actual cutoff eventual window, lines177–211.** Lines185–197 independently instantiate the generic-window theorem with the identical coefficient/exponent expressions and proof order. Lines198–207 independently establish the same eventual height identity with the same paid signs. Lines208–211 intersect the generic window with that identity, retain its first two conjuncts and rewrite only the height in the third. This proves exactly the actual cutoff window and assumes none of its conjuncts. Lines213–215 close the anonymous section and namespace in the frozen order. No declarations appear after the closure.

## Primary interfaces, assumptions and chronological scope

All 32 selected raw declarations, including the following contextual/supporting declarations, were read completely with their proof bodies. The 146 chronological rows and all six global instances were read and checked against full-file packet slices. Namespace and section closures are material: the root logarithmic little-o theorem is outside the earlier `Complex` and `Asymptotics` sections; the `NoBotOrder` section in `OrderClosed` has ended before `eventually_const_lt`; command-local `open ... in` and `set_option ... in` do not become persistent ambient settings. No earlier `[NeBot l]` or unrelated variables are silently added to the consumed interface.

| Pinned source | Selected complete declarations and paid interface |
|---|---|
| `Pow/Asymptotics.lean` | Root `tendsto_rpow_atTop {y:ℝ} (hy:0<y)` is used at1/3. Root `isLittleO_log_rpow_rpow_atTop {s:ℝ} (r:ℝ) (hs:0<s)` is used at explicit `r=2*a`, `s=2/3`. The earlier scopes close before the latter; no extra parameter is captured. |
| `Pow/Real.lean` | `Real.rpow` and the anonymous `Pow ℝ ℝ := ⟨rpow⟩` bridge notation to the explicit function; no compiled anonymous-instance name is invented. `rpow_natCast(x:ℝ)(n:ℕ)`, `rpow_pos_of_pos(hx:0<x)(y:ℝ)`, `rpow_zero(x:ℝ)`, `zero_rpow(h:x≠0)`, `rpow_one(x:ℝ)`, `rpow_nonneg(hx:0≤x)(y:ℝ)`, `rpow_neg(hx:0≤x)(y:ℝ)`, `rpow_sub(hx:0<x)(y z:ℝ)`, `rpow_mul(hx:0≤x)(y z:ℝ)`, `mul_rpow(hx:0≤x)(hy:0≤y)` with implicit real exponent, and `rpow_mul_natCast(hx:0≤x)(y:ℝ)(n:ℕ)` have their complete raw assumptions checked. These are13 selected rows in this file, including definition and instance. Zero/one identities also justify the finite-index discussion. |
| `Asymptotics/Lemmas.lean` | `IsLittleO.tendsto_div_nhds_zero` is specialized to normed division ring ℝ and α=ℕ, with no nonzero-denominator premise. `IsLittleO.natCast_atTop` uses `[Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R]` and the ambient norm structures of the function codomains. All are standard for ℝ. Earlier local sections close in their chronological positions. |
| `AtTopBot/Archimedean.lean` | `tendsto_natCast_atTop_atTop` uses `[Semiring R] [PartialOrder R] [IsOrderedRing R] [Archimedean R]` and is used at R=ℝ. `Filter.Eventually.natCast_atTop` was read as complete contextual evidence; the proof instead uses the IsLittleO restriction. |
| `Topology/Algebra/Monoid/Defs.lean` | `Filter.Tendsto.const_mul` explicitly takes `b` and then `hf`, under topological multiplication with separately continuous multiplication. The raw global instance deriving `SeparatelyContinuousMul` from `ContinuousMul` is present. Specialization M=ℝ and source α=ℕ meets every bearing assumption. The unused source X variables do not become theorem hypotheses. |
| `Topology/Order/OrderClosed.lean` | `Ioi_mem_nhds`, `eventually_gt_nhds`, and raw `Filter.Tendsto.eventually_const_lt(hv)(h)` were read. The bearing frame is topological linear order with `ClosedIicTopology` on the real value type; source index type γ is instantiated by ℕ. Universes u,v,w and intervening section closures were checked. Four global instances in this prefix concern order dual topology; none is a new local instance in this module. `@[to_dual eventually_lt_const]` is provenance only; no generated type is asserted or consumed. |
| `Log/Basic.lean` | `Real.log`, `log_zero`, `log_one`, `log_pos(hx:1<x)` and `log_nonneg(hx:1≤x)` were read. Total `log` uses the zero branch and otherwise absolute value. The implementation uses `log_pos` only after proving the strict real lower bound. The earlier command-local transparency option does not persist. |
| `AtTopBot/Defs.lean` | `Filter.atTop [Preorder α]`, `eventually_ge_atTop [Preorder α](a)`, and `eventually_gt_atTop [Preorder α][NoTopOrder α](a)` were read. The used strict natural event has standard Nat order/no-top instances and parameter `(1:ℕ)`. |
| `AtTopBot/Tendsto.lean` | The complete raw protected declaration `Tendsto.eventually_ge_atTop [Preorder β](hf)(c)` is used with β=ℝ, hf=the cube-root limit and c=`2/t0`. It is not confused with the uncomposed filter theorem of the preceding file. |

These interfaces use only standard real/natural algebra, order, topology and filter instances. All type universes specialize to the ordinary real or natural types; the new module declares no universe or ambient type variable. The actual elaborated level parameters and implicit-instance terms remain subject to the machine packet rather than a fabricated TYPE print.

## All 29 ordinary Prop contexts and all local data

I independently extracted every written `have`, including bullet-prefixed forms, and read its full written type and proof. The complete types in `INDEPENDENT-STATIC-BINDING.json` match the source and the author's full static map. Each is genuinely Prop-valued by its outer constructor, and none is subsequently eliminated to select or compute data.

| Source line(s) | Complete context classification and proof use |
|---|---|
|41,45|`hreal`, `hnat`: `Asymptotics.IsLittleO` propositions over fully displayed real/natural functions.|
|49,53|`hbase`, `hscaled`: `Tendsto` propositions; the scalar is the frozen direct real expression `C^2*t0`, not data produced by the proof.|
|58|`heq`: an eventual equality proposition, specialized pointwise only on `1<n`.|
|65,66,67|`hn1`, `hn0`, `hlog`: strict real inequalities paid from the natural event and `log_pos`.|
|68,73|`hlogpow`, `hthird`: real equalities; used only for rewriting inside the eventual algebra.|
|101,105,110|`hratio`, `htwice`, `hnegative`: `Tendsto` propositions for the original, twice and negative twice-ratios.|
|114,119|`hnegativeLower`, `hupper`: eventual strict inequalities; no selected index or chosen threshold.|
|124,128|`hpower`: `Tendsto ... atTop atTop`; `hpowerLower`: eventual lower inequality at the direct threshold `2/t0`.|
|139,140|`hn1`, `hn0`: strict cast inequalities scoped to the upper-window branch.|
|153,155|`hCoefficient`, `hExponent`: weak real inequalities proving the generic specialization's hypotheses.|
|156,163,168|`hgeneric`: `Tendsto`; `heq`: eventual height equality; `hn1`: strict cast inequality inside that equality.|
|185,187|The second `hCoefficient`, `hExponent`: separate weak inequality proofs in the last theorem.|
|188,198,203|`hgeneric`: eventual conjunction; `heq`: eventual height equality; `hn1`: strict cast inequality.|

The count is10+9+5+5=29 across the four proofs. All `filter_upwards` binders introduce an arbitrary `n:ℕ` with ordinary Prop hypotheses; they do not choose an index witness. Both angle-bracket constructions build conjunction proofs in Prop. `congr`, `ring`, `norm_num`, `linarith`, cast proofs and equality transport produce proof terms only. There is no new data `let`, `choose`, selector, recursive value, data-producing branch, structure value or local/global instance. No Prop proof supports a data choice.

I checked the full ordered scope contract, including all direct anonymous values: `2*a`, `2/3`, `C^2*t0`, natural2, real1/3 and1, scalar2, scalar−1, threshold `2/t0`, `(A/tau)^(1/alpha)` and `1/alpha`, all full function lambdas, each eventual predicate, and the direct base arguments of both `mul_rpow` applications. Generic equality scopes capture `C,a,t0`; generic final-window proof also uses `ht0`. Cutoff equality scopes capture `A,tau,alpha,hA,htau`, with `n` bound locally; the final predicate captures `A,tau,alpha,t0`. No hidden capture or initializer delta was found. Ordinary proof branches are within the frozen Prop exemption.

## Boundary cases, axioms and qualification boundary

All functions are total on every natural n, including0 and1. The proof transports limits only by eventual equality, so it makes no all-index positivity assertion. `log 0=log 1=0`, and the cube-root exponent1/3 is nonzero and positive. At n=0, q is0 and the ratio is0 under total real division. At n=1, the height is C if a=0 and0 if a>0, while q=t0; the window is not asserted there. The cutoff's positive reciprocal exponent gives cutoff0 at both indices. C=0 makes the ratio identically0; a=0 is a constant height. Both are allowed and correctly handled. A positive but arbitrarily small t0 still makes q tend to infinity. Removing t0>0 would invalidate the lower-window claim, so the retained hypothesis has a genuine purpose. No new lower bound on C or a is used.

The source contains no `sorry`, `admit`, new `axiom`, `unsafe`, or `native_decide`, and no new data choice. Imported noncomputable real functions are part of the pinned library interface. This source inspection does not establish their transitive axiom list. Final acceptance still requires actual source-bound native success and complete all-module-owner axiom evidence with whitelist `propext`, `Classical.choice`, `Quot.sound`, checked for the same original object. Every owner, including generated auxiliaries, needs complete TYPE and full value/body coverage where applicable, level parameters, component references and recursive dependency closure. The review must examine those actual outputs before changing `qualified=false` or `actualOwned=UNKNOWN`.

The only outstanding requirement is this machine-evidence qualification, not a mathematical repair. This SOURCE review is complete and source-bound; it can be reused unchanged if the exact source hash remains unchanged. A proof or statement change requires an affected-evidence assessment. I have not run or replayed any accepted producer, old leaf axiom check, local Lean probe, server command or heavy process.
