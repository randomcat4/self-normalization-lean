# Unit275 repair03: closed-declaration proposal only

The proposed remedy is to replace the current single large proof command by eight closed private declarations and a short proof under the unchanged public theorem statement. The exact complete helper statements are in `PROPOSED-HELPER-HEADS.json`; their dependency order, old source/proof ranges, and assembly rules are in `PROPOSED-DECLARATION-ORDER.json`. No helper or replacement main proof body has been implemented. The declaration pack is proposed, not frozen. The parent must read and freeze its exact bytes and issue a separate implementation activation before any body is written.

This is a conservative partition along existing substantial mathematical interfaces. Eight is not a proved minimum number of declarations. It avoids adding a helper for each elementary inequality while separating finite algebra, retained-array measurability, actual cost admissibility, the finite CDF engine, common localization, uncentered bounds, physical transport, and uniform rate absorption. No new mathematical premise or external result is proposed for the public theorem.

## Exact starting point and evidence

The activation is `C:/game/shao lean/drafts/oq56/unit275/repair03-proposal-ACTIVATION.json`, SHA256 `aab3624385d4856d0952c727aad8420de5b5f7154c35ab7da6f25d91e92d11c6`, 28767 bytes. All 117 bound inputs were verified by actual bytes and SHA256 before the first write; a final recheck found zero mismatches. The sole new write scope is this `repair03-proposal-01` directory. Other owners, old sources, freezes, reviews, receipts, the curated library, and shared files remain untouched.

The current failed source is `author-repair-02/UniformPMomentOriginalPhysicalCompactCDF.lean`, SHA256 `57ed4f80977d8cf5d6154f20cbab1b549539eae51b995ee4ad43af7ff9954b90`, 67561 bytes, 1154 LF. Its `PROOF.txt` is SHA256 `987664a776c3895d8b0256dead01023b5fbb635507277c37145733bb1f357c21`, 64445 bytes, 1087 LF. The repair02 independent full SOURCE/proof coverage union and parent intake were read. They remain evidence for that exact source; they are not a kernel success or blanket coverage of a future declaration refactor.

Native03 naturally ended with RC1 in 30.918530501425266 seconds, no object, all owned work ended, and `ownLive=[]`. The receipt records all 34814 protected artifacts preserved, no timeout intervention and no cleanup. It records five errors and nineteen warnings. No prior native request was replayed and no new Lean or axiom call was made for this proposal.

The bound original normalized diagnostic receipt is `lead-execution-01/native03-terminal-inspection.json`, SHA256 `a087cb5ae15b84047089e9c212eb2cd490c761a7b28e7c967c308a82873be400`, 12508 bytes. The parent's later supplemental receipt, fully read and verified, is `lead-execution-01/native03-terminal-inspection-v2.json`, SHA256 `6061f8f6083d556687eb1fe1b97ad4a78e2984ed3a950496c33ab35ab7c8a535`, 11719 bytes. Its alternate diagnostic-code normalizer confirms the same five errors and nineteen warnings, with no additional unit275 error. It is one supplemental binding, separate from the original 117; the activation has not been rewritten.

The raw stdout stays on the server: 79929 bytes, SHA256 `59d5b24958097580cf6b0c66ac563946e64d11600dc37a159a3e21368895aef8`. It was not transferred or read here. All available normalized entries were read. Four heartbeat messages are complete; the linarith context has 68713 characters in total with 64713 middle characters explicitly omitted. No claim is made to have read that omitted context. The nineteen warnings are retained as evidence; this proposal authorizes no warning cleanup.

## Failure diagnosis and exact local arithmetic obligation

The emitted errors are SOURCE296:10 (linarith), SOURCE791:68 (isDefEq heartbeat limit), SOURCE799:12 and SOURCE897:8 (tactic heartbeat limit), and SOURCE19:0 (whnf heartbeat limit). Each timeout reports a maximum of 200000 heartbeats. Their presence is not a mathematical proof failure of the desired CDF statement, and RC1 is not a proof pass.

At SOURCE296, write S for the actual finite sum of true projection squares and N for the actual cast of n. The subset argument already has N > 0 from n >= 3. The available diagnostic tail has `hξ : S / N <= 1 / 2` and `ht : S <= (1 / 2) * N`; the target event uses `S <= N / 2`. These thresholds are equal over the reals. The proposed affected repair is an explicitly typed local inclusion between those two actual events, conversion through the positive denominator, then a direct rewrite of `(1 / 2) * N = N / 2`. The current broad `linarith only [ht]` occurs inside the unresolved inclusion passed to `measureReal_mono`, and the printed goal is False. Giving the inclusion its exact event type before passing it to the measure comparison removes dependence on broad tactic inference there. No stronger low-energy assumption is needed, and no new proof body is written by this proposal.

The other locations are late, elementary-looking steps: SOURCE791 is the coefficient inequality `1 <= 16 * (1 + 4096) * (1 + z)` from z >= 0; SOURCE799 forms nonnegativity of the displayed rate; SOURCE897 obtains positivity of q from the already derived fact. A further timeout is reported at the main declaration's start during whnf. Together with the long nested context this supports a source-structure diagnosis: expensive elaboration of a monolithic nested command and retained large dependent tuples is a plausible bottleneck. The exact internal cause at each timeout is not certified by the available diagnostics. A scalar tactic substitution alone would leave all four resource errors unresolved.

The proposed declaration boundaries give each substantial block a closed command with narrow explicit data and opaque earlier results. In particular, consumers receive only the actual low-energy probability bound they use, instead of retaining all measurable/Laplace/tensor-power conjuncts from unit265 in every later local context. The residual scale split is moved before finite-cost array elaboration in the uncentered consumer. This structure is expected to reduce unnecessary context and definitional equality work. It has no measured default-budget result yet and carries no guarantee of fitting that budget.

## Default limits and frozen assembly

The inherited current PROOF begins `:= by`; HEAD contains only the theorem statement. In the current source, SOURCE67 and SOURCE68 are the body directives `set_option maxHeartbeats 2400000 in` and `set_option maxRecDepth 4096 in`. Native03 nevertheless emitted default-200000 heartbeat diagnostics. The scope/effect of the old directives is not interpreted as authorization for higher limits.

The separately activated implementation must REMOVE BOTH inherited body directives, and introduce no heartbeat, recursion-depth, memory, time, or job override in any helper or in the main theorem. Plain default options apply throughout the new proof commands. The existing frozen PRE contains `set_option autoImplicit false`; that is retained byte-for-byte and is not a resource increase. This proposal has not changed the old source or those old directive bytes.

The parent-controlled future assembly is: exact PREAMBLE18, followed by the eight complete private declarations in the proposed order after freeze, followed by exact public HEAD47 and its new short `:= by` proof, followed by exact CLOSING2. Existing exact bindings are:

| Frozen fragment | Bytes / LF | SHA256 |
| --- | --- | --- |
| PREAMBLE.txt | 464 / 18 | `55c590fc357c0e1c551e483199c010fefd091663c0826c70d6e34b42b183ea31` |
| HEAD.txt | 2594 / 47 | `c0f79900ad0a8791e47db66c03ed89b6e9e03ad30a29bbb897540406374231c2` |
| CLOSING.txt | 58 / 2 | `0ac3f5180df19b40d33b3e034c671ebc8e5353464e567c56093f43f7becae921` |

The exact helper pack is 28414 bytes, SHA256 `02746f870912ac72a870183a4c56ed03449d32268245d5e559fb581a5458d45f`. The exact order/map pack is 12580 bytes, SHA256 `968f3a00b099b9572cd08c0fef1c7f2f0fce0f9ca19debb7a915bbbcd4937c00`. Each helper entry contains its full typed HEAD, visibility, universe parameters, explicit and implicit binders, exact let-defined actual objects, output, byte count and SHA256. There are zero helper bodies in the pack. The common context is the existing namespace `Shao.OQ6.UniformPMomentOriginalPhysicalCompactCDF`, noncomputable section, universe u and existing imports/open declarations; no undeclared local proof context is assumed.

## Declaration order and source mapping

All ranges below are one-based, inclusive, and refer to the exact current failed source/proof above, not to yet-unwritten new line numbers. The JSON order pack gives the complete mapping when a helper uses several noncontiguous blocks.

| Order and complete private declaration name | Closed responsibility | Principal old SOURCE / PROOF ranges | Earlier proposed dependencies |
| --- | --- | --- | --- |
| 1. `finite_projection_residual_numerator` | Actual finite unordered-pair/projection numerator algebra; no model hypothesis | 89-162 / 24-97 | none |
| 2. `compact_retained_deletion_measurability` | Exact retained arrays, both deleted envelopes, measurability and nonnegativity | 405-406 and 511-563 / 446-498 | none |
| 3. `actual_compact_cost_admissibility` | True projection/residual data, actual full/deletion integrability, exact truncation sum, finite cost upper bound | 200-218,376-420,460-482,503-510,564-615 | 2 |
| 4. `actual_compact_numerator_threshold_bounds` | Apply explicit external finite CDF engine to actual arrays, clipped denominator and exact numerator thresholds | 426-459,483-502,621-626,631-698 | 3 |
| 5. `actual_common_compact_localization` | One actual G/H/Z event payment, measurability, nondegeneracy and clock-independent physical comparison | 200-370 / 135-305 | none |
| 6. `actual_common_uncentered_compact_bounds` | Complete residual-scale split, actual numerator identification, H agreement, both complements and four uncentered errors | 371-425,616-630,699-820 / 634-755 for final block | 1,4,5 |
| 7. `actual_common_physical_compact_raw_bounds` | Physical clock transport, normal-CDF shift and strict/closed complements | 821-896 / 756-831 | 6,5 |
| 8. `countably_generated_uniform_compact_rate` | Common clock/K positivity before models; derive actual265 low-energy input; absorb raw cost for all n and x | 70-88,163-199,897-1025 / 832-960 for absorption | 7 |
| 9. unchanged public main theorem | Original-model reduction and law transport; call closed class supplier | 70-88,1026-1152 / 961-1087 for transport | 8 |

The first declaration is universe-free. Declarations 2-8 have universe u; only 4,6,7,8 require the internal CountablyGenerated instance where the existing finite CDF/source route uses it. Declarations 2,3,5 do not introduce that requirement. The public main theorem retains arbitrary measurable spaces through the existing original-to-countably-generated reduction. No StandardBorel assumption is added.

## Quantifiers, data fidelity and call-site obligations

The proposed helper8 has explicit tB, cg and K as let-defined outputs before quantifying over models. Here tB=(1/(4B))^(2/(p-2)), cg=tB/4 and K=131112*C+33117+2/cg. Thus the same K depends only on C,p,B and is fixed before every space, measure, kernel, n or x. The public theorem's original existential common-constant quantifier remains byte-exact. Helper8 proves the countably-generated class supplier from its premises and earlier helpers; it does not take any desired uniform CDF conclusion as input.

The explicit external `ScalarShaoZhouFiniteCostCDFInput.{u} C` remains an external hypothesis. The proposal neither proves its existence nor replaces it by an unnamed analytic assumption. The public p range 2<p<=3, B>=1, true-projection p integrability, beta<=B and normalization remain exactly as frozen. Neither unit273 nor unit274 is a dependency; neither is qualified by this proposal.

Every model helper defines g(o)=integral h(o,y), r(o,y)=h(o,y)-g(o)-g(y), v=integral r^2 and s=1+sqrt(v). The finite statistic is the same FiniteRows.uStatistic divided by the square root of the actual FiniteRows.jackknifeSq, with the exact branch returning zero when the denominator is not positive. No proxy variance or alternative statistic is substituted. The numerator helper uses the actual unordered residual pair sum with the original n-1 and sqrt(n) coefficients. The deletion envelopes use the same full-n indexing and erase incident entries rather than changing normalization to n-1.

The only extra local input to helpers5-7 is a narrowly typed hLow: for the actual true g and every finite n, product probability of sum(g_i^2)<=n/2 is <=exp(-cg*n). At each call it must be supplied by projecting the already-qualified unit265 theorem using the actual normalized model, actual p integrability/beta bound, and the same common cg. It is not a new main assumption, a CDF conclusion, a residual budget or a reusable arbitrary-envelope premise. Helper8 and the main original-model path must establish that projection explicitly. The large full unit265 tuple should be destructured only long enough to produce this typed fact.

Helper4's s<=q premise is internal to helper6's complete scale split. In the s<=sqrt(n) branch the actual full/deletion functions are elaborated, their integrability/cost comes from helper3, the legal clip is proved on the actual G, and the external finite CDF engine supplies both numerator threshold tails. In the s>sqrt(n) branch, probability and normal-CDF values lie in [0,1], so every absolute error is <=1; the displayed nonnegative residual term already dominates 1. That branch is closed after the common K is fixed, with no bound on actual v assumed. All n>=3 remain covered. Moving the split earlier is a proof-structure change, not an alteration of a hypothesis or of the final error.

The common G/H/Z construction and its payments remain the original ones: G-complement <=exp(-cg*N)+1/(16*q), H-complement <=exp(-cg*N)+(1/16+16384*s)/q, and zero event <=exp(-cg*N)+(1/16+16720*s)/q. Only old public clock-independent conjuncts are used to derive these new common payments and physical comparison. Helpers6-7 preserve strict and closed CDF and tail bounds by their actual complements. Helper7's raw error remains C*(L+65552*(1+y)*s/q)+2*exp(-cg*N)+(1/8+33104*s)/q+12/N with y=tau(x). Helper8 performs the same truncation-moment and exponential absorption to the common K rate. The public four errors hold for each x in [0,1], including both endpoints, and for all n>=3.

No independence, mixed-moment, residual-budget, additional envelope, StandardBorel, or desired-conclusion input is introduced. Independence and the actual envelope inequalities required by the finite engine are derived internally from the actual product model and qualified source interfaces, as in the mapped current blocks. The final main proof retains exact measurable observable law transport of the original model, instead of retaining a large collection of unused transported conjuncts.

## Review and server gates affected by the proposal

All new closed HEADs, their universe/binder closure, exact actual let objects, private hLow supply, proof bodies, declaration dependencies and main call integration need qualified independent review after implementation. SOURCE296's typed inclusion repair and the earlier scale split are actual affected proof changes and need review. Moving a byte-identical mathematical subblock into a new declaration changes its surrounding hypotheses and elaboration context; old proof coverage alone does not certify the new closure. The existing source-to-pages interpretation, qualified unchanged public dependency evidence, and old exact-source receipts can be reused for their covered scope. A future reviewer must map new source/proof ranges and identify exactly which unchanged mathematics is inherited and which new context/calls were checked; no blanket old coverage claim is made.

Only after the parent freezes these exact declarations, separately activates implementation, and accepts the affected independent SOURCE review may the parent run a new full source-bound native check with the original defaults. A successful new native object must receive the mandatory all-owned type/value/transitive-axiom audit against the standard whitelist propext, Classical.choice, Quot.sound. Future owned declaration and audit counts must be derived from the actual new source/object, not copied from the old one-theorem counts. No such object, audit or qualified result exists for this proposal.

The next action belongs to the parent: read and either freeze or revise the exact proposed HEAD/order pack. Any revision changes the exact pack to be frozen. No author keeps implementation authority while awaiting that decision.

## Static observations and release

The proposal pack has eight distinct private theorem names, no proof body, no resource override, a forward-free dependency order, and exact internal HEAD byte/hash metadata. The unchanged PRE18/HEAD47/CLOSE2 bindings and the 117 original inputs plus one supplemental diagnostic binding are verified. All proposal outputs use UTF-8 without BOM, LF and one final LF. These are deterministic file/structure observations, not Lean parsing, elaboration, kernel verification or an independent mathematical qualification.

Prescribed role settings are gpt-6.1-sol/xhigh. Actual model/backend/effort and input/cached-input/output/reasoning-subset usage are not exposed by this runtime and are recorded as null. No exact subscription percentage is inferred. There were no Lean, AX, toolchain, server, SSH, network, transfer, Git/API, child, Goal, schedule, sidebar or proxy actions. OQ56 and its root groups remain OPEN. This proposal is complete only as a proposal, with qualified=false and kernelChecked=false.

The unique terminal LASTFINALWRITE record releases all proposal, author, repair, implementation, write, review, execution, child, publication and retained authority. Heavy, inflight, pendingExternal, writer, child and publication counters are all zero; there is no active wait or persistent continuation claim. The ordinary turn ends after sealing.
