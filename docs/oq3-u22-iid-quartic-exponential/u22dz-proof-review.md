# U22DZ / DZ211 independent complete source-to-statement and proof review

STATUS: CORRECT
JUSTIFICATION: The complete frozen theorem and proof establish the actual SAME-E IID characteristic-function Gaussian bound and Gaussian-weighted quartic exponential error on one common positive radius. Every new model premise is derived from the retained canonical packet; the actual product-pushforward characteristic function is identified using the existing DW theorem, without a new coherence, Gaussian, error, law, or logarithm-branch premise. The original successful server kernel and all-owner recursive-axiom evidence are exact-source-bound and sufficient for this version.

Reviewer role: fresh NON-AUTHOR complete reviewer, assigned gpt-6.1-sol / xhigh; math-theorem, not math-ultra. I neither authored nor changed the implementation, frozen declaration, audit, evidence, coordination, Git state, or dependencies. My only write is this report. No children, delegation, sidebar operations, or outgoing cross-thread messages. I ran no Lean, Lake, recompilation, audit replay, cache mutation, or new proof gate. Read-only server operations only inspected existing bytes, pins, object bindings, and Git identities. Review finalized on 2026-10-24 UTC.

I read all 155 frozen-scope lines, all 214 successful source lines, all 239 actual-type lines, all 47 Audit.lean lines, and all relevant contents of the receipt, audit environment/record, two-attempt build history, and dependency-source binding. I read the entire original 206-line failed source, complete 1973-byte failure log, complete 133-byte success log, complete 20673-byte original axiom log, and full failed-to-successful diff directly from the server. Raw logs and failed source remain on the server; none were downloaded or rewritten. SERVER.md, current TEAM ownership information, compact current REGISTRY fields, and streamlined-acceptance-current.md were checked. Old dependency proofs/reports/gates were not replayed or fully reread; their exact qualified evidence was reused as authorized, while all consumed interfaces were read completely here.

## Exact frozen and evidence bindings

| Artifact in drafts/oq3 | Lines | Bytes | SHA256 |
| --- | ---: | ---: | --- |
| two-hundred-eleventh-unit-scope.md | 155 | 10818 | 0640474d1d9695bda5a9ce8f0daa471b0e33fe0f3c3c044d0fd0a01d219709f2 |
| u22dz-source.lean | 214 | 12672 | d2c25f7df0fcee50c5acfdd59fe4df2d66b46dfac77142cb77119a15d314fe3f |
| u22dz-frozen-declaration.lean.txt | 149 | 9616 | 358499a4f53956227ea43e5a52949513484619ba3da3ad5798580579f2326e84 |
| u22dz-actual-types.txt | 239 | 20421 | 7287b300567a1b57bd687d76cbb686792da3cb55c7509166f31c90ec845b8d90 |
| u22dz-Audit.lean | 47 | 2029 | 684b5ea95c3a2cd415ed997c3e3dc0441c7ae2f5d2301bd6b6ce69ec823b0380 |
| u22dz-receipt.json | 156 | 32102 | f7be4474efad55f7a63266ff31023f9e7ada6fe06eb60405a67d14da40d6686b |
| u22dz-audit-environment.json | 42 | 26787 | 8bcbe9843373987f1e0637b0e06dacb156e5017e93744fd5cf56b5c8d728ef41 |
| u22dz-audit-record.json | 18 | 499 | 69583f3a952b936d253509b55d8bac949d451e7103022422952366068a4a8093 |
| u22dz-build-history.json | 50 | 4431 | c0b69b2c3b13d5e6044db13a69040646b6a977b85632ddac5300493974ad6c2b |
| u22dz-dependency-source-binding.json | 40 | 25612 | 11a5cebc88495644fbd20104237e8d1b8a95d453be1aa4b8f9a38bc116b18430 |

Read-only server inspection verified the matching run copies under `/root/rivermind-data/shao-lean-20261021/runs/oq3/u22dz-20261023`, the live successful source in worktree `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`, and its original 1334144-byte olean SHA256 `b21ad721df160aae2c17cdf62106611ead36b492e05dd7d3cad5c9228fdea823`. The branch is `feat/oq3-normalized-edgeworth-characteristic`; HEAD is `e8a8e2a1916e068d5fd96a1af1a72c0dbad515e7`, tree `1bd1241d2cadc1bda5a159b3b0bad28926cfea38`. Project pins read from existing files are Lean `leanprover/lean4:v4.36.0-rc1` and mathlib `807d3836b165983210ee2ecf3cd28f239436949c`. No version command or compiler was rerun.

The 149-line declaration extracted from the scope equals the successful source declaration exactly, excluding only the proof introducer `:= by`; it also equals the frozen declaration artifact after its terminal newline. There are exactly 25 literal statement lets and exactly 25 corresponding actual-type `have` values, in the same order. Successful source is UTF-8 without BOM and contains no CR bytes. Frozen bytes were preserved.

## Complete literal-value and semantic statement coverage

The following covers every statement let, not just the final conclusion. Line references are to the successful source and actual-types.txt respectively. All values were read in full in both representations, including their coercions, measures, operators, and binder placement.

| No. / value | Source / actual-type lines | Checked literal meaning |
| --- | --- | --- |
| 1 tilt | 21-22 / 15 | The original scalar exponential tilt of mu by p.1*x+p.2*x^2. |
| 2 D | 23 / 16 | parabolaCovariance of that same tilt. |
| 3 s | 24 / 17 | sqrt(D00*D11-D01^2). |
| 4 t | 25 / 18 | sqrt(D00+D11+2*s). |
| 5 A | 26-28 / 19-21 | The full literal symmetric matrix: diagonal entries (D11+s)/(s*t), (D00+s)/(s*t), both off-diagonal entries -D01/(s*t). |
| 6 means | 29-30 / 22 | The actual first and second scalar moments under tilt p. |
| 7 Y | 31 / 23 | A applied to the centered vector [x,x^2]-means. |
| 8 laws | 32 / 24 | The map of the same tilt by Y; no free law. |
| 9 Phi | 33-35 / 25-26 | Actual integral of exp(i*(xi*y0+eta*y1)) under laws p. |
| 10 L | 57 / 53 | 1/sqrt(hi). |
| 11 U | 58 / 54 | 1/sqrt(lo). |
| 12 cA | 59 / 55 | c*U^(-beta), using Real.rpow. |
| 13 RA | 60 / 56 | R/L. |
| 14 P | 92-93 / 119-123 | The complete finite characteristic-function Taylor sum through Finset.range m, with I^j/j.factorial and the actual directional j-th moment. |
| 15 Q | 100-104 / 139-148 | -r^2/2-I*m3/6+(m4-3*(u^2+v^2)^2)/24; m3 and m4 are actual directional moments under laws p. |
| 16 retained Qsample | 109 / 158-159 | Measure.pi of n copies of the same tilt p. |
| 17 retained M | 110-111 / 160-161 | (sum_i z_i/n, Shao.energy z/n), the retained sample mean/square-mean pair. |
| 18 retained T | 112-113 / 162-163 | sqrt(n) times the same E p applied to M minus the same means pair. |
| 19 retained rho | 114 / 164 | The map of that Qsample by that T. |
| 20 retained Qn | 117-122 / 168-178 | -r^2/2-I*m3/(6*sqrt(n))+(m4-3*(u^2+v^2)^2)/(24*n), with the full real/complex casts as frozen. |
| 21 appended Qsample | 137 / 205-206 | The same literal product measure as no.16. |
| 22 appended M | 138-139 / 207-208 | The same literal sample pair as no.17. |
| 23 appended T | 140-141 / 209-210 | The same sqrt(n), E, centering, and sample map as no.18. |
| 24 appended rho | 142 / 211 | The same literal pushforward as no.19. |
| 25 appended Qn | 145-150 / 215-225 | The same literal quartic exponent as no.20; no independent approximation polynomial is introduced. |

Here r=sqrt(u^2+v^2), and mj denotes the displayed actual integral of (u*y0+v*y1)^j. In Q and both Qn occurrences, subtraction of 3*(u^2+v^2)^2 is OUTSIDE the fourth-moment integral. The pretty printer's compressed integral notation was checked against the explicit parentheses of the exact frozen source; no subtraction was moved into the integrand.

All assumptions at source 10-20 / actual types 2-14 remain the probability law, compact Theta inside the actual bivariate MGF domain interior, beta>=0, c>0, R>=0, positive determinant, and the actual tilted weak-Cramer bound. The conclusion retains positive lo/hi and their full two-sided covariance bounds, one continuous linear equivalence E with exact matrix action and both operator bounds, all real 8+delta radial moments, L/U/cA/RA positivity, full pointwise whitening/positivity/probability/L2/mean-zero/covariance/distortion/weak-Cramer packet, every integer moment, all Taylor/log-Taylor and quartic-log bounds, and the entire previous actual normalized IID logarithmic-exponent packet. No retained conjunct or old literal value was dropped.

The new existential C>0 and 0<delta<=1 occurs before ALL n>=1, p:Theta, and u,v with r<=delta*sqrt(n). Probability of the actual rho is asserted before the frequency restriction. The final bounds concern the actual integral under rho: norm<=exp(-(u^2+v^2)/4) and error from exp(Qn)<=C*r^5/(n*sqrt(n))*exp(-(u^2+v^2)/8). They are uniform over the stated compact family and all permitted sample sizes/frequencies. No additional E, law, coherence identity, Gaussian estimate, desired error bound, or logarithmic-branch condition is assumed.

## Whole-proof review

Source 158-165: The proof introduces only the nine leading let values and applies qualified `compact_open_domain_normalized_iid_log_exponent` to the identical mu, Theta, compact/domain hypotheses, beta,c,R, determinant and weak-Cramer assumptions. It extracts lo,hi and the SINGLE E once, preserves hspec/hE/hreal, unfolds only existing aliases, and reconstructs every retained conjunct hL,hU,hcA,hRA,hpoint,hmom,hchar,hlog,hquartic,hIID. This preserves both old existence witnesses and all their interactions; there is no second standardization choice.

Source 166-180: hmom at k=3,4,5 supplies genuinely common M3,M4,M5 and integrability/bounds under precisely laws p. For p:Theta, p.property is the required membership proof. The hpoint projections correctly give probability after the five preceding conjuncts, coordinate MemLp/zero means from the next paired conjunct, and the identity covariance from the following conjunct. They are not Gaussian or desired-error assumptions. The unused positivity witnesses for the moment constants cause no mathematical weakening; the DY interface does not require those witnesses as additional premises.

Source 181-186: The complete DY theorem is instantiated with index type Theta and law (fun p=>laws p). Every input is discharged from those same hpoint/hmom results: probability, each coordinate's L2 membership, both zero means, each covariance entry, and true uniform radial 3rd/4th/5th integrability and moment bounds. Its literal Phi and Qn become definitionally the frozen Phi and quartic Qn. This yields positive C,d1 with d1<=1 and the genuine power-characteristic-function Gaussian norm and weighted quartic-exponential error; it does not assume either conclusion for rho.

Source 187-200: The proof extracts the retained IID radius d0 and uses delta=min d0 d1. Both radii are positive; lt_min proves positivity and min_le_right followed by d1<=1 proves delta<=1. C and delta are fixed before introducing n, hn and p, then u,v. hpacket.1 gives probability of the actual product-pushforward rho for every n>=1. Both radius comparisons follow by multiplying min<=d0/d1 by the NONNEGATIVE sqrt(n); the closed <= boundary is retained. No frequency- or sample-dependent constant is selected.

Source 201-211: In the retained IID output, `.2.2.1` correctly selects the ACTUAL rho characteristic-function equality to Phi(u/sqrt(n),v/sqrt(n))^n, after the nonzero and logarithmic-error conjuncts. happrox is the DY bound on that very power on its own restricted radius. hcf_typed explicitly expands exactly the same product measure, map, sqrt(n), E, sample pair, energy, and centering, and is proved by the existing hcf. It is a derived local equality, not an assumption. Rewriting the two actual-rho integral occurrences by this equality and using happrox proves both required bounds, with exactly the frozen Qn and error factors. The proof never substitutes a second law or concludes an actual probability-law result merely from a formal power expression without this identity.

All remaining source lines (imports, namespace, opens, noncomputable section, and closing delimiters) were also reviewed. n=0 is explicitly excluded by hn; n=1 and zero frequency are included. The proof requires only sqrt(n)>=0 for the radius transfer, so it creates no missing division/strict-positivity side condition there. Divisions and logarithmic identities already belong to the exact qualified n>=1 IID/DY interfaces. Empty Theta introduces no hidden nonemptiness assumption; all p-indexed obligations are universally quantified and inherited existence is reused unchanged. No quantifier loss or uncovered endpoint was found.

## Qualified direct dependencies: entire interfaces and exact reuse

The dependency binding was recorded at `2026-10-24T03:26:29.457510+00:00`, before implementation/first kernel. Its two full actual-type strings exactly equal the local hash-bound type files: DW198 lines/all20 lets and DY62 lines/all2 lets, 260 lines and 22 consumed literal values in total. Receipt.direct_dependencies, audit-environment.parent_actual_source, and binding.exact_sources are structurally identical. I read every one of these interface lines and every literal value, including all eight DY actual owners (the public theorem and seven generated simp theorems). Their formal universes, model premises, measure domains, characteristic function, quartic exponent, constants and quantifier order match the calls above.

DW: `Shao/OQ3/CompactOpenDomainNormalizedIIDLogExponent.lean`, 183 lines/10668 bytes, source `563b693b005031e515a4761cbe351ae613e2b8f9402388c3fe5bd9f689cf26c1`; original object 1097024 bytes `83423df9d64ad22e01c4b97c748dfebc0a4900c0309d3094eb6799284b5413a8`; receipt `b33ac80c1dabb39beb1f529d7eed58caeb5c109307f0790a92d4660637f30518`; actual types `3d7584119ad44a17de698d5ae561decc0cac415d1324182629a6e1f9360baecd`; qualified fresh complete CORRECT review, 97 lines/21102 bytes, `d50c18b9d7a87da3607ce52703a2e95ac319b8d5f50d2c63eca10e32b160f7b4`. The binding records the new report fully parent-read and its reviewer completed/stopped before DZ implementation. This exact whole canonical packet is reused, not independently reconstructed with a different E.

DY: `Shao/OQ3/StandardizedPairQuarticExponentialError.lean`, 166 lines/8024 bytes, source `57e43c1a18d2dda37d06b57429c1888591d8ad49bd16a58f4c6c186cba1521c7`; original object 519536 bytes `dcb7cb878156e5300498210b0f3082275d497a6cd604e98d144b906866f879cb`; receipt `f7b8931269242fcf048b75ac81b93560b5b404e59820940e067d4024e6bed40e`; actual types `23db6e5160c4a56724553aeab7e0846d7a4550f0f45b902f15cbc8ab530bbdd3`; qualified fresh complete CORRECT review, 117 lines/23821 bytes, `2a77aa48c873a9050048b74bd3f074971b2ace70f156f94629ceaf90d6f299a9`. The binding records full parent reading and reviewer completion/stopping before DZ implementation. The qualified theorem genuinely derives both Gaussian power bounds from its displayed moment/standardization inputs; those exact inputs are discharged here.

Read-only hashing verified both current server dependency sources and both original objects against these bindings. The accepted-source-view paths resolve to those SAME hash-matching DW/DY objects. Local sources, receipts, actual types and review files also match all recorded hashes and lengths. I reuse the qualified complete dependency proofs/reviews/axiom receipts rather than rerunning unchanged old evidence. The new interface interaction and actual-rho transfer have received the complete fresh review above.

## Original failure, first success, and complete transitive axiom audit

Attempt 01 was an actual COMPLETE_FAILURE: original source 206 lines/12249 bytes SHA256 `1a4f9a5a8da0c71f6401d3bdcb0763d02e550bc72c1b6f02dffb596fe9a61ff1`; exit 1 after 12.35635063610971 seconds; full log 1973 bytes/30 lines SHA256 `5cb9b1f13ca00916fd9e205aadcc417b99a9abf06d555ba2d873b5506718139d`. I read the entire original source and entire failure. The sole substantive error is source line 203: `simpa only [hcf] using happrox` leaves the Phi-power estimate instead of rewriting the expanded actual product-map rho integral. The printed expected and actual Qn, constants, moments and bounds otherwise agree.

The full diff replaces only that last one-line proof step with hcf_typed and `rw [hcf_typed]; exact happrox`, increasing source length by eight lines. This explicitly exposes the already-derived SAME actual law identity; no hypothesis, definition, statement let, conclusion, or earlier proof step changes. The complete 149-line header and all25 literal values are unchanged. The failed artifact remains preserved; it is not counted as a successful gate.

Attempt 02 is the FIRST COMPLETE_SUCCESS for the reviewed source: exit 0 after 12.559981783851981 seconds. Its entire original log is 133 bytes/two lines, SHA256 `fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626`. Those two lines are only the known Lake mathlib local-changes warning and its path. No mathematical warning/error is hidden by truncation. The evidence records CPU14-17, native memory8192 MiB, jobs4, autoImplicit=false for both attempts. I verified exact source/object/log hashes without repeating the successful check or editing source cosmetically.

The original whole-owner audit has exit 0 after 5.778326136991382 seconds, with the same CPU14-17 / memory8192 MiB / jobs4 / autoImplicit=false recorded. Full original audit log: 20673 bytes/246 lines, SHA256 `2583f1598e37b2c5faee9beb31afb2aa91f563e926a43aecefa41929eb295ae6`. I read all246 lines, including both initial warning lines, every type/value line and the final counts/PASS. Its complete DECL-through-KIND segment is byte-for-byte the 239-line actual-types artifact; the audit-record also exactly equals receipt.audit.

Audit.lean checks that the frozen target exists as a theorem, then traverses ALL env.constants, selecting actual module ownership through getModuleIdxFor? and env.header.moduleNames, not a namespace-prefix or public-only filter. Every selected owner is rejected if it is a new axiom; Lean.collectAxioms recursively audits that owner's proof/type dependencies against ONLY propext, Classical.choice, Quot.sound. Any definition would also print its full VALUE. Private/generated/unexpected-name constants owned by the module would enter the same loop. The actual result is exactly ONE owned declaration/theorem, the frozen `Shao.OQ3.compact_open_domain_quartic_exponential_error`; public definitions0, private theorems0, generated theorems0. The sole full actual type and all25 literal values are reviewed above. Its recursively collected axiom set is exactly `[propext, Classical.choice, Quot.sound]`. Final markers are FROZEN_DEFINITIONS0, FROZEN_THEOREMS1, ALL_THEOREMS1, ALL_DECLARATIONS1, AXIOM_GATE PASS. No unexamined current-module owner is left outside the receipt.

External owners from imports are not miscounted as new module declarations. DW's actual theorem and DY's complete eight-owner interface are separately source/object/review-bound as above; the recursive collectAxioms on the new sole theorem additionally covers every external proof dependency actually used by it. The source contains none of sorry/admit/new axiom/unsafe/native_decide/implemented_by or a settings change. Audit options pp.deepTerms and pp.maxSteps only affect evidence printing and do not weaken kernel/proof checks. No forbidden or non-whitelisted axiom appears anywhere in the new owner's transitive audit.

## Scope and completion

This accepts the entire exact DZ211 frozen auxiliary result and its complete proof, including all retained DW content and the new Gaussian-weighted ACTUAL characteristic-function quartic EXPONENTIAL approximation. It does not establish the Edgeworth characteristic polynomial, analytic CGF derivatives, all-frequency/exterior control, inversion, new rho-Laplace conclusions, or original root B-D/OQ3 closure. It preserves the inherited source/p54 repairs and external-result attribution. The auxiliary beta>=0 assumption is unchanged from the qualified dependency; it is not represented as replacing the original strict 0<beta<2/5 root condition. No novelty claim or stronger original-root status is inferred from this auxiliary theorem.

No mathematical gap, statement-fidelity gap, owner-coverage gap, or source-bound evidence mismatch was found for the reviewed hashes. No implementation repair is requested. Qualification by the parent still requires FULL reading of this entire NEW report once; the parent's prior reading of old dependency reports does not substitute for that step.

Review is complete. After finalizing this report and reporting its independently computed length/byte count/SHA256, this reviewer stops all tools/writes and releases EXCLUSIVE write authority for `C:/game/shao lean/drafts/oq3/u22dz-proof-review.md`. This release concerns the review report only; it neither releases the lead's lane ownership nor activates a successor writer.
