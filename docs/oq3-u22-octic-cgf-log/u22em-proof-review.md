# EM224 independent complete final source/proof review

STATUS: CORRECT
JUSTIFICATION: The exact frozen theorem is proved from the actual law's normalized zeroth moment, true zero mean, genuine moment/CGF recurrence, qualified centered third-through-eighth derivative identities, and finite complex polynomial algebra. No additional moment, variance, coherence, cumulant, or target-bound premise is introduced. This accepts the auxiliary finite identity only.

Reviewer: /root/oq3_em224_final_review, fresh independent final reviewer; no authorship or source edits. Applied math-theorem SKILL.md and its complete prompt-library, openai-workflow, and lean-verification references; no math-ultra. Current local AGENTS.md explicitly records OQ3's human resumption and sole existing owner. SERVER.md broker/pin rules and TEAM.md mechanical ownership/type/value audit boundary were read. The project restriction to reuse exact successful server evidence overrides generic skill suggestions to run another compiler probe.

## Exact reviewed snapshot and complete coverage

Production module: Shao.OQ3.ActualCGFOcticLogPolynomial. The complete 58-LF production SOURCE, sole complete 20-LF frozen declaration, complete 23-LF scope, all 22-LF actual TYPE/AX/KIND output, and complete 47-LF audit program were read. All proof lines and all ten statement-let values were reviewed, without ellipsis or structural-summary substitution. The frozen declaration is byte-for-byte the production declaration head with its proof suffix removed. The complete receipt, audit-record, build-history, dependency-source-binding, qualified-dependency-binding, and original native/audit logs were read.

| Artifact | SHA256 | Bytes / LF where applicable |
| --- | --- | --- |
| u22em-source.lean | 242df2a8134a921eedd945eb0716ef059617f73dfffca841a542217253045260 | 2678 / 58 |
| u22em-frozen-declaration.lean.txt | 069381ba4afc5db1e3322c96d96d4b443e101c5718fff1bfeae38d8f20035120 | 1039 / 20 |
| two-hundred-twenty-fourth-unit-scope.md | 0ed98975bf844e025cbd0e7c3ca509d307b975c330caef47eb48d72f20ef3895 | 1556 / 23 |
| first original ActualCGFOcticLogPolynomial.olean | f9fc5c37d73d3b9921ca0e7f8c2346a4c3c14fb07f5cd03a988095ad4a8ddfba | 729648 |
| u22em-actual-types.txt | 076b178bae9eab287ed8e87f2ad13e9066d6176b65d45757b7e123d41b81cf98 | 1097 / 22 |
| u22em-Audit.lean | ec1bc323cab0fa590029457db799c20d44f733cd167a8ce7f0806a3e0c223542 | 1998 / 47 |
| u22em-receipt.json | 137326b8a7b377a196862e2ccd88733115d5a896759be2dc29dd47782fa62640 | 5360 / 185 |
| u22em-audit-record.json | 1a28e84e589ff9c1fee19e85ebf29494865c52cb923c11e8ee090776b6b2c128 | 3020 / 103 |
| u22em-build-history.json | a3d83d276b981130d37c02e5bc1410e99f7d71a9108df0f7d8cdbfe1b9d8ff7f | 2158 / 82 |
| u22em-dependency-source-binding.json | fd7dbe2521b2ef0f30dc8e28d1bfb53b6145aaebdb866f6b5620c8e7c97e218e | 504 / 12 |
| u22em-qualified-dependency-binding.json | 561bcc7357ce8a93312ed2d2e7655adc6f8d5559f7e89a245b2208e933d988d6 | 2321 / 50 |
| native build-01.log | 9c81fbdefc7a5d3695dd21fcd0bd6c8e6c71fce336c2cb4b8b1a5deb0b498379 | 877 / 14 |
| original audit.log | c28f43dbab56593ffeb3f2137155699e6a562aaba7fc1f25b9d31fd0270d12e3 | 1349 / 29 |

The reviewed local text artifacts are UTF-8, no BOM, and LF-only. Read-only broker observations confirmed current server production source, original object, all listed run artifacts, and both project dependency sources/original objects match the exact local/bound hashes. Run directory: /root/rivermind-data/shao-lean-20261021/runs/oq3/u22em-20261027; worktree: /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3. A final read-only observation again matched production SOURCE, original O, native log, and audit log. The audit's full DECL-through-KIND block is exactly the actual-types.txt bytes.

## Frozen statement and every let value

SOURCE 10-29 and actual TYPE describe arbitrary universe-polymorphic Ω with MeasurableSpace, actual mu with IsProbabilityMeasure, and the same real-valued X throughout. The only mathematical hypotheses are h0: 0 is in the interior of integrableExpSet X mu, and hmean: the actual integral of X under mu is zero. There is no S, positive variance, standardization, independent sequence, formal free cumulant sequence, coefficient identity premise, or conclusion-bound premise.

Let 1, m(k), is exactly integral (X w)^k under mu; let 2, kappa(k), is exactly iteratedDeriv k (cgf X mu) at 0. Neither is a replacement symbolic sequence. All later casts are real-to-complex casts of these same values.

| Statement let | Exact value | I-power/factorial check |
| --- | --- | --- |
| a | -(m 2 : complex)/2 | I^2=-1, 2!=2 |
| b | -I*(m 3 : complex)/6 | I^3=-I, 3!=6 |
| c | (m 4 : complex)/24 | I^4=1, 4!=24 |
| d | I*(m 5 : complex)/120 | I^5=I, 5!=120 |
| e | -(m 6 : complex)/720 | I^6=-1, 6!=720 |
| f | -I*(m 7 : complex)/5040 | I^7=-I, 7!=5040 |
| g | (m 8 : complex)/40320 | I^8=1, 8!=40320 |

Let 10, Q, is exactly a+b+c+d+e+f+g minus (a^2+2ab+2ac+b^2+2ad+2bc+2ae+2bd+c^2)/2 plus (a^3+3a^2b+3a^2c+3ab^2)/3 minus a^4/4. Every term, sign, multiplicity, and denominator in SOURCE 24-27, freeze 15-18, and actual TYPE 15-19 agrees. With a,...,g of moment weights 2,...,8, the retained quadratic weights are 4:a^2; 5:2ab; 6:2ac+b^2; 7:2ad+2bc; 8:2ae+2bd+c^2. Cubic weights are 6:a^3; 7:3a^2b; 8:3a^2c+3ab^2. The sole quartic weight is 8:a^4. Thus this is the weight-at-most-eight logarithm polynomial, evaluated as a finite expression; the theorem does not equate an actual Complex.log value to a finite polynomial.

The exact target is Q = sum over j in range 9 of (I^j/(j.factorial : complex))*(kappa j : complex), hence j=0,...,8 inclusive. There is no omitted endpoint, changed frequency, missing factorial, or additional parameter hidden by elaboration.

## Complete proof review

SOURCE 30 introduces only the ten frozen lets. SOURCE 31 proves m0=1 by X^0=1 and probability normalization; SOURCE 32 proves m1=0 by X^1=X and hmean. The 0^0 convention is the ordinary natural-power convention, so it also works at X=0.

SOURCE 33 proves kappa0=0: iteratedDeriv 0 evaluates the same real CGF at zero; mgf(0)=mu.real univ=1 and log 1=0. This is actual probability normalization. SOURCE 34-35 uses ProbabilityTheory.deriv_cgf_zero h0, whose pinned type gives integral X / mu.real univ, and iteratedDeriv_one; the genuine hmean makes this zero. It does not assume that a free first cumulant vanishes. Pinned Mathlib Basic.lean (cgf definition, zero identities) and MGFAnalytic.lean (deriv_cgf_zero) were inspected at the relevant interfaces.

SOURCE 36-40 instantiates the qualified actual_moment_cgf_derivative_recursion at n=1, with the same mu, X, h0. The exact sum has j in range 2 and is choose(1,0)*kappa1*m1 + choose(1,1)*kappa2*m0. Using m0=1 and m1=kappa1=0 gives m2=kappa2, and hr.symm gives kappa2=m2. This derives the second identity from the genuine recurrence; it does not posit a variance or coherence premise.

SOURCE 41-43 consumes qualified EE216 for kappa3=m3 and kappa4=m4-3*m2^2, with precisely the same probability law, X, h0, and actual mean. SOURCE 44-50 consumes qualified EH219; all coefficient signs and factors in its actual public type are preserved: kappa5=m5-10*m3*m2; kappa6=m6-15*m4*m2-10*m3^2+30*m2^3; kappa7=m7-21*m5*m2-35*m4*m3+210*m3*m2^2; kappa8=m8-28*m6*m2-56*m5*m3-35*m4^2+420*m4*m2^2+560*m3^2*m2-630*m2^4. The change commands use only definitional unfolding of the same m/kappa lets and do not alter any hypothesis or result.

SOURCE 51-55 expands the finite range, substitutes all kappa0,...,kappa8 identities and the exact lets, reduces factorials and powers of I, handles real-to-complex casts, and closes finite commutative polynomial algebra. Independently grouping Q by moment weight gives the following full check (the real m-values are cast into complex):

| Weight | Resulting Q contribution |
| --- | --- |
| 2 | -m2/2 = I^2*kappa2/2! |
| 3 | -I*m3/6 = I^3*kappa3/3! |
| 4 | (m4-3*m2^2)/24 = I^4*kappa4/4! |
| 5 | I*(m5-10*m3*m2)/120 = I^5*kappa5/5! |
| 6 | -(m6-15*m4*m2-10*m3^2+30*m2^3)/720 = I^6*kappa6/6! |
| 7 | -I*(m7-21*m5*m2-35*m4*m3+210*m3*m2^2)/5040 = I^7*kappa7/7! |
| 8 | (m8-28*m6*m2-56*m5*m3-35*m4^2+420*m4*m2^2+560*m3^2*m2-630*m2^4)/40320 = I^8*kappa8/8! |

For the most sensitive weight eight, the raw contributions are g-ae-bd-c^2/2+a^2c+ab^2-a^4/4. Their denominators are respectively 40320,1440,720,1152,96,72,64, giving exactly 1,-28,-56,-35,+420,+560,-630 after multiplying by 40320. Weight seven is f-ad-bc+a^2b and has coefficients -I*(1,-21,-35,+210)/5040. Weight six is e-ac-b^2/2+a^3/3. These checks account for every retained monomial; zero and first weights on the target vanish by the proved kappa0/kappa1 identities. No analytic Taylor remainder, convergence, branch choice, or limit argument is asserted or needed.

## Qualified dependency/interface reuse

EH219 qualification is COMPLETE_QUALIFIED with completed/stopped fresh reviewer /root/oq3_eh219_final_review, parentFullReportRead=true, 2 full actual TYPE, 0 required VALUE, and both statement lets covered. Source SHA256 3112808a1283faa3a1a1782893a841fb0300f6abea1a05e7ac982a5ff230e819; original O 1fc4c4a69d7081fbbba31786e697c8cc10080bd6a4e64d4dbd8714a0305d9fc2; prior independent report ff814884c8a5212f42898213ef4361509f3a5d80c12b748ca49f44bf9e4d1b37 (97 LF); receipt e6ec850e1f98a88e96e82e3d93286828db21d553b11fd9f988780c3dfef53055; actual types a871cadbe025f2dbd8c6fa2288fc2e74e6cd8c893c9f2018806fac37951ca891. All hashes were checked; the complete consumed recurrence and centered fifth-to-eighth SOURCE declaration heads, both statement lets, and all 25 LF of actual type output were read. This review uses the already qualified proofs without rereading their content or replaying their checks.

EE216 qualification is COMPLETE_QUALIFIED with completed/stopped fresh reviewer /root/oq3_ee216_final_review, parentFullReportRead=true, 3 full actual TYPE, 0 required VALUE, and both statement lets covered. Source SHA256 e45f0061beaa274734b17fe61f484f9cfc2199d0ec33d884b59b9c77c2644b8a; original O 97621896a1fb97829675965fdbdba8176ddfd30a00237d98faa326a85965bab1; prior independent report 4297ee009177bbcab1a6814fe1f0057c5d7d701b741ad5c10fa5c73f38ba3191 (108 LF); receipt b8abefd3afb4b2502ed6843cd1d37692fc0572c7bf2cd3665cf66a2969020045; actual types 364225218818d9d17e67cb99387ef11e10a417ca188c432e46d18f5116f1f8fe. All hashes were checked; the entire consumed centered third/fourth SOURCE head and all 26 LF of actual type output were read. The two tilted M-let values in that output are actual integrals against exp(v*X), and the consumed centered type is the same actual integral formula. Old proof and report content were not reread.

Thus every project theorem actually used has qualified exact evidence and compatible full mathematical interfaces. EM adds only the pinned Mathlib.Analysis.SpecialFunctions.Complex.LogBounds import beyond its two project dependencies. Toolchain is leanprover/lean4:v4.36.0-rc1 (toolchain file d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4); lake-manifest SHA256 40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e; mathlib manifest and actual git HEAD both 807d3836b165983210ee2ecf3cd28f239436949c. The current relevant Basic.lean, MGFAnalytic.lean, and additional Complex/LogBounds.lean bytes were compared directly with pinned HEAD and agree. Their hashes are respectively 73264d34c22038347bc73821a45442346ce12756475359325ebb9340a89af8fa, 4cd9ee9d7724459443aef04ad083267bc1e11da13a98b28b6cf59bee9dbb94c2, d3711d5d5b528b8d1733d531d5ae78bc77d13a68079a7243af3251abc48380f7. The existing package-view local-changes warning is preserved; no package/cache/version was altered.

## Original source fidelity, boundaries, and remaining obligations

Read-only original C:/game/shao/current/oq3/proofs/r2/report.md lines 1-158, including full sections 1-2, was read. It requires the strict range 0<beta<2/5, genuine compact tilted laws, uniform moments/covariance and the original same-model frequency work; it attributes the external weak-Cramer Edgeworth engine to Angst--Poly. EM is an auxiliary actual coefficient substitution compatible with that program. It does not certify the original report's external theorem application or quantitative uniformity merely by proving a finite coefficient identity. It changes no original assumptions, p54 repairs, source-law/E/rho data, or external-result attribution.

There is no positivity-of-variance or nonzero-m2 division. Degenerate X, including X=0, and variance zero are covered by the same polynomial proof. General Ω is not restricted by a hidden Nonempty instance; an empty Ω cannot carry IsProbabilityMeasure since mu(univ)=0 there, so that instantiation is vacuous rather than an omitted branch. No measurability or integrability assumption beyond the frozen genuine h0 is secretly added; the qualified analytic identities have exactly the consumed h0/mean hypotheses. All factorial divisions are fixed nonzero complex natural numerals, with no data-dependent denominator.

For a canonical application, h0 and hmean must be instantiated from the actual EG/EJ (and relevant EF) producers for the SAME canonical law/scalar projection; they must not be promoted to new root assumptions. The actual m2=S binding also belongs to that consumer, not this theorem. EL223's generic quantitative r9 bound is already qualified but is not an EM import/dependency and is not reviewed or accepted by this report. EN225's planned canonical whole packet is not proved here. No n-normalization, remainder size, uniform order-six expansion, full-frequency bound, inversion, exterior estimate, B-D result, or OQ3/root conclusion follows from EM alone. Those scopes remain OPEN. No novelty or paper-core claim is made for this routine finite coefficient identity.

## Existing machine evidence and transitive axiom coverage

The immutable build history has exactly one native attempt, attempt 1 at 2026-10-27T15:30:20.931043+00:00, source SHA256 as above, RC0, 6.687617598101497 seconds, producing the exact first original O above. There are no failed EM native attempts. The same-original-object all-owned audit ended RC0 at 2026-10-27T15:30:37.644891+00:00, 5.792838413268328 seconds. Original warning lines for unused push_cast, stylistic <;>, unused/unexecuted ring, and mathlib package view are retained without cosmetic edits or rechecks.

The complete Audit.lean enumerates all environment constants and selects owner module equality (not a public-name/namespace filter), rejects every new project axiom, recursively calls Lean.collectAxioms for each actual owner, and admits only propext, Classical.choice, Quot.sound. It checks the frozen theorem kind/existence and rejects empty ownership or missing frozen count. The actual original audit log reports frozen definitions 0, frozen theorems 1, all theorems 1, all declarations 1, U22EM_AXIOM_GATE PASS. Thus this exact module owns precisely the reviewed theorem, with its full 22-LF TYPE and recursive AX [propext, Classical.choice, Quot.sound], and no hidden private/generated definitions requiring VALUE output. Required non-theorem VALUE count is exactly 0; all ten theorem statement-let values are nevertheless explicitly covered above. Source scan contains no sorry, admit, new axiom, unsafe, or native_decide.

Recorded native/audit metadata uses CPU36-39,44-47, native -M8192 -j4, outer resource phase ROOT_OQ56_OQ3_40; nested memory helper phase ROOT_OQ56_OQ4_39 is its historical shared label. Recorded budgets are project140GiB, reserve60GiB, aggregate180GiB, hard200GiB, bounded clean-inactive-file discount only, no cache mutation or active-file/slab discount. This read-only review took no heavy slot or lock, made no resource changes, and ran no Lean, AX, build, upload, Git/API publication, or mathematical computation gate. One read-only source search found server rg absent and used a Python read fallback; it was not a proof/check failure and produced no mathematical/source effects. Existing successful producer/leaf evidence was never replayed.

## Verdict, telemetry, and release

Accepted review scope: complete exact EM224 SOURCE-to-frozen-statement semantics, all ten statement lets, every proof step, the sole actual-owned full TYPE, zero required non-theorem VALUES, and same-original-object recursive AX receipt. Mathematical correctness: CORRECT. Existing machine coverage for this exact auxiliary theorem: LEAN_FULLY_CHECKED, reused from original server native/audit evidence; this reviewer ran zero compiler commands. Root/OQ3 mathematical completion: not claimed. Critical gaps in the frozen EM224 theorem/proof/evidence: none.

Prescribed model/effort: gpt-6.1-sol / xhigh, fresh context. Independently exposed actual-model and effort telemetry: null / null (the reviewer API does not expose those runtime fields; spawning-owner metadata can supply the actual binding). Token telemetry is input=null, cached_input=null, output=null, reasoning_subset=null, because those counts are not exposed. These are unavailable fields, not zero counts; no subscription-percentage allocation or purchased-credit estimate is inferred.

RELEASE: The only authorized written artifact is this UTF-8/LF report. No production/source/server/cache/publication/coordination file was written. No child was spawned and no cross-chat message was sent. No mathematical source writer authority was held. After sealing this report, reviewer authority is released; writer0, heavy0, inflight0, pending external0, no uncertain write/check. This reviewer stops. Any changed EM proof or statement requires only the independent evidence affected by that actual change; unchanged exact dependency evidence remains reusable.
