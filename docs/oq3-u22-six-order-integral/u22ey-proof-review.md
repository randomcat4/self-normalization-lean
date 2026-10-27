# EY236 complete independent final review

STATUS: CORRECT

The exact final EY236 source proves the complete frozen public declaration, with all ten statement lets unchanged. Its literal actual scalar-CGF coefficients and sqrt(n) normalization identify the Gaussian-weighted filtered finite-word polynomial with all six explicit coefficient rows. I found no missing assumption, changed quantifier, incorrect coefficient, proof gap, forbidden proof device, or uncovered actual owned declaration. This accepts this algebraic identity only; it does not assert a new distributional error estimate or close the original OQ3 root.

## Reviewer boundary and full reading coverage

Reviewer: `/root/oq3_ey236_final_review`; fresh independent assigned model/effort: `gpt-6.1-sol` / `xhigh`. I did not author or edit either proof attempt. I used math-theorem and its prompt/workflow/Lean-verification references, not math-ultra. I read all 32 frozen-declaration lines before reading the proof, then read all 48 final source lines, all 48 failed-attempt source lines, all 22 actual-type lines, the complete 26-line scope, and the entire EY receipt, audit record, build history, audit program, bearing-dependency binding, server-dependency binding, qualified-dependency binding, and own-first-object binding.

For the actual bearing interface I read the entire 30-line EX235 frozen interface and all 33 actual-type lines, including its two generated theorem types, all nine statement lets, its qualification and relevant object/dependency bindings. I checked its exact qualification, source, type, receipt and prior independent-review hashes. Its already accepted full proof/review/kernel/axiom evidence is reused; I did not conduct another full review of the old EX proof. I also read EW234's relevant final frozen public conclusion and actual TYPE segment defining the same X, kappa, a, Pn, E and rho, and its complete qualification; I verified its exact evidence hashes without re-reviewing its old full proof. ER229's exact qualified import evidence was checked only as an existing import/API dependency; EY does not invoke ER's analytic theorem.

I read original `C:/game/shao/current/oq3/proofs/r2/report.md` lines 1-158 and its terminal scope, all of `repair01.md`, and all of `verdict.md`. I read the current OQ3 phase40 resumption authority, current applicable AGENTS direction, and relevant SERVER/TEAM execution and independence rules. The explicit 2026-10-27 OQ3 resumption supersedes the old pause entries. This reviewer took no lane ownership and executed no server, Lean, axiom, upload, Git, publication or child-agent operation. Only this report was written.

## Exact byte provenance

All following new-unit local files were read and hashed as bytes; all have UTF-8 LF text and zero CR bytes. The final frozen declaration is exactly the final source's theorem header before `:= by`; the deterministic byte-text comparison returned true. No declaration or premise changed between the failed and successful source.

| EY236 artifact | SHA256 | Bytes / LF |
| --- | --- | --- |
| Frozen declaration | `701601d939af1d39249261e20ea600f28bea70f5dc30de9a9c54ee549d10f63d` | 1604 / 32 |
| Final source | `164b9973082c4363e1494aec6b138568c7d66b776b10fd57ba092ee989bc2c77` | 2152 / 48 |
| Full actual TYPE artifact | `3be0ff3c232a7e7ffcb2577d44835518a144c40519d574936a71e4c44f277119` | 1320 / 22 |
| Failed attempt01 source | `d0e77dd2cdd17b31ffae1b2036127346631c335befbed197374921d1c7dd6223` | 2143 / 48 |
| Unit scope | `a63f331725060f06f7342e5b318a0cdeb0a919715c26f78b9aee1a3414a90c40` | 1625 / 26 |
| Receipt | `ea5a6b5a01fa61d8818ff10f80ee358b48b1639ac312894b470aa398e7a620ef` | 7932 / 267 |
| Audit record | `272eda0d74e022a974c40f13ad619d4812c02348ab034db3a11deed9881d5812` | 3046 / 103 |
| Build history | `7f89edd96b2ccd06b48ba82bb9377ea222bd67e2d1f3aa289002a1257f83f7c1` | 4540 / 164 |
| Audit program | `3a9d137b99fa54783371700e897fdb021cb1e9b96a616989e81b56e42a97c701` | 2032 / 47 |
| Bearing dependency binding | `b576fecdd8c9a62f6c8bf7f9216cd7f82d7cdde22f8361e8ba0dea2ca7dadcfa` | 417 / 8 |
| Server dependency binding | `02babc157c42b3769a594b149a820f29abca428d28373d67f68ad5f8e0792f89` | 439 / 9 |
| Qualified dependency binding | `b2ad69ff820a3dfe1b2e1d039553b1d54e0439c0baccba9b20439e519c747a28` | 1436 / 30 |
| Own-first-object binding | `32bdadb7f248a76a069c432ab0cd8a7f13909798e0db49d76b725e32d5153462` | 579 / 10 |

The original read-only report hash is `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55` (20102 B / 523 LF); repair01 is `9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd` (5846 B / 226 LF); verdict is `fd0a5732845aa96ab1725e6d1e52676502092e49d2c00225ce1fde26ac06f3b5` (3041 B / 58 LF). These are provenance and scope references, not newly machine-checked source claims.

## Frozen statement, all ten lets, and all actual types

The sole public theorem is `Shao.OQ3.actual_cgf_six_order_edgeworth_polynomial_identification`. It quantifies over every supplied `mu : Measure (Fin 2 -> R)`, every natural n, and every real u,v. No probability-measure, moment, analyticity, covariance, positivity, independence or n>=1 premise is silently used. Every let below agrees in the frozen text, final source and full actual TYPE.

| Let | Exact meaning and review |
| --- | --- |
| X | The same actual direction `y -> u*y 0 + v*y 1`, on the same supplied measure's domain; no replacement random variable or law. |
| kappa | `j -> iteratedDeriv j (ProbabilityTheory.cgf X mu) 0`; literal derivatives of that scalar CGF, not free cumulants or independent formal input. |
| A | On Fin 6, `A_j = (I^(j+3)/(j+3)!)*kappa_(j+3)` after the explicit real-to-complex coercion; orders exactly 3 through 8, with the correct I power and factorial. |
| a | `a_j = A_j / (sqrt(n) : C)^(j+1)`; exponents exactly 1 through 6. |
| B1 | `A0`. |
| B2 | `A1 + A0^2/2`. |
| B3 | `A2 + A0*A1 + A0^3/6`. |
| B4 | `A3 + A0*A2 + A1^2/2 + A0^2*A1/2 + A0^4/24`. |
| B5 | `A4 + A0*A3 + A1*A2 + A0^2*A2/2 + A0*A1^2/2 + A0^3*A1/6 + A0^5/120`. |
| B6 | `A5 + A0*A4 + A1*A3 + A2^2/2 + A0^2*A3/2 + A0*A1*A2 + A1^3/6 + A0^3*A2/6 + A0^2*A1^2/4 + A0^4*A1/24 + A0^6/720`. |

The finite polynomial is exactly the sum over q in Fin 7, then sigma : Fin q.val -> Fin 6, with coefficient 1/q! and cutoff sum_i(sigma_i.val+1)<=6. The product uses the actual a at every letter. The same factor `G = exp(-((u^2+v^2 : R) : C)/2)` multiplies both sides. The right side is exactly `G*(1+B1/c+B2/c^2+...+B6/c^6)`, with `c=(sqrt(n):C)`. There is no changed cutoff, missing factorial, sign, degree, Gaussian normalization or range of q.

The actual ownership artifact has one DECL, one theorem KIND, the complete TYPE including all ten lets and all six rows, and the axiom list `[propext, Classical.choice, Quot.sound]`. There are exactly 1 public theorem, 1 actual owned declaration/TYPE, 1 actual theorem and 0 required non-theorem VALUEs. No generated or private owner is omitted. These counts are actual module-owner audit counts, not inferred from a namespace or copied from the dependency's counts.

The absence of analytic hypotheses is appropriate for this identity: the proof is valid for arbitrary complex coefficient values, and the actual CGF derivatives merely supply those values. For an arbitrary measure this does not claim the CGF is analytic or that its total Lean derivatives satisfy probabilistic cumulant identities. The later canonical analytic consumer obtains such information from the qualified actual-law development under its own hypotheses.

## Complete proof review

At source line 41, `intro X kappa A a B1 B2 B3 B4 B5 B6` introduces precisely the frozen let definitions. It neither drops assumptions nor replaces the defined derivatives by free parameters. The proof may treat the resulting A values abstractly because the EX polynomial identity holds for every A.

At line 42, `apply congrArg (fun z : C => G*z)` reduces the goal to the finite polynomial identity without cancelling G, dividing by it or assuming it is nonzero. This is ordinary congruence for multiplication by the exact common factor, so it is valid even independently of any property of the complex exponential.

At lines 43-45, the complete argument is EX235's `complex_six_order_weighted_polynomial_coefficients A (1/c)`, followed by `simpa only [a, B1, B2, B3, B4, B5, B6, one_div, one_mul, inv_pow, div_eq_mul_inv]`. EX supplies exactly the same q/sigma/cutoff polynomial and exactly the same six B rows, with its letter values `A_j*t^(j+1)`. Substituting t=1/c gives `A_j*(c^-1)^(j+1) = A_j*(c^(j+1))^-1 = A_j/c^(j+1)`, which is EY's a. Each right-side `B_j*t^j` becomes `B_j/c^j`; the j=1 term is `B1/c`. The listed simplifications are exact field equalities and unit-factor normalizations; none uses cancellation requiring c!=0. All lets B1..B6 are unfolded at the same values, so this is the entire required proof.

As a coefficient cross-check of the applied interface, the six rows correspond to all positive-weight partitions of 1,2,3,4,5,6, with A_r carrying weight r+1. For weight 6 the eleven partitions are 6;5+1;4+2;3+3;4+1+1;3+2+1;2+2+2;3+1+1+1;2+2+1+1;2+1+1+1+1;1+1+1+1+1+1. Their multiplicity denominators are respectively 1,1,1,2,2,1,6,6,4,24,720, exactly the B6 row. The lower rows have respectively 1,2,3,5,7 terms and their displayed factorial multiplicities match. This checks the applied six-row statement and its transfer, without repeating EX's already accepted recurrence/coefficient proof.

The failed attempt01 and final source have identical statements and differ only by adding `one_mul` to this final `simpa only` list: replacing `one_div, inv_pow` with `one_div, one_mul, inv_pow` produces the final file exactly. The +9 byte repair is solely proof normalization. The prior failure remains evidence of that failed proof attempt; it is not a pass, and no accepted successful producer was replayed.

## Boundary and quantifier attack

For n=0, c=0. Every j in Fin 6 has j.val+1>=1, so EY's `a_j=A_j/0=0` under the total complex-field division convention. The q=0 word has empty weight sum 0 and empty product 1 and contributes exactly 1/0!=1. Every q>=1 product has a zero letter factor, so all other retained terms vanish. Every explicit B_j/c^j is also zero. Both complete sides therefore equal G. No accidental zero-denominator side condition is missing.

For n>=1, c is the usual positive real square root coerced to C, but this proof does not need positivity. The same algebra works for u=0, v=0, both zero, negative coordinates, arbitrary measures, and zero coefficient values. It invokes no differentiability theorem at a potentially undefined analytic point and no interchange of derivative, expectation or limit. The sums and products are finite. No probabilistic approximation, almost-everywhere statement, coupling or asymptotic limit is substituted for the displayed exact equality.

Including n=0 here does not enlarge EW234's error theorem: that theorem still explicitly has n>=1, its own local frequency window and actual-law analytic hypotheses. EY cannot remove those hypotheses by an equality rewrite.

## Dependency qualification and canonical bearing

EX235's 30-LF freeze hash is `c217719c69b3fdab7ed02ccecbb79f0a6459ff66ef951ef6ddceef6c49cdaef3`; source `8d1d737258428a93f4d2189fc7bd37bf42d105349300c41bbdc1271a2e7c95d4` is 3828 B / 102 LF; full 33-LF actual TYPE hash is `783501bb536c62ca8f193ab37746bede715b22ff321984057fe69db1d426b114`. Its 2 public theorems, 4 actual TYPEs, 9 lets and 0 VALUEs are covered by accepted independent review `98a6e7eb6887ef21d76be0e3e76df81f206f3fc36ac27a4a990449cca3a0a12e` (144 LF, parent fully read) and receipt `d1af742848cc244ba9dd7c8cbf4a47fbd3a9b3337c470fb1214a9f998426b8d4`. Its qualification hash is `6fcfdad9d34fb65ed93ec8fee4b032cfb14ab84c842fe2a37e09d787e6151928`, state COMPLETE_QUALIFIED; first original O is `3a744b7db87235f28ad57d1f0e7b3b2ceba589b010d968b88ba2a458982085d9` / 906440 B.

EY's bearing/server records accurately preserve the historical fact that EX was exact native/all-owner pass but final-review pending when EY was checked. The later complete qualified-dependency record now binds the identical EX source, TYPE, first O, receipt and completed independent review; `sourceAndFirstOUnchanged=true`. It supplies the previously required final-qualification condition without mathematical source change or replay. The server binding targets the accepted-source-view link for `ComplexSixOrderPolynomialCoefficients.olean` and records zero old-entry changes, new links and cache writes. The stale pending wording in the immutable native-time records is not a current missing proof.

EW234's relevant interface is the final conjunct of its 275-LF freeze, hash `13d76df5bfd55879bfa1d67937272bcdd28c6a83e4f4281f730625b92abfd7a9`. Its qualified source `658e38ea04ae94b9744e9152ad0bd671a89b09c5c5082da6117256eb2f7a2935`, full actual TYPE artifact `0619ac4e6af1b13276c4914345b700c8ec02fd6244b3a6cd9a9ade5e53b3e620`, independent review `71d1a82ed270f5d23c75e672bd0f4109e306e2f2bb100f944696222f583c77c8`, receipt `7d86183866f494c56c7fa767695689637914eb4f5154125ee2d7eeb151e3d8e8` and qualification `74ff7d7ba88079fb6f9092d16653eb471963ae44f6cf30aaf121f3eb3dbbb798` all match local bytes. Its first original O remains `197ec4621ba0f19c61ad59eb9f0a0de138513ccd8997b930e5786344e7a356a9`.

That EW conclusion defines the same `X(y)=u*y0+v*y1`, kappa from `cgf X (laws p)`, and a_j as exactly EY's A_j divided by c^(j+1). Its Pn is exactly EY's left side, including G, Fin 7, Fin q.val -> Fin 6, 1/q!, cutoff<=6 and the same product. Hence the canonical substitution `mu=laws p` identifies that very polynomial with the explicit six-row expression; it requires no different law, free cumulants, coefficient-coherence premise, or a new E/rho witness. EW's existing E and its actual iid pushforward rho remain the same. EY itself has no E/rho or CF-error claim. Rewriting EW's error conclusion is possible while preserving its C, delta, n>=1, p and frequency guard, but that larger rewritten error theorem is not separately declared in EY.

The second import is qualified ER229 (`ActualCGFNormalizedOcticPolynomial`), source `ae3883790c028b072e081216fd09b20d2c4ab81e54ee7fd64bc4b4d6b493aa19`, prior review `4ec53e1fe4c44a9a1b49052f584b5e0d83aa540167a0f152d8d9bf98325adef5`, receipt `8b9b645ab79d13d8ff34b720e71bdc15730fdd63aa19bcb874ef18c9f53bbf48`, actual TYPE hash `c50ff8a304ebd643f23b7d17047964c83b7c02cb5473c5e64a5fd251651bb373`, first O `81721abf718d8592feb7788e37b3d20330e0be3b1c0a418494c3cdc219f12f0f`. EY calls only the EX polynomial theorem; the ER import makes the existing CGF environment available, rather than adding an analytic premise or analytic conclusion to EY. Its old proof and machine evidence are reused without rerun.

## Exact-source server kernel and transitive-axiom evidence

The pinned project toolchain is `leanprover/lean4:v4.36.0-rc1`, mathlib `807d3836b165983210ee2ecf3cd28f239436949c`, shared-v34 read-only package view. I read the project pin and supplied execution policy; I did not probe or run a local Lean installation. EY native002 at 2026-10-27T17:16:25.733180+00:00 returned RC0 on the final 2152-B source, 5.415929527953267 seconds. Its log is bound as `fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626` / 133 B, with only the recorded shared-package historical dirty warning. Native001 RC1 is retained with log `a2e3194b962a87514a2aa905f9f95ea024bfc97559402d75476c8c52d431ae86` / 2244 B and the exact failed source hash above.

The successful first original O is `ee96995c2958896e461a14c52fe73d65adae01c96981f3e08c5f9a17873128eb` / 93000 B. The all-owner audit used that same first object, returned RC0 in 5.7546181827783585 seconds, and is bound to log `bc05a658f9718470fcf321455e6926e00df849d808d9db8c85fbf71b74952857` / 1572 B. Source, receipt, audit record, full actual TYPE and own-first-object link binding agree. The own link records one new own-first-O link, zero old-entry changes, zero shared-cache writes and zero binary copies.

The entire audit program checks its target exists and is a theorem, discovers every constant whose actual environment module owner is EY's module, rejects any newly owned axiom, calls `Lean.collectAxioms` for every owned declaration, rejects any axiom outside propext/Classical.choice/Quot.sound, emits each full TYPE and any definition VALUE, and checks the frozen target count. The supplied complete output has exactly the sole expected theorem. Its complete transitive axiom set is the standard whitelist. The source additionally has no occurrence of sorry, admit, a new axiom, unsafe or native_decide. There is no unreviewed non-theorem VALUE or hidden generated-owner gap.

The receipts record native -M8192 -j4, phase ROOT_OQ56_OQ3_40, CPU36-39/44-47 and current resource-helper hash `0b3119b972b736fec56c818717462cfa8f1fea897dea94baa2120a19d2b1acda`. Its internal phase39 label is the already documented unchanged memory formula, not a reactivation of an obsolete lane allocation. Project140GiB/reserve60GiB/aggregate180GiB/hard200GiB, cacheMutation=false, activeFileOrSlabDiscounted=false and OOM/max events0 are recorded. These are exact supplied author/server receipts, not a fresh runtime observation by this local reviewer. No successful source/object check or old producer/leaf axiom check was replayed in this review.

## Original scope, attribution and limits

The bearing purpose is the actual sixth-order Edgeworth correction in the original R2 positive repair. EY closes the exact coefficient-identification/reciprocal-power substitution step for the existing finite local polynomial. It neither proves the external uniform Edgeworth theorem nor establishes its assumptions for arbitrary mu. The original corrected attribution is Song's 2020 uniform-in-law weak-Cramer theorem, Theorem 2.1 with s=8, as stated in repair01; the old report's Angst-Poly diagonal attribution is not promoted as the corrected uniform input.

The strict original range remains 0<beta<2/5. EY supplies no equality endpoint, optimal-threshold result, uniformity beyond the original law class or new probability approximation for arbitrary measures. The p54/leading-constant repair, explicit far-field localization for the positive result and previously accepted counterexample evidence remain unchanged. The original constant remains `v_corr=-t_hat0*sqrt(det Delta)*sqrt(Lambda1)` in the corrected boundary-Laplace normalization; this finite polynomial identity does not prove that reconstruction.

Integrated errors, full-frequency control, exterior contribution, Fourier inversion/Hermite-density identification, B-D consumers and the original OQ3 root remain OPEN. A pointwise finite identity cannot substitute for these estimates. No novelty or historical-priority certification is supplied; the six coefficient rows are standard finite algebra, and this review concerns faithful formal linkage to the actual CGF polynomial.

## Verdict, usage and release

CORRECT for exactly the frozen EY236 statement, final source SHA `164b9973082c4363e1494aec6b138568c7d66b776b10fd57ba092ee989bc2c77`, all ten statement lets, its one complete actual TYPE, zero required VALUEs, the entire proof and the supplied exact-source same-first-object kernel/recursive-axiom evidence. No repair or uncovered obligation remains inside this unit. EX's final qualification condition is satisfied by the unchanged-source/first-O binding. Parent acceptance still requires reading this entire report and binding its exact bytes; this reviewer does not publish, merge, qualify on behalf of the parent or claim original-root completion.

Usage record: model=gpt-6.1-sol; effort=xhigh; input_tokens=null; cached_input_tokens=null; output_tokens=null; reasoning_subset_tokens=null. Reliable per-review token counters are not exposed here; no invented count, credit amount or subscription-percentage allocation is asserted.

RELEASE: COMPLETED_STOPPED. Reviewer writer=0 after report completion; server_execution=0; Lean_AX=0; in_flight=0; pending_external=0; children=0. No subsequent work or write is scheduled by this reviewer.
