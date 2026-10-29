# Unit 272 complete implementation candidate

Status: COMPLETE_PROOF_CANDIDATE; qualified=false; kernelChecked=false. This is the author's complete source and mathematical derivation, awaiting the independent complete source-to-statement/proof review and the lead's designated-server kernel/all-owned TYPE/necessary VALUE/transitive-axiom gates. Static checks are byte/structure checks only and do not parse, elaborate or verify Lean.

The sole public declaration is exactly the frozen 55-LF HEAD. SOURCE is the byte concatenation frozen PREAMBLE + frozen HEAD + PROOF + frozen CLOSING. No frozen bytes, mathematical assumptions, import, public name or statement were amended. All edits are confined to author-01. No sibling or shared implementation was changed.

## Complete argument and source map

SOURCE 72-82 proves q>0, q<=1/6, 3q<=1/2 and q*p=(p-2)/2 from exactly 2<p<=3. The q*p identity uses p>0 to cancel the denominator. SOURCE 83-106 introduces the exact c/K expressions of qualified 270 and calls that complete common-window theorem. Its common N270 is obtained before any n or original model.

SOURCE 108-130 proves (n:Real)^q tends to infinity, its reciprocal tends to zero, and a_n=(1+b_n)/(n:Real)^q tends to zero by adding the reciprocal to the supplied b_n/(n:Real)^q limit. The addition/division identity is valid also at n=0 under total field division. Since p>0, real rpow with fixed exponent p is continuous at zero (the implementation uses its global continuous extension), so a_n^p tends to zero. Cubic continuity gives a_n^3 -> 0. Thus E_n=K*(B*a_n^p+(1+Menv)*a_n^3) -> 0. No all-index positivity assumption on b is introduced; its finite prefix may be negative.

SOURCE 131-160 obtains window/lower/error thresholds, then chooses N=max N270 (max Nwin (max Nlower Nerror)). This one N is selected before n and before every original model. For n>=N it gives b_n>=1, n>=4, positive n^q and sqrt(n), b_n<=c*B^(-1/p)*n^q, and E_n<=epsilon. Only at SOURCE 161 is an arbitrary original model introduced. N may depend on the fixed class parameters, b and epsilon, and cannot depend on any n, Omega, measurable structure, mu, h, true beta/rho, w or z. The same threshold therefore permits changing models and envelopes with n.

SOURCE 162-180 extracts beta>=1 from 270, keeps the actual beta<=B premise, and uses negative-exponent antitonicity to obtain B^(-1/p)<=beta^(-1/p). Every 1<=z<=b_n therefore lies in the actual beta window. The invocation of 270 supplies the same original product-law, zero-denominator physical-statistic and closed-tail relative-error bound; no statistical or exceptional-event proof is replayed.

SOURCE 182-195 extracts only the same original r product-L2 fact from the accepted ActualQuadraticTiltMoments contract at auxiliary (n,x)=(3,0), then passes the original mu,r,w,hW,hSq,Menv,hMenv,hSqBound,hEnv unchanged to qualified 269. This gives the true original rho<=Menv, including Menv=0. It does not create a model-dependent sample-size clock or replace rho by a budget in its definition.

SOURCE 196-221 bounds beta*(1+z)^p by B*(1+b_n)^p using nonnegative-base rpow monotonicity. Positive-base composition and division identify (n^q)^p=n^((p-2)/2) and a_n^p=(1+b_n)^p/n^((p-2)/2). Real.rpow_neg converts the remaining negative power to the reciprocal, yielding the exact first payment T_p<=B*a_n^p.

SOURCE 222-256 proves (n^q)^3=n^(3q)<=n^(1/2)=sqrt(n) using n>=1 and 3q<=1/2. Cube monotonicity, rho<=Menv, positive denominators and div_pow then give T_3<=(1+Menv)*a_n^3. At p=3 the exponent inequality is equality, and a_n^3 still tends to zero. No division by Menv is used. SOURCE 257-265 adds both payments, multiplies by positive K, and finishes with the preselected E_n<=epsilon.

## Exact suppliers, API reading, and normalization

Direct qualified mathematical suppliers are 270 source SHA256 26d2ebb296f939f60461e9b32fa419e071f570a6875b894bd1b14f26320dd018 and 269 source SHA256 5fc29e9c832de61f4cb1d7e85a54b0499fe4cf263ae1190922f4196474840fc8. Their existing independent qualifications, first original objects and exact machine evidence are reused via the activation binding. The 270 machine metadata was completely parsed for its actual owner/count/axiom summaries; its 4202 TYPE lines were not rereviewed by this author. Its qualified final report, full 530-LF source, frozen HEAD and proposal were read. The complete 64-LF 269 source was read. Existing strict-wrapper-false warning disclosures are retained; this author did not rerun old producer or leaf checks.

271's frozen HEAD and proposal were read only to compare scope. No 271 source/proof was read or called, and no 271 qualification is presumed. General b=o(n^q) is handled directly and is not replaced by a fixed subcritical power window.

The established local pinned Pow.Real snapshot has SHA256 f8a26d662fb7966fa5b45aef95c8d7cf0383c9921fa3e9ee1cd2c41561e9fbfd / 50402 B and matches its pinnedGitBlobExact manifest. Needed definitions/heads include rpow_eq_pow(40), rpow_natCast(61), zero_rpow(128), rpow_neg(259), rpow_mul(414), div_rpow(488), rpow_le_rpow(550), negative-exponent antitonicity(565), and exponent monotonicity(617). Pow/Asymptotics 1-48 was read for tendsto_rpow_atTop. The exact qualified 270 source already uses the natural-cast/atTop reciprocal/eventually API patterns. The accepted SparsePopulationKernel 74-83 was read for Continuous.rpow_const, replacing continuous_abs there by continuous_id here. No local toolchain probe or execution was used for any of these readings.

At the nested-real-power rewrite site SOURCE 201-202, explicit Real.rpow is deliberately normalized with Real.rpow_eq_pow before applying the HPow-form rpow_mul lemma. The division, negative-power and natural-cube identities are proved as explicitly typed equalities using exact terms, then rewritten by those local equalities. This avoids assuming the simplifier automatically matches opaque syntactic Real.rpow and HPow forms.

## Fidelity, boundaries and open scope

The original h measurability/product-L2/symmetry/mean-zero/projection-second-moment conditions, actual g/r/v/rho/beta definitions, original p-moment integrability, beta budget and all five w/envelope premises remain literal frozen binders. P remains the product of the same mu and mOmega; D1 remains the same residualStatisticD; physical retains sqrt(centeredSq)=0 => 0; the event remains the closed tail z<=physical. No positivity of the random denominator, atomlessness, continuity of the law, new probability bound, monotonicity of b, b->infinity or fixed-power majorant is assumed.

Covered mathematical boundaries are p=3, B=1, Menv=0, b eventually equal to 1, arbitrary finite negative b prefix, oscillating/subcritical-slow b, z=1 and z=b_n. The actual comparison proof only uses n>=4. The external nominal ScalarShaoZhouFiniteCostTailInput.{u} hSZ and all five original constants are unchanged; its complete definition was read at 18-72. The full ActualQuadraticTiltMoments public contract was read at 186-279; no claim of independently rereviewing those old complete proofs is made.

No external hSZ/hSZC existence, actual p54 conditional model/mean/variance/law, unrestricted unbounded/general-L2 result, DC, full OQ56, root closure or novelty is claimed. Root scope stays OPEN. This unit proves only the frozen conditional uniform relative-error convergence in the original retained envelope class, subject to completion of the new exact-source evidence gates.

## Execution and authority

The activation SHA256 is a0afd84ad99ecf136e098a4974059c3baa56128032886fd2a8fc7b5ff78518c4 / 7458 B. All 25 input byte/hash bindings were actually verified before writing and are reverified at seal. Math-theorem and its required role/workflow/Lean references were read; more specific project instructions forbid local Lean/toolchain probes, so all Lean and AX checks are delegated to the lead's designated server.

This role executed zero Lean/Lake/AX/toolchain probe or installation, server/SSH/transfer, network, Git/API, children, Goals, schedules or sidebar operations. It introduces no extra top-level declaration or forbidden proof escape. Requested configuration is gpt-6.1-sol/xhigh. Actual backend/model/effort and input/cachedInput/output/reasoningSubset usage are not reliably exposed and are null. The unique final LASTFINALWRITE.json seals the payloads and releases all author/writer/execution/child/publication/review authority. Its six-zero statement concerns this role only, with no claim about other owners' runtime. After seal the ordinary turn ends, with no active wait or autonomous reactivation.
