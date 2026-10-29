# Unit 272 independent complete SOURCE review

STATUS: CORRECT

Decision: SOURCE_ACCEPTED_PENDING_NEW_MACHINE. The complete new 267-LF SOURCE, complete 198-LF PROOF, and complete frozen 55-LF HEAD have been independently read and reviewed. No critical mathematical gap, changed assumption, or source-to-statement mismatch was found. This is a SOURCE-stage conclusion: `qualified=false` and `kernelChecked=false`. It is not a claim that the new source has parsed, elaborated, compiled, or passed its actual-owner audit.

The independent role is `/root/oq56_unit272_review`, distinct from the unit272 author. Its only write scope is `C:/game/shao lean/drafts/oq56/unit272/source-review-01`. The author's report and static checks were read after the new proof and frozen statement; they do not substitute for this complete independent mathematical review. The math-theorem skill and its role, workflow and Lean references were read. Project and activation restrictions supersede the skill's generic toolchain-probing instructions for this reviewer.

## Exact reviewed version and binding checks

The activation is `drafts/oq56/unit272/source-review-ACTIVATION.json`, SHA256 `489a2a6cc810181e8239eef8f1cca1337d50a02044f98d79e9fe3cf961367c26`, 8373 bytes. All 30 listed input SHA256 and byte-length bindings were independently checked before the substantive review and rechecked at the SOURCE seal. The review adds no mutation of any bound input.

The exact new SOURCE is `author-01/UniformPMomentGeneralSubcriticalWindowPhysicalRelativeConvergence.lean`, SHA256 `b0bb6c13452b3d7a31c642140fce55afcd76355b2f0aa4c42f1c224441467844`, 14643 bytes, 267 LF. PROOF is SHA256 `24b48245261eeb00b402ac52766008f282088b7623bb4f99a3af3b2da0d46f0f`, 11067 bytes, 198 LF. The unchanged frozen HEAD is SHA256 `b9b6a3ef93f27f66b6b27888b870f899f73d56d18cca9d2c5e2b6e7c50d5f42b`, 3098 bytes, 55 LF.

Independently reconstructed SOURCE as frozen PREAMBLE + frozen HEAD + PROOF + frozen CLOSING, with byte-exact equality. SOURCE and PROOF are strict UTF-8 without BOM or CR and have one final LF. The new SOURCE contains no `sorry`, `admit`, new `axiom`, `unsafe`, or `native_decide` token. These checks concern bytes and structure, not Lean acceptance.

## Frozen statement and original-source fidelity

SOURCE 12-66 is exactly the complete frozen statement. It fixes `2<p<=3`, `B>=1`, all five original external constants and the exact nominal `ScalarShaoZhouFiniteCostTailInput.{u}` predicate. It then fixes the retained nonnegative environment parameters, positive t0 and nonnegative Menv. The only new sequence assumptions are eventual `1<=b n` and `b n/(n:Real)^q -> 0`, with `q=(p-2)/(2*p)`. There is no all-index sign condition, monotonicity, divergence of b, or fixed subcritical-power majorant.

For each positive epsilon the existential N occurs before every n and every probability model. For all n>=N the statement includes the eventual lower bound and then all original model and envelope binders. Thus models, measurable spaces and envelopes may vary with n. The conclusion is a uniform epsilon bound over the whole closed interval `1<=z<=b n`; it does not claim that this interval contains [1,2].

The original h assumptions are retained literally: product measurability and product L2, pointwise symmetry, product mean zero and projection second moment one. The actual g is the original projection integral; r is h-g-g; v is the original product integral of r squared; rho is sqrt(v); beta is the original integral of |g|^p. The true p-moment integrability and beta<=B remain assumptions. No definition of beta or rho is replaced by its class budget.

All retained w premises remain: a.e. nonnegativity, the current n-dependent polylogarithmic height, integrable square, square integral at most Menv, and the product envelope for this same original r. The finite-product P uses the same mOmega and mu. D1 is the original residualStatisticD. The physical statistic still equals zero when sqrt(centeredSq)=0 and otherwise uses the original quotient. The event is the actual closed tail `{z<=physical}`. No atomlessness, random-denominator positivity, altered model law or modified zero convention has been inserted.

I read the complete external nominal predicate at NormalizedIntegrableTailAssembly 18-72. It retains the five positive constants, arbitrary normalized independent sources, full and true-deleted costs and their integrability/positivity requirements, and both original closed-tail inequalities with their actual exceptional events. Unit272 assumes this predicate exactly and does not prove its existence or change the Shao-Zhou attribution.

## Complete proof review

SOURCE 67-83 / PROOF 1-17: p>2 implies p>0 and q>0. Cross-multiplication by the positive 2p turns q<=1/6 into the supplied p<=3 condition; hence 3q<=1/2. Cancellation using p nonzero proves the exact identity `q*p=(p-2)/2`. No endpoint p=3 is discarded.

SOURCE 84-103 / PROOF 18-37: cMoment, cRemainder, cAbsorb, cTilt, cGeometry, c, K0 and K agree exactly with qualified270's frozen contract. Calling 270 at the fixed class parameters yields c>0, K>0 and a class-only N270>=4 before any n or original model. B>=1 gives B>0, so `commonA=c*B^(-1/p)>0` is independent of every model.

SOURCE 104-114 / PROOF 38-48: the natural real cast tends to +infinity; q>0 gives n^q->+infinity and 1/n^q->0. Adding the supplied b/n^q limit yields `a_n=(1+b_n)/n^q ->0`. The quotient addition identity is valid for total real division even at n=0. It does not require b to be nonnegative. All subsequent exponent comparison and division steps are performed only after n>=4.

SOURCE 115-124 / PROOF 49-58: the fixed positive exponent p makes real rpow continuous at zero, so a_n^p->0. The code uses the globally continuous real-rpow extension with the sufficient p>=0 branch of Continuous.rpow_const, not a false all-index positivity assertion about a. This remains valid for a finite negative prefix: on negative arguments real rpow is the real part of complex power, whose magnitude decays as |x|^p at zero when p>0. Cubic continuity separately gives a_n^3->0. The pinned Pow.Real definition, zero_rpow and the existing Continuous.rpow_const application pattern were read as API context; no claim of elaboration is made.

SOURCE 125-140 / PROOF 59-74: define the model-free sequence `E_n=K*(B*a_n^p+(1+Menv)*a_n^3)`. Limit addition and fixed scalar multiplication give E_n->0. The b/n^q limit supplies Nwin with b/n^q<=commonA; hbLower supplies Nlower; the E limit supplies Nerror with E_n<=epsilon. Their maximum with N270 is the one selected N. It is chosen before n, Omega, mOmega, mu, h, beta, rho, w or z. No exchange of model-specific eventual quantifiers occurs.

SOURCE 141-160 / PROOF 75-94: for arbitrary n above this N, every component threshold is below n. In particular n>=4, n as a real is at least one, n^q and sqrt(n) are strictly positive, b_n>=1 and 1+b_n>=0. The preselected window inequality can therefore be multiplied by positive n^q, and E_n<=epsilon is already available before the model is introduced. The lower-bound conclusion is supplied explicitly.

SOURCE 161-177 / PROOF 95-111: only now introduce an arbitrary original model. The same 270 contract supplies the actual beta>=1 and its rate theorem. Together with the retained beta<=B, positive p gives the nonpositive exponent -1/p and the correct antitonic inequality `B^(-1/p)<=beta^(-1/p)`. Multiplication by nonnegative c and n^q preserves it. Thus every z<=b_n lies in the true-beta window required by 270. The proof does not assume that window, or tilt, absorption or geometry conditions, as extra premises. The unused stronger nonempty-window output of 270 does not alter the desired interval.

SOURCE 178-193 / PROOF 112-127: the extracted rate concerns exactly the same physical closed tail under the same original P, with first term `beta*(1+z)^p*n^(-((p-2)/2))` and cubic term `(1+rho)*(1+z)^3/sqrt(n)`. The original quadratic contract is invoked at the fixed auxiliary pair (3,0). Its inputs are precisely the retained h assumptions; 3>=3, 0>=0 and the nonnegative auxiliary window are valid. The sixth conjunct of its complete public output is L2 of this same original r under mu.prod mu. Extracting it introduces no sample-size or model-dependent asymptotic clock. Qualified269 then receives this r, this mu and the exact current envelope assumptions, giving `0<=v<=Menv^2` and `0<=rho<=Menv`. The auxiliary tilted measure from the supplier is not used in place of the original measure.

SOURCE 194-221 / PROOF 128-155: z>=1 and z<=b_n imply `0<=1+z<=1+b_n`. Monotonicity of rpow in a nonnegative base for p>=0, beta<=B, and nonnegative factors give `beta*(1+z)^p<=B*(1+b_n)^p`. For positive n and n^q, composition and quotient identities give `(n^q)^p=n^((p-2)/2)` and `a_n^p=(1+b_n)^p/n^((p-2)/2)`. Real.rpow_neg changes the remaining negative n power to the reciprocal. The exact resulting payment is `T_p<=B*a_n^p`, with no asymptotic equality replacing a bound.

SOURCE 222-239 / PROOF 156-173: natural-cube/rpow agreement and positive-base composition give `(n^q)^3=n^(3q)`. Since n>=1 and 3q<=1/2, exponent monotonicity gives `(n^q)^3<=sqrt(n)`. The explicit quotient cube identity is `a_n^3=(1+b_n)^3/(n^q)^3`.

SOURCE 240-256 / PROOF 174-190: rho<=Menv and monotonicity of the nonnegative cube bound the cubic numerator by `(1+Menv)*(1+b_n)^3`. Both required denominator signs are checked: sqrt(n)>0 and `(n^q)^3>0`. Because the latter denominator is no larger than sqrt(n), division by it gives an upper bound, in the correct direction, for the nonnegative numerator. Consequently `T_3<=(1+Menv)*a_n^3`. At p=3, 3q=1/2 and this denominator comparison is equality; decay still follows from a_n->0. No division by Menv or rho occurs.

SOURCE 257-264 / PROOF 191-198: add the two payments and multiply by K>=0. The resulting bound is exactly E_n and is at most the preselected epsilon. The entire original physical closed-tail expression is unchanged in this last comparison. SOURCE 265-267 contains only the final blank line and section/namespace closure.

## Direct supplier reuse and comparison boundary

Qualified270 source SHA256 is `26d2ebb296f939f60461e9b32fa419e071f570a6875b894bd1b14f26320dd018`; its qualification seal is `e2cb8c05cafcd2ca2e80865abd1d4b5ca9164c38048fd81133a4908c9f3f11d0`. Its full frozen 67-LF contract and complete current independent final report were read. Qualified269 source SHA256 is `5fc29e9c832de61f4cb1d7e85a54b0499fe4cf263ae1190922f4196474840fc8`; its qualification seal is `e9e44739fb2b93d2017200794490543569acc03cd87ba3e21218f7068ebad610`. Its complete public contract was checked. The old 269 source happened to be displayed in full; its already accepted proof is reused, not assigned a new complete-proof review here.

Both local seals record qualification, kernel acceptance, a qualified independent complete source/proof plus actual-TYPE review, the same first original object and recursive axioms restricted to propext, Classical.choice and Quot.sound. I additionally verified eight locally bound seal records: for each supplier its independent qualified verdict, independent manifest, independent release and parent final intake. Their source and first-object identities agree with the consumer dependency binding. This is exact accepted-evidence reuse, not a new remote observation or a replay of old producer/leaf checks. The old strict-wrapper-false disclosures remain unchanged. Neither lane qualification is misrepresented as Root acceptance.

The complete original quadratic public contract at 186-279 and complete external predicate at 18-72 were read. Old270's full proof and its 4202 actual TYPE lines were not re-reviewed or rerun. Unit271 is a scope comparison only and is absent from imports and callees. In particular general b=o(n^q) cannot be replaced by one fixed power n^s with s<q; a near-critical sequence such as n^q/log(n) illustrates the need for the direct 270 argument. No qualification or future result of 271 is presumed.

## Boundary checks, remaining gates and scope

Covered by the actual argument are arbitrary finite negative b prefixes, eventually b=1, nonmonotone or oscillatory b satisfying the two stated limits, arbitrarily slow subcritical approach, p=3, B=1, Menv=0, Cenv=aenv=0, every permitted positive t0 and both closed endpoints z=1 and z=b_n. The proof uses no sign information on b before Nlower. The case p=2 is excluded by the original strict hypothesis, and a fixed positive multiple of n^q does not satisfy hbSmall. No full critical-window convergence is claimed.

Before qualification the lead must run the new exact272 source on the designated pinned server and preserve the first successful original object; audit every actual owner by module ownership, including private/generated declarations, with complete TYPE, necessary non-theorem VALUE and recursive AX; then explicitly reactivate this same independent FINAL identity for complete actual-output semantic review and exact source/object binding. Actual owner counts, TYPE/VALUE coverage, new native result and new AX result are unknown at this SOURCE stage. A successful old supplier receipt does not fill any of those new272 gates.

This is a conditional corollary in the retained bounded-product/polylog-envelope class under the explicit external hSZ input. It does not establish external hSZ/hSZC existence, actual p54 conditional model/mean/variance/law, unrestricted unbounded L2 results, DC, full OQ56, Root closure or mathematical novelty. These broader scopes remain OPEN.

This role ran no Lean/Lake/AX/toolchain probe or installation, server/SSH/transfer, network, Git/API, children, Goals, schedules or sidebar operation. Requested configuration is gpt-6.1-sol/xhigh; actual backend/model/effort and the four usage fields are not reliably exposed and remain null. The final SOURCE-CHECKPOINT seals this stage, records role-local six-zero and ends the ordinary turn without active waiting. The SAME independent FINAL identity remains dormant, requiring explicit later activation; no further SOURCE writes are authorized after the seal.
