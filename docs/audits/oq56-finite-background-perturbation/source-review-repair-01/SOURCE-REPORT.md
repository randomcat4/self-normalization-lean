# Unit278 repair01: SAME independent affected SOURCE review

STATUS: CORRECT

The repaired complete source is accepted at the independent mathematical SOURCE layer. The three changed complete proofs, their frozen interfaces, and their dependency/caller contexts have been independently reviewed. No new mathematical/fidelity gap or hidden assumption was found. The prior complete SOURCE evidence is reused only for the independently verified byte-identical scope. `sourceAccepted=true`, `kernelChecked=false`, `qualified=false`.

## Exact activation and coverage method

This is explicit reactivation of the SAME independent reviewer `/root/oq56_unit278_review`, separate from the implementation author. Its activation SHA256 is `4b225b33355c8ddee1e13b54e4852126f27faeefab781f231469a4f51abd77e1`, 55078 bytes. All 246 bound input SHA256/byte pairs passed independently before the first report write; an actual ACK246 was sent to the parent. They are rechecked before the final seal. Only this new `source-review-repair-01` directory is writable.

The current complete source is `C:/game/shao lean/drafts/oq56/unit278/author-repair-01/FiniteBackgroundPerturbation.lean`, SHA256 `4ef892a876624e601fd98f32a49f383b54b3748af0d4226bf98f50a9152646c3`, 30130 bytes, 694 LF. It contains the same 33 declarations, 14 definitions and 19 theorems. Its streams have HEAD118 LF, PROOF523 LF, fixed-RHS36 LF, PRE14 LF and CLOSE3 LF.

I read the full current bodies of T08 (13 LF), T12 (35 LF) and T13 (29 LF), their entire heads, and their actual uses in T10, T17 and T19. The full repair author report/MFT, diagnostic-coverage file and all three complete normalized server diagnostics were read. Accepted supplier usage locations for `Finset.sum_mul` and `abs_add_le` were inspected as narrow read-only API context, without reopening the supplier proof qualification or running a probe.

I independently compared all component bytes to the prior author packet and the frozen components, verified every current component source byte/line interval, and reconstructed the complete source. Exactly T08/T12/T13 changed, and each equals the precise expected replacement of its old body. The other 16 proofs are byte-identical, as are all 33 frozen HEADs, all 14 fixed RHS, PRE and CLOSE. The unchanged proofs account for 446 LF, and the three independently reread current proofs account for 77 LF, totaling all 523 current proof LF. All concatenated streams are checked against their current components before seal.

The prior complete review of source SHA256 `29285b2347c5fcf61af5703d6d6756caf56f3364471dc376a690812ac69e0d43` remains sealed in `source-review-01`. Its manifest SHA256 is `79c73fc59b19224a3df9198171a00918a89f098a152c155ac1f77c484bb68245`, and final release SHA256 is `6858d02f1538f2040ccb742833091f031c311e095df7d5c2f06a2c1706124158`. Complete current coverage is the combination of that exact unchanged evidence and the present complete affected-body/context review. I do not claim a redundant literal rereading of all 694 current lines or a new supplier proof review.

## Actual first native failure is retained

The first native checked the old 693-LF source, ended naturally RC1 after 5.047405 seconds, and reported three errors and fourteen warnings. It produced no object and no AX result. The receipt binding is SHA256 `7ffda0617d3c9ba695e0c6f4aa06153c9835a863210cac69cfa3c0adbf6d94d0`, 37468071 bytes. The compact terminal inspection records all owned processes ended, no live owned members, no timeout/cleanup/ownership issue, and all 36060 protected artifacts equal before and after. The raw receipt/logs remain on the server; I read the bound complete normalized diagnostics without accessing the server.

The three complete errors were:

* Old line317, column34: Unknown constant `Finset.sum_div` (diagnostic SHA256 `1738152159b14acc074fe2cf6ca2da34f7e70f0369bdb5e2020faa8619ab47b9`).
* Old line429, column22: Unknown identifier `abs_add` (diagnostic SHA256 `cca62cbac21d6be2de3cb2de3fc7862f8df2f4ed848f2cd5b6020698551def3b`).
* Old line473, column22: the same complete unknown-identifier `abs_add` message and diagnostic SHA256.

These are actual elaboration failures, not a proof pass, mathematical counterexample, timeout or quota result. My earlier SOURCE review certified mathematical reasoning and frozen-statement fidelity while explicitly leaving API spelling/elaboration and kernel evidence pending. The current review does not erase or relabel that failed attempt. No uncertain request or check was replayed by this reviewer. The repaired current source has no machine pass in this packet.

## T08: full affected derivation and caller

Current T08 head lines303-310 and body lines311-323 are fully reviewed. The proof body SHA256 is `08da2b9980e8df986c627764ece607e47029abe9ec06541930d51e6234a60a46`, 411 bytes/13 LF. Its fixed claim remains

    a0 = G/M + (2FB+C_AB)/(M*(N-2)) - F/((N-1)*(N-2)).

It has only the original symmetric-r premise, no cardinal positivity or nonzero-denominator assumption. After unfolding the actual adjusted row, `Finset.sum_add_distrib` separates sum_B g from the sum of residual-row quotients. `simp only [div_eq_mul_inv]` rewrites every quotient in the local identity as multiplication by the same scalar inverse `(N-2)^-1`. Thus the needed subidentity becomes

    sum_(i in B)(R_i * d^-1) = (2FB+C_AB) * d^-1,
    R_i=sum_(j in univ.erase i)r_ij, d=N-2.

The reverse `Finset.sum_mul` rewrite collects the sum as `(sum_B R_i)*d^-1`. The already reviewed exact T05 `background_original_row_sum B r hsym` supplies sum_B R_i=2FB+C_AB with the correct cross orientation and diagonal cancellation. The local sum identity is therefore established without any division-specific API name or field cancellation.

Unfolding the original anchor and block mean, substituting this local identity, expanding division and inverse products, and ring normalization yields the unchanged head. This remains valid for total division when M or d is zero; no step cancels a possibly zero denominator. No desired coefficient identity was inserted as a premise.

The direct caller is the unchanged T10 current lines368-390, whose complete current head and use were read. It calls T08 with the same B,g,r,hsym, then uses the unchanged square-root scaling and full pair partition before deriving real K=N-M and justifiably clearing its positive endpoint denominators. T08's output still supplies exactly the expected G, FB and C_AB coefficients. This repair cannot alter the outer sqrt N, the real K-1 cross coefficient, or any original n-2/n-1 coefficient.

## T12: full affected derivation and endpoint

Current T12 head lines417-421 and body lines422-456 are fully reviewed. The body SHA256 is `4da6b68ce2b2e74379d356d6b41f1b428542f239398eda46afa69373e92a865e`, 1378 bytes/35 LF. The only textual change is `(abs_add _ _)` to `(abs_add_le _ _)` in the local finite-sum triangle proof.

For the induction insertion step, the goal after finite-sum rewriting is

    abs(f i + sum_S f) <= abs(f i) + sum_S abs(f).

`abs_add_le` gives the first inequality to abs(f i)+abs(sum_S f). `add_le_add_left ih _` supplies the second inequality to abs(f i)+sum_S abs(f). Their transitive composition is the exact required step. It is valid for arbitrary real f; no nonnegativity of f or r is assumed.

The rest of the complete body applies this finite triangle inequality twice to the strict anomaly-pair sum, uses i<j to obtain i!=j for the original finite envelope, and bounds each pair by w_i*w_j. The unchanged exact pair-product square identity leaves the nonnegative diagonal square sum, giving abs FA<=ell^2/2. The half is retained exactly. Diagonal residual values never enter; empty A, K=1 and ell=0 remain covered. This endpoint introduces no symmetry, probability or positive-energy premise. No in-module theorem depends on T12; its intended exported use is the exact first inequality of p41(5), whose interpretation was established in the prior complete source review.

## T13: full affected derivation and callers

Current T13 head lines457-463 and body lines464-492 are fully reviewed. The body SHA256 is `8ae742c57f4faae76d871d41d4d794fcd18d429af03365cc5a26c70176ee4bc8`, 1020 bytes/29 LF. Again, the only textual change is the same two-term `abs_add_le` triangle step in a complete finite-sum induction. The transitivity and addition orientation match the T12 argument exactly.

The full body derives d=N-2>0 from n>=4; rewrites the actual row difference using unchanged T06; handles abs division using this positive d; and bounds abs(sum_A r_ia) by sum_A abs r_ia. If a is in A and i in B, the actual complement membership proves a!=i, so the offdiagonal-index envelope applies in the required i,a orientation. The weight sum becomes ell*w_i by finite multiplication distribution and commutativity. Division remains by the same original d. There is no diagonal-zero assumption and no need for distinct observed values.

The unchanged T17 current lines589-617 was read in context. Its call to T13 still obtains the exact nonnegative right side ell*w_i/d, proves the signs needed for squaring, and sums to `(ell/d)^2 Qw`. The unchanged T19 current lines643-691 consumes that bound after the already reviewed coefficient-one centered-norm and studentizer identities. The changed triangle name neither inserts a factor 2 nor changes an energy or denominator. The zero ell/Qw/Qb/Q0/sB cases remain included without division by any energy.

## Preserved source contract and future gate

All 33 statements and 14 actual mathematical objects remain frozen and unchanged. Source p41(4)-(5) is still a finite deterministic result with main n>=4 and card B>=3, while old physical P51 wrappers retain sample-size-at-least-four premises. Same-n rows/lambda, real K-1, sharp FA half, coefficient-one norm, arbitrary diagonal residuals, repeated observations and zero energies are preserved. No helper, import, option, assumption, unqualified unit276/277 dependency, law-level everywhere envelope or mathematical scope has been added.

The prior complete primary-source reading and source-to-statement review are reused at their exact bound bytes. This packet does not claim the B-to-Fin-m physical transport, simultaneous product-a.e. sample-pair lift, conditional first-projection/canonical-residual/mean/variance transfers, p41(3), conditional interaction concentration, quantitative tail shift, rareblock integration or unconditional PE-R/PE-L/OQ56/root closure.

The actual parent server must check this exact new complete source. Only if it succeeds may the same FIRST original object be used for complete actual-owner TYPE, non-theorem/definition full VALUE and recursive AX evidence, followed by explicit SAME FINAL-review reactivation. In particular all fourteen definition VALUEs and actual generated non-theorem owners remain mandatory; source counts are not compiled-owner counts. All current qualification fields remain false except SOURCE acceptance.

This reviewer performed no SSH/network/Lean/AX/compiler/toolchain probe/prefix/upload/Git/API/publication/child/Goal/schedule/resource action and edited no source. Requested model/effort are gpt-6.1-sol/xhigh; actual backend/model/effort and input/cached-input/output/reasoning-subset counts remain null because not exposed. Final sealing releases all active authority, sixzero, queued work0 and no active wait; only the dormant same FINAL identity is retained for explicit actual-machine-evidence activation.
