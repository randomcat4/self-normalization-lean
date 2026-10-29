# Unit277 independent early interface and bearing-mathematics review

STATUS: CORRECT_AS_SCOPED for the five closed interfaces and their mathematical plan.

WHOLE-UNIT STATUS: INCOMPLETE_SOURCE_BODY_UNAVAILABLE. This report does not accept a Lean SOURCE, proof body, machine TYPE/VALUE, object or axiom receipt. `sourceAccepted`, `qualified` and `kernelChecked` are false. The same independent complete SOURCE/FINAL reviewer identity is retained dormant for explicit reactivation when the entire source and later machine evidence are available.

## Authority and independence

The reviewer is `/root/oq56_unit277_review`, prescribed fresh `gpt-6.1-sol` / `xhigh`. Actual backend, model, effort and input/cached-input/output/reasoning-subset counts are unexposed and recorded as null. Activation `independent-interface-review-ACTIVATION.json` was verified at SHA256 `e4f48cc9bbe2da87fc1b444044c113cc43bc9c7d5e2f2b915c507aaff5dc9d06`, 9337 bytes. All 32 listed input SHA256/byte bindings matched before the first report write. The runtime ACK is an actual output of this reviewer, not an inferred active lease.

Only `drafts/oq56/unit277/interface-review-01/` is writable by this role. The author remains the sole writer of `author-01`. Neither that unfinished directory nor an unqualified unit276 proof body was read. No frozen HEAD, old seal, library file, shared file, original source, other owner's report or implementation was changed. No child was created. The prescribed math-theorem skill and its prompt-library/openai-workflow/lean-verification references were read; explicit project/activation prohibitions override its generic local-toolchain probing step. No local Lean/toolchain, server, network, upload, AX or publication action was attempted.

## Exact material actually read

The complete five frozen HEADs were read: H01 12 LF, H02 6 LF, H03 18 LF, H04 20 LF and H05 27 LF, totaling 83 LF, together with PRE 6 LF and CLOSE 2 LF. The complete 8185-character / 15045-byte / 166-LF proposal was read. Both complete primary sources were read: p41 1–449 and p51 1–355. Their frozen hashes and all public interface files are bound in READ_ACK.json. Hash verification of an input is distinguished there from complete content reading.

Bearing API coverage comprises the actual P35 arithmetic mean, center, unordered pair sum and full off-diagonal double-counting signature; actual P51 W, D, residualU, centeredSq definitions and the complete erased-row, unordered-U, centered-row and centered-square public statements; actual originalRows/originalUpper definitions and original_half_eq_upper public statement; actual FiniteRows U-statistic, erased row mean and jackknife square definitions. The existing physical-statistic public let expression was also compared. Accepted old proof/kernel/AX evidence is reused; old producers were not given another proof qualification.

## H01: energy partition, including the empty exceptional block

Write N=n, M=card B, K=card A with A=univ\B, and use real casts throughout. The finite partition implies N=M+K. The assumptions give N>0 and M>0; K is merely nonnegative. Let beta be the actual P35 mean of b, u=muB, v=muA and y=v-u. For both blocks one has

    sum_B b = M u,    sum_A b = K v,
    beta = (M u + K v)/N.

The second identity is valid even when K=0: A is empty, its sum is zero, v=0 under total real division, and K v=0. In particular, this identity must not be proved by cancelling K without a separate branch.

Expanding around each block mean and using its zero centered sum gives

    sum_B (b-beta)^2 = q + M(u-beta)^2,
    sum_A (b-beta)^2 = QA + K(v-beta)^2.

Since u-beta=-K y/N and v-beta=M y/N, the two mean-shift terms sum to

    [M K^2 + K M^2] y^2/N^2 = M K y^2/N.

This is exactly H01 with the existing P35.center, not an alternative centering definition. If K=0, B=univ and q=Q; both the exceptional within-block energy and the between-block term are zero. The statement does not require an undefined nonempty-exceptional-block mean. No extra mathematical premise is needed.

## H02: all scalar quantifiers and signs

Set Aplus=max(a,0), X=N a+K y and Z=N Aplus+K y. Because N>0 and a<=Aplus, X<=Z. If Z>=0, max(X,0)<=Z and hence max(X,0)^2<=Z^2. If Z<0 then X<0, so the left side is zero and the same comparison holds. This establishes the positive-part step for arbitrary real a and y, including negative y. In particular the proof must not infer `max(X,0)<=Z` in the Z<0 branch.

For C=N Aplus^2/q+K/M and D0=q+(K M/N)y^2, direct expansion yields

    N C D0 - Z^2 = [N K/(M q)] (q-M Aplus y)^2 >= 0.

Only N, M and q are cancelled, and they are positive. K is never divided out. This proves the frozen H02 for ALL N>0, M>0, K>=0, q>0 and all real a,y. The cardinality relation N=M+K is not used or required by this scalar lemma.

Independent exact sanity instances reinforce the quantified argument rather than replace it. With N=7, M=2, K=3, q=5, a=1, y=5/2, N differs from M+K and both sides are 841/4, so equality is possible outside the cardinality relation. With the same N,M,K,q, a=-2 and y=9, X=13 and the bound is 169<=1563/2. With a=1 and y=-3, X=-2 and the left positive part is zero. When K=0, the statement reduces identically to N^2(max(a,0))^2 on both sides, for every y and every sign of a.

This also pinpoints why positive part is essential: N=M=q=1, K=0, a=-1 gives positive-part square zero and RHS zero, whereas replacing the left positive part by the untruncated square would give 1<=0. No such replacement occurs in the frozen interface or proposal.

## H03: derived true full energy and the n-1 factor

Here N=M+K follows from the actual complement cardinalities, and M>0 from hB. Set a=muB-c, y=muA-muB, q=Qb and QA as in H01. The full numerator is

    X=sum_all b-Nc=N a+K y.

H01 gives Q=q+QA+(M K/N)y^2. Squares are nonnegative and N,M>0, K>=0. Therefore D0=q+(M K/N)y^2>=q>0, and Q>=D0>0. This derives the first conjunct from the frozen hQb; Q>0 is not an additional or circular premise. It permits removal of the actual Q=0 guard and implies sqrt(Q)>0.

The multiplier C=N(max(a,0))^2/q+K/M is nonnegative. H02 therefore gives

    max(X,0)^2 <= N C D0 <= N C Q.

Since n>=2, N-1>0. The positive scaling factor f=sqrt((N-1)/N)/sqrt(Q) satisfies f^2=(N-1)/(N Q), and max(f X,0)=f max(X,0). Dividing only by the now-proved positive Q yields

    max(T,0)^2 <= (N-1)[N(max(a,0))^2/q+K/M].

No n, n-1, square-root or background-cardinality factor is lost. The n>=2 condition is explicit; no positive sign of c, a, b or y was assumed. The stronger fact that q>0 forces at least two background coordinates need not be added to the HEAD.

For a direct finite-vector equality check, n=4, B={0,1,2}, b_B=(-1,0,1), b_A=2/3 and c=-1 give muB=0, q=2, Q=7/3 and X=14/3. Then T^2=7 and the frozen RHS is 3(4/2+1/3)=7. For c=0 and b_A=t>0, the LHS is (3t^2/4)/(2+3t^2/4), approaching the RHS 1. This confirms the a=0 supremum interpretation without claiming finite attainment. For K=0, n=4, b=(-1,0,1,2), c=0 gives equality 3/5; with c=1 the positive part and RHS are both zero although the untruncated T square is 3/5.

## H04: original numerator, original jackknife and zero branches

Using the actual erased-row formula, write psi_i=sum_{j!=i}r(x_i,x_j). Pointwise hsym supplies the accepted double-counting premise, so sum_i psi_i=2F with F=originalUpper, the unordered strict-index pair sum. Thus

    sum_i b_i = sum_i g(x_i)+2F/(N-2),
    sum_i b_i-Nc = sum_i g(x_i)+F/(N-1),
    W+D = [sum_i b_i-Nc]/sqrt(N).

The exact coefficient reduction uses 2/(N-2)-N/[(N-1)(N-2)]=1/(N-1). Both denominator factors are nonzero because n>=4. Symmetry is supplied on all points as frozen; no independence of g and r, no canonicality, no distribution and no a.e.-to-everywhere upgrade is used.

The actual P51 centeredSq definition is FiniteRows.jackknifeSq(sampledKernel)/4. That original jackknife is

    [4(N-1)/(N-2)^2] sum_i(rowMean_i-U)^2,

with unordered-pair U and erased-row means. The accepted sampled-centered-row identity is rowMean_i-U=(N-2)/(N-1) center(b)_i; hence centeredSq=Q/(N-1). This agrees with the complete accepted centeredSq_eq_center_sum statement. It also proves R_h=2s; no uncentered row norm or modified studentizer is substituted.

Because Q>=0 and N-1>0, s=sqrt(Q/(N-1))=sqrt(Q)/sqrt(N-1)>=0, and s=0 iff Q=0. At Q=0 both guarded expressions are exactly zero. This remains necessary when the numerator is nonzero. For example on a singleton observation type, g=1 and r=2 make b constant, Q=s=0 and W+D=2sqrt(N) !=0; the frozen guards correctly give zero on both sides. Division cancellation outside a nonzero branch would be invalid for this example.

At Q>0, substitute W+D=X/sqrt(N) and s=sqrt(Q)/sqrt(N-1). The ratio becomes sqrt((N-1)/N) X/sqrt(Q), precisely the frozen RHS. The identity is pointwise over every sample vector, including repeated observed values and arbitrary r(o,o). Only equal indices are omitted from row/pair sums; distinct indices with equal observed values remain included.

## H05: literal source scope and remaining interfaces

For the same actual b and F, hQb is exactly the q>0 condition in p41 lines 68–76, and c=F/[(N-1)(N-2)] is exactly its offset. The `3<=B.card` premise implies B nonempty. H03 supplies Q>0 and the exact positive-part inequality; H04 replaces its abstract T by the actual physical `(W+D)/s` with the same guard. The accepted square identity gives s>0 from Q>0, so the first conjunct is justified without adding a low-energy event as an assumption.

The output is literally p41 (3), with n-1, n, k/m, Qb and a0^+ retained, restricted explicitly to n>=4 and card B>=3. The source block-size condition alone permits n=3, but this wrapper does not claim that endpoint. H03 covers abstract n=3 vector geometry; it is not an actual n=3 jackknife bridge. The restriction agrees with p51 S1 and the supplied public bridge scope. Treating H05 as every source endpoint would be an overclaim; none is made in the frozen pack.

This unit does not conclude p41 (4)–(5), the reindexed background-statistic comparison, the full-exceptional-observation conditional cross-interaction estimate, the exponentially weighted rare-block integration, the original-mu relative tail rate or PE-R. The proposal's later numerator formula preserves the real K-1 term and lambda=(M-2)/(N-2); its norm perturbation requires the separate envelope/background interfaces it records. These are explicit future obligations, not hidden premises of H05. The alpha_p=2(p-2)/(2p-1) requirement for eventual PE-R cannot be replaced by unit276's arbitrary-positive-alpha conditional scope. No external SZ/CDF existence or desired tail/relative-payment premise is smuggled into these finite heads.

The complete p41/p51 reading identifies these boundaries; it is not a certification of every probabilistic argument in those candidate source documents. H05 is a deterministic source-bound ingredient. It does not by itself close original mu/PE-R, NR, DC, OQ56 or a root theorem.

## Verdict, future review and release

No concrete counterexample, missing premise or mathematical mismatch was found in the five exact frozen interfaces or their complete plan, as scoped above. No patch or change request to a frozen declaration is warranted by this early review. This verdict concerns the mathematics of the closed HEADs and plan; it does not certify a tactic script, elaborated declaration, newly introduced auxiliary fact, proof-body dependency or transitive axiom set.

Before SOURCE acceptance, this same independent reviewer must read the eventual complete assembled source and all its proof bodies, confirm exact PRE/HEAD/order/CLOSE preservation and no extra assumptions/declarations/options, inspect every new proof branch and actual owned full TYPE/VALUE coverage, and bind the successful server kernel/all-actual-owner recursive-AX receipts to that exact source and first original object. Reuse accepted unchanged old evidence; do not replay old producers merely because this context resumes. Server entry timeout is an execution obstacle reported by the parent, not a result of this mathematics, and this role made no SSH attempt.

At the unique LASTFINALWRITE seal, all active report/write/execution/publication/delegation/child/wait authority of this role is released, with role-local sourceWriters/heavy/inflight/pendingExternal/activeChildren/activeWaits all zero. There is no active wait or persistent execution after the ordinary turn ends. Only the identity for a future explicitly reactivated complete SOURCE/FINAL review remains dormant. The author's separate current authority is unaffected by this role-local release.
