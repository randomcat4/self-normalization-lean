# Unit277 complete independent SOURCE review

STATUS: CORRECT — SOURCE_ACCEPTED_PENDING_KERNEL.

The exact complete source `author-01/FiniteExceptionalBlockOptimization.lean`, SHA256 `d183e84abbb1d37364b3272f465150e1018a5a60349a5b7eb2afd56783265939`, 15280 bytes / 359 LF, receives independent SOURCE acceptance. All five frozen statements and all five actual proof bodies were read in full and reviewed against the original finite mathematical scope. No critical mathematical gap, silently modified assumption, incorrect public-interface instantiation or concrete counterexample was found. This is a source/proof-semantic verdict, not evidence that Lean has elaborated or checked the source. `sourceAccepted=true`, `kernelChecked=false`, `qualified=false`.

## Authority, exact inputs and assembly

This is the same independent reviewer `/root/oq56_unit277_review`, explicitly reactivated for complete SOURCE review after the author and prior interface role released their active authority. The prescribed configuration remains fresh-at-instantiation gpt-6.1-sol/xhigh. Actual backend/model/effort and input/cached-input/output/reasoning-subset counts are unexposed and null. Activation `source-review-ACTIVATION.json` is SHA256 `bf0a156e62d89525434d52ee7c4af4cacb0cd830b062873c1dd683699506b88e`, 14634B. All 56 bindings matched SHA256 and byte count before the first write; they are reverified before the final seal.

The complete previously accepted interface review is reused, bound by its exact report/coverage/release hashes. The same context already read all p41 449 LF, p51 355 LF, the 8185-character proposal, PRE/CLOSE and the five complete frozen HEADs. Their bytes still match. This phase adds the previously unavailable entire source and every actual proof body; it does not treat the earlier plan verdict as proof-body review.

An independent text reconstruction verified PRE + HEAD01 + PROOF01 + ... + HEAD05 + PROOF05 + CLOSE byte-for-byte against the source, without separator bytes. The source-derived spans agree with both author maps. ALL-HEADS and ALL-PROOFS match their exact component concatenations. Derived counts are PRE6 + HEAD83 + PROOF268 + CLOSE2 = 359 LF. Source bytes are strict UTF-8 without BOM or CR, with exactly one final LF. The five source declarations are exactly three private helpers and two public theorems in frozen order. No additional top-level definition, abbreviation, instance, axiom or declaration is present. The sole option is the frozen `autoImplicit false`; prohibited bypass tokens are absent. These are source/text checks, not parser or kernel receipts, and source declaration counts are not compiled owner counts.

## H01: source lines 7–66, proof 19–66

The statement is byte-identical to its frozen 12-line HEAD. The body introduces the fixed local lets, establishes n's positive real cast is nonzero, and constructs the two membership filters (23–28). The full finite partition (29–33) is the true B/complement split. Applying it to 1 yields M+K=N (34–37), not a new premise or an unproved arithmetic identification.

The weighted-mean identity (38–47) is the important empty-block branch: for any finite s it first separates s=empty, then derives nonzero card(s) only in the nonempty branch before clearing that denominator. Thus K=0 is valid. The full mean formula (48–52) uses only this identity, the true split and nonzero N. P35.mean is exactly the existing N-inverse arithmetic mean.

The local square-sum expansion (53–59) is algebraically exact: sum(b-t)^2=sum b^2-2t sum b+card(s)t^2. Applying it to univ, B and A, substituting the established weighted sums and M+K=N, gives the claimed between-block term MK/N times (muA-muB)^2 (60–66). The final denominator is the nonzero M+K; K is never cancelled. The actual center is P35.center. No positive-energy or sign condition is introduced. The body proves the full identity, including the exceptional within-block energy QA, rather than only the lower bound needed later.

Verdict: correct for the complete frozen domain, including empty A.

## H02: source lines 67–100, proof 73–100

The six-line statement is exact and retains only N,M,q>0 and K>=0; no N=M+K premise appears in either statement or body. With ap=max(a,0), lines75–76 prove X<=Z. Lines79–85 separate Z>=0 from Z<0. In the first branch both squared terms are nonnegative and max(X,0)<=Z follows from X<=Z and 0<=Z. In the second branch X<=0 is explicitly derived and the positive part becomes zero. This avoids the invalid inference max(X,0)<=Z when Z<0.

The implemented field identity (86–91) is exactly

    N[N ap^2/q+K/M][q+(KM/N)y^2]-(Nap+Ky)^2
      = NK/(Mq)(q-M ap y)^2.

Expansion confirms all coefficients and powers. Only N,M,q are cancelled, with their recorded nonzero facts. Lines92–95 derive nonnegativity from K>=0 and positive N,M,q. The two inequalities are then composed. K=0, a<=0 and either sign of y require no missing branch or premise. The earlier independent scalar countercheck with N=7,M=2,K=3 is still relevant: the lemma is truly independent of the cardinality relation. Positive part remains necessary and is preserved.

Verdict: correct under every quantified sign and degenerate case.

## H03: source lines 101–222, proof 119–222

The 18-line HEAD exactly preserves actual Qb, actual P35-centered Q, the Q=0 guard, arbitrary real c and n>=2. Lines122–138 introduce only definitions and derive N>0, N-1>0, M>0, K>=0 and actual Qb>0. The repeated finite split/cardinality/weighted-mean facts (139–162) are valid, including empty A, and prove X=Na+Ky (163–166).

The actual H01 invocation (167–170) supplies n>0 from the stronger n>=2 and the same B.Nonempty. Its instantiated lets match the intended Q,Qb,QA,y; the commuted coefficient is KM/N. Lines171–181 derive QA>=0, the between-block term>=0, Qb<=D<=Q and finally Q>0. This proves the first conjunct before removing any zero guard; it is not circular or assumed.

Lines182–192 prove C>=0 and invoke H02 with exactly N,M,K,Qb,a,y and its four required sign premises. Monotonicity replaces D by Q only after N C is shown nonnegative. Lines193–197 remove the guard using the already-proved Q>0 and square the actual sqrt factors with valid nonnegative radicands. The exact identity is T^2=((N-1)/N)X^2/Q.

The final split (200–222) covers X<=0, giving T<=0 and zero positive part, and X>0, giving T>=0 and using the positive numerator bound. All divisions by Q and N have established positivity/nonzero facts. The last cancellation is precisely (N-1)C. Neither the factor n-1 nor the inner n nor K/M is dropped or replaced. No implicit a>=0, c>=0, positive exceptional count or zero full mean is used.

Verdict: correct, including actual Q positivity and all sign/empty-block boundaries.

## H04: source lines 223–300, proof 243–300

The 20-line frozen HEAD is unchanged. The body derives the needed N,N-1,sqrt(N),sqrt(N-1) positivity and N-2 nonzero from explicit n>=4 (246–252). The sampled residual matrix passed to P35.offDiagonalSum_eq_two_unordered is exactly r(x_i,x_j), and the required matrix symmetry is correctly instantiated by hsym(x_i)(x_j) (253–259). Its unorderedPairSum is definitionally the actual originalUpper F, so the row sum is 2F.

P51.residualU_eq_erased_row is applied to the same n,r,x,i, preserving the coefficient 1/(N-2). The finite sum division and preceding double count give sum residualU=2F/(N-2), then sum b=sum g+2F/(N-2) (260–267). Unfolding the existing W and D definitions yields the original numerator identity (268–277): W+D=(sum b-Nc)/sqrt(N), with c=F/[(N-1)(N-2)]. The field identity uses 2/(N-2)-N/[(N-1)(N-2)]=1/(N-1). Its cleared denominators are all known nonzero.

The complete accepted public P51.centeredSq_eq_center_sum signature requires precisely the supplied g,r,x,hsym,hn and yields centeredSq=Q/(N-1) (278–279). The actual P51.centeredSq is the original FiniteRows.jackknifeSq/4; the original row identity and jackknife coefficients were already independently mapped in the interface review. There is no replacement by an uncentered row norm. Q>=0 (280) is a finite sum of real squares. The sqrt quotient identities (281–285) use nonnegative radicands, and the positive sqrt denominator facts are available.

The Q=0 branch (286–289) explicitly proves s=0 and reduces both guarded expressions to zero; it does not cancel by s or require a zero numerator. The Q!=0 branch (290–300) derives Q>0 from Q>=0 and nonzero Q, then establishes sqrt(Q)>0 and s>0 before removing the guards and clearing sqrt denominators. The remaining algebra is exactly sqrt((N-1)/N)X/sqrt(Q).

The singleton-type example g=1,r=2 has nonzero W+D and Q=s=0, so it attacks the crucial zero branch; that branch is explicitly sound. Repeated observations at distinct indices are retained in the row sums, while equal indices alone are erased. No condition r(o,o)=0 or g/r independence is introduced. The symmetry premise is pointwise as frozen, not an unacknowledged upgrade of an a.e. condition.

Verdict: correct as an all-sample original-statistic identity, including zero denominators.

## H05: source lines 301–357, proof 328–357

The public 27-line HEAD remains exact. n>=4 implies n>=2 and card B>=3 implies B.Nonempty (336–338). H03 is applied to the same actual b,B,c and actual background energy premise (339–344), providing Q>0 and its full positive-part inequality. H04 is instantiated on exactly the original g,r,x,hsym,hn, giving T=Tf with the original s guard (345). The existing centered-square identity plus Q>0 and N-1>0 yields s>0 (346–354). The final conjunction uses this positivity and rewrites T to the abstract statistic; no desired conclusion is assumed.

The source-to-statement mapping is literal p41:65–82 formula(3), with p51:18–29 defining the actual F,psi,b,W,D,s and zero convention. It preserves n-1, n, complement card/B.card, actual Qb and the positive part of muB-F/[(n-1)(n-2)]. This wrapper is explicitly n>=4/card B>=3. Abstract H03 covers n=3 geometry; H05 does not claim the actual n=3 endpoint. This restriction is visible, matches the supplied P51 bridge, and is not silently presented as every source endpoint.

Verdict: correct in the exact frozen finite original-statistic scope.

## Public-interface fidelity, scope and pending qualification

All three directly used established theorem interfaces were checked in complete public form: residualU_eq_erased_row, offDiagonalSum_eq_two_unordered and centeredSq_eq_center_sum. Their arguments and sign/range/symmetry hypotheses are supplied exactly at the source lines identified above. The existing P35 mean/center and originalRows/originalUpper, FiniteRows original row/U/jackknife and P51 W/D/residualU/centeredSq definitions are unchanged exact inputs already covered by the accepted interface review. Supplier proof/kernel/AX evidence is reused; no old proof was requalified or rerun.

Local finite-sum, order, square, field and sqrt operations implement the mathematically valid identities explained above. Source review finds no invalid inference or missing API hypothesis. Actual elaboration/tactic execution and default-budget success still require the authorized server kernel check; no success is inferred from familiar API spelling. Every actual-owned full TYPE, non-theorem VALUE and recursive AX set, including private/generated owners, remains pending server evidence and final review. The five source theorems must not be used as an inferred actual compiled-owner count. The allowed final transitive axiom whitelist remains propext, Classical.choice, Quot.sound.

This source has no probability, tail, CDF, external-SZ, independence, canonicality, moment, alpha or relative-payment premise. It does not prove p41(4)–(5), reindexed background comparison, conditional interaction concentration, rare-block weighted integration, original-mu full-tail PE-R, or an OQ56/root closure. The source's deterministic relaxation does not claim optimized g/r configurations are realizable in the original model. The original PE-R alpha_p condition and p54 repairs remain future scope constraints. Unit276's body is unnecessary and was not read or qualified here.

No source patch is requested. The SOURCE verdict is complete now; it does not wait for unavailable server evidence. No Lean, AX, SSH, toolchain probe, network, upload, publication, child, Goal, schedule or sidebar action was taken. Only this role's `source-review-01` files were written. All other owners' files and prior seals remain untouched.

At the unique LASTFINALWRITE, this role releases all active write/execution/publication/delegation/child/wait authority. Role-local sourceWriters/heavy/inflight/pendingExternal/activeChildren/activeWaits are all zero. There is no active wait or ongoing background mechanism. Only the same independent FINAL reviewer identity remains dormant for explicit parent reactivation on actual exact-source server evidence.
