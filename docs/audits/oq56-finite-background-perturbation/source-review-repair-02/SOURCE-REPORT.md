# Unit278 repair02: SAME independent affected SOURCE review

STATUS: CORRECT for the current repaired source at the independent SOURCE layer. `sourceAccepted=true`, `kernelChecked=false`, `qualified=false`.

The current T12/T13 complete proof bodies and their interfaces/use contexts have been independently read and checked against the two complete actual native02 diagnostics. The explicit addition comparison now has the exact ordered intermediate expected by `le_trans`. All remaining source coverage is reused only after independent byte-identity verification against the prior complete/repair01 review evidence.

## Exact reviewed object and scope of reading

The activation is SHA256 `e26b3754fd2f99ca32d9838d920f51459d9bbd74970bc0584d0fdb023266232f`, 76191 bytes. All 340 input SHA256/byte pairs were independently verified before first write, and an actual ACK340 was sent. All are rechecked before the unique final seal. The SAME reviewer `/root/oq56_unit278_review` remains separate from the author and writes only this new `source-review-repair-02` directory.

Current source: `C:/game/shao lean/drafts/oq56/unit278/author-repair-02/FiniteBackgroundPerturbation.lean`, SHA256 `8481562684fc7a3c5455e8ab99d6f85b15f4778860fa414da93099b83b4adcb8`, 30148 bytes/694 LF. It retains 33 declarations, 14 definitions and 19 theorem bodies, with HEAD118 LF, PROOF523 LF, fixed-RHS36 LF, PRE14 LF and CLOSE3 LF.

Current T12 head417-421/body422-456 and T13 head457-463/body464-492 were read completely: 35+29=64 proof LF. The complete current T17 call/use at lines589-617 and the downstream T19 context at lines643-691, with intervening T18, were read. The full author repair02 report, current MFT addendum, both complete diagnostics and diagnostic-coverage account were read. The current MFT's full original body is byte-exact to the originally read author MFT SHA256 `3c66f11a5eb36dd353c4dc5f5e0fde1bde36ad8ad8a18c3d99c03ed9ae7db27d`; that unchanged body is reused rather than reread ceremonially.

The other 17 complete proofs account for 459 LF and are independently verified byte-exact to repair01, including the already affected-reviewed T08. All 33 frozen heads, all 14 fixed definition RHS, PRE and CLOSE also match repair01 and the authoritative freeze. Exact full-source assembly, all current source byte/line intervals and the three concatenated streams were checked. The only whole-source edits are the two expected addition-composition replacements, with no statement, definition, import, option, helper or assumption change. Complete coverage is 64 newly reviewed proof LF plus 459 exact reused proof LF. I do not claim a redundant literal rereading of all 694 current source lines.

## Correction to the earlier independent review

I missed the concrete addition-orientation error in repair01. In `source-review-repair-01/SOURCE-REPORT.md` line56 I wrote that `add_le_add_left ih _` supplied the fixed-first-addend comparison required by the triangle composition, and line62 reused that assertion for T13. The actual native02 elaborated type shows that this term puts the induction comparison first and the added constant second. Those two explanation assertions were incorrect. They are explicitly superseded here; the sealed old report and failures are left unchanged.

The abstract finite triangle reasoning remains valid, but commutativity of real addition does not make the old incorrectly oriented proof term definitionally equal to the expected Lean type. The present review therefore checks the new term's exact ordered summands, not merely its mathematical equivalence up to commutativity. The two changed proofs are not accepted by reuse of the mistaken earlier assertion; they receive the complete current review below. No kernel pass was previously claimed and no old failed attempt is relabeled.

## Actual native02 failure and exact diagnostics

Native02 checked repair01 source SHA256 `4ef892a876624e601fd98f32a49f383b54b3748af0d4226bf98f50a9152646c3`. Its receipt SHA256 is `733e620844f3e03ef0e8f637a46a7b7c1d813b3a1cb8944fd192e8acd21b4a2f`, 37738031 bytes. It ended naturally RC1 after 5.148428468 seconds with two errors and fourteen warnings, no object and no AX. The bound terminal inspection reports all owned processes ended, no timeout/cleanup/ownership issue, and all 36308 protected artifacts equal. Raw receipt/logs remain on the server. I used the complete bound normalized diagnostics and made no server connection.

At line430/column38 the old term's actual type was

    abs(sum_(i in S) f i) + c <= sum_(i in S) abs(f i) + c,

but `le_trans (abs_add_le (f i) (sum_(i in S) f i)) ...` expected

    abs(f i) + abs(sum_(i in S) f i)
      <= abs(f i) + sum_(i in S) abs(f i).

The full diagnostic SHA256 is `ffc7213b05cac6c48c70d6894b8af55b4344cab0142090887e26b403481cb0f6`, 295 characters. At line474/column38, the a-index term had the identical order mismatch with its a-index sums; that complete diagnostic SHA256 is `16f10292329b955a0b91947071faf60273743adccc9b1936f89905e1767f4da4`, 299 characters. Both complete messages are retained in READ_ACK and bound diagnostic inputs.

Native01 also remains its original RC1/three API-name errors/no-object failure. Native02's lack of a T08 error is not promoted into a module or individual kernel qualification. The new whole-source gate is pending.

## T12 complete proof and exact addition orientation

T12's current body is SHA256 `381eed884b2cc7507cef1faedb4412379b54b717f2b9c81e91284449af414db6`, 35 LF. Its exact head remains the p41(5) inequality abs FA<=ell^2/2 under the original finite nonnegative weights and offdiagonal-index envelope.

The local finite-sum absolute-value bound is proved by induction. The empty case is zero<=zero. For insertion i into S, rewriting finite sums produces the exact goal

    abs(f i + sum_S f) <= abs(f i) + sum_S abs(f).

The first `le_trans` argument is `abs_add_le (f i) (sum_S f)`, giving

    abs(f i + sum_S f) <= abs(f i) + abs(sum_S f).

The new second argument is `add_le_add (le_refl |f i|) ih`. Its first premise is exactly abs(f i)<=abs(f i), and its second premise is the induction inequality abs(sum_S f)<=sum_S abs(f). Componentwise addition therefore yields, in the actual required order,

    abs(f i) + abs(sum_S f) <= abs(f i) + sum_S abs(f).

The shared intermediate is literally the triangle bound's right side. No rearrangement, additional rewrite, hidden reflexivity hypothesis or commutativity shortcut is required. The reflexive comparison is proved by `le_refl`, not assumed by the theorem caller.

The rest of the complete T12 body applies this verified finite triangle inequality to the outer anomaly sum and each inner anomaly sum. For strict i<j, the original envelope applies because i!=j. The symmetric product-weight square identity relates twice the strict-pair product sum to ell^2 minus the diagonal square sum; the latter is nonnegative. This yields the exact half with arbitrary residual diagonals, empty A and all zero weights included. The global weight nonnegativity premise and finite index envelope are unchanged. There is no internal theorem caller of T12; its exported conclusion is exactly the original sharp-FA-half endpoint.

## T13 complete proof, index orientation and downstream contexts

T13's current body is SHA256 `676473d8e543589f4f5b0c6aae944a633a65f4a0e54606d974aa51e85ab5a306`, 29 LF. It retains the actual bound abs(b_i-b0_i)<=ell*w_i/(N-2) for i in B and n>=4.

The local induction has an inserted a-index and arbitrary real f. Its new second `le_trans` argument is `add_le_add (le_refl |f a|) ih`: reflexivity proves the first abs(f a) comparison, and the induction hypothesis supplies the second sum comparison. Its derived type is exactly

    abs(f a)+abs(sum_S f) <= abs(f a)+sum_S abs(f),

which matches the preceding `abs_add_le (f a) (sum_S f)` intermediate with the same ordered summands. This is the complete orientation correction required by the second diagnostic.

The remaining body derives d=N-2>0 from n>=4, rewrites the exact original row difference with T06, and uses the correctly proved finite triangle inequality. Actual a in A and i in B imply a!=i through complement membership, so the offdiagonal-index envelope applies as r_i,a. The resulting sum of w_i*w_a is ell*w_i, and division is by the original positive d. No symmetry, diagonal-zero condition or distinct observation-value condition is introduced.

The unchanged current T17 calls this exact T13 with B,g,r,w,hn,hw,henv,i,hi. Its right side has the same nonnegative factors required for squaring, and summing gives `(ell/d)^2 Qw`. The downstream T19 consumes the resulting energy estimate after the exact studentizer rewrite and the already independently reviewed coefficient-one centered-norm inequality. Its factors and sqrt comparisons are unaffected. There is no new factor 2, no division by any energy, and no changed zero case.

## Scope and pending machine qualification

All original mathematical fidelity constraints remain: same-n row and lambda, real K-1, finite n>=4/cardB>=3, separate existing physical m>=4 wrappers, offdiagonal indices with repeated observed values allowed, arbitrary r_ii, sharp FA half, coefficient-one norm, and zero ell/Qw/Qb/Q0/sB. No unqualified unit276/277 dependency is added. All fourteen concrete definition bodies remain frozen.

The finite packet still does not establish physical B-to-Fin-m transport, product-a.e. sample-pair lifting, conditional recentering/mean/variance payments, p41(3), interaction concentration, rareblock integration, unconditional PE-R/PE-L or OQ56/root closure. The original complete primary-source/proposal/source-fidelity evidence applies only within that unchanged scope.

The next machine step belongs to the parent: the complete exact repair02 source must pass a new server native gate. Only the actual successful FIRST original object may then support all actual-owned full TYPEs, every non-theorem/definition/generated full VALUE and recursive AX. Definition VALUE auditing remains mandatory for all fourteen fixed definitions plus any actual generated non-theorem owners. These are not inferred from source counts. Explicit SAME FINAL reactivation with actual machine evidence is required before qualification.

No SSH/network/Lean/AX/compiler/toolchain probe/prefix/upload/Git/API/publication/child/Goal/schedule/resource action or source edit was performed by this role. Requested model/effort are gpt-6.1-sol/xhigh; unexposed actual backend/model/effort and input/cached-input/output/reasoning counts remain null. The unique seal releases all active authority with sixzero, queued work0 and no active wait. Only the dormant same FINAL identity is retained for explicit actual-machine-evidence activation.
