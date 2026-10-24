# Independent final review: corrected Brownian boundary

STATUS: CORRECT

Reviewer context237, fresh independent context, actual configured model `gpt-6.1-sol`, reasoning effort `xhigh`. Mathematical author235 and implementation author236 are distinct from this reviewer. This review covers only `Shao.OQ4.RademacherCorrectedBrownianBoundary` at source SHA256 `26fb55261e84d7cb7081d276748c2acd382c25f09a337360db6114a443ca7fe6` (13374 bytes, 278 LF, valid UTF-8 without BOM or CR). It accepts the exact paired finite-law corollary, without a novelty or original-root closure claim.

The six frozen declaration heads and both complete transparent definition values are unchanged. Removing the four recorded proof insertions recovers the frozen file byte for byte, SHA256 `c839455bec9f2ff7bc79241e62e2f4b2f33411fa31d8f675bed2cb5f3f03d956`. The lead freeze is `ea02df4003e0a02739ca9a7293afb945964e0fca28dc92e0fcd0977e0b202aa0`. Combined source plus audit suffix is exactly `433705565623d0290e0e587073d211f9b28953d3aadd33d90896bd6c0be56d4b`.

## Source-to-statement review

I read the complete original `spectrum01.md`, `frozen01.md` and `sharp01.md`; the complete author235 problem, assumptions, proof and provenance; the entire successful new Lean source; the frozen heads; every actual owned type; both full actual transparent values; and all 35 direct project interfaces (5 theorem types and 30 full definition values) exported by the successful audit. Exact text-source pins were independently hashed. Old full proofs are reused under their qualified exact-source evidence, rather than reviewed or compiled again.

The original source's S4 residual uses the actual weak Rademacher finite-path probability at the unchanged threshold h. Its absorbing height is floorNat(h)+1, including the shift of one at integer h. The strict convention uses ceilNat(h), giving zero shift at positive integer h. This module preserves both numerator events and places these respective heights only in the Brownian denominator. It therefore pays for the source's boundary shift instead of silently changing the finite event.

The weak numerator's transparent chain is S4.p -> S3.p -> S2.p -> the real mass of `Shao.closedStrip h` under the finite product of `RademacherCosine.law`. The latter law is the fixed half-weighted pair of Dirac measures at +1 and -1. `Path n` is `Fin n -> Real`, and `prefixSum` sums entries with index below the requested prefix. `closedStrip` quantifies all prefixes r<=n, including zero. The strict numerator is exactly `strictP n h`, the real mass of `strictEvent n h` under the same finite product law; that event quantifies 1<=r<=n and uses strict inequality. No varying law, free spectral probability, or generic asymptotic primitive appears in either public conclusion.

The denominator is the actual `BrownianSup.probability B P hB`, with its full type and value inspected. This is P.real{U<=x}, where U is the qualified measurable version of the absolute Brownian supremum on [0,1]. Its `U`, `traceSup`, `pathSup`, rational times and `fullStrip` values and the actual-event bridge were inspected. The Brownian sample universe is arbitrary and independent of the finite-path universe. No coupling is assumed.

Both public heads have exactly h->infinity, n/h^2->infinity and one eventually bounded positive upper witness for n/h^3. There is no additional n-limit, vanishing third scale, phase limit, fractional-part limit, parity condition, AC/S predicate, nonlattice assumption, moment assumption or density assumption. The private transfer helper's abstract A and S4 residual are discharged by the two qualified actual S4 theorems; they are absent from the public hypotheses.

The result is a source-derived fixed-Rademacher corrected-denominator corollary. It does not establish the original general fixed-iid uniform-window OQ4 statement, an uncorrected critical ratio, a p54 repair, or any other original root. C12/OQ3/OQ4/OQ56 remain OPEN.

## Complete new-proof review

* Source lines 19 and 21: the complete values are exactly `(Nat.floor h : Real)+1` and `(Nat.ceil h : Real)`. Natural floor/ceiling at nonpositive initial values are total; no positive-tail inference is made about those initial values.
* Lines 23-49, inverse-square bound: h>0 and 0<=d<=1 imply h+d>0 and d^2<=1. The exact factorization is
  `E-W = -(pi^2/8)(n/h^4)d^2 h(3h+2d)/(h+d)^2`.
  The ratio factor is nonnegative and at most 3, since `3(h+d)^2-h(3h+2d)=4hd+3d^2>=0`. Multiplication by the nonnegative n-dependent factor yields precisely `|E-W| <= 3(pi^2/8)n/h^4`. The endpoints d=0 and d=1 and n=0 are included. The algebra introduces no unproved Taylor estimate or stronger scale condition.
* Lines 53-100, legal tail and positivity: h>=1 and n/h^2>=1 give n>=h^2>0, sqrt(n)>0 and sqrt(n)^2=n. Positivity of x=h/sqrt(n) follows. The wall h<=H<=h+1 supplies positivity of y=H/sqrt(n). All cancellations and ordinary log identities occur only after the requisite positive tail has been established.
* Lines 101-133, normalized heights: the epsilon argument uses n/h^2>epsilon^(-2), multiplies only positive denominators, and compares nonnegative squares to derive 0<x<epsilon. Since h>=1 and H<=h+1<=2h, 0<y<=2x, so y->0. This proves the actual Brownian-shift theorem's complete hypotheses without adding n->infinity as an input.
* Lines 134-144, Brownian exponent: the qualified actual Brownian boundary-shift theorem is applied to these same x,y. The equality `1/(z/sqrt(n))^2=n/z^2` is a legitimate total real identity using sqrt(n)^2=n. Consequently its exponent is exactly `E=(pi^2/8)(n/h^2-n/H^2)`.
* Lines 145-167, fourth scale and remainder: the given boundedness yields `0<=n/h^4=(n/h^3)/h<=M/h` on the legal tail, hence n/h^4->0. Applying the exact remainder bound with d=H-h gives E-W->0. No inference requires n/h^3->0 or convergence of H-h.
* Lines 168-188, transfer: writing r=log(A/F(x))-W and b=log(F(y)/F(x))-E, the expression `r-b-(E-W)` equals log(A/F(y)). The sign of the exponent cancellation is correct. A,F(x),F(y) are strictly positive on the common tail, making all three log divisions legitimate. The three residuals tend to zero, and continuity of exp plus exp(log q)=q for positive q gives A/F(y)->1 and the claimed eventual positivity pair.
* Lines 196-235, weak wrapper: eventual h>=2 gives m=floorNat(h)>=1 and the exact weak cell m<=h<m+1. The complete actual `S4_EVENTUAL` type and `S4Outputs` value show that `hwlog` is the eighth component, the desired actual logQ-w residual. The extracted `hp` is the tenth component of `ProbabilityLegal`, actual p>0. The full S4 p,N,x,b,w,scale3/delta aliases and bridge statements identify these components definitionally with the helper inputs. The wall h<=m+1<=h+1 follows from the same cell; the original numerator stays p(n,h).
* Lines 240-272, strict wrapper: `strict_S4_EVENTUAL` has exactly the public three sequence assumptions and returns actual strictP positivity and the required actual log residual. The full Q/correction values and delta=ceilNat(h)-h identify it with the helper input. The actual `ceil_boundary_bridge` supplies h<=ceilNat(h); its truncated-natural predecessor equality and strict lower boundary imply ceilNat(h)<h+1, hence the required weak upper bound. Only its geometric components are used. The original strict numerator stays strictP(n,h).

The complete proof has no missing mathematical interface, hidden assumption, circular probability hypothesis or unresolved case. The internally established log limit is legitimately omitted from the public output. Finite initial zero time/nonpositive walls do not affect these eventual statements; the source's literal positive-prefix maximum is used only on the derived n>0,h>0 tail.

## Actual declaration and dependency coverage

The saved unfiltered environment difference, module ownership map and stage2 roster agree exactly on 13 actual declarations: 4 public (2 definitions and 2 theorems), 2 explicit private helper theorems and 7 generated helper theorems. Native kinds are 2 definitions and 11 theorems. I read all 13 unabridged explicit actual types and both unabridged definition values. A deterministic reconstruction of `owned-interface.txt` from the raw native type/value fields is byte exact. There are no other owned non-theorem values, opaque declarations, source instances, unsafe/partial constants or new axioms.

The seven generated theorem types were reviewed individually. Three encode nonzero numerals 2,3,4; the others encode nonzero products, natural powers, integer powers, and cast(n)+1 under their explicit algebraic hypotheses. They are internal simplifier certificates, not extra hypotheses attached to the public heads. All their raw explicit types and per-root recursive axiom lists are covered.

The saved owned TYPE+VALUE references have exactly 556 distinct foreign frontier declarations, equal to the complete exported old-direct roster. All 556 metadata/type/value-availability records were checked deterministically, including complete nonempty definition values for its 253 definitions. The 35 project frontier interfaces, from 9 project modules, were fully read at the actual exported type/value level. The remaining 521 standard Lean/Mathlib frontier declarations reuse their pinned library qualification; this report does not claim to re-prove those libraries or manually re-review every library typeclass body.

The old complete proof/evidence qualifications reused are:

| Input | Exact source SHA256 | Existing qualification |
|---|---|---|
| RademacherS4Assembly | 803ee8488697c8f335e35a32f32fdd31ca69d521e1071eef2018af5b12f775bd | context95 complete CORRECT, source-to-statement/actual types CORRECT, LEAN_FULLY_CHECKED; review 2f3b67ef6f6239f437daef649253d85b0eca4b3e0aaf1ae2da4f883226385ae1 |
| RademacherGeneralStrictS4 | 935753f46f606adb975c944598896ebc4e0ff75da0a3ce92111f5dd0292de034 | context217 complete independent exact-source CORRECT; receipt 374db42c494013e1d70fd46264b6dec1230c8551d45f453f8433ed93343372fc |
| RademacherBrownianBoundaryShift | a1afd98a0f645623b736a1a5b88f4974e3e955cf0b38c02f5153776c1e24d1ac | context214 complete independent CORRECT plus existing lead acceptance; execution f7a5c080f05b73159c3adc1f6b96c790052d15a5039efe2040226250b525601f |
| RademacherRealStrictBoundary | 009ec0792ffdb48ff38be1f402c71c5c3892d5ae35a9227fbcaca16d6565b9c2 | context214 complete independent CORRECT plus existing lead acceptance; execution b7d17ff4d40f0e6fd2d6ad662c8f4b39409b603727774ce0b7f27aaf4022117a |

The last module is a direct bridge used by the new strict wrapper and a qualified transitive input of strict S4. Although omitted from the author's 14-source local pin list, its existing acceptance, source bytes in both the old attempt003 and library, execution hash and exact actual bridge interface were independently bound here. This closes that provenance detail using existing evidence; no new gate or old proof rereview was needed.

## Mechanical evidence and independent deterministic audit

I reused exactly the original successful attempt002 server evidence, execution receipt SHA256 `570059ee9f13d7a133722df4ade40413ace00551c53ec265716c894354e17347` and compact manifest `3fd22d38367a922e571c0617b88d7d462b8dc922bcb9c8f0eae2d1619ad5007e`. All 21 manifest text entries matched their recorded sizes and hashes. The actual Lean process PID931210 returned 0 in 19.89525880664587 seconds, reaped, without timeout; full kernel checking was enabled, autoImplicit false and trustLevel1025. The pinned toolchain is Lean v4.36.0-rc1, mathlib807d3836b165983210ee2ecf3cd28f239436949c.

The audit suffix was fully read. It checks every actual owned declaration with `Lean.collectAxioms`, follows every type and available value recursively, rejects unsafe/partial or unapproved axiom nodes, and checks project ownership by module metadata. The original audit reports 61231 recursive nodes, 652 project dependency declarations in 30 recursive project modules, and 101 resolved project imports. The 101 import records and 30 module roster were counted and crossmatched independently. The original successful projection binds those 101 imports to the 113 unchanged prior object-stat records. The 61231/652/113 counts are retained original audit/projection facts; they are not represented as a fresh native walk or fresh server stat performed by this reviewer.

Independently, `audit_evidence.py` reconstructs every owned root's recursive axiom union from saved owned TYPE+VALUE edges and the same audit's complete recursive axiom result at each exact foreign frontier. All 13 reconstructions equal both the native row and the saved per-root receipt. The union is exactly `propext`, `Classical.choice`, `Quot.sound`; every root is within that whitelist. This is a separate deterministic consistency check over one saved native audit, with no new Lean/native execution.

The first successful object identity is retained as metadata only: SHA256 `cdb094e515dd929995fd85eb5f6d96771982b947fc037edfa7a9740b6c11ee9c`, device64947, inode5505191, size971496, mtime_ns1792843452806476785. Python integer parsing preserved all nanoseconds exactly. Source/combined/object/receipt/manifest bindings agree. This reviewer did not read, hash, download or copy this or any old binary.

The earlier attempt001 failure remains archived. It had exit1 after a body-local missing `mul_one` simplification and was correctly rejected for error-recovery `sorryAx`. The successful source changes only that body simplification, has no prohibited tokens, and its successful whole-owned recursive audit has no `sorryAx`. The failed attempt is not evidence of a successful proof and has not been erased or replayed.

Full mechanical status for this exact new unit: LEAN_FULLY_CHECKED, by reuse of its source-bound server kernel/all-owned-transitive-axiom evidence plus this independent source fidelity/proof/type/value review. This reviewer ran zero Lean/parser/build/native commands, zero server commands and zero Git/cache/shared/source mutations. All local writes are confined to this final-review directory.

## Disposition and release

Critical gaps: none. Required independent final-review work for this exact unit: complete. The stale generic sparse-critical-denominator label in the text interface is a nonmathematical display residue; the enforced module, source, owned roster and object bindings are correct.

Review authority is released for this completed unit with pending tools, writes, Lean, server and other operations all zero. The exact next dependency is the separately frozen original fixed-law iid weak/strict consumer, preserving the original sample event/energy and h/sqrt(n) numerator argument while changing only the Brownian denominator. That consumer is outside this review and needs its own exact source evidence and independent delta review. This release is not a continuing runtime claim. All original root groups remain OPEN.

Input, cached-input, output and reasoning-subset token counters are unavailable and recorded separately as null. No token count or subscription-percentage estimate is inferred.
