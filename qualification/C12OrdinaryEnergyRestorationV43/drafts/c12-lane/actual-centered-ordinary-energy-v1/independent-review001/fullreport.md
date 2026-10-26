# Unit221 complete new implementation source review001

STATUS: CRITICAL_GAPS, limited to the concrete static interface defect G1 below.

**Verdict: SOURCE_REPAIR_REQUIRED_STATIC_UNRESOLVED_NAME_H_UNQUALIFIED.** I read the entire new160LF/8426-byte source and its one complete public proof. The implementation follows the previously accepted conditional mathematical argument and retains the exact frozen public statement. One concrete name-resolution defect occurs at source71: `Shao.standardNormalTail_pos` is not an exported declaration in the bound read-only Gaussian-tail interface or relevant imported project sources. This source version needs an author repair before its first native attempt. No other mathematical or statically identifiable call/binder/transport defect was found in the complete source. This is a source-only review, not a compiler pass. `formalQualified=false`; H and the consumer still lack qualified compiled actualTYPE/original-object/axiom evidence.

## Exact source, independence, and limits

Reviewed source: `drafts/c12-lane/actual-centered-ordinary-energy-v1/source001/ActualCenteredOrdinaryEnergy.lean`, SHA256 `c0f302bda404ba9d873826f27e211a9867afe6a42cf8bf7ed9b42bc0b7cda431`,8426 bytes,160LF,0CR,noBOM. Activation is the read-only parent-complete-source-review-activation001.json in this review directory, SHA256 `ecce4ce197b0555fdea5d6cc74e7b0706bf638ac5de98b21c905ee42a6dbeeca`,5290 bytes. All16 activation inputs were independently verified before ACK and reverified at sealing.

Reviewer is the same independent `/root/centered_ordinary_energy_math_review001`, configured `gpt-6.1-sol/xhigh`, distinct from parent source author/C12 owner `01a174b9-5b2e-7611-ba13-02580d678eb3`. Actual model/effort and all four usage fields remain null. I wrote only the assigned new implementation review directory, preserving the parent activation, source001 and all old sealed math review artifacts. No source proof was implemented or edited, and no child, Lean/AX/server/network/upload/Git/API or background work was started. Current phase26 C12heavy0 was observed as a task restriction, not reinterpreted as permission to execute a check.

## G1 — unresolved Gaussian-tail positivity name at source71

The source writes:

`have hPsi : 0 ≤ Shao.standardNormalTail x := (Shao.standardNormalTail_pos x).le`

Exact-name searches in the read-only library, the C12 sources and the current Root H sources found no declaration named `Shao.standardNormalTail_pos`; the sole occurrence of that name in those sources is the new unit221 call. The defining shared module `library/Shao/Probability/GaussianTail.lean` is SHA256 `f166fab0061199e25d0391bbde5c977905e368513a6e0e18b492877c65160922`,14106 bytes. Its `tail_positive` at63 is private. Its actual public positivity interface is `standardNormalTail_basic` at91–95: the third conjunct states forall x,0<tail(x) and tail(x)<1. Thus the available positivity proof is `(Shao.standardNormalTail_basic.2.2.1 x).1`, whose `.le` gives exactly the required nonnegative fact. Qualified L220 source564 and Root H source111 already use this public projection.

This is a concrete source-interface defect, not a false mathematical inequality. The author can use the existing public projection locally without changing the theorem assumptions or shared Gaussian-tail module. I did not repair the source. No native command was run, so this finding is a static diagnosis rather than a claimed observed compiler error. After a minimal repair, only the affected source/evidence must be updated; unchanged complete proof/semantic coverage and accepted producer checks need not be replayed.

## Frozen statement, preamble, and source-to-original meaning

Source1–15 is byte-exact to the frozen538-byte preamble SHA256 `03a4a1b462b2a3e0e2fed4091bea54095cf96aac258cafdbb6cc22a297a77950`; parent preamble freeze is `56a73f01769a5adf17ff0277d50193978943dadb253bb6bda9c4febffe67ddca`. It imports accepted L220, the real frozen Root H module and TwoSided, and fixes namespaces/scopes/options before the proof. There is no new local instance in the source. Opening namespaces/scopes and using the `classical` tactic does not add a mathematical premise.

Source16–32, excluding the proof delimiter, is byte-exact to frozen public head SHA256 `86bf8d7a0b434bfbfdcf429bd26902a3b1e944ff974690692f5130dff3e5f4a3`. Its existing declaration freeze `ffd4974244b7326e0691712ba4116652ed18a6c21837311010c8715e54dbeeca` and the whole accepted mathematical report `e14debdbfe2abf673d82648377c82ee850ae4bdcac7f0525b3efbfb537f1c4d2`/parent acceptance `1f7fa838e9b910410f9b854e5fe002da15d6e35618ce9b32e19b878a789d3fa5` are reused unchanged. They already cover original g:centered, the canonical iid law, actual ordinary energy, weak crossings including all-zero samples and the actual Brownian representation. This is not a second old mathematical audit.

The complete source contains one public theorem/proof command, zero private theorem commands, definitions, new instances or extra public heads, and no sorry/admit/axiom/unsafe/native_decide token. Actual compiled environment ownership/generated declaration counts are not known yet; source-command counts are not substituted for the eventual all-owned audit.

## Updated H freeze and unchanged mathematical interface

The previous math report's H-unfrozen status is historical. Root now has the real preimplementation freeze `coordination/actual-bounded-relative-consumer-frozen-v1.lean.txt`,3065 bytes,SHA256 `f1376a57e91a7bdd943f8d29ef3af81701c64586a8cd05b8fdd1135615047ba1`, author activation `711637cea315f69a3c03cbd9ebc5430940df3bfc206d1c83739ad670e83c7649`, and2095-byte source PUBLIC-TYPE SHA256 `748d7c11038640989e91819b98d4d050e5457a76d2a5143621aa87552c4e3eac`.

I verified the whole2095-byte public head against the old reviewed proposal, the Root freeze and its unique immediate-before-proof occurrence in current Root H source01, SHA256 `da4a687c0c1636a13821441bc5373f66f88d95a24908b7a211ef2ff6ab97c173`,26660 bytes. Parent H binding is `832ad398bbdfc14bf6cd945c17e2ae631ca85d7d410866f1efb7eec82c96ea5c`. Root H whole proof was not reviewed; this check is only exact public-head binding and current source identity. Current checkpoint `0b956c807776723f19aebce628b880abf89b7cf2f9825baf57d355bc4c8ae2da` explicitly says complete source/uncompiled/released and formalQualified=false.

Therefore purelocal source implementation against this frozen real imported contract does not add an axiom or placeholder. The mathematical H interface is unchanged from the prior review. The source PUBLIC-TYPE is not yet a compiler-expanded actualTYPE, and no H formal qualification is claimed. H's qualified source/original object/all actual owners/types/values/transitive axioms/final independent review must be bound before any first unit221 native acceptance attempt, together with a valid C12 heavy phase allocation.

## Complete proof review: constants and all quantified data, source33–53

The L destructuring at34–35 follows the qualified actual publicTYPE535–895: epsilonF,CA,KD, their four conditions and the universal-M conclusion are in the right order. Specializing M16 at36 selects CF>0 before any Brownian process/law/n/x. H at37–38 similarly selects a universal CH before all data. At39–41, eta1/200 and min(epsilonF,1/(27*20000)) are positive; max(CF,CH)>0 follows already from CF>0. Ignoring unused upper/absolute constants and CH's positivity proof does not weaken a producer premise.

The introduced Brownian type/measure/probability instance, actual IsBrownianReal hypothesis, rho probability instance,n>0,x>=1/2,support,mean0/second1 occur in the exact public binder order. The anonymous probability instances remain in the local context for producer synthesis. `dsimp only` eliminates target lets; the later local beta/delta/P/DB are definitionally the same expressions. The two `change` commands retain the exact smallness and target quantities. Constants were chosen before every datum, with no hidden dependence or added hypothesis.

## Support, signs, and smallness, source54–84

At54–58, x>0 follows from x>=1/2, and n>0 casts to real positivity then sqrt(n)>0, so Bcap=sqrt(n)/(200x)>0. The field-algebra identity59–61 is legitimate using x!=0; `filter_upwards` at62–64 transports precisely the original a.e. cap to Bcap. The division-order call65–68 has the correct denominator orientation: nonnegative numerator, positive100x and100x<=200x imply sqrt(n)/(200x)<=sqrt(n)/(100x).

The `integral_nonneg` fact69 requires only pointwise nonnegativity of |z|^3; its real integral is nonnegative even without an explicit integrability hypothesis. A.e. finite support already guarantees the actual moment integrability mathematically, and no new moment assumption is added. Dividing by nonnegative sqrt(n) gives hdelta. Line71's intended hPsi is mathematically valid but its declaration name needs G1 repair. Given that fact, hWeight72–73 correctly records the nonnegative multiplier needed later.

The low smallness74 follows from the left min bound. At75–84,1+x<=3x and1+x>=0 justify `pow_le_pow_left₀` with natural exponent3; multiplication uses hdelta. Ring reassociation yields27(delta*x^3); the right min bound gives <=27/(27*20000)=1/20000. Thus H's true own smallness is derived from the frozen original smallness, not an extra premise.

## Entire explicit finite-event proof, source85–130

The local hHit proof85–109 treats both signs1/-1 and uses actualWall=x*sqrt(actual energy). At rank0, the prefix sum is0 and wall<=0. Nonnegative energy plus x>0 forces energy0; sign preservation gives signed energy0, and the positive-prefix maximum is0 because n>0. No zero-energy path is removed. For nonzero rank<=n, `Nat.one_le_iff_ne_zero` supplies rank>=1; `le_upperMax`, `prefixSum_smul`, and transitivity give the maximum bound. Conversely `upperMax_attained` furnishes a positive rank<=n and rewriting the attained value plus scalar-prefix identity produces a witness. These APIs agree with the existing FinitePath declarations and with the previously accepted transport implementation.

At110–130, unfolding doubleCrossingEvent and TwoSided.doubleCrossing gives exactly upper/lower weak-hit conjunctions. For the upper sign,1-smul/one-mul reduces directly. For the lower sign,(-1)-smul/negation and real arithmetic convert prefix<=-wall to wall<=-prefix in each direction. Upper and lower witnesses are independently extracted and reconstructed; no common hitting time or law symmetry appears. Both finite events use the same actual final energy. The explicit local equality avoids relying on an unavailable private/local export from220.

## Both producer calls and final estimates, source131–158

The x<=16 split131 is exhaustive, including x=16 in the low branch. The L call132–133 matches every qualified actual public binder in order: rho,Bcap,positivecap,a.e.support,mean,second,n,hn,x,hx,cap100,smallness,thenBm/PB/hBm. Its five result components are ownR0,ownRx,absolute-double,relative-double implication and absolute-maximum. `hRelative hlow` chooses the fixed-interval relative result; no absolute CA/KD estimate is promoted to an all-x relative bound. Rewriting hEvent and changing local aliases at135–137 yields the exact target events, with the actual public Brownian lower event already literally Bm(t)<=-x. At141–143, `mul_le_mul_of_nonneg_right` uses hWeight and CF<=max(CF,CH), and associativity matches the source product.

In the other branch, `lt_of_not_ge hlow` gives16<x and hence16<=x. The H call145–146 matches the whole frozen public binder order: Bm/PB/hBm first, then rho/Bcap/support/moments/n/hn/x/lower threshold/cap200/derivedu. The cap comparison is definitionally reflexive because Bcap was defined with that denominator. Its eleven conjuncts are destructured correctly: second/third integrability,positive delta,R=u,measurability/integrability ofD,DB/Z0 facts, the residual implication,then the final Brownian comparison. The residual implication is ignored rather than supplied without its additional premise.

`rw [hR]` at149 substitutes H's genuine own normalized-law truncation budget R=u in the final Brownian comparison. P,D,DB,delta/u aliases are definitionally the frozen same-law expressions. Associativity at152 gives CH*delta*(1+x)^3*Psi(x). At156–158 the nonnegative multiplier hWeight enlarges CH to max(CF,CH). There is no unhandled boundary or hidden payment assumption. Source159–160 closes the theorem scope and namespace, adding no declaration.

## Findings, evidence status, and natural handoff

G1 is the sole identified new-source defect. The complete conditional mathematics and unchanged public/source fidelity remain covered by the old accepted report plus the full new implementation review above. This report does not certify elaboration success: static inspection cannot replace native Lean/kernel checking, and the uncompiled H module remains a separate qualification dependency.

The next source-bound step is the author's local correction of line71 with a genuine public positivity interface, a new exact source hash/version and review of that affected change. Once H is formally qualified and bound and a C12 heavy phase exists, run the new complete consumer native check and same-original-object all-ownedTYPE/non-theoremVALUE/transitiveAX audit, then an independent exact machine supplement. Do not replay accepted219/220 or change shared Gaussian-tail code for this local call defect. C2/C12/fullRootOD remain OPEN; original unbounded-law restoration is outside this unit and OQ3 remains PAUSED_BY_USER.

All review and artifact writer authority is released at natural completion: reviewer0,proof/artifact writers0,children0,heavy0,inflight0,external0. Source001, producer files, parent activation and old sealed mathematical review remain byte-identical. This finite release does not claim continuing execution.
