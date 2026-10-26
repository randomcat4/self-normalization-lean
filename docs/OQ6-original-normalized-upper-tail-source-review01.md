# Unit204 independent complete source/proof review

STATUS: SOURCE_CORRECT

This is a fresh independent complete source-to-statement and proof review of the exact unit204 source. It is a source verdict, not a kernel or transitive-axiom qualification. Unit204 remains qualified=false and actualOwned=UNKNOWN until its own first native run and same first-original-object complete ownership audit have been reviewed in a new machine subdirectory. The reviewer has not authored or changed this proof.

## Exact object under review

The sole written global declaration is Shao.OQ6.OriginalNormalizedUpperTail.original_normalized_upper_tail. The complete source is 4730 bytes, 105 LF, no CR or BOM, SHA256 18c4ea27e6214beb74cd995da40461b772aca724566086629ac195e2bf2b6aa3. The whole105-line source, all proof bodies, full proof notes, static scan, consumed bindings and all nonredundant semantic fields of the source/declaration/data/closure map were read. Repeated fields were independently compared against the completely read frozen contract; mapped source bodies and all67 byte spans were independently checked against the actual source. The source was already UTF-8/LF before any unit204 machine gate. No source normalization or byte repair was performed by this reviewer.

The exact parent freeze is cbc8550c5eb575888aa63a4012b68c937f7ffd88e0ab138e284cb049083ca208/6027B. The canonical complete data/Prop contract is e7d264e92c28c7482c497150beeb430ae2f430b182656041d9a4b5dd9eb88c29/33657B. The 798-byte public head hash is ccf2cfd75a781f4e72bcf4fd8c759bbbc73752835c8cb71a6a848b537deaa03d, with 14 internal LF and no terminal LF. The prelude is exact: its three frozen imports, autoImplicit=false, namespace, noncomputable section and open MeasureTheory are preserved. There are no surrounding section variables, extra global definitions, private helpers or instances. There is one written source theorem; this is not a claim that actual generated environment ownership has already been enumerated.

## Original source and statement fidelity

The complete read-only p51 source was read, all355 LF/17326B, SHA256 96920f428b8fc09788a6388103cefe398e3ec739129a5922b984babd09e99359. Its status remains an uncertified repair candidate at the source-document level; reviewing this one exact component does not certify its other sections. S1 fixes W=S/sqrt(n) and V²=E/n. With V taken to be the nonnegative square root, S10's upper-threshold complement is the strict event sqrt(y)*n^(1/4)*(4+sqrt(E/n)) < |S/sqrt(n)|. The upper term of S11 is 4*exp(-y*sqrt(n)/2). The Lean head expresses precisely this event, law and bound, with the literal Real.rpow(n,1/4), rather than an alternative power convention or asymptotic substitute.

The exact statement is:

```lean
theorem original_normalized_upper_tail
    (n : ℕ) (hn : 0 < n) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgmean : (∫ o : Ω, g o ∂μ) = 0)
    (hgsecond : (∫ o : Ω, (g o) ^ (2 : ℕ) ∂μ) = 1)
    (y : ℝ) (hy : (1 : ℝ) ≤ y) :
    (Shao.OQ6.CanonicalDoubleGhostRowMoments.sampleLaw n μ).real
      {x : Fin n → Ω |
        Real.sqrt y * Real.rpow (n : ℝ) ((1 : ℝ) / 4) *
            ((4 : ℝ) + Real.sqrt
              (Shao.OQ6.OriginalGhostGoodEvent.sampleEnergy n g x / (n : ℝ))) <
          |Shao.OQ6.OriginalGhostGoodEvent.sampleSum n g x /
            Real.sqrt (n : ℝ)|} ≤
      (4 : ℝ) * Real.exp (-(y * Real.sqrt (n : ℝ)) / (2 : ℝ))
```

The theorem explicitly assumes n>0 for deterministic normalization. Source n>=4 implies this condition. This is a transparently stronger positive-natural component, and does not extend the other p51 arguments to n=1,2,3. The sample domain is Fin n -> Omega on an arbitrary measurable space, under the identical-coordinate finite product law mu. The complete source's measurable-factor discussion permits the actual real observables on arbitrary measurable spaces; the proof here merely consumes the already qualified arbitrary-measurable unit202 interface.

The assumptions are exactly probability mu, measurable and L² real g, integral g=0, integral g²=1, and y>=1, together with the explicit positive natural n. The Bochner-integral syntax and MemLp exponent2 are the actual ones in the consumed TYPE. There is no StandardBorelSpace, fourth or mixed moment, exponential moment, symmetry, atom-free law, tail continuity, conditioning, or positive sample-energy assumption.

## Complete data, binder and capture review

The eight local aliases M,r,q,t,E,S,A,B have exactly the frozen typed initializers and order. M is the actual sampleLaw; r=sqrt(n), q=literal Real.rpow(n,1/4), and t=sqrt(y)*q. E and S are the actual sampleEnergy and sampleSum functions. A and B are the two exact strict event predicates. M captures n/Omega/mOmega/mu, r and q capture only n, and t captures n/y through q. E and S capture n/Omega/g, with their x binders restricted to their initializer bodies. A and B capture these fixed aliases, n/Omega and t, with x restricted to their set predicates. Neither t nor r sees any sample point, energy or sum.

The three other frozen closures are the two global integral integrands (o -> g(o), o -> g(o)^2) and the typed measure-evaluation closure (a -> M.real a). Their domain and captures are unchanged. The map explicitly counts eight semantic function/predicate closures: these three, the global target predicate, E, S, A, B. The global target predicate and the A/B notation closures were already contained in frozen heads/initializers; they introduce no new mathematical declaration.

All22 local proposition heads are exactly frozen. Every mapped ambient context equals the13 global theorem binders. Every lexical available-name list is precisely the eight aliases and the preceding local facts; no forward capture occurs. Four intro-x proof lambdas implement hE_div/hAbs_div/hscale/hpoint with the types supplied by their explicit universal heads. The fifth pointwise proof function is the set-extensionality x in hevents. Each x is bound only in that individual proof, after the fixed aliases.

The22 anonymous by blocks are the outer theorem proof,17 local by proofs and four small numeric/algebraic calc arguments. The closed 0<=1/4 proof captures no mathematical input; the rational exponent simplification captures n; the two ht_square calc proofs capture the displayed y/q/r and square identities. The direct-term local proofs hNnonneg, hysqrt_ge_one, hrne, hy_square and hmeasure are also covered. Tactic-generated elaborated proof terms and any owned descendants remain unobserved until the actual audit; source-level counts are never substituted for that audit. Full heads, captures, scopes, source spans and independent decisions are in SOURCE-COVERAGE.json.

## Proof review

1. **hNatOne**: Natural discreteness changes 0<n into 1<=n; omega is applied only to the stated natural hypothesis.

2. **hNpos**: The order-preserving natural-to-real cast transports hn; it adds no real-valued domain generalization.

3. **hNnonneg**: Order weakening of the already proved strict positive real cast.

4. **hNge1**: Casts hNatOne after using natural discreteness, so the positive-natural lower bound is justified.

5. **hy_nonneg**: Transitivity from 0<=1<=y; linarith only uses hy and arithmetic.

6. **hysqrt_ge_one**: Real.one_le_sqrt.mpr has the exact direction 1<=y -> 1<=sqrt y and no extra hypothesis.

7. **hq_ge_one**: After delta-unfolding q, Real.one_le_rpow takes hNge1 and the closed rational proof 0<=1/4; Real.rpow is definitionally the real Pow instance.

8. **ht**: After delta-unfolding t, the product of the two established factors >=1 is >=1; all typeclass inputs specialize to Real.

9. **hrpos**: The Real.sqrt_pos equivalence, after unfolding r, consumes exactly hNpos.

10. **hrne**: ne_of_gt hrpos is the correct orientation r != 0.

11. **hq_square**: The symmetric direction of Real.rpow_mul_natCast at nonnegative base n, exponent 1/4 and natural exponent2 gives q^2=n^((1/4)*2). Rational normalization gives exponent1/2 and reversed sqrt_eq_rpow gives r. The outer square is natural Pow, not real rpow.

12. **hy_square**: Real.sq_sqrt requires y>=0, supplied by hy_nonneg.

13. **ht_square**: The square of sqrt(y)*q expands polynomially, then the two exact square identities give y*r.

14. **hE_div**: Real.sqrt_div' has an arbitrary real numerator and only denominator n>=0. For each x it gives sqrt(E(x)/n)=sqrt(E(x))/sqrt(n); unfolding r finishes. No positivity, or even a separate nonnegativity lemma, for E(x) is consumed.

15. **hAbs_div**: abs_div at the real-field instance rewrites |S(x)/r| to |S(x)|/|r|; generated additive abs_of_pos at hrpos rewrites |r| to r. S(x) can have any sign.

16. **hscale**: Distribution and cancellation of the single denominator r yield (t*(4+sqrt(E)/r))*r=t*(sqrt(E)+4*r). hrne proves every variable cancellation lawful. field_simp/ring is a candidate tactic implementation pending kernel execution.

17. **hpoint**: Unfolding A/B and applying hE_div and hAbs_div produces a<|S|/r. The unprimed lt_div_iff₀ hrpos is exactly a<|S|/r iff a*r<|S|; hscale identifies a*r with the B threshold. The resulting biconditional is exact for every x.

18. **hevents**: Set extensionality uses hpoint at an arbitrary x. There is no almost-everywhere deletion or boundary exception.

19. **hmeasure**: Congruence through fun (a : Set (Fin n -> Omega)) => M.real a transports equality of sets. No measure monotonicity, measurable-set side condition, or probability approximation is needed.

20. **hproducer**: The full90-line actual qualified unit202 TYPE specializes with n, mu, g, hg, hg2, hgmean, hgsecond, t, ht. It has no hn argument. Unfolding only M/B/E/S/r gives exactly its sampleLaw and strict self-normalized event. No old proof is reopened.

21. **hexponent**: Substitution of ht_square under negation and division by2 gives exactly the target exponential argument.

22. **hrhs**: Equality congruence through exp and multiplication by4 substitutes hexponent; no exp inequality or approximation is used.

The final change/calc at lines99-103 is equality/inequality/equality transport: M.real A = M.real B <= 4 exp(-t²/2) = 4 exp(-y*r/2). Delta-unfolding the aliases is exactly the unique frozen conclusion. There is no new random variable, witness, choice, branch restriction or hidden premise. The argument is complete as mathematics and as the submitted source-level proof route. Tactic elaboration success is deliberately left to the new native gate.

## Complete pinned primary API review

The pin is mathlib807d3836b165983210ee2ecf3cd28f239436949c and Lean leanprover/lean4:v4.36.0-rc1. All17 mapped primary entries were reviewed with their whole raw and effective heads and full chronological namespace/section/inherited-variable/typeclass contexts, rather than name-prefix matches. The actual raw prefixes were read through Pow/Real994, Real/Sqrt384, Order/Field/Basic675 and Order/GroupWithZero/Basic1138; Group/Abs261 and Group/Unbundled/Abs317 were read in full. A truncated display in the GroupWithZero prefix was resolved by a complete bounded reread of lines521-605, covering the omitted portion. All six full-source packet hashes, all17 raw head slices, effective-head hashes and exact prefix bytes agree.

Real.rpow is the real part of the complex power, and the real Pow instance is defined from it; rpow_eq_pow is definitional. rpow_mul_natCast has implicit nonnegative base x and explicit hx/y/n, with direction x^(y*(n:Real))=(x^y)^n. Source uses its symmetric direction at natural2. one_le_rpow needs only base>=1 and exponent>=0. sqrt_eq_rpow is read in the reopened Real/Sqrt section, with explicit x and exponent1/2; the source uses its reverse direction. Real.sqrt_pos and one_le_sqrt are the Real declarations, not the earlier NNReal names. sq_sqrt consumes y>=0.

The selected sqrt_div' has explicit arbitrary real numerator x, implicit real denominator y, and only hy:0<=y. The similarly named unprimed rule's numerator-nonnegative hypothesis is not silently borrowed. abs_div is the root declaration in the LinearOrderedField section, effectively Field/LinearOrder/IsStrictOrderedRing, all fulfilled by Real. abs_of_pos is the additive declaration generated by the exact @[to_additive] mabs_of_one_lt under Lattice/Group/MulLeftMono: effective Lattice/AddGroup/AddLeftMono and h:0<a. Its generated source provenance is stated honestly; no new actual-TYPE probe is claimed.

The selected unprimed lt_div_iff₀ is in GroupWithZero/PartialOrder/MulPosReflectLT with all effective class assumptions, not a primed or differently oriented rule. For Real and r>0 it is a<b/r iff a*r<b; it needs no sign on a or b. one_le_mul_of_one_le_of_one_le is in MonoidWithZero/Preorder with ZeroLEOneClass/PosMulMono and requires exactly both factors>=1. The unused rpow_mul/sqrt_nonneg/sqrt_div/abs_of_nonneg alternatives were read and distinguished. No raw head was cut at a default binder or mistaken for a similarly named declaration.

## Consumed qualified interfaces and evidence reuse

Unit202 is reused as a qualified exact theorem. Both the authoritative parent qualification193512d907a4b871da7400e2165d1aa122d9baa39012f6691771d9f136718049 and independent final qualification44f9cad7e90e7076173a74d0e3cfb6f02b94a45e1a534530b254ea3bfc2a6b3d were read completely and locally rehashed. Their exact source is cfa791fd240ee560b2a876ea69a64e46c7c84735c935e1380446025e69a9e61a/3989B79LF. The parent key originalObject and independent key firstOriginalObject both bind1bbfe0d3c074f66d956598045e392b776bccf127508122d58e553d507d7eda84/188680B/mtime_ns1792995157698608053. The existing independently qualified actual native and same-original-object audit exits are0/0; historical wrapper success=false is retained and is not described as a new wrapper pass.

The complete90-line actual unit202 TYPE was read, including all universes, measurable-space/probability instances, MemLp/integral parameters and the actual strict conclusion. Its exact SHA is3d7d9a3e5f03be6db28f7b6e8d34182b156cf67a0e852b3566a1c2b21d711169 and matches original metadata b3093f9650cf953122572b5b6101dd1c6e0e3ccc0b9a1d70d14e0c82d6e4b22d. The call n mu g hg hg2 hgmean hgsecond t ht is exact: no hn parameter is inserted.

The complete actual TYPE and FULLVALUE of unit188 sampleLaw and unit200 sampleEnergy/sampleSum were read and independently matched to each original metadata and exact qualification. sampleLaw is Measure.pi of the identical coordinate law on Fin n; sampleEnergy is the finite sum of natural squares; sampleSum is the finite sum of g at the actual coordinates. All stored TYPE/VALUE hashes agree. No old theorem proof body was re-reviewed and no old producer/kernel/leaf-axiom check was replayed. The old source/object qualification is reused; no new server observation is claimed by this local reviewer.

The deterministic binding record checks66 distinct path/hash pairs, all pass. It also checks all67 map source spans, all17 primary raw/effective heads, all six full pinned primary sources and the three consumed data TYPE/FULLVALUE records. Counts are derived from actual verified maps, not copied from descriptive status text.

## Boundary and scope decisions

At n=1 and y=1 the deterministic factors still satisfy all inequalities and denominators are positive. n=0 is explicitly excluded. Signed sums and repeated observations remain allowed. The events agree at every point, including exact threshold equality, where both strict predicates are false. At E=0, sqrt_div' remains valid and no energy division or exceptional branch appears. There is no null-set deletion, continuity passage, or atom assumption. The measure equality is pointwise set equality, so atoms and ties are retained exactly.

This verdict addresses only the normalized strict upper component. Lowenergy203, the G_y union, fullS11, C2/C12/OQ56 remain OPEN. Original C1 immutablev85 remains complete and OQ3 remains separately PAUSED_BY_USER. Existing p54 repairs are preserved. Attribution remains p51 -> Shao-Zhou2016(92), with upstream named Jing-Shao-Wang2003 Lemma6.4; this reviewer read p51 and the exact formal/primary packets and does not claim to have newly read those full published texts or establish originality. The124 unified mechanism remains a non-prerequisite.

## Remaining qualification gate and reviewer release

No source-level mathematical or frozen-contract gap was found. No forbidden sorry/admit/new axiom/unsafe/native_decide token occurs. Qualification still requires the lead's first exact-source native run, complete sameFIRST original-object owner enumeration without a namespace filter, every actual owned TYPE, every non-theorem FULLVALUE, recursive axiom whitelist audit, original-object/source binding and actual natural command completion. This same independent context may review those new records later in a fresh machine subdirectory; this SOURCE seal must remain immutable.

The reviewer has used only local read/hash/static comparison/report writes under final-review-01. Server/Lean/AX/upload/Git/API/network/child operations are all zero. Current phase37 resources are acknowledged without consuming a heavy slot; earlier phase35/36 prose is historical and does not alter exact old evidence. Author and reviewer remain separate. Configured model/effort is gpt-6.1-sol/xhigh; actual backend model/effort and input/cached-input/output/reasoning-subset counters are unobservable and remain null. DONE/CHECKPOINT/RELEASE0 record zero writer/execution/heavy/inflight/pendingExternal/children after this completed local unit; they do not claim persistent runtime continuation.
