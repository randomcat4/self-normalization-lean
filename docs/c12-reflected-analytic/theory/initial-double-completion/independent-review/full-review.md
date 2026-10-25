# Fresh independent complete mathematical review

STATUS: CORRECT

The frozen theoretical target is true and the complete candidate proves it under its stated assumptions. This verdict covers only the new initial actual double-completion estimate, its whole-real-line BV bound, and its strengthened closed terminal-cutoff comparison. It gives no new Lean, kernel, transitive-axiom, or whole-C2 qualification. C2/C12 remain OPEN.

The review is independent of the author. I received the exact frozen subject and candidate in a fresh review context, read every listed mathematical input completely, checked the current curated source bindings, and did not alter the subject, candidate, public contracts, or source files. No Lean/build/axiom/server/simulation/upload/publication command was run. Existing qualified producer proofs were consumed through their complete public heads and relevant values; they were not re-reviewed.

Requested configuration: gpt-6.1-sol / xhigh / fresh fork none. Actual backend identifier, actual effort, and token subdivisions are unobservable to this reviewer and are recorded as null. A real running-context RUNTIME-ACK was written before the mathematical review.

## 1. Exact coverage and binding result

The six frozen inputs were fully read, with these byte counts, line spans, and SHA256 hashes:

| Input | Bytes | Complete read | SHA256 |
|---|---:|---|---|
| frozen-theory-subject.json | 1452 | 1–18 | b1b23518729ad6661f72f6c9a849e560a14ddb55e3ec032d357d5950b186a95b |
| full-proof-candidate.md | 9949 | 1–212 | 51996bf52efb755edf9012cdf50da16d1c910afb2069ffb5e192395854c0b298 |
| primary-source-excerpts.tex.txt | 4041 | 1–86 | 2146f9f315c8139ebd068eaa8219c07b714385510781e6ef447c2ea9fc09118d |
| consumed-contracts-and-values.md | 10392 | 1–338 | b16545283862663abc3917ceed817cd473c4ddf45df691f818136f800e9c5f03 |
| consumed-interface-bindings.json | 5039 | 1–157 | 43baac3725bda95a9d59399a6567feda4865a42e9e30985bddfc3903d20f7b5f |
| formal-interface-plan.md | 5135 | 1–40 | 1aa5eea00589fe3fe8939e0245f4f60fe6bc3aa87559eecf0293b75a041abe29 |

All six input hashes and byte counts match input-freeze.json. All 16 curated source file hashes and byte counts match consumed-interface-bindings.json. All 36 fenced contract/value snippets are exact raw UTF-8 substrings of the corresponding current curated files, at the recorded source lines. The detailed source start-byte offsets, snippet UTF-8 byte lengths, line counts, hashes, and checks are in binding-validation.json.

The primary source C:/game/shao/current/c12/supplement.tex has 235015 bytes and SHA256 b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd, matching the freeze. Both supplied excerpts exactly equal the current source spans: lines 3934–3965 and 4699–4749. Including the final LF of each span, the read primary-source spans contain 1615 and 2359 UTF-8 bytes respectively. Full-source hashing is a binding check, not a claim to have read all 235015 bytes as mathematical context.

Additional relevant values read directly were:
- library/Shao/Basic/FinitePath.lean, lines 1–34: Path, prefixSum, prefixSquares, energy (the incidental following trivial lemma was not re-reviewed).
- library/Shao/Probability/GaussianTail.lean, lines 1–21: actual standard Gaussian density and strict-upper-tail probability definitions.
- library/Shao/C2/BrownianBridgeLaw.lean, lines 1–22: actual bridgeNoise and pinPath values, including endpoint pinning.

Their full-file hashes and exact additional read spans/byte counts are recorded in validation.json. AGENTS.md and the math-theorem skill and required reviewer references were read. Relevant server/team restrictions were consulted without running or changing any server process.

## 2. Frozen scope, source fidelity, and admissible inputs

The frozen subject is lines 10–17 of frozen-theory-subject.json. The mathematical objects in candidate lines 14–23 agree with that subject:
- the two weak-wall hits are on the same bridge path G_t+t w;
- rho is the original real Borel probability law, with EX=0 and EX²=1, only finite second moment;
- P is the actual n-coordinate iid product, n≥1;
- Q is the sum of the actual squares, and W equals S/sqrt(Q) on Q>0 and 0 on Q=0;
- R_n(t)=n E F((1+t)X/sqrt(n)), with F(z)=z² min(|z|,1);
- Z0 has value 1, not j_x(0), on Q=0;
- x≥1 and b=R_n(x)≤1/2;
- a single universal C precedes all laws, n, x, v, Brownian processes, and implementation spaces.

The source excerpt defines this same double-hit kernel and marginal initial-completion expression. The candidate explicitly labels and pays the source's zero-energy sentence repair: the correction is 1_{Q=0}(1-j_x(0)), not a probability multiplied by the small supremum of j_x. No source byte or mathematical assumption is changed.

The terminal closed-cutoff rare bound is an explicitly stated strengthening, proved by the same BV argument and same constant. It is not misidentified as the separate source assertion about absolute interval comparisons for arbitrary x>0. The candidate does not claim to prove that separate assertion, regular cancellation, rare suffix, postwall, fixed-window, final status/telescope assembly, or whole C2.

The scalar input remains an attributed existing Shao scalar bound as restated by Pinelis2011. No novelty claim is made.

## 3. Same-path event identity and legal use of reflection/image contracts

Candidate lines 38–43 are correct. For fixed w, write U={all bridge values < x}, L={all bridge values > -x}. The strict interval is U∩L by the actual strictInterval definition. The double weak-hit event is Uᶜ∩Lᶜ, since negating the universal strict inequality gives existence of a weak hit. Consequently its probability is

j_x(w)=1-P(U)-P(L)+P(U∩L).

This is both crossings, not their union. The identity is pointwise in w and retains w=±x. The bridge law is a probability by the consumed isProbabilityMeasure_bridgeLaw contract. The actual strictUpper/strictLower values and bridgePath endpoints in the packet match the candidate's U,L.

For |w|<x, set a=x,y=0,T=1,z=w in bridge_upper_formula and bridge_lower_formula. Their hypotheses are satisfied: T>0, 0<x, w<x, 0>-x, and w>-x. This yields U(w)=1-exp[-2x(x-w)] and L(w)=1-exp[-2x(x+w)]. The interval theorem additionally needs |y|<a and |z|<a, also satisfied; its actual parameter order is intervalImageCandidate a z T y. Thus the required instance is intervalImageCandidate x w 1 0, exactly the exponent specialization used in candidate lines 50–55.

Here is the complete indexing check. The finite image terms contain A-indices m=0,1,-1 and B-indices m=0,-1. At y=0,z=w,T=1,

imageA=8m²x²+4mxw,
imageB=2(2m+1)²x²+2(2m+1)xw.

The m=0 A-term is 1. The two finite B-indices give k=2m+1=1,-1. These are exactly exp[-2x(x+w)] and exp[-2x(x-w)], which cancel the terms contributed by 1-U-L. The actual spatialTailBlock has A-indices n+2 and -(n+2), giving every m with |m|≥2 exactly once, and B-indices n+1 and -(n+2), giving k=2n+3 and -(2n+3), hence every odd |k|≥3 exactly once. The finite m=±1 A-terms remain. The result is precisely candidate (5). The absolute convergence verified in the next section legitimizes separation, pairing, and reindexing of these tails; equivalently one can first use the same finite block identities and pass to their absolutely convergent limits.

For w≥x, strictUpper is empty because bridgePath at t=1 equals w. The double hit is therefore the lower weak hit, and the lower reflection theorem is legal because w≥x>0>-x. Its probability is exp[-2x(x+w)]. For w≤-x, strictLower is empty; the upper reflection theorem is legal because w≤-x<x and yields exp[-2x(x-w)]. This proves the candidate's exterior formula, including w=±x, and gives j_x(±x)=exp(-4x²). No distributional assertion discarding equality at a wall is used.

## 4. Uniform convergence, complete tails, exact wall joining, and global variation

Let r=exp(-4x²). For x≥1, 0<r≤exp(-4)<1/2.

For each A-pair indexed by h≥1, the maximum of either signed-m exponential on [-x,x] is A_h=exp[-4h(2h-1)x²]. For each odd B-pair k=±(2l+1), l≥1, the maximum of either exponential is B_l=exp[-4l(2l+1)x²]. Each individual term is nonnegative and monotone in w, so its interval variation is at most its maximum. Since h(2h-1)≥h and l(2l+1)≥l,

2 sum A_h + 2 sum B_l ≤ 4 sum_{h≥1} r^h = 4r/(1-r) ≤ 8r.

This proves absolute uniform convergence on the entire closed interval, not merely interior pointwise convergence. It bounds the supremum norm of the difference series and the variation of every finite partial sum by 8r. For any fixed finite partition, uniform convergence passes each increment to its limit; the bound 8r therefore passes to its variation sum. Taking the supremum over partitions gives interval variation ≤8r. No derivative series or exchange of derivative and integral is required.

The wall joining in lines 84–91 is exact. Set r_h=exp[-4h(2h-1)x²] and s_h=exp[-4h(2h+1)x²]. At w=x the A-pair m=±h is r_h+s_h, whereas the B-pair k=±(2h+1) is r_{h+1}+s_h. Hence matching truncations through h=M differ by r_1-r_{M+1}, tending to r. At w=-x, changing both integer signs gives the same value. These values equal the true exterior reflection value already established, so the glued actual j_x is continuous at both walls.

Each exterior monotone piece has variation r, since its finite endpoint value is r and its limit at the corresponding infinity is 0. Refining any global finite partition by the walls bounds its variation by the sum of the three pieces. Thus TV_R(j_x)≤8r+r+r=10r, ||j_x||∞≤8r, and their sum is at most 18r, proving the frozen coefficient. Continuity also holds throughout the interior by uniform convergence and outside by the exponential formula. The limits at both infinities are 0. No finite-window estimate is promoted to an unproved whole-line claim.

## 5. True scalar normalization, atoms, and the closed-cutoff BV transfer

Candidate lines 97–124 legally consume finite_second_scalar_closed_cdf_budget. The hypothesis int X²=1 makes its sigma equal to 1, and its normalizedLaw is exactly map(X/sqrt(n))rho. Finite second moment and positive n imply that this mapped law has integrable square. The actual prefixSum at k=n is the sum of all coordinates, since every Fin n coordinate has value < n; actual energy is sum X_i²≥0. Its normalizedEndpoint branch therefore agrees with the candidate's W, including W=0 exactly on Q=0. The existing scalar contract gives a universal Cs>0, before rho and n, satisfying the closed-CDF estimate for every real t. No scalar result is smuggled in as a hypothesis to the new theorem.

The budget is finite because F(z)≤z²; the relevant map identity gives R_n(t)=n int F((1+t)z) under that normalized law. The monotonicity contract with s=0,t=x uses -1≤0, 0≤x and the mapped finite second moment. It gives R0≤b. There is no atomlessness assumption.

The Stieltjes convention in lines 104–111 is correct. A bounded left-continuous BV function f has finite signed right-increment measure df characterized by df([a,b))=f(b)-f(a), with total variation at most TV_R(f). Its finite limit c=f(-infinity) exists and

f(w)=c+int 1_{t<w} df(t).

The strict inequality is essential. The integrand is Borel and bounded by 1; the product probability with the finite measure |df| gives absolute integrability. Signed Fubini therefore yields, for probability laws mu and gamma,

int f dmu-int f dgamma
 = int [mu((t,infinity))-gamma((t,infinity))] df(t)
 = -int [mu((−infinity,t])-gamma((−infinity,t])] df(t).

The constant c cancels and the absolute value is at most TV_R(f) sup_t |F_mu(t)-F_gamma(t)|. This proves the candidate's bound with the closed CDF directly, including arbitrary atoms of mu.

Applying it to continuous j_x gives 10 Cs R0 r. For f_v(w)=j_x(w)1_{w≤v}, continuity of j_x makes f_v left-continuous, with right jump -j_x(v) at v. Its increment measure has the atom -j_x(v) delta_v, and its total variation is at most TV(j_x)+|j_x(v)|≤18r. Its representation contains 1_{v<w}, the complement of the closed cutoff. Consequently the bound is 18 Cs R0 r. This verifies the sign, endpoint convention, and v=0 case without replacing a controlled closed-CDF discrepancy by an uncontrolled atom probability.

## 6. Actual Brownian product law, simultaneous reconstruction, and integrability

The bridgeNoise and pinPath values are genuine continuous paths pinned at 0 and 1. On BridgeNoise×R the map (g,w)↦[t↦g(t)+t w] is continuous for the supremum norm: its change is bounded by ||g-g'||∞+|w-w'|. The maximum and minimum on the compact unit interval are continuous path functionals. Thus the same-path double weak-hit event is a Borel set of the product, and so is its intersection with {w≤v}. This also directly supplies joint measurability, rather than relying only on separate measurability of each bridge section.

The consumed bridge_endpoint_hasLaw states the actual joint law (bridgeNoise(B),B_1)=Qbridge.prod(gaussianReal 0 1). The ae_bridgeNoise_eq statement supplies one a.e set on which reconstruction holds for every t simultaneously. Therefore both raw Brownian events in the target agree a.e with pullbacks of the corresponding measurable product events; uncountably many timewise exceptional sets are not unioned. If the ambient probability space is not complete, this a.e transport gives completion/null measurability, which is sufficient for the real measure and indicator integrals used here. No unmentioned completeness or pointwise continuity of every raw sample is needed.

Fubini for the bounded nonnegative product indicators now gives

int j_x(w) dgamma(w)=P_B(double weak hit),
int j_x(w)1_{w≤v} dgamma(w)=P_B(double weak hit and B_1≤v).

The bridge sections are exactly the already-defined j_x. This establishes both identifications in candidate (11) from the actual qualified joint law; no arbitrary HasLaw oracle or new conditional-probability assumption is introduced.

On the sample side, Q and S are measurable finite sums and W is their measurable branch-defined ratio. The established continuous j_x is Borel and lies in [0,1]. Hence Z0 is measurable, bounded in [0,1], and integrable under the actual product probability; the terminal-cutoff observable is also measurable, bounded in [0,1], and integrable. There is no missing integrability of either observable. The normal expectations are likewise integrable.

## 7. Finite-second-moment rare zero-energy payment

I checked candidate lines 143–180 directly on the original law, not a conditioned or truncated replacement law. Put A=sqrt(n)/(1+x)>0 and p=P(X≠0). The variance-one condition gives p>0; p≤1 holds because rho is a probability.

Since |(1+x)X/sqrt(n)|≤1 exactly when |X|≤A, splitting F at that threshold gives

b=(1+x)² E[X²;|X|>A] + (1+x)³/sqrt(n) E[|X|³;|X|≤A].

Equality at |X|=A may be put in the small part because both branches of F agree there. This identity is exact. The truncated cubic is integrable because |X|³1_{|X|≤A}≤A X². Thus finite second moment alone suffices.

Writing m2=E[X²;|X|≤A], m3=E[|X|³;|X|≤A], the identity and b≤1/2 give m2≥1-b/(1+x)²≥1/2. Apply Holder with exponents 3/2 and 3 on E={0<|X|≤A}:

m2 ≤ m3^(2/3) P(E)^(1/3) ≤ m3^(2/3) p^(1/3).

Hence m3²p≥m2³≥1/8. In particular m3>0 and the nonnegative budget decomposition implies b>0. Its cubic term also gives n b²≥(1+x)^6 m3². Multiplying by p and dividing by the now strictly positive b² gives

n p ≥ (1+x)^6/(8b²).

No full third moment is used.

For the actual finite path, Q=0 if and only if every squared coordinate vanishes, equivalently every coordinate is zero. The actual iid product law therefore has P(Q=0)=(1-p)^n. The elementary inequality 1-p≤exp(-p) for p∈[0,1] yields

P(Q=0)≤exp(-np)≤exp[-(1+x)^6/(8b²)].

This includes p=1: the left side is 0 for n≥1, and there is no logarithm of zero. Neither the Holder step nor the all-zero probability step assumes a density, symmetry, or absence of atoms.

For the uniform Gaussian comparison let c0=exp(-3/2)/sqrt(2 pi), with pi here the numerical circle constant. On [x,x+1/(1+x)] write u=x+h. Then xh≤1 and h²/2≤1/2, so the standard Gaussian density is at least c0 exp(-x²/2). Integrating over length 1/(1+x) gives

Psi(x)≥c0 exp(-x²/2)/(1+x).

For x≥1, (1+x)^6≥2x²+8. Since b²≤1/4,

(1+x)^6/(8b²)≥x²+1/b².

Thus the ratio of the exponential rare bound to b Psi(x) is at most

c0^(-1) (1+x) exp(-x²/2) b^(-1) exp(-1/b²) ≤ 2 c0^(-1).

The last two factors are bounded by 2 and 1 respectively on x≥1, 0<b≤1/2. The first follows, for example, by differentiating (1+x)exp(-x²/2), which is decreasing on x≥1 and is less than 2 at 1. For the second put u=1/b≥2 and use u exp(-u²)≤1. Consequently K=2 sqrt(2 pi) exp(3/2) is one numerical constant, fixed before all data, with P(Q=0)≤K b Psi(x). The Gaussian is atomless by its density; no such condition is added to rho.

The same lower Gaussian estimate gives

r/Psi(x)≤c0^(-1)(1+x)exp(-7x²/2)≤2 c0^(-1)=K.

All inequalities retain x=1 and b=1/2.

## 8. Exact correction, terminal strengthening, and constant order

The pointwise identity in candidate line 188 is exact, because W=0 on Q=0:

Z0=j_x(W)+1_{Q=0}(1-j_x(0)).

Since 0≤j_x(0)≤1, the correction has absolute expectation at most the full rare P(Q=0). The small supremum of j_x cannot be used to bound 1-j_x(0), and the candidate does not do so.

Multiplication by 1_{W≤v} gives the exact correction
1_{Q=0}1_{0≤v}(1-j_x(0)).
It is bounded by the same rare probability for every real v. At v=0 the correction is included. For v<0 it vanishes. This accounts for the actual Q=0 atom and every other endpoint atom without changing the terminal inequality.

The marginal scalar error is at most 10 Cs R0 r and the terminal scalar error at most 18 Cs R0 r. The Brownian identifications, R0≤b, r≤K Psi(x), and the rare probability bound therefore give both errors at most

(18 Cs+1) K b Psi(x).

Choosing Cs from the pre-existing universal scalar theorem, then the numerical K, and finally C=(18 Cs+1)K>0 establishes the exact quantifier order. C is independent of rho,n,x,v,B and all implementation spaces. The same C works for the marginal and simultaneously for every closed cutoff v.

## 9. Boundary and assumption audit

- n=1 is not excluded by a new hypothesis. The conditional estimates remain valid, even though the small-budget hypotheses themselves force a much larger n through the derived support bound.
- x=1 and b=1/2 are retained throughout non-strict inequalities.
- b=0 is excluded by a proved consequence of variance one and the actual budget, not by a silently added assumption.
- p=1, arbitrary atoms including an atom at X=0, Q=0, W=0, v=0, and w=±x are all covered explicitly.
- The strict-survival complements are the intended weak-wall hits. No zero probability assertion about a bridge extremum at a wall is required.
- Only finite second moment is assumed on the original law. The cubic quantity is always truncated and is proved integrable.
- The argument never substitutes an either-crossing probability, a finite-window variation, an arbitrary replacement endpoint law, a conditional iid law, or a desired rare-zero estimate as an assumption.
- No circular target-equivalent lemma appears. The genuinely new pieces are the direct image/BV estimates, the Stieltjes transfer derivation, and the direct finite2 rare-zero payment.

## 10. Formal-interface plan and qualification boundary

The value plan in formal-interface-plan.md lines 8–18 is faithful: initialDoubleCompletion is the intersection of two strict-survival complements on the same BridgeNoise; initialDoubleObservable takes the exact value 1 at zero energy; brownianInitialDouble uses the two weak walls over BridgeTime. Its public result shape in lines 25–28 retains the actual Brownian bridge, whole-real-line variation, actual iid Measure.pi, normalizedEndpoint, closed terminal cutoff, variance-one finite2 assumptions, genuine integrability, and universal-constant order.

The plan correctly warns that its all-integer image notation still needs exact Lean reindexing/summability when implemented, and that the theorem declaration must be frozen before implementation. These are future formalization obligations, not a gap in the current mathematical series argument. The plan is not an elaborated frozen Lean declaration and receives no formal credit from this review.

There are no critical mathematical gaps or counterexamples for this frozen version. The mathematical proof is complete in the reviewed auxiliary scope. Original C2/C12 remain OPEN; no previously accepted proof or kernel receipt is re-awarded or replaced.

