# Complete changing-row small-boundary and closed-window proof

STATUS: PROVED_MATHEMATICAL_CANDIDATE_RELATIVE_TO_SEALED_D_MATHEMATICS; independent review and formal gates pending. The statement is exactly problem.md, assumptions.md and the exhaustive proposal. Original fixed-law v79 acceptance is unchanged; no new completion or novelty credit is asserted by this author verdict.

## 1. Exact objects and bearing inputs

Write N_j=nSeq j, ν_j=νSeq j and μ_j=Measure.pi(fun _ : Fin N_j => ν_j). Install hprob j for each finite call. The actual transparent shared values are

\[
\begin{split}
\mathrm{Path}(N)&=\mathrm{Fin}(N)\to\mathbb R,\\
S_k(v)&=\sum_{i\in\mathrm{univ.filter}(i.\mathrm{val}<k)}v_i,
\qquad Q(v)=\sum_{i\in\mathrm{Fin}(N)}v_i^2,\\
A_N(b)&=\{v:\forall k\in\mathbb N,\ k\le N\Rightarrow |S_k(v)|\le b\},\\
E(N,H)&=\{v:v\in A_N((H/\sqrt N)\sqrt{Q(v)})\},\\
m(N,H)&=(4/\pi)\exp[-(\pi^2/8)((N:\mathbb R)/H^2)],\\
g(x)&=(4/\pi)\exp[-(\pi^2/8)/x^2].
\end{split}\tag{1.1}
\]

These are respectively Shao.Path, prefixSum, energy, closedStrip, RandomDenominatorFarTail.randomDenominatorEvent, farMainTerm and BrownianSup.firstTerm. Natural numbers in real formulas are coerced to ℝ. Let λ=π²/8>0, G_j(b)=μ_j.real(A_Nj(b)), and use the following body-local notation only:

\[
T_j(x)=\{v:v\in A_{N_j}(x\sqrt{Q(v)})\},\quad
p_j(x)=\mu_j.\mathrm{real}(T_j(x)),\quad
R_j(x)=p_j(x)/F(x),\quad e_j(x)=|R_j(x)-1|.
\tag{1.2}
\]

Here F(x) is the **same actual Brownian CDF at every occurrence**, defined by
F(x)=P.real{ω : U B P hB ω≤x}, with U the existing measurable version of the Brownian path supremum. Its measurable-version convention is unchanged. The Brownian domain ΩB has independent universe uB; none of the following steps couples it with μ_j.

The exact bearing inputs are:

* **A, qualified moving positive-boundary ratio.** Under the written common-M row assumptions, N_j→∞ and x_j→c>0, RowPositiveBoundaryStudentized.varying_row_studentized_positive_boundary_ratio_tendsto gives p_j(x_j)/F(x_j)→1, for the literal event in (1.2). It requires no all-index positivity of x_j. Exact source/review/first-object qualification is reused, not reviewed or checked again.
* **K, qualified genuine changing-row strip theorem.** UnconditionalKernelAsymptotic.varying_row_closedStrip_relative_asymptotic takes the common-M row assumptions and all-index positive H_j, with H_j→∞, N_j/H_j²→∞, N_j/H_j³→0. It concludes G_j(H_j)/[(4/π)exp(−λ N_j/H_j²)]→1. This is an actual changing-row theorem; no fixed-law limit is used.
* **D, sealed complete mathematical random-denominator theorem.** RowRandomDenominatorAsymptotic.varying_row_randomDenominator_relative_closedStrip_tendsto, at the same row assumptions and three scale limits but only eventual scale signs derived internally, gives μ_j.real(E(N_j,H_j))/G_j(H_j)→1. D's complete source-bound mathematical packet is read and pinned. Its actual formal implementation/qualification remains pending; this proof is a mathematical consumer of that theorem rather than a claim that D is already kernel accepted.
* **Actual Brownian facts, qualified.** BrownianSup.actual_brownian_firstTerm says for every ε>0 there is δ>0 such that 0<x<δ implies |F(x)/g(x)−1|<ε. BrownianPositiveCDF.probability_pos gives F(x)>0 at every x>0, and probability_mono gives F nondecreasing. These actual producer types and g's full value are read; no abstract reference CDF is introduced.

The new C uniform-radius result is a predecessor of D. Its assigned exact first server pass/final-review-pending state is recorded in source-pins.json, together with reviewer248's subsequently observed CORRECT receipt and the then appeared exact lead qualification at that same source. These are new status observations at unchanged bytes; D formal qualification remains pending. C is not a new hypothesis of any public theorem here. Old center/middle/far finite proofs and their payment remain within the pinned D theorem and its source qualification boundary.

## 2. Exact scale identities on the derived positive tail

Fix an integer N>0 and real x>0. Set p=N^((1:ℝ)/6), q=xp and H=x√N. Since N>0, real power laws give p>0, p³=N^(3/6)=√N and

\[
\sqrt N=N^{1/2}=N^{1/6}N^{1/3}.
\tag{2.1}
\]

These real exponents are exactly (1:ℝ)/6, (1:ℝ)/3 and (1:ℝ)/2. The rpow multiplication and addition laws are invoked only at the positive base N; no rational equality is inferred from natural division or floating arithmetic. Therefore

\[
H=qN^{1/3},\quad H^2=x^2N,\quad
q^3=x^3\sqrt N,\quad H^3=Nq^3.
\tag{2.2}
\]

The last equality follows by expanding H³=x³(√N)³ and using (√N)²=N. All of N,x,p,q,H are positive. Cancel only these positive factors to obtain

\[
\boxed{N/H^2=1/x^2,\qquad N/H^3=1/q^3.}
\tag{2.3}
\]

Equations (2.1)–(2.3) prove private scale_identities, which records H=qN^(1/3) and both exact quotient identities. They do not require or assert an identity at N=0.

Now suppose the small-boundary hypotheses hold. N_j→∞ gives eventually N_j≥1; intersect this with x_j>0. Put q_j=x_j N_j^(1/6) and H_j=x_j√N_j. On that tail all identities above apply. N_j≥1 gives N_j^(1/3)≥1 and q_j>0, so H_j≥q_j. Since q_j→∞, H_j→∞ by eventual domination (one may also use N_j^(1/3)→∞). Because x_j→0 through positive values, 1/x_j→∞ and hence 1/x_j²→∞. By (2.3), N_j/H_j²→∞. Finally q_j→∞ gives q_j⁻¹→0, so 1/q_j³→0 and N_j/H_j³→0. This proves private small_boundary_scales with exactly the written hypotheses, retaining every finite early value of the sequences.

## 3. Strip main term without a new all-index height premise

For any H_j satisfying the three scale limits, H_j→∞ gives a tail with H_j>0. Define **inside this proof only**

\[
\widetilde H_j=\begin{cases}H_j,&0<H_j,\\1,&\text{otherwise}.\end{cases}
\tag{3.1}
\]

Then Htilde is positive at every index and agrees eventually with H. Every sequence limit involving Htilde is transported from the corresponding H sequence by eventual equality, including both real quotient scales. Apply the qualified K head of §1 at the original ν_j and N_j, using the same M. Its all-index positive-height premise is now satisfied, without adding one to our public target. K gives

\[
G_j(\widetilde H_j)/m(N_j,\widetilde H_j)\longrightarrow1.
\]

The written K exponential is −λN/H², and m uses −λ(N/H²). They are the same real expression by multiplication/division association, including at a zero denominator in the total real convention; this rewrite does not cancel H. Eventual Htilde=H transfers the limit to

\[
\boxed{G_j(H_j)/m(N_j,H_j)\longrightarrow1.}
\tag{3.2}
\]

This proves private varying_row_closedStrip_relative_main_tendsto. At every j the full value m(N_j,H_j) is positive, since 4/π>0 and exp is positive. Equation (3.2) gives eventually G_j(H_j)/m(N_j,H_j)>1/2, and hence G_j(H_j)>0. This is the positive actual strip denominator used below; no total division by an early zero probability is canceled.

## 4. Literal random event and exact Brownian main term

For N>0, √N>0. For every real x and every v∈Path(N),

\[
\frac{x\sqrt N}{\sqrt N}\sqrt{Q(v)}=x\sqrt{Q(v)}.
\tag{4.1}
\]

Only √N is canceled. Thus, as **equal sets**, including all weak prefix endpoints and Q=0,

\[
E(N,x\sqrt N)=\{v:v\in\mathrm{closedStrip}(x\sqrt{Q(v)})\}.
\tag{4.2}
\]

This is private actual_event_eq_randomDenominatorEvent (with the equality orientation written in the proposal). No sign premise on x is needed for (4.2). In particular it is not a statement about a random quotient. If Q=0 then every v_i=0 because a sum of nonnegative squares is zero, and all prefixes equal zero. The realized wall in either side of (4.2) is zero, so that atom remains in the event. We do not assert it has zero mass.

For N>0,x>0, insert (2.3) into the full value m to obtain the exact positive equality

\[
m(N,x\sqrt N)=g(x)>0.
\tag{4.3}
\]

This identity is proof-local, rather than an additional top-level helper. Its exponent is exactly −λ/x², not merely asymptotically equivalent or logarithmically close.

The actual Brownian epsilon-delta theorem in §1 immediately gives, if x_j→0 and eventually x_j>0,

\[
F(x_j)/g(x_j)\longrightarrow1.
\tag{4.4}
\]

Explicitly, for a prescribed ε>0 choose the theorem's δ>0. Then x_j→0 ensures eventually x_j<δ, and intersecting with x_j>0 gives the exact absolute error bound <ε. This proves private actual_firstTerm_ratio_tendsto. Independently, BrownianPositiveCDF.probability_pos gives F(x_j)>0 on the positive tail. The positivity is checked before canceling F; equation (4.4) is not used to conceal a zero CDF in total division.

## 5. Public small-boundary relative CDF limit

Under the public small-boundary hypotheses use §2 with H_j=x_j√N_j. Apply D at the **actual** laws ν_j and these H_j,N_j to get

\[
\mu_j.\mathrm{real}(E(N_j,H_j))/G_j(H_j)\longrightarrow1.
\tag{5.1}
\]

Apply (3.2) and (4.4) to the same sequences. On a common tail we have N_j>0,x_j>0,G_j(H_j)>0,m(N_j,H_j)>0 and F(x_j)>0. Equations (4.2)–(4.3) give the exact identity

\[
\frac{p_j(x_j)}{F(x_j)}
=\frac{\mu_j.\mathrm{real}(E(N_j,H_j))}{G_j(H_j)}
 \frac{G_j(H_j)}{m(N_j,H_j)}
 \left(\frac{F(x_j)}{g(x_j)}\right)^{-1}.
\tag{5.2}
\]

Every canceled factor has just been shown positive. By (5.1),(3.2),(4.4), the factors tend to 1,1,1 respectively; inversion is continuous at the nonzero limit 1. Their product tends to one, and eventual equality in (5.2) transfers the limit to the literal numerator. This is public varying_row_studentized_small_boundary_ratio_tendsto.

This proof neither substitutes the desired Brownian result as a premise of D nor adds a law-dependent rate. All common-M dependence has already been paid inside the genuine K and D theorem inputs. A possible atom at Q=0 and arbitrary finite-prefix behavior remain part of the actual probabilities.

## 6. Genuine bad-index and compact-radius extraction

We prove the private purely deterministic extraction head. Let e:ℕ→ℝ→ℝ, a:ℕ→ℝ, ε∈ℝ, suppose eventually a_j>0, and suppose frequently there exists x∈[a_j,1] with ε≤e_j(x). Intersect this frequent set with the eventual positivity tail. It remains frequent: an eventual set cannot remove a cofinal infinite subset of ℕ.

Choose a strictly increasing sequence m_k of such indices. To see the quantifier explicitly, choose m_0 from that frequent set; after m_k has been chosen, frequency gives a later index ≥m_k+1 in the same set, and choose it as m_(k+1). At each k choose an actual witness y_k∈[a_(m_k),1] with ε≤e_(m_k)(y_k). Since a_(m_k)>0, we have 0<y_k≤1. Thus all y_k lie in compact [0,1]. Sequential compactness supplies c∈[0,1] and a strictly increasing φ:ℕ→ℕ with y_(φ(k))→c. Define κ=m∘φ and x_k=y_(φ(k)). Then κ is strictly increasing and κ→∞, x_k→c, and for **every k**

\[
0<x_k,\qquad a_{\kappa(k)}\le x_k\le1,\qquad
\varepsilon\le e_{\kappa(k)}(x_k).
\tag{6.1}
\]

This is bad_closed_window_subsequence, including the full witness quantifiers. No original row-length sequence is made monotone; only a selected index map κ is strictly increasing. The extraction uses closed [a_j,1], so it retains x=a_j and x=1.

## 7. Public eventual uniform bound on the closed window

Fix ε>0 and suppose, for contradiction, that the public eventual-for-all-x conclusion fails. Negating it gives frequently j with an x∈[a_j,1] and ε≤e_j(x). Apply §6 with the actual error function in (1.2) and hapos. Obtain κ,x_k,c as above.

Reindex all row data, rather than freezing a row law:

\[
\nu'_k=\nu_{\kappa(k)},\quad N'_k=N_{\kappa(k)},\quad a'_k=a_{\kappa(k)}.
\tag{7.1}
\]

For every k the original hprob,h3,hmean,hsecond,hM at κ(k) give exactly the same assumptions for ν'_k, with the same real M. StrictMono κ gives κ→∞, hence N'_k→∞ by composition with hn. Likewise a'_k→0 and

\[
a'_k(N'_k)^{1/6}\longrightarrow\infty
\tag{7.2}
\]

by composing the original hslow with κ. The actual product measure for ν'_k,N'_k is literally μ_(κ(k)); no transport of samples or additional row law is involved.

There are two exhaustive possibilities, since c∈[0,1].

**If c=0:** every x_k>0, x_k→0, and from (6.1), nonnegativity of (N'_k)^(1/6), and (7.2),

\[
x_k(N'_k)^{1/6}\ge a'_k(N'_k)^{1/6}\longrightarrow\infty.
\tag{7.3}
\]

Apply public small-boundary theorem §5 to the complete reindexed row sequence and x_k. All its hypotheses have now been supplied, including eventual positivity (indeed every k) and the exact real-power growth. It gives R_(κ(k))(x_k)→1.

**If c>0:** use the qualified moving-positive-boundary theorem A from §1 with ν',N',x_k,c. The same row hypotheses and N'→∞ were verified above, and x_k→c>0 is the extracted limit. It gives the same R_(κ(k))(x_k)→1. The case c=1 is included without any x<1 premise.

In either case continuity of z↦|z−1| yields e_(κ(k))(x_k)→0. There is therefore a tail on which this error is <ε, contradicting ε≤e_(κ(k))(x_k) for every k in (6.1). The failure assumption is impossible. We have proved

\[
\boxed{\forall\varepsilon>0,\ \forall^{\mathrm{eventually}}j,\
 \forall x\in[a_j,1],\ |p_j(x)/F(x)-1|<\varepsilon.}
\tag{7.4}
\]

This is public varying_row_closed_window_eventually. Its order of quantifiers is exactly the one displayed: one eventual tail for **all** x at that row and the prescribed ε. The proof does not infer uniformity from a fixed-x limit; it creates genuinely bad radii when uniformity is negated, reindexes the laws/lengths along their actual cofinal indices, and then uses the appropriate moving-radius limit. No Antitone condition on a or monotonicity on N was used.

## 8. One transparent actual errors image and its genuine sSup

The full proposed value actualWindowErrors B P hB ν N a is

\[
\left(x\mapsto\left|
 \frac{(\mathrm{Measure.pi}(\_:\mathrm{Fin}(N)\mapsto\nu)).\mathrm{real}
    \{v:v\in\mathrm{closedStrip}(x\sqrt{Q(v)})\}}
 {\mathrm{BrownianSup.probability}(B,P,hB,x)}-1\right|\right)''[a,1].
\tag{8.1}
\]

Its full Lean value and every parameter/instance/universe are in the exhaustive proposal. It has no premise asserting any limit, boundedness or window property. In particular ν,N,a are finite arguments and may be instantiated by νSeq j,nSeq j,aSeq j with no fixed-law limit inference. sSup is taken inline in the theorem, so no second new value is needed.

We prove private actualWindowErrors_spec at an arbitrary finite ν probability, N∈ℕ and 0<a≤1. The existing actual finite path event is measurable: every prefix sum is continuous, Q is a nonnegative continuous polynomial, sqrt∘Q is continuous, each weak inequality is closed, and only the finite collection k=0,…,N is relevant. The μ finite-product probability therefore gives for every x

\[
0\le p(x)\le1.
\tag{8.2}
\]

The same bounds also follow directly from measure-real monotonicity against the whole space and finiteness, so no extra measurable-event premise is required in the head. At x≥a>0, qualified CDF positivity and monotonicity give 0<F(a)≤F(x). Thus

\[
0\le p(x)/F(x)\le1/F(a),\qquad
0\le|p(x)/F(x)-1|\le1+1/F(a).
\tag{8.3}
\]

For the first upper bound use p≤1 and the nonnegative reciprocal comparison for positive F(a)≤F(x). The second follows from |z−1|≤|z|+1=z+1 when z≥0. The bound is a finite real depending on this actual a, which is all finite-row boundedness requires.

The point x=a belongs to [a,1], so its error is a member of the image (8.1), proving nonemptiness. Equation (8.3) makes 1+1/F(a) an upper bound. Conditional completeness of ℝ now supplies IsLUB(image)(sSup image). Each image member is nonnegative, and one member exists, so le_csSup at that member gives 0≤sSup image. This proves every clause of private actualWindowErrors_spec: nonempty, BddAbove, IsLUB and nonnegative sSup. The argument permits N=0; no n>0 premise is hidden in the finite supremum lemma.

## 9. Public exact closed-window sSup tends to zero

From a_j→0 and eventual a_j>0 obtain one eventual tail with 0<a_j<1. (For example, use the neighborhood upper bound a_j<1 and intersect hapos.) On that tail specialize §8 to ν_j,N_j,a_j, obtaining an actual nonempty bounded errors image and a nonnegative real supremum S_j. This pays its mathematical meaning; no empty/unbounded-set sSup rule is used on that tail.

Given any ε>0, apply (7.4) with ε/2>0. On its tail every member of the actual errors image is <ε/2, hence is ≤ε/2. Intersect with the preceding geometry tail. The least-upper-bound property gives S_j≤ε/2, and S_j≥0 gives |S_j−0|=S_j<ε. This is exactly

\[
\boxed{\mathrm{sSup}(\mathrm{actualWindowErrors}(B,P,hB,\nu_j,N_j,a_j))\longrightarrow0.}
\tag{9.1}
\]

The public varying_row_closed_window_sSup_tendsto therefore concerns the exact absolute relative error, rather than a logarithm or free upper envelope. Early a>1 may make the image empty; early a≤0 may make CDF positivity unavailable; early N=0 is allowed. The public value is retained at every index, but the proof of its limit uses only the derived tail. No early-index correction, assumption, discarded atom or repeated old check is introduced.

## 10. Exhaustive proof plan, boundaries and qualification status

The seven private heads are scale_identities (§2), small_boundary_scales (§2), actual_event_eq_randomDenominatorEvent (§4), varying_row_closedStrip_relative_main_tendsto (§3), actual_firstTerm_ratio_tendsto (§4), bad_closed_window_subsequence (§6), and actualWindowErrors_spec (§8). The three public heads are the small-boundary limit (§5), closed-window eventual uniform statement (§7), and exact sSup limit (§9). There is exactly one new transparent non-theorem value, actualWindowErrors, completely given in §8 and the proposal. The complete prelude is listed in that proposal. Every other quantity in this proof, including positive-height patch (3.1), κ,φ and the reindexed laws, is body-local; no hidden helper API or unlisted top-level axiom/value is intended.

The finite weak strip includes k=0 and k=N. Equality x=a_j is included in the zero-limit branch, and equality x=1 in the positive branch; a singleton interval a_j=1 also satisfies the finite spec. N→∞ supplies the n>0 tail needed by (4.2), while the definition/spec itself retains N=0. Q=0 is never divided out and is included literally. All limiting row hypotheses transport along κ without law convergence. All canceled strip/main/CDF denominators are positive on the exact common tails. Real rpow identities are used only at positive natural casts. Original common-M K is patched only at finite nonpositive heights by an explicitly eventual-equal body-local sequence; the actual row laws and public target are unchanged.

This packet is a complete proposed mathematical consumer of sealed D mathematics and qualified A/K/Brownian producers. C's subsequent exact lead qualification is bound without proof/check replay; D's formal qualification is still an explicit outstanding predecessor gate, not a logical premise inserted into the public statements. Lead declaration freeze must precede implementation. After those gates, actual implementation still needs a fresh qualified complete final independent source-to-statement/proof/all-type/value review and exact-source server kernel/all-owned transitive-axiom receipt. This author runs none of those gates and cannot self-certify independent correctness. No old full proof re-review, native build, leaf axiom replay or remote object read was performed. No 124 unified mechanism is required.
