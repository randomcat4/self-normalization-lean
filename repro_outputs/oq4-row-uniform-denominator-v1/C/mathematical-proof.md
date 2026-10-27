# Complete mathematical proof of the varying-row radius consumer

STATUS: PROVED_MATHEMATICAL_CANDIDATE_PENDING_INDEPENDENT_REVIEW.

This is a mathematical proof of the exact three conclusions in problem.md and proposed-interface.lean.txt. It uses the complete mathematical L-row producer at its frozen interface, whose formal implementation/qualification is pending. It is not a new kernel receipt, an independent review verdict, a novelty claim or a whole-window completion claim.

## 1. Actual objects and the two bearing asymptotic producers

Put ν_j=νSeq j, n_j=n j and h_j=h j. All finite-row notation below is body-local. On `Shao.Path n_j = Fin n_j → ℝ`, put

\[
\pi_j=\operatorname{Measure.pi}(i\in\operatorname{Fin}(n_j)\mapsto\nu_j),
\quad Q(a)=\sum_i a_i^2,
\quad A_j(b)=\{a:\forall k\le n_j,\ |S_k(a)|\le b\}.
\tag{1.1}
\]

The zero prefix belongs to the monitored range. Write

\[
G_j(b)=\pi_j.\mathrm{real}(A_j(b)),\qquad
m_j(b)=\frac4\pi\exp\left(-\lambda\frac{n_j}{b^2}\right),
\quad\lambda=\frac{\pi^2}{8}.
\tag{1.2}
\]

The real value of the product measure is its actual probability because each row law is a probability. For every real b, including zero, m_j(b)>0 under real total division: 4/π>0 and exp is strictly positive. This observation does not justify canceling b itself when b=0; all such cancellations below are explicitly on the positive tail.

The actual energy integral is

\[
I_j(b,u)=\operatorname{energyJointIntegral}(\nu_j,n_j,b,u)
 =\int 1_{A_j(b)}(a)\exp\left(u\frac{Q(a)-n_j}{b^2}\right)d\pi_j(a).
\tag{1.3}
\]

Here the `if` expression in `energyPathIntegrand` is meant literally; it is zero outside the event. The existing full transparent J value is

\[
J_j(b,h,s)=\int 1_{A_j(b)}(a)
 \left[\frac{\exp(s(Q(a)-n_j)/h^2)+\exp(-s(Q(a)-n_j)/h^2)}2-1\right]d\pi_j(a).
\tag{1.4}
\]

Equation (1.4) is exactly `UniformConditionalEnergy.energyCoshExcessIntegral`, not a new value or a free conditional expectation.

Accepted K is `UnconditionalKernelAsymptotic.varying_row_closedStrip_relative_asymptotic`. Its exact public input is the row probability and moment hypotheses with one common M, a height sequence positive **at every index**, and the three scales. Its conclusion is G_j(b_j)/m_j(b_j)→1. Its current source SHA matches its qualified acceptance receipt. We do not rerun or re-review that old proof.

L-row has two frozen public heads in namespace `Shao.OQ4.RowEnergyLaplace`, frozen interface SHA256 `c0dd919b66763097709857a8a77adf8d8540a055c1215cd50f70e4d4b894c2d5`:

* `varying_row_closedStrip_probability_eventually_pos`: the same actual row hypotheses and three scales imply eventually G_j(b_j)>0, without an all-index height-sign premise.
* `varying_row_energy_laplace_ratio_tendsto`: for the same hypotheses, T≥0 and any real parameter sequence u with **∀j, |u_j|≤T**, I_j(b_j,u_j)/G_j(b_j)→1.

Its mathematical proof is the complete packet `row-energy-laplace-math-v1/proof.md`; its formal producer is not yet qualified. These are theorem dependencies with actual row inputs, not hypotheses added to any proposed consumer head. Consumer implementation is gated on the producer's actual qualification.

The reusable accepted finite public heads are `energyPathIntegrand_integrable`, `UniformConditionalEnergy.energyCoshExcessIntegral_nonneg` and `UniformConditionalEnergy.energy_deviation_finite_bound`. The last two are law-parametric finite results. None of the old fixed-law asymptotic heads is used as a changing-row limit.

## 2. Every selected admissible radius preserves the three scales

Let b:ℕ→ℝ satisfy eventually

\[
\frac{h_j}{2}\le b_j\le C h_j,\qquad C\ge1.
\tag{2.1}
\]

The given h_j→∞ implies eventually h_j>0. On the intersection with (2.1), b_j≥h_j/2>0. Since h_j/2→∞, the lower bound gives b_j→∞. In particular, eventually h_j>0 and b_j≥1.

Because C>0, squaring the nonnegative upper bound gives b_j²≤C²h_j². With n_j≥0 and positive denominators,

\[
\frac{n_j/h_j^2}{C^2}=\frac{n_j}{C^2h_j^2}
 \le\frac{n_j}{b_j^2}.
\tag{2.2}
\]

The left side tends to +∞ by the original long-scale assumption and C²>0. Thus n_j/b_j²→∞.

Cubing the positive lower bound gives h_j³≤8b_j³, so

\[
0\le\frac{n_j}{b_j^3}\le8\frac{n_j}{h_j^3}\longrightarrow0.
\tag{2.3}
\]

Squeezing proves n_j/b_j³→0. These estimates use no restriction at an early index and no assumption that ν_j is constant. They prove the first private proposed helper `selected_radius_scales`.

## 3. Accepted K on an internal positive-prefix repair

For the selected b from §2 define the body-local sequence

\[
\widehat b_j=\begin{cases}b_j,&0<b_j,\\1,&\text{otherwise}.\end{cases}
\tag{3.1}
\]

It is strictly positive for every j and eventually equals b_j. Hence all three scale limits from §2 transfer unchanged to \widehat b. Apply accepted row K to the original νSeq, its original common M, the original n, and \widehat b. Its all-index probability, integrability, moment and third-moment bound hypotheses are exactly the given ones; its all-index height-sign hypothesis now holds by (3.1). Transfer the conclusion back by eventual equality:

\[
\frac{G_j(b_j)}{m_j(b_j)}\longrightarrow1.
\tag{3.2}
\]

Taking absolute deviations gives |G_j(b_j)/m_j(b_j)−1|→0. Since m_j(b_j)>0, the same limit also proves eventual G_j(b_j)>0: eventually the quotient is >1/2 and multiplication by the positive main term gives strict positivity. L-row's positivity head can equivalently provide this positive denominator. No original row is patched or replaced.

## 4. An all-index bounded parameter sequence with the exact desired tail exponent

Fix s>0 and C≥1, and set the constant T=sC²>0. The selected b is admissible only eventually. To meet the literal all-index parameter bound in L-row, define

\[
H_j:\quad0<h_j\ \text{and}\ h_j/2\le b_j\le C h_j,
\qquad
u_j=\begin{cases}s(b_j/h_j)^2,&H_j,\\0,&\neg H_j.\end{cases}
\tag{4.1}
\]

At an index satisfying H_j, division by h_j>0 gives 1/2≤b_j/h_j≤C. Thus 0≤(b_j/h_j)²≤C², and consequently

\[
|u_j|=s(b_j/h_j)^2\le sC^2=T.
\tag{4.2}
\]

At every other index u_j=0 and |u_j|≤T. Therefore **∀j, |u_j|≤T**, and likewise **∀j, |−u_j|≤T**. Moreover H_j eventually holds by (2.1) and h_j→∞, so u_j=s(b_j/h_j)² on one tail. This patch changes neither public h,n,νSeq nor the desired eventual J.

Apply the exact frozen L-row ratio theorem twice, with wall sequence b and the parameter sequences u and −u. Section 2 discharges its scale hypotheses and (4.2) discharges its all-index parameter hypotheses. We obtain

\[
\frac{I_j(b_j,u_j)}{G_j(b_j)}\to1,
\qquad
\frac{I_j(b_j,-u_j)}{G_j(b_j)}\to1.
\tag{4.3}
\]

This is an application of the changing-row producer. Applying the old fixed-law Laplace result separately at each j would not justify either sequence limit and is not used.

## 5. Pay finite integrability before the literal integral identity

Restrict to one common tail where H_j holds, b_j≥1, h_j>0 and G_j(b_j)>0. Fix one such j and work entirely inside its own path space. Put μ=π_j, A=A_j(b_j), u=u_j and f_±=`energyPathIntegrand b_j (±u)`.

Install the given `IsProbabilityMeasure (νSeq j)` locally. The existing public finite theorem

    energyPathIntegrand_integrable (νSeq j) (n j) T (b j) (±u)
      (0≤T) (1≤b j) (|±u|≤T)

proves Integrable(f_+,μ) and Integrable(f_−,μ). Its assumptions require no exponential moment of the untruncated law and no uniform numeric envelope in j. Each finite integral is genuinely integrable before linearity is used.

A is measurable. One exact existing API derivation uses

    shiftedClosedSurvival_eq_closedStrip (n j) (b j) (0≤b j)
    measurableSet_shiftedClosedSurvival (n j) (b j) 0.

Because μ is a finite probability, its indicator i_A of the constant function 1 is integrable, and the ordinary indicator integral is ∫i_A dμ=μ.real(A)=G_j(b_j).

For every real q, on this positive tail ordinary field algebra gives

\[
u\frac q{b_j^2}=s\frac q{h_j^2},\qquad
(-u)\frac q{b_j^2}=-s\frac q{h_j^2}.
\tag{5.1}
\]

Indeed substitute u=s(b_j/h_j)²=s b_j²/h_j² and cancel b_j²≠0. Both h_j and b_j are nonzero here. Using q=Q(a)−n_j, the literal integrand in (1.4) therefore agrees pointwise with

\[
\frac{f_+(a)+f_-(a)}2-i_A(a).
\tag{5.2}
\]

If a∈A this is (5.1); if a∉A, all three terms and the J integrand are zero. Sums, scalar multiples and differences of the already integrable functions in (5.2) are integrable. This also proves integrability of the literal J integrand on the tail. Only now apply integral linearity to obtain the exact identity

\[
J_j(b_j,h_j,s)=\frac{I_j(b_j,u_j)+I_j(b_j,-u_j)}2-G_j(b_j).
\tag{5.3}
\]

No private theorem name from UniformConditionalEnergy is referenced. This short body-local finite algebra derives the required identity from accepted public finite integrability and the complete transparent definitions. It does not reprove old path transport or any layer cover.

Divide (5.3) only by the already positive G_j(b_j):

\[
\frac{J_j(b_j,h_j,s)}{G_j(b_j)}
 =\frac12\left(\frac{I_j(b_j,u_j)}{G_j(b_j)}+
                 \frac{I_j(b_j,-u_j)}{G_j(b_j)}\right)-1
 \longrightarrow0
\tag{5.4}
\]

by (4.3) and continuity of addition and scalar multiplication. The equality is eventual, which suffices to transfer the limit; its early values need not satisfy it. The public finite nonnegativity theorem, applied to the actual law at j, gives J_j(b_j,h_j,s)≥0 without additional premises. On the positive-denominator tail this proves J_j/G_j≥0. Equations (2.1)–(5.4) prove the second private proposed helper `selected_radius_energy_ratio_tendsto` with exactly the original row hypotheses and eventual selected-radius premise.

## 6. From every selected sequence to one tail for every radius

Fix C≥1, s>0 and δ>0. For each j and b define the body-local proposition

\[
P(j,b):\quad G_j(b)>0\ \land\
 |G_j(b)/m_j(b)-1|<\delta\ \land\
 0\le J_j(b,h_j,s)/G_j(b)\ \land\
 J_j(b,h_j,s)/G_j(b)<\delta.
\tag{6.1}
\]

For every sequence b satisfying eventual (2.1), §§2–3 prove the K error and positivity conclusions, and §§4–5 prove the energy limit and nonnegativity conclusions. Intersect their finitely many eventual sets. By the definition of convergence and δ>0 this gives

\[
\text{for every eventually admissible }b:\mathbb N\to\mathbb R,
\qquad \forall^{\mathrm{eventual}}j,\ P(j,b_j).
\tag{6.2}
\]

The passage to a uniform tail uses choice at **every bad index**, as follows. Let

\[
B_j:\Longleftrightarrow\exists b\in\mathbb R,
 \ h_j/2\le b\le C h_j\ \land\ \neg P(j,b).
\]

Using classical choice define β_j to be one such bad radius if B_j holds and to be h_j otherwise. On the tail h_j>0, if B_j holds the chosen radius is admissible by its choice specification. If B_j does not hold, the fallback h_j is admissible because h_j/2≤h_j and h_j≤C h_j. Thus β is eventually admissible. Equation (6.2) supplies a tail where P(j,β_j) holds.

At any index in this last tail, a purported admissible b with ¬P(j,b) makes B_j true. By the **same** definition and choice specification of β_j, ¬P(j,β_j) follows, contradicting P(j,β_j). Hence at every such index every admissible real b satisfies P(j,b). This proves

\[
\forall^{\mathrm{eventual}}j,\ \forall b\in[h_j/2,C h_j],\ P(j,b),
\tag{6.3}
\]

the first proposed public head. It is stronger than a statement about any one fixed b or one fixed ratio b/h_j. No compactness, supremum attainment or unjustified exchange of quantifiers is used. The internal choice has no measurable-selection requirement because its domain is the deterministic sequence index, not a random path.

## 7. Simultaneous boundary ratios and the factor four

Apply §6 with s=1 and δ=1/2, keeping the specified C. Restrict further to h_j>0. The radius h_j itself is admissible because C≥1. Thus on one tail, simultaneously for every admissible b,

\[
G_j(h_j)>0,\quad G_j(b)>0,\quad
\left|\frac{G_j(b)}{m_j(b)}-1\right|<\frac12,
\quad
\left|\frac{G_j(h_j)}{m_j(h_j)}-1\right|<\frac12.
\tag{7.1}
\]

The upper half of the first error gives G_j(b)/m_j(b)<3/2≤2, and the lower half of the second gives 1/2<G_j(h_j)/m_j(h_j). Since both main terms are positive, we may weaken these to

\[
G_j(b)\le2m_j(b),\qquad m_j(h_j)\le2G_j(h_j).
\tag{7.2}
\]

Let E=exp(λ(n_j/h_j²−n_j/b²))>0. Exact exponential addition gives

\[
m_j(b)=E\,m_j(h_j),
\tag{7.3}
\]

since λ(n_j/h_j²−n_j/b²)−λn_j/h_j²=−λn_j/b² and the factor 4/π is the same. Multiplying the second inequality in (7.2) by 2E≥0 and using the first yields G_j(b)≤4E G_j(h_j). Divide by the positive G_j(h_j):

\[
\boxed{\frac{G_j(b)}{G_j(h_j)}\le
4\exp\left(\lambda\left(\frac{n_j}{h_j^2}-\frac{n_j}{b^2}\right)\right).}
\tag{7.4}
\]

This is the second proposed public head, including both denominator and numerator positivity. The factor four comes from simultaneous relative K controls for the actual probabilities; no unproved boundary comparison is assumed.

## 8. Uniform energy-deviation concentration at the original h² scale

Fix C≥1, ε>0 and δ>0. Define the positive scalar

\[
D=\frac{e^\varepsilon+e^{-\varepsilon}}2-1>0.
\tag{8.1}
\]

Strict positivity can be read from the first conjunct of the accepted finite `energy_deviation_finite_bound` at s=1, or proved directly: e^ε>1+ε because ε≠0, while e^{-ε}≥1−ε, so their sum is >2. Thus δD>0.

Apply §6 with s=1 and tolerance δD. On a common tail including h_j>0, every admissible b has b≥h_j/2>0 and G_j(b)>0, and

\[
\frac{J_j(b,h_j,1)}{G_j(b)}<\delta D.
\tag{8.2}
\]

For this exact finite actual law ν_j, install its given probability instance and apply the existing finite theorem with n=n_j, wall b, reference height h_j, s=1 and ε. Every hypothesis is now paid: b>0, h_j>0, 1>0 and ε>0. With

\[
R_j(b)=\pi_j.\mathrm{real}\left(A_j(b)\cap
 \{a:\varepsilon h_j^2<|Q(a)-n_j|\}\right),
\tag{8.3}
\]

its second conjunct is exactly D R_j(b)≤J_j(b,h_j,1). Dividing by G_j(b)>0 and using (8.2) gives

\[
D\frac{R_j(b)}{G_j(b)}\le\frac{J_j(b,h_j,1)}{G_j(b)}<\delta D.
\tag{8.4}
\]

Since D>0, cancellation proves R_j(b)/G_j(b)<δ. Nonnegativity follows from `.real` of a measure and G_j(b)>0. These inequalities hold for every admissible b on the same tail supplied by §6. Therefore

\[
\boxed{\forall^{\mathrm{eventual}}j,\ \forall b\in[h_j/2,C h_j],\quad
G_j(b)>0,\quad0\le R_j(b)/G_j(b)<\delta.}
\tag{8.5}
\]

This is the third proposed public head. The event in (8.3) uses εh_j²; at no point is that threshold replaced by εb² or εn_j.

## 9. Degenerate cases, endpoints and quantifier audit

1. Early h_j≤0, including h_j=0, are allowed. Their radius classes can be empty; no claim of an early positive denominator is made. Every denominator cancellation, sign-sensitive power comparison and finite integrability call occurs after h_j>0 and b_j≥1, or after b>0 for the finite deviation theorem.
2. Early n_j=0 are allowed. The actual empty product and zero-prefix strip are never replaced with a different event. None of the finite heads used here assumes n>0. The asymptotic long-scale assumption supplies all eventual growth needed by the producers.
3. C=1 is included. The fallback h_j remains admissible, T=sC²=s>0, and all comparisons stay valid. There is no division by C−1 or a strict upper-radius requirement.
4. No symmetry of ν_j is used. The two signs of the energy parameter are supplied separately by the literal L-row theorem, then averaged through an integrable identity.
5. There is no law convergence premise or cross-row path identification. Each finite identity and Markov inequality concerns one ν_j and one Fin(n_j). Sequence limits are obtained by the common-M varying-row producers.
6. The absolute third-moment bound implies M≥0 because each third-moment integral is nonnegative and the index set contains 0, although the proof does not need a new public premise stating this. Lower-moment integrability required inside L-row is discharged by its complete producer proof, not added to the consumer heads.
7. The parameter patch (4.1) supplies an all-index bound. Merely asserting that s(b_j/h_j)² is eventually bounded would not satisfy the frozen L-row type. It is not left as an implicit finite-prefix convention.
8. The bad-radius selector chooses at every bad index and has a valid fallback on the positive tail. It proves the exact eventual-for-all quantifier. A collection of fixed-radius pointwise limits would be insufficient.
9. The J identity is used only after actual integrability of both finite Laplace integrands and the event indicator. The proof never treats the default value of a nonintegrable Bochner integral as an expectation.
10. All walls remain literal weak ≤ walls, and the energy deviation remains strict >. No atom at a wall or at Q=0 is discarded. The Q=0 path is not divided by Q, and no normalized random path ratio appears in this unit.
11. No old finite layer-cover or far-tail proof is repeated. The old private finite identities and fixed-law asymptotic heads are source guidance, while their reusable public finite facts are used at their exact generic scope.

## 10. Exact proposed source inventory and remaining downstream work

The proposal contains three public theorem heads: `varying_row_uniform_closedStrip_energy_controls`, `varying_row_uniform_closedStrip_boundary_ratio_bound`, and `varying_row_uniform_energy_concentration`. They are in the new namespace `Shao.OQ4.RowUniformConditionalEnergy` and display νSeq, hprob, h3, hmean, hsecond, M and hM explicitly. The two private bearing heads are `selected_radius_scales` (§2) and `selected_radius_energy_ratio_tendsto` (§§4–5). All other functions, patches, propositions, indicators, finite identities and choices in this proof are body-local. There are zero new non-theorem values, aliases, instances, structures, notation or universe declarations.

After actual L-row qualification and lead freeze, implementation must preserve these complete headers or return a proposed interface change to the lead. One qualified fresh final independent complete source-to-statement/proof review and exact new-source server kernel/all-owned transitive-axiom receipt remain necessary. Nothing here asserts those checks have run.

The next genuine mathematical dependency is the changing-row assembly of the already accepted finite `middle_finite_bound`, the centerHeight comparison and center error bounds, and `far_tail_bound`, followed by their literal random-denominator/strip ratio squeeze. The present three heads supply the common-radius G, K, J/G, boundary-ratio and original-h² concentration inputs to those finite center/middle consumers. Far-tail common-M payment and the final random-denominator/window assembly are not conclusions of this packet. Original fixed-law v79 scope remains retained and the broader row window remains OPEN.
