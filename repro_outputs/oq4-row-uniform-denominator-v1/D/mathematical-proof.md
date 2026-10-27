# Complete changing-row random-denominator proof

STATUS: PROVED_MATHEMATICAL_CANDIDATE_PENDING_INDEPENDENT_REVIEW_AND_FORMAL_GATES.

The statement is exactly problem.md and the ten complete proposed heads. The new uniform-radius mathematical theorem is used at its original assumptions and complete proposal, with formal qualification explicitly pending. This author verdict is not an independent review or a machine result. Original fixed-law v79 remains retained; the broader row window remains OPEN.

## 1. Actual finite objects, with unchanged full values

For the entire proof write ν_j=νSeq j, N_j=n j, H_j=h j, and

\[
\mu_j=\operatorname{Measure.pi}(i\in\operatorname{Fin}(N_j)\mapsto\nu_j),
\quad Q(a)=\sum_{i\in\operatorname{Fin}(N_j)}a_i^2,
\quad S_k(a)=\sum_{i:i.\mathrm{val}<k}a_i.
\tag{1.1}
\]

`Shao.Path N` is exactly `Fin N → ℝ`. Its `prefixSum` is the sum over `Finset.univ.filter (fun i : Fin N => i.val < k)` and `energy` is exactly `∑ i, (a i)^2`. Set

\[
A_j(b)=\{a:\forall k\in\mathbb N,\ k\le N_j\Rightarrow|S_k(a)|\le b\},
\quad G_j(b)=\mu_j.\mathrm{real}(A_j(b)).
\tag{1.2}
\]

This is the literal shared `closedStrip`. For every j, install the supplied instance hprob j inside its finite calls. Then μ_j is a probability, and `.real` is its actual finite probability. There is no cross-row identification of paths or measures. Define only body-local scalar sequences

\[
t_j=N_j/H_j^2,\quad r_j=N_j/H_j^3,\quad
\lambda=\pi^2/8>0,\quad m_j(b)=(4/\pi)e^{-\lambda N_j/b^2}>0.
\tag{1.3}
\]

The `farMainTerm N b` value is `(4 / Real.pi) * Real.exp (-(Real.pi ^ 2 / 8) * ((N : ℝ) / b ^ 2))`; thus it agrees identically with m_j(b). The relative-error denominator in the row-uniform proposal is `(4 / Real.pi) * Real.exp (-lambda * (N : ℝ) / b ^ 2)`, the same value by field association, without canceling b. Its positivity follows from π>0 and exp>0 even at an early zero height under total real division.

Here are all the remaining existing transparent values used in the argument. They are consumed unchanged; these lines define notation for reading, not new source declarations:

\[
\begin{aligned}
E(N,H)&=\{a:a\in\operatorname{closedStrip}((H/\sqrt N)\sqrt{Q(a)})\},\\
c(N,H,d)&=H\sqrt{1+d/((N:\mathbb R)/H^2)},\\
I(N,H,\varepsilon)&=\operatorname{Finset.Icc}\bigl(1,\operatorname{Nat.ceil}(((N:\mathbb R)/H^2)/\varepsilon)\bigr),\\
b(N,H,\varepsilon,k)&=c(N,H,((k:\mathbb R)+1)\varepsilon),\\
L(N,H,\varepsilon,k)&=E(N,H)\cap
 \{a:N+k\varepsilon H^2<Q(a)\ \land\ Q(a)\le N+(k+1)\varepsilon H^2\},\\
T(N,H,\varepsilon)&=E(N,H)\cap\{a:N+\varepsilon H^2<Q(a)\ \land\ Q(a)<2N\},\\
B(s,\varepsilon)&=\frac{8e^{\lambda\varepsilon}e^{-(s-\lambda)\varepsilon}}
 {(1-e^{-s\varepsilon})^2(1-e^{-(s-\lambda)\varepsilon})}.
\end{aligned}
\tag{1.4}
\]

The code names in order are `randomDenominatorEvent`, `centerHeight`, `middleIndices`, `middleHeight`, `middleLayer`, `middleEvent`, `middleSumConstant`. All natural values in real formulas are coerced to ℝ. The full existing energy value is

\[
J_j(b,H,s)=\int_{\mathrm{Path}(N_j)}
\begin{cases}
\dfrac{e^{s(Q(a)-N_j)/H^2}+e^{-(s(Q(a)-N_j)/H^2)}}2-1,&a\in A_j(b),\\
0,&a\notin A_j(b)
\end{cases}d\mu_j(a).
\tag{1.5}
\]

This is `UniformConditionalEnergy.energyCoshExcessIntegral (νSeq j) (n j) b H s`, not an arbitrary conditional moment. Finally, the existing far values are

\[
\begin{aligned}
\operatorname{farLayer}(N,H,k)&=E(N,H)\cap\{a:2^kN\le Q(a)\ \land\ Q(a)<2^{k+1}N\},\\
\operatorname{farHeight}(H,k)&=\sqrt{2^{k+1}}\,H,\\
D_s=\operatorname{farDifferenceConstant}(s)&=e^{4s}s,\\
C_s=\operatorname{energyNormalizerErrorConstant}(s)&=1/8+s/2+e^{4s}s^2,\\
\operatorname{farScalarBound}(s,\beta,N,H)
 &=D_s(N/H^2)\exp[-s(N/H^2)/4+C_s\beta(N/H^3)/8].
\end{aligned}
\tag{1.6}
\]

The full truncated normalizer retained by the accepted finite proof is

\[
\operatorname{energyWeight}(H,s,x)=
 \begin{cases}e^{s x^2/H^2},&|x|\le2H,\\0,&\text{otherwise},\end{cases}
\quad Z_\nu(H,s)=\int\operatorname{energyWeight}(H,s,x)d\nu(x).
\tag{1.7}
\]

Its actual code name is `energyNormalizer`. It appears here to state exactly which already paid far mechanism is reused in §8; the consumer makes no new call needing an exponential moment of the untruncated law.

## 2. Bearing predecessor and exact finite inputs

Author244's complete mathematical proposal has precisely three public heads in `Shao.OQ4.RowUniformConditionalEnergy`. With the row hypotheses and three scale limits of assumptions.md, they yield, for fixed C≥1:

* Given s>0 and δ>0, on one tail, **for every real b∈[H_j/2,CH_j]**, G_j(b)>0, |G_j(b)/m_j(b)−1|<δ, and 0≤J_j(b,H_j,s)/G_j(b)<δ.
* On one tail G_j(H_j)>0 and, simultaneously for every such b, G_j(b)>0 and G_j(b)/G_j(H_j)≤4exp[λ(t_j−N_j/b²)].
* Given ε>0 and δ>0, on one tail for every such b, G_j(b)>0 and
  \[
  0\le\frac{\mu_j.\mathrm{real}(A_j(b)\cap\{\varepsilon H_j^2<|Q-N_j|\})}{G_j(b)}<\delta.
  \tag{2.1}
  \]

The last event uses the **original H_j²**. These are theorem dependencies, not new premises in the proposed consumer. The complete selected-radius/choice argument and bounded-parameter L-row proof beneath them are in the pinned predecessor packets. Their new formal qualification gates remain pending. Accepted common-M row K underlies that packet and is reused at its exact existing source/evidence. No fixed-law theorem supplies a varying-row Tendsto here.

The already qualified generic finite inputs in `RandomDenominatorAsymptotic` are consumed with the actual ν_j at each j:

* `center_lower_probability_bound`: if N>0,H>0,ε>0,2ε≤N/H², then
  \[
  G(c(N,H,-\varepsilon))-
  \mu.\mathrm{real}(A(c(N,H,-\varepsilon))\cap\{\varepsilon H^2<|Q-N|\})
  \le\mu.\mathrm{real}(E(N,H)).
  \tag{2.2}
  \]
* `randomDenominator_probability_upper_bound`, at exactly those hypotheses:
  \[
  \mu.\mathrm{real}(E(N,H))\le
  G(c(N,H,\varepsilon))+\mu.\mathrm{real}(T(N,H,\varepsilon))+
  \mu.\mathrm{real}(E(N,H)\cap\{2N\le Q\}).
  \tag{2.3}
  \]
* `middleHeight_geometry`: if N>0,H>0,ε>0,ε≤N/H² and k∈I(N,H,ε), then
  \[
  H\le b_k\le2H,\quad b_k^2=H^2(1+(k+1)\varepsilon/(N/H^2)),\quad
  N/H^2-N/b_k^2\le(k+1)\varepsilon.
  \tag{2.4}
  \]
* `middle_finite_bound`: for s>λ,η≥0 at the preceding finite hypotheses, G(H)>0 and **for all k∈I(N,H,ε)** the three conditions
  \[
  G(b_k)>0,\quad J(b_k,H,s)/G(b_k)\le\eta,\quad
  G(b_k)/G(H)\le4e^{\lambda(k+1)\varepsilon}
  \tag{2.5}
  \]
  imply μ.real(T(N,H,ε))/G(H)≤η B(s,ε). The qualified `middleSumConstant_pos` says B(s,ε)>0 for s>λ,ε>0.

The finite cover, exact weak inclusions, Markov bounds and geometric payment beneath these inputs are already qualified. The consumer does not prove a new layer cover. Section 7 spells out all their actual hypotheses and growing-index quantifiers.

The accepted finite `RandomDenominatorFarTail.far_tail_bound` requires N>0,H≥1,s>0, log2≤s(N/H²)/2, Integrable x², Integrable |x|³ and ∫x²=1 under an actual probability law. It yields

\[
\mu.\mathrm{real}(E(N,H)\cap\{2N\le Q\})
\le\operatorname{farScalarBound}\left(s,\int|x|^3d\nu,N,H\right).
\tag{2.6}
\]

It requires neither centering nor K. Its old fixed-law asymptotic head is not used; the new common-M limit is proved in §§8–9.

## 3. Derive every finite tail and the missing lower-moment integrability

First fix a probability law ν with Integrable |x|³. The nonnegative function 1+|x|³ is integrable because ν is finite. For every real x, let u=|x|≥0. If u≤1 then u≤1 and u²≤1, so u,u²≤1+u³. If u≥1 then u≤u³ and u²≤u³, so again u,u²≤1+u³. Since x and x² are measurable and their absolute values are u and u², integrable domination proves Integrable x and Integrable x². This proves proposed private `lower_moments_integrable` without adding a premise. Applying it separately to each ν_j supplies (2.6)'s square integrability.

For every fixed ε>0, h→∞ and t→∞ supply one tail with H_j>0 and t_j≥2ε. If N_j=0 there, then t_j=0 under real total division, contradicting t_j≥2ε>0. Thus N_j>0. This proves proposed private `eventual_finite_conditions`. For any other fixed scalar lower threshold R, t→∞ similarly supplies t_j≥R. In particular H_j≥1, N_j>0 and log2≤s t_j/2 all hold eventually for each fixed s>0: take t_j≥max(1,2log2/s). No all-index sign/positivity hypothesis has been introduced.

The actual β_j=∫|x|³dν_j is nonnegative by nonnegative integrand and finite by h3. Since the index set contains j=0, hM 0 proves M≥β_0≥0. On the tail H_j>0, also r_j≥0. These are derived facts used only where required.

## 4. Actual strip main limit and signed center geometry

Apply the first predecessor head of §2 with C=1,s=1 and arbitrary δ>0. On its tail intersect H_j>0. The radius b=H_j is admissible because H_j/2≤H_j≤H_j. It gives |G_j(H_j)/m_j(H_j)−1|<δ. This is exactly

\[
G_j(H_j)/m_j(H_j)\longrightarrow1,
\tag{4.1}
\]

proposed private `closedStrip_relative_main_tendsto`. The boundary head with C=1 or C=2 also supplies G_j(H_j)>0 eventually. m_j(H_j)>0 already holds at every index.

Fix any real d. Write c_j=c(N_j,H_j,d). On a tail take H_j>0 and t_j≥max(1,2|d|). Then t_j>0 and N_j>0. Put u_j=1+d/t_j. From |d|/t_j≤1/2,

\[
1/2\le u_j\le3/2,
\quad c_j=H_j\sqrt{u_j}>0,
\quad c_j^2=H_j^2u_j.
\tag{4.2}
\]

The square identity follows only after u_j≥0 is established. Both sides of every comparison below are nonnegative. The lower square bound c_j²≥H_j²/2≥(H_j/2)² gives c_j≥H_j/2. The upper bound c_j²≤3H_j²/2≤(2H_j)² gives c_j≤2H_j. Thus c is eventually in the exact common radius interval.

With all denominators in this calculation positive, field algebra gives

\[
\frac{N_j}{c_j^2}-t_j
 =\frac{t_j}{1+d/t_j}-t_j
 =\frac{-d}{1+d/t_j}.
\tag{4.3}
\]

Because t_j→∞, d/t_j→0, so the right side tends to −d. Equation (4.3) is asserted only on the derived tail; eventual equality transfers its limit to the total sequence at earlier indices. Equations (4.2)–(4.3) prove the complete proposed private `centerHeight_tail_geometry`, including the signed exponent difference. A height-ratio limit alone would not determine the required exponential ratio and is not substituted for (4.3).

## 5. Public center probability ratio for every real d

For any sequence b_j eventually in [H_j/2,2H_j], the first predecessor head with C=2,s=1,arbitrary δ>0 gives, by restriction to that sequence,

\[
q_j(b_j):=G_j(b_j)/m_j(b_j)\longrightarrow1.
\tag{5.1}
\]

The tail in that theorem quantifies over every admissible b; no pointwise-to-uniform inference is made here. Apply (5.1) to c_j from §4 and to H_j. By (4.3),

\[
e_j:=\exp\{\lambda(t_j-N_j/c_j^2)\}\longrightarrow e^{\lambda d}.
\tag{5.2}
\]

Exact exponential addition, using the full value (1.3), gives at every j

\[
m_j(c_j)=e_jm_j(H_j).
\tag{5.3}
\]

No cancellation of c_j or H_j is needed for this identity: the total real quotients are simply real numbers in the exponent. On the tail G_j(H_j)>0, both main terms and e_j are strictly positive, and (5.3) permits

\[
\frac{G_j(c_j)}{G_j(H_j)}
 =\frac{q_j(c_j)}{q_j(H_j)}e_j.
\tag{5.4}
\]

The denominator limit q_j(H_j)→1 is nonzero. Ordinary quotient/product convergence in (5.1)–(5.2), followed by the eventual identity (5.4), yields

\[
\boxed{G_j(c(N_j,H_j,d))/G_j(H_j)\longrightarrow e^{\lambda d}.}
\tag{5.5}
\]

This is public `varying_row_center_probability_ratio_tendsto`. It covers d=0 and both signs without any all-index radicand or wall-sign premise.

## 6. Lower-center bad energy is negligible relative to the original strip

Fix ε>0 and c_j=c(N_j,H_j,−ε), and write

\[
R_j=\mu_j.\mathrm{real}(A_j(c_j)\cap\{\varepsilon H_j^2<|Q-N_j|\}).
\tag{6.1}
\]

The predecessor concentration head (2.1), with C=2 and arbitrary δ>0, applies to c_j on the common tail from §4. It gives G_j(c_j)>0 and 0≤R_j/G_j(c_j)<δ. Hence R_j/G_j(c_j)→0. This concentration is exactly the already proved consequence of the uniform **actual J_j(c_j,H_j,1)/G_j(c_j)** bound at the original H_j² scale; no different energy normalization or desired conditional law is assumed.

Equation (5.5) with d=−ε gives G_j(c_j)/G_j(H_j)→e^{−λε}, a finite positive limit, and therefore this center ratio is bounded on a tail. Multiplying the two convergent sequences yields zero. On the tail G_j(c_j)>0 and G_j(H_j)>0,

\[
\frac{R_j}{G_j(c_j)}\frac{G_j(c_j)}{G_j(H_j)}=\frac{R_j}{G_j(H_j)}.
\tag{6.2}
\]

Thus R_j/G_j(H_j)→0, exactly proposed private `center_deviation_relative_tendsto_zero`. The lower center's strict deviation in (6.1) matches (2.2); no boundary atom is discarded by replacing it with a non-strict or one-sided event.

## 7. Public whole-middle limit: one tail pays the complete growing finite set

Fix ε>0 and choose the body-local s=λ+1. Then s>λ>0 and the accepted scalar B=B(s,ε)>0 is a fixed finite real. Let τ>0 be arbitrary and set η=τ/(B+1)>0. The predecessor energy controls with C=2,s and tolerance η yield one tail for every b∈[H_j/2,2H_j]. Its boundary-ratio head with C=2 gives a second such common tail, including G_j(H_j)>0. Intersect these with §3's finite tail for this ε.

Fix any j in that intersection, and then any k in the **literal entire** set

\[
I_j=\operatorname{Finset.Icc}(1,\operatorname{Nat.ceil}(t_j/\varepsilon)).
\tag{7.1}
\]

By the accepted `middleHeight_geometry` at N_j,H_j,ε,k, all its hypotheses hold: N_j>0,H_j>0,ε>0,ε≤t_j and k∈I_j. For b_k=middleHeight(N_j,H_j,ε,k), it yields H_j≤b_k≤2H_j and

\[
t_j-N_j/b_k^2\le(k+1)\varepsilon.
\tag{7.2}
\]

In particular H_j/2≤b_k. The same one-tail energy control, now specialized to this actual b_k, gives

\[
G_j(b_k)>0,\qquad J_j(b_k,H_j,s)/G_j(b_k)<\eta.
\tag{7.3}
\]

The same one-tail boundary estimate and (7.2), multiplied by λ>0 and passed through the increasing exponential, give

\[
G_j(b_k)/G_j(H_j)
 \le4e^{\lambda(t_j-N_j/b_k^2)}
 \le4e^{\lambda(k+1)\varepsilon}.
\tag{7.4}
\]

Because k was arbitrary in I_j, (7.3)–(7.4) establish **all** the local controls (2.5), simultaneously, after weakening `<η` to `≤η`. The remaining finite hypotheses are paid: η≥0, s>λ, ε>0,H_j>0,N_j>0,ε≤t_j and G_j(H_j)>0. Install hprob j and call the accepted `middle_finite_bound` for the actual ν_j. It yields

\[
0\le\frac{\mu_j.\mathrm{real}(T(N_j,H_j,\varepsilon))}{G_j(H_j)}
 \le\eta B=\frac{\tau B}{B+1}<\tau.
\tag{7.5}
\]

Nonnegativity uses only measure-real nonnegativity and the positive denominator. Since τ>0 was arbitrary, (7.5) proves public `varying_row_middle_relative_tendsto_zero`.

No rate of convergence has been imposed on η_j: η is a freely chosen **fixed tolerance after B is fixed**, and the common-radius theorem supplies its tail. The number of indices in I_j may grow arbitrarily. There is no application of a pointwise-in-k convergence statement to a growing set. In particular the enlarged I_j includes its harmless endpoint/overshoot indices, and no extra guard kε<t_j is inserted into the old geometry or finite bound.

The finite producer's cover is exactly T⊆⋃_{k∈I_j}L_k with L_k strict at its left energy endpoint and closed at its right endpoint. At an integer energy index the previous layer owns that endpoint. Q=N_j+εH_j² belongs to the center part, while Q=2N_j belongs to FAR. Last-layer overshoot remains covered by (2.4) for every I_j index. These facts are reused from the exact qualified finite cover and do not require a new or infinite middle decomposition.

## 8. Common-M FAR: reuse the actual finite bound without dropping its payment

Fix s>4λ for this derivation; the public far proof chooses s=4λ+1 internally. Then s>0, D_s=e^{4s}s>0 and C_s=1/8+s/2+e^{4s}s²≥0. By §3, eventually N_j>0,H_j≥1,log2≤s t_j/2, and each actual ν_j satisfies the finite square and cube integrability hypotheses with second moment one. Therefore the exact finite FAR theorem (2.6) applies at every j on this tail. Put

\[
F_j=\mu_j.\mathrm{real}(E(N_j,H_j)\cap\{2N_j\le Q\}).
\tag{8.1}
\]

It yields, with the **actual** β_j,

\[
0\le F_j\le D_s t_j
 \exp[-s t_j/4+C_s\beta_j r_j/8]
 \le D_s t_j\exp[-s t_j/4+C_s M r_j/8].
\tag{8.2}
\]

For the last inequality β_j≤M is supplied by hM, C_s≥0 and r_j≥0 on H_j>0, and D_s t_j≥0. Thus the exponent comparison, exponential monotonicity and multiplication by the nonnegative prefactor are all legitimate. No varying β_j is treated as a fixed constant in a limit.

The old finite payment retained by (8.2) is specifically the following qualified mechanism. For k≥1 the actual FAR layer is the closed/open band `farLayer N H k`; its wall is `farHeight H k=√(2^(k+1))H`. The accepted cutoff Markov difference has numerator

\[
Z_{\nu_j}(\operatorname{farHeight}(H_j,k),s)^{N_j}
-Z_{\nu_j}(\operatorname{farHeight}(H_j,k),0)^{N_j},
\tag{8.3}
\]

and denominator exp(s·2^kN_j/farHeight²)−1. The numerator is the integral of the cutoff-box indicator times exp(sQ/farHeight²)−1. Both terms retain the truncation |X_i|≤2farHeight. The qualified finite scalar estimate pays that difference by a factor N_j/farHeight² and yields the exact layer bound

\[
\mu_j.\mathrm{real}(\operatorname{farLayer}(N_j,H_j,k))
 \le \frac{2\operatorname{farScalarBound}(s,\beta_j,N_j,H_j)}{2^{k+1}}.
\tag{8.4}
\]

Its dyadic cover includes Q=2N_j and all arbitrarily large Q. Its summation is over k=ℓ+1, ℓ≥0, and

\[
\sum_{\ell\ge0}\frac{2B}{2^{\ell+2}}=B.
\tag{8.5}
\]

That is precisely how (2.6) is already proved and qualified. The present consumer calls that theorem; it neither repeats nor changes this proof. In particular it does not replace (8.3) by Z(s)^N, remove the cutoff, use an unweighted infinite cover or sum a constant error over infinitely many layers. The 2^(−k) payment is still present in (2.6), and is the reason the entire F_j, rather than a truncated part, is bounded by (8.2).

## 9. Public FAR relative limit, with a complete scalar decay proof

Set δ=s/4−λ>0, c=C_s M/8≥0 and a=D_sπ/4>0. By the full values of `farMainTerm` and `farScalarBound`, exact exponential addition gives on the same tail

\[
\frac{D_s t_j\exp(-s t_j/4+C_s M r_j/8)}{m_j(H_j)}
 =a\,[t_j e^{-\delta t_j}]\,e^{c r_j}.
\tag{9.1}
\]

Only π and exp are canceled here; both are nonzero. We now give the complete scalar fact used in proposed private `time_mul_exp_neg_tendsto`: if t_j→∞ and δ>0, then t_j exp(−δt_j)→0. On the tail t_j≥1, let v=δt_j/2>0. The elementary inequality exp(v)≥1+v≥v yields

\[
e^{\delta t_j}=e^{2v}=(e^v)^2\ge v^2=\delta^2t_j^2/4.
\]

Consequently

\[
0\le t_j e^{-\delta t_j}=t_j/e^{\delta t_j}
 \le4/(\delta^2 t_j)\longrightarrow0.
\tag{9.2}
\]

The rightmost limit uses t_j→∞ and δ²>0. This proves the private scalar head under exactly its stated hypotheses, without a separate positivity premise for the entire sequence.

Since r_j→0 and c is fixed, exp(c r_j)→1. Equations (9.1)–(9.2) make the right side of (9.1) tend to zero. Divide (8.2) by the positive m_j(H_j); squeezing with the nonnegative F_j gives F_j/m_j(H_j)→0. Divide this sequence by (4.1), whose limit is one. On the tail G_j(H_j)>0, cancellation of the positive main term gives

\[
\frac{F_j/m_j(H_j)}{G_j(H_j)/m_j(H_j)}=\frac{F_j}{G_j(H_j)}.
\tag{9.3}
\]

Thus F_j/G_j(H_j)→0. Choosing s=4λ+1 closes public `varying_row_far_relative_closedStrip_tendsto_zero` without a new public s assumption. The derivation in §§8–9 remains valid for every fixed s>4λ, exactly identifying the positive exponential gap required by this argument.

## 10. Actual finite lower/upper bounds and final squeeze

Put f_j=μ_j.real(E(N_j,H_j))/G_j(H_j). For any fixed ε>0, on the finite tail from §3 and the positive G_j(H_j) tail, apply (2.2) and (2.3) at the actual law ν_j and divide by G_j(H_j)>0. With R_j(ε) as (6.1), T_j(ε)=μ_j.real(T(N_j,H_j,ε)), and F_j as (8.1), this yields

\[
\underbrace{\frac{G_j(c(N_j,H_j,-\varepsilon))}{G_j(H_j)}-
 \frac{R_j(\varepsilon)}{G_j(H_j)}}_{\ell_j(\varepsilon)}
\le f_j\le
\underbrace{\frac{G_j(c(N_j,H_j,\varepsilon))}{G_j(H_j)}+
 \frac{T_j(\varepsilon)}{G_j(H_j)}+\frac{F_j}{G_j(H_j)}}_{u_j(\varepsilon)}.
\tag{10.1}
\]

By §§5–7 and §9 these two actual scalar sequences satisfy

\[
\ell_j(\varepsilon)\longrightarrow e^{-\lambda\varepsilon},
\qquad u_j(\varepsilon)\longrightarrow e^{\lambda\varepsilon}.
\tag{10.2}
\]

For completeness, the passage ε↓0 can be made without any liminf/limsup convention or exchange of limits. Given real a<1, continuity of ε↦e^(−λε) at ε=0 and its value one provide a fixed ε>0 with a<e^(−λε). Equation (10.2) then gives eventually a<ℓ_j(ε), and (10.1) gives eventually a<f_j. Given real b>1, continuity of ε↦e^(λε) at zero provides a fixed ε>0 with e^(λε)<b. Equation (10.2) gives eventually u_j(ε)<b and then f_j<b. Both choices use fixed positive ε before taking any row tail. Equivalently one can take ε=v⁻¹ for sufficiently large positive real v, since exp(±λ/v)→1 as v→∞. This is the order-characterization of f_j→1:

\[
\boxed{\mu_j.\mathrm{real}(E(N_j,H_j))/G_j(H_j)\longrightarrow1.}
\tag{10.3}
\]

This is public `varying_row_randomDenominator_relative_closedStrip_tendsto` with exactly the original row hypotheses and scale limits, and no new desired-conclusion premise. It concerns the literal weak random-wall event (1.4), not a normalized quotient random variable.

## 11. Degeneracies, endpoints and quantifiers

1. Early H_j<0 or H_j=0 and N_j=0 are permitted. All finite calls with N>0,H>0 or H≥1 are made on tails explicitly derived in §3. Real total division at earlier indices is never used to justify a cancellation. No prefix, row law or n sequence is modified.
2. The center radicand may be negative early when d<0. The proof of (4.2) waits until u_j≥1/2, after which the square identity and positive root are valid. Both signs and d=0 are covered by the same tail proof.
3. The zero-energy atom remains in E. If Q=0 then every coordinate is zero and every prefix is zero; on the positive-height/n tail the realized wall is zero and the weak event holds. The finite lower inclusion is allowed to lose some such mass in its lower-bound error, but never asserts the atom is absent. No division by Q or √Q occurs anywhere.
4. Weak spatial walls are unchanged. The finite lower event uses Q≥N−εH²; its complement error is controlled by the strict absolute deviation in (6.1). The upper center includes Q=N+εH². Middle bands are strict-left/closed-right; the complete middle event is strict at Q=N+εH² and Q=2N. FAR is closed at Q=2N and each dyadic lower endpoint, open at each upper endpoint. The exact accepted finite inclusions and covers pay every equality case.
5. The row laws are not assumed equal, convergent or coupled. Every finite call installs hprob j and takes ν=νSeq j. The actual β_j is bounded by the original common M in (8.2). No old fixed-law asymptotic theorem is evaluated at ν_j and then mislabeled a sequence limit.
6. The middle radius estimates hold simultaneously for all b in a fixed interval on one tail, hence for every k in the growing **actual** I_j on that tail. Geometry includes all indices through Nat.ceil(t_j/ε), without an extra kε<t_j premise. The fixed scalar B is paid before η is sent to zero; neither a hidden rate nor an unweighted infinite middle sum is used.
7. FAR keeps the actual finite Z(s)^N−Z(0)^N difference, cutoff and summed 2^(−k) payment through its qualified finite head. A new common-M scalar limit is proved; the old fixed-law FAR limit is not reused outside its scope.
8. The only law-moment bound on M is the given common real upper bound. M≥0 and finite square integrability are derived; no β lower bound, h all-index sign, n monotonicity or extra growth relation is introduced.
9. The final row limit is first proved for each fixed ε>0. Continuity in ε at zero is applied afterward to choose a fixed ε for each target neighborhood. No diagonal ε_j, unjustified exchange of limits or dependence of the finite constant B on the row is hidden.
10. Denominators canceled in (5.4),(6.2),(9.3),(10.1) are actual positive G values supplied on the stated tail. Main terms are strictly positive from their full values. The proof never treats total real division by an early zero strip probability as a conditional expectation.

## 12. Exhaustive source plan, semantic scope and outstanding gates

The proposed source has exactly six private theorem heads: `lower_moments_integrable` (§3), `eventual_finite_conditions` (§3), `closedStrip_relative_main_tendsto` (§4), `centerHeight_tail_geometry` (§4), `center_deviation_relative_tendsto_zero` (§6), and `time_mul_exp_neg_tendsto` (§9). Its exactly four public heads are the center (§5), whole middle (§7), whole FAR (§9), and actual random-denominator/strip ratio (§10). They all have their complete headers in proposed-interface.lean.txt. No new top-level value, instance, universe, variable, alias, notation or opaque constant is proposed. Every μ/G/J/R/F/t/r/main-ratio sequence, positive scalar choice, finite-threshold conjunction, equality and hprob instance is body-local. There is no hidden helper API or unfinished top-level body.

This is a complete mathematical argument using the specified predecessor mathematics. The lead must first bind/freeze the actual declarations and qualify RowUniformConditionalEnergy before this consumer implementation proceeds. The L-row exact source attempt003 has a first full machine pass, but final independent review is pending at the pinned checkpoint. The row-uniform complete mathematical proof and proposal are sealed, but no accepted formal producer is claimed here. A new final independent complete source-to-statement/proof review, every actual-owned full type/value coverage and exact new-source server kernel/transitive-axiom evidence are still required for formal acceptance. The standard axiom whitelist remains propext, Classical.choice and Quot.sound. No such gate is run or inferred by this mathematical author.

The next downstream mathematical tasks, after actual qualification, are the genuine small-x row adapter/Brownian comparison and the full changing-row window assembly, using the separately qualified positive-boundary branch where appropriate. They are not conclusions of (10.3). The original fixed-law v79 result remains COMPLETE; this packet neither reopens nor recounts it, and claims no novelty. No 124 unified mechanism is needed for any step above.
