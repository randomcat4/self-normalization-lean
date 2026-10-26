# Complete mathematical proof of L-row

STATUS: PROVED_MATHEMATICAL_CANDIDATE_PENDING_INDEPENDENT_REVIEW.

No Lean/parser/server/kernel/axiom check is claimed for this new packet. The author does not supply its independent final review. The original fixed-law OQ4 theorem remains COMPLETE_V79_RETAINED; the broader common-M row window remains OPEN.

## 1. Exact objects and already qualified inputs

Write `ν_j=νSeq j`, `n_j=n j`, `h_j=h j`, `s_j=s j`, and

\[
\pi_j=\operatorname{Measure.pi}(i\in\mathrm{Fin}(n_j)\mapsto\nu_j),
\qquad A_j=\{a:\forall k\le n_j,\ |S_k(a)|\le h_j\}.
\]

The zero prefix is included. In particular, for h≥0 the all-zero path belongs to A; for h<0 the strip is empty. Define, only inside this proof,

\[
p_j=\pi_j.\mathrm{real}(A_j),\qquad
I_j=\operatorname{energyJointIntegral}(\nu_j,n_j,h_j,s_j).
\tag{1.1}
\]

The actual transparent definitions inspected are

\[
\begin{aligned}
Q_n(a)&=\texttt{Shao.energy}\ a=\sum_{i\in\mathrm{Fin}(n)}a_i^2,\\
\texttt{energyPathIntegrand}\ h\ s\ a
 &=\begin{cases}\exp(s(Q_n(a)-n)/h^2),&a\in\texttt{Shao.closedStrip}\ h,\\0,&\text{otherwise},\end{cases}\\
\texttt{energyJointIntegral}\ \nu\ n\ h\ s
 &=\int\texttt{energyPathIntegrand}\ h\ s\ a\,d\nu^{\otimes n}(a).
\end{aligned}
\tag{1.2}
\]

Thus I is the literal numerator in the task. It is not an unspecified weighted event. The real measure `.real` is the real value of the same finite product measure; when its factors are probability laws it is the actual probability.

We use the qualified K and Kv with their actual constants
`lambda = Real.pi ^ 2 / 8` and `4 / Real.pi`. Set λ=π²/8. K says that for centered unit-variance changing row laws with a common third-moment bound,

\[
\frac{p_j}{a_j}\to1,
\qquad a_j=(4/\pi)\exp(-\lambda n_j/h_j^2),
\tag{1.3}
\]

provided the height sequence is positive at every index and has the three stated scales. Kv replaces the second moment one with a sequence v_j∈[1/2,2] and replaces a_j by `(4/π)exp(-λv_j n_j/h_j²)`. No variance convergence or convergence of the measures is an input.

The existing finite E2 theorem supplies, for every actual ν in the class and every `h≥energyE2Threshold M T`, `|s|≤T`, a real θ and the complete actual-law conclusion. Put

\[
P=\texttt{energyE1Constant}\ T,\qquad
C=\texttt{energyE2Constant}\ M\ T,\qquad H_2=\texttt{energyE2Threshold}\ M\ T.
\tag{1.4}
\]

When M,T≥0, the qualified domination theorems give P≥1 and C≥1. For the same selected θ, E2 gives the actual probability law

\[
\mu=\texttt{energyLinearTiltLaw}\ \nu\ h\ s\ \theta,
\quad E_\mu X=0,
\quad |\theta|\le C/h^2,
\quad |\log L|\le C/h^4,
\tag{1.5}
\]
\[
|E_\mu X^2-1|\le C/h,\qquad E_\mu|X|^3\le C,
\tag{1.6}
\]

and integrability of X, X², |X|³ under this same actual law. Here, with no hidden change of measures,

\[
\begin{aligned}
w_{h,s}(x)&=1_{\{|x|\le2h\}}\exp(sx^2/h^2),\quad Z=\int w_{h,s}\,d\nu,\\
\nu^{E}&=\nu.\mathrm{withDensity}\bigl(\operatorname{ofReal}(w_{h,s}/Z)\bigr),\\
L&=\int\exp(\theta x)\,d\nu^{E},\\
\mu&=\nu^{E}.\mathrm{withDensity}\bigl(\operatorname{ofReal}(\exp(\theta x)/L)\bigr).
\end{aligned}
\tag{1.7}
\]

These are precisely `energyWeight`, `energyNormalizer`, `energyTiltedLaw`, `energyLinearNormalizer`, and `energyLinearTiltLaw`. E2 asserts the probability and moment facts; they are not assumed.

The complete finite JointTransport conclusion, at the same ν,h,s,θ,n, contains Z>0, L>0, integrability of (1.2), and

\[
|I-c|\le (e^{e}-1)c,
\quad c=\texttt{energyJointCenteredProbability}\ \nu\ n\ h\ s\ \theta
     =\mu^{\otimes n}.\mathrm{real}(A_n(h)),
\tag{1.8}
\]
\[
e=PMn/h^3+C/h+Cn/h^4
  =\texttt{energyRelativePathError}\ M\ T\ n\ h\ge0.
\tag{1.9}
\]

This is a finite theorem for every actual law, not the fixed-original-law sequence wrapper. Its multiplicative estimate remains valid if c=0. The path transport retains the same absolute partial-sum event and the endpoint factor; it does not move the wall by a cumulative drift.

## 2. Derived lower moments and sign of M

For r≥0, both r≤1+r³ and r²≤1+r³. For 0≤r≤1, use r≤1, r²≤1 and r³≥0. For r≥1, use r≤r³ and r²≤r³. Consequently `|x|` and `x²` are dominated by the integrable function `1+|x|³` under each probability law ν_j. They are measurable. This proves the first- and second-moment integrability needed by the finite E1/E2 theorems without adding a public hypothesis.

The integral β_j=∫|x|³dν_j is nonnegative. Since β_0≤M, one obtains M≥0. This argument uses no division by M and works for any nonempty index type used here, in particular ℕ. There is no implicit assumption that the measures themselves converge.

## 3. K on a positive-height patch and eventual strict positivity

Since h_j→∞, choose N_0 such that h_j≥1 for all j≥N_0. Let

\[
\bar h_j=\begin{cases}h_j,&j\ge N_0,\\1,&j<N_0.\end{cases}
\tag{3.1}
\]

Every \bar h_j is strictly positive. It eventually equals h_j, so \bar h→∞ and the ratios `n/\bar h²`, `n/\bar h³` have exactly the required limits. Apply qualified row K to the original actual ν_j, the original common M and lengths n_j, and heights \bar h_j. All of K's all-index row moment and probability hypotheses hold by assumption. On j≥N_0 its numerator and comparison exponential are exactly p_j and a_j from (1.3). Thus eventual equality transfers its limit to

\[
p_j/a_j\to1.
\tag{3.2}
\]

For every j, a_j>0: π>0 and every real exponential is positive, including at any early `h_j=0` under Lean's real division convention. By (3.2), eventually p_j/a_j>1/2>0. Multiplication by a_j>0 gives p_j>0. This proves the first proposed public head for completely arbitrary early heights and lengths. No limit is divided by a sequence tending to a nonzero number unless that is explicitly justified below.

## 4. Select exact centers on one common tail

Choose a single integer N such that, for every j≥N,

\[
h_j\ge H_*:=\max\{H_2,\max(1,2C)\}.
\tag{4.1}
\]

The number H_* depends on M,T only. Its existence as a common height threshold follows from h→∞; it does not depend on a selected row law. For every j≥N, apply `energyE2_common_bounds` to the actual ν_j, h_j,s_j, using the integrability proved in §2 and all the given row moments. The hypotheses `h_j≥H_2` and `|s_j|≤T` both hold. Classical choice selects one θ_j satisfying the entire `energyE2Conclusion` for that same row. Set θ_j=0 for j<N. In Lean this is a body-local `if hj : N ≤ j then Classical.choose (...) else 0`; no selector is a public argument or top-level definition.

For every j define the actual, possibly only tail-probability, law and its actual second moment

\[
\mu_j=\texttt{energyLinearTiltLaw}\ \nu_j\ h_j\ s_j\ \theta_j,
\qquad v_j=\int x^2d\mu_j,
\tag{4.2}
\]

and c_j=`energyJointCenteredProbability ν_j n_j h_j s_j θ_j`. For j≥N, E2 gives (1.5)--(1.6) and probability/integrability/mean zero for μ_j. Since h_j≥1>0 and h_j≥2C,

\[
C/h_j\le1/2,\qquad 1/2\le v_j\le3/2\le2.
\tag{4.3}
\]

We have used the two sides of `|v_j-1|≤C/h_j` for both variance bounds. No bound is inferred from a signed moment without its integrability.

## 5. A legitimate all-index changing-row Kv input

The laws μ_j need not satisfy E2 at early indices. To meet the actual all-index hypotheses of Kv, patch only its internal input. Use the already assumed original law ν_0, whose probability, integrable third moment, exact mean zero and unit second moment are all given. Define

\[
\rho_j=\begin{cases}\mu_j,&j\ge N,\\\nu_0,&j<N,\end{cases}\quad
\widetilde v_j=\begin{cases}v_j,&j\ge N,\\1,&j<N,\end{cases}\quad
\widetilde h_j=\begin{cases}h_j,&j\ge N,\\1,&j<N.\end{cases}
\tag{5.1}
\]

Every ρ_j is an actual probability law, has integrable |X|³, exact mean zero and exact second moment \widetilde v_j. Its variance lies in [1/2,2] by (4.3) on the tail and by its value one before N. Every \widetilde h_j>0. Set

\[
B=\max(M,C).
\tag{5.2}
\]

For j≥N the third moment of ρ_j is ≤C≤B by E2; for j<N it is β_0≤M≤B. This is a single common third-moment bound for the entire patched sequence. The three height/length scales are unchanged because \widetilde h eventually equals h. Thus every hypothesis of qualified changing-row Kv is satisfied, including its all-index variance and positivity requirements.

It follows, by eventual equality on j≥N, that

\[
\frac{c_j}{b_j}\to1,
\qquad b_j=(4/\pi)\exp(-\lambda v_j n_j/h_j^2).
\tag{5.3}
\]

The unpatched b_j uses the actual second moment from (4.2). Its early values are immaterial to the limit; it remains a positive real exponential at every index. We did not assert that μ_j was a probability law before the E2 tail, did not replace any original public row law, and did not require an extra Gaussian or Rademacher construction.

## 6. Compare the true centered and original survival probabilities

On j≥N the variance estimate gives

\[
\left|-\lambda(v_j-1)\frac{n_j}{h_j^2}\right|
\le |\lambda|\frac C{h_j}\frac{n_j}{h_j^2}
=|\lambda|C\frac{n_j}{h_j^3}\longrightarrow0.
\tag{6.1}
\]

The multiplication of the variance bound uses `n_j/h_j²≥0` and h_j>0. Thus the exponent in (6.1) tends to zero by the absolute-value squeeze theorem. The exact real exponential algebra, using a_j>0, is

\[
\frac{b_j}{a_j}
=\exp\left(-\lambda(v_j-1)\frac{n_j}{h_j^2}\right).
\tag{6.2}
\]

Indeed expand `v_j=(v_j-1)+1`, use `exp(u+v)=exp(u)exp(v)` and cancel the positive factor a_j. This identity is meaningful even before N; the convergence argument only uses the tail estimate. Continuity of exp and exp(0)=1 yield b_j/a_j→1.

From (3.2), (5.3) and (6.2), division by the scalar limit one is legitimate and gives

\[
\frac{(c_j/b_j)(b_j/a_j)}{p_j/a_j}\to1.
\tag{6.3}
\]

On the eventual set p_j>0, a_j,b_j>0. Ordinary field cancellation identifies the expression in (6.3) with c_j/p_j. Therefore

\[
c_j/p_j\to1.
\tag{6.4}
\]

In particular, no absolute error of order o(1) was substituted for an error relative to the exponentially small p_j. This is why both row K and row Kv, and the exponent payment (6.1), are used.

## 7. Actual normalizers and endpoint payments for varying rows

This section verifies directly the normalizer assertion requested in the task. It does not call the existing fixed-ν `energyJointTransport_normalization_limits`.

For j≥N put

\[
Z_j=\texttt{energyNormalizer}\ \nu_j\ h_j\ s_j,
\qquad L_j=\texttt{energyLinearNormalizer}\ \nu_j\ h_j\ s_j\ \theta_j.
\]

The finite `energyJointTransport_finite_of_e2` applies to each row and the same θ_j. It supplies Z_j>0 and L_j>0. Its E1 field supplies

\[
\left|\log Z_j-\frac{s_j}{h_j^2}\right|
\le P\beta_j/h_j^3\le PM/h_j^3.
\tag{7.1}
\]

The last inequality uses P≥0, h_j>0 and β_j≤M. E2 gives the log-L and θ estimates (1.5). Hence

\[
\left|n_j\left(\log Z_j-\frac{s_j}{h_j^2}\right)\right|
\le PMn_j/h_j^3\to0,
\tag{7.2}
\]
\[
|n_j\log L_j|\le Cn_j/h_j^4\to0,
\qquad 0\le|\theta_j|h_j\le C/h_j\to0.
\tag{7.3}
\]

For the first limit in (7.3), use on the positive-height tail the exact identity
`n_j/h_j⁴=(n_j/h_j³)(1/h_j)`, where both factors tend to zero. Thus no additional relation between n_j and h_j is required. All the absolute bounds have nonnegative right sides on their tail.

For x>0 and an integer m≥0, `x^m=exp(m log x)`. This follows by induction from exp(log x)=x and exp-add; it includes m=0. Apply it only after establishing Z_j,L_j>0. On that tail the exact normalization is

\[
e^{-s_jn_j/h_j^2}Z_j^{n_j}L_j^{n_j}
=\exp\left[n_j\left(\log Z_j-s_j/h_j^2\right)+n_j\log L_j\right]\to1.
\tag{7.4}
\]

The same bounds separately give `L_j^n_j→1`, `exp(-s_j n_j/h_j²) Z_j^n_j→1`, and endpoint factors `exp(±|θ_j|h_j)→1`. These conclusions hold for the bounded, arbitrarily varying s_j because all their bounds use the same M,T-only constants. The proof never seeks an untruncated positive exponential moment of X². Equations (7.1)--(7.4) explain explicitly how the finite normalization payments survive row changes; they are absorbed already into (1.8)--(1.9).

## 8. Pass from centered survival to the literal energy integral

Use the accepted distribution-free scalar theorem `energyJointTransport_error_limits M T h n hinfty hshort`. Its complete conclusion includes

\[
\delta_j:=\exp(\texttt{energyRelativePathError}\ M\ T\ n_j\ h_j)-1\to0.
\tag{8.1}
\]

This theorem has no original-law parameter, so its use for the present h,n is exact. For each j≥N, use the finite theorem from §7 again as a mathematical fact about the same selected θ_j; no execution or replay is involved. Its final field is exactly

\[
|I_j-c_j|\le\delta_jc_j,
\qquad \delta_j\ge0,\quad c_j\ge0.
\tag{8.2}
\]

The nonnegativity of c_j is that of `.real` of a measure. On the common eventual set from §3 where p_j>0, divide (8.2) by p_j to obtain

\[
\left|\frac{I_j}{p_j}-\frac{c_j}{p_j}\right|
=\frac{|I_j-c_j|}{p_j}
\le\delta_j\frac{c_j}{p_j}.
\tag{8.3}
\]

The right side tends to zero by (8.1) and (6.4). Its tail is nonnegative by (8.2) and p_j>0. Squeezing the absolute difference between zero and this quantity proves

\[
I_j/p_j-c_j/p_j\to0.
\tag{8.4}
\]

Adding (6.4) to (8.4) yields the required literal result

\[
\boxed{\operatorname{energyJointIntegral}(\nu_j,n_j,h_j,s_j)/
\nu_j^{\otimes n_j}.\mathrm{real}(A_{n_j}(h_j))\to1.}
\tag{8.5}
\]

This proves the second proposed public head. Eventual integrability of its numerator is also supplied by the finite theorem, rather than being inferred from the asymptotic formula.

## 9. Quantifier, endpoint and scope checks

- Every occurrence of ν_j in a finite theorem is the actual row law at the same j; its hypotheses are discharged using that row's given moments and the common M. No fixed-original-law sequence theorem is applied with a varying ν_j.
- The arbitrary bounded sequence s_j can change sign and oscillate. The common bound T is chosen before the common E2 threshold and the choice of θ_j. No convergence assumption on s is present. The cases T=0, s_j=0 and negative s_j are all included in the same finite statements.
- Height positivity is only used after a common tail. Both applications of K/Kv are made to legitimate all-positive patched height sequences and transferred back by eventual equality. The public head has no all-index height-positivity assumption. Lengths may be zero at early indices; K, the finite transport, powers, and the actual path definitions all include n=0.
- The early centered-law filler ν_0 comes from the original row hypotheses. It is used only as an internal all-index Kv input. No false E2 assertion about early μ_j is made.
- The weak condition `|S_k|≤h` is unchanged in I,p,c and the comparison inputs. On its event every increment has `|X_i|≤2h`; this includes boundary equality, the first increment and the all-zero path. The accepted finite path law uses exactly this support consequence. No sample division by Q or removal of Q=0 occurs.
- The third-moment bound C for centered laws is common; the patched bound is exactly max(M,C). The variance perturbation costs O(n/h³), not O(n/h²). The normalizer log-L costs O(n/h⁴), and the endpoint costs O(1/h).
- No claim about the random-denominator event or the supremum over a shrinking x-window follows directly from (8.5). The original accepted fixed-law theorem is retained without a recheck, and no old proof or receipt is replayed.

## 10. Exact next mathematical dependency

L-row supplies the bounded varying-parameter deterministic-wall interface identified in the previous packet. To obtain a common bounded-radius cosh-excess control on `h_j/2≤b≤C_0 h_j`, a later proof must make an actual bad-radius sequence choice b_j. Its parameter becomes `±s(b_j/h_j)²`, bounded by `s C_0²`, and its scales satisfy `b_j→∞`, `n_j/b_j²→∞`, `n_j/b_j³→0` because `1/2≤b_j/h_j≤C_0`. Applying (8.5) to both signs then contradicts a bad relative cosh-excess. This is the precise next consumer; it is not an exported third head or a proof of the entire random-denominator assembly here.

After that common-radius control, the original center/middle/far finite decompositions still need their changing-row sequence assembly and independent review. The finite far-tail bound retains its explicit common-third-moment payment and the indispensable `Z(s)^n-Z(0)^n` difference. No complete W-row or broader common mechanism is claimed by this unit.
