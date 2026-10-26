# Complete proof of the positive-boundary bearing unit

**UNIT STATUS: PROVED, mathematical candidate pending independent review.**

**BROADER W-row STATUS: INCOMPLETE in this packet.** No counterexample to W-row is asserted. No source check, Lean/parser/kernel/axiom check, or independent qualification is claimed.

## 1. Existing exact inputs and the scope of reuse

Only already qualified mathematical interfaces are reused. This author has inspected their actual public types and the actual transparent values needed here; this is not a new full review of their old proof bodies.

* `PolygonalKilledFunctionalLimit.discrete_survival_tendsto_brownian` already accepts a changing law `νSeq`, a common third-moment bound M, lengths `nSeq`, height scales tending to infinity, moving nonnegative boundary factors tending to one, and moving starts. It returns the actual finite-product weak strip-survival probability for the actual given B/P. It does not require a fixed original law.
* `BrownianPositiveCDF.survival_time_eq_probability` supplies the actual Brownian time-scaling identification at a positive time. `probability_continuousAt`, `probability_tendsto`, and `probability_pos` supply continuity and strict positivity of the actual Brownian CDF at positive points.
* `PositiveBoundaryStudentized.sandwich_probability` is a finite statement for each actual probability law. `randomDenominatorEvent_eq` is the exact all-n equality between its event and the literal multiplicative event, including n=0. Neither of those finite statements imposes a law-independent asymptotic conclusion.
* `Shao.energy`, `Shao.closedStrip`, and `RandomDenominatorFarTail.randomDenominatorEvent` have their literal finite-path meanings. In particular, `energy` is the sum of actual squared coordinates and `closedStrip` monitors every prefix including zero.

The current v120 curated library snapshot is only a read-only source input. Accepted old source/object/review evidence is not rerun. The v79 original-scope acceptance is retained exactly and is not extended by this packet.

## 2. A finite truncation bound requiring no fourth moment

Fix a real probability law ν with integrable `|X|³`, `E X²=1`, and `E|X|³≤M`. Here X denotes the identity real coordinate. Let n≥1, K>0, δ>0. Work under the actual law `π_n=ν^⊗n`. Put
\[
 Y=X^2,\quad T_K=\min(Y,K),\quad c=E T_K,
 \quad R_K=Y-T_K,\quad r=E R_K=1-c.
\]
These are definitions within the proof, not new public abstractions.

Both Y and R_K are integrable; T_K and its square are bounded and measurable. We have
\[
 0\le T_K\le Y,\quad 0\le c\le1,\quad 0\le R_K,
 \qquad T_K^2\le K Y.
 \tag{2.1}
\]
The last inequality follows by `T_K≤K` and `T_K≤Y`, all quantities being nonnegative. Thus
\[
 E T_K^2\le K E Y=K.
 \tag{2.2}
\]
This is an estimate of a truncated fourth power only. It is not an assumption about `E X⁴`.

At every real z,
\[
 0\le z^2-\min(z^2,K)\le |z|^3/\sqrt K.
 \tag{2.3}
\]
For z²≤K the left difference is zero, including the cutoff endpoint. For z²>K, we have `|z|>√K>0`, so
`z²−K≤z²≤|z|³/√K`. This proves (2.3) for every sign and also z=0. Integrating gives
\[
 0\le r\le M/\sqrt K.
 \tag{2.4}
\]

For the iid finite coordinates under π_n, write `T_i=min(a_i²,K)` and `Z_i=T_i−c`. Boundedness makes all products below integrable. For i≠l, the product law gives
\[
 E_{\pi_n}(Z_i Z_l)=(E_\nu(T_K-c))^2=0.
\]
This is ordinary finite-product integral factorization, with no asymptotic input. For each i,
\[
 E_{\pi_n}Z_i^2=E_\nu T_K^2-c^2\le K.
\]
Expanding the finite square of the sum, all cross terms vanish; hence, with
\(W=n^{-1}\sum_i Z_i\),
\[
 E_{\pi_n}W^2\le K/n,
 \qquad E_{\pi_n}|W|\le\sqrt{E W^2}\le\sqrt{K/n}.
 \tag{2.5}
\]
The middle inequality is Cauchy--Schwarz against the constant one on a probability space.

Set `R=n⁻¹Σ_i(a_i²−T_i)`. It is nonnegative and integrable, with `E R=r`. The exact identity
\[
 Q/n-1=W+R-r
\]
therefore yields
\[
 E_{\pi_n}|Q/n-1|
 \le E|W|+E R+r
 \le\sqrt{K/n}+2M/\sqrt K.
 \tag{2.6}
\]
For every path, `δ·1_{δ<|Q/n−1|}≤|Q/n−1|`. Integrating this inequality, then dividing by δ>0, proves
\[
 \pi_n\{|Q-n|>\delta n\}
 \le \frac{\sqrt{K/n}+2M/\sqrt K}{\delta}.
 \tag{2.7}
\]
The event equality uses n>0. No assertion dividing by n was made for n=0.

## 3. Changing-row energy weak law (P1)

Fix δ>0 and a desired ε>0. The integrand `|z|³` is nonnegative, so M≥0 follows from the common bound for any row. Choose one K>0 so large that
`2M/√K<δε/2`. If M=0, any sufficiently large positive K works as well; there is no division by M. Since `n_j→∞`, eventually n_j>0 and
`√(K/n_j)<δε/2`. Apply (2.7) to ν_j with this same K and same M at every such index. It gives
\[
 0\le\pi_j\{|Q-n_j|>\delta n_j\}<\varepsilon.
\]
This is P1. The order of choices is ε, then K using M and δ, then a length threshold using K. No row-law-dependent threshold occurs. Mean zero was not used. No assumption that the laws converge, that the row lengths are monotone, or that the rows live on one common probability space was used.

## 4. Changing-row positive deterministic boundary (P2)

Fix B/P/hB and a real r>0. Let `r_j→r`. Define
\[
 N_j=\max(n_j,1),\quad T=r^{-2}>0,
 \quad h_j=r\sqrt{N_j}>0,\quad
 b_j=\max(r_j/r,0)\in\mathbb R_{\ge0},\quad u_j=0.
\]
In Lean, T is `Real.toNNReal ((r^2)⁻¹)` and b_j is `Real.toNNReal (rSeq j/r)`. Since `N_j≥1`, all h_j are positive, and h_j→∞ because N_j→∞. The exact real identities are
\[
 T h_j^2=N_j,\qquad \lfloor T h_j^2\rfloor=N_j.
 \tag{4.1}
\]
Also b_j→1 in the nonnegative reals and u_j→0, with 0∈[−1,1]. The horizon condition of the existing changing-row survival theorem holds with equality, not merely eventually. Its hypotheses are thus met by the original row laws ν_j with the original common M.

Applying `discrete_survival_tendsto_brownian` gives
\[
 \pi_{N_j}(\nu_j)\{
    |S_k/h_j|\le b_j\text{ for all }k\le N_j\}
 \longrightarrow
 P\{ |B_t|\le1\text{ for all }0\le t\le T\}.
 \tag{4.2}
\]
This display is exactly the existing theorem's start-zero discrete event after (4.1). Eventually n_j≥1 and r_j>0, so N_j=n_j and b_j=r_j/r. On that tail,
\[
 b_j h_j=r_j\sqrt{n_j},
\]
and the left event in (4.2) is exactly `A_{n_j}(r_j√n_j)`. This equality holds on the actual finite path spaces, so there is no identification of sample spaces with different dimensions at early indices.

The already qualified Brownian scaling interface identifies the right side with
\[
 F_B(1/\sqrt T)=F_B(r).
\]
Here `√(r⁻²)=1/r` because r>0. This is precisely `BrownianPositiveCDF.survival_time_eq_probability`; all its positive-time hypotheses are met. Eventual equality of the left sequences proves P2 for the original n_j and r_j. The Brownian object was arbitrary throughout, and no row/Brownian coupling was introduced.

## 5. Exact studentized sandwich and P3

Fix x_j→x>0. For each fixed δ∈(0,1), the old finite sandwich, applied separately to the actual ν_j, gives on the eventual tail x_j≥0
\[
 \begin{split}
 \pi_j(A_{n_j}(x_j\sqrt{n_j}\sqrt{1-\delta}))-q_j(\delta)
 &\le\pi_j(E_{n_j}(x_j))\\
 &\le\pi_j(A_{n_j}(x_j\sqrt{n_j}\sqrt{1+\delta}))+q_j(\delta),
 \end{split}
 \tag{5.1}
\]
where `q_j(δ)=π_j(|Q−n_j|>δn_j)`. The finite event bridge is exact:
\[
 \texttt{randomDenominatorEvent}\ n\ (x\sqrt n)
 =\{a:a\in\texttt{closedStrip}(x\sqrt{\texttt{energy}(a)})\}.
 \tag{5.2}
\]
It holds for every n and x, including n=0. Thus (5.1) concerns the literal desired event, not a convention on a quotient.

For clarity, the underlying set argument also verifies the endpoints. On `|Q−n|≤δn`, one has `n(1−δ)≤Q≤n(1+δ)`; monotonicity of the real square root and x≥0 gives the lower inclusion and upper inclusion in (5.1). At either energy endpoint equality is allowed. The complement is exactly the strict bad event used in P1.

P1 gives q_j(δ)→0. The sequences
`x_j√(1−δ)` and `x_j√(1+δ)` tend to the positive limits
`x√(1−δ)` and `x√(1+δ)`. P2 therefore gives the respective deterministic probability limits
\[
 F_B(x\sqrt{1-\delta}),\qquad F_B(x\sqrt{1+\delta}).
 \tag{5.3}
\]
To turn this into convergence without an implicit compactness claim, fix ε>0. Continuity of F_B at x and continuity of `δ↦x√(1±δ)` at δ=0 let us choose δ∈(0,1) such that both values in (5.3) differ from F_B(x) by less than ε/3. For that fixed δ, eventually each deterministic probability differs from its limit by less than ε/3 and q_j(δ)<ε/3. Substitution into (5.1) gives
\[
 F_B(x)-\varepsilon<\pi_j(E_{n_j}(x_j))<F_B(x)+\varepsilon.
\]
This proves P3. The order of limits is j→∞ for fixed δ, then δ↓0. No fourth moment and no common fixed law entered.

## 6. The relative limit P4

By the existing positive-point CDF continuity theorem,
`F_B(x_j)→F_B(x)`. The existing positivity theorem gives `F_B(x)>0`. P3 supplies the same numerator limit. Division is continuous at a nonzero denominator, so
\[
 \frac{\pi_j(E_{n_j}(x_j))}{F_B(x_j)}\to1.
\]
The real quotient is defined at every early index by the existing real field convention. Eventually x_j>0 and the denominator is strictly positive; thus no early zero denominator changes the limit. In particular no sample-energy division or zero-energy omission occurs anywhere.

## 7. Why this is a genuine bearing unit

For the row window contradiction argument, choose bad indices j_k and bad points x_k∈(a_{j_k},1). Since eventually a_j>0, a subsequence of x_k converges to a point in [0,1]. If its limit x_* is positive, P4 applies to the row laws `ν_{j_k}`, lengths `n_{j_k}`, and points x_k, with the same M. It forces the bad relative error to zero, a contradiction. This covers x_*=1 as well as the interior of (0,1).

P1 alone cannot cover x_*=0: it controls deviations of size δn, and its elementary error bound is generally only polynomial in n. The small-boundary survival probability is of order `exp(−λ/x_k²)`, so subtracting an unconditional bad-energy probability is not a valid relative-error argument. We explicitly do not do that.

## 8. Precise remaining W-row interface and accepted payments

The next substantive interface is the following bounded-parameter, deterministic-boundary statement. It is **not established or exported by this packet**. With the same actual row laws/common M, assume
\[
 h_j>0,\quad h_j\to\infty,\quad n_j/h_j^2\to\infty,
 \quad n_j/h_j^3\to0,\qquad |s_j|\le T<\infty.
\]
The required statement is
\[
 \frac{\displaystyle\int 1_{A_{n_j}(h_j)}
   \exp\!\left(s_j\frac{Q-n_j}{h_j^2}\right)d\pi_j}
 {\pi_j(A_{n_j}(h_j))}\longrightarrow1.
 \tag{L-row}
\]
Its denominator is eventually positive by the accepted changing-row deterministic K theorem. It is strictly weaker than W-row: both occurrences of the path event have the same deterministic wall, there is no random-wall probability in its statement, and it makes no claim on an x-window. It permits bounded varying s_j because later radius selection replaces a fixed exponent s/h_j² by `(s(b_j/h_j)²)/b_j²`.

This is a sequence-assembly gap, not a missing finite exponential-moment estimate. Existing exact inputs already pay the following obligations:

* `UnconditionalKernelAsymptotic.varying_row_closedStrip_relative_asymptotic` is K for unit-variance changing rows/common M. Its variance version accepts centered changing laws with variances in [1/2,2] and a common third-moment bound.
* `EnergyE1Bounds.energyE1_common_bounds` is a finite uniform theorem for every actual ν satisfying the moments. The threshold `energyLogThreshold M T` and its error constants depend only on M,T. It supplies the actual truncated energy law and log normalizer error, not a hypothetical global exponential square moment.
* `EnergyE2Bounds.energyE2_common_bounds` is likewise finite uniform with threshold `energyE2Threshold M T`; it supplies an exact centering θ, `|θ|≤C/h²`, `|log L|≤C/h⁴`, centered variance `1+O(1/h)`, and a common centered third-moment bound.
* `EnergyRelativePathBounds.energyRelativePath_common_bounds` and `EnergyJointTransport.energyJointTransport_finite_of_e2` are generic finite statements for every actual ν. Their thresholds and scalar relative errors use M,T; `energyJointTransport_error_limits` is deterministic. They retain the same absolute path event, the endpoint factor, and the zero-energy path.

The currently exported sequence wrappers `energyJointTransport_normalization_limits`, `energyJointTransport_common_bounds`, `ConditionalEnergyConcentration.energy_laplace_ratio_tendsto`, and the controls in `UniformConditionalEnergy` instead bind one fixed ν outside the sequence. Substitution of ν_j into a fixed-law limit is invalid. A new assembly must select θ_j on the common tail, use the finite estimates with the same M,T, put the centered laws into the accepted varying-variance K theorem, and use the scalar error limits. None of those finite estimates should be reproved or rerun solely to add a changing-row wrapper.

After L-row, the exact additional consumers are the bounded-radius cosh-excess control over `h_j/2≤b≤C h_j`, and the random-denominator center/middle/far assembly. The common-radius control must be obtained by a genuine bad-radius sequence contradiction or an equivalent uniform argument. Existing `middle_finite_bound` and its finite covers/Markov inequality can then be applied to each ν_j; the original fixed-law asymptotic `middle_relative_tendsto_zero` cannot simply be called with changing ν_j.

For the far layers, the finite accepted `RandomDenominatorFarTail.far_tail_bound` is already uniform through its explicit β parameter: its right side is
\[
 C_s(n/h^2)\exp\{-s(n/h^2)/4+C'_s\beta(n/h^3)/8\}.
\]
Replacing β_j by the common M is legitimate by monotonicity of this explicit expression. The accepted finite difference `Z(s)^n−Z(0)^n` pays the infinite layer sum; one must retain it. No new uniform-tail probability estimate is being asserted here. The changing-row asymptotic wrapper and the final diagonal/window proof remain to be written and reviewed.

For small points x_j→0 with `x_j n_j^(1/6)→∞`, h_j=x_j√n_j has exactly `h_j→∞`, `n_j/h_j²→∞`, and `n_j/h_j³→0`. The original source E5 decomposition and Brownian first-term asymptotic are therefore the intended later consumers once L-row and its radius/denominator assembly are closed. This identifies a concrete missing interface rather than assuming the whole desired window as a proxy lemma.

## 9. Acceptance and boundary ledger

* Mathematical status P1--P4: PROVED by Sections 2--6, candidate only until independent review.
* Full common-M row window: INCOMPLETE in this packet; L-row and its subsequent sequence assemblies remain unexported/unreviewed.
* Original weak fixed-law window/sharp criterion: COMPLETE_V79_RETAINED, no new closure credit.
* Original C1/C2/C12 scope: no change; their later accepted complete scope is not reopened here.
* OQ3: separately PAUSED_BY_USER; no wake or resource activation.
* OQ56 and broader extensions: no conclusion supplied by this packet.
* Zero energy: literal multiplicative event retained at all n; no probability mass discarded.
* Early zero lengths / negative moving points: handled by eventual equality/positivity, not removed from the public quantifiers.
* Required next evidence: lead freezes the exact five heads and any implementation delta; a different fresh qualified reviewer reads complete source-to-statement/proof/all actual types and any required values; new exact-source server kernel/all-owned transitive axiom receipt is then required under the existing lane lease. The author is not its own reviewer.
