# Actual terminal killed-kernel block: complete mathematical proposal

Status: PROVED mathematically relative to the exact frozen upstream contracts listed below; DECLARATIONS_PROPOSED, NOT_FROZEN, NOT_IMPLEMENTED, NOT_KERNEL_CHECKED, NOT_INDEPENDENTLY_REVIEWED. Author150, fresh gpt-6.1-sol / xhigh context, OQ4 lane. This packet owns only `drafts/oq4/brownian-terminal-kernel-block-author-v1/`. It uses math-theorem, never math-ultra. The author cannot certify the final independent review.

The original bearing is `C:/game/shao/current/oq4/b01/proof01.md`329–343, SHA256 `7c51246eb02a0d694a366ce3ab5a3a9cca03723160c1291bce29dd817f68bc38`: integrate a last Brownian-scale block to recover the coefficient 4/π. The immediate downstream consumer is the original normalized P2/long-time limit, which is outside this unit. This unit eliminates the finite last-block error estimate P1 and provides its fixed-law eventual form. It does not prove long-time normalization, the source K/Kv theorem, or any original root closure.

All ten proposed owned heads and the sole literal value are in `declarations.lean.txt`. There are one public definition, six private theorems and three public theorems; no new instance, abbrev, structure, auxiliary top-level head or hidden assumed result is proposed. Labels P1/P2/P3 below are packet labels; packet P2 is the error-limit theorem, not original source equation (P2). Every helper is proved below. No implementation is authorized before the lane lead has read and frozen this exact complete packet.

## Exact objects, dependencies and assumptions

Let ν be an actual Borel probability measure on ℝ, and let the existing `killedKernel ν h` be the translated increment law restricted to the CLOSED interval [−h,h]. Its rows are not normalized. Its monoid power is `killedIterKernel ν h n`, including the identity kernel at n=0. Write

\[
 K_h^n(z,dw)=\operatorname{killedIterKernel}(\nu,h,n,z),\quad
 G_n(z)=\operatorname{killedMass}(\nu,h,n,z),\quad G_n=G_n(0).
\]

The existing `killedMass` is literally `killedAction ... (fun _ => 1)` and is equal to the REAL total row mass. The existing accepted finite kernel facts give, for every real z,h and natural n,

\[
0\le G_n(z)\le1,\qquad
K_h^0(z,\cdot)=\delta_z,\qquad
G_n(z)=K_h^n(z,\cdot).\mathrm{real}(\mathbb R).
\]

Each row is a finite measure; if |z|≤h then its support is contained in [−h,h] in its own almost-everywhere sense, even at n=0. Its action has the exact semigroup identity on globally bounded Borel tests. All of these are accepted `KilledIteration.lean` facts, rather than hypotheses introduced by this packet. `KilledPathLaw.lean` identifies the rows with the actual unconditioned finite product law, restricted to survival and pushed forward by the endpoint; this also identifies G_n with the source survival probability at start zero for h≥0. No new finite-product adapter is needed.

Use only the literal canonical model of producer146:

\[
\Omega_*=(\mathbb N\times\mathbb N)\to\mathbb R,\quad
P_*=\operatorname{CanonicalBrownian.law},\quad B_*=\operatorname{CanonicalBrownian.B}.
\]

Its probability instance and `CanonicalBrownian.isBrownianReal` have no Brownian existence or desired-limit premise. We use that theorem internally. It is not an input of any declaration in this module. The actual upstream qualification is still unpaid: producer146 is under its first-check API repair; producers147 and149 are locally written/frozen but not accepted. The mathematical argument here uses their frozen statements, and no acceptance claim is made before those producers are qualified.

For T∈ℝ≥0, h∈ℝ and u∈ℝ, set in this proof only

\[
 L=\lfloor (T:\mathbb R)h^2\rfloor_+,\quad
 g_T(u)=P_*.\mathrm{real}\{\omega:\forall t\in\mathbb R_{\ge0},\ t\le T\Rightarrow |u+B_*(t,\omega)|\le1\},
\]
\[
 \lambda=\frac{\pi^2}{8},\quad
 a_T=\frac4\pi e^{-\lambda T},\quad
 f_h(w)=\cos\frac{\pi w}{2h},\quad
 C_P=\frac4{3\pi(1-e^{-2\pi^2})},\quad b_T=C_Pe^{-9\lambda T}.
\]

L is exactly `PolygonalKilledFunctionalLimit.floorHorizon T h`; λ is exactly the accepted `RademacherScalarBounds.lambda`; C_P is exactly producer149's public `BrownianTerminalSpectral.remainderC`. The local notations in this proof do not add transparent module definitions. Only D1 below adds a definition.

Producer147 defines `brownianSurvival` to be the actual raw probability g_T and defines `survivalError` to be the real sSup of ALL physical starting-point errors. Its public `tendsto_survivalError` gives convergence to zero for fixed T>0 and fixed ν under precisely integrability of |x|³, mean zero and second moment one. Producer149's public `brownian_terminal_block`, instantiated with B_*,P_* and the unconditional146 Brownian theorem, gives for T≥1 and every u∈[−1,1]

\[
 g_T(u)=a_T\cos(\pi u/2)+r_T(u),\qquad |r_T(u)|\le b_T.
\]

Its remainder is literally `terminalRemainder B_* P_* T u = g_T(u)-a_T*cos(pi*u/2)`. It is not supplied data. Its positive constant is independent of ν,T,h,u,n. No given Brownian model, weak convergence, killed heat identity, source S, terminal P1 or root K conclusion occurs among this module's public hypotheses. Producer148/B1 is not used.

## D1: literal sourceSurvivalError value

The definition is exactly

\[
E_\nu(T,h):=\operatorname{BrownianUniformSurvival.survivalError}(B_*,P_*,\nu,T,h)
=\sup_{z\in[-h,h]}|G_L(z)-g_T(z/h)|,
\]

where the final supremum is the literal real `sSup` of that image. The definition exists for every real h. Claims requiring interval nonemptiness state h≥0 or h>0 explicitly. No maximum, measurable selection, attainment, countable dense subset, open interval, supplied error bound or different Brownian version replaces this value.

## L1: survival_error_image_bddAbove

Fix ν,T,h as in its head; no sign assumption on h is needed. For every real z, `killedMass_nonneg` and `killedMass_le_one` give 0≤G_L(z)≤1. The canonical probability instance gives 0≤g_T(z/h)≤1 by `measureReal_nonneg` and `measureReal_le_one`. These bounds hold for every set, so they do not require a new measurability theorem for the raw Brownian event. If p,q∈[0,1], then −1≤p−q≤1, hence |p−q|≤1. Consequently 1 is an upper bound of the entire error image over [−h,h]. This is the required BddAbove witness, including when h<0 makes the interval empty.

## L2: sourceSurvivalError_bounds

Assume h≥0. Then 0∈[−h,h], so the image A of errors is nonempty: it contains e(0):=|G_L(0)−g_T(0/h)|. By L1 the image is bounded above. The actual conditionally complete lattice theorem `le_csSup` gives e(0)≤sSup A, so 0≤e(0)≤E_ν(T,h). For the upper bound, `csSup_le` applies to the nonempty image, using the pointwise bound e(z)≤1 proved in L1. It gives E_ν(T,h)≤1. This proves both conjuncts. Nonempty image and boundedness are not inferred from an attainment claim.

## L3: source_survival_error_le

Let |z|≤h. By `abs_le`, z∈[−h,h], so e(z)=|G_L(z)−g_T(z/h)| is an actual member of A. Apply `le_csSup` with L1's BddAbove witness and this image membership. Its conclusion is exactly e(z)≤E_ν(T,h) after unfolding D1 and147's public literal definitions. No cross-module private lemma from147 is called. No strict inequality for the supremum is asserted.

## L4: terminal_row_error

Assume h>0, T≥1 and |z|≤h. From −h≤z≤h and positivity of h, division gives −1≤z/h≤1. Apply producer149's public terminal theorem to u=z/h in the SAME actual canonical model. Its equality and tail bound yield

\[
 |g_T(z/h)-a_T\cos(\pi(z/h)/2)|=|r_T(z/h)|\le b_T.
\]

Since h≠0, the real identity π(z/h)/2=πz/(2h) identifies this cosine with f_h(z). Write

\[
G_L(z)-a_T f_h(z)=(G_L(z)-g_T(z/h))+(g_T(z/h)-a_T f_h(z)).
\]

The triangle inequality and L3 give |G_L(z)−a_T f_h(z)|≤E_ν(T,h)+b_T. Endpoints z=±h are legal because both upstream ranges are closed. This estimate uses probabilityν,h>0,T≥1 only; no moment, invariance or source S hypothesis is used.

## L5: terminal_residual_regular

Let T,h,n,z have exactly the unrestricted values in this head. Define only within the proof

\[
 q(w)=G_L(w),\quad c(w)=f_h(w),\quad R(w)=q(w)-a_Tc(w),\quad\mu=K_h^n(z,\cdot).
\]

First, q is Borel measurable: unfold `killedMass` and apply `killedAction_measurable ν h L (fun _ => 1) measurable_const`. The cosine c is continuous, hence Borel measurable, as a cosine of a real linear function with the fixed total real coefficient π/(2h). This remains true at h=0, under Lean's total real division. Constant multiplication and subtraction give Borel measurability of R. This proves the first conjunct of L5.

For every real w, 0≤q(w)≤1 by the actual killed-mass lemmas, and |c(w)|≤1 by `Real.abs_cos_le_one`. Thus

\[
 |R(w)|\le |q(w)|+|a_T|\,|c(w)|\le1+|a_T|.
\]

The row μ is an actual finite measure by `killedIterKernel_isFiniteKernel`. Apply `killedAction_integrable ν h n z R` to the just-proved Borel measurability and the explicit global bound 1+|a_T|. This gives genuine integrability of R under μ, proving the second conjunct. It also implies integrability of |R|. The proof can equivalently apply the pinned `Integrable.of_bound` used by that existing lemma. No Brownian survival function is integrated in L5 or any later step; its measurability as a function of physical start is therefore not needed here.

For use in L6, note separately that q is globally bounded by 1 and c by 1, so the same accepted `killedAction_integrable` gives integrability of q and c under μ; a_Tc is integrable by constant multiplication. These are facts about the actual row, and do not follow merely from the existence of an abstract residual integral.

## L6: terminal_integral_identity

Let ν,T,h,n have exactly the unrestricted values in this head, and put μ=K_h^n(0,·). Apply `killedAction_semigroup ν h n L 0 (fun _ => 1) measurable_const` with its explicit bound 1. Since killedMass is the action on the constant one test, the result is

\[
 G_{n+L}=\int_{\mathbb R}G_L(w)\,\mu(dw).
\]

The integrability of G_L under μ can be obtained either from its actual Borel measurability and bound 1 as above, or directly from `killedAction_iterated_integrable` with the constant test. The actual definition gives

\[
 F_n:=\operatorname{killedAction}(\nu,h,n,f_h,0)=\int c(w)\,\mu(dw).
\]

The two integrands q and a_Tc are integrable, as established after L5. Therefore the pinned `integral_sub` and `integral_const_mul` give

\[
 \int(q-a_Tc)\,d\mu=\int q\,d\mu-a_T\int c\,d\mu=G_{n+L}-a_TF_n.
\]

Reverse this equality for the exact orientation of L6. The semigroup has actual natural powers; neither n>0 nor L>0 has been assumed or needed. There is no time-zero kill and no artificial truncation of the cosine.

## P1: terminal_kernel_block

Assume exactly probabilityν, T≥1, h>0 and arbitrary n∈ℕ. Let μ=K_h^n(0,·), R as in L5, and M=E_ν(T,h)+b_T. The existing `killedIterKernel_ae_support ν h n 0` applies since |0|=0≤h. It gives

\[
 |w|\le h\quad\text{for μ-almost every }w.
\]

For each such w, L4 gives |R(w)|≤M. This is an actual μ-almost-everywhere bound. L5 gives integrability of R and |R| under μ, while the constant M is integrable since μ is finite. Consequently

\[
\begin{aligned}
 |G_{n+L}-a_TF_n|
 &=\left|\int R\,d\mu\right| &&\text{by L6},\\
 &\le\int |R|\,d\mu &&\text{by the pinned norm-integral inequality},\\
 &\le\int M\,d\mu &&\text{by integral_mono_ae and the bound above},\\
 &=M\,\mu.\mathrm{real}(\mathbb R) &&\text{by integral_const},\\
 &=(E_\nu(T,h)+C_Pe^{-9\lambda T})G_n &&\text{by killedMass_eq_real}.
\end{aligned}
\]

Here real norm is absolute value; the constant integral initially has order `μ.real univ * M`, and real commutativity gives exactly M*G_n. The factor is nonnegative as well: E≥0 by L2, and b_T>0 by149's `remainderC_pos` and positivity of real exponential. This positivity is not an extra premise. No row is renormalized, and no division by G_n occurs. If G_n=0, μ has zero total mass and the same calculation yields zero error. It does not require a separate survival-positivity assertion.

## P2: tendsto_sourceSurvivalError

Assume exactly probabilityν, fixed T>0, integrability of |x|³, mean zero and second moment one, as displayed in the proposed head. Apply147's public `tendsto_survivalError` with B_*,P_*, the unconditional146 `isBrownianReal`, and these same ν/T/moment hypotheses. Its conclusion, after unfolding only D1, is

\[
 \operatorname{Tendsto}(E_\nu(T,\cdot),\mathrm{atTop},\mathcal N(0)).
\]

This is the exact desired statement. The canonical model is not existentially chosen after ν or h, and no desired Brownian limit is passed as an assumption. Third-moment boundedness across a class is not added;147 supplies the fixed-law conclusion from the finite third moment of this very law. No uniformity in T or ν is claimed.

## P3: eventually_terminal_kernel_block

Assume exactly the displayed moment hypotheses, fixed T≥1 and ε>0. Then T>0, so P2 applies. By the definition of convergence, the open interval (−∞,ε) is a neighborhood of zero; there is a real H₀ such that E_ν(T,h)<ε for every h≥H₀. This can be obtained by `Tendsto.eventually` and then the pinned `Filter.eventually_atTop` equivalence. Set H=max(1,H₀). Then H>0 and h≥H implies h>0 and E_ν(T,h)≤ε.

For every such h and every natural n, P1 yields a bound with factor E_ν(T,h)+b_T. Because G_n≥0 by `killedMass_nonneg`, multiplication preserves E+b_T≤ε+b_T and gives

\[
 |G_{n+L}-a_TF_n|\le(\epsilon+C_Pe^{-9\lambda T})G_n.
\]

The same H works for all n, since the convergence cutoff is chosen before n and P1 holds for every n. This is precisely the proposed existential H>0 statement, with no h-dependent or n-dependent threshold concealed in the quantifiers. A strict supremum bound is obtained here from an actual limit of the literal supremum, not from taking the supremum of strict pointwise bounds.

## Source fidelity, boundary attacks and remaining gates

For the original P1 notation, let N≥L and use n=N−L. The natural-number identity (N−L)+L=N gives the displayed source G_N expression and error bound. This is arithmetic for a downstream consumer; no extra public theorem, large-N hypothesis or long-time assertion is proposed here. In the original argument the independent long-time condition later supplies N≥L (indeed N−L≥m); none of it is needed to prove the finite n+L statement.

All natural n are covered, including n=0: μ=δ₀, the support condition follows from h>0, G₀=1 and F₀=cos0=1. L may be zero for small positive h. The actual semigroup and L1–L4 still apply: the literal error E accounts for the discrepancy between the identity kernel mass and the positive-time Brownian survival. No floor-time asymptotic is invoked in this finite bound. The closed endpoints are included. ν may have atoms or be a degenerate probability law in P1, since that theorem has no moment hypotheses. Such laws do not falsely acquire P2/P3 unless their exact source moments hold. G_n=0 causes no division issue. T=1 is included. T=0 has total definitions and the explicitly unrestricted auxiliary algebra, but is outside P1/P3 and outside P2's positive-time limit.

Dependency ledger: accepted finite kernel/support/semigroup/path-law and λ definitions are KNOWN_ACCEPTED. The explicit all-start Brownian P0 and the B0 limit are EXACT_FROZEN_UPSTREAM_CONTRACTS, currently UNQUALIFIED rather than open assumptions in the proposed public types. L1–L6/P1/P2/P3 are PROVED_HERE at the mathematical level. No original K/P2 conclusion or equivalent blocker is hidden as a helper. This is the classical positivity/semigroup argument already in the source, with explicit C_P; no novelty claim is made.

Unpaid gates: (i) lane lead full packet read and exact declaration/import/value freeze; (ii) complete local implementation only after that freeze; (iii) actual qualification of146/147/149 and their139/143/145 producer chain, without replaying accepted142; (iv) the actual necessary import-presence and source-bound server kernel/all-owned type/value/transitive-axiom receipt, under the existing single-heavy OQ4 lease; (v) one fresh qualified independent complete source-to-statement/proof review, including every actual private/public/generated head and literal value; (vi) lane/root integration and exact artifact binding. Allowed standard axioms remain only propext, Classical.choice and Quot.sound. No Lean executable, toolchain/import/object inspection, build, Git, cache action or remote mutation was run by author150. Source inspection is not kernel evidence. Original general OQ4/K/Kv and every other open root remain OPEN.
