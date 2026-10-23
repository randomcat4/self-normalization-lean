# All-start Brownian terminal spectrum: complete mathematical proposal

Status: mathematical derivation complete, declarations PROPOSED and NOT FROZEN; no Lean implementation or kernel check. The full formal deliverable is INCOMPLETE. In particular, the actual producers 139/143/145 have the exact recorded interfaces but are not treated here as qualified accepted modules. Their qualification, parent freeze, implementation, exact-source kernel/transitive-axiom receipt and fresh complete independent review remain unpaid.

This author149 packet is confined to `drafts/oq4/brownian-terminal-spectral-author-v1/`. It proposes `Shao.OQ4.BrownianTerminalSpectral`. The exhaustive heads and all literal transparent values are in `declarations.lean.txt`. The proof below covers every proposed theorem, including private theorems. No additional mathematical premise is proposed.

## Source and contract

The source is read-only `C:/game/shao/current/oq4/b01/proof01.md`, lines 316–343, especially the displayed killed Brownian series and P0. Its immediate consumer is the one terminal Brownian block in P1/P2. The source uses the classical Dirichlet killed-heat eigenfunction expansion. This proposal derives that same expansion from the already established actual finite Rademacher spectrum and the actual Brownian survival limit. It is an alternative formal proof, with classical attribution; no novelty claim is made.

Let Ω be any type with its given measurable structure, P any probability measure on Ω, and B an actual process satisfying `IsBrownianReal B P`. This is the exact Brownian API appearing in producer143. Put

`g_T(u) = P.real (BrownianSurvivalBoundary.closedSurvival B T u)`.

The event is the producer's literal closed survival event, monitoring all times in the closed interval, including time zero. No completion, same-space coupling, canonical process, semigroup, Markov, reflection, boundary-null, weak-convergence or spectral hypothesis is added. For every T>0 and every u∈[-1,1] the proposed conclusion is

`g_T(u) = Σ_(ell≥0) 4(-1)^ell/[π(2ell+1)] exp[-λ(2ell+1)^2 T] cos[(2ell+1)πu/2]`,

where λ=π²/8, using the existing transparent `RademacherScalarBounds.lambda`. Both the series and its absolute-value series converge uniformly in all real u for each fixed positive T. For every T≥1 and every u∈[-1,1], including both endpoints,

`g_T(u)=(4/π) exp(-λT) cos(πu/2)+R_T(u)`,

`|R_T(u)|≤C exp(-9λT)`, `C=4/[3π(1-exp(-2π²))]>0`.

`terminalRemainder` is literally the raw actual probability minus that principal term. Thus the remainder is not an existentially supplied function. The single C is independent of Ω, P, B, T and u. No supremum measurability is used or needed.

## Reusable inputs and their scope

Accepted finite sources are `RademacherFiniteBasis`, `RademacherAllModes`, `RademacherFiniteS1`, `RademacherSpectralPairing`, `RademacherScalarBounds`, `RademacherCosine`, `KilledIteration` and `KilledPathLaw`. Only their public actual declarations are used. In particular, `RademacherFiniteS1.vector_even_zero` is NOT used to cancel the coefficients at arbitrary starts.

Producer145 `BrownianKilledCosineIdentity.discrete_killed_test_integral` is used with F identically one. Its B4 theorem is not used. Producer143 `PolygonalKilledFunctionalLimit.discrete_survival_tendsto_brownian` is used with the literal Rademacher law, ceil ambient rows, floor monitored horizon, and the explicit varying starts and radii. Its boundary input is internal, from139; this proposal does not assume that boundary input. The exact producer source and formal-freeze hashes are recorded in `api-evidence.md`/`checkpoint.json` and must be qualified before a successful consumer check is acceptance evidence. Canonical-existence producer146 is unnecessary for a theorem about this supplied actual B/P/hB.

## Notation and the ten transparent values

Throughout, H=m+1, m≥1 when using the finite killed spectrum, and q_ell=2ell+1. The finite states are the integers from -m through m. The already defined angles are α_(m,ell)=q_ell π/(4H) and β_(m,ell)=q_ell π/(2H). `rawStartTerm` is precisely

`H^-1 (-1)^ell cot(α_(m,ell)) cos(β_(m,ell))^n cos(β_(m,ell) r)`.

Here `cot` is exactly the accepted `RademacherFiniteS1.cotangent`, the real quotient cos/sin. All powers are natural real powers, including negative finite eigenvalues. `spectralTerm` and `spectralSeries` are the term and real tsum in the displayed Brownian series. `stripRadius=m/(m+1)` is an NNReal. `latticeStart` clamps the integer floor of H*u to [-m,m]. `rowLength` is the NATURAL CEILING of T*H². `lowTerm T u j ell` is `rawStartTerm` at m=j+1, n=floor(T*H²), the clamped start, when ell belongs to the accepted `lowerModes`; it is zero otherwise. Finally

`majorant T ell = (4/π) exp[-λT q_ell/2]`.

The remaining two public values are the explicit C and the literal probability-minus-principal-term remainder. These are exactly the ten definition values in the head file; there are no proposed aliases, opaque values, structures or constructors.

## A. Finite all-start algebra

### `survivalCoefficient_even_zero`

This head holds for every natural m,k, without a legal-mode hypothesis. Unfold the accepted coefficient formula:

`c_(m,2k)=H^-1 Σ_(s=-m)^m sin[(kπ/H)(s+H)]`.

For every integer s the sine at -s is the negative of the sine at s: the two angles are kπ-(kπ/H)s and kπ+(kπ/H)s; `sin(kπ)=0` and `cos(kπ)=(-1)^k` give the identity directly from sine addition/subtraction. H>0 for every natural m, so the displayed algebra is valid even at m=0. Negation is an involutive bijection on the finite integer state interval. Reindexing by that bijection makes the finite sum its own negative. Over ℝ it is therefore zero, and multiplication by H^-1 preserves zero. This argument cancels the counting coefficient itself, independently of the start r. The same reasoning includes k=0.

### `vector_odd_start`

For every m,ell,r, unfold `vector`, `phi`, `theta` and `RademacherCosine.angle`. Its sine argument is

`β_(m,ell) r + (ell π + π/2)`.

Sine addition, `sin(ellπ)=0`, `cos(ellπ)=(-1)^ell`, and `sin(x+π/2)=cos x` give exactly `(-1)^ell cos(β r)`. H>0 justifies the denominator simplification. No restriction on r or on whether the mode is in the finite mode interval is needed for this identity.

### `killedMass_odd_start`

For m≥1 and r in the actual states, apply `RademacherAllModes.killedMass_spectrum` with the real physical threshold h=m. The accepted weak-cell conditions are m≤h<m+1, true by equality and 1>0. Its full sum has modes 1,...,2m+1. Partition those modes into the disjoint injective images 2k, k=1,...,m, and 2ell+1, ell=0,...,m, using the public parity partition and odd-index membership/injectivity lemmas in `RademacherFiniteS1`. All even contributions vanish by the preceding COEFFICIENT identity. For an odd mode, the accepted `survivalCoefficient_odd` is H^-1 cot α, `mu` is cos β, and the preceding arbitrary-start identity supplies the vector. Rearranging the real products gives `rawStartTerm`. This retains every signed eigenvalue and works for all natural n, including n=0.

### `finite_mass_split`

Apply the accepted `RademacherSpectralPairing.sum_reflection_partition` to the function `rawStartTerm m n r`. Its lower modes satisfy q_ell<H; its reflected index is m-ell and q_(m-ell)=2H-q_ell, so these are precisely the high modes. The optional central index exists exactly when m is even. At that index the accepted `beta_center` gives β=π/2, hence cos β=0. Since n≥1 its natural power is zero; all other finite factors are real, so the central contribution is zero. The partition identity, followed by finite sum distributivity, is the exact split displayed in the proposed head. No negative eigenvalue is removed in this equality.

## B. Deterministic lattice approximation and actual probability attachment

### `latticeStart_bounds`

For a=-(m:ℤ), b=(m:ℤ) we have a≤b. The maximum `max a (min b floor(Hu))` is ≥a by definition. Both a and `min b floor(Hu)` are ≤b, so that maximum is ≤b. This proves both integer bounds, for every u and m.

### `scaledStart_error`

Write H=m+1 and q=Hu. The assumption u∈[-1,1] gives -H≤q≤H. Put z=floor q, so z≤q<z+1. We show |clamp(z)-q|≤1. If -m≤z≤m, the clamp is z and 0≤q-z<1. If z<-m, integrality yields z≤-m-1=-H; the floor inequalities and q≥-H yield z=-H and -H≤q<-m. The clamped value is -m, at distance at most one. If m<z, then z≥m+1=H; z≤q≤H forces z=q=H. The clamped value m is at distance exactly one. Divide by the positive H to obtain the head. This explicitly includes u=-1 and u=1, at which the error is 1/H rather than a falsely claimed strict error.

### `scale_tendsto`, `radius_tendsto`, `start_tendsto`

The scale sequence is H(j+1)=j+2; it tends to positive infinity by the natural-cast limit and addition of a constant. Consequently H^-1→0 and H^-2→0. The real coercion of `stripRadius (j+1)` is 1-H^-1, which tends to one. The NNReal conclusion follows from its subtype/embedding topology; all radii are nonnegative by their literal NNReal expression. The absolute error bound from `scaledStart_error` and H^-1→0 proves the scaled start tends to u by squeezing its distance to u. These statements do not assert finite clamped endpoints already equal u.

### `rowLength_horizon`

This is exactly `Nat.le_ceil` applied to the nonnegative real T*H². The ambient product row is CEIL, satisfying143's inequality in the required direction. The monitored horizon remains FLOOR. The public `floorHorizon_le` then gives the required monitored-length≤ambient-length hypothesis of145.

### `rademacher_moments`

Unfold the actual accepted law as halfENNReal•δ_1 + halfENNReal•δ_(-1). The half weight is finite and has real value 1/2. Every real-valued function on these two atoms is integrable: each Dirac integral is integrable and finite scalar multiplication and finite measure addition preserve integrability. Thus, for each of the three specified functions, its actual integral equals `[f(1)+f(-1)]/2`. For f(x)=x this is zero, for f(x)=x² it is one, and for f(x)=|x|³ it is one. The latter function is integrable. This supplies every probabilistic moment and integrability requirement of143 for the fixed law; no assertion that a general third-moment premise is automatic is used.

### `discrete_row_mass`

Set h=H, b=m/H, z=r and F=1 in the public generic145 theorem `discrete_killed_test_integral`. Its strict h>0 condition is satisfied. The identity b*h=m is algebraic because H>0. The state bounds imply |r|≤m, hence the required physical start condition |z|≤b*h. The monitored length is floor(T H²), the ambient length ceil(T H²), so the preceding ceiling inequality and143's public floor bound provide l≤n. The constant test is measurable and has the literal bound M=1. Use the final equality in145. The indicator integral of the constant one is the actual real probability of the same discrete event, which is measurable by143's public measurability theorem. Its right side is the literal definition of `killedMass`. Rewriting b*h=m gives precisely this head. This step is why the time-zero condition is harmless: it has been explicitly paid by |r|≤m, rather than silently dropped.

### `finite_mass_tendsto_brownian`

Apply143's actual `discrete_survival_tendsto_brownian` with, at index j:

- hSeq(j)=H(j+1), nSeq(j)=rowLength T (j+1), and νSeq(j)=the actual Rademacher law;
- bSeq(j)=stripRadius(j+1), uSeq(j)=latticeStart(j+1,u)/H(j+1), and M=1.

The actual probability instance is accepted `law_isProbabilityMeasure`. Positivity of the scale, the ceiling horizon, the integrability/mean/second/third moments, hSeq→∞, bSeq→1 and uSeq→u have all been proved above. hB,T>0 and the full closed-interval hu are exactly the given hypotheses of this head. Thus143 yields convergence of the literal finite-product probabilities to the raw P.real closedSurvival of this same supplied process B. At every index `latticeStart_bounds` puts r in the state set. Replace each finite-product probability by `discrete_row_mass`. This proves this head and makes no replacement of the Brownian model or common-space assumption on the changing finite products.

## C. Scalar bounds, with all domain conditions

All differentiability arguments in this section are on compact real intervals on which cos is strictly positive. They may be formalized using the actual pinned `monotoneOn_of_hasDerivWithinAt_nonneg` API and derivative APIs listed in `api-evidence.md`. A continuous differentiable function with nonnegative derivative on such an interval is monotone, and a function vanishing at zero with that property is nonnegative. The differentiability also supplies the required continuity. The following proofs spell out the functions and derivative signs; they introduce no new declared helper heads.

### `tan_lower`

Fix 0≤x<π/2. Throughout [0,x], cos t>0. The function F(t)=tan t-t vanishes at zero and has derivative tan²t≥0, since tan'=1/cos² and sin²+cos²=1. Therefore F(x)≥0. The case x=0 is included in the same argument.

### `tan_upper_quarter`

On [0,π/4], cos(2t)≥0, so the double-angle identity yields cos²t≥1/2. Cos t>0 there. The function G(t)=2t-tan t vanishes at zero and has derivative 2-1/cos²t≥0. It is therefore nonnegative, proving the bound. Both endpoints are included.

### `log_cos_bounds`

On [0,x]⊆[0,π/4], first put U(t)=tan t-t. From the preceding bounds 0≤tan t≤2t and U≥0. The function V(t)=(4/3)t³-U(t) vanishes at zero and has derivative 4t²-tan²t≥0. Hence 0≤U(t)≤(4/3)t³.

Now L(t)=-log(cos t)-t²/2 vanishes at zero and has derivative U(t). Thus L≥0. The function W(t)=t⁴/3-L(t) also vanishes at zero, and its derivative is (4/3)t³-U(t)≥0. Hence W≥0, giving L≤x⁴/3. Cos t>0 throughout, so the logarithm derivative uses a nonzero argument and is valid at every point used. This proves both inequalities, including x=0.

### `cotangent_bound`

For 0<x≤π/4, sin x>0, cos x>0 and tan x≥x>0. The literal cos/sin quotient is 1/tan x. Therefore it is nonnegative and at most 1/x. All divisions have a proved positive denominator.

### `cosine_power_bound`

For 0≤x<π/2, the function E(t)=log(cos t)+t²/2 has derivative t-tan t≤0 throughout [0,x], by `tan_lower` at each t. It is zero at zero, so log(cos x)≤-x²/2. Since cos x>0, for every natural n,

`|cos(x)^n|=cos(x)^n=exp(n log(cos x))≤exp(-n x²/2)`.

This is valid for n=0 as well. The proposed head deliberately has strict x<π/2: the central x=π/2 case was handled separately in the exact finite split, with n≥1. No logarithm of zero is used.

### `floor_time_error`, `floor_time_tendsto`, `scaled_time_eventually`

For n=floor(T H²), the actual natural floor inequalities give 0≤T H²-n<1, since T H²≥0. Division by H²>0 gives `floor_time_error`. H(j+1)^-2→0 then squeezes n/H²→T, proving `floor_time_tendsto`. If T>0, convergence implies eventually n/H²≥T/2>0, hence n>0 and, being natural, n≥1. These are the two simultaneous assertions in `scaled_time_eventually`, with one uniform eventual index and no dependence on the frequency or start.

### `coefficient_tendsto`

Fix ell and q=2ell+1≥1. For m=j+1 put a_j=qπ/(4H). Then a_j>0 and a_j→0, so the sequence approaches zero through the punctured neighborhood. The actual pinned `Real.tendsto_sin_div_nhdsNE_zero` gives sin(a_j)/a_j→1; cos(a_j)→1 by continuity. Therefore

`H^-1 cot(a_j) = [4/(πq)] * cos(a_j)/(sin(a_j)/a_j) → 4/(πq)`.

The algebraic identity uses a_j≠0. For the continuity-of-division step the limiting denominator is 1≠0. Finite accidental zero sine values away from the eventual neighborhood do not affect a filter limit; all needed rewrites are taken eventually where 0<a_j<π/2. Thus this head does not assume legality of the fixed mode at every finite m.

### `power_log_error`

Fix m≥1 and ell with b=β_(m,ell)≤π/4. This b is positive because q≥1,H>0,π>0. Let n=floor(T H²). The preceding log bound supplies

`0≤-log(cos b)-λq²/H²≤C_rho*q⁴/H⁴`,

because b²/2=λq²/H² and b⁴/3=C_rho*q⁴/H⁴, with the existing literal C_rho=π⁴/48. Write d=-log(cos b)-λq²/H²≥0 and δ=T-n/H²∈[0,H^-2). Then

`n log(cos b)+λq²T = λq²δ-n d`.

Its absolute value is ≤λq²δ+n d. Use δ≤H^-2 and n≤T H² to bound the latter by `(λq²+T*C_rho*q⁴)/H²`, exactly the proposed head. T=0 causes n=0 and is covered. No frequency-uniform fourth-order remainder is asserted without the displayed small-angle condition.

### `mode_power_tendsto`

For fixed ell, β_(j+1,ell)→0, so eventually 0<β≤π/4. The preceding error bound has a fixed finite numerator, while H^-2→0. Consequently the logarithmic exponent tends to -λq²T. On this eventual interval cos β>0, so exp of the logarithmic exponent equals the actual natural power cos(β)^n. Continuity of exp proves the proposed limit. This includes T=0 and uses only eventual positivity, not positivity of the high negative eigenvalues.

## D. Countable domination and the negative-mode estimate

### `majorant_summable`

For T>0 put Q=exp(-λT)∈(0,1) and A=(4/π)exp(-λT/2)>0. The literal majorant equals A Q^ell by exponential addition and natural multiplication. Its summability follows from the actual geometric summability API and multiplication by a fixed scalar. In particular its real tsum is finite and nonnegative.

### `spectralTerm_bound`

For q=2ell+1≥1, the sign has absolute value one and |cos|≤1, so

`|spectralTerm T u ell|≤[4/(πq)] exp(-λTq²)`.

Use 1/q≤1 and q²≥q/2 to obtain the majorant. This holds for every real u, independently of hu and of the Brownian model.

### `lowTerm_tendsto`

Fix ell. The accepted membership criterion for `lowerModes (j+1)` is 2ell<j+1, which holds eventually. Then `lowTerm` is its raw finite term. Its coefficient tends to 4/(πq) by `coefficient_tendsto`; its eigenvalue power tends to exp(-λq²T) by `mode_power_tendsto`; its sign is fixed. Finally

`β_(m,ell) * latticeStart(m,u) = (qπ/2) * [latticeStart(m,u)/H] → qπu/2`

by `start_tendsto`; continuity of cos gives the last factor. Product continuity gives exactly the proposed `spectralTerm`, with all signs retained. The hu hypothesis includes both endpoints.

### `lowTerm_eventually_bound`

Take the common eventual condition of `scaled_time_eventually`. For any ell outside `lowerModes`, the term is zero, below the nonnegative majorant. For a lower mode q<H, 0<α<π/4 and 0<β<π/2 by the accepted lower-angle bounds. The coefficient bound gives

`0≤H^-1 cot α≤4/(πq)`.

`cosine_power_bound` gives `|cos(β)^n|≤exp[-λ(n/H²)q²]`. The last cosine factor is bounded by one for every start. Since n/H²≥T/2, q≥1 and q²≥q, this implies

`|rawStartTerm|≤[4/(πq)] exp(-λTq²/2)≤(4/π) exp(-λTq/2)=majorant`.

The same eventual condition works simultaneously for every ell and u. Thus it supplies the universally quantified eventual domination required by the actual Tannery theorem, rather than a weaker frequency-dependent eventual estimate.

### `low_sum_tendsto`

Apply the exact pinned `tendsto_tsum_of_dominated_convergence` with index filter atTop, countable summation index ell, f(j,ell)=lowTerm T u j ell, g(ell)=spectralTerm T u ell and bound=majorant T. `majorant_summable`, `lowTerm_tendsto`, and `lowTerm_eventually_bound` supply its three hypotheses, converting real norms to absolute values. At each j, lowTerm is supported on the actual finite `lowerModes`; its tsum is the finite sum in this head. The limiting tsum is the literal `spectralSeries`. This proves the result. The actual API explicitly permits one eventual uniform bound, so no additional ad hoc summation-limit lemma is being assumed.

### `high_sum_abs_le`

For a lower index ell, write q=2ell+1<H and ell'=reflect(m,ell)=m-ell. The accepted reflection identities give

`cot α_(m,ell') = tan α_(m,ell)` and `cos β_(m,ell') = -cos β_(m,ell)`.

On 0≤a<π/4, tan a≤1: indeed sin a≥0 and cos a>0; cos(2a)≥0 and sin²+cos²=1 imply sin²a≤cos²a, hence sin a≤cos a. Thus the reflected coefficient is ≤1/H and is nonnegative. The factor (-1)^ell' has absolute value one and the start cosine is bounded by one, regardless of r. After taking absolute values of the genuine signed power, `|(-cos β)^n|=|cos β|^n`. This retains the exact parity until the justified absolute-value step. The positive-angle cosine bound then gives

`|rawStartTerm(m,n,r,ell')|≤H^-1 exp[-λ(n/H²)q²]`

`≤H^-1 exp(-λTq/2) = [π/(4H)] majorant T ell`.

Use the triangle inequality for the finite high sum. The summable majorant is nonnegative, so its finite sum over `lowerModes` is at most its real tsum. This proves the exact proposed high-sum bound. This estimate includes the last mode q_(ell')=2H-1: it corresponds to the lower q=1 and its small coefficient, not a large-index damping claim.

### `high_sum_tendsto_zero`

At m=j+1,n=floor(T H²), the common time condition holds eventually. The preceding bound has right side `[π/(4H)] Σ majorant`, which tends to zero since its tsum is a fixed finite real number and H→∞. Squeeze the nonnegative absolute value between zero and this bound; equivalently use convergence of distance to zero. No property of the clamped start is needed for this estimate, so the head works for all real u.

### `finite_mass_tendsto_series`

For each j, latticeStart is in the actual states. On the common eventual time condition n≥1, `finite_mass_split` identifies the actual finite killed mass as the low finite sum plus the high reflected finite sum. Their limits are spectralSeries and zero by the two preceding results. Addition of limits and eventual equality prove this head. This completes the deterministic spectral limit, separately from the probabilistic limit in section B.

## E. Public convergence and the actual spectral formula

### `spectralTerm_abs_summable`

Apply real comparison with the nonnegative summable majorant in section D and `spectralTerm_bound`. Thus Σ|term| is summable, hence so is the original real series. This is at every fixed T>0 and every real u.

### `spectral_uniform_absolute_convergence`

Use the pinned `tendstoUniformly_tsum_nat` with f(ell,u)=|spectralTerm T u ell| and u_majorant=majorant T. Its norm is just the same absolute term, because it is nonnegative. The domination in section D is uniform in all real u. The theorem yields exactly the partial-sum and absolute-tsum functions appearing in this public head. This proves uniform absolute convergence, without taking any nonmeasurable supremum.

### `spectral_uniform_convergence`

Apply the same uniform-summation API directly to f(ell,u)=spectralTerm T u ell, using the same summable majorant. Its limiting function is the literal `spectralSeries T`. This gives the displayed public head on all real u.

### `brownian_survival_spectral`

The identical sequence of actual finite killed masses tends both to the raw probability, by `finite_mass_tendsto_brownian`, and to the spectralSeries, by `finite_mass_tendsto_series`. AtTop on ℕ is nontrivial and ℝ is Hausdorff, so uniqueness of the limit identifies those two reals. This is exactly the actual all-start formula; it does not merely exhibit some Brownian law on another probability space. At u=±1, every limiting cosine is zero, consistently giving zero raw survival. That conclusion is derived, not used as a separate endpoint premise.

## F. Geometric terminal remainder

### `shifted_tail_identity`

The established absolute summability gives ordinary summability. Split a summable natural series after its zeroth term by `Summable.tsum_eq_zero_add` (or the equivalent public natural-add tail identity). The literal term at ell=0 is `(4/π) exp(-λT) cos(πu/2)`. Subtracting it yields precisely the shifted tail in this head.

### `tail_term_bound`

Write ell=k+1 and q=2k+3. Then q≥3, so 4/(πq)≤4/(3π). Furthermore

`q²≥9+16k`.

For k=0 this is equality. For k≥1 its difference is 4k(k-1)≥0, proving it for every natural k rather than all real k. Since T≥1,

`λTq²≥9λT+16λk`,

and 16λ=2π². The sign and start cosine again have absolute values at most one. Exponential monotonicity, addition and natural multiplication therefore give the bound in the exact proposed head, with ratio exp(-2π²). It is uniform for all real u.

### `series_remainder_bound`

The shifted series is absolutely summable. Apply the triangle inequality to its tsum and the preceding termwise comparison. For Q=exp(-2π²), we have 0<Q<1 because π²>0. The actual geometric tsum is 1/(1-Q). Thus the bound is

`[4/(3π)] exp(-9λT)/(1-Q) = remainderC * exp(-9λT)`.

All denominator factors are positive. This proves this private head, again on all real u.

### `remainderC_pos`

π>0 and 0<exp(-2π²)<1 imply 3π(1-exp(-2π²))>0. Its numerator is 4>0, so the literal quotient is positive.

### `brownian_terminal_block`

For T≥1 we have T>0. Use the actual spectral identity to replace only the raw P.real probability by the spectralSeries in `terminalRemainder`. The preceding bound gives its absolute bound. The displayed decomposition follows exactly from the literal definition of terminalRemainder by real subtraction and addition. Both statements hold for every allowed actual B/P/hB and every u in the full closed interval. This is P0 with its actual probability and one explicit universal constant.

## Remaining gates and scope

There is no unresolved mathematical step hidden in an assumed Brownian spectral, Markov, boundary-null or convergence premise in the proposed heads. The genuine formal work remains substantial: parent full-head/value/proof freeze; qualification of the exact139/143/145 dependencies; implementation of this module; server-only targeted Lean checking and complete actual-owned transitive-axiom receipt; fresh independent complete original-source-to-statement/proof/all-head/all-value review. Actual import-object availability has not been tested. No result here is an accepted new module, and no C12/OQ3/OQ4/OQ56 root closes. The next authorized action is parent review/freeze of this packet; author149 stops before implementation.
