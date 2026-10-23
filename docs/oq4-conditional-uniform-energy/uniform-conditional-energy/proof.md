# Uniform conditional energy on a bounded radius window — author175

STATUS: COMPLETE_MATHEMATICAL_PROOF_AND_EXHAUSTIVE_DECLARATION_PROPOSAL; NOT_PARENT_FROZEN; NOT_LEAN_IMPLEMENTED; NOT_INDEPENDENTLY_REVIEWED. This is a proof of the stated deduction from the actual public K/E4 producers, whose formal qualification remains a prerequisite to implementation. It is not an acceptance or original OQ4 closure claim.

The proposed production module is `Shao.OQ4.UniformConditionalEnergy`, file `Shao/OQ4/UniformConditionalEnergy.lean`. The exhaustive new declaration/value/import inventory is `declarations.lean.txt`. This author owns only this new draft directory. Existing owners and upstream source bytes are untouched. No children, sidebar chats, source implementation, parser, server operation, Lean invocation, Git operation or cache operation was used.

## Frozen-source target and permitted inputs

The complete original sources were read: `C:/game/shao/current/oq4/denom01.md`, SHA256 `71b4f28df03edfe3cc8a4ff5f95beb7d80b716d4b7c64fed01a2dc6989448d3f`, 131 LF; and `energy01.md`, SHA256 `2e0387f0a35ca677853e45fff271cc2fb0e87db9ee9c6b2f00d3bcf56b51d9e6`, 125 LF. The direct target is denom01 lines23–46, equations(3)–(4); the finite deviation bound also supplies the ingredient of(6). Both parent mathematical intake notes were read completely.

Fix an actual Borel probability measure ν on ℝ with integrable |x|³, integral x=0, and integral x²=1. There is no fourth moment, global exponential moment, extra first/square integrability premise, supplied survival asymptotic or supplied conditional-energy limit. Let n:ℕ→ℕ and h:ℕ→ℝ satisfy

* h_k→+∞;
* t_k=n_k/h_k²→+∞;
* r_k=n_k/h_k³→0.

There is no all-index h_k>0 or n_k>0 hypothesis. In all finite formulas n denotes the real cast of a natural length. Write μ_n=Measure.pi(fun _:Fin n=>ν), A_b=the existing literal Shao.closedStrip b, Q=Shao.energy, G(n,b)=μ_n.real(A_b), λ=π²/8, and m(n,b)=(4/π)exp(-λn/b²). These are proof-local notation only, not new Lean definitions. Existing closedStrip monitors prefixes0,…,n with weak walls, so the full zero path and n=0 convention are retained.

The two actual imported producers used internally are:

1. `UnconditionalKernelAsymptotic.varying_row_closedStrip_relative_asymptotic`: actual unit-variance finite-product G/m→1, with actual moment premises and all-index positive radii. It has no S/AC or desired-K premise. We instantiate the row law constantly ν and its common moment bound at β=∫|x|³dν, and repair only a finite height prefix.
2. `ConditionalEnergyConcentration.energy_laplace_ratio_tendsto` at each fixed real parameter, together with `closedStrip_probability_eventually_pos`. These accept the original tail scales without all-index height positivity and refer to the actual `energyJointIntegral`. The third public head, `energy_concentration_ratio_tendsto`, was also read; it is not needed for the new original-h²-scale conclusion.

The qualified EnergyJointTransport/EnergyPathLaw definitions and public measurability/integrability interfaces are reused. No private theorem from E4 or EnergyPathLaw is called by this new module. The new finite scalar and integrability helpers below pay their own proofs.

## 1. Elementary exp-pair facts, including negative deviations

For proof exposition alone write F(y)=(exp(y)+exp(-y))/2-1. The new module introduces no top-level F value. F is even by exchanging its two summands. The two bounds exp(y)≥1+y and exp(-y)≥1-y imply F(y)≥0 for every real y. If y>0, exp(y)>1+y and exp(-y)≥1-y give F(y)>0.

For 0≤u≤v, put a=exp(v-u). Exact exponential multiplication gives

2(F(v)-F(u))=(a-1)(exp(u)-exp(-v)).

Here a≥1 because v-u≥0, and exp(u)≥exp(-v) because -v≤u. Thus F(u)≤F(v). Evenness then proves F(u)≤F(v) whenever |u|≤|v|, with no sign restriction on u or v. This is the complete proof of the proposed `exp_pair_mono_abs`; the preceding strict argument proves `exp_pair_strict_pos`. In particular the energy-deviation argument does not discard Q-n<0.

## 2. Finite measurability, true integrability, and the exact integral identity

The sole new transparent value is the actual integral

J(ν,n,b,h,s)=∫ 1_(A_b)(a) F(s(Q(a)-n)/h²) dμ_n(a),

spelled with the exp-pair and a literal if in `energyCoshExcessIntegral`. Its full value, all binders and the actual product measure are frozen in the proposal. Real division is total at early h=0, but identities involving cancellation will only be used at h>0. The integrand is pointwise nonnegative for all real b,h,s; `integral_nonneg` consequently proves `energyCoshExcessIntegral_nonneg` with no probability or positivity hypothesis. This unconditional nonnegativity claim does not assert an unproved finite value or integral linearity.

For the finite analytic statements assume b>0. The old coordinate theorem gives |a_i|≤2b on A_b. Squaring, summing over Fin n, and using n≥0 give

0≤Q(a)≤4nb²,   |Q(a)-n|≤Q(a)+n≤4nb²+n   (a∈A_b).

These statements also hold at n=0: the sums are empty. The old `energyPath_energy_le` is private and is not used; its required sum argument is paid here from the public coordinate bound and energy_nonneg. The closed event is measurable: use the existing `shiftedClosedSurvival_eq_closedStrip n b hb.le` and `measurableSet_shiftedClosedSurvival n b 0` (or the equivalent finite/countable intersection of the measurable prefix inequalities). The actual energy is measurable by the qualified `Shao.measurable_energy`.

For any real u and b>0, put B=|u|(4n+n/b²), a finite nonnegative real constant. On A_b,

u(Q-n)/b² ≤ |u(Q-n)/b²| ≤ B.

The original `energyPathIntegrand b u` is zero outside A_b and between0 and exp(B) inside. Its existing public measurability head applies because b≥0. The integrable constant exp(B) under the actual probability μ_n dominates its absolute value. `Integrable.mono'` proves the new `energyPathIntegrand_integrable_pos` for every b>0, including b<1. This extends the usable finite interface without adding moments or invoking an untruncated MGF.

Now also assume h>0 and put u=s(b/h)². Both b and h are nonzero. The literal algebra

u(Q-n)/b²=s(Q-n)/h²,   (-u)(Q-n)/b²=-(s(Q-n)/h²)

follows by cancelling b² and h². Consequently the J integrand equals pointwise

(energyPathIntegrand b u + energyPathIntegrand b (-u))/2 - 1_(A_b).

Both exponential integrands are genuinely integrable by the newly proved finite helper. The indicator is measurable and integrable because μ_n is a probability measure. Addition, division by2 and subtraction therefore prove integrability of the J integrand BEFORE integral_add/sub are used. The constant-indicator integral equals μ_n.real(A_b), by the pinned integral_indicator_one API. Linearity gives the exact identity

J(ν,n,b,h,s)=(energyJointIntegral ν n b (s(b/h)²)
                 +energyJointIntegral ν n b (-(s(b/h)²)))/2-G(n,b).

This proves every conjunct of `energyCoshExcess_integrable_identity`. The imported energyJointIntegral is its actual transparent integral of the actual bounded-strip energyPathIntegrand; it is not a supplied conditional expectation or an abstract Laplace symbol.

## 3. One fixed pair of parameters dominates the whole window

Assume b,h,s>0, C≥1 and b≤Ch. Set c=b/h and Y_b=(Q-n)/b². Then 0<c≤C and 0≤c²≤C². Hence

|s c²Y_b|≤|s C²Y_b|,

even if Y_b is negative. Section1 proves pointwise

0≤F(s(Q-n)/h²)=F(s c²Y_b)≤F(s C²Y_b).

The left function, cut off by A_b, is integrable by Section2. For the right function use the genuinely integrable energyPathIntegrands at the two FIXED parameters ±sC² and the same integrable indicator, so it is integrable as well. Integral monotonicity and linearity therefore give

0≤J(ν,n,b,h,s)≤(I(ν,n,b,sC²)+I(ν,n,b,-sC²))/2-G(n,b),

where I is the actual energyJointIntegral. This proves `energyCoshExcess_le_fixed`. The proof does not apply E4 to s c_k², does not claim moving-parameter continuity, and does not need c_k to converge.

## 4. Finite Markov bound at the original h² threshold

Assume b,h,s,ε>0. Put D=F(sε)>0, as proved in Section1. Let

B=A_b∩{a: εh²<|Q(a)-n|}.

The strict energy event is measurable by measurable_energy and real continuous operations; so B is measurable. On B, positivity of s and h² gives sε<|s(Q-n)/h²|, whence D≤F(s(Q-n)/h²). Outside B, D1_B=0≤1_(A_b)F(s(Q-n)/h²). Thus the inequality holds pointwise, including the boundary |Q-n|=εh² (which is outside B) and every weak strip boundary.

The left indicator times D is integrable under the probability measure; the right function was proved integrable in Section2. Integrate and use the constant-indicator identity to obtain

D·μ_n.real(A_b∩{εh²<|Q-n|})≤J(ν,n,b,h,s).

This is `energy_deviation_finite_bound`, including its explicit D>0 conjunct. Neither G(n,b)>0 nor any moment assumption is needed. There is no division by G in the finite result. At n=0 the deviation event is empty, so it remains valid without an n>0 premise.

## 5. All selected radii have the original asymptotic scales

Fix C≥1 and any deterministic b:ℕ→ℝ such that h_k/2≤b_k≤Ch_k eventually. Intersect this tail with h_k>0, which follows from h→+∞. Then b_k>0 and C>0. On this common tail,

b_k≥h_k/2,
n_k/b_k²≥(n_k/h_k²)/C²,
0≤n_k/b_k³≤8(n_k/h_k³).

The first two lower comparison sequences tend to+∞ since2 and C² are fixed positive constants. For the third inequality, cube b_k≥h_k/2; both denominators are positive and n_k≥0, so division preserves the stated order. The upper bound tends to0 by the given short-scale limit; the lower bound is0. The eventual squeeze proves n_k/b_k³→0. This proves all three conjuncts of `selected_radius_scales`. No assumption on n at early indices, or even at a selected index, is inserted.

For arbitrary h satisfying the original scales, the all-index height condition of K is discharged as follows. Define proof-locally h'_k=if 0<h_k then h_k else1. It is positive at every index and eventually equals h because h→+∞. Therefore h', n/(h')² and n/(h')³ have the given limits by exact eventual equality. Apply the actual K producer with the constant row law ν, constant moment bound β=∫|x|³dν and h'. All its row probability, integrability, mean, second moment and common-third-moment hypotheses are the original ones or reflexivity. Transfer its G/m limit back along eventual equality h'=h. This proves `fixed_law_closedStrip_relative_asymptotic` without a public all-index positivity condition. The same construction applies to each selected b sequence. It does not alter n, ν, actual path events, or any accepted source file.

## 6. Selected-radius conditional excess tends to zero

For a selected b as in Section5, the actual E4 positivity producer gives G(n_k,b_k)>0 eventually. Apply the actual E4 Laplace producer TWICE, with radius sequence b and the two fixed real parameters p=sC² and -p. It gives I(n_k,b_k,p)/G(n_k,b_k)→1 and I(n_k,b_k,-p)/G(n_k,b_k)→1. Their arithmetic combination

U_k=(I(n_k,b_k,p)/G(n_k,b_k)+I(n_k,b_k,-p)/G(n_k,b_k))/2-1

tends to0. On the common tail of the selected interval, h>0 and G(n,b)>0, divide the finite comparison of Section3 by G and use the exact algebra G/G=1 to obtain

0≤J(ν,n_k,b_k,h_k,s)/G(n_k,b_k)≤U_k.

The eventual squeeze proves the quotient tends to0. This proves `selected_radius_energy_ratio_tendsto`. Every upper integral was known integrable before its algebraic use. Positivity precedes cancellation and division inequalities; early zero G or h is harmless because the proof uses a tail. This uses no law-ratio convergence, no radius-ratio convergence and no moving-parameter E4 extension.

## 7. The selection principle and exact uniform quantifiers

We prove a deterministic logical principle. Suppose h_k>0 eventually, C≥1, and for EVERY selected sequence b in the radius interval eventually, P(k,b_k) eventually. Define a single proof-local sequence β as follows, using classical choice:

* If there exists b with h_k/2≤b≤Ch_k and ¬P(k,b), choose such a bad b and set β_k to it.
* If no such b exists, set β_k=h_k.

At every index on the positive-height tail, β_k belongs to the radius interval: in the first case by its witness; in the second because h_k/2≤h_k≤Ch_k follows from h_k>0 and C≥1. Hence β is an admissible selected sequence. The assumed selected-sequence assertion gives P(k,β_k) on a tail. At each index of the intersection of these two tails there can be no bad witness, since a bad witness would put the definition in its first branch and give ¬P(k,β_k). Therefore at every such index P(k,b) holds for ALL b in the interval. This proves `eventually_forall_radius_of_selected`.

This argument explicitly defines a witness at every bad index. It needs neither a compactness subsequence nor a measurable selector: β is a deterministic real sequence chosen using the fixed law and index, not a function of the sampled path. It never asserts that not-eventually-P implies eventually-not-P. Equivalently any cofinal collection of violations is excluded, but no unproved cofinal reindexing lemma is being used.

For any δ>0, take P(k,b) to be the conjunction

G(n_k,b)>0;
|G(n_k,b)/m(n_k,b)-1|<δ;
0≤J(ν,n_k,b,h_k,s)/G(n_k,b)<δ.

For every admissible selected b, Section5 gives its scales. Section5's fixed-law K adapter gives the relative K limit and thus its absolute-error tail. The E4 positivity producer gives positivity. Section6 gives the upper excess tail, while Section2 nonnegativity divided by the eventually positive G gives its lower bound. Intersecting these finitely many tails establishes the selected-sequence premise of the logical principle. Applying it proves `uniform_closedStrip_energy_controls` with EXACT quantifiers

for each fixed C≥1, s>0 and δ>0, eventually in k, for EVERY real b with h_k/2≤b≤Ch_k, all displayed inequalities hold simultaneously.

The tail may depend on ν,h,n,C,s,δ; it may not depend on b. No actual supremum or new error sequence is needed or defined. This is stronger than the h≤b≤Ch version of the source(3). On G>0, true finite integral linearity also gives the actual conditional mean of cosh(s(Q-n)/h²) as 1+J/G. Its difference from1 is nonnegative, so its absolute value equals J/G. Thus the new public result has the exact intended conditional-energy meaning, rather than an unrelated abstract quotient.

## 8. A single-tail boundary ratio bound

Apply the main uniform result with s=1, δ=1/2, and intersect with h_k>0. The radius h_k itself belongs to the window. For each b in it put q_b=G(n_k,b)/m(n_k,b), and q_h=G(n_k,h_k)/m(n_k,h_k). The absolute-error bounds imply 1/2<q_b<3/2≤2 and 1/2<q_h. The literal m values are strictly positive because π>0 and exp is positive, at every finite argument. The main result also supplies both actual G values strictly positive.

Consequently q_b/q_h≤4, and exact cancellation gives

G(n_k,b)/G(n_k,h_k)=(q_b/q_h)(m(n_k,b)/m(n_k,h_k))
  ≤4 exp(λ(n_k/h_k²-n_k/b²)).

The exponential identity follows by cancelling the common positive4/π and using exp(a)/exp(c)=exp(a-c), followed by real ring/field algebra. This proves `uniform_closedStrip_boundary_ratio_bound` on ONE tail for every b in the window; it also includes explicit positivity of the denominator and each numerator. The proof is valid for b<h, where the exponent can be negative.

More generally uniform q_b→1 and q_h→1 imply the relative factor q_b/q_h→1 uniformly, recovering the source meaning of(4). No extra formal head for that elementary derived statement is proposed; the explicit factor4 bound is the direct middle-layer consumer interface.

## 9. Uniform concentration at εh²

Fix ε,δ>0 and put D=F(ε)>0. Apply `uniform_closedStrip_energy_controls` with s=1 and requested tolerance δD>0. On a common tail h>0, every radius in the window is positive and the actual G is positive. Apply Section4's finite bound at each such radius. Writing R_b for the literal joint strict-deviation event mass, it gives

D R_b/G_b≤J_b/G_b<δD.

Divide by D>0 to obtain R_b/G_b<δ. The ratio is nonnegative because a real measure is nonnegative and G_b>0. This proves `uniform_energy_concentration`, with the exact actual event A_b∩{|Q-n|>εh²}. The same one-tail statement holds for every radius; no moment stronger than the original absolute third moment entered.

## 10. Scope, finite-prefix cases and remaining obligations

The new unit eliminates bounded-radius uniformity of the actual K relative error and actual fixed-parameter E4 energy integral, supplies a literal finite Markov inequality, the factor4 actual boundary ratio bound, and original-h²-scale uniform concentration. A finite number of h≤0, h=0, n=0 or G=0 indices is never removed from the public object or assumptions; the asymptotic proofs only use tails where their needed signs have been derived. The finite Markov result itself permits n=0. There is no unannounced variance normalization, law replacement or strong moment assumption.

Downstream center inclusions, central exponent differences, growing middle-layer cover and summation, FAR transfer to actual G_h, the ε→0 squeeze, Brownian identification, E6 moving-boundary LLN/weak-limit branch and arbitrary-iid/variance transfer remain separate units. The public actual K and E4 modules must be fully qualified before this module enters implementation/Lean. A future fresh independent complete source-to-statement/proof review and exact-source server kernel/all-owned transitive-axiom receipt are still mandatory. Only propext, Classical.choice and Quot.sound are allowed. No mathematical novelty or original root closure is asserted.

This mathematical proof is complete for the proposed statements under the actual producer contracts. It is an author proof, not its own independent verification. Parent full reading and exact declaration freeze are the next step; this context stops proposal writes at the ready checkpoint and remains available for an explicitly authorized implementation follow-up.
