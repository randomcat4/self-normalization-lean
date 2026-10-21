# Anonymous mathematical proof: reflected finite survival inputs

Status: complete mathematical derivation of the frozen reflected-survival-v1 interface; formal verification pending. This document does not certify itself independently.

## Objects and inputs

Let ν be any Borel probability measure on ℝ and ν⁻ = (x ↦ −x)₊ν. Write Π_t(ν) for the genuine finite product on paths a : Fin t → ℝ, T_k(a) for the public prefixSum, and M_t(a) = max(0,T_1(a),…,T_t(a)) for public maxWithZero. Let Φ be the actual CDF of Mathlib gaussianReal 0 1. Fix β ≥ 1 and C ≥ 0. The only CDF input is

|Π_t(ν){T_t/√t ≤ x} − Φ(x)| ≤ Cβ/√t    (t ≥ 1, x ∈ ℝ).

The two separate additional SP inputs, one for each λ ∈ {ν,ν⁻}, are exactly the original identities for every L > 0 and 0 < s < 1:

Σ_{j≥0} s^j E_{Π_j(λ)} exp(−M_j/L)
= exp(Σ_{k≥1} s^k E_{Π_k(λ)} exp(−max(T_k,0)/L)/k).

Their Lean expressions are laplaceG (maxLaplaceMean λ L) s = exp(laplaceW (endpointLaplaceMean λ L) s). They are inputs, not conclusions. No moment hypothesis is imposed here.

## 1. Reflection of the actual finite laws and events

Finite product pushforward under the coordinate maps x ↦ −x gives

Π_t(ν⁻) = (a ↦ −a)₊ Π_t(ν)

for every natural t. This is the finite product map theorem, also valid when Fin t is empty. Both ν⁻ and every product are probability measures. Prefix sums obey T_k(−a) = −T_k(a) for every k, with no restriction k ≤ t needed for this algebraic identity.

The public upper event is U_t(d) = {a : ∀ k ≤ t, T_k(a) ≤ d}. The existing lowerBlockSurvival event is L_t(d) = {a : −a ∈ U_t(d)}. Therefore the reflection preimages are exactly

neg⁻¹ U_t(d) = L_t(d),   neg⁻¹ L_t(d) = U_t(d).

Expanding prefixSum_neg also gives L_t(d) = {a : ∀ k ≤ t, −d ≤ T_k(a)}. The quantifier includes k = 0; no event is killed at time zero. All inequalities are closed, so atoms and equality endpoints remain. Both events are Borel by the previously accepted measurable-event lemmas. Consequently Π_t(ν⁻)(U_t(d)) = Π_t(ν)(L_t(d)); the symmetric lower-to-upper identity holds as well. The statements include t = 0 and arbitrary d.

## 2. The actual Gaussian reflection and a strict-CDF limit

Put γ = gaussianReal 0 1. Its pushforward under negation equals itself, by the Gaussian affine-map theorem. Its positive variance implies every singleton has zero γ-mass. Thus

Φ(−x) = γ(−∞,−x] = γ[x,∞) = γ(x,∞) = 1 − Φ(x).

Only the comparison Gaussian is atomless; ν is not assumed atomless.

For a general probability P and real function X, suppose |P(X ≤ u) − Φ(u)| ≤ ε for every u. Let p = P(X < x). Monotonicity gives p ≤ P(X ≤ x) ≤ Φ(x)+ε. For each δ > 0,

P(X < x) ≥ P(X ≤ x−δ) ≥ Φ(x−δ)−ε ≥ Φ(x)−δ−ε,

where the final bound follows from the already proved global 1-Lipschitz property of Φ. Letting δ decrease to zero yields p ≥ Φ(x)−ε. This limit is an elementary order limit of inequalities, not an identification of strict and non-strict events. Hence |P(X < x)−Φ(x)| ≤ ε with the same constant, regardless of atoms of X.

For fixed t ≥ 1, X = T_t/√t is measurable. Product reflection and √t > 0 give

Π_t(ν⁻){X ≤ x} = Π_t(ν){−X ≤ x}
= 1 − Π_t(ν){X < −x}.

Using the strict-CDF estimate at −x and Φ(−x)=1−Φ(x), the reflected CDF error is exactly the negative of the strict-CDF error. Its absolute value is at most Cβ/√t. Therefore the same complete CDF premise holds for ν⁻ with the same β and C; no second BE premise has been added.

## 3. Both actual one-sided survival probabilities

The accepted FiniteSurvivalLaplace theorem applies to ν with the displayed CDF premise and ν's original SP. It yields, for every t ≥ 1 and d ≥ 0,

Π_t(ν)(U_t(d)) ≤ √2 exp(6+3C) (d+β)/√t.

Apply that same theorem to ν⁻, using the CDF premise just proved and the separately supplied original SP for ν⁻. The reflection identity converts its upper-event probability exactly to Π_t(ν)(L_t(d)), with the identical upper bound. Together these are the existing iidOneSidedSurvival ν β Cs predicate, where Cs = √2 exp(6+3C). No antitone, summability, normalized SP identity, or survival assertion is supplied as a premise: those analytic steps are derived inside the accepted FiniteSurvivalLaplace theorem.

## 4. Actual closed unit-interval concentration without moments

Fix t ≥ 1, r = √t > 0, X = T_t/r, and let μ = X₊Π_t(ν). This is a probability law. Its CDF satisfies the given error ε = Cβ/r relative to the actual globally 1-Lipschitz Φ. For any a ∈ ℝ the accepted arbitrary-law closed-interval CDF theorem, including the left atom, gives

Π_t(ν){a ≤ T_t ≤ a+1}
= μ[a/r,(a+1)/r]
≤ 1/r + 2Cβ/r
≤ (1+2C)β/r.

The last step is exactly β ≥ 1. We do not call the high-level moment-based concentration theorem, and β is not identified with any integral. Hence the result is precisely the existing iidIntervalConcentration ν β Cq predicate for Cq = 1+2C.

## 5. Constants, joint output, and scope

C ≥ 0 implies Cq ≥ 0. The square root √2 is nonnegative and the exponential is positive, so Cs ≥ 0. The joint result returns these two nonnegativity facts and the two genuine existing probability predicates, with expanded hypotheses exactly the sole ν-CDF premise and the two original SP premises.

No step assumes a fourth moment, any moment, bounded support, a density, nonlattice structure, symmetry of ν, or independence after conditioning on survival. Product reflection and event identities are valid at t = 0; final survival and concentration conclusions explicitly quantify t ≥ 1. Values d = 0, t = 1, all-zero paths, atoms, and closed endpoint equalities are retained. SP and BE themselves, unconditional S/AC/O0, B1, long-time K/Kv, the energy denominator, and complete OQ4 remain OPEN.
