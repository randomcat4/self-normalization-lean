# Anonymous proof: truncated-energy normalization N0

Mathematical version N0-v1. Complete derivation of frozen-truncated-energy-v1.md, ready for independent mathematical verification. Lean implementation is not yet checked. This proof does not certify itself independently.

Source: oq4/energy01.md §E1, especially (1), (4), and its first-order normalization expansion. This is only the even-weight finite normalization subproblem N0, not all of E1.

## Objects and hypotheses

Let ν be any Borel probability measure on ℝ. Assume that x ↦ x² and x ↦ |x|³ are genuinely ν-integrable, and ∫x² dν = 1. Define the actual β = ∫|x|³ dν; its nonnegativity follows by integration. No centering, symmetry, first-moment integrability premise, fourth moment, bounded support, density, or exponential moment is imposed.

Let T ≥ 0, h ≥ 1 and |s| ≤ T. Write B = {x : |x| ≤ 2h}, D = {x : 2h < |x|}; thus D is exactly the complement of B, including the correct strictness at the truncation boundary. Define

w(x) = 1_B(x) exp(s x²/h²),
Z = ∫w dν,
C_Z(T) = 1/8 + T/2 + exp(4T) T².

All definitions are actual Borel functions and actual real integrals.

## 1. Measurability, sign and finite integrability of w

For arbitrary real h and s, B is Borel, x ↦ exp(s x²/h²) is continuous as a function of x, and its product with 1_B is Borel. This also covers h = 0, using the real field's totalized division in the definition. The exponential is positive on B and w = 0 off B, so w is nonnegative for every real h,s.

Under the admissible h ≥ 1, for x ∈ B one has 0 ≤ x²/h² ≤ 4. Consequently

−4T ≤ s x²/h² ≤ 4T.

It follows that on B, exp(−4T) ≤ w(x) ≤ exp(4T), and off B one has w(x)=0. In particular, 0 ≤ w ≤ exp(4T) globally. Since ν is a probability measure, the constant exp(4T) is integrable, hence w is genuinely integrable. There is no use of a nonintegrable real integral's default value.

At x = 0 and h ≥ 0 the weight is exactly one. At s = 0 the weight is exactly 1_B, so Z_{h,0} = ν.real B for arbitrary h; it is not assumed to equal one.

## 2. Four third-moment payments, with genuine integrability

The payments actually hold for every h > 0. Put u = |x| ≥ 0. On D, u > 2h and therefore

1 ≤ u³/(8h³),
u ≤ u³/(4h²),
u² ≤ u³/(2h).

On B one has u⁴ ≤ 2h u³, and x⁴ = u⁴. Off the corresponding sets the truncated functions are zero. Thus the following pointwise inequalities hold globally:

1_D ≤ |x|³/(8h³),
0 ≤ 1_D |x| ≤ |x|³/(4h²),
0 ≤ 1_D x² ≤ |x|³/(2h),
0 ≤ 1_B x⁴ ≤ 2h |x|³.

All three truncated moment functions are Borel. Each is dominated in absolute value by the displayed integrable scalar multiple of |x|³; hence each is genuinely integrable. The indicator 1_D is integrable because ν is finite. Integrate the pointwise inequalities, use the true indicator-mass identity and linearity for integrable functions, to obtain

ν.real D ≤ β/(8h³),
∫ 1_D |x| dν ≤ β/(4h²),
∫ 1_D x² dν ≤ β/(2h),
∫ 1_B x⁴ dν ≤ 2hβ.

These include all boundary atoms in B and none in D. No global fourth moment is needed for the final truncated fourth integral.

## 3. Uniform finite positive lower and upper bounds for Z

The lower bound uses the unit second moment rather than a smallness requirement on β. For any h > 0, the global pointwise estimate

1_D ≤ x²/(4h²)

implies ν.real D ≤ 1/(4h²). For h ≥ 1 this is at most 1/4. Since B and D are measurable complements in a probability space, ν.real B = 1−ν.real D ≥ 3/4.

The lower weight estimate from §1 gives

Z ≥ exp(−4T) ν.real B ≥ (3/4) exp(−4T).

The global upper estimate in §1 gives Z ≤ ∫exp(4T) dν = exp(4T). Both integral comparisons use already established genuine integrability. The lower bound is strictly positive because exp(−4T)>0, so positivity and finiteness of the actual normalizer are consequences, not hypotheses. This holds at h=1 with no restriction on the size of β.

## 4. Exact second-order exponential remainder

For real u with |u| ≤ 4T, Taylor's theorem at zero, applied to exp with its actual second derivative exp, gives

|exp(u)−1−u| ≤ (exp(4T)/2) u².

For u=0 this is equality. Otherwise the Lagrange remainder is exp(ξ)u²/2 for a ξ between 0 and u. Since T≥0 and ξ≤max(0,u)≤4T, exp(ξ)≤exp(4T), giving the stated constant. This argument works for negative u as well as positive u and does not assume a distributional exponential moment.

Define the Borel truncated remainder

r(x) = 1_B(x) [exp(s x²/h²)−1−s x²/h²].

The preceding pointwise Taylor bound implies

|r(x)| ≤ [exp(4T)s²/(2h⁴)] 1_B(x)x⁴.

The right side is nonnegative and genuinely integrable by §2; hence r and |r| are genuinely integrable. Integrating and applying the truncated fourth-moment payment gives

|∫r dν| ≤ ∫|r| dν
≤ [exp(4T)s²/(2h⁴)] (2hβ)
= exp(4T)s² β/h³
≤ exp(4T)T² β/h³.

The last step uses s²≤T², β≥0, and h>0. The exact factor 1/2 in the Taylor estimate cancels the factor 2h in the fourth-moment payment; no constant has been enlarged or suppressed.

## 5. Actual first-order normalizer expansion

There is the exact pointwise identity

w = (1−1_D) + (s/h²)(x²−1_D x²) + r.

Every term is genuinely integrable: constants/indicators by finiteness, x² by hypothesis, the truncated square by §2, and r by §4. Integrating, using ∫x²=1 and unit mass, yields

Z = 1−ν.real D + (s/h²)(1−∫1_D x² dν) + ∫r dν.

Therefore

|Z−1−s/h²|
≤ ν.real D + (|s|/h²) ∫1_D x² dν + |∫r dν|
≤ β/(8h³) + Tβ/(2h³) + exp(4T)T²β/h³
= C_Z(T) β/h³.

The second term uses the actual nonnegative truncated-square integral and |s|≤T, followed by β/(2h) from §2. The identity and all inequalities are valid at s=0 and T=0. Then the exponential remainder vanishes and the error estimate simply pays the omitted tail mass. In particular, no assertion Z_{h,0}=1 has entered the argument.

## Boundaries and scope

All inequalities quantify over the complete frozen domain. They retain h=1, T=0, s=0, atoms at ±2h and at zero, arbitrary unbounded support, and arbitrary nonsymmetric or noncentered ν. Auxiliary third-moment payments require only h>0; the final normalization statements retain h≥1. β is always the actual integral and is never replaced by a free upper-bound parameter or assumed to satisfy a new distributional condition.

Only N0 is proved. No normalized tilted measure, tilted mean, normalized moment or log Z estimate, E2 exact recentering, E3 path density, E4, BE/SP, K/Kv, energy denominator, or complete root theorem is supplied. All complete roots remain OPEN.
