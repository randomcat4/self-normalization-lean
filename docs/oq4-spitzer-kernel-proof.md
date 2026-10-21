# Anonymous proof: explicit BE and two original SP inputs imply finite killed-kernel absorption

Status: complete mathematical derivation for frozen-spitzer-kernel-bounds-v1; formal verification pending. No independent certification is claimed here.

## Objects and exact hypotheses

Let ν be any Borel probability measure on ℝ. Assume id, y², and |y|³ are genuinely integrable under ν; EνY = 0 and EνY² = 1. Define the actual β = ∫|y|³ dν. Fix M ≥ 0 with β ≤ M, and C_BE ≥ 0. The sole BE premise is the all-positive-integer-time CDF estimate for the genuine product law:

|Π_t(ν){prefixSum a t / √t ≤ x} − standardNormalCDF x| ≤ C_BE β/√t,

for every t ≥ 1 and x ∈ ℝ. Independently assume the two original SP identities for ν and reflectedLaw ν, each for every L > 0 and 0 < s < 1:

laplaceG (maxLaplaceMean λ L) s = exp(laplaceW (endpointLaplaceMean λ L) s).

The two measures λ are ν and reflectedLaw ν. This is the original identity, not the normalized equivalent formula. There is no separate BE premise for reflectedLaw ν and no S, AC, O0, R3, R4, monotonicity, summability, B1, or desired absorption assertion in the hypotheses.

Set

Cq = 1 + 2 C_BE,
Cs = √2 exp(6 + 3 C_BE),
Clayer = 12 Cq Cs M(1 + M),
E = π³M/48 + 2π Clayer(1 + 2M).

The constants Cq and Cs depend only on C_BE. The constants Clayer and E depend only on C_BE and M. These are not claimed to be unconditional universal numerical constants.

All kernel objects below are the accepted actual killed kernel, its genuine powers and integrals: killedIterKernel, killedAction, killedMass, cosineResidual, principalCosine, normalizedKernelMass and normalizedKernelCosine. No abstract sequences are substituted for them.

## 1. Actual moment parameter and actual probability inputs

For u = |y| ≥ 0, (u−1)²(2u+1) ≥ 0 is exactly 3u² ≤ 2u³+1. Integrating is legitimate by the explicit square and cube integrability hypotheses. Unit total mass and E Y² = 1 imply 3 ≤ 2β+1, hence β ≥ 1. This is exactly the accepted third_absolute_moment_ge_one theorem. The mean-zero and first-moment hypotheses are retained for the later true residual and absorption theorems; they are not needed for this inequality.

Apply the accepted ReflectedSurvival joint theorem at this actual β. Its own reflection proof obtains the reflected-law BE bound from the sole ν-BE premise, preserving atoms by a strict-CDF cutoff limit and actual Gaussian reflection. Its two applications of FiniteSurvivalLaplace use the separately supplied original SP identities. Its direct closed-CDF argument derives concentration without adding moments. Therefore it returns

0 ≤ Cs, 0 ≤ Cq,
iidOneSidedSurvival ν β Cs,
iidIntervalConcentration ν β Cq.

This is the accepted actual parameter order ν, β, C. Expanding the predicates yields exactly all t ≥ 1, d ≥ 0 closed upper/lower survival estimates Cs(d+β)/√t, and all t ≥ 1, x ∈ ℝ closed unit-interval mass estimates Cqβ/√t. No extra event interface is introduced.

## 2. Actual R3 and R4 for the square-height block

Fix h ≥ 3 and a closed-domain start |z| ≤ h. Put m = floor(h²), a natural integer. The accepted KilledBlockBounds theorem has precisely the complete moment, centering, M, and nonnegative-constant assumptions above, plus the two actual predicates just supplied internally. Apply killed_block_residual_bound with Cq and Cs. It returns true integrability of

w ↦ |cosineResidual ν (π/(2h)) h w|

under the actual row (killedIterKernel ν h m) z, and the actual integral estimate

killedAction ν h m (|cosineResidual ν (π/(2h)) h|) z ≤ E/h³.

Its parameter constant killedResidualConstant M Cq Cs unfolds exactly to E, including killedLayerConstant = Clayer. No arithmetic enlargement or alteration of constants is involved. Parameter measurability is already provided by the accepted principalResidual_measurable theorem; taking absolute values preserves measurability. Thus the displayed residual remains an actual Borel function and a genuine row-integrable integrand.

Apply killed_block_mass_bound with the actual β, using β ≥ 1 to supply β ≥ 0 and β ≤ M unchanged. It yields

killedMass ν h m z ≤ 2Cs principalCosine h z + (2CsM)/h.

The accepted proof uses the true killed path representation, a sign-selected one-sided event, and the cosine chord only on |z| ≤ h. Its square-height block and floor endpoints are already handled; no cosine nonnegativity on the whole real line is assumed. Hence the module internally supplies both actual R3 and actual R4.

## 3. Finite noncircular absorption

Add π(1+M) ≤ h and N ≥ m, with N natural. Set R = exp(π²) and H = 2(1+(2Cs)R)R. Assume exactly the explicit numerical smallness condition

((2Cs)R)(E R/h³) N + (2CsM)R/h ≤ 1/2.

The accepted killed_block_finite_absorption theorem has exactly these hypotheses after supplying the two actual probability predicates. Its residual constant unfolds identically to E, so the smallness premise is definitionally the same expression. Apply it without weakening or strengthening that premise. It returns, simultaneously,

0 ≤ normalizedKernelMass ν h k z ≤ H          for every natural k ≤ N,

and

|normalizedKernelCosine ν h k z − normalizedKernelCosine ν h m z|
≤ (E R/h³) ((k−m : ℕ) : ℝ) H                whenever m ≤ k ≤ N.

The mass statement includes k = 0. The cosine increment includes k = m; natural subtraction is taken before coercion to ℝ. The case N = m is retained. The inherited finite absorption proof obtains the bound from true kernel initial data and a finite maximum argument; this wrapper assumes no uniform normalized-mass bound, no R3/R4 block premise, and no desired conclusion. All coefficient enlargements, positivity requirements, and inverse-power controls are inherited from that accepted theorem with precisely the displayed constants.

## Scope and endpoints

The old modules are used without any source modification. All integrals in the hypotheses and R3 conclusion are genuine integrals with explicit integrability. The closed source domain |z| ≤ h includes its endpoints, all one-sided and interval predicates retain atoms/equalities, and no density, bounded-support, fourth-moment, lattice, symmetry, or survival-conditioned independence hypothesis is added. β remains the actual third absolute moment in every exported wrapper, not a free surrogate parameter.

This closes only the finite source-bound BE/two-SP → actual S/AC → actual R3/R4 → finite D8 chain. It proves neither external BE nor either SP, Brownian B1, long-time limits, 4/π, K/Kv, energy results E1–E6, nor complete OQ4. All complete roots remain OPEN.
