# Root exact declaration freeze: actual whole-line odd/even twice IBP

Root has fully read the two complete proposed declarations, the complete contract, and read-only supplement.tex LF2350–2367 and LF2570–2583. Production is authorized only in new Shao/Probability/SourceOddEvenWholeLineIBP.lean by the current high-frequency author. Preserve all displayed hypotheses, actual D/W factors, nested standard real derivatives, all natural m including zero, every v, and both signs of a. No silent premise or conclusion changes. No supplied decay/regularity/IBP hypotheses. Pinned Lean/mathlib and the existing root heavy lock/resource lease apply.

This closes the actual full-real-line identity only. Actual marked-pair Fubini/amplitude substitution and regional/source probability consumers are subsequent dependencies. Complete final independent source/proof/all-owned actual-type/value semantic review and exact server kernel/transitive-axiom evidence are required once; qualified evidence and unchanged dependencies are reused.

Candidate SHA256: 05529e5474b849116d4d4d05dcc7dcaeb4c738c9352f238e3c6030d63d7a6c11
Contract SHA256: 123e403ce3f7a3e307e9cf1a83721b3331e587c8257ddf44da783176ee619929

# Actual D and uE: whole-line twice integration by parts

Status: CANDIDATE_PENDING_ROOT_FREEZE. Proposed new module Shao/Probability/SourceOddEvenWholeLineIBP.lean. Exactly two public theorems, no new public definitions.

```lean
namespace Shao.Probability

open MeasureTheory ProbabilityTheory

theorem quadraticFullNoise_odd_wholeLine_twiceIBP
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (m : ℕ) (v : ℝ) :
    let D : ℝ → ℂ := fun u =>
      ((quadraticChar ν u v) ^ m - (quadraticChar ν (-u) v) ^ m) / 2 *
        quadraticFullNoiseChar ν u v
    Differentiable ℝ D ∧ Differentiable ℝ (fun u : ℝ => deriv D u) ∧
      Integrable D ∧ Integrable (fun u : ℝ => deriv D u) ∧
      Integrable (fun u : ℝ => deriv (fun t : ℝ => deriv D t) u) ∧
      ∀ a : ℝ, a ≠ 0 →
        Integrable (fun u : ℝ => (Real.sin (a * u) : ℂ) * D u) ∧
        Integrable (fun u : ℝ => (Real.sin (a * u) : ℂ) *
          deriv (fun t : ℝ => deriv D t) u) ∧
        (∫ u : ℝ, (Real.sin (a * u) : ℂ) * D u) =
          -(((a ^ 2 : ℝ) : ℂ)⁻¹) *
            ∫ u : ℝ, (Real.sin (a * u) : ℂ) * deriv (fun t : ℝ => deriv D t) u

theorem quadraticFullNoise_even_wholeLine_twiceIBP
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (m : ℕ) (v : ℝ) :
    let E : ℝ → ℂ := fun u =>
      ((quadraticChar ν u v) ^ m + (quadraticChar ν (-u) v) ^ m) / 2 *
        quadraticFullNoiseChar ν u v
    let W : ℝ → ℂ := fun u => (u : ℂ) * E u
    Differentiable ℝ W ∧ Differentiable ℝ (fun u : ℝ => deriv W u) ∧
      Integrable W ∧ Integrable (fun u : ℝ => deriv W u) ∧
      Integrable (fun u : ℝ => deriv (fun t : ℝ => deriv W t) u) ∧
      ∀ a : ℝ, a ≠ 0 →
        Integrable (fun u : ℝ => (Real.sin (a * u) : ℂ) * W u) ∧
        Integrable (fun u : ℝ => (Real.sin (a * u) : ℂ) *
          deriv (fun t : ℝ => deriv W t) u) ∧
        (∫ u : ℝ, (Real.sin (a * u) : ℂ) * W u) =
          -(((a ^ 2 : ℝ) : ℂ)⁻¹) *
            ∫ u : ℝ, (Real.sin (a * u) : ℂ) * deriv (fun t : ℝ => deriv W t) u

end Shao.Probability
```

The sine-weighted integrability is explicit at the actual consumer boundary. The standard nested derivatives are of the true displayed D and W=uE. No freely supplied regularity, Fourier L1, endpoint decay, or integration-by-parts identity is assumed. The all-m/v statement includes m=0; a may be either sign and is only excluded at0 because the source divides by its square.

# Source contract: actual whole-line u integration by parts

Read-only source: C:/game/shao/current/c12/supplement.tex LF2575–2583, using actual D and E from LF2354–2366 and the actual scalar-noise construction. The source asserts the full-real-line identity int sin(a*u) F = -a^-2 int sin(a*u) partial_u^2 F for F=D or F=uE. Its justification is rapid u decay from the smooth scalar noise. The proposed two declarations prove exactly these actual factors, their true first/nested second derivative regularity and absolute integrability, then the identity for every nonzero real a.

Inputs are the already used genuine probability law, actual finite third moment, positive actual variance and bounded original increment support. All remaining-length exponents m and every v are retained; no symmetric or mean-zero increment assumption is added. The actual gamma=(int|x|^3)/variance is positive, proved from the actual moments and positive variance. It is not a free scale and no extra gamma<=2h is assumed.

Payment route: Xi=K(u,v)^8*K(-u,v)^8*sourceScalarChar(gamma*u). The genuine compact smooth scalar density and its x and x^2 multiples have Schwartz Fourier transforms; this pays polynomially weighted L1 of the scalar factor and both of its standard derivatives. Bounded-law raw signed powers and actual chord characteristic factors have genuine bounded first and second derivatives, proved from their finite first/second spatial moments. Product differentiation then pays actual D,D',D'' and uE,(uE)',(uE)'' L1, including m=0. The scalar route reuses accepted actual scalar derivative identities and pinned Schwartz Fourier APIs; it does not assume decay of D or uE.

Pinned Mathlib integral_mul_deriv_eq_deriv_mul_of_integrable (IntegralEqImproper.lean LF1369) derives vanishing boundary terms from genuine product L1 hypotheses. Applying it to sin(a*u),F' and cos(a*u),F proves the exact negative inverse-square coefficient. No supplied limits at either infinity appear.

This unit does not claim the five-region estimates, the source amplitude family, positive-phase lower bounds or the final probability/C1/C2 theorem. Those remain distinct consumers. The source substitution a=y*sqrt(r)+/-w and the bound a>=3y/16 on actual cutoff support are paid downstream with y>0 and |w|<=y/16, not silently required here. The region3/5 and amplitude producer are owned by another author and are not edited.
