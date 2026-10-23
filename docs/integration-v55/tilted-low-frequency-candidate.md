# Joint quadratic tilt: second moments and actual low-frequency powers

State: `CANDIDATE_COMPLETE_AWAITING_ROOT_FREEZE`.
Author: `/root/common_tilted_low_author`, actual model `gpt-6.1-sol`, effort `xhigh`.
This file contains two complete proposed public heads and zero new global
definitions. It is not production Lean and has not been elaborated or checked.
Root owns declaration freeze. No implementation starts before that freeze.

Proposed module: `Shao.Probability.TiltedLowFrequency`.

Proposed imports and namespace context:

```lean
import Shao.Probability.BoundedQuadraticTilt
import Shao.Probability.LowFrequencyDamping
import Shao.Probability.SourceFourierScale

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
```

The source-law corollary below uses the literal remaining clock
`N = q + ((n - i : ℕ) : ℝ) * m2`. Its moment and support inputs come from the
actual conditional law; none is a supplied tilted moment or decay conclusion.
The low-frequency outputs require no `(y + lam) * Gamma` smallness. That
smallness appears only as the antecedent of the mean/variance comparison.

## 1. Generic joint-law producer

The three base moment bounds are the source-scale payments. The only signed
mean input is a bound on its absolute value; its value is not required to be
zero. All moment quantities in the head are actual integrals.

```lean
theorem boundedQuadraticTilt_joint_second_moments_lowFrequency
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (n : ℕ) (h lam b s y : ℝ)
    (hh : 0 < h) (hlam : 0 ≤ lam)
    (hb : b = lam ∨ b = -lam)
    (hs : 0 ≤ s) (hsquare : s ≤ lam ^ 2)
    (hslope : s * h ≤ lam)
    (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (hy : 2 ≤ y)
    (hnV : (1 / 2 : ℝ) ≤
      (n : ℝ) * variance (id : ℝ → ℝ) nu)
    (hnm2 : (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂nu) ≤ (4 / 3 : ℝ))
    (hnmu : (n : ℝ) * |∫ a : ℝ, a ∂nu| ≤ (1 / 2 : ℝ)) :
    let rho : Measure ℝ := nu.tilted (fun a => b * a - s * a ^ 2)
    let mu : ℝ := ∫ a : ℝ, a ∂nu
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂nu
    let V : ℝ := variance (id : ℝ → ℝ) nu
    let gamma : ℝ := m3 / V
    let murho : ℝ := ∫ a : ℝ, a ∂rho
    let m2rho : ℝ := ∫ a : ℝ, a ^ 2 ∂rho
    let m3rho : ℝ := ∫ a : ℝ, |a| ^ 3 ∂rho
    let Vrho : ℝ := variance (id : ℝ → ℝ) rho
    let Gamma : ℝ := 8 * Real.exp (8 * lam * h) * gamma
    IsProbabilityMeasure rho ∧
      (∀ᵐ a : ℝ ∂rho, |a| ≤ h) ∧
      Integrable (fun a : ℝ => a) rho ∧
      Integrable (fun a : ℝ => a ^ 2) rho ∧
      Integrable (fun a : ℝ => |a| ^ 3) rho ∧
      0 < V ∧ 0 < Vrho ∧ 0 < Gamma ∧
      Real.exp (-(4 * lam * h)) * V ≤ Vrho ∧
      Vrho ≤ Real.exp (4 * lam * h) * V ∧
      m3rho / Vrho ≤ Gamma ∧
      Real.sqrt m2rho ≤ Gamma ∧ m2rho ≤ Gamma ^ 2 ∧
      ((y + lam) * Gamma ≤ (1 / 8 : ℝ) →
        |murho| ≤ Real.sqrt Vrho ∧ murho ^ 2 ≤ Vrho ∧
          Vrho ≤ m2rho ∧ m2rho ≤ 2 * Vrho) ∧
      (∀ (ell : ℕ) (u v : ℝ),
        |u| ≤ (1 / 128 : ℝ) / Gamma →
        |v| ≤ (1 / 128 : ℝ) * |u| / Gamma →
        ‖(quadraticChar rho u v) ^ ell‖ ≤
            Real.exp (-Real.exp (-(4 * lam * h)) *
              ((ell : ℝ) * m2) * u ^ 2 / 128) ∧
          ‖(quadraticChar rho (-u) v) ^ ell‖ ≤
            Real.exp (-Real.exp (-(4 * lam * h)) *
              ((ell : ℝ) * m2) * u ^ 2 / 128))
```

## 2. Original conditional law and original remaining clock

The threshold window is the literal original half-window. The explicit
`hyh` is the numerical realization of original "sufficiently small yh";
it pays `s * h ≤ lam` even when `lam * h` is large. The budget bound is the
original `R ≤ epsilon³/8`. The stronger original `eta` bound is not needed
for this unit's base mean payment.

```lean
theorem sourceTruncation_jointTilt_second_moments_lowFrequency
    (nu0 : Measure ℝ) [IsProbabilityMeasure nu0] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu0)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu0) = 1)
    (hmean : (∫ z : ℝ, z ∂nu0) = 0)
    (x epsilon epsilon0 : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilon0 : 0 < epsilon0)
    (hepsilon0One : epsilon0 ≤ 1)
    (hepsilonSmall : epsilon ≤ epsilon0 / 2)
    (hR : Shao.truncationBudget nu0 n x ≤ epsilon ^ 3 / 8)
    (y : ℝ) (hy : 2 ≤ y)
    (hwindow : |y - x| ≤ 1 / (2 * (1 + x)))
    (hyh : y * (epsilon0 / (1 + y)) ≤ (1 / 4 : ℝ))
    (i : ℕ) (hi : i ≤ n) (q : ℝ) (hq : 0 ≤ q)
    (hNlo : (1 / 16 : ℝ) ≤ q + ((n - i : ℕ) : ℝ) *
      (∫ z : ℝ, z ^ 2 ∂ProbabilityTheory.cond nu0
        {z : ℝ | |z| ≤ epsilon / (1 + x)}))
    (hNhi : q + ((n - i : ℕ) : ℝ) *
      (∫ z : ℝ, z ^ 2 ∂ProbabilityTheory.cond nu0
        {z : ℝ | |z| ≤ epsilon / (1 + x)}) ≤ 7)
    (lam b s : ℝ)
    (hlam : y / Real.sqrt (q + ((n - i : ℕ) : ℝ) *
      (∫ z : ℝ, z ^ 2 ∂ProbabilityTheory.cond nu0
        {z : ℝ | |z| ≤ epsilon / (1 + x)})) ≤ lam)
    (hb : b = lam ∨ b = -lam)
    (hschoice : s = 0 ∨ s = lam * y / Real.sqrt
      (q + ((n - i : ℕ) : ℝ) *
        (∫ z : ℝ, z ^ 2 ∂ProbabilityTheory.cond nu0
          {z : ℝ | |z| ≤ epsilon / (1 + x)}))) :
    let nu : Measure ℝ := ProbabilityTheory.cond nu0
      {z : ℝ | |z| ≤ epsilon / (1 + x)}
    let h : ℝ := epsilon0 / (1 + y)
    let mu : ℝ := ∫ a : ℝ, a ∂nu
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂nu
    let V : ℝ := variance (id : ℝ → ℝ) nu
    let gamma : ℝ := m3 / V
    let T : ℝ := ((n - i : ℕ) : ℝ) * m2
    let N : ℝ := q + T
    let rho : Measure ℝ := nu.tilted (fun a => b * a - s * a ^ 2)
    let murho : ℝ := ∫ a : ℝ, a ∂rho
    let m2rho : ℝ := ∫ a : ℝ, a ^ 2 ∂rho
    let m3rho : ℝ := ∫ a : ℝ, |a| ^ 3 ∂rho
    let Vrho : ℝ := variance (id : ℝ → ℝ) rho
    let Gamma : ℝ := 8 * Real.exp (8 * lam * h) * gamma
    IsProbabilityMeasure nu ∧ IsProbabilityMeasure rho ∧
      0 < h ∧ epsilon / (1 + x) ≤ h ∧
      (∀ᵐ a : ℝ ∂nu, |a| ≤ h) ∧
      (∀ᵐ a : ℝ ∂rho, |a| ≤ h) ∧
      0 ≤ lam ∧ 0 ≤ s ∧ s ≤ lam ^ 2 ∧ s * h ≤ lam ∧
      0 ≤ T ∧ T ≤ (4 / 3 : ℝ) ∧ (1 / 16 : ℝ) ≤ N ∧ N ≤ 7 ∧
      (3 / 4 : ℝ) ≤ (n : ℝ) * m2 ∧
      (n : ℝ) * m2 ≤ (4 / 3 : ℝ) ∧
      (1 / 2 : ℝ) ≤ (n : ℝ) * V ∧
      (n : ℝ) * |mu| ≤ epsilon / (4 * (1 + x)) ∧
      (n : ℝ) * |mu| ≤ (1 / 2 : ℝ) ∧
      0 < V ∧ 0 < Vrho ∧ 0 < gamma ∧ 0 < Gamma ∧
      gamma ≤ y ∧
      Integrable (fun a : ℝ => a) rho ∧
      Integrable (fun a : ℝ => a ^ 2) rho ∧
      Integrable (fun a : ℝ => |a| ^ 3) rho ∧
      Real.exp (-(4 * lam * h)) * V ≤ Vrho ∧
      Vrho ≤ Real.exp (4 * lam * h) * V ∧
      m3rho / Vrho ≤ Gamma ∧
      Real.sqrt m2rho ≤ Gamma ∧ m2rho ≤ Gamma ^ 2 ∧
      ((y + lam) * Gamma ≤ (1 / 8 : ℝ) →
        |murho| ≤ Real.sqrt Vrho ∧ murho ^ 2 ≤ Vrho ∧
          Vrho ≤ m2rho ∧ m2rho ≤ 2 * Vrho) ∧
      (∀ u v : ℝ,
        |u| ≤ (1 / 128 : ℝ) / Gamma →
        |v| ≤ (1 / 128 : ℝ) * |u| / Gamma →
        ‖(quadraticChar rho u v) ^ (n - i)‖ ≤
            Real.exp (-Real.exp (-(4 * lam * h)) * T * u ^ 2 / 128) ∧
          ‖(quadraticChar rho (-u) v) ^ (n - i)‖ ≤
            Real.exp (-Real.exp (-(4 * lam * h)) * T * u ^ 2 / 128))
```

Namespace closes with `end Shao.Probability`.

The complex powers above are exactly the original modulus powers, by
`norm_pow`. The two signs cover the frequency signs for either allowed drift
sign `b`. The `ell = 0` / `i = n` case is included and has both sides equal to
one. No lower bound on `T / gamma²` is needed for this damping-only result.

The source bounds `q ≥ 0`, `N ≤ 7`, and `i ≤ n` preserve the original clock
context; `N ≤ 7` is not used in the two elementary `s` payments. There is no
claim of contour shifts, derivative amplitudes, survival, second regulator
moments, desmoothing, or root C1/C2 closure.
