# Complex chord extension: complete candidate declarations

Status: CANDIDATE, not frozen by root, not implemented, not kernel checked, not independently reviewed. Author: `/root/common_complex_chord_author`, prescribed `gpt-6.1-sol` / `xhigh`. Production write authority has not been granted. Only this draft directory is owned.

This candidate has two new definitions and three substantive public theorem heads. The definitions extend the existing actual noise laws; they do not replace either law. Every new global definition value is written below. Additional global definitions, including private definitions, require a root addendum before implementation. Proof-local `let`s may name their full literal values.

Proposed module: `Shao/Probability/QuadraticComplexChord.lean`.

```lean
import Shao.Probability.QuadraticFullNoise
import Shao.Probability.BoundedQuadraticTilt
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Trigonometric

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

noncomputable def quadraticChordCharComplex (nu : Measure ℝ) (z w : ℂ) : ℂ :=
  ∫ p : ℝ × ℝ,
    Complex.exp ((z * (p.1 : ℂ) + w * (p.2 : ℂ)) * Complex.I)
    ∂quadraticChordLaw nu

noncomputable def quadraticFullNoiseCharComplex (nu : Measure ℝ) (z w : ℂ) : ℂ :=
  ∫ p : ℝ × ℝ,
    Complex.exp ((z * (p.1 : ℂ) + w * (p.2 : ℂ)) * Complex.I)
    ∂quadraticFullNoiseLaw nu

theorem complex_cosine_chord_bound (a b : ℝ) :
    ‖1 - Complex.cos ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
      2 * Real.exp |b| * (1 - Real.cos a + b ^ 2)

theorem quadraticComplexChord_extension_and_cone
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (h : ℝ) (hh : 0 < h)
    (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h) :
    let V : ℝ := variance (id : ℝ → ℝ) nu
    let gamma : ℝ := (∫ a : ℝ, |a| ^ 3 ∂nu) / V
    let Q : ℂ → ℂ → ℝ × ℝ → ℂ := fun z w p =>
      if z + w * ((p.1 + p.2 : ℝ) : ℂ) = 0 then
        (((p.1 - p.2) ^ 2 / 2 : ℝ) : ℂ)
      else
        (1 - Complex.cos (((p.1 - p.2 : ℝ) : ℂ) *
          (z + w * ((p.1 + p.2 : ℝ) : ℂ)))) /
          (z + w * ((p.1 + p.2 : ℝ) : ℂ)) ^ 2
    let S : ℂ → ℂ := fun z =>
      ∫ t : ℝ, Complex.exp
        ((gamma : ℂ) * z * (t : ℂ) * Complex.I) ∂sourceScalarLaw
    IsProbabilityMeasure (quadraticChordLaw nu) ∧
      IsProbabilityMeasure (quadraticFullNoiseLaw nu) ∧
      Differentiable ℂ (fun p : ℂ × ℂ =>
        quadraticChordCharComplex nu p.1 p.2) ∧
      Differentiable ℂ (fun p : ℂ × ℂ =>
        quadraticFullNoiseCharComplex nu p.1 p.2) ∧
      (∀ z w : ℂ,
        Integrable (fun p : ℝ × ℝ =>
          Complex.exp ((z * (p.1 : ℂ) + w * (p.2 : ℂ)) * Complex.I))
          (quadraticChordLaw nu) ∧
        Integrable (Q z w) (nu.prod nu) ∧
        quadraticChordCharComplex nu z w =
          (∫ p : ℝ × ℝ, Q z w p ∂nu.prod nu) / (V : ℂ) ∧
        ‖quadraticChordCharComplex nu z w‖ ≤
          Real.exp (2 * h * |z.im| + 4 * h ^ 2 * |w.im|) ∧
        Integrable (fun p : ℝ × ℝ =>
          Complex.exp ((z * (p.1 : ℂ) + w * (p.2 : ℂ)) * Complex.I))
          (quadraticFullNoiseLaw nu) ∧
        Integrable (fun t : ℝ => Complex.exp
          ((gamma : ℂ) * z * (t : ℂ) * Complex.I)) sourceScalarLaw ∧
        ‖S z‖ ≤ Real.exp (|gamma| * |z.im|) ∧
        quadraticFullNoiseCharComplex nu z w =
          quadraticChordCharComplex nu z w ^ 8 *
          quadraticChordCharComplex nu (-z) w ^ 8 * S z) ∧
      (∀ u v : ℝ,
        quadraticChordCharComplex nu (u : ℂ) (v : ℂ) =
          quadraticChordChar nu u v ∧
        quadraticFullNoiseCharComplex nu (u : ℂ) (v : ℂ) =
          quadraticFullNoiseChar nu u v) ∧
      ∀ lam b s : ℝ, 0 ≤ lam → (b = lam ∨ b = -lam) →
        0 ≤ s → s ≤ lam ^ 2 → s * h ≤ lam →
        let rho : Measure ℝ := nu.tilted (fun a => b * a - s * a ^ 2)
        IsProbabilityMeasure rho ∧
          ∀ u v : ℝ, u ≠ 0 → |v| ≤ |u| / (4 * h) →
            let theta : ℝ × ℝ → ℂ := fun p =>
              (u : ℂ) - (b : ℂ) * Complex.I +
              ((v : ℂ) + (s : ℂ) * Complex.I) *
                ((p.1 + p.2 : ℝ) : ℂ)
            (∀ᵐ p : ℝ × ℝ ∂nu.prod nu,
              |u| / 2 ≤ ‖theta p‖ ∧ theta p ≠ 0) ∧
            ‖quadraticChordCharComplex nu
                ((u : ℂ) - (b : ℂ) * Complex.I)
                ((v : ℂ) + (s : ℂ) * Complex.I)‖ ≤
              144 * Real.exp (14 * lam * h) *
                ((1 - ‖quadraticChar rho u v‖ ^ 2) / V + lam ^ 2) /
                  u ^ 2

theorem quadraticComplexChord_matching_power
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (h : ℝ) (hh : 0 < h)
    (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (hm2V : (∫ a : ℝ, a ^ 2 ∂nu) ≤
      2 * variance (id : ℝ → ℝ) nu)
    (lam b s : ℝ) (hlam : 0 ≤ lam) (hb : b = lam ∨ b = -lam)
    (hs : 0 ≤ s) (hsquare : s ≤ lam ^ 2) (hslope : s * h ≤ lam)
    (ell J : ℕ) (hell : 0 < ell)
    (u v : ℝ) (hu : u ≠ 0) (hv : |v| ≤ |u| / (4 * h)) :
    let V : ℝ := variance (id : ℝ → ℝ) nu
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
    let T : ℝ := (ell : ℝ) * m2
    let rho : Measure ℝ := nu.tilted (fun a => b * a - s * a ^ 2)
    let reflectedRho : Measure ℝ :=
      nu.tilted (fun a => -b * a - s * a ^ 2)
    let z : ℂ := (u : ℂ) - (b : ℂ) * Complex.I
    let w : ℂ := (v : ℂ) + (s : ℂ) * Complex.I
    let CJ : ℝ := (144 * (1 + 4 * (J : ℝ))) ^ J
    0 < T ∧
      ‖quadraticChar rho u v‖ ^ ell *
          ‖quadraticChordCharComplex nu z w‖ ^ J ≤
        CJ * Real.exp (14 * (J : ℝ) * lam * h) *
          (T⁻¹ + lam ^ 2) ^ J / |u| ^ (2 * J) ∧
      ‖quadraticChar rho u v‖ ^ ell *
          ‖quadraticFullNoiseCharComplex nu z w‖ ≤
        (4752 : ℝ) ^ 8 * Real.exp (162 * lam * h) *
          (T⁻¹ + lam ^ 2) ^ 8 / |u| ^ 16 ∧
      ‖quadraticChar reflectedRho (-u) v‖ ^ ell *
          ‖quadraticFullNoiseCharComplex nu z w‖ ≤
        (4752 : ℝ) ^ 8 * Real.exp (162 * lam * h) *
          (T⁻¹ + lam ^ 2) ^ 8 / |u| ^ 16

end Shao.Probability
```

The `Differentiable ℂ` assertions are joint entire extensions on `ℂ × ℂ`. The cone remains the real cone, with real `u ≠ 0`; the complex denominator is not assumed nonzero, but is concluded almost everywhere from its real part. The exact value at denominator zero is included for the all-complex identity, including `z = w = 0`.

`J` is arbitrary in the K estimate and the displayed constant depends on it. The full-noise law already has exactly eight copies in each family, so its two bounds use exponent eight. No artificial arbitrary-J full-noise law is introduced. `ell > 0` is sufficient for the candidate's elementary cancellation proof; the original large-frequency/lower-clock restrictions remain in their downstream source application.

The square guard is retained to match the actual joint-tilt interface; the direct cone proof only needs the slope guard in addition to nonnegativity. No tilted low-frequency Gamma smallness, symmetry, centering, nonatomicity, positive characteristic value or supplied defect bound is assumed.
