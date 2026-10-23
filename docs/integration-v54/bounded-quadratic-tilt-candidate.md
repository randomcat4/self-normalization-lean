# Actual bounded quadratic exponential tilt — candidate declarations

State: `CANDIDATE_COMPLETE_NOT_FROZEN_NOT_PROVED`.
Owner: `/root/common_quadratic_tilt_author`, actual prescribed model
`gpt-6.1-sol`, reasoning effort `xhigh`. No subagents.

Proposed production module: `Shao.Probability.BoundedQuadraticTilt`.
Only root may freeze these declarations and activate production writing.
This file contains proposed Lean signatures, not implementations or a Lean
check result. No theorem here is labelled `CORRECT` or accepted.

There are **zero new global definitions**. Every object is given by its
literal `let` value below. In particular, every changed measure is literally
`ν.tilted (fun a => b * a - s * a ^ 2)` or its energy specialization; no
unrelated density, abstract tilted-moment package, or assumed tilted mean is
substituted for that measure. `ν` is a probability law on the usual measurable
real line. Its mean may be nonzero and it need not be symmetric.

The three signatures form one substantive milestone: a general measure
comparison producer, its energy-tilt drift/decay application, and the actual
signed joint-tilt moment/normalizer application. They do not add a separate
one-line source-parameter wrapper. The exact payment of source parameters is
in `source-contract.md` and remains a consumer obligation.

```lean
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.Calculus.Taylor

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

theorem boundedQuadraticTilt_density_moments
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h b s : ℝ) (hh : 0 < h) (hs : 0 ≤ s)
    (hsupport : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) :
    let W : ℝ → ℝ := fun a => Real.exp (b * a - s * a ^ 2)
    let Z : ℝ := ∫ a : ℝ, W a ∂ν
    let ρ : Measure ℝ := ν.tilted (fun a => b * a - s * a ^ 2)
    let w : ℝ → ℝ := fun a => W a / Z
    let S : ℝ := |b| * h + s * h ^ 2
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let μρ : ℝ := ∫ a : ℝ, a ∂ρ
    let V : ℝ := variance (id : ℝ → ℝ) ν
    let Vρ : ℝ := variance (id : ℝ → ℝ) ρ
    Integrable W ν ∧
      0 < Z ∧
      Real.exp (-S) ≤ Z ∧ Z ≤ Real.exp S ∧
      -S ≤ Real.log Z ∧ Real.log Z ≤ S ∧
      IsProbabilityMeasure ρ ∧
      ρ ≪ ν ∧ ν ≪ ρ ∧
      (∀ᵐ a : ℝ ∂ρ, |a| ≤ h) ∧
      (∀ᵐ a : ℝ ∂ν,
        Real.exp (-(2 * S)) ≤ w a ∧ w a ≤ Real.exp (2 * S)) ∧
      (∀ g : ℝ → ℝ, Integrable g ρ ↔ Integrable g ν) ∧
      (∀ g : ℝ → ℝ, Integrable g ν →
        (∫ a : ℝ, g a ∂ρ) = ∫ a : ℝ, w a * g a ∂ν) ∧
      (∀ g : ℝ → ℝ, Integrable g ν →
        (∀ᵐ a : ℝ ∂ν, 0 ≤ g a) →
        Real.exp (-(2 * S)) * (∫ a : ℝ, g a ∂ν) ≤
            (∫ a : ℝ, g a ∂ρ) ∧
          (∫ a : ℝ, g a ∂ρ) ≤
            Real.exp (2 * S) * (∫ a : ℝ, g a ∂ν)) ∧
      (∀ k : ℕ,
        Integrable (fun a : ℝ => a ^ k) ν ∧
        Integrable (fun a : ℝ => a ^ k) ρ ∧
        Integrable (fun a : ℝ => |a| ^ k) ν ∧
        Integrable (fun a : ℝ => |a| ^ k) ρ ∧
        (∫ a : ℝ, |a| ^ k ∂ν) ≤ h ^ k ∧
        (∫ a : ℝ, |a| ^ k ∂ρ) ≤ h ^ k) ∧
      |μ| ≤ h ∧ |μρ| ≤ h ∧
      V = (∫ a : ℝ, a ^ 2 ∂ν) - μ ^ 2 ∧
      Vρ = (∫ a : ℝ, a ^ 2 ∂ρ) - μρ ^ 2 ∧
      Real.exp (-(2 * S)) * V ≤ Vρ ∧
      Vρ ≤ Real.exp (2 * S) * V ∧
      (Vρ = 0 ↔ V = 0)

theorem boundedEnergyTilt_drift_decay
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h s : ℝ) (hh : 0 < h) (hs : 0 ≤ s)
    (hsupport : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (hsmall : s * h ^ 2 ≤ 1) :
    let W : ℝ → ℝ := fun a => Real.exp (-s * a ^ 2)
    let Z : ℝ := ∫ a : ℝ, W a ∂ν
    let ρ : Measure ℝ := ν.tilted (fun a => -s * a ^ 2)
    let w : ℝ → ℝ := fun a => W a / Z
    let S : ℝ := s * h ^ 2
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    let V : ℝ := variance (id : ℝ → ℝ) ν
    let μρ : ℝ := ∫ a : ℝ, a ∂ρ
    let m2ρ : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
    let m3ρ : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
    let Vρ : ℝ := variance (id : ℝ → ℝ) ρ
    Integrable W ν ∧ IsProbabilityMeasure ρ ∧
      (∀ᵐ a : ℝ ∂ρ, |a| ≤ h) ∧
      Integrable (fun a : ℝ => a) ρ ∧
      Integrable (fun a : ℝ => a ^ 2) ρ ∧
      Integrable (fun a : ℝ => |a| ^ 3) ρ ∧
      Integrable (fun a : ℝ => |a - μρ| ^ 3) ρ ∧
      0 < Z ∧ Real.exp (-S) ≤ Z ∧ Z ≤ 1 ∧
      (∀ᵐ a : ℝ ∂ν,
        Real.exp (-S) ≤ w a ∧ w a ≤ Real.exp S) ∧
      Real.exp (-S) * V ≤ Vρ ∧ Vρ ≤ Real.exp S * V ∧
      Real.exp (-S) * m2 ≤ m2ρ ∧ m2ρ ≤ Real.exp S * m2 ∧
      Real.exp (-S) * m3 ≤ m3ρ ∧ m3ρ ≤ Real.exp S * m3 ∧
      Vρ = m2ρ - μρ ^ 2 ∧
      μρ - μ = (∫ a : ℝ, (a - μ) * (W a - 1) ∂ν) / Z ∧
      |μρ - μ| ≤ 2 * s * Real.exp S * m3 ∧
      |μρ| ≤ |μ| + 2 * s * Real.exp S * m3 ∧
      (∫ a : ℝ, |a - μρ| ^ 3 ∂ρ) ≤ 8 * Real.exp S * m3 ∧
      Z ≤ 1 - s * m2 / 2 ∧
      Z ≤ Real.exp (-(s * m2 / 2)) ∧
      (∀ i : ℕ, Z ^ i ≤ Real.exp (-(s * m2 / 2) * (i : ℝ))) ∧
      (s = 0 → ρ = ν ∧ Z = 1)

theorem boundedQuadraticTilt_joint_moments_normalizer
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h λ b s : ℝ) (hh : 0 < h) (hλ : 0 ≤ λ)
    (hb : b = λ ∨ b = -λ)
    (hs : 0 ≤ s) (hsquare : s ≤ λ ^ 2)
    (hslope : s * h ≤ λ)
    (hsupport : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) :
    let W : ℝ → ℝ := fun a => Real.exp (b * a - s * a ^ 2)
    let Z : ℝ := ∫ a : ℝ, W a ∂ν
    let ρ : Measure ℝ := ν.tilted (fun a => b * a - s * a ^ 2)
    let w : ℝ → ℝ := fun a => W a / Z
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    let V : ℝ := variance (id : ℝ → ℝ) ν
    let μρ : ℝ := ∫ a : ℝ, a ∂ρ
    let m2ρ : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
    let m3ρ : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
    let Vρ : ℝ := variance (id : ℝ → ℝ) ρ
    let Γ : ℝ := 8 * Real.exp (8 * λ * h) * (m3 / V)
    Integrable W ν ∧ IsProbabilityMeasure ρ ∧
      (∀ᵐ a : ℝ ∂ρ, |a| ≤ h) ∧
      Integrable (fun a : ℝ => a) ρ ∧
      Integrable (fun a : ℝ => a ^ 2) ρ ∧
      Integrable (fun a : ℝ => |a| ^ 3) ρ ∧
      Integrable (fun a : ℝ => |a - μρ| ^ 3) ρ ∧
      0 < Z ∧ Real.exp (-(2 * λ * h)) ≤ Z ∧
      Z ≤ Real.exp (λ * h) ∧
      (∀ᵐ a : ℝ ∂ν,
        Real.exp (-(4 * λ * h)) ≤ w a ∧
          w a ≤ Real.exp (4 * λ * h)) ∧
      Real.exp (-(4 * λ * h)) * V ≤ Vρ ∧
      Vρ ≤ Real.exp (4 * λ * h) * V ∧
      Real.exp (-(4 * λ * h)) * m2 ≤ m2ρ ∧
      m2ρ ≤ Real.exp (4 * λ * h) * m2 ∧
      m3ρ ≤ Real.exp (4 * λ * h) * m3 ∧
      Vρ = m2ρ - μρ ^ 2 ∧
      |μρ| ≤ Real.exp (4 * λ * h) * (|μ| + λ * m2 + s * m3) ∧
      (∫ a : ℝ, |a - μρ| ^ 3 ∂ρ) ≤
        8 * Real.exp (4 * λ * h) * m3 ∧
      (Vρ = 0 ↔ V = 0) ∧
      (0 < V → 0 < Vρ ∧ m3ρ / Vρ ≤ Γ) ∧
      |Z - 1 - b * μ - (λ ^ 2 / 2 - s) * m2| ≤
        24 * λ ^ 3 * m3 * Real.exp (λ * h) ∧
      Real.log Z ≤ b * μ + (λ ^ 2 / 2 - s) * m2 +
        24 * λ ^ 3 * m3 * Real.exp (λ * h) ∧
      (λ = 0 → s = 0 ∧ ρ = ν ∧ Z = 1)

end Shao.Probability
```

## Literal constants and boundaries

- Core `S = |b| * h + s * h ^ 2`; density and variance comparison factors
  are `Real.exp (±(2*S))`. No sign or size restriction on `b` is hidden.
- Energy `S = s * h ^ 2`; density, raw moments and variances have factors
  `Real.exp (±S)`. Its smallness hypothesis is exactly `s*h^2 ≤ 1`, used for
  the decay of `Z`; this admits `s>0`. Its mean-shift coefficient is `2`, and
  centered-third-moment coefficient is `8`.
- Joint tilt requires **both** `s ≤ λ^2` and `s*h ≤ λ`, as well as `s ≥ 0`.
  Neither is inferred from the other. `b` is exactly one of `λ,-λ`.
  Density, raw-second, raw-third and variance factors use exponent `4*λ*h`;
  the source gamma envelope is literally `Γ=8*exp(8*λ*h)*(m3/V)`, so `L3=8`.
  The Taylor/log remainder uses the literal absolute coefficient `24` and
  exponent `λ*h`. This implies the source's looser single-constant form with
  `C=24` because `λ*h ≥ 0`.
- With `λ=0`, the joint theorem's stated `0 ≤ s ≤ λ^2` forces `s=0`. This is
  **only** a fact inside that theorem. It does not restrict the general core
  or energy theorem, and cannot be used to reject an energy tilt with
  `b=0,s>0`.
- No nondegeneracy assumption occurs in the measure/density/raw-moment/
  variance statements. They remain meaningful at `V=0`, with the explicit
  equivalence `Vρ=0 ↔ V=0`. The quotient gamma bound is asserted only under
  `0<V`; `Γ` uses Lean's real division convention outside that branch and
  has no claimed interpretation or positivity there.
- At `m3=0` the law is supported at zero, so the intended exact equalities
  and zero remainder are consistent. At `s=0`, energy tilt equals the base
  probability law. No center-zero or symmetry premise is introduced.

## Freeze and later acceptance

Before implementation, root must read the complete signatures and source
contract, choose this exact module scope, and record its complete declaration
freeze. The implementation then needs a fresh independent complete
source-to-statement/proof review and a source-hash-bound server kernel plus
all-owned transitive-axiom receipt. The allowed axioms remain `propext`,
`Classical.choice`, `Quot.sound`. No production source or checks have been
created for this candidate.
