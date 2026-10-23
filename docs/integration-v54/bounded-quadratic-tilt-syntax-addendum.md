# Root syntax-only literal freeze addendum: quoted lambda identifier

APPROVED 2026-10-23T13:39:30.914142+00:00.

Original complete mathematical freeze and candidate remain immutable. Lean reserves standalone λ as a parser token; only that standalone variable token is represented as escaped identifier «λ» in the complete literal code below. This is the same intended binder name and quantifier, with no mathematical premise/definition/numerical constant/conclusion change. hλ and all other identifiers are unchanged. Every changed token is exactly this required lexical quotation. Private helpers may choose their own valid binder names. Exact representation-normalized comparison must first replace «λ» by λ and then compare the original complete frozen statements/lets.

Original candidateSHA 8cfbe112eff7822ae646f978b5eba52575e142fb81abf4e59798647861b3fcdd; original root freezeSHA e00bdbaecad07aca91057c733bca55535fe35af45ff90ef835eaa2b835d3628f. Full syntax-correct signature blockSHA 9738a80cf193225713419abd43fa0095eb17a576ba2b44d394c11e1b485302a0. Changed token occurrences 26. This addendum does not accept any proof or authorize a successful-check replay. The independent final reviewer must verify exact token-only delta and all original source semantics.

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
    (h «λ» b s : ℝ) (hh : 0 < h) (hλ : 0 ≤ «λ»)
    (hb : b = «λ» ∨ b = -«λ»)
    (hs : 0 ≤ s) (hsquare : s ≤ «λ» ^ 2)
    (hslope : s * h ≤ «λ»)
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
    let Γ : ℝ := 8 * Real.exp (8 * «λ» * h) * (m3 / V)
    Integrable W ν ∧ IsProbabilityMeasure ρ ∧
      (∀ᵐ a : ℝ ∂ρ, |a| ≤ h) ∧
      Integrable (fun a : ℝ => a) ρ ∧
      Integrable (fun a : ℝ => a ^ 2) ρ ∧
      Integrable (fun a : ℝ => |a| ^ 3) ρ ∧
      Integrable (fun a : ℝ => |a - μρ| ^ 3) ρ ∧
      0 < Z ∧ Real.exp (-(2 * «λ» * h)) ≤ Z ∧
      Z ≤ Real.exp («λ» * h) ∧
      (∀ᵐ a : ℝ ∂ν,
        Real.exp (-(4 * «λ» * h)) ≤ w a ∧
          w a ≤ Real.exp (4 * «λ» * h)) ∧
      Real.exp (-(4 * «λ» * h)) * V ≤ Vρ ∧
      Vρ ≤ Real.exp (4 * «λ» * h) * V ∧
      Real.exp (-(4 * «λ» * h)) * m2 ≤ m2ρ ∧
      m2ρ ≤ Real.exp (4 * «λ» * h) * m2 ∧
      m3ρ ≤ Real.exp (4 * «λ» * h) * m3 ∧
      Vρ = m2ρ - μρ ^ 2 ∧
      |μρ| ≤ Real.exp (4 * «λ» * h) * (|μ| + «λ» * m2 + s * m3) ∧
      (∫ a : ℝ, |a - μρ| ^ 3 ∂ρ) ≤
        8 * Real.exp (4 * «λ» * h) * m3 ∧
      (Vρ = 0 ↔ V = 0) ∧
      (0 < V → 0 < Vρ ∧ m3ρ / Vρ ≤ Γ) ∧
      |Z - 1 - b * μ - («λ» ^ 2 / 2 - s) * m2| ≤
        24 * «λ» ^ 3 * m3 * Real.exp («λ» * h) ∧
      Real.log Z ≤ b * μ + («λ» ^ 2 / 2 - s) * m2 +
        24 * «λ» ^ 3 * m3 * Real.exp («λ» * h) ∧
      («λ» = 0 → s = 0 ∧ ρ = ν ∧ Z = 1)

end Shao.Probability
```
