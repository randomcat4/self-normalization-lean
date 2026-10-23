# Actual joint-tilt part(c) and low-frequency declaration freeze

Root has fully read both complete candidate heads/ALL lets and the entire source contract. All TWO literal public declarations below are approved before production, with ZERO new global definitions. Candidate SHA256 `17a8eb7e8cd61d1bd1896da2d1074fd304b1edccaf5dbd7627faa729b192c1a0`; contract SHA256 `253e77e48ee9add3b8ddb472d4ece3eb042cf3b8fcbf4ec78e9e19d96f4ad3d7`.

Owner `/root/common_tilted_low_author` is activated for ONLY new `Shao/Probability/TiltedLowFrequency.lean` and `drafts/c12-tilted-low-frequency/`. The exact released server worktree is `common-short-kernel-v51`, parent `5e1a6a7fef2121bc0208798f7a0678975b44a0e9`, branch `feat/common-short-time-kernel`. Old author and independent reviewer have both released authority. Existing sources/untracked support are preserved. This consumer imports the exact already-qualified upstream tilt producer source `93c302d9de61bc4bf0cb238e82a4ed5b7f66e0ddbd2e833fec5bc6bbb25a8257`, object `cd1e326090a3fce3ecab7d8b38c14d7239c6b4fcedb600f8bb8dffb14d3dc2ec`, review `3f6c037bdecb6b989040a013fe8575eac35073923b986edc22be355823c44ec8`; no producer replay.

The actual original conditional law, nonzero conditional mean, true characteristic powers and actual remaining clock are retained. Raw-second/variance comparison is conditional on literal `(y+lam)*Gamma <= 1/8`; actual frequency damping and sqrt(raw2)<=Gamma do not require this smallness. Both s-square and s-slope guards must be actually paid from original threshold/clock/yh conditions, never conflated. Generic base-scale assumptions are paid in the actual-source corollary. Natural zero power/zero remaining time is included. No supplied decay, mean-ratio or conditional centering premise is introduced. Future prescribed-lambda smallness, complex contour/growing amplitudes, probability survival/weighted second moments/desmoothing/C1C2 remain OPEN.

New source UTF8 LF before first gate. All Lean/heavy server CPU10–13/root-heavy.lock, pinned versions and -M8192 -j4 -DautoImplicit=false. Targeted necessary gates only, original direct Lean exit immediately retained with commands/log/source/object hashes. First successful complete source stays immutable; one actual-owned types/definition values/private/generated/recursive-axiom audit; fresh independent full review required. Standard three axioms only; no proof escapes. Do not change mathematical heads or assumptions silently. Root may supply a missing accepted readonly dependency object if genuinely absent; no deliberate missing-import smoke or old successful rechecks.

## Complete frozen public interface

```lean
import Shao.Probability.BoundedQuadraticTilt
import Shao.Probability.LowFrequencyDamping
import Shao.Probability.SourceFourierScale

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
```

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

end Shao.Probability
