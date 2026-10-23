# Actual complex K/Xi and high-frequency declaration freeze

Root fully read all TWO literal actual-law extension definitions, all THREE complete theorem heads/every let, and the entire source contract/proof route. Exact candidate SHA256 e2927ed7653934a978e3d19e31ab52d6772388167e493e674a3266df1a6dd910; contract c698c818ce63841eade8fa471a798243fc9fc0390f7624abe79fa7b32f745939. Their mathematical interfaces below are frozen before implementation.

Owner /root/common_complex_chord_author may write ONLY new Shao/Probability/QuadraticComplexChord.lean and drafts/c12-complex-chord/. Parent f1cd24313487008ceae325eff12fc0f1fdbf3118, released server common-centered-characteristic-v44/feat/common-centered-characteristic. Previous weighted author/reviewer both released. Root supplies exact accepted dependency object closure before first target check. Preserve other owners' sources/untracked support; commit only own new module. No mathematical head/definition changes without explicit addendum. Additional global definition values, including private ones, require full-value freeze; proof-local lets and private theorem support are permitted and receive complete final owned audit.

These integrals use the EXISTING actual quadraticChordLaw/quadraticFullNoiseLaw, with original scalar and exactly eight+eight copies. Full all-complex chord formula includes the removable zero-denominator value, genuine L1 and joint entire extension; real compatibility must be proved. Cone nonzero denominator is a conclusion, actual tilted defect is paid via true pair density/characteristic identity. Generic power constant depends on J; reflected matching law is distinct and is genuinely paired with the SAME Xi at the same contour. Bounds include atoms/noncentering and lam0/s0/J0; original positive variance and ell>0 remain explicit. Source m2<=2V and separate square/slope conditions are justified in the contract, not silently assumed source facts. No Gamma-smallness premise is introduced. No contour displacement, full growing kernel/odd difference, probability survival/desmoothing or C1C2 root closure is accepted by this freeze.

All Lean/heavy designated server only, root CPU10–13/root-heavy.lock, pinned versions, -M8192 -j4 -DautoImplicit=false. New source UTF8LF write_bytes before first gate. First whole successful target must emit its reusable -o object; preserve original actual direct Lean exits immediately plus commands/request/return/log/source/object hashes. No old accepted producer recompilation/check replay. One complete actual-owned types/definition values/private/generated recursive-axiom audit and fresh independent complete source-to-statement/proof review are mandatory. Only propext/Classical.choice/Quot.sound; no sorry/admit/newaxiom/unsafe/native_decide.

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
