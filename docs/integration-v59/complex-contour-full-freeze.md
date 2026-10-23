# Actual complex characteristic and boundary-contour declaration freeze

Root fully read all three complete candidate/contract/route files, verifies the entire/strip IBP3+IBP8/sequential Cauchy rectangle/Fubini/real derivative/explicit512 majorant mathematics, and freezes exactly TWO literal definitions and FOUR full public heads below, with every let. No mathematical premise/value/constant changed.

Module placement for independent useful production: first definition quadraticCharComplex and first full head quadraticCharComplex_data go in NEW Shao/Probability/QuadraticComplexCharacteristic.lean. Second definition sourceComplexBoundaryContourIntegrand and remaining three exact heads go in NEW Shao/Probability/SourceComplexBoundaryContour.lean, importing the first. The mathematical declarations and namespace stay literally unchanged. This split lets the first producer progress without the still-evolving amplitude module.

Sole author common_complex_growing_candidate owns only those two new sources and drafts/c12-complex-growing-kernel/. Worktree common-centered-characteristic-v44, branchfeat/common-centered-characteristic, frozenparent83f968d3917f3b602f49435a4a80c351186f2cd2, released oldwriter and reviewer. Begin actual firstmodule now; prepare contour proofs independently. Import/check the amplitude-dependent module only after SourceComplexBoundaryAmplitude final immutable complete independent qualification; root will install its exact accepted source/object. No provisional old dependency replay/emission. The contour unit consumes only fixed theta/literal amplitude/mark, not unpaid sharpBundle3 conclusions.

Nonuniform strip B depends on all displayed fixed parameters and cannot become a uniform growing-y bound. Closed/horizontal/vertical L1 and edge limits are proved before Fubini/Cauchy. SAMEXi in both reflected terms, actual real full f'' (not even-only) and negative coefficient(2pi)^-2 stay exact. Square/slope guards paid independently; noGamma condition introduced to contour. Majorant512 is fixed. General moment/normalizer data stays actual and noncentered. Arbitrary/optimal/logarithmic tilts are not assumed <=4y, and no fourth regional bound is claimed.

Additional global definitions INCLUDING private require full literal-value addendum first; proof-local lets/helper theorems allowed. All new sourcesUTF8LF beforefirstcheck; allLean/heavy serveronly CPU10-13/root-heavy.lock/M8192/j4/autoImplicitfalse, directrcimmediate, firstwhole success-o. No sorry/admit/newaxiom/unsafe/native_decide. New exact source/types/values/private/generated/transitiveAX require one fresh independent complete review per substantive accepted milestone; reuse qualified oldchecks/proofs. Root publishes/integrates; all original roots and growing-kernel estimates stayOPEN.

Exact document bindings:
- drafts/c12-complex-growing-kernel/candidate-declarations.md SHA256 fa6555f80e1c05754388a5aba11f1e3180a22286fc2e4afac0584fdcce3cf1ff
- drafts/c12-complex-growing-kernel/source-contract.md SHA256 0c5646b6b3de5e897445f71c89f7dc9565737fed48090ddb42b74b49cd3570b6
- drafts/c12-complex-growing-kernel/proof-route.md SHA256 9254ba5f5b0164fb0610a53d5875a68d4cb70d130c37e56a3b8dbae91858b77b

## Exact frozen declarations (module placement above)

# Actual complex-boundary contour displacement: candidate declarations

Status: CANDIDATE, awaiting root's complete reading and declaration freeze.
There is no production source, Lean elaboration, kernel receipt, or independent
acceptance for this candidate. The proposed production module is
`Shao/Probability/SourceComplexBoundaryContour.lean`.

This is the next substantive part of source `h:supp:contour`: the actual
two-frequency contour displacement, its full real-kernel derivative linkage,
and the normalizer/noise/spatial exponential majorant. It also pays the actual
complex increment characteristic function and source `oddcommon(a)` needed by
that consumer. It does not assume a contour identity, kernel estimate, amplitude
estimate, transform decay, edge limit, or Fourier integrability.

Only the following TWO new definition values are proposed. Everything else in
the heads is an explicit proof-local let. Fin 2 value 0 denotes derivative order
1, while value 1 denotes derivative order 2; for the boundary split it denotes
the original branches j=0 and j=1. The existing theta/amplitudes/marks retain
their frozen literal values and names.

```lean
import Shao.Probability.QuadraticComplexChord
import Shao.Probability.SourceComplexBoundaryAmplitude
import Shao.Probability.SourceFutureNoiseOddEven
import Shao.Probability.BoundedQuadraticTilt
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ContDiff

noncomputable def quadraticCharComplex
    (nu : Measure ℝ) (z zeta : ℂ) : ℂ :=
  ∫ a : ℝ,
    Complex.exp ((z * (a : ℂ) + zeta * ((a ^ 2 : ℝ) : ℂ)) * Complex.I) ∂nu

noncomputable def sourceComplexBoundaryContourIntegrand
    (nu : Measure ℝ) (m : ℕ) (j d : Fin 2)
    (y N lam w q : ℝ) (z zeta : ℂ) : ℂ :=
  let Delta : ℝ := (1 + lam * y)⁻¹
  let c : ℝ → ℝ := fun r => sourceKernelCutoff r *
    (if j = 0 then sourceComplexSplitTheta ((r - N) / Delta)
      else 1 - sourceComplexSplitTheta ((r - N) / Delta))
  let R : ℂ :=
    if d = 0 then
      quadraticCharComplex nu z zeta ^ m -
        quadraticCharComplex nu (-z) zeta ^ m
    else
      Complex.I * z *
        (Complex.exp (z * (w : ℂ) * Complex.I) *
            quadraticCharComplex nu z zeta ^ m +
          Complex.exp (-z * (w : ℂ) * Complex.I) *
            quadraticCharComplex nu (-z) zeta ^ m)
  Complex.exp (zeta * (q : ℂ) * Complex.I) *
    (∫ r : ℝ, (c r : ℂ) *
      Complex.exp (-(z * ((y * Real.sqrt r : ℝ) : ℂ) +
        zeta * (r : ℂ)) * Complex.I)) *
    quadraticFullNoiseCharComplex nu z zeta * R

theorem quadraticCharComplex_data
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (h : ℝ) (hh : 0 < h)
    (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h) :
    Differentiable ℂ (fun p : ℂ × ℂ =>
      quadraticCharComplex nu p.1 p.2) ∧
      (∀ z zeta : ℂ,
        Integrable (fun a : ℝ =>
          Complex.exp ((z * (a : ℂ) +
            zeta * ((a ^ 2 : ℝ) : ℂ)) * Complex.I)) nu ∧
        ‖quadraticCharComplex nu z zeta‖ ≤
          Real.exp (h * |z.im| + h ^ 2 * |zeta.im|)) ∧
      (∀ u v : ℝ,
        quadraticCharComplex nu (u : ℂ) (v : ℂ) = quadraticChar nu u v) ∧
      (∀ b s : ℝ,
        let W : ℝ → ℝ := fun a => Real.exp (b * a - s * a ^ 2)
        let Z : ℝ := ∫ a : ℝ, W a ∂nu
        let rho : Measure ℝ := nu.tilted (fun a => b * a - s * a ^ 2)
        Integrable W nu ∧ 0 < Z ∧ IsProbabilityMeasure rho ∧
          ∀ u v : ℝ,
            quadraticCharComplex nu
                ((u : ℂ) - (b : ℂ) * Complex.I)
                ((v : ℂ) + (s : ℂ) * Complex.I) =
              (Z : ℂ) * quadraticChar rho u v) ∧
      ∀ lam s u v : ℝ, 0 ≤ lam → 0 ≤ s →
        let z : ℂ := (u : ℂ) - (lam : ℂ) * Complex.I
        let zeta : ℂ := (v : ℂ) + (s : ℂ) * Complex.I
        let mu : ℝ := ∫ a : ℝ, a ∂nu
        let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂nu
        ‖quadraticCharComplex nu z zeta -
            quadraticCharComplex nu (-z) zeta‖ ≤
          4 * Real.exp (lam * h) *
            (|mu| * ‖z‖ + m3 *
              (‖z‖ ^ 3 + ‖z‖ * (|v| + s)))

theorem sourceComplexBoundary_contour_displacement
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (h : ℝ) (hh : 0 < h)
    (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (m : ℕ) (y N lam w q : ℝ)
    (hy : 2 ≤ y) (hNlo : (1 / 16 : ℝ) ≤ N) (hNhi : N ≤ 7)
    (hlam : y / Real.sqrt N ≤ lam) :
    let s : ℝ := lam * y / Real.sqrt N
    let sj : Fin 2 → ℝ := fun j => if j = 0 then 0 else s
    ∃ B : ℝ, 0 < B ∧ ∀ j d : Fin 2,
      let F : ℂ → ℂ → ℂ :=
        sourceComplexBoundaryContourIntegrand nu m j d y N lam w q
      let EU : ℝ → ℝ := fun R =>
        ∫ p : ℝ × ℝ in Set.Icc (-lam) 0 ×ˢ Set.univ,
          ‖F ((R : ℂ) + (p.1 : ℂ) * Complex.I) (p.2 : ℂ)‖
      let EV : ℝ → ℝ := fun R =>
        ∫ p : ℝ × ℝ in Set.univ ×ˢ Set.Icc 0 (sj j),
          ‖F ((p.1 : ℂ) - (lam : ℂ) * Complex.I)
            ((R : ℂ) + (p.2 : ℂ) * Complex.I)‖
      Differentiable ℂ (fun p : ℂ × ℂ => F p.1 p.2) ∧
        (∀ u v eta xi : ℝ, |eta| ≤ lam → |xi| ≤ s →
          ‖F ((u : ℂ) + (eta : ℂ) * Complex.I)
            ((v : ℂ) + (xi : ℂ) * Complex.I)‖ ≤
            B / ((1 + |u|) ^ (5 - d.val) * (1 + |v|) ^ 3)) ∧
        (∀ eta xi : ℝ, |eta| ≤ lam → |xi| ≤ s →
          Integrable (fun p : ℝ × ℝ =>
            F ((p.1 : ℂ) + (eta : ℂ) * Complex.I)
              ((p.2 : ℂ) + (xi : ℂ) * Complex.I))
            (volume : Measure (ℝ × ℝ))) ∧
        (∀ R : ℝ,
          IntegrableOn (fun p : ℝ × ℝ =>
            F ((R : ℂ) + (p.1 : ℂ) * Complex.I) (p.2 : ℂ))
            (Set.Icc (-lam) 0 ×ˢ Set.univ) ∧
          IntegrableOn (fun p : ℝ × ℝ =>
            F ((p.1 : ℂ) - (lam : ℂ) * Complex.I)
              ((R : ℂ) + (p.2 : ℂ) * Complex.I))
            (Set.univ ×ˢ Set.Icc 0 (sj j)) ∧
          EU R ≤ lam * B / (1 + |R|) ^ (5 - d.val) ∧
          EV R ≤ s * B / (1 + |R|) ^ 3) ∧
        Filter.Tendsto EU Filter.atTop (nhds 0) ∧
        Filter.Tendsto EU Filter.atBot (nhds 0) ∧
        Filter.Tendsto EV Filter.atTop (nhds 0) ∧
        Filter.Tendsto EV Filter.atBot (nhds 0) ∧
        (∫ p : ℝ × ℝ, F (p.1 : ℂ) (p.2 : ℂ)) =
          ∫ p : ℝ × ℝ,
            F ((p.1 : ℂ) - (lam : ℂ) * Complex.I)
              ((p.2 : ℂ) + (sj j : ℂ) * Complex.I)

theorem sourceFutureNoiseKernel_complex_boundary_identity
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (h : ℝ) (hh : 0 < h)
    (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (m : ℕ) (y lam w q : ℝ) (hy : 2 ≤ y) (hq : 0 ≤ q)
    (hNlo : (1 / 16 : ℝ) ≤ q +
      (m : ℝ) * (∫ a : ℝ, a ^ 2 ∂nu))
    (hNhi : q + (m : ℝ) * (∫ a : ℝ, a ^ 2 ∂nu) ≤ 7)
    (hlam : y / Real.sqrt (q +
      (m : ℝ) * (∫ a : ℝ, a ^ 2 ∂nu)) ≤ lam) :
    let T : ℝ := (m : ℝ) * (∫ a : ℝ, a ^ 2 ∂nu)
    let N : ℝ := q + T
    let s : ℝ := lam * y / Real.sqrt N
    let sj : Fin 2 → ℝ := fun j => if j = 0 then 0 else s
    let bj : Fin 2 → ℝ := fun j =>
      if j = 0 then Real.exp (-lam * y * Real.sqrt N)
        else Real.exp (-s * q)
    let z : ℝ → ℂ := fun u => (u : ℂ) - (lam : ℂ) * Complex.I
    let rhoPlus : Fin 2 → Measure ℝ := fun j =>
      nu.tilted (fun a => lam * a - sj j * a ^ 2)
    let rhoMinus : Fin 2 → Measure ℝ := fun j =>
      nu.tilted (fun a => -lam * a - sj j * a ^ 2)
    let Zplus : Fin 2 → ℝ := fun j =>
      ∫ a : ℝ, Real.exp (lam * a - sj j * a ^ 2) ∂nu
    let Zminus : Fin 2 → ℝ := fun j =>
      ∫ a : ℝ, Real.exp (-lam * a - sj j * a ^ 2) ∂nu
    let R : Fin 2 → Fin 2 → ℝ → ℝ → ℂ := fun d j u v =>
      if d = 0 then
        (Zplus j : ℂ) ^ m * quadraticChar (rhoPlus j) u v ^ m -
          (Zminus j : ℂ) ^ m * quadraticChar (rhoMinus j) (-u) v ^ m
      else
        Complex.I * z u *
          (Complex.exp (z u * (w : ℂ) * Complex.I) *
              (Zplus j : ℂ) ^ m * quadraticChar (rhoPlus j) u v ^ m +
            Complex.exp (-z u * (w : ℂ) * Complex.I) *
              (Zminus j : ℂ) ^ m * quadraticChar (rhoMinus j) (-u) v ^ m)
    let G : Fin 2 → Fin 2 → ℝ × ℝ → ℂ := fun d j p =>
      Complex.exp (((p.2 * q : ℝ) : ℂ) * Complex.I) *
        sourceComplexBoundaryMark j y N lam p.1 p.2 *
        quadraticFullNoiseCharComplex nu (z p.1)
          ((p.2 : ℂ) + (sj j : ℂ) * Complex.I) * R d j p.1 p.2
    let f : ℝ → ℝ := fun r => sourceFutureNoiseKernel nu m y (r, q)
    DifferentiableAt ℝ f 0 ∧ DifferentiableAt ℝ f w ∧
      DifferentiableAt ℝ (fun r : ℝ => deriv f r) w ∧
      (∀ j : Fin 2, IsProbabilityMeasure (rhoPlus j) ∧
        IsProbabilityMeasure (rhoMinus j) ∧ 0 < Zplus j ∧ 0 < Zminus j) ∧
      (∀ d j : Fin 2,
        Integrable (G d j) (volume : Measure (ℝ × ℝ)) ∧
        ∀ u v : ℝ,
          sourceComplexBoundaryContourIntegrand nu m j d y N lam w q
              (z u) ((v : ℂ) + (sj j : ℂ) * Complex.I) =
            (bj j : ℂ) * G d j (u, v)) ∧
      ((deriv f 0 : ℝ) : ℂ) =
        -((((2 * Real.pi) ^ 2 : ℝ) : ℂ)⁻¹) *
          ∑ j : Fin 2, (bj j : ℂ) * (∫ p : ℝ × ℝ, G 0 j p) ∧
      ((deriv (fun r : ℝ => deriv f r) w : ℝ) : ℂ) =
        -((((2 * Real.pi) ^ 2 : ℝ) : ℂ)⁻¹) *
          ∑ j : Fin 2, (bj j : ℂ) * (∫ p : ℝ × ℝ, G 1 j p)

theorem sourceComplexBoundary_exponential_majorant
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (h : ℝ) (hh : 0 < h)
    (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (hm2V : (∫ a : ℝ, a ^ 2 ∂nu) ≤
      2 * variance (id : ℝ → ℝ) nu)
    (m : ℕ) (y lam q : ℝ) (hy : 2 ≤ y) (hq : 0 ≤ q)
    (hyh : y * h ≤ (1 / 4 : ℝ))
    (hNlo : (1 / 16 : ℝ) ≤ q +
      (m : ℝ) * (∫ a : ℝ, a ^ 2 ∂nu))
    (hNhi : q + (m : ℝ) * (∫ a : ℝ, a ^ 2 ∂nu) ≤ 7)
    (hlam : y / Real.sqrt (q +
      (m : ℝ) * (∫ a : ℝ, a ^ 2 ∂nu)) ≤ lam) :
    let mu : ℝ := ∫ a : ℝ, a ∂nu
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂nu
    let T : ℝ := (m : ℝ) * m2
    let N : ℝ := q + T
    let s : ℝ := lam * y / Real.sqrt N
    let sj : Fin 2 → ℝ := fun j => if j = 0 then 0 else s
    let bj : Fin 2 → ℝ := fun j =>
      if j = 0 then Real.exp (-lam * y * Real.sqrt N)
        else Real.exp (-s * q)
    let Z : ℝ → Fin 2 → ℝ := fun b j =>
      ∫ a : ℝ, Real.exp (b * a - sj j * a ^ 2) ∂nu
    let E : ℝ := Real.exp
      (-lam * y * Real.sqrt N + T * lam ^ 2 / 2 +
        (m : ℝ) * lam * |mu| +
        512 * (m : ℝ) * lam ^ 3 * m3 * Real.exp (512 * lam * h) +
        512 * lam * h)
    0 ≤ lam ∧ 0 ≤ s ∧ s ≤ lam ^ 2 ∧ s * h ≤ lam ∧
      m3 / variance (id : ℝ → ℝ) nu ≤ 2 * h ∧
      ∀ (j : Fin 2) (b : ℝ), (b = lam ∨ b = -lam) →
        0 < Z b j ∧
          ∀ u v w : ℝ, |w| ≤ h →
            bj j * (Z b j) ^ m *
                ‖quadraticFullNoiseCharComplex nu
                  ((u : ℂ) - (lam : ℂ) * Complex.I)
                  ((v : ℂ) + (sj j : ℂ) * Complex.I)‖ *
                Real.exp (lam * |w|) ≤ E

end Shao.Probability
```

All double integrals here are the existing standard product Lebesgue volume
on `ℝ × ℝ`, with unit frequencies and coefficient `-(2*pi)^(-2)`. Their
genuine L1 makes them equal to either iterated order by Fubini. In particular
there is no hidden 2*pi rescaling or normalized probability volume.

The contour theorem deliberately proves a stronger analytic identity for every
finite m, every w,q, and the explicit split N in [1/16,7]. Its analytic proof
needs neither the clock lower bound nor source smallness. The kernel identity
then fixes N=q+T and q>=0. The final majorant separately pays the square and
slope guards using exactly the displayed assumptions. No conclusion in this
candidate asserts the four-region table or any part of growingkernel(i)-(iii).

Bundle3 of the upstream amplitude module, including sharp localized marks and
outside32, is FROZEN BUT OPEN. This unit consumes only the fixed theta data and
the literal amplitude/mark definitions. It does not need the unaccepted sharp
norm conclusions. A later four-region consumer must explicitly wait for their
qualification; it cannot treat this contour candidate as their acceptance.
