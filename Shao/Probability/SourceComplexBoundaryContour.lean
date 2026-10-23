import Shao.Probability.QuadraticComplexCharacteristic
import Shao.Probability.SourceComplexBoundaryAmplitude
import Shao.Probability.SourceFutureNoiseOddEven
import Shao.Probability.BoundedQuadraticTilt
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open Filter
open scoped Topology BigOperators ContDiff

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

private theorem contour_parameter_guards (y N lam h : ℝ)
    (hy : 2 ≤ y) (hN : (1 / 16 : ℝ) ≤ N)
    (hlam : y / Real.sqrt N ≤ lam) (hh : 0 < h)
    (hyh : y * h ≤ (1 / 4 : ℝ)) :
    let s : ℝ := lam * y / Real.sqrt N
    0 ≤ lam ∧ 0 ≤ s ∧ s ≤ lam ^ 2 ∧ s * h ≤ lam := by
  dsimp only
  have hN0 : 0 < N := by linarith
  have hr : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hr2 := Real.sq_sqrt hN0.le
  have hrlo : (1 / 4 : ℝ) ≤ Real.sqrt N := by nlinarith [Real.sqrt_nonneg N]
  have hl : 0 ≤ lam := (div_nonneg (by linarith) hr.le).trans hlam
  have hyl : y ≤ lam * Real.sqrt N := (div_le_iff₀ hr).mp hlam
  refine ⟨hl, div_nonneg (mul_nonneg hl (by linarith)) hr.le, ?_, ?_⟩
  · apply (div_le_iff₀ hr).mpr
    nlinarith [mul_le_mul_of_nonneg_left hyl hl]
  · rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hr).mpr
    nlinarith [mul_le_mul_of_nonneg_left (hyh.trans hrlo) hl]

private theorem contour_gamma_bound
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (hm2V : (∫ a : ℝ, a ^ 2 ∂nu) ≤ 2 * variance (id : ℝ → ℝ) nu) :
    (∫ a : ℝ, |a| ^ 3 ∂nu) / variance (id : ℝ → ℝ) nu ≤ 2 * h := by
  have h2 : Integrable (fun a : ℝ => a ^ 2) nu := by
    apply (integrable_const (h ^ 2)).mono' (by fun_prop)
    filter_upwards [hs] with a ha
    simpa [Real.norm_eq_abs, abs_pow] using pow_le_pow_left₀ (abs_nonneg a) ha 2
  have hm : (∫ a : ℝ, |a| ^ 3 ∂nu) ≤ h * ∫ a : ℝ, a ^ 2 ∂nu := by
    rw [← integral_const_mul]
    apply integral_mono_ae h3 (h2.const_mul h)
    filter_upwards [hs] with a ha
    calc
      |a| ^ 3 = |a| * a ^ 2 := by rw [pow_succ, sq_abs]; ring
      _ ≤ h * a ^ 2 := mul_le_mul_of_nonneg_right ha (sq_nonneg a)
  apply (div_le_iff₀ hV).mpr
  nlinarith [mul_le_mul_of_nonneg_left hm2V hh.le]

private theorem contour_actual_noise_norm
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (h : ℝ) (hh : 0 < h) (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (hgamma : (∫ a : ℝ, |a| ^ 3 ∂nu) / variance (id : ℝ → ℝ) nu ≤ 2 * h)
    (lam s : ℝ) (hlam : 0 ≤ lam) (hs : 0 ≤ s) (hslope : s * h ≤ lam)
    (u v : ℝ) :
    ‖quadraticFullNoiseCharComplex nu
      ((u : ℂ) - (lam : ℂ) * Complex.I)
      ((v : ℂ) + (s : ℂ) * Complex.I)‖ ≤ Real.exp (98 * lam * h) := by
  haveI : IsProbabilityMeasure (quadraticFullNoiseLaw nu) :=
    (quadraticFullNoise_law_data nu h3 hV h hh hsupport).2.2.1
  have hp := (quadraticFullNoise_support_moments nu h3 hV h hh hsupport hgamma).1
  unfold quadraticFullNoiseCharComplex
  have hb : ∀ᵐ p : ℝ × ℝ ∂quadraticFullNoiseLaw nu,
      ‖Complex.exp ((((u : ℂ) - (lam : ℂ) * Complex.I) * (p.1 : ℂ) +
        ((v : ℂ) + (s : ℂ) * Complex.I) * (p.2 : ℂ)) * Complex.I)‖ ≤
        Real.exp (98 * lam * h) := by
    filter_upwards [hp] with p hp
    rw [Complex.norm_exp_mul_I]
    apply Real.exp_le_exp.mpr
    simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
      zero_mul, sub_zero, zero_sub, zero_add, add_zero]
    have hsp : s * h ^ 2 ≤ lam * h := by
      nlinarith [mul_le_mul_of_nonneg_right hslope hh.le]
    calc
      -(-lam * p.1 + s * p.2) ≤ lam * |p.1| + s * |p.2| := by
        nlinarith [mul_le_mul_of_nonneg_left (le_abs_self p.1) hlam,
          mul_le_mul_of_nonneg_left (neg_le_abs p.2) hs]
      _ ≤ lam * (34 * h) + s * (64 * h ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hp.1 hlam)
          (mul_le_mul_of_nonneg_left hp.2 hs)
      _ ≤ 98 * lam * h := by nlinarith
  simpa only [integral_const, probReal_univ, one_smul] using
    norm_integral_le_of_norm_le (integrable_const (Real.exp (98 * lam * h))) hb

private theorem contour_normalizer_power
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h lam b s : ℝ) (hh : 0 < h) (hlam : 0 ≤ lam)
    (hb : b = lam ∨ b = -lam) (hs : 0 ≤ s)
    (hsquare : s ≤ lam ^ 2) (hslope : s * h ≤ lam)
    (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h) (m : ℕ) :
    let Z : ℝ := ∫ a : ℝ, Real.exp (b * a - s * a ^ 2) ∂nu
    let mu : ℝ := ∫ a : ℝ, a ∂nu
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂nu
    0 < Z ∧ Z ^ m ≤ Real.exp ((m : ℝ) *
      (b * mu + (lam ^ 2 / 2 - s) * m2 +
        24 * lam ^ 3 * m3 * Real.exp (lam * h))) := by
  dsimp only
  have hd := boundedQuadraticTilt_joint_moments_normalizer nu h lam b s hh hlam hb
    hs hsquare hslope hsupport
  dsimp only at hd
  rcases hd with ⟨_, _, _, _, _, _, _, hZ, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hlog, _⟩
  refine ⟨hZ, ?_⟩
  have hZe : (∫ a : ℝ, Real.exp (b * a - s * a ^ 2) ∂nu) ≤
      Real.exp (b * (∫ a : ℝ, a ∂nu) + (lam ^ 2 / 2 - s) * (∫ a : ℝ, a ^ 2 ∂nu) +
        24 * lam ^ 3 * (∫ a : ℝ, |a| ^ 3 ∂nu) * Real.exp (lam * h)) := by
    calc
      _ = Real.exp (Real.log (∫ a : ℝ, Real.exp (b * a - s * a ^ 2) ∂nu)) :=
        (Real.exp_log hZ).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlog
  calc
    _ ≤ (Real.exp (b * (∫ a : ℝ, a ∂nu) + (lam ^ 2 / 2 - s) * (∫ a : ℝ, a ^ 2 ∂nu) +
        24 * lam ^ 3 * (∫ a : ℝ, |a| ^ 3 ∂nu) * Real.exp (lam * h))) ^ m :=
      pow_le_pow_left₀ hZ.le hZe m
    _ = _ := (Real.exp_nat_mul _ _).symm

private theorem contour_shifted_phase (u v lam s t r : ℝ) :
    Complex.exp (-(((u : ℂ) - (lam : ℂ) * Complex.I) * (t : ℂ) +
      ((v : ℂ) + (s : ℂ) * Complex.I) * (r : ℂ)) * Complex.I) =
      (Real.exp (-lam * t + s * r) : ℂ) *
        Complex.exp (-(((u * t + v * r : ℝ) : ℂ)) * Complex.I) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  simp [Complex.I_sq] <;> ring

private theorem contour_split_transport (j : Fin 2) (y N lam r : ℝ) :
    let Delta : ℝ := (1 + lam * y)⁻¹
    let c : ℝ := sourceKernelCutoff r *
      (if j = 0 then sourceComplexSplitTheta ((r - N) / Delta)
        else 1 - sourceComplexSplitTheta ((r - N) / Delta))
    let sj : ℝ := if j = 0 then 0 else lam * y / Real.sqrt N
    let beta : ℝ := if j = 0 then Real.exp (-lam * y * Real.sqrt N) else 1
    c * Real.exp (-lam * (y * Real.sqrt r) + sj * r) =
      beta * sourceComplexBoundaryAmplitude j y N lam r := by
  dsimp only
  by_cases hj : j = 0
  · simp only [hj, if_pos, zero_mul, add_zero, sourceComplexBoundaryAmplitude]
    calc
      _ = (sourceKernelCutoff r * sourceComplexSplitTheta
          ((r - N) / (1 + lam * y)⁻¹)) *
          (Real.exp (-lam * y * Real.sqrt N) *
            Real.exp (-lam * y * (Real.sqrt r - Real.sqrt N))) := by
        rw [← Real.exp_add]
        congr 1
        congr 1
        ring
      _ = _ := by ring
  · simp only [sourceComplexBoundaryAmplitude, hj, ite_false, one_mul]
    congr 1
    congr 1
    ring

private theorem contour_boundary_shift (j : Fin 2) (y N lam u v : ℝ) :
    let Delta : ℝ := (1 + lam * y)⁻¹
    let c : ℝ → ℝ := fun r => sourceKernelCutoff r *
      (if j = 0 then sourceComplexSplitTheta ((r - N) / Delta)
        else 1 - sourceComplexSplitTheta ((r - N) / Delta))
    let sj : ℝ := if j = 0 then 0 else lam * y / Real.sqrt N
    let beta : ℝ := if j = 0 then Real.exp (-lam * y * Real.sqrt N) else 1
    (∫ r : ℝ, (c r : ℂ) *
      Complex.exp (-(((u : ℂ) - (lam : ℂ) * Complex.I) *
          ((y * Real.sqrt r : ℝ) : ℂ) +
        ((v : ℂ) + (sj : ℂ) * Complex.I) * (r : ℂ)) * Complex.I)) =
      (beta : ℂ) * sourceComplexBoundaryMark j y N lam u v := by
  dsimp only
  have hmark : sourceComplexBoundaryMark j y N lam u v =
      ∫ r : ℝ, (sourceComplexBoundaryAmplitude j y N lam r : ℂ) *
        Complex.exp (-((((u * y * Real.sqrt r + v * r : ℝ) : ℂ)) * Complex.I)) := by
    run_tac
      let n : Lean.Name := .str (.str (.str
        (.num (.str (.str (.str (.str .anonymous "_private") "Shao")
          "Probability") "SourceComplexBoundaryAmplitude") 0) "Shao") "Probability")
        "boundaryMark_eq"
      Lean.Elab.Tactic.evalTactic (← `(tactic| apply $(Lean.mkIdent n)))
  rw [hmark, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with r
  rw [contour_shifted_phase]
  have ht := contour_split_transport j y N lam r
  dsimp only at ht
  calc
    _ = (((sourceKernelCutoff r *
        (if j = 0 then sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹)
          else 1 - sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹))) *
        Real.exp (-lam * (y * Real.sqrt r) +
          (if j = 0 then 0 else lam * y / Real.sqrt N) * r) : ℝ) : ℂ) *
        Complex.exp (-(((u * (y * Real.sqrt r) + v * r : ℝ) : ℂ)) * Complex.I) := by
      push_cast
      ring
    _ = _ := by
      rw [ht, Complex.ofReal_mul]
      have hp : Complex.exp (-(((u * (y * Real.sqrt r) + v * r : ℝ) : ℂ)) * Complex.I) =
          Complex.exp (-((((u * y * Real.sqrt r + v * r : ℝ) : ℂ)) * Complex.I)) := by
        congr 1
        push_cast
        ring
      rw [hp]
      ring

private theorem contour_phase_norm (z w : ℂ) (x y M1 M2 : ℝ)
    (hx : |x| ≤ M1) (hy : |y| ≤ M2) :
    ‖Complex.exp ((z * (x : ℂ) + w * (y : ℂ)) * Complex.I)‖ ≤
      Real.exp (M1 * |z.im| + M2 * |w.im|) := by
  run_tac
    let n : Lean.Name := .str (.str (.str
      (.num (.str (.str (.str (.str .anonymous "_private") "Shao")
        "Probability") "QuadraticComplexChord") 0) "Shao") "Probability") "qcc_phase_bound"
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply $(Lean.mkIdent n) <;> assumption))

private theorem contour_weighted_entire
    (a : ℝ → ℂ) (ha : Continuous a) (hai : Integrable a)
    (t1 t2 : ℝ → ℝ) (ht1 : Continuous t1) (ht2 : Continuous t2)
    (M1 M2 : ℝ) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hsupport : ∀ r ∈ tsupport a, |t1 r| ≤ M1 ∧ |t2 r| ≤ M2) :
    Differentiable ℂ (fun p : ℂ × ℂ =>
      ∫ r : ℝ, a r * Complex.exp
        ((p.1 * (t1 r : ℂ) + p.2 * (t2 r : ℂ)) * Complex.I)) := by
  let A : ℝ → (ℂ × ℂ →L[ℂ] ℂ) := fun r =>
    ((t1 r : ℂ) * Complex.I) • ContinuousLinearMap.fst ℂ ℂ ℂ +
      ((t2 r : ℂ) * Complex.I) • ContinuousLinearMap.snd ℂ ℂ ℂ
  let F : (ℂ × ℂ) → ℝ → ℂ := fun p r => a r * Complex.exp (A r p)
  let F' : (ℂ × ℂ) → ℝ → (ℂ × ℂ →L[ℂ] ℂ) :=
    fun p r => (a r * Complex.exp (A r p)) • A r
  have hAval (p : ℂ × ℂ) (r : ℝ) :
      A r p = (p.1 * (t1 r : ℂ) + p.2 * (t2 r : ℂ)) * Complex.I := by
    change (t1 r : ℂ) * Complex.I * p.1 + (t2 r : ℂ) * Complex.I * p.2 = _
    ring
  have hnorm (p : ℂ × ℂ) (r : ℝ) :
      ‖F p r‖ ≤ ‖a r‖ * Real.exp (M1 * |p.1.im| + M2 * |p.2.im|) := by
    by_cases hr : a r = 0
    · simp [F, hr]
    · have hs := hsupport r (subset_tsupport a hr)
      dsimp only [F]
      rw [norm_mul, hAval]
      exact mul_le_mul_of_nonneg_left
        (contour_phase_norm p.1 p.2 (t1 r) (t2 r) M1 M2 hs.1 hs.2) (norm_nonneg _)
  have hdiff : Differentiable ℂ (fun p : ℂ × ℂ => ∫ r : ℝ, F p r) := by
    intro p0
    let U : Set (ℂ × ℂ) := {p | |p.1.im| < |p0.1.im| + 1 ∧
      |p.2.im| < |p0.2.im| + 1}
    let C : ℝ := Real.exp (M1 * (|p0.1.im| + 1) + M2 * (|p0.2.im| + 1))
    have hU : U ∈ nhds p0 := by
      have h1 : IsOpen {p : ℂ × ℂ | |p.1.im| < |p0.1.im| + 1} :=
        isOpen_lt (by fun_prop) continuous_const
      have h2 : IsOpen {p : ℂ × ℂ | |p.2.im| < |p0.2.im| + 1} :=
        isOpen_lt (by fun_prop) continuous_const
      apply (h1.inter h2).mem_nhds
      change |p0.1.im| < |p0.1.im| + 1 ∧ |p0.2.im| < |p0.2.im| + 1
      constructor <;> linarith
    have hFi : Integrable (F p0) :=
      (hai.norm.mul_const _).mono' (by dsimp [F, A]; fun_prop) (ae_of_all _ (hnorm p0))
    have hderiv (p : ℂ × ℂ) (r : ℝ) :
        HasFDerivAt (fun p => F p r) (F' p r) p := by
      convert (((A r).hasFDerivAt.cexp).const_mul (a r)) using 1 <;>
        dsimp [F, F'] <;> simp only [smul_smul, smul_eq_mul]
    have hb : ∀ᵐ r : ℝ, ∀ p ∈ U, ‖F' p r‖ ≤ ‖a r‖ * ((M1 + M2) * C) := by
      filter_upwards [] with r
      intro p hp
      by_cases hr : a r = 0
      · dsimp only [F']
        rw [norm_smul, hr]
        simp
      · have hs := hsupport r (subset_tsupport a hr)
        have hA : ‖A r‖ ≤ M1 + M2 := by
          apply (A r).opNorm_le_bound (add_nonneg hM1 hM2)
          intro q
          change ‖(t1 r : ℂ) * Complex.I * q.1 + (t2 r : ℂ) * Complex.I * q.2‖ ≤ _
          have hq1 : ‖q.1‖ ≤ ‖q‖ := le_max_left _ _
          have hq2 : ‖q.2‖ ≤ ‖q‖ := le_max_right _ _
          calc
            _ ≤ ‖(t1 r : ℂ) * Complex.I * q.1‖ +
                ‖(t2 r : ℂ) * Complex.I * q.2‖ := norm_add_le _ _
            _ = |t1 r| * ‖q.1‖ + |t2 r| * ‖q.2‖ := by
              simp [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            _ ≤ M1 * ‖q‖ + M2 * ‖q‖ :=
              add_le_add (mul_le_mul hs.1 hq1 (norm_nonneg _) hM1)
                (mul_le_mul hs.2 hq2 (norm_nonneg _) hM2)
            _ = _ := by ring
        have hpval : ‖F p r‖ ≤ ‖a r‖ * C := by
          apply (hnorm p r).trans
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          apply Real.exp_le_exp.mpr
          exact add_le_add (mul_le_mul_of_nonneg_left hp.1.le hM1)
            (mul_le_mul_of_nonneg_left hp.2.le hM2)
        calc
          ‖F' p r‖ = ‖F p r‖ * ‖A r‖ := norm_smul _ _
          _ ≤ (‖a r‖ * C) * (M1 + M2) :=
            mul_le_mul hpval hA (norm_nonneg _) (by positivity)
          _ = _ := by ring
    exact (hasFDerivAt_integral_of_dominated_of_fderiv_le (F := F) (F' := F') hU
      (Eventually.of_forall fun p => (show Continuous (F p) by dsimp [F, A]; fun_prop).aestronglyMeasurable)
      hFi (show Continuous (F' p0) by dsimp [F', A]; fun_prop).aestronglyMeasurable hb
      (hai.norm.mul_const _) (ae_of_all _ fun r p _ => hderiv p r)).differentiableAt
  convert hdiff using 1
  funext p
  apply integral_congr_ae
  filter_upwards [] with r
  dsimp only [F]
  rw [hAval]

private theorem contour_boundary_entire (j : Fin 2) (y N lam : ℝ) :
    let Delta : ℝ := (1 + lam * y)⁻¹
    let c : ℝ → ℝ := fun r => sourceKernelCutoff r *
      (if j = 0 then sourceComplexSplitTheta ((r - N) / Delta)
        else 1 - sourceComplexSplitTheta ((r - N) / Delta))
    Differentiable ℂ (fun p : ℂ × ℂ =>
      ∫ r : ℝ, (c r : ℂ) * Complex.exp
        (-(p.1 * ((y * Real.sqrt r : ℝ) : ℂ) + p.2 * (r : ℂ)) * Complex.I)) := by
  dsimp only
  let c : ℝ → ℝ := fun r => sourceKernelCutoff r *
    (if j = 0 then sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹)
      else 1 - sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹))
  have hc : Continuous c := by
    have ht : Continuous (fun r : ℝ =>
        sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹)) :=
      sourceComplexSplitTheta_data.1.continuous.comp
        ((continuous_id.sub continuous_const).div_const _)
    by_cases hj : j = 0
    · convert sourceKernelCutoff_data.1.continuous.mul ht using 1
      funext r
      simp [c, hj]
    · convert sourceKernelCutoff_data.1.continuous.mul
        ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).sub ht) using 1
      funext r
      simp [c, hj]
  have hcs : tsupport c ⊆ tsupport sourceKernelCutoff := by
    apply closure_mono
    intro r hr hz
    exact hr (by dsimp [c]; rw [hz]; simp)
  have hcc : HasCompactSupport c := sourceKernelCutoff_data.2.1.of_isClosed_subset
    (isClosed_tsupport _) hcs
  have hai : Integrable (fun r : ℝ => (c r : ℂ)) :=
    (hc.integrable_of_hasCompactSupport hcc).ofReal (𝕜 := ℂ)
  have hacs : tsupport (fun r : ℝ => (c r : ℂ)) ⊆ tsupport c := by
    apply closure_mono
    intro r hr hz
    exact hr (by change (c r : ℂ) = 0; rw [hz]; rfl)
  have hb : ∀ r ∈ tsupport (fun r : ℝ => (c r : ℂ)),
      |-(y * Real.sqrt r)| ≤ 2 * |y| ∧ |(-r)| ≤ 4 := by
    intro r hr
    have hrc := sourceKernelCutoff_data.2.2.2.2 (hcs (hacs hr))
    have hrs : Real.sqrt r ≤ 2 := by
      nlinarith [hrc.2, Real.sq_sqrt (show 0 ≤ r by linarith [hrc.1]), Real.sqrt_nonneg r]
    constructor
    · rw [abs_neg, abs_mul, abs_of_nonneg (Real.sqrt_nonneg r)]
      nlinarith [abs_nonneg y, mul_le_mul_of_nonneg_left hrs (abs_nonneg y)]
    · rw [abs_neg, abs_of_pos (by linarith [hrc.1])]
      exact hrc.2.le
  have hd := contour_weighted_entire (fun r : ℝ => (c r : ℂ)) (by fun_prop) hai
    (fun r => -(y * Real.sqrt r)) (fun r => -r) (by fun_prop) (by fun_prop)
    (2 * |y|) 4 (by positivity) (by norm_num) hb
  convert hd using 1
  funext p
  apply integral_congr_ae
  filter_upwards [] with r
  congr 1
  congr 1
  push_cast
  ring

private theorem contour_split_cutoff_data (j : Fin 2) (y N lam : ℝ) :
    let Delta : ℝ := (1 + lam * y)⁻¹
    let c : ℝ → ℝ := fun r => sourceKernelCutoff r *
      (if j = 0 then sourceComplexSplitTheta ((r - N) / Delta)
        else 1 - sourceComplexSplitTheta ((r - N) / Delta))
    ContDiff ℝ ∞ c ∧ tsupport c ⊆ Set.Icc (1 / 16 : ℝ) 4 := by
  dsimp only
  let c : ℝ → ℝ := fun r => sourceKernelCutoff r *
    (if j = 0 then sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹)
      else 1 - sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹))
  have hc : ContDiff ℝ ∞ c := by
    have ht : ContDiff ℝ ∞ (fun r : ℝ =>
        sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹)) :=
      sourceComplexSplitTheta_data.1.comp (by fun_prop)
    by_cases hj : j = 0
    · convert sourceKernelCutoff_data.1.mul ht using 1
      funext r
      simp [c, hj]
    · convert sourceKernelCutoff_data.1.mul
        ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (1 : ℝ))).sub ht) using 1
      funext r
      simp [c, hj]
  refine ⟨hc, ?_⟩
  have hcs : tsupport c ⊆ tsupport sourceKernelCutoff := by
    apply closure_mono
    intro r hr hz
    exact hr (by dsimp [c]; rw [hz]; simp)
  intro r hr
  have h := sourceKernelCutoff_data.2.2.2.2 (hcs hr)
  exact ⟨h.1.le, h.2.le⟩

private theorem contour_integrand_entire
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (h : ℝ) (hh : 0 < h) (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (m : ℕ) (j d : Fin 2) (y N lam w q : ℝ) :
    Differentiable ℂ (fun p : ℂ × ℂ =>
      sourceComplexBoundaryContourIntegrand nu m j d y N lam w q p.1 p.2) := by
  have hp := (quadraticCharComplex_data nu h3 h hh hsupport).1
  have href : Differentiable ℂ (fun p : ℂ × ℂ => (-p.1, p.2)) := by fun_prop
  have hm := hp.comp href
  have hn := (quadraticComplexChord_extension_and_cone nu h3 hV h hh hsupport).2.2.2.1
  have hb := contour_boundary_entire j y N lam
  dsimp only at hb
  have he : Differentiable ℂ (fun p : ℂ × ℂ => Complex.exp (p.2 * (q : ℂ) * Complex.I)) :=
    (differentiable_snd.mul_const _ |>.mul_const _).cexp
  unfold sourceComplexBoundaryContourIntegrand
  dsimp only
  by_cases hd : d = 0
  · simp only [hd, ite_true]
    exact ((he.mul hb).mul hn).mul ((hp.pow m).sub (hm.pow m))
  · simp only [hd, ite_false]
    have hwplus : Differentiable ℂ (fun p : ℂ × ℂ =>
        Complex.exp (p.1 * (w : ℂ) * Complex.I)) :=
      (differentiable_fst.mul_const _ |>.mul_const _).cexp
    have hwminus : Differentiable ℂ (fun p : ℂ × ℂ =>
        Complex.exp (-p.1 * (w : ℂ) * Complex.I)) :=
      (differentiable_fst.neg.mul_const _ |>.mul_const _).cexp
    exact ((he.mul hb).mul hn).mul
      ((differentiable_fst.const_mul Complex.I).mul
        ((hwplus.mul (hp.pow m)).add (hwminus.mul (hm.pow m))))

private theorem contour_rectangle_limit
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) (a b : ℝ)
    (ha : Integrable (fun x : ℝ => F ((x : ℂ) + (a : ℂ) * Complex.I)))
    (hb : Integrable (fun x : ℝ => F ((x : ℂ) + (b : ℂ) * Complex.I)))
    (htop : Tendsto (fun R : ℝ =>
      ∫ eta : ℝ in a..b, F ((R : ℂ) + (eta : ℂ) * Complex.I)) atTop (nhds 0))
    (hbot : Tendsto (fun R : ℝ =>
      ∫ eta : ℝ in a..b, F ((R : ℂ) + (eta : ℂ) * Complex.I)) atBot (nhds 0)) :
    (∫ x : ℝ, F ((x : ℂ) + (a : ℂ) * Complex.I)) =
      ∫ x : ℝ, F ((x : ℂ) + (b : ℂ) * Complex.I) := by
  have hrect (R : ℝ) :
      (∫ x : ℝ in (-R)..R, F ((x : ℂ) + (a : ℂ) * Complex.I)) -
        (∫ x : ℝ in (-R)..R, F ((x : ℂ) + (b : ℂ) * Complex.I)) +
        Complex.I • (∫ eta : ℝ in a..b, F ((R : ℂ) + (eta : ℂ) * Complex.I)) -
        Complex.I • (∫ eta : ℝ in a..b,
          F (((-R : ℝ) : ℂ) + (eta : ℂ) * Complex.I)) = 0 := by
    have hr := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
      (((-R : ℝ) : ℂ) + (a : ℂ) * Complex.I)
      ((R : ℂ) + (b : ℂ) * Complex.I) hF.differentiableOn
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
      zero_mul, mul_one, one_mul, add_zero, zero_add, sub_zero] at hr
    convert hr using 1
  have hleft : Tendsto (fun R : ℝ =>
      ∫ eta : ℝ in a..b, F (((-R : ℝ) : ℂ) + (eta : ℂ) * Complex.I))
      atTop (nhds 0) := hbot.comp tendsto_neg_atTop_atBot
  have hI := (tendsto_const_nhds : Tendsto (fun _ : ℝ => Complex.I) atTop (nhds Complex.I))
  have hlim := ((intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id).sub
    (intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id)).add
      (hI.smul htop) |>.sub (hI.smul hleft)
  have hzero : Tendsto (fun R : ℝ =>
      (∫ x : ℝ in (-R)..R, F ((x : ℂ) + (a : ℂ) * Complex.I)) -
        (∫ x : ℝ in (-R)..R, F ((x : ℂ) + (b : ℂ) * Complex.I)) +
        Complex.I • (∫ eta : ℝ in a..b, F ((R : ℂ) + (eta : ℂ) * Complex.I)) -
        Complex.I • (∫ eta : ℝ in a..b, F (((-R : ℝ) : ℂ) +
          (eta : ℂ) * Complex.I))) atTop (nhds (0 : ℂ)) := by
    convert (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (nhds 0)) using 1
    funext R
    exact hrect R
  have heq := tendsto_nhds_unique hlim hzero
  apply sub_eq_zero.mp
  simpa only [smul_zero, add_zero, sub_zero] using heq

private theorem contour_translate_fourier_norm (f : ℝ → ℝ) (v c : ℝ) :
    ‖∫ r : ℝ, (f (r - c) : ℂ) *
      Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I))‖ =
      ‖∫ r : ℝ, (f r : ℂ) *
        Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I))‖ := by
  have he : (∫ r : ℝ, (f (r - c) : ℂ) *
      Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I))) =
      Complex.exp (-(((v * c : ℝ) : ℂ) * Complex.I)) *
        ∫ r : ℝ, (f r : ℂ) *
          Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I)) := by
    calc
      _ = ∫ r : ℝ, (f ((r + c) - c) : ℂ) *
          Complex.exp (-(((v * (r + c) : ℝ) : ℂ) * Complex.I)) :=
        (integral_add_right_eq_self (μ := (volume : Measure ℝ))
          (fun r => (f (r - c) : ℂ) *
            Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I))) c).symm
      _ = _ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with r
        simp only [add_sub_cancel_right]
        have he : -(↑(v * (r + c)) * Complex.I) =
            -(↑(v * c) * Complex.I) + -(↑(v * r) * Complex.I) := by
          push_cast
          ring
        rw [he, Complex.exp_add]
        ring
  rw [he, norm_mul]
  have hn : ‖Complex.exp (-(((v * c : ℝ) : ℂ) * Complex.I))‖ = 1 := by
    simp only [Complex.norm_exp, Complex.neg_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, neg_zero, Real.exp_zero]
  rw [hn, one_mul]

private theorem contour_uniform_fourier32
    (F : ℝ × ℝ × ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hsupp : ∀ p ∈ tsupport F, p.2.2 ∈ Set.Icc (1 / 16 : ℝ) 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ s theta v : ℝ,
      (1 + |v|) ^ 32 * ‖∫ r : ℝ, (F (s, theta, r) : ℂ) *
        Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I))‖ ≤ C := by
  run_tac
    let n : Lean.Name := .str (.str (.str
      (.num (.str (.str (.str (.str .anonymous "_private") "Shao")
        "Probability") "SourceKernelMarkedOutside") 0) "Shao") "Probability")
      "markedOscillatory_fourier_decay"
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply $(Lean.mkIdent n) <;> assumption))

private theorem contour_scalar_density_uniform_fourier
    (gamma lam : ℝ) (hlam : 0 ≤ lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ eta v : ℝ, |eta| ≤ lam →
      (1 + |v|) ^ 32 * ‖∫ t : ℝ,
        ((sourceScalarDensity t * Real.exp (-gamma * eta * t) : ℝ) : ℂ) *
          Complex.exp (-(((v * t : ℝ) : ℂ) * Complex.I))‖ ≤ C := by
  let etaCut : ContDiffBump (0 : ℝ) :=
    ⟨lam + 1, lam + 2, by linarith, by linarith⟩
  let auxCut : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let F : ℝ × ℝ × ℝ → ℝ := fun p =>
    etaCut p.1 * auxCut p.2.1 * sourceScalarDensity (p.2.2 - 2) *
      Real.exp (-gamma * p.1 * (p.2.2 - 2))
  let Box : Set (ℝ × ℝ × ℝ) := Set.Icc (-(lam + 2)) (lam + 2) ×ˢ
    (Set.Icc (-2 : ℝ) 2 ×ˢ Set.Icc (1 : ℝ) 3)
  have hF : ContDiff ℝ ∞ F := by
    have hd : ContDiff ℝ ∞ (fun p : ℝ × ℝ × ℝ => sourceScalarDensity (p.2.2 - 2)) :=
      sourceScalarDensity_data.1.comp (by fun_prop)
    exact (((etaCut.contDiff.comp contDiff_fst).mul
      (auxCut.contDiff.comp (contDiff_fst.comp contDiff_snd))).mul hd).mul (by fun_prop)
  have hsF : tsupport F ⊆ Box := by
    apply closure_minimal
    · intro p hp
      have hn : etaCut p.1 * auxCut p.2.1 * sourceScalarDensity (p.2.2 - 2) ≠ 0 :=
        left_ne_zero_of_mul hp
      have hrho : sourceScalarDensity (p.2.2 - 2) ≠ 0 := right_ne_zero_of_mul hn
      have hbase : etaCut p.1 * auxCut p.2.1 ≠ 0 := left_ne_zero_of_mul hn
      have he := subset_tsupport (etaCut : ℝ → ℝ) (left_ne_zero_of_mul hbase)
      have ht := subset_tsupport (auxCut : ℝ → ℝ) (right_ne_zero_of_mul hbase)
      rw [etaCut.tsupport_eq] at he
      rw [auxCut.tsupport_eq] at ht
      have he' : |p.1| ≤ lam + 2 := by simpa [etaCut, Real.dist_eq] using he
      have ht' : |p.2.1| ≤ 2 := by simpa [auxCut, Real.dist_eq] using ht
      have hr' : |p.2.2 - 2| < 1 := by
        by_contra hnot
        exact hrho (sourceScalarDensity_data.2.2.2.2.1 _ (le_of_not_gt hnot))
      have heq := abs_le.mp he'
      have htq := abs_le.mp ht'
      have hrq := abs_lt.mp hr'
      exact ⟨heq, htq, by linarith [hrq.1], by linarith [hrq.2]⟩
    · exact isClosed_Icc.prod (isClosed_Icc.prod isClosed_Icc)
  have hFc : HasCompactSupport F :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset
      (isClosed_tsupport _) hsF
  obtain ⟨C, hC, hb⟩ := contour_uniform_fourier32 F hF hFc (fun p hp => by
    have hr := (hsF hp).2.2
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩)
  refine ⟨C, hC, ?_⟩
  intro eta v heta
  have he : etaCut eta = 1 := by
    apply etaCut.one_of_mem_closedBall
    have hl : |eta| ≤ lam + 1 := by linarith
    simpa [etaCut, Real.dist_eq] using hl
  have ht : auxCut 0 = 1 := by
    apply auxCut.one_of_mem_closedBall
    norm_num [auxCut, Real.dist_eq]
  have hbound := hb eta 0 v
  simp only [F, he, ht, one_mul] at hbound
  have hn := contour_translate_fourier_norm
    (fun t : ℝ => sourceScalarDensity t * Real.exp (-gamma * eta * t)) v 2
  rw [hn] at hbound
  exact hbound

private theorem contour_real_oscillatory_bound (f phi : ℝ → ℝ) (v M : ℝ)
    (hM : 0 ≤ M) (hb : ∀ r, |f r| ≤ M)
    (hsupp : tsupport f ⊆ Set.Icc (1 / 16 : ℝ) 4) :
    ‖∫ r : ℝ, (f r : ℂ) * Complex.exp (((v * phi r : ℝ) : ℂ) * Complex.I)‖ ≤
      4 * M := by
  run_tac
    let n : Lean.Name := .str (.str (.str
      (.num (.str (.str (.str (.str .anonymous "_private") "Shao")
        "Probability") "SourceKernelMarkedOutside") 0) "Shao") "Probability")
      "markedOscillatory_norm_bound"
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply $(Lean.mkIdent n) <;> assumption))

private theorem contour_real_oscillatory_ibp (f q phi : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ (fun r => f r / q r))
    (hq : ∀ r ∈ tsupport f, q r ≠ 0)
    (hphi : Continuous phi) (hphid : ∀ r ∈ tsupport f, HasDerivAt phi (q r) r)
    (v : ℝ) :
    ((v : ℂ) * Complex.I) * (∫ r : ℝ, (f r : ℂ) *
        Complex.exp (((v * phi r : ℝ) : ℂ) * Complex.I)) =
      -(∫ r : ℝ, ((deriv (fun z => f z / q z) r : ℝ) : ℂ) *
        Complex.exp (((v * phi r : ℝ) : ℂ) * Complex.I)) := by
  run_tac
    let n : Lean.Name := .str (.str (.str
      (.num (.str (.str (.str (.str .anonymous "_private") "Shao")
        "Probability") "SourceKernelMarkedOutside") 0) "Shao") "Probability")
      "markedOscillatory_ibp"
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply $(Lean.mkIdent n) <;> assumption))

private theorem contour_quotient_regular
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F q : E → ℝ) (hF : ContDiff ℝ ∞ F)
    (hq : ∀ p ∈ tsupport F, ContDiffAt ℝ ∞ q p ∧ q p ≠ 0) :
    ContDiff ℝ ∞ (fun p => F p / q p) ∧
      tsupport (fun p => F p / q p) ⊆ tsupport F := by
  constructor
  · rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p ∈ tsupport F
    · exact hF.contDiffAt.div (hq p hp).1 (hq p hp).2
    · have he : F =ᶠ[nhds p] 0 := notMem_tsupport_iff_eventuallyEq.mp hp
      apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E => (0 : ℝ)) p).congr_of_eventuallyEq
      filter_upwards [he] with z hz
      simp only [Pi.zero_apply] at hz ⊢
      simp [hz]
  · apply closure_mono
    intro p hp hz
    exact hp (by simp [hz])

/-- A genuine compact-parameter nonstationary estimate. The recursive amplitudes
are constructed in the proof; no transform estimate is supplied as a premise. -/
private theorem contour_compact_family_power
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F q : E × ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hq : ∀ p ∈ tsupport F, ContDiffAt ℝ ∞ q p ∧ q p ≠ 0)
    (hsupp : ∀ p ∈ tsupport F, p.2 ∈ Set.Icc (1 / 16 : ℝ) 4) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (e : E) (phi : ℝ → ℝ), Continuous phi →
      (∀ r, (e, r) ∈ tsupport F → HasDerivAt phi (q (e, r)) r) →
      ∀ v : ℝ, |v| ^ n * ‖∫ r : ℝ, (F (e, r) : ℂ) *
        Complex.exp (((v * phi r : ℝ) : ℂ) * Complex.I)‖ ≤ C := by
  let D : E × ℝ := (0, 1)
  let J : ℕ → E × ℝ → ℝ := Nat.rec F
    (fun _ H p => fderiv ℝ (fun z => H z / q z) p D)
  have hreg (k : ℕ) : ContDiff ℝ ∞ (J k) ∧ tsupport (J k) ⊆ tsupport F := by
    induction k with
    | zero => exact ⟨hF, fun _ h => h⟩
    | succ k ih =>
      have hd := contour_quotient_regular (J k) q ih.1 (fun p hp => hq p (ih.2 hp))
      refine ⟨(hd.1.fderiv_right (by simp)).clm_apply contDiff_const, ?_⟩
      exact (tsupport_fderiv_apply_subset ℝ D).trans (hd.2.trans ih.2)
  have hslice (H : E × ℝ → ℝ) (hH : ContDiff ℝ ∞ H) (e : E) :
      ContDiff ℝ ∞ (fun r : ℝ => H (e, r)) :=
    hH.comp (contDiff_const.prodMk contDiff_id)
  have hmem (H : E × ℝ → ℝ) (e : E) (r : ℝ)
      (hr : r ∈ tsupport (fun t : ℝ => H (e, t))) : (e, r) ∈ tsupport H :=
    tsupport_comp_subset_preimage H (continuous_const.prodMk continuous_id) hr
  have hss (k : ℕ) (e : E) :
      tsupport (fun r : ℝ => J k (e, r)) ⊆ Set.Icc (1 / 16 : ℝ) 4 :=
    fun r hr => hsupp (e, r) ((hreg k).2 (hmem _ e r hr))
  have hsc (k : ℕ) (e : E) : HasCompactSupport (fun r : ℝ => J k (e, r)) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hss k e)
  obtain ⟨M, hM⟩ := Continuous.bounded_above_of_compact_support (hreg n).1.continuous
    (hFc.of_isClosed_subset (isClosed_tsupport _) (hreg n).2)
  refine ⟨4 * max 0 M, by positivity, ?_⟩
  intro e phi hphi hphid v
  have hstep (k : ℕ) :
      |v| * ‖∫ r : ℝ, (Complex.ofReal (J k (e, r))) *
        Complex.exp (((v * phi r : ℝ) : ℂ) * Complex.I)‖ =
      ‖∫ r : ℝ, (Complex.ofReal (J (k + 1) (e, r))) *
        Complex.exp (((v * phi r : ℝ) : ℂ) * Complex.I)‖ := by
    have hd := contour_quotient_regular (J k) q (hreg k).1
      (fun p hp => hq p ((hreg k).2 hp))
    have hder : deriv (fun r : ℝ => J k (e, r) / q (e, r)) =
        fun r : ℝ => J (k + 1) (e, r) := by
      funext r
      have he : HasDerivAt (fun r : ℝ => ((e, r) : E × ℝ)) D r := by
        simpa only [D, id_eq] using (hasDerivAt_const r e).prodMk (hasDerivAt_id r)
      exact ((hd.1.differentiable (by simp) (e, r)).hasFDerivAt.comp_hasDerivAt r he).deriv
    have hi := contour_real_oscillatory_ibp (fun r => J k (e, r))
      (fun r => q (e, r)) phi (hslice _ (hreg k).1 e) (hsc k e)
      (hslice _ hd.1 e)
      (fun r hr => (hq _ ((hreg k).2 (hmem _ e r hr))).2) hphi
      (fun r hr => hphid r ((hreg k).2 (hmem _ e r hr))) v
    rw [hder] at hi
    have hh := congrArg norm hi
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      mul_one, norm_neg] using hh
  have heq (k : ℕ) : |v| ^ k * ‖∫ r : ℝ, (F (e, r) : ℂ) *
      Complex.exp (((v * phi r : ℝ) : ℂ) * Complex.I)‖ =
      ‖∫ r : ℝ, (Complex.ofReal (J k (e, r))) *
        Complex.exp (((v * phi r : ℝ) : ℂ) * Complex.I)‖ := by
    induction k with
    | zero => simp [J]
    | succ k ih =>
      rw [pow_succ, mul_comm (|v| ^ k), mul_assoc, ih]
      exact hstep k
  rw [heq n]
  exact contour_real_oscillatory_bound _ phi v (max 0 M) (le_max_left _ _)
    (fun r => (show |J n (e, r)| ≤ M by simpa only [Real.norm_eq_abs] using hM (e, r)).trans
      (le_max_right _ _)) (hss n e)

private theorem contour_scalar_strip_decay
    (gamma lam : ℝ) (hgamma : 0 < gamma) (hlam : 0 ≤ lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ u eta : ℝ, |eta| ≤ lam →
      (1 + |u|) ^ 8 * ‖∫ t : ℝ,
        Complex.exp ((gamma : ℂ) * ((u : ℂ) + (eta : ℂ) * Complex.I) *
          (t : ℂ) * Complex.I) ∂sourceScalarLaw‖ ≤ C := by
  obtain ⟨C0, hC0, hb⟩ := contour_scalar_density_uniform_fourier gamma lam hlam
  let A : ℝ := 1 + gamma⁻¹
  have hA : 1 ≤ A := by dsimp [A]; linarith [inv_nonneg.mpr hgamma.le]
  refine ⟨A ^ 8 * C0, by positivity, ?_⟩
  intro u eta heta
  have he : (∫ t : ℝ,
      Complex.exp ((gamma : ℂ) * ((u : ℂ) + (eta : ℂ) * Complex.I) *
        (t : ℂ) * Complex.I) ∂sourceScalarLaw) =
      ∫ t : ℝ, ((sourceScalarDensity t * Real.exp (-gamma * eta * t) : ℝ) : ℂ) *
        Complex.exp (-((((-gamma * u) * t : ℝ) : ℂ) * Complex.I)) := by
    unfold sourceScalarLaw
    rw [integral_withDensity_eq_integral_toReal_smul
      sourceScalarDensity_data.1.continuous.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [ENNReal.toReal_ofReal (sourceScalarDensity_data.2.2.1 t),
      Complex.real_smul, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_exp]
    calc
      _ = (sourceScalarDensity t : ℂ) * Complex.exp
          (((-gamma * eta * t : ℝ) : ℂ) +
            -((((-gamma * u) * t : ℝ) : ℂ) * Complex.I)) := by
        congr 1
        congr 1
        push_cast
        ring_nf
        simp only [Complex.I_sq]
        ring
      _ = _ := by rw [Complex.exp_add]; push_cast; ring
  rw [he]
  have hsize : 1 + |u| ≤ A * (1 + |-gamma * u|) := by
    rw [abs_mul, abs_neg, abs_of_pos hgamma]
    dsimp [A]
    have he : gamma⁻¹ * gamma = 1 := inv_mul_cancel₀ hgamma.ne'
    nlinarith [abs_nonneg u, inv_nonneg.mpr hgamma.le]
  have hp : (1 + |-gamma * u|) ^ 8 ≤ (1 + |-gamma * u|) ^ 32 :=
    pow_le_pow_right₀ (by linarith [abs_nonneg (-gamma * u)]) (by norm_num)
  calc
    _ ≤ (A * (1 + |-gamma * u|)) ^ 8 * ‖∫ t : ℝ,
        ((sourceScalarDensity t * Real.exp (-gamma * eta * t) : ℝ) : ℂ) *
          Complex.exp (-((((-gamma * u) * t : ℝ) : ℂ) * Complex.I))‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hsize 8) (norm_nonneg _)
    _ = A ^ 8 * ((1 + |-gamma * u|) ^ 8 * ‖∫ t : ℝ,
        ((sourceScalarDensity t * Real.exp (-gamma * eta * t) : ℝ) : ℂ) *
          Complex.exp (-((((-gamma * u) * t : ℝ) : ℂ) * Complex.I))‖) := by ring
    _ ≤ A ^ 8 * ((1 + |-gamma * u|) ^ 32 * ‖∫ t : ℝ,
        ((sourceScalarDensity t * Real.exp (-gamma * eta * t) : ℝ) : ℂ) *
          Complex.exp (-((((-gamma * u) * t : ℝ) : ℂ) * Complex.I))‖) := by
      gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb eta (-gamma * u) heta) (by positivity)

private theorem contour_noise_strip_decay
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (h : ℝ) (hh : 0 < h) (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (lam s : ℝ) (hlam : 0 ≤ lam) (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v eta xi : ℝ, |eta| ≤ lam → |xi| ≤ s →
      (1 + |u|) ^ 8 * ‖quadraticFullNoiseCharComplex nu
        ((u : ℂ) + (eta : ℂ) * Complex.I)
        ((v : ℂ) + (xi : ℂ) * Complex.I)‖ ≤ C := by
  let gamma : ℝ := (∫ a : ℝ, |a| ^ 3 ∂nu) / variance (id : ℝ → ℝ) nu
  have hm3 : 0 < ∫ a : ℝ, |a| ^ 3 ∂nu := by
    run_tac
      let n : Lean.Name := .str (.str (.str
        (.num (.str (.str (.str (.str .anonymous "_private") "Shao")
          "Probability") "SourceFutureNoiseInversion") 0) "Shao") "Probability")
        "third_moment_pos"
      Lean.Elab.Tactic.evalTactic (← `(tactic| apply $(Lean.mkIdent n) <;> assumption))
  have hg : 0 < gamma := div_pos hm3 hV
  obtain ⟨Cs, hCs, hb⟩ := contour_scalar_strip_decay gamma lam hg hlam
  let L : ℝ := Real.exp (2 * h * lam + 4 * h ^ 2 * s)
  have hL : 0 < L := Real.exp_pos _
  have hdata := (quadraticComplexChord_extension_and_cone nu h3 hV h hh hsupport).2.2.2.2.1
  have hK (z zeta : ℂ) (hz : |z.im| ≤ lam) (hw : |zeta.im| ≤ s) :
      ‖quadraticChordCharComplex nu z zeta‖ ≤ L := by
    rcases hdata z zeta with ⟨_, _, _, hk, _, _, _, _⟩
    exact hk.trans (Real.exp_le_exp.mpr (add_le_add
      (mul_le_mul_of_nonneg_left hz (by positivity))
      (mul_le_mul_of_nonneg_left hw (by positivity))))
  refine ⟨L ^ 8 * L ^ 8 * Cs, by positivity, ?_⟩
  intro u v eta xi heta hxi
  let z : ℂ := (u : ℂ) + (eta : ℂ) * Complex.I
  let zeta : ℂ := (v : ℂ) + (xi : ℂ) * Complex.I
  have hz : |z.im| ≤ lam := by simpa [z] using heta
  have hmz : |(-z).im| ≤ lam := by simpa [z, abs_neg] using heta
  have hw : |zeta.im| ≤ s := by simpa [zeta] using hxi
  have hk := pow_le_pow_left₀ (norm_nonneg _) (hK z zeta hz hw) 8
  have hkm := pow_le_pow_left₀ (norm_nonneg _) (hK (-z) zeta hmz hw) 8
  rcases hdata z zeta with ⟨_, _, _, _, _, _, _, hprod⟩
  change (1 + |u|) ^ 8 * ‖quadraticFullNoiseCharComplex nu z zeta‖ ≤ _
  rw [hprod, norm_mul, norm_mul, norm_pow, norm_pow]
  calc
    _ = ‖quadraticChordCharComplex nu z zeta‖ ^ 8 *
        ‖quadraticChordCharComplex nu (-z) zeta‖ ^ 8 *
        ((1 + |u|) ^ 8 * ‖∫ t : ℝ, Complex.exp
          ((gamma : ℂ) * z * (t : ℂ) * Complex.I) ∂sourceScalarLaw‖) := by ring
    _ ≤ (L ^ 8 * L ^ 8) * Cs :=
      mul_le_mul (mul_le_mul hk hkm (by positivity) (by positivity))
        (hb u eta heta) (by positivity) (by positivity)
    _ = _ := by ring

private theorem contour_smooth_sqrt :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧
      (∀ r : ℝ, (1 / 16 : ℝ) ≤ r → g r = Real.sqrt r) ∧
      ∃ M : ℝ, 1 ≤ M ∧ ∀ k : ℕ, k ≤ 32 →
        ∀ r ∈ Set.Icc (1 / 16 : ℝ) 4, |iteratedDeriv k g r| ≤ M := by
  run_tac
    let n : Lean.Name := .str (.str (.str
      (.num (.str (.str (.str (.str .anonymous "_private") "Shao")
        "Probability") "SourceComplexBoundaryAmplitude") 0) "Shao") "Probability")
      "smooth_sqrt_extension"
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n)))

private theorem contour_strip_boundary_fourier
    (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
    (has : tsupport a ⊆ Set.Icc (1 / 16 : ℝ) 4)
    (y lam s : ℝ) (hlam : 0 ≤ lam) (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v eta xi : ℝ, |eta| ≤ lam → |xi| ≤ s →
      (1 + |v|) ^ 3 * ‖∫ r : ℝ,
        ((a r * Real.exp (eta * y * Real.sqrt r + xi * r) : ℝ) : ℂ) *
          Complex.exp (-(((u * y * Real.sqrt r + v * r : ℝ) : ℂ) * Complex.I))‖ ≤
        C * (1 + |u|) ^ 3 := by
  obtain ⟨g, hg, hgeq, _⟩ := contour_smooth_sqrt
  let ec : ContDiffBump (0 : ℝ) := ⟨lam + 1, lam + 2, by linarith, by linarith⟩
  let xc : ContDiffBump (0 : ℝ) := ⟨s + 1, s + 2, by linarith, by linarith⟩
  let tc : ContDiffBump (0 : ℝ) := ⟨1 / 16, 1 / 8, by norm_num, by norm_num⟩
  let F : (ℝ × ℝ × ℝ) × ℝ → ℝ := fun p =>
    ec p.1.1 * xc p.1.2.1 * tc p.1.2.2 * a p.2 *
      Real.exp (p.1.1 * y * g p.2 + p.1.2.1 * p.2)
  let Q : (ℝ × ℝ × ℝ) × ℝ → ℝ := fun p => p.1.2.2 / (2 * g p.2) - 1
  let Box : Set ((ℝ × ℝ × ℝ) × ℝ) :=
    (Set.Icc (-(lam + 2)) (lam + 2) ×ˢ
      (Set.Icc (-(s + 2)) (s + 2) ×ˢ Set.Icc (-1 / 8 : ℝ) (1 / 8))) ×ˢ
        Set.Icc (1 / 16 : ℝ) 4
  have hF : ContDiff ℝ ∞ F := by
    have he : ContDiff ℝ ∞ (fun p : (ℝ × ℝ × ℝ) × ℝ => ec p.1.1) :=
      ec.contDiff.comp (contDiff_fst.comp contDiff_fst)
    have hx : ContDiff ℝ ∞ (fun p : (ℝ × ℝ × ℝ) × ℝ => xc p.1.2.1) :=
      xc.contDiff.comp (by fun_prop)
    have ht : ContDiff ℝ ∞ (fun p : (ℝ × ℝ × ℝ) × ℝ => tc p.1.2.2) :=
      tc.contDiff.comp (by fun_prop)
    exact (((he.mul hx).mul ht).mul (ha.comp contDiff_snd)).mul
      ((((contDiff_fst.comp contDiff_fst).mul contDiff_const).mul
        (hg.comp contDiff_snd)).add (by fun_prop)).exp
  have hFs : tsupport F ⊆ Box := by
    apply closure_minimal
    · intro p hp
      have hbase : ec p.1.1 * xc p.1.2.1 * tc p.1.2.2 * a p.2 ≠ 0 :=
        left_ne_zero_of_mul hp
      have har : a p.2 ≠ 0 := right_ne_zero_of_mul hbase
      have hb : ec p.1.1 * xc p.1.2.1 * tc p.1.2.2 ≠ 0 := left_ne_zero_of_mul hbase
      have hbt : tc p.1.2.2 ≠ 0 := right_ne_zero_of_mul hb
      have hbx : ec p.1.1 * xc p.1.2.1 ≠ 0 := left_ne_zero_of_mul hb
      have he := subset_tsupport (ec : ℝ → ℝ) (left_ne_zero_of_mul hbx)
      have hx := subset_tsupport (xc : ℝ → ℝ) (right_ne_zero_of_mul hbx)
      have ht := subset_tsupport (tc : ℝ → ℝ) hbt
      rw [ec.tsupport_eq] at he
      rw [xc.tsupport_eq] at hx
      rw [tc.tsupport_eq] at ht
      have he' : |p.1.1| ≤ lam + 2 := by simpa [ec, Real.dist_eq] using he
      have hx' : |p.1.2.1| ≤ s + 2 := by simpa [xc, Real.dist_eq] using hx
      have ht' : |p.1.2.2| ≤ (1 / 8 : ℝ) := by simpa [tc, Real.dist_eq] using ht
      exact ⟨⟨abs_le.mp he', abs_le.mp hx',
        by constructor <;> linarith [(abs_le.mp ht').1, (abs_le.mp ht').2]⟩,
        has (subset_tsupport a har)⟩
    · exact (isClosed_Icc.prod (isClosed_Icc.prod isClosed_Icc)).prod isClosed_Icc
  have hFc : HasCompactSupport F :=
    ((isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).prod isCompact_Icc).of_isClosed_subset
      (isClosed_tsupport _) hFs
  have hQ : ∀ p ∈ tsupport F, ContDiffAt ℝ ∞ Q p ∧ Q p ≠ 0 := by
    intro p hp
    have hr := (hFs hp).2
    have hgs : g p.2 = Real.sqrt p.2 := hgeq _ hr.1
    have hgpos : (1 / 4 : ℝ) ≤ g p.2 := by
      rw [hgs]
      nlinarith [hr.1, Real.sq_sqrt (show 0 ≤ p.2 by linarith [hr.1]), Real.sqrt_nonneg p.2]
    have hden : 0 < 2 * g p.2 := by linarith
    refine ⟨((contDiffAt_snd.comp p (contDiffAt_snd.comp p contDiffAt_fst)).div
      (contDiffAt_const.mul (hg.contDiffAt.comp p contDiffAt_snd)) hden.ne').sub
        contDiffAt_const, ?_⟩
    have ht := (hFs hp).1.2.2.2
    have hle : p.1.2.2 / (2 * g p.2) ≤ (1 / 4 : ℝ) :=
      (div_le_iff₀ hden).mpr (by nlinarith)
    dsimp only [Q]
    linarith
  obtain ⟨C0, hC0, hpower⟩ := contour_compact_family_power F Q hF hFc hQ
    (fun p hp => (hFs hp).2) 3
  obtain ⟨M0, hM0⟩ := Continuous.bounded_above_of_compact_support hF.continuous hFc
  let M : ℝ := max 0 M0
  have hM : 0 ≤ M := le_max_left _ _
  have hMb (p) : |F p| ≤ M :=
    (show |F p| ≤ M0 by simpa only [Real.norm_eq_abs] using hM0 p).trans (le_max_right _ _)
  have hec (eta : ℝ) (heta : |eta| ≤ lam) : ec eta = 1 := by
    apply ec.one_of_mem_closedBall
    have h : |eta| ≤ lam + 1 := by linarith
    simpa [ec, Real.dist_eq] using h
  have hxc (xi : ℝ) (hxi : |xi| ≤ s) : xc xi = 1 := by
    apply xc.one_of_mem_closedBall
    have h : |xi| ≤ s + 1 := by linarith
    simpa [xc, Real.dist_eq] using h
  have htc (t : ℝ) (ht : |t| ≤ (1 / 16 : ℝ)) : tc t = 1 := by
    apply tc.one_of_mem_closedBall
    simpa [tc, Real.dist_eq] using ht
  have hFe (eta xi t r : ℝ) (heta : |eta| ≤ lam) (hxi : |xi| ≤ s)
      (ht : |t| ≤ (1 / 16 : ℝ)) :
      F ((eta, xi, t), r) = a r * Real.exp (eta * y * Real.sqrt r + xi * r) := by
    dsimp only [F]
    rw [hec eta heta, hxc xi hxi, htc t ht, one_mul, one_mul, one_mul]
    by_cases hr : a r = 0
    · simp [hr]
    · rw [hgeq r (has (subset_tsupport a hr)).1]
  let C : ℝ := max (8 * C0) ((2 + 16 * |y|) ^ 3 * (4 * M)) + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro u v eta xi heta hxi
  let B : ℂ := ∫ r : ℝ,
    ((a r * Real.exp (eta * y * Real.sqrt r + xi * r) : ℝ) : ℂ) *
      Complex.exp (-(((u * y * Real.sqrt r + v * r : ℝ) : ℂ) * Complex.I))
  have hbound : ‖B‖ ≤ 4 * M := by
    have h := contour_real_oscillatory_bound (fun r => F ((eta, xi, 0), r))
      (fun r => -(u * y * Real.sqrt r + v * r)) 1 M hM
      (fun r => hMb _) (fun r hr => (hFs
        (tsupport_comp_subset_preimage F (continuous_const.prodMk continuous_id) hr)).2)
    simpa only [B, hFe eta xi 0 _ heta hxi (by norm_num), one_mul,
      Complex.ofReal_neg, neg_mul] using h
  change (1 + |v|) ^ 3 * ‖B‖ ≤ C * (1 + |u|) ^ 3
  by_cases hv : |v| ≤ 1 + 16 * |u * y|
  · have hsize : 1 + |v| ≤ (2 + 16 * |y|) * (1 + |u|) := by
      rw [abs_mul] at hv
      nlinarith [abs_nonneg u, abs_nonneg y]
    calc
      _ ≤ ((2 + 16 * |y|) * (1 + |u|)) ^ 3 * (4 * M) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hsize 3) hbound
          (norm_nonneg _) (by positivity)
      _ = ((2 + 16 * |y|) ^ 3 * (4 * M)) * (1 + |u|) ^ 3 := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact (le_max_right _ _).trans (by dsimp [C]; linarith)
  · have hv1 : 1 < |v| := by linarith [abs_nonneg (u * y)]
    have hv0 : v ≠ 0 := by intro hz; rw [hz, abs_zero] at hv1; linarith
    let t : ℝ := -u * y / v
    have ht : |t| ≤ (1 / 16 : ℝ) := by
      dsimp [t]
      rw [abs_div, abs_mul, abs_neg]
      apply (div_le_iff₀ (lt_trans (by norm_num : (0 : ℝ) < 1) hv1)).mpr
      rw [abs_mul] at hv
      linarith
    have hphi : ∀ r, (((eta, xi, t), r) : (ℝ × ℝ × ℝ) × ℝ) ∈ tsupport F →
        HasDerivAt (fun r => t * Real.sqrt r - r) (Q ((eta, xi, t), r)) r := by
      intro r hr
      have hrlo := (hFs hr).2.1
      have hr0 : r ≠ 0 := by linarith
      convert ((Real.hasDerivAt_sqrt hr0).const_mul t).sub (hasDerivAt_id r) using 1
      · funext z
        rfl
      · change t / (2 * g r) - 1 = t * (1 / (2 * Real.sqrt r)) - 1
        rw [hgeq r hrlo]
        ring
    have hp := hpower (eta, xi, t) (fun r => t * Real.sqrt r - r) (by fun_prop) hphi v
    have hBe : B = ∫ r : ℝ, (F ((eta, xi, t), r) : ℂ) *
        Complex.exp (((v * (t * Real.sqrt r - r) : ℝ) : ℂ) * Complex.I) := by
      apply integral_congr_ae
      filter_upwards [] with r
      rw [hFe eta xi t r heta hxi ht]
      have he : v * (t * Real.sqrt r - r) = -(u * y * Real.sqrt r + v * r) := by
        dsimp [t]
        field_simp
        ring
      rw [he, Complex.ofReal_neg, neg_mul]
    rw [← hBe] at hp
    calc
      _ ≤ (2 * |v|) ^ 3 * ‖B‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) 3)
          (norm_nonneg _)
      _ = 8 * (|v| ^ 3 * ‖B‖) := by ring
      _ ≤ 8 * C0 := mul_le_mul_of_nonneg_left hp (by norm_num)
      _ ≤ C := (le_max_left _ _).trans (by dsimp [C]; linarith)
      _ ≤ C * (1 + |u|) ^ 3 := le_mul_of_one_le_right (by dsimp [C]; positivity)
        (one_le_pow₀ (by linarith [abs_nonneg u]))

private theorem contour_boundary_strip_decay (j : Fin 2) (y N lam s : ℝ)
    (hlam : 0 ≤ lam) (hs : 0 ≤ s) :
    let Delta : ℝ := (1 + lam * y)⁻¹
    let c : ℝ → ℝ := fun r => sourceKernelCutoff r *
      (if j = 0 then sourceComplexSplitTheta ((r - N) / Delta)
        else 1 - sourceComplexSplitTheta ((r - N) / Delta))
    ∃ C : ℝ, 0 < C ∧ ∀ u v eta xi : ℝ, |eta| ≤ lam → |xi| ≤ s →
      (1 + |v|) ^ 3 * ‖∫ r : ℝ, (c r : ℂ) * Complex.exp
        (-(((u : ℂ) + (eta : ℂ) * Complex.I) * ((y * Real.sqrt r : ℝ) : ℂ) +
          ((v : ℂ) + (xi : ℂ) * Complex.I) * (r : ℂ)) * Complex.I)‖ ≤
        C * (1 + |u|) ^ 3 := by
  dsimp only
  let c : ℝ → ℝ := fun r => sourceKernelCutoff r *
    (if j = 0 then sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹)
      else 1 - sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹))
  have hc := contour_split_cutoff_data j y N lam
  obtain ⟨C, hC, hb⟩ := contour_strip_boundary_fourier c hc.1 hc.2 y lam s hlam hs
  refine ⟨C, hC, ?_⟩
  intro u v eta xi heta hxi
  convert hb u v eta xi heta hxi using 1
  congr 2
  apply integral_congr_ae
  filter_upwards [] with r
  have hp := contour_shifted_phase u v (-eta) xi (y * Real.sqrt r) r
  simp only [Complex.ofReal_neg, neg_mul, sub_neg_eq_add, neg_neg] at hp
  have hp' : Complex.exp
      (-(((u : ℂ) + (eta : ℂ) * Complex.I) * ((y * Real.sqrt r : ℝ) : ℂ) +
        ((v : ℂ) + (xi : ℂ) * Complex.I) * (r : ℂ)) * Complex.I) =
      (Real.exp (eta * (y * Real.sqrt r) + xi * r) : ℂ) *
        Complex.exp (-(((u * (y * Real.sqrt r) + v * r : ℝ) : ℂ)) * Complex.I) := by
    convert hp using 1 <;> congr 1 <;> ring
  rw [hp']
  have he : eta * (y * Real.sqrt r) + xi * r = eta * y * Real.sqrt r + xi * r := by ring
  have hf : u * (y * Real.sqrt r) + v * r = u * y * Real.sqrt r + v * r := by ring
  rw [he, hf]
  dsimp only [c]
  push_cast
  simp only [mul_assoc, neg_mul] <;> ring

private theorem contour_power_profile (n : ℕ) (hn : 3 ≤ n) :
    Integrable (fun v : ℝ => 1 / (1 + |v|) ^ n) ∧
      (∫ v : ℝ, 1 / (1 + |v|) ^ n) ≤ 1 := by
  have hi (k : ℕ) (hk : 1 < k) : Integrable (fun v : ℝ => 1 / (1 + |v|) ^ k) := by
    run_tac
      let n : Lean.Name := .str (.str (.str
        (.num (.str (.str (.str (.str .anonymous "_private") "Shao")
          "Probability") "SourceKernelMarkedOutside") 0) "Shao") "Probability")
        "outsidePowerProfile_integrable"
      Lean.Elab.Tactic.evalTactic (← `(tactic| apply $(Lean.mkIdent n) <;> assumption))
  have htail : (∫ v : ℝ in {v : ℝ | (0 : ℝ) < |v|}, (1 + |v|) ^ (-3 : ℝ)) = 1 := by
    have he : (∫ v : ℝ in {v : ℝ | (0 : ℝ) < |v|}, (1 + |v|) ^ (-3 : ℝ)) =
        2 * (-(1 + (0 : ℝ)) ^ ((-3 : ℝ) + 1) / ((-3 : ℝ) + 1)) := by
      run_tac
        let n : Lean.Name := .str (.str (.str
          (.num (.str (.str (.str (.str .anonymous "_private") "Shao")
            "Probability") "SourceKernelMarkedOutside") 0) "Shao") "Probability")
          "outsideAbsProfile_tail"
        Lean.Elab.Tactic.evalTactic (← `(tactic| apply $(Lean.mkIdent n) <;> norm_num))
    norm_num at he
    simpa using he
  have hset : {v : ℝ | (0 : ℝ) < |v|} =ᵐ[volume] Set.univ := by
    have hz : ∀ᵐ v : ℝ ∂volume, v ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [hz] with v hv
    simp [abs_pos, hv]
  rw [Measure.restrict_congr_set hset, Measure.restrict_univ] at htail
  have he (v : ℝ) : (1 + |v|) ^ (-3 : ℝ) = 1 / (1 + |v|) ^ 3 := by
    rw [show (-3 : ℝ) = -(3 : ℝ) by norm_num, Real.rpow_neg (by positivity)]
    norm_num [one_div]
  simp_rw [he] at htail
  have hle (v : ℝ) : 1 / (1 + |v|) ^ n ≤ 1 / (1 + |v|) ^ 3 :=
    one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by linarith [abs_nonneg v]) hn)
  refine ⟨hi n (by omega), ?_⟩
  exact (integral_mono (hi n (by omega)) (hi 3 (by norm_num)) hle).trans htail.le

private theorem contour_dominated_product
    (mu nu : Measure ℝ) [SFinite mu] [SFinite nu]
    (f : ℝ × ℝ → ℂ) (hf : Continuous f)
    (g h : ℝ → ℝ) (hg : Integrable g mu) (hh : Integrable h nu)
    (hb : ∀ᵐ p : ℝ × ℝ ∂mu.prod nu, ‖f p‖ ≤ g p.1 * h p.2) :
    Integrable f (mu.prod nu) ∧
      (∫ p : ℝ × ℝ, ‖f p‖ ∂mu.prod nu) ≤ (∫ u : ℝ, g u ∂mu) * (∫ v : ℝ, h v ∂nu) := by
  have hi := hg.mul_prod hh
  have hfi : Integrable f (mu.prod nu) := hi.mono' hf.aestronglyMeasurable hb
  refine ⟨hfi, ?_⟩
  exact (integral_mono_ae hfi.norm hi hb).trans_eq (integral_prod_mul g h)

private theorem contour_coordinate_exp_bound (u eta w L : ℝ) (hL : 0 ≤ L)
    (heta : |eta| ≤ L) :
    ‖Complex.exp (((u : ℂ) + (eta : ℂ) * Complex.I) * (w : ℂ) * Complex.I)‖ ≤
      Real.exp (L * |w|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have he : ((((u : ℂ) + (eta : ℂ) * Complex.I) * (w : ℂ) * Complex.I).re) =
      -(eta * w) := by simp [Complex.mul_re, Complex.mul_im]
  rw [he]
  exact (neg_le_abs (eta * w)).trans (by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right heta (abs_nonneg w))

private theorem contour_integrand_strip_bound
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (h : ℝ) (hh : 0 < h) (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (m : ℕ) (y N lam s w q : ℝ) (hlam : 0 ≤ lam) (hs : 0 ≤ s) :
    ∃ B : ℝ, 0 < B ∧ ∀ (j d : Fin 2) (u v eta xi : ℝ),
      |eta| ≤ lam → |xi| ≤ s →
      ‖sourceComplexBoundaryContourIntegrand nu m j d y N lam w q
        ((u : ℂ) + (eta : ℂ) * Complex.I)
        ((v : ℂ) + (xi : ℂ) * Complex.I)‖ ≤
        B / ((1 + |u|) ^ (5 - d.val) * (1 + |v|) ^ 3) := by
  have hcb := fun j : Fin 2 => contour_boundary_strip_decay j y N lam s hlam hs
  choose C hC hcb using hcb
  let Cb : ℝ := ∑ j : Fin 2, C j
  have hCb : 0 < Cb := Finset.sum_pos (fun j _ => hC j) (by simp)
  have hCble (j : Fin 2) : C j ≤ Cb :=
    Finset.single_le_sum (fun i _ => (hC i).le) (Finset.mem_univ j)
  obtain ⟨Cx, hCx, hxb⟩ := contour_noise_strip_decay nu h3 hV h hh hsupport lam s hlam hs
  let P : ℝ := Real.exp (h * lam + h ^ 2 * s)
  let Ew : ℝ := Real.exp (lam * |w|)
  let Eq : ℝ := Real.exp (s * |q|)
  let Cr : ℝ := 2 * P ^ m * (1 + (1 + lam) * Ew)
  let B : ℝ := Eq * Cb * Cx * Cr
  have hP : 0 < P := Real.exp_pos _
  have hEw : 0 < Ew := Real.exp_pos _
  have hEq : 0 < Eq := Real.exp_pos _
  have hCr : 0 < Cr := by dsimp [Cr]; positivity
  have hchar := (quadraticCharComplex_data nu h3 h hh hsupport).2.1
  have hphi (z zeta : ℂ) (hz : |z.im| ≤ lam) (hw : |zeta.im| ≤ s) :
      ‖quadraticCharComplex nu z zeta ^ m‖ ≤ P ^ m := by
    rw [norm_pow]
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact (hchar z zeta).2.trans (Real.exp_le_exp.mpr (add_le_add
      (mul_le_mul_of_nonneg_left hz hh.le)
      (mul_le_mul_of_nonneg_left hw (sq_nonneg h))))
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  intro j d u v eta xi heta hxi
  let z : ℂ := (u : ℂ) + (eta : ℂ) * Complex.I
  let zeta : ℂ := (v : ℂ) + (xi : ℂ) * Complex.I
  let A : ℝ := 1 + |u|
  let D : ℝ := 1 + |v|
  let H : ℂ := ∫ r : ℝ,
    ((sourceKernelCutoff r * (if j = 0 then
      sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹)
      else 1 - sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹)) : ℝ) : ℂ) *
      Complex.exp (-(z * ((y * Real.sqrt r : ℝ) : ℂ) + zeta * (r : ℂ)) * Complex.I)
  let R : ℂ := if d = 0 then quadraticCharComplex nu z zeta ^ m -
      quadraticCharComplex nu (-z) zeta ^ m else Complex.I * z *
      (Complex.exp (z * (w : ℂ) * Complex.I) * quadraticCharComplex nu z zeta ^ m +
        Complex.exp (-z * (w : ℂ) * Complex.I) * quadraticCharComplex nu (-z) zeta ^ m)
  have hA : 0 < A := by dsimp [A]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hz : |z.im| ≤ lam := by simpa [z] using heta
  have hmz : |(-z).im| ≤ lam := by simpa [z, abs_neg] using heta
  have hw : |zeta.im| ≤ s := by simpa [zeta] using hxi
  have hp := hphi z zeta hz hw
  have hpm := hphi (-z) zeta hmz hw
  have hwp : ‖Complex.exp (z * (w : ℂ) * Complex.I)‖ ≤ Ew :=
    contour_coordinate_exp_bound u eta w lam hlam heta
  have hwm : ‖Complex.exp (-z * (w : ℂ) * Complex.I)‖ ≤ Ew := by
    have hb := contour_coordinate_exp_bound (-u) (-eta) w lam hlam (by simpa using heta)
    convert hb using 1 <;> congr 2 <;> dsimp [z] <;> push_cast <;> ring
  have hnz : ‖z‖ ≤ (1 + lam) * A := by
    have he : ‖z‖ ≤ |u| + |eta| := by
      simpa [z, norm_mul, Complex.norm_real, Real.norm_eq_abs] using
        norm_add_le (u : ℂ) ((eta : ℂ) * Complex.I)
    dsimp [A]
    nlinarith [mul_nonneg hlam (abs_nonneg u)]
  have hR : ‖R‖ ≤ Cr * A ^ d.val := by
    by_cases hd : d = 0
    · have hdval : d.val = 0 := by rw [hd]; rfl
      rw [hdval, pow_zero, mul_one]
      dsimp only [R]
      rw [if_pos hd]
      calc
        _ ≤ ‖quadraticCharComplex nu z zeta ^ m‖ +
            ‖quadraticCharComplex nu (-z) zeta ^ m‖ := norm_sub_le _ _
        _ ≤ 2 * P ^ m := by linarith
        _ ≤ Cr := by
          dsimp [Cr]
          have ht : 0 ≤ (1 + lam) * Ew := by positivity
          nlinarith [mul_nonneg (pow_nonneg hP.le m) ht]
    · have hdval : d.val = 1 := by
        have hn : d.val ≠ 0 := by intro hz; exact hd (Fin.ext hz)
        have hlt := d.isLt
        omega
      rw [hdval, pow_one]
      dsimp only [R]
      rw [if_neg hd]
      simp only [norm_mul, Complex.norm_I, one_mul]
      calc
        _ ≤ ‖z‖ * (‖Complex.exp (z * (w : ℂ) * Complex.I) *
            quadraticCharComplex nu z zeta ^ m‖ +
            ‖Complex.exp (-z * (w : ℂ) * Complex.I) *
              quadraticCharComplex nu (-z) zeta ^ m‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
        _ ≤ ((1 + lam) * A) * (Ew * P ^ m + Ew * P ^ m) := by
          simp only [norm_mul]
          exact mul_le_mul hnz (add_le_add
            (mul_le_mul hwp hp (norm_nonneg _) hEw.le)
            (mul_le_mul hwm hpm (norm_nonneg _) hEw.le)) (by positivity) (by positivity)
        _ ≤ Cr * A := by dsimp [Cr]; nlinarith [mul_nonneg hA.le (pow_nonneg hP.le m)]
  have hH : ‖H‖ ≤ Cb * A ^ 3 / D ^ 3 := by
    apply (le_div_iff₀ (pow_pos hD 3)).mpr
    have hb := hcb j u v eta xi heta hxi
    change D ^ 3 * ‖H‖ ≤ C j * A ^ 3 at hb
    nlinarith [mul_le_mul_of_nonneg_right (hCble j) (pow_nonneg hA.le 3)]
  have hX : ‖quadraticFullNoiseCharComplex nu z zeta‖ ≤ Cx / A ^ 8 := by
    apply (le_div_iff₀ (pow_pos hA 8)).mpr
    have hb := hxb u v eta xi heta hxi
    change A ^ 8 * ‖quadraticFullNoiseCharComplex nu z zeta‖ ≤ Cx at hb
    nlinarith
  have hqexp : ‖Complex.exp (zeta * (q : ℂ) * Complex.I)‖ ≤ Eq :=
    contour_coordinate_exp_bound v xi q s hs hxi
  change ‖Complex.exp (zeta * (q : ℂ) * Complex.I) * H *
    quadraticFullNoiseCharComplex nu z zeta * R‖ ≤ B / (A ^ (5 - d.val) * D ^ 3)
  simp only [norm_mul]
  calc
    _ ≤ Eq * (Cb * A ^ 3 / D ^ 3) * (Cx / A ^ 8) * (Cr * A ^ d.val) := by
      exact mul_le_mul
        (mul_le_mul (mul_le_mul hqexp hH (norm_nonneg _) hEq.le) hX
          (norm_nonneg _) (by positivity)) hR (norm_nonneg _) (by positivity)
    _ = _ := by
      dsimp [B]
      fin_cases d <;> norm_num <;> field_simp <;> ring

private theorem contour_profile_limits (k : ℕ) (hk : 0 < k) (C : ℝ) :
    Tendsto (fun R : ℝ => C / (1 + |R|) ^ k) atTop (nhds 0) ∧
      Tendsto (fun R : ℝ => C / (1 + |R|) ^ k) atBot (nhds 0) := by
  have hdtop : Tendsto (fun R : ℝ => 1 + |R|) atTop atTop :=
    tendsto_atTop_mono (fun R : ℝ => by change R ≤ 1 + |R|; linarith [le_abs_self R]) tendsto_id
  have hdbot : Tendsto (fun R : ℝ => 1 + |R|) atBot atTop :=
    tendsto_atTop_mono (fun R : ℝ => by linarith [neg_le_abs R]) tendsto_neg_atBot_atTop
  constructor
  · have h := (tendsto_const_nhds (x := C)).mul
      ((tendsto_inv_atTop_zero.comp hdtop).pow k)
    simpa only [Function.comp_def, zero_pow hk.ne', mul_zero, div_eq_mul_inv, inv_pow] using h
  · have h := (tendsto_const_nhds (x := C)).mul
      ((tendsto_inv_atTop_zero.comp hdbot).pow k)
    simpa only [Function.comp_def, zero_pow hk.ne', mul_zero, div_eq_mul_inv, inv_pow] using h

private theorem contour_line_displacement
    (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (a b C : ℝ) (hab : a ≤ b) (hC : 0 ≤ C)
    (k : ℕ) (hk : 3 ≤ k)
    (hb : ∀ u eta : ℝ, eta ∈ Set.Icc a b →
      ‖F ((u : ℂ) + (eta : ℂ) * Complex.I)‖ ≤ C / (1 + |u|) ^ k) :
    (∫ u : ℝ, F ((u : ℂ) + (a : ℂ) * Complex.I)) =
      ∫ u : ℝ, F ((u : ℂ) + (b : ℂ) * Complex.I) := by
  have hi (eta : ℝ) (heta : eta ∈ Set.Icc a b) :
      Integrable (fun u : ℝ => F ((u : ℂ) + (eta : ℂ) * Complex.I)) := by
    apply ((contour_power_profile k hk).1.const_mul C).mono'
      (hF.continuous.comp (by fun_prop)).aestronglyMeasurable
    filter_upwards [] with u
    simpa only [Function.comp_def, div_eq_mul_inv, one_mul] using hb u eta heta
  have hedge (R : ℝ) :
      ‖∫ eta : ℝ in a..b, F ((R : ℂ) + (eta : ℂ) * Complex.I)‖ ≤
        ((b - a) * C) / (1 + |R|) ^ k := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (C := C / (1 + |R|) ^ k) (fun eta heta => hb R eta (by
        rw [Set.uIoc_of_le hab] at heta
        exact ⟨heta.1.le, heta.2⟩))
    have he : |b - a| = b - a := abs_of_nonneg (sub_nonneg.mpr hab)
    rw [he] at h
    exact h.trans_eq (by ring)
  have hl := contour_profile_limits k (by omega) ((b - a) * C)
  have htop : Tendsto (fun R : ℝ =>
      ∫ eta : ℝ in a..b, F ((R : ℂ) + (eta : ℂ) * Complex.I)) atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hedge hl.1
  have hbot : Tendsto (fun R : ℝ =>
      ∫ eta : ℝ in a..b, F ((R : ℂ) + (eta : ℂ) * Complex.I)) atBot (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hedge hl.2
  exact contour_rectangle_limit F hF a b (hi a ⟨le_rfl, hab⟩)
    (hi b ⟨hab, le_rfl⟩) htop hbot

private theorem contour_strip_integrability
    (F : ℂ → ℂ → ℂ) (hF : Continuous (fun p : ℂ × ℂ => F p.1 p.2))
    (k : ℕ) (hk : 3 ≤ k) (B lam s t : ℝ) (hB : 0 < B)
    (hlam : 0 ≤ lam) (hs : 0 ≤ s) (ht : 0 ≤ t ∧ t ≤ s)
    (hb : ∀ u v eta xi : ℝ, |eta| ≤ lam → |xi| ≤ s →
      ‖F ((u : ℂ) + (eta : ℂ) * Complex.I)
        ((v : ℂ) + (xi : ℂ) * Complex.I)‖ ≤
        B / ((1 + |u|) ^ k * (1 + |v|) ^ 3)) :
    (∀ eta xi : ℝ, |eta| ≤ lam → |xi| ≤ s →
      Integrable (fun p : ℝ × ℝ =>
        F ((p.1 : ℂ) + (eta : ℂ) * Complex.I)
          ((p.2 : ℂ) + (xi : ℂ) * Complex.I))) ∧
    ∀ R : ℝ,
      IntegrableOn (fun p : ℝ × ℝ =>
        F ((R : ℂ) + (p.1 : ℂ) * Complex.I) (p.2 : ℂ))
        (Set.Icc (-lam) 0 ×ˢ Set.univ) ∧
      IntegrableOn (fun p : ℝ × ℝ =>
        F ((p.1 : ℂ) - (lam : ℂ) * Complex.I)
          ((R : ℂ) + (p.2 : ℂ) * Complex.I))
        (Set.univ ×ˢ Set.Icc 0 t) ∧
      (∫ p : ℝ × ℝ in Set.Icc (-lam) 0 ×ˢ Set.univ,
        ‖F ((R : ℂ) + (p.1 : ℂ) * Complex.I) (p.2 : ℂ)‖) ≤
          lam * B / (1 + |R|) ^ k ∧
      (∫ p : ℝ × ℝ in Set.univ ×ˢ Set.Icc 0 t,
        ‖F ((p.1 : ℂ) - (lam : ℂ) * Complex.I)
          ((R : ℂ) + (p.2 : ℂ) * Complex.I)‖) ≤
          s * B / (1 + |R|) ^ 3 := by
  have hp := contour_power_profile k hk
  have hp3 := contour_power_profile 3 (by norm_num)
  have hprodU : ((volume : Measure ℝ).restrict (Set.Icc (-lam) 0)).prod volume =
      (volume : Measure (ℝ × ℝ)).restrict (Set.Icc (-lam) 0 ×ˢ Set.univ) := by
    simpa only [Measure.restrict_univ, Measure.volume_eq_prod ℝ ℝ] using
      (Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := volume)
        (Set.Icc (-lam) 0) Set.univ)
  have hprodV : (volume : Measure ℝ).prod (volume.restrict (Set.Icc 0 t)) =
      (volume : Measure (ℝ × ℝ)).restrict (Set.univ ×ˢ Set.Icc 0 t) := by
    simpa only [Measure.restrict_univ, Measure.volume_eq_prod ℝ ℝ] using
      (Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := volume)
        Set.univ (Set.Icc 0 t))
  constructor
  · intro eta xi heta hxi
    rw [Measure.volume_eq_prod ℝ ℝ]
    apply (contour_dominated_product volume volume
      (fun p : ℝ × ℝ => F ((p.1 : ℂ) + (eta : ℂ) * Complex.I)
        ((p.2 : ℂ) + (xi : ℂ) * Complex.I))
      (hF.comp (by fun_prop : Continuous (fun p : ℝ × ℝ =>
        (((p.1 : ℂ) + (eta : ℂ) * Complex.I), ((p.2 : ℂ) + (xi : ℂ) * Complex.I)))))
      (fun u : ℝ => B * (1 / (1 + |u|) ^ k))
      (fun v : ℝ => 1 / (1 + |v|) ^ 3) (hp.1.const_mul B) hp3.1 ?_).1
    filter_upwards [] with p
    convert hb p.1 p.2 eta xi heta hxi using 1 <;> field_simp <;> ring
  · intro R
    let KU : ℝ := B / (1 + |R|) ^ k
    let KV : ℝ := B / (1 + |R|) ^ 3
    have hKU : 0 ≤ KU := by dsimp [KU]; positivity
    have hKV : 0 ≤ KV := by dsimp [KV]; positivity
    have hUdom : ∀ᵐ p : ℝ × ℝ ∂((volume : Measure ℝ).restrict (Set.Icc (-lam) 0)).prod volume,
        ‖F ((R : ℂ) + (p.1 : ℂ) * Complex.I) (p.2 : ℂ)‖ ≤
          KU * (1 / (1 + |p.2|) ^ 3) := by
      rw [hprodU]
      filter_upwards [ae_restrict_mem (measurableSet_Icc.prod MeasurableSet.univ)] with p hp
      have he : |p.1| ≤ lam := by
        rw [abs_of_nonpos hp.1.2]
        linarith [hp.1.1]
      have h := hb R p.2 p.1 0 he (by simpa using hs)
      simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
      convert h using 1 <;> dsimp [KU] <;> field_simp <;> ring
    have hVdom : ∀ᵐ p : ℝ × ℝ ∂(volume : Measure ℝ).prod (volume.restrict (Set.Icc 0 t)),
        ‖F ((p.1 : ℂ) - (lam : ℂ) * Complex.I)
          ((R : ℂ) + (p.2 : ℂ) * Complex.I)‖ ≤
            (1 / (1 + |p.1|) ^ k) * KV := by
      rw [hprodV]
      filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Icc)] with p hp
      have he : |p.2| ≤ s := by rw [abs_of_nonneg hp.2.1]; exact hp.2.2.trans ht.2
      have h := hb p.1 R (-lam) p.2 (by simpa [abs_of_nonneg hlam]) he
      simp only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] at h
      convert h using 1 <;> dsimp [KV] <;> field_simp <;> ring
    obtain ⟨hiU, hbU⟩ := contour_dominated_product
      (volume.restrict (Set.Icc (-lam) 0)) volume
      (fun p : ℝ × ℝ => F ((R : ℂ) + (p.1 : ℂ) * Complex.I) (p.2 : ℂ))
      (hF.comp (by fun_prop : Continuous (fun p : ℝ × ℝ =>
        (((R : ℂ) + (p.1 : ℂ) * Complex.I), (p.2 : ℂ)))))
      (fun _ : ℝ => KU) (fun v : ℝ => 1 / (1 + |v|) ^ 3)
      (integrable_const _) hp3.1 hUdom
    obtain ⟨hiV, hbV⟩ := contour_dominated_product volume
      (volume.restrict (Set.Icc 0 t))
      (fun p : ℝ × ℝ => F ((p.1 : ℂ) - (lam : ℂ) * Complex.I)
        ((R : ℂ) + (p.2 : ℂ) * Complex.I))
      (hF.comp (by fun_prop : Continuous (fun p : ℝ × ℝ =>
        (((p.1 : ℂ) - (lam : ℂ) * Complex.I), ((R : ℂ) + (p.2 : ℂ) * Complex.I)))))
      (fun u : ℝ => 1 / (1 + |u|) ^ k) (fun _ : ℝ => KV)
      hp.1 (integrable_const _) hVdom
    rw [hprodU] at hiU hbU
    rw [hprodV] at hiV hbV
    have hconstU : (∫ _ : ℝ in Set.Icc (-lam) 0, KU) = lam * KU := by
      simp [integral_const, Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal hlam,
        smul_eq_mul, mul_comm]
    have hconstV : (∫ _ : ℝ in Set.Icc 0 t, KV) = t * KV := by
      simp [integral_const, Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal ht.1,
        smul_eq_mul, mul_comm]
    rw [hconstU] at hbU
    rw [hconstV] at hbV
    refine ⟨hiU, hiV, ?_, ?_⟩
    · apply hbU.trans
      calc
        _ ≤ (lam * KU) * 1 := mul_le_mul_of_nonneg_left hp3.2 (mul_nonneg hlam hKU)
        _ = _ := by dsimp [KU]; ring
    · apply hbV.trans
      calc
        _ ≤ 1 * (t * KV) := mul_le_mul_of_nonneg_right hp.2 (mul_nonneg ht.1 hKV)
        _ ≤ s * KV := by nlinarith [mul_le_mul_of_nonneg_right ht.2 hKV]
        _ = _ := by dsimp [KV]; ring

private theorem contour_two_frequency_displacement
    (F : ℂ → ℂ → ℂ) (hF : Differentiable ℂ (fun p : ℂ × ℂ => F p.1 p.2))
    (k : ℕ) (hk : 3 ≤ k) (B lam s t : ℝ) (hB : 0 < B)
    (hlam : 0 ≤ lam) (hs : 0 ≤ s) (ht : 0 ≤ t ∧ t ≤ s)
    (hb : ∀ u v eta xi : ℝ, |eta| ≤ lam → |xi| ≤ s →
      ‖F ((u : ℂ) + (eta : ℂ) * Complex.I)
        ((v : ℂ) + (xi : ℂ) * Complex.I)‖ ≤
        B / ((1 + |u|) ^ k * (1 + |v|) ^ 3)) :
    (∫ p : ℝ × ℝ, F (p.1 : ℂ) (p.2 : ℂ)) =
      ∫ p : ℝ × ℝ, F ((p.1 : ℂ) - (lam : ℂ) * Complex.I)
        ((p.2 : ℂ) + (t : ℂ) * Complex.I) := by
  have hi := (contour_strip_integrability F hF.continuous k hk B lam s t hB hlam hs ht hb).1
  have hi0 : Integrable (fun p : ℝ × ℝ => F (p.1 : ℂ) (p.2 : ℂ)) := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using
      hi 0 0 (by simpa using hlam) (by simpa using hs)
  have hi1 : Integrable (fun p : ℝ × ℝ =>
      F ((p.1 : ℂ) - (lam : ℂ) * Complex.I) (p.2 : ℂ)) := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero, Complex.ofReal_neg,
      neg_mul, sub_eq_add_neg] using hi (-lam) 0 (by simpa [abs_of_nonneg hlam]) (by simpa using hs)
  have hi2 : Integrable (fun p : ℝ × ℝ =>
      F ((p.1 : ℂ) - (lam : ℂ) * Complex.I)
        ((p.2 : ℂ) + (t : ℂ) * Complex.I)) := by
    simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using
      hi (-lam) t (by simpa [abs_of_nonneg hlam]) (by simpa [abs_of_nonneg ht.1] using ht.2)
  have hfirst (v : ℝ) : (∫ u : ℝ, F (u : ℂ) (v : ℂ)) =
      ∫ u : ℝ, F ((u : ℂ) - (lam : ℂ) * Complex.I) (v : ℂ) := by
    have he : Differentiable ℂ (fun z : ℂ => F z (v : ℂ)) :=
      hF.comp (by fun_prop : Differentiable ℂ (fun z : ℂ => (z, (v : ℂ))))
    have h := contour_line_displacement (fun z => F z (v : ℂ)) he (-lam) 0
      (B / (1 + |v|) ^ 3) (by linarith) (by positivity) k hk (fun u eta heta => by
        have heta' : |eta| ≤ lam := by rw [abs_of_nonpos heta.2]; linarith [heta.1]
        have h := hb u v eta 0 heta' (by simpa using hs)
        simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
        convert h using 1 <;> field_simp <;> ring)
    simpa only [Complex.ofReal_zero, zero_mul, add_zero, Complex.ofReal_neg,
      neg_mul, sub_eq_add_neg] using h.symm
  have hsecond (u : ℝ) :
      (∫ v : ℝ, F ((u : ℂ) - (lam : ℂ) * Complex.I) (v : ℂ)) =
      ∫ v : ℝ, F ((u : ℂ) - (lam : ℂ) * Complex.I)
        ((v : ℂ) + (t : ℂ) * Complex.I) := by
    have he : Differentiable ℂ (fun zeta : ℂ =>
        F ((u : ℂ) - (lam : ℂ) * Complex.I) zeta) :=
      hF.comp (by fun_prop : Differentiable ℂ (fun zeta : ℂ =>
        (((u : ℂ) - (lam : ℂ) * Complex.I), zeta)))
    have h := contour_line_displacement (fun zeta =>
      F ((u : ℂ) - (lam : ℂ) * Complex.I) zeta) he 0 t
      (B / (1 + |u|) ^ k) ht.1 (by positivity) 3 (by norm_num)
      (fun v xi hxi => by
        have hxi' : |xi| ≤ s := by rw [abs_of_nonneg hxi.1]; exact hxi.2.trans ht.2
        have h := hb u v (-lam) xi (by simpa [abs_of_nonneg hlam]) hxi'
        simp only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] at h
        convert h using 1 <;> field_simp <;> ring)
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using h
  rw [Measure.volume_eq_prod ℝ ℝ] at hi0 hi1 hi2 ⊢
  calc
    _ = ∫ v : ℝ, ∫ u : ℝ, F (u : ℂ) (v : ℂ) := integral_prod_symm _ hi0
    _ = ∫ v : ℝ, ∫ u : ℝ, F ((u : ℂ) - (lam : ℂ) * Complex.I) (v : ℂ) :=
      integral_congr_ae (ae_of_all _ hfirst)
    _ = ∫ p : ℝ × ℝ, F ((p.1 : ℂ) - (lam : ℂ) * Complex.I) (p.2 : ℂ) :=
      (integral_prod_symm _ hi1).symm
    _ = ∫ u : ℝ, ∫ v : ℝ, F ((u : ℂ) - (lam : ℂ) * Complex.I) (v : ℂ) :=
      integral_prod _ hi1
    _ = ∫ u : ℝ, ∫ v : ℝ, F ((u : ℂ) - (lam : ℂ) * Complex.I)
        ((v : ℂ) + (t : ℂ) * Complex.I) := integral_congr_ae (ae_of_all _ hsecond)
    _ = _ := (integral_prod _ hi2).symm

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
              ((p.2 : ℂ) + (sj j : ℂ) * Complex.I) := by
  dsimp only
  let s : ℝ := lam * y / Real.sqrt N
  have hN0 : 0 < N := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hl : 0 ≤ lam := (div_nonneg hy0 (Real.sqrt_nonneg N)).trans hlam
  have hs : 0 ≤ s := div_nonneg (mul_nonneg hl hy0) (Real.sqrt_nonneg N)
  obtain ⟨B, hB, hb⟩ := contour_integrand_strip_bound nu h3 hV h hh hsupport
    m y N lam s w q hl hs
  refine ⟨B, hB, ?_⟩
  intro j d
  let F : ℂ → ℂ → ℂ := sourceComplexBoundaryContourIntegrand nu m j d y N lam w q
  have hF : Differentiable ℂ (fun p : ℂ × ℂ => F p.1 p.2) :=
    contour_integrand_entire nu h3 hV h hh hsupport m j d y N lam w q
  have hk : 3 ≤ 5 - d.val := by have hlt := d.isLt; omega
  have ht : 0 ≤ (if j = 0 then 0 else s) ∧ (if j = 0 then 0 else s) ≤ s := by
    by_cases hj : j = 0 <;> simp [hj, hs]
  have hdata := contour_strip_integrability F hF.continuous (5 - d.val) hk B lam s
    (if j = 0 then 0 else s) hB hl hs ht (hb j d)
  have hlimU := contour_profile_limits (5 - d.val) (by omega) (lam * B)
  have hlimV := contour_profile_limits 3 (by norm_num) (s * B)
  refine ⟨hF, hb j d, hdata.1, hdata.2, ?_, ?_, ?_, ?_, ?_⟩
  · exact squeeze_zero (fun _ => integral_nonneg (fun _ => norm_nonneg _))
      (fun R => (hdata.2 R).2.2.1) hlimU.1
  · exact squeeze_zero (fun _ => integral_nonneg (fun _ => norm_nonneg _))
      (fun R => (hdata.2 R).2.2.1) hlimU.2
  · exact squeeze_zero (fun _ => integral_nonneg (fun _ => norm_nonneg _))
      (fun R => (hdata.2 R).2.2.2) hlimV.1
  · exact squeeze_zero (fun _ => integral_nonneg (fun _ => norm_nonneg _))
      (fun R => (hdata.2 R).2.2.2) hlimV.2
  · exact contour_two_frequency_displacement F hF (5 - d.val) hk B lam s
      (if j = 0 then 0 else s) hB hl hs ht (hb j d)

private theorem contour_boundary_slice_integrable (j : Fin 2) (y N lam : ℝ) (z zeta : ℂ) :
    let c : ℝ → ℝ := fun r => sourceKernelCutoff r *
      (if j = 0 then sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹)
        else 1 - sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹))
    Integrable (fun r : ℝ => (c r : ℂ) * Complex.exp
      (-(z * ((y * Real.sqrt r : ℝ) : ℂ) + zeta * (r : ℂ)) * Complex.I)) := by
  dsimp only
  let c : ℝ → ℝ := fun r => sourceKernelCutoff r *
    (if j = 0 then sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹)
      else 1 - sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹))
  have hc := contour_split_cutoff_data j y N lam
  have hcc : HasCompactSupport c :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hc.2
  have hcast : HasCompactSupport (fun r : ℝ => (c r : ℂ)) :=
    hcc.comp_left (g := Complex.ofReal) rfl
  exact (((Complex.continuous_ofReal.comp hc.1.continuous).mul (by fun_prop))).integrable_of_hasCompactSupport
    hcast.mul_right

private theorem contour_boundary_recombine (y N lam : ℝ) (z zeta : ℂ) :
    (∑ j : Fin 2, ∫ r : ℝ,
      ((sourceKernelCutoff r * (if j = 0 then
        sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹)
        else 1 - sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹)) : ℝ) : ℂ) *
        Complex.exp (-(z * ((y * Real.sqrt r : ℝ) : ℂ) + zeta * (r : ℂ)) * Complex.I)) =
      ∫ r : ℝ, (sourceKernelCutoff r : ℂ) *
        Complex.exp (-(z * ((y * Real.sqrt r : ℝ) : ℂ) + zeta * (r : ℂ)) * Complex.I) := by
  rw [Fin.sum_univ_two, ← integral_add (contour_boundary_slice_integrable 0 y N lam z zeta)
    (contour_boundary_slice_integrable 1 y N lam z zeta)]
  apply integral_congr_ae
  filter_upwards [] with r
  simp only [show (1 : Fin 2) ≠ 0 by decide, ite_true, ite_false]
  push_cast
  ring

set_option maxHeartbeats 1000000 in
private theorem contour_real_boundary_moment_integrable
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (h : ℝ) (hh : 0 < h) (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (m : ℕ) (j : Fin 2) (y N lam w q b : ℝ) (hlam : 0 ≤ lam)
    (k : ℕ) (hk : k ≤ 1) :
    Integrable (fun p : ℝ × ℝ =>
      (Complex.I * (p.1 : ℂ)) ^ k *
        Complex.exp (((p.1 * w + p.2 * q : ℝ) : ℂ) * Complex.I) *
        (∫ r : ℝ,
          ((sourceKernelCutoff r * (if j = 0 then
            sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹)
            else 1 - sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹)) : ℝ) : ℂ) *
            Complex.exp (-((p.1 : ℂ) * ((y * Real.sqrt r : ℝ) : ℂ) +
              (p.2 : ℂ) * (r : ℂ)) * Complex.I)) *
        quadraticFullNoiseCharComplex nu (p.1 : ℂ) (p.2 : ℂ) *
        quadraticCharComplex nu ((b * p.1 : ℝ) : ℂ) (p.2 : ℂ) ^ m) := by
  obtain ⟨Cb, hCb, hbb⟩ := contour_boundary_strip_decay j y N lam 0 hlam le_rfl
  obtain ⟨Cx, hCx, hxb⟩ := contour_noise_strip_decay nu h3 hV h hh hsupport 0 0 le_rfl le_rfl
  let H : ℂ → ℂ → ℂ := fun z zeta => ∫ r : ℝ,
    ((sourceKernelCutoff r * (if j = 0 then
      sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹)
      else 1 - sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹)) : ℝ) : ℂ) *
      Complex.exp (-(z * ((y * Real.sqrt r : ℝ) : ℂ) + zeta * (r : ℂ)) * Complex.I)
  have hH : Continuous (fun p : ℝ × ℝ => H (p.1 : ℂ) (p.2 : ℂ)) :=
    (contour_boundary_entire j y N lam).continuous.comp
      (by fun_prop : Continuous (fun p : ℝ × ℝ => ((p.1 : ℂ), (p.2 : ℂ))))
  have hX : Continuous (fun p : ℝ × ℝ =>
      quadraticFullNoiseCharComplex nu (p.1 : ℂ) (p.2 : ℂ)) :=
    (quadraticComplexChord_extension_and_cone nu h3 hV h hh hsupport).2.2.2.1.continuous.comp
      (by fun_prop : Continuous (fun p : ℝ × ℝ => ((p.1 : ℂ), (p.2 : ℂ))))
  have hP : Continuous (fun p : ℝ × ℝ =>
      quadraticCharComplex nu ((b * p.1 : ℝ) : ℂ) (p.2 : ℂ) ^ m) :=
    (((quadraticCharComplex_data nu h3 h hh hsupport).1.continuous.comp
      (by fun_prop : Continuous (fun p : ℝ × ℝ => (((b * p.1 : ℝ) : ℂ), (p.2 : ℂ)))))).pow m
  rw [Measure.volume_eq_prod ℝ ℝ]
  apply (contour_dominated_product volume volume _
    (((((by fun_prop : Continuous (fun p : ℝ × ℝ => (Complex.I * (p.1 : ℂ)) ^ k)).mul
      (by fun_prop : Continuous (fun p : ℝ × ℝ =>
        Complex.exp (((p.1 * w + p.2 * q : ℝ) : ℂ) * Complex.I)))).mul hH).mul hX).mul hP)
    (fun u : ℝ => (Cb * Cx) * (1 / (1 + |u|) ^ 4))
    (fun v : ℝ => 1 / (1 + |v|) ^ 3)
    ((contour_power_profile 4 (by norm_num)).1.const_mul _)
    (contour_power_profile 3 (by norm_num)).1 ?_).1
  filter_upwards [] with p
  let A : ℝ := 1 + |p.1|
  let D : ℝ := 1 + |p.2|
  have hA : 0 < A := by dsimp [A]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hHb : ‖H (p.1 : ℂ) (p.2 : ℂ)‖ ≤ Cb * A ^ 3 / D ^ 3 := by
    apply (le_div_iff₀ (pow_pos hD 3)).mpr
    have hb := hbb p.1 p.2 0 0 (by simpa using hlam) (by simp)
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at hb
    change D ^ 3 * ‖H (p.1 : ℂ) (p.2 : ℂ)‖ ≤ Cb * A ^ 3 at hb
    nlinarith
  have hXb : ‖quadraticFullNoiseCharComplex nu (p.1 : ℂ) (p.2 : ℂ)‖ ≤ Cx / A ^ 8 := by
    apply (le_div_iff₀ (pow_pos hA 8)).mpr
    have hb := hxb p.1 p.2 0 0 (by simp) (by simp)
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at hb
    change A ^ 8 * ‖quadraticFullNoiseCharComplex nu (p.1 : ℂ) (p.2 : ℂ)‖ ≤ Cx at hb
    nlinarith
  have hPb : ‖quadraticCharComplex nu ((b * p.1 : ℝ) : ℂ) (p.2 : ℂ) ^ m‖ ≤ 1 := by
    rw [norm_pow]
    have hb := ((quadraticCharComplex_data nu h3 h hh hsupport).2.1
      (((b * p.1 : ℝ) : ℂ)) (p.2 : ℂ)).2
    simp only [Complex.ofReal_im, abs_zero, mul_zero, add_zero, Real.exp_zero] at hb
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) hb m
  have hkp : |p.1| ^ k ≤ A := by
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl <;> dsimp [A] <;> norm_num <;> linarith [abs_nonneg p.1]
  have hep : ‖Complex.exp (((p.1 * w + p.2 * q : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  change ‖(Complex.I * (p.1 : ℂ)) ^ k *
    Complex.exp (((p.1 * w + p.2 * q : ℝ) : ℂ) * Complex.I) *
    H (p.1 : ℂ) (p.2 : ℂ) * quadraticFullNoiseCharComplex nu (p.1 : ℂ) (p.2 : ℂ) *
    quadraticCharComplex nu ((b * p.1 : ℝ) : ℂ) (p.2 : ℂ) ^ m‖ ≤ _
  simp only [norm_mul, norm_pow, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    one_mul, hep, mul_one]
  rw [norm_pow] at hPb
  calc
    _ ≤ A * (Cb * A ^ 3 / D ^ 3) * (Cx / A ^ 8) * 1 :=
      mul_le_mul (mul_le_mul (mul_le_mul hkp hHb (norm_nonneg _) hA.le) hXb
        (norm_nonneg _) (by positivity)) hPb (by positivity) (by positivity)
    _ = _ := by dsimp [A, D]; field_simp <;> ring

private theorem contour_test_boundary_identity (y N lam : ℝ) (hy : 0 ≤ y) (u v : ℝ) :
    Complex.I * (u : ℂ) * sourceFourierTestTransform y u v =
      ∑ j : Fin 2,
        ((∫ r : ℝ,
          ((sourceKernelCutoff r * (if j = 0 then
            sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹)
            else 1 - sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹)) : ℝ) : ℂ) *
            Complex.exp (-(((-u : ℝ) : ℂ) * ((y * Real.sqrt r : ℝ) : ℂ) +
              (v : ℂ) * (r : ℂ)) * Complex.I)) -
        (∫ r : ℝ,
          ((sourceKernelCutoff r * (if j = 0 then
            sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹)
            else 1 - sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹)) : ℝ) : ℂ) *
            Complex.exp (-((u : ℂ) * ((y * Real.sqrt r : ℝ) : ℂ) +
              (v : ℂ) * (r : ℂ)) * Complex.I))) := by
  rw [Finset.sum_sub_distrib, contour_boundary_recombine, contour_boundary_recombine]
  have hi (z zeta : ℂ) : Integrable (fun r : ℝ => (sourceKernelCutoff r : ℂ) *
      Complex.exp (-(z * ((y * Real.sqrt r : ℝ) : ℂ) + zeta * (r : ℂ)) * Complex.I)) := by
    exact ((Complex.continuous_ofReal.comp sourceKernelCutoff_data.1.continuous).mul
      (by fun_prop)).integrable_of_hasCompactSupport
        (sourceKernelCutoff_data.2.1.comp_left (g := Complex.ofReal) rfl).mul_right
  rw [sourceFourierTestTransform_eq y hy, ← integral_const_mul,
    ← integral_sub (hi ((-u : ℝ) : ℂ) (v : ℂ)) (hi (u : ℂ) (v : ℂ))]
  apply integral_congr_ae
  filter_upwards [] with r
  by_cases hu : u = 0
  · simp [hu]
  · let t : ℝ := u * y * Real.sqrt r
    have huC : (u : ℂ) ≠ 0 := by exact_mod_cast hu
    have hsine : Complex.I * (2 * (Real.sin t : ℂ)) =
        Complex.exp ((t : ℂ) * Complex.I) - Complex.exp (-(t : ℂ) * Complex.I) := by
      rw [Complex.ofReal_sin, Complex.two_sin]
      ring_nf
      simp only [Complex.I_sq]
      ring
    have heplus : Complex.exp (-(((-u : ℝ) : ℂ) * ((y * Real.sqrt r : ℝ) : ℂ) +
        (v : ℂ) * (r : ℂ)) * Complex.I) =
        Complex.exp ((t : ℂ) * Complex.I) *
          Complex.exp (-((v : ℂ) * (r : ℂ) * Complex.I)) := by
      rw [← Complex.exp_add]
      congr 1
      dsimp [t]
      push_cast
      ring
    have heminus : Complex.exp (-((u : ℂ) * ((y * Real.sqrt r : ℝ) : ℂ) +
        (v : ℂ) * (r : ℂ)) * Complex.I) =
        Complex.exp (-(t : ℂ) * Complex.I) *
          Complex.exp (-((v : ℂ) * (r : ℂ) * Complex.I)) := by
      rw [← Complex.exp_add]
      congr 1
      dsimp [t]
      push_cast
      ring
    rw [if_neg hu, heplus, heminus]
    simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
    change Complex.I * (u : ℂ) *
      ((sourceKernelCutoff r : ℂ) * (2 * (Real.sin t : ℂ) / (u : ℂ)) *
        Complex.exp (-((v : ℂ) * (r : ℂ) * Complex.I))) = _
    have he : (u : ℂ) * (2 * (Real.sin t : ℂ) / (u : ℂ)) = 2 * (Real.sin t : ℂ) := by
      field_simp
    calc
      _ = (sourceKernelCutoff r : ℂ) * (Complex.I * (2 * (Real.sin t : ℂ))) *
          Complex.exp (-((v : ℂ) * (r : ℂ) * Complex.I)) := by
        linear_combination (sourceKernelCutoff r : ℂ) * Complex.I *
          Complex.exp (-((v : ℂ) * (r : ℂ) * Complex.I)) * he
      _ = _ := by rw [hsine]; ring

set_option maxHeartbeats 1000000 in
private theorem contour_real_kernel_identity
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (h : ℝ) (hh : 0 < h) (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (m : ℕ) (y N lam w q : ℝ) (hy : 0 ≤ y) (hlam : 0 ≤ lam) :
    let f : ℝ → ℝ := fun r => sourceFutureNoiseKernel nu m y (r, q)
    DifferentiableAt ℝ f 0 ∧ DifferentiableAt ℝ f w ∧
      DifferentiableAt ℝ (fun r : ℝ => deriv f r) w ∧
      ((deriv f 0 : ℝ) : ℂ) = -((((2 * Real.pi) ^ 2 : ℝ) : ℂ)⁻¹) *
        ∑ j : Fin 2, ∫ p : ℝ × ℝ,
          sourceComplexBoundaryContourIntegrand nu m j 0 y N lam w q (p.1 : ℂ) (p.2 : ℂ) ∧
      ((deriv (fun r : ℝ => deriv f r) w : ℝ) : ℂ) =
        -((((2 * Real.pi) ^ 2 : ℝ) : ℂ)⁻¹) *
          ∑ j : Fin 2, ∫ p : ℝ × ℝ,
            sourceComplexBoundaryContourIntegrand nu m j 1 y N lam w q (p.1 : ℂ) (p.2 : ℂ) := by
  dsimp only
  let wd : Fin 2 → ℝ := fun d => if d = 0 then 0 else w
  let H : Fin 2 → ℝ → ℝ → ℂ := fun j u v => ∫ r : ℝ,
    ((sourceKernelCutoff r * (if j = 0 then
      sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹)
      else 1 - sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹)) : ℝ) : ℂ) *
      Complex.exp (-((u : ℂ) * ((y * Real.sqrt r : ℝ) : ℂ) +
        (v : ℂ) * (r : ℂ)) * Complex.I)
  let A : Fin 2 → Fin 2 → ℝ × ℝ → ℂ := fun d j p =>
    (Complex.I * (p.1 : ℂ)) ^ d.val *
      Complex.exp (((p.1 * wd d + p.2 * q : ℝ) : ℂ) * Complex.I) * H j p.1 p.2 *
      quadraticFullNoiseCharComplex nu (p.1 : ℂ) (p.2 : ℂ) *
      quadraticCharComplex nu (p.1 : ℂ) (p.2 : ℂ) ^ m
  let M : Fin 2 → Fin 2 → ℝ × ℝ → ℂ := fun d j p =>
    (Complex.I * (p.1 : ℂ)) ^ d.val *
      Complex.exp (((p.1 * (-wd d) + p.2 * q : ℝ) : ℂ) * Complex.I) * H j p.1 p.2 *
      quadraticFullNoiseCharComplex nu (p.1 : ℂ) (p.2 : ℂ) *
      quadraticCharComplex nu ((-p.1 : ℝ) : ℂ) (p.2 : ℂ) ^ m
  let J : Fin 2 → ℝ × ℝ → ℂ := fun d p =>
    (Complex.I * (p.1 : ℂ)) ^ (d.val + 1) *
      Complex.exp (((p.1 * wd d + p.2 * q : ℝ) : ℂ) * Complex.I) *
      sourceFutureNoiseKernelTransform nu m y p.1 p.2
  let refl : ℝ × ℝ → ℝ × ℝ := fun p => (-p.1, p.2)
  have hr : MeasurePreserving refl (volume : Measure (ℝ × ℝ)) volume := by
    rw [Measure.volume_eq_prod ℝ ℝ]
    exact (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id volume)
  have hri (g : ℝ × ℝ → ℂ) : (∫ p : ℝ × ℝ, g (refl p)) = ∫ p : ℝ × ℝ, g p :=
    hr.integral_comp ((MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl ℝ)).measurableEmbedding g
  have hAi (d j : Fin 2) : Integrable (A d j) := by
    have hk : d.val ≤ 1 := by have hlt := d.isLt; omega
    simpa only [A, H, one_mul] using contour_real_boundary_moment_integrable nu h3 hV h hh
      hsupport m j y N lam (wd d) q 1 hlam d.val hk
  have hMi (d j : Fin 2) : Integrable (M d j) := by
    have hk : d.val ≤ 1 := by have hlt := d.isLt; omega
    simpa only [M, H, neg_one_mul] using contour_real_boundary_moment_integrable nu h3 hV h hh
      hsupport m j y N lam (-wd d) q (-1) hlam d.val hk
  have hsplit (a b : ℝ) : Complex.exp (((a + b : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((a : ℂ) * Complex.I) * Complex.exp ((b : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hsplitC (a b : ℂ) : Complex.exp ((a + b) * Complex.I) =
      Complex.exp (a * Complex.I) * Complex.exp (b * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hwd0 : wd 0 = 0 := by simp [wd]
  have hwd1 : wd 1 = w := by simp [wd]
  have hFpoint (d j : Fin 2) (p : ℝ × ℝ) :
      sourceComplexBoundaryContourIntegrand nu m j d y N lam w q (p.1 : ℂ) (p.2 : ℂ) =
        A d j p - (-1 : ℂ) ^ d.val * M d j p := by
    change Complex.exp ((p.2 : ℂ) * (q : ℂ) * Complex.I) * H j p.1 p.2 *
      quadraticFullNoiseCharComplex nu (p.1 : ℂ) (p.2 : ℂ) *
      (if d = 0 then quadraticCharComplex nu (p.1 : ℂ) (p.2 : ℂ) ^ m -
        quadraticCharComplex nu (-(p.1 : ℂ)) (p.2 : ℂ) ^ m
      else Complex.I * (p.1 : ℂ) *
        (Complex.exp ((p.1 : ℂ) * (w : ℂ) * Complex.I) *
          quadraticCharComplex nu (p.1 : ℂ) (p.2 : ℂ) ^ m +
        Complex.exp (-(p.1 : ℂ) * (w : ℂ) * Complex.I) *
          quadraticCharComplex nu (-(p.1 : ℂ)) (p.2 : ℂ) ^ m)) = _
    fin_cases d <;> simp [A, M, wd, hsplitC, Complex.ofReal_mul, Complex.ofReal_neg] <;> ring
  have hXe (u v : ℝ) : quadraticFullNoiseCharComplex nu ((-u : ℝ) : ℂ) (v : ℂ) =
      quadraticFullNoiseCharComplex nu (u : ℂ) (v : ℂ) := by
    have he := (quadraticComplexChord_extension_and_cone nu h3 hV h hh hsupport).2.2.2.2.2.1
    rw [(he (-u) v).2, (he u v).2]
    exact (quadraticFullNoiseChar_product nu h3 hV h hh hsupport u v).2.1
  have hXe' (u v : ℝ) : quadraticFullNoiseCharComplex nu (-(u : ℂ)) (v : ℂ) =
      quadraticFullNoiseCharComplex nu (u : ℂ) (v : ℂ) := by
    simpa only [Complex.ofReal_neg] using hXe u v
  have hJpoint (d : Fin 2) (p : ℝ × ℝ) :
      J d p = ∑ j : Fin 2, ((-1 : ℂ) ^ d.val * M d j (refl p) - A d j p) := by
    have ht := contour_test_boundary_identity y N lam hy p.1 p.2
    change Complex.I * (p.1 : ℂ) * sourceFourierTestTransform y p.1 p.2 =
      ∑ j : Fin 2, (H j (-p.1) p.2 - H j p.1 p.2) at ht
    rw [Fin.sum_univ_two] at ht
    dsimp only [J]
    rw [sourceFutureNoiseKernelTransform_factor nu h3 hV h hh hsupport m y hy]
    have he := (quadraticComplexChord_extension_and_cone nu h3 hV h hh hsupport).2.2.2.2.2.1
    have hp := (quadraticCharComplex_data nu h3 h hh hsupport).2.2.1
    rw [← (he p.1 p.2).2, ← hp p.1 p.2]
    simp only [Fin.sum_univ_two, M, A, refl, neg_neg, Complex.ofReal_neg,
      mul_neg, neg_mul, neg_neg, hXe']
    fin_cases d <;> simp [wd]
    · linear_combination (norm := skip) (Complex.exp (((p.2 * q : ℝ) : ℂ) * Complex.I) *
        quadraticFullNoiseCharComplex nu (p.1 : ℂ) (p.2 : ℂ) *
          quadraticCharComplex nu (p.1 : ℂ) (p.2 : ℂ) ^ m) * ht
      push_cast
      ring_nf <;> (try simp only [Complex.I_sq]) <;> ring
    · linear_combination (norm := skip) (Complex.I * (p.1 : ℂ) *
        Complex.exp (((p.1 * w + p.2 * q : ℝ) : ℂ) * Complex.I) *
        quadraticFullNoiseCharComplex nu (p.1 : ℂ) (p.2 : ℂ) *
          quadraticCharComplex nu (p.1 : ℂ) (p.2 : ℂ) ^ m) * ht
      push_cast
      ring_nf <;> (try simp only [Complex.I_sq]) <;> ring
  have hsumint (d : Fin 2) :
      (∫ p : ℝ × ℝ, J d p) =
        -(∑ j : Fin 2, ∫ p : ℝ × ℝ,
          sourceComplexBoundaryContourIntegrand nu m j d y N lam w q (p.1 : ℂ) (p.2 : ℂ)) := by
    have hfun : J d = fun p => ∑ j : Fin 2,
        ((-1 : ℂ) ^ d.val * M d j (refl p) - A d j p) := funext (hJpoint d)
    have hmri (j : Fin 2) : Integrable (fun p : ℝ × ℝ => M d j (refl p)) := by
      simpa only [Function.comp_def] using hr.integrable_comp_of_integrable (hMi d j)
    have hLi (j : Fin 2) : Integrable (fun p : ℝ × ℝ =>
        (-1 : ℂ) ^ d.val * M d j (refl p) - A d j p) := by
      convert ((hmri j).const_mul ((-1 : ℂ) ^ d.val)).sub (hAi d j) using 1
    have hL (j : Fin 2) : (∫ p : ℝ × ℝ, (-1 : ℂ) ^ d.val * M d j (refl p) - A d j p) =
        (-1 : ℂ) ^ d.val * (∫ p : ℝ × ℝ, M d j p) - ∫ p : ℝ × ℝ, A d j p := by
      rw [integral_sub (f := fun p : ℝ × ℝ => (-1 : ℂ) ^ d.val * M d j (refl p))
        (g := A d j) ((hmri j).const_mul _) (hAi d j), integral_const_mul, hri]
    have hR (j : Fin 2) : (∫ p : ℝ × ℝ,
        sourceComplexBoundaryContourIntegrand nu m j d y N lam w q (p.1 : ℂ) (p.2 : ℂ)) =
        (∫ p : ℝ × ℝ, A d j p) - (-1 : ℂ) ^ d.val * ∫ p : ℝ × ℝ, M d j p := by
      simp_rw [hFpoint]
      rw [integral_sub (f := A d j) (g := fun p => (-1 : ℂ) ^ d.val * M d j p)
        (hAi d j) ((hMi d j).const_mul _), integral_const_mul]
    rw [hfun]
    simp only [Fin.sum_univ_two]
    rw [integral_add
      (f := fun p : ℝ × ℝ => (-1 : ℂ) ^ d.val * M d 0 (refl p) - A d 0 p)
      (g := fun p : ℝ × ℝ => (-1 : ℂ) ^ d.val * M d 1 (refl p) - A d 1 p)
      (hLi 0) (hLi 1), hL 0, hL 1, hR 0, hR 1]
    ring
  have hd0 := sourceFutureNoiseKernel_spatial_derivatives nu h3 hV h hh hsupport m y hy 0 q
  have hdw := sourceFutureNoiseKernel_spatial_derivatives nu h3 hV h hh hsupport m y hy w q
  refine ⟨hd0.1, hdw.1, hdw.2.1, ?_, ?_⟩
  · rw [hd0.2.2.1]
    dsimp only
    simp only [mul_zero, zero_add, pow_one]
    have he := hsumint 0
    simp only [J, wd, ite_true, Fin.val_zero, zero_add, pow_one, mul_zero, zero_add] at he
    rw [he]
    ring
  · rw [hdw.2.2.2]
    dsimp only
    have he := hsumint 1
    norm_num only [J, wd, show (1 : Fin 2) ≠ 0 by decide, ite_false, Fin.val_one, Nat.reduceAdd] at he
    rw [he]
    ring

set_option maxHeartbeats 1000000 in
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
          ∑ j : Fin 2, (bj j : ℂ) * (∫ p : ℝ × ℝ, G 1 j p) := by
  dsimp only
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
  have hy0 : 0 ≤ y := by linarith
  have hN0 : 0 < N := by dsimp [N, T]; linarith
  have hl : 0 ≤ lam := (div_nonneg hy0 (Real.sqrt_nonneg N)).trans hlam
  have hs : 0 ≤ s := div_nonneg (mul_nonneg hl hy0) (Real.sqrt_nonneg N)
  have hsj (j : Fin 2) : 0 ≤ sj j ∧ sj j ≤ s := by
    by_cases hj : j = 0 <;> simp [sj, hj, hs]
  have hbpos (j : Fin 2) : 0 < bj j := by dsimp [bj]; split_ifs <;> positivity
  have hdata := (quadraticCharComplex_data nu h3 h hh hsupport).2.2.2.1
  have hp (j : Fin 2) := hdata lam (sj j)
  have hm (j : Fin 2) := hdata (-lam) (sj j)
  have htilts (j : Fin 2) : IsProbabilityMeasure (rhoPlus j) ∧
      IsProbabilityMeasure (rhoMinus j) ∧ 0 < Zplus j ∧ 0 < Zminus j :=
    ⟨(hp j).2.2.1, (hm j).2.2.1, (hp j).2.1, (hm j).2.1⟩
  have hplus (j : Fin 2) (u v : ℝ) : quadraticCharComplex nu (z u)
      ((v : ℂ) + (sj j : ℂ) * Complex.I) =
      (Zplus j : ℂ) * quadraticChar (rhoPlus j) u v := (hp j).2.2.2 u v
  have hminus (j : Fin 2) (u v : ℝ) : quadraticCharComplex nu (-z u)
      ((v : ℂ) + (sj j : ℂ) * Complex.I) =
      (Zminus j : ℂ) * quadraticChar (rhoMinus j) (-u) v := by
    convert (hm j).2.2.2 (-u) v using 1 <;> dsimp [z] <;> push_cast <;> ring
  have hshift (d j : Fin 2) (u v : ℝ) :
      sourceComplexBoundaryContourIntegrand nu m j d y N lam w q
        (z u) ((v : ℂ) + (sj j : ℂ) * Complex.I) = (bj j : ℂ) * G d j (u, v) := by
    have hboundary := contour_boundary_shift j y N lam u v
    have he : Complex.exp (((v : ℂ) + (sj j : ℂ) * Complex.I) * (q : ℂ) * Complex.I) =
        (Real.exp (-sj j * q) : ℂ) * Complex.exp (((v * q : ℝ) : ℂ) * Complex.I) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      ring_nf
      simp only [Complex.I_sq]
      ring
    have hb : (Real.exp (-sj j * q) : ℂ) *
        ((if j = 0 then Real.exp (-lam * y * Real.sqrt N) else 1 : ℝ) : ℂ) = (bj j : ℂ) := by
      by_cases hj : j = 0 <;> simp [sj, bj, hj]
    unfold sourceComplexBoundaryContourIntegrand
    dsimp only
    rw [hboundary, he]
    simp only [hplus j u v, hminus j u v, mul_pow]
    change _ = (bj j : ℂ) * (Complex.exp (((v * q : ℝ) : ℂ) * Complex.I) *
      sourceComplexBoundaryMark j y N lam u v *
      quadraticFullNoiseCharComplex nu (z u) ((v : ℂ) + (sj j : ℂ) * Complex.I) * R d j u v)
    dsimp only [R]
    have hbf := congrArg (fun x : ℂ => x * Complex.exp (((v * q : ℝ) : ℂ) * Complex.I) *
      sourceComplexBoundaryMark j y N lam u v *
      quadraticFullNoiseCharComplex nu (z u) ((v : ℂ) + (sj j : ℂ) * Complex.I)) hb
    by_cases hd : d = 0
    · simp only [hd, ite_true]
      linear_combination (norm := skip)
        ((Zplus j : ℂ) ^ m * quadraticChar (rhoPlus j) u v ^ m -
          (Zminus j : ℂ) ^ m * quadraticChar (rhoMinus j) (-u) v ^ m) * hbf
      ring
    · simp only [hd, ite_false]
      linear_combination (norm := skip) (Complex.I * z u *
        (Complex.exp (z u * (w : ℂ) * Complex.I) * (Zplus j : ℂ) ^ m *
          quadraticChar (rhoPlus j) u v ^ m +
        Complex.exp (-z u * (w : ℂ) * Complex.I) * (Zminus j : ℂ) ^ m *
          quadraticChar (rhoMinus j) (-u) v ^ m)) * hbf
      ring
  obtain ⟨B, hB, hc⟩ := sourceComplexBoundary_contour_displacement nu h3 hV h hh hsupport
    m y N lam w q hy hNlo hNhi hlam
  have hGi (d j : Fin 2) : Integrable (G d j) := by
    rcases hc j d with ⟨_, _, hhor, _, _, _, _, _, _⟩
    have hi := hhor (-lam) (sj j) (by simpa [abs_of_nonneg hl])
      (by simpa [abs_of_nonneg (hsj j).1] using (hsj j).2)
    simp only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] at hi
    have hbn : (bj j : ℂ) ≠ 0 := by exact_mod_cast (hbpos j).ne'
    have hfun : G d j = fun p : ℝ × ℝ => (bj j : ℂ)⁻¹ *
        sourceComplexBoundaryContourIntegrand nu m j d y N lam w q
          (z p.1) ((p.2 : ℂ) + (sj j : ℂ) * Complex.I) := by
      funext p
      rw [hshift]
      field_simp
    rw [hfun]
    exact hi.const_mul _
  have hsum (d : Fin 2) :
      (∑ j : Fin 2, ∫ p : ℝ × ℝ,
        sourceComplexBoundaryContourIntegrand nu m j d y N lam w q (p.1 : ℂ) (p.2 : ℂ)) =
        ∑ j : Fin 2, (bj j : ℂ) * ∫ p : ℝ × ℝ, G d j p := by
    apply Finset.sum_congr rfl
    intro j _
    rcases hc j d with ⟨_, _, _, _, _, _, _, _, heq⟩
    rw [heq, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with p
    exact hshift d j p.1 p.2
  have hd := contour_real_kernel_identity nu h3 hV h hh hsupport m y N lam w q hy0 hl
  refine ⟨hd.1, hd.2.1, hd.2.2.1, htilts, ?_, ?_, ?_⟩
  · exact fun d j => ⟨hGi d j, hshift d j⟩
  · rw [hd.2.2.2.1, hsum 0]
  · rw [hd.2.2.2.2, hsum 1]

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
                Real.exp (lam * |w|) ≤ E := by
  dsimp only
  let mu : ℝ := ∫ a : ℝ, a ∂nu
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂nu
  let T : ℝ := (m : ℝ) * m2
  let N : ℝ := q + T
  let s : ℝ := lam * y / Real.sqrt N
  let sj : Fin 2 → ℝ := fun j => if j = 0 then 0 else s
  let bj : Fin 2 → ℝ := fun j =>
    if j = 0 then Real.exp (-lam * y * Real.sqrt N) else Real.exp (-s * q)
  let Z : ℝ → Fin 2 → ℝ := fun b j =>
    ∫ a : ℝ, Real.exp (b * a - sj j * a ^ 2) ∂nu
  let E : ℝ := Real.exp
    (-lam * y * Real.sqrt N + T * lam ^ 2 / 2 +
      (m : ℝ) * lam * |mu| +
      512 * (m : ℝ) * lam ^ 3 * m3 * Real.exp (512 * lam * h) + 512 * lam * h)
  change 0 ≤ lam ∧ 0 ≤ s ∧ s ≤ lam ^ 2 ∧ s * h ≤ lam ∧
    m3 / variance (id : ℝ → ℝ) nu ≤ 2 * h ∧
    ∀ (j : Fin 2) (b : ℝ), (b = lam ∨ b = -lam) →
      0 < Z b j ∧ ∀ u v w : ℝ, |w| ≤ h →
        bj j * (Z b j) ^ m *
            ‖quadraticFullNoiseCharComplex nu ((u : ℂ) - (lam : ℂ) * Complex.I)
              ((v : ℂ) + (sj j : ℂ) * Complex.I)‖ * Real.exp (lam * |w|) ≤ E
  have hNlo' : (1 / 16 : ℝ) ≤ N := hNlo
  obtain ⟨hl, hs, hsq, hslope⟩ := contour_parameter_guards y N lam h hy hNlo' hlam hh hyh
  have hgamma := contour_gamma_bound nu h3 hV h hh hsupport hm2V
  refine ⟨hl, hs, hsq, hslope, hgamma, ?_⟩
  intro j b hb
  have hsj0 : 0 ≤ sj j := by
    dsimp [sj]
    split_ifs
    · exact le_rfl
    · exact hs
  have hsjsq : sj j ≤ lam ^ 2 := by
    dsimp [sj]
    split_ifs
    · exact sq_nonneg lam
    · exact hsq
  have hsjslope : sj j * h ≤ lam := by
    dsimp [sj]
    split_ifs
    · simpa using hl
    · exact hslope
  obtain ⟨hZ, hZpow⟩ := contour_normalizer_power nu h lam b (sj j) hh hl hb
    hsj0 hsjsq hsjslope hsupport m
  refine ⟨hZ, ?_⟩
  intro u v w hw
  let A : ℝ := b * mu + (lam ^ 2 / 2 - sj j) * m2 +
    24 * lam ^ 3 * m3 * Real.exp (lam * h)
  change Z b j ^ m ≤ Real.exp ((m : ℝ) * A) at hZpow
  have hnoise := contour_actual_noise_norm nu h3 hV h hh hsupport hgamma
    lam (sj j) hl hsj0 hsjslope u v
  have hwe : Real.exp (lam * |w|) ≤ Real.exp (lam * h) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw hl)
  have hbj : 0 ≤ bj j := by dsimp [bj]; split_ifs <;> positivity
  have hm3 : 0 ≤ m3 := integral_nonneg (fun a => by positivity)
  have hbmu : b * mu ≤ lam * |mu| := by
    rcases hb with rfl | rfl
    · exact mul_le_mul_of_nonneg_left (le_abs_self mu) hl
    · nlinarith [mul_le_mul_of_nonneg_left (neg_le_abs mu) hl]
  have hcost : 24 * lam ^ 3 * m3 * Real.exp (lam * h) ≤
      512 * lam ^ 3 * m3 * Real.exp (512 * lam * h) := by
    calc
      _ ≤ 512 * lam ^ 3 * m3 * Real.exp (lam * h) := by gcongr <;> norm_num
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg hl hh.le]
  have hN0 : 0 < N := by linarith
  have hr : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hsN : s * (q + T) = lam * y * Real.sqrt N := by
    change (lam * y / Real.sqrt N) * N = _
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff hr.ne').mpr
    calc
      lam * y * N = lam * y * (Real.sqrt N) ^ 2 := by rw [Real.sq_sqrt hN0.le]
      _ = _ := by ring
  calc
    _ ≤ bj j * Real.exp ((m : ℝ) * A) * Real.exp (98 * lam * h) *
        Real.exp (lam * h) := by
      apply mul_le_mul _ hwe (Real.exp_pos _).le (by positivity)
      apply mul_le_mul _ hnoise (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left hZpow hbj
    _ = Real.exp ((if j = 0 then -lam * y * Real.sqrt N else -s * q) +
        (m : ℝ) * A + 99 * lam * h) := by
      dsimp [bj]
      split_ifs <;> rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      all_goals congr 1; ring
    _ ≤ E := by
      apply Real.exp_le_exp.mpr
      have hmu := mul_le_mul_of_nonneg_left hbmu (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
      have hce := mul_le_mul_of_nonneg_left hcost (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
      have hlh : 0 ≤ lam * h := mul_nonneg hl hh.le
      change (if j = 0 then -lam * y * Real.sqrt N else -s * q) + (m : ℝ) * A +
          99 * lam * h ≤
        -lam * y * Real.sqrt N + T * lam ^ 2 / 2 + (m : ℝ) * lam * |mu| +
          512 * (m : ℝ) * lam ^ 3 * m3 * Real.exp (512 * lam * h) + 512 * lam * h
      dsimp [A, sj]
      split_ifs with hj
      · dsimp [T]
        nlinarith
      · dsimp [T] at hsN ⊢
        nlinarith

end Shao.Probability
