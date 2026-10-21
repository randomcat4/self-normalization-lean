import Shao.Probability.FiniteIID
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
The actual joint characteristic integral of an increment and its square.
All estimates in this file concern real frequencies and the fixed actual law.
They do not assert low-frequency damping or a Fourier comparison theorem.
-/

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable def quadraticChar (ν : Measure ℝ) (u v : ℝ) : ℂ :=
  ∫ a : ℝ, Complex.exp
    (((u * a + v * a ^ 2 : ℝ) : ℂ) * Complex.I) ∂ν

private noncomputable def phase (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

private lemma phase_continuous : Continuous phase := by
  unfold phase
  fun_prop

private lemma phase_norm (t : ℝ) : ‖phase t‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re]

private lemma phase_sub_one (t : ℝ) : ‖phase t - 1‖ ≤ |t| := by
  simpa [phase, mul_comm, Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t))

private lemma phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  simp [phase, add_mul, Complex.exp_add]

private lemma phase_odd (s t : ℝ) :
    phase (s + t) - phase (-s + t) =
      2 * Complex.I * (Real.sin s : ℂ) * phase t := by
  rw [phase_add, phase_add]
  have h : phase s - phase (-s) = 2 * Complex.I * (Real.sin s : ℂ) := by
    simp only [phase, Complex.ofReal_neg, Complex.exp_mul_I, Complex.cos_neg,
      Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  linear_combination h * phase t

private lemma phase_integrable (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (u v : ℝ) : Integrable (fun a : ℝ => phase (u * a + v * a ^ 2)) ν := by
  refine (integrable_const (1 : ℝ)).mono' ?_ (Filter.Eventually.of_forall ?_)
  · exact (phase_continuous.comp (by fun_prop)).aestronglyMeasurable
  · intro a
    exact (phase_norm _).le

private lemma weighted_integrable {ν : Measure ℝ} {g : ℝ → ℝ}
    (hg : Integrable g ν) (v : ℝ) :
    Integrable (fun a : ℝ => (g a : ℂ) * phase (v * a ^ 2)) ν := by
  refine hg.norm.mono' ?_ (Filter.Eventually.of_forall ?_)
  · exact (hg.ofReal (𝕜 := ℂ)).aestronglyMeasurable.mul
      (phase_continuous.comp (by fun_prop)).aestronglyMeasurable
  · intro a
    simp [phase_norm]

private lemma moments_of_third {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν) :
    Integrable (fun a : ℝ => a) ν ∧ Integrable (fun a : ℝ => a ^ 2) ν := by
  have hb := (integrable_const (1 : ℝ)).add h3
  have hpoint (a : ℝ) : |a| ≤ 1 + |a| ^ 3 ∧ a ^ 2 ≤ 1 + |a| ^ 3 := by
    have ha := abs_nonneg a
    have ha2 : |a| ^ 2 = a ^ 2 := sq_abs a
    by_cases h : |a| ≤ 1
    · constructor <;> nlinarith [sq_nonneg (|a|), pow_nonneg ha 3]
    · have : 1 ≤ |a| := le_of_not_ge h
      constructor <;> nlinarith [sq_nonneg (|a| - 1),
        mul_nonneg (sub_nonneg.mpr this) (sq_nonneg |a|)]
  constructor
  · exact hb.mono' measurable_id.aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => by simpa using (hpoint a).1)
  · exact hb.mono' (by fun_prop)
      (Filter.Eventually.of_forall fun a => by
        simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg a)] using (hpoint a).2)

theorem norm_quadraticChar_le_one (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (u v : ℝ) :
    ‖quadraticChar ν u v‖ ≤ 1 := by
  change ‖∫ a : ℝ, phase (u * a + v * a ^ 2) ∂ν‖ ≤ 1
  simpa using norm_integral_le_of_norm_le (integrable_const (μ := ν) (1 : ℝ))
    (Filter.Eventually.of_forall fun a : ℝ => (phase_norm (u * a + v * a ^ 2)).le)

theorem iid_quadraticChar_factor
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (u v : ℝ) :
    (∫ ω, Complex.exp
      (((u * Shao.prefixSum (samplePath X ω) n +
          v * Shao.energy (samplePath X ω) : ℝ) : ℂ) * Complex.I) ∂μ) =
      (quadraticChar ν u v) ^ n := by
  have hp (ω : Ω) :
      Complex.exp (((u * Shao.prefixSum (samplePath X ω) n +
        v * Shao.energy (samplePath X ω) : ℝ) : ℂ) * Complex.I) =
        ∏ i, phase (u * X i ω + v * X i ω ^ 2) := by
    rw [show u * Shao.prefixSum (samplePath X ω) n +
        v * Shao.energy (samplePath X ω) =
        ∑ i, (u * X i ω + v * X i ω ^ 2) by
      simp [Shao.prefixSum, Shao.energy, samplePath, Finset.mul_sum, Finset.sum_add_distrib]]
    simp [phase, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  simp_rw [hp]
  rw [hIndep.integral_fun_prod_comp (f := fun (_ : Fin n) a => phase (u * a + v * a ^ 2))
    (fun i => (hX i).aemeasurable)
    (fun _ => (phase_continuous.comp (by fun_prop)).aestronglyMeasurable)]
  have he (i : Fin n) : (∫ ω, phase (u * X i ω + v * X i ω ^ 2) ∂μ) =
      quadraticChar ν u v := by
    have hc : Continuous (fun a : ℝ => phase (u * a + v * a ^ 2)) :=
      phase_continuous.comp (by fun_prop)
    exact ((hLaw i).comp hc.measurable).integral_eq
  simp_rw [he]
  simp

private lemma odd_identity (ν : Measure ℝ) [IsProbabilityMeasure ν] (u v : ℝ) :
    quadraticChar ν u v - quadraticChar ν (-u) v =
      2 * Complex.I * ∫ a : ℝ, (Real.sin (u * a) : ℂ) * phase (v * a ^ 2) ∂ν := by
  change (∫ a : ℝ, phase (u * a + v * a ^ 2) ∂ν) -
    (∫ a : ℝ, phase (-u * a + v * a ^ 2) ∂ν) = _
  rw [← integral_sub (phase_integrable ν u v) (phase_integrable ν (-u) v)]
  simp_rw [neg_mul, phase_odd]
  rw [← integral_const_mul]
  congr 1
  funext a
  ring

private lemma sin_integrable (ν : Measure ℝ) [IsProbabilityMeasure ν] (u : ℝ) :
    Integrable (fun a : ℝ => Real.sin (u * a)) ν := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun a => ?_)
  simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (u * a)

private lemma acos_integrable {ν : Measure ℝ}
    (h1 : Integrable (fun a : ℝ => a) ν) (u : ℝ) :
    Integrable (fun a : ℝ => a * Real.cos (u * a)) ν := by
  refine h1.norm.mono' (by fun_prop) (Filter.Eventually.of_forall fun a => ?_)
  simpa [Real.norm_eq_abs, abs_mul] using
    mul_le_of_le_one_right (abs_nonneg a) (Real.abs_cos_le_one (u * a))

private lemma asqsin_integrable {ν : Measure ℝ}
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (u : ℝ) :
    Integrable (fun a : ℝ => a ^ 2 * Real.sin (u * a)) ν := by
  refine h2.norm.mono' (by fun_prop) (Filter.Eventually.of_forall fun a => ?_)
  simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg a)] using
    mul_le_of_le_one_right (sq_nonneg a) (Real.abs_sin_le_one (u * a))

private lemma sin_integral_hasDerivAt (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h1 : Integrable (fun a : ℝ => a) ν) (u v : ℝ) :
    HasDerivAt
      (fun r : ℝ => ∫ a : ℝ, (Real.sin (r * a) : ℂ) * phase (v * a ^ 2) ∂ν)
      (∫ a : ℝ, ((a * Real.cos (u * a) : ℝ) : ℂ) * phase (v * a ^ 2) ∂ν) u := by
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ) (F' := fun r a => ((a * Real.cos (r * a) : ℝ) : ℂ) * phase (v * a ^ 2))
    (bound := fun a : ℝ => |a|) (by simp)
    (Filter.Eventually.of_forall fun r => (weighted_integrable (sin_integrable ν r) v).aestronglyMeasurable)
    (weighted_integrable (sin_integrable ν u) v)
    (weighted_integrable (acos_integrable h1 u) v).aestronglyMeasurable
    (Filter.Eventually.of_forall fun a r _ => ?_) h1.abs
    (Filter.Eventually.of_forall fun a r _ => ?_)).2
  · simpa only [norm_mul, phase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul] using
      mul_le_of_le_one_right (abs_nonneg a) (Real.abs_cos_le_one (r * a))
  · convert ((((Real.hasDerivAt_sin (r * a)).comp r
      ((hasDerivAt_id r).mul_const a)).ofReal_comp).mul_const (phase (v * a ^ 2))) using 1
    all_goals try funext x
    all_goals try dsimp
    all_goals push_cast
    all_goals ring

private lemma acos_integral_hasDerivAt (ν : Measure ℝ)
    (h1 : Integrable (fun a : ℝ => a) ν)
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (u v : ℝ) :
    HasDerivAt
      (fun r : ℝ => ∫ a : ℝ, ((a * Real.cos (r * a) : ℝ) : ℂ) * phase (v * a ^ 2) ∂ν)
      (∫ a : ℝ, -((a ^ 2 * Real.sin (u * a) : ℝ) : ℂ) * phase (v * a ^ 2) ∂ν) u := by
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ) (F' := fun r a => -((a ^ 2 * Real.sin (r * a) : ℝ) : ℂ) * phase (v * a ^ 2))
    (bound := fun a : ℝ => a ^ 2) (by simp)
    (Filter.Eventually.of_forall fun r => (weighted_integrable (acos_integrable h1 r) v).aestronglyMeasurable)
    (weighted_integrable (acos_integrable h1 u) v)
    ((weighted_integrable (asqsin_integrable h2 u) v).neg.aestronglyMeasurable.congr
      (Filter.Eventually.of_forall fun a => by simp))
    (Filter.Eventually.of_forall fun a r _ => ?_) h2
    (Filter.Eventually.of_forall fun a r _ => ?_)).2
  · simpa only [norm_mul, norm_neg, phase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (sq_nonneg a)] using
      mul_le_of_le_one_right (sq_nonneg a) (Real.abs_sin_le_one (r * a))
  · convert (((((Real.hasDerivAt_cos (r * a)).comp r
      ((hasDerivAt_id r).mul_const a)).const_mul a).ofReal_comp).mul_const
        (phase (v * a ^ 2))) using 1
    all_goals try funext x
    all_goals try dsimp
    all_goals push_cast
    all_goals ring

theorem quadraticChar_odd_hasDerivAt (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν) (u v : ℝ) :
    HasDerivAt (fun r : ℝ => quadraticChar ν r v - quadraticChar ν (-r) v)
      (2 * Complex.I *
        ∫ a : ℝ, ((a * Real.cos (u * a) : ℝ) : ℂ) *
          Complex.exp (((v * a ^ 2 : ℝ) : ℂ) * Complex.I) ∂ν) u := by
  exact ((sin_integral_hasDerivAt ν (moments_of_third h3).1 u v).const_mul
    (2 * Complex.I)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun r => odd_identity ν r v)

theorem quadraticChar_odd_deriv_hasDerivAt (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν) (u v : ℝ) :
    HasDerivAt
      (fun r : ℝ => deriv
        (fun s : ℝ => quadraticChar ν s v - quadraticChar ν (-s) v) r)
      (-(2 * Complex.I) *
        ∫ a : ℝ, ((a ^ 2 * Real.sin (u * a) : ℝ) : ℂ) *
          Complex.exp (((v * a ^ 2 : ℝ) : ℂ) * Complex.I) ∂ν) u := by
  have hd := (acos_integral_hasDerivAt ν (moments_of_third h3).1
    (moments_of_third h3).2 u v).const_mul (2 * Complex.I)
  have he : (∫ a : ℝ, -((a ^ 2 * Real.sin (u * a) : ℝ) : ℂ) * phase (v * a ^ 2) ∂ν) =
      -(∫ a : ℝ, ((a ^ 2 * Real.sin (u * a) : ℝ) : ℂ) * phase (v * a ^ 2) ∂ν) := by
    simp only [neg_mul, integral_neg]
  rw [he, mul_neg, ← neg_mul] at hd
  exact hd.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r => (quadraticChar_odd_hasDerivAt ν h3 r v).deriv)

private lemma sin_phase_error (b c : ℝ) :
    ‖(Real.sin b : ℂ) * phase c - (b : ℂ)‖ ≤ |b| ^ 3 / 6 + |b| * |c| := by
  have hs : |Real.sin b - b| ≤ |b| ^ 3 / 6 := by
    simpa only [abs_sub_comm] using Real.abs_sub_sin_le b
  calc
    ‖(Real.sin b : ℂ) * phase c - (b : ℂ)‖ =
        ‖((Real.sin b - b : ℝ) : ℂ) * phase c + (b : ℂ) * (phase c - 1)‖ := by
      congr 1
      push_cast
      ring
    _ ≤ ‖((Real.sin b - b : ℝ) : ℂ) * phase c‖ + ‖(b : ℂ) * (phase c - 1)‖ :=
      norm_add_le _ _
    _ ≤ |b| ^ 3 / 6 + |b| * |c| := by
      simp only [norm_mul, phase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add hs (mul_le_mul_of_nonneg_left (phase_sub_one c) (abs_nonneg b))

private lemma cos_phase_error (b c : ℝ) :
    ‖(Real.cos b : ℂ) * phase c - 1‖ ≤ b ^ 2 / 2 + |c| := by
  have hc : |Real.cos b - 1| ≤ b ^ 2 / 2 := by
    rw [abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one b))]
    linarith [Real.one_sub_sq_div_two_le_cos (x := b)]
  calc
    ‖(Real.cos b : ℂ) * phase c - 1‖ =
        ‖((Real.cos b - 1 : ℝ) : ℂ) * phase c + (phase c - 1)‖ := by
      congr 1
      push_cast
      ring
    _ ≤ ‖((Real.cos b - 1 : ℝ) : ℂ) * phase c‖ + ‖phase c - 1‖ := norm_add_le _ _
    _ ≤ b ^ 2 / 2 + |c| := by
      simp only [norm_mul, phase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add hc (phase_sub_one c)

private lemma integral_linear_error {ν : Measure ℝ} {g : ℝ → ℝ}
    (hg : Integrable g ν) (h1 : Integrable (fun a : ℝ => a) ν) (c v : ℝ) :
    (∫ a : ℝ, (g a : ℂ) * phase (v * a ^ 2) - ((c * a : ℝ) : ℂ) ∂ν) =
      (∫ a : ℝ, (g a : ℂ) * phase (v * a ^ 2) ∂ν) -
        (c : ℂ) * ((∫ a : ℝ, a ∂ν : ℝ) : ℂ) := by
  calc
    _ = (∫ a : ℝ, (g a : ℂ) * phase (v * a ^ 2) ∂ν) -
        (∫ a : ℝ, ((c * a : ℝ) : ℂ) ∂ν) := by
      exact integral_sub (weighted_integrable hg v) ((h1.const_mul c).ofReal (𝕜 := ℂ))
    _ = _ := by
      simp only [Complex.ofReal_mul, integral_const_mul]
      congr 2
      exact integral_ofReal

theorem quadraticChar_odd_remainder (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν) (u v : ℝ) :
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    ‖quadraticChar ν u v - quadraticChar ν (-u) v -
        2 * Complex.I * (u : ℂ) * (μ : ℂ)‖ ≤
      m3 * (|u| ^ 3 / 3 + 2 * |u| * |v|) := by
  dsimp only
  have he := integral_linear_error (sin_integrable ν u) (moments_of_third h3).1 u v
  have hb : ‖∫ a : ℝ, (Real.sin (u * a) : ℂ) * phase (v * a ^ 2) -
      ((u * a : ℝ) : ℂ) ∂ν‖ ≤
      (|u| ^ 3 / 6 + |u| * |v|) * ∫ a : ℝ, |a| ^ 3 ∂ν := by
    calc
      _ ≤ ∫ a : ℝ, (|u| ^ 3 / 6 + |u| * |v|) * |a| ^ 3 ∂ν :=
        norm_integral_le_of_norm_le (h3.const_mul _) (Filter.Eventually.of_forall fun a => by
          calc
            _ ≤ |u * a| ^ 3 / 6 + |u * a| * |v * a ^ 2| := sin_phase_error _ _
            _ = _ := by rw [abs_mul, abs_mul, abs_pow]; ring)
      _ = _ := integral_const_mul _ _
  rw [odd_identity]
  have hid : 2 * Complex.I * (∫ a : ℝ, (Real.sin (u * a) : ℂ) * phase (v * a ^ 2) ∂ν) -
      2 * Complex.I * (u : ℂ) * ((∫ a : ℝ, a ∂ν : ℝ) : ℂ) =
      2 * Complex.I * (∫ a : ℝ, (Real.sin (u * a) : ℂ) * phase (v * a ^ 2) -
        ((u * a : ℝ) : ℂ) ∂ν) := by rw [he]; ring
  rw [hid, norm_mul]
  have hn : ‖(2 : ℂ) * Complex.I‖ = 2 := by simp
  rw [hn]
  nlinarith [hb]

theorem quadraticChar_odd_bound (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν) (u v : ℝ) :
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    ‖quadraticChar ν u v - quadraticChar ν (-u) v‖ ≤
      2 * |μ| * |u| + m3 * (|u| ^ 3 / 3 + 2 * |u| * |v|) := by
  dsimp only
  have h := quadraticChar_odd_remainder ν h3 u v
  have hn : ‖2 * Complex.I * (u : ℂ) * ((∫ a : ℝ, a ∂ν : ℝ) : ℂ)‖ =
      2 * |∫ a : ℝ, a ∂ν| * |u| := by
    simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      mul_one]
    norm_num
    ring
  have ht := norm_sub_le (quadraticChar ν u v - quadraticChar ν (-u) v -
    2 * Complex.I * (u : ℂ) * ((∫ a : ℝ, a ∂ν : ℝ) : ℂ))
    (-(2 * Complex.I * (u : ℂ) * ((∫ a : ℝ, a ∂ν : ℝ) : ℂ)))
  simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at ht
  rw [hn] at ht
  linarith

theorem quadraticChar_odd_derivative_bounds (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν) (u v : ℝ) :
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    let d : ℝ → ℂ := fun r => quadraticChar ν r v - quadraticChar ν (-r) v
    ‖deriv d u - 2 * Complex.I * (μ : ℂ)‖ ≤ m3 * (u ^ 2 + 2 * |v|) ∧
      ‖deriv (fun r : ℝ => deriv d r) u‖ ≤ 2 * m3 * |u| := by
  dsimp only
  constructor
  · rw [(quadraticChar_odd_hasDerivAt ν h3 u v).deriv]
    change ‖2 * Complex.I * (∫ a : ℝ, ((a * Real.cos (u * a) : ℝ) : ℂ) * phase (v * a ^ 2) ∂ν) -
      2 * Complex.I * ((∫ a : ℝ, a ∂ν : ℝ) : ℂ)‖ ≤ _
    have he := integral_linear_error (acos_integrable (moments_of_third h3).1 u)
      (moments_of_third h3).1 1 v
    simp only [one_mul, Complex.ofReal_one] at he
    rw [← mul_sub, ← he, norm_mul]
    have hn : ‖(2 : ℂ) * Complex.I‖ = 2 := by simp
    rw [hn]
    have hb : ‖∫ a : ℝ, ((a * Real.cos (u * a) : ℝ) : ℂ) * phase (v * a ^ 2) -
        (a : ℂ) ∂ν‖ ≤ (u ^ 2 / 2 + |v|) * ∫ a : ℝ, |a| ^ 3 ∂ν := by
      calc
        _ ≤ ∫ a : ℝ, (u ^ 2 / 2 + |v|) * |a| ^ 3 ∂ν :=
          norm_integral_le_of_norm_le (h3.const_mul _) (Filter.Eventually.of_forall fun a => by
            have heq : ((a * Real.cos (u * a) : ℝ) : ℂ) * phase (v * a ^ 2) - (a : ℂ) =
                (a : ℂ) * ((Real.cos (u * a) : ℂ) * phase (v * a ^ 2) - 1) := by
              push_cast
              ring
            rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
            calc
              _ ≤ |a| * ((u * a) ^ 2 / 2 + |v * a ^ 2|) :=
                mul_le_mul_of_nonneg_left (cos_phase_error _ _) (abs_nonneg a)
              _ = _ := by rw [abs_mul, abs_pow, mul_pow, ← sq_abs a]; ring)
        _ = _ := integral_const_mul _ _
    nlinarith [hb]
  · rw [(quadraticChar_odd_deriv_hasDerivAt ν h3 u v).deriv]
    change ‖-(2 * Complex.I) * (∫ a : ℝ,
      ((a ^ 2 * Real.sin (u * a) : ℝ) : ℂ) * phase (v * a ^ 2) ∂ν)‖ ≤ _
    rw [norm_mul, norm_neg]
    have hn : ‖(2 : ℂ) * Complex.I‖ = 2 := by simp
    rw [hn]
    have hb : ‖∫ a : ℝ, ((a ^ 2 * Real.sin (u * a) : ℝ) : ℂ) * phase (v * a ^ 2) ∂ν‖ ≤
        |u| * ∫ a : ℝ, |a| ^ 3 ∂ν := by
      calc
        _ ≤ ∫ a : ℝ, |u| * |a| ^ 3 ∂ν :=
          norm_integral_le_of_norm_le (h3.const_mul _) (Filter.Eventually.of_forall fun a => by
            simp only [norm_mul, phase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_pow]
            calc
              _ ≤ |a| ^ 2 * |u * a| :=
                mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (sq_nonneg |a|)
              _ = _ := by rw [abs_mul]; ring)
        _ = _ := integral_const_mul _ _
    nlinarith [hb]

end Shao.Probability
