import Shao.Probability.SourceScalarNoise
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.Deriv.Support

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped FourierTransform ContDiff

private noncomputable def scalarPhase (gamma u r : ℝ) : ℂ :=
  Complex.exp (((gamma * u * r : ℝ) : ℂ) * Complex.I)

private lemma scalarPhase_norm (gamma u r : ℝ) :
    ‖scalarPhase gamma u r‖ = 1 := by
  simp [scalarPhase, Complex.norm_exp, Complex.mul_re]

private lemma scalarFirst_norm (gamma u r : ℝ) :
    ‖Complex.I * ((gamma * r : ℝ) : ℂ) * scalarPhase gamma u r‖ =
      |gamma| * |r| := by
  simp [scalarPhase_norm]

private lemma scalarSecond_norm (gamma u r : ℝ) :
    ‖-(((gamma * r) ^ 2 : ℝ) : ℂ) * scalarPhase gamma u r‖ =
      gamma ^ 2 * r ^ 2 := by
  simp [scalarPhase_norm, mul_pow]

private lemma scalarPhase_integrable (gamma u : ℝ) :
    Integrable (scalarPhase gamma u) sourceScalarLaw := by
  let := sourceScalarLaw_data.1
  refine (integrable_const (μ := sourceScalarLaw) (1 : ℝ)).mono' ?_
    (Filter.Eventually.of_forall fun r => (scalarPhase_norm gamma u r).le)
  unfold scalarPhase
  fun_prop

private lemma scalarFirst_integrable (gamma u : ℝ) :
    Integrable (fun r : ℝ => Complex.I * ((gamma * r : ℝ) : ℂ) * scalarPhase gamma u r)
      sourceScalarLaw := by
  have h1 := sourceScalarLaw_data.2.2.2.2.1
  refine (h1.const_mul |gamma|).mono' ?_
    (Filter.Eventually.of_forall fun r => (scalarFirst_norm gamma u r).le)
  unfold scalarPhase
  fun_prop

private lemma scalarSecond_integrable (gamma u : ℝ) :
    Integrable (fun r : ℝ => -(((gamma * r) ^ 2 : ℝ) : ℂ) * scalarPhase gamma u r)
      sourceScalarLaw := by
  have h2 := sourceScalarLaw_data.2.2.2.2.2.1
  refine (h2.const_mul (gamma ^ 2)).mono' ?_
    (Filter.Eventually.of_forall fun r => (scalarSecond_norm gamma u r).le)
  unfold scalarPhase
  fun_prop

private lemma scalarPhase_hasDerivAt (gamma u r : ℝ) :
    HasDerivAt (fun t : ℝ => scalarPhase gamma t r)
      (Complex.I * ((gamma * r : ℝ) : ℂ) * scalarPhase gamma u r) u := by
  unfold scalarPhase
  convert (((((hasDerivAt_id u).const_mul gamma).mul_const r).ofReal_comp).mul_const
    Complex.I).cexp using 1
  all_goals try funext x
  all_goals try dsimp
  all_goals push_cast
  all_goals ring

private lemma scalarIntegral_hasDerivAt (gamma u : ℝ) :
    HasDerivAt (fun t : ℝ => sourceScalarChar (gamma * t))
      (∫ r : ℝ, Complex.I * ((gamma * r : ℝ) : ℂ) * scalarPhase gamma u r
        ∂sourceScalarLaw) u := by
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ)
    (F' := fun t r => Complex.I * ((gamma * r : ℝ) : ℂ) * scalarPhase gamma t r)
    (bound := fun r : ℝ => |gamma| * |r|) (by simp)
    (Filter.Eventually.of_forall fun t => (scalarPhase_integrable gamma t).aestronglyMeasurable)
    (scalarPhase_integrable gamma u)
    (scalarFirst_integrable gamma u).aestronglyMeasurable
    (Filter.Eventually.of_forall fun r t _ => (scalarFirst_norm gamma t r).le)
    (sourceScalarLaw_data.2.2.2.2.1.const_mul |gamma|)
    (Filter.Eventually.of_forall fun r t _ => scalarPhase_hasDerivAt gamma t r)).2

private lemma scalarFirstIntegral_hasDerivAt (gamma u : ℝ) :
    HasDerivAt
      (fun t : ℝ => ∫ r : ℝ, Complex.I * ((gamma * r : ℝ) : ℂ) * scalarPhase gamma t r
        ∂sourceScalarLaw)
      (∫ r : ℝ, -(((gamma * r) ^ 2 : ℝ) : ℂ) * scalarPhase gamma u r
        ∂sourceScalarLaw) u := by
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ)
    (F' := fun t r => -(((gamma * r) ^ 2 : ℝ) : ℂ) * scalarPhase gamma t r)
    (bound := fun r : ℝ => gamma ^ 2 * r ^ 2) (by simp)
    (Filter.Eventually.of_forall fun t => (scalarFirst_integrable gamma t).aestronglyMeasurable)
    (scalarFirst_integrable gamma u)
    (scalarSecond_integrable gamma u).aestronglyMeasurable
    (Filter.Eventually.of_forall fun r t _ => (scalarSecond_norm gamma t r).le)
    (sourceScalarLaw_data.2.2.2.2.2.1.const_mul (gamma ^ 2))
    (Filter.Eventually.of_forall fun r t _ => ?_)).2
  convert (scalarPhase_hasDerivAt gamma t r).const_mul
    (Complex.I * ((gamma * r : ℝ) : ℂ)) using 1
  push_cast
  calc
    -(((gamma : ℂ) * r) ^ 2) * scalarPhase gamma t r =
        (Complex.I * Complex.I) * (((gamma : ℂ) * r) ^ 2) * scalarPhase gamma t r := by
      rw [Complex.I_mul_I]
      ring
    _ = _ := by ring

theorem sourceScalarChar_scaled_derivatives (gamma u0 : ℝ) :
    let d1 : ℂ := ∫ r : ℝ,
      Complex.I * ((gamma * r : ℝ) : ℂ) *
        Complex.exp ((((gamma * u0 * r : ℝ) : ℂ)) * Complex.I) ∂sourceScalarLaw
    let d2 : ℂ := ∫ r : ℝ,
      -(((gamma * r) ^ 2 : ℝ) : ℂ) *
        Complex.exp ((((gamma * u0 * r : ℝ) : ℂ)) * Complex.I) ∂sourceScalarLaw
    HasDerivAt (fun u : ℝ => sourceScalarChar (gamma * u)) d1 u0 ∧
    HasDerivAt
      (fun u : ℝ => deriv (fun t : ℝ => sourceScalarChar (gamma * t)) u) d2 u0 ∧
    deriv (fun u : ℝ => sourceScalarChar (gamma * u)) u0 = d1 ∧
    deriv
      (fun u : ℝ => deriv (fun t : ℝ => sourceScalarChar (gamma * t)) u) u0 = d2 := by
  have hsecond := (scalarFirstIntegral_hasDerivAt gamma u0).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u => (scalarIntegral_hasDerivAt gamma u).deriv)
  exact ⟨scalarIntegral_hasDerivAt gamma u0, hsecond,
    (scalarIntegral_hasDerivAt gamma u0).deriv, hsecond.deriv⟩

private noncomputable def scalarAmplitude (k : ℕ) (r : ℝ) : ℂ :=
  (r : ℂ) ^ k * (sourceScalarDensity r : ℂ)

private lemma scalarAmplitude_smooth (k : ℕ) :
    ContDiff ℝ ∞ (scalarAmplitude k) := by
  have hd : ContDiff ℝ ∞ (fun r : ℝ => (sourceScalarDensity r : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp sourceScalarDensity_data.1
  have hi : ContDiff ℝ ∞ (fun r : ℝ => (r : ℂ)) := Complex.ofRealCLM.contDiff
  exact (hi.pow k).mul hd

private lemma scalarAmplitude_compact (k : ℕ) :
    HasCompactSupport (scalarAmplitude k) := by
  have hd : HasCompactSupport (fun r : ℝ => (sourceScalarDensity r : ℂ)) :=
    sourceScalarDensity_data.2.1.comp_left Complex.ofReal_zero
  exact hd.mul_left

private lemma scalar_iteratedDeriv_compact {f : ℝ → ℂ}
    (hf : HasCompactSupport f) (n : ℕ) : HasCompactSupport (iteratedDeriv n f) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv

private lemma scalar_iteratedDeriv_integrable {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (n : ℕ) :
    Integrable (iteratedDeriv n f) :=
  (hf.continuous_iteratedDeriv n (by simp)).integrable_of_hasCompactSupport
    (scalar_iteratedDeriv_compact hs n)

private noncomputable def scalarPositiveFourier (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ r : ℝ, Complex.exp (((t * r : ℝ) : ℂ) * Complex.I) * f r

-- Mathlib uses exp(-2*pi*i*r*w); our source uses exp(i*t*r).
private lemma scalarPositiveFourier_eq (f : ℝ → ℂ) (t : ℝ) :
    scalarPositiveFourier f t = 𝓕 f (-t / (2 * Real.pi)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with r
  have he : -2 * Real.pi * r * (-t / (2 * Real.pi)) = t * r := by
    field_simp
  simp only [he, smul_eq_mul]

private lemma scalarPositiveFourier_power_bound {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (n : ℕ) (t : ℝ) :
    |t| ^ n * ‖scalarPositiveFourier f t‖ ≤ ∫ r : ℝ, ‖iteratedDeriv n f r‖ := by
  have hi := congrFun
    (Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) hf
      (fun k _ => scalar_iteratedDeriv_integrable hf hs k) (n := n) (by simp))
    (-t / (2 * Real.pi))
  have hc : ‖(2 * (Real.pi : ℂ) * Complex.I * ((-t / (2 * Real.pi) : ℝ) : ℂ)) ^ n‖ =
      |t| ^ n := by
    rw [norm_pow]
    congr 1
    have he : 2 * (Real.pi : ℂ) * Complex.I * ((-t / (2 * Real.pi) : ℝ) : ℂ) =
        -(t : ℂ) * Complex.I := by
      push_cast
      field_simp
    rw [he]
    simp
  calc
    |t| ^ n * ‖scalarPositiveFourier f t‖ =
        ‖𝓕 (iteratedDeriv n f) (-t / (2 * Real.pi))‖ := by
      rw [hi, norm_smul, hc, scalarPositiveFourier_eq]
    _ ≤ _ := Real.norm_fourier_le_integral_norm _ _

private lemma scalar_integral_density (g : ℝ → ℂ) :
    (∫ r : ℝ, g r ∂sourceScalarLaw) = ∫ r : ℝ, (sourceScalarDensity r : ℂ) * g r := by
  unfold sourceScalarLaw
  rw [integral_withDensity_eq_integral_toReal_smul
    sourceScalarDensity_data.1.continuous.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sourceScalarDensity_data.2.2.1 _), Complex.real_smul]

private lemma scalarFirst_fourier (gamma u : ℝ) :
    (∫ r : ℝ, Complex.I * ((gamma * r : ℝ) : ℂ) * scalarPhase gamma u r
      ∂sourceScalarLaw) =
        ((gamma : ℂ) * Complex.I) * scalarPositiveFourier (scalarAmplitude 1) (gamma * u) := by
  rw [scalar_integral_density, scalarPositiveFourier, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with r
  simp only [scalarAmplitude, pow_one, scalarPhase, Complex.ofReal_mul]
  ring

private lemma scalarSecond_fourier (gamma u : ℝ) :
    (∫ r : ℝ, -(((gamma * r) ^ 2 : ℝ) : ℂ) * scalarPhase gamma u r
      ∂sourceScalarLaw) =
        -((gamma : ℂ) ^ 2) * scalarPositiveFourier (scalarAmplitude 2) (gamma * u) := by
  rw [scalar_integral_density, scalarPositiveFourier, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with r
  simp only [scalarAmplitude, scalarPhase, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

theorem sourceScalarChar_scaled_derivative_bounds :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
      ∀ gamma u : ℝ, u ≠ 0 →
        ‖deriv (fun t : ℝ => sourceScalarChar (gamma * t)) u‖ ≤ C1 / |u| ∧
        ‖deriv
          (fun t : ℝ => deriv (fun r : ℝ => sourceScalarChar (gamma * r)) t) u‖ ≤
            C2 / u ^ 2 := by
  let A : ℝ := ∫ r : ℝ, ‖iteratedDeriv 1 (scalarAmplitude 1) r‖
  let B : ℝ := ∫ r : ℝ, ‖iteratedDeriv 2 (scalarAmplitude 2) r‖
  have hA : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  have hB : 0 ≤ B := integral_nonneg fun _ => norm_nonneg _
  refine ⟨1 + A, 1 + B, by positivity, by positivity, ?_⟩
  intro gamma u hu
  obtain ⟨_, _, hd1, hd2⟩ := sourceScalarChar_scaled_derivatives gamma u
  have hnorm1 : ‖deriv (fun t : ℝ => sourceScalarChar (gamma * t)) u‖ =
      |gamma| * ‖scalarPositiveFourier (scalarAmplitude 1) (gamma * u)‖ := by
    rw [hd1]
    change ‖∫ r : ℝ, Complex.I * ((gamma * r : ℝ) : ℂ) * scalarPhase gamma u r
      ∂sourceScalarLaw‖ = _
    rw [scalarFirst_fourier]
    simp
  have hnorm2 : ‖deriv
      (fun t : ℝ => deriv (fun r : ℝ => sourceScalarChar (gamma * r)) t) u‖ =
      gamma ^ 2 * ‖scalarPositiveFourier (scalarAmplitude 2) (gamma * u)‖ := by
    rw [hd2]
    change ‖∫ r : ℝ, -(((gamma * r) ^ 2 : ℝ) : ℂ) * scalarPhase gamma u r
      ∂sourceScalarLaw‖ = _
    rw [scalarSecond_fourier]
    simp [sq_abs]
  have hb1 : |u| * ‖deriv (fun t : ℝ => sourceScalarChar (gamma * t)) u‖ ≤ A := by
    have h := scalarPositiveFourier_power_bound
      (scalarAmplitude_smooth 1) (scalarAmplitude_compact 1) 1 (gamma * u)
    rw [hnorm1]
    simpa only [pow_one, abs_mul, mul_assoc, mul_left_comm] using h
  have hb2 : u ^ 2 * ‖deriv
      (fun t : ℝ => deriv (fun r : ℝ => sourceScalarChar (gamma * r)) t) u‖ ≤ B := by
    have h := scalarPositiveFourier_power_bound
      (scalarAmplitude_smooth 2) (scalarAmplitude_compact 2) 2 (gamma * u)
    rw [hnorm2]
    simpa only [sq_abs, mul_pow, mul_assoc, mul_left_comm] using h
  constructor
  · apply (le_div_iff₀ (abs_pos.mpr hu)).2
    nlinarith only [hb1]
  · apply (le_div_iff₀ (sq_pos_of_ne_zero hu)).2
    nlinarith only [hb2]

end Shao.Probability
