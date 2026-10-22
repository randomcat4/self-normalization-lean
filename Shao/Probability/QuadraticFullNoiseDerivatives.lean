import Shao.Probability.QuadraticFullNoise

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

private noncomputable def noisePhase (u v : ℝ) (z : ℝ × ℝ) : ℂ :=
  Complex.exp (((u * z.1 + v * z.2 : ℝ) : ℂ) * Complex.I)

private lemma noisePhase_norm (u v : ℝ) (z : ℝ × ℝ) :
    ‖noisePhase u v z‖ = 1 := by
  simp [noisePhase, Complex.norm_exp, Complex.mul_re]

private lemma firstPhase_norm (u v : ℝ) (z : ℝ × ℝ) :
    ‖Complex.I * (z.1 : ℂ) * noisePhase u v z‖ = |z.1| := by
  simp only [norm_mul, Complex.norm_I, one_mul, noisePhase_norm, mul_one,
    Complex.norm_real, Real.norm_eq_abs]

private lemma secondPhase_norm (u v : ℝ) (z : ℝ × ℝ) :
    ‖-((z.1 ^ 2 : ℝ) : ℂ) * noisePhase u v z‖ = z.1 ^ 2 := by
  simp only [norm_mul, norm_neg, noisePhase_norm, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z.1)]

private lemma noisePhase_integrable (μ : Measure (ℝ × ℝ))
    [IsProbabilityMeasure μ] (u v : ℝ) :
    Integrable (noisePhase u v) μ := by
  refine (integrable_const (μ := μ) (1 : ℝ)).mono' ?_
    (Filter.Eventually.of_forall fun z => (noisePhase_norm u v z).le)
  unfold noisePhase
  fun_prop

private lemma firstPhase_integrable (μ : Measure (ℝ × ℝ))
    (h1 : Integrable (fun z : ℝ × ℝ => |z.1|) μ) (u v : ℝ) :
    Integrable (fun z : ℝ × ℝ => Complex.I * (z.1 : ℂ) * noisePhase u v z) μ := by
  refine h1.mono' ?_ (Filter.Eventually.of_forall fun z => (firstPhase_norm u v z).le)
  unfold noisePhase
  fun_prop

private lemma secondPhase_integrable (μ : Measure (ℝ × ℝ))
    (h2 : Integrable (fun z : ℝ × ℝ => z.1 ^ 2) μ) (u v : ℝ) :
    Integrable (fun z : ℝ × ℝ => -((z.1 ^ 2 : ℝ) : ℂ) * noisePhase u v z) μ := by
  refine h2.mono' ?_ (Filter.Eventually.of_forall fun z => (secondPhase_norm u v z).le)
  unfold noisePhase
  fun_prop

private lemma noisePhase_hasDerivAt (z : ℝ × ℝ) (u v : ℝ) :
    HasDerivAt (fun r : ℝ => noisePhase r v z)
      (Complex.I * (z.1 : ℂ) * noisePhase u v z) u := by
  unfold noisePhase
  convert (((((hasDerivAt_id u).mul_const z.1).add_const (v * z.2)).ofReal_comp).mul_const
    Complex.I).cexp using 1
  all_goals try funext x
  all_goals try dsimp
  all_goals push_cast
  all_goals ring

private lemma noiseIntegral_hasDerivAt (μ : Measure (ℝ × ℝ))
    [IsProbabilityMeasure μ]
    (h1 : Integrable (fun z : ℝ × ℝ => |z.1|) μ) (u v : ℝ) :
    HasDerivAt (fun r : ℝ => ∫ z : ℝ × ℝ, noisePhase r v z ∂μ)
      (∫ z : ℝ × ℝ, Complex.I * (z.1 : ℂ) * noisePhase u v z ∂μ) u := by
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ)
    (F' := fun r z => Complex.I * (z.1 : ℂ) * noisePhase r v z)
    (bound := fun z : ℝ × ℝ => |z.1|) (by simp)
    (Filter.Eventually.of_forall fun r => (noisePhase_integrable μ r v).aestronglyMeasurable)
    (noisePhase_integrable μ u v)
    (firstPhase_integrable μ h1 u v).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z r _ => (firstPhase_norm r v z).le)
    h1
    (Filter.Eventually.of_forall fun z r _ => noisePhase_hasDerivAt z r v)).2

private lemma firstIntegral_hasDerivAt (μ : Measure (ℝ × ℝ))
    (h1 : Integrable (fun z : ℝ × ℝ => |z.1|) μ)
    (h2 : Integrable (fun z : ℝ × ℝ => z.1 ^ 2) μ) (u v : ℝ) :
    HasDerivAt
      (fun r : ℝ => ∫ z : ℝ × ℝ, Complex.I * (z.1 : ℂ) * noisePhase r v z ∂μ)
      (∫ z : ℝ × ℝ, -((z.1 ^ 2 : ℝ) : ℂ) * noisePhase u v z ∂μ) u := by
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ)
    (F' := fun r z => -((z.1 ^ 2 : ℝ) : ℂ) * noisePhase r v z)
    (bound := fun z : ℝ × ℝ => z.1 ^ 2) (by simp)
    (Filter.Eventually.of_forall fun r => (firstPhase_integrable μ h1 r v).aestronglyMeasurable)
    (firstPhase_integrable μ h1 u v)
    (secondPhase_integrable μ h2 u v).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z r _ => (secondPhase_norm r v z).le)
    h2
    (Filter.Eventually.of_forall fun z r _ => ?_)).2
  convert (noisePhase_hasDerivAt z r v).const_mul (Complex.I * (z.1 : ℂ)) using 1
  push_cast
  calc
    -((z.1 : ℂ) ^ 2) * noisePhase r v z =
        (Complex.I * Complex.I) * ((z.1 : ℂ) ^ 2) * noisePhase r v z := by
      rw [Complex.I_mul_I]
      ring
    _ = _ := by ring

theorem quadraticFullNoiseChar_derivatives
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h)
    (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (hgamma : (∫ a : ℝ, |a| ^ 3 ∂ν) /
      variance (id : ℝ → ℝ) ν ≤ 2 * h)
    (u0 v0 : ℝ) :
    let d1 : ℂ := ∫ z : ℝ × ℝ,
      Complex.I * (z.1 : ℂ) *
        Complex.exp (((u0 * z.1 + v0 * z.2 : ℝ) : ℂ) * Complex.I)
      ∂quadraticFullNoiseLaw ν
    let d2 : ℂ := ∫ z : ℝ × ℝ,
      -((z.1 ^ 2 : ℝ) : ℂ) *
        Complex.exp (((u0 * z.1 + v0 * z.2 : ℝ) : ℂ) * Complex.I)
      ∂quadraticFullNoiseLaw ν
    HasDerivAt (fun u : ℝ => quadraticFullNoiseChar ν u v0) d1 u0 ∧
    HasDerivAt
      (fun u : ℝ => deriv (fun r : ℝ => quadraticFullNoiseChar ν r v0) u)
      d2 u0 ∧
    deriv (fun u : ℝ => quadraticFullNoiseChar ν u v0) u0 = d1 ∧
    deriv
      (fun u : ℝ => deriv (fun r : ℝ => quadraticFullNoiseChar ν r v0) u) u0 = d2 := by
  obtain ⟨_, _, hl, _⟩ := quadraticFullNoise_law_data ν h3 hV h hh hs
  let := hl
  obtain ⟨_, h1, _, h2, _, _, _, _⟩ :=
    quadraticFullNoise_support_moments ν h3 hV h hh hs hgamma
  have hfirst (r : ℝ) :
      HasDerivAt (fun u : ℝ => quadraticFullNoiseChar ν u v0)
        (∫ z : ℝ × ℝ, Complex.I * (z.1 : ℂ) * noisePhase r v0 z
          ∂quadraticFullNoiseLaw ν) r := by
    exact noiseIntegral_hasDerivAt (quadraticFullNoiseLaw ν) h1 r v0
  have hsecond :
      HasDerivAt
        (fun u : ℝ => deriv (fun r : ℝ => quadraticFullNoiseChar ν r v0) u)
        (∫ z : ℝ × ℝ, -((z.1 ^ 2 : ℝ) : ℂ) * noisePhase u0 v0 z
          ∂quadraticFullNoiseLaw ν) u0 :=
    (firstIntegral_hasDerivAt (quadraticFullNoiseLaw ν) h1 h2 u0 v0).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun r => (hfirst r).deriv)
  exact ⟨hfirst u0, hsecond, (hfirst u0).deriv, hsecond.deriv⟩

theorem quadraticFullNoiseChar_derivative_bounds
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h)
    (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (hgamma : (∫ a : ℝ, |a| ^ 3 ∂ν) /
      variance (id : ℝ → ℝ) ν ≤ 2 * h)
    (u0 v0 : ℝ) :
    let gamma := (∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν
    ‖deriv (fun u : ℝ => quadraticFullNoiseChar ν u v0) u0‖ ≤
      (67 / 3 : ℝ) * gamma ∧
    ‖deriv
      (fun u : ℝ => deriv (fun r : ℝ => quadraticFullNoiseChar ν r v0) u) u0‖ ≤
      (70 / 3 : ℝ) * h * gamma := by
  obtain ⟨_, h1, _, h2, b1, _, _, b2⟩ :=
    quadraticFullNoise_support_moments ν h3 hV h hh hs hgamma
  obtain ⟨_, _, hd1, hd2⟩ :=
    quadraticFullNoiseChar_derivatives ν h3 hV h hh hs hgamma u0 v0
  constructor
  · rw [hd1]
    exact (norm_integral_le_of_norm_le h1
      (Filter.Eventually.of_forall fun z : ℝ × ℝ => by
        simpa only [noisePhase] using (firstPhase_norm u0 v0 z).le)).trans b1
  · rw [hd2]
    exact (norm_integral_le_of_norm_le h2
      (Filter.Eventually.of_forall fun z : ℝ × ℝ => by
        simpa only [noisePhase] using (secondPhase_norm u0 v0 z).le)).trans b2

end Shao.Probability
