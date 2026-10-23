import Shao.OQ3.OpenDomainExponentialEnvelope
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Analysis.Complex.Trigonometric

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem open_domain_weighted_fourier_continuousAt
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta xi : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))) :
    Integrable (fun x : ℝ =>
      Real.exp (theta.1 * x + theta.2 * x ^ 2) •
        Complex.exp (((xi.1 * x + xi.2 * x ^ 2 : ℝ) : ℂ) * Complex.I)) mu ∧
      ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
        ∫ x : ℝ, Real.exp (z.1.1 * x + z.1.2 * x ^ 2) •
          Complex.exp (((z.2.1 * x + z.2.2 * x ^ 2 : ℝ) : ℂ) * Complex.I) ∂mu)
        (theta, xi) := by
  obtain ⟨r, hr, _, _, hg, hgnonneg, hnear⟩ :=
    open_domain_local_exponential_envelope mu theta htheta
  let g : ℝ → ℝ := fun x =>
    Real.exp ((theta.1 + r) * x + (theta.2 + r) * x ^ 2) +
      Real.exp ((theta.1 - r) * x + (theta.2 + r) * x ^ 2)
  let F : ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ → ℂ := fun z x =>
    Real.exp (z.1.1 * x + z.1.2 * x ^ 2) •
      Complex.exp (((z.2.1 * x + z.2.2 * x ^ 2 : ℝ) : ℂ) * Complex.I)
  have hnorm : ∀ z x, ‖F z x‖ = Real.exp (z.1.1 * x + z.1.2 * x ^ 2) := by
    intro z x
    dsimp only [F]
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), mul_one]
  have hmeas : ∀ z, AEStronglyMeasurable (F z) mu := fun z =>
    (show Continuous (F z) by dsimp [F]; fun_prop).aestronglyMeasurable
  have hpoint : ‖theta - theta‖ < r := by simpa using hr
  have hint : Integrable (F (theta, xi)) mu :=
    hg.mono' (hmeas (theta, xi)) (Filter.Eventually.of_forall (fun x => by
      rw [hnorm]
      exact (hnear theta hpoint).2 x))
  have hclose : ∀ᶠ z : (ℝ × ℝ) × (ℝ × ℝ) in 𝓝 (theta, xi),
      ‖z.1 - theta‖ < r := by
    have h := (continuous_fst : Continuous
      (fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1)).tendsto (theta, xi)
    simpa only [Metric.mem_ball, dist_eq_norm] using
      h.eventually (Metric.ball_mem_nhds theta hr)
  refine ⟨hint, MeasureTheory.continuousAt_of_dominated
    (Filter.Eventually.of_forall hmeas) ?_ hg ?_⟩
  · exact hclose.mono (fun z hz => Filter.Eventually.of_forall (fun x => by
      rw [hnorm]
      exact (hnear z.1 hz).2 x))
  · exact Filter.Eventually.of_forall (fun x => by
      change ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ) => F z x) (theta, xi)
      dsimp [F]
      fun_prop)

theorem open_domain_partition_function_continuousAt
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))) :
    0 < (∫ x : ℝ, Real.exp (theta.1 * x + theta.2 * x ^ 2) ∂mu) ∧
      ContinuousAt (fun p : ℝ × ℝ =>
        ∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu) theta := by
  have hf : Integrable (fun x : ℝ =>
      Real.exp (theta.1 * x + theta.2 * x ^ 2)) mu := interior_subset htheta
  obtain ⟨r, hr, _, _, hg, _, hnear⟩ :=
    open_domain_local_exponential_envelope mu theta htheta
  have hclose : ∀ᶠ p : ℝ × ℝ in 𝓝 theta, ‖p - theta‖ < r := by
    have h : ∀ᶠ p : ℝ × ℝ in 𝓝 theta, p ∈ Metric.ball theta r :=
      Metric.ball_mem_nhds theta hr
    simpa only [Metric.mem_ball, dist_eq_norm] using h
  refine ⟨integral_exp_pos hf, MeasureTheory.continuousAt_of_dominated
    (bound := fun x => Real.exp ((theta.1 + r) * x + (theta.2 + r) * x ^ 2) +
      Real.exp ((theta.1 - r) * x + (theta.2 + r) * x ^ 2)) ?_ ?_ hg ?_⟩
  · exact Filter.Eventually.of_forall (fun p =>
      (show Continuous (fun x : ℝ =>
        Real.exp (p.1 * x + p.2 * x ^ 2)) by fun_prop).aestronglyMeasurable)
  · exact hclose.mono (fun p hp => Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
        (hnear p hp).2 x))
  · exact Filter.Eventually.of_forall (fun x => by fun_prop)

theorem open_domain_tilted_fourier_continuousAt
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta xi : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))) :
    let nu : Measure ℝ := mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)
    let phase : ℝ → ℂ := fun x =>
      Complex.exp (((xi.1 * x + xi.2 * x ^ 2 : ℝ) : ℂ) * Complex.I)
    IsProbabilityMeasure nu ∧ Integrable phase nu ∧
      ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
        ∫ x : ℝ, Complex.exp
          (((z.2.1 * x + z.2.2 * x ^ 2 : ℝ) : ℂ) * Complex.I)
          ∂mu.tilted (fun x => z.1.1 * x + z.1.2 * x ^ 2)) (theta, xi) := by
  dsimp only
  let f : (ℝ × ℝ) → ℝ → ℝ := fun p x => p.1 * x + p.2 * x ^ 2
  let phase : (ℝ × ℝ) → ℝ → ℂ := fun a x =>
    Complex.exp (((a.1 * x + a.2 * x ^ 2 : ℝ) : ℂ) * Complex.I)
  let Z : (ℝ × ℝ) → ℝ := fun p => ∫ x : ℝ, Real.exp (f p x) ∂mu
  let N : ((ℝ × ℝ) × (ℝ × ℝ)) → ℂ := fun z =>
    ∫ x : ℝ, Real.exp (f z.1 x) • phase z.2 x ∂mu
  let nu : Measure ℝ := mu.tilted (f theta)
  have hf : Integrable (fun x : ℝ => Real.exp (f theta x)) mu :=
    interior_subset htheta
  letI : IsProbabilityMeasure nu := isProbabilityMeasure_tilted hf
  have hphase : Continuous (phase xi) := by dsimp [phase]; fun_prop
  have hint : Integrable (phase xi) nu := (integrable_const (1 : ℝ)).mono'
    hphase.aestronglyMeasurable (Filter.Eventually.of_forall (fun x =>
      (Complex.norm_exp_ofReal_mul_I _).le))
  obtain ⟨hZpos, hZcont⟩ := open_domain_partition_function_continuousAt mu theta htheta
  have hNcont : ContinuousAt N (theta, xi) :=
    (open_domain_weighted_fourier_continuousAt mu theta xi htheta).2
  have hZlocal : ContinuousAt Z theta := hZcont
  have hZpull : ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ) => Z z.1) (theta, xi) :=
    ContinuousAt.comp (x := (theta, xi))
      (f := fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1) (g := Z)
      hZlocal continuous_fst.continuousAt
  have hcont : ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ) => (Z z.1)⁻¹ • N z)
      (theta, xi) :=
    (hZpull.inv₀ (ne_of_gt hZpos)).smul hNcont
  have heq : (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      ∫ x : ℝ, phase z.2 x ∂mu.tilted (f z.1)) =
      (fun z => (Z z.1)⁻¹ • N z) := by
    funext z
    change (∫ x : ℝ, phase z.2 x ∂mu.tilted (f z.1)) =
      (Z z.1)⁻¹ • (∫ x : ℝ, Real.exp (f z.1 x) • phase z.2 x ∂mu)
    rw [integral_tilted]
    change (∫ x : ℝ, (Real.exp (f z.1 x) / Z z.1) • phase z.2 x ∂mu) =
      (Z z.1)⁻¹ • (∫ x : ℝ, Real.exp (f z.1 x) • phase z.2 x ∂mu)
    simp_rw [div_eq_mul_inv, mul_comm (Real.exp _) ((Z z.1)⁻¹), mul_smul]
    rw [integral_smul]
  refine ⟨inferInstance, hint, ?_⟩
  change ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
    ∫ x : ℝ, phase z.2 x ∂mu.tilted (f z.1)) (theta, xi)
  rw [heq]
  exact hcont

end
end Shao.OQ3
