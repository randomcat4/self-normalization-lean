import Shao.Probability.BivariateLegendre
import Shao.OQ3.RegularCovariance
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.MeasureTheory.Measure.Tilted

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology NNReal ENNReal
noncomputable section

theorem quadratic_tilt_mgf_identity
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta d : ℝ × ℝ)
    (htheta : theta ∈ Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))) :
    let nu : Measure ℝ := mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)
    let F : ℝ → ℝ := fun x => d.1 * x + d.2 * x ^ 2
    let Z : (ℝ × ℝ) → ℝ := fun p =>
      ∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu
    IsProbabilityMeasure nu ∧ 0 < Z theta ∧
      ∀ t : ℝ,
        (Integrable (fun x => Real.exp (t * F x)) nu ↔
          (theta.1 + t * d.1, theta.2 + t * d.2) ∈
            Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))) ∧
        ProbabilityTheory.mgf F nu t = Z (theta.1 + t * d.1, theta.2 + t * d.2) / Z theta := by
  let nu : Measure ℝ := mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)
  let F : ℝ → ℝ := fun x => d.1 * x + d.2 * x ^ 2
  let Z : (ℝ × ℝ) → ℝ := fun p =>
    ∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu
  have hf : Integrable (fun x : ℝ => Real.exp (theta.1 * x + theta.2 * x ^ 2)) mu := htheta
  refine ⟨isProbabilityMeasure_tilted hf, integral_exp_pos hf, ?_⟩
  intro t
  constructor
  · change Integrable (fun x => Real.exp (t * F x)) (mu.tilted _) ↔ _
    rw [integrable_tilted_iff hf]
    change Integrable (fun x => Real.exp (theta.1 * x + theta.2 * x ^ 2) * Real.exp (t * F x)) mu ↔
      Integrable (fun x => Real.exp ((theta.1 + t * d.1) * x + (theta.2 + t * d.2) * x ^ 2)) mu
    have heq : (fun x : ℝ => Real.exp (theta.1 * x + theta.2 * x ^ 2) * Real.exp (t * F x)) =
        (fun x => Real.exp ((theta.1 + t * d.1) * x + (theta.2 + t * d.2) * x ^ 2)) := by
      funext x
      rw [← Real.exp_add]
      congr 1
      dsimp [F]
      ring
    rw [heq]
  · change (∫ x, Real.exp (t * F x) ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)) = _
    rw [integral_exp_tilted]
    change (∫ x, Real.exp ((theta.1 * x + theta.2 * x ^ 2) + t * F x) ∂mu) / Z theta = _
    congr 1
    congr 1
    funext x
    congr 1
    dsimp [F]
    ring

private theorem quadratic_tilt_projection_interior
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta d : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))) :
    0 ∈ interior (ProbabilityTheory.integrableExpSet (fun x : ℝ => d.1 * x + d.2 * x ^ 2)
      (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))) := by
  have hbase := quadratic_tilt_mgf_identity mu theta d (interior_subset htheta)
  have hcont : Continuous (fun t : ℝ => (theta.1 + t * d.1, theta.2 + t * d.2)) := by fun_prop
  have hline : Filter.Tendsto (fun t : ℝ => (theta.1 + t * d.1, theta.2 + t * d.2))
      (𝓝 0) (𝓝 theta) := by simpa [ContinuousAt] using hcont.continuousAt (x := 0)
  apply mem_interior_iff_mem_nhds.mpr
  have hnear := hline.eventually (isOpen_interior.mem_nhds htheta)
  filter_upwards [hnear] with t ht
  exact ((hbase.2.2 t).1).2 (interior_subset ht)

private theorem quadratic_tilt_variance_eq (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h1 : MemLp (fun x : ℝ => x) 2 nu)
    (h2 : MemLp (fun x : ℝ => x ^ 2) 2 nu) (a b : ℝ) :
    ProbabilityTheory.variance (fun x : ℝ => a * x + b * x ^ 2) nu =
      a ^ 2 * parabolaCovariance nu 0 0 + 2 * a * b * parabolaCovariance nu 0 1 +
        b ^ 2 * parabolaCovariance nu 1 1 := by
  change ProbabilityTheory.variance (fun x : ℝ => a * x + b * x ^ 2) nu =
    a ^ 2 * ProbabilityTheory.variance (fun x : ℝ => x) nu +
      2 * a * b * ProbabilityTheory.covariance (fun x : ℝ => x) (fun x : ℝ => x ^ 2) nu +
      b ^ 2 * ProbabilityTheory.variance (fun x : ℝ => x ^ 2) nu
  rw [ProbabilityTheory.variance_fun_add (h1.const_mul a) (h2.const_mul b),
    ProbabilityTheory.variance_const_mul, ProbabilityTheory.variance_const_mul,
    ProbabilityTheory.covariance_const_mul_left, ProbabilityTheory.covariance_const_mul_right]
  ring

theorem open_domain_quadratic_tilt_directional_cumulants
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))) :
    let nu : Measure ℝ := mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)
    let means : Fin 2 → ℝ := ![∫ x : ℝ, x ∂nu, ∫ x : ℝ, x ^ 2 ∂nu]
    let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance nu
    IsProbabilityMeasure nu ∧
      MemLp (fun x : ℝ => x) 2 nu ∧ MemLp (fun x : ℝ => x ^ 2) 2 nu ∧
      ∀ d : ℝ × ℝ,
        let F : ℝ → ℝ := fun x => d.1 * x + d.2 * x ^ 2
        let f : ℝ → ℝ := fun t => Real.log
          (∫ x : ℝ, Real.exp
            ((theta.1 + t * d.1) * x + (theta.2 + t * d.2) * x ^ 2) ∂mu)
        0 ∈ interior (ProbabilityTheory.integrableExpSet F nu) ∧ MemLp F 2 nu ∧
          (∀ k : ℕ, Integrable (fun x => (F x) ^ k) nu) ∧
          HasDerivAt f (d.1 * means 0 + d.2 * means 1) 0 ∧
          HasDerivAt (deriv f)
            (d.1 ^ 2 * D 0 0 + 2 * d.1 * d.2 * D 0 1 + d.2 ^ 2 * D 1 1) 0 := by
  let nu : Measure ℝ := mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)
  let means : Fin 2 → ℝ := ![∫ x : ℝ, x ∂nu, ∫ x : ℝ, x ^ 2 ∂nu]
  let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance nu
  have hmem := interior_subset htheta
  have hprob : IsProbabilityMeasure nu := (quadratic_tilt_mgf_identity mu theta (0, 0) hmem).1
  letI : IsProbabilityMeasure nu := hprob
  have hzero (d : ℝ × ℝ) : 0 ∈ interior
      (ProbabilityTheory.integrableExpSet (fun x : ℝ => d.1 * x + d.2 * x ^ 2) nu) :=
    quadratic_tilt_projection_interior mu theta d htheta
  have h1 : MemLp (fun x : ℝ => x) 2 nu := by
    simpa using ProbabilityTheory.memLp_of_mem_interior_integrableExpSet (hzero (1, 0)) (2 : ℝ≥0)
  have h2 : MemLp (fun x : ℝ => x ^ 2) 2 nu := by
    simpa using ProbabilityTheory.memLp_of_mem_interior_integrableExpSet (hzero (0, 1)) (2 : ℝ≥0)
  refine ⟨hprob, h1, h2, ?_⟩
  intro d
  let F : ℝ → ℝ := fun x => d.1 * x + d.2 * x ^ 2
  let f : ℝ → ℝ := fun t => Real.log (∫ x : ℝ, Real.exp
    ((theta.1 + t * d.1) * x + (theta.2 + t * d.2) * x ^ 2) ∂mu)
  let Z : (ℝ × ℝ) → ℝ := fun p => ∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu
  have h0 : 0 ∈ interior (ProbabilityTheory.integrableExpSet F nu) := hzero d
  have hF : MemLp F 2 nu := by
    simpa using ProbabilityTheory.memLp_of_mem_interior_integrableExpSet h0 (2 : ℝ≥0)
  have hmean : (∫ x, F x ∂nu) = d.1 * means 0 + d.2 * means 1 := by
    dsimp [F, means]
    rw [integral_add ((h1.const_mul d.1).integrable (by norm_num))
      ((h2.const_mul d.2).integrable (by norm_num)), integral_const_mul, integral_const_mul]
  have hcgf := ProbabilityTheory.analyticAt_cgf h0
  have hd0 : deriv (ProbabilityTheory.cgf F nu) 0 = ∫ x, F x ∂nu := by
    simpa using ProbabilityTheory.deriv_cgf_zero h0
  have hd : HasDerivAt (ProbabilityTheory.cgf F nu) (∫ x, F x ∂nu) 0 := by
    simpa only [hd0] using hcgf.differentiableAt.hasDerivAt
  have hv : deriv (deriv (ProbabilityTheory.cgf F nu)) 0 = ProbabilityTheory.variance F nu := by
    have he := ProbabilityTheory.iteratedDeriv_two_cgf h0
    rw [iteratedDeriv_succ, iteratedDeriv_one] at he
    simp only [zero_mul, Real.exp_zero, mul_one, ProbabilityTheory.mgf_zero, div_one, hd0] at he
    rw [he]
    exact (ProbabilityTheory.variance_eq_sub hF).symm
  have hdd : HasDerivAt (deriv (ProbabilityTheory.cgf F nu)) (ProbabilityTheory.variance F nu) 0 := by
    simpa only [hv] using hcgf.deriv.differentiableAt.hasDerivAt
  have ident := quadratic_tilt_mgf_identity mu theta d hmem
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ interior (ProbabilityTheory.integrableExpSet F nu) :=
    isOpen_interior.mem_nhds h0
  have heq : f =ᶠ[𝓝 (0 : ℝ)] fun t => Real.log (Z theta) + ProbabilityTheory.cgf F nu t := by
    filter_upwards [hnear] with t ht
    have hm := (ident.2.2 t).2
    have hshift := ((ident.2.2 t).1).1 (interior_subset ht)
    have hz : 0 < Z (theta.1 + t * d.1, theta.2 + t * d.2) := integral_exp_pos hshift
    change Real.log (Z (theta.1 + t * d.1, theta.2 + t * d.2)) = _
    unfold ProbabilityTheory.cgf
    rw [hm, Real.log_div (ne_of_gt hz) (ne_of_gt ident.2.1)]
    ring
  have hderEq : deriv f =ᶠ[𝓝 (0 : ℝ)] deriv (ProbabilityTheory.cgf F nu) := by
    refine heq.deriv.trans ?_
    exact Filter.Eventually.of_forall fun t => by simp
  refine ⟨h0, hF, ProbabilityTheory.integrable_pow_of_mem_interior_integrableExpSet h0, ?_, ?_⟩
  · have hh := hd.const_add (Real.log (Z theta))
    have hfder := heq.hasDerivAt_iff.mpr hh
    simpa only [hmean] using hfder
  · have hh := hderEq.hasDerivAt_iff.mpr hdd
    simpa only [F, quadratic_tilt_variance_eq nu h1 h2 d.1 d.2] using hh

end
end Shao.OQ3
