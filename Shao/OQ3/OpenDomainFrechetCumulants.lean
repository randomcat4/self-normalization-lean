import Shao.OQ3.OpenDomainWeightedMoments
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology
noncomputable section

private def qWeightedMoment (mu : Measure ℝ) (k : ℕ) (p : ℝ × ℝ) : ℝ :=
  ∫ x : ℝ, x ^ k * Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu

private def qMomentSlope (mu : Measure ℝ) (k : ℕ) (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  qWeightedMoment mu (k + 1) p • ContinuousLinearMap.fst ℝ ℝ ℝ +
    qWeightedMoment mu (k + 2) p • ContinuousLinearMap.snd ℝ ℝ ℝ

private def qNormalizedMoment (mu : Measure ℝ) (k : ℕ) (p : ℝ × ℝ) : ℝ :=
  qWeightedMoment mu k p / qWeightedMoment mu 0 p

private def qNormalizedSlope (mu : Measure ℝ) (k : ℕ) (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (qNormalizedMoment mu (k + 1) p - qNormalizedMoment mu k p * qNormalizedMoment mu 1 p) •
      ContinuousLinearMap.fst ℝ ℝ ℝ +
    (qNormalizedMoment mu (k + 2) p - qNormalizedMoment mu k p * qNormalizedMoment mu 2 p) •
      ContinuousLinearMap.snd ℝ ℝ ℝ

private def qPartitionGradient (mu : Measure ℝ) (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  qNormalizedMoment mu 1 p • ContinuousLinearMap.fst ℝ ℝ ℝ +
    qNormalizedMoment mu 2 p • ContinuousLinearMap.snd ℝ ℝ ℝ

private theorem qPartition_pos (mu : Measure ℝ) [IsProbabilityMeasure mu] (p : ℝ × ℝ)
    (hp : p ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))) :
    0 < qWeightedMoment mu 0 p := by
  simpa only [qWeightedMoment, pow_zero, one_mul] using
    integral_exp_pos (show Integrable
      (fun x : ℝ => Real.exp (p.1 * x + p.2 * x ^ 2)) mu from interior_subset hp)

private theorem qNormalizedMoment_hasFDerivAt
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (k : ℕ) (p : ℝ × ℝ)
    (hp : p ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))) :
    HasFDerivAt (qNormalizedMoment mu k) (qNormalizedSlope mu k p) p := by
  have hz := (qPartition_pos mu p hp).ne'
  have h0 : HasFDerivAt (qWeightedMoment mu 0) (qMomentSlope mu 0 p) p :=
    (open_domain_weighted_moment_hasFDerivAt mu 0 p hp).2
  have hk : HasFDerivAt (qWeightedMoment mu k) (qMomentSlope mu k p) p :=
    (open_domain_weighted_moment_hasFDerivAt mu k p hp).2
  have hi := (hasDerivAt_inv hz).comp_hasFDerivAt p h0
  have hd := hk.mul hi
  convert hd using 1
  · funext t
    simp only [qNormalizedMoment, div_eq_mul_inv, Pi.mul_apply, Function.comp_apply]
  · apply ContinuousLinearMap.ext
    intro v
    simp [qNormalizedSlope, qNormalizedMoment, qMomentSlope]
    field_simp [hz]
    <;> ring

private theorem qLogPartition_hasFDerivAt
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (p : ℝ × ℝ)
    (hp : p ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))) :
    HasFDerivAt (fun t => Real.log (qWeightedMoment mu 0 t)) (qPartitionGradient mu p) p := by
  have h0 : HasFDerivAt (qWeightedMoment mu 0) (qMomentSlope mu 0 p) p :=
    (open_domain_weighted_moment_hasFDerivAt mu 0 p hp).2
  have hd := h0.log (qPartition_pos mu p hp).ne'
  convert hd using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [qPartitionGradient, qNormalizedMoment, qMomentSlope]
  ring

private theorem qTiltedMoment_eq (mu : Measure ℝ) (k : ℕ) (p : ℝ × ℝ) :
    (∫ x : ℝ, x ^ k ∂mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) =
      qNormalizedMoment mu k p := by
  rw [integral_tilted]
  unfold qNormalizedMoment qWeightedMoment
  simp only [pow_zero, one_mul, smul_eq_mul]
  have hf : (fun x : ℝ =>
      (Real.exp (p.1 * x + p.2 * x ^ 2) / (∫ y, Real.exp (p.1 * y + p.2 * y ^ 2) ∂mu)) * x ^ k) =
      (fun x => (x ^ k * Real.exp (p.1 * x + p.2 * x ^ 2)) /
        (∫ y, Real.exp (p.1 * y + p.2 * y ^ 2) ∂mu)) := by
    funext x
    ring
  rw [hf, integral_div]

theorem open_domain_quadratic_tilt_frechet_cumulants
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))) :
    let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    let means : (ℝ × ℝ) → (ℝ × ℝ) := fun p =>
      (∫ x : ℝ, x ∂nu p, ∫ x : ℝ, x ^ 2 ∂nu p)
    let K : (ℝ × ℝ) → ℝ := fun p =>
      Real.log (∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu)
    let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (nu theta)
    let pr0 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
    let pr1 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
    let row0 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 0 • pr0 + D 0 1 • pr1
    let row1 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 1 • pr0 + D 1 1 • pr1
    let gradient : (ℝ × ℝ) →L[ℝ] ℝ :=
      (means theta).1 • pr0 + (means theta).2 • pr1
    let hessian : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ) :=
      row0.smulRight pr0 + row1.smulRight pr1
    IsProbabilityMeasure (nu theta) ∧
      MemLp (fun x : ℝ => x) 2 (nu theta) ∧
      MemLp (fun x : ℝ => x ^ 2) 2 (nu theta) ∧
      HasFDerivAt means (row0.prod row1) theta ∧
      HasFDerivAt K gradient theta ∧
      HasFDerivAt (fun p => fderiv ℝ K p) hessian theta := by
  let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
    mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
  let means : (ℝ × ℝ) → (ℝ × ℝ) := fun p =>
    (∫ x : ℝ, x ∂nu p, ∫ x : ℝ, x ^ 2 ∂nu p)
  let K : (ℝ × ℝ) → ℝ := fun p =>
    Real.log (∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu)
  let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (nu theta)
  let pr0 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let pr1 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  let row0 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 0 • pr0 + D 0 1 • pr1
  let row1 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 1 • pr0 + D 1 1 • pr1
  have h := open_domain_quadratic_tilt_directional_cumulants mu theta htheta
  have hp : IsProbabilityMeasure (nu theta) := h.1
  letI : IsProbabilityMeasure (nu theta) := hp
  have hx : MemLp (fun x : ℝ => x) 2 (nu theta) := h.2.1
  have hx2 : MemLp (fun x : ℝ => x ^ 2) 2 (nu theta) := h.2.2.1
  have hR (k : ℕ) : (∫ x : ℝ, x ^ k ∂nu theta) = qNormalizedMoment mu k theta :=
    qTiltedMoment_eq mu k theta
  have h00 : D 0 0 = qNormalizedMoment mu 2 theta - qNormalizedMoment mu 1 theta ^ 2 := by
    change ProbabilityTheory.variance (fun x : ℝ => x) (nu theta) = _
    rw [ProbabilityTheory.variance_eq_sub hx]
    simpa only [Pi.pow_apply, pow_one] using congrArg₂ (fun a b : ℝ => a - b ^ 2) (hR 2) (hR 1)
  have h01 : D 0 1 = qNormalizedMoment mu 3 theta -
      qNormalizedMoment mu 1 theta * qNormalizedMoment mu 2 theta := by
    change ProbabilityTheory.covariance (fun x : ℝ => x) (fun x => x ^ 2) (nu theta) = _
    rw [ProbabilityTheory.covariance_eq_sub hx hx2]
    have hf : (fun x : ℝ => x * x ^ 2) = (fun x => x ^ 3) := by funext x; ring
    change (∫ x : ℝ, x * x ^ 2 ∂nu theta) - _ = _
    rw [hf, hR 3, hR 2]
    simpa only [pow_one] using congrArg (fun a : ℝ => qNormalizedMoment mu 3 theta -
      a * qNormalizedMoment mu 2 theta) (hR 1)
  have h11 : D 1 1 = qNormalizedMoment mu 4 theta - qNormalizedMoment mu 2 theta ^ 2 := by
    change ProbabilityTheory.variance (fun x : ℝ => x ^ 2) (nu theta) = _
    rw [ProbabilityTheory.variance_eq_sub hx2]
    have hf : (fun x : ℝ => (x ^ 2) ^ 2) = (fun x => x ^ 4) := by funext x; ring
    simp only [Pi.pow_apply, hf, hR 4, hR 2]
  have hr0 : qNormalizedSlope mu 1 theta = row0 := by
    apply ContinuousLinearMap.ext
    intro v
    change (qNormalizedMoment mu 2 theta - qNormalizedMoment mu 1 theta * qNormalizedMoment mu 1 theta) * v.1 +
      (qNormalizedMoment mu 3 theta - qNormalizedMoment mu 1 theta * qNormalizedMoment mu 2 theta) * v.2 =
        D 0 0 * v.1 + D 0 1 * v.2
    rw [h00, h01]
    ring
  have hr1 : qNormalizedSlope mu 2 theta = row1 := by
    apply ContinuousLinearMap.ext
    intro v
    change (qNormalizedMoment mu 3 theta - qNormalizedMoment mu 2 theta * qNormalizedMoment mu 1 theta) * v.1 +
      (qNormalizedMoment mu 4 theta - qNormalizedMoment mu 2 theta * qNormalizedMoment mu 2 theta) * v.2 =
        D 0 1 * v.1 + D 1 1 * v.2
    rw [h01, h11]
    ring
  have hmeans : means = fun p => (qNormalizedMoment mu 1 p, qNormalizedMoment mu 2 p) := by
    funext p
    apply Prod.ext
    · simpa only [means, nu, pow_one] using qTiltedMoment_eq mu 1 p
    · exact qTiltedMoment_eq mu 2 p
  have hmeanDer := (qNormalizedMoment_hasFDerivAt mu 1 theta htheta).prodMk
    (qNormalizedMoment_hasFDerivAt mu 2 theta htheta)
  rw [hr0, hr1, ← hmeans] at hmeanDer
  have hfirst := qLogPartition_hasFDerivAt mu theta htheta
  have hgrad : qPartitionGradient mu theta = (means theta).1 • pr0 + (means theta).2 • pr1 := by
    rw [hmeans]
    rfl
  rw [hgrad] at hfirst
  have hsecond := ((qNormalizedMoment_hasFDerivAt mu 1 theta htheta).smul_const pr0).add
    ((qNormalizedMoment_hasFDerivAt mu 2 theta htheta).smul_const pr1)
  change HasFDerivAt (qPartitionGradient mu) _ theta at hsecond
  rw [hr0, hr1] at hsecond
  have heq : (fun p => fderiv ℝ (fun t => Real.log (qWeightedMoment mu 0 t)) p) =ᶠ[𝓝 theta]
      qPartitionGradient mu := by
    filter_upwards [isOpen_interior.mem_nhds htheta] with p hp'
    exact (qLogPartition_hasFDerivAt mu p hp').fderiv
  have hsecond' := heq.hasFDerivAt_iff.mpr hsecond
  refine ⟨hp, hx, hx2, hmeanDer, ?_, ?_⟩
  · simpa only [K, qWeightedMoment, pow_zero, one_mul] using hfirst
  · simpa only [K, qWeightedMoment, pow_zero, one_mul] using hsecond'

end
end Shao.OQ3
