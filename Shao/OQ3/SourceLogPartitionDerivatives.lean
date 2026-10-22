import Shao.OQ3.RegularCovariance
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Actual first and second derivatives of the source log partition

Source: current/oq3/proofs/r1/report.md, lines 146-159 and 239-257.
Source SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U19c scope: 66a18870fa58a2f4ca0853c5fe9ac0f6d27b292972a8feb6f6c089c0c502d6b9.
-/

namespace Shao.OQ3

open MeasureTheory
open scoped Matrix Topology BigOperators

noncomputable section

private def coordinate (i : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj i

private def weightedMoment (mu : Measure ℝ) (k : ℕ) (theta : Fin 2 → ℝ) : ℝ :=
  ∫ x : ℝ, x ^ k * Real.exp (theta 0 * x + theta 1 * x ^ 2) ∂mu

private def momentSlope (mu : Measure ℝ) (k : ℕ) (theta : Fin 2 → ℝ) :
    (Fin 2 → ℝ) →L[ℝ] ℝ :=
  weightedMoment mu (k + 1) theta • coordinate 0 +
    weightedMoment mu (k + 2) theta • coordinate 1

private def normalizedMoment (mu : Measure ℝ) (k : ℕ) (theta : Fin 2 → ℝ) : ℝ :=
  weightedMoment mu k theta / weightedMoment mu 0 theta

private def normalizedSlope (mu : Measure ℝ) (k : ℕ) (theta : Fin 2 → ℝ) :
    (Fin 2 → ℝ) →L[ℝ] ℝ :=
  (normalizedMoment mu (k + 1) theta -
      normalizedMoment mu k theta * normalizedMoment mu 1 theta) • coordinate 0 +
    (normalizedMoment mu (k + 2) theta -
      normalizedMoment mu k theta * normalizedMoment mu 2 theta) • coordinate 1

private def partitionGradient (mu : Measure ℝ) (theta : Fin 2 → ℝ) :
    (Fin 2 → ℝ) →L[ℝ] ℝ :=
  normalizedMoment mu 1 theta • coordinate 0 + normalizedMoment mu 2 theta • coordinate 1

private theorem weighted_integrable (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (k : ℕ) (theta : Fin 2 → ℝ) :
    Integrable (fun x : ℝ => x ^ k * Real.exp (theta 0 * x + theta 1 * x ^ 2)) mu := by
  apply integrable_continuous_of_fixed_bounds mu hb
  fun_prop

private theorem partition_pos (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (theta : Fin 2 → ℝ) :
    0 < weightedMoment mu 0 theta := by
  simpa only [weightedMoment, pow_zero, one_mul] using
    integral_exp_pos (by simpa only [pow_zero, one_mul] using weighted_integrable mu hb 0 theta)

private theorem weightedMoment_hasFDerivAt (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (k : ℕ) (theta : Fin 2 → ℝ) :
    HasFDerivAt (weightedMoment mu k) (momentSlope mu k theta) theta := by
  let F : (Fin 2 → ℝ) → ℝ → ℝ := fun t x =>
    x ^ k * Real.exp (t 0 * x + t 1 * x ^ 2)
  let F' : (Fin 2 → ℝ) → ℝ → ((Fin 2 → ℝ) →L[ℝ] ℝ) := fun t x =>
    (x ^ (k + 1) * Real.exp (t 0 * x + t 1 * x ^ 2)) • coordinate 0 +
      (x ^ (k + 2) * Real.exp (t 0 * x + t 1 * x ^ 2)) • coordinate 1
  have hdiff (x : ℝ) (t : Fin 2 → ℝ) : HasFDerivAt (fun t => F t x) (F' t x) t := by
    have hlin : HasFDerivAt (fun t : Fin 2 → ℝ => t 0 * x + t 1 * x ^ 2)
        (x • coordinate 0 + x ^ 2 • coordinate 1) t := by
      convert ((coordinate 0).hasFDerivAt.mul_const x).add
        ((coordinate 1).hasFDerivAt.mul_const (x ^ 2)) using 1 <;>
        ext v <;> simp [coordinate, mul_comm]
    convert hlin.exp.const_mul (x ^ k) using 1
    ext v
    simp [F', ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      coordinate, pow_add]
    ring
  have hcont : Continuous (fun p : (Fin 2 → ℝ) × ℝ => F' p.1 p.2) := by
    dsimp [F']
    fun_prop
  have hcpt : IsCompact (Metric.closedBall theta 1 ×ˢ
      Set.Icc (-(4 + Real.sqrt 10)) (4 + Real.sqrt 10)) :=
    (isCompact_closedBall theta 1).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hcont.continuousOn
  have hbound : ∀ᵐ x ∂mu, ∀ t ∈ Metric.ball theta 1, ‖F' t x‖ ≤ C := by
    filter_upwards [hb] with x hx
    intro t ht
    exact hC (t, x) ⟨Metric.ball_subset_closedBall ht, abs_le.mp hx⟩
  have hmeas (t : Fin 2 → ℝ) : AEStronglyMeasurable (F t) mu := by
    have hc : Continuous (F t) := by dsimp [F]; fun_prop
    exact hc.aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (F' theta) mu := by
    have hc : Continuous (F' theta) := by dsimp [F']; fun_prop
    exact hc.aestronglyMeasurable
  have hd := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (Metric.ball_mem_nhds theta zero_lt_one) (Filter.Eventually.of_forall hmeas)
    (weighted_integrable mu hb k theta) hmeas' hbound (integrable_const C)
    (Filter.Eventually.of_forall fun x t _ => hdiff x t)
  have hi0 := (weighted_integrable mu hb (k + 1) theta).smul_const (coordinate 0)
  have hi1 := (weighted_integrable mu hb (k + 2) theta).smul_const (coordinate 1)
  have hder : (∫ x, F' theta x ∂mu) = momentSlope mu k theta := by
    dsimp [F', momentSlope, weightedMoment]
    rw [integral_add hi0 hi1, integral_smul_const, integral_smul_const]
  rw [hder] at hd
  exact hd

private theorem normalizedMoment_hasFDerivAt (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (k : ℕ) (theta : Fin 2 → ℝ) :
    HasFDerivAt (normalizedMoment mu k) (normalizedSlope mu k theta) theta := by
  have hz := (partition_pos mu hb theta).ne'
  have hi := (hasDerivAt_inv hz).comp_hasFDerivAt theta
    (weightedMoment_hasFDerivAt mu hb 0 theta)
  have hd := (weightedMoment_hasFDerivAt mu hb k theta).mul hi
  convert hd using 1
  · funext t
    simp only [normalizedMoment, div_eq_mul_inv, Pi.mul_apply, Function.comp_apply]
  · ext v
    simp [normalizedSlope, normalizedMoment, momentSlope, coordinate,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    field_simp [hz]
    <;> ring

private theorem logPartition_hasFDerivAt (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (theta : Fin 2 → ℝ) :
    HasFDerivAt (fun t => Real.log (weightedMoment mu 0 t))
      (partitionGradient mu theta) theta := by
  have hd := (weightedMoment_hasFDerivAt mu hb 0 theta).log
    (partition_pos mu hb theta).ne'
  convert hd using 1
  ext v
  simp [partitionGradient, normalizedMoment, momentSlope, coordinate,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  ring

private theorem source_normalized_moment (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (k : ℕ) :
    normalizedMoment (originalMeasure sourceEll w) k ![8 * sourceEll, -sourceEll] =
      ∫ x : ℝ, x ^ k ∂atomicMeasure w := by
  letI := originalMeasure_isProbabilityMeasure sourceEll w hw hs
  have hb := (originalMeasure_ae_bounds sourceEll w).mono fun _ hx => hx.2
  have hi := weighted_integrable (originalMeasure sourceEll w) hb k
    ![8 * sourceEll, -sourceEll]
  have hp := partition_pos (originalMeasure sourceEll w) hb ![8 * sourceEll, -sourceEll]
  have he (x : ℝ) : ![8 * sourceEll, -sourceEll] 0 * x +
      ![8 * sourceEll, -sourceEll] 1 * x ^ 2 = sourceEll * normalValue x := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, normalValue]
    ring
  unfold normalizedMoment weightedMoment
  simp only [pow_zero, one_mul]
  simp_rw [he]
  rw [← originalMeasure_retilt sourceEll w hw hs, integral_tilted]
  change _ = ∫ x : ℝ, (Real.exp (sourceEll * normalValue x) /
    (∫ y, Real.exp (sourceEll * normalValue y) ∂originalMeasure sourceEll w)) * x ^ k
      ∂originalMeasure sourceEll w
  have hf : (fun x : ℝ => (Real.exp (sourceEll * normalValue x) /
      (∫ y, Real.exp (sourceEll * normalValue y) ∂originalMeasure sourceEll w)) * x ^ k) =
      (fun x => (x ^ k * Real.exp (sourceEll * normalValue x)) /
        (∫ y, Real.exp (sourceEll * normalValue y) ∂originalMeasure sourceEll w)) := by
    funext x
    ring
  rw [hf, integral_div]

theorem source_log_partition_first_and_second_derivatives
    (q : ℝ) (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k : Fin 4,
      HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
        (constraintTarget q k)) :
    let P : Measure ℝ := originalMeasure sourceEll w
    let K : (Fin 2 → ℝ) → ℝ := fun theta =>
      Real.log (∫ x : ℝ, Real.exp (theta 0 * x + theta 1 * x ^ 2) ∂P)
    let theta0 : Fin 2 → ℝ := ![8 * sourceEll, -sourceEll]
    let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (atomicMeasure w)
    let pr : Fin 2 → ((Fin 2 → ℝ) →L[ℝ] ℝ) := fun i => ContinuousLinearMap.proj i
    let gradient : (Fin 2 → ℝ) →L[ℝ] ℝ :=
      (pr 0).smulRight (q / 4) + (pr 1).smulRight q
    let hessian : (Fin 2 → ℝ) →L[ℝ] ((Fin 2 → ℝ) →L[ℝ] ℝ) :=
      ∑ i : Fin 2, ∑ j : Fin 2, (pr i).smulRight ((pr j).smulRight (D i j))
    HasFDerivAt K gradient theta0 ∧
      HasFDerivAt (fun theta => fderiv ℝ K theta) hessian theta0 := by
  have hs : HasSum w 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  let P := originalMeasure sourceEll w
  let theta0 : Fin 2 → ℝ := ![8 * sourceEll, -sourceEll]
  letI := originalMeasure_isProbabilityMeasure sourceEll w hw hs
  letI := atomicMeasure_isProbabilityMeasure w hw hs
  have hb : ∀ᵐ x ∂P, |x| ≤ 4 + Real.sqrt 10 :=
    (originalMeasure_ae_bounds sourceEll w).mono fun _ hx => hx.2
  have hR (k : ℕ) : normalizedMoment P k theta0 = ∫ x : ℝ, x ^ k ∂atomicMeasure w :=
    source_normalized_moment w hw hs k
  have hmean : (∫ x : ℝ, x ∂atomicMeasure w) = q / 4 :=
    (atomicMeasure_mean sourceEll q w hw hm).2
  have hsq : (∫ x : ℝ, x ^ 2 ∂atomicMeasure w) = q := by
    simpa [constraintFeature, constraintTarget] using
      (atomicMeasure_constraints sourceEll q w hw hm 3).2
  have hLp (k : ℕ) : MemLp (fun x : ℝ => x ^ k) 2 (atomicMeasure w) := by
    have hc : Continuous (fun x : ℝ => x ^ k) := by fun_prop
    apply MemLp.of_bound hc.aestronglyMeasurable ((4 + Real.sqrt 10) ^ k)
    filter_upwards [atomicMeasure_ae_bounds w] with x hx
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hx.2 k
  have hx : MemLp (fun x : ℝ => x) 2 (atomicMeasure w) := by simpa using hLp 1
  have hx2 := hLp 2
  have h00 : parabolaCovariance (atomicMeasure w) 0 0 =
      (∫ x : ℝ, x ^ 2 ∂atomicMeasure w) - (∫ x : ℝ, x ∂atomicMeasure w) ^ 2 := by
    simpa only [parabolaCovariance, Matrix.cons_val_zero, Pi.pow_apply] using
      ProbabilityTheory.variance_eq_sub hx
  have h01 : parabolaCovariance (atomicMeasure w) 0 1 =
      (∫ x : ℝ, x ^ 3 ∂atomicMeasure w) -
        (∫ x : ℝ, x ∂atomicMeasure w) * (∫ x : ℝ, x ^ 2 ∂atomicMeasure w) := by
    change ProbabilityTheory.covariance (fun x : ℝ => x) (fun x => x ^ 2) _ = _
    rw [ProbabilityTheory.covariance_eq_sub hx hx2]
    have hf : (fun x : ℝ => x * x ^ 2) = (fun x => x ^ 3) := by funext x; ring
    change (∫ x : ℝ, x * x ^ 2 ∂atomicMeasure w) - _ = _
    rw [hf]
  have h10 : parabolaCovariance (atomicMeasure w) 1 0 =
      parabolaCovariance (atomicMeasure w) 0 1 := rfl
  have h11 : parabolaCovariance (atomicMeasure w) 1 1 =
      (∫ x : ℝ, x ^ 4 ∂atomicMeasure w) - (∫ x : ℝ, x ^ 2 ∂atomicMeasure w) ^ 2 := by
    change ProbabilityTheory.variance (fun x : ℝ => x ^ 2) _ = _
    have hf : (fun x : ℝ => (x ^ 2) ^ 2) = (fun x => x ^ 4) := by funext x; ring
    simpa only [Pi.pow_apply, hf] using ProbabilityTheory.variance_eq_sub hx2
  have hgrad : partitionGradient P theta0 =
      (coordinate 0).smulRight (q / 4) + (coordinate 1).smulRight q := by
    ext v
    simp [partitionGradient, hR, hmean, hsq, coordinate]
    ring
  have hHess : (normalizedSlope P 1 theta0).smulRight (coordinate 0) +
      (normalizedSlope P 2 theta0).smulRight (coordinate 1) =
      ∑ i : Fin 2, ∑ j : Fin 2,
        (coordinate i).smulRight ((coordinate j).smulRight
          (parabolaCovariance (atomicMeasure w) i j)) := by
    ext v u
    simp only [Fin.sum_univ_two, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
      normalizedSlope, coordinate, ContinuousLinearMap.proj_apply, smul_eq_mul]
    norm_num only [Nat.reduceAdd]
    rw [hR 1, hR 2, hR 3, hR 4, h10, h00, h01, h11]
    simp only [pow_one]
    ring
  have hfirst := logPartition_hasFDerivAt P hb theta0
  have hfderiv : fderiv ℝ (fun t => Real.log (weightedMoment P 0 t)) = partitionGradient P :=
    fderiv_eq (logPartition_hasFDerivAt P hb)
  have hsecond := ((normalizedMoment_hasFDerivAt P hb 1 theta0).smul_const (coordinate 0)).add
    ((normalizedMoment_hasFDerivAt P hb 2 theta0).smul_const (coordinate 1))
  change HasFDerivAt (partitionGradient P) _ theta0 at hsecond
  rw [hHess] at hsecond
  rw [hgrad] at hfirst
  dsimp only
  constructor
  · simpa only [weightedMoment, pow_zero, one_mul, P, theta0, coordinate] using hfirst
  · rw [← hfderiv] at hsecond
    simpa only [weightedMoment, pow_zero, one_mul, P, theta0, coordinate] using hsecond

end
end Shao.OQ3
