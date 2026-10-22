import Shao.OQ3.InverseTilt
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth actual tilted means and log partition for the bounded source law

Source: current/oq3/proofs/r1/report.md 137–159 and proofs/r2/report.md 38–60.
Frozen U20e v2 scope: f2daa316ffcbb81fd564f4bdc51f5e991818af98449bb4b3ca8a83609f3d3c8e.
The private weighted-moment derivative is reproved here, rather than calling another module's private names.
-/

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology BigOperators ContDiff
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

private theorem weightedMoment_contDiff (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (k : ℕ) :
    ContDiff ℝ ∞ (weightedMoment mu k) := by
  have hfinite : ∀ n : ℕ, ∀ j : ℕ, ContDiff ℝ n (weightedMoment mu j) := by
    intro n
    induction n with
    | zero =>
        intro j
        apply contDiff_zero.mpr
        have hd : Differentiable ℝ (weightedMoment mu j) :=
          fun theta => (weightedMoment_hasFDerivAt mu hb j theta).differentiableAt
        exact hd.continuous
    | succ n ih =>
        intro j
        apply contDiff_succ_iff_hasFDerivAt.mpr
        refine ⟨momentSlope mu j, ?_, fun theta => weightedMoment_hasFDerivAt mu hb j theta⟩
        exact ((ih (j + 1)).smul_const (coordinate 0)).add
          ((ih (j + 2)).smul_const (coordinate 1))
  exact contDiff_infty.mpr fun n => hfinite n k

private theorem normalizedMoment_tilt (mu : Measure ℝ) (k : ℕ) (theta : Fin 2 → ℝ) :
    normalizedMoment mu k theta =
      ∫ x : ℝ, x ^ k ∂mu.tilted (fun x => theta 0 * x + theta 1 * x ^ 2) := by
  unfold normalizedMoment weightedMoment
  simp only [pow_zero, one_mul]
  rw [integral_tilted]
  change _ = ∫ x : ℝ,
    (Real.exp (theta 0 * x + theta 1 * x ^ 2) /
      (∫ y : ℝ, Real.exp (theta 0 * y + theta 1 * y ^ 2) ∂mu)) * x ^ k ∂mu
  have hf : (fun x : ℝ =>
      (Real.exp (theta 0 * x + theta 1 * x ^ 2) /
        (∫ y : ℝ, Real.exp (theta 0 * y + theta 1 * y ^ 2) ∂mu)) * x ^ k) =
      (fun x : ℝ => (x ^ k * Real.exp (theta 0 * x + theta 1 * x ^ 2)) /
        (∫ y : ℝ, Real.exp (theta 0 * y + theta 1 * y ^ 2) ∂mu)) := by
    funext x
    ring
  rw [hf, integral_div]

theorem source_log_partition_and_tilted_mean_smooth
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) :
    let P : Measure ℝ := originalMeasure sourceEll w
    let Z : (Fin 2 → ℝ) → ℝ := fun theta =>
      ∫ x : ℝ, Real.exp (theta 0 * x + theta 1 * x ^ 2) ∂P
    let K : (Fin 2 → ℝ) → ℝ := fun theta => Real.log (Z theta)
    let tilt : (Fin 2 → ℝ) → Measure ℝ := fun theta =>
      P.tilted (fun x => theta 0 * x + theta 1 * x ^ 2)
    let mean : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun theta =>
      ![∫ x : ℝ, x ∂tilt theta, ∫ x : ℝ, x ^ 2 ∂tilt theta]
    let pr : Fin 2 → ((Fin 2 → ℝ) →L[ℝ] ℝ) := fun i => ContinuousLinearMap.proj i
    IsProbabilityMeasure P ∧
      (∀ theta : Fin 2 → ℝ,
        Integrable (fun x : ℝ => Real.exp (theta 0 * x + theta 1 * x ^ 2)) P ∧
        0 < Z theta ∧ IsProbabilityMeasure (tilt theta) ∧
        Integrable (fun x : ℝ => x) (tilt theta) ∧
        Integrable (fun x : ℝ => x ^ 2) (tilt theta)) ∧
      ContDiff ℝ ∞ K ∧ ContDiff ℝ ∞ mean ∧
      ∀ theta : Fin 2 → ℝ,
        HasFDerivAt K
          ((pr 0).smulRight (mean theta 0) + (pr 1).smulRight (mean theta 1)) theta := by
  let P : Measure ℝ := originalMeasure sourceEll w
  letI : IsProbabilityMeasure P := originalMeasure_isProbabilityMeasure sourceEll w hw hs
  let Z : (Fin 2 → ℝ) → ℝ := fun theta =>
    ∫ x : ℝ, Real.exp (theta 0 * x + theta 1 * x ^ 2) ∂P
  let K : (Fin 2 → ℝ) → ℝ := fun theta => Real.log (Z theta)
  let tilt : (Fin 2 → ℝ) → Measure ℝ := fun theta =>
    P.tilted (fun x => theta 0 * x + theta 1 * x ^ 2)
  let mean : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun theta =>
    ![∫ x : ℝ, x ∂tilt theta, ∫ x : ℝ, x ^ 2 ∂tilt theta]
  let pr : Fin 2 → ((Fin 2 → ℝ) →L[ℝ] ℝ) := fun i => ContinuousLinearMap.proj i
  have hb : ∀ᵐ x ∂P, |x| ≤ 4 + Real.sqrt 10 :=
    (originalMeasure_ae_bounds sourceEll w).mono fun _ hx => hx.2
  have hZpos (theta : Fin 2 → ℝ) : 0 < Z theta := by
    simpa only [weightedMoment, pow_zero, one_mul] using partition_pos P hb theta
  have hZeq : weightedMoment P 0 = Z := by
    funext theta
    simp only [weightedMoment, pow_zero, one_mul, Z]
  have hZ : ContDiff ℝ ∞ Z := by
    rw [← hZeq]
    exact weightedMoment_contDiff P hb 0
  have hK : ContDiff ℝ ∞ K := hZ.log (fun theta => (hZpos theta).ne')
  have hnormal (k : ℕ) : ContDiff ℝ ∞ (normalizedMoment P k) :=
    (weightedMoment_contDiff P hb k).div (weightedMoment_contDiff P hb 0)
      (fun theta => (partition_pos P hb theta).ne')
  have hm0 (theta : Fin 2 → ℝ) : mean theta 0 = normalizedMoment P 1 theta := by
    simpa only [mean, tilt, Matrix.cons_val_zero, pow_one] using
      (normalizedMoment_tilt P 1 theta).symm
  have hm1 (theta : Fin 2 → ℝ) : mean theta 1 = normalizedMoment P 2 theta := by
    simpa only [mean, tilt, Matrix.cons_val_one, Matrix.cons_val_fin_one] using
      (normalizedMoment_tilt P 2 theta).symm
  have hmean : mean = fun theta => ![normalizedMoment P 1 theta, normalizedMoment P 2 theta] := by
    funext theta
    ext i
    fin_cases i
    · exact hm0 theta
    · exact hm1 theta
  have hmeanSmooth : ContDiff ℝ ∞ mean := by
    rw [hmean]
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · simpa using hnormal 1
    · simpa using hnormal 2
  have hgrad (theta : Fin 2 → ℝ) : partitionGradient P theta =
      (pr 0).smulRight (mean theta 0) + (pr 1).smulRight (mean theta 1) := by
    ext v
    simp only [partitionGradient, coordinate, pr, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [hm0 theta, hm1 theta]
    ring
  refine ⟨inferInstance, ?_, hK, hmeanSmooth, ?_⟩
  · intro theta
    have hi : Integrable (fun x : ℝ => Real.exp (theta 0 * x + theta 1 * x ^ 2)) P := by
      simpa only [pow_zero, one_mul] using weighted_integrable P hb 0 theta
    letI : IsProbabilityMeasure (tilt theta) := isProbabilityMeasure_tilted hi
    have hbt : ∀ᵐ x ∂tilt theta, |x| ≤ 4 + Real.sqrt 10 :=
      (tilted_absolutelyContinuous P (fun x => theta 0 * x + theta 1 * x ^ 2)).ae_le hb
    refine ⟨hi, hZpos theta, inferInstance, ?_, ?_⟩
    · apply integrable_continuous_of_fixed_bounds (tilt theta) hbt
      fun_prop
    · apply integrable_continuous_of_fixed_bounds (tilt theta) hbt
      fun_prop
  · intro theta
    have hd := logPartition_hasFDerivAt P hb theta
    rw [hgrad theta] at hd
    simpa only [weightedMoment, pow_zero, one_mul] using hd

end
end Shao.OQ3
