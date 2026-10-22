import Shao.OQ3.AtomicProductControl
import Shao.OQ3.RegularCovariance
import Mathlib.Analysis.Matrix.Normed

/-!
# Moment continuity and a future-tail budget for the corrected scale

Source: current/oq3/proofs/r1/report.md, lines 239-257, 438-443 and 523-529.
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U11d v2 scope: 4857b5da48d16c4f05c6b81fed92f7e9109ad8b94cd355e4c78ce0e8f7f28d8c.
-/

namespace Shao.OQ3

open MeasureTheory
open scoped Matrix Matrix.Norms.Elementwise

noncomputable section

def correctedInverseScale (ell q : ℝ) (mu : Measure ℝ) : ℝ :=
  (ell * Real.sqrt (normalVariance mu -
    (32 * ell / q) * (parabolaCovariance mu).det))⁻¹

theorem atomic_power_integral_sub_le (w v : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hsw : HasSum w 1) (hsv : HasSum v 1) (k : ℕ) :
  |(∫ x : ℝ, x ^ k ∂atomicMeasure w) - (∫ x : ℝ, x ^ k ∂atomicMeasure v)| ≤
    (4 + Real.sqrt 10) ^ k * atomicMassL1 w v := by
  apply atomicMeasure_integral_sub_le w v hw hv hsw.summable hsv.summable _
    (pow_nonneg (by positivity) k) (fun x => x ^ k)
  intro i
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (fixedAtom_bounds i).2 k

private def rawMomentVector (w : AtomicIndex → ℝ) : Fin 4 → ℝ :=
  fun i => ∫ x : ℝ, x ^ (i.val + 1) ∂atomicMeasure w

private def covarianceFromMoments (m : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![m 1 - (m 0) ^ 2, m 2 - m 0 * m 1],
    ![m 2 - m 0 * m 1, m 3 - (m 1) ^ 2]]

private def momentData (m : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ × ℝ :=
  (covarianceFromMoments m,
    64 * covarianceFromMoments m 0 0 - 16 * covarianceFromMoments m 0 1 +
      covarianceFromMoments m 1 1)

private theorem covariance_raw_moments (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) :
    parabolaCovariance (atomicMeasure w) = covarianceFromMoments (rawMomentVector w) := by
  let := atomicMeasure_isProbabilityMeasure w hw hs
  have hLp (k : ℕ) : MemLp (fun x : ℝ => x ^ k) 2 (atomicMeasure w) := by
    have hf : Measurable (fun x : ℝ => x ^ k) := by fun_prop
    apply MemLp.of_bound hf.aestronglyMeasurable ((4 + Real.sqrt 10) ^ k)
    filter_upwards [atomicMeasure_ae_bounds w] with x hx
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hx.2 k
  have hx : MemLp (fun x : ℝ => x) 2 (atomicMeasure w) := by simpa using hLp 1
  have hx2 := hLp 2
  have hv1 := ProbabilityTheory.variance_eq_sub hx
  have hv2 : ProbabilityTheory.variance (fun x : ℝ => x ^ 2) (atomicMeasure w) =
      (∫ x : ℝ, x ^ 4 ∂atomicMeasure w) - (∫ x : ℝ, x ^ 2 ∂atomicMeasure w) ^ 2 := by
    have hfun : (fun x : ℝ => (x ^ 2) ^ 2) = (fun x => x ^ 4) := by funext x; ring
    simpa only [Pi.pow_apply, hfun] using ProbabilityTheory.variance_eq_sub hx2
  have hcov : ProbabilityTheory.covariance (fun x : ℝ => x) (fun x => x ^ 2)
      (atomicMeasure w) = (∫ x : ℝ, x ^ 3 ∂atomicMeasure w) -
        (∫ x : ℝ, x ∂atomicMeasure w) * (∫ x : ℝ, x ^ 2 ∂atomicMeasure w) := by
    rw [ProbabilityTheory.covariance_eq_sub hx hx2]
    have hfun : (fun x : ℝ => x * x ^ 2) = (fun x => x ^ 3) := by funext x; ring
    change (∫ x : ℝ, x * x ^ 2 ∂atomicMeasure w) - _ = _
    rw [hfun]
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [parabolaCovariance, covarianceFromMoments, rawMomentVector, Pi.pow_apply] using hv1
  · simpa [parabolaCovariance, covarianceFromMoments, rawMomentVector, Pi.pow_apply] using hcov
  · simpa [parabolaCovariance, covarianceFromMoments, rawMomentVector, Pi.pow_apply] using hcov
  · simpa [parabolaCovariance, covarianceFromMoments, rawMomentVector, Pi.pow_apply] using hv2

private theorem momentData_eq (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) :
    momentData (rawMomentVector w) =
      (parabolaCovariance (atomicMeasure w), normalVariance (atomicMeasure w)) := by
  let := atomicMeasure_isProbabilityMeasure w hw hs
  apply Prod.ext
  · exact (covariance_raw_moments w hw hs).symm
  · rw [normalVariance_eq_covariance (atomicMeasure w)
      ((atomicMeasure_ae_bounds w).mono fun _ hx => hx.2), covariance_raw_moments w hw hs]
    rfl

private theorem continuous_momentData : Continuous momentData := by
  have hc : Continuous covarianceFromMoments := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    fin_cases i <;> fin_cases j <;> simp only [covarianceFromMoments] <;> fun_prop
  have hn : Continuous (fun m : Fin 4 → ℝ =>
      64 * covarianceFromMoments m 0 0 - 16 * covarianceFromMoments m 0 1 +
        covarianceFromMoments m 1 1) := by
    simp only [covarianceFromMoments, Matrix.cons_val_zero, Matrix.cons_val_one]
    fun_prop
  exact hc.prodMk hn

private theorem rawMomentVector_norm_le (w v : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hsw : HasSum w 1) (hsv : HasSum v 1) :
    ‖rawMomentVector v - rawMomentVector w‖ ≤
      (4 + Real.sqrt 10) ^ 4 * atomicMassL1 v w := by
  have hL : 0 ≤ atomicMassL1 v w := tsum_nonneg fun _ => abs_nonneg _
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by positivity) hL)).mpr
  intro i
  change |(∫ x : ℝ, x ^ (i.val + 1) ∂atomicMeasure v) -
    (∫ x : ℝ, x ^ (i.val + 1) ∂atomicMeasure w)| ≤ _
  exact (atomic_power_integral_sub_le v w hv hw hsv hsw (i.val + 1)).trans
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by nlinarith [Real.sqrt_nonneg (10 : ℝ)] :
        1 ≤ 4 + Real.sqrt 10) (Nat.succ_le_of_lt i.isLt)) hL)

theorem exists_atomic_covariance_radius (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsw : HasSum w 1) (eta : ℝ) (heta : 0 < eta) :
  ∃ delta : ℝ, 0 < delta ∧ ∀ (v : AtomicIndex → ℝ),
    (∀ i, 0 ≤ v i) → HasSum v 1 → atomicMassL1 v w < delta →
      ‖parabolaCovariance (atomicMeasure v) - parabolaCovariance (atomicMeasure w)‖ < eta ∧
      |normalVariance (atomicMeasure v) - normalVariance (atomicMeasure w)| < eta := by
  have hcont : ContinuousAt momentData (rawMomentVector w) := continuous_momentData.continuousAt
  obtain ⟨d, hd, hnear⟩ := Metric.continuousAt_iff.mp hcont eta heta
  have hC : 0 < (4 + Real.sqrt 10) ^ 4 := by positivity
  refine ⟨d / (4 + Real.sqrt 10) ^ 4, div_pos hd hC, ?_⟩
  intro v hv hsv hL
  have hdist : dist (rawMomentVector v) (rawMomentVector w) < d := by
    rw [dist_eq_norm]
    exact (rawMomentVector_norm_le w v hw hv hsw hsv).trans_lt
      (by nlinarith [(lt_div_iff₀ hC).mp hL])
  have h := hnear hdist
  rw [momentData_eq v hv hsv, momentData_eq w hw hsw, Prod.dist_eq,
    dist_eq_norm, Real.dist_eq] at h
  exact max_lt_iff.mp h

theorem source_atomic_corrected_radicand_pos (q : ℝ) (hlo : 1 < q) (hhi : q < 103 / 100)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i) (hbase : ∀ i : Fin 4, 0 < w (Sum.inl i))
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
      (constraintTarget q k)) :
  0 < normalVariance (atomicMeasure w) -
    (32 * sourceEll / q) * (parabolaCovariance (atomicMeasure w)).det := by
  have hmass : HasSum w 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  let := atomicMeasure_isProbabilityMeasure w hw hmass
  have hb := (atomicMeasure_ae_bounds w).mono fun _ hx => hx.2
  have hbpos (i : Fin 4) : 0 < (atomicMeasure w).real {baseAtom i} := by
    change 0 < (atomicMeasure w).real {fixedAtom (Sum.inl i)}
    rw [atomicMeasure_real_singleton w hw]
    exact hbase i
  have hD := parabolaCovariance_det_pos (atomicMeasure w) hb hbpos
  have h := mul_pos (atomic_curvature_pos q hlo hhi w hw hbase hm) hD
  rw [sub_mul, div_mul_cancel₀ _ hD.ne'] at h
  exact h

theorem exists_atomic_corrected_scale_radius (ell : ℝ) (hell : 0 < ell) (q : ℝ)
    (hq : 0 < q) (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i) (hsw : HasSum w 1)
    (hR : 0 < normalVariance (atomicMeasure w) -
      (32 * ell / q) * (parabolaCovariance (atomicMeasure w)).det)
    (eta : ℝ) (heta : 0 < eta) :
  ∃ delta : ℝ, 0 < delta ∧ ∀ (v : AtomicIndex → ℝ),
    (∀ i, 0 ≤ v i) → HasSum v 1 → atomicMassL1 v w < delta →
      0 < normalVariance (atomicMeasure v) -
        (32 * ell / q) * (parabolaCovariance (atomicMeasure v)).det ∧
      |correctedInverseScale ell q (atomicMeasure v) -
        correctedInverseScale ell q (atomicMeasure w)| < eta := by
  let a : Matrix (Fin 2) (Fin 2) ℝ × ℝ :=
    (parabolaCovariance (atomicMeasure w), normalVariance (atomicMeasure w))
  let R (t : Matrix (Fin 2) (Fin 2) ℝ × ℝ) : ℝ := t.2 - |32 * ell / q| * t.1.det
  have hcoeff : 0 < 32 * ell / q := div_pos (mul_pos (by norm_num) hell) hq
  have hRa : 0 < R a := by simpa [R, a, abs_of_pos hcoeff] using hR
  have hRc : Continuous R := by
    dsimp [R]
    simp_rw [Matrix.det_fin_two]
    fun_prop
  have hInv : ContinuousAt (fun t => (ell * Real.sqrt (R t))⁻¹) a :=
    (continuousAt_const.mul (Real.continuous_sqrt.continuousAt.comp
      hRc.continuousAt)).inv₀
      (mul_ne_zero hell.ne' (Real.sqrt_ne_zero'.mpr hRa))
  have hG := hRc.continuousAt.prodMk hInv
  obtain ⟨d, hd, hnear⟩ := Metric.continuousAt_iff.mp hG
    (min (R a) eta) (lt_min hRa heta)
  obtain ⟨delta, hdelta, hrad⟩ := exists_atomic_covariance_radius w hw hsw d hd
  refine ⟨delta, hdelta, ?_⟩
  intro v hv hsv hL
  obtain ⟨hcv, hS⟩ := hrad v hv hsv hL
  let b : Matrix (Fin 2) (Fin 2) ℝ × ℝ :=
    (parabolaCovariance (atomicMeasure v), normalVariance (atomicMeasure v))
  have hdist : dist b a < d := by
    rw [dist_eq_norm]
    change max ‖parabolaCovariance (atomicMeasure v) - parabolaCovariance (atomicMeasure w)‖
      |normalVariance (atomicMeasure v) - normalVariance (atomicMeasure w)| < d
    exact max_lt_iff.mpr ⟨hcv, hS⟩
  have h := hnear hdist
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at h
  have hdiff : |R b - R a| < R a := (max_lt_iff.mp h).1.trans_le (min_le_left _ _)
  have hbR : 0 < R b := by have hh := (abs_lt.mp hdiff).1; linarith
  refine ⟨?_, ?_⟩
  · simpa [R, b, abs_of_pos hcoeff] using hbR
  · have hh := (max_lt_iff.mp h).2.trans_le (min_le_right _ _)
    simpa [correctedInverseScale, R, a, b, abs_of_pos hcoeff] using hh

private theorem finiteMass_eq_of_prefix (ell : ℝ) (p : Fin 4 → ℝ)
    (s r : ℕ → ℝ) (J : ℕ) (hpref : ∀ j : Fin J, s j.val = r j.val) :
    finiteMass ell p s J = finiteMass ell p r J := by
  have hm : addedMoment ell (fun j : Fin J => addedAtom j.val) (fun j => s j.val) =
      addedMoment ell (fun j : Fin J => addedAtom j.val) (fun j => r j.val) := by
    funext k
    unfold addedMoment
    exact Finset.sum_congr rfl (fun j _ => by dsimp only; rw [hpref j])
  have hb : finiteBase ell p s J = finiteBase ell p r J := by
    unfold finiteBase compensatedBase
    rw [hm]
  funext i
  cases i with
  | inl i => change finiteBase ell p s J i = finiteBase ell p r J i; rw [hb]
  | inr j =>
    change (if j < J then s j else 0) = if j < J then r j else 0
    by_cases hj : j < J
    · simp [hj, hpref ⟨j, hj⟩]
    · simp [hj]

theorem exists_corrected_scale_future_tail_cap (ell : ℝ) (hell : 0 < ell) (q : ℝ)
    (hq : 0 < q) (p : Fin 4 → ℝ) (r : ℕ → ℝ) (hr : ∀ j, 0 ≤ r j) (J : ℕ)
    (hM : (constraintMatrix ell).det ≠ 0)
    (hc : (constraintMatrix ell) *ᵥ p = constraintTarget q)
    (hj : ∀ i, 0 ≤ finiteBase ell p r J i)
    (hR : 0 < normalVariance (atomicMeasure (finiteMass ell p r J)) -
      (32 * ell / q) * (parabolaCovariance (atomicMeasure (finiteMass ell p r J))).det)
    (eta : ℝ) (heta : 0 < eta) :
  ∃ cap : ℝ, 0 < cap ∧ ∀ (s : ℕ → ℝ),
    (∀ j, 0 ≤ s j) → Summable s → (∀ j : Fin J, s j.val = r j.val) →
    (∀ i, 0 ≤ limitingBase ell p s i) → (∑' j, s (J + j)) < cap →
      0 < normalVariance (atomicMeasure (limitingMass ell p s)) -
        (32 * ell / q) * (parabolaCovariance (atomicMeasure (limitingMass ell p s))).det ∧
      |correctedInverseScale ell q (atomicMeasure (limitingMass ell p s)) -
        correctedInverseScale ell q (atomicMeasure (finiteMass ell p r J))| < eta := by
  have hwj := finiteMass_nonneg ell p r J hj hr
  have hmj : HasSum (finiteMass ell p r J) 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using
      finiteMass_constraints ell q p r J hM hc 0
  obtain ⟨delta, hdelta, hrad⟩ := exists_atomic_corrected_scale_radius ell hell q hq
    (finiteMass ell p r J) hwj hmj hR eta heta
  have hC := compensationTailConstant_pos ell
  refine ⟨delta / compensationTailConstant ell, div_pos hdelta hC, ?_⟩
  intro s hsn hss hpref hls htail
  have hwl : ∀ i, 0 ≤ limitingMass ell p s i := by
    intro i
    cases i with
    | inl i => exact hls i
    | inr j => exact hsn j
  have hml : HasSum (limitingMass ell p s) 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using
      limitingMoment_hasSum ell q hell.le p s hM hc hsn hss 0
  apply hrad (limitingMass ell p s) hwl hml
  have hle := atomicMassL1_limiting_finite_le ell hell.le p s hsn hss J
  rw [finiteMass_eq_of_prefix ell p s r J hpref] at hle
  exact hle.trans_lt (by nlinarith [(lt_div_iff₀ hC).mp htail])

end
end Shao.OQ3
