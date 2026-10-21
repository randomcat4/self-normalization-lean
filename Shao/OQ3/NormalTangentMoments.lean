import Shao.OQ3.NormalTangentGaussian

/-!
# Actual centered normal/tangent projection moments

Source: current/oq3/proofs/r1/report.md, lines 309-345, especially 335-343.
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U12c scope: 56af302fa669d878206ebed0b2d59830bf528a59c76317b5c7cc9a5c559370ce.
-/

namespace Shao.OQ3

open MeasureTheory
open scoped Matrix

noncomputable section

def centeredNormalProjection (q a v s x : ℝ) : ℝ :=
  v * (normalValue x - q) + s * (x - a)

theorem centeredNormalProjection_memLp_two (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a v s : ℝ) :
    MemLp (centeredNormalProjection q a v s) 2 mu := by
  have hcont : Continuous (centeredNormalProjection q a v s) := by
    unfold centeredNormalProjection normalValue
    fun_prop
  apply (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).mpr
  exact integrable_continuous_of_fixed_bounds mu hb _ (hcont.pow 2)

theorem centeredNormalProjection_integral_zero (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a : ℝ)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (v s : ℝ) :
    (∫ x : ℝ, centeredNormalProjection q a v s x ∂mu) = 0 := by
  have hY : Integrable normalValue mu :=
    integrable_continuous_of_fixed_bounds mu hb _ (by unfold normalValue; fun_prop)
  have hX : Integrable (fun x : ℝ => x) mu :=
    integrable_continuous_of_fixed_bounds mu hb _ continuous_id
  have hcy : Integrable (fun x : ℝ => normalValue x - q) mu :=
    hY.sub (integrable_const q)
  have hcx : Integrable (fun x : ℝ => x - a) mu :=
    hX.sub (integrable_const a)
  unfold centeredNormalProjection
  rw [integral_add (hcy.const_mul v) (hcx.const_mul s),
    integral_const_mul, integral_const_mul, integral_sub hY (integrable_const q),
    integral_sub hX (integrable_const a)]
  simp [hq, ha, measureReal_def]

theorem centeredNormalProjection_second_moment (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a : ℝ)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (v s : ℝ) :
    (∫ x : ℝ, (centeredNormalProjection q a v s x) ^ 2 ∂mu) =
      normalTangentQuadratic mu v s := by
  have hY2 : Integrable (fun x : ℝ => (normalValue x - q) ^ 2) mu :=
    integrable_continuous_of_fixed_bounds mu hb _ (by unfold normalValue; fun_prop)
  have hX2 : Integrable (fun x : ℝ => (x - a) ^ 2) mu :=
    integrable_continuous_of_fixed_bounds mu hb _ (by fun_prop)
  have hYX : Integrable (fun x : ℝ => (normalValue x - q) * (x - a)) mu :=
    integrable_continuous_of_fixed_bounds mu hb _ (by unfold normalValue; fun_prop)
  have hYm : AEMeasurable normalValue mu := by unfold normalValue; fun_prop
  have hVY : (∫ x : ℝ, (normalValue x - q) ^ 2 ∂mu) = normalVariance mu := by
    simpa only [normalVariance, hq] using (ProbabilityTheory.variance_eq_integral hYm).symm
  have hVX : (∫ x : ℝ, (x - a) ^ 2 ∂mu) =
      ProbabilityTheory.variance (fun x : ℝ => x) mu := by
    simpa only [ha] using (ProbabilityTheory.variance_eq_integral
      (X := fun x : ℝ => x) (μ := mu) (by fun_prop)).symm
  have hC : (∫ x : ℝ, (normalValue x - q) * (x - a) ∂mu) =
      ProbabilityTheory.covariance normalValue (fun x : ℝ => x) mu := by
    unfold ProbabilityTheory.covariance
    rw [hq, ha]
  have heq : (fun x : ℝ => (centeredNormalProjection q a v s x) ^ 2) =
      (fun x : ℝ => v ^ 2 * (normalValue x - q) ^ 2 +
        (2 * v * s) * ((normalValue x - q) * (x - a)) + s ^ 2 * (x - a) ^ 2) := by
    funext x
    unfold centeredNormalProjection
    ring
  have hab : Integrable (fun x : ℝ => v ^ 2 * (normalValue x - q) ^ 2 +
      (2 * v * s) * ((normalValue x - q) * (x - a))) mu :=
    (hY2.const_mul (v ^ 2)).add (hYX.const_mul (2 * v * s))
  rw [heq, integral_add hab
    (hX2.const_mul (s ^ 2)),
    integral_add (hY2.const_mul (v ^ 2)) (hYX.const_mul (2 * v * s))]
  simp_rw [integral_const_mul]
  rw [hVY, hVX, hC]
  unfold normalTangentQuadratic
  ring

theorem finite_atomic_normal_tangent_moments (ell q : ℝ) (p : Fin 4 → ℝ)
    (r : ℕ → ℝ) (J : ℕ) (hM : (constraintMatrix ell).det ≠ 0)
    (hc : (constraintMatrix ell) *ᵥ p = constraintTarget q)
    (hp : ∀ i, 0 ≤ finiteBase ell p r J i) (hr : ∀ j, 0 ≤ r j) :
    IsProbabilityMeasure (atomicMeasure (finiteMass ell p r J)) ∧
      (∫ x : ℝ, x ∂atomicMeasure (finiteMass ell p r J)) = q / 4 ∧
      (∫ x : ℝ, normalValue x ∂atomicMeasure (finiteMass ell p r J)) = q ∧
      ∀ v s : ℝ,
        MemLp (centeredNormalProjection q (q / 4) v s) 2
          (atomicMeasure (finiteMass ell p r J)) ∧
        (∫ x : ℝ, centeredNormalProjection q (q / 4) v s x
          ∂atomicMeasure (finiteMass ell p r J)) = 0 ∧
        (∫ x : ℝ, (centeredNormalProjection q (q / 4) v s x) ^ 2
          ∂atomicMeasure (finiteMass ell p r J)) =
            normalTangentQuadratic (atomicMeasure (finiteMass ell p r J)) v s := by
  let w := finiteMass ell p r J
  have hw : ∀ i, 0 ≤ w i := finiteMass_nonneg ell p r J hp hr
  have hm := finiteMass_constraints ell q p r J hM hc
  have hmass : HasSum w 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  let := atomicMeasure_isProbabilityMeasure w hw hmass
  have hX := atomicMeasure_mean ell q w hw hm
  have hX2 : Integrable (fun x : ℝ => x ^ 2) (atomicMeasure w) ∧
      (∫ x : ℝ, x ^ 2 ∂atomicMeasure w) = q := by
    simpa [constraintFeature, constraintTarget] using atomicMeasure_constraints ell q w hw hm 3
  have hY : (∫ x : ℝ, normalValue x ∂atomicMeasure w) = q := by
    unfold normalValue
    rw [integral_sub (hX.1.const_mul 8) hX2.1, integral_const_mul, hX.2, hX2.2]
    ring
  have hb : ∀ᵐ x ∂atomicMeasure w, |x| ≤ 4 + Real.sqrt 10 :=
    (atomicMeasure_ae_bounds w).mono fun _ hx => hx.2
  refine ⟨inferInstance, hX.2, hY, ?_⟩
  intro v s
  exact ⟨centeredNormalProjection_memLp_two _ hb _ _ v s,
    centeredNormalProjection_integral_zero _ hb _ _ hY hX.2 v s,
    centeredNormalProjection_second_moment _ hb _ _ hY hX.2 v s⟩

end
end Shao.OQ3
