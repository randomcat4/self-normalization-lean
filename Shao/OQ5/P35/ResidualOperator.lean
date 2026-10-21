import Shao.OQ5.P35.KernelMoments
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# The actual canonical residual operator on the full p35 L² space

Source: `current/oq56/inputs02/p35.md`, §1 formula (1), and §3 after (8).
The operator acts on the actual quotient L²(realLaw). Its representative agrees
almost everywhere with integration against the fixed canonical residual.
No finite-dimensional ambient assumption or fourth feature moment is used.
-/

set_option autoImplicit false

namespace Shao.OQ5.P35

open MeasureTheory

noncomputable section

abbrev ObservationL2 := Lp ℝ 2 realLaw

theorem memLp_observationFeature : MemLp observationFeature 2 realLaw :=
  (memLp_two_iff_integrable_sq
    measurable_observationFeature.aestronglyMeasurable).mpr integrable_observationFeature_sq

/-- The centered feature as an element of the actual quotient L² space. -/
def featureL2 : ObservationL2 :=
  MemLp.toLp observationFeature memLp_observationFeature

/-- The canonical residual operator on every element of the full L² space. -/
def residualOperator : ObservationL2 →L[ℝ] ObservationL2 :=
  InnerProductSpace.rankOne ℝ (-featureL2) featureL2

theorem featureL2_coe : (featureL2 : ℝ → ℝ) =ᵐ[realLaw] observationFeature :=
  memLp_observationFeature.coeFn_toLp

theorem integrable_feature_mul_Lp (f : ObservationL2) :
    Integrable (fun y => observationFeature y * f y) realLaw := by
  refine (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) featureL2 f).congr ?_
  filter_upwards [featureL2_coe] with y hy
  simp [hy, mul_comm]

theorem inner_featureL2 (f : ObservationL2) :
    inner ℝ featureL2 f = ∫ y, observationFeature y * f y ∂realLaw := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [featureL2_coe] with y hy
  simp [hy, mul_comm]

theorem inner_featureL2_self : inner ℝ featureL2 featureL2 = featureVariance := by
  calc
    inner ℝ featureL2 featureL2 =
        ∫ y, observationFeature y * featureL2 y ∂realLaw := inner_featureL2 featureL2
    _ = ∫ y, observationFeature y ^ 2 ∂realLaw := by
      apply integral_congr_ae
      filter_upwards [featureL2_coe] with y hy
      rw [hy, pow_two]
    _ = featureVariance := integral_observationFeature_sq

theorem featureL2_ne_zero : featureL2 ≠ 0 := by
  intro hz
  have hv : featureVariance = 0 := by
    simpa only [hz, inner_zero_left] using inner_featureL2_self.symm
  exact (ne_of_gt featureVariance_pos) hv

theorem integrable_residual_mul_Lp_right (f : ObservationL2) (x : ℝ) :
    Integrable (fun y => populationResidual x y * f y) realLaw := by
  simpa only [populationResidual, mul_assoc] using
    (integrable_feature_mul_Lp f).const_mul (-observationFeature x)

private theorem integral_residual_mul_Lp_right (f : ObservationL2) (x : ℝ) :
    (∫ y, populationResidual x y * f y ∂realLaw) =
      -observationFeature x * ∫ y, observationFeature y * f y ∂realLaw := by
  simp only [populationResidual, mul_assoc]
  rw [integral_const_mul]

theorem residualOperator_apply_ae (f : ObservationL2) :
    (residualOperator f : ℝ → ℝ) =ᵐ[realLaw]
      (fun x => ∫ y, populationResidual x y * f y ∂realLaw) := by
  simp only [residualOperator, InnerProductSpace.rankOne_apply]
  filter_upwards [Lp.coeFn_smul (inner ℝ featureL2 f) (-featureL2),
    Lp.coeFn_neg featureL2, featureL2_coe] with x hs hn hz
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  simp only [Pi.neg_apply] at hn
  rw [hs, hn, hz, inner_featureL2, integral_residual_mul_Lp_right]
  ring

theorem memLp_residualIntegral (f : ObservationL2) :
    MemLp (fun x => ∫ y, populationResidual x y * f y ∂realLaw) 2 realLaw :=
  (memLp_congr_ae (residualOperator_apply_ae f)).mp (Lp.memLp (residualOperator f))

theorem residualOperator_feature :
    residualOperator featureL2 = (-featureVariance) • featureL2 := by
  simp only [residualOperator, InnerProductSpace.rankOne_apply,
    inner_featureL2_self, smul_neg, neg_smul]

theorem residualOperator_range : LinearMap.range residualOperator.toLinearMap =
    Submodule.span ℝ ({featureL2} : Set ObservationL2) := by
  have hinner : innerSL ℝ featureL2 ≠ 0 := by
    intro hzero
    have hv := congrArg (fun L : ObservationL2 →L[ℝ] ℝ => L featureL2) hzero
    simp only [innerSL_apply_apply, zero_apply,
      inner_featureL2_self] at hv
    exact (ne_of_gt featureVariance_pos) hv
  unfold residualOperator
  rw [InnerProductSpace.rankOne_def, ContinuousLinearMap.range_smulRight_apply hinner]
  simpa only [neg_one_smul] using
    (Submodule.span_singleton_smul_eq
      (show IsUnit (-1 : ℝ) from isUnit_iff_ne_zero.mpr (by norm_num)) featureL2)

theorem residualOperator_rank : residualOperator.toLinearMap.rank = 1 := by
  exact InnerProductSpace.rank_rankOne (neg_ne_zero.mpr featureL2_ne_zero) featureL2_ne_zero

theorem residualOperator_nonzero_eigenvalues :
    {lam : ℝ | lam ≠ 0 ∧ Module.End.HasEigenvalue residualOperator.toLinearMap lam} =
      {(-featureVariance)} := by
  ext lam
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hlam0, hlam⟩
    obtain ⟨f, hf⟩ := hlam.exists_hasEigenvector
    have hf0 : f ≠ 0 := (Module.End.hasEigenvector_iff.mp hf).2
    have heq : residualOperator f = lam • f := hf.apply_eq_smul
    have hc0 : inner ℝ featureL2 f ≠ 0 := by
      intro hc
      have hz : residualOperator f = 0 := by
        simp only [residualOperator, InnerProductSpace.rankOne_apply, hc, zero_smul]
      exact (smul_ne_zero hlam0 hf0) (heq.symm.trans hz)
    have hs := congrArg (fun v : ObservationL2 => inner ℝ featureL2 v) heq
    simp only [residualOperator, InnerProductSpace.rankOne_apply,
      inner_smul_right, inner_neg_right, inner_featureL2_self] at hs
    have hs' : (-featureVariance) * inner ℝ featureL2 f =
        lam * inner ℝ featureL2 f := by
      rw [mul_comm]
      exact hs
    exact (mul_right_cancel₀ hc0 hs').symm
  · intro hlam
    subst lam
    refine ⟨neg_ne_zero.mpr (ne_of_gt featureVariance_pos), ?_⟩
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := featureL2)
    exact ⟨Module.End.mem_eigenspace_iff.mpr residualOperator_feature, featureL2_ne_zero⟩

end
end Shao.OQ5.P35
