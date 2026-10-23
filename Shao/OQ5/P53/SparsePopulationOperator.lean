import Shao.OQ5.P53.SparsePopulationKernel
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The actual positive canonical residual operator on the full p53 L² space

The feature belongs to the same fixed population as the canonical residual.
Actual product integrability precedes identification of the integral operator;
the identity of quotient representatives holds almost everywhere for each f.
No finite-dimensional ambient assumption or fourth moment is used.
-/

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace Shao.OQ5.P53

theorem memLp_sparsePopulationZ :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (_hα : 0 < α),
  MemLp (sparsePopulationZ α x N) 2 (sparsePopulationMeasure α x N) := by
  intro α x N hα
  apply (memLp_two_iff_integrable_sq
    (measurable_sparsePopulationZ α x N).aestronglyMeasurable).mpr
  simpa only [Real.rpow_two, sq_abs] using
    integrable_sparsePopulationZ_rpow α x N hα 2 (by norm_num)

def sparsePopulationFeatureL2 (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α) :
    Lp ℝ 2 (sparsePopulationMeasure α x N) :=
  (memLp_sparsePopulationZ α x N hα).toLp (sparsePopulationZ α x N)

def sparsePopulationResidualOperator (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α) :
    (Lp ℝ 2 (sparsePopulationMeasure α x N)) →L[ℝ] (Lp ℝ 2 (sparsePopulationMeasure α x N)) :=
  InnerProductSpace.rankOne ℝ (sparsePopulationFeatureL2 α x N hα) (sparsePopulationFeatureL2 α x N hα)

theorem sparsePopulationFeatureL2_coe :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α),
  (sparsePopulationFeatureL2 α x N hα : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) → ℝ) =ᵐ[(sparsePopulationMeasure α x N)] sparsePopulationZ α x N := by
  intro α x N hα
  exact (memLp_sparsePopulationZ α x N hα).coeFn_toLp

theorem integrable_sparsePopulationZ_mul_Lp :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (_hα : 0 < α), ∀ f : Lp ℝ 2 (sparsePopulationMeasure α x N),
  Integrable (fun u => sparsePopulationZ α x N u * f u) (sparsePopulationMeasure α x N) := by
  intro α x N hα f
  refine (MeasureTheory.L2.integrable_inner (𝕜 := ℝ)
    (sparsePopulationFeatureL2 α x N hα) f).congr ?_
  filter_upwards [sparsePopulationFeatureL2_coe α x N hα] with u hu
  simp [hu, mul_comm]

theorem inner_sparsePopulationFeatureL2 :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), ∀ f : Lp ℝ 2 (sparsePopulationMeasure α x N),
  inner ℝ (sparsePopulationFeatureL2 α x N hα) f = ∫ u, sparsePopulationZ α x N u * f u ∂(sparsePopulationMeasure α x N) := by
  intro α x N hα f
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sparsePopulationFeatureL2_coe α x N hα] with u hu
  simp [hu, mul_comm]

theorem inner_sparsePopulationFeatureL2_self :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α),
  inner ℝ (sparsePopulationFeatureL2 α x N hα) (sparsePopulationFeatureL2 α x N hα) = ∫ u, (sparsePopulationZ α x N u) ^ 2 ∂(sparsePopulationMeasure α x N) := by
  intro α x N hα
  rw [inner_sparsePopulationFeatureL2]
  apply integral_congr_ae
  filter_upwards [sparsePopulationFeatureL2_coe α x N hα] with u hu
  rw [hu, pow_two]

theorem sparsePopulationFeatureL2_ne_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), SparseSelectionCore α x N →
  sparsePopulationFeatureL2 α x N hα ≠ 0 := by
  intro α x N hα hN hz
  have hsecond : (∫ u, (sparsePopulationZ α x N u) ^ 2
      ∂(sparsePopulationMeasure α x N)) = 0 := by
    simpa only [hz, inner_zero_left] using
      (inner_sparsePopulationFeatureL2_self α x N hα).symm
  exact (ne_of_gt (integral_sparsePopulationZ_sq_pos α x N hα hN)) hsecond

theorem integrable_sparsePopulationResidual_mul_Lp_right :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (_hα : 0 < α), ∀ (f : Lp ℝ 2 (sparsePopulationMeasure α x N)) (u : ((ℝ × (ℕ × Bool)) × (ℕ × Bool))),
  Integrable (fun v => sparsePopulationResidual α x N u v * f v) (sparsePopulationMeasure α x N) := by
  intro α x N hα f u
  simpa only [sparsePopulationResidual, mul_assoc] using
    (integrable_sparsePopulationZ_mul_Lp α x N hα f).const_mul
      (sparsePopulationZ α x N u)

theorem sparsePopulationResidualOperator_apply_ae :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), ∀ f : Lp ℝ 2 (sparsePopulationMeasure α x N),
  (sparsePopulationResidualOperator α x N hα f : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) → ℝ) =ᵐ[(sparsePopulationMeasure α x N)]
    (fun u => ∫ v, sparsePopulationResidual α x N u v * f v ∂(sparsePopulationMeasure α x N)) := by
  intro α x N hα f
  simp only [sparsePopulationResidualOperator, InnerProductSpace.rankOne_apply]
  filter_upwards [Lp.coeFn_smul
    (inner ℝ (sparsePopulationFeatureL2 α x N hα) f)
    (sparsePopulationFeatureL2 α x N hα),
    sparsePopulationFeatureL2_coe α x N hα] with u hs hz
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hs, hz, inner_sparsePopulationFeatureL2]
  simp only [sparsePopulationResidual, mul_assoc, integral_const_mul]
  ring

theorem memLp_sparsePopulationResidualIntegral :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (_hα : 0 < α), ∀ f : Lp ℝ 2 (sparsePopulationMeasure α x N),
  MemLp (fun u => ∫ v, sparsePopulationResidual α x N u v * f v ∂(sparsePopulationMeasure α x N)) 2 (sparsePopulationMeasure α x N) := by
  intro α x N hα f
  exact (memLp_congr_ae (sparsePopulationResidualOperator_apply_ae α x N hα f)).mp
    (Lp.memLp (sparsePopulationResidualOperator α x N hα f))

theorem sparsePopulationResidualOperator_isSelfAdjoint :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α),
  IsSelfAdjoint (sparsePopulationResidualOperator α x N hα) := by
  intro α x N hα
  apply ContinuousLinearMap.isSelfAdjoint_iff'.mpr
  exact InnerProductSpace.adjoint_rankOne
    (sparsePopulationFeatureL2 α x N hα) (sparsePopulationFeatureL2 α x N hα)

theorem sparsePopulationResidualOperator_quadratic :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), ∀ f : Lp ℝ 2 (sparsePopulationMeasure α x N),
  inner ℝ f (sparsePopulationResidualOperator α x N hα f) = (inner ℝ (sparsePopulationFeatureL2 α x N hα) f) ^ 2 := by
  intro α x N hα f
  rw [sparsePopulationResidualOperator, InnerProductSpace.inner_right_rankOne_apply,
    real_inner_comm f (sparsePopulationFeatureL2 α x N hα), pow_two]

theorem sparsePopulationResidualOperator_positive :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), ∀ f : Lp ℝ 2 (sparsePopulationMeasure α x N),
  0 ≤ inner ℝ f (sparsePopulationResidualOperator α x N hα f) := by
  intro α x N hα f
  rw [sparsePopulationResidualOperator_quadratic]
  exact sq_nonneg _

theorem sparsePopulationResidualOperator_rank :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), SparseSelectionCore α x N →
  (sparsePopulationResidualOperator α x N hα).toLinearMap.rank = 1 := by
  intro α x N hα hN
  exact InnerProductSpace.rank_rankOne
    (sparsePopulationFeatureL2_ne_zero α x N hα hN)
    (sparsePopulationFeatureL2_ne_zero α x N hα hN)

theorem sparsePopulationResidualOperator_ne_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), SparseSelectionCore α x N →
  sparsePopulationResidualOperator α x N hα ≠ 0 := by
  intro α x N hα hN
  exact InnerProductSpace.rankOne_ne_zero
    (sparsePopulationFeatureL2_ne_zero α x N hα hN)
    (sparsePopulationFeatureL2_ne_zero α x N hα hN)

end Shao.OQ5.P53
