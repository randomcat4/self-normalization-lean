import Shao.OQ5.P53.SparseRealModel
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The positive canonical residual operator on the actual real p53 L² space

Source: current/oq56/inputs02/p53.md §3. The feature is the actual real Z
under the actual encoded real observation law. Honest product integrability
precedes the integral identity, which holds almost everywhere for each f.
The positive rank-one operator acts on the full real L² space, without a
fourth-moment or finite-dimensional ambient assumption.
-/

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace Shao.OQ5.P53

theorem memLp_sparseRealZ :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (_hα : 0 < α),
  MemLp (sparseRealZ α x N) 2 (sparseRealMeasure α x N) := by
  intro α x N hα
  apply (memLp_two_iff_integrable_sq
    (measurable_sparseRealZ α x N).aestronglyMeasurable).mpr
  simpa only [Real.rpow_two, sq_abs] using
    integrable_sparseRealZ_rpow α x N hα 2 (by norm_num)

def sparseRealFeatureL2 (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α) :
    Lp ℝ 2 (sparseRealMeasure α x N) :=
  (memLp_sparseRealZ α x N hα).toLp (sparseRealZ α x N)

def sparseRealResidualOperator (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α) :
    (Lp ℝ 2 (sparseRealMeasure α x N)) →L[ℝ] (Lp ℝ 2 (sparseRealMeasure α x N)) :=
  InnerProductSpace.rankOne ℝ (sparseRealFeatureL2 α x N hα) (sparseRealFeatureL2 α x N hα)

theorem sparseRealFeatureL2_coe :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α),
  (sparseRealFeatureL2 α x N hα : ℝ → ℝ) =ᵐ[(sparseRealMeasure α x N)] sparseRealZ α x N := by
  intro α x N hα
  exact (memLp_sparseRealZ α x N hα).coeFn_toLp

theorem integrable_sparseRealZ_mul_Lp :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (_hα : 0 < α), ∀ f : Lp ℝ 2 (sparseRealMeasure α x N),
  Integrable (fun u => sparseRealZ α x N u * f u) (sparseRealMeasure α x N) := by
  intro α x N hα f
  refine (MeasureTheory.L2.integrable_inner (𝕜 := ℝ)
    (sparseRealFeatureL2 α x N hα) f).congr ?_
  filter_upwards [sparseRealFeatureL2_coe α x N hα] with u hu
  simp [hu, mul_comm]

theorem inner_sparseRealFeatureL2 :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), ∀ f : Lp ℝ 2 (sparseRealMeasure α x N),
  inner ℝ (sparseRealFeatureL2 α x N hα) f = ∫ u, sparseRealZ α x N u * f u ∂(sparseRealMeasure α x N) := by
  intro α x N hα f
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sparseRealFeatureL2_coe α x N hα] with u hu
  simp [hu, mul_comm]

theorem inner_sparseRealFeatureL2_self :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α),
  inner ℝ (sparseRealFeatureL2 α x N hα) (sparseRealFeatureL2 α x N hα) = ∫ u, (sparseRealZ α x N u) ^ 2 ∂(sparseRealMeasure α x N) := by
  intro α x N hα
  rw [inner_sparseRealFeatureL2]
  apply integral_congr_ae
  filter_upwards [sparseRealFeatureL2_coe α x N hα] with u hu
  rw [hu, pow_two]

theorem sparseRealFeatureL2_ne_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), SparseSelectionCore α x N →
  sparseRealFeatureL2 α x N hα ≠ 0 := by
  intro α x N hα hN hz
  have hsecond : (∫ u, (sparseRealZ α x N u) ^ 2
      ∂(sparseRealMeasure α x N)) = 0 := by
    simpa only [hz, inner_zero_left] using
      (inner_sparseRealFeatureL2_self α x N hα).symm
  exact (ne_of_gt (integral_sparseRealZ_sq_pos α x N hα hN)) hsecond

theorem integrable_sparseRealResidual_mul_Lp_right :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (_hα : 0 < α), ∀ (f : Lp ℝ 2 (sparseRealMeasure α x N)) (u : ℝ),
  Integrable (fun v => sparseRealResidual α x N u v * f v) (sparseRealMeasure α x N) := by
  intro α x N hα f u
  simpa only [sparseRealResidual, mul_assoc] using
    (integrable_sparseRealZ_mul_Lp α x N hα f).const_mul
      (sparseRealZ α x N u)

theorem sparseRealResidualOperator_apply_ae :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), ∀ f : Lp ℝ 2 (sparseRealMeasure α x N),
  (sparseRealResidualOperator α x N hα f : ℝ → ℝ) =ᵐ[(sparseRealMeasure α x N)]
    (fun u => ∫ v, sparseRealResidual α x N u v * f v ∂(sparseRealMeasure α x N)) := by
  intro α x N hα f
  simp only [sparseRealResidualOperator, InnerProductSpace.rankOne_apply]
  filter_upwards [Lp.coeFn_smul
    (inner ℝ (sparseRealFeatureL2 α x N hα) f)
    (sparseRealFeatureL2 α x N hα),
    sparseRealFeatureL2_coe α x N hα] with u hs hz
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hs, hz, inner_sparseRealFeatureL2]
  simp only [sparseRealResidual, mul_assoc, integral_const_mul]
  ring

theorem memLp_sparseRealResidualIntegral :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (_hα : 0 < α), ∀ f : Lp ℝ 2 (sparseRealMeasure α x N),
  MemLp (fun u => ∫ v, sparseRealResidual α x N u v * f v ∂(sparseRealMeasure α x N)) 2 (sparseRealMeasure α x N) := by
  intro α x N hα f
  exact (memLp_congr_ae (sparseRealResidualOperator_apply_ae α x N hα f)).mp
    (Lp.memLp (sparseRealResidualOperator α x N hα f))

theorem sparseRealResidualOperator_isSelfAdjoint :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α),
  IsSelfAdjoint (sparseRealResidualOperator α x N hα) := by
  intro α x N hα
  apply ContinuousLinearMap.isSelfAdjoint_iff'.mpr
  exact InnerProductSpace.adjoint_rankOne
    (sparseRealFeatureL2 α x N hα) (sparseRealFeatureL2 α x N hα)

theorem sparseRealResidualOperator_quadratic :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), ∀ f : Lp ℝ 2 (sparseRealMeasure α x N),
  inner ℝ f (sparseRealResidualOperator α x N hα f) = (inner ℝ (sparseRealFeatureL2 α x N hα) f) ^ 2 := by
  intro α x N hα f
  rw [sparseRealResidualOperator, InnerProductSpace.inner_right_rankOne_apply,
    real_inner_comm f (sparseRealFeatureL2 α x N hα), pow_two]

theorem sparseRealResidualOperator_positive :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), ∀ f : Lp ℝ 2 (sparseRealMeasure α x N),
  0 ≤ inner ℝ f (sparseRealResidualOperator α x N hα f) := by
  intro α x N hα f
  rw [sparseRealResidualOperator_quadratic]
  exact sq_nonneg _

theorem sparseRealResidualOperator_rank :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), SparseSelectionCore α x N →
  (sparseRealResidualOperator α x N hα).toLinearMap.rank = 1 := by
  intro α x N hα hN
  exact InnerProductSpace.rank_rankOne
    (sparseRealFeatureL2_ne_zero α x N hα hN)
    (sparseRealFeatureL2_ne_zero α x N hα hN)

theorem sparseRealResidualOperator_ne_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), SparseSelectionCore α x N →
  sparseRealResidualOperator α x N hα ≠ 0 := by
  intro α x N hα hN
  exact InnerProductSpace.rankOne_ne_zero
    (sparseRealFeatureL2_ne_zero α x N hα hN)
    (sparseRealFeatureL2_ne_zero α x N hα hN)

end Shao.OQ5.P53
