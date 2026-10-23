import Shao.OQ5.P53.SparseRealNormalization
import Shao.OQ5.P53.SparseRealOperator

/-!
# The normalized positive residual operator on the same actual real p53 L² space

Source: current/oq56/inputs02/p53.md §§1,3. The actual real measure is
unchanged. The feature is sqrt(c) Z and the canonical residual is c ZZ′.
The scalar c is nonnegative even in the totalized zero-variance case, so
their product identity does not require selection Core. Honest product
integrability precedes the per-f almost-everywhere integral identity.
Only nonzero and exact-rank-one conclusions use selection Core.
-/

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace Shao.OQ5.P53

private theorem normalization_scale_nonneg (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) :
    0 ≤ sparseRealNormalizationScale α x N := by
  exact inv_nonneg.mpr (Real.sqrt_nonneg _)

private theorem normalized_residual_eq_feature_mul
    (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (u v : ℝ) :
    sparseNormalizedRealResidual α x N u v =
      sparseNormalizedRealZ α x N u * sparseNormalizedRealZ α x N v := by
  dsimp only [sparseNormalizedRealResidual, sparseRealResidual, sparseNormalizedRealZ]
  calc
    _ = (Real.sqrt (sparseRealNormalizationScale α x N)) ^ 2 *
        (sparseRealZ α x N u * sparseRealZ α x N v) := by
      rw [Real.sq_sqrt (normalization_scale_nonneg α x N)]
    _ = _ := by ring

theorem memLp_sparseNormalizedRealZ :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (_hα : 0 < α),
  MemLp (sparseNormalizedRealZ α x N) 2 (sparseRealMeasure α x N) := by
  intro α x N hα
  exact (memLp_sparseRealZ α x N hα).const_mul
    (Real.sqrt (sparseRealNormalizationScale α x N))

def sparseNormalizedRealFeatureL2 (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α) :
    Lp ℝ 2 (sparseRealMeasure α x N) :=
  (memLp_sparseNormalizedRealZ α x N hα).toLp (sparseNormalizedRealZ α x N)

def sparseNormalizedRealResidualOperator (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α) :
    (Lp ℝ 2 (sparseRealMeasure α x N)) →L[ℝ] (Lp ℝ 2 (sparseRealMeasure α x N)) :=
  InnerProductSpace.rankOne ℝ (sparseNormalizedRealFeatureL2 α x N hα) (sparseNormalizedRealFeatureL2 α x N hα)

theorem sparseNormalizedRealFeatureL2_coe :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α),
  (sparseNormalizedRealFeatureL2 α x N hα : ℝ → ℝ) =ᵐ[(sparseRealMeasure α x N)] sparseNormalizedRealZ α x N := by
  intro α x N hα
  exact (memLp_sparseNormalizedRealZ α x N hα).coeFn_toLp

theorem integrable_sparseNormalizedRealZ_mul_Lp :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (_hα : 0 < α), ∀ f : Lp ℝ 2 (sparseRealMeasure α x N),
  Integrable (fun u => sparseNormalizedRealZ α x N u * f u) (sparseRealMeasure α x N) := by
  intro α x N hα f
  refine (MeasureTheory.L2.integrable_inner (𝕜 := ℝ)
    (sparseNormalizedRealFeatureL2 α x N hα) f).congr ?_
  filter_upwards [sparseNormalizedRealFeatureL2_coe α x N hα] with u hu
  simp [hu, mul_comm]

theorem inner_sparseNormalizedRealFeatureL2 :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), ∀ f : Lp ℝ 2 (sparseRealMeasure α x N),
  inner ℝ (sparseNormalizedRealFeatureL2 α x N hα) f = ∫ u, sparseNormalizedRealZ α x N u * f u ∂(sparseRealMeasure α x N) := by
  intro α x N hα f
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sparseNormalizedRealFeatureL2_coe α x N hα] with u hu
  simp [hu, mul_comm]

theorem inner_sparseNormalizedRealFeatureL2_self :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α),
  inner ℝ (sparseNormalizedRealFeatureL2 α x N hα) (sparseNormalizedRealFeatureL2 α x N hα) = ∫ u, (sparseNormalizedRealZ α x N u) ^ 2 ∂(sparseRealMeasure α x N) := by
  intro α x N hα
  rw [inner_sparseNormalizedRealFeatureL2]
  apply integral_congr_ae
  filter_upwards [sparseNormalizedRealFeatureL2_coe α x N hα] with u hu
  rw [hu, pow_two]

theorem sparseNormalizedRealFeatureL2_ne_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), SparseSelectionCore α x N →
  sparseNormalizedRealFeatureL2 α x N hα ≠ 0 := by
  intro α x N hα hN hz
  have hsecond : (∫ u, (sparseNormalizedRealZ α x N u) ^ 2
      ∂(sparseRealMeasure α x N)) = 0 := by
    simpa only [hz, inner_zero_left] using
      (inner_sparseNormalizedRealFeatureL2_self α x N hα).symm
  exact (ne_of_gt (integral_sparseNormalizedRealZ_sq_pos α x N hα hN)) hsecond

theorem integrable_sparseNormalizedRealResidual_mul_Lp_right :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (_hα : 0 < α), ∀ (f : Lp ℝ 2 (sparseRealMeasure α x N)) (u : ℝ),
  Integrable (fun v => sparseNormalizedRealResidual α x N u v * f v) (sparseRealMeasure α x N) := by
  intro α x N hα f u
  simpa only [normalized_residual_eq_feature_mul, mul_assoc] using
    (integrable_sparseNormalizedRealZ_mul_Lp α x N hα f).const_mul
      (sparseNormalizedRealZ α x N u)

theorem sparseNormalizedRealResidualOperator_apply_ae :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), ∀ f : Lp ℝ 2 (sparseRealMeasure α x N),
  (sparseNormalizedRealResidualOperator α x N hα f : ℝ → ℝ) =ᵐ[(sparseRealMeasure α x N)]
    (fun u => ∫ v, sparseNormalizedRealResidual α x N u v * f v ∂(sparseRealMeasure α x N)) := by
  intro α x N hα f
  simp only [sparseNormalizedRealResidualOperator, InnerProductSpace.rankOne_apply]
  filter_upwards [Lp.coeFn_smul
    (inner ℝ (sparseNormalizedRealFeatureL2 α x N hα) f)
    (sparseNormalizedRealFeatureL2 α x N hα),
    sparseNormalizedRealFeatureL2_coe α x N hα] with u hs hz
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hs, hz, inner_sparseNormalizedRealFeatureL2]
  simp only [normalized_residual_eq_feature_mul, mul_assoc, integral_const_mul]
  ring

theorem memLp_sparseNormalizedRealResidualIntegral :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (_hα : 0 < α), ∀ f : Lp ℝ 2 (sparseRealMeasure α x N),
  MemLp (fun u => ∫ v, sparseNormalizedRealResidual α x N u v * f v ∂(sparseRealMeasure α x N)) 2 (sparseRealMeasure α x N) := by
  intro α x N hα f
  exact (memLp_congr_ae (sparseNormalizedRealResidualOperator_apply_ae α x N hα f)).mp
    (Lp.memLp (sparseNormalizedRealResidualOperator α x N hα f))

theorem sparseNormalizedRealResidualOperator_isSelfAdjoint :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α),
  IsSelfAdjoint (sparseNormalizedRealResidualOperator α x N hα) := by
  intro α x N hα
  apply ContinuousLinearMap.isSelfAdjoint_iff'.mpr
  exact InnerProductSpace.adjoint_rankOne
    (sparseNormalizedRealFeatureL2 α x N hα) (sparseNormalizedRealFeatureL2 α x N hα)

theorem sparseNormalizedRealResidualOperator_quadratic :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), ∀ f : Lp ℝ 2 (sparseRealMeasure α x N),
  inner ℝ f (sparseNormalizedRealResidualOperator α x N hα f) = (inner ℝ (sparseNormalizedRealFeatureL2 α x N hα) f) ^ 2 := by
  intro α x N hα f
  rw [sparseNormalizedRealResidualOperator, InnerProductSpace.inner_right_rankOne_apply,
    real_inner_comm f (sparseNormalizedRealFeatureL2 α x N hα), pow_two]

theorem sparseNormalizedRealResidualOperator_positive :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), ∀ f : Lp ℝ 2 (sparseRealMeasure α x N),
  0 ≤ inner ℝ f (sparseNormalizedRealResidualOperator α x N hα f) := by
  intro α x N hα f
  rw [sparseNormalizedRealResidualOperator_quadratic]
  exact sq_nonneg _

theorem sparseNormalizedRealResidualOperator_rank :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), SparseSelectionCore α x N →
  (sparseNormalizedRealResidualOperator α x N hα).toLinearMap.rank = 1 := by
  intro α x N hα hN
  exact InnerProductSpace.rank_rankOne
    (sparseNormalizedRealFeatureL2_ne_zero α x N hα hN)
    (sparseNormalizedRealFeatureL2_ne_zero α x N hα hN)

theorem sparseNormalizedRealResidualOperator_ne_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), SparseSelectionCore α x N →
  sparseNormalizedRealResidualOperator α x N hα ≠ 0 := by
  intro α x N hα hN
  exact InnerProductSpace.rankOne_ne_zero
    (sparseNormalizedRealFeatureL2_ne_zero α x N hα hN)
    (sparseNormalizedRealFeatureL2_ne_zero α x N hα hN)

end Shao.OQ5.P53
