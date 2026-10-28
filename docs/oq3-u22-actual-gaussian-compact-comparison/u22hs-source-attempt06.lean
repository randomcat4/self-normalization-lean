import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.Ring

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem standardized_plane_affine_jacobian
    (n : ℕ) (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) :
    |(Real.sqrt (n : ℝ) • (E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))).toLinearMap.det| =
      (n : ℝ) * |(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)).toLinearMap.det| := by
  have hdim : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  change |LinearMap.det (Real.sqrt (n : ℝ) •
    (E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)).toLinearMap)| = _
  rw [LinearMap.det_smul, hdim, Real.sq_sqrt (Nat.cast_nonneg n),
    abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]

theorem standardized_exponential_gaussian_cell_pullback
    (n : ℕ) (hn : 1 ≤ n) (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (y theta : ℝ × ℝ) (A : Set (ℝ × ℝ)) (hA : MeasurableSet A) :
    let F : (ℝ × ℝ) → (ℝ × ℝ) := fun w => Real.sqrt (n : ℝ) • E (w - y)
    let phi : (ℝ × ℝ) → ℝ := fun z =>
      (1 / (2 * Real.pi)) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2)
    let g : (ℝ × ℝ) → ℝ := fun z => Real.exp (-Real.sqrt (n : ℝ) *
      (theta.1 * (E.symm z).1 + theta.2 * (E.symm z).2))
    MeasurableSet (F '' A) ∧
      (∫ z : ℝ × ℝ, ((F '' A).indicator g) z * phi z) =
        ((n : ℝ) * |(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)).toLinearMap.det| /
          (2 * Real.pi)) *
          ∫ w : ℝ × ℝ in A, Real.exp (-(n : ℝ) *
            (theta.1 * (w - y).1 + theta.2 * (w - y).2) -
            ((n : ℝ) / 2) * ((E (w - y)).1 ^ 2 + (E (w - y)).2 ^ 2)) := by
  intro F phi g
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) hn)
  let s : ℝ := Real.sqrt (n : ℝ)
  have hs : 0 < s := Real.sqrt_pos.mpr hnpos
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  let d : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := s • (E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
  let H : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
    { toFun := F
      invFun := fun z => E.symm (s⁻¹ • z) + y
      left_inv := by intro w; simp [F, s, smul_smul, hs.ne']
      right_inv := by intro z; simp [F, s, smul_smul, hs.ne']
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hImage : MeasurableSet (F '' A) :=
    H.isClosedEmbedding.measurableEmbedding.measurableSet_image' hA
  refine ⟨hImage, ?_⟩
  have hDeriv (w : ℝ × ℝ) : HasFDerivAt F d w := by
    simpa [F, d, s, Function.comp_def, Pi.smul_apply] using
      (((E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)).hasFDerivAt.comp w
        ((hasFDerivAt_id w).sub_const y)).const_smul s)
  have hIndicator : (fun z : ℝ × ℝ => ((F '' A).indicator g) z * phi z) =
      (F '' A).indicator (fun z => g z * phi z) := by
    funext z
    by_cases hz : z ∈ F '' A <;> simp [hz]
  rw [hIndicator, integral_indicator hImage]
  letI : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    change ((volume : Measure ℝ).prod (volume : Measure ℝ)).IsAddHaarMeasure
    infer_instance
  have hJac := integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure (ℝ × ℝ)) hA
    (fun w _ => (hDeriv w).hasFDerivWithinAt) H.injective.injOn
      (fun z : ℝ × ℝ => g z * phi z)
  have hDet : |d.toLinearMap.det| =
      (n : ℝ) * |(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)).toLinearMap.det| :=
    standardized_plane_affine_jacobian n E
  have hInv (w : ℝ × ℝ) : E.symm (F w) = s • (w - y) := by
    dsimp only [F]
    rw [map_smul, E.symm_apply_apply]
  have hExponent (w : ℝ × ℝ) :
      (-s * (theta.1 * (E.symm (F w)).1 + theta.2 * (E.symm (F w)).2)) +
        (-( (F w).1 ^ 2 + (F w).2 ^ 2) / 2) =
      -(n : ℝ) * (theta.1 * (w - y).1 + theta.2 * (w - y).2) -
        ((n : ℝ) / 2) * ((E (w - y)).1 ^ 2 + (E (w - y)).2 ^ 2) := by
    rw [hInv]
    change (-s * (theta.1 * (s * (w - y).1) + theta.2 * (s * (w - y).2))) +
      (-((s * (E (w - y)).1) ^ 2 + (s * (E (w - y)).2) ^ 2) / 2) = _
    calc
      _ = -(s ^ 2) * (theta.1 * (w - y).1 + theta.2 * (w - y).2) -
        (s ^ 2 / 2) * ((E (w - y)).1 ^ 2 + (E (w - y)).2 ^ 2) := by ring
      _ = _ := by rw [hs2]
  have hPoint (w : ℝ × ℝ) :
      |d.toLinearMap.det| • (g (F w) * phi (F w)) =
        ((n : ℝ) * |(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)).toLinearMap.det| /
          (2 * Real.pi)) *
        Real.exp (-(n : ℝ) * (theta.1 * (w - y).1 + theta.2 * (w - y).2) -
          ((n : ℝ) / 2) * ((E (w - y)).1 ^ 2 + (E (w - y)).2 ^ 2)) := by
    calc
      _ = (|d.toLinearMap.det| / (2 * Real.pi)) *
        Real.exp ((-s * (theta.1 * (E.symm (F w)).1 + theta.2 * (E.symm (F w)).2)) +
          (-( (F w).1 ^ 2 + (F w).2 ^ 2) / 2)) := by
        dsimp only [g, phi, s]
        rw [Real.exp_add]
        simp only [smul_eq_mul]
        ring
      _ = _ := by rw [hExponent, hDet]
  calc
    (∫ z in F '' A, g z * phi z) = ∫ w in A, |d.toLinearMap.det| • (g (F w) * phi (F w)) := hJac
    _ = ∫ w in A, ((n : ℝ) * |(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)).toLinearMap.det| /
        (2 * Real.pi)) *
      Real.exp (-(n : ℝ) * (theta.1 * (w - y).1 + theta.2 * (w - y).2) -
        ((n : ℝ) / 2) * ((E (w - y)).1 ^ 2 + (E (w - y)).2 ^ 2)) :=
      integral_congr_ae (Filter.Eventually.of_forall hPoint)
    _ = _ := integral_const_mul _ _

end
end Shao.OQ3
