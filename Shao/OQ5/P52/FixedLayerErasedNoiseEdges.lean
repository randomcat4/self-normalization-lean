import Shao.OQ5.P52.FixedLayerErasedEdgeMoments
import Shao.OQ5.P52.FixedLayerErasedNoise

/-!
# Actual erased sample noise and residual orthogonality

Honest scalar square integrability gives sample noise L2 by ordinary
coordinate pushforward. Canonical rows handle weighted edges at either
endpoint, and full grouped coordinate independence handles an outside index.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

attribute [local instance] fixedErasedLaw_isProbabilityMeasure

private theorem first_memLp_two (j : ℕ) :
    MemLp (fun o : LayerObs => o.1) 2 (fixedErasedLaw j) :=
  (memLp_two_iff_integrable_sq measurable_fst.aestronglyMeasurable).mpr
    (integrable_fixedErasedLaw_first_sq j)

private theorem coordinate_independence (j n : ℕ) :
    iIndepFun (fun i (x : Fin n → LayerObs) => x i)
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) :=
  iIndepFun_pi (μ := fun _ : Fin n => fixedErasedLaw j)
    (X := fun _ (o : LayerObs) => o) (fun _ => measurable_id.aemeasurable)

private theorem coordinate_map (j n : ℕ) (i : Fin n) :
    (Measure.pi (fun _ : Fin n => fixedErasedLaw j)).map
      (fun x : Fin n → LayerObs => x i) = fixedErasedLaw j :=
  (measurePreserving_eval (μ := fun _ : Fin n => fixedErasedLaw j) i).map_eq

private theorem coordinate_pair_mp (j n : ℕ) (a b : Fin n) (hab : a ≠ b) :
    MeasurePreserving (fun x : Fin n → LayerObs => (x a, x b))
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j))
      ((fixedErasedLaw j).prod (fixedErasedLaw j)) := by
  refine ⟨(measurable_pi_apply a).prodMk (measurable_pi_apply b), ?_⟩
  have hi := (coordinate_independence j n).indepFun hab
  simpa only [coordinate_map] using hi.map_prod_eq_prod_map_map
    (measurable_pi_apply a).aemeasurable (measurable_pi_apply b).aemeasurable

private theorem integral_coordinate_pullback (j n : ℕ) (i : Fin n)
    (f : LayerObs → ℝ) (hf : Integrable f (fixedErasedLaw j)) :
    (∫ x : Fin n → LayerObs, f (x i)
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) =
      ∫ o : LayerObs, f o ∂fixedErasedLaw j := by
  have hp := measurePreserving_eval (μ := fun _ : Fin n => fixedErasedLaw j) i
  have hfm : Integrable f ((Measure.pi (fun _ : Fin n => fixedErasedLaw j)).map
      (fun x : Fin n → LayerObs => x i)) := by
    rw [hp.map_eq]
    exact hf
  calc
    _ = ∫ o : LayerObs, f o
        ∂(Measure.pi (fun _ : Fin n => fixedErasedLaw j)).map
          (fun x : Fin n → LayerObs => x i) :=
      (integral_map hp.measurable.aemeasurable hfm.aestronglyMeasurable).symm
    _ = _ := by rw [hp.map_eq]

private theorem integral_pair_pullback (j n : ℕ) (a b : Fin n) (hab : a ≠ b)
    (f : LayerObs × LayerObs → ℝ)
    (hf : Integrable f ((fixedErasedLaw j).prod (fixedErasedLaw j))) :
    (∫ x : Fin n → LayerObs, f (x a, x b)
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) =
      ∫ z : LayerObs × LayerObs, f z ∂(fixedErasedLaw j).prod (fixedErasedLaw j) := by
  have hp := coordinate_pair_mp j n a b hab
  have hfm : Integrable f ((Measure.pi (fun _ : Fin n => fixedErasedLaw j)).map
      (fun x : Fin n → LayerObs => (x a, x b))) := by
    rw [hp.map_eq]
    exact hf
  calc
    _ = ∫ z : LayerObs × LayerObs, f z
        ∂(Measure.pi (fun _ : Fin n => fixedErasedLaw j)).map
          (fun x : Fin n → LayerObs => (x a, x b)) :=
      (integral_map hp.measurable.aemeasurable hfm.aestronglyMeasurable).symm
    _ = _ := by rw [hp.map_eq]

theorem fixedErasedSampleNoise_memLp_two (j n : ℕ) (i : Fin n) :
    MemLp (fun x : Fin n → LayerObs => (x i).1) 2
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) :=
  (first_memLp_two j).comp_measurePreserving
    (measurePreserving_eval (μ := fun _ : Fin n => fixedErasedLaw j) i)

theorem integral_fixedErasedSampleNoise_eq_zero (j n : ℕ) (i : Fin n) :
    (∫ x : Fin n → LayerObs, (x i).1
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) = 0 := by
  have _hnoise : Integrable (fun x : Fin n → LayerObs => (x i).1)
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) :=
    (fixedErasedSampleNoise_memLp_two j n i).integrable (by norm_num)
  rw [integral_coordinate_pullback j n i (fun o : LayerObs => o.1)
    (integrable_fixedErasedLaw_first j)]
  exact integral_fixedErasedLaw_first_eq_zero j

theorem integral_fixedErasedSampleNoise_mul (j n : ℕ) (i k : Fin n) :
    (∫ x : Fin n → LayerObs, (x i).1 * (x k).1
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) =
      if i = k then (1 / 3 : ℝ) else 0 := by
  have _hproduct : Integrable (fun x : Fin n → LayerObs => (x i).1 * (x k).1)
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) :=
    (fixedErasedSampleNoise_memLp_two j n i).integrable_mul
      (fixedErasedSampleNoise_memLp_two j n k)
  by_cases hik : i = k
  · subst k
    rw [ite_eq_left rfl]
    calc
      _ = ∫ x : Fin n → LayerObs, (x i).1 ^ 2
          ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => (pow_two ((x i).1)).symm
      _ = ∫ o : LayerObs, o.1 ^ 2 ∂fixedErasedLaw j :=
        integral_coordinate_pullback j n i (fun o : LayerObs => o.1 ^ 2)
          (integrable_fixedErasedLaw_first_sq j)
      _ = _ := integral_fixedErasedLaw_first_sq j
  · rw [ite_eq_right hik]
    have hi : IndepFun (fun x : Fin n → LayerObs => (x i).1)
        (fun x : Fin n → LayerObs => (x k).1)
        (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) :=
      ((coordinate_independence j n).indepFun hik).comp measurable_fst measurable_fst
    rw [hi.integral_fun_mul_eq_mul_integral
      (fixedErasedSampleNoise_memLp_two j n i).aestronglyMeasurable
      (fixedErasedSampleNoise_memLp_two j n k).aestronglyMeasurable,
      integral_fixedErasedSampleNoise_eq_zero j n i,
      integral_fixedErasedSampleNoise_eq_zero j n k]
    exact zero_mul _

theorem integrable_fixedErasedSampleNoise_mul_residualEdge
    (j n : ℕ) (i a b : Fin n) (hab : a ≠ b) :
    Integrable (fun x : Fin n → LayerObs =>
      (x i).1 * fixedResidualKernel (x a, x b))
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) :=
  (fixedErasedSampleNoise_memLp_two j n i).integrable_mul
    (fixedErasedResidualEdge_memLp_two j n a b hab)

private theorem integrable_weighted_pair (j : ℕ) :
    Integrable (fun z : LayerObs × LayerObs => z.1.1 * fixedResidualKernel z)
      ((fixedErasedLaw j).prod (fixedErasedLaw j)) := by
  have hG : MemLp (fun z : LayerObs × LayerObs => z.1.1) 2
      ((fixedErasedLaw j).prod (fixedErasedLaw j)) :=
    (first_memLp_two j).comp_measurePreserving
      (measurePreserving_fst (μ := fixedErasedLaw j) (ν := fixedErasedLaw j))
  exact hG.integrable_mul (fixedResidualKernel_memLp_two_fixedErasedLaw j)

private theorem integral_weighted_pair_eq_zero (j : ℕ) :
    (∫ z : LayerObs × LayerObs, z.1.1 * fixedResidualKernel z
      ∂(fixedErasedLaw j).prod (fixedErasedLaw j)) = 0 := by
  rw [integral_prod _ (integrable_weighted_pair j)]
  calc
    _ = ∫ _o : LayerObs, (0 : ℝ) ∂fixedErasedLaw j := by
      apply integral_congr_ae
      filter_upwards [integrable_fixedResidualKernel_row_fixedErasedLaw_ae j,
        integral_fixedResidualKernel_row_fixedErasedLaw_eq_zero_ae j] with o hrow hz
      have _hinner : Integrable (fun o' : LayerObs =>
          o.1 * fixedResidualKernel (o, o')) (fixedErasedLaw j) :=
        hrow.const_mul o.1
      change (∫ o' : LayerObs, o.1 * fixedResidualKernel (o, o') ∂fixedErasedLaw j) = 0
      rw [integral_const_mul, hz, mul_zero]
    _ = 0 := by simp only [integral_zero]

theorem integral_fixedErasedSampleNoise_mul_residualEdge
    (j n : ℕ) (i a b : Fin n) (hab : a ≠ b) :
    (∫ x : Fin n → LayerObs,
      (x i).1 * fixedResidualKernel (x a, x b)
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) = 0 := by
  have _hproduct := integrable_fixedErasedSampleNoise_mul_residualEdge j n i a b hab
  by_cases hia : i = a
  · subst i
    exact (integral_pair_pullback j n a b hab
      (fun z : LayerObs × LayerObs => z.1.1 * fixedResidualKernel z)
      (integrable_weighted_pair j)).trans (integral_weighted_pair_eq_zero j)
  · by_cases hib : i = b
    · subst i
      calc
        _ = ∫ x : Fin n → LayerObs,
            (x b).1 * fixedResidualKernel (x b, x a)
            ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j) := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by
            dsimp only
            rw [fixedResidualKernel_symmetric (x a) (x b)]
        _ = ∫ z : LayerObs × LayerObs, z.1.1 * fixedResidualKernel z
            ∂(fixedErasedLaw j).prod (fixedErasedLaw j) :=
          integral_pair_pullback j n b a hab.symm
            (fun z : LayerObs × LayerObs => z.1.1 * fixedResidualKernel z)
            (integrable_weighted_pair j)
        _ = 0 := integral_weighted_pair_eq_zero j
    · have hind := (coordinate_independence j n).indepFun_prodMk
        (fun k => measurable_pi_apply k) a b i (Ne.symm hia) (Ne.symm hib)
      have hi : IndepFun (fun x : Fin n → LayerObs => (x i).1)
          (fun x : Fin n → LayerObs => fixedResidualKernel (x a, x b))
          (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) :=
        hind.symm.comp measurable_fst measurable_fixedResidualKernel
      rw [hi.integral_fun_mul_eq_mul_integral
        (fixedErasedSampleNoise_memLp_two j n i).aestronglyMeasurable
        (fixedErasedResidualEdge_memLp_two j n a b hab).aestronglyMeasurable,
        integral_fixedErasedSampleNoise_eq_zero j n i]
      exact zero_mul _

end
end Shao.OQ5.P52
