import Shao.OQ5.P52.FixedLayerCostBudget

open MeasureTheory
open scoped BigOperators

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

private theorem finitePowerExp_eq_product (J : Finset ℕ) (η «λ» : ℝ)
    (z : LayerObs × LayerObs) :
    Real.exp («λ» * ∑ j ∈ J, |fixedLayerTerm j z| ^ η) =
      ∏ j ∈ J, Real.exp («λ» * |fixedLayerTerm j z| ^ η) := by
  rw [Finset.mul_sum, Real.exp_sum]

theorem integrable_fixedLayerFinitePowerExp (J : Finset ℕ) (η «λ» : ℝ) :
    Integrable (fun z : LayerObs × LayerObs =>
      Real.exp («λ» * ∑ j ∈ J, |fixedLayerTerm j z| ^ η))
      (fixedObservationLaw.prod fixedObservationLaw) := by
  have hI : Integrable (fun z : LayerObs × LayerObs =>
      ∏ j ∈ J, Real.exp («λ» * |fixedLayerTerm j z| ^ η))
      (fixedObservationLaw.prod fixedObservationLaw) :=
    Shao.OQ5.P50.integrable_layerObservation_pair_finiteProduct
      fixedLayerP fixedLayerQ (fun j => (fixedLayerP_bounds j).1.le)
      (fun j => (fixedLayerQ_bounds j).1.le)
      (fun j => (fixedLayerP_add_Q_lt_one j).le) J
      (fun j s => Real.exp («λ» * |Shao.OQ5.P50.layerKernel (fixedLayerN j)
        (fixedLayerT j) (fixedLayerP j) (fixedLayerQ j) s.1 s.2| ^ η))
  exact hI.congr (Filter.Eventually.of_forall (fun z =>
    (finitePowerExp_eq_product J η «λ» z).symm))

theorem integral_fixedLayerFinitePowerExp (J : Finset ℕ) (η «λ» : ℝ) :
    (∫ z : LayerObs × LayerObs,
      Real.exp («λ» * ∑ j ∈ J, |fixedLayerTerm j z| ^ η)
      ∂fixedObservationLaw.prod fixedObservationLaw) =
      ∏ j ∈ J, (1 + fixedLayerExcessCost j η «λ») := by
  calc
    _ = ∫ z : LayerObs × LayerObs,
        ∏ j ∈ J, Real.exp («λ» * |fixedLayerTerm j z| ^ η)
        ∂fixedObservationLaw.prod fixedObservationLaw :=
      integral_congr_ae (Filter.Eventually.of_forall
        (finitePowerExp_eq_product J η «λ»))
    _ = ∏ j ∈ J, ∫ s : Fin 3 × Fin 3,
        Real.exp («λ» * |Shao.OQ5.P50.layerKernel (fixedLayerN j)
          (fixedLayerT j) (fixedLayerP j) (fixedLayerQ j) s.1 s.2| ^ η)
        ∂(Shao.OQ5.P50.layerMeasure (fixedLayerP j) (fixedLayerQ j)).prod
          (Shao.OQ5.P50.layerMeasure (fixedLayerP j) (fixedLayerQ j)) :=
      Shao.OQ5.P50.integral_layerObservation_pair_finiteProduct
        fixedLayerP fixedLayerQ (fun j => (fixedLayerP_bounds j).1.le)
        (fun j => (fixedLayerQ_bounds j).1.le)
        (fun j => (fixedLayerP_add_Q_lt_one j).le) J
        (fun j s => Real.exp («λ» * |Shao.OQ5.P50.layerKernel (fixedLayerN j)
          (fixedLayerT j) (fixedLayerP j) (fixedLayerQ j) s.1 s.2| ^ η))
    _ = _ := Finset.prod_congr rfl (fun j _ => integral_fixedLayerAtomExp j η «λ»)

theorem integral_fixedLayerFinitePowerExp_le (J : Finset ℕ) (η «λ» : ℝ)
    (hη0 : 0 < η) (hη : η < 1 / 5) («hλ» : 0 < «λ») :
    (∫ z : LayerObs × LayerObs,
      Real.exp («λ» * ∑ j ∈ J, |fixedLayerTerm j z| ^ η)
      ∂fixedObservationLaw.prod fixedObservationLaw) ≤
      Real.exp (∑' j : ℕ, fixedLayerExcessCost j η «λ») := by
  rw [integral_fixedLayerFinitePowerExp]
  calc
    _ ≤ Real.exp (∑ j ∈ J, fixedLayerExcessCost j η «λ») :=
      Real.prod_one_add_le_exp_sum J
        (fun j => fixedLayerExcessCost_nonneg j η «λ» «hλ».le)
    _ ≤ _ := Real.exp_le_exp.mpr
      ((summable_fixedLayerExcessCost η «λ» hη0 hη «hλ»).sum_le_tsum J
        (fun j _ => fixedLayerExcessCost_nonneg j η «λ» «hλ».le))

end
end Shao.OQ5.P52
