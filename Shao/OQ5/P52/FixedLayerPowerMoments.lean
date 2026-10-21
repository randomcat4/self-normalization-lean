import Shao.OQ5.P52.FixedLayerFiniteMoments
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Order.LiminfLimsup

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

private theorem measurable_absPower (j : ℕ) (η : ℝ) :
    Measurable (fun z : LayerObs × LayerObs => |fixedLayerTerm j z| ^ η) :=
  by
    simpa only [Real.norm_eq_abs] using
      (measurable_fixedLayerTerm j).norm.pow_const η

private theorem absPower_le_excess (j : ℕ) (η : ℝ) (z : LayerObs × LayerObs) :
    |fixedLayerTerm j z| ^ η ≤ Real.exp (1 * |fixedLayerTerm j z| ^ η) - 1 := by
  simp only [one_mul]
  linarith [Real.add_one_le_exp (|fixedLayerTerm j z| ^ η)]

theorem integrable_fixedLayerAbsPower (j : ℕ) (η : ℝ) :
    Integrable (fun z : LayerObs × LayerObs => |fixedLayerTerm j z| ^ η)
      (fixedObservationLaw.prod fixedObservationLaw) := by
  exact (integrable_fixedLayerTermExcess j η 1).mono_nonneg
    (measurable_absPower j η).aestronglyMeasurable
    (Eventually.of_forall (fun z => Real.rpow_nonneg (abs_nonneg _) _))
    (Eventually.of_forall (absPower_le_excess j η))

theorem summable_integral_fixedLayerAbsPower (η : ℝ)
    (hη0 : 0 < η) (hη : η < 1 / 5) :
    Summable (fun j : ℕ =>
      ∫ z : LayerObs × LayerObs, |fixedLayerTerm j z| ^ η
        ∂fixedObservationLaw.prod fixedObservationLaw) := by
  refine Summable.of_nonneg_of_le
    (fun j => integral_nonneg (fun z => Real.rpow_nonneg (abs_nonneg _) _)) ?_
    (summable_fixedLayerExcessCost η 1 hη0 hη (by norm_num))
  intro j
  rw [fixedLayerExcessCost_eq_pair_integral]
  exact integral_mono (integrable_fixedLayerAbsPower j η)
    (integrable_fixedLayerTermExcess j η 1) (absPower_le_excess j η)

theorem ae_summable_fixedLayerAbsPower (η : ℝ)
    (hη0 : 0 < η) (hη : η < 1 / 5) :
    ∀ᵐ z : LayerObs × LayerObs ∂fixedObservationLaw.prod fixedObservationLaw,
      Summable (fun j : ℕ => |fixedLayerTerm j z| ^ η) := by
  have hn (j : ℕ) (z : LayerObs × LayerObs) :
      ‖|fixedLayerTerm j z| ^ η‖ = |fixedLayerTerm j z| ^ η :=
    Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
  have hs : Summable (fun j : ℕ =>
      ∫ z : LayerObs × LayerObs, ‖|fixedLayerTerm j z| ^ η‖
        ∂fixedObservationLaw.prod fixedObservationLaw) := by
    simpa only [hn] using summable_integral_fixedLayerAbsPower η hη0 hη
  have he (j : ℕ) :
      (∫⁻ z : LayerObs × LayerObs, ‖|fixedLayerTerm j z| ^ η‖ₑ
        ∂fixedObservationLaw.prod fixedObservationLaw) =
      ENNReal.ofReal (∫ z : LayerObs × LayerObs, ‖|fixedLayerTerm j z| ^ η‖
        ∂fixedObservationLaw.prod fixedObservationLaw) :=
    (ofReal_integral_norm_eq_lintegral_enorm (integrable_fixedLayerAbsPower j η)).symm
  have hb : (∑' j : ℕ,
      ∫⁻ z : LayerObs × LayerObs, ‖|fixedLayerTerm j z| ^ η‖ₑ
        ∂fixedObservationLaw.prod fixedObservationLaw) ≠ ∞ := by
    simpa only [he] using hs.tsum_ofReal_ne_top
  have hm (j : ℕ) : Measurable
      (fun z : LayerObs × LayerObs => ‖|fixedLayerTerm j z| ^ η‖ₑ) :=
    (measurable_absPower j η).enorm
  have hi : (∫⁻ z : LayerObs × LayerObs, ∑' j : ℕ, ‖|fixedLayerTerm j z| ^ η‖ₑ
      ∂fixedObservationLaw.prod fixedObservationLaw) ≠ ∞ := by
    rw [lintegral_tsum (fun j => (hm j).aemeasurable)]
    exact hb
  filter_upwards [ae_lt_top (Measurable.tsum hm) hi] with z hz
  have hz' := tsum_enorm_ne_top_iff_summable_norm.mp hz.ne
  simpa only [hn] using hz'

private theorem measurable_powerSumExp (η «λ» : ℝ) :
    Measurable (fun z : LayerObs × LayerObs =>
      Real.exp («λ» * ∑' j : ℕ, |fixedLayerTerm j z| ^ η)) :=
  (measurable_const.mul (Measurable.tsum (fun j => measurable_absPower j η))).exp

private theorem lintegral_powerSumExp_le (η «λ» : ℝ)
    (hη0 : 0 < η) (hη : η < 1 / 5) («hλ» : 0 < «λ») :
    (∫⁻ z : LayerObs × LayerObs,
      ENNReal.ofReal (Real.exp («λ» * ∑' j : ℕ, |fixedLayerTerm j z| ^ η))
      ∂fixedObservationLaw.prod fixedObservationLaw) ≤
      ENNReal.ofReal (Real.exp (∑' j : ℕ, fixedLayerExcessCost j η «λ»)) := by
  let M := fixedObservationLaw.prod fixedObservationLaw
  let F : ℕ → LayerObs × LayerObs → ℝ := fun n z =>
    Real.exp («λ» * ∑ j ∈ Finset.range n, |fixedLayerTerm j z| ^ η)
  let H : ℕ → LayerObs × LayerObs → ℝ≥0∞ := fun n z => ENNReal.ofReal (F n z)
  let C := Real.exp (∑' j : ℕ, fixedLayerExcessCost j η «λ»)
  have hm (n : ℕ) : Measurable (H n) :=
    ENNReal.measurable_ofReal.comp
      ((measurable_const.mul ((Finset.range n).measurable_sum
        (fun j _ => measurable_absPower j η))).exp)
  have hnn (n : ℕ) : 0 ≤ᵐ[M] F n :=
    Eventually.of_forall (fun z => (Real.exp_pos _).le)
  have hI (n : ℕ) : Integrable (F n) M :=
    integrable_fixedLayerFinitePowerExp (Finset.range n) η «λ»
  have hbound (n : ℕ) : (∫⁻ z, H n z ∂M) ≤ ENNReal.ofReal C := by
    change (∫⁻ z, ENNReal.ofReal (F n z) ∂M) ≤ ENNReal.ofReal C
    rw [← ofReal_integral_eq_lintegral_ofReal (hI n) (hnn n)]
    exact ENNReal.ofReal_le_ofReal
      (integral_fixedLayerFinitePowerExp_le (Finset.range n) η «λ» hη0 hη «hλ»)
  have hlim : ∀ᵐ z ∂M,
      liminf (fun n : ℕ => H n z) atTop =
        ENNReal.ofReal (Real.exp («λ» * ∑' j : ℕ, |fixedLayerTerm j z| ^ η)) := by
    filter_upwards [ae_summable_fixedLayerAbsPower η hη0 hη] with z hz
    have hp := hz.tendsto_sum_tsum_nat.const_mul «λ»
    have hE := Real.continuous_exp.continuousAt.tendsto.comp hp
    exact (ENNReal.tendsto_ofReal hE).liminf_eq
  have hlimbound : liminf (fun n : ℕ => ∫⁻ z, H n z ∂M) atTop ≤ ENNReal.ofReal C :=
    liminf_le_of_frequently_le' (Eventually.frequently (Eventually.of_forall hbound))
  calc
    _ = ∫⁻ z, liminf (fun n : ℕ => H n z) atTop ∂M := by
      apply lintegral_congr_ae
      filter_upwards [hlim] with z hz
      exact hz.symm
    _ ≤ liminf (fun n : ℕ => ∫⁻ z, H n z ∂M) atTop := lintegral_liminf_le hm
    _ ≤ _ := hlimbound

theorem integrable_fixedLayerPowerSumExp (η «λ» : ℝ)
    (hη0 : 0 < η) (hη : η < 1 / 5) («hλ» : 0 < «λ») :
    Integrable (fun z : LayerObs × LayerObs =>
      Real.exp («λ» * ∑' j : ℕ, |fixedLayerTerm j z| ^ η))
      (fixedObservationLaw.prod fixedObservationLaw) := by
  refine ⟨(measurable_powerSumExp η «λ»).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall (fun z => (Real.exp_pos _).le))).mpr
  exact lt_of_le_of_lt (lintegral_powerSumExp_le η «λ» hη0 hη «hλ»)
    ENNReal.ofReal_lt_top

theorem integral_fixedLayerPowerSumExp_le (η «λ» : ℝ)
    (hη0 : 0 < η) (hη : η < 1 / 5) («hλ» : 0 < «λ») :
    (∫ z : LayerObs × LayerObs,
      Real.exp («λ» * ∑' j : ℕ, |fixedLayerTerm j z| ^ η)
      ∂fixedObservationLaw.prod fixedObservationLaw) ≤
      Real.exp (∑' j : ℕ, fixedLayerExcessCost j η «λ») := by
  have hb := lintegral_powerSumExp_le η «λ» hη0 hη «hλ»
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_fixedLayerPowerSumExp η «λ» hη0 hη «hλ»)
    (Eventually.of_forall (fun z => (Real.exp_pos _).le))] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).mp hb

end
end Shao.OQ5.P52
