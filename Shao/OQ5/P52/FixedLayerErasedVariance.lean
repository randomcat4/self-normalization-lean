import Shao.OQ5.P52.FixedLayerErasedCanonical
import Shao.OQ5.P52.FixedLayerVariance

/-!
# Exact second moment of the actual erased background

Honest finite-prefix cross moments converge under an L1 Holder dominator.
The actual paired erasure law and a.e. source-mask deletion then give the
background square integral by a licensed integrable square expansion.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

attribute [local instance] fixedObservationLaw_isProbabilityMeasure
attribute [local instance] fixedErasedLaw_isProbabilityMeasure

private theorem layer_mean_zero (j : ℕ) :
    (∫ z : LayerObs × LayerObs, fixedLayerTerm j z
      ∂fixedObservationLaw.prod fixedObservationLaw) = 0 := by
  have hi : Integrable (fixedLayerTerm j)
      (fixedObservationLaw.prod fixedObservationLaw) :=
    (fixedLayerTerm_memLp_two j).integrable (by norm_num)
  rw [integral_prod (fixedLayerTerm j) hi]
  simp only [integral_fixedLayerTerm_row_zero, integral_zero]

private theorem prefix_cross_moment (n j : ℕ) (hnj : j < n) :
    (∫ z : LayerObs × LayerObs,
      (∑ k ∈ Finset.range n, fixedLayerTerm k z) * fixedLayerTerm j z
        ∂fixedObservationLaw.prod fixedObservationLaw) =
      ∫ z : LayerObs × LayerObs, (fixedLayerTerm j z) ^ 2
        ∂fixedObservationLaw.prod fixedObservationLaw := by
  let M := fixedObservationLaw.prod fixedObservationLaw
  have hI (k : ℕ) : Integrable (fun z => fixedLayerTerm k z * fixedLayerTerm j z) M :=
    (fixedLayerTerm_memLp_two k).integrable_mul (fixedLayerTerm_memLp_two j)
  calc
    _ = ∫ z : LayerObs × LayerObs,
        ∑ k ∈ Finset.range n, fixedLayerTerm k z * fixedLayerTerm j z ∂M := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => Finset.sum_mul _ _ _)
    _ = ∑ k ∈ Finset.range n, ∫ z : LayerObs × LayerObs,
        fixedLayerTerm k z * fixedLayerTerm j z ∂M :=
      integral_finsetSum (Finset.range n) (fun k _ => hI k)
    _ = ∫ z : LayerObs × LayerObs, fixedLayerTerm j z * fixedLayerTerm j z ∂M := by
      apply Finset.sum_eq_single j
      · intro k _ hkj
        have hind := iIndepFun_fixedLayerTerms.indepFun hkj
        rw [hind.integral_fun_mul_eq_mul_integral
          (fixedLayerTerm_memLp_two k).aestronglyMeasurable
          (fixedLayerTerm_memLp_two j).aestronglyMeasurable,
          layer_mean_zero, layer_mean_zero]
        exact zero_mul _
      · intro hj
        exact False.elim (hj (Finset.mem_range.mpr hnj))
    _ = _ := by simp only [pow_two, M]

theorem integral_fixedResidualKernel_mul_fixedLayerTerm (j : ℕ) :
    (∫ z : LayerObs × LayerObs, fixedResidualKernel z * fixedLayerTerm j z
      ∂fixedObservationLaw.prod fixedObservationLaw) =
      ∫ z : LayerObs × LayerObs, (fixedLayerTerm j z) ^ 2
        ∂fixedObservationLaw.prod fixedObservationLaw := by
  let M := fixedObservationLaw.prod fixedObservationLaw
  let S : LayerObs × LayerObs → ℝ := fun z => ∑' k : ℕ, |fixedLayerTerm k z|
  let F : ℕ → LayerObs × LayerObs → ℝ := fun n z =>
    ∑ k ∈ Finset.range n, fixedLayerTerm k z
  have hS : MemLp S 2 M := by
    simpa only [ENNReal.ofReal_ofNat] using fixedLayerAbsSum_memLp 2 (by norm_num)
  have hr : MemLp fixedResidualKernel 2 M := by
    simpa only [ENNReal.ofReal_ofNat] using fixedResidualKernel_memLp 2 (by norm_num)
  have hk : MemLp (fixedLayerTerm j) 2 M := fixedLayerTerm_memLp_two j
  have _hcrossI : Integrable (fun z => fixedResidualKernel z * fixedLayerTerm j z) M :=
    hr.integrable_mul hk
  have hdom : Integrable (fun z => S z * |fixedLayerTerm j z|) M := by
    convert hS.integrable_mul hk.norm using 1
  have hF (n : ℕ) : Measurable (F n) :=
    (Finset.range n).measurable_sum (fun k _ => measurable_fixedLayerTerm k)
  have hbound (n : ℕ) : ∀ᵐ z ∂M,
      ‖F n z * fixedLayerTerm j z‖ ≤ S z * |fixedLayerTerm j z| := by
    filter_upwards [ae_mem_fixedAbsoluteConvergenceSet] with z hz
    change Summable (fun k : ℕ => |fixedLayerTerm k z|) at hz
    have hb : |F n z| ≤ S z := by
      calc
        _ = ‖F n z‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∑ k ∈ Finset.range n, ‖fixedLayerTerm k z‖ := norm_sum_le _ _
        _ = ∑ k ∈ Finset.range n, |fixedLayerTerm k z| := by
          simp only [Real.norm_eq_abs]
        _ ≤ _ := hz.sum_le_tsum (Finset.range n) (fun k _ => abs_nonneg _)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  have hlim : ∀ᵐ z ∂M, Tendsto (fun n : ℕ => F n z * fixedLayerTerm j z) atTop
      (nhds (fixedResidualKernel z * fixedLayerTerm j z)) := by
    filter_upwards [ae_mem_fixedAbsoluteConvergenceSet] with z hz
    have hsabs : Summable (fun k : ℕ => |fixedLayerTerm k z|) := by
      change Summable (fun k : ℕ => |fixedLayerTerm k z|) at hz
      exact hz
    have hs : Summable (fun k : ℕ => fixedLayerTerm k z) :=
      Summable.of_norm (by simpa only [Real.norm_eq_abs] using hsabs)
    rw [fixedResidualKernel_eq_tsum z hz]
    exact hs.tendsto_sum_tsum_nat.mul_const (fixedLayerTerm j z)
  have hc := tendsto_integral_of_dominated_convergence
    (fun z => S z * |fixedLayerTerm j z|)
    (fun n => ((hF n).mul (measurable_fixedLayerTerm j)).aestronglyMeasurable)
    hdom hbound hlim
  have he : ∀ᶠ n : ℕ in atTop,
      (∫ z : LayerObs × LayerObs, F n z * fixedLayerTerm j z ∂M) =
        ∫ z : LayerObs × LayerObs, (fixedLayerTerm j z) ^ 2 ∂M := by
    filter_upwards [eventually_ge_atTop (j + 1)] with n hn
    exact prefix_cross_moment n j (Nat.lt_of_succ_le hn)
  have hcst : Tendsto
      (fun n : ℕ => ∫ z : LayerObs × LayerObs, F n z * fixedLayerTerm j z ∂M)
      atTop (nhds (∫ z : LayerObs × LayerObs, (fixedLayerTerm j z) ^ 2 ∂M)) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [he] with n hn
      exact hn.symm)
  exact tendsto_nhds_unique hc hcst

theorem integral_fixedResidualKernel_sq_fixedErasedLaw_eq_sub (j : ℕ) :
    (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
      ∂(fixedErasedLaw j).prod (fixedErasedLaw j)) =
      (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
        ∂fixedObservationLaw.prod fixedObservationLaw) -
      ∫ z : LayerObs × LayerObs, (fixedLayerTerm j z) ^ 2
        ∂fixedObservationLaw.prod fixedObservationLaw := by
  let M := fixedObservationLaw.prod fixedObservationLaw
  let T : LayerObs × LayerObs → LayerObs × LayerObs := fun z =>
    (fixedEraseLayer j z.1, fixedEraseLayer j z.2)
  have hT : Measurable T :=
    ((measurable_fixedEraseLayer j).comp measurable_fst).prodMk
      ((measurable_fixedEraseLayer j).comp measurable_snd)
  have hr : MemLp fixedResidualKernel 2 M := by
    simpa only [ENNReal.ofReal_ofNat] using fixedResidualKernel_memLp 2 (by norm_num)
  have hk : MemLp (fixedLayerTerm j) 2 M := fixedLayerTerm_memLp_two j
  have hm : Integrable (fun z => fixedResidualKernel z * fixedLayerTerm j z) M :=
    hr.integrable_mul hk
  have hback : Integrable (fun z => (fixedResidualKernel z) ^ 2)
      ((fixedErasedLaw j).prod (fixedErasedLaw j)) :=
    (fixedResidualKernel_memLp_two_fixedErasedLaw j).integrable_sq
  have hmap : Integrable (fun z => (fixedResidualKernel z) ^ 2) (M.map T) := by
    rw [map_fixedEraseLayer_pair]
    exact hback
  have _hpull : Integrable (fun z => (fixedResidualKernel (T z)) ^ 2) M :=
    hmap.comp_measurable hT
  have _hdiff : Integrable (fun z => (fixedResidualKernel z - fixedLayerTerm j z) ^ 2) M :=
    (hr.sub hk).integrable_sq
  calc
    _ = ∫ z : LayerObs × LayerObs, (fixedResidualKernel (T z)) ^ 2 ∂M := by
      rw [← map_fixedEraseLayer_pair j]
      exact integral_map hT.aemeasurable hmap.aestronglyMeasurable
    _ = ∫ z : LayerObs × LayerObs,
        (fixedResidualKernel z - fixedLayerTerm j z) ^ 2 ∂M := by
      apply integral_congr_ae
      filter_upwards [fixedResidualKernel_erase_pair_ae_eq_sub j] with z hz
      change (fixedResidualKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2)) ^ 2 = _
      rw [hz]
    _ = (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2 ∂M) -
        2 * (∫ z : LayerObs × LayerObs, fixedResidualKernel z * fixedLayerTerm j z ∂M) +
        ∫ z : LayerObs × LayerObs, (fixedLayerTerm j z) ^ 2 ∂M := by
      have he : (fun z : LayerObs × LayerObs =>
          (fixedResidualKernel z - fixedLayerTerm j z) ^ 2) =
          (fun z => ((fixedResidualKernel z) ^ 2 -
            2 * (fixedResidualKernel z * fixedLayerTerm j z)) + (fixedLayerTerm j z) ^ 2) := by
        funext z
        ring
      have hsub : Integrable (fun z : LayerObs × LayerObs =>
          (fixedResidualKernel z) ^ 2 -
            2 * (fixedResidualKernel z * fixedLayerTerm j z)) M :=
        hr.integrable_sq.sub (hm.const_mul 2)
      rw [he, integral_add hsub hk.integrable_sq,
        integral_sub hr.integrable_sq (hm.const_mul 2), integral_const_mul]
    _ = _ := by
      rw [integral_fixedResidualKernel_mul_fixedLayerTerm]
      ring

theorem integral_fixedResidualKernel_sq_fixedErasedLaw_le (j : ℕ) :
    (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
      ∂(fixedErasedLaw j).prod (fixedErasedLaw j)) ≤
      ∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
        ∂fixedObservationLaw.prod fixedObservationLaw := by
  rw [integral_fixedResidualKernel_sq_fixedErasedLaw_eq_sub]
  exact sub_le_self _ (integral_nonneg (fun z => sq_nonneg (fixedLayerTerm j z)))

end
end Shao.OQ5.P52
