import Shao.Probability.SourceFutureNoiseFourier
import Shao.Probability.SourceGrowingMicrotimeTail
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Normed.Group.Bounded

/-! Actual scalar-noise endpoint cancellation for supplement.tex 895--907,922.
The future sum and full chord/scalar noise are unchanged. -/

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators ContDiff Topology

private theorem lm_test_measurable (y : ℝ) : Measurable (sourceFourierTest y) := by
  have hA : MeasurableSet {p : ℝ × ℝ | |p.1| < y * Real.sqrt p.2} :=
    (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet
  exact (sourceKernelCutoff_data.1.continuous.measurable.comp measurable_snd).mul
    (Measurable.ite hA measurable_const measurable_const)

private theorem lm_test_bounds (y : ℝ) (p : ℝ × ℝ) :
    0 ≤ sourceFourierTest y p ∧ sourceFourierTest y p ≤ 1 := by
  unfold sourceFourierTest
  split_ifs
  · simpa using sourceKernelCutoff_data.2.2.1 p.2
  · simp

private theorem lm_scalar_interval (gamma y w q : ℝ) (hg : 0 < gamma) (hy : 0 ≤ y) :
    (∫ t : ℝ, sourceFourierTest y (w + gamma * t, q) ∂sourceScalarLaw) =
      sourceKernelCutoff q *
        ((∫ t in (0 : ℝ)..((y * Real.sqrt q - w) / gamma), sourceScalarDensity t) -
          ∫ t in (0 : ℝ)..((-y * Real.sqrt q - w) / gamma), sourceScalarDensity t) := by
  let lo : ℝ := (-y * Real.sqrt q - w) / gamma
  let hi : ℝ := (y * Real.sqrt q - w) / gamma
  have hr := sourceScalarDensity_data.1.continuous
  have hR : 0 ≤ y * Real.sqrt q := mul_nonneg hy (Real.sqrt_nonneg q)
  have hle : lo ≤ hi := (div_le_div_iff_of_pos_right hg).2 (by linarith)
  have hmem (t : ℝ) : |w + gamma * t| < y * Real.sqrt q ↔ t ∈ Set.Ioo lo hi := by
    rw [abs_lt, Set.mem_Ioo]
    dsimp [lo, hi]
    rw [div_lt_iff₀ hg, lt_div_iff₀ hg]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith
  unfold sourceScalarLaw
  rw [integral_withDensity_eq_integral_toReal_smul
    (sourceScalarDensity_data.1.continuous.measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (sourceScalarDensity_data.2.2.1 _), smul_eq_mul]
  calc
    _ = ∫ t : ℝ, sourceKernelCutoff q * (Set.Ioo lo hi).indicator sourceScalarDensity t := by
      apply integral_congr_ae
      filter_upwards [] with t
      by_cases ht : t ∈ Set.Ioo lo hi
      · simp [sourceFourierTest, (hmem t).2 ht, Set.indicator_of_mem ht, mul_comm]
      · simp [sourceFourierTest, not_congr (hmem t), ht, Set.indicator_of_notMem ht]
    _ = sourceKernelCutoff q * ∫ t in Set.Ioo lo hi, sourceScalarDensity t := by
      rw [integral_const_mul, integral_indicator measurableSet_Ioo]
    _ = sourceKernelCutoff q * ∫ t in lo..hi, sourceScalarDensity t := by
      rw [intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo]
    _ = _ := by
      rw [← intervalIntegral.integral_interval_sub_left
        (hr.intervalIntegrable 0 hi) (hr.intervalIntegrable 0 lo)]

private theorem lm_scalar_hasDeriv (gamma y q w : ℝ) (hg : 0 < gamma) (hy : 0 ≤ y) :
    HasDerivAt
      (fun v : ℝ => ∫ t : ℝ, sourceFourierTest y (v + gamma * t, q) ∂sourceScalarLaw)
      (sourceKernelCutoff q / gamma *
        (sourceScalarDensity ((-y * Real.sqrt q - w) / gamma) -
          sourceScalarDensity ((y * Real.sqrt q - w) / gamma))) w := by
  have hr := sourceScalarDensity_data.1.continuous
  have hA (t : ℝ) : HasDerivAt
      (fun v : ℝ => ∫ z in (0 : ℝ)..v, sourceScalarDensity z) (sourceScalarDensity t) t :=
    intervalIntegral.integral_hasDerivAt_right (hr.intervalIntegrable 0 t)
      hr.stronglyMeasurable.stronglyMeasurableAtFilter hr.continuousAt
  have hlo := ((hasDerivAt_const w (-y * Real.sqrt q)).sub (hasDerivAt_id w)).div_const gamma
  have hhi := ((hasDerivAt_const w (y * Real.sqrt q)).sub (hasDerivAt_id w)).div_const gamma
  have hh := (((hA _).comp w hhi).sub ((hA _).comp w hlo)).const_mul (sourceKernelCutoff q)
  have he : (fun v : ℝ => ∫ t : ℝ,
      sourceFourierTest y (v + gamma * t, q) ∂sourceScalarLaw) =
      (fun v : ℝ => sourceKernelCutoff q *
        ((∫ t in (0 : ℝ)..((y * Real.sqrt q - v) / gamma), sourceScalarDensity t) -
          ∫ t in (0 : ℝ)..((-y * Real.sqrt q - v) / gamma), sourceScalarDensity t)) :=
    funext fun v => lm_scalar_interval gamma y v q hg hy
  rw [he]
  convert hh using 1 <;> dsimp only [Function.comp_def, Pi.sub_apply, id_eq] <;> ring

private theorem lm_scalar_first_hasDeriv (gamma y q w : ℝ) :
    HasDerivAt
      (fun v : ℝ => sourceKernelCutoff q / gamma *
        (sourceScalarDensity ((-y * Real.sqrt q - v) / gamma) -
          sourceScalarDensity ((y * Real.sqrt q - v) / gamma)))
      (sourceKernelCutoff q / gamma ^ 2 *
        (deriv sourceScalarDensity ((y * Real.sqrt q - w) / gamma) -
          deriv sourceScalarDensity ((-y * Real.sqrt q - w) / gamma))) w := by
  have hd : Differentiable ℝ sourceScalarDensity := sourceScalarDensity_data.1.differentiable (by simp)
  have hlo := ((hasDerivAt_const w (-y * Real.sqrt q)).sub (hasDerivAt_id w)).div_const gamma
  have hhi := ((hasDerivAt_const w (y * Real.sqrt q)).sub (hasDerivAt_id w)).div_const gamma
  have hh := (((hd _).hasDerivAt.comp w hlo).sub
    ((hd _).hasDerivAt.comp w hhi)).const_mul (sourceKernelCutoff q / gamma)
  convert hh using 1 <;> dsimp only [Function.comp_def, Pi.sub_apply, id_eq] <;> ring

private theorem lm_density_bounds :
    ∃ M : ℝ, 0 < M ∧ (∀ t : ℝ, |sourceScalarDensity t| ≤ M) ∧
      (∀ t : ℝ, |deriv sourceScalarDensity t| ≤ M) := by
  obtain ⟨M0, h0⟩ := sourceScalarDensity_data.1.continuous.bounded_above_of_compact_support
    sourceScalarDensity_data.2.1
  obtain ⟨M1, h1⟩ := (sourceScalarDensity_data.1.continuous_deriv (by simp)).bounded_above_of_compact_support
    sourceScalarDensity_data.2.1.deriv
  refine ⟨|M0| + |M1| + 1, by positivity, ?_, ?_⟩
  · intro t
    have hh := h0 t
    rw [Real.norm_eq_abs] at hh
    linarith [le_abs_self M0, abs_nonneg M1]
  · intro t
    have hh := h1 t
    rw [Real.norm_eq_abs] at hh
    linarith [le_abs_self M1, abs_nonneg M0]

private theorem lm_scalar_average
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (b c : α → ℝ) (hb : Measurable b) (hc : Measurable c)
    (gamma y q M : ℝ) (hg : 0 < gamma) (hy : 0 ≤ y) (hM : 0 < M)
    (h0 : ∀ t : ℝ, |sourceScalarDensity t| ≤ M)
    (h1 : ∀ t : ℝ, |deriv sourceScalarDensity t| ≤ M) :
    let f : ℝ → ℝ := fun w => ∫ a : α, ∫ t : ℝ,
      sourceFourierTest y (w + b a + gamma * t, q + c a) ∂sourceScalarLaw ∂μ
    (∀ w : ℝ,
      DifferentiableAt ℝ f w ∧ DifferentiableAt ℝ (fun r : ℝ => deriv f r) w ∧
        |deriv f w| ≤ 2 * M / gamma ∧
        |deriv (fun r : ℝ => deriv f r) w| ≤ 2 * M / gamma ^ 2 ∧
        deriv f w = ∫ a : α, sourceKernelCutoff (q + c a) / gamma *
          (sourceScalarDensity ((-y * Real.sqrt (q + c a) - (w + b a)) / gamma) -
            sourceScalarDensity ((y * Real.sqrt (q + c a) - (w + b a)) / gamma)) ∂μ ∧
        deriv (fun r : ℝ => deriv f r) w = ∫ a : α,
          sourceKernelCutoff (q + c a) / gamma ^ 2 *
            (deriv sourceScalarDensity ((y * Real.sqrt (q + c a) - (w + b a)) / gamma) -
              deriv sourceScalarDensity ((-y * Real.sqrt (q + c a) - (w + b a)) / gamma)) ∂μ) ∧
      (∀ w v : ℝ, |f w - f v| ≤ 2 * M / gamma * |w - v|) := by
  letI : IsProbabilityMeasure sourceScalarLaw := sourceScalarLaw_data.1
  let F : ℝ → α → ℝ := fun w a => ∫ t : ℝ,
    sourceFourierTest y (w + b a + gamma * t, q + c a) ∂sourceScalarLaw
  let D : ℝ → α → ℝ := fun w a => sourceKernelCutoff (q + c a) / gamma *
    (sourceScalarDensity ((-y * Real.sqrt (q + c a) - (w + b a)) / gamma) -
      sourceScalarDensity ((y * Real.sqrt (q + c a) - (w + b a)) / gamma))
  let E : ℝ → α → ℝ := fun w a => sourceKernelCutoff (q + c a) / gamma ^ 2 *
    (deriv sourceScalarDensity ((y * Real.sqrt (q + c a) - (w + b a)) / gamma) -
      deriv sourceScalarDensity ((-y * Real.sqrt (q + c a) - (w + b a)) / gamma))
  have hFmeas (w : ℝ) : Measurable (F w) := by
    have hh : Measurable (fun p : α × ℝ =>
        sourceFourierTest y (w + b p.1 + gamma * p.2, q + c p.1)) :=
      (lm_test_measurable y).comp (by fun_prop)
    exact hh.stronglyMeasurable.integral_prod_right'.measurable
  have hFbound (w : ℝ) (a : α) : ‖F w a‖ ≤ 1 := by
    have hh := norm_integral_le_of_norm_le
      (f := fun t : ℝ => sourceFourierTest y (w + b a + gamma * t, q + c a))
      (integrable_const (μ := sourceScalarLaw) (1 : ℝ))
      (Filter.Eventually.of_forall fun t =>
        by simpa only [Real.norm_eq_abs, abs_of_nonneg (lm_test_bounds y _).1]
          using (lm_test_bounds y (w + b a + gamma * t, q + c a)).2)
    simpa only [F, integral_const, probReal_univ, one_smul] using hh
  have hFi (w : ℝ) : Integrable (F w) μ :=
    (integrable_const (1 : ℝ)).mono' (hFmeas w).aestronglyMeasurable
      (Filter.Eventually.of_forall (hFbound w))
  have hDmeas (w : ℝ) : Measurable (D w) := by
    dsimp [D]
    have hr := sourceScalarDensity_data.1.continuous.measurable
    have hχ := sourceKernelCutoff_data.1.continuous.measurable
    fun_prop
  have hEmeas (w : ℝ) : Measurable (E w) := by
    dsimp [E]
    have hr := (sourceScalarDensity_data.1.continuous_deriv (by simp)).measurable
    have hχ := sourceKernelCutoff_data.1.continuous.measurable
    fun_prop
  have hbnd (r : ℝ → ℝ) (hr : ∀ t, |r t| ≤ M) (k : ℝ) (hk : 0 < k)
      (z u v : ℝ) :
      |sourceKernelCutoff z / k * (r u - r v)| ≤ 2 * M / k := by
    have hχ := sourceKernelCutoff_data.2.2.1 z
    rw [abs_mul, abs_of_nonneg (div_nonneg hχ.1 hk.le)]
    calc
      _ ≤ sourceKernelCutoff z / k * (|r u| + |r v|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (div_nonneg hχ.1 hk.le)
      _ ≤ sourceKernelCutoff z / k * (2 * M) := by
        exact mul_le_mul_of_nonneg_left (by linarith [hr u, hr v])
          (div_nonneg hχ.1 hk.le)
      _ ≤ 1 / k * (2 * M) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hχ.2 hk.le) (by positivity)
      _ = _ := by ring
  have hDb (w : ℝ) (a : α) : ‖D w a‖ ≤ 2 * M / gamma := by
    simpa only [D, Real.norm_eq_abs] using hbnd sourceScalarDensity h0 gamma hg
      (q + c a) ((-y * Real.sqrt (q + c a) - (w + b a)) / gamma)
      ((y * Real.sqrt (q + c a) - (w + b a)) / gamma)
  have hEb (w : ℝ) (a : α) : ‖E w a‖ ≤ 2 * M / gamma ^ 2 := by
    simpa only [E, Real.norm_eq_abs] using hbnd (deriv sourceScalarDensity) h1 (gamma ^ 2)
      (sq_pos_of_pos hg) (q + c a)
      ((y * Real.sqrt (q + c a) - (w + b a)) / gamma)
      ((-y * Real.sqrt (q + c a) - (w + b a)) / gamma)
  have hDi (w : ℝ) : Integrable (D w) μ :=
    (integrable_const (2 * M / gamma)).mono' (hDmeas w).aestronglyMeasurable
      (Filter.Eventually.of_forall (hDb w))
  have hEi (w : ℝ) : Integrable (E w) μ :=
    (integrable_const (2 * M / gamma ^ 2)).mono' (hEmeas w).aestronglyMeasurable
      (Filter.Eventually.of_forall (hEb w))
  have hFD (w : ℝ) (a : α) : HasDerivAt (fun v => F v a) (D w a) w := by
    simpa only [F, D, Function.comp_def, mul_one, id_eq] using
      (lm_scalar_hasDeriv gamma y (q + c a) (w + b a) hg hy).comp w
        ((hasDerivAt_id w).add_const (b a))
  have hDE (w : ℝ) (a : α) : HasDerivAt (fun v => D v a) (E w a) w := by
    simpa only [D, E, Function.comp_def, mul_one, id_eq] using
      (lm_scalar_first_hasDeriv gamma y (q + c a) (w + b a)).comp w
        ((hasDerivAt_id w).add_const (b a))
  have hdf (w : ℝ) : HasDerivAt (fun v => ∫ a : α, F v a ∂μ) (∫ a : α, D w a ∂μ) w :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ)
      (bound := fun _ : α => 2 * M / gamma) (by simp)
      (Filter.Eventually.of_forall fun v => (hFmeas v).aestronglyMeasurable) (hFi w)
      (hDmeas w).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a v _ => hDb v a) (integrable_const _)
      (Filter.Eventually.of_forall fun a v _ => hFD v a)).2
  have hddf (w : ℝ) : HasDerivAt
      (fun v => deriv (fun r => ∫ a : α, F r a ∂μ) v) (∫ a : α, E w a ∂μ) w := by
    have hh := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ)
      (bound := fun _ : α => 2 * M / gamma ^ 2) (by simp)
      (Filter.Eventually.of_forall fun v => (hDmeas v).aestronglyMeasurable) (hDi w)
      (hEmeas w).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a v _ => hEb v a) (integrable_const _)
      (Filter.Eventually.of_forall fun a v _ => hDE v a)).2
    exact hh.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => (hdf v).deriv)
  have hd_bound (w : ℝ) : |deriv (fun v => ∫ a : α, F v a ∂μ) w| ≤ 2 * M / gamma := by
    rw [(hdf w).deriv, ← Real.norm_eq_abs]
    simpa only [integral_const, probReal_univ, one_smul] using
      norm_integral_le_of_norm_le (integrable_const (μ := μ) _)
        (Filter.Eventually.of_forall (hDb w))
  refine ⟨fun w => ⟨(hdf w).differentiableAt, (hddf w).differentiableAt,
    hd_bound w, ?_, (hdf w).deriv, (hddf w).deriv⟩, ?_⟩
  · rw [(hddf w).deriv, ← Real.norm_eq_abs]
    simpa only [integral_const, probReal_univ, one_smul] using
      norm_integral_le_of_norm_le (integrable_const (μ := μ) _)
        (Filter.Eventually.of_forall (hEb w))
  · intro w v
    have hh := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun z _ => (hdf z).differentiableAt)
      (fun z _ => by simpa only [Real.norm_eq_abs] using hd_bound z)
      (Set.mem_univ v) (Set.mem_univ w)
    simpa only [F, Real.norm_eq_abs] using hh

private theorem lm_unit_integrable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (F : α → ℝ) (hF : Measurable F) (h01 : ∀ a, 0 ≤ F a ∧ F a ≤ 1) :
    Integrable F μ ∧ 0 ≤ ∫ a, F a ∂μ ∧ (∫ a, F a ∂μ) ≤ 1 := by
  have hi : Integrable F μ := (integrable_const (1 : ℝ)).mono' hF.aestronglyMeasurable
    (Filter.Eventually.of_forall fun a => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (h01 a).1] using (h01 a).2)
  refine ⟨hi, integral_nonneg (fun a => (h01 a).1), ?_⟩
  simpa using integral_mono hi (integrable_const (1 : ℝ)) (fun a => (h01 a).2)

private theorem lm_kernel_scalar_eq (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure (quadraticChordFamilyLaw ν)] (m : ℕ) (y w q : ℝ) :
    sourceFutureNoiseKernel ν m y (w, q) =
      ∫ a : Shao.Path m × ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)),
        ∫ t : ℝ, sourceFourierTest y
          (w + (Shao.prefixSum a.1 m + (∑ j : Fin 8, (a.2.1 j).1) -
            (∑ j : Fin 8, (a.2.2 j).1)) +
            ((∫ r : ℝ, |r| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν) * t,
            q + (Shao.energy a.1 + (∑ j : Fin 8, (a.2.1 j).2) +
              (∑ j : Fin 8, (a.2.2 j).2))) ∂sourceScalarLaw
        ∂(Measure.pi (fun _ : Fin m => ν)).prod
          ((quadraticChordFamilyLaw ν).prod (quadraticChordFamilyLaw ν)) := by
  letI : IsProbabilityMeasure sourceScalarLaw := sourceScalarLaw_data.1
  letI : IsProbabilityMeasure (quadraticNoiseInputLaw ν) := by
    unfold quadraticNoiseInputLaw
    infer_instance
  let H := fun (a : Shao.Path m) (z : ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) × ℝ) =>
    sourceFourierTest y
      (w + Shao.prefixSum a m + (quadraticFullNoiseMap ν z).1,
        q + Shao.energy a + (quadraticFullNoiseMap ν z).2)
  have hm (a : Shao.Path m) : Measurable (H a) := by
    dsimp [H]
    apply (lm_test_measurable y).comp
    unfold quadraticFullNoiseMap
    fun_prop
  have hi (a : Shao.Path m) : Integrable (H a) (quadraticNoiseInputLaw ν) :=
    (lm_unit_integrable _ _ (hm a) (fun z => lm_test_bounds y _)).1
  have he (a : Shao.Path m) :
      (∫ z : ℝ × ℝ, sourceFourierTest y
        (w + Shao.prefixSum a m + z.1, q + Shao.energy a + z.2) ∂quadraticFullNoiseLaw ν) =
        ∫ c : (Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ),
          ∫ t : ℝ, H a (c, t) ∂sourceScalarLaw
          ∂(quadraticChordFamilyLaw ν).prod (quadraticChordFamilyLaw ν) := by
    unfold quadraticFullNoiseLaw
    rw [integral_map (μ := quadraticNoiseInputLaw ν) (φ := quadraticFullNoiseMap ν)
      (f := fun z : ℝ × ℝ => sourceFourierTest y
        (w + Shao.prefixSum a m + z.1, q + Shao.energy a + z.2))
      (by unfold quadraticFullNoiseMap; fun_prop)
      (((lm_test_measurable y).comp (by fun_prop)).aestronglyMeasurable)]
    exact integral_prod _ (hi a)
  unfold sourceFutureNoiseKernel
  simp_rw [he]
  have hK : Measurable (fun a : Shao.Path m × ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) =>
      ∫ t : ℝ, H a.1 (a.2, t) ∂sourceScalarLaw) := by
    have ht : Measurable (fun p :
        (Shao.Path m × ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ))) × ℝ =>
        H p.1.1 (p.1.2, p.2)) := by
      dsimp [H, quadraticFullNoiseMap, Shao.prefixSum, Shao.energy]
      apply (lm_test_measurable y).comp
      fun_prop
    exact ht.stronglyMeasurable.integral_prod_right'.measurable
  have hKi := (lm_unit_integrable
    ((Measure.pi (fun _ : Fin m => ν)).prod
      ((quadraticChordFamilyLaw ν).prod (quadraticChordFamilyLaw ν))) _ hK
    (fun a => (lm_unit_integrable sourceScalarLaw _ ((hm a.1).comp (by fun_prop))
      (fun t => lm_test_bounds y _)).2)).1
  rw [← integral_prod _ hKi]
  apply integral_congr_ae
  filter_upwards [] with a
  apply integral_congr_ae
  filter_upwards [] with t
  dsimp [H, quadraticFullNoiseMap]
  congr 1 <;> ring

private theorem lm_endpoint_bound (r : ℝ → ℝ) (M : ℝ)
    (hr : ∀ t : ℝ, |r t| ≤ M) (k : ℝ) (hk : 0 < k) (z u v : ℝ) :
    |sourceKernelCutoff z / k * (r u - r v)| ≤ 2 * M / k := by
  have hχ := sourceKernelCutoff_data.2.2.1 z
  rw [abs_mul, abs_of_nonneg (div_nonneg hχ.1 hk.le)]
  calc
    _ ≤ sourceKernelCutoff z / k * (|r u| + |r v|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) (div_nonneg hχ.1 hk.le)
    _ ≤ sourceKernelCutoff z / k * (2 * M) :=
      mul_le_mul_of_nonneg_left (by linarith [hr u, hr v]) (div_nonneg hχ.1 hk.le)
    _ ≤ 1 / k * (2 * M) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hχ.2 hk.le)
        (by linarith [abs_nonneg (r u), hr u])
    _ = _ := by ring

private theorem lm_density_deriv_zero (t : ℝ) (ht : 1 < |t|) :
    deriv sourceScalarDensity t = 0 := by
  have ho : IsOpen {s : ℝ | 1 < |s|} := isOpen_lt continuous_const continuous_abs
  have hn : ∀ᶠ s : ℝ in 𝓝 t, 1 < |s| := ho.mem_nhds ht
  have he : sourceScalarDensity =ᶠ[𝓝 t] (fun _ : ℝ => 0) :=
    hn.mono (fun s hs => sourceScalarDensity_data.2.2.2.2.1 s hs.le)
  exact ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq he).deriv

private theorem lm_geometry (h y : ℝ) (hh : 0 < h) (hy : 2 ≤ y)
    (hs : h ≤ 1 / (192 * (1 + y))) :
    64 * h ^ 2 < 1 ∧ 36 * h ≤ y / 32 := by
  have hp : 0 < 192 * (1 + y) := by positivity
  have hb := (le_div_iff₀ hp).mp hs
  have ht := mul_nonneg (sub_nonneg.mpr hy) hh.le
  have hsmall : h ≤ 1 / 576 := by nlinarith
  have hsquare := pow_le_pow_left₀ hh.le hsmall 2
  constructor <;> nlinarith

private theorem lm_cutoff_radius (y R : ℝ) (hy : 0 < y)
    (hχ : sourceKernelCutoff R ≠ 0) : y / 4 < y * Real.sqrt R := by
  have hmem : R ∈ tsupport sourceKernelCutoff := subset_closure hχ
  have hR := (sourceKernelCutoff_data.2.2.2.2 hmem).1
  have hsq := Real.sq_sqrt (show 0 ≤ R by linarith)
  have hr : (1 / 4 : ℝ) < Real.sqrt R := by nlinarith [Real.sqrt_nonneg R]
  nlinarith

private theorem lm_good_endpoints (h y gamma w s B R : ℝ)
    (hy : 2 ≤ y) (hh : 0 < h) (hg : 0 < gamma) (hgamma : gamma ≤ 2 * h)
    (hgeom : 36 * h ≤ y / 32) (hw : |w| ≤ h)
    (hs : |s| < y / 8) (hB : |B| ≤ 32 * h)
    (hχ : sourceKernelCutoff R ≠ 0) :
    1 < |(-y * Real.sqrt R - w - (s + B)) / gamma| ∧
      1 < |(y * Real.sqrt R - w - (s + B)) / gamma| := by
  have hr := lm_cutoff_radius y R (by linarith) hχ
  have hcenter : |w + s + B| + gamma < y * Real.sqrt R := by
    have hsum := abs_add_le (w + s) B
    have hsum' := abs_add_le w s
    nlinarith
  have hc := abs_le.mp (le_refl |w + s + B|)
  have hlo : (-y * Real.sqrt R - w - (s + B)) / gamma < -1 := by
    apply (div_lt_iff₀ hg).mpr
    nlinarith [neg_abs_le (w + s + B)]
  have hhi : 1 < (y * Real.sqrt R - w - (s + B)) / gamma := by
    apply (lt_div_iff₀ hg).mpr
    nlinarith [le_abs_self (w + s + B)]
  exact ⟨by simpa only [neg_neg] using (neg_lt_neg hlo).trans_le (neg_le_abs _),
    hhi.trans_le (le_abs_self _)⟩

private theorem lm_family_support (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) :
    ∀ᵐ c : (Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)
      ∂(quadraticChordFamilyLaw ν).prod (quadraticChordFamilyLaw ν),
      |(∑ j : Fin 8, (c.1 j).1) - (∑ j : Fin 8, (c.2 j).1)| ≤ 32 * h ∧
        |(∑ j : Fin 8, (c.1 j).2) + (∑ j : Fin 8, (c.2 j).2)| ≤ 64 * h ^ 2 := by
  obtain ⟨_, hp, hcs, _⟩ := quadraticChord_law_data ν h3 hV h hh hs
  letI := hp
  letI : IsProbabilityMeasure (quadraticChordFamilyLaw ν) := by
    unfold quadraticChordFamilyLaw
    infer_instance
  have hf : ∀ᵐ c : Fin 8 → ℝ × ℝ ∂quadraticChordFamilyLaw ν,
      ∀ j : Fin 8, |(c j).1| ≤ 2 * h ∧ |(c j).2| ≤ 4 * h ^ 2 := by
    rw [ae_all_iff]
    intro j
    filter_upwards [(measurePreserving_eval
      (fun _ : Fin 8 => quadraticChordLaw ν) j).quasiMeasurePreserving.ae hcs] with c hc
    refine ⟨hc.1, ?_⟩
    have hm := mul_le_mul_of_nonneg_left hc.1 (show 0 ≤ 2 * h by positivity)
    nlinarith [hc.2]
  have hfam (c : Fin 8 → ℝ × ℝ)
      (hc : ∀ j : Fin 8, |(c j).1| ≤ 2 * h ∧ |(c j).2| ≤ 4 * h ^ 2) :
      |∑ j : Fin 8, (c j).1| ≤ 16 * h ∧
        |∑ j : Fin 8, (c j).2| ≤ 32 * h ^ 2 := by
    constructor
    · calc
        _ ≤ ∑ j : Fin 8, |(c j).1| := by simpa only [Real.norm_eq_abs] using norm_sum_le (s := Finset.univ) (f := fun j : Fin 8 => (c j).1)
        _ ≤ ∑ _j : Fin 8, 2 * h := Finset.sum_le_sum (fun j _ => (hc j).1)
        _ = _ := by simp; ring
    · calc
        _ ≤ ∑ j : Fin 8, |(c j).2| := by simpa only [Real.norm_eq_abs] using norm_sum_le (s := Finset.univ) (f := fun j : Fin 8 => (c j).2)
        _ ≤ ∑ _j : Fin 8, 4 * h ^ 2 := Finset.sum_le_sum (fun j _ => (hc j).2)
        _ = _ := by simp; ring
  have hc := (measurePreserving_fst.quasiMeasurePreserving.ae hf).and
    (measurePreserving_snd.quasiMeasurePreserving.ae hf)
  filter_upwards [hc] with c hc
  obtain ⟨h1, h2⟩ := hfam c.1 hc.1
  obtain ⟨h3, h4⟩ := hfam c.2 hc.2
  constructor
  · exact (abs_sub _ _).trans (by linarith)
  · exact (abs_add_le _ _).trans (by linarith)

theorem sourceFutureNoiseKernel_scalar_localized_bounds :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
        Integrable (fun a : ℝ => |a| ^ 3) ν →
        0 < variance (id : ℝ → ℝ) ν →
        ∀ h : ℝ, 0 < h → (∀ᵐ a : ℝ ∂ν, |a| ≤ h) →
          let gamma : ℝ :=
            (∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν
          gamma ≤ 2 * h →
            ∀ (m : ℕ) (y : ℝ), 2 ≤ y →
              h ≤ 1 / (192 * (1 + y)) →
              let pi : Measure (Shao.Path m) :=
                Measure.pi (fun _ : Fin m => ν)
              let f : ℝ → ℝ → ℝ :=
                fun q w => sourceFutureNoiseKernel ν m y (w, q)
              (∀ q w : ℝ,
                DifferentiableAt ℝ (f q) w ∧
                  DifferentiableAt ℝ (fun r : ℝ => deriv (f q) r) w) ∧
              (∀ q : ℝ, 5 < q → ∀ w : ℝ,
                f q w = 0 ∧ deriv (f q) w = 0 ∧
                  deriv (fun r : ℝ => deriv (f q) r) w = 0) ∧
              (∀ q w : ℝ, q ∈ Set.Icc (1 / 16 : ℝ) 5 → |w| ≤ h →
                |deriv (f q) w| ≤ C / gamma *
                    pi.real {a : Shao.Path m |
                      y / 8 ≤ |Shao.prefixSum a m|} ∧
                  |deriv (fun r : ℝ => deriv (f q) r) w| ≤ C / gamma ^ 2 *
                    pi.real {a : Shao.Path m |
                      y / 8 ≤ |Shao.prefixSum a m|}) ∧
              (m = 0 →
                (∀ q w : ℝ, |w| ≤ 2 * h → f q w = f q 0) ∧
                  (∀ q w : ℝ, |w| ≤ h →
                    deriv (f q) w = 0 ∧
                      deriv (fun r : ℝ => deriv (f q) r) w = 0)) := by
  obtain ⟨M, hM, h0, h1⟩ := lm_density_bounds
  refine ⟨2 * M, by positivity, ?_⟩
  intro ν hp h3 hV h hh hs
  letI := hp
  let gamma : ℝ := (∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν
  change gamma ≤ 2 * h → _
  intro hgamma m y hy hsmall
  dsimp only
  have hprob := quadraticFullNoise_law_data ν h3 hV h hh hs
  letI := hprob.1
  letI := hprob.2.2.1
  have hm3 : 0 < ∫ a : ℝ, |a| ^ 3 ∂ν := by
    have hn : 0 ≤ ∫ a : ℝ, |a| ^ 3 ∂ν := integral_nonneg (fun a => by positivity)
    by_contra hbad
    have hz : (∫ a : ℝ, |a| ^ 3 ∂ν) = 0 := by linarith
    have hae := (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun a : ℝ => pow_nonneg (abs_nonneg a) 3) h3).1 hz
    have he : (id : ℝ → ℝ) =ᵐ[ν] (fun _ => (0 : ℝ)) := by
      filter_upwards [hae] with a ha
      exact abs_eq_zero.1 (eq_zero_of_pow_eq_zero ha)
    have hv := variance_congr he
    have hv0 : variance (fun _ : ℝ => (0 : ℝ)) ν = 0 := by
      rw [variance_eq_sub (memLp_const (0 : ℝ))]
      simp
    linarith
  have hg : 0 < gamma := div_pos hm3 hV
  obtain ⟨hY, hgeom⟩ := lm_geometry h y hh hy hsmall
  have hfull := (quadraticFullNoise_support_moments ν h3 hV h hh hs hgamma).1
  let P : Measure ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) :=
    (quadraticChordFamilyLaw ν).prod (quadraticChordFamilyLaw ν)
  let pi : Measure (Shao.Path m) := Measure.pi (fun _ : Fin m => ν)
  let μ : Measure
      (Shao.Path m × ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ))) := pi.prod P
  let B : ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) → ℝ :=
    fun c => (∑ j : Fin 8, (c.1 j).1) - (∑ j : Fin 8, (c.2 j).1)
  let D : ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) → ℝ :=
    fun c => (∑ j : Fin 8, (c.1 j).2) + (∑ j : Fin 8, (c.2 j).2)
  let b : (Shao.Path m × ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ))) → ℝ :=
    fun a => Shao.prefixSum a.1 m + B a.2
  have hb : Measurable b := by dsimp [b, B, Shao.prefixSum]; fun_prop
  have hc : Measurable (fun a : Shao.Path m ×
      ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) => Shao.energy a.1 + D a.2) := by
    dsimp [D, Shao.energy]; fun_prop
  have he (q : ℝ) : (fun w : ℝ => sourceFutureNoiseKernel ν m y (w, q)) =
      (fun w : ℝ => ∫ a, ∫ t : ℝ,
        sourceFourierTest y (w + b a + gamma * t, q + (Shao.energy a.1 + D a.2))
          ∂sourceScalarLaw ∂μ) := by
    funext w
    rw [lm_kernel_scalar_eq ν m y w q]
    apply integral_congr_ae
    filter_upwards [] with a
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp [b, B, D, gamma]
    congr 1 <;> ring
  have HG := fun q : ℝ => lm_scalar_average μ b
    (fun a => Shao.energy a.1 + D a.2) hb hc gamma y q M hg (by linarith) hM h0 h1
  have hder (q w : ℝ) :
      DifferentiableAt ℝ (fun v : ℝ => sourceFutureNoiseKernel ν m y (v, q)) w ∧
        DifferentiableAt ℝ (fun r : ℝ => deriv (fun v : ℝ => sourceFutureNoiseKernel ν m y (v, q)) r) w := by
    rw [he q]
    exact ⟨((HG q).1 w).1, ((HG q).1 w).2.1⟩
  have hlocal (q w : ℝ) (hw : |w| ≤ h) :
      |deriv (fun v : ℝ => sourceFutureNoiseKernel ν m y (v, q)) w| ≤
        2 * M / gamma * pi.real {a : Shao.Path m | y / 8 ≤ |Shao.prefixSum a m|} ∧
      |deriv (fun r : ℝ => deriv (fun v : ℝ => sourceFutureNoiseKernel ν m y (v, q)) r) w| ≤
        2 * M / gamma ^ 2 * pi.real {a : Shao.Path m | y / 8 ≤ |Shao.prefixSum a m|} := by
    let R : (Shao.Path m × ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ))) → ℝ :=
      fun a => q + Shao.energy a.1 + D a.2
    let lo : ℝ →
        (Shao.Path m × ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ))) → ℝ :=
      fun w a => (-y * Real.sqrt (R a) - w - b a) / gamma
    let hi : ℝ →
        (Shao.Path m × ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ))) → ℝ :=
      fun w a => (y * Real.sqrt (R a) - w - b a) / gamma
    let F1 : ℝ →
        (Shao.Path m × ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ))) → ℝ :=
      fun w a => sourceKernelCutoff (R a) / gamma *
        (sourceScalarDensity (lo w a) - sourceScalarDensity (hi w a))
    let F2 : ℝ →
        (Shao.Path m × ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ))) → ℝ :=
      fun w a => sourceKernelCutoff (R a) / gamma ^ 2 *
        (deriv sourceScalarDensity (hi w a) - deriv sourceScalarDensity (lo w a))
    let E : Set (Shao.Path m) := {a : Shao.Path m | y / 8 ≤ |Shao.prefixSum a m|}
    have hEm : MeasurableSet E := by dsimp [E, Shao.prefixSum]; measurability
    have hF1m : Measurable (F1 w) := by
      dsimp [F1, R, lo, hi, b, B, D]
      have hr := sourceScalarDensity_data.1.continuous.measurable
      have hχ := sourceKernelCutoff_data.1.continuous.measurable
      dsimp [Shao.prefixSum, Shao.energy]
      fun_prop
    have hF2m : Measurable (F2 w) := by
      dsimp [F2, R, lo, hi, b, B, D]
      have hr := (sourceScalarDensity_data.1.continuous_deriv (by simp)).measurable
      have hχ := sourceKernelCutoff_data.1.continuous.measurable
      dsimp [Shao.prefixSum, Shao.energy]
      fun_prop
    have hF1b (a) : |F1 w a| ≤ 2 * M / gamma :=
      lm_endpoint_bound sourceScalarDensity M h0 gamma hg _ _ _
    have hF2b (a) : |F2 w a| ≤ 2 * M / gamma ^ 2 :=
      lm_endpoint_bound (deriv sourceScalarDensity) M h1 (gamma ^ 2) (sq_pos_of_pos hg) _ _ _
    have hF1i : Integrable (F1 w) μ := Integrable.of_bound hF1m.aestronglyMeasurable
      (2 * M / gamma) (Filter.Eventually.of_forall (by simpa only [Real.norm_eq_abs] using hF1b))
    have hF2i : Integrable (F2 w) μ := Integrable.of_bound hF2m.aestronglyMeasurable
      (2 * M / gamma ^ 2) (Filter.Eventually.of_forall (by simpa only [Real.norm_eq_abs] using hF2b))
    have hfamily : ∀ᵐ a ∂μ, |B a.2| ≤ 32 * h ∧ |D a.2| ≤ 64 * h ^ 2 :=
      measurePreserving_snd.quasiMeasurePreserving.ae (lm_family_support ν h3 hV h hh hs)
    have hz : ∀ᵐ a ∂μ, a.1 ∉ E → F1 w a = 0 ∧ F2 w a = 0 := by
      filter_upwards [hfamily] with a ha
      intro hn
      have hS : |Shao.prefixSum a.1 m| < y / 8 := lt_of_not_ge hn
      by_cases hχ : sourceKernelCutoff (R a) = 0
      · simp [F1, F2, hχ]
      · obtain ⟨hl, hu⟩ := lm_good_endpoints h y gamma w (Shao.prefixSum a.1 m)
          (B a.2) (R a) hy hh hg hgamma hgeom hw hS ha.1 hχ
        have hrl : sourceScalarDensity (lo w a) = 0 :=
          sourceScalarDensity_data.2.2.2.2.1 _ hl.le
        have hru : sourceScalarDensity (hi w a) = 0 :=
          sourceScalarDensity_data.2.2.2.2.1 _ hu.le
        have hdl : deriv sourceScalarDensity (lo w a) = 0 := lm_density_deriv_zero _ hl
        have hdu : deriv sourceScalarDensity (hi w a) = 0 := lm_density_deriv_zero _ hu
        simp [F1, F2, hrl, hru, hdl, hdu]
    have hmajor (k : ℝ) :
        Integrable (fun a : Shao.Path m × ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) =>
          if a.1 ∈ E then k else 0) μ := by
      exact (integrable_const k).indicator (measurable_fst hEm)
    have hmajorint (k : ℝ) :
        (∫ a : Shao.Path m × ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)),
          (if a.1 ∈ E then k else 0) ∂μ) = k * pi.real E := by
      change (∫ a, E.indicator (fun _ => k) a.1 ∂pi.prod P) = _
      rw [integral_fun_fst (E.indicator (fun _ => k))]
      rw [integral_indicator_const k hEm]
      simp [mul_comm]
    have hb1 : (∫ a, |F1 w a| ∂μ) ≤ 2 * M / gamma * pi.real E := by
      rw [← hmajorint]
      apply integral_mono_ae hF1i.abs (hmajor _)
      filter_upwards [hz] with a ha
      by_cases he : a.1 ∈ E
      · simpa [he] using hF1b a
      · simp [he, (ha he).1]
    have hb2 : (∫ a, |F2 w a| ∂μ) ≤ 2 * M / gamma ^ 2 * pi.real E := by
      rw [← hmajorint]
      apply integral_mono_ae hF2i.abs (hmajor _)
      filter_upwards [hz] with a ha
      by_cases he : a.1 ∈ E
      · simpa [he] using hF2b a
      · simp [he, (ha he).2]
    rcases (HG q).1 w with ⟨_, _, _, _, hd1, hd2⟩
    have hdF1 : deriv (fun v : ℝ => sourceFutureNoiseKernel ν m y (v, q)) w = ∫ a, F1 w a ∂μ := by
      rw [he q]
      simpa only [F1, lo, hi, R, sub_sub, add_assoc] using hd1
    have hdF2 : deriv (fun r : ℝ => deriv (fun v : ℝ => sourceFutureNoiseKernel ν m y (v, q)) r) w = ∫ a, F2 w a ∂μ := by
      rw [he q]
      simpa only [F2, lo, hi, R, sub_sub, add_assoc] using hd2
    rw [hdF1, hdF2]
    exact ⟨abs_integral_le_integral_abs.trans hb1, abs_integral_le_integral_abs.trans hb2⟩
  refine ⟨hder, ?_, fun q w _ hw => hlocal q w hw, ?_⟩
  · intro q hq
    have hz (w : ℝ) : sourceFutureNoiseKernel ν m y (w, q) = 0 := by
      unfold sourceFutureNoiseKernel
      apply integral_eq_zero_of_ae
      filter_upwards [] with a
      apply integral_eq_zero_of_ae
      filter_upwards [hfull] with z hz
      have hR : 4 < q + Shao.energy a + z.2 := by
        have hneg := (abs_le.mp hz.2).1
        nlinarith [Shao.energy_nonneg a]
      have hχ : sourceKernelCutoff (q + Shao.energy a + z.2) = 0 := by
        by_contra hn
        have hm := sourceKernelCutoff_data.2.2.2.2 (subset_closure hn)
        linarith [hm.2]
      simp [sourceFourierTest, hχ]
    have hez : (fun w : ℝ => sourceFutureNoiseKernel ν m y (w, q)) = (fun _ => 0) := funext hz
    intro w
    simp [hez, hz]
  · intro hm
    subst m
    constructor
    · intro q w hw
      unfold sourceFutureNoiseKernel
      apply integral_congr_ae
      filter_upwards [] with a
      apply integral_congr_ae
      filter_upwards [hfull] with z hz
      have ht (v : ℝ) (hv : |v| ≤ 2 * h) :
          sourceFourierTest y (v + z.1, q + z.2) = sourceKernelCutoff (q + z.2) := by
        by_cases hχ : sourceKernelCutoff (q + z.2) = 0
        · simp [sourceFourierTest, hχ]
        · have hr := lm_cutoff_radius y (q + z.2) (by linarith) hχ
          have hi : |v + z.1| < y * Real.sqrt (q + z.2) := by
            nlinarith [abs_add_le v z.1, hz.1]
          simp [sourceFourierTest, hi]
      have hw' := ht w hw
      have hzero := ht 0 (by simp; linarith)
      simpa [Shao.energy, Shao.prefixSum_zero] using hw'.trans hzero.symm
    · intro q w hw
      have hbad : ¬ y / 8 ≤ (0 : ℝ) := by linarith
      have hpi : pi.real {a : Shao.Path 0 | y / 8 ≤ |Shao.prefixSum a 0|} = 0 := by
        simp [hbad]
      obtain ⟨hd1, hd2⟩ := hlocal q w hw
      rw [hpi, mul_zero] at hd1 hd2
      exact ⟨abs_eq_zero.mp (le_antisymm hd1 (abs_nonneg _)),
        abs_eq_zero.mp (le_antisymm hd2 (abs_nonneg _))⟩

theorem sourceTruncation_growing_microtime_derivative_bounds :
    ∃ C : ℝ, 0 < C ∧
      ∀ L2 epsilon0 : ℝ, 0 < L2 → 0 < epsilon0 →
        epsilon0 ≤ 1 / (192 * Real.sqrt (L2 + 1)) →
        ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
          ∀ n : ℕ, Integrable (fun a : ℝ => a ^ 2) ν0 →
            (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1 →
            (∫ a : ℝ, a ∂ν0) = 0 →
            ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon →
              epsilon ≤ epsilon0 / 2 →
              Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
              ∀ y : ℝ, 2 ≤ y →
                |y - x| ≤ 1 / (2 * (1 + x)) →
                ∀ m : ℕ, m ≤ n →
                  let h : ℝ := epsilon0 / (1 + y)
                  let ρ : Measure ℝ := ProbabilityTheory.cond ν0
                    {a : ℝ | |a| ≤ epsilon / (1 + x)}
                  let raw2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
                  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
                  let V : ℝ := variance (id : ℝ → ℝ) ρ
                  let gamma : ℝ := m3 / V
                  let T : ℝ := (m : ℝ) * raw2
                  let pi : Measure (Shao.Path m) :=
                    Measure.pi (fun _ : Fin m => ρ)
                  let f : ℝ → ℝ → ℝ :=
                    fun q w => sourceFutureNoiseKernel ρ m y (w, q)
                  T ≤ L2 * gamma ^ 2 →
                    (∀ q w : ℝ,
                      DifferentiableAt ℝ (f q) w ∧
                        DifferentiableAt ℝ (fun r : ℝ => deriv (f q) r) w) ∧
                    (∀ q : ℝ, 5 < q → ∀ w : ℝ,
                      f q w = 0 ∧ deriv (f q) w = 0 ∧
                        deriv (fun r : ℝ => deriv (f q) r) w = 0) ∧
                    (∀ q w : ℝ, q ∈ Set.Icc (1 / 16 : ℝ) 5 → |w| ≤ h →
                      |deriv (f q) w| ≤ C / gamma *
                          pi.real {a : Shao.Path m |
                            y / 8 ≤ |Shao.prefixSum a m|} ∧
                        |deriv (fun r : ℝ => deriv (f q) r) w| ≤ C / gamma ^ 2 *
                          pi.real {a : Shao.Path m |
                            y / 8 ≤ |Shao.prefixSum a m|} ∧
                        |deriv (f q) w| ≤
                          C / gamma * Real.exp (-4 * y ^ 2) ∧
                        |deriv (fun r : ℝ => deriv (f q) r) w| ≤
                          C / gamma ^ 2 * Real.exp (-4 * y ^ 2)) ∧
                    (m = 0 →
                      (∀ q w : ℝ, |w| ≤ 2 * h → f q w = f q 0) ∧
                        (∀ q w : ℝ, |w| ≤ h →
                          deriv (f q) w = 0 ∧
                            deriv (fun r : ℝ => deriv (f q) r) w = 0)) := by
  obtain ⟨C0, hC0, H⟩ := sourceFutureNoiseKernel_scalar_localized_bounds
  refine ⟨C0 * (2 * Real.exp 17 + 1), by positivity, ?_⟩
  intro L2 epsilon0 hL2 he0 he0bound ν0 hp n h2 hnorm hmean x epsilon hx he heSmall hR y hy hwindow m hm
  letI := hp
  dsimp only
  let h : ℝ := epsilon0 / (1 + y)
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {a : ℝ | |a| ≤ epsilon / (1 + x)}
  let raw2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
  let V : ℝ := variance (id : ℝ → ℝ) ρ
  let gamma : ℝ := m3 / V
  let T : ℝ := (m : ℝ) * raw2
  let pi : Measure (Shao.Path m) := Measure.pi (fun _ : Fin m => ρ)
  let hcut : ℝ := epsilon / (1 + x)
  intro hclock
  have hroot : 1 ≤ Real.sqrt (L2 + 1) := by
    have hs := Real.sq_sqrt (show 0 ≤ L2 + 1 by linarith)
    nlinarith [Real.sqrt_nonneg (L2 + 1)]
  have he192 : epsilon0 ≤ 1 / 192 := by
    apply he0bound.trans
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have heHalf : epsilon ≤ 1 / 2 := by linarith
  have hxp : 0 < 1 + x := by linarith
  have hyp : 0 < 1 + y := by linarith
  have hh : 0 < h := div_pos he0 hyp
  have hhalf : 1 / (2 * (1 + x)) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (show 0 < 2 * (1 + x) by positivity)).mpr
    linarith
  have hratio : 1 + y ≤ 2 * (1 + x) := by linarith [(abs_le.mp hwindow).2]
  have hcutH : hcut ≤ h := by
    apply (div_le_div_iff₀ hxp hyp).mpr
    calc
      epsilon * (1 + y) ≤ (epsilon0 / 2) * (1 + y) :=
        mul_le_mul_of_nonneg_right heSmall hyp.le
      _ ≤ (epsilon0 / 2) * (2 * (1 + x)) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = epsilon0 * (1 + x) := by ring
  obtain ⟨_, _, hprob, hs, _, _, h3, _⟩ :=
    Shao.sourceTruncation_law_data ν0 n h2 hnorm x epsilon hx he heHalf hR
  change IsProbabilityMeasure ρ at hprob
  letI := hprob
  change ∀ᵐ a : ℝ ∂ρ, |a| ≤ hcut at hs
  have hsupport : ∀ᵐ a : ℝ ∂ρ, |a| ≤ h := hs.mono (fun a ha => ha.trans hcutH)
  have hV := (Shao.sourceTruncation_variance_bounds ν0 n h2 hnorm hmean x epsilon hx he heHalf hR).2.2.2.2.2.1
  have hgammaData := Shao.sourceTruncation_gamma_bounds ν0 n h2 hnorm hmean x epsilon hx he heHalf hR
  change 0 < m3 ∧ 0 < gamma ∧ _ at hgammaData
  have hg : 0 < gamma := hgammaData.2.1
  have hgamma : gamma ≤ 2 * h := hgammaData.2.2.2.2.1.trans (by linarith)
  have hsmall : h ≤ 1 / (192 * (1 + y)) := by
    calc
      h ≤ (1 / 192) / (1 + y) := div_le_div_of_nonneg_right he192 hyp.le
      _ = _ := by field_simp <;> ring
  have HK := H ρ hprob h3 hV h hh hsupport hgamma m y hy hsmall
  have HT := sourceTruncation_growing_microtime_abs_tail L2 epsilon0 hL2 he0 he0bound
    ν0 n h2 hnorm hmean x epsilon hx he heSmall hR y hy hwindow m hm hclock
  have htail : pi.real {a : Shao.Path m | y / 8 ≤ |Shao.prefixSum a m|} ≤
      2 * Real.exp 17 * Real.exp (-4 * y ^ 2) := HT.2.2
  refine ⟨HK.1, HK.2.1, ?_, HK.2.2.2⟩
  intro q w hq hw
  obtain ⟨hd1, hd2⟩ := HK.2.2.1 q w hq hw
  have hlarge : C0 ≤ C0 * (2 * Real.exp 17 + 1) := by nlinarith [Real.exp_pos (17 : ℝ)]
  have hlargeTail : C0 * (2 * Real.exp 17) ≤ C0 * (2 * Real.exp 17 + 1) := by linarith
  have hprobNonneg : 0 ≤ pi.real {a : Shao.Path m | y / 8 ≤ |Shao.prefixSum a m|} := ENNReal.toReal_nonneg
  have hdiv1 := div_le_div_of_nonneg_right hlarge hg.le
  have hdiv2 := div_le_div_of_nonneg_right hlarge (sq_nonneg gamma)
  refine ⟨hd1.trans (mul_le_mul_of_nonneg_right hdiv1 hprobNonneg),
    hd2.trans (mul_le_mul_of_nonneg_right hdiv2 hprobNonneg), ?_, ?_⟩
  · calc
      _ ≤ C0 / gamma * (2 * Real.exp 17 * Real.exp (-4 * y ^ 2)) :=
        hd1.trans (mul_le_mul_of_nonneg_left htail (by positivity))
      _ = (C0 * (2 * Real.exp 17)) / gamma * Real.exp (-4 * y ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hlargeTail hg.le) (Real.exp_pos _).le
  · calc
      _ ≤ C0 / gamma ^ 2 * (2 * Real.exp 17 * Real.exp (-4 * y ^ 2)) :=
        hd2.trans (mul_le_mul_of_nonneg_left htail (by positivity))
      _ = (C0 * (2 * Real.exp 17)) / gamma ^ 2 * Real.exp (-4 * y ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hlargeTail (sq_nonneg gamma)) (Real.exp_pos _).le

end Shao.Probability
