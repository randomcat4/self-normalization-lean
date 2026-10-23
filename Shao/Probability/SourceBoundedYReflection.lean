import Shao.Probability.SourceLongKernelBounds
import Shao.Probability.SourceShortTimeKernelTaylor
import Shao.Probability.SourceLindleyRegulatorFirstMomentSums
import Shao.Probability.SourceLindleySurvival
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators ContDiff Topology

private theorem br_test_measurable (y : ℝ) : Measurable (sourceFourierTest y) := by
  have hA : MeasurableSet {p : ℝ × ℝ | |p.1| < y * Real.sqrt p.2} :=
    (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet
  exact (sourceKernelCutoff_data.1.continuous.measurable.comp measurable_snd).mul
    (Measurable.ite hA measurable_const measurable_const)

private theorem br_test_bounds (y : ℝ) (p : ℝ × ℝ) :
    0 ≤ sourceFourierTest y p ∧ sourceFourierTest y p ≤ 1 := by
  unfold sourceFourierTest
  split_ifs
  · simpa using sourceKernelCutoff_data.2.2.1 p.2
  · simp

private theorem br_scalar_interval (gamma y w q : ℝ) (hg : 0 < gamma) (hy : 0 ≤ y) :
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

private theorem br_scalar_hasDeriv (gamma y q w : ℝ) (hg : 0 < gamma) (hy : 0 ≤ y) :
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
    funext fun v => br_scalar_interval gamma y v q hg hy
  rw [he]
  convert hh using 1 <;> dsimp only [Function.comp_def, Pi.sub_apply, id_eq] <;> ring

private theorem br_scalar_first_hasDeriv (gamma y q w : ℝ) :
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

private theorem br_density_bounds :
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

private theorem br_scalar_average
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
        |deriv (fun r : ℝ => deriv f r) w| ≤ 2 * M / gamma ^ 2) ∧
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
      (br_test_measurable y).comp (by fun_prop)
    exact hh.stronglyMeasurable.integral_prod_right'.measurable
  have hFbound (w : ℝ) (a : α) : ‖F w a‖ ≤ 1 := by
    have hh := norm_integral_le_of_norm_le
      (f := fun t : ℝ => sourceFourierTest y (w + b a + gamma * t, q + c a))
      (integrable_const (μ := sourceScalarLaw) (1 : ℝ))
      (Filter.Eventually.of_forall fun t =>
        by simpa only [Real.norm_eq_abs, abs_of_nonneg (br_test_bounds y _).1]
          using (br_test_bounds y (w + b a + gamma * t, q + c a)).2)
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
      (br_scalar_hasDeriv gamma y (q + c a) (w + b a) hg hy).comp w
        ((hasDerivAt_id w).add_const (b a))
  have hDE (w : ℝ) (a : α) : HasDerivAt (fun v => D v a) (E w a) w := by
    simpa only [D, E, Function.comp_def, mul_one, id_eq] using
      (br_scalar_first_hasDeriv gamma y (q + c a) (w + b a)).comp w
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
  refine ⟨fun w => ⟨(hdf w).differentiableAt, (hddf w).differentiableAt, hd_bound w, ?_⟩, ?_⟩
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

private theorem br_unit_integrable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (F : α → ℝ) (hF : Measurable F) (h01 : ∀ a, 0 ≤ F a ∧ F a ≤ 1) :
    Integrable F μ ∧ 0 ≤ ∫ a, F a ∂μ ∧ (∫ a, F a ∂μ) ≤ 1 := by
  have hi : Integrable F μ := (integrable_const (1 : ℝ)).mono' hF.aestronglyMeasurable
    (Filter.Eventually.of_forall fun a => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (h01 a).1] using (h01 a).2)
  refine ⟨hi, integral_nonneg (fun a => (h01 a).1), ?_⟩
  simpa using integral_mono hi (integrable_const (1 : ℝ)) (fun a => (h01 a).2)

private theorem br_kernel_scalar_eq (ν : Measure ℝ) [IsProbabilityMeasure ν]
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
    apply (br_test_measurable y).comp
    unfold quadraticFullNoiseMap
    fun_prop
  have hi (a : Shao.Path m) : Integrable (H a) (quadraticNoiseInputLaw ν) :=
    (br_unit_integrable _ _ (hm a) (fun z => br_test_bounds y _)).1
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
      (((br_test_measurable y).comp (by fun_prop)).aestronglyMeasurable)]
    exact integral_prod _ (hi a)
  unfold sourceFutureNoiseKernel
  simp_rw [he]
  have hK : Measurable (fun a : Shao.Path m × ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) =>
      ∫ t : ℝ, H a.1 (a.2, t) ∂sourceScalarLaw) := by
    have ht : Measurable (fun p :
        (Shao.Path m × ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ))) × ℝ =>
        H p.1.1 (p.1.2, p.2)) := by
      dsimp [H, quadraticFullNoiseMap, Shao.prefixSum, Shao.energy]
      apply (br_test_measurable y).comp
      fun_prop
    exact ht.stronglyMeasurable.integral_prod_right'.measurable
  have hKi := (br_unit_integrable
    ((Measure.pi (fun _ : Fin m => ν)).prod
      ((quadraticChordFamilyLaw ν).prod (quadraticChordFamilyLaw ν))) _ hK
    (fun a => (br_unit_integrable sourceScalarLaw _ ((hm a.1).comp (by fun_prop))
      (fun t => br_test_bounds y _)).2)).1
  rw [← integral_prod _ hKi]
  apply integral_congr_ae
  filter_upwards [] with a
  apply integral_congr_ae
  filter_upwards [] with t
  dsimp [H, quadraticFullNoiseMap]
  congr 1 <;> ring

theorem sourceFutureNoiseKernel_scalar_rough_bounds :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
        Integrable (fun a : ℝ => |a| ^ 3) ν →
        0 < variance (id : ℝ → ℝ) ν →
        ∀ h : ℝ, 0 < h → (∀ᵐ a : ℝ ∂ν, |a| ≤ h) →
          let gamma : ℝ :=
            (∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν
          ∀ (m : ℕ) (y : ℝ), 0 ≤ y →
            (∀ p : ℝ × ℝ,
              0 ≤ sourceFutureNoiseKernel ν m y p ∧
                sourceFutureNoiseKernel ν m y p ≤ 1) ∧
            (∀ q : ℝ,
              let f : ℝ → ℝ := fun w => sourceFutureNoiseKernel ν m y (w, q)
              (∀ w : ℝ,
                DifferentiableAt ℝ f w ∧
                  DifferentiableAt ℝ (fun r : ℝ => deriv f r) w ∧
                  |deriv f w| ≤ C / gamma ∧
                  |deriv (fun r : ℝ => deriv f r) w| ≤ C / gamma ^ 2) ∧
              (∀ w v : ℝ, |f w - f v| ≤ C / gamma * |w - v|)) := by
  obtain ⟨M, hM, h0, h1⟩ := br_density_bounds
  refine ⟨2 * M, by positivity, ?_⟩
  intro ν hp h3 hV h hh hs
  letI := hp
  have hprob := quadraticFullNoise_law_data ν h3 hV h hh hs
  letI := hprob.1
  letI := hprob.2.2.1
  let gamma : ℝ := (∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν
  have hthird : 0 < ∫ a : ℝ, |a| ^ 3 ∂ν := by
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
  have hg : 0 < gamma := div_pos hthird hV
  dsimp only
  intro m y hy
  refine ⟨?_, ?_⟩
  · intro p
    have hi (a : Shao.Path m) := br_unit_integrable (quadraticFullNoiseLaw ν)
      (fun z : ℝ × ℝ => sourceFourierTest y
        (p.1 + Shao.prefixSum a m + z.1, p.2 + Shao.energy a + z.2))
      ((br_test_measurable y).comp (by fun_prop)) (fun z => br_test_bounds y _)
    constructor
    · exact integral_nonneg (fun a => (hi a).2.1)
    · have hm : Measurable (fun a : Shao.Path m => ∫ z : ℝ × ℝ,
          sourceFourierTest y (p.1 + Shao.prefixSum a m + z.1,
            p.2 + Shao.energy a + z.2) ∂quadraticFullNoiseLaw ν) := by
        have ht : Measurable (fun z : Shao.Path m × (ℝ × ℝ) =>
            sourceFourierTest y (p.1 + Shao.prefixSum z.1 m + z.2.1,
              p.2 + Shao.energy z.1 + z.2.2)) := by
          apply (br_test_measurable y).comp
          dsimp [Shao.prefixSum, Shao.energy]
          fun_prop
        exact ht.stronglyMeasurable.integral_prod_right'.measurable
      exact (br_unit_integrable _ _ hm (fun a => (hi a).2)).2.2
  · intro q
    let μ := (Measure.pi (fun _ : Fin m => ν)).prod
      ((quadraticChordFamilyLaw ν).prod (quadraticChordFamilyLaw ν))
    let b : Shao.Path m × ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) → ℝ := fun a =>
      Shao.prefixSum a.1 m + (∑ j : Fin 8, (a.2.1 j).1) - (∑ j : Fin 8, (a.2.2 j).1)
    let c : Shao.Path m × ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) → ℝ := fun a =>
      Shao.energy a.1 + (∑ j : Fin 8, (a.2.1 j).2) + (∑ j : Fin 8, (a.2.2 j).2)
    have hb : Measurable b := by dsimp [b, Shao.prefixSum]; fun_prop
    have hc : Measurable c := by dsimp [c, Shao.energy]; fun_prop
    have he : (fun w : ℝ => sourceFutureNoiseKernel ν m y (w, q)) =
        (fun w => ∫ a, ∫ t : ℝ, sourceFourierTest y
          (w + b a + gamma * t, q + c a) ∂sourceScalarLaw ∂μ) :=
      funext fun w => br_kernel_scalar_eq ν m y w q
    rw [he]
    have H := br_scalar_average μ b c hb hc gamma y q M hg hy hM h0 h1
    refine ⟨H.1, ?_⟩
    intro w v
    simpa only [congrFun he w, congrFun he v] using H.2 w v

private theorem br_source_scale
    (ν0 : Measure ℝ) [IsProbabilityMeasure ν0] (n : ℕ)
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν0)
    (hn : (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1)
    (hm : (∫ a : ℝ, a ∂ν0) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x) (he : 0 < epsilon) (he2 : epsilon ≤ 1 / 2)
    (hR : Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8) :
    let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
    let mu : ℝ := ∫ a : ℝ, a ∂ρ
    let s : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
    let b : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
    let V : ℝ := variance (id : ℝ → ℝ) ρ
    let gamma : ℝ := b / V
    0 < n ∧ 0 < s ∧ 0 < b ∧ 0 < V ∧ 0 < gamma ∧ s ≤ gamma ^ 2 ∧
      (3 / 4 : ℝ) ≤ (n : ℝ) * s ∧ (n : ℝ) * s ≤ 4 / 3 ∧
      (1 / 2 : ℝ) ≤ (n : ℝ) * V ∧ (n : ℝ) * V ≤ 4 / 3 ∧
      (n : ℝ) * |mu| ≤ 1 / 8 := by
  dsimp only
  obtain ⟨hslo, hshi, _, hVeq, _, hV, hVlo, hVhi⟩ :=
    Shao.sourceTruncation_variance_bounds ν0 n h2 hn hm x epsilon hx he he2 hR
  obtain ⟨hb, hg, _, hsg, _⟩ :=
    Shao.sourceTruncation_gamma_bounds ν0 n h2 hn hm x epsilon hx he he2 hR
  have hn0 : 0 < n := by
    obtain ⟨_, _, hn64, _⟩ := Shao.sourceTruncation_sample_size ν0 n h2 hn x epsilon hx he he2 hR
    omega
  have hs : 0 < ∫ a : ℝ, a ^ 2 ∂ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)} := by
    nlinarith [sq_nonneg (∫ a : ℝ, a ∂ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)})]
  have hpaid := (Shao.sourceTruncation_paid_moments ν0 n h2 hn hm x epsilon hx he he2 hR).1
  have hden : 0 < epsilon ^ 2 * (1 + x) := by positivity
  have hmu := (le_div_iff₀ hden).1 hpaid
  have hbound : (n : ℝ) * |∫ a : ℝ, a ∂ProbabilityTheory.cond ν0
      {a | |a| ≤ epsilon / (1 + x)}| ≤ 1 / 8 := by
    have hmul : epsilon ^ 2 * (1 + x) / 8 ≤ epsilon ^ 2 * (1 + x) / 8 := le_rfl
    have he8 : epsilon ^ 3 / 4 ≤ epsilon ^ 2 * (1 + x) / 8 := by
      have hs2 : 0 < epsilon ^ 2 := sq_pos_of_pos he
      nlinarith [mul_nonneg hs2.le hx]
    apply (mul_le_mul_iff_left₀ hden).1
    nlinarith only [hmu, hR, he8]
  exact ⟨hn0, hs, hb, hV, hg, hsg, hslo, hshi, hVlo, hVhi, hbound⟩

private theorem br_late_roots (N I V : ℝ) (hN : 0 < N) (hI : 0 < I) (hV : 0 < V)
    (hhalf : N ≤ 2 * I) (hlo : (1 / 2 : ℝ) ≤ N * V) (hhi : N * V ≤ 4 / 3) :
    Real.sqrt V / Real.sqrt I ≤ 2 / N ∧ 1 / (Real.sqrt V * Real.sqrt I) ≤ 2 := by
  have hv := Real.sqrt_nonneg V
  have hi := Real.sqrt_nonneg I
  have hv2 := Real.sq_sqrt hV.le
  have hi2 := Real.sq_sqrt hI.le
  have hvi : (1 / 4 : ℝ) ≤ V * I := by nlinarith
  have hprod2 : (Real.sqrt V * Real.sqrt I) ^ 2 = V * I := by rw [mul_pow, hv2, hi2]
  have hprod : 1 / 2 ≤ Real.sqrt V * Real.sqrt I := by
    nlinarith [mul_nonneg hv hi]
  refine ⟨?_, (div_le_iff₀ (by positivity)).2 (by linarith)⟩
  apply (div_le_div_iff₀ (Real.sqrt_pos.2 hI) hN).2
  have hNhi := mul_le_mul_of_nonneg_left hhi hN.le
  have hsq : (Real.sqrt V * N) ^ 2 ≤ (2 * Real.sqrt I) ^ 2 := by
    rw [mul_pow, hv2, mul_pow, hi2]
    nlinarith only [hNhi, hhalf, hI]
  nlinarith [mul_nonneg hv hN.le]

private theorem br_source_late_moments
    (ν0 : Measure ℝ) [IsProbabilityMeasure ν0] (n : ℕ)
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν0)
    (hn : (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1)
    (hm : (∫ a : ℝ, a ∂ν0) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x) (he : 0 < epsilon) (he2 : epsilon ≤ 1 / 2)
    (hR : Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8) :
    let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
    let b : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ρ)
    ∀ j : Fin n, n / 2 < j.val + 1 →
      (∫ a : Shao.Path n, lindleyRegulator a j ∂P) ≤ 4 / (n : ℝ) ∧
      (∫ a : Shao.Path n, (lindleyRegulator a j) ^ 2 ∂P) ≤
        (96 * Real.exp (7 + 3 * (1024 : ℝ))) * b := by
  dsimp only
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
  obtain ⟨_, _, hp, _, _, h2ρ, _, _⟩ :=
    Shao.sourceTruncation_law_data ν0 n h2 hn x epsilon hx he he2 hR
  letI : IsProbabilityMeasure ρ := hp
  obtain ⟨hn0, _, _, hV, _, _, _, _, hVlo, hVhi, hmu⟩ :=
    br_source_scale ν0 n h2 hn hm x epsilon hx he he2 hR
  have hN : (0 : ℝ) < n := by exact_mod_cast hn0
  intro j hj
  have hj0 : (0 : ℝ) < ((j.val + 1 : ℕ) : ℝ) := by positivity
  have hhalf : (n : ℝ) ≤ 2 * ((j.val + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show n ≤ 2 * (j.val + 1) by omega)
  obtain ⟨hroot, hinv⟩ := br_late_roots (n : ℝ) ((j.val + 1 : ℕ) : ℝ)
    (variance (id : ℝ → ℝ) ρ) hN hj0 hV hhalf hVlo hVhi
  have hfirst := (iid_lindleyRegulator_prefix_first_moment ρ h2ρ n j).2.2
  have hsecond := (sourceTruncation_lindleyRegulator_second_moment
    ν0 n h2 hn hm x epsilon hx he he2 hR j).2
  constructor
  · apply hfirst.trans
    have hmu' : |∫ a : ℝ, a ∂ρ| ≤ (1 / 8 : ℝ) / n :=
      (le_div_iff₀ hN).2 (by simpa only [mul_comm] using hmu)
    calc
      _ ≤ 2 / (n : ℝ) + (1 / 8 : ℝ) / n := add_le_add hroot hmu'
      _ = (2 + 1 / 8 : ℝ) / n := by ring
      _ ≤ 4 / (n : ℝ) := div_le_div_of_nonneg_right (by norm_num) hN.le
  · apply hsecond.trans
    have hm3 : 0 ≤ ∫ a : ℝ, |a| ^ 3 ∂ρ := integral_nonneg (fun a => by positivity)
    calc
      _ = (48 * Real.exp (7 + 3 * (1024 : ℝ))) * (∫ a : ℝ, |a| ^ 3 ∂ρ) *
          (1 / (Real.sqrt (variance (id : ℝ → ℝ) ρ) *
            Real.sqrt ((j.val + 1 : ℕ) : ℝ))) := by ring
      _ ≤ (48 * Real.exp (7 + 3 * (1024 : ℝ))) * (∫ a : ℝ, |a| ^ 3 ∂ρ) * 2 :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by ring

private theorem br_smoothed_data (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure (quadraticFullNoiseLaw ν)] (y : ℝ) :
    let ψ : ℝ × ℝ → ℝ := fun p => ∫ z : ℝ × ℝ,
      sourceFourierTest y (p.1 + z.1, p.2 + z.2) ∂quadraticFullNoiseLaw ν
    Measurable ψ ∧ (∀ p, 0 ≤ ψ p ∧ ψ p ≤ 1) ∧
      ∀ m : ℕ, ∀ p : ℝ × ℝ, lindleyFutureKernel ν m ψ p = sourceFutureNoiseKernel ν m y p := by
  dsimp only
  have hmeas : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      sourceFourierTest y (p.1.1 + p.2.1, p.1.2 + p.2.2)) :=
    (br_test_measurable y).comp (by fun_prop)
  refine ⟨hmeas.stronglyMeasurable.integral_prod_right'.measurable,
    fun p => (br_unit_integrable _ _ ((br_test_measurable y).comp (by fun_prop))
      (fun z => br_test_bounds y _)).2, ?_⟩
  intro m p
  rfl

private theorem br_regulator_measurable {n : ℕ} (j : Fin n) :
    Measurable (fun a : Shao.Path n => lindleyRegulator a j) := by
  have hp : Measurable (fun a : Shao.Path n => Shao.prefixPath a j.val (by omega)) :=
    Measurable.of_eval (fun _ => measurable_pi_apply _)
  have hr : Measurable (Shao.reversePath : Shao.Path j.val → Shao.Path j.val) :=
    Measurable.of_eval (fun _ => measurable_pi_apply _)
  have hstate : Measurable (fun a : Shao.Path n => Shao.lindleyState a j.val (by omega)) := by
    simpa only [Shao.lindleyState_eq_maxWithZero_reverse_prefix, Function.comp_def] using
      Shao.measurable_maxWithZero.comp (hr.comp hp)
  exact (hstate.add (measurable_pi_apply j)).neg.max measurable_const

private theorem br_delta_data (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (ψ : ℝ × ℝ → ℝ) (hψ : Measurable ψ)
    (h01 : ∀ p, 0 ≤ ψ p ∧ ψ p ≤ 1) (j : Fin n) :
    Measurable (fun a : Shao.Path n => |lindleyDelta ν ψ a j|) ∧
      (∀ a : Shao.Path n, 0 ≤ |lindleyDelta ν ψ a j| ∧ |lindleyDelta ν ψ a j| ≤ 1) ∧
      Integrable (fun a : Shao.Path n => |lindleyDelta ν ψ a j|)
        (Measure.pi (fun _ : Fin n => ν)) := by
  have hK := measurable_lindleyFutureKernel ν (n - (j.val + 1)) ψ hψ
  have hU := br_regulator_measurable j
  have hQ := Shao.measurable_prefixSquares (n := n) (j.val + 1)
  have hd : Measurable (fun a : Shao.Path n => |lindleyDelta ν ψ a j|) :=
    continuous_abs.measurable.comp ((hK.comp (measurable_const.prodMk hQ)).sub
      (hK.comp (hU.neg.prodMk hQ)))
  have hb (a : Shao.Path n) : |lindleyDelta ν ψ a j| ≤ 1 := by
    have h0 := lindleyFutureKernel_bounds ν (n - (j.val + 1)) ψ hψ h01
      (0, Shao.prefixSquares a (j.val + 1))
    have h1 := lindleyFutureKernel_bounds ν (n - (j.val + 1)) ψ hψ h01
      (-lindleyRegulator a j, Shao.prefixSquares a (j.val + 1))
    exact abs_le.2 ⟨by dsimp [lindleyDelta]; linarith, by dsimp [lindleyDelta]; linarith⟩
  exact ⟨hd, fun a => ⟨abs_nonneg _, hb a⟩,
    (br_unit_integrable _ _ hd (fun a => ⟨abs_nonneg _, hb a⟩)).1⟩

private theorem br_clock_card {n : ℕ} (J : Finset (Fin n)) (s A : ℝ)
    (hs : 0 < s) (hA : 0 ≤ A)
    (hJ : ∀ j ∈ J, (((n - (j.val + 1) : ℕ) : ℝ)) * s < A) :
    (J.card : ℝ) ≤ A / s + 1 ∧
      ((∀ j ∈ J, 0 < (((n - (j.val + 1) : ℕ) : ℝ)) * s) →
        (J.card : ℝ) ≤ A / s) := by
  classical
  let K : Finset ℕ := J.image (fun j => n - (j.val + 1))
  have hinj : Function.Injective (fun j : Fin n => n - (j.val + 1)) := by
    intro j k hjk
    change n - (j.val + 1) = n - (k.val + 1) at hjk
    apply Fin.ext
    have hj := j.is_lt
    have hk := k.is_lt
    omega
  have hcard : K.card = J.card := Finset.card_image_of_injective J hinj
  by_cases hne : K.Nonempty
  · let z : ℕ := K.max' hne
    obtain ⟨j, hj, hz⟩ := Finset.mem_image.1 (Finset.max'_mem K hne)
    have hzs : (z : ℝ) * s < A := by simpa only [z, ← hz] using hJ j hj
    have hzA : (z : ℝ) < A / s := (lt_div_iff₀ hs).2 hzs
    have hbound : K.card ≤ z + 1 := by
      simpa only [Finset.card_range] using Finset.card_le_card
        (show K ⊆ Finset.range (z + 1) from
          fun k hk => Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_max' K k hk)))
    have hbound' : (J.card : ℝ) ≤ (z : ℝ) + 1 := by exact_mod_cast hcard ▸ hbound
    refine ⟨by linarith, ?_⟩
    intro hpos
    have hbound2 : K.card ≤ z := by
      have hsub : K ⊆ Finset.Ico 1 (z + 1) := by
        intro k hk
        obtain ⟨r, hr, hkr⟩ := Finset.mem_image.1 hk
        have hkrpos := hpos r hr
        have hkpos : 0 < k := by
          by_contra hbad
          have hkzero : k = 0 := by omega
          rw [hkr, hkzero] at hkrpos
          simp at hkrpos
        exact Finset.mem_Ico.2 ⟨hkpos, Nat.lt_succ_of_le (Finset.le_max' K k hk)⟩
      simpa using Finset.card_le_card hsub
    have hbound2' : (J.card : ℝ) ≤ (z : ℝ) := by exact_mod_cast hcard ▸ hbound2
    exact hbound2'.trans hzA.le
  · have hzero : J.card = 0 := by
      rw [← hcard, Finset.not_nonempty_iff_eq_empty.1 hne]
      rfl
    simp only [hzero, Nat.cast_zero]
    have ha := div_nonneg hA hs.le
    exact ⟨by linarith, fun _ => ha⟩

private theorem br_large_push_markov
    {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    (U D : α → ℝ) (hU : Measurable U) (hD : Measurable D)
    (hUn : ∀ a, 0 ≤ U a) (hD01 : ∀ a, 0 ≤ D a ∧ D a ≤ 1)
    (hU2 : Integrable (fun a => (U a) ^ 2) P) (y : ℝ) (hy : 0 < y) :
    (∫ a, (if y / 16 < U a then D a else 0) ∂P) ≤
      (P {a | y / 16 < U a}).toReal ∧
      (P {a | y / 16 < U a}).toReal ≤
        256 / y ^ 2 * (∫ a, (U a) ^ 2 ∂P) := by
  classical
  have hS : MeasurableSet {a | y / 16 < U a} := measurableSet_lt measurable_const hU
  have hDi := (br_unit_integrable P D hD hD01).1
  have hmask : Integrable (fun a => if y / 16 < U a then D a else 0) P := by
    refine (br_unit_integrable P _ (Measurable.ite hS hD measurable_const) ?_).1
    intro a
    split_ifs
    · exact hD01 a
    · simp
  have hOne : Integrable (fun a => if y / 16 < U a then (1 : ℝ) else 0) P := by
    refine (br_unit_integrable P _ (Measurable.ite hS measurable_const measurable_const) ?_).1
    intro a
    split_ifs <;> norm_num
  have hprob : (∫ a, (if y / 16 < U a then (1 : ℝ) else 0) ∂P) =
      (P {a | y / 16 < U a}).toReal := by
    simpa only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply, measureReal_def] using
      (integral_indicator_one (μ := P) hS)
  refine ⟨?_, ?_⟩
  · rw [← hprob]
    apply integral_mono hmask hOne
    intro a
    change (if y / 16 < U a then D a else 0) ≤ (if y / 16 < U a then 1 else 0)
    split_ifs <;> simp_all only [le_refl]
  · rw [← hprob, ← integral_const_mul]
    apply integral_mono hOne (hU2.const_mul (256 / y ^ 2))
    intro a
    change (if y / 16 < U a then (1 : ℝ) else 0) ≤ 256 / y ^ 2 * (U a) ^ 2
    split_ifs with ha
    · rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (sq_pos_of_pos hy)).2
      have hUa := hUn a
      nlinarith
    · positivity

theorem sourceTruncation_lindleyDelta_large_push_sum :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun a : ℝ => a ^ 2) ν0 →
          (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1 →
          (∫ a : ℝ, a ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 2 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            let ρ : Measure ℝ :=
              ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
            let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
            let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ρ)
            ∀ y : ℝ, 0 < y →
              let ψ : ℝ × ℝ → ℝ := fun p =>
                ∫ z : ℝ × ℝ,
                  sourceFourierTest y (p.1 + z.1, p.2 + z.2)
                  ∂quadraticFullNoiseLaw ρ
              let T : Fin n → ℝ := fun j =>
                (((n - (j.val + 1) : ℕ) : ℝ)) * m2
              let J : Finset (Fin n) := Finset.univ.filter
                (fun j => n / 2 < j.val + 1 ∧ 0 < T j ∧ T j < y ^ 2)
              (∑ j ∈ J,
                ∫ a : Shao.Path n,
                  (if y / 16 < lindleyRegulator a j then
                    |lindleyDelta ρ ψ a j| else 0) ∂P) ≤
                (∑ j ∈ J,
                  (P {a : Shao.Path n | y / 16 < lindleyRegulator a j}).toReal) ∧
              (∑ j ∈ J,
                (P {a : Shao.Path n | y / 16 < lindleyRegulator a j}).toReal) ≤
                  C * (n : ℝ) * m3 := by
  classical
  let B : ℝ := 96 * Real.exp (7 + 3 * (1024 : ℝ))
  refine ⟨512 * B, by dsimp [B]; positivity, ?_⟩
  intro ν0 hp n h2 hn hm x epsilon hx he he2 hR
  letI := hp
  dsimp only
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
  let s : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
  let b : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ρ)
  obtain ⟨_, _, hpρ, hsρ, _, _, h3ρ, _⟩ :=
    Shao.sourceTruncation_law_data ν0 n h2 hn x epsilon hx he he2 hR
  letI : IsProbabilityMeasure ρ := hpρ
  obtain ⟨_, hs, hb, hV, _, _, hslo, _, _, _, _⟩ :=
    br_source_scale ν0 n h2 hn hm x epsilon hx he he2 hR
  letI : IsProbabilityMeasure (quadraticFullNoiseLaw ρ) :=
    (quadraticFullNoise_law_data ρ h3ρ hV (epsilon / (1 + x)) (by positivity) hsρ).2.2.1
  intro y hy
  let ψ : ℝ × ℝ → ℝ := fun p => ∫ z : ℝ × ℝ,
    sourceFourierTest y (p.1 + z.1, p.2 + z.2) ∂quadraticFullNoiseLaw ρ
  let T : Fin n → ℝ := fun j => (((n - (j.val + 1) : ℕ) : ℝ)) * s
  let J : Finset (Fin n) := Finset.univ.filter
    (fun j => n / 2 < j.val + 1 ∧ 0 < T j ∧ T j < y ^ 2)
  change (∑ j ∈ J, ∫ a : Shao.Path n,
    (if y / 16 < lindleyRegulator a j then |lindleyDelta ρ ψ a j| else 0) ∂P) ≤ _ ∧ _
  have hψ := br_smoothed_data ρ y
  have hmark (j : Fin n) := br_large_push_markov P
    (fun a => lindleyRegulator a j) (fun a => |lindleyDelta ρ ψ a j|)
    (br_regulator_measurable j) (br_delta_data ρ n ψ hψ.1 hψ.2.1 j).1
    (fun a => le_max_right _ _) (br_delta_data ρ n ψ hψ.1 hψ.2.1 j).2.1
    (sourceTruncation_lindleyRegulator_second_moment ν0 n h2 hn hm x epsilon hx he he2 hR j).1 y hy
  refine ⟨Finset.sum_le_sum (fun j _ => (hmark j).1), ?_⟩
  have hcard : (J.card : ℝ) ≤ y ^ 2 / s :=
    (br_clock_card J s (y ^ 2) hs (sq_nonneg y)
      (fun j hj => (Finset.mem_filter.1 hj).2.2.2)).2
      (fun j hj => (Finset.mem_filter.1 hj).2.2.1)
  have hcarddiv : (J.card : ℝ) / y ^ 2 ≤ 1 / s :=
    (div_le_div_iff₀ (sq_pos_of_pos hy) hs).2
      (by simpa only [one_mul] using (le_div_iff₀ hs).1 hcard)
  have hinv : 1 / s ≤ (4 / 3 : ℝ) * n := (div_le_iff₀ hs).2 (by nlinarith only [hslo])
  calc
    _ ≤ ∑ j ∈ J, (256 / y ^ 2) * (B * b) := by
      apply Finset.sum_le_sum
      intro j hj
      apply (hmark j).2.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (br_source_late_moments ν0 n h2 hn hm x epsilon hx he he2 hR j
        (Finset.mem_filter.1 hj).2.1).2
    _ = 256 * B * b * ((J.card : ℝ) / y ^ 2) := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ 256 * B * b * (1 / s) := mul_le_mul_of_nonneg_left hcarddiv (by dsimp [B]; positivity)
    _ ≤ 256 * B * b * ((4 / 3 : ℝ) * n) := mul_le_mul_of_nonneg_left hinv (by dsimp [B]; positivity)
    _ ≤ 512 * B * (n : ℝ) * b := by
      have hNb : 0 ≤ B * (n : ℝ) * b := by dsimp [B]; positivity
      nlinarith only [hNb]

theorem sourceTruncation_lindleyDelta_micro_clock_sum :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun a : ℝ => a ^ 2) ν0 →
          (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1 →
          (∫ a : ℝ, a ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 2 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            let ρ : Measure ℝ :=
              ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
            let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
            let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
            let gamma : ℝ := m3 / variance (id : ℝ → ℝ) ρ
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ρ)
            ∀ L y : ℝ, 1 ≤ L → 0 ≤ y →
              let ψ : ℝ × ℝ → ℝ := fun p =>
                ∫ z : ℝ × ℝ,
                  sourceFourierTest y (p.1 + z.1, p.2 + z.2)
                  ∂quadraticFullNoiseLaw ρ
              let T : Fin n → ℝ := fun j =>
                (((n - (j.val + 1) : ℕ) : ℝ)) * m2
              let J : Finset (Fin n) := Finset.univ.filter
                (fun j => n / 2 < j.val + 1 ∧ T j < L * gamma ^ 2)
              (∑ j ∈ J, ∫ a : Shao.Path n, |lindleyDelta ρ ψ a j| ∂P) ≤
                C * (L + 1) * ((n : ℝ) * m3) := by
  classical
  obtain ⟨Cr, hCr, hrough⟩ := sourceFutureNoiseKernel_scalar_rough_bounds
  refine ⟨16 * Cr, by positivity, ?_⟩
  intro ν0 hp n h2 hn hm x epsilon hx he he2 hR
  letI := hp
  dsimp only
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
  let s : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
  let b : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
  let gamma : ℝ := b / variance (id : ℝ → ℝ) ρ
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ρ)
  obtain ⟨_, _, hpρ, hsρ, _, h2ρ, h3ρ, _⟩ :=
    Shao.sourceTruncation_law_data ν0 n h2 hn x epsilon hx he he2 hR
  letI : IsProbabilityMeasure ρ := hpρ
  obtain ⟨hn0, hs, hb, hV, hg, hsg, hslo, _, _, _, _⟩ :=
    br_source_scale ν0 n h2 hn hm x epsilon hx he he2 hR
  change 0 < s at hs
  change 0 < gamma at hg
  change s ≤ gamma ^ 2 at hsg
  have hN : (0 : ℝ) < n := by exact_mod_cast hn0
  obtain ⟨_, _, _, _, _, _, hgammaHi, _, _⟩ :=
    Shao.sourceTruncation_gamma_bounds ν0 n h2 hn hm x epsilon hx he he2 hR
  letI : IsProbabilityMeasure (quadraticFullNoiseLaw ρ) :=
    (quadraticFullNoise_law_data ρ h3ρ hV (epsilon / (1 + x)) (by positivity) hsρ).2.2.1
  intro L y hL hy
  let ψ : ℝ × ℝ → ℝ := fun p => ∫ z : ℝ × ℝ,
    sourceFourierTest y (p.1 + z.1, p.2 + z.2) ∂quadraticFullNoiseLaw ρ
  let T : Fin n → ℝ := fun j => (((n - (j.val + 1) : ℕ) : ℝ)) * s
  let J : Finset (Fin n) := Finset.univ.filter
    (fun j => n / 2 < j.val + 1 ∧ T j < L * gamma ^ 2)
  change (∑ j ∈ J, ∫ a : Shao.Path n, |lindleyDelta ρ ψ a j| ∂P) ≤
    16 * Cr * (L + 1) * ((n : ℝ) * b)
  have hψ := br_smoothed_data ρ y
  have hshift (j : Fin n) (a : Shao.Path n) :
      |lindleyDelta ρ ψ a j| ≤ Cr / gamma * lindleyRegulator a j := by
    have hlip := (hrough ρ hpρ h3ρ hV (epsilon / (1 + x)) (by positivity) hsρ
      (n - (j.val + 1)) y hy).2 (Shao.prefixSquares a (j.val + 1))
    dsimp [lindleyDelta]
    rw [hψ.2.2, hψ.2.2]
    have hU : 0 ≤ lindleyRegulator a j := le_max_right _ _
    simpa only [zero_sub, neg_neg, abs_of_nonneg hU] using
      hlip.2 0 (-lindleyRegulator a j)
  have hterm (j : Fin n) (hj : j ∈ J) :
      (∫ a : Shao.Path n, |lindleyDelta ρ ψ a j| ∂P) ≤ Cr / gamma * (4 / (n : ℝ)) := by
    have hu := iid_lindleyRegulator_prefix_first_moment ρ h2ρ n j
    calc
      _ ≤ ∫ a : Shao.Path n, Cr / gamma * lindleyRegulator a j ∂P :=
        integral_mono (br_delta_data ρ n ψ hψ.1 hψ.2.1 j).2.2
          (hu.1.const_mul _) (hshift j)
      _ = Cr / gamma * (∫ a : Shao.Path n, lindleyRegulator a j ∂P) := integral_const_mul _ _
      _ ≤ Cr / gamma * (4 / (n : ℝ)) := mul_le_mul_of_nonneg_left
        (br_source_late_moments ν0 n h2 hn hm x epsilon hx he he2 hR j
          (Finset.mem_filter.1 hj).2.1).1 (by positivity)
  have hbase : (J.card : ℝ) ≤ L * gamma ^ 2 / s + 1 :=
    (br_clock_card J s (L * gamma ^ 2) hs (by positivity)
      (fun j hj => (Finset.mem_filter.1 hj).2.2)).1
  have hcard : (J.card : ℝ) ≤ (L + 1) * gamma ^ 2 / s := by
    have hmul := mul_le_mul_of_nonneg_right hbase hs.le
    have heq : (L * gamma ^ 2 / s + 1) * s = L * gamma ^ 2 + s := by
      field_simp [ne_of_gt hs]
    apply (le_div_iff₀ hs).2
    rw [heq] at hmul
    nlinarith only [hmul, hsg]
  have hinv : 1 / s ≤ (4 / 3 : ℝ) * n := (div_le_iff₀ hs).2 (by nlinarith only [hslo])
  have hcardN : (J.card : ℝ) ≤ (4 / 3 : ℝ) * (L + 1) * (n : ℝ) * gamma ^ 2 := by
    apply hcard.trans
    calc
      _ = (L + 1) * gamma ^ 2 * (1 / s) := by ring
      _ ≤ (L + 1) * gamma ^ 2 * ((4 / 3 : ℝ) * n) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ j ∈ J, Cr / gamma * (4 / (n : ℝ)) := Finset.sum_le_sum hterm
    _ = (J.card : ℝ) * (Cr / gamma * (4 / (n : ℝ))) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((4 / 3 : ℝ) * (L + 1) * (n : ℝ) * gamma ^ 2) * (Cr / gamma * (4 / (n : ℝ))) :=
      mul_le_mul_of_nonneg_right hcardN (by positivity)
    _ = (16 / 3 : ℝ) * Cr * (L + 1) * gamma := by
      field_simp [ne_of_gt hg, ne_of_gt hN]
      <;> ring
    _ ≤ (16 / 3 : ℝ) * Cr * (L + 1) * (2 * (n : ℝ) * b) :=
      mul_le_mul_of_nonneg_left hgammaHi (by positivity)
    _ ≤ 16 * Cr * (L + 1) * ((n : ℝ) * b) := by
      have hprod : 0 ≤ Cr * (L + 1) * ((n : ℝ) * b) := by positivity
      nlinarith only [hprod]

private theorem br_reciprocal_sqrt_step (n : ℕ) :
    1 / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤
      2 * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  apply (div_le_iff₀ (Real.sqrt_pos.2 hnp)).2
  have ha2 := Real.sq_sqrt hn
  have hb2 := Real.sq_sqrt hnp.le
  have hd := sq_nonneg (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ))
  norm_num only [Nat.cast_add, Nat.cast_one] at *
  nlinarith

private theorem br_reciprocal_sqrt_sum (N : ℕ) :
    (∑ i : Fin N, 1 / Real.sqrt ((i.val + 1 : ℕ) : ℝ)) ≤
      2 * Real.sqrt (N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    calc
      _ ≤ 2 * Real.sqrt (N : ℝ) +
          2 * (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt (N : ℝ)) :=
        add_le_add ih (br_reciprocal_sqrt_step N)
      _ = _ := by ring

private theorem br_total_roots (N V : ℝ) (hN : 0 < N) (hV : 0 < V)
    (hlo : (1 / 2 : ℝ) ≤ N * V) (hhi : N * V ≤ 4 / 3) :
    Real.sqrt V * Real.sqrt N ≤ 2 ∧ Real.sqrt N / Real.sqrt V ≤ 2 * N := by
  have hv := Real.sqrt_nonneg V
  have hn := Real.sqrt_nonneg N
  have hv2 := Real.sq_sqrt hV.le
  have hn2 := Real.sq_sqrt hN.le
  have hp2 : (Real.sqrt V * Real.sqrt N) ^ 2 = V * N := by rw [mul_pow, hv2, hn2]
  refine ⟨by nlinarith [mul_nonneg hv hn], ?_⟩
  apply (div_le_iff₀ (Real.sqrt_pos.2 hV)).2
  have hlo' := mul_le_mul_of_nonneg_left hlo (show 0 ≤ 4 * N by positivity)
  have hsq : (Real.sqrt N) ^ 2 ≤ (2 * N * Real.sqrt V) ^ 2 := by
    rw [hn2, mul_pow, mul_pow, hv2]
    nlinarith only [hlo', hN]
  nlinarith [mul_nonneg (show 0 ≤ 2 * N by positivity) hv]

private theorem br_source_total_moments
    (ν0 : Measure ℝ) [IsProbabilityMeasure ν0] (n : ℕ)
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν0)
    (hn : (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1)
    (hm : (∫ a : ℝ, a ∂ν0) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x) (he : 0 < epsilon) (he2 : epsilon ≤ 1 / 2)
    (hR : Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8) :
    let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
    let b : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ρ)
    (∑ j : Fin n, ∫ a : Shao.Path n, lindleyRegulator a j ∂P) ≤ 5 ∧
      (∑ j : Fin n, ∫ a : Shao.Path n, (lindleyRegulator a j) ^ 2 ∂P) ≤
        (256 * Real.exp (7 + 3 * (1024 : ℝ))) * ((n : ℝ) * b) := by
  classical
  dsimp only
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
  let b : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
  let V : ℝ := variance (id : ℝ → ℝ) ρ
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ρ)
  obtain ⟨_, _, hpρ, _, _, h2ρ, _, _⟩ :=
    Shao.sourceTruncation_law_data ν0 n h2 hn x epsilon hx he he2 hR
  letI : IsProbabilityMeasure ρ := hpρ
  obtain ⟨hn0, _, hb, hV, _, _, _, _, hVlo, hVhi, hmu⟩ :=
    br_source_scale ν0 n h2 hn hm x epsilon hx he he2 hR
  have hN : (0 : ℝ) < n := by exact_mod_cast hn0
  obtain ⟨hroot, hratio⟩ := br_total_roots (n : ℝ) V hN hV hVlo hVhi
  constructor
  · have hf := iid_lindleyRegulator_sum_first_moment ρ h2ρ n
    dsimp only at hf
    have hi (j : Fin n) := (iid_lindleyRegulator_prefix_first_moment ρ h2ρ n j).1
    rw [integral_finsetSum Finset.univ (fun j _ => hi j)] at hf
    exact hf.2.trans (by nlinarith only [hroot, hmu])
  · let A : ℝ := 48 * Real.exp (7 + 3 * (1024 : ℝ))
    have hsum := br_reciprocal_sqrt_sum n
    calc
      _ ≤ ∑ j : Fin n, A * b / (Real.sqrt V * Real.sqrt ((j.val + 1 : ℕ) : ℝ)) :=
        Finset.sum_le_sum (fun j _ => (sourceTruncation_lindleyRegulator_second_moment
          ν0 n h2 hn hm x epsilon hx he he2 hR j).2)
      _ = A * b / Real.sqrt V * (∑ j : Fin n, 1 / Real.sqrt ((j.val + 1 : ℕ) : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ A * b / Real.sqrt V * (2 * Real.sqrt (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum (by dsimp [A]; positivity)
      _ = 2 * A * b * (Real.sqrt (n : ℝ) / Real.sqrt V) := by ring
      _ ≤ 2 * A * b * (2 * (n : ℝ)) := mul_le_mul_of_nonneg_left hratio (by dsimp [A]; positivity)
      _ ≤ (256 * Real.exp (7 + 3 * (1024 : ℝ))) * ((n : ℝ) * b) := by
        dsimp only [A]
        have hprod : 0 ≤ Real.exp (7 + 3 * (1024 : ℝ)) * ((n : ℝ) * b) := by positivity
        nlinarith only [hprod]

private theorem br_even_odd_shift (f : ℝ → ℝ) (O E u : ℝ) (hO : 0 ≤ O)
    (hE : 0 ≤ E) (hu : 0 ≤ u)
    (hd : ∀ w : ℝ,
      DifferentiableAt ℝ (fun t => (f t - f (-t)) / 2) w ∧
        DifferentiableAt ℝ (fun t => (f t + f (-t)) / 2) w ∧
        DifferentiableAt ℝ (fun r => deriv (fun t => (f t + f (-t)) / 2) r) w)
    (hb : ∀ w : ℝ,
      |deriv (fun t => (f t - f (-t)) / 2) w| ≤ O ∧
        |deriv (fun r => deriv (fun t => (f t + f (-t)) / 2) r) w| ≤ E) :
    |f 0 - f (-u)| ≤ u * O + u ^ 2 * E := by
  let o : ℝ → ℝ := fun t => (f t - f (-t)) / 2
  let e : ℝ → ℝ := fun t => (f t + f (-t)) / 2
  have ho0 : o 0 = 0 := by simp [o]
  have heven (t : ℝ) : e (-t) = e t := by dsimp [e]; ring
  have he0 : deriv e 0 = 0 := by
    have hdneg : HasDerivAt e (deriv e 0) (-(0 : ℝ)) := by
      simpa only [neg_zero] using (hd 0).2.1.hasDerivAt
    have hh := hdneg.comp 0 ((hasDerivAt_id (0 : ℝ)).neg)
    have heq : (fun t => e (-t)) = e := funext heven
    change HasDerivAt (fun t => e (-t)) (deriv e 0 * -1) 0 at hh
    rw [heq] at hh
    have huniq := hh.unique (hd 0).2.1.hasDerivAt
    linarith
  have hodd : |o u| ≤ O * u := by
    have hh := (convex_Icc (0 : ℝ) u).norm_image_sub_le_of_norm_deriv_le
      (fun w _ => (hd w).1) (fun w _ => by simpa only [Real.norm_eq_abs] using (hb w).1)
      (show (0 : ℝ) ∈ Set.Icc 0 u from ⟨le_rfl, hu⟩) (show u ∈ Set.Icc 0 u from ⟨hu, le_rfl⟩)
    change |o u - o 0| ≤ O * |u - 0| at hh
    simpa only [Real.norm_eq_abs, ho0, sub_zero, abs_of_nonneg hu] using hh
  have heder (w : ℝ) (hw : w ∈ Set.Icc 0 u) : |deriv e w| ≤ E * u := by
    have hh := (convex_Icc (0 : ℝ) u).norm_image_sub_le_of_norm_deriv_le
      (fun z _ => (hd z).2.2) (fun z _ => by simpa only [Real.norm_eq_abs] using (hb z).2)
      (show (0 : ℝ) ∈ Set.Icc 0 u from ⟨le_rfl, hu⟩) hw
    change |deriv e w - deriv e 0| ≤ E * |w - 0| at hh
    have hh' : |deriv e w| ≤ E * w := by
      simpa only [Real.norm_eq_abs, he0, sub_zero, abs_of_nonneg hw.1] using hh
    exact hh'.trans (mul_le_mul_of_nonneg_left hw.2 hE)
  have hevenb : |e u - e 0| ≤ E * u * u := by
    have hh := (convex_Icc (0 : ℝ) u).norm_image_sub_le_of_norm_deriv_le
      (fun w _ => (hd w).2.1) (fun w hw => by simpa only [Real.norm_eq_abs] using heder w hw)
      (show (0 : ℝ) ∈ Set.Icc 0 u from ⟨le_rfl, hu⟩) (show u ∈ Set.Icc 0 u from ⟨hu, le_rfl⟩)
    change |e u - e 0| ≤ E * u * |u - 0| at hh
    simpa only [sub_zero, abs_of_nonneg hu] using hh
  have hid : f 0 - f (-u) = -(e u - e 0) + o u := by dsimp [e, o]; ring
  rw [hid]
  calc
    _ ≤ |-(e u - e 0)| + |o u| := abs_add_le _ _
    _ ≤ E * u * u + O * u := add_le_add (by simpa only [abs_neg] using hevenb) hodd
    _ = _ := by ring

private theorem br_long_grid_step (s : ℝ) (hs : 0 < s) (k : ℕ) (hk : 1 ≤ k) :
    s / (Real.sqrt ((k : ℝ) * s)) ^ 3 ≤
      4 * (1 / Real.sqrt ((k : ℝ) * s) - 1 / Real.sqrt (((k + 1 : ℕ) : ℝ) * s)) := by
  let r : ℝ := Real.sqrt ((k : ℝ) * s)
  let t : ℝ := Real.sqrt (((k + 1 : ℕ) : ℝ) * s)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  have ht : 0 < t := Real.sqrt_pos.2 (by positivity)
  have hr2 : r ^ 2 = (k : ℝ) * s := Real.sq_sqrt (by positivity)
  have ht2 : t ^ 2 = ((k : ℝ) + 1) * s := by
    simpa only [t, Nat.cast_add, Nat.cast_one] using Real.sq_sqrt
      (show 0 ≤ (((k + 1 : ℕ) : ℝ) * s) by positivity)
  have hdiff : 0 ≤ t - r := sub_nonneg.2 (Real.sqrt_le_sqrt (by
    norm_num only [Nat.cast_add, Nat.cast_one]; nlinarith only [hs]))
  have hid : (r + t) * (t - r) = s := by nlinarith only [hr2, ht2]
  have hbound : t * (r + t) ≤ 4 * r ^ 2 := by
    nlinarith [sq_nonneg (r - t)]
  have hmul := mul_le_mul_of_nonneg_right hbound hdiff
  have hmain : t * s ≤ 4 * r ^ 2 * (t - r) := by
    calc
      t * s = (t * (r + t)) * (t - r) := by rw [mul_assoc, hid]
      _ ≤ _ := hmul
  change s / r ^ 3 ≤ 4 * (1 / r - 1 / t)
  apply (div_le_iff₀ (pow_pos hr 3)).2
  have heq : 4 * (1 / r - 1 / t) * r ^ 3 = (4 * r ^ 2 * (t - r)) / t := by
    field_simp [hr.ne', ht.ne']
    <;> ring
  rw [heq]
  exact (le_div_iff₀ ht).2 (by simpa only [mul_comm] using hmain)

private theorem br_reciprocal_sqrt_nat_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), 1 / Real.sqrt (k : ℝ)) ≤ 2 * Real.sqrt (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc
      _ ≤ 2 * Real.sqrt (n : ℝ) +
          2 * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)) :=
        add_le_add ih (br_reciprocal_sqrt_step n)
      _ = _ := by ring

private theorem br_long_grid (n : ℕ) (K : Finset ℕ) (s y : ℝ)
    (hs : 0 < s) (hy : 0 < y) (hns : (n : ℝ) * s ≤ 4 / 3)
    (hK : ∀ k ∈ K, k ≤ n ∧ y ^ 2 ≤ (k : ℝ) * s) :
    s * (∑ k ∈ K, 1 / Real.sqrt ((k : ℝ) * s)) ≤ 4 ∧
      s * (∑ k ∈ K, 1 / (Real.sqrt ((k : ℝ) * s)) ^ 3) ≤ 4 / y := by
  classical
  have hsub : K ⊆ Finset.range (n + 1) := fun k hk =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (hK k hk).1)
  have hfirst : (∑ k ∈ K, 1 / Real.sqrt (k : ℝ)) ≤ 2 * Real.sqrt (n : ℝ) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans
      (br_reciprocal_sqrt_nat_sum n)
  have hsroot : s / Real.sqrt s = Real.sqrt s := by
    apply (div_eq_iff (Real.sqrt_pos.2 hs).ne').2
    nlinarith only [Real.sq_sqrt hs.le]
  have hprod2 : (Real.sqrt s * Real.sqrt (n : ℝ)) ^ 2 = s * (n : ℝ) := by
    rw [mul_pow, Real.sq_sqrt hs.le, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hprod : Real.sqrt s * Real.sqrt (n : ℝ) ≤ 2 := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg s) (Real.sqrt_nonneg (n : ℝ))]
  refine ⟨?_, ?_⟩
  · calc
      _ = s / Real.sqrt s * (∑ k ∈ K, 1 / Real.sqrt (k : ℝ)) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [Real.sqrt_mul (Nat.cast_nonneg k)]
        ring
      _ = Real.sqrt s * (∑ k ∈ K, 1 / Real.sqrt (k : ℝ)) := by rw [hsroot]
      _ ≤ Real.sqrt s * (2 * Real.sqrt (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hfirst (Real.sqrt_nonneg s)
      _ ≤ 4 := by nlinarith only [hprod]
  · by_cases hne : K.Nonempty
    · let a : ℕ := K.min' hne
      have ha : a ∈ K := Finset.min'_mem K hne
      have han : a ≤ n := (hK a ha).1
      have hay : y ^ 2 ≤ (a : ℝ) * s := (hK a ha).2
      have ha0 : 1 ≤ a := by
        by_contra hbad
        have hz : a = 0 := by omega
        simp only [hz, Nat.cast_zero, zero_mul] at hay
        nlinarith only [hay, sq_pos_of_pos hy]
      have hKI : K ⊆ Finset.Ico a (n + 1) := fun k hk =>
        Finset.mem_Ico.2 ⟨Finset.min'_le K k hk, Nat.lt_succ_of_le (hK k hk).1⟩
      have haR : 0 < Real.sqrt ((a : ℝ) * s) := Real.sqrt_pos.2 (by positivity)
      have hya : y ≤ Real.sqrt ((a : ℝ) * s) := by
        nlinarith [Real.sq_sqrt (show 0 ≤ (a : ℝ) * s by positivity), Real.sqrt_nonneg ((a : ℝ) * s)]
      have htel : (∑ k ∈ Finset.Ico a (n + 1),
          (1 / Real.sqrt ((k : ℝ) * s) - 1 / Real.sqrt (((k + 1 : ℕ) : ℝ) * s))) =
          1 / Real.sqrt ((a : ℝ) * s) - 1 / Real.sqrt (((n + 1 : ℕ) : ℝ) * s) := by
        simpa only [neg_sub_neg] using Finset.sum_Ico_sub
          (f := fun k : ℕ => -(1 / Real.sqrt ((k : ℝ) * s))) (Nat.le_succ_of_le han)
      calc
        _ ≤ s * (∑ k ∈ Finset.Ico a (n + 1), 1 / (Real.sqrt ((k : ℝ) * s)) ^ 3) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg hKI (fun _ _ _ => by positivity)) hs.le
        _ = ∑ k ∈ Finset.Ico a (n + 1), s / (Real.sqrt ((k : ℝ) * s)) ^ 3 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ ≤ ∑ k ∈ Finset.Ico a (n + 1),
            4 * (1 / Real.sqrt ((k : ℝ) * s) - 1 / Real.sqrt (((k + 1 : ℕ) : ℝ) * s)) :=
          Finset.sum_le_sum (fun k hk => br_long_grid_step s hs k
            (ha0.trans (Finset.mem_Ico.1 hk).1))
        _ = 4 * (1 / Real.sqrt ((a : ℝ) * s) - 1 / Real.sqrt (((n + 1 : ℕ) : ℝ) * s)) := by
          rw [← Finset.mul_sum, htel]
        _ ≤ 4 * (1 / Real.sqrt ((a : ℝ) * s)) := by
          have hh : 0 ≤ 1 / Real.sqrt (((n + 1 : ℕ) : ℝ) * s) := by positivity
          linarith only [hh]
        _ ≤ 4 * (1 / y) := by gcongr
        _ = 4 / y := by ring
    · simp only [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty, mul_zero]
      positivity

private theorem br_remaining_sum_le (n : ℕ) (J : Finset (Fin n)) (f : ℕ → ℝ)
    (K : Finset ℕ) (hf : ∀ k, 0 ≤ f k)
    (hJK : ∀ j ∈ J, n - (j.val + 1) ∈ K) :
    (∑ j ∈ J, f (n - (j.val + 1))) ≤ ∑ k ∈ K, f k := by
  classical
  have hinj : Function.Injective (fun j : Fin n => n - (j.val + 1)) := by
    intro j k hjk
    change n - (j.val + 1) = n - (k.val + 1) at hjk
    apply Fin.ext
    have hj := j.is_lt
    have hk := k.is_lt
    omega
  have hsub : J.image (fun j => n - (j.val + 1)) ⊆ K := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hk
    exact hJK j hj
  rw [← Finset.sum_image (fun j _ k _ hjk => hinj hjk)]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => hf k)

private theorem br_index_sum_le (n : ℕ) (J : Finset (Fin n)) (f : ℕ → ℝ)
    (K : Finset ℕ) (hf : ∀ k, 0 ≤ f k)
    (hJK : ∀ j ∈ J, j.val + 1 ∈ K) :
    (∑ j ∈ J, f (j.val + 1)) ≤ ∑ k ∈ K, f k := by
  classical
  have hsub : J.image (fun j => j.val + 1) ⊆ K := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hk
    exact hJK j hj
  rw [← Finset.sum_image (fun j _ k _ hjk => by apply Fin.ext; omega)]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => hf k)

private theorem br_taylor_integral (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (ψ : ℝ × ℝ → ℝ) (hψ : Measurable ψ)
    (h01 : ∀ p, 0 ≤ ψ p ∧ ψ p ≤ 1) (y : ℝ)
    (hbridge : ∀ m p, lindleyFutureKernel ν m ψ p = sourceFutureNoiseKernel ν m y p)
    (j : Fin n) (O E : ℝ) (hO : 0 ≤ O) (hE : 0 ≤ E)
    (hU : Integrable (fun a : Shao.Path n => lindleyRegulator a j)
      (Measure.pi (fun _ : Fin n => ν)))
    (hU2 : Integrable (fun a : Shao.Path n => (lindleyRegulator a j) ^ 2)
      (Measure.pi (fun _ : Fin n => ν)))
    (hd : ∀ w q : ℝ,
      DifferentiableAt ℝ (fun t => (sourceFutureNoiseKernel ν (n - (j.val + 1)) y (t, q) -
        sourceFutureNoiseKernel ν (n - (j.val + 1)) y (-t, q)) / 2) w ∧
      DifferentiableAt ℝ (fun t => (sourceFutureNoiseKernel ν (n - (j.val + 1)) y (t, q) +
        sourceFutureNoiseKernel ν (n - (j.val + 1)) y (-t, q)) / 2) w ∧
      DifferentiableAt ℝ (fun r => deriv (fun t =>
        (sourceFutureNoiseKernel ν (n - (j.val + 1)) y (t, q) +
          sourceFutureNoiseKernel ν (n - (j.val + 1)) y (-t, q)) / 2) r) w)
    (hb : ∀ w q : ℝ,
      |deriv (fun t => (sourceFutureNoiseKernel ν (n - (j.val + 1)) y (t, q) -
        sourceFutureNoiseKernel ν (n - (j.val + 1)) y (-t, q)) / 2) w| ≤ O ∧
      |deriv (fun r => deriv (fun t =>
        (sourceFutureNoiseKernel ν (n - (j.val + 1)) y (t, q) +
          sourceFutureNoiseKernel ν (n - (j.val + 1)) y (-t, q)) / 2) r) w| ≤ E) :
    (∫ a : Shao.Path n, |lindleyDelta ν ψ a j| ∂Measure.pi (fun _ : Fin n => ν)) ≤
      O * (∫ a : Shao.Path n, lindleyRegulator a j ∂Measure.pi (fun _ : Fin n => ν)) +
      E * (∫ a : Shao.Path n, (lindleyRegulator a j) ^ 2 ∂Measure.pi (fun _ : Fin n => ν)) := by
  have hp (a : Shao.Path n) : |lindleyDelta ν ψ a j| ≤
      O * lindleyRegulator a j + E * (lindleyRegulator a j) ^ 2 := by
    have hh := br_even_odd_shift
      (fun w => sourceFutureNoiseKernel ν (n - (j.val + 1)) y
        (w, Shao.prefixSquares a (j.val + 1))) O E (lindleyRegulator a j)
      hO hE (le_max_right _ _) (fun w => hd w _) (fun w => hb w _)
    dsimp only [lindleyDelta]
    rw [hbridge, hbridge]
    convert hh using 1 <;> ring
  have hi := integral_mono (br_delta_data ν n ψ hψ h01 j).2.2
    ((hU.const_mul O).add (hU2.const_mul E)) hp
  simp only [Pi.add_apply] at hi
  simpa only [integral_add (hU.const_mul O) (hU2.const_mul E), integral_const_mul] using hi

private theorem br_sum_cover {α : Type*} [Fintype α] [DecidableEq α]
    (d : α → ℝ) (hd : ∀ a, 0 ≤ d a) (E L S M : Finset α)
    (hcover : ∀ a, a ∈ E ∨ a ∈ L ∨ a ∈ S ∨ a ∈ M) :
    (∑ a : α, d a) ≤ (∑ a ∈ E, d a) + (∑ a ∈ L, d a) +
      (∑ a ∈ S, d a) + ∑ a ∈ M, d a := by
  classical
  have hp (a : α) : d a ≤
      (if a ∈ E then d a else 0) + (if a ∈ L then d a else 0) +
        (if a ∈ S then d a else 0) + (if a ∈ M then d a else 0) := by
    rcases hcover a with h | h | h | h
    all_goals simp only [if_pos h]
    all_goals split_ifs <;> linarith only [hd a]
  have hh := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hp a)
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter] using hh

private theorem br_bounded_y_abs_sum :
    ∃ C epsilon0 : ℝ, 0 < C ∧ 0 < epsilon0 ∧ epsilon0 ≤ 1 / 2 ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun a : ℝ => a ^ 2) ν0 →
          (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1 → (∫ a : ℝ, a ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ epsilon0 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
            let mu : ℝ := ∫ a : ℝ, a ∂ρ
            let b : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
            let gamma : ℝ := b / variance (id : ℝ → ℝ) ρ
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ρ)
            ∀ y : ℝ, gamma ≤ y → y ≤ 2 →
              let ψ : ℝ × ℝ → ℝ := fun p => ∫ z : ℝ × ℝ,
                sourceFourierTest y (p.1 + z.1, p.2 + z.2) ∂quadraticFullNoiseLaw ρ
              (∑ j : Fin n, ∫ a : Shao.Path n, |lindleyDelta ρ ψ a j| ∂P) ≤
                C * ((n : ℝ) * |mu| + (n : ℝ) * b) := by
  classical
  obtain ⟨Kl, el, Ll, hKl, hel, hel2, hLl, hlong⟩ := sourceTruncation_futureNoise_early_long_kernel_bounds
  obtain ⟨Ks, es, Ls, hKs, hes, hes2, hLs, hshort⟩ := sourceTruncation_futureNoise_short_kernel_local_shift_budgets
  obtain ⟨Cp, hCp, hpush⟩ := sourceTruncation_lindleyDelta_large_push_sum
  obtain ⟨Cm, hCm, hmicro⟩ := sourceTruncation_lindleyDelta_micro_clock_sum
  let B : ℝ := 256 * Real.exp (7 + 3 * (1024 : ℝ))
  let L : ℝ := max Ll Ls
  let C : ℝ := Kl * (85 + 9 * B) + Ks * (6 + 2 * B) + Cp + Cm * (L + 1)
  have hB : 0 < B := by dsimp [B]; positivity
  have hL : 1 ≤ L := le_trans (by linarith only [hLl]) (le_max_left _ _)
  refine ⟨C, min el es, by dsimp [C]; positivity, lt_min hel hes,
    (min_le_left el es).trans hel2, ?_⟩
  intro ν0 hp n h2 hn hm x epsilon hx he he0 hR
  letI := hp
  dsimp only
  have hele : epsilon ≤ el := he0.trans (min_le_left _ _)
  have hese : epsilon ≤ es := he0.trans (min_le_right _ _)
  have he2 : epsilon ≤ 1 / 2 := hele.trans hel2
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
  let mu : ℝ := ∫ a : ℝ, a ∂ρ
  let s : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
  let b : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
  let gamma : ℝ := b / variance (id : ℝ → ℝ) ρ
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ρ)
  let N0 : ℝ := (n : ℝ) * |mu|
  let N3 : ℝ := (n : ℝ) * b
  let A : ℝ := N0 + N3
  obtain ⟨_, _, hpρ, hsρ, _, h2ρ, h3ρ, _⟩ :=
    Shao.sourceTruncation_law_data ν0 n h2 hn x epsilon hx he he2 hR
  letI : IsProbabilityMeasure ρ := hpρ
  obtain ⟨hn0, hs, hb, hV, hg, _, hslo, hshi, _, _, _⟩ :=
    br_source_scale ν0 n h2 hn hm x epsilon hx he he2 hR
  change 0 < s at hs
  change 0 < b at hb
  change 0 < gamma at hg
  change (3 / 4 : ℝ) ≤ (n : ℝ) * s at hslo
  change (n : ℝ) * s ≤ 4 / 3 at hshi
  have hN : (0 : ℝ) < n := by exact_mod_cast hn0
  have hN0 : 0 ≤ N0 := by dsimp [N0]; positivity
  have hN3 : 0 < N3 := by dsimp [N3]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hN3A : N3 ≤ A := by dsimp [A]; linarith only [hN0]
  letI : IsProbabilityMeasure (quadraticFullNoiseLaw ρ) :=
    (quadraticFullNoise_law_data ρ h3ρ hV (epsilon / (1 + x)) (by positivity) hsρ).2.2.1
  intro y hgy hy2
  have hy : 0 < y := hg.trans_le hgy
  let ψ : ℝ × ℝ → ℝ := fun p => ∫ z : ℝ × ℝ,
    sourceFourierTest y (p.1 + z.1, p.2 + z.2) ∂quadraticFullNoiseLaw ρ
  let T : Fin n → ℝ := fun j => (((n - (j.val + 1) : ℕ) : ℝ)) * s
  let d : Fin n → ℝ := fun j => ∫ a : Shao.Path n, |lindleyDelta ρ ψ a j| ∂P
  let U : Fin n → ℝ := fun j => ∫ a : Shao.Path n, lindleyRegulator a j ∂P
  let U2 : Fin n → ℝ := fun j => ∫ a : Shao.Path n, (lindleyRegulator a j) ^ 2 ∂P
  let Eset : Finset (Fin n) := Finset.univ.filter (fun j => j.val + 1 ≤ n / 2)
  let Lset : Finset (Fin n) := Finset.univ.filter
    (fun j => n / 2 < j.val + 1 ∧ max (L * gamma ^ 2) (y ^ 2) ≤ T j)
  let Sset : Finset (Fin n) := Finset.univ.filter
    (fun j => n / 2 < j.val + 1 ∧ L * gamma ^ 2 ≤ T j ∧ T j < max (L * gamma ^ 2) (y ^ 2))
  let Mset : Finset (Fin n) := Finset.univ.filter
    (fun j => n / 2 < j.val + 1 ∧ T j < L * gamma ^ 2)
  have hψ := br_smoothed_data ρ y
  have hd (j : Fin n) : 0 ≤ d j := integral_nonneg (fun _ => abs_nonneg _)
  have hU (j : Fin n) : 0 ≤ U j := integral_nonneg (fun _ => le_max_right _ _)
  have hU2 (j : Fin n) : 0 ≤ U2 j := integral_nonneg (fun _ => sq_nonneg _)
  have hUi (j : Fin n) := (iid_lindleyRegulator_prefix_first_moment ρ h2ρ n j).1
  have hU2i (j : Fin n) := (sourceTruncation_lindleyRegulator_second_moment
    ν0 n h2 hn hm x epsilon hx he he2 hR j).1
  have hl (j : Fin n) := hlong ν0 hp n h2 hn hm x epsilon hx he hele hR y hgy hy2
    (j.val + 1) (by omega) (by have hj := j.is_lt; omega)
  have hlate (j : Fin n) (hj : n / 2 < j.val + 1) : U j ≤ 6 * s ∧ U2 j ≤ 2 * B * s * N3 := by
    have hh := br_source_late_moments ν0 n h2 hn hm x epsilon hx he he2 hR j hj
    have hfirst : (4 : ℝ) / n ≤ 6 * s := (div_le_iff₀ hN).2 (by nlinarith only [hslo])
    have hsecond : U2 j ≤ B * b := hh.2.trans (mul_le_mul_of_nonneg_right
      (by dsimp [B]; have hh := Real.exp_pos (7 + 3 * (1024 : ℝ)); linarith) hb.le)
    have hscale : b ≤ 2 * s * N3 := by
      have hmul := mul_le_mul_of_nonneg_right
        (show (1 : ℝ) ≤ 2 * (n : ℝ) * s by nlinarith only [hslo]) hb.le
      dsimp only [N3]
      nlinarith only [hmul]
    exact ⟨hh.1.trans hfirst, hsecond.trans (by
      convert mul_le_mul_of_nonneg_left hscale hB.le using 1 <;> ring)⟩
  have htotal := br_source_total_moments ν0 n h2 hn hm x epsilon hx he he2 hR
  change (∑ j, U j) ≤ 5 ∧ (∑ j, U2 j) ≤ B * N3 at htotal
  have hEbound : (∑ j ∈ Eset, d j) ≤ Kl * (5 + B) * A := by
    have hterm (j : Fin n) (hj : j ∈ Eset) : d j ≤ Kl * A * U j + Kl * U2 j := by
      exact br_taylor_integral ρ n ψ hψ.1 hψ.2.1 y hψ.2.2 j (Kl * A) Kl
        (by positivity) hKl.le (hUi j) (hU2i j) (hl j).1
        ((hl j).2.1 (Finset.mem_filter.1 hj).2)
    have hsumU : (∑ j ∈ Eset, U j) ≤ 5 :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Eset) (fun j _ _ => hU j)).trans htotal.1
    have hsumU2 : (∑ j ∈ Eset, U2 j) ≤ B * N3 :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Eset) (fun j _ _ => hU2 j)).trans htotal.2
    calc
      _ ≤ ∑ j ∈ Eset, (Kl * A * U j + Kl * U2 j) := Finset.sum_le_sum hterm
      _ = Kl * A * (∑ j ∈ Eset, U j) + Kl * (∑ j ∈ Eset, U2 j) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ Kl * A * 5 + Kl * (B * N3) := add_le_add
        (mul_le_mul_of_nonneg_left hsumU (by positivity)) (mul_le_mul_of_nonneg_left hsumU2 hKl.le)
      _ ≤ Kl * A * 5 + Kl * (B * A) := by gcongr
      _ = _ := by ring
  have hLbound : (∑ j ∈ Lset, d j) ≤ Kl * (80 + 8 * B) * A := by
    let K : Finset ℕ := (Finset.range (n + 1)).filter (fun k => y ^ 2 ≤ (k : ℝ) * s)
    have hgK := br_long_grid n K s y hs hy hshi (fun k hk =>
      ⟨Nat.le_of_lt_succ (Finset.mem_range.1 (Finset.mem_filter.1 hk).1), (Finset.mem_filter.1 hk).2⟩)
    have hmap (j : Fin n) (hj : j ∈ Lset) : n - (j.val + 1) ∈ K :=
      Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega),
        (le_max_right (L * gamma ^ 2) (y ^ 2)).trans (Finset.mem_filter.1 hj).2.2⟩
    have hg1 : s * (∑ j ∈ Lset, 1 / Real.sqrt (T j)) ≤ 4 :=
      (mul_le_mul_of_nonneg_left (br_remaining_sum_le n Lset
        (fun k => 1 / Real.sqrt ((k : ℝ) * s)) K (fun _ => by positivity) hmap) hs.le).trans hgK.1
    have hg3 : s * (∑ j ∈ Lset, 1 / (Real.sqrt (T j)) ^ 3) ≤ 4 / y :=
      (mul_le_mul_of_nonneg_left (br_remaining_sum_le n Lset
        (fun k => 1 / (Real.sqrt ((k : ℝ) * s)) ^ 3) K (fun _ => by positivity) hmap) hs.le).trans hgK.2
    have hterm (j : Fin n) (hj : j ∈ Lset) : d j ≤ Kl *
        (6 * y * N0 * (s / Real.sqrt (T j)) +
          (6 + 2 * B) * y * N3 * (s / (Real.sqrt (T j)) ^ 3)) := by
      have hjl := (Finset.mem_filter.1 hj).2
      have hTl : max (Ll * gamma ^ 2) (y ^ 2) ≤ T j :=
        (max_le_max (mul_le_mul_of_nonneg_right (le_max_left Ll Ls) (sq_nonneg gamma)) le_rfl).trans hjl.2
      let O : ℝ := Kl * y * (N0 / Real.sqrt (T j) + N3 / (Real.sqrt (T j)) ^ 3)
      let E : ℝ := Kl * y / (Real.sqrt (T j)) ^ 3
      have hh := br_taylor_integral ρ n ψ hψ.1 hψ.2.1 y hψ.2.2 j O E
        (by dsimp [O]; positivity) (by dsimp [E]; positivity) (hUi j) (hU2i j) (hl j).1
        ((hl j).2.2 hjl.1 hTl)
      apply hh.trans
      calc
        _ ≤ O * (6 * s) + E * (2 * B * s * N3) := add_le_add
          (mul_le_mul_of_nonneg_left (hlate j hjl.1).1 (by dsimp [O]; positivity))
          (mul_le_mul_of_nonneg_left (hlate j hjl.1).2 (by dsimp [E]; positivity))
        _ = _ := by dsimp [O, E]; ring
    calc
      _ ≤ ∑ j ∈ Lset, Kl * (6 * y * N0 * (s / Real.sqrt (T j)) +
          (6 + 2 * B) * y * N3 * (s / (Real.sqrt (T j)) ^ 3)) := Finset.sum_le_sum hterm
      _ = Kl * (6 * y * N0 * (s * (∑ j ∈ Lset, 1 / Real.sqrt (T j))) +
          (6 + 2 * B) * y * N3 * (s * (∑ j ∈ Lset, 1 / (Real.sqrt (T j)) ^ 3))) := by
        calc
          _ = (Kl * (6 * y * N0 * s)) * (∑ j ∈ Lset, 1 / Real.sqrt (T j)) +
              (Kl * ((6 + 2 * B) * y * N3 * s)) * (∑ j ∈ Lset, 1 / (Real.sqrt (T j)) ^ 3) := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ = _ := by ring
      _ ≤ Kl * (6 * y * N0 * 4 + (6 + 2 * B) * y * N3 * (4 / y)) := by gcongr
      _ = Kl * (24 * y * N0 + (24 + 8 * B) * N3) := by field_simp [hy.ne']; ring
      _ ≤ Kl * (48 * N0 + (24 + 8 * B) * N3) := by gcongr; linarith only [hy2]
      _ ≤ Kl * ((80 + 8 * B) * N0 + (80 + 8 * B) * N3) := by gcongr <;> linarith only [hB]
      _ = _ := by dsimp only [A]; ring
  let Js : Finset ℕ := (Finset.range (n + 1)).filter (fun i => n / 2 < i ∧
    Ls * gamma ^ 2 ≤ (((n - i : ℕ) : ℝ) * s) ∧
      (((n - i : ℕ) : ℝ) * s) < max (Ls * gamma ^ 2) (y ^ 2))
  obtain ⟨O, E, hOE, hlocal, hOs, hEs⟩ :=
    hshort ν0 hp n h2 hn hm x epsilon hx he hese hR y hgy hy2
  change s * (∑ i ∈ Js, O i) ≤ Ks * A at hOs
  change s * (∑ i ∈ Js, E i) ≤ Ks at hEs
  have hSmem (j : Fin n) (hj : j ∈ Sset) : j.val + 1 ∈ Js := by
    have hjs := (Finset.mem_filter.1 hj).2
    have hTy : T j < y ^ 2 := by
      rcases lt_max_iff.1 hjs.2.2 with h | h
      · exact (not_lt_of_ge hjs.2.1 h).elim
      · exact h
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (by have hh := j.is_lt; omega), hjs.1, ?_, ?_⟩
    · exact (mul_le_mul_of_nonneg_right (le_max_right Ll Ls) (sq_nonneg gamma)).trans hjs.2.1
    · exact hTy.trans_le (le_max_right _ _)
  let big : Fin n → ℝ := fun j => ∫ a : Shao.Path n,
    (if y / 16 < lindleyRegulator a j then |lindleyDelta ρ ψ a j| else 0) ∂P
  have hbigi (j : Fin n) : Integrable (fun a : Shao.Path n =>
      if y / 16 < lindleyRegulator a j then |lindleyDelta ρ ψ a j| else 0) P := by
    refine (br_unit_integrable P _ (Measurable.ite
      (measurableSet_lt measurable_const (br_regulator_measurable j))
      (br_delta_data ρ n ψ hψ.1 hψ.2.1 j).1 measurable_const) ?_).1
    intro a
    split_ifs
    · exact (br_delta_data ρ n ψ hψ.1 hψ.2.1 j).2.1 a
    · simp
  have hbig (j : Fin n) : 0 ≤ big j := integral_nonneg (fun a => by split_ifs <;> positivity)
  have hSterm (j : Fin n) (hj : j ∈ Sset) :
      d j ≤ 6 * s * O (j.val + 1) + 2 * B * s * N3 * E (j.val + 1) + big j := by
    have hloc := (hlocal (j.val + 1) (hSmem j hj)).2
    have hpnt (a : Shao.Path n) : |lindleyDelta ρ ψ a j| ≤
        O (j.val + 1) * lindleyRegulator a j + E (j.val + 1) * (lindleyRegulator a j) ^ 2 +
          (if y / 16 < lindleyRegulator a j then |lindleyDelta ρ ψ a j| else 0) := by
      by_cases ha : y / 16 < lindleyRegulator a j
      · rw [if_pos ha]
        have hnon : 0 ≤ O (j.val + 1) * lindleyRegulator a j +
            E (j.val + 1) * (lindleyRegulator a j) ^ 2 := by
          have hu : 0 ≤ lindleyRegulator a j := le_max_right _ _
          exact add_nonneg (mul_nonneg (hOE _).1 hu) (mul_nonneg (hOE _).2 (sq_nonneg _))
        linarith only [hnon]
      · rw [if_neg ha, add_zero]
        have hh := hloc (lindleyRegulator a j) (Shao.prefixSquares a (j.val + 1))
          (le_max_right _ _) (le_of_not_gt ha)
        dsimp only [lindleyDelta]
        rw [hψ.2.2, hψ.2.2]
        have hnon := mul_nonneg (hOE (j.val + 1)).2 (sq_nonneg (lindleyRegulator a j))
        nlinarith only [hh, hnon]
    have hint := integral_mono (br_delta_data ρ n ψ hψ.1 hψ.2.1 j).2.2
      (((hUi j).const_mul _).add ((hU2i j).const_mul _) |>.add (hbigi j)) hpnt
    simp only [Pi.add_apply] at hint
    have hF0 : Integrable (fun a : Shao.Path n =>
        O (j.val + 1) * lindleyRegulator a j + E (j.val + 1) * (lindleyRegulator a j) ^ 2) P :=
      ((hUi j).const_mul (O (j.val + 1))).add ((hU2i j).const_mul (E (j.val + 1)))
    have heq : (∫ a : Shao.Path n,
        (O (j.val + 1) * lindleyRegulator a j + E (j.val + 1) * (lindleyRegulator a j) ^ 2) +
          (if y / 16 < lindleyRegulator a j then |lindleyDelta ρ ψ a j| else 0) ∂P) =
        O (j.val + 1) * U j + E (j.val + 1) * U2 j + big j := by
      rw [integral_add hF0 (hbigi j)]
      rw [integral_add ((hUi j).const_mul (O (j.val + 1)))
        ((hU2i j).const_mul (E (j.val + 1))), integral_const_mul, integral_const_mul]
    rw [heq] at hint
    apply hint.trans
    have hl := hlate j (Finset.mem_filter.1 hj).2.1
    have hh := add_le_add (mul_le_mul_of_nonneg_left hl.1 (hOE (j.val + 1)).1)
      (mul_le_mul_of_nonneg_left hl.2 (hOE (j.val + 1)).2)
    convert add_le_add_right hh (big j) using 1 <;> ring
  let Jp : Finset (Fin n) := Finset.univ.filter
    (fun j => n / 2 < j.val + 1 ∧ 0 < T j ∧ T j < y ^ 2)
  have hSp : Sset ⊆ Jp := by
    intro j hj
    have hjs := (Finset.mem_filter.1 hj).2
    have hTy : T j < y ^ 2 := by
      rcases lt_max_iff.1 hjs.2.2 with h | h
      · exact (not_lt_of_ge hjs.2.1 h).elim
      · exact h
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hjs.1,
      (show 0 < L * gamma ^ 2 by positivity).trans_le hjs.2.1, hTy⟩
  have hbigsum : (∑ j ∈ Sset, big j) ≤ Cp * N3 := by
    have hh := hpush ν0 hp n h2 hn hm x epsilon hx he he2 hR y hy
    have hhfinal : (∑ j ∈ Jp, big j) ≤ Cp * N3 := by
      simpa only [N3, mul_assoc] using hh.1.trans hh.2
    exact (Finset.sum_le_sum_of_subset_of_nonneg hSp (fun j _ _ => hbig j)).trans hhfinal
  have hSOs : s * (∑ j ∈ Sset, O (j.val + 1)) ≤ Ks * A :=
    (mul_le_mul_of_nonneg_left (br_index_sum_le n Sset O Js (fun i => (hOE i).1) hSmem) hs.le).trans hOs
  have hSEs : s * (∑ j ∈ Sset, E (j.val + 1)) ≤ Ks :=
    (mul_le_mul_of_nonneg_left (br_index_sum_le n Sset E Js (fun i => (hOE i).2) hSmem) hs.le).trans hEs
  have hSbound : (∑ j ∈ Sset, d j) ≤ Ks * (6 + 2 * B) * A + Cp * N3 := by
    calc
      _ ≤ ∑ j ∈ Sset, (6 * s * O (j.val + 1) + 2 * B * s * N3 * E (j.val + 1) + big j) :=
        Finset.sum_le_sum hSterm
      _ = 6 * (s * (∑ j ∈ Sset, O (j.val + 1))) +
          2 * B * N3 * (s * (∑ j ∈ Sset, E (j.val + 1))) + ∑ j ∈ Sset, big j := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
      _ ≤ 6 * (Ks * A) + 2 * B * N3 * Ks + Cp * N3 :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left hSOs (by norm_num))
          (mul_le_mul_of_nonneg_left hSEs (by positivity))) hbigsum
      _ ≤ 6 * (Ks * A) + 2 * B * A * Ks + Cp * N3 := by gcongr
      _ = _ := by ring
  have hMbound : (∑ j ∈ Mset, d j) ≤ Cm * (L + 1) * N3 :=
    hmicro ν0 hp n h2 hn hm x epsilon hx he he2 hR L y hL hy.le
  have hcover (j : Fin n) : j ∈ Eset ∨ j ∈ Lset ∨ j ∈ Sset ∨ j ∈ Mset := by
    by_cases hearly : j.val + 1 ≤ n / 2
    · exact Or.inl (Finset.mem_filter.2 ⟨Finset.mem_univ _, hearly⟩)
    have hlate : n / 2 < j.val + 1 := by omega
    by_cases hsmall : T j < L * gamma ^ 2
    · exact Or.inr (Or.inr (Or.inr (Finset.mem_filter.2 ⟨Finset.mem_univ _, hlate, hsmall⟩)))
    by_cases hlarge : max (L * gamma ^ 2) (y ^ 2) ≤ T j
    · exact Or.inr (Or.inl (Finset.mem_filter.2 ⟨Finset.mem_univ _, hlate, hlarge⟩))
    exact Or.inr (Or.inr (Or.inl (Finset.mem_filter.2
      ⟨Finset.mem_univ _, hlate, le_of_not_gt hsmall, lt_of_not_ge hlarge⟩)))
  change (∑ j : Fin n, d j) ≤ C * A
  calc
    _ ≤ (∑ j ∈ Eset, d j) + (∑ j ∈ Lset, d j) +
        (∑ j ∈ Sset, d j) + ∑ j ∈ Mset, d j := br_sum_cover d hd Eset Lset Sset Mset hcover
    _ ≤ Kl * (5 + B) * A + Kl * (80 + 8 * B) * A +
        (Ks * (6 + 2 * B) * A + Cp * N3) + Cm * (L + 1) * N3 :=
      add_le_add (add_le_add (add_le_add hEbound hLbound) hSbound) hMbound
    _ ≤ Kl * (5 + B) * A + Kl * (80 + 8 * B) * A +
        (Ks * (6 + 2 * B) * A + Cp * A) + Cm * (L + 1) * A := by gcongr
    _ = _ := by dsimp only [C]; ring

theorem sourceTruncation_bounded_y_reflection_comparison :
    ∃ C epsilon0 : ℝ, 0 < C ∧ 0 < epsilon0 ∧ epsilon0 ≤ 1 / 2 ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun a : ℝ => a ^ 2) ν0 →
          (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1 →
          (∫ a : ℝ, a ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ epsilon0 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            let ρ : Measure ℝ :=
              ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
            let mu : ℝ := ∫ a : ℝ, a ∂ρ
            let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
            let gamma : ℝ := m3 / variance (id : ℝ → ℝ) ρ
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ρ)
            ∀ y : ℝ, gamma ≤ y → y ≤ 2 →
              let ψ : ℝ × ℝ → ℝ := fun p =>
                ∫ z : ℝ × ℝ,
                  sourceFourierTest y (p.1 + z.1, p.2 + z.2)
                  ∂quadraticFullNoiseLaw ρ
              (∀ j : Fin n,
                Integrable (fun a : Shao.Path n => |lindleyDelta ρ ψ a j|) P) ∧
              (∑ j : Fin n, ∫ a : Shao.Path n, |lindleyDelta ρ ψ a j| ∂P) ≤
                C * ((n : ℝ) * |mu| + (n : ℝ) * m3) ∧
              ((∫ a : Shao.Path n,
                  ψ (Shao.lindleyState a n le_rfl, Shao.energy a) ∂P) -
                (∫ a : Shao.Path n,
                  ψ (Shao.prefixSum a n, Shao.energy a) ∂P) =
                ∑ j : Fin n, ∫ a : Shao.Path n, lindleyDelta ρ ψ a j ∂P) ∧
              |(∫ a : Shao.Path n,
                  ψ (Shao.lindleyState a n le_rfl, Shao.energy a) ∂P) -
                (∫ a : Shao.Path n,
                  ψ (Shao.prefixSum a n, Shao.energy a) ∂P)| ≤
                C * ((n : ℝ) * |mu| + (n : ℝ) * m3) := by
  classical
  obtain ⟨C, epsilon0, hC, he0, he02, hsum⟩ := br_bounded_y_abs_sum
  refine ⟨C, epsilon0, hC, he0, he02, ?_⟩
  intro ν0 hp n h2 hn hm x epsilon hx he he0le hR
  letI := hp
  dsimp only
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ρ)
  obtain ⟨_, _, hpρ, hsρ, _, _, h3ρ, _⟩ :=
    Shao.sourceTruncation_law_data ν0 n h2 hn x epsilon hx he (he0le.trans he02) hR
  letI : IsProbabilityMeasure ρ := hpρ
  have hV := (Shao.sourceTruncation_variance_bounds ν0 n h2 hn hm x epsilon hx he
    (he0le.trans he02) hR).2.2.2.2.2.1
  letI : IsProbabilityMeasure (quadraticFullNoiseLaw ρ) :=
    (quadraticFullNoise_law_data ρ h3ρ hV (epsilon / (1 + x)) (by positivity) hsρ).2.2.1
  intro y hgy hy2
  let ψ : ℝ × ℝ → ℝ := fun p => ∫ z : ℝ × ℝ,
    sourceFourierTest y (p.1 + z.1, p.2 + z.2) ∂quadraticFullNoiseLaw ρ
  have hψ := br_smoothed_data ρ y
  have hbound := hsum ν0 hp n h2 hn hm x epsilon hx he he0le hR y hgy hy2
  have hLaw (j : Fin n) : IdentDistrib (fun a : Shao.Path n => a j) (id : ℝ → ℝ) P ρ := by
    refine ⟨(measurable_pi_apply j).aemeasurable, aemeasurable_id, ?_⟩
    simpa only [Measure.map_id] using (measurePreserving_eval (fun _ : Fin n => ρ) j).map_eq
  have htel := iid_lindley_telescoping (fun j => measurable_pi_apply j)
    (iIndepFun_pi (fun _ : Fin n => aemeasurable_id)) hLaw ψ hψ.1 hψ.2.1
  change (∫ a : Shao.Path n, ψ (Shao.lindleyState a n le_rfl, Shao.energy a) ∂P) -
    (∫ a : Shao.Path n, ψ (Shao.prefixSum a n, Shao.energy a) ∂P) =
      ∑ j : Fin n, ∫ a : Shao.Path n, lindleyDelta ρ ψ a j ∂P at htel
  refine ⟨fun j => (br_delta_data ρ n ψ hψ.1 hψ.2.1 j).2.2, hbound, htel, ?_⟩
  rw [htel]
  calc
    _ ≤ ∑ j : Fin n, |∫ a : Shao.Path n, lindleyDelta ρ ψ a j ∂P| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin n, ∫ a : Shao.Path n, |lindleyDelta ρ ψ a j| ∂P :=
      Finset.sum_le_sum (fun j _ => abs_integral_le_integral_abs)
    _ ≤ _ := hbound

end Shao.Probability
