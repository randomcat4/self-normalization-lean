import Shao.OQ5.P52.FixedLayerNormalizedRealTailLimits

/-!
# The same fixed real p52 counterexample

All population, projection, canonicality, moment and original Studentized
tail properties are bound to one fixed tuple. The projection is its actual
row integral and the statistic retains its actual pair-mean center.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace Shao.OQ5.P52

noncomputable section

attribute [local instance] fixedRealObservationLaw_isProbabilityMeasure

def FixedP52Counterexample (μ : Measure ℝ) (P : Measure (ℕ → ℝ))
    (H : ℝ × ℝ → ℝ) (c : ℝ → (ℕ → Fin 3))
    (K : (ℕ → Fin 3) × (ℕ → Fin 3) → ℝ) : Prop :=
  let a : ℝ := Real.sqrt 3
  let h : ℝ × ℝ → ℝ := fun z => a * H z
  let g0 : ℝ → ℝ := fun x => ∫ y : ℝ, H (x, y) ∂μ
  let r0 : ℝ × ℝ → ℝ := fun z => H z - g0 z.1 - g0 z.2
  let g : ℝ → ℝ := fun x => ∫ y : ℝ, h (x, y) ∂μ
  let r : ℝ × ℝ → ℝ := fun z => h z - g z.1 - g z.2
  let U : (ℝ × ℝ → ℝ) → (n : ℕ) → (Fin n → ℝ) → ℝ :=
    fun A n z => (n.choose 2 : ℝ)⁻¹ *
      ∑ i : Fin n, ∑ k : Fin n, if i < k then A (z i, z k) else 0
  let q : (ℝ × ℝ → ℝ) → (n : ℕ) → (Fin n → ℝ) → Fin n → ℝ :=
    fun A n z i => ((n : ℝ) - 1)⁻¹ *
      ∑ k ∈ Finset.univ.erase i, A (z i, z k)
  let Sq : (ℝ × ℝ → ℝ) → (n : ℕ) → (Fin n → ℝ) → ℝ :=
    fun A n z => (4 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2) *
      ∑ i : Fin n, (q A n z i - U A n z) ^ 2
  let R : (ℝ × ℝ → ℝ) → (n : ℕ) → (Fin n → ℝ) → ℝ :=
    fun A n z => Real.sqrt (Sq A n z)
  let T : (ℝ × ℝ → ℝ) → (n : ℕ) → (Fin n → ℝ) → ℝ :=
    fun A n z => Real.sqrt (n : ℝ) *
      (U A n z - ∫ w : ℝ × ℝ, A w ∂μ.prod μ) / R A n z
  let tail : (ℝ × ℝ → ℝ) → ℕ → ℝ → ℝ :=
    fun A n t => P.real {ξ : ℕ → ℝ | t ≤ T A n (fun i : Fin n => ξ i.val)}
  let x : ℕ → ℝ := fun n => (n : ℝ) ^ (1 / 6 : ℝ) / Real.log (n : ℝ)
  let N : ℕ → ℕ := fun j => 2 ^ (3 * (j + 6) ^ 3)
  IsProbabilityMeasure μ ∧
  IsProbabilityMeasure P ∧
  (∀ i : ℕ, Measurable (fun ξ : ℕ → ℝ => ξ i)) ∧
  (∀ i : ℕ, P.map (fun ξ : ℕ → ℝ => ξ i) = μ) ∧
  ProbabilityTheory.iIndepFun (fun (i : ℕ) (ξ : ℕ → ℝ) => ξ i) P ∧
  (∀ n : ℕ, P.map (fun (ξ : ℕ → ℝ) (i : Fin n) => ξ i.val) =
    Measure.pi (fun _ : Fin n => μ)) ∧
  Measurable c ∧
  Measurable K ∧
  (∀ u v : ℕ → Fin 3, K (u, v) = K (v, u)) ∧
  Measurable H ∧
  (∀ u v : ℝ, H (u, v) = H (v, u)) ∧
  Integrable H (μ.prod μ) ∧
  Integrable (fun z : ℝ × ℝ => H z ^ 2) (μ.prod μ) ∧
  (∀ ν : ℝ, 1 ≤ ν → MemLp H (ENNReal.ofReal ν) (μ.prod μ)) ∧
  (∫ z : ℝ × ℝ, H z ∂μ.prod μ) = 0 ∧
  (∀ᵐ u : ℝ ∂μ, Integrable (fun v : ℝ => H (u, v)) μ) ∧
  Measurable g0 ∧
  MemLp g0 2 μ ∧
  Integrable g0 μ ∧
  Integrable (fun u : ℝ => g0 u ^ 2) μ ∧
  (∫ u : ℝ, g0 u ∂μ) = 0 ∧
  (∫ u : ℝ, g0 u ^ 2 ∂μ) = (1 / 3 : ℝ) ∧
  μ.map g0 = Shao.OQ5.P50.layerNoiseLaw ∧
  (∀ᵐ u : ℝ ∂μ, |g0 u| ≤ 1) ∧
  ProbabilityTheory.IndepFun g0 c μ ∧
  Measurable r0 ∧
  (∀ u v : ℝ, r0 (u, v) = r0 (v, u)) ∧
  (∀ u v : ℝ, H (u, v) = g0 u + g0 v + r0 (u, v)) ∧
  MemLp r0 2 (μ.prod μ) ∧
  Integrable r0 (μ.prod μ) ∧
  (∀ᵐ u : ℝ ∂μ, Integrable (fun v : ℝ => r0 (u, v)) μ) ∧
  (∀ᵐ u : ℝ ∂μ, (∫ v : ℝ, r0 (u, v) ∂μ) = 0) ∧
  (r0 =ᵐ[μ.prod μ] fun z : ℝ × ℝ => K (c z.1, c z.2)) ∧
  0 < a ∧
  Measurable h ∧
  (∀ u v : ℝ, h (u, v) = h (v, u)) ∧
  Integrable h (μ.prod μ) ∧
  MemLp h 2 (μ.prod μ) ∧
  Integrable (fun z : ℝ × ℝ => h z ^ 2) (μ.prod μ) ∧
  (∀ ν : ℝ, 1 ≤ ν → MemLp h (ENNReal.ofReal ν) (μ.prod μ)) ∧
  (∫ z : ℝ × ℝ, h z ∂μ.prod μ) = 0 ∧
  (∀ᵐ u : ℝ ∂μ, Integrable (fun v : ℝ => h (u, v)) μ) ∧
  Measurable g ∧
  (∀ u : ℝ, g u = a * g0 u) ∧
  MemLp g 2 μ ∧
  Integrable g μ ∧
  Integrable (fun u : ℝ => g u ^ 2) μ ∧
  (∫ u : ℝ, g u ∂μ) = 0 ∧
  (∫ u : ℝ, g u ^ 2 ∂μ) = 1 ∧
  μ.map g = Shao.OQ5.P50.layerNoiseLaw.map (fun t : ℝ => a * t) ∧
  (∀ᵐ u : ℝ ∂μ, |g u| ≤ a) ∧
  ProbabilityTheory.IndepFun g c μ ∧
  Measurable r ∧
  (∀ u v : ℝ, r (u, v) = r (v, u)) ∧
  (∀ u v : ℝ, h (u, v) = g u + g v + r (u, v)) ∧
  (∀ z : ℝ × ℝ, r z = a * r0 z) ∧
  MemLp r 2 (μ.prod μ) ∧
  Integrable r (μ.prod μ) ∧
  (∀ᵐ u : ℝ ∂μ, Integrable (fun v : ℝ => r (u, v)) μ) ∧
  (∀ᵐ u : ℝ ∂μ, (∫ v : ℝ, r (u, v) ∂μ) = 0) ∧
  (r =ᵐ[μ.prod μ] fun z : ℝ × ℝ => a * K (c z.1, c z.2)) ∧
  (∀ m : ℕ, Integrable (fun z : ℝ × ℝ => |H z| ^ m) (μ.prod μ)) ∧
  (∀ m : ℕ, Integrable (fun z : ℝ × ℝ => |h z| ^ m) (μ.prod μ)) ∧
  (∀ η lambda : ℝ, 0 < η → η < 1 / 5 → 0 < lambda →
    Integrable (fun z : ℝ × ℝ => Real.exp (lambda * |H z| ^ η)) (μ.prod μ)) ∧
  (∀ η lambda : ℝ, 0 < η → η < 1 / 5 → 0 < lambda →
    Integrable (fun z : ℝ × ℝ => Real.exp (lambda * |h z| ^ η)) (μ.prod μ)) ∧
  (∀ lambda : ℝ, 0 < lambda →
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal
      (Real.exp (lambda * |H z| ^ (1 / 5 : ℝ))) ∂μ.prod μ) = ⊤) ∧
  (∀ lambda : ℝ, 0 < lambda →
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal
      (Real.exp (lambda * |h z| ^ (1 / 5 : ℝ))) ∂μ.prod μ) = ⊤) ∧
  (∀ lambda : ℝ, 0 < lambda →
    ¬ Integrable (fun z : ℝ × ℝ =>
      Real.exp (lambda * |H z| ^ (1 / 5 : ℝ))) (μ.prod μ)) ∧
  (∀ lambda : ℝ, 0 < lambda →
    ¬ Integrable (fun z : ℝ × ℝ =>
      Real.exp (lambda * |h z| ^ (1 / 5 : ℝ))) (μ.prod μ)) ∧
  (∀ n : ℕ, Measurable (U h n)) ∧
  (∀ (n : ℕ) (i : Fin n), Measurable (fun z : Fin n → ℝ => q h n z i)) ∧
  (∀ n : ℕ, Measurable (Sq h n)) ∧
  (∀ n : ℕ, Measurable (R h n)) ∧
  (∀ n : ℕ, Measurable (T h n)) ∧
  (∀ n : ℕ, Measurable
    (fun ξ : ℕ → ℝ => T h n (fun i : Fin n => ξ i.val))) ∧
  (∀ (n : ℕ) (z : Fin n → ℝ), U h n z = a * U H n z) ∧
  (∀ (n : ℕ) (z : Fin n → ℝ) (i : Fin n), q h n z i = a * q H n z i) ∧
  (∀ (n : ℕ) (z : Fin n → ℝ), Sq h n z = 3 * Sq H n z) ∧
  (∀ (n : ℕ) (z : Fin n → ℝ), R h n z = a * R H n z) ∧
  (∀ (n : ℕ) (z : Fin n → ℝ), T h n z = T H n z) ∧
  (∀ (n : ℕ) (t : ℝ), tail h n t = tail H n t) ∧
  (∀ n : ℕ, 3 ≤ n → ∀ᵐ ξ : ℕ → ℝ ∂P,
    0 < R H n (fun i : Fin n => ξ i.val)) ∧
  (∀ n : ℕ, 3 ≤ n → ∀ᵐ ξ : ℕ → ℝ ∂P,
    0 < R h n (fun i : Fin n => ξ i.val)) ∧
  (∀ n : ℕ, 2 ≤ n → 0 < x n) ∧
  Tendsto x atTop atTop ∧
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ (1 / 6 : ℝ)) atTop (nhds 0) ∧
  Tendsto (fun n : ℕ => x n / Real.sqrt (n : ℝ)) atTop (nhds 0) ∧
  Tendsto (fun n : ℕ => 2 * x n / (n : ℝ) ^ (1 / 6 : ℝ)) atTop (nhds 0) ∧
  StrictMono N ∧
  Tendsto N atTop atTop ∧
  (∀ j : ℕ, 8 ≤ N j) ∧
  (∀ᶠ j : ℕ in atTop, (1 / 4 : ℝ) * Real.exp
    (-2 * (N j : ℝ) ^ fixedLayerTau j) ≤ tail h (N j) (x (N j))) ∧
  (∀ᶠ j : ℕ in atTop, 0 < tail h (N j) (x (N j))) ∧
  Tendsto (fun j : ℕ => Real.log (tail h (N j) (x (N j))) /
    (-(x (N j) ^ 2) / 2)) atTop (nhds 0) ∧
  Tendsto (fun j : ℕ => tail h (N j) (x (N j)) /
    Shao.OQ5.P35.standardNormalUpperTail (x (N j))) atTop atTop ∧
  (¬ Tendsto (fun n : ℕ => Real.log (tail h n (x n)) /
    (-(x n ^ 2) / 2)) atTop (nhds 1)) ∧
  (¬ Tendsto (fun n : ℕ => tail h n (x n) /
    Shao.OQ5.P35.standardNormalUpperTail (x n)) atTop (nhds 1)) ∧
  ¬ (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    ∀ t : ℝ, 0 ≤ t → t ≤ 2 * x n →
      |tail h n t / Shao.OQ5.P35.standardNormalUpperTail t - 1| ≤ ε)

theorem fixedP52Counterexample :
    FixedP52Counterexample fixedRealObservationLaw fixedRealSampleLaw fixedRealKernel
      (fun u : ℝ => (Shao.OQ5.P50.layerDecode u).2) fixedCategoryResidualKernel := by
  classical
  have hRawIntegral := integrable_fixedRealKernel
  have hRawMean := integral_fixedRealKernel_eq_zero
  have hKernelTwo : MemLp fixedNormalizedRealKernel 2
      (fixedRealObservationLaw.prod fixedRealObservationLaw) := by
    simpa using fixedNormalizedRealKernel_memLp 2 (by norm_num)
  have hProjectionOne : Integrable fixedNormalizedRealFirstProjection
      fixedRealObservationLaw :=
    MemLp.integrable (by norm_num) fixedNormalizedRealFirstProjection_memLp_two
  have hResidualOne : Integrable fixedNormalizedRealCanonicalResidual
      (fixedRealObservationLaw.prod fixedRealObservationLaw) :=
    MemLp.integrable (by norm_num) fixedNormalizedRealCanonicalResidual_memLp_two
  have hResidualMeasurable : Measurable fixedNormalizedRealCanonicalResidual :=
    (measurable_fixedNormalizedRealKernel.sub
      (measurable_fixedNormalizedRealFirstProjection.comp measurable_fst)).sub
      (measurable_fixedNormalizedRealFirstProjection.comp measurable_snd)
  have hResidualSymmetric (u v : ℝ) :
      fixedNormalizedRealCanonicalResidual (u, v) =
        fixedNormalizedRealCanonicalResidual (v, u) := by
    calc
      _ = Real.sqrt 3 * fixedRealCanonicalResidual (u, v) :=
        fixedNormalizedRealCanonicalResidual_eq (u, v)
      _ = Real.sqrt 3 * fixedRealCanonicalResidual (v, u) :=
        congrArg (fun t : ℝ => Real.sqrt 3 * t)
          (fixedRealCanonicalResidual_symmetric u v)
      _ = _ := (fixedNormalizedRealCanonicalResidual_eq (v, u)).symm
  dsimp only [FixedP52Counterexample]
  refine ⟨
    fixedRealObservationLaw_isProbabilityMeasure,
    fixedRealSampleLaw_isProbabilityMeasure,
    measurable_fixedRealSampleCoordinate,
    map_fixedRealSampleCoordinate,
    iIndepFun_fixedRealSampleCoordinate,
    map_fixedRealSamplePrefix,
    measurable_snd.comp Shao.OQ5.P50.measurable_layerDecode,
    measurable_fixedCategoryResidualKernel,
    fixedCategoryResidualKernel_symmetric,
    measurable_fixedRealKernel,
    fixedRealKernel_symmetric,
    hRawIntegral,
    integrable_fixedRealKernel_sq,
    fixedRealKernel_memLp,
    hRawMean,
    integrable_fixedRealKernel_row_ae,
    measurable_fixedRealFirstProjection,
    fixedRealFirstProjection_memLp_two,
    integrable_fixedRealFirstProjection,
    integrable_fixedRealFirstProjection_sq,
    integral_fixedRealFirstProjection_eq_zero,
    integral_fixedRealFirstProjection_sq,
    map_fixedRealFirstProjection,
    fixedRealFirstProjection_abs_le_one_ae,
    fixedRealFirstProjection_indep_categories,
    measurable_fixedRealCanonicalResidual,
    fixedRealCanonicalResidual_symmetric,
    fixedRealKernel_hoeffding,
    fixedRealCanonicalResidual_memLp_two,
    integrable_fixedRealCanonicalResidual,
    integrable_fixedRealCanonicalResidual_row_ae,
    integral_fixedRealCanonicalResidual_row_eq_zero_ae,
    fixedRealCanonicalResidual_ae_eq_categoryResidual,
    Real.sqrt_pos.mpr (by norm_num),
    measurable_fixedNormalizedRealKernel,
    fixedNormalizedRealKernel_symmetric,
    integrable_fixedNormalizedRealKernel,
    hKernelTwo,
    hKernelTwo.integrable_sq,
    fixedNormalizedRealKernel_memLp,
    integral_fixedNormalizedRealKernel_eq_zero,
    integrable_fixedNormalizedRealKernel.prod_right_ae,
    measurable_fixedNormalizedRealFirstProjection,
    fixedNormalizedRealFirstProjection_eq,
    fixedNormalizedRealFirstProjection_memLp_two,
    hProjectionOne,
    fixedNormalizedRealFirstProjection_memLp_two.integrable_sq,
    integral_fixedNormalizedRealFirstProjection_eq_zero,
    integral_fixedNormalizedRealFirstProjection_sq,
    map_fixedNormalizedRealFirstProjection,
    fixedNormalizedRealFirstProjection_abs_le_sqrt_three_ae,
    fixedNormalizedRealFirstProjection_indep_categories,
    hResidualMeasurable,
    hResidualSymmetric,
    ?_,
    fixedNormalizedRealCanonicalResidual_eq,
    fixedNormalizedRealCanonicalResidual_memLp_two,
    hResidualOne,
    integrable_fixedNormalizedRealCanonicalResidual_row_ae,
    integral_fixedNormalizedRealCanonicalResidual_row_eq_zero_ae,
    fixedNormalizedRealCanonicalResidual_ae_eq_categoryResidual,
    integrable_fixedRealKernel_abs_pow,
    integrable_fixedNormalizedRealKernel_abs_pow,
    integrable_fixedRealKernel_subcritical_exp,
    integrable_fixedNormalizedRealKernel_subcritical_exp,
    lintegral_fixedRealKernel_critical_exp_eq_top,
    lintegral_fixedNormalizedRealKernel_critical_exp_eq_top,
    not_integrable_fixedRealKernel_critical_exp,
    not_integrable_fixedNormalizedRealKernel_critical_exp,
    measurable_fixedNormalizedRealSampleU,
    measurable_fixedNormalizedRealSampleRowMean,
    measurable_fixedNormalizedRealSampleStudentizerSq,
    measurable_fixedNormalizedRealSampleStudentizer,
    measurable_fixedNormalizedRealSampleStudentized,
    measurable_fixedNormalizedRealSampleStudentized_sample,
    fixedNormalizedRealSampleU_eq,
    fixedNormalizedRealSampleRowMean_eq,
    fixedNormalizedRealSampleStudentizerSq_eq,
    fixedNormalizedRealSampleStudentizer_eq,
    ?_,
    ?_,
    fixedRealSampleStudentizer_prefix_pos_ae,
    fixedNormalizedRealSampleStudentizer_prefix_pos_ae,
    fixedLayerTailThreshold_pos,
    fixedLayerTailThreshold_tendsto,
    fixedLayerTailThreshold_div_sixth_tendsto_zero,
    fixedLayerTailThreshold_div_sqrt_tendsto_zero,
    fixedLayer_double_threshold_div_sixth_tendsto_zero,
    strictMono_fixedLayerN,
    fixedLayerN_tendsto,
    fixedLayerN_ge_eight,
    fixedNormalizedRealSampleStudentizedTailProbability_ge_quarter_exp_eventually,
    fixedNormalizedRealSampleStudentizedTailProbability_eventually_pos,
    fixedNormalizedRealLayer_log_tail_ratio_tendsto_zero,
    fixedNormalizedRealLayer_relative_tail_ratio_tendsto_atTop,
    fixedNormalizedRealLayer_full_log_tail_ratio_not_tendsto_one,
    fixedNormalizedRealLayer_full_relative_tail_ratio_not_tendsto_one,
    fixedNormalizedRealLayer_uniform_relative_tail_window_fails⟩
  · intro u v
    change fixedNormalizedRealKernel (u, v) =
      fixedNormalizedRealFirstProjection u + fixedNormalizedRealFirstProjection v +
        (fixedNormalizedRealKernel (u, v) - fixedNormalizedRealFirstProjection u -
          fixedNormalizedRealFirstProjection v)
    ring
  · intro n z
    change fixedNormalizedRealSampleStudentized z =
      Real.sqrt (n : ℝ) *
        (fixedRealSampleU z - ∫ w : ℝ × ℝ, fixedRealKernel w
          ∂fixedRealObservationLaw.prod fixedRealObservationLaw) /
        fixedRealSampleStudentizer z
    rw [hRawMean, sub_zero]
    exact fixedNormalizedRealSampleStudentized_eq n z
  · intro n t
    change fixedNormalizedRealSampleStudentizedTailProbability n t =
      fixedRealSampleLaw.real {ξ : ℕ → ℝ |
        t ≤ Real.sqrt (n : ℝ) *
          (fixedRealSampleU (fun i : Fin n => ξ i.val) -
            ∫ w : ℝ × ℝ, fixedRealKernel w
              ∂fixedRealObservationLaw.prod fixedRealObservationLaw) /
          fixedRealSampleStudentizer (fun i : Fin n => ξ i.val)}
    rw [hRawMean]
    simp only [sub_zero]
    exact fixedNormalizedRealSampleStudentizedTailProbability_eq_real n t

theorem exists_fixedP52Counterexample :
    ∃ (μ : Measure ℝ) (P : Measure (ℕ → ℝ)) (H : ℝ × ℝ → ℝ)
      (c : ℝ → (ℕ → Fin 3)) (K : (ℕ → Fin 3) × (ℕ → Fin 3) → ℝ),
      FixedP52Counterexample μ P H c K := by
  exact ⟨fixedRealObservationLaw, fixedRealSampleLaw, fixedRealKernel,
    (fun u : ℝ => (Shao.OQ5.P50.layerDecode u).2), fixedCategoryResidualKernel,
    fixedP52Counterexample⟩

end

end Shao.OQ5.P52
