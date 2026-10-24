/- Inclusive Gaussian wall profiles from the actual iid true-energy strip. -/
import Shao.Probability.SourceTrueEnergyStrip
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Shao.Probability
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Classical

private theorem twp_kernel_tail (T a : ℝ) (hT : 0 < T) (ha : 0 ≤ a) :
    IntegrableOn (fun s : ℝ => (2 * s / T) * Real.exp (-(s ^ 2) / T)) (Set.Ioi a) ∧
      (∫ s : ℝ in Set.Ioi a, (2 * s / T) * Real.exp (-(s ^ 2) / T)) =
        Real.exp (-(a ^ 2) / T) := by
  have hu : Tendsto (fun s : ℝ => s ^ 2 / T) atTop atTop := by
    simpa only [div_eq_mul_inv] using (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).atTop_mul_const (inv_pos.2 hT)
  have he : Tendsto (fun u : ℝ => Real.exp (-u)) atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
  have hf : Tendsto (fun s : ℝ => -Real.exp (-(s ^ 2) / T)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_div, neg_zero] using (he.comp hu).neg
  have hd (s : ℝ) (_hs : s ∈ Set.Ici a) : HasDerivAt
      (fun s : ℝ => -Real.exp (-(s ^ 2) / T))
      ((2 * s / T) * Real.exp (-(s ^ 2) / T)) s := by
    convert ((((hasDerivAt_id s).pow 2).neg.div_const T).exp.neg) using 1
    · funext y
      simp only [Pi.neg_apply, Pi.pow_apply, id_eq, div_eq_inv_mul]
    · simp only [Pi.neg_apply, Pi.pow_apply, id_eq, div_eq_inv_mul]
      ring
  have hn (s : ℝ) (hs : s ∈ Set.Ioi a) : 0 ≤ (2 * s / T) * Real.exp (-(s ^ 2) / T) := by
    have hs0 : 0 ≤ s := ha.trans hs.le
    positivity
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hn hf, ?_⟩
  simpa only [zero_sub, neg_neg] using integral_Ioi_of_hasDerivAt_of_nonneg' hd hn hf

private theorem twp_kernel_second (T : ℝ) (hT : 0 < T) :
    IntegrableOn (fun s : ℝ => s ^ 2 * ((2 * s / T) * Real.exp (-(s ^ 2) / T))) (Set.Ioi 0) ∧
      (∫ s : ℝ in Set.Ioi 0, s ^ 2 * ((2 * s / T) * Real.exp (-(s ^ 2) / T))) = T := by
  have hu : Tendsto (fun s : ℝ => s ^ 2 / T) atTop atTop := by
    simpa only [div_eq_mul_inv] using (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).atTop_mul_const (inv_pos.2 hT)
  have he : Tendsto (fun u : ℝ => Real.exp (-u)) atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
  have he1 : Tendsto (fun u : ℝ => u * Real.exp (-u)) atTop (𝓝 0) := by
    simpa only [pow_one] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hf : Tendsto (fun s : ℝ => -(s ^ 2 + T) * Real.exp (-(s ^ 2) / T)) atTop (𝓝 0) := by
    have hh : Tendsto (fun s : ℝ => (-T) * ((s ^ 2 / T + 1) * Real.exp (-(s ^ 2) / T))) atTop (𝓝 0) := by
      convert ((he1.add he).comp hu).const_mul (-T) using 1 <;> simp only [Function.comp_def, neg_div, add_mul, one_mul, add_zero, mul_zero]
    convert hh using 1
    funext s
    field_simp <;> ring
  have hd (s : ℝ) (_hs : s ∈ Set.Ici (0 : ℝ)) : HasDerivAt
      (fun s : ℝ => -(s ^ 2 + T) * Real.exp (-(s ^ 2) / T))
      (s ^ 2 * ((2 * s / T) * Real.exp (-(s ^ 2) / T))) s := by
    convert ((((hasDerivAt_id s).pow 2).add_const T).neg.mul
      (((hasDerivAt_id s).pow 2).neg.div_const T).exp) using 1
    · funext y
      simp only [Pi.neg_apply, Pi.pow_apply, Pi.mul_apply, id_eq, div_eq_inv_mul]
    · simp only [Pi.neg_apply, Pi.pow_apply, Pi.mul_apply, id_eq, div_eq_inv_mul]
      field_simp [hT.ne'] <;> ring
  have hn (s : ℝ) (hs : s ∈ Set.Ioi (0 : ℝ)) :
      0 ≤ s ^ 2 * ((2 * s / T) * Real.exp (-(s ^ 2) / T)) := by
    have hs0 : 0 ≤ s := hs.le
    positivity
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hn hf, ?_⟩
  simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, neg_zero, zero_div,
    Real.exp_zero, mul_one, zero_sub, neg_neg] using integral_Ioi_of_hasDerivAt_of_nonneg' hd hn hf

private theorem twp_profile_as_integral (T M z : ℝ) (hT : 0 < T) (hM : 0 ≤ M) :
    (∫ s : ℝ in Set.Ioi 0, if z ≤ M + s then
      (2 * s / T) * Real.exp (-(s ^ 2) / T) else 0) =
      Real.exp (-((max (z - M) 0) ^ 2) / T) := by
  classical
  let k : ℝ → ℝ := fun s => (2 * s / T) * Real.exp (-(s ^ 2) / T)
  by_cases hz : z ≤ M
  · rw [max_eq_right (sub_nonpos.2 hz)]
    have he : (∫ s : ℝ in Set.Ioi 0, if z ≤ M + s then k s else 0) = ∫ s : ℝ in Set.Ioi 0, k s := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : 0 < s := hs
      rw [if_pos (by linarith only [hz, hs0])]
    change (∫ s : ℝ in Set.Ioi 0, if z ≤ M + s then k s else 0) = _
    rw [he, (twp_kernel_tail T 0 hT (by norm_num)).2]
  · let a : ℝ := z - M
    have ha : 0 < a := sub_pos.2 (lt_of_not_ge hz)
    have he : (∫ s : ℝ in Set.Ioi 0, if z ≤ M + s then k s else 0) = ∫ s : ℝ in Set.Ioi a, k s := by
      calc
        _ = ∫ s : ℝ, (Set.Ioi 0).indicator (fun s => if z ≤ M + s then k s else 0) s :=
          (integral_indicator measurableSet_Ioi).symm
        _ = ∫ s : ℝ, (Set.Ioi a).indicator k s := by
          apply integral_congr_ae
          have hne : ({a} : Set ℝ)ᶜ ∈ ae (volume : Measure ℝ) :=
            compl_mem_ae_iff.2 (measure_singleton a)
          filter_upwards [hne] with s hs
          have hsa : s ≠ a := by simpa using hs
          by_cases hs0 : 0 < s
          · rw [Set.indicator_of_mem hs0]
            by_cases hsz : z ≤ M + s
            · have hsa' : a < s := lt_of_le_of_ne (by dsimp [a]; linarith only [hsz]) (Ne.symm hsa)
              rw [if_pos hsz, Set.indicator_of_mem hsa']
            · have hsa' : s ∉ Set.Ioi a := by change ¬ a < s; dsimp [a]; linarith only [hsz]
              rw [if_neg hsz, Set.indicator_of_notMem hsa']
          · have hsa' : s ∉ Set.Ioi a := by change ¬ a < s; linarith only [ha, hs0]
            rw [Set.indicator_of_notMem hs0, Set.indicator_of_notMem hsa']
        _ = _ := integral_indicator measurableSet_Ioi
    change (∫ s : ℝ in Set.Ioi 0, if z ≤ M + s then k s else 0) = _
    rw [he, (twp_kernel_tail T a hT ha.le).2, max_eq_left ha.le]

private theorem twp_profile_product_integrable
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (A : Set Ω) (hA : MeasurableSet A)
    (w : Ω → ℝ) (hw : Measurable w)
    (T M : ℝ) (hT : 0 < T) :
    Integrable (fun p : Ω × ℝ => if p.1 ∈ A ∧ w p.1 ≤ M + p.2 then
      (2 * p.2 / T) * Real.exp (-(p.2 ^ 2) / T) else 0)
      (mu.prod (volume.restrict (Set.Ioi 0))) := by
  classical
  let k : ℝ → ℝ := fun s => (2 * s / T) * Real.exp (-(s ^ 2) / T)
  have hki : Integrable k (volume.restrict (Set.Ioi 0)) := (twp_kernel_tail T 0 hT (by norm_num)).1
  have hkabs : Integrable (fun p : Ω × ℝ => |k p.2|) (mu.prod (volume.restrict (Set.Ioi 0))) := by
    simpa only [Real.norm_eq_abs, one_mul] using (integrable_const (1 : ℝ) (μ := mu)).mul_prod hki.norm
  have hBm : MeasurableSet {p : Ω × ℝ | p.1 ∈ A ∧ w p.1 ≤ M + p.2} :=
    (hA.preimage measurable_fst).inter (measurableSet_le (hw.comp measurable_fst) (measurable_const.add measurable_snd))
  have hm : Measurable (fun p : Ω × ℝ => if p.1 ∈ A ∧ w p.1 ≤ M + p.2 then k p.2 else 0) := by
    apply Measurable.ite hBm
    · dsimp [k]; fun_prop
    · exact measurable_const
  apply hkabs.mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun p => by
    split_ifs <;> simp only [Real.norm_eq_abs, norm_zero, le_refl, abs_nonneg]

theorem gaussian_wall_profile_layer_cake
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (A : Set Ω) (hA : MeasurableSet A)
    (w : Ω → ℝ) (hw : Measurable w)
    (T M : ℝ) (hT : 0 < T) (hM : 0 ≤ M) :
    let profile : Ω → ℝ := fun omega =>
      Real.exp (-((max (w omega - M) 0) ^ 2) / T)
    let F : ℝ → ℝ := fun v => mu.real {omega | omega ∈ A ∧ w omega ≤ v}
    let kernel : ℝ → ℝ := fun s => (2 * s / T) * Real.exp (-(s ^ 2) / T)
    Integrable (A.indicator profile) mu ∧
      IntegrableOn (fun s : ℝ => F (M + s) * kernel s) (Set.Ioi 0) ∧
      (∫ omega, A.indicator profile omega ∂mu) =
        ∫ s : ℝ in Set.Ioi 0, F (M + s) * kernel s := by
  classical
  intro profile F kernel
  let J : Ω × ℝ → ℝ := fun p => if p.1 ∈ A ∧ w p.1 ≤ M + p.2 then kernel p.2 else 0
  have hJ : Integrable J (mu.prod (volume.restrict (Set.Ioi 0))) :=
    twp_profile_product_integrable mu A hA w hw T M hT
  have hl (omega : Ω) : (∫ s : ℝ in Set.Ioi 0, J (omega, s)) = A.indicator profile omega := by
    by_cases ha : omega ∈ A
    · rw [Set.indicator_of_mem ha]
      simp only [J, ha, true_and]
      exact twp_profile_as_integral T M (w omega) hT hM
    · simp only [J, ha, false_and, ite_false, integral_zero, Set.indicator_of_notMem ha]
  have hr (s : ℝ) : (∫ omega, J (omega, s) ∂mu) = F (M + s) * kernel s := by
    have hm : MeasurableSet {omega | omega ∈ A ∧ w omega ≤ M + s} :=
      hA.inter (measurableSet_le hw measurable_const)
    calc
      _ = ∫ omega, ({omega | omega ∈ A ∧ w omega ≤ M + s}).indicator
          (fun _ => kernel s) omega ∂mu := by
        apply integral_congr_ae
        exact ae_of_all _ fun omega => by
          by_cases h : omega ∈ A ∧ w omega ≤ M + s
          · simp [J, Set.indicator, h]
          · simp [J, Set.indicator, h]
      _ = _ := by simpa only [smul_eq_mul] using integral_indicator_const (kernel s) hm
  have hl' : (fun omega => ∫ s : ℝ in Set.Ioi 0, J (omega, s)) = A.indicator profile := funext hl
  have hr' : (fun s => ∫ omega, J (omega, s) ∂mu) = fun s => F (M + s) * kernel s := funext hr
  refine ⟨hl' ▸ hJ.integral_prod_left, hr' ▸ hJ.integral_prod_right, ?_⟩
  rw [← hl', ← hr']
  exact integral_integral_swap hJ

theorem gaussian_wall_profile_of_quadratic_closed_cdf
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (A : Set Ω) (hA : MeasurableSet A)
    (w : Ω → ℝ) (hw : Measurable w)
    (K B V T M : ℝ) (hK : 0 ≤ K) (hV : 0 < V)
    (hT : 0 < T) (hM : 0 ≤ M)
    (hCDF : ∀ v : ℝ, 0 ≤ v →
      mu.real {omega | omega ∈ A ∧ w omega ≤ v} ≤ K * (v ^ 2 / V + B ^ 2)) :
    (∫ omega, A.indicator (fun omega =>
      Real.exp (-((max (w omega - M) 0) ^ 2) / T)) omega ∂mu) ≤
      K * (2 * (M ^ 2 + T) / V + B ^ 2) := by
  let k : ℝ → ℝ := fun s => (2 * s / T) * Real.exp (-(s ^ 2) / T)
  have hc := gaussian_wall_profile_layer_cake mu A hA w hw T M hT hM
  dsimp only at hc
  have hi0 := (twp_kernel_tail T 0 hT (by norm_num)).1
  have hi2 := (twp_kernel_second T hT).1
  have hg : Integrable (fun s : ℝ => (K * (2 * M ^ 2 / V + B ^ 2)) * k s +
      (K * 2 / V) * (s ^ 2 * k s)) (volume.restrict (Set.Ioi 0)) :=
    (hi0.const_mul _).add (hi2.const_mul _)
  calc
    _ = ∫ s : ℝ in Set.Ioi 0, mu.real {omega | omega ∈ A ∧ w omega ≤ M + s} * k s := hc.2.2
    _ ≤ ∫ s : ℝ in Set.Ioi 0, (K * (2 * M ^ 2 / V + B ^ 2)) * k s +
        (K * 2 / V) * (s ^ 2 * k s) := by
      apply integral_mono_ae hc.2.1 hg
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : 0 < s := hs
      have hk : 0 ≤ k s := by dsimp [k]; positivity
      have hf := hCDF (M + s) (by linarith only [hM, hs0])
      have hsq : (M + s) ^ 2 ≤ 2 * M ^ 2 + 2 * s ^ 2 := by nlinarith [sq_nonneg (M - s)]
      calc
        _ ≤ (K * ((M + s) ^ 2 / V + B ^ 2)) * k s := mul_le_mul_of_nonneg_right hf hk
        _ ≤ (K * ((2 * M ^ 2 + 2 * s ^ 2) / V + B ^ 2)) * k s :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (add_le_add (div_le_div_of_nonneg_right hsq hV.le) le_rfl) hK) hk
        _ = _ := by ring
    _ = _ := by
      rw [integral_add (hi0.const_mul _) (hi2.const_mul _), integral_const_mul,
        integral_const_mul]
      change K * (2 * M ^ 2 / V + B ^ 2) * (∫ s : ℝ in Set.Ioi 0, k s) +
        (K * 2 / V) * (∫ s : ℝ in Set.Ioi 0, s ^ 2 * k s) = _
      rw [(twp_kernel_tail T 0 hT (by norm_num)).2, (twp_kernel_second T hT).2]
      simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), neg_zero, zero_div, Real.exp_zero, mul_one]
      ring

private theorem twp_signed_strip :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu] (r : ℕ) (hr : 0 < r),
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 → 0 < (∫ z : ℝ, z ^ 2 ∂nu) →
        let scale : ℝ := Real.sqrt ((r : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu))
        let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / scale) nu
        let R : ℝ := Shao.truncationBudget normalizedLaw r 0
        ∀ (q x u s : ℝ), 0 ≤ q → 0 ≤ x → x ≤ 1 → 0 ≤ u →
          (s = 1 ∨ s = -1) →
          let wall : Shao.Path r → ℝ := fun v => x * Real.sqrt (q + Shao.energy v)
          (Measure.pi (fun _ : Fin r => nu)).real
            {v : Shao.Path r | Shao.maxWithZero (s • v) ≤ wall v ∧
              wall v - u ≤ s * Shao.prefixSum v r ∧ s * Shao.prefixSum v r ≤ wall v} ≤
              C * min 1 ((u / scale + R) ^ 2) := by
  classical
  obtain ⟨C, hC, hbound⟩ := iid_true_energy_closed_strip
  refine ⟨C, hC, ?_⟩
  intro nu hnu r hr h2 hmean hpos scale normalizedLaw R q x u s hq hx hx1 hu hs wall
  letI : IsProbabilityMeasure nu := hnu
  let nus : Measure ℝ := Measure.map (fun z : ℝ => s * z) nu
  have hm : Measurable (fun z : ℝ => s * z) := measurable_const.mul measurable_id
  have hsq (z : ℝ) : (s * z) ^ 2 = z ^ 2 := by
    rcases hs with rfl | rfl <;> ring
  have hprob : IsProbabilityMeasure nus := by dsimp [nus]; infer_instance
  letI : IsProbabilityMeasure nus := hprob
  have h2s : Integrable (fun z : ℝ => z ^ 2) nus := by
    apply (integrable_map_measure (by fun_prop) hm.aemeasurable).2
    simpa only [Function.comp_def, hsq] using h2
  have hmeans : (∫ z : ℝ, z ∂nus) = 0 := by
    rw [show nus = Measure.map (fun z : ℝ => s * z) nu from rfl,
      integral_map hm.aemeasurable (f := fun z : ℝ => z) (by fun_prop),
      integral_const_mul, hmean, mul_zero]
  have hsecond : (∫ z : ℝ, z ^ 2 ∂nus) = ∫ z : ℝ, z ^ 2 ∂nu := by
    rw [show nus = Measure.map (fun z : ℝ => s * z) nu from rfl,
      integral_map hm.aemeasurable (by fun_prop)]
    simp only [hsq]
  have hbudget : Shao.truncationBudget (Measure.map (fun z : ℝ => z / scale) nus) r 0 = R := by
    change Shao.truncationBudget (Measure.map (fun z : ℝ => z / scale) nus) r 0 =
      Shao.truncationBudget (Measure.map (fun z : ℝ => z / scale) nu) r 0
    unfold Shao.truncationBudget
    congr 1
    have hchange (rho : Measure ℝ) :
        (∫ z : ℝ, Shao.truncationF ((1 + 0) * z) ∂Measure.map (fun z : ℝ => z / scale) rho) =
          ∫ z : ℝ, Shao.truncationF ((1 + 0) * (z / scale)) ∂rho :=
      integral_map (μ := rho) (φ := fun z : ℝ => z / scale)
        (measurable_id.div_const scale).aemeasurable
        ((Shao.continuous_truncationF.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
    rw [hchange, hchange]
    rw [show nus = Measure.map (fun z : ℝ => s * z) nu from rfl,
      integral_map (f := fun z : ℝ => Shao.truncationF ((1 + 0) * (z / scale))) hm.aemeasurable
        ((Shao.continuous_truncationF.comp (continuous_const.mul (continuous_id.div_const scale))).aestronglyMeasurable)]
    apply integral_congr_ae
    filter_upwards [] with z
    rcases hs with rfl | rfl
    · simp
    · simpa only [add_zero, one_mul, neg_one_mul, neg_div] using Shao.truncationF_neg (z / scale)
  have hb := hbound nus r hr h2s hmeans (hsecond ▸ hpos) q x u hq hx hx1 hu
  dsimp only at hb
  rw [hsecond, hbudget] at hb
  let S : Shao.Path r → Shao.Path r := fun v => s • v
  have hSm : Measurable S := Measurable.of_eval fun i => measurable_const.mul (measurable_pi_apply i)
  have hmap : Measure.map S (Measure.pi (fun _ : Fin r => nu)) = Measure.pi (fun _ : Fin r => nus) :=
    Measure.pi_map_pi (fun _ : Fin r => hm.aemeasurable)
  have hE : MeasurableSet {v : Shao.Path r |
      Shao.maxWithZero v ≤ x * Real.sqrt (q + Shao.energy v) ∧
      x * Real.sqrt (q + Shao.energy v) - u ≤ Shao.prefixSum v r ∧
      Shao.prefixSum v r ≤ x * Real.sqrt (q + Shao.energy v)} := by
    have hwm : Measurable (fun v : Shao.Path r => x * Real.sqrt (q + Shao.energy v)) :=
      measurable_const.mul ((measurable_const.add Shao.measurable_energy).sqrt)
    exact (measurableSet_le Shao.measurable_maxWithZero hwm).inter
      ((measurableSet_le (hwm.sub_const u) (Shao.measurable_prefixSum r)).inter
        (measurableSet_le (Shao.measurable_prefixSum r) hwm))
  have he (v : Shao.Path r) : Shao.energy (s • v) = Shao.energy v := by
    rw [Shao.energy_smul]
    rcases hs with rfl | rfl <;> norm_num
  rw [← hmap] at hb
  simpa only [Measure.real_def, Measure.map_apply hSm hE, Set.preimage_setOf_eq,
    S, he, Shao.prefixSum_smul] using hb

private theorem twp_survival_measurable
    (r : ℕ) (q x : ℝ) (signs : Finset ℝ) (closed : Bool) :
    MeasurableSet {v : Shao.Path r | ∀ s ∈ signs,
      if closed = true then Shao.maxWithZero (s • v) ≤ x * Real.sqrt (q + Shao.energy v)
      else Shao.maxWithZero (s • v) < x * Real.sqrt (q + Shao.energy v)} := by
  classical
  induction signs using Finset.induction_on with
  | empty => simp
  | @insert s signs hs ih =>
    simp only [Finset.forall_mem_insert]
    have hsm : Measurable (fun v : Shao.Path r => Shao.maxWithZero (s • v)) :=
      Shao.measurable_maxWithZero.comp (Measurable.of_eval fun i =>
        measurable_const.mul (measurable_pi_apply i))
    have hwm : Measurable (fun v : Shao.Path r => x * Real.sqrt (q + Shao.energy v)) :=
      measurable_const.mul ((measurable_const.add Shao.measurable_energy).sqrt)
    have hsm' : MeasurableSet {v : Shao.Path r | if closed = true then
        Shao.maxWithZero (s • v) ≤ x * Real.sqrt (q + Shao.energy v)
        else Shao.maxWithZero (s • v) < x * Real.sqrt (q + Shao.energy v)} := by
      split_ifs
      · exact measurableSet_le hsm hwm
      · exact measurableSet_lt hsm hwm
    exact hsm'.inter ih

private theorem twp_suffix_geometry
    (T d b : ℝ) (hT : 0 < T) (hb : b ^ 2 ≤ T) :
    1 ≤ (1 + |d| / Real.sqrt T) ^ 2 ∧
      (|b| + |d|) ^ 2 + T ≤ 2 * T * (1 + |d| / Real.sqrt T) ^ 2 := by
  have ht : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have ht2 : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt hT.le
  have hD : 1 ≤ 1 + |d| / Real.sqrt T := by linarith [div_nonneg (abs_nonneg d) ht.le]
  have hb' : |b| ≤ Real.sqrt T := (sq_le_sq₀ (abs_nonneg b) ht.le).1 (by simpa only [sq_abs, ht2] using hb)
  have hm : |b| + |d| ≤ Real.sqrt T * (1 + |d| / Real.sqrt T) := by
    rw [mul_add, mul_one, mul_div_cancel₀ _ ht.ne']
    exact add_le_add hb' le_rfl
  have hm2 := sq_le_sq₀ (add_nonneg (abs_nonneg b) (abs_nonneg d)) (by positivity) |>.2 hm
  rw [mul_pow, ht2] at hm2
  have hD2 : 1 ≤ (1 + |d| / Real.sqrt T) ^ 2 := by nlinarith only [hD]
  exact ⟨hD2, by nlinarith only [hm2, mul_le_mul_of_nonneg_left hD2 hT.le]⟩

theorem iid_true_wall_gaussian_profile :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu] (r : ℕ) (hr : 0 < r),
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 → 0 < (∫ z : ℝ, z ^ 2 ∂nu) →
        let V : ℝ := (r : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu)
        let scale : ℝ := Real.sqrt V
        let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / scale) nu
        let R : ℝ := Shao.truncationBudget normalizedLaw r 0
        ∀ (q T d b x : ℝ), 0 ≤ q → 0 < T → b ^ 2 ≤ T → 0 < x → x ≤ 1 →
          ∀ (signs : Finset ℝ), (∀ s ∈ signs, s = 1 ∨ s = -1) →
            ∀ (closed : Bool) (wallSign : ℝ), wallSign ∈ signs →
              let D : ℝ := 1 + |d| / Real.sqrt T
              let Mstar : ℝ := |b| + |d|
              let wall : Shao.Path r → ℝ := fun v => x * Real.sqrt (q + Shao.energy v)
              let A : Set (Shao.Path r) := {v | ∀ s ∈ signs,
                if closed = true then Shao.maxWithZero (s • v) ≤ wall v
                else Shao.maxWithZero (s • v) < wall v}
              let w : Shao.Path r → ℝ := fun v => wall v - wallSign * Shao.prefixSum v r
              (∫ v : Shao.Path r, A.indicator (fun v =>
                Real.exp (-((max (w v - Mstar) 0) ^ 2) / T)) v
                ∂Measure.pi (fun _ : Fin r => nu)) ≤
                C * D ^ 2 * (T / V + R ^ 2) := by
  classical
  obtain ⟨Cs, hCs, hstrip⟩ := twp_signed_strip
  refine ⟨8 * Cs, by positivity, ?_⟩
  intro nu hnu r hr h2 hmean hsecond V scale normalizedLaw R q T d b x hq hT hb hx hx1
    signs hsigns closed wallSign hmem D Mstar wall A w
  letI : IsProbabilityMeasure nu := hnu
  let P : Measure (Shao.Path r) := Measure.pi (fun _ : Fin r => nu)
  have hV : 0 < V := mul_pos (by exact_mod_cast hr) hsecond
  have hs : 0 < scale := Real.sqrt_pos.2 hV
  have hs2 : scale ^ 2 = V := Real.sq_sqrt hV.le
  have hwm : Measurable wall := measurable_const.mul ((measurable_const.add Shao.measurable_energy).sqrt)
  have hw : Measurable w := hwm.sub (measurable_const.mul (Shao.measurable_prefixSum r))
  have hA : MeasurableSet A := twp_survival_measurable r q x signs closed
  have hR : 0 ≤ R := by
    change 0 ≤ (r : ℝ) * (∫ z, Shao.truncationF ((1 + 0) * z) ∂normalizedLaw)
    exact mul_nonneg (Nat.cast_nonneg r) (integral_nonneg fun z => Shao.truncationF_nonneg _)
  have hCDF (u : ℝ) (hu : 0 ≤ u) : P.real {v | v ∈ A ∧ w v ≤ u} ≤
      (2 * Cs) * (u ^ 2 / V + R ^ 2) := by
    have hbnd := hstrip nu r hr h2 hmean hsecond q x u wallSign hq hx.le hx1 hu (hsigns wallSign hmem)
    dsimp only at hbnd
    change P.real {v | v ∈ A ∧ w v ≤ u} ≤ _
    have he : {v | v ∈ A ∧ w v ≤ u} ⊆ {v : Shao.Path r |
        Shao.maxWithZero (wallSign • v) ≤ wall v ∧
        wall v - u ≤ wallSign * Shao.prefixSum v r ∧ wallSign * Shao.prefixSum v r ≤ wall v} := by
      intro v hv
      have hvmax : Shao.maxWithZero (wallSign • v) ≤ wall v := by
        have hh := hv.1 wallSign hmem
        by_cases hc : closed = true
        · simpa only [hc, ite_true] using hh
        · exact (show Shao.maxWithZero (wallSign • v) < wall v by simpa [hc] using hh).le
      have hvsum := (Shao.maxWithZero_le_iff (wallSign • v) (wall v)).1 hvmax r le_rfl
      rw [Shao.prefixSum_smul] at hvsum
      refine ⟨hvmax, ?_, hvsum⟩
      have hvw : wall v - wallSign * Shao.prefixSum v r ≤ u := hv.2
      linarith only [hvw]
    have hsq : (u / scale + R) ^ 2 ≤ 2 * (u ^ 2 / V + R ^ 2) := by
      have hh : (u / scale) ^ 2 = u ^ 2 / V := by rw [div_pow, hs2]
      nlinarith only [sq_nonneg (u / scale - R), hh]
    calc
      _ ≤ P.real {v : Shao.Path r | Shao.maxWithZero (wallSign • v) ≤ wall v ∧
          wall v - u ≤ wallSign * Shao.prefixSum v r ∧ wallSign * Shao.prefixSum v r ≤ wall v} :=
        measureReal_mono he
      _ ≤ Cs * min 1 ((u / scale + R) ^ 2) := hbnd
      _ ≤ Cs * ((u / scale + R) ^ 2) := mul_le_mul_of_nonneg_left (min_le_right _ _) hCs.le
      _ ≤ Cs * (2 * (u ^ 2 / V + R ^ 2)) := mul_le_mul_of_nonneg_left hsq hCs.le
      _ = _ := by ring
  have hg := gaussian_wall_profile_of_quadratic_closed_cdf P A hA w hw (2 * Cs) R V T Mstar
    (by positivity) hV hT (add_nonneg (abs_nonneg b) (abs_nonneg d)) hCDF
  have hgeom := twp_suffix_geometry T d b hT hb
  change 1 ≤ D ^ 2 ∧ Mstar ^ 2 + T ≤ 2 * T * D ^ 2 at hgeom
  apply hg.trans
  have hmain : 2 * (Mstar ^ 2 + T) / V ≤ 4 * D ^ 2 * (T / V) := by
    calc
      _ ≤ 2 * (2 * T * D ^ 2) / V := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hgeom.2 (by norm_num)) hV.le
      _ = _ := by ring
  have hRpay : R ^ 2 ≤ D ^ 2 * R ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_right hgeom.1 (sq_nonneg R)]
  have htot : 2 * (Mstar ^ 2 + T) / V + R ^ 2 ≤ 4 * D ^ 2 * (T / V + R ^ 2) := by
    have hn : 0 ≤ D ^ 2 * R ^ 2 := mul_nonneg (sq_nonneg D) (sq_nonneg R)
    nlinarith only [hmain, hRpay, hn]
  calc
    _ ≤ (2 * Cs) * (4 * D ^ 2 * (T / V + R ^ 2)) := mul_le_mul_of_nonneg_left htot (by positivity)
    _ = _ := by ring

theorem iid_fixed_suffix_gaussian_wall_profiles :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu] (r : ℕ) (hr : 0 < r),
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 → 0 < (∫ z : ℝ, z ^ 2 ∂nu) →
        let V : ℝ := (r : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu)
        let scale : ℝ := Real.sqrt V
        let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / scale) nu
        let R : ℝ := Shao.truncationBudget normalizedLaw r 0
        ∀ (t : ℕ) (suffix : Shao.Path (t + 1)),
          let T : ℝ := Shao.energy suffix
          let d : ℝ := Shao.prefixSum suffix (t + 1)
          let b : ℝ := suffix 0
          let D : ℝ := 1 + |d| / Real.sqrt T
          0 < T → ∀ (x : ℝ), 0 < x → x ≤ 1 →
            ∀ (signs : Finset ℝ), (∀ s ∈ signs, s = 1 ∨ s = -1) →
              ∀ (closed : Bool),
                let wall : Shao.Path r → ℝ := fun v => x * Real.sqrt (T + Shao.energy v)
                let A : Set (Shao.Path r) := {v | ∀ s ∈ signs,
                  if closed = true then Shao.maxWithZero (s • v) ≤ wall v
                  else Shao.maxWithZero (s • v) < wall v}
                let profiles : Shao.Path r → ℝ := fun v =>
                  ∑ s ∈ signs, Real.exp
                    (-((max (wall v - s * Shao.prefixSum v r - (|b| + max (s * d) 0)) 0) ^ 2) / T)
                (∫ v : Shao.Path r, A.indicator profiles v
                  ∂Measure.pi (fun _ : Fin r => nu)) ≤
                  C * D ^ 2 * (T / V + R ^ 2) := by
  classical
  obtain ⟨C, hC, hbound⟩ := iid_true_wall_gaussian_profile
  refine ⟨2 * C, by positivity, ?_⟩
  intro nu hnu r hr h2 hmean hsecond V scale normalizedLaw R t suffix T d b D hT x hx hx1 signs hsigns closed wall A profiles
  letI : IsProbabilityMeasure nu := hnu
  let P : Measure (Shao.Path r) := Measure.pi (fun _ : Fin r => nu)
  have hA : MeasurableSet A := twp_survival_measurable r T x signs closed
  have hwm : Measurable wall := measurable_const.mul ((measurable_const.add Shao.measurable_energy).sqrt)
  have hb : b ^ 2 ≤ T := by
    change (suffix (0 : Fin (t + 1))) ^ 2 ≤ ∑ i : Fin (t + 1), (suffix i) ^ 2
    exact Finset.single_le_sum (fun i _ => sq_nonneg (suffix i)) (Finset.mem_univ (0 : Fin (t + 1)))
  let f : ℝ → Shao.Path r → ℝ := fun s v =>
    Real.exp (-((max (wall v - s * Shao.prefixSum v r - (|b| + max (s * d) 0)) 0) ^ 2) / T)
  have hi (s : ℝ) : Integrable (A.indicator (f s)) P := by
    exact (gaussian_wall_profile_layer_cake P A hA
      (fun v => wall v - s * Shao.prefixSum v r)
      (hwm.sub (measurable_const.mul (Shao.measurable_prefixSum r))) T (|b| + max (s * d) 0)
      hT (add_nonneg (abs_nonneg b) (le_max_right _ _))).1
  have hterm (s : ℝ) (hs : s ∈ signs) : (∫ v, A.indicator (f s) v ∂P) ≤
      C * D ^ 2 * (T / V + R ^ 2) := by
    have hbnd := hbound nu r hr h2 hmean hsecond T T d b x hT.le hT hb hx hx1 signs hsigns closed s hs
    dsimp only at hbnd
    have hi' := (gaussian_wall_profile_layer_cake P A hA
      (fun v => wall v - s * Shao.prefixSum v r)
      (hwm.sub (measurable_const.mul (Shao.measurable_prefixSum r))) T (|b| + |d|)
      hT (add_nonneg (abs_nonneg b) (abs_nonneg d))).1
    apply (integral_mono_ae (hi s) hi' ?_).trans hbnd
    exact ae_of_all _ fun v => by
      by_cases hv : v ∈ A
      · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv]
        have hsd : s * d ≤ |d| := by
          rcases hsigns s hs with rfl | rfl
          · simpa only [one_mul] using le_abs_self d
          · simpa only [neg_one_mul] using neg_le_abs d
        have hm : |b| + max (s * d) 0 ≤ |b| + |d| :=
          add_le_add le_rfl (max_le hsd (abs_nonneg d))
        have hmax : max (wall v - s * Shao.prefixSum v r - (|b| + |d|)) 0 ≤
            max (wall v - s * Shao.prefixSum v r - (|b| + max (s * d) 0)) 0 :=
          max_le_max_right 0 (by linarith only [hm])
        have hsq := (sq_le_sq₀ (le_max_right _ _) (le_max_right _ _)).2 hmax
        exact Real.exp_le_exp.2 (div_le_div_of_nonneg_right (neg_le_neg hsq) hT.le)
      · simp only [Set.indicator_of_notMem hv, le_refl]
  have he : A.indicator profiles = fun v => ∑ s ∈ signs, A.indicator (f s) v := by
    funext v
    by_cases hv : v ∈ A
    · simp only [Set.indicator_of_mem hv]; rfl
    · simp only [Set.indicator_of_notMem hv, Finset.sum_const_zero]
  have hsub : signs ⊆ ({1, -1} : Finset ℝ) := by
    intro s hs
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hsigns s hs
  have hc : (signs.card : ℝ) ≤ 2 := by
    have hh := Finset.card_le_card hsub
    norm_num at hh
    exact_mod_cast hh
  have hV : 0 < V := mul_pos (by exact_mod_cast hr) hsecond
  have hnonneg : 0 ≤ C * D ^ 2 * (T / V + R ^ 2) := by positivity
  calc
    _ = ∑ s ∈ signs, ∫ v, A.indicator (f s) v ∂P := by
      rw [he]
      exact integral_finsetSum _ (fun s _ => hi s)
    _ ≤ ∑ s ∈ signs, C * D ^ 2 * (T / V + R ^ 2) := Finset.sum_le_sum hterm
    _ = (signs.card : ℝ) * (C * D ^ 2 * (T / V + R ^ 2)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * (C * D ^ 2 * (T / V + R ^ 2)) := mul_le_mul_of_nonneg_right hc hnonneg
    _ = _ := by ring

end Shao.Probability
