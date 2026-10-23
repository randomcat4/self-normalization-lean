import Shao.Probability.SourceFourierScale
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

private theorem shortTime_power_integral (b r : ℝ) (hb : 0 < b) (hr : -1 < r) :
    IntegrableOn (fun t : ℝ => t ^ r) (Set.Ioo 0 b) ∧
      (∫ t in Set.Ioo 0 b, t ^ r) = b ^ (r + 1) / (r + 1) := by
  have hi : IntervalIntegrable (fun t : ℝ => t ^ r) volume 0 b :=
    intervalIntegral.intervalIntegrable_rpow' hr
  have hic : IntegrableOn (fun t : ℝ => t ^ r) (Set.Ioc 0 b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mp hi
  refine ⟨hic.mono_set Set.Ioo_subset_Ioc_self, ?_⟩
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hb.le,
    integral_rpow (Or.inl hr), Real.zero_rpow (by linarith : r + 1 ≠ 0),
    sub_zero]

private theorem shortTime_sqrt_scale (y r : ℝ) (hy : 0 < y) :
    Real.sqrt y * (y ^ 2) ^ r = y ^ ((1 / 2 : ℝ) + 2 * r) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast y 2,
    ← Real.rpow_mul hy.le, ← Real.rpow_add hy]
  norm_num

theorem sourceShortTime_R_integrals (y : ℝ) (hy : 0 < y) :
    let R : ℝ → ℝ := fun T => 1 + Real.sqrt y * T ^ (-(1 / 4 : ℝ))
    IntegrableOn R (Set.Ioo 0 (y ^ 2)) ∧
      IntegrableOn (fun T => T * R T) (Set.Ioo 0 (y ^ 2)) ∧
      (1 / y ^ 2) * (∫ T in Set.Ioo 0 (y ^ 2), R T) = (7 / 3 : ℝ) ∧
      (1 / y ^ 2) * (∫ T in Set.Ioo 0 (y ^ 2), T * R T) = (15 / 14 : ℝ) * y ^ 2 := by
  dsimp only
  have hy2 : 0 < y ^ 2 := sq_pos_of_pos hy
  obtain ⟨hi0, hv0⟩ := shortTime_power_integral (y ^ 2) 0 hy2 (by norm_num)
  obtain ⟨hi1, hv1⟩ := shortTime_power_integral (y ^ 2) 1 hy2 (by norm_num)
  obtain ⟨hiq, hvq⟩ := shortTime_power_integral (y ^ 2) (-(1 / 4 : ℝ)) hy2 (by norm_num)
  obtain ⟨hit, hvt⟩ := shortTime_power_integral (y ^ 2) (3 / 4 : ℝ) hy2 (by norm_num)
  have hic : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo 0 (y ^ 2)) := by
    simpa only [Real.rpow_zero] using hi0
  have hii : IntegrableOn (fun t : ℝ => t) (Set.Ioo 0 (y ^ 2)) := by
    simpa only [Real.rpow_one] using hi1
  have hR := hic.add (hiq.const_mul (Real.sqrt y))
  have hTR := hii.add (hit.const_mul (Real.sqrt y))
  have hpoint (t : ℝ) (ht : t ∈ Set.Ioo 0 (y ^ 2)) :
      t * (1 + Real.sqrt y * t ^ (-(1 / 4 : ℝ))) = t + Real.sqrt y * t ^ (3 / 4 : ℝ) := by
    have hp : t * t ^ (-(1 / 4 : ℝ)) = t ^ (3 / 4 : ℝ) := by
      calc
        _ = t ^ (1 : ℝ) * t ^ (-(1 / 4 : ℝ)) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add ht.1]; norm_num
    calc
      _ = t + Real.sqrt y * (t * t ^ (-(1 / 4 : ℝ))) := by ring
      _ = _ := by rw [hp]
  have hTR' : IntegrableOn (fun t : ℝ => t * (1 + Real.sqrt y * t ^ (-(1 / 4 : ℝ))))
      (Set.Ioo 0 (y ^ 2)) := hTR.congr_fun (fun t ht => (hpoint t ht).symm) measurableSet_Ioo
  have hRval : (∫ t in Set.Ioo 0 (y ^ 2), 1 + Real.sqrt y * t ^ (-(1 / 4 : ℝ))) =
      (7 / 3 : ℝ) * y ^ 2 := by
    rw [integral_add hic (hiq.const_mul (Real.sqrt y)), integral_const_mul]
    have hc : (∫ t in Set.Ioo 0 (y ^ 2), (1 : ℝ)) = y ^ 2 := by
      simpa only [Real.rpow_zero, zero_add, Real.rpow_one, div_one] using hv0
    rw [hc, hvq]
    norm_num only [neg_add_rev, add_neg_cancel, sub_eq_add_neg] at *
    have hs := shortTime_sqrt_scale y (3 / 4 : ℝ) hy
    norm_num at hs
    rw [← mul_div_assoc, hs]
    ring
  have hTRval : (∫ t in Set.Ioo 0 (y ^ 2), t * (1 + Real.sqrt y * t ^ (-(1 / 4 : ℝ)))) =
      (15 / 14 : ℝ) * y ^ 4 := by
    rw [setIntegral_congr_fun measurableSet_Ioo hpoint,
      integral_add hii (hit.const_mul (Real.sqrt y)), integral_const_mul]
    have hc : (∫ t in Set.Ioo 0 (y ^ 2), t) = (y ^ 2) ^ 2 / 2 := by
      simpa only [Real.rpow_one, one_add_one_eq_two, Real.rpow_two] using hv1
    rw [hc, hvt]
    have hs := shortTime_sqrt_scale y (7 / 4 : ℝ) hy
    norm_num at hs
    norm_num
    rw [← mul_div_assoc, hs]
    ring
  refine ⟨hR, hTR', ?_, ?_⟩
  · rw [hRval]
    field_simp
  · rw [hTRval]
    field_simp

private theorem shortTime_grid_power (n : ℕ) (m gamma L y a : ℝ)
    (hm : 0 < m) (hg : 0 < gamma) (hmg : m ≤ gamma ^ 2) (hL : 2 ≤ L) :
    let T : ℕ → ℝ := fun i => ((n - i : ℕ) : ℝ) * m
    let J : Finset ℕ := (Finset.range (n + 1)).filter
      (fun i => n / 2 < i ∧ L * gamma ^ 2 ≤ T i ∧ T i < y ^ 2)
    IntegrableOn (fun t : ℝ => t ^ a) (Set.Icc (L * gamma ^ 2 / 2) (y ^ 2)) ∧
      m * (∑ i ∈ J, T i ^ a) ≤
        (2 : ℝ) ^ |a| * (∫ t in Set.Icc (L * gamma ^ 2 / 2) (y ^ 2), t ^ a) := by
  classical
  let T : ℕ → ℝ := fun i => ((n - i : ℕ) : ℝ) * m
  let J : Finset ℕ := (Finset.range (n + 1)).filter
    (fun i => n / 2 < i ∧ L * gamma ^ 2 ≤ T i ∧ T i < y ^ 2)
  let W : ℕ → Set ℝ := fun i => Set.Ioc (T i - m) (T i)
  let S : Set ℝ := Set.Icc (L * gamma ^ 2 / 2) (y ^ 2)
  change IntegrableOn (fun t : ℝ => t ^ a) S ∧ _
  have hleft : 0 < L * gamma ^ 2 / 2 := by positivity
  have hcont : ContinuousOn (fun t : ℝ => t ^ a) S :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (hleft.trans_le ht.1)))
  have hInt : IntegrableOn (fun t : ℝ => t ^ a) S := hcont.integrableOn_Icc
  have htwom : 2 * m ≤ L * gamma ^ 2 :=
    (mul_le_mul_of_nonneg_left hmg (by norm_num : (0 : ℝ) ≤ 2)).trans
      (mul_le_mul_of_nonneg_right hL (sq_nonneg gamma))
  have hguard (i : ℕ) (hi : i ∈ J) : i ≤ n ∧ L * gamma ^ 2 ≤ T i ∧ T i < y ^ 2 := by
    have hp := Finset.mem_filter.mp hi
    exact ⟨by have := Finset.mem_range.mp hp.1; omega, hp.2.2.1, hp.2.2.2⟩
  have hTpos (i : ℕ) (hi : i ∈ J) : 0 < T i :=
    (by positivity : 0 < L * gamma ^ 2).trans_le (hguard i hi).2.1
  have hWsub (i : ℕ) (hi : i ∈ J) : W i ⊆ S := by
    intro t ht
    have h := hguard i hi
    exact ⟨by have hlow := ht.1; linarith only [hlow, h.2.1, htwom], ht.2.trans h.2.2.le⟩
  have hWi (i : ℕ) (hi : i ∈ J) : IntegrableOn (fun t : ℝ => t ^ a) (W i) :=
    hInt.mono_set (hWsub i hi)
  have hsep (i j : ℕ) (hij : i < j) (hj : j ≤ n) : T j ≤ T i - m := by
    have hn : n - j + 1 ≤ n - i := by omega
    have hc : ((n - j : ℕ) : ℝ) + 1 ≤ ((n - i : ℕ) : ℝ) := by exact_mod_cast hn
    have hh := mul_le_mul_of_nonneg_right hc hm.le
    dsimp [T]
    nlinarith only [hh]
  have hdis : Set.Pairwise (↑J : Set ℕ) (fun i j => Disjoint (W i) (W j)) := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro t hti htj
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hs := hsep i j hij (hguard j hj).1
      exact (not_lt_of_ge (htj.2.trans hs)) hti.1
    · have hs := hsep j i hji (hguard i hi).1
      exact (not_lt_of_ge (hti.2.trans hs)) htj.1
  have hfactor : 1 ≤ (2 : ℝ) ^ |a| := Real.one_le_rpow (by norm_num) (abs_nonneg a)
  have hlocal (i : ℕ) (hi : i ∈ J) :
      m * T i ^ a ≤ (2 : ℝ) ^ |a| * (∫ t in W i, t ^ a) := by
    have hpoint (t : ℝ) (ht : t ∈ W i) : T i ^ a ≤ (2 : ℝ) ^ |a| * t ^ a := by
      have ht0 : 0 < t := hleft.trans_le (hWsub i hi ht).1
      have hTi := hTpos i hi
      have hhalf : T i ≤ 2 * t := by
        have h := (hguard i hi).2.1
        have hlow := ht.1
        linarith only [hlow, h, htwom]
      by_cases ha : 0 ≤ a
      · rw [abs_of_nonneg ha]
        exact (Real.rpow_le_rpow hTi.le hhalf ha).trans_eq (Real.mul_rpow (by norm_num) ht0.le)
      · exact (Real.rpow_le_rpow_of_nonpos ht0 ht.2 (le_of_not_ge ha)).trans
          (le_mul_of_one_le_left (Real.rpow_nonneg ht0.le a) hfactor)
    have hc : IntegrableOn (fun _ : ℝ => T i ^ a) (W i) := by
      exact (continuous_const.integrableOn_Icc : IntegrableOn (fun _ : ℝ => T i ^ a)
        (Set.Icc (T i - m) (T i))).mono_set Set.Ioc_subset_Icc_self
    have hh := setIntegral_mono_on hc ((hWi i hi).const_mul ((2 : ℝ) ^ |a|))
      measurableSet_Ioc hpoint
    have hcv : (∫ _t in W i, T i ^ a) = m * T i ^ a := by
      dsimp [W]
      simp only [integral_const, measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioc,
        show T i - (T i - m) = m by ring, ENNReal.toReal_ofReal hm.le, smul_eq_mul]
    rw [hcv, integral_const_mul] at hh
    exact hh
  have hunion : (⋃ i ∈ J, W i) ⊆ S := by
    intro t ht
    obtain ⟨i, hi, hti⟩ := Set.mem_iUnion₂.mp ht
    exact hWsub i hi hti
  have hnonneg : 0 ≤ᵐ[volume.restrict S] (fun t : ℝ => t ^ a) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact Real.rpow_nonneg (hleft.le.trans ht.1) a
  have henlarge := setIntegral_mono_set hInt hnonneg (Filter.Eventually.of_forall hunion)
  have hsum := integral_biUnion_finset J (fun _ _ => measurableSet_Ioc) hdis hWi
  refine ⟨hInt, ?_⟩
  calc
    m * (∑ i ∈ J, T i ^ a) = ∑ i ∈ J, m * T i ^ a := by rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ J, (2 : ℝ) ^ |a| * (∫ t in W i, t ^ a) := Finset.sum_le_sum hlocal
    _ = (2 : ℝ) ^ |a| * (∫ t in ⋃ i ∈ J, W i, t ^ a) := by rw [hsum, Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left henlarge (Real.rpow_nonneg (by norm_num) _)

theorem sourceTruncation_remainingClock_power_integral_comparison :
    ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
      ∀ n : ℕ, Integrable (fun z : ℝ => z ^ 2) ν0 →
        (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν0) = 1 →
        (∫ z : ℝ, z ∂ν0) = 0 →
        ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 2 →
          Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
          ∀ L2 y a : ℝ, 2 ≤ L2 → 0 < y →
            let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
            let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂ρ
            let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
            let T : ℕ → ℝ := fun i => ((n - i : ℕ) : ℝ) * m2
            let J : Finset ℕ := (Finset.range (n + 1)).filter
              (fun i => n / 2 < i ∧ L2 * gamma ^ 2 ≤ T i ∧ T i < y ^ 2)
            IntegrableOn (fun t : ℝ => t ^ a) (Set.Icc (L2 * gamma ^ 2 / 2) (y ^ 2)) ∧
              m2 * (∑ i ∈ J, T i ^ a) ≤
                (2 : ℝ) ^ |a| * (∫ t in Set.Icc (L2 * gamma ^ 2 / 2) (y ^ 2), t ^ a) := by
  intro ν0 hp n h2 hnorm hmean x epsilon hx he hehalf hbudget L2 y a hL hy
  letI : IsProbabilityMeasure ν0 := hp
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
  let mu : ℝ := ∫ z : ℝ, z ∂ρ
  let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂ρ
  let V : ℝ := variance (id : ℝ → ℝ) ρ
  let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂ρ) / V
  obtain ⟨_, _, _, hVeq, _, hVp, _, _⟩ :=
    Shao.sourceTruncation_variance_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget
  change V = m2 - mu ^ 2 at hVeq
  change 0 < V at hVp
  have hm2 : 0 < m2 := by nlinarith only [hVeq, hVp, sq_nonneg mu]
  obtain ⟨_, hgp, _, hmg, _⟩ :=
    Shao.sourceTruncation_gamma_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget
  exact shortTime_grid_power n m2 gamma L2 y a hm2 hgp hmg hL

private theorem shortTime_grid_power_full (n : ℕ) (m gamma L y a : ℝ)
    (hm : 0 < m) (hg : 0 < gamma) (hmg : m ≤ gamma ^ 2) (hL : 2 ≤ L)
    (hy : 0 < y) (ha : -1 < a) (ha1 : |a| ≤ 1) :
    let T : ℕ → ℝ := fun i => ((n - i : ℕ) : ℝ) * m
    let J : Finset ℕ := (Finset.range (n + 1)).filter
      (fun i => n / 2 < i ∧ L * gamma ^ 2 ≤ T i ∧ T i < y ^ 2)
    m * (∑ i ∈ J, T i ^ a) ≤ 2 * (∫ t in Set.Ioo 0 (y ^ 2), t ^ a) := by
  dsimp only
  obtain ⟨hi, hp⟩ := shortTime_grid_power n m gamma L y a hm hg hmg hL
  have hleft : 0 < L * gamma ^ 2 / 2 := by positivity
  have hn : 0 ≤ᵐ[volume.restrict (Set.Icc (L * gamma ^ 2 / 2) (y ^ 2))]
      (fun t : ℝ => t ^ a) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact Real.rpow_nonneg (hleft.le.trans ht.1) a
  have hip : 0 ≤ ∫ t in Set.Icc (L * gamma ^ 2 / 2) (y ^ 2), t ^ a := integral_nonneg_of_ae hn
  have hf : (2 : ℝ) ^ |a| ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ha1
  have hfull : IntegrableOn (fun t : ℝ => t ^ a) (Set.Ioc 0 (y ^ 2)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (sq_nonneg y)).mp
      (intervalIntegral.intervalIntegrable_rpow' ha)
  have hnfull : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 (y ^ 2))] (fun t : ℝ => t ^ a) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le a
  have hsubset : Set.Icc (L * gamma ^ 2 / 2) (y ^ 2) ⊆ Set.Ioc 0 (y ^ 2) :=
    fun _ ht => ⟨hleft.trans_le ht.1, ht.2⟩
  have hle := setIntegral_mono_set hfull hnfull (Filter.Eventually.of_forall hsubset)
  rw [integral_Ioc_eq_integral_Ioo] at hle
  exact hp.trans ((mul_le_mul_of_nonneg_right hf hip).trans (mul_le_mul_of_nonneg_left hle (by norm_num)))

private theorem shortTime_grid_R (n : ℕ) (m gamma L y : ℝ)
    (hm : 0 < m) (hg : 0 < gamma) (hmg : m ≤ gamma ^ 2) (hL : 2 ≤ L) (hy : 0 < y) :
    let T : ℕ → ℝ := fun i => ((n - i : ℕ) : ℝ) * m
    let J : Finset ℕ := (Finset.range (n + 1)).filter
      (fun i => n / 2 < i ∧ L * gamma ^ 2 ≤ T i ∧ T i < y ^ 2)
    let R : ℝ → ℝ := fun t => 1 + Real.sqrt y * t ^ (-(1 / 4 : ℝ))
    m / y ^ 2 * (∑ i ∈ J, R (T i)) ≤ 10 ∧
      m / y ^ 2 * (∑ i ∈ J, T i * R (T i)) ≤ 10 * y ^ 2 := by
  classical
  let T : ℕ → ℝ := fun i => ((n - i : ℕ) : ℝ) * m
  let J : Finset ℕ := (Finset.range (n + 1)).filter
    (fun i => n / 2 < i ∧ L * gamma ^ 2 ≤ T i ∧ T i < y ^ 2)
  let R : ℝ → ℝ := fun t => 1 + Real.sqrt y * t ^ (-(1 / 4 : ℝ))
  change m / y ^ 2 * (∑ i ∈ J, R (T i)) ≤ 10 ∧ _
  have h0 := shortTime_grid_power_full n m gamma L y 0 hm hg hmg hL hy (by norm_num) (by norm_num)
  have hq := shortTime_grid_power_full n m gamma L y (-(1 / 4 : ℝ)) hm hg hmg hL hy (by norm_num) (by norm_num)
  have h1 := shortTime_grid_power_full n m gamma L y 1 hm hg hmg hL hy (by norm_num) (by norm_num)
  have ht := shortTime_grid_power_full n m gamma L y (3 / 4 : ℝ) hm hg hmg hL hy (by norm_num) (by norm_num)
  change m * (∑ i ∈ J, T i ^ (0 : ℝ)) ≤ _ at h0
  change m * (∑ i ∈ J, T i ^ (-(1 / 4 : ℝ))) ≤ _ at hq
  change m * (∑ i ∈ J, T i ^ (1 : ℝ)) ≤ _ at h1
  change m * (∑ i ∈ J, T i ^ (3 / 4 : ℝ)) ≤ _ at ht
  obtain ⟨hi0, _⟩ := shortTime_power_integral (y ^ 2) 0 (sq_pos_of_pos hy) (by norm_num)
  obtain ⟨hiq, _⟩ := shortTime_power_integral (y ^ 2) (-(1 / 4 : ℝ)) (sq_pos_of_pos hy) (by norm_num)
  obtain ⟨hi1, _⟩ := shortTime_power_integral (y ^ 2) 1 (sq_pos_of_pos hy) (by norm_num)
  obtain ⟨hit, _⟩ := shortTime_power_integral (y ^ 2) (3 / 4 : ℝ) (sq_pos_of_pos hy) (by norm_num)
  have hic : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo 0 (y ^ 2)) := by
    simpa only [Real.rpow_zero] using hi0
  have hii : IntegrableOn (fun t : ℝ => t) (Set.Ioo 0 (y ^ 2)) := by
    simpa only [Real.rpow_one] using hi1
  have hTpos (i : ℕ) (hi : i ∈ J) : 0 < T i := by
    have hh := (Finset.mem_filter.mp hi).2.2.1
    exact (by positivity : 0 < L * gamma ^ 2).trans_le hh
  have hpoint (t : ℝ) (ht : 0 < t) : t * R t = t + Real.sqrt y * t ^ (3 / 4 : ℝ) := by
    have hp : t * t ^ (-(1 / 4 : ℝ)) = t ^ (3 / 4 : ℝ) := by
      calc
        _ = t ^ (1 : ℝ) * t ^ (-(1 / 4 : ℝ)) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add ht]; norm_num
    dsimp [R]
    calc
      _ = t + Real.sqrt y * (t * t ^ (-(1 / 4 : ℝ))) := by ring
      _ = _ := by rw [hp]
  have hRs : m * (∑ i ∈ J, R (T i)) ≤ 2 * (∫ t in Set.Ioo 0 (y ^ 2), R t) := by
    have hh := add_le_add h0 (mul_le_mul_of_nonneg_left hq (Real.sqrt_nonneg y))
    simp only [Real.rpow_zero] at hh
    dsimp [R]
    rw [integral_add hic (hiq.const_mul (Real.sqrt y)), integral_const_mul]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    nlinarith only [hh]
  have hTRs : m * (∑ i ∈ J, T i * R (T i)) ≤ 2 * (∫ t in Set.Ioo 0 (y ^ 2), t * R t) := by
    have hh := add_le_add h1 (mul_le_mul_of_nonneg_left ht (Real.sqrt_nonneg y))
    simp only [Real.rpow_one] at hh
    have hs : (∑ i ∈ J, T i * R (T i)) = ∑ i ∈ J, (T i + Real.sqrt y * T i ^ (3 / 4 : ℝ)) :=
      Finset.sum_congr rfl (fun i hi => hpoint (T i) (hTpos i hi))
    rw [hs, setIntegral_congr_fun measurableSet_Ioo (fun t ht => hpoint t ht.1),
      integral_add hii (hit.const_mul (Real.sqrt y)), integral_const_mul]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    nlinarith only [hh]
  obtain ⟨_, _, hRv, hTRv⟩ := sourceShortTime_R_integrals y hy
  change (1 / y ^ 2) * (∫ t in Set.Ioo 0 (y ^ 2), R t) = 7 / 3 at hRv
  change (1 / y ^ 2) * (∫ t in Set.Ioo 0 (y ^ 2), t * R t) = 15 / 14 * y ^ 2 at hTRv
  have hscale : 0 ≤ 1 / y ^ 2 := by positivity
  constructor
  · have hh := mul_le_mul_of_nonneg_left hRs hscale
    have heq : (1 / y ^ 2) * (m * ∑ i ∈ J, R (T i)) = m / y ^ 2 * ∑ i ∈ J, R (T i) := by ring
    rw [heq] at hh
    nlinarith only [hh, hRv]
  · have hh := mul_le_mul_of_nonneg_left hTRs hscale
    have heq : (1 / y ^ 2) * (m * ∑ i ∈ J, T i * R (T i)) = m / y ^ 2 * ∑ i ∈ J, T i * R (T i) := by ring
    rw [heq] at hh
    nlinarith only [hh, hTRv, sq_nonneg y]

theorem sourceTruncation_shortClock_R_sums :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun z : ℝ => z ^ 2) ν0 →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν0) = 1 →
          (∫ z : ℝ, z ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 2 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            ∀ L2 y : ℝ, 2 ≤ L2 → 0 < y →
              let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
              let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂ρ
              let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
              let T : ℕ → ℝ := fun i => ((n - i : ℕ) : ℝ) * m2
              let J : Finset ℕ := (Finset.range (n + 1)).filter
                (fun i => n / 2 < i ∧ L2 * gamma ^ 2 ≤ T i ∧ T i < y ^ 2)
              let R : ℝ → ℝ := fun t => 1 + Real.sqrt y * t ^ (-(1 / 4 : ℝ))
              m2 / y ^ 2 * (∑ i ∈ J, R (T i)) ≤ C ∧
                m2 / y ^ 2 * (∑ i ∈ J, T i * R (T i)) ≤ C * y ^ 2 := by
  refine ⟨10, by norm_num, ?_⟩
  intro ν0 hp n h2 hnorm hmean x epsilon hx he hehalf hbudget L2 y hL hy
  letI : IsProbabilityMeasure ν0 := hp
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
  let mu : ℝ := ∫ z : ℝ, z ∂ρ
  let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂ρ
  let V : ℝ := variance (id : ℝ → ℝ) ρ
  let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂ρ) / V
  obtain ⟨_, _, _, hVeq, _, hVp, _, _⟩ :=
    Shao.sourceTruncation_variance_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget
  change V = m2 - mu ^ 2 at hVeq
  change 0 < V at hVp
  have hm2 : 0 < m2 := by nlinarith only [hVeq, hVp, sq_nonneg mu]
  obtain ⟨_, hgp, _, hmg, _⟩ :=
    Shao.sourceTruncation_gamma_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget
  exact shortTime_grid_R n m2 gamma L2 y hm2 hgp hmg hL hy

end Shao.Probability
