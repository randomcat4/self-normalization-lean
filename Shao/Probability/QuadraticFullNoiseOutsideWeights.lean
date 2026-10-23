import Shao.Probability.QuadraticFullNoiseGlobalOddEven
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
The actual Region3/5 D'' and (uE)'' u-integrals against the N0=32
deterministic outside envelopes. Actual marked-v estimates and their source
scale payments, integration by parts and inversion remain separate.
-/

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory Set

private lemma abs_tail_rpow (a p : ℝ) (ha : 0 < a) (hp : p < -1) :
    IntegrableOn (fun u : ℝ => |u| ^ p) {u | a ≤ |u|} ∧
      (∫ u in {u : ℝ | a ≤ |u|}, |u| ^ p) = 2 * (-a ^ (p + 1) / (p + 1)) := by
  have hright : IntegrableOn (fun u : ℝ => |u| ^ p) (Set.Ici a) := by
    have hr : IntegrableOn (fun u : ℝ => u ^ p) (Set.Ici a) :=
      (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).2 (integrableOn_Ioi_rpow_of_lt hp ha)
    exact hr.congr_fun (fun u hu => by dsimp; rw [abs_of_pos (ha.trans_le hu)]) measurableSet_Ici
  have hleft : IntegrableOn (fun u : ℝ => |u| ^ p) (Set.Iic (-a)) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let e : MeasurableEmbedding fun u : ℝ => -u := (Homeomorph.neg ℝ).measurableEmbedding
    rw [e.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_neg]
    exact hright
  have hset : {u : ℝ | a ≤ |u|} = Set.Iic (-a) ∪ Set.Ici a := by
    ext u
    rcases le_total 0 u with hu | hu
    · simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici, abs_of_nonneg hu]
      constructor
      · exact Or.inr
      · rintro (hl | hr)
        · linarith
        · exact hr
    · simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici, abs_of_nonpos hu]
      constructor
      · intro h; exact Or.inl (by linarith)
      · rintro (hl | hr) <;> linarith
  have hdis : Disjoint (Set.Iic (-a)) (Set.Ici a) := by
    apply Set.disjoint_left.2
    intro u hl hr
    have : u ≤ -a := hl
    have : a ≤ u := hr
    linarith
  refine ⟨hset ▸ hleft.union hright, ?_⟩
  rw [hset, setIntegral_union hdis measurableSet_Ici hleft hright]
  have hleftval : (∫ u in Set.Iic (-a), |u| ^ p) = ∫ u in Set.Ioi a, |u| ^ p := by
    simpa only [abs_neg, neg_neg] using
      (integral_comp_neg_Iic (-a) (fun u : ℝ => |u| ^ p))
  have hrightval : (∫ u in Set.Ioi a, |u| ^ p) = ∫ u in Set.Ioi a, u ^ p := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp
    rw [abs_of_pos (ha.trans hu)]
  rw [hleftval, integral_Ici_eq_integral_Ioi, hrightval, integral_Ioi_rpow_of_lt hp ha]
  ring

private lemma profile_bounds (b t : ℝ) (hb : 0 < b) (ht : 0 ≤ t) :
    0 ≤ 1 / (1 + t / b) ^ 31 ∧ 1 / (1 + t / b) ^ 31 ≤ 1 ∧
      (0 < t → 1 / (1 + t / b) ^ 31 ≤ b ^ 31 / t ^ 31) := by
  have hd : 1 ≤ (1 + t / b) ^ 31 := one_le_pow₀ (by nlinarith only [div_nonneg ht hb.le])
  refine ⟨by positivity, ?_, ?_⟩
  · exact (one_div_le_one_div_of_le (by norm_num) hd).trans_eq (by norm_num)
  · intro htp
    have hp := pow_le_pow_left₀ (div_nonneg ht hb.le)
      (show t / b ≤ 1 + t / b by linarith) 31
    calc
      _ ≤ 1 / (t / b) ^ 31 := one_div_le_one_div_of_le (by positivity) hp
      _ = _ := by field_simp

private lemma profile_moments (b : ℝ) (hb : 0 < b) :
    Integrable (fun u : ℝ => 1 / (1 + |u| / b) ^ 31) ∧
      Integrable (fun u : ℝ => |u| / (1 + |u| / b) ^ 31) ∧
      (∫ u : ℝ, 1 / (1 + |u| / b) ^ 31) ≤ 4 * b ∧
      (∫ u : ℝ, |u| / (1 + |u| / b) ^ 31) ≤ 4 * b ^ 2 := by
  let S : Set ℝ := {u | b ≤ |u|}
  let K : Set ℝ := Icc (-b) b
  let J : ℝ → ℝ := K.indicator (fun _ => 1)
  let H0 : ℝ → ℝ := fun u => J u + b ^ 31 * S.indicator (fun x => |x| ^ (-31 : ℝ)) u
  let H1 : ℝ → ℝ := fun u => b * J u + b ^ 31 * S.indicator (fun x => |x| ^ (-30 : ℝ)) u
  have hS : MeasurableSet S := (isClosed_le continuous_const continuous_abs).measurableSet
  have hK : MeasurableSet K := measurableSet_Icc
  have hJOn : IntegrableOn (fun _ : ℝ => (1 : ℝ)) K :=
    integrableOn_const (μ := volume) (by dsimp [K]; rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hJ : Integrable J := (integrable_indicator_iff hK).2 hJOn
  obtain ⟨ht0, hv0⟩ := abs_tail_rpow b (-31) hb (by norm_num)
  obtain ⟨ht1, hv1⟩ := abs_tail_rpow b (-30) hb (by norm_num)
  have ht0ind := (integrable_indicator_iff hS).2 ht0
  have ht1ind := (integrable_indicator_iff hS).2 ht1
  have hH0 : Integrable H0 := hJ.add (ht0ind.const_mul (b ^ 31))
  have hH1 : Integrable H1 := (hJ.const_mul b).add (ht1ind.const_mul (b ^ 31))
  have hc0 (u : ℝ) : 1 / (1 + |u| / b) ^ 31 ≤ H0 u := by
    by_cases hc : |u| ≤ b
    · have hm : u ∈ K := abs_le.mp hc
      have hn : 0 ≤ b ^ 31 * S.indicator (fun x => |x| ^ (-31 : ℝ)) u := by
        by_cases ht : u ∈ S
        · rw [Set.indicator_of_mem ht]; positivity
        · rw [Set.indicator_of_notMem ht]; norm_num
      dsimp only [H0, J]
      rw [Set.indicator_of_mem hm]
      exact (profile_bounds b |u| hb (abs_nonneg u)).2.1.trans (by linarith)
    · have ht : b ≤ |u| := le_of_not_ge hc
      have hm : u ∉ K := by intro hm; exact hc (abs_le.mpr hm)
      have htu : 0 < |u| := hb.trans_le ht
      dsimp only [H0, J]
      rw [Set.indicator_of_notMem hm, Set.indicator_of_mem ht, zero_add]
      simpa only [Real.rpow_neg htu.le, Real.rpow_ofNat, div_eq_mul_inv] using
        (profile_bounds b |u| hb (abs_nonneg u)).2.2 htu
  have hc1 (u : ℝ) : |u| / (1 + |u| / b) ^ 31 ≤ H1 u := by
    by_cases hc : |u| ≤ b
    · have hm : u ∈ K := abs_le.mp hc
      have hn : 0 ≤ b ^ 31 * S.indicator (fun x => |x| ^ (-30 : ℝ)) u := by
        by_cases ht : u ∈ S
        · rw [Set.indicator_of_mem ht]; positivity
        · rw [Set.indicator_of_notMem ht]; norm_num
      dsimp only [H1, J]
      rw [Set.indicator_of_mem hm, mul_one]
      have hp := mul_le_mul_of_nonneg_left (profile_bounds b |u| hb (abs_nonneg u)).2.1 (abs_nonneg u)
      calc
        _ = |u| * (1 / (1 + |u| / b) ^ 31) := by ring
        _ ≤ |u| * 1 := hp
        _ ≤ b := by simpa using hc
        _ ≤ _ := by linarith
    · have ht : b ≤ |u| := le_of_not_ge hc
      have hm : u ∉ K := by intro hm; exact hc (abs_le.mpr hm)
      have htu : 0 < |u| := hb.trans_le ht
      dsimp only [H1, J]
      rw [Set.indicator_of_notMem hm, Set.indicator_of_mem ht, mul_zero, zero_add]
      calc
        _ = |u| * (1 / (1 + |u| / b) ^ 31) := by ring
        _ ≤ |u| * (b ^ 31 / |u| ^ 31) := mul_le_mul_of_nonneg_left
          ((profile_bounds b |u| hb (abs_nonneg u)).2.2 htu) (abs_nonneg u)
        _ = b ^ 31 * |u| ^ (-30 : ℝ) := by
          simp only [Real.rpow_neg htu.le, Real.rpow_ofNat]
          field_simp
  have hp0 : Integrable (fun u : ℝ => 1 / (1 + |u| / b) ^ 31) :=
    hH0.mono' (by exact (show Measurable (fun u : ℝ => 1 / (1 + |u| / b) ^ 31) by fun_prop).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun u => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (profile_bounds b |u| hb (abs_nonneg u)).1] using hc0 u)
  have hp1 : Integrable (fun u : ℝ => |u| / (1 + |u| / b) ^ 31) :=
    hH1.mono' (by exact (show Measurable (fun u : ℝ => |u| / (1 + |u| / b) ^ 31) by fun_prop).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun u => by
      have hn : 0 ≤ |u| / (1 + |u| / b) ^ 31 := by positivity
      simpa only [Real.norm_eq_abs, abs_of_nonneg hn] using hc1 u)
  have hJval : (∫ u, J u) = 2 * b := by
    rw [integral_indicator hK, integral_const]
    simp only [smul_eq_mul, mul_one, measureReal_def, Measure.restrict_apply_univ]
    rw [show K = Icc (-b) b from rfl, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ b - -b)]
    ring
  have hv0' : b ^ 31 * (∫ u in S, |u| ^ (-31 : ℝ)) = b / 15 := by
    rw [hv0, show (-31 : ℝ) + 1 = -(30 : ℝ) by norm_num]
    simp only [Real.rpow_neg hb.le, Real.rpow_ofNat]
    field_simp
    ring
  have hv1' : b ^ 31 * (∫ u in S, |u| ^ (-30 : ℝ)) = 2 * b ^ 2 / 29 := by
    rw [hv1, show (-30 : ℝ) + 1 = -(29 : ℝ) by norm_num]
    simp only [Real.rpow_neg hb.le, Real.rpow_ofNat]
    field_simp
  refine ⟨hp0, hp1, (integral_mono hp0 hH0 hc0).trans ?_, (integral_mono hp1 hH1 hc1).trans ?_⟩
  · change (∫ u, J u + b ^ 31 * S.indicator (fun x => |x| ^ (-31 : ℝ)) u) ≤ 4 * b
    rw [integral_add hJ (ht0ind.const_mul _), integral_const_mul,
      integral_indicator hS, hJval, hv0']
    linarith
  · change (∫ u, b * J u + b ^ 31 * S.indicator (fun x => |x| ^ (-30 : ℝ)) u) ≤ 4 * b ^ 2
    rw [integral_add (hJ.const_mul b) (ht1ind.const_mul _), integral_const_mul,
      integral_const_mul, integral_indicator hS, hJval, hv1']
    nlinarith only [sq_nonneg b]

private lemma profile_compare (F : ℝ → ℝ) (A : Set ℝ) (b c0 c1 : ℝ)
    (hb : 0 < b) (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hA : MeasurableSet A)
    (hF : Measurable F) (hF0 : ∀ u, 0 ≤ F u)
    (hbound : ∀ u ∈ A, F u ≤ c0 + c1 * |u|) :
    IntegrableOn (fun u => F u / (1 + |u| / b) ^ 31) A ∧
      (∫ u in A, F u / (1 + |u| / b) ^ 31) ≤ 4 * (c0 * b + c1 * b ^ 2) := by
  obtain ⟨hp0, hp1, hp0val, hp1val⟩ := profile_moments b hb
  let H : ℝ → ℝ := fun u => c0 * (1 / (1 + |u| / b) ^ 31) +
    c1 * (|u| / (1 + |u| / b) ^ 31)
  have hH : Integrable H := (hp0.const_mul c0).add (hp1.const_mul c1)
  have hH0 (u : ℝ) : 0 ≤ H u := by dsimp [H]; positivity
  have hdom (u : ℝ) (hu : u ∈ A) : F u / (1 + |u| / b) ^ 31 ≤ H u := by
    calc
      _ ≤ (c0 + c1 * |u|) / (1 + |u| / b) ^ 31 :=
        div_le_div_of_nonneg_right (hbound u hu) (by positivity)
      _ = _ := by dsimp [H]; ring
  have hint : IntegrableOn (fun u => F u / (1 + |u| / b) ^ 31) A := by
    refine hH.integrableOn.mono' (show Measurable (fun u => F u / (1 + |u| / b) ^ 31) by fun_prop).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hA] with u hu
    have hn : 0 ≤ F u / (1 + |u| / b) ^ 31 := div_nonneg (hF0 u) (by positivity)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hn] using hdom u hu
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ u in A, H u := setIntegral_mono_on hint hH.integrableOn hA hdom
    _ ≤ ∫ u, H u := setIntegral_le_integral hH (Filter.Eventually.of_forall hH0)
    _ = c0 * (∫ u : ℝ, 1 / (1 + |u| / b) ^ 31) +
        c1 * (∫ u : ℝ, |u| / (1 + |u| / b) ^ 31) := by
      rw [integral_add (hp0.const_mul _) (hp1.const_mul _), integral_const_mul, integral_const_mul]
    _ ≤ c0 * (4 * b) + c1 * (4 * b ^ 2) := add_le_add
      (mul_le_mul_of_nonneg_left hp0val hc0) (mul_le_mul_of_nonneg_left hp1val hc1)
    _ = _ := by ring

private lemma power_tail_moments (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => |u| ^ (-31 : ℝ)) {u : ℝ | a ≤ |u|} ∧
      IntegrableOn (fun u : ℝ => |u| ^ (-30 : ℝ)) {u : ℝ | a ≤ |u|} ∧
      (∫ u in {u : ℝ | a ≤ |u|}, |u| ^ (-31 : ℝ)) ≤ (a⁻¹) ^ 30 ∧
      (∫ u in {u : ℝ | a ≤ |u|}, |u| ^ (-30 : ℝ)) ≤ (a⁻¹) ^ 29 := by
  obtain ⟨h0, hv0⟩ := abs_tail_rpow a (-31) ha (by norm_num)
  obtain ⟨h1, hv1⟩ := abs_tail_rpow a (-30) ha (by norm_num)
  refine ⟨h0, h1, ?_, ?_⟩
  · rw [hv0, show (-31 : ℝ) + 1 = -(30 : ℝ) by norm_num]
    simp only [Real.rpow_neg ha.le, Real.rpow_ofNat, inv_pow]
    have hn : 0 ≤ (a ^ 30)⁻¹ := by positivity
    nlinarith only [hn]
  · rw [hv1, show (-30 : ℝ) + 1 = -(29 : ℝ) by norm_num]
    simp only [Real.rpow_neg ha.le, Real.rpow_ofNat, inv_pow]
    have hn : 0 ≤ (a ^ 29)⁻¹ := by positivity
    nlinarith only [hn]

private lemma tail_profile_compare (F : ℝ → ℝ) (A : Set ℝ) (a d c0 c1 : ℝ)
    (ha : 0 < a) (hd : 0 < d) (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1)
    (hA : MeasurableSet A) (hAB : A ⊆ {u : ℝ | a ≤ |u|})
    (hF : Measurable F) (hF0 : ∀ u, 0 ≤ F u)
    (hbound : ∀ u ∈ A, F u ≤ c0 + c1 * |u|) :
    IntegrableOn (fun u => F u / (1 + |u| / d) ^ 31) A ∧
      (∫ u in A, F u / (1 + |u| / d) ^ 31) ≤
        d ^ 31 * (c0 * (a⁻¹) ^ 30 + c1 * (a⁻¹) ^ 29) := by
  obtain ⟨hp0, hp1, hp0val, hp1val⟩ := power_tail_moments a ha
  let H : ℝ → ℝ := fun u => d ^ 31 * (c0 * |u| ^ (-31 : ℝ) + c1 * |u| ^ (-30 : ℝ))
  have hH : IntegrableOn H {u : ℝ | a ≤ |u|} :=
    ((hp0.const_mul c0).add (hp1.const_mul c1)).const_mul (d ^ 31)
  have hHA : IntegrableOn H A := hH.mono_set hAB
  have hH0 (u : ℝ) : 0 ≤ H u := by dsimp [H]; positivity
  have hdom (u : ℝ) (hu : u ∈ A) : F u / (1 + |u| / d) ^ 31 ≤ H u := by
    have htu : 0 < |u| := ha.trans_le (hAB hu)
    calc
      _ = F u * (1 / (1 + |u| / d) ^ 31) := by ring
      _ ≤ (c0 + c1 * |u|) * (d ^ 31 / |u| ^ 31) :=
        mul_le_mul (hbound u hu) ((profile_bounds d |u| hd (abs_nonneg u)).2.2 htu)
          (profile_bounds d |u| hd (abs_nonneg u)).1 (by positivity)
      _ = _ := by
        dsimp [H]
        simp only [Real.rpow_neg htu.le, Real.rpow_ofNat]
        field_simp
  have hint : IntegrableOn (fun u => F u / (1 + |u| / d) ^ 31) A := by
    refine hHA.mono' (show Measurable (fun u => F u / (1 + |u| / d) ^ 31) by fun_prop).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hA] with u hu
    have hn : 0 ≤ F u / (1 + |u| / d) ^ 31 := div_nonneg (hF0 u) (by positivity)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hn] using hdom u hu
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ u in A, H u := setIntegral_mono_on hint hHA hA hdom
    _ ≤ ∫ u in {u : ℝ | a ≤ |u|}, H u := setIntegral_mono_set hH
      (Filter.Eventually.of_forall hH0) (Filter.Eventually.of_forall fun u hu => hAB hu)
    _ = d ^ 31 * (c0 * (∫ u in {u : ℝ | a ≤ |u|}, |u| ^ (-31 : ℝ)) +
        c1 * (∫ u in {u : ℝ | a ≤ |u|}, |u| ^ (-30 : ℝ))) := by
      rw [integral_const_mul, integral_add (hp0.const_mul _) (hp1.const_mul _),
        integral_const_mul, integral_const_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left hp0val hc0) (mul_le_mul_of_nonneg_left hp1val hc1)) (by positivity)

theorem sourceTruncation_odd_even_fullNoise_lowOutside_weighted_integrals :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun a : ℝ => a ^ 2) ν0 →
          (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1 →
          (∫ a : ℝ, a ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 2 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            ∀ i : ℕ, i ≤ n → ∀ h kappa : ℝ,
              epsilon / (1 + x) ≤ h → 0 < kappa →
              let ρ : Measure ℝ :=
                ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
              let m : ℕ := n - i
              let T : ℝ := (m : ℝ) * (∫ a : ℝ, a ^ 2 ∂ρ)
              let gamma : ℝ := (∫ a : ℝ, |a| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
              ∀ v : ℝ,
                let A : Set ℝ :=
                  {u | |u| ≤ kappa / gamma ∧ kappa * |u| / gamma < |v|}
                let b : ℝ := gamma / kappa
                let D : ℝ → ℂ := fun r =>
                  (quadraticChar ρ r v ^ m - quadraticChar ρ (-r) v ^ m) /
                    2 * quadraticFullNoiseChar ρ r v
                let E : ℝ → ℂ := fun r =>
                  (quadraticChar ρ r v ^ m + quadraticChar ρ (-r) v ^ m) /
                    2 * quadraticFullNoiseChar ρ r v
                let W : ℝ → ℂ := fun r => (r : ℂ) * E r
                let Iodd : ℝ → ℝ := fun u =>
                  ‖deriv (fun r : ℝ => deriv D r) u‖ /
                    (1 + kappa * |u| / gamma) ^ 31
                let Ieven : ℝ → ℝ := fun u =>
                  ‖deriv (fun r : ℝ => deriv W r) u‖ /
                    (1 + kappa * |u| / gamma) ^ 31
                IntegrableOn Iodd A ∧ IntegrableOn Ieven A ∧
                  (∫ u in A, Iodd u) ≤ C * b * (T + h * gamma) ∧
                  (∫ u in A, Ieven u) ≤
                    C * (b * (Real.sqrt T + gamma) + b ^ 2 * (T + h * gamma)) := by
  obtain ⟨C, hC, hglobal⟩ := sourceTruncation_odd_even_fullNoise_global_derivatives
  refine ⟨4 * C, by positivity, ?_⟩
  intro ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h kappa hh hkappa
  dsimp only
  intro v
  let := hp0
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
  let m : ℕ := n - i
  let T : ℝ := (m : ℝ) * (∫ a : ℝ, a ^ 2 ∂ρ)
  let gamma : ℝ := (∫ a : ℝ, |a| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
  let b : ℝ := gamma / kappa
  let N : ℝ := T + h * gamma
  let A : Set ℝ := {u | |u| ≤ kappa / gamma ∧ kappa * |u| / gamma < |v|}
  let D : ℝ → ℂ := fun r => (quadraticChar ρ r v ^ m - quadraticChar ρ (-r) v ^ m) / 2 *
    quadraticFullNoiseChar ρ r v
  let E : ℝ → ℂ := fun r => (quadraticChar ρ r v ^ m + quadraticChar ρ (-r) v ^ m) / 2 *
    quadraticFullNoiseChar ρ r v
  let W : ℝ → ℂ := fun r => (r : ℂ) * E r
  let Fo : ℝ → ℝ := fun u => ‖deriv (fun r => deriv D r) u‖
  let Fe : ℝ → ℝ := fun u => ‖deriv (fun r => deriv W r) u‖
  have hg : 0 < gamma := (Shao.sourceTruncation_gamma_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget).2.1
  have hb : 0 < b := div_pos hg hkappa
  have hhpos : 0 < h := (div_pos he (by linarith : 0 < 1 + x)).trans_le hh
  have hT : 0 ≤ T := mul_nonneg (Nat.cast_nonneg m) (integral_nonneg fun a => sq_nonneg a)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hA : MeasurableSet A :=
    (isClosed_le continuous_abs continuous_const).measurableSet.inter
      (isOpen_lt ((continuous_const.mul continuous_abs).div_const _) continuous_const).measurableSet
  have ho (u : ℝ) : Fo u ≤ C * N :=
    (hglobal ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h hh u v).2.2.2.2.1
  have heven (u : ℝ) : Fe u ≤ C * (Real.sqrt T + gamma) + C * N * |u| := by
    refine (hglobal ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h hh u v).2.2.2.2.2.trans_eq ?_
    dsimp [N]
    ring
  obtain ⟨hio, hioVal⟩ := profile_compare Fo A b (C * N) 0 hb (by positivity) (by norm_num)
    hA (measurable_deriv (fun r => deriv D r)).norm (fun _ => norm_nonneg _)
    (fun u _ => by simpa only [zero_mul, add_zero] using ho u)
  obtain ⟨hie, hieVal⟩ := profile_compare Fe A b (C * (Real.sqrt T + gamma)) (C * N) hb
    (by positivity) (by positivity) hA (measurable_deriv (fun r => deriv W r)).norm
    (fun _ => norm_nonneg _) (fun u _ => heven u)
  have hEq (F : ℝ → ℝ) : (fun u => F u / (1 + |u| / b) ^ 31) =
      (fun u => F u / (1 + kappa * |u| / gamma) ^ 31) := by
    funext u
    dsimp only [b]
    rw [div_div_eq_mul_div]
    congr 1
    ring
  rw [hEq] at hio hioVal hie hieVal
  refine ⟨hio, hie, hioVal.trans_eq ?_, hieVal.trans_eq ?_⟩
  · dsimp only [N]
    ring
  · dsimp only [N]
    ring

theorem sourceTruncation_odd_even_fullNoise_highOutside_weighted_integrals :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun a : ℝ => a ^ 2) ν0 →
          (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1 →
          (∫ a : ℝ, a ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 2 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            ∀ i : ℕ, i ≤ n → ∀ h kappa : ℝ,
              epsilon / (1 + x) ≤ h → 0 < kappa →
              let ρ : Measure ℝ :=
                ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
              let m : ℕ := n - i
              let T : ℝ := (m : ℝ) * (∫ a : ℝ, a ^ 2 ∂ρ)
              let gamma : ℝ := (∫ a : ℝ, |a| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
              ∀ v : ℝ,
                let A : Set ℝ :=
                  {u | kappa / gamma ≤ |u| ∧ |u| / (4 * h) < |v|}
                let b : ℝ := gamma / kappa
                let D : ℝ → ℂ := fun r =>
                  (quadraticChar ρ r v ^ m - quadraticChar ρ (-r) v ^ m) /
                    2 * quadraticFullNoiseChar ρ r v
                let E : ℝ → ℂ := fun r =>
                  (quadraticChar ρ r v ^ m + quadraticChar ρ (-r) v ^ m) /
                    2 * quadraticFullNoiseChar ρ r v
                let W : ℝ → ℂ := fun r => (r : ℂ) * E r
                let Iodd : ℝ → ℝ := fun u =>
                  ‖deriv (fun r : ℝ => deriv D r) u‖ /
                    (1 + |u| / (4 * h)) ^ 31
                let Ieven : ℝ → ℝ := fun u =>
                  ‖deriv (fun r : ℝ => deriv W r) u‖ /
                    (1 + |u| / (4 * h)) ^ 31
                IntegrableOn Iodd A ∧ IntegrableOn Ieven A ∧
                  (∫ u in A, Iodd u) ≤
                    C * (4 * h) ^ 31 * b ^ 30 * (T + h * gamma) ∧
                  (∫ u in A, Ieven u) ≤
                    C * (4 * h) ^ 31 *
                      (b ^ 30 * (Real.sqrt T + gamma) + b ^ 29 * (T + h * gamma)) := by
  obtain ⟨C, hC, hglobal⟩ := sourceTruncation_odd_even_fullNoise_global_derivatives
  refine ⟨C, hC, ?_⟩
  intro ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h kappa hh hkappa
  dsimp only
  intro v
  let := hp0
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
  let m : ℕ := n - i
  let T : ℝ := (m : ℝ) * (∫ a : ℝ, a ^ 2 ∂ρ)
  let gamma : ℝ := (∫ a : ℝ, |a| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
  let a : ℝ := kappa / gamma
  let N : ℝ := T + h * gamma
  let A : Set ℝ := {u | a ≤ |u| ∧ |u| / (4 * h) < |v|}
  let D : ℝ → ℂ := fun r => (quadraticChar ρ r v ^ m - quadraticChar ρ (-r) v ^ m) / 2 *
    quadraticFullNoiseChar ρ r v
  let E : ℝ → ℂ := fun r => (quadraticChar ρ r v ^ m + quadraticChar ρ (-r) v ^ m) / 2 *
    quadraticFullNoiseChar ρ r v
  let W : ℝ → ℂ := fun r => (r : ℂ) * E r
  let Fo : ℝ → ℝ := fun u => ‖deriv (fun r => deriv D r) u‖
  let Fe : ℝ → ℝ := fun u => ‖deriv (fun r => deriv W r) u‖
  have hg : 0 < gamma := (Shao.sourceTruncation_gamma_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget).2.1
  have ha : 0 < a := div_pos hkappa hg
  have hhpos : 0 < h := (div_pos he (by linarith : 0 < 1 + x)).trans_le hh
  have hT : 0 ≤ T := mul_nonneg (Nat.cast_nonneg m) (integral_nonneg fun z => sq_nonneg z)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hA : MeasurableSet A :=
    (isClosed_le continuous_const continuous_abs).measurableSet.inter
      (isOpen_lt (continuous_abs.div_const _) continuous_const).measurableSet
  have hAB : A ⊆ {u : ℝ | a ≤ |u|} := fun _ hu => hu.1
  have ho (u : ℝ) : Fo u ≤ C * N :=
    (hglobal ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h hh u v).2.2.2.2.1
  have heven (u : ℝ) : Fe u ≤ C * (Real.sqrt T + gamma) + C * N * |u| := by
    refine (hglobal ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h hh u v).2.2.2.2.2.trans_eq ?_
    dsimp [N]
    ring
  obtain ⟨hio, hioVal⟩ := tail_profile_compare Fo A a (4 * h) (C * N) 0 ha (by positivity)
    (by positivity) (by norm_num) hA hAB (measurable_deriv (fun r => deriv D r)).norm
    (fun _ => norm_nonneg _) (fun u _ => by simpa only [zero_mul, add_zero] using ho u)
  obtain ⟨hie, hieVal⟩ := tail_profile_compare Fe A a (4 * h) (C * (Real.sqrt T + gamma))
    (C * N) ha (by positivity) (by positivity) (by positivity) hA hAB
    (measurable_deriv (fun r => deriv W r)).norm (fun _ => norm_nonneg _) (fun u _ => heven u)
  refine ⟨hio, hie, hioVal.trans_eq ?_, hieVal.trans_eq ?_⟩
  · simp only [a, N, inv_div]
    ring
  · simp only [a, N, inv_div]
    ring

end Shao.Probability
