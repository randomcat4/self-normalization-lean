import Shao.Probability.SourceComplexBoundaryContour
import Shao.Probability.TiltedLowFrequency
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual shifted four-region integrals for the source future/noise kernel.
The complete public declaration is frozen before implementation. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Shao.Probability

open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators

private theorem sgr_raw_root (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun a : ℝ => a ^ 2) nu)
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu) :
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂nu
    let V : ℝ := variance (id : ℝ → ℝ) nu
    let gamma : ℝ := m3 / V
    0 < m2 ∧ 0 < m3 ∧ 0 < gamma ∧ m2 ≤ gamma ^ 2 := by
  dsimp only
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂nu
  let V : ℝ := variance (id : ℝ → ℝ) nu
  let t : ℝ := Real.sqrt m2
  have hformula : V = m2 - (∫ a : ℝ, a ∂nu) ^ 2 := by
    simpa only [V, m2, Pi.pow_apply, id_eq] using
      variance_eq_sub ((memLp_two_iff_integrable_sq
        measurable_id.aestronglyMeasurable).2 h2)
  have hVm2 : V ≤ m2 := by nlinarith only [hformula, sq_nonneg (∫ a : ℝ, a ∂nu)]
  have hm2 : 0 < m2 := hV.trans_le hVm2
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = m2 := Real.sq_sqrt hm2.le
  have hpoint (a : ℝ) : (3 * t) * a ^ 2 ≤ 2 * |a| ^ 3 + t ^ 3 := by
    have hf := mul_nonneg (sq_nonneg (|a| - t))
      (show 0 ≤ 2 * |a| + t by positivity)
    rw [← sq_abs a]
    nlinarith only [hf]
  have hi := integral_mono (h2.const_mul (3 * t))
    ((h3.const_mul 2).add (integrable_const (t ^ 3))) hpoint
  change (∫ a : ℝ, (3 * t) * a ^ 2 ∂nu) ≤
    ∫ a : ℝ, 2 * |a| ^ 3 + t ^ 3 ∂nu at hi
  rw [integral_const_mul, integral_add (h3.const_mul 2) (integrable_const (t ^ 3)),
    integral_const_mul, integral_const, probReal_univ, one_smul] at hi
  have ht3 : t ^ 3 = t * m2 := by rw [pow_succ, ht2]; ring
  have hlyap : t * m2 ≤ m3 := by
    change (3 * t) * m2 ≤ 2 * m3 + t ^ 3 at hi
    linarith
  have hm3 : 0 < m3 := (mul_pos (Real.sqrt_pos.2 hm2) hm2).trans_le hlyap
  have hgamma : 0 < m3 / V := div_pos hm3 hV
  have hroot : Real.sqrt m2 ≤ m3 / V := by
    apply (le_div_iff₀ hV).2
    exact (mul_le_mul_of_nonneg_left hVm2 (Real.sqrt_nonneg _)).trans hlyap
  have hsquare := pow_le_pow_left₀ (Real.sqrt_nonneg m2) hroot 2
  rw [Real.sq_sqrt hm2.le] at hsquare
  exact ⟨hm2, hm3, hgamma, hsquare⟩

private theorem sgr_power_difference (a b : ℂ) (m : ℕ) (Q D : ℝ)
    (hQ : 0 ≤ Q) (ha : ‖a‖ ≤ Q) (hb : ‖b‖ ≤ Q) (hd : ‖a - b‖ ≤ D) :
    ‖a ^ m - b ^ m‖ ≤ (m : ℝ) * Q ^ (m - 1) * D := by
  have hs : ‖∑ i ∈ Finset.range m, a ^ i * b ^ (m - 1 - i)‖ ≤
      (m : ℝ) * Q ^ (m - 1) := by
    calc
      _ ≤ ∑ i ∈ Finset.range m, ‖a ^ i * b ^ (m - 1 - i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range m, Q ^ (m - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul, norm_pow, norm_pow]
        have he : i + (m - 1 - i) = m - 1 := by
          have := Finset.mem_range.mp hi
          omega
        calc
          _ ≤ Q ^ i * Q ^ (m - 1 - i) := by gcongr
          _ = _ := by rw [← pow_add, he]
      _ = _ := by simp
  rw [← geom_sum₂_mul, norm_mul]
  exact (mul_le_mul hs hd (norm_nonneg _) (by positivity)).trans_eq (by ring)

private lemma sgr_abs_tail_rpow (a p : ℝ) (ha : 0 < a) (hp : p < -1) :
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

private lemma sgr_profile_bounds (b t : ℝ) (hb : 0 < b) (ht : 0 ≤ t) :
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

private lemma sgr_profile_moments (b : ℝ) (hb : 0 < b) :
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
  obtain ⟨ht0, hv0⟩ := sgr_abs_tail_rpow b (-31) hb (by norm_num)
  obtain ⟨ht1, hv1⟩ := sgr_abs_tail_rpow b (-30) hb (by norm_num)
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
      exact (sgr_profile_bounds b |u| hb (abs_nonneg u)).2.1.trans (by linarith)
    · have ht : b ≤ |u| := le_of_not_ge hc
      have hm : u ∉ K := by intro hm; exact hc (abs_le.mpr hm)
      have htu : 0 < |u| := hb.trans_le ht
      dsimp only [H0, J]
      rw [Set.indicator_of_notMem hm, Set.indicator_of_mem ht, zero_add]
      simpa only [Real.rpow_neg htu.le, Real.rpow_ofNat, div_eq_mul_inv] using
        (sgr_profile_bounds b |u| hb (abs_nonneg u)).2.2 htu
  have hc1 (u : ℝ) : |u| / (1 + |u| / b) ^ 31 ≤ H1 u := by
    by_cases hc : |u| ≤ b
    · have hm : u ∈ K := abs_le.mp hc
      have hn : 0 ≤ b ^ 31 * S.indicator (fun x => |x| ^ (-30 : ℝ)) u := by
        by_cases ht : u ∈ S
        · rw [Set.indicator_of_mem ht]; positivity
        · rw [Set.indicator_of_notMem ht]; norm_num
      dsimp only [H1, J]
      rw [Set.indicator_of_mem hm, mul_one]
      have hp := mul_le_mul_of_nonneg_left (sgr_profile_bounds b |u| hb (abs_nonneg u)).2.1 (abs_nonneg u)
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
          ((sgr_profile_bounds b |u| hb (abs_nonneg u)).2.2 htu) (abs_nonneg u)
        _ = b ^ 31 * |u| ^ (-30 : ℝ) := by
          simp only [Real.rpow_neg htu.le, Real.rpow_ofNat]
          field_simp
  have hp0 : Integrable (fun u : ℝ => 1 / (1 + |u| / b) ^ 31) :=
    hH0.mono' (by exact (show Measurable (fun u : ℝ => 1 / (1 + |u| / b) ^ 31) by fun_prop).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun u => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sgr_profile_bounds b |u| hb (abs_nonneg u)).1] using hc0 u)
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

private lemma sgr_gaussian_abs_moment (s : ℝ) (hs : -1 < s) :
    let H : ℝ → ℝ := fun u => |u| ^ s * Real.exp (-(1 / 256 : ℝ) * u ^ 2)
    Integrable H ∧ ∀ a : ℝ, 0 < a →
      Integrable (fun u => |u| ^ s * Real.exp (-(1 / 256 : ℝ) * (a * u) ^ 2)) ∧
      (∫ u : ℝ, |u| ^ s * Real.exp (-(1 / 256 : ℝ) * (a * u) ^ 2)) =
        a ^ (-s - 1) * (∫ u : ℝ, H u) := by
  let H : ℝ → ℝ := fun u => |u| ^ s * Real.exp (-(1 / 256 : ℝ) * u ^ 2)
  have hright : IntegrableOn H (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num : 0 < (1 / 256 : ℝ)) hs).congr_fun
      (fun u hu => by dsimp [H]; rw [abs_of_pos hu]) measurableSet_Ioi
  have hrightIci : IntegrableOn H (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hright
  have hleft : IntegrableOn H (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let e : MeasurableEmbedding fun u : ℝ => -u := (Homeomorph.neg ℝ).measurableEmbedding
    rw [e.integrableOn_map_iff]
    simpa only [Function.comp_def, H, abs_neg, neg_sq, neg_preimage, neg_Iic, neg_zero] using hrightIci
  have hH : Integrable H := by
    rw [← integrableOn_univ, ← (show Iic (0 : ℝ) ∪ Ioi 0 = univ from Iic_union_Ioi)]
    exact hleft.union hright
  refine ⟨hH, ?_⟩
  intro a ha
  have heq : (fun u => |u| ^ s * Real.exp (-(1 / 256 : ℝ) * (a * u) ^ 2)) =
      (fun u => (a ^ s)⁻¹ * H (a * u)) := by
    funext u
    dsimp [H]
    rw [abs_mul, abs_of_pos ha, Real.mul_rpow ha.le (abs_nonneg u)]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos ha s)]
  have hcompose : Integrable (fun u => H (a * u)) :=
    (integrable_comp_mul_left_iff H ha.ne').mpr hH
  have hcoef : (a ^ s)⁻¹ * a⁻¹ = a ^ (-s - 1) := by
    calc
      _ = a ^ (-s) * a ^ (-1 : ℝ) := by rw [Real.rpow_neg ha.le, Real.rpow_neg_one]
      _ = a ^ (-s + -1) := (Real.rpow_add ha _ _).symm
      _ = _ := by congr 1
  refine ⟨heq ▸ hcompose.const_mul _, ?_⟩
  rw [heq, integral_const_mul, Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr ha),
    smul_eq_mul, ← mul_assoc, hcoef]

private theorem sgr_gaussian_scale (r T L : ℝ) (hT : 0 < T) :
    let a : ℝ := Real.exp (-2 * L + Real.log T / 2)
    a ^ 2 = Real.exp (-4 * L) * T ∧
      a ^ (-r - 1) = Real.exp ((2 * r + 2) * L) * T ^ (-(r + 1) / 2) := by
  dsimp only
  constructor
  · rw [← Real.exp_nat_mul, ← Real.exp_log hT, ← Real.exp_add]
    congr 1
    norm_num
    ring
  · rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
      Real.rpow_def_of_pos hT, ← Real.exp_add]
    congr 1
    ring

private theorem sgr_gaussian_budget (k : ℕ) (hk : k ≤ 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ T L y D : ℝ,
      0 < T → 0 ≤ L → 0 ≤ y → 0 ≤ D →
      let H : ℝ → ℝ := fun u => |u| ^ k * (1 + D * Real.sqrt (y * |u|)) *
        Real.exp (-Real.exp (-4 * L) * T * u ^ 2 / 256)
      Integrable H ∧ (∫ u : ℝ, H u) ≤
        C * Real.exp (9 * L) *
          (T ^ (-((k : ℝ) + 1) / 2) +
            Real.sqrt y * D * T ^ (-(2 * (k : ℝ) + 3) / 4)) := by
  let M : ℝ → ℝ := fun r => ∫ u : ℝ, |u| ^ r * Real.exp (-(1 / 256 : ℝ) * u ^ 2)
  have hM (r : ℝ) : 0 ≤ M r := integral_nonneg fun u => by dsimp; positivity
  let C : ℝ := 1 + M k + M ((k : ℝ) + 1 / 2)
  have hC : 0 < C := by dsimp [C]; linarith [hM k, hM ((k : ℝ) + 1 / 2)]
  have hC0 : M k ≤ C := by dsimp [C]; linarith [hM ((k : ℝ) + 1 / 2)]
  have hC1 : M ((k : ℝ) + 1 / 2) ≤ C := by dsimp [C]; linarith [hM k]
  refine ⟨C, hC, ?_⟩
  intro T L y D hT hL hy hD
  dsimp only
  let a : ℝ := Real.exp (-2 * L + Real.log T / 2)
  have ha : 0 < a := Real.exp_pos _
  have ha2 := (sgr_gaussian_scale 0 T L hT).1
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hr0 : (-1 : ℝ) < k := by linarith
  have hr1 : (-1 : ℝ) < (k : ℝ) + 1 / 2 := by linarith
  obtain ⟨hi0, hv0⟩ := (sgr_gaussian_abs_moment (k : ℝ) hr0).2 a ha
  obtain ⟨hi1, hv1⟩ := (sgr_gaussian_abs_moment ((k : ℝ) + 1 / 2) hr1).2 a ha
  let H0 : ℝ → ℝ := fun u => |u| ^ (k : ℝ) *
    Real.exp (-(1 / 256 : ℝ) * (a * u) ^ 2)
  let H1 : ℝ → ℝ := fun u => |u| ^ ((k : ℝ) + 1 / 2) *
    Real.exp (-(1 / 256 : ℝ) * (a * u) ^ 2)
  let H : ℝ → ℝ := fun u => |u| ^ k * (1 + D * Real.sqrt (y * |u|)) *
    Real.exp (-Real.exp (-4 * L) * T * u ^ 2 / 256)
  have heq : H =ᵐ[volume] (fun u => H0 u + (Real.sqrt y * D) * H1 u) := by
    filter_upwards [(volume : Measure ℝ).ae_ne 0] with u hu
    have hu0 : 0 < |u| := abs_pos.mpr hu
    dsimp [H, H0, H1]
    rw [Real.sqrt_mul hy, Real.rpow_add hu0, Real.rpow_natCast,
      ← Real.sqrt_eq_rpow]
    have he : -(1 / 256 : ℝ) * (a * u) ^ 2 =
        -Real.exp (-4 * L) * T * u ^ 2 / 256 := by
      rw [mul_pow, ha2]
      ring
    rw [he]
    ring
  have hi : Integrable H := (hi0.add (hi1.const_mul (Real.sqrt y * D))).congr heq.symm
  refine ⟨hi, ?_⟩
  rw [integral_congr_ae heq, integral_add hi0 (hi1.const_mul _), integral_const_mul,
    hv0, hv1]
  rw [(sgr_gaussian_scale (k : ℝ) T L hT).2,
    (sgr_gaussian_scale ((k : ℝ) + 1 / 2) T L hT).2]
  change Real.exp ((2 * (k : ℝ) + 2) * L) * T ^ (-((k : ℝ) + 1) / 2) * M k +
    (Real.sqrt y * D) * (Real.exp ((2 * ((k : ℝ) + 1 / 2) + 2) * L) *
      T ^ (-((k : ℝ) + 1 / 2 + 1) / 2) * M ((k : ℝ) + 1 / 2)) ≤ _
  have hkR : (k : ℝ) ≤ 3 := by exact_mod_cast hk
  have he0 : Real.exp ((2 * (k : ℝ) + 2) * L) ≤ Real.exp (9 * L) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have he1 : Real.exp ((2 * ((k : ℝ) + 1 / 2) + 2) * L) ≤ Real.exp (9 * L) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hq : -((k : ℝ) + 1 / 2 + 1) / 2 = -(2 * (k : ℝ) + 3) / 4 := by ring
  rw [hq]
  calc
    _ ≤ Real.exp (9 * L) * T ^ (-((k : ℝ) + 1) / 2) * C +
        (Real.sqrt y * D) * (Real.exp (9 * L) *
          T ^ (-(2 * (k : ℝ) + 3) / 4) * C) := by gcongr
    _ = _ := by ring

private theorem sgr_slice_bound (f : ℝ → ℂ) (hf : Continuous f)
    (S : Set ℝ) (hS : MeasurableSet S) (H : ℝ → ℝ) (hHi : Integrable H)
    (hH0 : ∀ v : ℝ, 0 ≤ H v) (hbound : ∀ v ∈ S, ‖f v‖ ≤ H v) :
    (∫ v : ℝ, S.indicator (fun v => ‖f v‖) v) ≤ ∫ v : ℝ, H v := by
  let F : ℝ → ℝ := S.indicator (fun v => ‖f v‖)
  have hF0 (v : ℝ) : 0 ≤ F v := Set.indicator_nonneg (fun v _ => norm_nonneg _) v
  have hle (v : ℝ) : F v ≤ H v := by
    by_cases hv : v ∈ S
    · simpa only [F, Set.indicator_of_mem hv] using hbound v hv
    · simp only [F, Set.indicator_of_notMem hv]
      exact hH0 v
  have hFi : Integrable F := hHi.mono'
    (hf.norm.measurable.indicator hS).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hF0 v)] using hle v)
  exact integral_mono hFi hHi hle

private theorem sgr_region_fibers (F : ℝ × ℝ → ℂ) (hF : Integrable F)
    (S : Set (ℝ × ℝ)) (hS : MeasurableSet S)
    (H : ℝ → ℝ) (hH : Integrable H)
    (hbound : ∀ u : ℝ,
      (∫ v : ℝ, S.indicator (fun p => ‖F p‖) (u, v)) ≤ H u) :
    (∫ p : ℝ × ℝ in S, ‖F p‖) ≤ ∫ u : ℝ, H u := by
  have hi := hF.norm.indicator hS
  have hip : Integrable (S.indicator (fun p => ‖F p‖))
      ((volume : Measure ℝ).prod volume) := by
    simpa only [← Measure.volume_eq_prod] using hi
  rw [← integral_indicator hS, Measure.volume_eq_prod,
    integral_prod (S.indicator (fun p => ‖F p‖)) hip]
  exact integral_mono hip.integral_prod_left hH hbound

private theorem sgr_nonneg_integral_le (F H : ℝ → ℝ)
    (hF : Measurable F) (hF0 : ∀ u : ℝ, 0 ≤ F u) (hH : Integrable H)
    (hle : ∀ u : ℝ, F u ≤ H u) :
    Integrable F ∧ (∫ u : ℝ, F u) ≤ ∫ u : ℝ, H u := by
  have hi : Integrable F := hH.mono' hF.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hF0 u)] using hle u)
  exact ⟨hi, integral_mono hi hH hle⟩

private theorem sgr_polynomial_moments (H : Fin 4 → ℝ → ℝ)
    (hH : ∀ k, Integrable (H k)) (J : Fin 4 → ℝ) (K : ℝ)
    (hb : ∀ k, (∫ u : ℝ, H k u) ≤ K * J k)
    (c : Fin 4 → ℝ) (hc : ∀ k, 0 ≤ c k) :
    Integrable (fun u : ℝ => ∑ k : Fin 4, c k * H k u) ∧
      (∫ u : ℝ, ∑ k : Fin 4, c k * H k u) ≤ K * ∑ k : Fin 4, c k * J k := by
  have hi := integrable_finsetSum Finset.univ (fun k _ => (hH k).const_mul (c k))
  refine ⟨hi, ?_⟩
  rw [integral_finsetSum _ (fun k _ => (hH k).const_mul (c k))]
  simp_rw [integral_const_mul]
  calc
    _ ≤ ∑ k : Fin 4, c k * (K * J k) := by
      exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hb k) (hc k)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring

private theorem sgr_integer_tail (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ Gamma : ℝ, 0 < Gamma →
      let S : Set ℝ := {u | (1 / 128 : ℝ) / Gamma ≤ |u|}
      IntegrableOn (fun u : ℝ => 1 / |u| ^ p) S ∧
        (∫ u : ℝ in S, 1 / |u| ^ p) = C * Gamma ^ (p - 1) := by
  let C : ℝ := 2 * (128 : ℝ) ^ (p - 1) / (p - 1 : ℕ)
  have hp1 : 0 < p - 1 := by omega
  have hpR : 1 < (p : ℝ) := by exact_mod_cast (show 1 < p by omega)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Gamma hGamma
  dsimp only
  let a : ℝ := (1 / 128 : ℝ) / Gamma
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨hi, hv⟩ := sgr_abs_tail_rpow a (-(p : ℝ)) ha (by linarith)
  have heq (u : ℝ) (hu : a ≤ |u|) : |u| ^ (-(p : ℝ)) = 1 / |u| ^ p := by
    rw [Real.rpow_neg (abs_nonneg u), Real.rpow_natCast, one_div]
  have hS : MeasurableSet {u : ℝ | a ≤ |u|} :=
    (isClosed_le continuous_const continuous_abs).measurableSet
  refine ⟨hi.congr_fun heq hS, ?_⟩
  rw [← setIntegral_congr_fun hS heq, hv]
  have he : -(p : ℝ) + 1 = -((p - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
    ring
  rw [he, Real.rpow_neg ha.le, Real.rpow_natCast]
  dsimp [a, C]
  rw [div_pow]
  have hpn : ((p - 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have h128 : (1 / 128 : ℝ) ^ (p - 1) * 128 ^ (p - 1) = 1 := by
    rw [← mul_pow]
    norm_num
  field_simp
  nlinarith [h128]

private theorem sgr_weighted_tail (p : ℕ) (hp : 3 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ Gamma y D : ℝ,
      0 < Gamma → 0 ≤ y → 0 ≤ D →
      let S : Set ℝ := {u | (1 / 128 : ℝ) / Gamma ≤ |u|}
      let H : ℝ → ℝ := fun u => 1 / |u| ^ p * (1 + D * Real.sqrt (y * |u|))
      IntegrableOn H S ∧ (∫ u : ℝ in S, H u) ≤
        C * (Gamma ^ (p - 1) +
          Real.sqrt y * D * Gamma ^ (p - 1) / Real.sqrt Gamma) := by
  obtain ⟨C0, hC0, ht0⟩ := sgr_integer_tail p (by omega)
  obtain ⟨C1, hC1, ht1⟩ := sgr_integer_tail (p - 1) (by omega)
  let C : ℝ := C0 + 16 * C1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Gamma y D hGamma hy hD
  dsimp only
  let S : Set ℝ := {u | (1 / 128 : ℝ) / Gamma ≤ |u|}
  have hS : MeasurableSet S := (isClosed_le continuous_const continuous_abs).measurableSet
  obtain ⟨hi0, hv0⟩ := ht0 Gamma hGamma
  obtain ⟨hi1, hv1⟩ := ht1 Gamma hGamma
  let H : ℝ → ℝ := fun u => 1 / |u| ^ p * (1 + D * Real.sqrt (y * |u|))
  let P : ℝ → ℝ := fun u => 1 / |u| ^ p +
    (16 * Real.sqrt Gamma * Real.sqrt y * D) * (1 / |u| ^ (p - 1))
  have hPi : IntegrableOn P S := hi0.add (hi1.const_mul _)
  have hle (u : ℝ) (hu : u ∈ S) : H u ≤ P u := by
    have hu0 : 0 < |u| := (by dsimp [S] at hu; positivity :
      0 < (1 / 128 : ℝ) / Gamma).trans_le hu
    have hbase : 1 ≤ 128 * Gamma * |u| := by
      have hh := (div_le_iff₀ hGamma).mp hu
      nlinarith
    have hs : Real.sqrt |u| ≤ 16 * Real.sqrt Gamma * |u| := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · have hm := mul_le_mul_of_nonneg_right hbase (abs_nonneg u)
        have hg := Real.sq_sqrt hGamma.le
        nlinarith [sq_nonneg (Real.sqrt Gamma * |u|)]
    have hpow : |u| ^ p = |u| ^ (p - 1) * |u| := by
      rw [← pow_succ]
      congr 1
      omega
    dsimp [H, P]
    rw [Real.sqrt_mul hy]
    calc
      _ ≤ 1 / |u| ^ p * (1 + D * (Real.sqrt y *
          (16 * Real.sqrt Gamma * |u|))) := by gcongr
      _ = _ := by rw [hpow]; field_simp
  have hHi : IntegrableOn H S := hPi.mono'
    (by exact (show Measurable H by dsimp [H]; fun_prop).aestronglyMeasurable)
    (by filter_upwards [ae_restrict_mem hS] with u hu
        simpa only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ H u by dsimp [H]; positivity)]
          using hle u hu)
  refine ⟨hHi, (setIntegral_mono_on hHi hPi hS hle).trans ?_⟩
  rw [integral_add hi0 (hi1.const_mul _), integral_const_mul, hv0, hv1]
  have hpow : Gamma ^ (p - 1) / Real.sqrt Gamma =
      Real.sqrt Gamma * Gamma ^ (p - 1 - 1) := by
    have he : p - 1 = (p - 1 - 1) + 1 := by omega
    conv_lhs => rw [he, pow_succ]
    have hg := Real.sq_sqrt hGamma.le
    have hgn : Real.sqrt Gamma ≠ 0 := (Real.sqrt_pos.mpr hGamma).ne'
    field_simp
    nlinarith
  have hpow' : Real.sqrt y * D * Gamma ^ (p - 1) / Real.sqrt Gamma =
      Real.sqrt y * D * (Real.sqrt Gamma * Gamma ^ (p - 1 - 1)) := by
    rw [mul_div_assoc, hpow]
  rw [hpow']
  dsimp [C]
  nlinarith [mul_nonneg (show 0 ≤ 16 * C1 by positivity) (pow_nonneg hGamma.le (p - 1)),
    mul_nonneg (show 0 ≤ C0 by positivity)
      (show 0 ≤ Real.sqrt y * D * (Real.sqrt Gamma * Gamma ^ (p - 1 - 1)) by positivity)]

private theorem sgr_low_integral
    (T L y D K Cm Cg : ℝ) (hT : 0 < T) (hL : 0 ≤ L)
    (hy : 0 ≤ y) (hD : 0 < D) (hK : 0 ≤ K) (hCm : 0 ≤ Cm)
    (F : ℝ × ℝ → ℂ) (hFc : Continuous F) (hFi : Integrable F)
    (S : Set (ℝ × ℝ)) (hS : MeasurableSet S)
    (B : ℝ → ℝ → ℂ)
    (hBi : ∀ u, Integrable (fun v => ‖B u v‖) ∧
      Integrable (fun v => |v| * ‖B u v‖))
    (hB0 : ∀ u, (∫ v : ℝ, ‖B u v‖) ≤ Cm * (1 + D * Real.sqrt (y * |u|)))
    (hB1 : ∀ u, (∫ v : ℝ, |v| * ‖B u v‖) ≤
      Cm * (D⁻¹ + y * |u|) * (1 + D * Real.sqrt (y * |u|)))
    (P0 P1 : ℝ → ℝ) (hP0 : ∀ r, 0 ≤ r → 0 ≤ P0 r)
    (hP1 : ∀ r, 0 ≤ r → 0 ≤ P1 r)
    (c : Fin 4 → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hpoly : ∀ r : ℝ, 0 ≤ r →
      P0 r + P1 r * (D⁻¹ + y * r) = ∑ k : Fin 4, c k * r ^ k.val)
    (hg : ∀ k : Fin 4,
      let H : ℝ → ℝ := fun u => |u| ^ k.val * (1 + D * Real.sqrt (y * |u|)) *
        Real.exp (-Real.exp (-4 * L) * T * u ^ 2 / 256)
      Integrable H ∧ (∫ u : ℝ, H u) ≤ Cg * Real.exp (9 * L) *
        (T ^ (-((k.val : ℝ) + 1) / 2) +
          Real.sqrt y * D * T ^ (-(2 * (k.val : ℝ) + 3) / 4)))
    (hbound : ∀ p ∈ S,
      ‖F p‖ ≤ K * Real.exp (-Real.exp (-4 * L) * T * p.1 ^ 2 / 256) *
        (P0 |p.1| + P1 |p.1| * |p.2|) * ‖B p.1 p.2‖) :
    (∫ p : ℝ × ℝ in S, ‖F p‖) ≤ K * Cm * Cg * Real.exp (9 * L) *
      (∑ k : Fin 4, c k *
        (T ^ (-((k.val : ℝ) + 1) / 2) +
          Real.sqrt y * D * T ^ (-(2 * (k.val : ℝ) + 3) / 4))) := by
  let H : Fin 4 → ℝ → ℝ := fun k u => |u| ^ k.val *
    (1 + D * Real.sqrt (y * |u|)) * Real.exp (-Real.exp (-4 * L) * T * u ^ 2 / 256)
  let J : Fin 4 → ℝ := fun k => T ^ (-((k.val : ℝ) + 1) / 2) +
    Real.sqrt y * D * T ^ (-(2 * (k.val : ℝ) + 3) / 4)
  have hi (k : Fin 4) : Integrable (H k) := (hg k).1
  have hb (k : Fin 4) : (∫ u : ℝ, H k u) ≤ (Cg * Real.exp (9 * L)) * J k := (hg k).2
  obtain ⟨hQi, hQb⟩ := sgr_polynomial_moments H hi J (Cg * Real.exp (9 * L)) hb c hc
  let Q : ℝ → ℝ := fun u => (K * Cm) * ∑ k : Fin 4, c k * H k u
  have hQi : Integrable Q := hQi.const_mul _
  have hslice (u : ℝ) : (∫ v : ℝ, S.indicator (fun p => ‖F p‖) (u, v)) ≤ Q u := by
    let A : Set ℝ := {v | (u, v) ∈ S}
    have hA : MeasurableSet A := hS.preimage (continuous_const.prodMk continuous_id).measurable
    let E : ℝ := Real.exp (-Real.exp (-4 * L) * T * u ^ 2 / 256)
    let R : ℝ → ℝ := fun v => K * E *
      (P0 |u| * ‖B u v‖ + P1 |u| * (|v| * ‖B u v‖))
    have hRi : Integrable R :=
      (((hBi u).1.const_mul (P0 |u|)).add ((hBi u).2.const_mul (P1 |u|))).const_mul _
    have hR0 (v : ℝ) : 0 ≤ R v := by
      dsimp [R, E]
      exact mul_nonneg (by positivity) (add_nonneg
        (mul_nonneg (hP0 _ (abs_nonneg u)) (norm_nonneg _))
        (mul_nonneg (hP1 _ (abs_nonneg u)) (by positivity)))
    have hsub := sgr_slice_bound (fun v => F (u, v))
      (hFc.comp (continuous_const.prodMk continuous_id)) A hA R hRi hR0
      (fun v hv => (hbound (u, v) hv).trans_eq (by dsimp [R, E]; ring))
    have heq : (fun v => S.indicator (fun p => ‖F p‖) (u, v)) =
        A.indicator (fun v => ‖F (u, v)‖) := by
      funext v
      by_cases hv : (u, v) ∈ S <;> simp [A, hv]
    rw [heq]
    refine hsub.trans ?_
    dsimp only [R]
    rw [integral_const_mul, integral_add ((hBi u).1.const_mul _) ((hBi u).2.const_mul _),
      integral_const_mul, integral_const_mul]
    calc
      _ ≤ K * E * (P0 |u| * (Cm * (1 + D * Real.sqrt (y * |u|))) +
          P1 |u| * (Cm * (D⁻¹ + y * |u|) * (1 + D * Real.sqrt (y * |u|)))) := by
        gcongr
        · exact hP0 _ (abs_nonneg u)
        · exact hB0 u
        · exact hP1 _ (abs_nonneg u)
        · exact hB1 u
      _ = Q u := by
        dsimp [Q, H, E]
        have he : (∑ k : Fin 4, c k * (|u| ^ k.val *
            (1 + D * Real.sqrt (y * |u|)) *
              Real.exp (-Real.exp (-4 * L) * T * u ^ 2 / 256))) =
            (∑ k : Fin 4, c k * |u| ^ k.val) *
              (1 + D * Real.sqrt (y * |u|)) *
                Real.exp (-Real.exp (-4 * L) * T * u ^ 2 / 256) := by
          rw [Finset.sum_mul, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _
          ring
        rw [he, ← hpoly |u| (abs_nonneg u)]
        ring
  calc
    _ ≤ ∫ u : ℝ, Q u := sgr_region_fibers F hFi S hS Q hQi hslice
    _ = (K * Cm) * ∫ u : ℝ, ∑ k : Fin 4, c k * H k u := integral_const_mul _ _
    _ ≤ (K * Cm) * ((Cg * Real.exp (9 * L)) * ∑ k : Fin 4, c k * J k) :=
      mul_le_mul_of_nonneg_left hQb (by positivity)
    _ = _ := by dsimp [J]; ring


private theorem sgr_parameter_guards (y N lam h : ℝ)
    (hy : 2 ≤ y) (hN : (1 / 16 : ℝ) ≤ N)
    (hlam : y / Real.sqrt N ≤ lam) (hh : 0 < h)
    (hyh : y * h ≤ (1 / 4 : ℝ)) :
    let s : ℝ := lam * y / Real.sqrt N
    0 ≤ lam ∧ 0 ≤ s ∧ s ≤ lam ^ 2 ∧ s * h ≤ lam := by
  dsimp only
  have hN0 : 0 < N := by linarith
  have hr : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hr2 := Real.sq_sqrt hN0.le
  have hrlo : (1 / 4 : ℝ) ≤ Real.sqrt N := by nlinarith [Real.sqrt_nonneg N]
  have hl : 0 ≤ lam := (div_nonneg (by linarith) hr.le).trans hlam
  have hyl : y ≤ lam * Real.sqrt N := (div_le_iff₀ hr).mp hlam
  refine ⟨hl, div_nonneg (mul_nonneg hl (by linarith)) hr.le, ?_, ?_⟩
  · apply (div_le_iff₀ hr).mpr
    nlinarith [mul_le_mul_of_nonneg_left hyl hl]
  · rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hr).mpr
    nlinarith [mul_le_mul_of_nonneg_left (hyh.trans hrlo) hl]

private theorem sgr_gamma_bound
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (hm2V : (∫ a : ℝ, a ^ 2 ∂nu) ≤ 2 * variance (id : ℝ → ℝ) nu) :
    (∫ a : ℝ, |a| ^ 3 ∂nu) / variance (id : ℝ → ℝ) nu ≤ 2 * h := by
  have h2 : Integrable (fun a : ℝ => a ^ 2) nu := by
    apply (integrable_const (h ^ 2)).mono' (by fun_prop)
    filter_upwards [hs] with a ha
    simpa [Real.norm_eq_abs, abs_pow] using pow_le_pow_left₀ (abs_nonneg a) ha 2
  have hm : (∫ a : ℝ, |a| ^ 3 ∂nu) ≤ h * ∫ a : ℝ, a ^ 2 ∂nu := by
    rw [← integral_const_mul]
    apply integral_mono_ae h3 (h2.const_mul h)
    filter_upwards [hs] with a ha
    calc
      |a| ^ 3 = |a| * a ^ 2 := by rw [pow_succ, sq_abs]; ring
      _ ≤ h * a ^ 2 := mul_le_mul_of_nonneg_right ha (sq_nonneg a)
  apply (div_le_iff₀ hV).mpr
  nlinarith [mul_le_mul_of_nonneg_left hm2V hh.le]

private theorem sgr_actual_noise_norm
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (h : ℝ) (hh : 0 < h) (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (hgamma : (∫ a : ℝ, |a| ^ 3 ∂nu) / variance (id : ℝ → ℝ) nu ≤ 2 * h)
    (lam s : ℝ) (hlam : 0 ≤ lam) (hs : 0 ≤ s) (hslope : s * h ≤ lam)
    (u v : ℝ) :
    ‖quadraticFullNoiseCharComplex nu
      ((u : ℂ) - (lam : ℂ) * Complex.I)
      ((v : ℂ) + (s : ℂ) * Complex.I)‖ ≤ Real.exp (98 * lam * h) := by
  haveI : IsProbabilityMeasure (quadraticFullNoiseLaw nu) :=
    (quadraticFullNoise_law_data nu h3 hV h hh hsupport).2.2.1
  have hp := (quadraticFullNoise_support_moments nu h3 hV h hh hsupport hgamma).1
  unfold quadraticFullNoiseCharComplex
  have hb : ∀ᵐ p : ℝ × ℝ ∂quadraticFullNoiseLaw nu,
      ‖Complex.exp ((((u : ℂ) - (lam : ℂ) * Complex.I) * (p.1 : ℂ) +
        ((v : ℂ) + (s : ℂ) * Complex.I) * (p.2 : ℂ)) * Complex.I)‖ ≤
        Real.exp (98 * lam * h) := by
    filter_upwards [hp] with p hp
    rw [Complex.norm_exp_mul_I]
    apply Real.exp_le_exp.mpr
    simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
      zero_mul, sub_zero, zero_sub, zero_add, add_zero]
    have hsp : s * h ^ 2 ≤ lam * h := by
      nlinarith [mul_le_mul_of_nonneg_right hslope hh.le]
    calc
      -(-lam * p.1 + s * p.2) ≤ lam * |p.1| + s * |p.2| := by
        nlinarith [mul_le_mul_of_nonneg_left (le_abs_self p.1) hlam,
          mul_le_mul_of_nonneg_left (neg_le_abs p.2) hs]
      _ ≤ lam * (34 * h) + s * (64 * h ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hp.1 hlam)
          (mul_le_mul_of_nonneg_left hp.2 hs)
      _ ≤ 98 * lam * h := by nlinarith
  simpa only [integral_const, probReal_univ, one_smul] using
    norm_integral_le_of_norm_le (integrable_const (Real.exp (98 * lam * h))) hb

private theorem sgr_normalizer_power
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h lam b s : ℝ) (hh : 0 < h) (hlam : 0 ≤ lam)
    (hb : b = lam ∨ b = -lam) (hs : 0 ≤ s)
    (hsquare : s ≤ lam ^ 2) (hslope : s * h ≤ lam)
    (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h) (m : ℕ) :
    let Z : ℝ := ∫ a : ℝ, Real.exp (b * a - s * a ^ 2) ∂nu
    let mu : ℝ := ∫ a : ℝ, a ∂nu
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂nu
    0 < Z ∧ Z ^ m ≤ Real.exp ((m : ℝ) *
      (b * mu + (lam ^ 2 / 2 - s) * m2 +
        24 * lam ^ 3 * m3 * Real.exp (lam * h))) := by
  dsimp only
  have hd := boundedQuadraticTilt_joint_moments_normalizer nu h lam b s hh hlam hb
    hs hsquare hslope hsupport
  dsimp only at hd
  rcases hd with ⟨_, _, _, _, _, _, _, hZ, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hlog, _⟩
  refine ⟨hZ, ?_⟩
  have hZe : (∫ a : ℝ, Real.exp (b * a - s * a ^ 2) ∂nu) ≤
      Real.exp (b * (∫ a : ℝ, a ∂nu) + (lam ^ 2 / 2 - s) * (∫ a : ℝ, a ^ 2 ∂nu) +
        24 * lam ^ 3 * (∫ a : ℝ, |a| ^ 3 ∂nu) * Real.exp (lam * h)) := by
    calc
      _ = Real.exp (Real.log (∫ a : ℝ, Real.exp (b * a - s * a ^ 2) ∂nu)) :=
        (Real.exp_log hZ).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlog
  calc
    _ ≤ (Real.exp (b * (∫ a : ℝ, a ∂nu) + (lam ^ 2 / 2 - s) * (∫ a : ℝ, a ^ 2 ∂nu) +
        24 * lam ^ 3 * (∫ a : ℝ, |a| ^ 3 ∂nu) * Real.exp (lam * h))) ^ m :=
      pow_le_pow_left₀ hZ.le hZe m
    _ = _ := (Real.exp_nat_mul _ _).symm

private theorem sgr_high_integral :
    ∃ C : ℝ, 0 < C ∧ ∀ Gamma y D K Cm a b : ℝ,
      0 < Gamma → 0 ≤ y → 0 ≤ D → 0 ≤ K → 0 ≤ Cm → 0 ≤ a → 0 ≤ b →
      ∀ (F : ℝ × ℝ → ℂ), Continuous F → Integrable F →
      ∀ (S : Set (ℝ × ℝ)), MeasurableSet S →
      (∀ p ∈ S, (1 / 128 : ℝ) / Gamma ≤ |p.1|) →
      ∀ (B : ℝ → ℝ → ℂ),
      (∀ u, Integrable (fun v => ‖B u v‖)) →
      (∀ u, (∫ v : ℝ, ‖B u v‖) ≤ Cm * (1 + D * Real.sqrt (y * |u|))) →
      (∀ p ∈ S, ‖F p‖ ≤ K * ((a + b * |p.1|) / |p.1| ^ 16) * ‖B p.1 p.2‖) →
      (∫ p : ℝ × ℝ in S, ‖F p‖) ≤ C * K * Cm *
        (a * (Gamma ^ 15 + Real.sqrt y * D * Gamma ^ 15 / Real.sqrt Gamma) +
          b * (Gamma ^ 14 + Real.sqrt y * D * Gamma ^ 14 / Real.sqrt Gamma)) := by
  obtain ⟨C0, hC0, ht0⟩ := sgr_weighted_tail 16 (by norm_num)
  obtain ⟨C1, hC1, ht1⟩ := sgr_weighted_tail 15 (by norm_num)
  let C : ℝ := C0 + C1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Gamma y D K Cm a b hGamma hy hD hK hCm ha hb F hFc hFi S hS hSu B hBi hBn hbound
  let U : Set ℝ := {u | (1 / 128 : ℝ) / Gamma ≤ |u|}
  have hU : MeasurableSet U := (isClosed_le continuous_const continuous_abs).measurableSet
  let H0 : ℝ → ℝ := fun u => 1 / |u| ^ 16 * (1 + D * Real.sqrt (y * |u|))
  let H1 : ℝ → ℝ := fun u => 1 / |u| ^ 15 * (1 + D * Real.sqrt (y * |u|))
  obtain ⟨hi0, hv0⟩ := ht0 Gamma y D hGamma hy hD
  obtain ⟨hi1, hv1⟩ := ht1 Gamma y D hGamma hy hD
  change IntegrableOn H0 U at hi0
  change IntegrableOn H1 U at hi1
  let Q : ℝ → ℝ := U.indicator (fun u => K * Cm * (a * H0 u + b * H1 u))
  have hQi : Integrable Q := (integrable_indicator_iff hU).2
    (((hi0.const_mul a).add (hi1.const_mul b)).const_mul (K * Cm))
  have hslice (u : ℝ) : (∫ v : ℝ, S.indicator (fun p => ‖F p‖) (u, v)) ≤ Q u := by
    by_cases hu : u ∈ U
    · have hu0 : 0 < |u| := (by dsimp [U] at hu; positivity :
        0 < (1 / 128 : ℝ) / Gamma).trans_le hu
      let A : Set ℝ := {v | (u, v) ∈ S}
      have hA : MeasurableSet A := hS.preimage (continuous_const.prodMk continuous_id).measurable
      let R : ℝ → ℝ := fun v => (K * ((a + b * |u|) / |u| ^ 16)) * ‖B u v‖
      have hR : Integrable R := (hBi u).const_mul _
      have hR0 (v : ℝ) : 0 ≤ R v := by dsimp [R]; positivity
      have hh := sgr_slice_bound (fun v => F (u, v))
        (hFc.comp (continuous_const.prodMk continuous_id)) A hA R hR hR0
        (fun v hv => hbound (u, v) hv)
      have heq : (fun v => S.indicator (fun p => ‖F p‖) (u, v)) =
          A.indicator (fun v => ‖F (u, v)‖) := by
        funext v
        by_cases hv : (u, v) ∈ S <;> simp [A, hv]
      rw [heq]
      refine hh.trans ?_
      dsimp only [R]
      rw [integral_const_mul]
      calc
        _ ≤ K * ((a + b * |u|) / |u| ^ 16) *
            (Cm * (1 + D * Real.sqrt (y * |u|))) :=
          mul_le_mul_of_nonneg_left (hBn u) (by positivity)
        _ = Q u := by
          rw [show Q u = K * Cm * (a * H0 u + b * H1 u) from Set.indicator_of_mem hu _]
          dsimp [H0, H1]
          field_simp
    · have heq : (fun v => S.indicator (fun p => ‖F p‖) (u, v)) = fun _ => 0 := by
        funext v
        have hv : (u, v) ∉ S := fun hv => hu (hSu (u, v) hv)
        exact Set.indicator_of_notMem hv _
      rw [heq, integral_zero, show Q u = 0 from Set.indicator_of_notMem hu _]
  calc
    _ ≤ ∫ u : ℝ, Q u := sgr_region_fibers F hFi S hS Q hQi hslice
    _ = K * Cm * (a * (∫ u : ℝ in U, H0 u) + b * (∫ u : ℝ in U, H1 u)) := by
      rw [integral_indicator hU, integral_const_mul,
        integral_add (hi0.const_mul a) (hi1.const_mul b), integral_const_mul, integral_const_mul]
    _ ≤ K * Cm * (a * (C0 * (Gamma ^ 15 +
          Real.sqrt y * D * Gamma ^ 15 / Real.sqrt Gamma)) +
        b * (C1 * (Gamma ^ 14 + Real.sqrt y * D * Gamma ^ 14 / Real.sqrt Gamma))) := by
      gcongr
    _ ≤ _ := by
      have h0 : C0 ≤ C := by dsimp [C]; linarith
      have h1 : C1 ≤ C := by dsimp [C]; linarith
      calc
        _ ≤ K * Cm * (a * (C * (Gamma ^ 15 +
            Real.sqrt y * D * Gamma ^ 15 / Real.sqrt Gamma)) +
          b * (C * (Gamma ^ 14 + Real.sqrt y * D * Gamma ^ 14 / Real.sqrt Gamma))) := by
          gcongr
        _ = _ := by ring

private theorem sgr_outside_fiber
    (F : ℝ × ℝ → ℂ) (hFc : Continuous F) (S : Set (ℝ × ℝ)) (hS : MeasurableSet S)
    (u : ℝ) (B : ℝ → ℂ) (aStar D K P Cm : ℝ)
    (haStar : 0 < aStar) (hD : 0 ≤ D) (hK : 0 ≤ K) (hP : 0 ≤ P) (hCm : 0 ≤ Cm)
    (hBi : IntegrableOn (fun v => ‖B v‖) {v | |u| / aStar < |v|})
    (hBn : (∫ v : ℝ in {v | |u| / aStar < |v|}, ‖B v‖) ≤
      Cm / (1 + D * |u| / aStar) ^ 31)
    (hSv : ∀ v, (u, v) ∈ S → |u| / aStar < |v|)
    (hbound : ∀ v, (u, v) ∈ S → ‖F (u, v)‖ ≤ K * P * ‖B v‖) :
    (∫ v : ℝ, S.indicator (fun p => ‖F p‖) (u, v)) ≤
      K * P * (Cm / (1 + D * |u| / aStar) ^ 31) := by
  let A : Set ℝ := {v | (u, v) ∈ S}
  let O : Set ℝ := {v | |u| / aStar < |v|}
  have hA : MeasurableSet A := hS.preimage (continuous_const.prodMk continuous_id).measurable
  have hO : MeasurableSet O := isOpen_lt continuous_const continuous_abs |>.measurableSet
  let H : ℝ → ℝ := fun v => (K * P) * O.indicator (fun v => ‖B v‖) v
  have hHi : Integrable H := ((integrable_indicator_iff hO).2 hBi).const_mul _
  have hH0 (v : ℝ) : 0 ≤ H v := mul_nonneg (mul_nonneg hK hP)
    (Set.indicator_nonneg (fun _ _ => norm_nonneg _) v)
  have hh := sgr_slice_bound (fun v => F (u, v))
    (hFc.comp (continuous_const.prodMk continuous_id)) A hA H hHi hH0 (by
      intro v hv
      dsimp [H]
      rw [Set.indicator_of_mem (hSv v hv)]
      exact hbound v hv)
  have heq : (fun v => S.indicator (fun p => ‖F p‖) (u, v)) =
      A.indicator (fun v => ‖F (u, v)‖) := by
    funext v
    by_cases hv : (u, v) ∈ S <;> simp [A, hv]
  rw [heq]
  refine hh.trans ?_
  dsimp only [H]
  rw [integral_const_mul, integral_indicator hO]
  exact mul_le_mul_of_nonneg_left hBn (mul_nonneg hK hP)

private theorem sgr_outside_integral
    (D aStar K Cm a b : ℝ) (hD : 0 < D) (haStar : 0 < aStar)
    (hK : 0 ≤ K) (hCm : 0 ≤ Cm) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (F : ℝ × ℝ → ℂ) (hFc : Continuous F) (hFi : Integrable F)
    (S : Set (ℝ × ℝ)) (hS : MeasurableSet S) (B : ℝ → ℝ → ℂ)
    (hBi : ∀ u, IntegrableOn (fun v => ‖B u v‖) {v | |u| / aStar < |v|})
    (hBn : ∀ u, (∫ v : ℝ in {v | |u| / aStar < |v|}, ‖B u v‖) ≤
      Cm / (1 + D * |u| / aStar) ^ 31)
    (hSv : ∀ p ∈ S, |p.1| / aStar < |p.2|)
    (hbound : ∀ p ∈ S, ‖F p‖ ≤ K * (a + b * |p.1|) * ‖B p.1 p.2‖) :
    (∫ p : ℝ × ℝ in S, ‖F p‖) ≤
      4 * K * Cm * (a * (aStar * D⁻¹) + b * (aStar * D⁻¹) ^ 2) := by
  let t : ℝ := aStar * D⁻¹
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨hi0, hi1, hv0, hv1⟩ := sgr_profile_moments t ht
  let Q : ℝ → ℝ := fun u => K * Cm *
    (a * (1 / (1 + |u| / t) ^ 31) + b * (|u| / (1 + |u| / t) ^ 31))
  have hQi : Integrable Q := ((hi0.const_mul a).add (hi1.const_mul b)).const_mul _
  have hslice (u : ℝ) : (∫ v : ℝ, S.indicator (fun p => ‖F p‖) (u, v)) ≤ Q u := by
    have hh := sgr_outside_fiber F hFc S hS u (B u) aStar D K (a + b * |u|) Cm
      haStar hD.le hK (by positivity) hCm (hBi u) (hBn u)
      (fun v hv => hSv (u, v) hv) (fun v hv => hbound (u, v) hv)
    refine hh.trans_eq ?_
    dsimp [Q, t]
    field_simp
  calc
    _ ≤ ∫ u : ℝ, Q u := sgr_region_fibers F hFi S hS Q hQi hslice
    _ = K * Cm * (a * (∫ u : ℝ, 1 / (1 + |u| / t) ^ 31) +
        b * (∫ u : ℝ, |u| / (1 + |u| / t) ^ 31)) := by
      rw [integral_const_mul, integral_add (hi0.const_mul a) (hi1.const_mul b),
        integral_const_mul, integral_const_mul]
    _ ≤ K * Cm * (a * (4 * t) + b * (4 * t ^ 2)) := by gcongr
    _ = _ := by dsimp [t]; ring

private theorem sgr_outside_tail_integral :
    ∃ C : ℝ, 0 < C ∧ ∀ Gamma D aStar K Cm a b : ℝ,
      0 < Gamma → 0 < D → 0 < aStar → 0 ≤ K → 0 ≤ Cm → 0 ≤ a → 0 ≤ b →
      ∀ (F : ℝ × ℝ → ℂ), Continuous F → Integrable F →
      ∀ (S : Set (ℝ × ℝ)), MeasurableSet S →
      (∀ p ∈ S, (1 / 128 : ℝ) / Gamma ≤ |p.1| ∧ |p.1| / aStar < |p.2|) →
      ∀ (B : ℝ → ℝ → ℂ),
      (∀ u, IntegrableOn (fun v => ‖B u v‖) {v | |u| / aStar < |v|}) →
      (∀ u, (∫ v : ℝ in {v | |u| / aStar < |v|}, ‖B u v‖) ≤
        Cm / (1 + D * |u| / aStar) ^ 31) →
      (∀ p ∈ S, ‖F p‖ ≤ K * (a + b * |p.1|) * ‖B p.1 p.2‖) →
      (∫ p : ℝ × ℝ in S, ‖F p‖) ≤ C * K * Cm * (aStar * D⁻¹) ^ 31 *
        (a * Gamma ^ 30 + b * Gamma ^ 29) := by
  obtain ⟨C0, hC0, ht0⟩ := sgr_integer_tail 31 (by norm_num)
  obtain ⟨C1, hC1, ht1⟩ := sgr_integer_tail 30 (by norm_num)
  let C : ℝ := C0 + C1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Gamma D aStar K Cm a b hGamma hD haStar hK hCm ha hb F hFc hFi S hS hSu B hBi hBn hbound
  let U : Set ℝ := {u | (1 / 128 : ℝ) / Gamma ≤ |u|}
  have hU : MeasurableSet U := (isClosed_le continuous_const continuous_abs).measurableSet
  obtain ⟨hi0, hv0⟩ := ht0 Gamma hGamma
  obtain ⟨hi1, hv1⟩ := ht1 Gamma hGamma
  let Q : ℝ → ℝ := U.indicator (fun u => K * Cm * (aStar * D⁻¹) ^ 31 *
    (a * (1 / |u| ^ 31) + b * (1 / |u| ^ 30)))
  have hQi : Integrable Q := (integrable_indicator_iff hU).2
    (((hi0.const_mul a).add (hi1.const_mul b)).const_mul _)
  have hslice (u : ℝ) : (∫ v : ℝ, S.indicator (fun p => ‖F p‖) (u, v)) ≤ Q u := by
    by_cases hu : u ∈ U
    · have hu0 : 0 < |u| := (by dsimp [U] at hu; positivity :
        0 < (1 / 128 : ℝ) / Gamma).trans_le hu
      have hh := sgr_outside_fiber F hFc S hS u (B u) aStar D K (a + b * |u|) Cm
        haStar hD.le hK (by positivity) hCm (hBi u) (hBn u)
        (fun v hv => (hSu (u, v) hv).2) (fun v hv => hbound (u, v) hv)
      have hp : 1 / (1 + D * |u| / aStar) ^ 31 ≤
          (aStar * D⁻¹) ^ 31 / |u| ^ 31 := by
        have he : D * |u| / aStar = |u| / (aStar * D⁻¹) := by field_simp
        rw [he]
        exact (sgr_profile_bounds (aStar * D⁻¹) |u| (by positivity) (abs_nonneg u)).2.2 hu0
      calc
        _ ≤ K * (a + b * |u|) * (Cm / (1 + D * |u| / aStar) ^ 31) := hh
        _ ≤ K * (a + b * |u|) * (Cm * ((aStar * D⁻¹) ^ 31 / |u| ^ 31)) := by
          rw [div_eq_mul_inv, ← one_div]
          gcongr
        _ = Q u := by
          rw [show Q u = K * Cm * (aStar * D⁻¹) ^ 31 *
            (a * (1 / |u| ^ 31) + b * (1 / |u| ^ 30)) from Set.indicator_of_mem hu _]
          field_simp
    · have heq : (fun v => S.indicator (fun p => ‖F p‖) (u, v)) = fun _ => 0 := by
        funext v
        have hv : (u, v) ∉ S := fun hv => hu (hSu (u, v) hv).1
        exact Set.indicator_of_notMem hv _
      rw [heq, integral_zero, show Q u = 0 from Set.indicator_of_notMem hu _]
  calc
    _ ≤ ∫ u : ℝ, Q u := sgr_region_fibers F hFi S hS Q hQi hslice
    _ = K * Cm * (aStar * D⁻¹) ^ 31 *
        (a * (C0 * Gamma ^ 30) + b * (C1 * Gamma ^ 29)) := by
      rw [integral_indicator hU, integral_const_mul,
        integral_add (hi0.const_mul a) (hi1.const_mul b), integral_const_mul, integral_const_mul,
        hv0, hv1]
    _ ≤ K * Cm * (aStar * D⁻¹) ^ 31 *
        (a * (C * Gamma ^ 30) + b * (C * Gamma ^ 29)) := by
      have h0 : C0 ≤ C := by dsimp [C]; linarith
      have h1 : C1 ≤ C := by dsimp [C]; linarith
      gcongr
    _ = _ := by ring

private theorem sgr_split_normalizer
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h lam y N q : ℝ) (m : ℕ) (hh : 0 < h) (hN : 0 < N)
    (hl : 0 ≤ lam) (hs : 0 ≤ lam * y / Real.sqrt N)
    (hsq : lam * y / Real.sqrt N ≤ lam ^ 2)
    (hslope : (lam * y / Real.sqrt N) * h ≤ lam)
    (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (hclock : N = q + (m : ℝ) * (∫ a : ℝ, a ^ 2 ∂nu)) :
    let mu : ℝ := ∫ a : ℝ, a ∂nu
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂nu
    let T : ℝ := (m : ℝ) * m2
    let s : ℝ := lam * y / Real.sqrt N
    let sj : Fin 2 → ℝ := fun j => if j = 0 then 0 else s
    let bj : Fin 2 → ℝ := fun j =>
      if j = 0 then Real.exp (-lam * y * Real.sqrt N) else Real.exp (-s * q)
    let Z : ℝ → Fin 2 → ℝ := fun b j => ∫ a : ℝ, Real.exp (b * a - sj j * a ^ 2) ∂nu
    ∀ (j : Fin 2) (b : ℝ), (b = lam ∨ b = -lam) →
      0 < Z b j ∧ Real.exp (-2 * lam * h) ≤ Z b j ∧
        bj j * (Z b j) ^ m ≤ Real.exp
          (-lam * y * Real.sqrt N + T * lam ^ 2 / 2 + (m : ℝ) * lam * |mu| +
            24 * (m : ℝ) * lam ^ 3 * m3 * Real.exp (lam * h)) := by
  dsimp only
  intro j b hb
  let mu : ℝ := ∫ a : ℝ, a ∂nu
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂nu
  let T : ℝ := (m : ℝ) * m2
  let s : ℝ := lam * y / Real.sqrt N
  let sj : ℝ := if j = 0 then 0 else s
  let bj : ℝ := if j = 0 then Real.exp (-lam * y * Real.sqrt N) else Real.exp (-s * q)
  let Z : ℝ := ∫ a : ℝ, Real.exp (b * a - sj * a ^ 2) ∂nu
  have hsj0 : 0 ≤ sj := by
    dsimp [sj]
    split_ifs
    · exact le_rfl
    · exact hs
  have hsjsq : sj ≤ lam ^ 2 := by dsimp [sj]; split_ifs; positivity; exact hsq
  have hsjslope : sj * h ≤ lam := by dsimp [sj]; split_ifs; simpa using hl; exact hslope
  have hd := boundedQuadraticTilt_joint_moments_normalizer nu h lam b sj hh hl hb
    hsj0 hsjsq hsjslope hsupport
  dsimp only at hd
  rcases hd with ⟨_, _, _, _, _, _, _, hZ, hZlo, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  obtain ⟨_, hZpow⟩ := sgr_normalizer_power nu h lam b sj hh hl hb hsj0 hsjsq hsjslope hsupport m
  refine ⟨hZ, by simpa only [neg_mul, mul_assoc] using hZlo, ?_⟩
  have hbmu : b * mu ≤ lam * |mu| := by
    rcases hb with rfl | rfl
    · exact mul_le_mul_of_nonneg_left (le_abs_self mu) hl
    · nlinarith [mul_le_mul_of_nonneg_left (neg_le_abs mu) hl]
  have hbj : 0 ≤ bj := by dsimp [bj]; split_ifs <;> positivity
  have hsN : s * (q + T) = lam * y * Real.sqrt N := by
    rw [← hclock]
    dsimp [s]
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff (Real.sqrt_pos.mpr hN).ne').mpr
    calc
      lam * y * N = lam * y * (Real.sqrt N) ^ 2 := by rw [Real.sq_sqrt hN.le]
      _ = _ := by ring
  calc
    _ ≤ bj * Real.exp ((m : ℝ) * (b * mu + (lam ^ 2 / 2 - sj) * m2 +
        24 * lam ^ 3 * m3 * Real.exp (lam * h))) :=
      mul_le_mul_of_nonneg_left hZpow hbj
    _ = Real.exp ((if j = 0 then -lam * y * Real.sqrt N else -s * q) +
        (m : ℝ) * (b * mu + (lam ^ 2 / 2 - sj) * m2 +
          24 * lam ^ 3 * m3 * Real.exp (lam * h))) := by
      dsimp [bj]
      split_ifs <;> rw [← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hmean := mul_le_mul_of_nonneg_left hbmu (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
      dsimp [sj]
      split_ifs
      · nlinarith
      · dsimp only [T] at hsN
        nlinarith

private theorem sgr_phase_norm (u lam w h : ℝ) (hl : 0 ≤ lam) (hw : |w| ≤ h) :
    ‖(u : ℂ) - (lam : ℂ) * Complex.I‖ ≤ |u| + lam ∧
      ‖Complex.exp (((u : ℂ) - (lam : ℂ) * Complex.I) * (w : ℂ) * Complex.I)‖ ≤
        Real.exp (lam * h) ∧
      ‖Complex.exp (-((u : ℂ) - (lam : ℂ) * Complex.I) * (w : ℂ) * Complex.I)‖ ≤
        Real.exp (lam * h) := by
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ ‖(u : ℂ)‖ + ‖(lam : ℂ) * Complex.I‖ := norm_sub_le _ _
      _ = _ := by simp [norm_mul, abs_of_nonneg hl]
  · rw [Complex.norm_exp_mul_I]
    simp only [Complex.mul_im, Complex.sub_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (le_trans (le_abs_self w) hw) hl]
  · rw [Complex.norm_exp_mul_I]
    simp only [Complex.mul_im, Complex.neg_im, Complex.neg_re, Complex.sub_im,
      Complex.sub_re, Complex.ofReal_im, Complex.ofReal_re, Complex.I_im, Complex.I_re]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (le_trans (neg_le_abs w) hw) hl]

private theorem sgr_actual_weighted_powers
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (h lam s bj E : ℝ) (m : ℕ) (hh : 0 < h) (hm : 0 < m)
    (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (hm2V : (∫ a : ℝ, a ^ 2 ∂nu) ≤ 2 * variance (id : ℝ → ℝ) nu)
    (hl : 0 ≤ lam) (hs : 0 ≤ s) (hsq : s ≤ lam ^ 2) (hslope : s * h ≤ lam)
    (hbj : 0 ≤ bj) (hE : 0 ≤ E)
    (hZp : bj * (∫ a : ℝ, Real.exp (lam * a - s * a ^ 2) ∂nu) ^ m ≤ E)
    (hZm : bj * (∫ a : ℝ, Real.exp (-lam * a - s * a ^ 2) ∂nu) ^ m ≤ E) :
    let T : ℝ := (m : ℝ) * (∫ a : ℝ, a ^ 2 ∂nu)
    ∀ u v : ℝ,
      let z : ℂ := (u : ℂ) - (lam : ℂ) * Complex.I
      let zeta : ℂ := (v : ℂ) + (s : ℂ) * Complex.I
      let Xi : ℂ := quadraticFullNoiseCharComplex nu z zeta
      let ap : ℂ := quadraticCharComplex nu z zeta ^ m
      let am : ℂ := quadraticCharComplex nu (-z) zeta ^ m
      bj * ‖ap‖ * ‖Xi‖ ≤ E * Real.exp (98 * lam * h) ∧
        bj * ‖am‖ * ‖Xi‖ ≤ E * Real.exp (98 * lam * h) ∧
        (u ≠ 0 → |v| ≤ |u| / (4 * h) →
          bj * ‖ap‖ * ‖Xi‖ ≤
            E * (4752 : ℝ) ^ 8 * Real.exp (162 * lam * h) *
              (T⁻¹ + lam ^ 2) ^ 8 / |u| ^ 16 ∧
          bj * ‖am‖ * ‖Xi‖ ≤
            E * (4752 : ℝ) ^ 8 * Real.exp (162 * lam * h) *
              (T⁻¹ + lam ^ 2) ^ 8 / |u| ^ 16) := by
  dsimp only
  let rp : Measure ℝ := nu.tilted (fun a => lam * a - s * a ^ 2)
  let rm : Measure ℝ := nu.tilted (fun a => -lam * a - s * a ^ 2)
  let Zp : ℝ := ∫ a : ℝ, Real.exp (lam * a - s * a ^ 2) ∂nu
  let Zm : ℝ := ∫ a : ℝ, Real.exp (-lam * a - s * a ^ 2) ∂nu
  have hdata := (quadraticCharComplex_data nu h3 h hh hsupport).2.2.2.1
  have hp := hdata lam s
  have hn := hdata (-lam) s
  have hZpp : 0 < Zp := hp.2.1
  have hZmp : 0 < Zm := hn.2.1
  haveI : IsProbabilityMeasure rp := hp.2.2.1
  haveI : IsProbabilityMeasure rm := hn.2.2.1
  intro u v
  let z : ℂ := (u : ℂ) - (lam : ℂ) * Complex.I
  let zeta : ℂ := (v : ℂ) + (s : ℂ) * Complex.I
  let Xi : ℂ := quadraticFullNoiseCharComplex nu z zeta
  have heqp : quadraticCharComplex nu z zeta = (Zp : ℂ) * quadraticChar rp u v := hp.2.2.2 u v
  have heqm : quadraticCharComplex nu (-z) zeta = (Zm : ℂ) * quadraticChar rm (-u) v := by
    have he : -z = ((-u : ℝ) : ℂ) - ((-lam : ℝ) : ℂ) * Complex.I := by
      dsimp [z]
      push_cast
      ring
    rw [he]
    exact hn.2.2.2 (-u) v
  have hnp : ‖quadraticCharComplex nu z zeta ^ m‖ = Zp ^ m * ‖quadraticChar rp u v‖ ^ m := by
    rw [heqp, mul_pow, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hZpp]
  have hnm : ‖quadraticCharComplex nu (-z) zeta ^ m‖ = Zm ^ m * ‖quadraticChar rm (-u) v‖ ^ m := by
    rw [heqm, mul_pow, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hZmp]
  have hgamma := sgr_gamma_bound nu h3 hV h hh hsupport hm2V
  have hXi := sgr_actual_noise_norm nu h3 hV h hh hsupport hgamma lam s hl hs hslope u v
  have hcp : ‖quadraticChar rp u v‖ ^ m ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (norm_quadraticChar_le_one rp u v)
  have hcm : ‖quadraticChar rm (-u) v‖ ^ m ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (norm_quadraticChar_le_one rm (-u) v)
  change bj * ‖quadraticCharComplex nu z zeta ^ m‖ * ‖Xi‖ ≤ _ ∧
    bj * ‖quadraticCharComplex nu (-z) zeta ^ m‖ * ‖Xi‖ ≤ _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [hnp]
    calc
      _ = (bj * Zp ^ m) * ‖quadraticChar rp u v‖ ^ m * ‖Xi‖ := by ring
      _ ≤ E * 1 * Real.exp (98 * lam * h) := by gcongr
      _ = _ := by ring
  · rw [hnm]
    calc
      _ = (bj * Zm ^ m) * ‖quadraticChar rm (-u) v‖ ^ m * ‖Xi‖ := by ring
      _ ≤ E * 1 * Real.exp (98 * lam * h) := by gcongr
      _ = _ := by ring
  · intro hu hv
    have hmatch := quadraticComplexChord_matching_power nu h3 hV h hh hsupport hm2V
      lam lam s hl (Or.inl rfl) hs hsq hslope m 8 hm u v hu hv
    dsimp only at hmatch
    refine ⟨?_, ?_⟩
    · rw [hnp]
      calc
        _ = (bj * Zp ^ m) * (‖quadraticChar rp u v‖ ^ m * ‖Xi‖) := by ring
        _ ≤ E * ((4752 : ℝ) ^ 8 * Real.exp (162 * lam * h) *
            (((m : ℝ) * (∫ a : ℝ, a ^ 2 ∂nu))⁻¹ + lam ^ 2) ^ 8 / |u| ^ 16) := by
          exact mul_le_mul hZp hmatch.2.2.1 (by positivity) hE
        _ = _ := by ring
    · rw [hnm]
      calc
        _ = (bj * Zm ^ m) * (‖quadraticChar rm (-u) v‖ ^ m * ‖Xi‖) := by ring
        _ ≤ E * ((4752 : ℝ) ^ 8 * Real.exp (162 * lam * h) *
            (((m : ℝ) * (∫ a : ℝ, a ^ 2 ∂nu))⁻¹ + lam ^ 2) ^ 8 / |u| ^ 16) := by
          exact mul_le_mul hZm hmatch.2.2.2 (by positivity) hE
        _ = _ := by ring

private theorem sgr_multiplier_bound
    (d : Fin 2) (F B Xi ap am z ep em : ℂ) (bj M R P : ℝ)
    (hbj : 0 ≤ bj) (hM : 0 ≤ M) (hR : 0 ≤ R) (hP : 0 ≤ P)
    (hz : ‖z‖ ≤ R) (hep : ‖ep‖ ≤ P) (hem : ‖em‖ ≤ P)
    (hap : bj * ‖ap‖ * ‖Xi‖ ≤ M) (ham : bj * ‖am‖ * ‖Xi‖ ≤ M)
    (hF : ‖F‖ = bj * ‖B‖ * ‖Xi‖ *
      ‖if d = 0 then ap - am else Complex.I * z * (ep * ap + em * am)‖) :
    ‖F‖ ≤ 2 * M * ‖B‖ * (if d = 0 then 1 else R * P) := by
  rw [hF]
  by_cases hd : d = 0
  · rw [if_pos hd, if_pos hd]
    calc
      _ ≤ bj * ‖B‖ * ‖Xi‖ * (‖ap‖ + ‖am‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le ap am) (by positivity)
      _ = (bj * ‖ap‖ * ‖Xi‖ + bj * ‖am‖ * ‖Xi‖) * ‖B‖ := by ring
      _ ≤ (M + M) * ‖B‖ := mul_le_mul_of_nonneg_right (add_le_add hap ham) (norm_nonneg _)
      _ = _ := by ring
  · rw [if_neg hd, if_neg hd, norm_mul, norm_mul, Complex.norm_I, one_mul]
    calc
      _ ≤ bj * ‖B‖ * ‖Xi‖ * (‖z‖ * (‖ep * ap‖ + ‖em * am‖)) := by
        gcongr
        exact norm_add_le _ _
      _ ≤ bj * ‖B‖ * ‖Xi‖ * (R * (P * ‖ap‖ + P * ‖am‖)) := by
        simp only [norm_mul]
        gcongr
      _ = (bj * ‖ap‖ * ‖Xi‖ + bj * ‖am‖ * ‖Xi‖) * ‖B‖ * (R * P) := by ring
      _ ≤ (M + M) * ‖B‖ * (R * P) := by gcongr
      _ = _ := by ring

private theorem sgr_actual_low_difference
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (n m : ℕ) (h lam s y bj E : ℝ) (hh : 0 < h) (hm : 0 < m)
    (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (hl : 0 ≤ lam) (hs : 0 ≤ s) (hsq : s ≤ lam ^ 2) (hslope : s * h ≤ lam)
    (hy : 2 ≤ y)
    (hnV : (1 / 2 : ℝ) ≤ (n : ℝ) * variance (id : ℝ → ℝ) nu)
    (hnm2 : (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂nu) ≤ (4 / 3 : ℝ))
    (hnmu : (n : ℝ) * |∫ a : ℝ, a ∂nu| ≤ (1 / 2 : ℝ))
    (hbj : 0 ≤ bj) (hE : 0 ≤ E)
    (hZp : bj * (∫ a : ℝ, Real.exp (lam * a - s * a ^ 2) ∂nu) ^ m ≤ E)
    (hZm : bj * (∫ a : ℝ, Real.exp (-lam * a - s * a ^ 2) ∂nu) ^ m ≤ E)
    (hhalf : (m : ℝ) * (∫ a : ℝ, a ^ 2 ∂nu) / 2 ≤
      ((m - 1 : ℕ) : ℝ) * (∫ a : ℝ, a ^ 2 ∂nu)) :
    let mu : ℝ := ∫ a : ℝ, a ∂nu
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂nu
    let T : ℝ := (m : ℝ) * m2
    let Gamma : ℝ := 8 * Real.exp (8 * lam * h) * (m3 / variance (id : ℝ → ℝ) nu)
    ∀ u v : ℝ, |u| ≤ (1 / 128 : ℝ) / Gamma →
      |v| ≤ (1 / 128 : ℝ) * |u| / Gamma →
      let z : ℂ := (u : ℂ) - (lam : ℂ) * Complex.I
      let zeta : ℂ := (v : ℂ) + (s : ℂ) * Complex.I
      bj * ‖quadraticCharComplex nu z zeta ^ m - quadraticCharComplex nu (-z) zeta ^ m‖ ≤
        4 * (m : ℝ) * E * Real.exp (3 * lam * h) *
          (|mu| * (|u| + lam) + m3 *
            ((|u| + lam) ^ 3 + (|u| + lam) * (|v| + s))) *
          Real.exp (-Real.exp (-4 * lam * h) * T * u ^ 2 / 256) := by
  dsimp only
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂nu
  let mu : ℝ := ∫ a : ℝ, a ∂nu
  let Zp : ℝ := ∫ a : ℝ, Real.exp (lam * a - s * a ^ 2) ∂nu
  let Zm : ℝ := ∫ a : ℝ, Real.exp (-lam * a - s * a ^ 2) ∂nu
  let Z : ℝ := max Zp Zm
  let rp : Measure ℝ := nu.tilted (fun a => lam * a - s * a ^ 2)
  let rm : Measure ℝ := nu.tilted (fun a => -lam * a - s * a ^ 2)
  have hd := quadraticCharComplex_data nu h3 h hh hsupport
  have hp := hd.2.2.2.1 lam s
  have hn := hd.2.2.2.1 (-lam) s
  have hZpp : 0 < Zp := hp.2.1
  have hZmp : 0 < Zm := hn.2.1
  have hZ : 0 < Z := hZpp.trans_le (le_max_left _ _)
  have hZnorm : bj * Z ^ m ≤ E := by
    rcases le_total Zp Zm with hpm | hmp
    · simpa only [Z, max_eq_right hpm] using hZm
    · simpa only [Z, max_eq_left hmp] using hZp
  have hZlo : Real.exp (-2 * lam * h) ≤ Z := by
    have hzdata := boundedQuadraticTilt_joint_moments_normalizer nu h lam lam s hh hl
      (Or.inl rfl) hs hsq hslope hsupport
    dsimp only at hzdata
    rcases hzdata with ⟨_, _, _, _, _, _, _, _, hZlo, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
    have hz : Real.exp (-(2 * lam * h)) ≤ Z :=
      hZlo.trans (show Zp ≤ Z from le_max_left _ _)
    convert hz using 1 <;> congr 1 <;> ring
  have hZone : 1 ≤ Z * Real.exp (2 * lam * h) := by
    calc
      1 = Real.exp (-2 * lam * h) * Real.exp (2 * lam * h) := by
        rw [← Real.exp_add]
        convert Real.exp_zero.symm using 1 <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hZlo (Real.exp_pos _).le
  have hZlost : bj * Z ^ (m - 1) ≤ E * Real.exp (2 * lam * h) := by
    calc
      _ ≤ (bj * Z ^ (m - 1)) * (Z * Real.exp (2 * lam * h)) :=
        le_mul_of_one_le_right (by positivity) hZone
      _ = (bj * Z ^ m) * Real.exp (2 * lam * h) := by
        calc
          _ = bj * (Z ^ (m - 1) * Z) * Real.exp (2 * lam * h) := by ring
          _ = _ := by rw [← pow_succ, Nat.sub_add_cancel hm]
      _ ≤ _ := mul_le_mul_of_nonneg_right hZnorm (Real.exp_pos _).le
  have hloP := boundedQuadraticTilt_joint_second_moments_lowFrequency nu n h lam lam s y
    hh hl (Or.inl rfl) hs hsq hslope hsupport hy hnV hnm2 hnmu
  have hloM := boundedQuadraticTilt_joint_second_moments_lowFrequency nu n h lam (-lam) s y
    hh hl (Or.inr rfl) hs hsq hslope hsupport hy hnV hnm2 hnmu
  dsimp only at hloP hloM
  rcases hloP with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hloP⟩
  rcases hloM with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hloM⟩
  intro u v hu hv
  let z : ℂ := (u : ℂ) - (lam : ℂ) * Complex.I
  let zeta : ℂ := (v : ℂ) + (s : ℂ) * Complex.I
  let ap : ℂ := quadraticCharComplex nu z zeta
  let am : ℂ := quadraticCharComplex nu (-z) zeta
  let c : ℝ := Real.exp (-4 * lam * h) * m2 * u ^ 2 / 128
  let Q : ℝ := Z * Real.exp (-c)
  have heqp : ap = (Zp : ℂ) * quadraticChar rp u v := hp.2.2.2 u v
  have heqm : am = (Zm : ℂ) * quadraticChar rm (-u) v := by
    have he : -z = ((-u : ℝ) : ℂ) - ((-lam : ℝ) : ℂ) * Complex.I := by
      dsimp [z]
      push_cast
      ring
    change quadraticCharComplex nu (-z) zeta = _
    rw [he]
    exact hn.2.2.2 (-u) v
  have hcp := (hloP 1 u v hu hv).1
  have hcm := (hloM 1 u v hu hv).2
  simp only [pow_one, Nat.cast_one, one_mul] at hcp hcm
  have hcp' : ‖quadraticChar rp u v‖ ≤ Real.exp (-c) := by
    convert hcp using 1 <;> dsimp [c, m2] <;> congr 1 <;> ring
  have hcm' : ‖quadraticChar rm (-u) v‖ ≤ Real.exp (-c) := by
    convert hcm using 1 <;> dsimp [c, m2] <;> congr 1 <;> ring
  have hpa : ‖ap‖ ≤ Q := by
    rw [heqp, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZpp]
    exact mul_le_mul (le_max_left _ _) hcp' (norm_nonneg _) hZ.le
  have hma : ‖am‖ ≤ Q := by
    rw [heqm, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZmp]
    exact mul_le_mul (le_max_right _ _) hcm' (norm_nonneg _) hZ.le
  let P : ℝ := |mu| * (|u| + lam) + m3 *
    ((|u| + lam) ^ 3 + (|u| + lam) * (|v| + s))
  have hm3 : 0 ≤ m3 := integral_nonneg fun a => by positivity
  have hzn : ‖z‖ ≤ |u| + lam :=
    (sgr_phase_norm u lam 0 h hl (by simpa only [abs_zero] using hh.le)).1
  have hdefect : ‖ap - am‖ ≤ 4 * Real.exp (lam * h) * P := by
    have he := hd.2.2.2.2 lam s u v hl hs
    exact he.trans (by dsimp [P]; gcongr)
  have hdiff := sgr_power_difference ap am m Q (4 * Real.exp (lam * h) * P)
    (by dsimp [Q]; positivity) hpa hma hdefect
  have hQpow : Q ^ (m - 1) = Z ^ (m - 1) *
      Real.exp (-((m - 1 : ℕ) : ℝ) * c) := by
    dsimp [Q]
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 1
    ring
  have hdamp : Real.exp (-((m - 1 : ℕ) : ℝ) * c) ≤
      Real.exp (-Real.exp (-4 * lam * h) * ((m : ℝ) * m2) * u ^ 2 / 256) := by
    apply Real.exp_le_exp.mpr
    have he := mul_le_mul_of_nonneg_right hhalf
      (show 0 ≤ Real.exp (-4 * lam * h) * u ^ 2 / 128 by positivity)
    dsimp [c, m2]
    nlinarith only [he]
  calc
    _ ≤ bj * ((m : ℝ) * Q ^ (m - 1) * (4 * Real.exp (lam * h) * P)) :=
      mul_le_mul_of_nonneg_left hdiff hbj
    _ = 4 * (m : ℝ) * (bj * Z ^ (m - 1)) * Real.exp (lam * h) * P *
        Real.exp (-((m - 1 : ℕ) : ℝ) * c) := by rw [hQpow]; ring
    _ ≤ 4 * (m : ℝ) * (E * Real.exp (2 * lam * h)) * Real.exp (lam * h) * P *
        Real.exp (-Real.exp (-4 * lam * h) * ((m : ℝ) * m2) * u ^ 2 / 256) := by
      gcongr
    _ = _ := by
      have he : Real.exp (2 * lam * h) * Real.exp (lam * h) = Real.exp (3 * lam * h) := by
        rw [← Real.exp_add]
        congr 1
        ring
      dsimp [P, mu, m3, m2]
      rw [show 4 * (m : ℝ) * (E * Real.exp (2 * lam * h)) * Real.exp (lam * h) =
        4 * (m : ℝ) * E * (Real.exp (2 * lam * h) * Real.exp (lam * h)) by ring, he]

private theorem sgr_bstar_gaussian (T y D b : ℝ) (hT : 0 < T)
    (hb : 1 ≤ b) (hTi : T⁻¹ ≤ b) (hy : 0 ≤ y) (hyb : Real.sqrt y ≤ b)
    (hD : 0 ≤ D) (hD1 : D ≤ 1) (k : ℕ) (hk : k ≤ 3) :
    T ^ (-((k : ℝ) + 1) / 2) +
      Real.sqrt y * D * T ^ (-(2 * (k : ℝ) + 3) / 4) ≤ 2 * b ^ 4 := by
  have hb0 : 0 ≤ b := (by norm_num : (0 : ℝ) ≤ 1).trans hb
  have hrpow (r : ℝ) (hr0 : -3 ≤ r) (hr1 : r ≤ 0) : T ^ r ≤ b ^ 3 := by
    by_cases hT1 : 1 ≤ T
    · exact (Real.rpow_le_one_of_one_le_of_nonpos hT1 hr1).trans (one_le_pow₀ hb)
    · have he := Real.rpow_le_rpow_of_exponent_ge hT (le_of_not_ge hT1) hr0
      have heq : T ^ (-3 : ℝ) = (T⁻¹) ^ 3 := by
        rw [Real.rpow_neg hT.le, Real.rpow_ofNat, inv_pow]
      rw [heq] at he
      exact he.trans (pow_le_pow_left₀ (inv_pos.mpr hT).le hTi 3)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hk3 : (k : ℝ) ≤ 3 := by exact_mod_cast hk
  have h0 := hrpow (-((k : ℝ) + 1) / 2) (by linarith only [hk0, hk3]) (by linarith only [hk0])
  have h1 := hrpow (-(2 * (k : ℝ) + 3) / 4) (by linarith only [hk0, hk3]) (by linarith only [hk0])
  have hcoeff : Real.sqrt y * D ≤ b := by
    exact (mul_le_mul hyb hD1 hD hb0).trans_eq (mul_one _)
  have hterm : Real.sqrt y * D * T ^ (-(2 * (k : ℝ) + 3) / 4) ≤ b * b ^ 3 :=
    mul_le_mul hcoeff h1 (Real.rpow_nonneg hT.le _) hb0
  have hp : b ^ 3 ≤ b ^ 4 := pow_le_pow_right₀ hb (by omega)
  nlinarith only [h0, hterm, hp]

private theorem sgr_bstar_polynomial (b lam s y d j0 j1 j2 j3 : ℝ)
    (hb : 1 ≤ b) (hl : 0 ≤ lam) (hlb : lam ≤ b) (hs : 0 ≤ s) (hsb : s ≤ 4 * b ^ 2)
    (hy : 0 ≤ y) (hyb : y ≤ b) (hd : 0 ≤ d) (hdb : d ≤ 2 * b ^ 2)
    (hj0 : 0 ≤ j0) (hj1 : 0 ≤ j1) (hj2 : 0 ≤ j2) (hj3 : 0 ≤ j3)
    (hb0 : j0 ≤ 2 * b ^ 4) (hb1 : j1 ≤ 2 * b ^ 4)
    (hb2 : j2 ≤ 2 * b ^ 4) (hb3 : j3 ≤ 2 * b ^ 4) :
    j1 + lam * j0 ≤ 4 * b ^ 5 ∧
      j3 + 3 * lam * j2 + 3 * lam ^ 2 * j1 + lam ^ 3 * j0 +
        (s + d) * (j1 + lam * j0) + y * (j2 + lam * j1) ≤ 44 * b ^ 7 := by
  have hbnonneg : 0 ≤ b := (by norm_num : (0 : ℝ) ≤ 1).trans hb
  have hU : j1 + lam * j0 ≤ 4 * b ^ 5 := by
    have hprod := mul_le_mul hlb hb0 hj0 hbnonneg
    have hp : b ^ 4 ≤ b ^ 5 := pow_le_pow_right₀ hb (by omega)
    nlinarith only [hb1, hprod, hp]
  refine ⟨hU, ?_⟩
  have hterm1 : 3 * lam * j2 ≤ 6 * b ^ 5 := by
    calc
      _ ≤ 3 * b * (2 * b ^ 4) := by gcongr
      _ = _ := by ring
  have hterm2 : 3 * lam ^ 2 * j1 ≤ 6 * b ^ 6 := by
    calc
      _ ≤ 3 * b ^ 2 * (2 * b ^ 4) := by gcongr
      _ = _ := by ring
  have hterm3 : lam ^ 3 * j0 ≤ 2 * b ^ 7 := by
    calc
      _ ≤ b ^ 3 * (2 * b ^ 4) := by gcongr
      _ = _ := by ring
  have hterm4 : (s + d) * (j1 + lam * j0) ≤ 24 * b ^ 7 := by
    calc
      _ ≤ (4 * b ^ 2 + 2 * b ^ 2) * (4 * b ^ 5) := by gcongr
      _ = _ := by ring
  have hterm5 : y * (j2 + lam * j1) ≤ 4 * b ^ 6 := by
    have hprod := mul_le_mul hlb hb1 hj1 hbnonneg
    have hh : y * (j2 + lam * j1) ≤ b * (2 * b ^ 4 + b * (2 * b ^ 4)) := by gcongr
    have hp : b ^ 5 ≤ b ^ 6 := pow_le_pow_right₀ hb (by omega)
    nlinarith only [hh, hp]
  have hp4 : b ^ 4 ≤ b ^ 7 := pow_le_pow_right₀ hb (by omega)
  have hp5 : b ^ 5 ≤ b ^ 7 := pow_le_pow_right₀ hb (by omega)
  have hp6 : b ^ 6 ≤ b ^ 7 := pow_le_pow_right₀ hb (by omega)
  linarith only [hb3, hterm1, hterm2, hterm3, hterm4, hterm5, hp4, hp5, hp6]

private theorem sgr_bstar_matching (T lam b : ℝ) (hT : 0 < T) (hb : 1 ≤ b)
    (hl : 0 ≤ lam) (hlb : lam ≤ b) (hTi : T⁻¹ ≤ b) :
    (T⁻¹ + lam ^ 2) ^ 8 ≤ 256 * b ^ 16 := by
  have hb0 : 0 ≤ b := (by norm_num : (0 : ℝ) ≤ 1).trans hb
  have hb2 : b ≤ b ^ 2 := by nlinarith only [mul_nonneg hb0 (sub_nonneg.mpr hb)]
  calc
    _ ≤ (b + b ^ 2) ^ 8 := by gcongr
    _ ≤ (2 * b ^ 2) ^ 8 := pow_le_pow_left₀ (by positivity) (by linarith only [hb2]) 8
    _ = _ := by ring

private theorem sgr_gamma_tail (Gamma r D b : ℝ) (hGamma : 0 < Gamma) (hG1 : Gamma ≤ 1)
    (hr : 0 ≤ r) (hrb : r ≤ b) (hD : 0 ≤ D) (hD1 : D ≤ 1) (hb : 1 ≤ b)
    (p : ℕ) (hp : 2 ≤ p) :
    Gamma ^ p + r * D * Gamma ^ p / Real.sqrt Gamma ≤ 2 * Gamma * b := by
  have hb0 : 0 ≤ b := (by norm_num : (0 : ℝ) ≤ 1).trans hb
  have hGp (i : ℕ) (hi : 1 ≤ i) : Gamma ^ i ≤ Gamma := by
    calc
      _ = Gamma ^ (i - 1) * Gamma := by rw [← pow_succ, Nat.sub_add_cancel hi]
      _ ≤ 1 * Gamma := mul_le_mul_of_nonneg_right (pow_le_one₀ hGamma.le hG1) hGamma.le
      _ = _ := one_mul _
  have hGr : Real.sqrt Gamma ≤ 1 := by
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, by simpa using hG1⟩
  have hsqrt : Gamma / Real.sqrt Gamma = Real.sqrt Gamma := by
    apply (div_eq_iff (Real.sqrt_pos.mpr hGamma).ne').mpr
    nlinarith only [Real.sq_sqrt hGamma.le]
  have hGdiv : Gamma ^ p / Real.sqrt Gamma ≤ Gamma := by
    calc
      _ = Gamma ^ (p - 1) * (Gamma / Real.sqrt Gamma) := by
        conv_lhs => rw [show p = p - 1 + 1 by omega, pow_succ]
        ring
      _ = Gamma ^ (p - 1) * Real.sqrt Gamma := by rw [hsqrt]
      _ ≤ Gamma ^ (p - 1) * 1 := mul_le_mul_of_nonneg_left hGr (by positivity)
      _ ≤ Gamma := by simpa only [mul_one] using hGp (p - 1) (by omega)
  have hcoeff : r * D ≤ b := (mul_le_mul hrb hD1 hD hb0).trans_eq (mul_one _)
  have hterm : r * D * Gamma ^ p / Real.sqrt Gamma ≤ b * Gamma := by
    rw [mul_div_assoc]
    exact mul_le_mul hcoeff hGdiv (by positivity) hb0
  have hplain := hGp p (by omega)
  nlinarith only [hterm, hplain, mul_nonneg hGamma.le (sub_nonneg.mpr hb)]

private theorem sgr_scalar_core (T Gamma y lam s : ℝ)
    (hT : 0 < T) (hGamma : 0 < Gamma) (hGamma1 : Gamma ≤ 1)
    (hy : 2 ≤ y) (hl : 0 ≤ lam) (hs : 0 ≤ s) (hsb : s ≤ 4 * lam * y) :
    let D : ℝ := (1 + lam * y)⁻¹
    let J : ℕ → ℝ := fun k => T ^ (-((k : ℝ) + 1) / 2) +
      Real.sqrt y * D * T ^ (-(2 * (k : ℝ) + 3) / 4)
    let U : ℝ := J 1 + lam * J 0
    let Vp : ℝ := J 3 + 3 * lam * J 2 + 3 * lam ^ 2 * J 1 + lam ^ 3 * J 0 +
      (s + D⁻¹) * U + y * (J 2 + lam * J 1)
    let PJ : ℝ := (T⁻¹ + lam ^ 2) ^ 8
    let R1 : ℝ := Gamma ^ 15 + Real.sqrt y * D * Gamma ^ 15 / Real.sqrt Gamma
    let R2 : ℝ := Gamma ^ 14 + Real.sqrt y * D * Gamma ^ 14 / Real.sqrt Gamma
    let b : ℝ := 1 + y + lam + T⁻¹
    1 ≤ b ∧ D⁻¹ ≤ 2 * b ^ 2 ∧ U ≤ 4 * b ^ 5 ∧ Vp ≤ 44 * b ^ 7 ∧
      PJ ≤ 256 * b ^ 16 ∧ R1 ≤ 2 * Gamma * b ∧ R2 ≤ 2 * Gamma * b := by
  dsimp only
  let D : ℝ := (1 + lam * y)⁻¹
  let J : ℕ → ℝ := fun k => T ^ (-((k : ℝ) + 1) / 2) +
    Real.sqrt y * D * T ^ (-(2 * (k : ℝ) + 3) / 4)
  let U : ℝ := J 1 + lam * J 0
  let Vp : ℝ := J 3 + 3 * lam * J 2 + 3 * lam ^ 2 * J 1 + lam ^ 3 * J 0 +
    (s + D⁻¹) * U + y * (J 2 + lam * J 1)
  let b : ℝ := 1 + y + lam + T⁻¹
  have hy0 : 0 ≤ y := by linarith only [hy]
  have hTi : 0 < T⁻¹ := inv_pos.mpr hT
  have hb : 1 ≤ b := by dsimp [b]; linarith only [hy, hl, hTi]
  have hb0 : 0 ≤ b := (by norm_num : (0 : ℝ) ≤ 1).trans hb
  have hyb : y ≤ b := by dsimp [b]; linarith only [hl, hTi]
  have hlb : lam ≤ b := by dsimp [b]; linarith only [hy, hTi]
  have hTb : T⁻¹ ≤ b := by dsimp [b]; linarith only [hy, hl]
  have hDb : 0 < D := by dsimp [D]; positivity
  have hD1 : D ≤ 1 := by
    dsimp [D]
    exact inv_le_one_of_one_le₀ (by nlinarith only [mul_nonneg hl hy0])
  have hyroot : Real.sqrt y ≤ b := by
    have hh : y ≤ y ^ 2 := by
      have hm := mul_nonneg hy0 (show 0 ≤ y - 1 by linarith only [hy])
      nlinarith only [hm]
    exact (Real.sqrt_le_iff.mpr ⟨hy0, hh⟩).trans hyb
  have hDinv : D⁻¹ ≤ 2 * b ^ 2 := by
    have hyl := mul_le_mul hlb hyb hy0 hb0
    dsimp [D]
    rw [inv_inv]
    nlinarith only [hyl, one_le_pow₀ hb (n := 2)]
  have hsb' : s ≤ 4 * b ^ 2 := by
    have hyl := mul_le_mul hlb hyb hy0 hb0
    nlinarith only [hsb, hyl]
  have hJ0 (k : ℕ) : 0 ≤ J k := by dsimp [J]; positivity
  have hJ (k : ℕ) (hk : k ≤ 3) : J k ≤ 2 * b ^ 4 :=
    sgr_bstar_gaussian T y D b hT hb hTb hy0 hyroot hDb.le hD1 k hk
  have hUV := sgr_bstar_polynomial b lam s y D⁻¹ (J 0) (J 1) (J 2) (J 3)
    hb hl hlb hs hsb' hy0 hyb (inv_pos.mpr hDb).le hDinv
    (hJ0 0) (hJ0 1) (hJ0 2) (hJ0 3)
    (hJ 0 (by omega)) (hJ 1 (by omega)) (hJ 2 (by omega)) (hJ 3 (by omega))
  have hPJ := sgr_bstar_matching T lam b hT hb hl hlb hTb
  have hR1 := sgr_gamma_tail Gamma (Real.sqrt y) D b hGamma hGamma1
    (Real.sqrt_nonneg y) hyroot hDb.le hD1 hb 15 (by omega)
  have hR2 := sgr_gamma_tail Gamma (Real.sqrt y) D b hGamma hGamma1
    (Real.sqrt_nonneg y) hyroot hDb.le hD1 hb 14 (by omega)
  exact ⟨hb, hDinv, hUV.1, hUV.2, hPJ, hR1, hR2⟩

private theorem sgr_actual_low_powers
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (n m : ℕ) (h lam s y bj E : ℝ) (hh : 0 < h)
    (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (hl : 0 ≤ lam) (hs : 0 ≤ s) (hsq : s ≤ lam ^ 2) (hslope : s * h ≤ lam)
    (hy : 2 ≤ y)
    (hnV : (1 / 2 : ℝ) ≤ (n : ℝ) * variance (id : ℝ → ℝ) nu)
    (hnm2 : (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂nu) ≤ (4 / 3 : ℝ))
    (hnmu : (n : ℝ) * |∫ a : ℝ, a ∂nu| ≤ (1 / 2 : ℝ))
    (hbj : 0 ≤ bj) (hE : 0 ≤ E)
    (hZp : bj * (∫ a : ℝ, Real.exp (lam * a - s * a ^ 2) ∂nu) ^ m ≤ E)
    (hZm : bj * (∫ a : ℝ, Real.exp (-lam * a - s * a ^ 2) ∂nu) ^ m ≤ E) :
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
    let T : ℝ := (m : ℝ) * m2
    let Gamma : ℝ := 8 * Real.exp (8 * lam * h) *
      ((∫ a : ℝ, |a| ^ 3 ∂nu) / variance (id : ℝ → ℝ) nu)
    ∀ u v : ℝ, |u| ≤ (1 / 128 : ℝ) / Gamma →
      |v| ≤ (1 / 128 : ℝ) * |u| / Gamma →
      let z : ℂ := (u : ℂ) - (lam : ℂ) * Complex.I
      let zeta : ℂ := (v : ℂ) + (s : ℂ) * Complex.I
      bj * ‖quadraticCharComplex nu z zeta ^ m‖ ≤
        E * Real.exp (-Real.exp (-4 * lam * h) * T * u ^ 2 / 256) ∧
      bj * ‖quadraticCharComplex nu (-z) zeta ^ m‖ ≤
        E * Real.exp (-Real.exp (-4 * lam * h) * T * u ^ 2 / 256) := by
  dsimp only
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
  let rp : Measure ℝ := nu.tilted (fun a => lam * a - s * a ^ 2)
  let rm : Measure ℝ := nu.tilted (fun a => -lam * a - s * a ^ 2)
  let Zp : ℝ := ∫ a : ℝ, Real.exp (lam * a - s * a ^ 2) ∂nu
  let Zm : ℝ := ∫ a : ℝ, Real.exp (-lam * a - s * a ^ 2) ∂nu
  have hd := (quadraticCharComplex_data nu h3 h hh hsupport).2.2.2.1
  have hp := hd lam s
  have hn := hd (-lam) s
  have hZpp : 0 < Zp := hp.2.1
  have hZmp : 0 < Zm := hn.2.1
  have hloP := boundedQuadraticTilt_joint_second_moments_lowFrequency nu n h lam lam s y
    hh hl (Or.inl rfl) hs hsq hslope hsupport hy hnV hnm2 hnmu
  have hloM := boundedQuadraticTilt_joint_second_moments_lowFrequency nu n h lam (-lam) s y
    hh hl (Or.inr rfl) hs hsq hslope hsupport hy hnV hnm2 hnmu
  dsimp only at hloP hloM
  rcases hloP with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hloP⟩
  rcases hloM with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hloM⟩
  intro u v hu hv
  let z : ℂ := (u : ℂ) - (lam : ℂ) * Complex.I
  let zeta : ℂ := (v : ℂ) + (s : ℂ) * Complex.I
  let g : ℝ := Real.exp (-Real.exp (-4 * lam * h) * ((m : ℝ) * m2) * u ^ 2 / 256)
  have hm20 : 0 ≤ m2 := integral_nonneg fun a => sq_nonneg a
  have hweak : Real.exp (-Real.exp (-(4 * lam * h)) *
      ((m : ℝ) * m2) * u ^ 2 / 128) ≤ g := by
    apply Real.exp_le_exp.mpr
    have he : Real.exp (-(4 * lam * h)) = Real.exp (-4 * lam * h) := by congr 1; ring
    rw [he]
    nlinarith only [mul_nonneg
      (mul_nonneg (Real.exp_pos (-4 * lam * h)).le
        (mul_nonneg (Nat.cast_nonneg m) hm20)) (sq_nonneg u)]
  have hcp : ‖quadraticChar rp u v‖ ^ m ≤ g := by
    simpa only [norm_pow] using ((hloP m u v hu hv).1.trans hweak)
  have hcm : ‖quadraticChar rm (-u) v‖ ^ m ≤ g := by
    simpa only [norm_pow] using ((hloM m u v hu hv).2.trans hweak)
  have heqp : quadraticCharComplex nu z zeta = (Zp : ℂ) * quadraticChar rp u v := hp.2.2.2 u v
  have heqm : quadraticCharComplex nu (-z) zeta = (Zm : ℂ) * quadraticChar rm (-u) v := by
    have he : -z = ((-u : ℝ) : ℂ) - ((-lam : ℝ) : ℂ) * Complex.I := by
      dsimp [z]
      push_cast
      ring
    rw [he]
    exact hn.2.2.2 (-u) v
  constructor
  · rw [heqp, mul_pow, norm_mul, norm_pow, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZpp]
    calc
      _ = (bj * Zp ^ m) * ‖quadraticChar rp u v‖ ^ m := by ring
      _ ≤ E * g := mul_le_mul hZp hcp (by positivity) hE
  · rw [heqm, mul_pow, norm_mul, norm_pow, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZmp]
    calc
      _ = (bj * Zm ^ m) * ‖quadraticChar rm (-u) v‖ ^ m := by ring
      _ ≤ E * g := mul_le_mul hZm hcm (by positivity) hE

private theorem sgr_norm_factorization (d : Fin 2)
    (bj vq : ℝ) (hbj : 0 ≤ bj) (B Xi ap am z ep em : ℂ) :
    ‖(bj : ℂ) * (Complex.exp ((vq : ℂ) * Complex.I) * B * Xi *
      (if d = 0 then ap - am else Complex.I * z * (ep * ap + em * am)))‖ =
      bj * ‖B‖ * ‖Xi‖ *
        ‖if d = 0 then ap - am else Complex.I * z * (ep * ap + em * am)‖ := by
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hbj,
    Complex.norm_exp_mul_I, Complex.ofReal_im, neg_zero, Real.exp_zero, one_mul]
  ring


private theorem sgr_partition_indicator (a : ℝ) (b c : ℝ → ℝ)
    (H : ℝ × ℝ → ℝ) :
    let regions : Fin 4 → Set (ℝ × ℝ) := fun k =>
      if k = 0 then {p | |p.1| ≤ a ∧ |p.2| ≤ b p.1}
      else if k = 1 then {p | |p.1| ≤ a ∧ b p.1 < |p.2|}
      else if k = 2 then {p | a < |p.1| ∧ |p.2| ≤ c p.1}
      else {p | a < |p.1| ∧ c p.1 < |p.2|}
    ∀ p : ℝ × ℝ, (∑ k : Fin 4, (regions k).indicator H p) = H p := by
  intro regions p
  by_cases hu : |p.1| ≤ a
  · by_cases hv : |p.2| ≤ b p.1
    · simp [Fin.sum_univ_succ, regions, Set.indicator, hu, hv, not_lt.mpr hu, not_lt.mpr hv]
    · simp [Fin.sum_univ_succ, regions, Set.indicator, hu, hv, not_lt.mpr hu, lt_of_not_ge hv]
  · by_cases hv : |p.2| ≤ c p.1
    · simp [Fin.sum_univ_succ, regions, Set.indicator, hu, hv, lt_of_not_ge hu, not_lt.mpr hv]
    · simp [Fin.sum_univ_succ, regions, Set.indicator, hu, hv, lt_of_not_ge hu, lt_of_not_ge hv]

private theorem sgr_coarse_table_sums
    (n : ℕ) (mu m3 T Gamma h lam b Delta U Vpoly PJ R1tail R2tail E : ℝ)
    (A B : Fin 4 → ℝ)
    (hm3 : 0 ≤ m3) (hT : 0 < T) (hGamma : 0 < Gamma) (hh : 0 < h)
    (hDelta : 0 < Delta) (hU0 : 0 ≤ U) (hVp0 : 0 ≤ Vpoly) (hPJ0 : 0 ≤ PJ)
    (hR10 : 0 ≤ R1tail) (hR20 : 0 ≤ R2tail) (hb : 1 ≤ b) (hl : 0 ≤ lam)
    (hlb : lam ≤ b) (hh1 : h ≤ 1) (hG1 : Gamma ≤ 1) (hT7 : T ≤ 7)
    (hDinv : Delta⁻¹ ≤ 2 * b ^ 2) (hU : U ≤ 4 * b ^ 5)
    (hVp : Vpoly ≤ 44 * b ^ 7) (hPj : PJ ≤ 256 * b ^ 16)
    (hR1 : R1tail ≤ 2 * Gamma * b) (hR2 : R2tail ≤ 2 * Gamma * b)
    (hExp8 : 1 ≤ E)
    (hGammaRn : Gamma ≤ 16 * E * ((n : ℝ) * |mu| + (n : ℝ) * m3))
    (hAe0 : A 0 = T * ((n : ℝ) * |mu| * U + (n : ℝ) * m3 * Vpoly))
    (hAe1 : A 1 = Gamma * Delta⁻¹) (hAe2 : A 2 = PJ * R1tail)
    (hAe3 : A 3 = (h * Delta⁻¹) ^ 31 * Gamma ^ 30)
    (hBe0 : B 0 = U)
    (hBe1 : B 1 = Gamma ^ 2 * Delta⁻¹ ^ 2 + lam * Gamma * Delta⁻¹)
    (hBe2 : B 2 = PJ * (R2tail + lam * R1tail))
    (hBe3 : B 3 = (h * Delta⁻¹) ^ 31 * (Gamma ^ 29 + lam * Gamma ^ 30)) :
    (∑ k : Fin 4, A k) ≤ (2 : ℝ) ^ 40 *
      (((n : ℝ) * |mu| + (n : ℝ) * m3) * E * b ^ 128) ∧
    (∑ k : Fin 4, B k) ≤ (2 : ℝ) ^ 40 * b ^ 128 := by
  have hE0 : 0 ≤ E := (by norm_num : (0 : ℝ) ≤ 1).trans hExp8
  have hb0 : 0 ≤ b := (by norm_num : (0 : ℝ) ≤ 1).trans hb
  have hpow (i j : ℕ) (hij : i ≤ j) : b ^ i ≤ b ^ j := pow_le_pow_right₀ hb hij
  have hGp (p : ℕ) (hp : 1 ≤ p) : Gamma ^ p ≤ Gamma := by
    calc
      _ = Gamma ^ (p - 1) * Gamma := by rw [← pow_succ, Nat.sub_add_cancel hp]
      _ ≤ 1 * Gamma := mul_le_mul_of_nonneg_right (pow_le_one₀ hGamma.le hG1) hGamma.le
      _ = _ := one_mul _
  have hU44 : U ≤ 44 * b ^ 7 := by
    exact hU.trans ((mul_le_mul_of_nonneg_left (hpow 5 7 (by omega)) (by norm_num)).trans
      (mul_le_mul_of_nonneg_right (by norm_num : (4 : ℝ) ≤ 44) (by positivity)))
  let Rn : ℝ := (n : ℝ) * |mu| + (n : ℝ) * m3
  change Gamma ≤ 16 * E * Rn at hGammaRn
  have hRn : 0 ≤ Rn := by dsimp [Rn]; positivity
  have hA0 : A 0 ≤ 308 * Rn * b ^ 7 := by
    calc
      _ ≤ 7 * ((n : ℝ) * |mu| * (44 * b ^ 7) + (n : ℝ) * m3 * (44 * b ^ 7)) := by
        rw [hAe0]
        gcongr
      _ = _ := by dsimp [Rn]; ring
  have hA1 : A 1 ≤ 2 * Gamma * b ^ 2 := by rw [hAe1]; nlinarith only [mul_le_mul_of_nonneg_left hDinv hGamma.le]
  have hA2 : A 2 ≤ 512 * Gamma * b ^ 17 := by
    calc
      _ ≤ (256 * b ^ 16) * (2 * Gamma * b) := by rw [hAe2]; gcongr
      _ = _ := by ring
  have hHD : (h * Delta⁻¹) ^ 31 ≤ (2 : ℝ) ^ 31 * b ^ 62 := by
    calc
      _ ≤ (1 * (2 * b ^ 2)) ^ 31 := by gcongr
      _ = _ := by ring
  have hA3 : A 3 ≤ (2 : ℝ) ^ 31 * Gamma * b ^ 62 := by
    calc
      _ ≤ ((2 : ℝ) ^ 31 * b ^ 62) * Gamma := by
        rw [hAe3]
        exact mul_le_mul hHD (hGp 30 (by omega)) (by positivity) (by positivity)
      _ = _ := by ring
  have hB0 : B 0 ≤ 4 * b ^ 5 := by rw [hBe0]; exact hU
  have hB1 : B 1 ≤ 6 * b ^ 4 := by
    calc
      _ ≤ (1 : ℝ) ^ 2 * (2 * b ^ 2) ^ 2 + b * 1 * (2 * b ^ 2) := by rw [hBe1]; gcongr
      _ ≤ _ := by nlinarith only [hpow 3 4 (by omega)]
  have hb2 : b ≤ b ^ 2 := by nlinarith only [mul_nonneg hb0 (sub_nonneg.mpr hb)]
  have hR1one : R1tail ≤ 2 * b := by
    calc
      _ ≤ 2 * Gamma * b := hR1
      _ ≤ 2 * 1 * b := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hG1 (by norm_num)) hb0
      _ = _ := by ring
  have hR2one : R2tail ≤ 2 * b := by
    calc
      _ ≤ 2 * Gamma * b := hR2
      _ ≤ 2 * 1 * b := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hG1 (by norm_num)) hb0
      _ = _ := by ring
  have hB2 : B 2 ≤ 1024 * b ^ 18 := by
    calc
      _ ≤ (256 * b ^ 16) * (2 * 1 * b + b * (2 * 1 * b)) := by
        rw [hBe2]
        exact mul_le_mul hPj
          (add_le_add (by simpa only [mul_one] using hR2one)
            (mul_le_mul hlb (by simpa only [mul_one] using hR1one) hR10 hb0))
          (add_nonneg hR20 (mul_nonneg hl hR10)) (by positivity)
      _ ≤ (256 * b ^ 16) * (4 * b ^ 2) := by gcongr; nlinarith only [hb2]
      _ = _ := by ring
  have hB3 : B 3 ≤ (2 : ℝ) ^ 32 * b ^ 63 := by
    calc
      _ ≤ ((2 : ℝ) ^ 31 * b ^ 62) * (1 + b * 1) := by
        rw [hBe3]
        gcongr
        · exact pow_le_one₀ hGamma.le hG1
        · exact pow_le_one₀ hGamma.le hG1
      _ ≤ ((2 : ℝ) ^ 31 * b ^ 62) * (2 * b) := by gcongr; linarith only [hb]
      _ = _ := by ring
  let Qodd : ℝ := Rn * E * b ^ 128
  have hQodd : 0 ≤ Qodd := by dsimp [Qodd]; positivity
  have hAc0 : A 0 ≤ 308 * Qodd := by
    refine hA0.trans ?_
    calc
      _ = 308 * Rn * 1 * b ^ 7 := by ring
      _ ≤ 308 * Rn * E * b ^ 128 := by gcongr <;> norm_num
      _ = _ := by dsimp [Qodd]; ring
  have hAc1 : A 1 ≤ 32 * Qodd := by
    refine hA1.trans ?_
    calc
      _ ≤ 2 * (16 * E * Rn) * b ^ 128 := by gcongr <;> norm_num
      _ = _ := by dsimp [Qodd]; ring
  have hAc2 : A 2 ≤ 8192 * Qodd := by
    refine hA2.trans ?_
    calc
      _ ≤ 512 * (16 * E * Rn) * b ^ 128 := by gcongr <;> norm_num
      _ = _ := by dsimp [Qodd]; ring
  have hAc3 : A 3 ≤ (2 : ℝ) ^ 35 * Qodd := by
    refine hA3.trans ?_
    calc
      _ ≤ (2 : ℝ) ^ 31 * (16 * E * Rn) * b ^ 128 := by gcongr <;> norm_num
      _ = _ := by dsimp [Qodd]; ring
  have hAsum : (∑ k : Fin 4, A k) ≤ (2 : ℝ) ^ 40 * Qodd := by
    have he : (∑ k : Fin 4, A k) = A 0 + A 1 + A 2 + A 3 := by simp [Fin.sum_univ_succ]; ring
    rw [he]
    calc
      _ ≤ 308 * Qodd + 32 * Qodd + 8192 * Qodd + (2 : ℝ) ^ 35 * Qodd :=
        add_le_add (add_le_add (add_le_add hAc0 hAc1) hAc2) hAc3
      _ = (308 + 32 + 8192 + (2 : ℝ) ^ 35) * Qodd := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) hQodd
  have hBc0 : B 0 ≤ 4 * b ^ 128 := hB0.trans
    (mul_le_mul_of_nonneg_left (hpow 5 128 (by omega)) (by norm_num))
  have hBc1 : B 1 ≤ 6 * b ^ 128 := hB1.trans
    (mul_le_mul_of_nonneg_left (hpow 4 128 (by omega)) (by norm_num))
  have hBc2 : B 2 ≤ 1024 * b ^ 128 := hB2.trans
    (mul_le_mul_of_nonneg_left (hpow 18 128 (by omega)) (by norm_num))
  have hBc3 : B 3 ≤ (2 : ℝ) ^ 32 * b ^ 128 := hB3.trans
    (mul_le_mul_of_nonneg_left (hpow 63 128 (by omega)) (by positivity))
  have hBsum : (∑ k : Fin 4, B k) ≤ (2 : ℝ) ^ 40 * b ^ 128 := by
    have he : (∑ k : Fin 4, B k) = B 0 + B 1 + B 2 + B 3 := by simp [Fin.sum_univ_succ]; ring
    rw [he]
    calc
      _ ≤ 4 * b ^ 128 + 6 * b ^ 128 + 1024 * b ^ 128 + (2 : ℝ) ^ 32 * b ^ 128 :=
        add_le_add (add_le_add (add_le_add hBc0 hBc1) hBc2) hBc3
      _ = (4 + 6 + 1024 + (2 : ℝ) ^ 32) * b ^ 128 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  exact ⟨hAsum, hBsum⟩

set_option maxHeartbeats 8000000 in
theorem sourceFutureNoiseKernel_growing_region_integrals :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu]
        (n m : ℕ) (h y lam q w : ℝ),
        Integrable (fun a : ℝ => |a| ^ 3) nu →
        0 < variance (id : ℝ → ℝ) nu →
        0 < h → 0 < m →
        (∀ᵐ a : ℝ ∂nu, |a| ≤ h) →
        (∫ a : ℝ, a ^ 2 ∂nu) ≤
          2 * variance (id : ℝ → ℝ) nu →
        (3 / 4 : ℝ) ≤ (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂nu) →
        (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂nu) ≤ (4 / 3 : ℝ) →
        (1 / 2 : ℝ) ≤ (n : ℝ) * variance (id : ℝ → ℝ) nu →
        (n : ℝ) * |∫ a : ℝ, a ∂nu| ≤ (1 / 2 : ℝ) →
        2 ≤ y → 0 ≤ q → y * h ≤ (1 / 64 : ℝ) →
        |w| ≤ h →
        let mu : ℝ := ∫ a : ℝ, a ∂nu
        let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
        let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂nu
        let V : ℝ := variance (id : ℝ → ℝ) nu
        let gamma : ℝ := m3 / V
        let Gamma : ℝ := 8 * Real.exp (8 * lam * h) * gamma
        let T : ℝ := (m : ℝ) * m2
        let N : ℝ := q + T
        let Delta : ℝ := (1 + lam * y)⁻¹
        let s : ℝ := lam * y / Real.sqrt N
        let sj : Fin 2 → ℝ := fun j => if j = 0 then 0 else s
        let z : ℝ → ℂ := fun u => (u : ℂ) - (lam : ℂ) * Complex.I
        let G : Fin 2 → Fin 2 → ℝ × ℝ → ℂ := fun d j p =>
          sourceComplexBoundaryContourIntegrand nu m j d y N lam w q
            (z p.1) ((p.2 : ℂ) + (sj j : ℂ) * Complex.I)
        let regions : Fin 4 → Set (ℝ × ℝ) := fun k =>
          if k = 0 then {p | |p.1| ≤ (1 / 128 : ℝ) / Gamma ∧
            |p.2| ≤ (1 / 128 : ℝ) * |p.1| / Gamma}
          else if k = 1 then {p | |p.1| ≤ (1 / 128 : ℝ) / Gamma ∧
            (1 / 128 : ℝ) * |p.1| / Gamma < |p.2|}
          else if k = 2 then {p | (1 / 128 : ℝ) / Gamma < |p.1| ∧
            |p.2| ≤ |p.1| / (4 * h)}
          else {p | (1 / 128 : ℝ) / Gamma < |p.1| ∧
            |p.1| / (4 * h) < |p.2|}
        let J : ℕ → ℝ := fun k =>
          Real.rpow T (-((k : ℝ) + 1) / 2) +
            Real.sqrt y * Delta * Real.rpow T (-(2 * (k : ℝ) + 3) / 4)
        let U : ℝ := J 1 + lam * J 0
        let Vpoly : ℝ := J 3 + 3 * lam * J 2 +
          3 * lam ^ 2 * J 1 + lam ^ 3 * J 0 +
          (s + Delta⁻¹) * U + y * (J 2 + lam * J 1)
        let PJ : ℝ := (T⁻¹ + lam ^ 2) ^ 8
        let R1tail : ℝ := Gamma ^ 15 +
          Real.sqrt y * Delta * Gamma ^ 15 / Real.sqrt Gamma
        let R2tail : ℝ := Gamma ^ 14 +
          Real.sqrt y * Delta * Gamma ^ 14 / Real.sqrt Gamma
        let A : Fin 4 → ℝ := fun k =>
          if k = 0 then T * ((n : ℝ) * |mu| * U + (n : ℝ) * m3 * Vpoly)
          else if k = 1 then Gamma * Delta⁻¹
          else if k = 2 then PJ * R1tail
          else (h * Delta⁻¹) ^ 31 * Gamma ^ 30
        let B : Fin 4 → ℝ := fun k =>
          if k = 0 then U
          else if k = 1 then Gamma ^ 2 * Delta⁻¹ ^ 2 + lam * Gamma * Delta⁻¹
          else if k = 2 then PJ * (R2tail + lam * R1tail)
          else (h * Delta⁻¹) ^ 31 * (Gamma ^ 29 + lam * Gamma ^ 30)
        let Ebase : ℝ := Real.exp
          (-lam * y * Real.sqrt N + T * lam ^ 2 / 2 +
            (m : ℝ) * lam * |mu| +
            24 * (m : ℝ) * lam ^ 3 * m3 * Real.exp (lam * h) + 200 * lam * h)
        let E512 : ℝ := Real.exp
          (-lam * y * Real.sqrt N + T * lam ^ 2 / 2 +
            (m : ℝ) * lam * |mu| +
            512 * (m : ℝ) * lam ^ 3 * m3 * Real.exp (512 * lam * h) +
            512 * lam * h)
        let Bstar : ℝ := 1 + y + lam + T⁻¹
        let f : ℝ → ℝ := fun r => sourceFutureNoiseKernel nu m y (r, q)
        (1 / 16 : ℝ) ≤ N → N ≤ 7 → y / Real.sqrt N ≤ lam →
        20 * gamma ^ 2 ≤ T →
        (y + lam) * Gamma ≤ (1 / 2048 : ℝ) →
        0 < T ∧ 0 < Gamma ∧ 0 < Delta ∧
          (∀ d j : Fin 2,
            Integrable (G d j) (volume : Measure (ℝ × ℝ))) ∧
          (∀ (d j : Fin 2) (k : Fin 4),
            (∫ p : ℝ × ℝ in regions k, ‖G d j p‖) ≤
              C * Ebase * (if d = 0 then A k else B k)) ∧
          DifferentiableAt ℝ f 0 ∧ DifferentiableAt ℝ f w ∧
          DifferentiableAt ℝ (fun r : ℝ => deriv f r) w ∧
          |deriv f 0| ≤ C * Ebase * (∑ k : Fin 4, A k) ∧
          |deriv (fun r : ℝ => deriv f r) w| ≤
            C * Ebase * (∑ k : Fin 4, B k) ∧
          |deriv f 0| ≤ C * ((n : ℝ) * |mu| + (n : ℝ) * m3) *
            Bstar ^ 128 * E512 ∧
          |deriv (fun r : ℝ => deriv f r) w| ≤ C * Bstar ^ 128 * E512 := by
  trace "SGR_PUBLIC_START"
  obtain ⟨Cm, hCm, hmark⟩ := sourceComplexBoundaryMark_localized_norms
  obtain ⟨Ch, hCh, hhighInt⟩ := sgr_high_integral
  obtain ⟨Co, hCo, houtInt⟩ := sgr_outside_tail_integral
  have hg0 : ∀ k : Fin 4, ∃ C : ℝ, 0 < C ∧ ∀ T L y D : ℝ,
      0 < T → 0 ≤ L → 0 ≤ y → 0 ≤ D →
      let H : ℝ → ℝ := fun u => |u| ^ k.val * (1 + D * Real.sqrt (y * |u|)) *
        Real.exp (-Real.exp (-4 * L) * T * u ^ 2 / 256)
      Integrable H ∧ (∫ u : ℝ, H u) ≤ C * Real.exp (9 * L) *
        (T ^ (-((k.val : ℝ) + 1) / 2) +
          Real.sqrt y * D * T ^ (-(2 * (k.val : ℝ) + 3) / 4)) := by
    intro k
    exact sgr_gaussian_budget k.val (by omega)
  choose cg hcg hgauss using hg0
  let Cg : ℝ := 1 + ∑ k : Fin 4, cg k
  have hCg : 0 < Cg := by
    have hh : 0 ≤ ∑ k : Fin 4, cg k := Finset.sum_nonneg fun k _ => (hcg k).le
    dsimp [Cg]
    linarith only [hh]
  have hcgLe (k : Fin 4) : cg k ≤ Cg := by
    have hh : cg k ≤ ∑ i : Fin 4, cg i :=
      Finset.single_le_sum (fun i _ => (hcg i).le) (Finset.mem_univ k)
    dsimp [Cg]
    linarith
  let Ctab : ℝ := 1 + 16 * Cm * Cg + (8 * 128 ^ 2) * Cm +
    2 * (4752 : ℝ) ^ 8 * Cm * Ch + 2 * (4 : ℝ) ^ 31 * Cm * Co
  have hCtab : 0 < Ctab := by dsimp [Ctab]; positivity
  let C : ℝ := (2 : ℝ) ^ 50 * Ctab
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro nu hprob n m h y lam q w h3 hV hh hm hsupport hm2V hnm2lo hnm2hi hnV hnmu hy hq hyh hw
  letI : IsProbabilityMeasure nu := hprob
  trace "SGR_PARAMETERS_ENTERED"
  intro mu m2 m3 V gamma Gamma T N Delta s sj z G regions J U Vpoly PJ R1tail R2tail A B Ebase E512 Bstar f
  intro hNlo hNhi hlam hclock hsmall
  trace "SGR_GOAL_FOLDED"
  have h2 : Integrable (fun a : ℝ => a ^ 2) nu := by
    apply (integrable_const (h ^ 2)).mono' (by fun_prop)
    filter_upwards [hsupport] with a ha
    simpa only [Real.norm_eq_abs, abs_pow] using pow_le_pow_left₀ (abs_nonneg a) ha 2
  obtain ⟨hm2, hm3, hgamma, hm2gamma⟩ := sgr_raw_root nu h2 h3 hV
  change 0 < m2 at hm2
  change 0 < m3 at hm3
  change 0 < gamma at hgamma
  change m2 ≤ gamma ^ 2 at hm2gamma
  have hT : 0 < T := mul_pos (Nat.cast_pos.mpr hm) hm2
  have hGamma : 0 < Gamma := by dsimp [Gamma]; positivity
  have hN0 : 0 < N := by linarith
  have hy0 : 0 ≤ y := by linarith
  obtain ⟨hl, hs, hsq, hslope⟩ := sgr_parameter_guards y N lam h hy hNlo hlam hh (by linarith)
  have hDelta : 0 < Delta := by dsimp [Delta]; positivity
  have hDelta1 : Delta ≤ 1 := by
    dsimp [Delta]
    exact inv_le_one_of_one_le₀ (by nlinarith only [mul_nonneg hl hy0])
  have hL : 0 ≤ lam * h := mul_nonneg hl hh.le
  have hT7 : T ≤ 7 := by
    change q + T ≤ 7 at hNhi
    linarith only [hNhi, hq]
  have hh1 : h ≤ 1 := by nlinarith only [hyh, hy, hh]
  have hG1 : Gamma ≤ 1 := by
    have he := mul_le_mul_of_nonneg_right (show 2 ≤ y + lam by linarith) hGamma.le
    change (y + lam) * Gamma ≤ (1 / 2048 : ℝ) at hsmall
    nlinarith only [hsmall, he]
  have hm20R : (20 : ℝ) ≤ m := by
    have he := mul_le_mul_of_nonneg_left hm2gamma (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    change 20 * gamma ^ 2 ≤ T at hclock
    change 20 * gamma ^ 2 ≤ (m : ℝ) * m2 at hclock
    nlinarith only [he, hclock, sq_pos_of_pos hgamma]
  have hm20 : 20 ≤ m := by exact_mod_cast hm20R
  have hhalf : T / 2 ≤ ((m - 1 : ℕ) : ℝ) * m2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    have he := mul_nonneg (show 0 ≤ (m : ℝ) / 2 - 1 by linarith only [hm20R]) hm2.le
    dsimp [T]
    nlinarith only [he]
  trace "SGR_RAW_CLOCK_DONE"
  have hmN : (m : ℝ) ≤ (4 / 3 : ℝ) * (n : ℝ) * T := by
    have he := mul_le_mul_of_nonneg_left hnm2lo (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    dsimp [T, m2]
    nlinarith only [he]
  have hgammaN : gamma ≤ 2 * (n : ℝ) * m3 := by
    apply (div_le_iff₀ hV).mpr
    have he := mul_le_mul_of_nonneg_right hnV hm3.le
    nlinarith only [he]
  have hGammaN : Gamma ≤ 16 * Real.exp (8 * lam * h) * (n : ℝ) * m3 := by
    calc
      _ = 8 * Real.exp (8 * lam * h) * gamma := rfl
      _ ≤ 8 * Real.exp (8 * lam * h) * (2 * (n : ℝ) * m3) := by gcongr
      _ = _ := by ring
  have hsj (j : Fin 2) : 0 ≤ sj j ∧ sj j ≤ s ∧ sj j ≤ lam ^ 2 ∧ sj j * h ≤ lam := by
    by_cases hj : j = 0
    · simp only [sj, hj, ite_true]
      exact ⟨le_rfl, hs, sq_nonneg lam, by simpa using hl⟩
    · simpa only [sj, hj, ite_false] using ⟨hs, le_rfl, hsq, hslope⟩
  trace "SGR_PARAMETER_GUARDS_DONE"
  let bj : Fin 2 → ℝ := fun j => if j = 0 then Real.exp (-lam * y * Real.sqrt N)
    else Real.exp (-s * q)
  let Zp : Fin 2 → ℝ := fun j => ∫ a : ℝ, Real.exp (lam * a - sj j * a ^ 2) ∂nu
  let Zm : Fin 2 → ℝ := fun j => ∫ a : ℝ, Real.exp (-lam * a - sj j * a ^ 2) ∂nu
  let rp : Fin 2 → Measure ℝ := fun j => nu.tilted (fun a => lam * a - sj j * a ^ 2)
  let rm : Fin 2 → Measure ℝ := fun j => nu.tilted (fun a => -lam * a - sj j * a ^ 2)
  let E0 : ℝ := Real.exp (-lam * y * Real.sqrt N + T * lam ^ 2 / 2 +
    (m : ℝ) * lam * |mu| + 24 * (m : ℝ) * lam ^ 3 * m3 * Real.exp (lam * h))
  have hE0 : 0 < E0 := Real.exp_pos _
  have hbj (j : Fin 2) : 0 < bj j := by dsimp [bj]; split_ifs <;> positivity
  have hnormal := sgr_split_normalizer nu h lam y N q m hh hN0 hl hs hsq hslope hsupport rfl
  have hZp (j : Fin 2) : 0 < Zp j ∧ bj j * (Zp j) ^ m ≤ E0 :=
    ⟨(hnormal j lam (Or.inl rfl)).1, (hnormal j lam (Or.inl rfl)).2.2⟩
  have hZm (j : Fin 2) : 0 < Zm j ∧ bj j * (Zm j) ^ m ≤ E0 :=
    ⟨(hnormal j (-lam) (Or.inr rfl)).1, (hnormal j (-lam) (Or.inr rfl)).2.2⟩
  trace "SGR_NORMALIZERS_DONE"
  let bm : Fin 2 → ℝ → ℝ → ℂ := fun j => sourceComplexBoundaryMark j y N lam
  have hbm (j : Fin 2) (u : ℝ) := hmark y N lam hy hNlo hNhi hlam j u
  dsimp only at hbm
  have hBi (j : Fin 2) (u : ℝ) : Integrable (fun v => ‖bm j u v‖) ∧
      Integrable (fun v => |v| * ‖bm j u v‖) := by
    rcases hbm j u with ⟨_, _, _, hi, hvi, _, _, _⟩
    exact ⟨hi, hvi⟩
  have hBn (j : Fin 2) (u : ℝ) : (∫ v : ℝ, ‖bm j u v‖) ≤
      Cm * (1 + Delta * Real.sqrt (y * |u|)) := by
    rcases hbm j u with ⟨_, _, _, _, _, hb, _, _⟩
    exact hb
  have hBv (j : Fin 2) (u : ℝ) : (∫ v : ℝ, |v| * ‖bm j u v‖) ≤
      Cm * (Delta⁻¹ + y * |u|) * (1 + Delta * Real.sqrt (y * |u|)) := by
    rcases hbm j u with ⟨_, _, _, _, _, _, hb, _⟩
    exact hb
  have hBo (j : Fin 2) (u aStar : ℝ) (haStar : 0 < aStar) (hguard : aStar * y ≤ (1 / 16 : ℝ)) :
      IntegrableOn (fun v => ‖bm j u v‖) {v | |u| / aStar < |v|} ∧
      (∫ v : ℝ in {v | |u| / aStar < |v|}, ‖bm j u v‖) ≤
        Cm / (1 + Delta * |u| / aStar) ^ 31 := by
    rcases hbm j u with ⟨_, _, _, _, _, _, _, ho⟩
    exact ho aStar haStar hguard
  trace "SGR_MARKS_DONE"
  obtain ⟨Cstrip, hCstrip, hcont⟩ := sourceComplexBoundary_contour_displacement nu h3 hV h hh hsupport
    m y N lam w q hy hNlo hNhi hlam
  trace "SGR_CONTOUR_DATA_OBTAINED"
  have hGc (d j : Fin 2) : Continuous (G d j) := by
    have hc : Continuous (fun p : ℂ × ℂ =>
        sourceComplexBoundaryContourIntegrand nu m j d y N lam w q p.1 p.2) :=
      (hcont j d).1.continuous
    have hmap : Continuous (fun p : ℝ × ℝ =>
        (z p.1, (p.2 : ℂ) + (sj j : ℂ) * Complex.I)) := by
      dsimp [z]
      fun_prop
    have hcomp := hc.comp hmap
    exact hcomp
  trace "SGR_CONTOUR_CONTINUITY_DONE"
  have hGi (d j : Fin 2) : Integrable (G d j) := by
    have hi := (hcont j d).2.2.1 (-lam) (sj j)
      (by simpa only [abs_neg, abs_of_nonneg hl] using (le_rfl : lam ≤ lam))
      (by simpa only [abs_of_nonneg (hsj j).1] using (hsj j).2.1)
    simpa only [G, z, Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using hi
  trace "SGR_CONTOUR_L1_DONE"
  have hreal := sourceFutureNoiseKernel_complex_boundary_identity nu h3 hV h hh hsupport
    m y lam w q hy hq hNlo hNhi hlam
  dsimp only at hreal
  have hdata := (quadraticCharComplex_data nu h3 h hh hsupport).2.2.2.1
  have hplus (j : Fin 2) (u v : ℝ) : quadraticCharComplex nu (z u)
      ((v : ℂ) + (sj j : ℂ) * Complex.I) = (Zp j : ℂ) * quadraticChar (rp j) u v :=
    (hdata lam (sj j)).2.2.2 u v
  have hminus (j : Fin 2) (u v : ℝ) : quadraticCharComplex nu (-z u)
      ((v : ℂ) + (sj j : ℂ) * Complex.I) = (Zm j : ℂ) * quadraticChar (rm j) (-u) v := by
    have he : -z u = ((-u : ℝ) : ℂ) - ((-lam : ℝ) : ℂ) * Complex.I := by
      dsimp [z]
      push_cast
      ring
    rw [he]
    exact (hdata (-lam) (sj j)).2.2.2 (-u) v
  let ap : Fin 2 → ℝ → ℝ → ℂ := fun j u v =>
    quadraticCharComplex nu (z u) ((v : ℂ) + (sj j : ℂ) * Complex.I) ^ m
  let am : Fin 2 → ℝ → ℝ → ℂ := fun j u v =>
    quadraticCharComplex nu (-z u) ((v : ℂ) + (sj j : ℂ) * Complex.I) ^ m
  let ep : ℝ → ℂ := fun u => Complex.exp (z u * (w : ℂ) * Complex.I)
  let em : ℝ → ℂ := fun u => Complex.exp (-z u * (w : ℂ) * Complex.I)
  let Xi : Fin 2 → ℝ → ℝ → ℂ := fun j u v =>
    quadraticFullNoiseCharComplex nu (z u) ((v : ℂ) + (sj j : ℂ) * Complex.I)
  let R : Fin 2 → Fin 2 → ℝ → ℝ → ℂ := fun d j u v =>
    if d = 0 then ap j u v - am j u v
    else Complex.I * z u * (ep u * ap j u v + em u * am j u v)
  trace "SGR_REAL_ID_AND_RAW_FACTORS_READY"
  have hraw (d j : Fin 2) (u v : ℝ) : G d j (u, v) = (bj j : ℂ) *
      (Complex.exp (((v * q : ℝ) : ℂ) * Complex.I) * bm j u v * Xi j u v * R d j u v) := by
    have hf := (hreal.2.2.2.2.1 d j).2 u v
    change G d j (u, v) = _ at hf
    rw [hf]
    dsimp [R, ap, am, ep, em, Xi, bm]
    rw [hplus, hminus, mul_pow, mul_pow]
    by_cases hd : d = 0 <;> simp only [hd, ite_true, ite_false] <;> ring
  have hGn (d j : Fin 2) (u v : ℝ) : ‖G d j (u, v)‖ = bj j * ‖bm j u v‖ * ‖Xi j u v‖ *
      ‖if d = 0 then ap j u v - am j u v
        else Complex.I * z u * (ep u * ap j u v + em u * am j u v)‖ := by
    rw [hraw]
    exact sgr_norm_factorization d (bj j) (v * q) (hbj j).le
      (bm j u v) (Xi j u v) (ap j u v) (am j u v) (z u) (ep u) (em u)
  trace "SGR_RAW_FACTORIZATION_DONE"
  have hphase (u : ℝ) := sgr_phase_norm u lam w h hl hw
  have hweighted (j : Fin 2) (u v : ℝ) :=
    sgr_actual_weighted_powers nu h3 hV h lam (sj j) (bj j) E0 m hh hm hsupport hm2V
      hl (hsj j).1 (hsj j).2.2.1 (hsj j).2.2.2 (hbj j).le hE0.le (hZp j).2 (hZm j).2 u v
  dsimp only at hweighted
  have htrivial (d j : Fin 2) (u v : ℝ) :
      ‖G d j (u, v)‖ ≤ 2 * E0 * Real.exp (99 * lam * h) *
        (if d = 0 then 1 else |u| + lam) * ‖bm j u v‖ := by
    have hh := sgr_multiplier_bound d (G d j (u, v)) (bm j u v) (Xi j u v)
      (ap j u v) (am j u v) (z u) (ep u) (em u) (bj j)
      (E0 * Real.exp (98 * lam * h)) (|u| + lam) (Real.exp (lam * h))
      (hbj j).le (by positivity) (by positivity) (by positivity)
      (hphase u).1 (hphase u).2.1 (hphase u).2.2
      (hweighted j u v).1 (hweighted j u v).2.1 (hGn d j u v)
    refine hh.trans ?_
    by_cases hd : d = 0
    · simp only [hd, ite_true, mul_one]
      have he : Real.exp (98 * lam * h) ≤ Real.exp (99 * lam * h) :=
        Real.exp_le_exp.mpr (by nlinarith only [hL])
      nlinarith only [mul_le_mul_of_nonneg_left he
        (show 0 ≤ 2 * E0 * ‖bm j u v‖ by positivity)]
    · simp only [hd, ite_false]
      have he : Real.exp (98 * lam * h) * Real.exp (lam * h) = Real.exp (99 * lam * h) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = 2 * E0 * (Real.exp (98 * lam * h) * Real.exp (lam * h)) *
            (|u| + lam) * ‖bm j u v‖ := by ring
        _ ≤ _ := by rw [he]
  have hhigh (d j : Fin 2) (u v : ℝ) (hu : u ≠ 0) (hv : |v| ≤ |u| / (4 * h)) :
      ‖G d j (u, v)‖ ≤ 2 * (4752 : ℝ) ^ 8 * E0 * Real.exp (163 * lam * h) * PJ *
        ((if d = 0 then 1 else |u| + lam) / |u| ^ 16) * ‖bm j u v‖ := by
    have hweights := (hweighted j u v).2.2 hu hv
    let M : ℝ := E0 * (4752 : ℝ) ^ 8 * Real.exp (162 * lam * h) * PJ / |u| ^ 16
    have hh := sgr_multiplier_bound d (G d j (u, v)) (bm j u v) (Xi j u v)
      (ap j u v) (am j u v) (z u) (ep u) (em u) (bj j) M
      (|u| + lam) (Real.exp (lam * h))
      (hbj j).le (by dsimp [M, PJ]; positivity) (by positivity) (by positivity)
      (hphase u).1 (hphase u).2.1 (hphase u).2.2 hweights.1 hweights.2 (hGn d j u v)
    refine hh.trans ?_
    by_cases hd : d = 0
    · simp only [hd, ite_true, mul_one]
      have he : Real.exp (162 * lam * h) ≤ Real.exp (163 * lam * h) :=
        Real.exp_le_exp.mpr (by nlinarith only [hL])
      dsimp [M]
      calc
        _ = (2 * (4752 : ℝ) ^ 8 * E0 * PJ * ‖bm j u v‖ / |u| ^ 16) *
            Real.exp (162 * lam * h) := by ring
        _ ≤ (2 * (4752 : ℝ) ^ 8 * E0 * PJ * ‖bm j u v‖ / |u| ^ 16) *
            Real.exp (163 * lam * h) := mul_le_mul_of_nonneg_left he (by dsimp [PJ]; positivity)
        _ = _ := by ring
    · simp only [hd, ite_false]
      have he : Real.exp (162 * lam * h) * Real.exp (lam * h) = Real.exp (163 * lam * h) := by
        rw [← Real.exp_add]
        congr 1
        ring
      dsimp [M]
      calc
        _ = 2 * (4752 : ℝ) ^ 8 * E0 * (Real.exp (162 * lam * h) * Real.exp (lam * h)) *
            PJ * ((|u| + lam) / |u| ^ 16) * ‖bm j u v‖ := by ring
        _ ≤ _ := by rw [he]
  trace "SGR_TRIVIAL_HIGH_DONE"
  let gauss : ℝ → ℝ := fun u => Real.exp
    (-Real.exp (-4 * (lam * h)) * T * u ^ 2 / 256)
  have hgauss0 (u : ℝ) : 0 ≤ gauss u := (Real.exp_pos _).le
  have hgamma2h := sgr_gamma_bound nu h3 hV h hh hsupport hm2V
  have hnoise (j : Fin 2) (u v : ℝ) : ‖Xi j u v‖ ≤ Real.exp (98 * lam * h) :=
    sgr_actual_noise_norm nu h3 hV h hh hsupport hgamma2h lam (sj j) hl
      (hsj j).1 (hsj j).2.2.2 u v
  have hlow0 (j : Fin 2) (u v : ℝ)
      (hu : |u| ≤ (1 / 128 : ℝ) / Gamma)
      (hv : |v| ≤ (1 / 128 : ℝ) * |u| / Gamma) :
      ‖G 0 j (u, v)‖ ≤ (4 * (m : ℝ) * E0 * Real.exp (101 * lam * h)) * gauss u *
        ((|mu| * (|u| + lam) + m3 * ((|u| + lam) ^ 3 + s * (|u| + lam))) +
          (m3 * (|u| + lam)) * |v|) * ‖bm j u v‖ := by
    have ho := sgr_actual_low_difference nu h3 n m h lam (sj j) y (bj j) E0 hh hm hsupport
      hl (hsj j).1 (hsj j).2.2.1 (hsj j).2.2.2 hy hnV hnm2hi hnmu
      (hbj j).le hE0.le (hZp j).2 (hZm j).2 hhalf u v hu hv
    have ho' : bj j * ‖ap j u v - am j u v‖ ≤
        4 * (m : ℝ) * E0 * Real.exp (3 * lam * h) *
          (|mu| * (|u| + lam) + m3 *
            ((|u| + lam) ^ 3 + (|u| + lam) * (|v| + s))) * gauss u := by
      have hg : Real.exp (-Real.exp (-4 * lam * h) * T * u ^ 2 / 256) = gauss u := by
        dsimp [gauss]
        congr 3
        ring
      rw [hg] at ho
      exact ho.trans (by gcongr; exact (hsj j).2.1)
    rw [hGn]
    simp only [ite_true]
    calc
      _ = ‖bm j u v‖ * ‖Xi j u v‖ * (bj j * ‖ap j u v - am j u v‖) := by ring
      _ ≤ ‖bm j u v‖ * Real.exp (98 * lam * h) *
          (4 * (m : ℝ) * E0 * Real.exp (3 * lam * h) *
            (|mu| * (|u| + lam) + m3 *
              ((|u| + lam) ^ 3 + (|u| + lam) * (|v| + s))) * gauss u) := by
        gcongr
        exact hnoise j u v
      _ = _ := by
        have he : Real.exp (98 * lam * h) * Real.exp (3 * lam * h) =
            Real.exp (101 * lam * h) := by rw [← Real.exp_add]; congr 1; ring
        calc
          _ = (Real.exp (98 * lam * h) * Real.exp (3 * lam * h)) *
              (4 * (m : ℝ) * E0 * gauss u *
                ((|mu| * (|u| + lam) + m3 * ((|u| + lam) ^ 3 + s * (|u| + lam))) +
                  (m3 * (|u| + lam)) * |v|) * ‖bm j u v‖) := by ring
          _ = _ := by rw [he]; ring
  have hlow1 (j : Fin 2) (u v : ℝ)
      (hu : |u| ≤ (1 / 128 : ℝ) / Gamma)
      (hv : |v| ≤ (1 / 128 : ℝ) * |u| / Gamma) :
      ‖G 1 j (u, v)‖ ≤ (2 * E0 * Real.exp (99 * lam * h)) * gauss u *
        ((|u| + lam) + 0 * |v|) * ‖bm j u v‖ := by
    have hpows := sgr_actual_low_powers nu h3 n m h lam (sj j) y (bj j) E0 hh hsupport
      hl (hsj j).1 (hsj j).2.2.1 (hsj j).2.2.2 hy hnV hnm2hi hnmu
      (hbj j).le hE0.le (hZp j).2 (hZm j).2 u v hu hv
    have hg : Real.exp (-Real.exp (-4 * lam * h) * T * u ^ 2 / 256) = gauss u := by
      dsimp [gauss]
      congr 3
      ring
    rw [hg] at hpows
    have hwp : bj j * ‖ap j u v‖ * ‖Xi j u v‖ ≤ E0 * gauss u * Real.exp (98 * lam * h) :=
      mul_le_mul hpows.1 (hnoise j u v) (norm_nonneg _) (by positivity)
    have hwm : bj j * ‖am j u v‖ * ‖Xi j u v‖ ≤ E0 * gauss u * Real.exp (98 * lam * h) :=
      mul_le_mul hpows.2 (hnoise j u v) (norm_nonneg _) (by positivity)
    have hh := sgr_multiplier_bound 1 (G 1 j (u, v)) (bm j u v) (Xi j u v)
      (ap j u v) (am j u v) (z u) (ep u) (em u) (bj j)
      (E0 * gauss u * Real.exp (98 * lam * h)) (|u| + lam) (Real.exp (lam * h))
      (hbj j).le (by positivity) (by positivity) (by positivity)
      (hphase u).1 (hphase u).2.1 (hphase u).2.2 hwp hwm (hGn 1 j u v)
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [h10, ite_false] at hh
    refine hh.trans_eq ?_
    have he : Real.exp (98 * lam * h) * Real.exp (lam * h) = Real.exp (99 * lam * h) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = 2 * E0 * (Real.exp (98 * lam * h) * Real.exp (lam * h)) * gauss u *
          (|u| + lam) * ‖bm j u v‖ := by ring
      _ = _ := by rw [he]; ring

  trace "SGR_LOW_POINTWISE_DONE"
  have hRmeas (k : Fin 4) : MeasurableSet (regions k) := by
    fin_cases k <;> dsimp [regions] <;> measurability
  have hJnonneg (k : ℕ) : 0 ≤ J k := by dsimp [J]; positivity
  have hJ0p := hJnonneg 0
  have hJ1p := hJnonneg 1
  have hJ2p := hJnonneg 2
  have hJ3p := hJnonneg 3
  have hU0 : 0 ≤ U := add_nonneg hJ1p (mul_nonneg hl hJ0p)
  have hVp0 : 0 ≤ Vpoly := by dsimp only [Vpoly]; positivity
  have hPJ0 : 0 ≤ PJ := by dsimp only [PJ]; positivity
  have hR10 : 0 ≤ R1tail := by dsimp only [R1tail]; positivity
  have hR20 : 0 ≤ R2tail := by dsimp only [R2tail]; positivity
  have hPV0 : 0 ≤ |mu| * U + m3 * Vpoly := by positivity
  have hnPV0 : 0 ≤ (n : ℝ) * |mu| * U + (n : ℝ) * m3 * Vpoly := by positivity
  have hAnonneg (k : Fin 4) : 0 ≤ A k := by
    fin_cases k <;> dsimp only [A] <;> positivity
  have hBnonneg (k : Fin 4) : 0 ≤ B k := by
    fin_cases k <;> dsimp only [B] <;> positivity
  have hA0p := hAnonneg 0
  have hA1p := hAnonneg 1
  have hA2p := hAnonneg 2
  have hA3p := hAnonneg 3
  have hB0p := hBnonneg 0
  have hB1p := hBnonneg 1
  have hB2p := hBnonneg 2
  have hB3p := hBnonneg 3
  have hg (k : Fin 4) :
      Integrable (fun u : ℝ => |u| ^ k.val * (1 + Delta * Real.sqrt (y * |u|)) * gauss u) ∧
      (∫ u : ℝ, |u| ^ k.val * (1 + Delta * Real.sqrt (y * |u|)) * gauss u) ≤
        Cg * Real.exp (9 * (lam * h)) * J k.val := by
    have hh := hgauss k T (lam * h) y Delta hT hL hy0 hDelta.le
    refine ⟨hh.1, hh.2.trans ?_⟩
    change cg k * Real.exp (9 * (lam * h)) * J k.val ≤ _
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hcgLe k) (Real.exp_pos _).le) (hJnonneg _)
  have hbase : Ebase = E0 * Real.exp (200 * lam * h) := by
    dsimp [Ebase, E0]
    rw [← Real.exp_add]
  have hbudget (c : ℝ) (hc : c ≤ 200) : E0 * Real.exp (c * lam * h) ≤ Ebase := by
    rw [hbase]
    apply mul_le_mul_of_nonneg_left _ hE0.le
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_right hc hL]
  have hCI : 16 * Cm * Cg ≤ Ctab := by
    have hh : 0 ≤ Ctab - 16 * Cm * Cg := by dsimp [Ctab]; ring_nf; positivity
    linarith only [hh]
  have hCII : (8 * (128 : ℝ) ^ 2) * Cm ≤ Ctab := by
    have hh : 0 ≤ Ctab - (8 * (128 : ℝ) ^ 2) * Cm := by dsimp [Ctab]; ring_nf; positivity
    linarith only [hh]
  have hCIII : 2 * (4752 : ℝ) ^ 8 * Cm * Ch ≤ Ctab := by
    have hh : 0 ≤ Ctab - 2 * (4752 : ℝ) ^ 8 * Cm * Ch := by dsimp [Ctab]; ring_nf; positivity
    linarith only [hh]
  have hCIV : 2 * (4 : ℝ) ^ 31 * Cm * Co ≤ Ctab := by
    have hh : 0 ≤ Ctab - 2 * (4 : ℝ) ^ 31 * Cm * Co := by dsimp [Ctab]; ring_nf; positivity
    linarith only [hh]
  have hguardII : (128 * Gamma) * y ≤ (1 / 16 : ℝ) := by
    have he := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hl : y ≤ y + lam) hGamma.le
    nlinarith only [he, hsmall]
  have hguardIV : (4 * h) * y ≤ (1 / 16 : ℝ) := by nlinarith only [hyh]
  trace "SGR_REGION_PREPARATION_DONE"
  have hregionOdd (j : Fin 2) (k : Fin 4) :
      (∫ p : ℝ × ℝ in regions k, ‖G 0 j p‖) ≤ Ctab * Ebase * A k := by
    fin_cases k
    · let c : Fin 4 → ℝ := ![|mu| * lam + m3 * (lam ^ 3 + s * lam + Delta⁻¹ * lam),
        |mu| + m3 * (3 * lam ^ 2 + s + Delta⁻¹ + y * lam), m3 * (3 * lam + y), m3]
      have hc (i : Fin 4) : 0 ≤ c i := by fin_cases i <;> dsimp [c] <;> positivity
      have hp (r : ℝ) (hr : 0 ≤ r) :
          (|mu| * (r + lam) + m3 * ((r + lam) ^ 3 + s * (r + lam))) +
          (m3 * (r + lam)) * (Delta⁻¹ + y * r) = ∑ i : Fin 4, c i * r ^ i.val := by
        simp [Fin.sum_univ_succ, c]
        ring
      have hi := sgr_low_integral T (lam * h) y Delta
        (4 * (m : ℝ) * E0 * Real.exp (101 * lam * h)) Cm Cg
        hT hL hy0 hDelta (by positivity) hCm.le
        (G 0 j) (hGc 0 j) (hGi 0 j) (regions 0) (hRmeas 0) (bm j)
        (hBi j) (hBn j) (hBv j)
        (fun r => |mu| * (r + lam) + m3 * ((r + lam) ^ 3 + s * (r + lam)))
        (fun r => m3 * (r + lam)) (by intro r hr; positivity) (by intro r hr; positivity)
        c hc hp hg (by
          rintro ⟨u, v⟩ huv
          have hh : |u| ≤ (1 / 128 : ℝ) / Gamma ∧
              |v| ≤ (1 / 128 : ℝ) * |u| / Gamma := by simpa [regions] using huv
          exact hlow0 j u v hh.1 hh.2)
      have hec : (∑ i : Fin 4, c i * J i.val) = |mu| * U + m3 * Vpoly := by
        simp [Fin.sum_univ_succ, c, U, Vpoly]
        ring
      change (∫ p : ℝ × ℝ in regions 0, ‖G 0 j p‖) ≤
        (4 * (m : ℝ) * E0 * Real.exp (101 * lam * h)) * Cm * Cg *
          Real.exp (9 * (lam * h)) * (∑ i : Fin 4, c i * J i.val) at hi
      rw [hec] at hi
      have he : Real.exp (101 * lam * h) * Real.exp (9 * (lam * h)) =
          Real.exp (110 * lam * h) := by rw [← Real.exp_add]; congr 1; ring
      refine hi.trans ?_
      calc
        _ = 4 * Cm * Cg * (E0 * Real.exp (110 * lam * h)) *
            ((m : ℝ) * (|mu| * U + m3 * Vpoly)) := by
          rw [← he]
          ring
        _ ≤ 4 * Cm * Cg * Ebase *
            (((4 / 3 : ℝ) * (n : ℝ) * T) * (|mu| * U + m3 * Vpoly)) := by
          gcongr <;> first | exact hbudget 110 (by norm_num) | exact hmN
        _ = (16 / 3 : ℝ) * Cm * Cg * Ebase * A 0 := by dsimp [A]; ring
        _ ≤ 16 * Cm * Cg * Ebase * A 0 := by gcongr; norm_num
        _ ≤ Ctab * Ebase * A 0 := by gcongr
    · have hi := sgr_outside_integral Delta (128 * Gamma)
        (2 * E0 * Real.exp (99 * lam * h)) Cm 1 0 hDelta (by positivity)
        (by positivity) hCm.le (by norm_num) (by norm_num)
        (G 0 j) (hGc 0 j) (hGi 0 j) (regions 1) (hRmeas 1) (bm j)
        (fun u => (hBo j u (128 * Gamma) (by positivity) hguardII).1)
        (fun u => (hBo j u (128 * Gamma) (by positivity) hguardII).2)
        (by rintro ⟨u, v⟩ huv
            have hh : (1 / 128 : ℝ) * |u| / Gamma < |v| := by simpa [regions] using huv.2
            convert hh using 1 <;> field_simp)
        (by rintro ⟨u, v⟩ huv; simpa using htrivial 0 j u v)
      refine hi.trans ?_
      calc
        _ = 1024 * Cm * (E0 * Real.exp (99 * lam * h)) * A 1 := by dsimp [A]; ring
        _ ≤ (8 * (128 : ℝ) ^ 2) * Cm * Ebase * A 1 := by
          gcongr
          · norm_num
          · exact hbudget 99 (by norm_num)
        _ ≤ Ctab * Ebase * A 1 := by gcongr
    · have hi := hhighInt Gamma y Delta
        (2 * (4752 : ℝ) ^ 8 * E0 * Real.exp (163 * lam * h) * PJ) Cm 1 0
        hGamma hy0 hDelta.le (by dsimp [PJ]; positivity) hCm.le (by norm_num) (by norm_num)
        (G 0 j) (hGc 0 j) (hGi 0 j) (regions 2) (hRmeas 2)
        (by rintro ⟨u, v⟩ huv; exact le_of_lt (by simpa [regions] using huv.1))
        (bm j) (fun u => (hBi j u).1) (hBn j) (by
          rintro ⟨u, v⟩ huv
          have hh : (1 / 128 : ℝ) / Gamma < |u| ∧ |v| ≤ |u| / (4 * h) := by
            simpa [regions] using huv
          have hu : u ≠ 0 := abs_pos.mp ((by positivity : 0 < (1 / 128 : ℝ) / Gamma).trans hh.1)
          simpa using hhigh 0 j u v hu hh.2)
      refine hi.trans ?_
      calc
        _ = (2 * (4752 : ℝ) ^ 8 * Cm * Ch) * (E0 * Real.exp (163 * lam * h)) * A 2 := by
          dsimp [A, R1tail]
          ring
        _ ≤ (2 * (4752 : ℝ) ^ 8 * Cm * Ch) * Ebase * A 2 := by gcongr; exact hbudget 163 (by norm_num)
        _ ≤ Ctab * Ebase * A 2 := by gcongr
    · have hi := houtInt Gamma Delta (4 * h)
        (2 * E0 * Real.exp (99 * lam * h)) Cm 1 0
        hGamma hDelta (by positivity) (by positivity) hCm.le (by norm_num) (by norm_num)
        (G 0 j) (hGc 0 j) (hGi 0 j) (regions 3) (hRmeas 3)
        (by rintro ⟨u, v⟩ huv
            have hh : (1 / 128 : ℝ) / Gamma < |u| ∧ |u| / (4 * h) < |v| := by
              simpa [regions] using huv
            exact ⟨hh.1.le, hh.2⟩)
        (bm j) (fun u => (hBo j u (4 * h) (by positivity) hguardIV).1)
        (fun u => (hBo j u (4 * h) (by positivity) hguardIV).2)
        (by rintro ⟨u, v⟩ huv; simpa using htrivial 0 j u v)
      refine hi.trans ?_
      calc
        _ = (2 * (4 : ℝ) ^ 31 * Cm * Co) * (E0 * Real.exp (99 * lam * h)) * A 3 := by
          dsimp [A]
          ring
        _ ≤ (2 * (4 : ℝ) ^ 31 * Cm * Co) * Ebase * A 3 := by gcongr; exact hbudget 99 (by norm_num)
        _ ≤ Ctab * Ebase * A 3 := by gcongr
  trace "SGR_ODD_REGIONS_DONE"
  have hregionEven (j : Fin 2) (k : Fin 4) :
      (∫ p : ℝ × ℝ in regions k, ‖G 1 j p‖) ≤ Ctab * Ebase * B k := by
    fin_cases k
    · let c : Fin 4 → ℝ := ![lam, 1, 0, 0]
      have hc (i : Fin 4) : 0 ≤ c i := by fin_cases i <;> dsimp [c] <;> positivity
      have hp (r : ℝ) (hr : 0 ≤ r) : (r + lam) + 0 * (Delta⁻¹ + y * r) =
          ∑ i : Fin 4, c i * r ^ i.val := by simp [Fin.sum_univ_succ, c]; ring
      have hi := sgr_low_integral T (lam * h) y Delta
        (2 * E0 * Real.exp (99 * lam * h)) Cm Cg
        hT hL hy0 hDelta (by positivity) hCm.le
        (G 1 j) (hGc 1 j) (hGi 1 j) (regions 0) (hRmeas 0) (bm j)
        (hBi j) (hBn j) (hBv j) (fun r => r + lam) (fun _ => 0)
        (by intro r hr; positivity) (by intro r hr; norm_num) c hc hp hg (by
          rintro ⟨u, v⟩ huv
          have hh : |u| ≤ (1 / 128 : ℝ) / Gamma ∧
              |v| ≤ (1 / 128 : ℝ) * |u| / Gamma := by simpa [regions] using huv
          exact hlow1 j u v hh.1 hh.2)
      change (∫ p : ℝ × ℝ in regions 0, ‖G 1 j p‖) ≤
        (2 * E0 * Real.exp (99 * lam * h)) * Cm * Cg * Real.exp (9 * (lam * h)) *
          (∑ i : Fin 4, c i * J i.val) at hi
      have hec : (∑ i : Fin 4, c i * J i.val) = U := by
        simp [Fin.sum_univ_succ, c, U]
        ring
      rw [hec] at hi
      have he : Real.exp (99 * lam * h) * Real.exp (9 * (lam * h)) =
          Real.exp (108 * lam * h) := by rw [← Real.exp_add]; congr 1; ring
      refine hi.trans ?_
      calc
        _ = 2 * Cm * Cg * (E0 * Real.exp (108 * lam * h)) * B 0 := by
          rw [← he]
          dsimp [B]
          ring
        _ ≤ 16 * Cm * Cg * Ebase * B 0 := by gcongr; norm_num; exact hbudget 108 (by norm_num)
        _ ≤ Ctab * Ebase * B 0 := by gcongr
    · have hi := sgr_outside_integral Delta (128 * Gamma)
        (2 * E0 * Real.exp (99 * lam * h)) Cm lam 1 hDelta (by positivity)
        (by positivity) hCm.le hl (by norm_num)
        (G 1 j) (hGc 1 j) (hGi 1 j) (regions 1) (hRmeas 1) (bm j)
        (fun u => (hBo j u (128 * Gamma) (by positivity) hguardII).1)
        (fun u => (hBo j u (128 * Gamma) (by positivity) hguardII).2)
        (by rintro ⟨u, v⟩ huv
            have hh : (1 / 128 : ℝ) * |u| / Gamma < |v| := by simpa [regions] using huv.2
            convert hh using 1 <;> field_simp)
        (by rintro ⟨u, v⟩ huv
            have hh := htrivial 1 j u v
            simpa [add_comm] using hh)
      refine hi.trans ?_
      calc
        _ = 8 * Cm * (E0 * Real.exp (99 * lam * h)) *
            (128 * lam * Gamma * Delta⁻¹ + (128 : ℝ) ^ 2 * Gamma ^ 2 * Delta⁻¹ ^ 2) := by ring
        _ ≤ 8 * Cm * Ebase * ((128 : ℝ) ^ 2 *
            (Gamma ^ 2 * Delta⁻¹ ^ 2 + lam * Gamma * Delta⁻¹)) := by
          gcongr
          · exact hbudget 99 (by norm_num)
          · nlinarith only [mul_nonneg hl (mul_nonneg hGamma.le (inv_pos.mpr hDelta).le)]
        _ = ((8 * (128 : ℝ) ^ 2) * Cm) * Ebase * B 1 := by dsimp [B]; ring
        _ ≤ Ctab * Ebase * B 1 := by gcongr
    · have hi := hhighInt Gamma y Delta
        (2 * (4752 : ℝ) ^ 8 * E0 * Real.exp (163 * lam * h) * PJ) Cm lam 1
        hGamma hy0 hDelta.le (by dsimp [PJ]; positivity) hCm.le hl (by norm_num)
        (G 1 j) (hGc 1 j) (hGi 1 j) (regions 2) (hRmeas 2)
        (by rintro ⟨u, v⟩ huv; exact le_of_lt (by simpa [regions] using huv.1))
        (bm j) (fun u => (hBi j u).1) (hBn j) (by
          rintro ⟨u, v⟩ huv
          have hh : (1 / 128 : ℝ) / Gamma < |u| ∧ |v| ≤ |u| / (4 * h) := by
            simpa [regions] using huv
          have hu : u ≠ 0 := abs_pos.mp ((by positivity : 0 < (1 / 128 : ℝ) / Gamma).trans hh.1)
          simpa [add_comm] using hhigh 1 j u v hu hh.2)
      refine hi.trans ?_
      calc
        _ = (2 * (4752 : ℝ) ^ 8 * Cm * Ch) * (E0 * Real.exp (163 * lam * h)) * B 2 := by
          dsimp [B, R1tail, R2tail]
          ring
        _ ≤ (2 * (4752 : ℝ) ^ 8 * Cm * Ch) * Ebase * B 2 := by gcongr; exact hbudget 163 (by norm_num)
        _ ≤ Ctab * Ebase * B 2 := by gcongr
    · have hi := houtInt Gamma Delta (4 * h)
        (2 * E0 * Real.exp (99 * lam * h)) Cm lam 1
        hGamma hDelta (by positivity) (by positivity) hCm.le hl (by norm_num)
        (G 1 j) (hGc 1 j) (hGi 1 j) (regions 3) (hRmeas 3)
        (by rintro ⟨u, v⟩ huv
            have hh : (1 / 128 : ℝ) / Gamma < |u| ∧ |u| / (4 * h) < |v| := by
              simpa [regions] using huv
            exact ⟨hh.1.le, hh.2⟩)
        (bm j) (fun u => (hBo j u (4 * h) (by positivity) hguardIV).1)
        (fun u => (hBo j u (4 * h) (by positivity) hguardIV).2)
        (by rintro ⟨u, v⟩ huv; simpa [add_comm] using htrivial 1 j u v)
      refine hi.trans ?_
      calc
        _ = (2 * (4 : ℝ) ^ 31 * Cm * Co) * (E0 * Real.exp (99 * lam * h)) * B 3 := by
          dsimp [B]
          ring
        _ ≤ (2 * (4 : ℝ) ^ 31 * Cm * Co) * Ebase * B 3 := by gcongr; exact hbudget 99 (by norm_num)
        _ ≤ Ctab * Ebase * B 3 := by gcongr
  trace "SGR_EVEN_REGIONS_DONE"
  have hpartition (d j : Fin 2) : (∫ p : ℝ × ℝ, ‖G d j p‖) =
      ∑ k : Fin 4, ∫ p : ℝ × ℝ in regions k, ‖G d j p‖ := by
    have hsum (p : ℝ × ℝ) : (∑ k : Fin 4, (regions k).indicator (fun p => ‖G d j p‖) p) =
        ‖G d j p‖ := by
      have hp := sgr_partition_indicator ((1 / 128 : ℝ) / Gamma)
        (fun u => (1 / 128 : ℝ) * |u| / Gamma) (fun u => |u| / (4 * h))
        (fun p => ‖G d j p‖) p
      exact hp
    have hi (k : Fin 4) : Integrable ((regions k).indicator (fun p => ‖G d j p‖)) :=
      (hGi d j).norm.indicator (hRmeas k)
    calc
      _ = ∫ p : ℝ × ℝ, ∑ k : Fin 4, (regions k).indicator (fun p => ‖G d j p‖) p := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun p => (hsum p).symm
      _ = ∑ k : Fin 4, ∫ p : ℝ × ℝ, (regions k).indicator (fun p => ‖G d j p‖) p :=
        integral_finsetSum _ (fun k _ => hi k)
      _ = _ := by apply Finset.sum_congr rfl; intro k _; exact integral_indicator (hRmeas k)
  have hplaneOdd (j : Fin 2) : (∫ p : ℝ × ℝ, ‖G 0 j p‖) ≤
      Ctab * Ebase * ∑ k : Fin 4, A k := by
    rw [hpartition]
    calc
      _ ≤ ∑ k : Fin 4, Ctab * Ebase * A k := Finset.sum_le_sum fun k _ => hregionOdd j k
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hplaneEven (j : Fin 2) : (∫ p : ℝ × ℝ, ‖G 1 j p‖) ≤
      Ctab * Ebase * ∑ k : Fin 4, B k := by
    rw [hpartition]
    calc
      _ ≤ ∑ k : Fin 4, Ctab * Ebase * B k := Finset.sum_le_sum fun k _ => hregionEven j k
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hderiv0 : ((deriv f 0 : ℝ) : ℂ) =
      -((((2 * Real.pi) ^ 2 : ℝ) : ℂ)⁻¹) * ∑ j : Fin 2, ∫ p : ℝ × ℝ, G 0 j p := by
    rw [hreal.2.2.2.2.2.1]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun p => ((hreal.2.2.2.2.1 0 j).2 p.1 p.2).symm
  have hderiv1 : ((deriv (fun r : ℝ => deriv f r) w : ℝ) : ℂ) =
      -((((2 * Real.pi) ^ 2 : ℝ) : ℂ)⁻¹) * ∑ j : Fin 2, ∫ p : ℝ × ℝ, G 1 j p := by
    rw [hreal.2.2.2.2.2.2]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun p => ((hreal.2.2.2.2.1 1 j).2 p.1 p.2).symm
  have hcoef : ‖-((((2 * Real.pi) ^ 2 : ℝ) : ℂ)⁻¹)‖ ≤ 1 := by
    rw [norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith only [Real.two_le_pi]))
  have hderivNorm0 : |deriv f 0| ≤ 2 * Ctab * Ebase * ∑ k : Fin 4, A k := by
    calc
      _ = ‖((deriv f 0 : ℝ) : ℂ)‖ := by simp
      _ = ‖-((((2 * Real.pi) ^ 2 : ℝ) : ℂ)⁻¹)‖ *
          ‖∑ j : Fin 2, ∫ p : ℝ × ℝ, G 0 j p‖ := by rw [hderiv0, norm_mul]
      _ ≤ 1 * ‖∑ j : Fin 2, ∫ p : ℝ × ℝ, G 0 j p‖ :=
        mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
      _ ≤ ∑ j : Fin 2, ‖∫ p : ℝ × ℝ, G 0 j p‖ := by simpa only [one_mul] using norm_sum_le _ _
      _ ≤ ∑ j : Fin 2, ∫ p : ℝ × ℝ, ‖G 0 j p‖ :=
        Finset.sum_le_sum fun j _ => norm_integral_le_integral_norm _
      _ ≤ ∑ j : Fin 2, Ctab * Ebase * ∑ k : Fin 4, A k := Finset.sum_le_sum fun j _ => hplaneOdd j
      _ = _ := by simp; ring
  have hderivNorm1 : |deriv (fun r : ℝ => deriv f r) w| ≤
      2 * Ctab * Ebase * ∑ k : Fin 4, B k := by
    calc
      _ = ‖((deriv (fun r : ℝ => deriv f r) w : ℝ) : ℂ)‖ := by simp
      _ = ‖-((((2 * Real.pi) ^ 2 : ℝ) : ℂ)⁻¹)‖ *
          ‖∑ j : Fin 2, ∫ p : ℝ × ℝ, G 1 j p‖ := by rw [hderiv1, norm_mul]
      _ ≤ 1 * ‖∑ j : Fin 2, ∫ p : ℝ × ℝ, G 1 j p‖ :=
        mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
      _ ≤ ∑ j : Fin 2, ‖∫ p : ℝ × ℝ, G 1 j p‖ := by simpa only [one_mul] using norm_sum_le _ _
      _ ≤ ∑ j : Fin 2, ∫ p : ℝ × ℝ, ‖G 1 j p‖ :=
        Finset.sum_le_sum fun j _ => norm_integral_le_integral_norm _
      _ ≤ ∑ j : Fin 2, Ctab * Ebase * ∑ k : Fin 4, B k := Finset.sum_le_sum fun j _ => hplaneEven j
      _ = _ := by simp; ring
  trace "SGR_REAL_DERIVATIVES_DONE"
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = Bstar := ⟨Bstar, rfl⟩
  have hrootlo : (1 / 4 : ℝ) ≤ Real.sqrt N := by
    have hr := Real.sq_sqrt hN0.le
    nlinarith only [hr, hNlo, Real.sqrt_nonneg N]
  have hs4 : s ≤ 4 * lam * y := by
    have he := div_le_div_of_nonneg_left (mul_nonneg hl hy0)
      (by norm_num : (0 : ℝ) < 1 / 4) hrootlo
    calc
      _ ≤ (lam * y) / (1 / 4 : ℝ) := he
      _ = _ := by ring
  have hcore : 1 ≤ b ∧ Delta⁻¹ ≤ 2 * b ^ 2 ∧ U ≤ 4 * b ^ 5 ∧ Vpoly ≤ 44 * b ^ 7 ∧
      PJ ≤ 256 * b ^ 16 ∧ R1tail ≤ 2 * Gamma * b ∧ R2tail ≤ 2 * Gamma * b := by
    rw [hbdef]
    exact sgr_scalar_core T Gamma y lam s hT hGamma hG1 hy hl hs hs4
  rcases hcore with ⟨hb, hDinv, hU, hVp, hPj, hR1, hR2⟩
  have hb0 : 0 ≤ b := (by norm_num : (0 : ℝ) ≤ 1).trans hb
  have hlb : lam ≤ b := by rw [hbdef]; dsimp [Bstar]; linarith only [hy, hl, inv_pos.mpr hT]
  let Rn : ℝ := (n : ℝ) * |mu| + (n : ℝ) * m3
  have hRn : 0 ≤ Rn := by dsimp [Rn]; positivity
  have hm3Rn : (n : ℝ) * m3 ≤ Rn := le_add_of_nonneg_left (by positivity)
  have hExp8 : 1 ≤ Real.exp (8 * lam * h) := Real.one_le_exp_iff.mpr (by nlinarith only [hL])
  have hGammaRn : Gamma ≤ 16 * Real.exp (8 * lam * h) * Rn := by
    calc
      _ ≤ 16 * Real.exp (8 * lam * h) * (n : ℝ) * m3 := hGammaN
      _ = 16 * Real.exp (8 * lam * h) * ((n : ℝ) * m3) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hm3Rn (by positivity)
  let Qodd : ℝ := Rn * Real.exp (8 * lam * h) * b ^ 128
  have hQodd : 0 ≤ Qodd := by dsimp [Qodd]; positivity
  have hcoarse := sgr_coarse_table_sums n mu m3 T Gamma h lam b Delta U Vpoly PJ R1tail R2tail
    (Real.exp (8 * lam * h)) A B hm3.le hT hGamma hh hDelta hU0 hVp0 hPJ0 hR10 hR20
    hb hl hlb hh1 hG1 hT7 hDinv hU hVp hPj hR1 hR2 hExp8 hGammaRn
    rfl rfl rfl rfl rfl rfl rfl rfl
  have hAsum : (∑ k : Fin 4, A k) ≤ (2 : ℝ) ^ 40 * Qodd := hcoarse.1
  have hBsum : (∑ k : Fin 4, B k) ≤ (2 : ℝ) ^ 40 * b ^ 128 := hcoarse.2
  trace "SGR_COARSE_SUMS_DONE"
  have hpay : Ebase * Real.exp (8 * lam * h) ≤ E512 := by
    dsimp only [Ebase, E512]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have he : Real.exp (lam * h) ≤ Real.exp (512 * lam * h) :=
      Real.exp_le_exp.mpr (by nlinarith only [hL])
    have hc : 24 * (m : ℝ) * lam ^ 3 * m3 * Real.exp (lam * h) ≤
        512 * (m : ℝ) * lam ^ 3 * m3 * Real.exp (512 * lam * h) := by
      calc
        _ ≤ 512 * (m : ℝ) * lam ^ 3 * m3 * Real.exp (lam * h) := by gcongr; norm_num
        _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)
    have hlinear : 200 * lam * h + 8 * lam * h ≤ 512 * lam * h := by nlinarith only [hL]
    linarith only [hc, hlinear]
  have hbase512 : Ebase ≤ E512 := by
    exact (le_mul_of_one_le_right (Real.exp_pos _).le hExp8).trans hpay
  have hCtabC : Ctab ≤ C := by
    dsimp [C]
    calc
      Ctab = 1 * Ctab := by ring
      _ ≤ (2 : ℝ) ^ 50 * Ctab := mul_le_mul_of_nonneg_right (by norm_num) hCtab.le
  have hC2 : 2 * Ctab ≤ C := by
    dsimp [C]
    exact mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 2 ^ 50) hCtab.le
  have hC41 : (2 : ℝ) ^ 41 * Ctab ≤ C := by
    dsimp [C]
    exact mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ^ 41 ≤ 2 ^ 50) hCtab.le
  have hfinal0 : |deriv f 0| ≤ C * Rn * b ^ 128 * E512 := by
    calc
      _ ≤ 2 * Ctab * Ebase * (∑ k : Fin 4, A k) := hderivNorm0
      _ ≤ 2 * Ctab * Ebase * ((2 : ℝ) ^ 40 * Qodd) := mul_le_mul_of_nonneg_left hAsum (by positivity)
      _ = ((2 : ℝ) ^ 41 * Ctab) * Rn * b ^ 128 * (Ebase * Real.exp (8 * lam * h)) := by
        dsimp [Qodd]
        ring
      _ ≤ C * Rn * b ^ 128 * E512 := by gcongr
  have hfinal1 : |deriv (fun r : ℝ => deriv f r) w| ≤ C * b ^ 128 * E512 := by
    calc
      _ ≤ 2 * Ctab * Ebase * (∑ k : Fin 4, B k) := hderivNorm1
      _ ≤ 2 * Ctab * Ebase * ((2 : ℝ) ^ 40 * b ^ 128) := mul_le_mul_of_nonneg_left hBsum (by positivity)
      _ = ((2 : ℝ) ^ 41 * Ctab) * b ^ 128 * Ebase := by ring
      _ ≤ C * b ^ 128 * E512 := by gcongr
  trace "SGR_FINAL_ASSEMBLY"
  refine ⟨hT, hGamma, hDelta, hGi, ?_, hreal.1, hreal.2.1, hreal.2.2.1, ?_, ?_, ?_, ?_⟩
  · intro d j k
    fin_cases d
    · simpa using (hregionOdd j k).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCtabC (Real.exp_pos _).le) (hAnonneg k))
    · simpa using (hregionEven j k).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCtabC (Real.exp_pos _).le) (hBnonneg k))
  · exact hderivNorm0.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC2 (Real.exp_pos _).le) (Finset.sum_nonneg fun k _ => hAnonneg k))
  · exact hderivNorm1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC2 (Real.exp_pos _).le) (Finset.sum_nonneg fun k _ => hBnonneg k))
  · simpa only [Rn, hbdef] using hfinal0
  · simpa only [hbdef] using hfinal1



end Shao.Probability
