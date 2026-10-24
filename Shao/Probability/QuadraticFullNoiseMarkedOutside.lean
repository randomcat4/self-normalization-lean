import Shao.Probability.QuadraticFullNoiseGlobalOddEven
import Shao.Probability.SourceKernelMarkedOutside
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Actual Region3/5 two-dimensional marked post-IBP norm integrals.
The exact two public declarations are frozen in the source contract.
No whole-u integration-by-parts identity or probability equality is asserted. -/

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory Set
open scoped Topology

private lemma jointDerivative_measurable (F : ℝ × ℝ → ℂ)
    (hF : Measurable F)
    (hd : ∀ p : ℝ × ℝ, DifferentiableAt ℝ (fun u => F (u, p.2)) p.1) :
    Measurable (fun p : ℝ × ℝ => deriv (fun u => F (u, p.2)) p.1) := by
  let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have ht : Filter.Tendsto t Filter.atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Filter.Eventually.of_forall fun n => by
      change 0 < 1 / ((n : ℝ) + 1)
      positivity
  apply measurable_of_tendsto_metrizable
    (f := fun (n : ℕ) (p : ℝ × ℝ) => (t n)⁻¹ • (F (p.1 + t n, p.2) - F p))
  · intro n
    exact ((hF.comp ((measurable_fst.add_const (t n)).prodMk measurable_snd)).sub hF).const_smul
      ((t n)⁻¹ : ℝ)
  · apply tendsto_pi_nhds.mpr
    intro p
    exact ((hd p).hasDerivAt.tendsto_slope_zero_right).comp ht

private lemma jointSecondDerivative_measurable (F : ℝ × ℝ → ℂ)
    (hF : Measurable F)
    (hd : ∀ p : ℝ × ℝ, DifferentiableAt ℝ (fun u => F (u, p.2)) p.1 ∧
      DifferentiableAt ℝ (fun u => deriv (fun z => F (z, p.2)) u) p.1) :
    Measurable (fun p : ℝ × ℝ => deriv
      (fun u => deriv (fun z => F (z, p.2)) u) p.1) :=
  jointDerivative_measurable _ (jointDerivative_measurable F hF (fun p => (hd p).1))
    (fun p => (hd p).2)

private lemma actualJointChar_continuous {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (z1 z2 : α → ℝ)
    (hz1 : Measurable z1) (hz2 : Measurable z2) :
    Continuous (fun p : ℝ × ℝ => ∫ z : α,
      Complex.exp (((p.1 * z1 z + p.2 * z2 z : ℝ) : ℂ) * Complex.I) ∂μ) := by
  apply continuous_of_dominated (bound := fun _ : α => (1 : ℝ))
  · intro p
    exact (by fun_prop : Measurable (fun z : α =>
      Complex.exp (((p.1 * z1 z + p.2 * z2 z : ℝ) : ℂ) * Complex.I))).aestronglyMeasurable
  · intro p
    filter_upwards with z
    simp [Complex.norm_exp, Complex.mul_re]
  · exact integrable_const _
  · filter_upwards with z
    fun_prop

private lemma actualQuadraticChar_continuous (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    Continuous (fun p : ℝ × ℝ => quadraticChar ρ p.1 p.2) :=
  actualJointChar_continuous ρ id (fun z => z ^ 2) measurable_id (by fun_prop)

private lemma actualFullNoiseChar_continuous (ρ : Measure ℝ)
    [IsProbabilityMeasure (quadraticFullNoiseLaw ρ)] :
    Continuous (fun p : ℝ × ℝ => quadraticFullNoiseChar ρ p.1 p.2) :=
  actualJointChar_continuous (quadraticFullNoiseLaw ρ) Prod.fst Prod.snd
    measurable_fst measurable_snd

private lemma actualOddEven_continuous (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure (quadraticFullNoiseLaw ρ)] (m : ℕ) :
    Continuous (fun p : ℝ × ℝ =>
      (quadraticChar ρ p.1 p.2 ^ m - quadraticChar ρ (-p.1) p.2 ^ m) / 2 *
        quadraticFullNoiseChar ρ p.1 p.2) ∧
    Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) *
      ((quadraticChar ρ p.1 p.2 ^ m + quadraticChar ρ (-p.1) p.2 ^ m) / 2 *
        quadraticFullNoiseChar ρ p.1 p.2)) := by
  have hp := (actualQuadraticChar_continuous ρ).pow m
  have hn : Continuous (fun p : ℝ × ℝ => quadraticChar ρ (-p.1) p.2 ^ m) :=
    hp.comp (continuous_fst.neg.prodMk continuous_snd)
  have hX := actualFullNoiseChar_continuous ρ
  exact ⟨((hp.sub hn).div_const 2).mul hX,
    (Complex.continuous_ofReal.comp continuous_fst).mul (((hp.add hn).div_const 2).mul hX)⟩

private lemma actualMarkedSine_continuous (a : ℝ → ℝ) (ha : Continuous a)
    (hac : HasCompactSupport a) (y w : ℝ) :
    Continuous (fun p : ℝ × ℝ => ∫ r : ℝ,
      ((a r * Real.sin (p.1 * (y * Real.sqrt r + w)) : ℝ) : ℂ) *
        Complex.exp (-(((p.2 * r : ℝ) : ℂ) * Complex.I))) := by
  apply continuous_of_dominated (bound := fun r => |a r|)
  · intro p
    exact ((Complex.continuous_ofReal.comp (ha.mul (by fun_prop))).mul
      (by fun_prop)).aestronglyMeasurable
  · intro p
    filter_upwards with r
    have he : ‖Complex.exp (-(((p.2 * r : ℝ) : ℂ) * Complex.I))‖ = 1 := by
      simp [Complex.norm_exp, Complex.mul_re]
    rw [norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.abs_sin_le_one (p.1 * (y * Real.sqrt r + w))) (abs_nonneg (a r))
  · simpa only [Real.norm_eq_abs] using (ha.integrable_of_hasCompactSupport hac).norm
  · filter_upwards with r
    fun_prop

private lemma movingNonnegativeIntegral (J : ℝ × ℝ → ℝ)
    (hJ : Measurable J) (hJ0 : ∀ p, 0 ≤ J p) (U : Set ℝ) (hU : MeasurableSet U)
    (a : ℝ) (G : ℝ → ℝ) (hGi : IntegrableOn G U)
    (hJi : ∀ u : ℝ, IntegrableOn (fun v => J (u, v)) {v : ℝ | |u| / a < |v|})
    (hJb : ∀ u ∈ U, (∫ v in {v : ℝ | |u| / a < |v|}, J (u, v)) ≤ G u) :
    IntegrableOn J {p : ℝ × ℝ | p.1 ∈ U ∧ |p.1| / a < |p.2|} ∧
      (∫ p in {p : ℝ × ℝ | p.1 ∈ U ∧ |p.1| / a < |p.2|}, J p) ≤ ∫ u in U, G u := by
  let R : Set (ℝ × ℝ) := {p | p.1 ∈ U ∧ |p.1| / a < |p.2|}
  let f : ℝ × ℝ → ℝ := R.indicator J
  have hV (u : ℝ) : MeasurableSet {v : ℝ | |u| / a < |v|} :=
    (isOpen_lt continuous_const continuous_abs).measurableSet
  have hR : MeasurableSet R :=
    (hU.preimage measurable_fst).inter
      (isOpen_lt (continuous_fst.abs.div_const a) continuous_snd.abs).measurableSet
  have hf : Measurable f := hJ.indicator hR
  have hf0 (p : ℝ × ℝ) : 0 ≤ f p := Set.indicator_nonneg (fun p _ => hJ0 p) p
  have hfi (u : ℝ) : Integrable (fun v => f (u, v)) := by
    by_cases hu : u ∈ U
    · have he : (fun v => f (u, v)) =
          ({v : ℝ | |u| / a < |v|}).indicator (fun v => J (u, v)) := by
        funext v
        by_cases hv : |u| / a < |v| <;> simp [f, R, Set.indicator, hu, hv]
      rw [he]
      exact (integrable_indicator_iff (hV u)).mpr (hJi u)
    · have he : (fun v => f (u, v)) = 0 := by funext v; simp [f, R, hu]
      rw [he]
      simp
  have hout (u : ℝ) : (∫ v : ℝ, ‖f (u, v)‖) ≤ U.indicator G u := by
    by_cases hu : u ∈ U
    · rw [Set.indicator_of_mem hu]
      have he : (fun v => ‖f (u, v)‖) =
          ({v : ℝ | |u| / a < |v|}).indicator (fun v => J (u, v)) := by
        funext v
        by_cases hv : |u| / a < |v| <;>
          simp [f, R, Set.indicator, hu, hv, Real.norm_eq_abs, abs_of_nonneg (hJ0 (u, v))]
      rw [he, integral_indicator (hV u)]
      exact hJb u hu
    · have he : (fun v => ‖f (u, v)‖) = 0 := by funext v; simp [f, R, hu]
      rw [Set.indicator_of_notMem hu, he]
      simp
  have hGind : Integrable (U.indicator G) := (integrable_indicator_iff hU).mpr hGi
  have houteri : Integrable (fun u => ∫ v : ℝ, ‖f (u, v)‖) :=
    hGind.mono' hf.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        have hn : 0 ≤ (∫ v : ℝ, ‖f (u, v)‖) := integral_nonneg (fun v => norm_nonneg (f (u, v)))
        change |∫ v : ℝ, ‖f (u, v)‖| ≤ U.indicator G u
        rw [abs_of_nonneg hn]
        exact hout u)
  have hfprod : Integrable f ((volume : Measure ℝ).prod volume) :=
    (integrable_prod_iff hf.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hfi, houteri⟩
  have hfvol : Integrable f (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    exact hfprod
  refine ⟨(integrable_indicator_iff hR).mp hfvol, ?_⟩
  calc
    _ = ∫ p : ℝ × ℝ, f p := (integral_indicator hR).symm
    _ = ∫ u : ℝ, ∫ v : ℝ, f (u, v) := by
      rw [Measure.volume_eq_prod, integral_prod f hfprod]
    _ ≤ ∫ u : ℝ, U.indicator G u := integral_mono hfprod.integral_prod_left hGind
      (fun u => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 _)] using hout u)
    _ = ∫ u in U, G u := integral_indicator hU

private lemma movingMarkedIntegral (F K : ℝ × ℝ → ℝ)
    (hF : Measurable F) (hK : Measurable K) (hF0 : ∀ p, 0 ≤ F p)
    (hK0 : ∀ p, 0 ≤ K p) (g : ℝ → ℝ) (hg : ∀ u v, F (u, v) ≤ g u)
    (U : Set ℝ) (hU : MeasurableSet U) (a y C : ℝ) (_hy : 0 < y) (_hC : 0 ≤ C)
    (hKi : ∀ u : ℝ, IntegrableOn (fun v => K (u, v)) {v : ℝ | |u| / a < |v|})
    (hKb : ∀ u : ℝ, (∫ v in {v : ℝ | |u| / a < |v|}, K (u, v)) ≤
      C / (1 + |u| / a) ^ 31)
    (hgi : IntegrableOn (fun u => g u / (1 + |u| / a) ^ 31) U) :
    IntegrableOn (fun p => F p * K p / y ^ 2)
      {p : ℝ × ℝ | p.1 ∈ U ∧ |p.1| / a < |p.2|} ∧
      (∫ p in {p : ℝ × ℝ | p.1 ∈ U ∧ |p.1| / a < |p.2|}, F p * K p / y ^ 2) ≤
        C / y ^ 2 * (∫ u in U, g u / (1 + |u| / a) ^ 31) := by
  let J : ℝ × ℝ → ℝ := fun p => F p * K p / y ^ 2
  have hg0 (u : ℝ) : 0 ≤ g u := (hF0 (u, 0)).trans (hg u 0)
  have hJi (u : ℝ) : IntegrableOn (fun v => J (u, v)) {v : ℝ | |u| / a < |v|} := by
    refine ((hKi u).const_mul (g u / y ^ 2)).mono'
      ((hF.mul hK).div_const (y ^ 2) |>.comp (measurable_const.prodMk measurable_id)
        |>.aestronglyMeasurable) ?_
    filter_upwards with v
    have hn : 0 ≤ J (u, v) := by dsimp [J]; exact div_nonneg (mul_nonneg (hF0 _) (hK0 _)) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    change F (u, v) * K (u, v) / y ^ 2 ≤ _
    calc
      _ ≤ g u * K (u, v) / y ^ 2 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hg u v) (hK0 _)) (sq_nonneg _)
      _ = _ := by ring
  obtain ⟨hi, hb⟩ := movingNonnegativeIntegral J ((hF.mul hK).div_const _) (fun p => by
    dsimp [J]; exact div_nonneg (mul_nonneg (hF0 _) (hK0 _)) (sq_nonneg _)) U hU a
    (fun u => C / y ^ 2 * (g u / (1 + |u| / a) ^ 31)) (hgi.const_mul _) hJi (by
      intro u hu
      calc
        _ ≤ ∫ v in {v : ℝ | |u| / a < |v|}, g u / y ^ 2 * K (u, v) :=
          integral_mono_ae (hJi u) ((hKi u).const_mul _) (Filter.Eventually.of_forall fun v => by
            dsimp [J]
            calc
              _ ≤ g u * K (u, v) / y ^ 2 := div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right (hg u v) (hK0 _)) (sq_nonneg _)
              _ = _ := by ring)
        _ = g u / y ^ 2 * (∫ v in {v : ℝ | |u| / a < |v|}, K (u, v)) := integral_const_mul _ _
        _ ≤ g u / y ^ 2 * (C / (1 + |u| / a) ^ 31) :=
          mul_le_mul_of_nonneg_left (hKb u) (div_nonneg (hg0 u) (sq_nonneg _))
        _ = _ := by ring)
  refine ⟨hi, ?_⟩
  simpa only [integral_const_mul] using hb

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


private lemma actualMarkedKernelData :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ (1 / 16 : ℝ) ∧
      ∀ aStar y w sigma : ℝ, 0 < aStar → 0 < y → y ≤ 2 →
        aStar * y ≤ delta → |w| ≤ y / 16 → |sigma| = 1 →
        let a : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r + sigma * w / y) ^ 2
        let B : ℝ × ℝ → ℂ := fun p => ∫ r : ℝ,
          ((a r * Real.sin (p.1 * (y * Real.sqrt r + sigma * w)) : ℝ) : ℂ) *
            Complex.exp (-(((p.2 * r : ℝ) : ℂ) * Complex.I))
        Measurable (fun p => ‖B p‖) ∧
          (∀ u : ℝ, IntegrableOn (fun v => ‖B (u, v)‖) {v : ℝ | |u| / aStar < |v|}) ∧
          ∀ u : ℝ, (∫ v in {v : ℝ | |u| / aStar < |v|}, ‖B (u, v)‖) ≤
            C / (1 + |u| / aStar) ^ 31 := by
  obtain ⟨C, delta, hC, hd, hd16, hkernel⟩ := sourceKernel_marked_outside_norms
  refine ⟨C, delta, hC, hd, hd16, ?_⟩
  intro aStar y w sigma ha hy hy2 hsmall hw hsigma
  have hsw : |sigma * w| ≤ y / 16 := by simpa only [abs_mul, hsigma, one_mul] using hw
  have ht : |sigma * w / y| ≤ (1 / 16 : ℝ) := by
    rw [abs_div, abs_of_pos hy]
    exact (div_le_iff₀ hy).mpr (by linarith)
  obtain ⟨M, hM, hfamily⟩ := sourceKernel_marked_amplitude_family
  have hfa := hfamily 2 (Or.inr rfl) (sigma * w / y) ht
  have hac : HasCompactSupport (fun r => sourceKernelCutoff r / (Real.sqrt r + sigma * w / y) ^ 2) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hfa.2.1
  refine ⟨(actualMarkedSine_continuous _ hfa.1.continuous hac y (sigma * w)).measurable.norm,
    fun u => (hkernel 2 (Or.inr rfl) _ ht aStar y u _ ha hy.le hy2 hsmall hsw).2.2.1, ?_⟩
  intro u
  refine (hkernel 2 (Or.inr rfl) _ ht aStar y u _ ha hy.le hy2 hsmall hsw).2.2.2.2.2.2.1.trans ?_
  exact div_le_div_of_nonneg_right
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (min_le_right (y * |u|) 1) hC.le)
    (by positivity)

theorem sourceTruncation_odd_even_fullNoise_region3_actual_marked_postIBP :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ (1 / 16 : ℝ) ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun z : ℝ => z ^ 2) ν0 →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν0) = 1 →
          (∫ z : ℝ, z ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 2 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            ∀ i : ℕ, i ≤ n → ∀ h kappa y w sigma : ℝ,
              epsilon / (1 + x) ≤ h → 0 < kappa → 0 < y → y ≤ 2 →
                |w| ≤ y / 16 → |sigma| = 1 →
                let ρ : Measure ℝ :=
                  ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
                let m : ℕ := n - i
                let T : ℝ := (m : ℝ) * (∫ z : ℝ, z ^ 2 ∂ρ)
                let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
                let b : ℝ := gamma / kappa
                b * y ≤ delta →
                let a : ℝ → ℝ := fun r =>
                  sourceKernelCutoff r / (Real.sqrt r + sigma * w / y) ^ 2
                let B : ℝ → ℝ → ℂ := fun u v =>
                  ∫ r : ℝ, ((a r * Real.sin (u * (y * Real.sqrt r + sigma * w)) : ℝ) : ℂ) *
                    Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I))
                let D : ℝ → ℝ → ℂ := fun u v =>
                  (quadraticChar ρ u v ^ m - quadraticChar ρ (-u) v ^ m) /
                    2 * quadraticFullNoiseChar ρ u v
                let E : ℝ → ℝ → ℂ := fun u v =>
                  (quadraticChar ρ u v ^ m + quadraticChar ρ (-u) v ^ m) /
                    2 * quadraticFullNoiseChar ρ u v
                let W : ℝ → ℝ → ℂ := fun u v => (u : ℂ) * E u v
                let R : Set (ℝ × ℝ) := {p | |p.1| ≤ kappa / gamma ∧ kappa * |p.1| / gamma < |p.2|}
                let Iodd : ℝ × ℝ → ℝ := fun p =>
                  ‖deriv (fun r : ℝ => deriv (fun t : ℝ => D t p.2) r) p.1‖ *
                    ‖B p.1 p.2‖ / y ^ 2
                let Ieven : ℝ × ℝ → ℝ := fun p =>
                  ‖deriv (fun r : ℝ => deriv (fun t : ℝ => W t p.2) r) p.1‖ *
                    ‖B p.1 p.2‖ / y ^ 2
                IntegrableOn Iodd R ∧ IntegrableOn Ieven R ∧
                  (∫ p in R, Iodd p) ≤ C / y ^ 2 * b * (T + h * gamma) ∧
                  (∫ p in R, Ieven p) ≤ C / y ^ 2 * (b * (Real.sqrt T + gamma) + b ^ 2 * (T + h * gamma))
 := by
  obtain ⟨Cg, hCg, hglobal⟩ := sourceTruncation_odd_even_fullNoise_global_derivatives
  obtain ⟨Ck, delta, hCk, hd, hd16, hkernel⟩ := actualMarkedKernelData
  refine ⟨4 * Ck * Cg, delta, by positivity, hd, hd16, ?_⟩
  intro ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h kappa y w sigma hh hk hy hy2 hw hsigma
  dsimp only
  intro hsmall
  let := hp0
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
  let m : ℕ := n - i
  let T : ℝ := (m : ℝ) * (∫ z : ℝ, z ^ 2 ∂ρ)
  let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
  let b : ℝ := gamma / kappa
  let N : ℝ := T + h * gamma
  let S : ℝ := Real.sqrt T + gamma
  let U : Set ℝ := {u | |u| ≤ kappa / gamma}
  let R : Set (ℝ × ℝ) := {p | p.1 ∈ U ∧ kappa * |p.1| / gamma < |p.2|}
  let a : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r + sigma * w / y) ^ 2
  let B : ℝ × ℝ → ℂ := fun p => ∫ r : ℝ,
    ((a r * Real.sin (p.1 * (y * Real.sqrt r + sigma * w)) : ℝ) : ℂ) *
      Complex.exp (-(((p.2 * r : ℝ) : ℂ) * Complex.I))
  let K : ℝ × ℝ → ℝ := fun p => ‖B p‖
  let D : ℝ → ℝ → ℂ := fun u v =>
    (quadraticChar ρ u v ^ m - quadraticChar ρ (-u) v ^ m) / 2 * quadraticFullNoiseChar ρ u v
  let W : ℝ → ℝ → ℂ := fun u v => (u : ℂ) *
    ((quadraticChar ρ u v ^ m + quadraticChar ρ (-u) v ^ m) / 2 * quadraticFullNoiseChar ρ u v)
  let Fo : ℝ × ℝ → ℝ := fun p => ‖deriv (fun r => deriv (fun t => D t p.2) r) p.1‖
  let Fe : ℝ × ℝ → ℝ := fun p => ‖deriv (fun r => deriv (fun t => W t p.2) r) p.1‖
  change IntegrableOn (fun p => Fo p * K p / y ^ 2) R ∧
    IntegrableOn (fun p => Fe p * K p / y ^ 2) R ∧
    (∫ p in R, Fo p * K p / y ^ 2) ≤ (4 * Ck * Cg) / y ^ 2 * b * N ∧
    (∫ p in R, Fe p * K p / y ^ 2) ≤ (4 * Ck * Cg) / y ^ 2 * (b * S + b ^ 2 * N)
  have hg : 0 < gamma := (Shao.sourceTruncation_gamma_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget).2.1
  have hb : 0 < b := div_pos hg hk
  have hhpos : 0 < h := (div_pos he (by linarith : 0 < 1 + x)).trans_le hh
  have hT : 0 ≤ T := mul_nonneg (Nat.cast_nonneg m) (integral_nonneg fun z => sq_nonneg z)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  obtain ⟨_, _, hp, hs, _, h2r, h3r, _⟩ := Shao.sourceTruncation_law_data ν0 n h2 hnorm x epsilon hx he hehalf hbudget
  have : IsProbabilityMeasure ρ := hp
  have hV : 0 < variance (id : ℝ → ℝ) ρ :=
    (Shao.sourceTruncation_variance_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget).2.2.2.2.2.1
  have hsupport : ∀ᵐ z : ℝ ∂ρ, |z| ≤ h := hs.mono fun _ hz => hz.trans hh
  have : IsProbabilityMeasure (quadraticFullNoiseLaw ρ) :=
    (quadraticFullNoise_law_data ρ h3r hV h hhpos hsupport).2.2.1
  have hdata := hglobal ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h hh
  have hcont := actualOddEven_continuous ρ m
  have hFo : Measurable Fo := (jointSecondDerivative_measurable _ hcont.1.measurable
    (fun p => ⟨(hdata p.1 p.2).1, (hdata p.1 p.2).2.1⟩)).norm
  have hFe : Measurable Fe := (jointSecondDerivative_measurable _ hcont.2.measurable
    (fun p => ⟨(hdata p.1 p.2).2.2.1, (hdata p.1 p.2).2.2.2.1⟩)).norm
  have ho (u v : ℝ) : Fo (u, v) ≤ Cg * N := (hdata u v).2.2.2.2.1
  have heven (u v : ℝ) : Fe (u, v) ≤ Cg * S + Cg * N * |u| := by
    refine (hdata u v).2.2.2.2.2.trans_eq ?_
    dsimp [S, N]
    ring
  have hU : MeasurableSet U := (isClosed_le continuous_abs continuous_const).measurableSet
  obtain ⟨hK, hKi, hKb⟩ := hkernel b y w sigma hb hy hy2 hsmall hw hsigma
  obtain ⟨hgo, hgob⟩ := profile_compare (fun _ => Cg * N) U b (Cg * N) 0 hb
    (by positivity) (by norm_num) hU measurable_const (fun _ => by positivity) (by intro u hu; simp)
  obtain ⟨hge, hgeb⟩ := profile_compare (fun u => Cg * S + Cg * N * |u|) U b (Cg * S) (Cg * N) hb
    (by positivity) (by positivity) hU (by fun_prop) (fun _ => by positivity) (by intro u hu; rfl)
  obtain ⟨hio, hiob⟩ := movingMarkedIntegral Fo K hFo hK (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) _ ho U hU b y Ck hy hCk.le hKi hKb hgo
  obtain ⟨hie, hieb⟩ := movingMarkedIntegral Fe K hFe hK (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) _ heven U hU b y Ck hy hCk.le hKi hKb hge
  have hReq : {p : ℝ × ℝ | p.1 ∈ U ∧ |p.1| / b < |p.2|} = R := by
    ext p
    have heq : |p.1| / b = kappa * |p.1| / gamma := by
      dsimp only [b]
      rw [div_div_eq_mul_div]
      ring
    simp only [R, heq, mem_ofPred_eq]
  rw [hReq] at hio hiob hie hieb
  refine ⟨hio, hie, hiob.trans ?_, hieb.trans ?_⟩
  · calc
      _ ≤ Ck / y ^ 2 * (4 * (Cg * N * b + 0 * b ^ 2)) :=
        mul_le_mul_of_nonneg_left hgob (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ Ck / y ^ 2 * (4 * (Cg * S * b + Cg * N * b ^ 2)) :=
        mul_le_mul_of_nonneg_left hgeb (by positivity)
      _ = _ := by ring

theorem sourceTruncation_odd_even_fullNoise_region5_actual_marked_postIBP :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ (1 / 16 : ℝ) ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun z : ℝ => z ^ 2) ν0 →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν0) = 1 →
          (∫ z : ℝ, z ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 2 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            ∀ i : ℕ, i ≤ n → ∀ h kappa y w sigma : ℝ,
              epsilon / (1 + x) ≤ h → 0 < kappa → 0 < y → y ≤ 2 →
                |w| ≤ y / 16 → |sigma| = 1 →
                let ρ : Measure ℝ :=
                  ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
                let m : ℕ := n - i
                let T : ℝ := (m : ℝ) * (∫ z : ℝ, z ^ 2 ∂ρ)
                let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
                let b : ℝ := gamma / kappa
                (4 * h) * y ≤ delta →
                let a : ℝ → ℝ := fun r =>
                  sourceKernelCutoff r / (Real.sqrt r + sigma * w / y) ^ 2
                let B : ℝ → ℝ → ℂ := fun u v =>
                  ∫ r : ℝ, ((a r * Real.sin (u * (y * Real.sqrt r + sigma * w)) : ℝ) : ℂ) *
                    Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I))
                let D : ℝ → ℝ → ℂ := fun u v =>
                  (quadraticChar ρ u v ^ m - quadraticChar ρ (-u) v ^ m) /
                    2 * quadraticFullNoiseChar ρ u v
                let E : ℝ → ℝ → ℂ := fun u v =>
                  (quadraticChar ρ u v ^ m + quadraticChar ρ (-u) v ^ m) /
                    2 * quadraticFullNoiseChar ρ u v
                let W : ℝ → ℝ → ℂ := fun u v => (u : ℂ) * E u v
                let R : Set (ℝ × ℝ) := {p | kappa / gamma < |p.1| ∧ |p.1| / (4 * h) < |p.2|}
                let Iodd : ℝ × ℝ → ℝ := fun p =>
                  ‖deriv (fun r : ℝ => deriv (fun t : ℝ => D t p.2) r) p.1‖ *
                    ‖B p.1 p.2‖ / y ^ 2
                let Ieven : ℝ × ℝ → ℝ := fun p =>
                  ‖deriv (fun r : ℝ => deriv (fun t : ℝ => W t p.2) r) p.1‖ *
                    ‖B p.1 p.2‖ / y ^ 2
                IntegrableOn Iodd R ∧ IntegrableOn Ieven R ∧
                  (∫ p in R, Iodd p) ≤ C / y ^ 2 * (4 * h) ^ 31 * b ^ 30 * (T + h * gamma) ∧
                  (∫ p in R, Ieven p) ≤ C / y ^ 2 * (4 * h) ^ 31 * (b ^ 30 * (Real.sqrt T + gamma) + b ^ 29 * (T + h * gamma)) := by
  obtain ⟨Cg, hCg, hglobal⟩ := sourceTruncation_odd_even_fullNoise_global_derivatives
  obtain ⟨Ck, delta, hCk, hd, hd16, hkernel⟩ := actualMarkedKernelData
  refine ⟨Ck * Cg, delta, by positivity, hd, hd16, ?_⟩
  intro ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h kappa y w sigma hh hk hy hy2 hw hsigma
  dsimp only
  intro hsmall
  let := hp0
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
  let m : ℕ := n - i
  let T : ℝ := (m : ℝ) * (∫ z : ℝ, z ^ 2 ∂ρ)
  let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
  let b : ℝ := gamma / kappa
  let N : ℝ := T + h * gamma
  let S : ℝ := Real.sqrt T + gamma
  let U : Set ℝ := {u | kappa / gamma < |u|}
  let R : Set (ℝ × ℝ) := {p | p.1 ∈ U ∧ |p.1| / (4 * h) < |p.2|}
  let a : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r + sigma * w / y) ^ 2
  let B : ℝ × ℝ → ℂ := fun p => ∫ r : ℝ,
    ((a r * Real.sin (p.1 * (y * Real.sqrt r + sigma * w)) : ℝ) : ℂ) *
      Complex.exp (-(((p.2 * r : ℝ) : ℂ) * Complex.I))
  let K : ℝ × ℝ → ℝ := fun p => ‖B p‖
  let D : ℝ → ℝ → ℂ := fun u v =>
    (quadraticChar ρ u v ^ m - quadraticChar ρ (-u) v ^ m) / 2 * quadraticFullNoiseChar ρ u v
  let W : ℝ → ℝ → ℂ := fun u v => (u : ℂ) *
    ((quadraticChar ρ u v ^ m + quadraticChar ρ (-u) v ^ m) / 2 * quadraticFullNoiseChar ρ u v)
  let Fo : ℝ × ℝ → ℝ := fun p => ‖deriv (fun r => deriv (fun t => D t p.2) r) p.1‖
  let Fe : ℝ × ℝ → ℝ := fun p => ‖deriv (fun r => deriv (fun t => W t p.2) r) p.1‖
  change IntegrableOn (fun p => Fo p * K p / y ^ 2) R ∧
    IntegrableOn (fun p => Fe p * K p / y ^ 2) R ∧
    (∫ p in R, Fo p * K p / y ^ 2) ≤ (Ck * Cg) / y ^ 2 * (4 * h) ^ 31 * b ^ 30 * N ∧
    (∫ p in R, Fe p * K p / y ^ 2) ≤ (Ck * Cg) / y ^ 2 * (4 * h) ^ 31 * (b ^ 30 * S + b ^ 29 * N)
  have hg : 0 < gamma := (Shao.sourceTruncation_gamma_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget).2.1
  have hb : 0 < b := div_pos hg hk
  have hhpos : 0 < h := (div_pos he (by linarith : 0 < 1 + x)).trans_le hh
  have hT : 0 ≤ T := mul_nonneg (Nat.cast_nonneg m) (integral_nonneg fun z => sq_nonneg z)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  obtain ⟨_, _, hp, hs, _, h2r, h3r, _⟩ := Shao.sourceTruncation_law_data ν0 n h2 hnorm x epsilon hx he hehalf hbudget
  have : IsProbabilityMeasure ρ := hp
  have hV : 0 < variance (id : ℝ → ℝ) ρ :=
    (Shao.sourceTruncation_variance_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget).2.2.2.2.2.1
  have hsupport : ∀ᵐ z : ℝ ∂ρ, |z| ≤ h := hs.mono fun _ hz => hz.trans hh
  have : IsProbabilityMeasure (quadraticFullNoiseLaw ρ) :=
    (quadraticFullNoise_law_data ρ h3r hV h hhpos hsupport).2.2.1
  have hdata := hglobal ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h hh
  have hcont := actualOddEven_continuous ρ m
  have hFo : Measurable Fo := (jointSecondDerivative_measurable _ hcont.1.measurable
    (fun p => ⟨(hdata p.1 p.2).1, (hdata p.1 p.2).2.1⟩)).norm
  have hFe : Measurable Fe := (jointSecondDerivative_measurable _ hcont.2.measurable
    (fun p => ⟨(hdata p.1 p.2).2.2.1, (hdata p.1 p.2).2.2.2.1⟩)).norm
  have ho (u v : ℝ) : Fo (u, v) ≤ Cg * N := (hdata u v).2.2.2.2.1
  have heven (u v : ℝ) : Fe (u, v) ≤ Cg * S + Cg * N * |u| := by
    refine (hdata u v).2.2.2.2.2.trans_eq ?_
    dsimp [S, N]
    ring
  have hU : MeasurableSet U := (isOpen_lt continuous_const continuous_abs).measurableSet
  obtain ⟨hK, hKi, hKb⟩ := hkernel (4 * h) y w sigma (by positivity) hy hy2 hsmall hw hsigma
  have ha : 0 < kappa / gamma := div_pos hk hg
  have hsub : U ⊆ {u : ℝ | kappa / gamma ≤ |u|} := by
    intro u hu
    change kappa / gamma < |u| at hu
    exact le_of_lt hu
  obtain ⟨hgo, hgob⟩ := tail_profile_compare (fun _ => Cg * N) U (kappa / gamma) (4 * h) (Cg * N) 0 ha
    (by positivity) (by positivity) (by norm_num) hU hsub measurable_const
    (fun _ => by positivity) (by intro u hu; simp)
  obtain ⟨hge, hgeb⟩ := tail_profile_compare (fun u => Cg * S + Cg * N * |u|) U
    (kappa / gamma) (4 * h) (Cg * S) (Cg * N) ha (by positivity)
    (by positivity) (by positivity) hU hsub (by fun_prop) (fun _ => by positivity) (by intro u hu; rfl)
  have hbinv : (kappa / gamma)⁻¹ = b := by simp [b, inv_div]
  rw [hbinv] at hgob hgeb
  obtain ⟨hio, hiob⟩ := movingMarkedIntegral Fo K hFo hK (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) _ ho U hU (4 * h) y Ck hy hCk.le hKi hKb hgo
  obtain ⟨hie, hieb⟩ := movingMarkedIntegral Fe K hFe hK (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) _ heven U hU (4 * h) y Ck hy hCk.le hKi hKb hge
  refine ⟨hio, hie, hiob.trans ?_, hieb.trans ?_⟩
  · calc
      _ ≤ Ck / y ^ 2 * ((4 * h) ^ 31 * (Cg * N * b ^ 30 + 0 * b ^ 29)) :=
        mul_le_mul_of_nonneg_left hgob (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ Ck / y ^ 2 * ((4 * h) ^ 31 * (Cg * S * b ^ 30 + Cg * N * b ^ 29)) :=
        mul_le_mul_of_nonneg_left hgeb (by positivity)
      _ = _ := by ring

/- BEGIN FIXED CUTOFF PUBLIC COMPANIONS.
Additive export of the fixed one-sixteenth cutoff from the existing proof.
The original source is recovered exactly by deleting this marked block.
-/

private lemma fixedCutoff_actualMarkedKernelData :
    ∃ C : ℝ, 0 < C ∧
      ∀ aStar y w sigma : ℝ, 0 < aStar → 0 < y → y ≤ 2 →
        aStar * y ≤ (1 / 16 : ℝ) → |w| ≤ y / 16 → |sigma| = 1 →
        let a : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r + sigma * w / y) ^ 2
        let B : ℝ × ℝ → ℂ := fun p => ∫ r : ℝ,
          ((a r * Real.sin (p.1 * (y * Real.sqrt r + sigma * w)) : ℝ) : ℂ) *
            Complex.exp (-(((p.2 * r : ℝ) : ℂ) * Complex.I))
        Measurable (fun p => ‖B p‖) ∧
          (∀ u : ℝ, IntegrableOn (fun v => ‖B (u, v)‖) {v : ℝ | |u| / aStar < |v|}) ∧
          ∀ u : ℝ, (∫ v in {v : ℝ | |u| / aStar < |v|}, ‖B (u, v)‖) ≤
            C / (1 + |u| / aStar) ^ 31 := by
  obtain ⟨C, hC, hkernel⟩ := sourceKernel_marked_outside_norms_fixed_sixteenth
  refine ⟨C, hC, ?_⟩
  intro aStar y w sigma ha hy hy2 hsmall hw hsigma
  have hsw : |sigma * w| ≤ y / 16 := by simpa only [abs_mul, hsigma, one_mul] using hw
  have ht : |sigma * w / y| ≤ (1 / 16 : ℝ) := by
    rw [abs_div, abs_of_pos hy]
    exact (div_le_iff₀ hy).mpr (by linarith)
  obtain ⟨M, hM, hfamily⟩ := sourceKernel_marked_amplitude_family
  have hfa := hfamily 2 (Or.inr rfl) (sigma * w / y) ht
  have hac : HasCompactSupport (fun r => sourceKernelCutoff r / (Real.sqrt r + sigma * w / y) ^ 2) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hfa.2.1
  refine ⟨(actualMarkedSine_continuous _ hfa.1.continuous hac y (sigma * w)).measurable.norm,
    fun u => (hkernel 2 (Or.inr rfl) _ ht aStar y u _ ha hy.le hy2 hsmall hsw).2.2.1, ?_⟩
  intro u
  refine (hkernel 2 (Or.inr rfl) _ ht aStar y u _ ha hy.le hy2 hsmall hsw).2.2.2.2.2.2.1.trans ?_
  exact div_le_div_of_nonneg_right
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (min_le_right (y * |u|) 1) hC.le)
    (by positivity)

theorem sourceTruncation_odd_even_fullNoise_region3_actual_marked_postIBP_fixed_sixteenth :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun z : ℝ => z ^ 2) ν0 →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν0) = 1 →
          (∫ z : ℝ, z ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 2 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            ∀ i : ℕ, i ≤ n → ∀ h kappa y w sigma : ℝ,
              epsilon / (1 + x) ≤ h → 0 < kappa → 0 < y → y ≤ 2 →
                |w| ≤ y / 16 → |sigma| = 1 →
                let ρ : Measure ℝ :=
                  ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
                let m : ℕ := n - i
                let T : ℝ := (m : ℝ) * (∫ z : ℝ, z ^ 2 ∂ρ)
                let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
                let b : ℝ := gamma / kappa
                b * y ≤ (1 / 16 : ℝ) →
                let a : ℝ → ℝ := fun r =>
                  sourceKernelCutoff r / (Real.sqrt r + sigma * w / y) ^ 2
                let B : ℝ → ℝ → ℂ := fun u v =>
                  ∫ r : ℝ, ((a r * Real.sin (u * (y * Real.sqrt r + sigma * w)) : ℝ) : ℂ) *
                    Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I))
                let D : ℝ → ℝ → ℂ := fun u v =>
                  (quadraticChar ρ u v ^ m - quadraticChar ρ (-u) v ^ m) /
                    2 * quadraticFullNoiseChar ρ u v
                let E : ℝ → ℝ → ℂ := fun u v =>
                  (quadraticChar ρ u v ^ m + quadraticChar ρ (-u) v ^ m) /
                    2 * quadraticFullNoiseChar ρ u v
                let W : ℝ → ℝ → ℂ := fun u v => (u : ℂ) * E u v
                let R : Set (ℝ × ℝ) := {p | |p.1| ≤ kappa / gamma ∧ kappa * |p.1| / gamma < |p.2|}
                let Iodd : ℝ × ℝ → ℝ := fun p =>
                  ‖deriv (fun r : ℝ => deriv (fun t : ℝ => D t p.2) r) p.1‖ *
                    ‖B p.1 p.2‖ / y ^ 2
                let Ieven : ℝ × ℝ → ℝ := fun p =>
                  ‖deriv (fun r : ℝ => deriv (fun t : ℝ => W t p.2) r) p.1‖ *
                    ‖B p.1 p.2‖ / y ^ 2
                IntegrableOn Iodd R ∧ IntegrableOn Ieven R ∧
                  (∫ p in R, Iodd p) ≤ C / y ^ 2 * b * (T + h * gamma) ∧
                  (∫ p in R, Ieven p) ≤ C / y ^ 2 * (b * (Real.sqrt T + gamma) + b ^ 2 * (T + h * gamma))
 := by
  obtain ⟨Cg, hCg, hglobal⟩ := sourceTruncation_odd_even_fullNoise_global_derivatives
  obtain ⟨Ck, hCk, hkernel⟩ := fixedCutoff_actualMarkedKernelData
  refine ⟨4 * Ck * Cg, by positivity, ?_⟩
  intro ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h kappa y w sigma hh hk hy hy2 hw hsigma
  dsimp only
  intro hsmall
  let := hp0
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
  let m : ℕ := n - i
  let T : ℝ := (m : ℝ) * (∫ z : ℝ, z ^ 2 ∂ρ)
  let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
  let b : ℝ := gamma / kappa
  let N : ℝ := T + h * gamma
  let S : ℝ := Real.sqrt T + gamma
  let U : Set ℝ := {u | |u| ≤ kappa / gamma}
  let R : Set (ℝ × ℝ) := {p | p.1 ∈ U ∧ kappa * |p.1| / gamma < |p.2|}
  let a : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r + sigma * w / y) ^ 2
  let B : ℝ × ℝ → ℂ := fun p => ∫ r : ℝ,
    ((a r * Real.sin (p.1 * (y * Real.sqrt r + sigma * w)) : ℝ) : ℂ) *
      Complex.exp (-(((p.2 * r : ℝ) : ℂ) * Complex.I))
  let K : ℝ × ℝ → ℝ := fun p => ‖B p‖
  let D : ℝ → ℝ → ℂ := fun u v =>
    (quadraticChar ρ u v ^ m - quadraticChar ρ (-u) v ^ m) / 2 * quadraticFullNoiseChar ρ u v
  let W : ℝ → ℝ → ℂ := fun u v => (u : ℂ) *
    ((quadraticChar ρ u v ^ m + quadraticChar ρ (-u) v ^ m) / 2 * quadraticFullNoiseChar ρ u v)
  let Fo : ℝ × ℝ → ℝ := fun p => ‖deriv (fun r => deriv (fun t => D t p.2) r) p.1‖
  let Fe : ℝ × ℝ → ℝ := fun p => ‖deriv (fun r => deriv (fun t => W t p.2) r) p.1‖
  change IntegrableOn (fun p => Fo p * K p / y ^ 2) R ∧
    IntegrableOn (fun p => Fe p * K p / y ^ 2) R ∧
    (∫ p in R, Fo p * K p / y ^ 2) ≤ (4 * Ck * Cg) / y ^ 2 * b * N ∧
    (∫ p in R, Fe p * K p / y ^ 2) ≤ (4 * Ck * Cg) / y ^ 2 * (b * S + b ^ 2 * N)
  have hg : 0 < gamma := (Shao.sourceTruncation_gamma_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget).2.1
  have hb : 0 < b := div_pos hg hk
  have hhpos : 0 < h := (div_pos he (by linarith : 0 < 1 + x)).trans_le hh
  have hT : 0 ≤ T := mul_nonneg (Nat.cast_nonneg m) (integral_nonneg fun z => sq_nonneg z)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  obtain ⟨_, _, hp, hs, _, h2r, h3r, _⟩ := Shao.sourceTruncation_law_data ν0 n h2 hnorm x epsilon hx he hehalf hbudget
  have : IsProbabilityMeasure ρ := hp
  have hV : 0 < variance (id : ℝ → ℝ) ρ :=
    (Shao.sourceTruncation_variance_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget).2.2.2.2.2.1
  have hsupport : ∀ᵐ z : ℝ ∂ρ, |z| ≤ h := hs.mono fun _ hz => hz.trans hh
  have : IsProbabilityMeasure (quadraticFullNoiseLaw ρ) :=
    (quadraticFullNoise_law_data ρ h3r hV h hhpos hsupport).2.2.1
  have hdata := hglobal ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h hh
  have hcont := actualOddEven_continuous ρ m
  have hFo : Measurable Fo := (jointSecondDerivative_measurable _ hcont.1.measurable
    (fun p => ⟨(hdata p.1 p.2).1, (hdata p.1 p.2).2.1⟩)).norm
  have hFe : Measurable Fe := (jointSecondDerivative_measurable _ hcont.2.measurable
    (fun p => ⟨(hdata p.1 p.2).2.2.1, (hdata p.1 p.2).2.2.2.1⟩)).norm
  have ho (u v : ℝ) : Fo (u, v) ≤ Cg * N := (hdata u v).2.2.2.2.1
  have heven (u v : ℝ) : Fe (u, v) ≤ Cg * S + Cg * N * |u| := by
    refine (hdata u v).2.2.2.2.2.trans_eq ?_
    dsimp [S, N]
    ring
  have hU : MeasurableSet U := (isClosed_le continuous_abs continuous_const).measurableSet
  obtain ⟨hK, hKi, hKb⟩ := hkernel b y w sigma hb hy hy2 hsmall hw hsigma
  obtain ⟨hgo, hgob⟩ := profile_compare (fun _ => Cg * N) U b (Cg * N) 0 hb
    (by positivity) (by norm_num) hU measurable_const (fun _ => by positivity) (by intro u hu; simp)
  obtain ⟨hge, hgeb⟩ := profile_compare (fun u => Cg * S + Cg * N * |u|) U b (Cg * S) (Cg * N) hb
    (by positivity) (by positivity) hU (by fun_prop) (fun _ => by positivity) (by intro u hu; rfl)
  obtain ⟨hio, hiob⟩ := movingMarkedIntegral Fo K hFo hK (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) _ ho U hU b y Ck hy hCk.le hKi hKb hgo
  obtain ⟨hie, hieb⟩ := movingMarkedIntegral Fe K hFe hK (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) _ heven U hU b y Ck hy hCk.le hKi hKb hge
  have hReq : {p : ℝ × ℝ | p.1 ∈ U ∧ |p.1| / b < |p.2|} = R := by
    ext p
    have heq : |p.1| / b = kappa * |p.1| / gamma := by
      dsimp only [b]
      rw [div_div_eq_mul_div]
      ring
    simp only [R, heq, mem_ofPred_eq]
  rw [hReq] at hio hiob hie hieb
  refine ⟨hio, hie, hiob.trans ?_, hieb.trans ?_⟩
  · calc
      _ ≤ Ck / y ^ 2 * (4 * (Cg * N * b + 0 * b ^ 2)) :=
        mul_le_mul_of_nonneg_left hgob (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ Ck / y ^ 2 * (4 * (Cg * S * b + Cg * N * b ^ 2)) :=
        mul_le_mul_of_nonneg_left hgeb (by positivity)
      _ = _ := by ring

theorem sourceTruncation_odd_even_fullNoise_region5_actual_marked_postIBP_fixed_sixteenth :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun z : ℝ => z ^ 2) ν0 →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν0) = 1 →
          (∫ z : ℝ, z ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 2 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            ∀ i : ℕ, i ≤ n → ∀ h kappa y w sigma : ℝ,
              epsilon / (1 + x) ≤ h → 0 < kappa → 0 < y → y ≤ 2 →
                |w| ≤ y / 16 → |sigma| = 1 →
                let ρ : Measure ℝ :=
                  ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
                let m : ℕ := n - i
                let T : ℝ := (m : ℝ) * (∫ z : ℝ, z ^ 2 ∂ρ)
                let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
                let b : ℝ := gamma / kappa
                (4 * h) * y ≤ (1 / 16 : ℝ) →
                let a : ℝ → ℝ := fun r =>
                  sourceKernelCutoff r / (Real.sqrt r + sigma * w / y) ^ 2
                let B : ℝ → ℝ → ℂ := fun u v =>
                  ∫ r : ℝ, ((a r * Real.sin (u * (y * Real.sqrt r + sigma * w)) : ℝ) : ℂ) *
                    Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I))
                let D : ℝ → ℝ → ℂ := fun u v =>
                  (quadraticChar ρ u v ^ m - quadraticChar ρ (-u) v ^ m) /
                    2 * quadraticFullNoiseChar ρ u v
                let E : ℝ → ℝ → ℂ := fun u v =>
                  (quadraticChar ρ u v ^ m + quadraticChar ρ (-u) v ^ m) /
                    2 * quadraticFullNoiseChar ρ u v
                let W : ℝ → ℝ → ℂ := fun u v => (u : ℂ) * E u v
                let R : Set (ℝ × ℝ) := {p | kappa / gamma < |p.1| ∧ |p.1| / (4 * h) < |p.2|}
                let Iodd : ℝ × ℝ → ℝ := fun p =>
                  ‖deriv (fun r : ℝ => deriv (fun t : ℝ => D t p.2) r) p.1‖ *
                    ‖B p.1 p.2‖ / y ^ 2
                let Ieven : ℝ × ℝ → ℝ := fun p =>
                  ‖deriv (fun r : ℝ => deriv (fun t : ℝ => W t p.2) r) p.1‖ *
                    ‖B p.1 p.2‖ / y ^ 2
                IntegrableOn Iodd R ∧ IntegrableOn Ieven R ∧
                  (∫ p in R, Iodd p) ≤ C / y ^ 2 * (4 * h) ^ 31 * b ^ 30 * (T + h * gamma) ∧
                  (∫ p in R, Ieven p) ≤ C / y ^ 2 * (4 * h) ^ 31 * (b ^ 30 * (Real.sqrt T + gamma) + b ^ 29 * (T + h * gamma)) := by
  obtain ⟨Cg, hCg, hglobal⟩ := sourceTruncation_odd_even_fullNoise_global_derivatives
  obtain ⟨Ck, hCk, hkernel⟩ := fixedCutoff_actualMarkedKernelData
  refine ⟨Ck * Cg, by positivity, ?_⟩
  intro ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h kappa y w sigma hh hk hy hy2 hw hsigma
  dsimp only
  intro hsmall
  let := hp0
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
  let m : ℕ := n - i
  let T : ℝ := (m : ℝ) * (∫ z : ℝ, z ^ 2 ∂ρ)
  let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
  let b : ℝ := gamma / kappa
  let N : ℝ := T + h * gamma
  let S : ℝ := Real.sqrt T + gamma
  let U : Set ℝ := {u | kappa / gamma < |u|}
  let R : Set (ℝ × ℝ) := {p | p.1 ∈ U ∧ |p.1| / (4 * h) < |p.2|}
  let a : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r + sigma * w / y) ^ 2
  let B : ℝ × ℝ → ℂ := fun p => ∫ r : ℝ,
    ((a r * Real.sin (p.1 * (y * Real.sqrt r + sigma * w)) : ℝ) : ℂ) *
      Complex.exp (-(((p.2 * r : ℝ) : ℂ) * Complex.I))
  let K : ℝ × ℝ → ℝ := fun p => ‖B p‖
  let D : ℝ → ℝ → ℂ := fun u v =>
    (quadraticChar ρ u v ^ m - quadraticChar ρ (-u) v ^ m) / 2 * quadraticFullNoiseChar ρ u v
  let W : ℝ → ℝ → ℂ := fun u v => (u : ℂ) *
    ((quadraticChar ρ u v ^ m + quadraticChar ρ (-u) v ^ m) / 2 * quadraticFullNoiseChar ρ u v)
  let Fo : ℝ × ℝ → ℝ := fun p => ‖deriv (fun r => deriv (fun t => D t p.2) r) p.1‖
  let Fe : ℝ × ℝ → ℝ := fun p => ‖deriv (fun r => deriv (fun t => W t p.2) r) p.1‖
  change IntegrableOn (fun p => Fo p * K p / y ^ 2) R ∧
    IntegrableOn (fun p => Fe p * K p / y ^ 2) R ∧
    (∫ p in R, Fo p * K p / y ^ 2) ≤ (Ck * Cg) / y ^ 2 * (4 * h) ^ 31 * b ^ 30 * N ∧
    (∫ p in R, Fe p * K p / y ^ 2) ≤ (Ck * Cg) / y ^ 2 * (4 * h) ^ 31 * (b ^ 30 * S + b ^ 29 * N)
  have hg : 0 < gamma := (Shao.sourceTruncation_gamma_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget).2.1
  have hb : 0 < b := div_pos hg hk
  have hhpos : 0 < h := (div_pos he (by linarith : 0 < 1 + x)).trans_le hh
  have hT : 0 ≤ T := mul_nonneg (Nat.cast_nonneg m) (integral_nonneg fun z => sq_nonneg z)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  obtain ⟨_, _, hp, hs, _, h2r, h3r, _⟩ := Shao.sourceTruncation_law_data ν0 n h2 hnorm x epsilon hx he hehalf hbudget
  have : IsProbabilityMeasure ρ := hp
  have hV : 0 < variance (id : ℝ → ℝ) ρ :=
    (Shao.sourceTruncation_variance_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget).2.2.2.2.2.1
  have hsupport : ∀ᵐ z : ℝ ∂ρ, |z| ≤ h := hs.mono fun _ hz => hz.trans hh
  have : IsProbabilityMeasure (quadraticFullNoiseLaw ρ) :=
    (quadraticFullNoise_law_data ρ h3r hV h hhpos hsupport).2.2.1
  have hdata := hglobal ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h hh
  have hcont := actualOddEven_continuous ρ m
  have hFo : Measurable Fo := (jointSecondDerivative_measurable _ hcont.1.measurable
    (fun p => ⟨(hdata p.1 p.2).1, (hdata p.1 p.2).2.1⟩)).norm
  have hFe : Measurable Fe := (jointSecondDerivative_measurable _ hcont.2.measurable
    (fun p => ⟨(hdata p.1 p.2).2.2.1, (hdata p.1 p.2).2.2.2.1⟩)).norm
  have ho (u v : ℝ) : Fo (u, v) ≤ Cg * N := (hdata u v).2.2.2.2.1
  have heven (u v : ℝ) : Fe (u, v) ≤ Cg * S + Cg * N * |u| := by
    refine (hdata u v).2.2.2.2.2.trans_eq ?_
    dsimp [S, N]
    ring
  have hU : MeasurableSet U := (isOpen_lt continuous_const continuous_abs).measurableSet
  obtain ⟨hK, hKi, hKb⟩ := hkernel (4 * h) y w sigma (by positivity) hy hy2 hsmall hw hsigma
  have ha : 0 < kappa / gamma := div_pos hk hg
  have hsub : U ⊆ {u : ℝ | kappa / gamma ≤ |u|} := by
    intro u hu
    change kappa / gamma < |u| at hu
    exact le_of_lt hu
  obtain ⟨hgo, hgob⟩ := tail_profile_compare (fun _ => Cg * N) U (kappa / gamma) (4 * h) (Cg * N) 0 ha
    (by positivity) (by positivity) (by norm_num) hU hsub measurable_const
    (fun _ => by positivity) (by intro u hu; simp)
  obtain ⟨hge, hgeb⟩ := tail_profile_compare (fun u => Cg * S + Cg * N * |u|) U
    (kappa / gamma) (4 * h) (Cg * S) (Cg * N) ha (by positivity)
    (by positivity) (by positivity) hU hsub (by fun_prop) (fun _ => by positivity) (by intro u hu; rfl)
  have hbinv : (kappa / gamma)⁻¹ = b := by simp [b, inv_div]
  rw [hbinv] at hgob hgeb
  obtain ⟨hio, hiob⟩ := movingMarkedIntegral Fo K hFo hK (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) _ ho U hU (4 * h) y Ck hy hCk.le hKi hKb hgo
  obtain ⟨hie, hieb⟩ := movingMarkedIntegral Fe K hFe hK (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) _ heven U hU (4 * h) y Ck hy hCk.le hKi hKb hge
  refine ⟨hio, hie, hiob.trans ?_, hieb.trans ?_⟩
  · calc
      _ ≤ Ck / y ^ 2 * ((4 * h) ^ 31 * (Cg * N * b ^ 30 + 0 * b ^ 29)) :=
        mul_le_mul_of_nonneg_left hgob (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ Ck / y ^ 2 * ((4 * h) ^ 31 * (Cg * S * b ^ 30 + Cg * N * b ^ 29)) :=
        mul_le_mul_of_nonneg_left hgeb (by positivity)
      _ = _ := by ring

/- END FIXED CUTOFF PUBLIC COMPANIONS. -/

end Shao.Probability
