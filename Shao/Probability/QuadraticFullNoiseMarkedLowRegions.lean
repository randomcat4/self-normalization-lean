import Shao.Probability.QuadraticFullNoiseLowDerivatives
import Shao.Probability.SourceKernelMarkedOutside
import Shao.Probability.SourceMarkFourierNorms
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Actual two-dimensional marked post-IBP integrals in source Regions1/2.
The exact complete declarations are frozen before implementation. -/
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


private lemma nonnegativeRegionIntegral (J : ℝ × ℝ → ℝ)
    (hJ : Measurable J) (hJ0 : ∀ p, 0 ≤ J p) (R : Set (ℝ × ℝ)) (hR : MeasurableSet R)
    (G : ℝ → ℝ) (hGi : Integrable G)
    (hJi : ∀ u : ℝ, Integrable (fun v => R.indicator J (u, v)))
    (hJb : ∀ u : ℝ, (∫ v : ℝ, R.indicator J (u, v)) ≤ G u) :
    IntegrableOn J R ∧ (∫ p in R, J p) ≤ ∫ u : ℝ, G u := by
  let f : ℝ × ℝ → ℝ := R.indicator J
  have hf : Measurable f := hJ.indicator hR
  have hf0 (p : ℝ × ℝ) : 0 ≤ f p := Set.indicator_nonneg (fun p _ => hJ0 p) p
  have hout (u : ℝ) : (∫ v : ℝ, ‖f (u, v)‖) ≤ G u := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 _)] using hJb u
  have houteri : Integrable (fun u => ∫ v : ℝ, ‖f (u, v)‖) :=
    hGi.mono' hf.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        have hn : 0 ≤ (∫ v : ℝ, ‖f (u, v)‖) := integral_nonneg (fun v => norm_nonneg (f (u, v)))
        change |∫ v : ℝ, ‖f (u, v)‖| ≤ G u
        rw [abs_of_nonneg hn]
        exact hout u)
  have hfprod : Integrable f ((volume : Measure ℝ).prod volume) :=
    (integrable_prod_iff hf.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hJi, houteri⟩
  have hfvol : Integrable f (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    exact hfprod
  refine ⟨(integrable_indicator_iff hR).mp hfvol, ?_⟩
  calc
    _ = ∫ p : ℝ × ℝ, f p := (integral_indicator hR).symm
    _ = ∫ u : ℝ, ∫ v : ℝ, f (u, v) := by
      rw [Measure.volume_eq_prod, integral_prod f hfprod]
    _ ≤ ∫ u : ℝ, G u := integral_mono hfprod.integral_prod_left hGi hJb

private lemma sineMinimum_sqrt (t : ℝ) (ht : 0 ≤ t) :
    min t (1 + Real.sqrt t) ≤ 2 * Real.sqrt t := by
  by_cases ht1 : t ≤ 1
  · have hh : t ≤ Real.sqrt t := Real.le_sqrt_of_sq_le (by nlinarith)
    exact (min_le_left _ _).trans (by nlinarith [Real.sqrt_nonneg t])
  · have hh : 1 ≤ Real.sqrt t := Real.one_le_sqrt.mpr (le_of_not_ge ht1)
    exact (min_le_right _ _).trans (by linarith)

private lemma gaussianAbsMoment (s : ℝ) (hs : -1 < s) :
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

private lemma actualMarkedGlobalData :
    ∃ C : ℝ, 0 < C ∧ ∀ y w sigma : ℝ, 0 < y → |w| ≤ y / 16 → |sigma| = 1 →
      let a : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r + sigma * w / y) ^ 2
      let B : ℝ × ℝ → ℂ := fun p => ∫ r : ℝ,
        ((a r * Real.sin (p.1 * (y * Real.sqrt r + sigma * w)) : ℝ) : ℂ) *
          Complex.exp (-(((p.2 * r : ℝ) : ℂ) * Complex.I))
      Measurable (fun p => ‖B p‖) ∧ ∀ u : ℝ,
        Integrable (fun v => ‖B (u, v)‖) ∧
        Integrable (fun v => |v| * ‖B (u, v)‖) ∧
        (∫ v : ℝ, ‖B (u, v)‖) ≤ C * min (y * |u|) (1 + Real.sqrt (y * |u|)) ∧
        (∫ v : ℝ, |v| * ‖B (u, v)‖) ≤ C * (1 + y * |u|) * min (y * |u|) (1 + Real.sqrt (y * |u|)) := by
  obtain ⟨M, hM, hfamily⟩ := sourceKernel_marked_amplitude_family
  obtain ⟨C, hC, hmark⟩ := sourceMarkSine_norms (1 / 16) 4 (by norm_num) (by norm_num)
  refine ⟨C * M, by positivity, ?_⟩
  intro y w sigma hy hw hsigma
  have hsw : |sigma * w| ≤ y / 16 := by simpa only [abs_mul, hsigma, one_mul] using hw
  have ht : |sigma * w / y| ≤ (1 / 16 : ℝ) := by
    rw [abs_div, abs_of_pos hy]
    exact (div_le_iff₀ hy).mpr (by linarith)
  have hfa := hfamily 2 (Or.inr rfl) (sigma * w / y) ht
  let a : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r + sigma * w / y) ^ 2
  have hac : HasCompactSupport a := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hfa.2.1
  have haM (r : ℝ) : |a r| ≤ M ∧ |deriv a r| ≤ M ∧ |deriv (deriv a) r| ≤ M := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [iteratedDeriv_zero] using hfa.2.2 0 (by norm_num) r
    · simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hfa.2.2 1 (by norm_num) r
    · simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hfa.2.2 2 (by norm_num) r
  exact ⟨(actualMarkedSine_continuous a hfa.1.continuous hac y (sigma * w)).measurable.norm,
    fun u => hmark M hM.le a hfa.1 hfa.2.1 haM y u (sigma * w) hy.le hsw⟩

private lemma gaussianSineMoment (k : ℝ) (hk : -1 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ a y : ℝ, 0 < a → 0 ≤ y →
      let J : ℝ → ℝ := fun u => |u| ^ k * Real.exp (-(1 / 256 : ℝ) * (a * u) ^ 2) *
        min (y * |u|) (1 + Real.sqrt (y * |u|))
      Integrable J ∧ (∫ u : ℝ, J u) ≤ C * a ^ (-k - 1) * (1 + Real.sqrt y * a ^ (-(1 / 2 : ℝ))) := by
  let I (s : ℝ) : ℝ := ∫ u : ℝ, |u| ^ s * Real.exp (-(1 / 256 : ℝ) * u ^ 2)
  have hI0 (s : ℝ) : 0 ≤ I s := integral_nonneg fun u => mul_nonneg
    (Real.rpow_nonneg (abs_nonneg u) _) (Real.exp_pos _).le
  let C : ℝ := 1 + I k + I (k + 1 / 2)
  have hC : 0 < C := by dsimp [C]; linarith [hI0 k, hI0 (k + 1 / 2)]
  have hCk : I k ≤ C := by dsimp [C]; linarith [hI0 (k + 1 / 2)]
  have hCkh : I (k + 1 / 2) ≤ C := by dsimp [C]; linarith [hI0 k]
  refine ⟨C, hC, ?_⟩
  intro a y ha hy
  let J : ℝ → ℝ := fun u => |u| ^ k * Real.exp (-(1 / 256 : ℝ) * (a * u) ^ 2) *
    min (y * |u|) (1 + Real.sqrt (y * |u|))
  let H0 : ℝ → ℝ := fun u => |u| ^ k * Real.exp (-(1 / 256 : ℝ) * (a * u) ^ 2)
  let H1 : ℝ → ℝ := fun u => |u| ^ (k + 1 / 2) * Real.exp (-(1 / 256 : ℝ) * (a * u) ^ 2)
  obtain ⟨hi0, hv0⟩ := (gaussianAbsMoment k hk).2 a ha
  obtain ⟨hi1, hv1⟩ := (gaussianAbsMoment (k + 1 / 2) (by linarith)).2 a ha
  have hH : Integrable (fun u => H0 u + Real.sqrt y * H1 u) := hi0.add (hi1.const_mul _)
  have hJ0 (u : ℝ) : 0 ≤ J u := by dsimp [J]; positivity
  have hdom : ∀ᵐ u : ℝ, J u ≤ H0 u + Real.sqrt y * H1 u := by
    filter_upwards [(volume : Measure ℝ).ae_ne 0] with u hu
    have huabs : 0 < |u| := abs_pos.mpr hu
    calc
      _ ≤ |u| ^ k * Real.exp (-(1 / 256 : ℝ) * (a * u) ^ 2) *
          (1 + Real.sqrt (y * |u|)) := mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = _ := by
        dsimp [H0, H1]
        rw [Real.sqrt_mul hy, Real.rpow_add huabs, ← Real.sqrt_eq_rpow]
        ring
  have hJi : Integrable J := hH.mono'
    (by exact (show Measurable J by dsimp [J]; fun_prop).aestronglyMeasurable)
    (hdom.mono fun u hu => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hJ0 u)] using hu)
  refine ⟨hJi, (integral_mono_ae hJi hH hdom).trans ?_⟩
  have hexp : a ^ (-(k + 1 / 2) - 1) = a ^ (-k - 1) * a ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add ha]
    congr 1
    ring
  calc
    _ = a ^ (-k - 1) * I k + Real.sqrt y * (a ^ (-(k + 1 / 2) - 1) * I (k + 1 / 2)) := by
      rw [integral_add hi0 (hi1.const_mul _), integral_const_mul, hv0, hv1]
    _ = a ^ (-k - 1) * (I k + Real.sqrt y * a ^ (-(1 / 2 : ℝ)) * I (k + 1 / 2)) := by
      rw [hexp]
      ring
    _ ≤ a ^ (-k - 1) * (C + Real.sqrt y * a ^ (-(1 / 2 : ℝ)) * C) := by gcongr
    _ = _ := by ring

private lemma gaussianSineInverseMoment :
    ∃ C : ℝ, 0 < C ∧ ∀ a y : ℝ, 0 < a → 0 ≤ y →
      let J : ℝ → ℝ := fun u => |u| ^ (-1 : ℝ) * Real.exp (-(1 / 256 : ℝ) * (a * u) ^ 2) *
        min (y * |u|) (1 + Real.sqrt (y * |u|))
      Integrable J ∧ (∫ u : ℝ, J u) ≤ C * (1 + Real.sqrt y * a ^ (-(1 / 2 : ℝ))) := by
  let I : ℝ := ∫ u : ℝ, |u| ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / 256 : ℝ) * u ^ 2)
  have hI : 0 ≤ I := integral_nonneg fun u => mul_nonneg
    (Real.rpow_nonneg (abs_nonneg u) _) (Real.exp_pos _).le
  refine ⟨1 + 2 * I, by positivity, ?_⟩
  intro a y ha hy
  let J : ℝ → ℝ := fun u => |u| ^ (-1 : ℝ) * Real.exp (-(1 / 256 : ℝ) * (a * u) ^ 2) *
    min (y * |u|) (1 + Real.sqrt (y * |u|))
  let H : ℝ → ℝ := fun u => |u| ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / 256 : ℝ) * (a * u) ^ 2)
  obtain ⟨hi, hv⟩ := (gaussianAbsMoment (-(1 / 2 : ℝ)) (by norm_num)).2 a ha
  have hH : Integrable (fun u => (2 * Real.sqrt y) * H u) := hi.const_mul _
  have hJ0 (u : ℝ) : 0 ≤ J u := by dsimp [J]; positivity
  have hdom : ∀ᵐ u : ℝ, J u ≤ (2 * Real.sqrt y) * H u := by
    filter_upwards [(volume : Measure ℝ).ae_ne 0] with u hu
    have huabs : 0 < |u| := abs_pos.mpr hu
    calc
      _ ≤ |u| ^ (-1 : ℝ) * Real.exp (-(1 / 256 : ℝ) * (a * u) ^ 2) *
          (2 * Real.sqrt (y * |u|)) := mul_le_mul_of_nonneg_left
            (sineMinimum_sqrt (y * |u|) (by positivity)) (by positivity)
      _ = _ := by
        dsimp [H]
        rw [Real.sqrt_mul hy]
        simp_rw [Real.sqrt_eq_rpow]
        rw [show -(1 / 2 : ℝ) = -1 + 1 / 2 by norm_num, Real.rpow_add huabs]
        ring
  have hJi : Integrable J := hH.mono'
    (by exact (show Measurable J by dsimp [J]; fun_prop).aestronglyMeasurable)
    (hdom.mono fun u hu => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hJ0 u)] using hu)
  refine ⟨hJi, (integral_mono_ae hJi hH hdom).trans ?_⟩
  calc
    _ = 2 * Real.sqrt y * (a ^ (-(1 / 2 : ℝ)) * I) := by
      rw [integral_const_mul, hv]
      change 2 * Real.sqrt y * (a ^ (- -(1 / 2 : ℝ) - 1) * I) = _
      norm_num
    _ ≤ _ := by
      have hz : 0 ≤ Real.sqrt y * a ^ (-(1 / 2 : ℝ)) := by positivity
      nlinarith only [hI, hz]

private lemma affineMarkedFiber (F K : ℝ → ℝ) (hF : Measurable F) (hK : Measurable K)
    (hF0 : ∀ v, 0 ≤ F v) (hK0 : ∀ v, 0 ≤ K v)
    (S V : Set ℝ) (hS : MeasurableSet S) (hV : MeasurableSet V) (hSV : S ⊆ V)
    (P0 P1 y : ℝ) (hP0 : 0 ≤ P0) (hP1 : 0 ≤ P1)
    (hb : ∀ v ∈ S, F v ≤ P0 + P1 * |v|)
    (hKi : IntegrableOn K V) (hKwi : IntegrableOn (fun v => |v| * K v) V) :
    Integrable (S.indicator (fun v => F v * K v / y ^ 2)) ∧
      (∫ v : ℝ, S.indicator (fun v => F v * K v / y ^ 2) v) ≤
        (P0 * (∫ v in V, K v) + P1 * (∫ v in V, |v| * K v)) / y ^ 2 := by
  let J : ℝ → ℝ := fun v => F v * K v / y ^ 2
  let D : ℝ → ℝ := fun v => (P0 * K v + P1 * (|v| * K v)) / y ^ 2
  have hD : IntegrableOn D V := ((hKi.const_mul P0).add (hKwi.const_mul P1)).div_const _
  have hDind : Integrable (V.indicator D) := (integrable_indicator_iff hV).mpr hD
  have hD0 (v : ℝ) : 0 ≤ D v := by
    dsimp [D]
    exact div_nonneg (add_nonneg (mul_nonneg hP0 (hK0 v))
      (mul_nonneg hP1 (mul_nonneg (abs_nonneg v) (hK0 v)))) (sq_nonneg _)
  have hJ0 (v : ℝ) : 0 ≤ J v := by dsimp [J]; exact div_nonneg (mul_nonneg (hF0 v) (hK0 v)) (sq_nonneg _)
  have hdom (v : ℝ) : S.indicator J v ≤ V.indicator D v := by
    by_cases hv : v ∈ S
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem (hSV hv)]
      calc
        _ ≤ (P0 + P1 * |v|) * K v / y ^ 2 := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hb v hv) (hK0 v)) (sq_nonneg _)
        _ = _ := by dsimp [D]; ring
    · rw [Set.indicator_of_notMem hv]
      exact Set.indicator_nonneg (fun v _ => hD0 v) v
  have hi : Integrable (S.indicator J) := hDind.mono'
    (((hF.mul hK).div_const _).indicator hS).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => by
      have hn : 0 ≤ S.indicator J v := Set.indicator_nonneg (fun v _ => hJ0 v) v
      simpa only [Real.norm_eq_abs, abs_of_nonneg hn] using hdom v)
  refine ⟨hi, (integral_mono hi hDind hdom).trans_eq ?_⟩
  rw [integral_indicator hV]
  change (∫ v in V, (P0 * K v + P1 * (|v| * K v)) / y ^ 2) = _
  rw [integral_div, integral_add (hKi.const_mul _) (hKwi.const_mul _), integral_const_mul, integral_const_mul]

private lemma fixedOutsideProfile_integrable :
    Integrable (fun u : ℝ => (1 + |u|) ^ 5 / (1 + |u| / 4) ^ 30) := by
  let H : ℝ → ℝ := fun u => (1 + |u|) ^ 5 / (1 + |u| / 4) ^ 30
  have hHC : Continuous H := ((continuous_const.add continuous_abs).pow 5).div
    ((continuous_const.add (continuous_abs.div_const 4)).pow 30) (fun u => by positivity)
  have hS : MeasurableSet {u : ℝ | 1 ≤ |u|} :=
    (isClosed_le continuous_const continuous_abs).measurableSet
  obtain ⟨ht, _⟩ := abs_tail_rpow 1 (-25) (by norm_num) (by norm_num)
  have hHt : IntegrableOn H {u : ℝ | 1 ≤ |u|} := by
    refine (ht.const_mul ((32 : ℝ) * 4 ^ 30)).mono' hHC.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hS] with u hu
    have huabs : 0 < |u| := lt_of_lt_of_le (by norm_num) hu
    have hH0 : 0 ≤ H u := by dsimp [H]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hH0]
    calc
      _ ≤ (2 * |u|) ^ 5 / (|u| / 4) ^ 30 := by dsimp [H]; gcongr <;> linarith
      _ = (32 : ℝ) * 4 ^ 30 * |u| ^ (-25 : ℝ) := by
        simp only [Real.rpow_neg huabs.le, Real.rpow_ofNat]
        field_simp
        ring
  have hcover : (univ : Set ℝ) ⊆ Icc (-1) 1 ∪ {u : ℝ | 1 ≤ |u|} := by
    intro u hu
    rcases le_total |u| 1 with h | h
    · exact Or.inl (abs_le.mp h)
    · exact Or.inr h
  simpa only [integrableOn_univ] using (((hHC.integrableOn_Icc).union hHt).mono_set hcover)

private lemma actualMarkedOutsideData :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ (1 / 16 : ℝ) ∧
      ∀ aStar y w sigma : ℝ, 0 < aStar → aStar ≤ 4 → 0 < y → y ≤ 2 →
        aStar * y ≤ delta → |w| ≤ y / 16 → |sigma| = 1 →
        let a : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r + sigma * w / y) ^ 2
        let B : ℝ × ℝ → ℂ := fun p => ∫ r : ℝ,
          ((a r * Real.sin (p.1 * (y * Real.sqrt r + sigma * w)) : ℝ) : ℂ) *
            Complex.exp (-(((p.2 * r : ℝ) : ℂ) * Complex.I))
        ∀ u : ℝ, IntegrableOn (fun v => ‖B (u, v)‖) {v : ℝ | |u| / aStar < |v|} ∧
          IntegrableOn (fun v => |v| * ‖B (u, v)‖) {v : ℝ | |u| / aStar < |v|} ∧
          (∫ v in {v : ℝ | |u| / aStar < |v|}, ‖B (u, v)‖) ≤ C / (1 + |u| / 4) ^ 30 ∧
          (∫ v in {v : ℝ | |u| / aStar < |v|}, |v| * ‖B (u, v)‖) ≤ C / (1 + |u| / 4) ^ 30 := by
  obtain ⟨C, delta, hC, hd, hd16, hkernel⟩ := sourceKernel_marked_outside_norms
  refine ⟨C, delta, hC, hd, hd16, ?_⟩
  intro aStar y w sigma ha ha4 hy hy2 hsmall hw hsigma
  have hsw : |sigma * w| ≤ y / 16 := by simpa only [abs_mul, hsigma, one_mul] using hw
  have ht : |sigma * w / y| ≤ (1 / 16 : ℝ) := by
    rw [abs_div, abs_of_pos hy]
    exact (div_le_iff₀ hy).mpr (by linarith)
  dsimp only
  intro u
  have hd0 : (1 : ℝ) ≤ 1 + |u| / aStar := by linarith [div_nonneg (abs_nonneg u) ha.le]
  have hbase : 1 + |u| / 4 ≤ 1 + |u| / aStar :=
    add_le_add le_rfl (div_le_div_of_nonneg_left (abs_nonneg u) ha ha4)
  have h30 : (1 + |u| / 4) ^ 30 ≤ (1 + |u| / aStar) ^ 30 :=
    pow_le_pow_left₀ (by positivity) hbase 30
  have h31 : (1 + |u| / 4) ^ 30 ≤ (1 + |u| / aStar) ^ 31 := h30.trans (by
    rw [pow_succ]
    have hp := mul_nonneg (pow_nonneg (by positivity : 0 ≤ 1 + |u| / aStar) 30) (sub_nonneg.mpr hd0)
    nlinarith only [hp])
  have h := hkernel 2 (Or.inr rfl) _ ht aStar y u _ ha hy.le hy2 hsmall hsw
  refine ⟨h.2.2.1, h.2.2.2.1, ?_, ?_⟩
  · refine h.2.2.2.2.2.2.1.trans ((div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (min_le_right (y * |u|) 1) hC.le) (by positivity)).trans ?_)
    simpa only [mul_one] using div_le_div_of_nonneg_left hC.le (by positivity) h31
  · refine h.2.2.2.2.2.2.2.trans ((div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (min_le_right (y * |u|) 1) hC.le) (by positivity)).trans ?_)
    simpa only [mul_one] using div_le_div_of_nonneg_left hC.le (by positivity) h30

private lemma coarseOddEnvelope (N0 N1 T gamma h t z : ℝ)
    (hN0 : 0 ≤ N0) (hN1 : 0 ≤ N1) (hT : 0 ≤ T) (hT2 : T ≤ 2)
    (hgamma : 0 ≤ gamma) (hgamma2 : gamma ≤ 2) (_hh : 0 ≤ h) (hh1 : h ≤ 1)
    (ht : 0 ≤ t) (hz : 0 ≤ z) :
    let Q : ℝ := Real.sqrt T * (1 + Real.sqrt T * t)
    let A : ℝ := N0 * t + N1 * (t ^ 3 + t * z)
    let B : ℝ := N0 + N1 * (t ^ 2 + z)
    N1 * t + (Q + gamma) * B +
      (T * (1 + T * t ^ 2) + gamma * Q + h * gamma) * A ≤
        1000 * (N0 + N1) * (1 + t) ^ 5 * (1 + z) := by
  let N : ℝ := N0 + N1
  let r : ℝ := 1 + t
  let Q : ℝ := Real.sqrt T * (1 + Real.sqrt T * t)
  let A : ℝ := N0 * t + N1 * (t ^ 3 + t * z)
  let B : ℝ := N0 + N1 * (t ^ 2 + z)
  have hN : 0 ≤ N := add_nonneg hN0 hN1
  have hr : 1 ≤ r := by dsimp [r]; linarith
  have hr0 : 0 ≤ r := by linarith
  have hN0N : N0 ≤ N := by dsimp [N]; linarith
  have hN1N : N1 ≤ N := by dsimp [N]; linarith
  have hroot : Real.sqrt T ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hQ : Q ≤ 4 * r := by
    calc
      _ ≤ 2 * (1 + 2 * t) := by dsimp [Q]; gcongr
      _ ≤ _ := by dsimp [r]; linarith
  have hQg : Q + gamma ≤ 6 * r := by dsimp [r] at *; linarith
  have hH : T * (1 + T * t ^ 2) + gamma * Q + h * gamma ≤ 14 * r ^ 2 := by
    have h1 : T * (1 + T * t ^ 2) ≤ 2 * (1 + 2 * t ^ 2) := by gcongr
    have h2 : gamma * Q ≤ 2 * (4 * r) := mul_le_mul hgamma2 hQ hQ0 (by norm_num)
    have h3 : h * gamma ≤ 2 := (mul_le_mul hh1 hgamma2 hgamma (by norm_num)).trans_eq (by norm_num)
    dsimp [r] at *
    nlinarith only [h1, h2, h3, ht, sq_nonneg t]
  have hAr : A ≤ 2 * N * r ^ 3 * (1 + z) := by
    calc
      _ ≤ N * t + N * (t ^ 3 + t * z) := by dsimp [A]; gcongr
      _ = N * (t + t ^ 3 + t * z) := by ring
      _ ≤ N * (2 * r ^ 3 * (1 + z)) := by
        apply mul_le_mul_of_nonneg_left _ hN
        apply sub_nonneg.mp
        dsimp [r]
        ring_nf
        positivity
      _ = _ := by ring
  have hBr : B ≤ 2 * N * r ^ 2 * (1 + z) := by
    calc
      _ ≤ N + N * (t ^ 2 + z) := by dsimp [B]; gcongr
      _ = N * (1 + t ^ 2 + z) := by ring
      _ ≤ N * (2 * r ^ 2 * (1 + z)) := by
        apply mul_le_mul_of_nonneg_left _ hN
        apply sub_nonneg.mp
        dsimp [r]
        ring_nf
        positivity
      _ = _ := by ring
  have hMr : N1 * t ≤ N * r ^ 5 * (1 + z) := by
    calc
      _ ≤ N * t := mul_le_mul_of_nonneg_right hN1N ht
      _ ≤ N * (r ^ 5 * (1 + z)) := by
        apply mul_le_mul_of_nonneg_left _ hN
        apply sub_nonneg.mp
        dsimp [r]
        ring_nf
        positivity
      _ = _ := by ring
  have hr35 : r ^ 3 ≤ r ^ 5 := by
    have hh := mul_nonneg (pow_nonneg hr0 3) (sub_nonneg.mpr (show 1 ≤ r ^ 2 from one_le_pow₀ hr))
    nlinarith only [hh]
  change N1 * t + (Q + gamma) * B + _ * A ≤ _
  calc
    _ ≤ N * r ^ 5 * (1 + z) + (6 * r) * (2 * N * r ^ 2 * (1 + z)) +
        (14 * r ^ 2) * (2 * N * r ^ 3 * (1 + z)) := by
      gcongr
    _ = 29 * N * r ^ 5 * (1 + z) + 12 * N * r ^ 3 * (1 + z) := by ring
    _ ≤ 29 * N * r ^ 5 * (1 + z) + 12 * N * r ^ 5 * (1 + z) := by gcongr
    _ ≤ _ := by dsimp [N, r]; nlinarith only [mul_nonneg (mul_nonneg hN (pow_nonneg (by positivity : 0 ≤ 1 + t) 5)) (by positivity : 0 ≤ 1 + z)]

theorem sourceTruncation_odd_even_fullNoise_region2_actual_marked_postIBP :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ (1 / 16 : ℝ) ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun z : ℝ => z ^ 2) ν0 →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν0) = 1 →
          (∫ z : ℝ, z ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 2 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            ∀ i : ℕ, i ≤ n → ∀ h kappa L2 y w sigma : ℝ,
              epsilon / (1 + x) ≤ h → h ≤ 1 → 0 < kappa → kappa ≤ (1 / 128 : ℝ) → 20 ≤ L2 →
                1 ≤ kappa * Real.sqrt L2 → 0 < y → y ≤ 2 →
                |w| ≤ y / 16 → |sigma| = 1 →
                let ρ : Measure ℝ :=
                  ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
                let m : ℕ := n - i
                let T : ℝ := (m : ℝ) * (∫ z : ℝ, z ^ 2 ∂ρ)
                let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
                let mu : ℝ := ∫ z : ℝ, z ∂ρ
                let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂ρ
                L2 * gamma ^ 2 ≤ T → T < y ^ 2 → (4 * h) * y ≤ delta →
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
                let R : Set (ℝ × ℝ) := {p | |p.1| ≤ kappa / gamma ∧ |p.2| ≤ kappa * |p.1| / gamma ∧ ¬(p.1 ≠ 0 ∧ |p.2| ≤ |p.1| / (4 * h))}
                let Iodd : ℝ × ℝ → ℝ := fun p =>
                  ‖deriv (fun r : ℝ => deriv (fun t : ℝ => D t p.2) r) p.1‖ *
                    ‖B p.1 p.2‖ / y ^ 2
                let Ieven : ℝ × ℝ → ℝ := fun p =>
                  ‖deriv (fun r : ℝ => deriv (fun t : ℝ => W t p.2) r) p.1‖ *
                    ‖B p.1 p.2‖ / y ^ 2
                IntegrableOn Iodd R ∧ IntegrableOn Ieven R ∧
                  (∫ p in R, Iodd p) ≤ C / y ^ 2 * T * ((n : ℝ) * |mu| + (n : ℝ) * m3) ∧
                  (∫ p in R, Ieven p) ≤ C / y ^ 2 * (Real.sqrt T + gamma) := by
  obtain ⟨Co, hCo, hlow⟩ := sourceTruncation_odd_even_fullNoise_lowFrequency_derivatives
  obtain ⟨Cg, hCg, hglobal⟩ := sourceTruncation_odd_even_fullNoise_global_derivatives
  obtain ⟨Ck, delta, hCk, hd, hd16, houtside⟩ := actualMarkedOutsideData
  obtain ⟨Cm, hCm, hmark⟩ := actualMarkedGlobalData
  let H : ℝ → ℝ := fun u => (1 + |u|) ^ 5 / (1 + |u| / 4) ^ 30
  let I : ℝ := ∫ u : ℝ, H u
  have hH : Integrable H := fixedOutsideProfile_integrable
  have hI : 0 ≤ I := integral_nonneg fun u => by dsimp [H]; positivity
  refine ⟨10000 * (Co + Cg) * Ck * (I + 1), delta, by positivity, hd, hd16, ?_⟩
  intro ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h kappa L2 y w sigma
    hh hh1 hk hk128 hL2 hkL2 hy hy2 hw hsigma
  dsimp only
  intro hTL hTy hsmall
  let := hp0
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
  let m : ℕ := n - i
  let mu : ℝ := ∫ z : ℝ, z ∂ρ
  let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂ρ
  let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂ρ
  let T : ℝ := (m : ℝ) * m2
  let gamma : ℝ := m3 / variance (id : ℝ → ℝ) ρ
  let N : ℝ := (m : ℝ) * |mu| + (m : ℝ) * m3
  let S : ℝ := Real.sqrt T + gamma
  let R : Set (ℝ × ℝ) := {p | |p.1| ≤ kappa / gamma ∧ |p.2| ≤ kappa * |p.1| / gamma ∧
    ¬(p.1 ≠ 0 ∧ |p.2| ≤ |p.1| / (4 * h))}
  let R' : Set (ℝ × ℝ) := {p | |p.1| ≤ kappa / gamma ∧ |p.2| ≤ kappa * |p.1| / gamma ∧
    |p.1| / (4 * h) < |p.2|}
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
  let Po : ℝ → ℝ := fun u => 1000 * Co * N * (1 + |u|) ^ 5
  let Pe : ℝ → ℝ := fun u => 2 * Cg * S * (1 + |u|) ^ 5
  obtain ⟨_, _, hp, hs, _, h2r, h3r, _⟩ := Shao.sourceTruncation_law_data ν0 n h2 hnorm x epsilon hx he hehalf hbudget
  have : IsProbabilityMeasure ρ := hp
  obtain ⟨hscalelo, hscalehi, _, _, _, hV, _, _⟩ :=
    Shao.sourceTruncation_variance_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget
  obtain ⟨hm3p, hgammap, _, _, hgamcut, _, _, _, _⟩ :=
    Shao.sourceTruncation_gamma_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget
  have hhpos : 0 < h := (div_pos he (by linarith : 0 < 1 + x)).trans_le hh
  have hsupport : ∀ᵐ z : ℝ ∂ρ, |z| ≤ h := hs.mono fun _ hz => hz.trans hh
  have hgam : gamma ≤ 2 * h := hgamcut.trans (by linarith)
  have hgam2 : gamma ≤ 2 := hgam.trans (by linarith)
  have hT : 0 ≤ T := mul_nonneg (Nat.cast_nonneg m) (integral_nonneg fun z => sq_nonneg z)
  have hTbound : T ≤ (4 / 3 : ℝ) := (mul_le_mul_of_nonneg_right
    (show (m : ℝ) ≤ n from Nat.cast_le.mpr (Nat.sub_le _ _)) (integral_nonneg fun z => sq_nonneg z)).trans hscalehi
  have hT2 : T ≤ 2 := by linarith
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have : IsProbabilityMeasure (quadraticFullNoiseLaw ρ) :=
    (quadraticFullNoise_law_data ρ h3r hV h hhpos hsupport).2.2.1
  have hdata := hglobal ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h hh
  have hcont := actualOddEven_continuous ρ m
  have hFo : Measurable Fo := (jointSecondDerivative_measurable _ hcont.1.measurable
    (fun p => ⟨(hdata p.1 p.2).1, (hdata p.1 p.2).2.1⟩)).norm
  have hFe : Measurable Fe := (jointSecondDerivative_measurable _ hcont.2.measurable
    (fun p => ⟨(hdata p.1 p.2).2.2.1, (hdata p.1 p.2).2.2.2.1⟩)).norm
  have hR' : MeasurableSet R' :=
    (isClosed_le continuous_fst.abs continuous_const).measurableSet.inter
      ((isClosed_le continuous_snd.abs ((continuous_const.mul continuous_fst.abs).div_const _)).measurableSet.inter
        (isOpen_lt (continuous_fst.abs.div_const _) continuous_snd.abs).measurableSet)
  have hRae : R =ᵐ[(volume : Measure (ℝ × ℝ))] R' := by
    filter_upwards [(volume : Measure (ℝ × ℝ)).ae_ne (0, 0)] with p hp0
    apply propext
    constructor
    · rintro ⟨hu, hv, hc⟩
      refine ⟨hu, hv, ?_⟩
      have hu0 : p.1 ≠ 0 := by
        intro heq
        have hv0 : p.2 = 0 := abs_eq_zero.mp (le_antisymm (by simpa only [heq, abs_zero, mul_zero, zero_div] using hv) (abs_nonneg _))
        exact hp0 (Prod.ext heq hv0)
      exact lt_of_not_ge (fun hvle => hc ⟨hu0, hvle⟩)
    · rintro ⟨hu, hv, hc⟩
      exact ⟨hu, hv, fun h => not_lt_of_ge h.2 hc⟩
  have hrestrict : (volume : Measure (ℝ × ℝ)).restrict R = volume.restrict R' := Measure.restrict_congr_set hRae
  have ho (u v : ℝ) (hp : (u, v) ∈ R') : Fo (u, v) ≤ Po u + Po u * |v| := by
    have hl := (hlow ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h kappa L2
      hh hk hk128 hL2 hkL2 hTL u v hp.1 hp.2.1).1
    have he := coarseOddEnvelope ((m : ℝ) * |mu|) ((m : ℝ) * m3) T gamma h |u| |v|
      (by positivity) (by positivity) hT hT2 hgammap.le hgam2 hhpos.le hh1 (abs_nonneg _) (abs_nonneg _)
    have hG1 : Real.exp (-T * u ^ 2 / 256) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_nonneg hT (sq_nonneg u)]
    have henv0 : 0 ≤ (m : ℝ) * m3 * |u| +
        (Real.sqrt T * (1 + Real.sqrt T * |u|) + gamma) *
          ((m : ℝ) * |mu| + (m : ℝ) * m3 * (u ^ 2 + |v|)) +
        (T * (1 + T * u ^ 2) + gamma * (Real.sqrt T * (1 + Real.sqrt T * |u|)) + h * gamma) *
          ((m : ℝ) * |mu| * |u| + (m : ℝ) * m3 * (|u| ^ 3 + |u| * |v|)) := by positivity
    refine hl.trans ?_
    calc
      _ ≤ Co * 1 * _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG1 hCo.le) henv0
      _ ≤ Co * (1000 * N * (1 + |u|) ^ 5 * (1 + |v|)) := by
        simp only [mul_one]
        apply mul_le_mul_of_nonneg_left _ hCo.le
        simpa only [sq_abs] using he
      _ = _ := by dsimp [Po]; ring
  have heven (u v : ℝ) : Fe (u, v) ≤ Pe u := by
    have hroot : Real.sqrt T ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
    have hTp : T ≤ 2 * Real.sqrt T := by nlinarith only [Real.sq_sqrt hT, Real.sqrt_nonneg T, hroot]
    have hN2 : T + h * gamma ≤ 2 * S := by
      have hp := mul_le_mul_of_nonneg_right hh1 hgammap.le
      dsimp [S]
      nlinarith only [hTp, hp, hgammap]
    have hr5 : 1 + |u| ≤ (1 + |u|) ^ 5 := by
      have hr : 1 ≤ 1 + |u| := by linarith [abs_nonneg u]
      have hp := mul_nonneg (by positivity : 0 ≤ 1 + |u|)
        (sub_nonneg.mpr (show 1 ≤ (1 + |u|) ^ 4 from one_le_pow₀ hr))
      nlinarith only [hp]
    calc
      _ ≤ Cg * (S + |u| * (T + h * gamma)) := (hdata u v).2.2.2.2.2
      _ ≤ Cg * (S + |u| * (2 * S)) := by gcongr
      _ ≤ 2 * Cg * S * (1 + |u|) := by nlinarith only [mul_nonneg hCg.le hS]
      _ ≤ _ := by dsimp [Pe]; gcongr
  obtain ⟨hKm, _⟩ := hmark y w sigma hy hw hsigma
  have hki := houtside (4 * h) y w sigma (by positivity) (by linarith) hy hy2 hsmall hw hsigma
  have hPo0 (u : ℝ) : 0 ≤ Po u := by dsimp [Po]; positivity
  have hPe0 (u : ℝ) : 0 ≤ Pe u := by dsimp [Pe]; positivity
  have hfiber (F : ℝ × ℝ → ℝ) (hFm : Measurable F) (hF0 : ∀ p, 0 ≤ F p)
      (P0 P1 : ℝ → ℝ) (hP0 : ∀ u, 0 ≤ P0 u) (hP1 : ∀ u, 0 ≤ P1 u)
      (hbound : ∀ u v, (u, v) ∈ R' → F (u, v) ≤ P0 u + P1 u * |v|) (u : ℝ) :
      Integrable (fun v => R'.indicator (fun p => F p * K p / y ^ 2) (u, v)) ∧
        (∫ v : ℝ, R'.indicator (fun p => F p * K p / y ^ 2) (u, v)) ≤
          (P0 u + P1 u) * (Ck / (1 + |u| / 4) ^ 30) / y ^ 2 := by
    let V : Set ℝ := {v | |u| / (4 * h) < |v|}
    let U : Set ℝ := {v | (u, v) ∈ R'}
    have hU : MeasurableSet U := hR'.preimage (measurable_const.prodMk measurable_id)
    have hV : MeasurableSet V := (isOpen_lt continuous_const continuous_abs).measurableSet
    obtain ⟨hi, hb⟩ := affineMarkedFiber (fun v => F (u, v)) (fun v => K (u, v))
      (hFm.comp (measurable_const.prodMk measurable_id)) (hKm.comp (measurable_const.prodMk measurable_id))
      (fun v => hF0 _) (fun v => norm_nonneg _) U V hU hV (fun v hv => hv.2.2)
      (P0 u) (P1 u) y (hP0 u) (hP1 u) (fun v hv => hbound u v hv) (hki u).1 (hki u).2.1
    refine ⟨hi, hb.trans ?_⟩
    calc
      _ ≤ (P0 u * (Ck / (1 + |u| / 4) ^ 30) + P1 u * (Ck / (1 + |u| / 4) ^ 30)) / y ^ 2 :=
        div_le_div_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left (hki u).2.2.1 (hP0 u))
          (mul_le_mul_of_nonneg_left (hki u).2.2.2 (hP1 u))) (sq_nonneg _)
      _ = _ := by ring
  have hfibo := hfiber Fo hFo (fun _ => norm_nonneg _) Po Po hPo0 hPo0 ho
  have hfibe := hfiber Fe hFe (fun _ => norm_nonneg _) Pe (fun _ => 0) hPe0 (fun _ => le_rfl)
    (fun u v hp => by simpa only [zero_mul, add_zero] using heven u v)
  obtain ⟨hio, hiob⟩ := nonnegativeRegionIntegral (fun p => Fo p * K p / y ^ 2)
    ((hFo.mul hKm).div_const _) (fun p => by dsimp [Fo, K]; positivity) R' hR'
    (fun u => (2000 * Co * Ck * N / y ^ 2) * H u) (hH.const_mul _)
    (fun u => (hfibo u).1) (fun u => (hfibo u).2.trans_eq (by dsimp [Po, H]; ring))
  obtain ⟨hie, hieb⟩ := nonnegativeRegionIntegral (fun p => Fe p * K p / y ^ 2)
    ((hFe.mul hKm).div_const _) (fun p => by dsimp [Fe, K]; positivity) R' hR'
    (fun u => (2 * Cg * Ck * S / y ^ 2) * H u) (hH.const_mul _)
    (fun u => (hfibe u).1) (fun u => (hfibe u).2.trans_eq (by dsimp [Pe, H]; ring))
  rw [integral_const_mul] at hiob hieb
  have hNpay : N ≤ 2 * T * ((n : ℝ) * |mu| + (n : ℝ) * m3) := by
    have hp := mul_le_mul_of_nonneg_left hscalelo (Nat.cast_nonneg m)
    have hmpay : (m : ℝ) ≤ 2 * T * (n : ℝ) := by
      dsimp [T, m2]
      nlinarith only [hp, (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hsum := mul_le_mul_of_nonneg_right hmpay (show 0 ≤ |mu| + m3 by positivity)
    dsimp [N]
    nlinarith only [hsum]
  have hcoefO : 4000 * Co * I ≤ 10000 * (Co + Cg) * (I + 1) := by
    apply sub_nonneg.mp
    ring_nf
    positivity
  have hcoefE : 2 * Cg * I ≤ 10000 * (Co + Cg) * (I + 1) := by
    apply sub_nonneg.mp
    ring_nf
    positivity
  have hoVal : (∫ p in R', Fo p * K p / y ^ 2) ≤
      (10000 * (Co + Cg) * Ck * (I + 1)) / y ^ 2 * T * ((n : ℝ) * |mu| + (n : ℝ) * m3) := by
    refine hiob.trans ?_
    calc
      _ ≤ (2000 * Co * Ck * (2 * T * ((n : ℝ) * |mu| + (n : ℝ) * m3)) / y ^ 2) * I := by gcongr
      _ = (4000 * Co * I) * (Ck / y ^ 2 * T * ((n : ℝ) * |mu| + (n : ℝ) * m3)) := by ring
      _ ≤ (10000 * (Co + Cg) * (I + 1)) * (Ck / y ^ 2 * T * ((n : ℝ) * |mu| + (n : ℝ) * m3)) := by gcongr
      _ = _ := by ring
  have heVal : (∫ p in R', Fe p * K p / y ^ 2) ≤
      (10000 * (Co + Cg) * Ck * (I + 1)) / y ^ 2 * S := by
    refine hieb.trans ?_
    calc
      _ = (2 * Cg * I) * (Ck / y ^ 2 * S) := by ring
      _ ≤ (10000 * (Co + Cg) * (I + 1)) * (Ck / y ^ 2 * S) := by gcongr
      _ = _ := by ring
  change IntegrableOn (fun p => Fo p * K p / y ^ 2) R ∧
    IntegrableOn (fun p => Fe p * K p / y ^ 2) R ∧
    (∫ p in R, Fo p * K p / y ^ 2) ≤ _ ∧ (∫ p in R, Fe p * K p / y ^ 2) ≤ _
  simpa only [IntegrableOn, hrestrict] using And.intro hio (And.intro hie (And.intro hoVal heVal))

private lemma integerGaussianSineMoment (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T y : ℝ, 0 < T → 0 ≤ y →
      let J : ℝ → ℝ := fun u => |u| ^ k * Real.exp (-T * u ^ 2 / 256) *
        min (y * |u|) (1 + Real.sqrt (y * |u|))
      Integrable J ∧ (∫ u : ℝ, J u) ≤ C / Real.sqrt T ^ (k + 1) *
        (1 + Real.sqrt y * T ^ (-(1 / 4 : ℝ))) := by
  obtain ⟨C, hC, hb⟩ := gaussianSineMoment (k : ℝ) (by have hh := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith)
  refine ⟨C, hC, ?_⟩
  intro T y hT hy
  have ha : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have heq (u : ℝ) : Real.exp (-(1 / 256 : ℝ) * (Real.sqrt T * u) ^ 2) =
      Real.exp (-T * u ^ 2 / 256) := by
    congr 1
    rw [mul_pow, Real.sq_sqrt hT.le]
    ring
  have hr : Real.sqrt T ^ (-(1 / 2 : ℝ)) = T ^ (-(1 / 4 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT.le]
    norm_num
  have hp : Real.sqrt T ^ (-(k : ℝ) - 1) = (Real.sqrt T ^ (k + 1))⁻¹ := by
    rw [show -(k : ℝ) - 1 = -((k + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_neg ha.le, Real.rpow_natCast]
  have h := hb T.sqrt y ha hy
  dsimp only at h
  simp_rw [heq] at h
  rw [hp, hr] at h
  simpa only [Real.rpow_natCast, div_eq_mul_inv] using h

private lemma gaussianSineMoments_finite :
    ∃ C : ℝ, 0 < C ∧ ∀ T y : ℝ, 0 < T → 0 ≤ y →
      let G : ℝ → ℝ := fun u => Real.exp (-T * u ^ 2 / 256)
      let F : ℝ → ℝ := fun u => min (y * |u|) (1 + Real.sqrt (y * |u|))
      let R : ℝ := 1 + Real.sqrt y * T ^ (-(1 / 4 : ℝ))
      (∀ k : ℕ, k ≤ 5 → Integrable (fun u => |u| ^ k * G u * F u) ∧
        (∫ u : ℝ, |u| ^ k * G u * F u) ≤ C / Real.sqrt T ^ (k + 1) * R) ∧
      Integrable (fun u => (1 / |u|) * G u * F u) ∧
      (∫ u : ℝ, (1 / |u|) * G u * F u) ≤ C * R := by
  classical
  choose c hc hcb using fun k : Fin 6 => integerGaussianSineMoment k.val
  obtain ⟨ci, hci, hib⟩ := gaussianSineInverseMoment
  let C : ℝ := ci + ∑ k : Fin 6, c k
  have hsum : 0 ≤ ∑ k : Fin 6, c k := Finset.sum_nonneg fun k _ => (hc k).le
  have hC : 0 < C := by dsimp [C]; positivity
  have hciC : ci ≤ C := by dsimp [C]; linarith
  have hcC (k : Fin 6) : c k ≤ C := by
    have hk := Finset.single_le_sum (fun j _ => (hc j).le) (Finset.mem_univ k)
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro T y hT hy
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    have hh := hcb ⟨k, by omega⟩ T y hT hy
    refine ⟨hh.1, hh.2.trans ?_⟩
    gcongr
    exact hcC ⟨k, by omega⟩
  · have hh := hib (Real.sqrt T) y (Real.sqrt_pos.mpr hT) hy
    have heq (u : ℝ) : Real.exp (-(1 / 256 : ℝ) * (Real.sqrt T * u) ^ 2) =
        Real.exp (-T * u ^ 2 / 256) := by congr 1; rw [mul_pow, Real.sq_sqrt hT.le]; ring
    dsimp only at hh
    simp_rw [heq] at hh
    simpa only [Real.rpow_neg_one, one_div] using hh.1
  · have hh := hib (Real.sqrt T) y (Real.sqrt_pos.mpr hT) hy
    have heq (u : ℝ) : Real.exp (-(1 / 256 : ℝ) * (Real.sqrt T * u) ^ 2) =
        Real.exp (-T * u ^ 2 / 256) := by congr 1; rw [mul_pow, Real.sq_sqrt hT.le]; ring
    have hr : Real.sqrt T ^ (-(1 / 2 : ℝ)) = T ^ (-(1 / 4 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT.le]
      norm_num
    have hb : (∫ u : ℝ, (1 / |u|) * Real.exp (-T * u ^ 2 / 256) *
        min (y * |u|) (1 + Real.sqrt (y * |u|))) ≤ ci * (1 + Real.sqrt y * T ^ (-(1 / 4 : ℝ))) := by
      dsimp only at hh
      simp_rw [heq] at hh
      rw [hr] at hh
      simpa only [Real.rpow_neg_one, one_div] using hh.2
    exact hb.trans (mul_le_mul_of_nonneg_right hciC (by positivity))

private lemma integral_linear4 (f0 f1 f2 f3 : ℝ → ℝ)
    (hi0 : Integrable f0) (hi1 : Integrable f1) (hi2 : Integrable f2) (hi3 : Integrable f3)
    (c0 c1 c2 c3 : ℝ) :
    (∫ u : ℝ, c0 * f0 u + c1 * f1 u + c2 * f2 u + c3 * f3 u) =
      c0 * (∫ u : ℝ, f0 u) + c1 * (∫ u : ℝ, f1 u) + c2 * (∫ u : ℝ, f2 u) + c3 * (∫ u : ℝ, f3 u) := by
  have h2 := integral_add (hi0.const_mul c0) (hi1.const_mul c1)
  have h3 := integral_add ((hi0.const_mul c0).add (hi1.const_mul c1)) (hi2.const_mul c2)
  have h4 := integral_add (((hi0.const_mul c0).add (hi1.const_mul c1)).add (hi2.const_mul c2)) (hi3.const_mul c3)
  simp only [Pi.add_apply] at h2 h3 h4
  rw [h3, h2] at h4
  simpa only [integral_const_mul] using h4

private lemma lowGaussianProfiles :
    ∃ C : ℝ, 0 < C ∧ ∀ T y : ℝ, 0 < T → 0 ≤ y →
      let a : ℝ := Real.sqrt T
      let G : ℝ → ℝ := fun u => Real.exp (-T * u ^ 2 / 256)
      let F : ℝ → ℝ := fun u => min (y * |u|) (1 + Real.sqrt (y * |u|))
      let R : ℝ := 1 + Real.sqrt y * T ^ (-(1 / 4 : ℝ))
      let K0 : ℝ → ℝ := fun u => 2 * a + 3 * T * |u| + 2 / |u| + T ^ 2 * |u| ^ 3
      let K3 : ℝ → ℝ := fun u => 3 * |u| + 2 * a * |u| ^ 2 + 3 * T * |u| ^ 3 + T ^ 2 * |u| ^ 5
      let K1 : ℝ → ℝ := fun u => 2 * y * a * |u| + 3 * y * T * |u| ^ 2 + 2 * y + y * T ^ 2 * |u| ^ 4
      let Ke : ℝ → ℝ := fun u => a + 2 * T * |u| + T ^ 2 * |u| ^ 3 + 1 / |u|
      (Integrable (fun u => G u * F u * K0 u) ∧ (∫ u : ℝ, G u * F u * K0 u) ≤ C * R) ∧
      (Integrable (fun u => G u * F u * K3 u) ∧ (∫ u : ℝ, G u * F u * K3 u) ≤ C / T * R) ∧
      (Integrable (fun u => G u * F u * K1 u) ∧ (∫ u : ℝ, G u * F u * K1 u) ≤ C * y / a * R) ∧
      (Integrable (fun u => G u * F u * Ke u) ∧ (∫ u : ℝ, G u * F u * Ke u) ≤ C * R) := by
  obtain ⟨C, hC, hmom⟩ := gaussianSineMoments_finite
  refine ⟨10 * C, by positivity, ?_⟩
  intro T y hT hy
  let a : ℝ := Real.sqrt T
  let G : ℝ → ℝ := fun u => Real.exp (-T * u ^ 2 / 256)
  let F : ℝ → ℝ := fun u => min (y * |u|) (1 + Real.sqrt (y * |u|))
  let R : ℝ := 1 + Real.sqrt y * T ^ (-(1 / 4 : ℝ))
  let J (k : ℕ) : ℝ → ℝ := fun u => |u| ^ k * G u * F u
  let Ji : ℝ → ℝ := fun u => (1 / |u|) * G u * F u
  let K0 : ℝ → ℝ := fun u => 2 * a + 3 * T * |u| + 2 / |u| + T ^ 2 * |u| ^ 3
  let K3 : ℝ → ℝ := fun u => 3 * |u| + 2 * a * |u| ^ 2 + 3 * T * |u| ^ 3 + T ^ 2 * |u| ^ 5
  let K1 : ℝ → ℝ := fun u => 2 * y * a * |u| + 3 * y * T * |u| ^ 2 + 2 * y + y * T ^ 2 * |u| ^ 4
  let Ke : ℝ → ℝ := fun u => a + 2 * T * |u| + T ^ 2 * |u| ^ 3 + 1 / |u|
  have ha : 0 < a := Real.sqrt_pos.mpr hT
  have ha2 : a ^ 2 = T := Real.sq_sqrt hT.le
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hJ := hmom T y hT hy
  obtain ⟨hi0, hb0⟩ := hJ.1 0 (by omega)
  obtain ⟨hi1, hb1⟩ := hJ.1 1 (by omega)
  obtain ⟨hi2, hb2⟩ := hJ.1 2 (by omega)
  obtain ⟨hi3, hb3⟩ := hJ.1 3 (by omega)
  obtain ⟨hi4, hb4⟩ := hJ.1 4 (by omega)
  obtain ⟨hi5, hb5⟩ := hJ.1 5 (by omega)
  change Integrable (J 0) at hi0
  change Integrable (J 1) at hi1
  change Integrable (J 2) at hi2
  change Integrable (J 3) at hi3
  change Integrable (J 4) at hi4
  change Integrable (J 5) at hi5
  have hii : Integrable Ji := hJ.2.1
  have hbi : (∫ u : ℝ, Ji u) ≤ C * R := hJ.2.2
  have he0 : (fun u => G u * F u * K0 u) =
      (fun u => 2 * a * J 0 u + 3 * T * J 1 u + 2 * Ji u + T ^ 2 * J 3 u) := by
    funext u
    dsimp [K0, J, Ji]
    ring
  have he3 : (fun u => G u * F u * K3 u) =
      (fun u => 3 * J 1 u + 2 * a * J 2 u + 3 * T * J 3 u + T ^ 2 * J 5 u) := by
    funext u
    dsimp [K3, J]
    ring
  have he1 : (fun u => G u * F u * K1 u) =
      (fun u => 2 * y * a * J 1 u + 3 * y * T * J 2 u + 2 * y * J 0 u + y * T ^ 2 * J 4 u) := by
    funext u
    dsimp [K1, J]
    ring
  have hee : (fun u => G u * F u * Ke u) =
      (fun u => a * J 0 u + 2 * T * J 1 u + T ^ 2 * J 3 u + Ji u) := by
    funext u
    dsimp [Ke, J, Ji]
    ring
  have hiK0 : Integrable (fun u => G u * F u * K0 u) := he0 ▸
    (((hi0.const_mul _).add (hi1.const_mul _)).add (hii.const_mul _)).add (hi3.const_mul _)
  have hiK3 : Integrable (fun u => G u * F u * K3 u) := he3 ▸
    (((hi1.const_mul _).add (hi2.const_mul _)).add (hi3.const_mul _)).add (hi5.const_mul _)
  have hiK1 : Integrable (fun u => G u * F u * K1 u) := he1 ▸
    (((hi1.const_mul _).add (hi2.const_mul _)).add (hi0.const_mul _)).add (hi4.const_mul _)
  have hiKe : Integrable (fun u => G u * F u * Ke u) := hee ▸
    (((hi0.const_mul _).add (hi1.const_mul _)).add (hi3.const_mul _)).add hii
  change (Integrable (fun u => G u * F u * K0 u) ∧ _) ∧
    (Integrable (fun u => G u * F u * K3 u) ∧ _) ∧
    (Integrable (fun u => G u * F u * K1 u) ∧ _) ∧
    (Integrable (fun u => G u * F u * Ke u) ∧ _)
  refine ⟨⟨hiK0, ?_⟩, ⟨hiK3, ?_⟩, ⟨hiK1, ?_⟩, ⟨hiKe, ?_⟩⟩
  · calc
      _ = 2 * a * (∫ u : ℝ, J 0 u) + 3 * T * (∫ u : ℝ, J 1 u) +
          2 * (∫ u : ℝ, Ji u) + T ^ 2 * (∫ u : ℝ, J 3 u) := by
        rw [he0]
        exact integral_linear4 (J 0) (J 1) Ji (J 3) hi0 hi1 hii hi3 (2 * a) (3 * T) 2 (T ^ 2)
      _ ≤ 2 * a * (C / a ^ 1 * R) + 3 * T * (C / a ^ 2 * R) +
          2 * (C * R) + T ^ 2 * (C / a ^ 4 * R) := by gcongr
      _ = 8 * C * R := by rw [← ha2]; field_simp; ring
      _ ≤ _ := by nlinarith only [mul_nonneg hC.le hR]
  · calc
      _ = 3 * (∫ u : ℝ, J 1 u) + 2 * a * (∫ u : ℝ, J 2 u) +
          3 * T * (∫ u : ℝ, J 3 u) + T ^ 2 * (∫ u : ℝ, J 5 u) := by
        rw [he3]
        exact integral_linear4 (J 1) (J 2) (J 3) (J 5) hi1 hi2 hi3 hi5 3 (2 * a) (3 * T) (T ^ 2)
      _ ≤ 3 * (C / a ^ 2 * R) + 2 * a * (C / a ^ 3 * R) +
          3 * T * (C / a ^ 4 * R) + T ^ 2 * (C / a ^ 6 * R) := by gcongr
      _ = 9 * C / T * R := by rw [← ha2]; field_simp; ring
      _ ≤ _ := by
        change 9 * C / T * R ≤ (10 * C) / T * R
        have hh : 0 ≤ C / T * R := by positivity
        simp only [div_eq_mul_inv] at hh ⊢
        nlinarith only [hh]
  · calc
      _ = 2 * y * a * (∫ u : ℝ, J 1 u) + 3 * y * T * (∫ u : ℝ, J 2 u) +
          2 * y * (∫ u : ℝ, J 0 u) + y * T ^ 2 * (∫ u : ℝ, J 4 u) := by
        rw [he1]
        exact integral_linear4 (J 1) (J 2) (J 0) (J 4) hi1 hi2 hi0 hi4 (2 * y * a) (3 * y * T) (2 * y) (y * T ^ 2)
      _ ≤ 2 * y * a * (C / a ^ 2 * R) + 3 * y * T * (C / a ^ 3 * R) +
          2 * y * (C / a ^ 1 * R) + y * T ^ 2 * (C / a ^ 5 * R) := by gcongr
      _ = 8 * C * y / a * R := by rw [← ha2]; field_simp; ring
      _ ≤ _ := by
        change 8 * C * y / a * R ≤ (10 * C) * y / a * R
        have hh : 0 ≤ C * y / a * R := by positivity
        simp only [div_eq_mul_inv] at hh ⊢
        nlinarith only [hh]
  · calc
      _ = a * (∫ u : ℝ, J 0 u) + 2 * T * (∫ u : ℝ, J 1 u) +
          T ^ 2 * (∫ u : ℝ, J 3 u) + (∫ u : ℝ, Ji u) := by
        rw [hee]
        simpa only [one_mul] using integral_linear4 (J 0) (J 1) (J 3) Ji hi0 hi1 hi3 hii a (2 * T) (T ^ 2) 1
      _ ≤ a * (C / a ^ 1 * R) + 2 * T * (C / a ^ 2 * R) +
          T ^ 2 * (C / a ^ 4 * R) + C * R := by gcongr
      _ = 5 * C * R := by rw [← ha2]; field_simp; ring
      _ ≤ _ := by nlinarith only [mul_nonneg hC.le hR]

private lemma oddConeGrouped (N0 N1 T a t z : ℝ) (ha : a ^ 2 = T) (ht : t ≠ 0) :
    N1 * t + (a * (1 + a * t) + 1 / t) * (N0 + N1 * (t ^ 2 + z)) +
      (T * (1 + T * t ^ 2) + a * (1 + a * t) / t + 1 / t ^ 2) *
        (N0 * t + N1 * (t ^ 3 + t * z)) =
      N0 * (2 * a + 3 * T * t + 2 / t + T ^ 2 * t ^ 3) +
        N1 * (3 * t + 2 * a * t ^ 2 + 3 * T * t ^ 3 + T ^ 2 * t ^ 5) +
        N1 * (2 * a + 3 * T * t + 2 / t + T ^ 2 * t ^ 3) * z := by
  rw [← ha]
  field_simp
  ring

private lemma evenConeGrouped (T a t : ℝ) (ha : a ^ 2 = T) :
    T * t * (1 + T * t ^ 2) + a * (1 + a * t) + 1 / t =
      a + 2 * T * t + T ^ 2 * t ^ 3 + 1 / t := by
  rw [← ha]
  ring

private lemma yTimesK0 (T a t y : ℝ) (hy : 0 ≤ y) :
    y * t * (2 * a + 3 * T * t + 2 / t + T ^ 2 * t ^ 3) ≤
      2 * y * a * t + 3 * y * T * t ^ 2 + 2 * y + y * T ^ 2 * t ^ 4 := by
  by_cases ht : t = 0
  · subst t
    simpa using (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hy)
  · apply le_of_eq
    field_simp

theorem sourceTruncation_odd_even_fullNoise_region1_actual_marked_postIBP :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun z : ℝ => z ^ 2) ν0 →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν0) = 1 →
          (∫ z : ℝ, z ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 2 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            ∀ i : ℕ, i ≤ n → ∀ h kappa L2 y w sigma : ℝ,
              epsilon / (1 + x) ≤ h → 0 < kappa → kappa ≤ (1 / 128 : ℝ) → 20 ≤ L2 →
                1 ≤ kappa * Real.sqrt L2 → 0 < y → y ≤ 2 →
                |w| ≤ y / 16 → |sigma| = 1 →
                let ρ : Measure ℝ :=
                  ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
                let m : ℕ := n - i
                let T : ℝ := (m : ℝ) * (∫ z : ℝ, z ^ 2 ∂ρ)
                let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
                let mu : ℝ := ∫ z : ℝ, z ∂ρ
                let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂ρ
                L2 * gamma ^ 2 ≤ T → T < y ^ 2 →
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
                let R : Set (ℝ × ℝ) := {p | |p.1| ≤ kappa / gamma ∧ |p.2| ≤ kappa * |p.1| / gamma ∧ p.1 ≠ 0 ∧ |p.2| ≤ |p.1| / (4 * h)}
                let Iodd : ℝ × ℝ → ℝ := fun p =>
                  ‖deriv (fun r : ℝ => deriv (fun t : ℝ => D t p.2) r) p.1‖ *
                    ‖B p.1 p.2‖ / y ^ 2
                let Ieven : ℝ × ℝ → ℝ := fun p =>
                  ‖deriv (fun r : ℝ => deriv (fun t : ℝ => W t p.2) r) p.1‖ *
                    ‖B p.1 p.2‖ / y ^ 2
                IntegrableOn Iodd R ∧ IntegrableOn Ieven R ∧
                  (∫ p in R, Iodd p) ≤ C / y ^ 2 * ((n : ℝ) * m3 + T * ((n : ℝ) * |mu|)) * (1 + Real.sqrt y * T ^ (-(1 / 4 : ℝ))) ∧
                  (∫ p in R, Ieven p) ≤ C / y ^ 2 * (1 + Real.sqrt y * T ^ (-(1 / 4 : ℝ))) := by
  obtain ⟨Co, hCo, hlow⟩ := sourceTruncation_odd_even_fullNoise_lowFrequency_derivatives
  obtain ⟨Cg, hCg, hglobal⟩ := sourceTruncation_odd_even_fullNoise_global_derivatives
  obtain ⟨Ck, hCk, hmark⟩ := actualMarkedGlobalData
  obtain ⟨Cp, hCp, hprofiles⟩ := lowGaussianProfiles
  refine ⟨100 * Co * Ck * Cp, by positivity, ?_⟩
  intro ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h kappa L2 y w sigma
    hh hk hk128 hL2 hkL2 hy hy2 hw hsigma
  dsimp only
  intro hTL hTy
  let := hp0
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
  let m : ℕ := n - i
  let mu : ℝ := ∫ z : ℝ, z ∂ρ
  let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂ρ
  let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂ρ
  let T : ℝ := (m : ℝ) * m2
  let gamma : ℝ := m3 / variance (id : ℝ → ℝ) ρ
  let aa : ℝ := Real.sqrt T
  let N0 : ℝ := (m : ℝ) * |mu|
  let N3 : ℝ := (m : ℝ) * m3
  let Qraw : ℝ := (n : ℝ) * m3 + T * ((n : ℝ) * |mu|)
  let RR : ℝ := 1 + Real.sqrt y * T ^ (-(1 / 4 : ℝ))
  let G : ℝ → ℝ := fun u => Real.exp (-T * u ^ 2 / 256)
  let F : ℝ → ℝ := fun u => min (y * |u|) (1 + Real.sqrt (y * |u|))
  let K0 : ℝ → ℝ := fun u => 2 * aa + 3 * T * |u| + 2 / |u| + T ^ 2 * |u| ^ 3
  let K3 : ℝ → ℝ := fun u => 3 * |u| + 2 * aa * |u| ^ 2 + 3 * T * |u| ^ 3 + T ^ 2 * |u| ^ 5
  let K1 : ℝ → ℝ := fun u => 2 * y * aa * |u| + 3 * y * T * |u| ^ 2 + 2 * y + y * T ^ 2 * |u| ^ 4
  let Ke : ℝ → ℝ := fun u => aa + 2 * T * |u| + T ^ 2 * |u| ^ 3 + 1 / |u|
  let A0 : ℝ → ℝ := fun u => G u * F u * K0 u
  let A3 : ℝ → ℝ := fun u => G u * F u * K3 u
  let A1 : ℝ → ℝ := fun u => G u * F u * K1 u
  let Ae : ℝ → ℝ := fun u => G u * F u * Ke u
  let R : Set (ℝ × ℝ) := {p | |p.1| ≤ kappa / gamma ∧ |p.2| ≤ kappa * |p.1| / gamma ∧
    p.1 ≠ 0 ∧ |p.2| ≤ |p.1| / (4 * h)}
  let amp : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r + sigma * w / y) ^ 2
  let B : ℝ × ℝ → ℂ := fun p => ∫ r : ℝ,
    ((amp r * Real.sin (p.1 * (y * Real.sqrt r + sigma * w)) : ℝ) : ℂ) *
      Complex.exp (-(((p.2 * r : ℝ) : ℂ) * Complex.I))
  let K : ℝ × ℝ → ℝ := fun p => ‖B p‖
  let D : ℝ → ℝ → ℂ := fun u v =>
    (quadraticChar ρ u v ^ m - quadraticChar ρ (-u) v ^ m) / 2 * quadraticFullNoiseChar ρ u v
  let W : ℝ → ℝ → ℂ := fun u v => (u : ℂ) *
    ((quadraticChar ρ u v ^ m + quadraticChar ρ (-u) v ^ m) / 2 * quadraticFullNoiseChar ρ u v)
  let Fo : ℝ × ℝ → ℝ := fun p => ‖deriv (fun r => deriv (fun t => D t p.2) r) p.1‖
  let Fe : ℝ × ℝ → ℝ := fun p => ‖deriv (fun r => deriv (fun t => W t p.2) r) p.1‖
  let P0 : ℝ → ℝ := fun u => Co * G u * (N0 * K0 u + N3 * K3 u)
  let P1 : ℝ → ℝ := fun u => Co * G u * N3 * K0 u
  let Pe : ℝ → ℝ := fun u => Co * G u * Ke u
  let Ho : ℝ → ℝ := fun u => Co * Ck / y ^ 2 * (N0 * A0 u + N3 * A3 u + N3 * A0 u + N3 * A1 u)
  let He : ℝ → ℝ := fun u => Co * Ck / y ^ 2 * Ae u
  obtain ⟨_, _, hp, hs, _, h2r, h3r, _⟩ := Shao.sourceTruncation_law_data ν0 n h2 hnorm x epsilon hx he hehalf hbudget
  have : IsProbabilityMeasure ρ := hp
  have hV := (Shao.sourceTruncation_variance_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget).2.2.2.2.2.1
  have hscalelo := (Shao.sourceTruncation_variance_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget).1
  have hscalehi := (Shao.sourceTruncation_variance_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget).2.1
  have hgammap := (Shao.sourceTruncation_gamma_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget).2.1
  have hm3p := (Shao.sourceTruncation_gamma_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget).1
  have hT : 0 < T := (mul_pos (by linarith : 0 < L2) (sq_pos_of_pos hgammap)).trans_le hTL
  have haa : 0 < aa := Real.sqrt_pos.mpr hT
  have haa2 : aa ^ 2 = T := Real.sq_sqrt hT.le
  have hTbound : T ≤ (4 / 3 : ℝ) := (mul_le_mul_of_nonneg_right
    (show (m : ℝ) ≤ n from Nat.cast_le.mpr (Nat.sub_le _ _)) (integral_nonneg fun z => sq_nonneg z)).trans hscalehi
  have haa2bound : aa ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hhpos : 0 < h := (div_pos he (by linarith : 0 < 1 + x)).trans_le hh
  have hsupport : ∀ᵐ z : ℝ ∂ρ, |z| ≤ h := hs.mono fun _ hz => hz.trans hh
  have : IsProbabilityMeasure (quadraticFullNoiseLaw ρ) :=
    (quadraticFullNoise_law_data ρ h3r hV h hhpos hsupport).2.2.1
  have hdata := hglobal ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h hh
  have hcont := actualOddEven_continuous ρ m
  have hFo : Measurable Fo := (jointSecondDerivative_measurable _ hcont.1.measurable
    (fun p => ⟨(hdata p.1 p.2).1, (hdata p.1 p.2).2.1⟩)).norm
  have hFe : Measurable Fe := (jointSecondDerivative_measurable _ hcont.2.measurable
    (fun p => ⟨(hdata p.1 p.2).2.2.1, (hdata p.1 p.2).2.2.2.1⟩)).norm
  have hR : MeasurableSet R :=
    (isClosed_le continuous_fst.abs continuous_const).measurableSet.inter
      ((isClosed_le continuous_snd.abs ((continuous_const.mul continuous_fst.abs).div_const _)).measurableSet.inter
        ((isClosed_eq continuous_fst continuous_const).measurableSet.compl.inter
          (isClosed_le continuous_snd.abs (continuous_fst.abs.div_const _)).measurableSet))
  have hN0 : 0 ≤ N0 := by dsimp [N0]; positivity
  have hN3 : 0 ≤ N3 := by dsimp [N3]; positivity
  have hF0 (u : ℝ) : 0 ≤ F u := by dsimp [F]; positivity
  have hG0 (u : ℝ) : 0 ≤ G u := (Real.exp_pos _).le
  have hK00 (u : ℝ) : 0 ≤ K0 u := by dsimp [K0]; positivity
  have hK30 (u : ℝ) : 0 ≤ K3 u := by dsimp [K3]; positivity
  have hK10 (u : ℝ) : 0 ≤ K1 u := by dsimp [K1]; positivity
  have hKe0 (u : ℝ) : 0 ≤ Ke u := by dsimp [Ke]; positivity
  have hP0 (u : ℝ) : 0 ≤ P0 u := by dsimp [P0]; positivity
  have hP1 (u : ℝ) : 0 ≤ P1 u := by dsimp [P1]; positivity
  have hPe (u : ℝ) : 0 ≤ Pe u := by dsimp [Pe]; positivity
  have ho (u v : ℝ) (hp : (u, v) ∈ R) : Fo (u, v) ≤ P0 u + P1 u * |v| := by
    have hl := ((hlow ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h kappa L2
      hh hk hk128 hL2 hkL2 hTL u v hp.1 hp.2.1).2 hp.2.2.1 hp.2.2.2).1
    have hg := oddConeGrouped N0 N3 T aa |u| |v| haa2 (abs_ne_zero.mpr hp.2.2.1)
    have hgroup : (m : ℝ) * m3 * |u| +
        (Real.sqrt T * (1 + Real.sqrt T * |u|) + 1 / |u|) *
          ((m : ℝ) * |mu| + (m : ℝ) * m3 * (u ^ 2 + |v|)) +
        (T * (1 + T * u ^ 2) + Real.sqrt T * (1 + Real.sqrt T * |u|) / |u| + 1 / u ^ 2) *
          ((m : ℝ) * |mu| * |u| + (m : ℝ) * m3 * (|u| ^ 3 + |u| * |v|)) =
          N0 * K0 u + N3 * K3 u + N3 * K0 u * |v| := by
      simpa only [N0, N3, aa, K0, K3, sq_abs] using hg
    refine hl.trans_eq ?_
    rw [hgroup]
    dsimp [P0, P1, G]
    ring
  have heven (u v : ℝ) (hp : (u, v) ∈ R) : Fe (u, v) ≤ Pe u := by
    have hl := ((hlow ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h kappa L2
      hh hk hk128 hL2 hkL2 hTL u v hp.1 hp.2.1).2 hp.2.2.1 hp.2.2.2).2
    have hg := evenConeGrouped T aa |u| haa2
    have hgroup : T * |u| * (1 + T * u ^ 2) + Real.sqrt T * (1 + Real.sqrt T * |u|) + 1 / |u| = Ke u := by
      simpa only [aa, Ke, sq_abs] using hg
    change Fe (u, v) ≤ Co * G u * (T * |u| * (1 + T * u ^ 2) + Real.sqrt T * (1 + Real.sqrt T * |u|) + 1 / |u|) at hl
    rw [hgroup] at hl
    exact hl
  obtain ⟨hKm, hkernel⟩ := hmark y w sigma hy hw hsigma
  have hpro := hprofiles T y hT hy.le
  have hA0i : Integrable A0 := hpro.1.1
  have hA3i : Integrable A3 := hpro.2.1.1
  have hA1i : Integrable A1 := hpro.2.2.1.1
  have hAei : Integrable Ae := hpro.2.2.2.1
  have hHoi : Integrable Ho := ((((hA0i.const_mul N0).add (hA3i.const_mul N3)).add
    (hA0i.const_mul N3)).add (hA1i.const_mul N3)).const_mul _
  have hHei : Integrable He := hAei.const_mul _
  have hfiber (FF : ℝ × ℝ → ℝ) (hFF : Measurable FF) (hFF0 : ∀ p, 0 ≤ FF p)
      (Q0 Q1 : ℝ → ℝ) (hQ0 : ∀ u, 0 ≤ Q0 u) (hQ1 : ∀ u, 0 ≤ Q1 u)
      (hbound : ∀ u v, (u, v) ∈ R → FF (u, v) ≤ Q0 u + Q1 u * |v|) (u : ℝ) :
      Integrable (fun v => R.indicator (fun p => FF p * K p / y ^ 2) (u, v)) ∧
        (∫ v : ℝ, R.indicator (fun p => FF p * K p / y ^ 2) (u, v)) ≤
          (Q0 u * (Ck * F u) + Q1 u * (Ck * (1 + y * |u|) * F u)) / y ^ 2 := by
    let U : Set ℝ := {v | (u, v) ∈ R}
    have hU : MeasurableSet U := hR.preimage (measurable_const.prodMk measurable_id)
    obtain ⟨hi, hb⟩ := affineMarkedFiber (fun v => FF (u, v)) (fun v => K (u, v))
      (hFF.comp (measurable_const.prodMk measurable_id)) (hKm.comp (measurable_const.prodMk measurable_id))
      (fun v => hFF0 _) (fun v => norm_nonneg _) U univ hU MeasurableSet.univ (by intro v hv; trivial)
      (Q0 u) (Q1 u) y (hQ0 u) (hQ1 u) (fun v hv => hbound u v hv)
      (by simpa only [integrableOn_univ] using (hkernel u).1)
      (by simpa only [integrableOn_univ] using (hkernel u).2.1)
    refine ⟨hi, hb.trans ?_⟩
    simp only [setIntegral_univ]
    exact div_le_div_of_nonneg_right (add_le_add
      (mul_le_mul_of_nonneg_left (hkernel u).2.2.1 (hQ0 u))
      (mul_le_mul_of_nonneg_left (hkernel u).2.2.2 (hQ1 u))) (sq_nonneg _)
  have hfibo := hfiber Fo hFo (fun _ => norm_nonneg _) P0 P1 hP0 hP1 ho
  have hfibe := hfiber Fe hFe (fun _ => norm_nonneg _) Pe (fun _ => 0) hPe (fun _ => le_rfl)
    (fun u v hp => by simpa only [zero_mul, add_zero] using heven u v hp)
  obtain ⟨hio, hiob⟩ := nonnegativeRegionIntegral (fun p => Fo p * K p / y ^ 2)
    ((hFo.mul hKm).div_const _) (fun p => by dsimp [Fo, K]; positivity) R hR Ho hHoi
    (fun u => (hfibo u).1) (fun u => (hfibo u).2.trans (by
      have hpaid : y * |u| * K0 u ≤ K1 u := yTimesK0 T aa |u| y hy.le
      calc
        _ = Co * Ck / y ^ 2 * (N0 * A0 u + N3 * A3 u + N3 * A0 u +
            N3 * (G u * F u * (y * |u| * K0 u))) := by dsimp [P0, P1, A0, A3]; ring
        _ ≤ Ho u := by dsimp [Ho, A1]; gcongr))
  obtain ⟨hie, hieb⟩ := nonnegativeRegionIntegral (fun p => Fe p * K p / y ^ 2)
    ((hFe.mul hKm).div_const _) (fun p => by dsimp [Fe, K]; positivity) R hR He hHei
    (fun u => (hfibe u).1) (fun u => (hfibe u).2.trans_eq (by dsimp [Pe, He, Ae]; ring))
  have hHoVal : (∫ u : ℝ, Ho u) ≤ Co * Ck / y ^ 2 * Cp *
      (N0 + N3 / T + N3 + N3 * y / aa) * RR := by
    change (∫ u : ℝ, Co * Ck / y ^ 2 * (N0 * A0 u + N3 * A3 u + N3 * A0 u + N3 * A1 u)) ≤ _
    rw [integral_const_mul, integral_linear4 A0 A3 A0 A1 hA0i hA3i hA0i hA1i N0 N3 N3 N3]
    calc
      _ ≤ Co * Ck / y ^ 2 * (N0 * (Cp * RR) + N3 * (Cp / T * RR) + N3 * (Cp * RR) + N3 * (Cp * y / aa * RR)) := by
        gcongr
        · exact hpro.1.2
        · exact hpro.2.1.2
        · exact hpro.1.2
        · exact hpro.2.2.1.2
      _ = _ := by ring
  have hHeVal : (∫ u : ℝ, He u) ≤ Co * Ck / y ^ 2 * Cp * RR := by
    change (∫ u : ℝ, Co * Ck / y ^ 2 * Ae u) ≤ _
    rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left hpro.2.2.2.2 (by positivity)).trans_eq (by ring)
  have hmpay : (m : ℝ) ≤ 2 * T * (n : ℝ) := by
    have hp := mul_le_mul_of_nonneg_left hscalelo (Nat.cast_nonneg m)
    dsimp [T, m2]
    nlinarith only [hp, (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hN0pay : N0 ≤ 2 * T * ((n : ℝ) * |mu|) := by
    simpa only [N0, mul_assoc] using mul_le_mul_of_nonneg_right hmpay (abs_nonneg mu)
  have hN3pay : N3 ≤ 2 * T * ((n : ℝ) * m3) := by
    simpa only [N3, mul_assoc] using mul_le_mul_of_nonneg_right hmpay hm3p.le
  have hn3 : 0 ≤ (n : ℝ) * m3 := by positivity
  have hN3div : N3 / T ≤ 2 * ((n : ℝ) * m3) := (div_le_iff₀ hT).mpr (hN3pay.trans_eq (by ring))
  have hN3small : N3 ≤ 4 * ((n : ℝ) * m3) := hN3pay.trans (by nlinarith only [mul_le_mul_of_nonneg_right hTbound hn3, hn3])
  have hN3y : N3 * y / aa ≤ 8 * ((n : ℝ) * m3) := by
    calc
      _ ≤ (2 * T * ((n : ℝ) * m3)) * y / aa := by gcongr
      _ = 2 * aa * y * ((n : ℝ) * m3) := by rw [← haa2]; field_simp
      _ ≤ _ := by
        have hpay : aa * y ≤ 4 := (mul_le_mul haa2bound hy2 hy.le (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by norm_num)
        nlinarith only [mul_le_mul_of_nonneg_right hpay hn3]
  have hraw : N0 + N3 / T + N3 + N3 * y / aa ≤ 20 * Qraw := by
    have hmu : 0 ≤ T * ((n : ℝ) * |mu|) := by positivity
    dsimp [Qraw]
    nlinarith only [hN0pay, hN3div, hN3small, hN3y, hmu, hn3]
  have hRR : 0 ≤ RR := by dsimp [RR]; positivity
  change IntegrableOn (fun p => Fo p * K p / y ^ 2) R ∧
    IntegrableOn (fun p => Fe p * K p / y ^ 2) R ∧
    (∫ p in R, Fo p * K p / y ^ 2) ≤ (100 * Co * Ck * Cp) / y ^ 2 * Qraw * RR ∧
    (∫ p in R, Fe p * K p / y ^ 2) ≤ (100 * Co * Ck * Cp) / y ^ 2 * RR
  refine ⟨hio, hie, hiob.trans (hHoVal.trans ?_), hieb.trans (hHeVal.trans ?_)⟩
  · calc
      _ ≤ Co * Ck / y ^ 2 * Cp * (20 * Qraw) * RR := by gcongr
      _ = 20 * (Co * Ck * Cp / y ^ 2 * Qraw * RR) := by ring
      _ ≤ 100 * (Co * Ck * Cp / y ^ 2 * Qraw * RR) := by
        have hx : 0 ≤ Co * Ck * Cp / y ^ 2 * Qraw * RR := by dsimp [Qraw]; positivity
        nlinarith only [hx]
      _ = _ := by ring
  · calc
      _ = Co * Ck * Cp / y ^ 2 * RR := by ring
      _ ≤ 100 * (Co * Ck * Cp / y ^ 2 * RR) := by nlinarith only [show 0 ≤ Co * Ck * Cp / y ^ 2 * RR by positivity]
      _ = _ := by ring

/- BEGIN FIXED CUTOFF PUBLIC COMPANIONS.
Additive export of the fixed one-sixteenth cutoff from the existing proof.
The original source is recovered exactly by deleting this marked block.
-/

private lemma fixedCutoff_actualMarkedOutsideData :
    ∃ C : ℝ, 0 < C ∧
      ∀ aStar y w sigma : ℝ, 0 < aStar → aStar ≤ 4 → 0 < y → y ≤ 2 →
        aStar * y ≤ (1 / 16 : ℝ) → |w| ≤ y / 16 → |sigma| = 1 →
        let a : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r + sigma * w / y) ^ 2
        let B : ℝ × ℝ → ℂ := fun p => ∫ r : ℝ,
          ((a r * Real.sin (p.1 * (y * Real.sqrt r + sigma * w)) : ℝ) : ℂ) *
            Complex.exp (-(((p.2 * r : ℝ) : ℂ) * Complex.I))
        ∀ u : ℝ, IntegrableOn (fun v => ‖B (u, v)‖) {v : ℝ | |u| / aStar < |v|} ∧
          IntegrableOn (fun v => |v| * ‖B (u, v)‖) {v : ℝ | |u| / aStar < |v|} ∧
          (∫ v in {v : ℝ | |u| / aStar < |v|}, ‖B (u, v)‖) ≤ C / (1 + |u| / 4) ^ 30 ∧
          (∫ v in {v : ℝ | |u| / aStar < |v|}, |v| * ‖B (u, v)‖) ≤ C / (1 + |u| / 4) ^ 30 := by
  obtain ⟨C, hC, hkernel⟩ := sourceKernel_marked_outside_norms_fixed_sixteenth
  refine ⟨C, hC, ?_⟩
  intro aStar y w sigma ha ha4 hy hy2 hsmall hw hsigma
  have hsw : |sigma * w| ≤ y / 16 := by simpa only [abs_mul, hsigma, one_mul] using hw
  have ht : |sigma * w / y| ≤ (1 / 16 : ℝ) := by
    rw [abs_div, abs_of_pos hy]
    exact (div_le_iff₀ hy).mpr (by linarith)
  dsimp only
  intro u
  have hd0 : (1 : ℝ) ≤ 1 + |u| / aStar := by linarith [div_nonneg (abs_nonneg u) ha.le]
  have hbase : 1 + |u| / 4 ≤ 1 + |u| / aStar :=
    add_le_add le_rfl (div_le_div_of_nonneg_left (abs_nonneg u) ha ha4)
  have h30 : (1 + |u| / 4) ^ 30 ≤ (1 + |u| / aStar) ^ 30 :=
    pow_le_pow_left₀ (by positivity) hbase 30
  have h31 : (1 + |u| / 4) ^ 30 ≤ (1 + |u| / aStar) ^ 31 := h30.trans (by
    rw [pow_succ]
    have hp := mul_nonneg (pow_nonneg (by positivity : 0 ≤ 1 + |u| / aStar) 30) (sub_nonneg.mpr hd0)
    nlinarith only [hp])
  have h := hkernel 2 (Or.inr rfl) _ ht aStar y u _ ha hy.le hy2 hsmall hsw
  refine ⟨h.2.2.1, h.2.2.2.1, ?_, ?_⟩
  · refine h.2.2.2.2.2.2.1.trans ((div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (min_le_right (y * |u|) 1) hC.le) (by positivity)).trans ?_)
    simpa only [mul_one] using div_le_div_of_nonneg_left hC.le (by positivity) h31
  · refine h.2.2.2.2.2.2.2.trans ((div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (min_le_right (y * |u|) 1) hC.le) (by positivity)).trans ?_)
    simpa only [mul_one] using div_le_div_of_nonneg_left hC.le (by positivity) h30

theorem sourceTruncation_odd_even_fullNoise_region2_actual_marked_postIBP_fixed_sixteenth :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun z : ℝ => z ^ 2) ν0 →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν0) = 1 →
          (∫ z : ℝ, z ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 2 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            ∀ i : ℕ, i ≤ n → ∀ h kappa L2 y w sigma : ℝ,
              epsilon / (1 + x) ≤ h → h ≤ 1 → 0 < kappa → kappa ≤ (1 / 128 : ℝ) → 20 ≤ L2 →
                1 ≤ kappa * Real.sqrt L2 → 0 < y → y ≤ 2 →
                |w| ≤ y / 16 → |sigma| = 1 →
                let ρ : Measure ℝ :=
                  ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
                let m : ℕ := n - i
                let T : ℝ := (m : ℝ) * (∫ z : ℝ, z ^ 2 ∂ρ)
                let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
                let mu : ℝ := ∫ z : ℝ, z ∂ρ
                let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂ρ
                L2 * gamma ^ 2 ≤ T → T < y ^ 2 → (4 * h) * y ≤ (1 / 16 : ℝ) →
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
                let R : Set (ℝ × ℝ) := {p | |p.1| ≤ kappa / gamma ∧ |p.2| ≤ kappa * |p.1| / gamma ∧ ¬(p.1 ≠ 0 ∧ |p.2| ≤ |p.1| / (4 * h))}
                let Iodd : ℝ × ℝ → ℝ := fun p =>
                  ‖deriv (fun r : ℝ => deriv (fun t : ℝ => D t p.2) r) p.1‖ *
                    ‖B p.1 p.2‖ / y ^ 2
                let Ieven : ℝ × ℝ → ℝ := fun p =>
                  ‖deriv (fun r : ℝ => deriv (fun t : ℝ => W t p.2) r) p.1‖ *
                    ‖B p.1 p.2‖ / y ^ 2
                IntegrableOn Iodd R ∧ IntegrableOn Ieven R ∧
                  (∫ p in R, Iodd p) ≤ C / y ^ 2 * T * ((n : ℝ) * |mu| + (n : ℝ) * m3) ∧
                  (∫ p in R, Ieven p) ≤ C / y ^ 2 * (Real.sqrt T + gamma) := by
  obtain ⟨Co, hCo, hlow⟩ := sourceTruncation_odd_even_fullNoise_lowFrequency_derivatives
  obtain ⟨Cg, hCg, hglobal⟩ := sourceTruncation_odd_even_fullNoise_global_derivatives
  obtain ⟨Ck, hCk, houtside⟩ := fixedCutoff_actualMarkedOutsideData
  obtain ⟨Cm, hCm, hmark⟩ := actualMarkedGlobalData
  let H : ℝ → ℝ := fun u => (1 + |u|) ^ 5 / (1 + |u| / 4) ^ 30
  let I : ℝ := ∫ u : ℝ, H u
  have hH : Integrable H := fixedOutsideProfile_integrable
  have hI : 0 ≤ I := integral_nonneg fun u => by dsimp [H]; positivity
  refine ⟨10000 * (Co + Cg) * Ck * (I + 1), by positivity, ?_⟩
  intro ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h kappa L2 y w sigma
    hh hh1 hk hk128 hL2 hkL2 hy hy2 hw hsigma
  dsimp only
  intro hTL hTy hsmall
  let := hp0
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
  let m : ℕ := n - i
  let mu : ℝ := ∫ z : ℝ, z ∂ρ
  let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂ρ
  let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂ρ
  let T : ℝ := (m : ℝ) * m2
  let gamma : ℝ := m3 / variance (id : ℝ → ℝ) ρ
  let N : ℝ := (m : ℝ) * |mu| + (m : ℝ) * m3
  let S : ℝ := Real.sqrt T + gamma
  let R : Set (ℝ × ℝ) := {p | |p.1| ≤ kappa / gamma ∧ |p.2| ≤ kappa * |p.1| / gamma ∧
    ¬(p.1 ≠ 0 ∧ |p.2| ≤ |p.1| / (4 * h))}
  let R' : Set (ℝ × ℝ) := {p | |p.1| ≤ kappa / gamma ∧ |p.2| ≤ kappa * |p.1| / gamma ∧
    |p.1| / (4 * h) < |p.2|}
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
  let Po : ℝ → ℝ := fun u => 1000 * Co * N * (1 + |u|) ^ 5
  let Pe : ℝ → ℝ := fun u => 2 * Cg * S * (1 + |u|) ^ 5
  obtain ⟨_, _, hp, hs, _, h2r, h3r, _⟩ := Shao.sourceTruncation_law_data ν0 n h2 hnorm x epsilon hx he hehalf hbudget
  have : IsProbabilityMeasure ρ := hp
  obtain ⟨hscalelo, hscalehi, _, _, _, hV, _, _⟩ :=
    Shao.sourceTruncation_variance_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget
  obtain ⟨hm3p, hgammap, _, _, hgamcut, _, _, _, _⟩ :=
    Shao.sourceTruncation_gamma_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget
  have hhpos : 0 < h := (div_pos he (by linarith : 0 < 1 + x)).trans_le hh
  have hsupport : ∀ᵐ z : ℝ ∂ρ, |z| ≤ h := hs.mono fun _ hz => hz.trans hh
  have hgam : gamma ≤ 2 * h := hgamcut.trans (by linarith)
  have hgam2 : gamma ≤ 2 := hgam.trans (by linarith)
  have hT : 0 ≤ T := mul_nonneg (Nat.cast_nonneg m) (integral_nonneg fun z => sq_nonneg z)
  have hTbound : T ≤ (4 / 3 : ℝ) := (mul_le_mul_of_nonneg_right
    (show (m : ℝ) ≤ n from Nat.cast_le.mpr (Nat.sub_le _ _)) (integral_nonneg fun z => sq_nonneg z)).trans hscalehi
  have hT2 : T ≤ 2 := by linarith
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have : IsProbabilityMeasure (quadraticFullNoiseLaw ρ) :=
    (quadraticFullNoise_law_data ρ h3r hV h hhpos hsupport).2.2.1
  have hdata := hglobal ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h hh
  have hcont := actualOddEven_continuous ρ m
  have hFo : Measurable Fo := (jointSecondDerivative_measurable _ hcont.1.measurable
    (fun p => ⟨(hdata p.1 p.2).1, (hdata p.1 p.2).2.1⟩)).norm
  have hFe : Measurable Fe := (jointSecondDerivative_measurable _ hcont.2.measurable
    (fun p => ⟨(hdata p.1 p.2).2.2.1, (hdata p.1 p.2).2.2.2.1⟩)).norm
  have hR' : MeasurableSet R' :=
    (isClosed_le continuous_fst.abs continuous_const).measurableSet.inter
      ((isClosed_le continuous_snd.abs ((continuous_const.mul continuous_fst.abs).div_const _)).measurableSet.inter
        (isOpen_lt (continuous_fst.abs.div_const _) continuous_snd.abs).measurableSet)
  have hRae : R =ᵐ[(volume : Measure (ℝ × ℝ))] R' := by
    filter_upwards [(volume : Measure (ℝ × ℝ)).ae_ne (0, 0)] with p hp0
    apply propext
    constructor
    · rintro ⟨hu, hv, hc⟩
      refine ⟨hu, hv, ?_⟩
      have hu0 : p.1 ≠ 0 := by
        intro heq
        have hv0 : p.2 = 0 := abs_eq_zero.mp (le_antisymm (by simpa only [heq, abs_zero, mul_zero, zero_div] using hv) (abs_nonneg _))
        exact hp0 (Prod.ext heq hv0)
      exact lt_of_not_ge (fun hvle => hc ⟨hu0, hvle⟩)
    · rintro ⟨hu, hv, hc⟩
      exact ⟨hu, hv, fun h => not_lt_of_ge h.2 hc⟩
  have hrestrict : (volume : Measure (ℝ × ℝ)).restrict R = volume.restrict R' := Measure.restrict_congr_set hRae
  have ho (u v : ℝ) (hp : (u, v) ∈ R') : Fo (u, v) ≤ Po u + Po u * |v| := by
    have hl := (hlow ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h kappa L2
      hh hk hk128 hL2 hkL2 hTL u v hp.1 hp.2.1).1
    have he := coarseOddEnvelope ((m : ℝ) * |mu|) ((m : ℝ) * m3) T gamma h |u| |v|
      (by positivity) (by positivity) hT hT2 hgammap.le hgam2 hhpos.le hh1 (abs_nonneg _) (abs_nonneg _)
    have hG1 : Real.exp (-T * u ^ 2 / 256) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_nonneg hT (sq_nonneg u)]
    have henv0 : 0 ≤ (m : ℝ) * m3 * |u| +
        (Real.sqrt T * (1 + Real.sqrt T * |u|) + gamma) *
          ((m : ℝ) * |mu| + (m : ℝ) * m3 * (u ^ 2 + |v|)) +
        (T * (1 + T * u ^ 2) + gamma * (Real.sqrt T * (1 + Real.sqrt T * |u|)) + h * gamma) *
          ((m : ℝ) * |mu| * |u| + (m : ℝ) * m3 * (|u| ^ 3 + |u| * |v|)) := by positivity
    refine hl.trans ?_
    calc
      _ ≤ Co * 1 * _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG1 hCo.le) henv0
      _ ≤ Co * (1000 * N * (1 + |u|) ^ 5 * (1 + |v|)) := by
        simp only [mul_one]
        apply mul_le_mul_of_nonneg_left _ hCo.le
        simpa only [sq_abs] using he
      _ = _ := by dsimp [Po]; ring
  have heven (u v : ℝ) : Fe (u, v) ≤ Pe u := by
    have hroot : Real.sqrt T ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
    have hTp : T ≤ 2 * Real.sqrt T := by nlinarith only [Real.sq_sqrt hT, Real.sqrt_nonneg T, hroot]
    have hN2 : T + h * gamma ≤ 2 * S := by
      have hp := mul_le_mul_of_nonneg_right hh1 hgammap.le
      dsimp [S]
      nlinarith only [hTp, hp, hgammap]
    have hr5 : 1 + |u| ≤ (1 + |u|) ^ 5 := by
      have hr : 1 ≤ 1 + |u| := by linarith [abs_nonneg u]
      have hp := mul_nonneg (by positivity : 0 ≤ 1 + |u|)
        (sub_nonneg.mpr (show 1 ≤ (1 + |u|) ^ 4 from one_le_pow₀ hr))
      nlinarith only [hp]
    calc
      _ ≤ Cg * (S + |u| * (T + h * gamma)) := (hdata u v).2.2.2.2.2
      _ ≤ Cg * (S + |u| * (2 * S)) := by gcongr
      _ ≤ 2 * Cg * S * (1 + |u|) := by nlinarith only [mul_nonneg hCg.le hS]
      _ ≤ _ := by dsimp [Pe]; gcongr
  obtain ⟨hKm, _⟩ := hmark y w sigma hy hw hsigma
  have hki := houtside (4 * h) y w sigma (by positivity) (by linarith) hy hy2 hsmall hw hsigma
  have hPo0 (u : ℝ) : 0 ≤ Po u := by dsimp [Po]; positivity
  have hPe0 (u : ℝ) : 0 ≤ Pe u := by dsimp [Pe]; positivity
  have hfiber (F : ℝ × ℝ → ℝ) (hFm : Measurable F) (hF0 : ∀ p, 0 ≤ F p)
      (P0 P1 : ℝ → ℝ) (hP0 : ∀ u, 0 ≤ P0 u) (hP1 : ∀ u, 0 ≤ P1 u)
      (hbound : ∀ u v, (u, v) ∈ R' → F (u, v) ≤ P0 u + P1 u * |v|) (u : ℝ) :
      Integrable (fun v => R'.indicator (fun p => F p * K p / y ^ 2) (u, v)) ∧
        (∫ v : ℝ, R'.indicator (fun p => F p * K p / y ^ 2) (u, v)) ≤
          (P0 u + P1 u) * (Ck / (1 + |u| / 4) ^ 30) / y ^ 2 := by
    let V : Set ℝ := {v | |u| / (4 * h) < |v|}
    let U : Set ℝ := {v | (u, v) ∈ R'}
    have hU : MeasurableSet U := hR'.preimage (measurable_const.prodMk measurable_id)
    have hV : MeasurableSet V := (isOpen_lt continuous_const continuous_abs).measurableSet
    obtain ⟨hi, hb⟩ := affineMarkedFiber (fun v => F (u, v)) (fun v => K (u, v))
      (hFm.comp (measurable_const.prodMk measurable_id)) (hKm.comp (measurable_const.prodMk measurable_id))
      (fun v => hF0 _) (fun v => norm_nonneg _) U V hU hV (fun v hv => hv.2.2)
      (P0 u) (P1 u) y (hP0 u) (hP1 u) (fun v hv => hbound u v hv) (hki u).1 (hki u).2.1
    refine ⟨hi, hb.trans ?_⟩
    calc
      _ ≤ (P0 u * (Ck / (1 + |u| / 4) ^ 30) + P1 u * (Ck / (1 + |u| / 4) ^ 30)) / y ^ 2 :=
        div_le_div_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left (hki u).2.2.1 (hP0 u))
          (mul_le_mul_of_nonneg_left (hki u).2.2.2 (hP1 u))) (sq_nonneg _)
      _ = _ := by ring
  have hfibo := hfiber Fo hFo (fun _ => norm_nonneg _) Po Po hPo0 hPo0 ho
  have hfibe := hfiber Fe hFe (fun _ => norm_nonneg _) Pe (fun _ => 0) hPe0 (fun _ => le_rfl)
    (fun u v hp => by simpa only [zero_mul, add_zero] using heven u v)
  obtain ⟨hio, hiob⟩ := nonnegativeRegionIntegral (fun p => Fo p * K p / y ^ 2)
    ((hFo.mul hKm).div_const _) (fun p => by dsimp [Fo, K]; positivity) R' hR'
    (fun u => (2000 * Co * Ck * N / y ^ 2) * H u) (hH.const_mul _)
    (fun u => (hfibo u).1) (fun u => (hfibo u).2.trans_eq (by dsimp [Po, H]; ring))
  obtain ⟨hie, hieb⟩ := nonnegativeRegionIntegral (fun p => Fe p * K p / y ^ 2)
    ((hFe.mul hKm).div_const _) (fun p => by dsimp [Fe, K]; positivity) R' hR'
    (fun u => (2 * Cg * Ck * S / y ^ 2) * H u) (hH.const_mul _)
    (fun u => (hfibe u).1) (fun u => (hfibe u).2.trans_eq (by dsimp [Pe, H]; ring))
  rw [integral_const_mul] at hiob hieb
  have hNpay : N ≤ 2 * T * ((n : ℝ) * |mu| + (n : ℝ) * m3) := by
    have hp := mul_le_mul_of_nonneg_left hscalelo (Nat.cast_nonneg m)
    have hmpay : (m : ℝ) ≤ 2 * T * (n : ℝ) := by
      dsimp [T, m2]
      nlinarith only [hp, (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hsum := mul_le_mul_of_nonneg_right hmpay (show 0 ≤ |mu| + m3 by positivity)
    dsimp [N]
    nlinarith only [hsum]
  have hcoefO : 4000 * Co * I ≤ 10000 * (Co + Cg) * (I + 1) := by
    apply sub_nonneg.mp
    ring_nf
    positivity
  have hcoefE : 2 * Cg * I ≤ 10000 * (Co + Cg) * (I + 1) := by
    apply sub_nonneg.mp
    ring_nf
    positivity
  have hoVal : (∫ p in R', Fo p * K p / y ^ 2) ≤
      (10000 * (Co + Cg) * Ck * (I + 1)) / y ^ 2 * T * ((n : ℝ) * |mu| + (n : ℝ) * m3) := by
    refine hiob.trans ?_
    calc
      _ ≤ (2000 * Co * Ck * (2 * T * ((n : ℝ) * |mu| + (n : ℝ) * m3)) / y ^ 2) * I := by gcongr
      _ = (4000 * Co * I) * (Ck / y ^ 2 * T * ((n : ℝ) * |mu| + (n : ℝ) * m3)) := by ring
      _ ≤ (10000 * (Co + Cg) * (I + 1)) * (Ck / y ^ 2 * T * ((n : ℝ) * |mu| + (n : ℝ) * m3)) := by gcongr
      _ = _ := by ring
  have heVal : (∫ p in R', Fe p * K p / y ^ 2) ≤
      (10000 * (Co + Cg) * Ck * (I + 1)) / y ^ 2 * S := by
    refine hieb.trans ?_
    calc
      _ = (2 * Cg * I) * (Ck / y ^ 2 * S) := by ring
      _ ≤ (10000 * (Co + Cg) * (I + 1)) * (Ck / y ^ 2 * S) := by gcongr
      _ = _ := by ring
  change IntegrableOn (fun p => Fo p * K p / y ^ 2) R ∧
    IntegrableOn (fun p => Fe p * K p / y ^ 2) R ∧
    (∫ p in R, Fo p * K p / y ^ 2) ≤ _ ∧ (∫ p in R, Fe p * K p / y ^ 2) ≤ _
  simpa only [IntegrableOn, hrestrict] using And.intro hio (And.intro hie (And.intro hoVal heVal))

/- END FIXED CUTOFF PUBLIC COMPANIONS. -/

end Shao.Probability
