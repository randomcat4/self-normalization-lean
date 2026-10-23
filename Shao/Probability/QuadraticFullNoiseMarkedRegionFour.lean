import Shao.Probability.QuadraticFullNoiseRegionFour
import Shao.Probability.QuadraticFullNoiseGlobalOddEven
import Shao.Probability.SourceKernelAmplitudeFamily
import Shao.Probability.SourceMarkFourierNorms
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Actual closed-cone Region4 two-dimensional marked post-IBP norm integrals.
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

private lemma movingConeNonnegativeIntegral (J : ℝ × ℝ → ℝ)
    (hJ : Measurable J) (hJ0 : ∀ p, 0 ≤ J p) (U : Set ℝ) (hU : MeasurableSet U)
    (a : ℝ) (G : ℝ → ℝ) (hGi : IntegrableOn G U)
    (hJi : ∀ u : ℝ, u ∈ U → IntegrableOn (fun v => J (u, v)) {v : ℝ | |v| ≤ |u| / a})
    (hJb : ∀ u ∈ U, (∫ v in {v : ℝ | |v| ≤ |u| / a}, J (u, v)) ≤ G u) :
    IntegrableOn J {p : ℝ × ℝ | p.1 ∈ U ∧ |p.2| ≤ |p.1| / a} ∧
      (∫ p in {p : ℝ × ℝ | p.1 ∈ U ∧ |p.2| ≤ |p.1| / a}, J p) ≤ ∫ u in U, G u := by
  let R : Set (ℝ × ℝ) := {p | p.1 ∈ U ∧ |p.2| ≤ |p.1| / a}
  let f : ℝ × ℝ → ℝ := R.indicator J
  have hV (u : ℝ) : MeasurableSet {v : ℝ | |v| ≤ |u| / a} :=
    (isClosed_le continuous_abs continuous_const).measurableSet
  have hR : MeasurableSet R :=
    (hU.preimage measurable_fst).inter
      (isClosed_le continuous_snd.abs (continuous_fst.abs.div_const a)).measurableSet
  have hf : Measurable f := hJ.indicator hR
  have hf0 (p : ℝ × ℝ) : 0 ≤ f p := Set.indicator_nonneg (fun p _ => hJ0 p) p
  have hfi (u : ℝ) : Integrable (fun v => f (u, v)) := by
    by_cases hu : u ∈ U
    · have he : (fun v => f (u, v)) =
          ({v : ℝ | |v| ≤ |u| / a}).indicator (fun v => J (u, v)) := by
        funext v
        by_cases hv : |v| ≤ |u| / a <;> simp [f, R, Set.indicator, hu, hv]
      rw [he]
      exact (integrable_indicator_iff (hV u)).mpr (hJi u hu)
    · have he : (fun v => f (u, v)) = 0 := by funext v; simp [f, R, hu]
      rw [he]
      simp
  have hout (u : ℝ) : (∫ v : ℝ, ‖f (u, v)‖) ≤ U.indicator G u := by
    by_cases hu : u ∈ U
    · rw [Set.indicator_of_mem hu]
      have he : (fun v => ‖f (u, v)‖) =
          ({v : ℝ | |v| ≤ |u| / a}).indicator (fun v => J (u, v)) := by
        funext v
        by_cases hv : |v| ≤ |u| / a <;>
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

private lemma tail_envelope (a y : ℝ) (ha : 0 < a) (hy : 0 ≤ y) (k : ℕ) (hk : 3 ≤ k) :
    let H : ℝ → ℝ := fun u => (1 + Real.sqrt (y * |u|)) / |u| ^ k
    IntegrableOn H {u : ℝ | a ≤ |u|} ∧
      (∫ u in {u : ℝ | a ≤ |u|}, H u) ≤
        2 * ((a⁻¹) ^ (k - 1) + Real.sqrt y * (a⁻¹) ^ (k - 2) * Real.sqrt a⁻¹) := by
  dsimp only
  let B0 : ℝ := (a⁻¹) ^ (k - 1)
  let B1 : ℝ := (a⁻¹) ^ (k - 2) * Real.sqrt a⁻¹
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hp0 : -(k : ℝ) < -1 := by linarith
  have hp1 : (1 / 2 : ℝ) - k < -1 := by linarith
  obtain ⟨h0, hi0⟩ := abs_tail_rpow a (-(k : ℝ)) ha hp0
  obtain ⟨h1, hi1⟩ := abs_tail_rpow a ((1 / 2 : ℝ) - k) ha hp1
  have hrepr (u : ℝ) (hu : a ≤ |u|) :
      (1 + Real.sqrt (y * |u|)) / |u| ^ k =
        |u| ^ (-(k : ℝ)) + Real.sqrt y * |u| ^ ((1 / 2 : ℝ) - k) := by
    have hu' : 0 < |u| := ha.trans_le hu
    rw [Real.sqrt_mul hy, Real.rpow_neg hu'.le, Real.rpow_natCast,
      Real.rpow_sub hu', Real.rpow_natCast, ← Real.sqrt_eq_rpow]
    ring
  have hsum := h0.add (h1.const_mul (Real.sqrt y))
  have hmeas : MeasurableSet {u : ℝ | a ≤ |u|} :=
    (isClosed_le continuous_const continuous_abs).measurableSet
  have hint : IntegrableOn (fun u => (1 + Real.sqrt (y * |u|)) / |u| ^ k)
      {u : ℝ | a ≤ |u|} := hsum.congr_fun (fun u hu => (hrepr u hu).symm) hmeas
  have hexp0 : -(k : ℝ) + 1 = -((k - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    norm_num
    ring
  have hexp1 : (1 / 2 : ℝ) - k + 1 = -(((k - 2 : ℕ) : ℝ) + 1 / 2) := by
    rw [Nat.cast_sub (by omega : 2 ≤ k)]
    norm_num
    ring
  have hpow0 : a ^ (-(k : ℝ) + 1) = B0 := by
    rw [hexp0, Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]
  have hpow1 : a ^ ((1 / 2 : ℝ) - k + 1) = B1 := by
    rw [hexp1, Real.rpow_neg_eq_inv_rpow,
      Real.rpow_add (inv_pos.mpr ha), Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have hB0 : 0 ≤ B0 := by dsimp [B0]; positivity
  have hB1 : 0 ≤ B1 := by dsimp [B1]; positivity
  have hb0 : -a ^ (-(k : ℝ) + 1) / (-(k : ℝ) + 1) ≤ B0 := by
    rw [hpow0]
    have heq : -B0 / (-(k : ℝ) + 1) = B0 / ((k : ℝ) - 1) := by
      convert (neg_div_neg_eq B0 ((k : ℝ) - 1)) using 1
      ring
    rw [heq]
    exact div_le_self hB0 (by linarith)
  have hb1 : -a ^ ((1 / 2 : ℝ) - k + 1) / ((1 / 2 : ℝ) - k + 1) ≤ B1 := by
    rw [hpow1]
    have heq : -B1 / ((1 / 2 : ℝ) - k + 1) = B1 / ((k : ℝ) - 3 / 2) := by
      convert (neg_div_neg_eq B1 ((k : ℝ) - 3 / 2)) using 1
      ring
    rw [heq]
    exact div_le_self hB1 (by linarith)
  refine ⟨hint, ?_⟩
  calc
    _ = (∫ u in {u : ℝ | a ≤ |u|}, |u| ^ (-(k : ℝ))) + Real.sqrt y *
        (∫ u in {u : ℝ | a ≤ |u|}, |u| ^ ((1 / 2 : ℝ) - k)) := by
      rw [setIntegral_congr_fun hmeas (fun u hu => hrepr u hu), integral_add h0 (h1.const_mul _),
        integral_const_mul]
    _ ≤ 2 * B0 + Real.sqrt y * (2 * B1) := by
      rw [hi0, hi1]
      exact add_le_add (mul_le_mul_of_nonneg_left hb0 (by norm_num))
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb1 (by norm_num))
          (Real.sqrt_nonneg y))
    _ = _ := by dsimp [B0, B1]; ring

private lemma compare_tail (F : ℝ → ℝ) (A : Set ℝ) (a y c : ℝ) (k : ℕ)
    (ha : 0 < a) (hy : 0 ≤ y) (hc : 0 ≤ c) (hk : 3 ≤ k)
    (hA : MeasurableSet A) (hAB : A ⊆ {u : ℝ | a ≤ |u|})
    (hF : Measurable F) (hF0 : ∀ u, 0 ≤ F u)
    (hbound : ∀ u ∈ A, F u ≤ c * ((1 + Real.sqrt (y * |u|)) / |u| ^ k)) :
    IntegrableOn F A ∧ (∫ u in A, F u) ≤
      2 * c * ((a⁻¹) ^ (k - 1) + Real.sqrt y * (a⁻¹) ^ (k - 2) * Real.sqrt a⁻¹) := by
  obtain ⟨hH, hHval⟩ := tail_envelope a y ha hy k hk
  have henv : IntegrableOn (fun u => c * ((1 + Real.sqrt (y * |u|)) / |u| ^ k))
      {u : ℝ | a ≤ |u|} := hH.const_mul c
  have henvA : IntegrableOn (fun u => c * ((1 + Real.sqrt (y * |u|)) / |u| ^ k)) A :=
    henv.mono_set hAB
  have hint : IntegrableOn F A := by
    refine henvA.mono' hF.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hA] with u hu
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hF0 u)] using hbound u hu
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ u in A, c * ((1 + Real.sqrt (y * |u|)) / |u| ^ k) :=
      setIntegral_mono_on hint henvA hA hbound
    _ ≤ ∫ u in {u : ℝ | a ≤ |u|}, c * ((1 + Real.sqrt (y * |u|)) / |u| ^ k) :=
      setIntegral_mono_set henv (Filter.Eventually.of_forall fun _ => by positivity)
        (Filter.Eventually.of_forall fun u hu => hAB hu)
    _ ≤ c * (2 * ((a⁻¹) ^ (k - 1) + Real.sqrt y * (a⁻¹) ^ (k - 2) * Real.sqrt a⁻¹)) := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hHval hc
    _ = _ := by ring


private lemma movingConeMarkedIntegral (F K : ℝ × ℝ → ℝ)
    (hF : Measurable F) (hK : Measurable K) (hF0 : ∀ p, 0 ≤ F p)
    (hK0 : ∀ p, 0 ≤ K p) (g L : ℝ → ℝ) (hg0 : ∀ u, 0 ≤ g u)
    (U : Set ℝ) (hU : MeasurableSet U) (a y : ℝ)
    (hg : ∀ u ∈ U, ∀ v, |v| ≤ |u| / a → F (u, v) ≤ g u)
    (hKi : ∀ u : ℝ, Integrable (fun v => K (u, v)))
    (hKb : ∀ u : ℝ, (∫ v : ℝ, K (u, v)) ≤ L u)
    (hgi : IntegrableOn (fun u => g u * L u) U) :
    IntegrableOn (fun p => F p * K p / y ^ 2)
      {p : ℝ × ℝ | p.1 ∈ U ∧ |p.2| ≤ |p.1| / a} ∧
      (∫ p in {p : ℝ × ℝ | p.1 ∈ U ∧ |p.2| ≤ |p.1| / a}, F p * K p / y ^ 2) ≤
        (1 / y ^ 2) * (∫ u in U, g u * L u) := by
  let J : ℝ × ℝ → ℝ := fun p => F p * K p / y ^ 2
  have hJi (u : ℝ) (hu : u ∈ U) : IntegrableOn (fun v => J (u, v)) {v : ℝ | |v| ≤ |u| / a} := by
    refine ((hKi u).integrableOn.const_mul (g u / y ^ 2)).mono'
      ((hF.mul hK).div_const (y ^ 2) |>.comp (measurable_const.prodMk measurable_id)
        |>.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem (isClosed_le continuous_abs continuous_const).measurableSet] with v hv
    have hn : 0 ≤ J (u, v) := by dsimp [J]; exact div_nonneg (mul_nonneg (hF0 _) (hK0 _)) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    change F (u, v) * K (u, v) / y ^ 2 ≤ _
    calc
      _ ≤ g u * K (u, v) / y ^ 2 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hg u hu v hv) (hK0 _)) (sq_nonneg _)
      _ = _ := by ring
  obtain ⟨hi, hb⟩ := movingConeNonnegativeIntegral J ((hF.mul hK).div_const _) (fun p => by
    dsimp [J]; exact div_nonneg (mul_nonneg (hF0 _) (hK0 _)) (sq_nonneg _)) U hU a
    (fun u => (1 / y ^ 2) * (g u * L u)) (hgi.const_mul _) hJi (by
      intro u hu
      calc
        _ ≤ ∫ v in {v : ℝ | |v| ≤ |u| / a}, g u / y ^ 2 * K (u, v) :=
          setIntegral_mono_on (hJi u hu) ((hKi u).integrableOn.const_mul _)
            (isClosed_le continuous_abs continuous_const).measurableSet (fun v hv => by
              dsimp [J]
              calc
                _ ≤ g u * K (u, v) / y ^ 2 := div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_right (hg u hu v hv) (hK0 _)) (sq_nonneg _)
                _ = _ := by ring)
        _ = g u / y ^ 2 * (∫ v in {v : ℝ | |v| ≤ |u| / a}, K (u, v)) := integral_const_mul _ _
        _ ≤ g u / y ^ 2 * (∫ v : ℝ, K (u, v)) := mul_le_mul_of_nonneg_left
          (setIntegral_le_integral (hKi u) (Filter.Eventually.of_forall fun v => hK0 _))
          (div_nonneg (hg0 u) (sq_nonneg _))
        _ ≤ g u / y ^ 2 * L u := mul_le_mul_of_nonneg_left (hKb u)
          (div_nonneg (hg0 u) (sq_nonneg _))
        _ = _ := by ring)
  refine ⟨hi, ?_⟩
  simpa only [integral_const_mul] using hb

private lemma actualGlobalMarkedKernelData :
    ∃ C : ℝ, 0 < C ∧ ∀ y w sigma : ℝ, 0 < y → |w| ≤ y / 16 → |sigma| = 1 →
      let a : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r + sigma * w / y) ^ 2
      let B : ℝ × ℝ → ℂ := fun p => ∫ r : ℝ,
        ((a r * Real.sin (p.1 * (y * Real.sqrt r + sigma * w)) : ℝ) : ℂ) *
          Complex.exp (-(((p.2 * r : ℝ) : ℂ) * Complex.I))
      Measurable (fun p => ‖B p‖) ∧
        (∀ u : ℝ, Integrable (fun v => ‖B (u, v)‖)) ∧
        ∀ u : ℝ, (∫ v : ℝ, ‖B (u, v)‖) ≤ C * (1 + Real.sqrt (y * |u|)) := by
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
  refine ⟨(actualMarkedSine_continuous a hfa.1.continuous hac y (sigma * w)).measurable.norm,
    fun u => (hmark M hM.le a hfa.1 hfa.2.1 haM y u (sigma * w) hy.le hsw).1, ?_⟩
  intro u
  exact (hmark M hM.le a hfa.1 hfa.2.1 haM y u (sigma * w) hy.le hsw).2.2.1.trans
    (mul_le_mul_of_nonneg_left (min_le_right (y * |u|) (1 + Real.sqrt (y * |u|))) (by positivity))

theorem sourceTruncation_odd_even_fullNoise_region4_actual_marked_postIBP :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun z : ℝ => z ^ 2) ν0 →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν0) = 1 →
          (∫ z : ℝ, z ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 2 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            ∀ i : ℕ, i ≤ n → ∀ h kappa L2 y w sigma : ℝ,
              epsilon / (1 + x) ≤ h → 0 < kappa → 20 ≤ L2 →
                1 ≤ kappa * Real.sqrt L2 → 0 < y → y ≤ 2 →
                |w| ≤ y / 16 → |sigma| = 1 →
                let ρ : Measure ℝ :=
                  ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
                let m : ℕ := n - i
                let T : ℝ := (m : ℝ) * (∫ z : ℝ, z ^ 2 ∂ρ)
                let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
                let b : ℝ := gamma / kappa
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
                let R : Set (ℝ × ℝ) := {p | kappa / gamma ≤ |p.1| ∧ |p.2| ≤ |p.1| / (4 * h)}
                let Iodd : ℝ × ℝ → ℝ := fun p =>
                  ‖deriv (fun r : ℝ => deriv (fun t : ℝ => D t p.2) r) p.1‖ *
                    ‖B p.1 p.2‖ / y ^ 2
                let Ieven : ℝ × ℝ → ℝ := fun p =>
                  ‖deriv (fun r : ℝ => deriv (fun t : ℝ => W t p.2) r) p.1‖ *
                    ‖B p.1 p.2‖ / y ^ 2
                IntegrableOn Iodd R ∧ IntegrableOn Ieven R ∧
                  (∫ p in R, Iodd p) ≤ C / y ^ 2 / T ^ 5 * (b ^ 11 + Real.sqrt y * b ^ 10 * Real.sqrt b) ∧
                  (∫ p in R, Ieven p) ≤ C / y ^ 2 / T ^ 5 * (b ^ 10 + Real.sqrt y * b ^ 9 * Real.sqrt b) := by
  obtain ⟨Cg, hCg, hcone⟩ := sourceTruncation_odd_even_fullNoise_highFrequency_derivatives
  obtain ⟨Ck, hCk, hkernel⟩ := actualGlobalMarkedKernelData
  obtain ⟨Cglobal, hCglobal, hglobal⟩ := sourceTruncation_odd_even_fullNoise_global_derivatives
  refine ⟨2 * Cg * Ck, by positivity, ?_⟩
  intro ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h kappa L2 y w sigma
    hh hk hL2 hkL2 hy hy2 hw hsigma
  dsimp only
  intro hTL hTy
  let := hp0
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
  let m : ℕ := n - i
  let T : ℝ := (m : ℝ) * (∫ z : ℝ, z ^ 2 ∂ρ)
  let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
  let b : ℝ := gamma / kappa
  let U : Set ℝ := {u | kappa / gamma ≤ |u|}
  let R : Set (ℝ × ℝ) := {p | p.1 ∈ U ∧ |p.2| ≤ |p.1| / (4 * h)}
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
  let go : ℝ → ℝ := fun u => Cg / (T ^ 5 * |u| ^ 12)
  let ge : ℝ → ℝ := fun u => Cg / (T ^ 5 * |u| ^ 11)
  let L : ℝ → ℝ := fun u => Ck * (1 + Real.sqrt (y * |u|))
  change IntegrableOn (fun p => Fo p * K p / y ^ 2) R ∧
    IntegrableOn (fun p => Fe p * K p / y ^ 2) R ∧
    (∫ p in R, Fo p * K p / y ^ 2) ≤ (2 * Cg * Ck) / y ^ 2 / T ^ 5 *
      (b ^ 11 + Real.sqrt y * b ^ 10 * Real.sqrt b) ∧
    (∫ p in R, Fe p * K p / y ^ 2) ≤ (2 * Cg * Ck) / y ^ 2 / T ^ 5 *
      (b ^ 10 + Real.sqrt y * b ^ 9 * Real.sqrt b)
  have hg : 0 < gamma := (Shao.sourceTruncation_gamma_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget).2.1
  have hb : 0 < b := div_pos hg hk
  have ha : 0 < kappa / gamma := div_pos hk hg
  have hhpos : 0 < h := (div_pos he (by linarith : 0 < 1 + x)).trans_le hh
  have hT : 0 < T := (mul_pos (by linarith : 0 < L2) (sq_pos_of_pos hg)).trans_le hTL
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
  have hpoint := hcone ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h kappa L2 hh hk hL2 hkL2 hTL
  have hu0 (u : ℝ) (hu : u ∈ U) : u ≠ 0 := by
    have hau : 0 < |u| := ha.trans_le hu
    exact abs_pos.mp hau
  have ho (u : ℝ) (hu : u ∈ U) (v : ℝ) (hv : |v| ≤ |u| / (4 * h)) : Fo (u, v) ≤ go u :=
    (hpoint u v (hu0 u hu) hu hv).2.2.2.2.1
  have heven (u : ℝ) (hu : u ∈ U) (v : ℝ) (hv : |v| ≤ |u| / (4 * h)) : Fe (u, v) ≤ ge u :=
    (hpoint u v (hu0 u hu) hu hv).2.2.2.2.2
  have hU : MeasurableSet U := (isClosed_le continuous_const continuous_abs).measurableSet
  obtain ⟨hK, hKi, hKb⟩ := hkernel y w sigma hy hw hsigma
  have hgo0 (u : ℝ) : 0 ≤ go u := by dsimp [go]; positivity
  have hge0 (u : ℝ) : 0 ≤ ge u := by dsimp [ge]; positivity
  have hL0 (u : ℝ) : 0 ≤ L u := by dsimp [L]; positivity
  obtain ⟨hgo, hgob⟩ := compare_tail (fun u => go u * L u) U (kappa / gamma) y
    (Cg * Ck / T ^ 5) 12 ha hy.le (by positivity) (by norm_num) hU (fun _ hu => hu)
    (by dsimp [go, L]; fun_prop) (fun u => mul_nonneg (hgo0 u) (hL0 u)) (by
      intro u hu
      dsimp [go, L]
      exact le_of_eq (by ring))
  obtain ⟨hge, hgeb⟩ := compare_tail (fun u => ge u * L u) U (kappa / gamma) y
    (Cg * Ck / T ^ 5) 11 ha hy.le (by positivity) (by norm_num) hU (fun _ hu => hu)
    (by dsimp [ge, L]; fun_prop) (fun u => mul_nonneg (hge0 u) (hL0 u)) (by
      intro u hu
      dsimp [ge, L]
      exact le_of_eq (by ring))
  have hbinv : (kappa / gamma)⁻¹ = b := by simp [b, inv_div]
  norm_num only at hgob hgeb
  rw [hbinv] at hgob hgeb
  obtain ⟨hio, hiob⟩ := movingConeMarkedIntegral Fo K hFo hK (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) go L hgo0 U hU (4 * h) y ho hKi hKb hgo
  obtain ⟨hie, hieb⟩ := movingConeMarkedIntegral Fe K hFe hK (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) ge L hge0 U hU (4 * h) y heven hKi hKb hge
  refine ⟨hio, hie, hiob.trans ?_, hieb.trans ?_⟩
  · calc
      _ ≤ 1 / y ^ 2 * (2 * (Cg * Ck / T ^ 5) *
          (b ^ 11 + Real.sqrt y * b ^ 10 * Real.sqrt b)) :=
        mul_le_mul_of_nonneg_left hgob (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ 1 / y ^ 2 * (2 * (Cg * Ck / T ^ 5) *
          (b ^ 10 + Real.sqrt y * b ^ 9 * Real.sqrt b)) :=
        mul_le_mul_of_nonneg_left hgeb (by positivity)
      _ = _ := by ring

end Shao.Probability
