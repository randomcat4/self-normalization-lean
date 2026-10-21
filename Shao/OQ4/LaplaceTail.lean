import Shao.OQ4.IntervalConcentration
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! A positive-part Laplace payment and its strict-tail representation. -/

namespace Shao.OQ4

open MeasureTheory ProbabilityTheory Set
open scoped Topology

noncomputable def positiveLaplace (L x : ℝ) : ℝ := 1 - Real.exp (-max x 0 / L)

noncomputable def laplacePayment (μ : Measure ℝ) (L : ℝ) : ℝ := ∫ x, positiveLaplace L x ∂μ

noncomputable def laplaceWeight (L u : ℝ) : ℝ := L⁻¹ * Real.exp (-u / L)

theorem positiveLaplace_bounds {L : ℝ} (hL : 0 < L) (x : ℝ) :
    0 ≤ positiveLaplace L x ∧ positiveLaplace L x ≤ 1 := by
  have he : Real.exp (-max x 0 / L) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (le_max_right x 0)) hL.le)
  constructor <;> dsimp [positiveLaplace]
  · linarith
  · linarith [Real.exp_pos (-max x 0 / L)]

theorem integrable_positiveLaplace (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {L : ℝ} (hL : 0 < L) : Integrable (positiveLaplace L) μ := by
  apply Integrable.of_bound (show AEStronglyMeasurable (positiveLaplace L) μ by
    apply Continuous.aestronglyMeasurable
    unfold positiveLaplace
    fun_prop) 1
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (positiveLaplace_bounds hL x).1]
    exact (positiveLaplace_bounds hL x).2

theorem laplacePayment_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {L : ℝ} (hL : 0 < L) : 0 ≤ laplacePayment μ L ∧ laplacePayment μ L ≤ 1 := by
  constructor
  · exact integral_nonneg fun x => (positiveLaplace_bounds hL x).1
  · calc
      _ ≤ ∫ _x, (1 : ℝ) ∂μ := integral_mono (integrable_positiveLaplace μ hL) (integrable_const 1)
        (fun x => (positiveLaplace_bounds hL x).2)
      _ = 1 := by simp

theorem laplaceWeight_nonneg {L : ℝ} (hL : 0 < L) (u : ℝ) : 0 ≤ laplaceWeight L u := by
  unfold laplaceWeight
  positivity

theorem measurable_strictTail (μ : Measure ℝ) : Measurable (fun u => μ.real (Ioi u)) := by
  apply Measurable.ennreal_toReal
  exact Antitone.measurable fun a b hab => measure_mono (Ioi_subset_Ioi hab)

theorem integrable_laplaceWeight {L : ℝ} (hL : 0 < L) :
    IntegrableOn (laplaceWeight L) (Ioi 0) := by
  have hi := (integrableOn_exp_mul_Ioi (a := -L⁻¹) (neg_neg_of_pos (inv_pos.mpr hL)) 0).const_mul L⁻¹
  have hf : laplaceWeight L = fun u => L⁻¹ * Real.exp (-L⁻¹ * u) := by
    ext u
    unfold laplaceWeight
    congr 1
    ring_nf
  rw [hf]
  exact hi

theorem integral_laplaceWeight {L : ℝ} (hL : 0 < L) :
    ∫ u in Ioi 0, laplaceWeight L u = 1 := by
  unfold laplaceWeight
  rw [integral_const_mul]
  have he := integral_exp_mul_Ioi (a := -L⁻¹) (neg_neg_of_pos (inv_pos.mpr hL)) 0
  simp only [mul_zero, Real.exp_zero] at he
  have hf : (fun u : ℝ => Real.exp (-u / L)) = (fun u => Real.exp (-L⁻¹ * u)) := by
    ext u; congr 1; ring_nf
  rw [hf, he]
  field_simp

theorem integrable_laplaceTail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {L : ℝ} (hL : 0 < L) :
    IntegrableOn (fun u => laplaceWeight L u * μ.real (Ioi u)) (Ioi 0) := by
  refine (integrable_laplaceWeight hL).mono' ?_ ?_
  · exact ((show Measurable (laplaceWeight L) by unfold laplaceWeight; fun_prop).mul
      (measurable_strictTail μ)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (laplaceWeight_nonneg hL u) (by positivity))]
      exact mul_le_of_le_one_right (laplaceWeight_nonneg hL u) (by
        exact (measureReal_mono (μ := μ) (subset_univ (Ioi u))).trans_eq (by simp))


theorem laplaceWeight_primitive {L : ℝ} (_hL : 0 < L) (v : ℝ) :
    ∫ u in 0..v, laplaceWeight L u = 1 - Real.exp (-v / L) := by
  have hd (u : ℝ) : HasDerivAt (fun u : ℝ => 1 - Real.exp (-u / L)) (laplaceWeight L u) u := by
    have hd0 := (((hasDerivAt_id u).neg.div_const L).exp.const_sub 1)
    have he : -(Real.exp (-u / L) * (-1 / L)) = laplaceWeight L u := by
      unfold laplaceWeight
      ring_nf
    dsimp only [Pi.neg_apply, id_eq] at hd0
    rw [he] at hd0
    exact hd0
  have hi : IntervalIntegrable (laplaceWeight L) volume 0 v := by
    apply Continuous.intervalIntegrable
    unfold laplaceWeight
    fun_prop
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hi

theorem laplacePayment_eq_strictTail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {L : ℝ} (hL : 0 < L) :
    laplacePayment μ L = ∫ u in Ioi 0, laplaceWeight L u * μ.real (Ioi u) := by
  have hk := lintegral_comp_eq_lintegral_meas_lt_mul μ
    (f := fun x : ℝ => max x 0) (g := laplaceWeight L)
    (Filter.Eventually.of_forall fun x => le_max_right x 0)
    (show AEMeasurable (fun x : ℝ => max x 0) μ by fun_prop)
    (fun t _ => (show Continuous (laplaceWeight L) by unfold laplaceWeight; fun_prop).intervalIntegrable _ _)
    (Filter.Eventually.of_forall (laplaceWeight_nonneg hL))
  have he : (∫⁻ x, ENNReal.ofReal (positiveLaplace L x) ∂μ) =
      ∫⁻ u in Ioi 0, ENNReal.ofReal (laplaceWeight L u * μ.real (Ioi u)) := by
    calc
      _ = ∫⁻ x, ENNReal.ofReal (∫ u in 0..max x 0, laplaceWeight L u) ∂μ := by
        apply lintegral_congr
        intro x
        rw [laplaceWeight_primitive hL]
        rfl
      _ = _ := hk
      _ = _ := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro u hu
        change 0 < u at hu
        dsimp only
        have hs : {x : ℝ | u < max x 0} = Ioi u := by
          ext x
          simp only [mem_ofPred_eq, mem_Ioi, lt_max_iff]
          simp [not_lt.mpr (le_of_lt hu)]
        rw [hs, ENNReal.ofReal_mul (laplaceWeight_nonneg hL u),
          measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)]
        exact mul_comm _ _
  unfold laplacePayment
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => (positiveLaplace_bounds hL x).1)
    (integrable_positiveLaplace μ hL).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun u => mul_nonneg (laplaceWeight_nonneg hL u) (by positivity))
      (integrable_laplaceTail μ hL).aestronglyMeasurable, he]

theorem standardGaussian_positive_mass : (gaussianReal 0 1).real (Ioi 0) = 1 / 2 := by
  let γ := gaussianReal 0 1
  have : NullSingletonClass γ := nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)
  have hn : γ.real (Ioi 0) = γ.real (Iio 0) := by
    have hmap : γ.map (fun x : ℝ => -x) = γ := by
      simpa [γ] using (gaussianReal_map_neg (μ := 0) (v := 1))
    calc
      γ.real (Ioi 0) = (γ.map (fun x : ℝ => -x)).real (Ioi 0) := by rw [hmap]
      _ = γ.real (Iio 0) := by
        apply congrArg ENNReal.toReal
        rw [Measure.map_apply (by fun_prop) measurableSet_Ioi]
        congr 1
        ext x
        simp
  have hne : ∀ᵐ x ∂γ, x ≠ 0 := by
    simp [ae_iff]
  have he : γ.real (Iic 0) = γ.real (Iio 0) := by
    apply measureReal_congr
    filter_upwards [hne] with x hx
    simp only [mem_Iic, mem_Iio]
    simp [le_iff_lt_or_eq, hx]
  have ht := measureReal_add_measureReal_compl (μ := γ) (s := Iic 0) measurableSet_Iic
  simp only [compl_Iic, probReal_univ] at ht
  change γ.real (Ioi 0) = 1 / 2
  linarith

theorem standardNormalCDF_zero : standardNormalCDF 0 = 1 / 2 := by
  rw [standardNormalCDF_eq_real]
  have ht := measureReal_add_measureReal_compl (μ := gaussianReal 0 1) (s := Iic 0) measurableSet_Iic
  simp only [compl_Iic, probReal_univ, standardGaussian_positive_mass] at ht
  linarith


theorem integrable_mul_laplaceWeight {L : ℝ} (hL : 0 < L) :
    IntegrableOn (fun u => u * laplaceWeight L u) (Ioi 0) := by
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := L⁻¹)
    (by norm_num) (by norm_num) (inv_pos.mpr hL)
  simp only [Real.rpow_one] at hi
  have hf : (fun u => u * laplaceWeight L u) = (fun u => L⁻¹ * (u * Real.exp (-L⁻¹ * u))) := by
    ext u
    unfold laplaceWeight
    rw [show -u / L = -L⁻¹ * u by ring_nf]
    ring_nf
  rw [hf]
  exact hi.const_mul L⁻¹

theorem integral_mul_laplaceWeight {L : ℝ} (hL : 0 < L) :
    ∫ u in Ioi 0, u * laplaceWeight L u = L := by
  have hf : (fun u => u * laplaceWeight L u) = (fun u => L⁻¹ * (u * Real.exp (-(L⁻¹ * u)))) := by
    ext u
    unfold laplaceWeight
    rw [show -u / L = -(L⁻¹ * u) by ring_nf]
    ring_nf
  rw [hf, integral_const_mul]
  have hg := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := L⁻¹) (by norm_num) (inv_pos.mpr hL)
  have hGamma : Real.Gamma 2 = 1 := by simp
  norm_num [hGamma, Real.rpow_two] at hg
  rw [hg]
  field_simp

/-- The actual standardized CDF input gives a bound on the strict unscaled tail. -/
theorem strictTail_lower_bound_of_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (q : ℕ) (hq : 1 ≤ q) (C_BE β : ℝ)
    (hCDF : ∀ x, |μ.real {y : ℝ | y / Real.sqrt q ≤ x} - standardNormalCDF x| ≤
      C_BE * β / Real.sqrt q) (u : ℝ) (hu : 0 ≤ u) :
    1 / 2 - u / Real.sqrt q - C_BE * β / Real.sqrt q ≤ μ.real (Ioi u) := by
  have hs : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq))
  have he := (abs_le.mp (hCDF (u / Real.sqrt q))).2
  have hset : {y : ℝ | y / Real.sqrt q ≤ u / Real.sqrt q} = Iic u := by
    ext y
    exact div_le_div_iff_of_pos_right hs
  rw [hset] at he
  have hLip := (le_abs_self (standardNormalCDF (u / Real.sqrt q) - standardNormalCDF 0)).trans
    (standardNormalCDF_lipschitz (u / Real.sqrt q) 0)
  rw [standardNormalCDF_zero, sub_zero, abs_of_nonneg (div_nonneg hu hs.le)] at hLip
  have ht := measureReal_add_measureReal_compl (μ := μ) (s := Iic u) measurableSet_Iic
  simp only [compl_Iic, probReal_univ] at ht
  linarith

/-- S1 from an explicit Berry--Esseen type input; the displayed lower bound may be negative. -/
theorem laplacePayment_lower_bound_of_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (q : ℕ) (hq : 1 ≤ q) (C_BE β L : ℝ) (hC : 0 ≤ C_BE) (hβ : 1 ≤ β) (hβL : β ≤ L)
    (hCDF : ∀ x, |μ.real {y : ℝ | y / Real.sqrt q ≤ x} - standardNormalCDF x| ≤
      C_BE * β / Real.sqrt q) :
    1 / 2 - (1 + C_BE) * L / Real.sqrt q ≤ laplacePayment μ L := by
  have hL : 0 < L := by linarith
  have hs : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq))
  let ε := C_BE * β / Real.sqrt q
  have hf : (fun u => laplaceWeight L u * (1 / 2 - u / Real.sqrt q - ε)) =
      (fun u => (1 / 2 - ε) * laplaceWeight L u - (Real.sqrt q)⁻¹ * (u * laplaceWeight L u)) := by
    ext u
    ring_nf
  have hi : IntegrableOn (fun u => laplaceWeight L u * (1 / 2 - u / Real.sqrt q - ε)) (Ioi 0) := by
    rw [hf]
    exact ((integrable_laplaceWeight hL).const_mul _).sub ((integrable_mul_laplaceWeight hL).const_mul _)
  have he : (∫ u in Ioi 0, laplaceWeight L u * (1 / 2 - u / Real.sqrt q - ε)) =
      1 / 2 - ε - L / Real.sqrt q := by
    rw [hf, integral_sub ((integrable_laplaceWeight hL).const_mul _)
      ((integrable_mul_laplaceWeight hL).const_mul _), integral_const_mul, integral_const_mul,
      integral_laplaceWeight hL, integral_mul_laplaceWeight hL, mul_one]
    ring_nf
  have hb := integral_mono_ae hi (integrable_laplaceTail μ hL) (show
      ∀ᵐ u ∂volume.restrict (Ioi 0), laplaceWeight L u * (1 / 2 - u / Real.sqrt q - ε) ≤
        laplaceWeight L u * μ.real (Ioi u) from by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_le_mul_of_nonneg_left (strictTail_lower_bound_of_cdf μ q hq C_BE β hCDF u hu.le)
      (laplaceWeight_nonneg hL u))
  rw [he, ← laplacePayment_eq_strictTail μ hL] at hb
  have hβmul := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hβL hC) hs.le
  have hsplit : (1 + C_BE) * L / Real.sqrt q = L / Real.sqrt q + C_BE * L / Real.sqrt q := by ring_nf
  rw [hsplit]
  dsimp [ε] at hb
  linarith

noncomputable def finiteSumLaplacePayment (ν : Measure ℝ) (q : ℕ) (L : ℝ) : ℝ :=
  ∫ a : Shao.Path q, positiveLaplace L (Shao.prefixSum a q) ∂Measure.pi (fun _ : Fin q => ν)

theorem iid_integrable_positiveLaplace (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (q : ℕ) {L : ℝ} (hL : 0 < L) :
    Integrable (fun a : Shao.Path q => positiveLaplace L (Shao.prefixSum a q))
      (Measure.pi (fun _ : Fin q => ν)) := by
  apply Integrable.of_bound (show AEStronglyMeasurable
    (fun a : Shao.Path q => positiveLaplace L (Shao.prefixSum a q)) (Measure.pi (fun _ : Fin q => ν)) by
      apply Measurable.aestronglyMeasurable
      exact (show Measurable (positiveLaplace L) by unfold positiveLaplace; fun_prop).comp
        (Shao.measurable_prefixSum q)) 1
  exact Filter.Eventually.of_forall fun a => by
    rw [Real.norm_eq_abs, abs_of_nonneg (positiveLaplace_bounds hL _).1]
    exact (positiveLaplace_bounds hL _).2

theorem finiteSumLaplacePayment_bounds (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (q : ℕ) {L : ℝ} (hL : 0 < L) :
    0 ≤ finiteSumLaplacePayment ν q L ∧ finiteSumLaplacePayment ν q L ≤ 1 := by
  constructor
  · exact integral_nonneg fun a => (positiveLaplace_bounds hL _).1
  · calc
      _ ≤ ∫ _a : Shao.Path q, (1 : ℝ) ∂Measure.pi (fun _ : Fin q => ν) :=
        integral_mono (iid_integrable_positiveLaplace ν q hL) (integrable_const 1)
          (fun a => (positiveLaplace_bounds hL _).2)
      _ = 1 := by simp

theorem finiteSumLaplacePayment_lower_bound_of_cdf (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (q : ℕ) (hq : 1 ≤ q) (C_BE β L : ℝ) (hC : 0 ≤ C_BE) (hβ : 1 ≤ β) (hβL : β ≤ L)
    (hCDF : ∀ x, |(Measure.pi (fun _ : Fin q => ν)).real
      {a : Shao.Path q | Shao.prefixSum a q / Real.sqrt q ≤ x} - standardNormalCDF x| ≤
        C_BE * β / Real.sqrt q) :
    1 / 2 - (1 + C_BE) * L / Real.sqrt q ≤ finiteSumLaplacePayment ν q L := by
  let law : Measure (Shao.Path q) := Measure.pi (fun _ : Fin q => ν)
  let X : Shao.Path q → ℝ := fun a => Shao.prefixSum a q
  have hX : Measurable X := Shao.measurable_prefixSum q
  let μ := law.map X
  have : IsProbabilityMeasure μ := by
    constructor
    change (law.map X) univ = 1
    rw [Measure.map_apply hX MeasurableSet.univ]
    simp [law]
  have hCDF' : ∀ x, |μ.real {y : ℝ | y / Real.sqrt q ≤ x} - standardNormalCDF x| ≤
      C_BE * β / Real.sqrt q := by
    intro x
    change |((law.map X) {y : ℝ | y / Real.sqrt q ≤ x}).toReal - standardNormalCDF x| ≤ _
    have hm : MeasurableSet {y : ℝ | y / Real.sqrt q ≤ x} :=
      measurableSet_le (show Measurable (fun y : ℝ => y / Real.sqrt q) by fun_prop) measurable_const
    rw [Measure.map_apply hX hm]
    exact hCDF x
  have hL : 0 < L := by linarith
  have he : laplacePayment μ L = finiteSumLaplacePayment ν q L := by
    unfold laplacePayment finiteSumLaplacePayment
    exact integral_map hX.aemeasurable (integrable_positiveLaplace μ hL).aestronglyMeasurable
  rw [← he]
  exact laplacePayment_lower_bound_of_cdf μ q hq C_BE β L hC hβ hβL hCDF'

end Shao.OQ4
