import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Finite normalization of the actual closed truncated even energy weight. -/

namespace Shao.OQ4

open MeasureTheory

noncomputable def energyWeight (h s x : ℝ) : ℝ :=
  if |x| ≤ 2 * h then Real.exp (s * x ^ 2 / h ^ 2) else 0

noncomputable def energyNormalizer (ν : Measure ℝ) (h s : ℝ) : ℝ :=
  ∫ x : ℝ, energyWeight h s x ∂ν

noncomputable def energyNormalizerErrorConstant (T : ℝ) : ℝ :=
  1 / 8 + T / 2 + Real.exp (4 * T) * T ^ 2

theorem energyWeight_measurable (h s : ℝ) : Measurable (energyWeight h s) := by
  exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
    (by fun_prop) measurable_const

theorem energyWeight_nonneg (h s x : ℝ) : 0 ≤ energyWeight h s x := by
  unfold energyWeight
  split_ifs <;> positivity

theorem energyWeight_at_zero (h s : ℝ) (hh : 0 ≤ h) : energyWeight h s 0 = 1 := by
  simp [energyWeight, hh]

theorem energyNormalizer_at_zero (ν : Measure ℝ) [IsFiniteMeasure ν] (h : ℝ) :
    energyNormalizer ν h 0 = ν.real {x : ℝ | |x| ≤ 2 * h} := by
  have hB : MeasurableSet {x : ℝ | |x| ≤ 2 * h} :=
    measurableSet_le (by fun_prop) measurable_const
  simpa [energyNormalizer, energyWeight, Set.indicator] using
    (integral_indicator_const (μ := ν) (1 : ℝ) hB)

theorem energy_argument_bounds (T h s x : ℝ) (hT : 0 ≤ T) (hh : 0 < h)
    (hs : |s| ≤ T) (hx : |x| ≤ 2 * h) :
    -4 * T ≤ s * x ^ 2 / h ^ 2 ∧ s * x ^ 2 / h ^ 2 ≤ 4 * T := by
  have hh2 : 0 < h ^ 2 := sq_pos_of_pos hh
  have hx2 : x ^ 2 ≤ 4 * h ^ 2 := by
    have hp := pow_le_pow_left₀ (abs_nonneg x) hx 2
    nlinarith [sq_abs x]
  have hq0 : 0 ≤ x ^ 2 / h ^ 2 := div_nonneg (sq_nonneg x) hh2.le
  have hq4 : x ^ 2 / h ^ 2 ≤ 4 := (div_le_iff₀ hh2).2 (by linarith)
  have htq := mul_le_mul_of_nonneg_left hq4 hT
  have hlo := mul_le_mul_of_nonneg_right (abs_le.mp hs).1 hq0
  have hup := mul_le_mul_of_nonneg_right (abs_le.mp hs).2 hq0
  rw [show s * x ^ 2 / h ^ 2 = s * (x ^ 2 / h ^ 2) by ring]
  constructor <;> nlinarith

theorem energyWeight_le (T h s x : ℝ) (hT : 0 ≤ T) (hh : 0 < h) (hs : |s| ≤ T) :
    energyWeight h s x ≤ Real.exp (4 * T) := by
  unfold energyWeight
  split_ifs with hx
  · exact Real.exp_le_exp.mpr (energy_argument_bounds T h s x hT hh hs hx).2
  · positivity

theorem energyWeight_lower_indicator (T h s x : ℝ) (hT : 0 ≤ T) (hh : 0 < h)
    (hs : |s| ≤ T) :
    (if |x| ≤ 2 * h then Real.exp (-4 * T) else 0) ≤ energyWeight h s x := by
  unfold energyWeight
  split_ifs with hx
  · exact Real.exp_le_exp.mpr (energy_argument_bounds T h s x hT hh hs hx).1
  · exact le_rfl

theorem energyWeight_integrable (ν : Measure ℝ) [IsFiniteMeasure ν]
    (T h s : ℝ) (hT : 0 ≤ T) (hh : 0 < h) (hs : |s| ≤ T) :
    Integrable (energyWeight h s) ν := by
  apply Integrable.of_bound (energyWeight_measurable h s).aestronglyMeasurable (Real.exp (4 * T))
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (energyWeight_nonneg h s x)] using
      energyWeight_le T h s x hT hh hs

/-- All four pointwise payments use only a positive cutoff and the cubic envelope. -/
theorem energy_third_moment_pointwise (h x : ℝ) (hh : 0 < h) :
    (if 2 * h < |x| then (1 : ℝ) else 0) ≤ |x| ^ 3 / (8 * h ^ 3) ∧
    (if 2 * h < |x| then |x| else 0) ≤ |x| ^ 3 / (4 * h ^ 2) ∧
    (if 2 * h < |x| then x ^ 2 else 0) ≤ |x| ^ 3 / (2 * h) ∧
    (if |x| ≤ 2 * h then x ^ 4 else 0) ≤ 2 * h * |x| ^ 3 := by
  have hu : 0 ≤ |x| := abs_nonneg x
  by_cases hx : 2 * h < |x|
  · have hB : ¬ |x| ≤ 2 * h := not_le.mpr hx
    have hp3 := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * h) hx.le 3
    have hp2 := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * h) hx.le 2
    have hm2 := mul_le_mul_of_nonneg_right hp2 hu
    have hm1 := mul_le_mul_of_nonneg_right hx.le (sq_nonneg |x|)
    simp only [hx, hB, ite_true, ite_false]
    refine ⟨(le_div_iff₀ (by positivity : 0 < 8 * h ^ 3)).2 ?_,
      (le_div_iff₀ (by positivity : 0 < 4 * h ^ 2)).2 ?_,
      (le_div_iff₀ (by positivity : 0 < 2 * h)).2 ?_, by positivity⟩
    · nlinarith
    · nlinarith
    · nlinarith [sq_abs x]
  · have hB : |x| ≤ 2 * h := le_of_not_gt hx
    have hm := mul_le_mul_of_nonneg_right hB (pow_nonneg hu 3)
    have hf : |x| ^ 4 = x ^ 4 := by
      calc
        _ = (|x| ^ 2) ^ 2 := by ring
        _ = (x ^ 2) ^ 2 := by rw [sq_abs]
        _ = _ := by ring
    simp only [hx, hB, ite_true, ite_false]
    refine ⟨by positivity, by positivity, by positivity, ?_⟩
    nlinarith

/-- The three displayed truncated moments are genuinely integrable, with all four payments. -/
theorem energy_third_moment_payments (ν : Measure ℝ) [IsFiniteMeasure ν]
    (h : ℝ) (hh : 0 < h) (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν) :
    Integrable (fun x : ℝ => if 2 * h < |x| then |x| else 0) ν ∧
    Integrable (fun x : ℝ => if 2 * h < |x| then x ^ 2 else 0) ν ∧
    Integrable (fun x : ℝ => if |x| ≤ 2 * h then x ^ 4 else 0) ν ∧
    ν.real {x : ℝ | 2 * h < |x|} ≤ (∫ x : ℝ, |x| ^ 3 ∂ν) / (8 * h ^ 3) ∧
    (∫ x : ℝ, if 2 * h < |x| then |x| else 0 ∂ν) ≤
      (∫ x : ℝ, |x| ^ 3 ∂ν) / (4 * h ^ 2) ∧
    (∫ x : ℝ, if 2 * h < |x| then x ^ 2 else 0 ∂ν) ≤
      (∫ x : ℝ, |x| ^ 3 ∂ν) / (2 * h) ∧
    (∫ x : ℝ, if |x| ≤ 2 * h then x ^ 4 else 0 ∂ν) ≤
      2 * h * (∫ x : ℝ, |x| ^ 3 ∂ν) := by
  have hD : MeasurableSet {x : ℝ | 2 * h < |x|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hi : Integrable (fun x : ℝ => if 2 * h < |x| then (1 : ℝ) else 0) ν := by
    convert (integrable_const (μ := ν) (1 : ℝ)).indicator hD using 1
    ext x
    by_cases hx : 2 * h < |x|
    · simp [hx]
    · simp [hx]
  have ha : Integrable (fun x : ℝ => if 2 * h < |x| then |x| else 0) ν := by
    apply (hCube.div_const (4 * h ^ 2)).mono' ((show Measurable (fun x : ℝ => if 2 * h < |x| then |x| else 0) from Measurable.ite hD (by fun_prop) measurable_const).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by split_ifs <;> positivity)]
      exact (energy_third_moment_pointwise h x hh).2.1
  have hsq : Integrable (fun x : ℝ => if 2 * h < |x| then x ^ 2 else 0) ν := by
    apply (hCube.div_const (2 * h)).mono' ((show Measurable (fun x : ℝ => if 2 * h < |x| then x ^ 2 else 0) from Measurable.ite hD (by fun_prop) measurable_const).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by split_ifs <;> positivity)]
      exact (energy_third_moment_pointwise h x hh).2.2.1
  have hf : Integrable (fun x : ℝ => if |x| ≤ 2 * h then x ^ 4 else 0) ν := by
    apply (hCube.const_mul (2 * h)).mono' ((show Measurable (fun x : ℝ => if |x| ≤ 2 * h then x ^ 4 else 0) from Measurable.ite (measurableSet_le (by fun_prop) measurable_const) (by fun_prop) measurable_const).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by split_ifs <;> positivity)]
      exact (energy_third_moment_pointwise h x hh).2.2.2
  refine ⟨ha, hsq, hf, ?_, ?_, ?_, ?_⟩
  · have hm : (∫ x : ℝ, if 2 * h < |x| then (1 : ℝ) else 0 ∂ν) =
        ν.real {x : ℝ | 2 * h < |x|} := by
      simpa [Set.indicator] using (integral_indicator_const (μ := ν) (1 : ℝ) hD)
    rw [← hm]
    calc
      _ ≤ ∫ x : ℝ, |x| ^ 3 / (8 * h ^ 3) ∂ν :=
        integral_mono hi (hCube.div_const _) fun x => (energy_third_moment_pointwise h x hh).1
      _ = _ := integral_div _ _
  · calc
      _ ≤ ∫ x : ℝ, |x| ^ 3 / (4 * h ^ 2) ∂ν :=
        integral_mono ha (hCube.div_const _) fun x => (energy_third_moment_pointwise h x hh).2.1
      _ = _ := integral_div _ _
  · calc
      _ ≤ ∫ x : ℝ, |x| ^ 3 / (2 * h) ∂ν :=
        integral_mono hsq (hCube.div_const _) fun x => (energy_third_moment_pointwise h x hh).2.2.1
      _ = _ := integral_div _ _
  · calc
      _ ≤ ∫ x : ℝ, 2 * h * |x| ^ 3 ∂ν :=
        integral_mono hf (hCube.const_mul _) fun x => (energy_third_moment_pointwise h x hh).2.2.2
      _ = _ := integral_const_mul _ _

/-- Unit second moment pays the cutoff mass without any cubic-moment smallness. -/
theorem energy_cutoff_mass_lower (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ℝ) (hh : 1 ≤ h) (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    (3 / 4 : ℝ) ≤ ν.real {x : ℝ | |x| ≤ 2 * h} := by
  have hD : MeasurableSet {x : ℝ | 2 * h < |x|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hi : Integrable (fun x : ℝ => if 2 * h < |x| then (1 : ℝ) else 0) ν := by
    convert (integrable_const (μ := ν) (1 : ℝ)).indicator hD using 1
    ext x
    by_cases hx : 2 * h < |x|
    · simp [hx]
    · simp [hx]
  have hp (x : ℝ) : (if 2 * h < |x| then (1 : ℝ) else 0) ≤ x ^ 2 / (4 * h ^ 2) := by
    split_ifs with hx
    · apply (le_div_iff₀ (by positivity : 0 < 4 * h ^ 2)).2
      nlinarith [sq_abs x]
    · positivity
  have hm : ν.real {x : ℝ | 2 * h < |x|} ≤ 1 / (4 * h ^ 2) := by
    have hi' := integral_mono hi (hSq.div_const (4 * h ^ 2)) hp
    have hei : (∫ x : ℝ, if 2 * h < |x| then (1 : ℝ) else 0 ∂ν) =
        ν.real {x : ℝ | 2 * h < |x|} := by
      simpa [Set.indicator] using (integral_indicator_const (μ := ν) (1 : ℝ) hD)
    rwa [hei, integral_div, hsecond] at hi'
  have ht : 1 / (4 * h ^ 2) ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * h ^ 2)).2
    nlinarith
  have hc := measureReal_add_measureReal_compl (μ := ν)
    (s := {x : ℝ | 2 * h < |x|}) hD
  have he : {x : ℝ | 2 * h < |x|}ᶜ = {x : ℝ | |x| ≤ 2 * h} := by ext x; simp
  rw [he, probReal_univ] at hc
  linarith

theorem energyNormalizer_bounds (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    (3 / 4 : ℝ) * Real.exp (-4 * T) ≤ energyNormalizer ν h s ∧
      energyNormalizer ν h s ≤ Real.exp (4 * T) := by
  have hh0 : 0 < h := by linarith
  have hw := energyWeight_integrable ν T h s hT hh0 hs
  have hB : MeasurableSet {x : ℝ | |x| ≤ 2 * h} :=
    measurableSet_le (by fun_prop) measurable_const
  have hi : Integrable (fun x : ℝ => if |x| ≤ 2 * h then Real.exp (-4 * T) else 0) ν := by
    convert (integrable_const (μ := ν) (Real.exp (-4 * T))).indicator hB using 1
    ext x
    by_cases hx : |x| ≤ 2 * h
    · simp [hx]
    · simp [hx]
  have hl := integral_mono hi hw (energyWeight_lower_indicator T h s · hT hh0 hs)
  have hei : (∫ x : ℝ, if |x| ≤ 2 * h then Real.exp (-4 * T) else 0 ∂ν) =
      ν.real {x : ℝ | |x| ≤ 2 * h} * Real.exp (-4 * T) := by
    simpa [Set.indicator] using (integral_indicator_const (μ := ν) (Real.exp (-4 * T)) hB)
  rw [hei] at hl
  constructor
  · exact (mul_le_mul_of_nonneg_right (energy_cutoff_mass_lower ν h hh hSq hsecond)
      (Real.exp_nonneg _)).trans hl
  · change (∫ x : ℝ, energyWeight h s x ∂ν) ≤ _
    calc
      _ ≤ ∫ _x : ℝ, Real.exp (4 * T) ∂ν :=
        integral_mono hw (integrable_const _) (energyWeight_le T h s · hT hh0 hs)
      _ = _ := by simp

/-- The precise quadratic exponential remainder, for both signs of the argument. -/
theorem energy_exp_remainder_bound (T u : ℝ) (hT : 0 ≤ T) (hu : |u| ≤ 4 * T) :
    |Real.exp u - 1 - u| ≤ (Real.exp (4 * T) / 2) * u ^ 2 := by
  have hn : 0 ≤ Real.exp u - 1 - u := by linarith [Real.add_one_le_exp u]
  rw [abs_of_nonneg hn]
  let g : ℝ → ℝ := fun v => Real.exp (4 * T) * v - Real.exp v + 1
  let F : ℝ → ℝ := fun v => Real.exp (4 * T) / 2 * v ^ 2 - (Real.exp v - 1 - v)
  have hg (v : ℝ) : deriv g v = Real.exp (4 * T) - Real.exp v := by
    simp (disch := fun_prop) [g]
  have hF (v : ℝ) : deriv F v = g v := by
    simp (disch := fun_prop) [F, g]
    ring
  have hgm : MonotoneOn g (Set.Icc (-4 * T) (4 * T)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (by fun_prop) (by fun_prop)
    intro v hv
    have hv' : v ∈ Set.Icc (-4 * T) (4 * T) := interior_subset hv
    rw [hg]
    exact sub_nonneg.mpr (Real.exp_le_exp.mpr hv'.2)
  have hg0 : g 0 = 0 := by norm_num [g]
  have hF0 : F 0 = 0 := by norm_num [F]
  have hz : (0 : ℝ) ∈ Set.Icc (-4 * T) (4 * T) := ⟨by linarith, by linarith⟩
  have hu' := abs_le.mp hu
  have hFu : 0 ≤ F u := by
    rcases le_total 0 u with hu0 | hu0
    · have hFm : MonotoneOn F (Set.Icc 0 (4 * T)) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (by fun_prop) (by fun_prop)
        intro v hv
        have hv' : v ∈ Set.Icc (0 : ℝ) (4 * T) := interior_subset hv
        rw [hF]
        have hm := hgm hz ⟨by linarith [hv'.1], hv'.2⟩ hv'.1
        simpa only [hg0] using hm
      have hm := hFm ⟨le_rfl, by linarith⟩ ⟨hu0, hu'.2⟩ hu0
      simpa only [hF0] using hm
    · have hFa : AntitoneOn F (Set.Icc (-4 * T) 0) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) (by fun_prop) (by fun_prop)
        intro v hv
        have hv' : v ∈ Set.Icc (-4 * T) (0 : ℝ) := interior_subset hv
        rw [hF]
        have hm := hgm ⟨hv'.1, by linarith [hv'.2]⟩ hz hv'.2
        simpa only [hg0] using hm
      have hm := hFa ⟨by linarith [hu'.1], hu0⟩ ⟨by linarith, le_rfl⟩ hu0
      simpa only [hF0] using hm
  dsimp only [F] at hFu
  linarith

noncomputable def energyRemainder (h s x : ℝ) : ℝ :=
  if |x| ≤ 2 * h then Real.exp (s * x ^ 2 / h ^ 2) - 1 - s * x ^ 2 / h ^ 2 else 0

theorem energyRemainder_measurable (h s : ℝ) : Measurable (energyRemainder h s) := by
  exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
    (by fun_prop) measurable_const

theorem energyRemainder_pointwise (T h s x : ℝ) (hT : 0 ≤ T) (hh : 0 < h)
    (hs : |s| ≤ T) :
    |energyRemainder h s x| ≤ (Real.exp (4 * T) * s ^ 2 / (2 * h ^ 4)) *
      (if |x| ≤ 2 * h then x ^ 4 else 0) := by
  by_cases hx : |x| ≤ 2 * h
  · have ha := energy_argument_bounds T h s x hT hh hs hx
    have hb := energy_exp_remainder_bound T (s * x ^ 2 / h ^ 2) hT
      (abs_le.mpr ⟨by linarith [ha.1], ha.2⟩)
    simp only [energyRemainder, hx, ite_true]
    calc
      _ ≤ (Real.exp (4 * T) / 2) * (s * x ^ 2 / h ^ 2) ^ 2 := hb
      _ = _ := by field_simp
  · simp only [energyRemainder, hx, ite_false, abs_zero, mul_zero, le_refl]

/-- The truncated Taylor remainder is genuinely integrable and paid by the cubic moment. -/
theorem energyRemainder_integral_bound (ν : Measure ℝ) [IsFiniteMeasure ν]
    (T h s : ℝ) (hT : 0 ≤ T) (hh : 0 < h) (hs : |s| ≤ T)
    (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν) :
    Integrable (energyRemainder h s) ν ∧
    |∫ x : ℝ, energyRemainder h s x ∂ν| ≤
      Real.exp (4 * T) * T ^ 2 * (∫ x : ℝ, |x| ^ 3 ∂ν) / h ^ 3 := by
  obtain ⟨_ha, _hq, hf, _hm, _hab, _hqb, hfb⟩ := energy_third_moment_payments ν h hh hCube
  let K : ℝ := Real.exp (4 * T) * s ^ 2 / (2 * h ^ 4)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hI : Integrable (energyRemainder h s) ν := by
    apply (hf.const_mul K).mono' (energyRemainder_measurable h s).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using energyRemainder_pointwise T h s x hT hh hs
  refine ⟨hI, ?_⟩
  have hβ : 0 ≤ ∫ x : ℝ, |x| ^ 3 ∂ν := integral_nonneg fun x => pow_nonneg (abs_nonneg x) 3
  have hs2 : s ^ 2 ≤ T ^ 2 := by
    have hp := pow_le_pow_left₀ (abs_nonneg s) hs 2
    nlinarith [sq_abs s]
  calc
    _ ≤ ∫ x : ℝ, K * (if |x| ≤ 2 * h then x ^ 4 else 0) ∂ν := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le (hf.const_mul K)
      exact Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using energyRemainder_pointwise T h s x hT hh hs
    _ = K * (∫ x : ℝ, if |x| ≤ 2 * h then x ^ 4 else 0 ∂ν) := integral_const_mul _ _
    _ ≤ K * (2 * h * (∫ x : ℝ, |x| ^ 3 ∂ν)) := mul_le_mul_of_nonneg_left hfb hK
    _ = Real.exp (4 * T) * s ^ 2 * (∫ x : ℝ, |x| ^ 3 ∂ν) / h ^ 3 := by
      dsimp only [K]
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs2 (Real.exp_nonneg _)) hβ)
      (le_of_lt (pow_pos hh 3))

theorem energyNormalizerErrorConstant_nonneg (T : ℝ) (hT : 0 ≤ T) :
    0 ≤ energyNormalizerErrorConstant T := by unfold energyNormalizerErrorConstant; positivity

/-- The actual first-order expansion, with the explicit frozen error constant. -/
theorem energyNormalizer_expansion (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    |energyNormalizer ν h s - 1 - s / h ^ 2| ≤
      energyNormalizerErrorConstant T * (∫ x : ℝ, |x| ^ 3 ∂ν) / h ^ 3 := by
  have hh0 : 0 < h := by linarith
  have hw := energyWeight_integrable ν T h s hT hh0 hs
  obtain ⟨_ha, hq, _hf, hm, _hab, hqb, _hfb⟩ := energy_third_moment_payments ν h hh0 hCube
  obtain ⟨hr, hrb⟩ := energyRemainder_integral_bound ν T h s hT hh0 hs hCube
  have hD : MeasurableSet {x : ℝ | 2 * h < |x|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hi : Integrable (fun x : ℝ => if 2 * h < |x| then (1 : ℝ) else 0) ν := by
    convert (integrable_const (μ := ν) (1 : ℝ)).indicator hD using 1
    ext x
    by_cases hx : 2 * h < |x| <;> simp [hx]
  have him : (∫ x : ℝ, if 2 * h < |x| then (1 : ℝ) else 0 ∂ν) =
      ν.real {x : ℝ | 2 * h < |x|} := by
    simpa [Set.indicator] using integral_indicator_const (μ := ν) (1 : ℝ) hD
  have hid : energyNormalizer ν h s - 1 - s / h ^ 2 =
      -ν.real {x : ℝ | 2 * h < |x|} - (s / h ^ 2) *
        (∫ x : ℝ, if 2 * h < |x| then x ^ 2 else 0 ∂ν) +
        (∫ x : ℝ, energyRemainder h s x ∂ν) := by
    calc
      _ = ∫ x : ℝ, energyWeight h s x - 1 - (s / h ^ 2) * x ^ 2 ∂ν := by
        have hsub1 := integral_sub (μ := ν) (hw.sub (integrable_const 1)) (hSq.const_mul (s / h ^ 2))
        have hsub2 := integral_sub (μ := ν) hw (integrable_const 1)
        simp only [Pi.sub_apply] at hsub1 hsub2
        rw [hsub1, hsub2, integral_const_mul, hsecond]
        simp [energyNormalizer]
      _ = ∫ x : ℝ, -(if 2 * h < |x| then (1 : ℝ) else 0) -
          (s / h ^ 2) * (if 2 * h < |x| then x ^ 2 else 0) + energyRemainder h s x ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          by_cases hx : |x| ≤ 2 * h
          · have hn : ¬ 2 * h < |x| := not_lt.mpr hx
            simp only [energyWeight, energyRemainder, hx, hn, ite_true, ite_false]
            ring
          · have hn : 2 * h < |x| := lt_of_not_ge hx
            simp only [energyWeight, energyRemainder, hx, hn, ite_true, ite_false]
            ring
      _ = _ := by
        have hadd := integral_add (μ := ν) (hi.neg.sub (hq.const_mul (s / h ^ 2))) hr
        have hsub := integral_sub (μ := ν) hi.neg (hq.const_mul (s / h ^ 2))
        simp only [Pi.neg_apply, Pi.sub_apply] at hadd hsub
        rw [hadd, hsub, integral_neg, integral_const_mul, him]
  have hp0 : 0 ≤ ν.real {x : ℝ | 2 * h < |x|} := measureReal_nonneg
  have hq0 : 0 ≤ ∫ x : ℝ, if 2 * h < |x| then x ^ 2 else 0 ∂ν :=
    integral_nonneg fun x => by split_ifs <;> positivity
  have hc : |s / h ^ 2| ≤ T / h ^ 2 := by
    rw [abs_div, abs_of_nonneg (sq_nonneg h)]
    exact div_le_div_of_nonneg_right hs (sq_nonneg h)
  calc
    _ = |-ν.real {x : ℝ | 2 * h < |x|} - (s / h ^ 2) *
        (∫ x : ℝ, if 2 * h < |x| then x ^ 2 else 0 ∂ν) +
        (∫ x : ℝ, energyRemainder h s x ∂ν)| := congrArg abs hid
    _ ≤ ν.real {x : ℝ | 2 * h < |x|} + |s / h ^ 2| *
        (∫ x : ℝ, if 2 * h < |x| then x ^ 2 else 0 ∂ν) +
        |∫ x : ℝ, energyRemainder h s x ∂ν| := by
      calc
        _ ≤ |-(ν.real {x : ℝ | 2 * h < |x|}) - (s / h ^ 2) *
            (∫ x : ℝ, if 2 * h < |x| then x ^ 2 else 0 ∂ν)| +
            |∫ x : ℝ, energyRemainder h s x ∂ν| := abs_add_le _ _
        _ ≤ (|-(ν.real {x : ℝ | 2 * h < |x|})| + |(s / h ^ 2) *
            (∫ x : ℝ, if 2 * h < |x| then x ^ 2 else 0 ∂ν)|) +
            |∫ x : ℝ, energyRemainder h s x ∂ν| := add_le_add (abs_sub _ _) le_rfl
        _ = _ := by rw [abs_neg, abs_of_nonneg hp0, abs_mul, abs_of_nonneg hq0]
    _ ≤ (∫ x : ℝ, |x| ^ 3 ∂ν) / (8 * h ^ 3) + (T / h ^ 2) *
        ((∫ x : ℝ, |x| ^ 3 ∂ν) / (2 * h)) +
        Real.exp (4 * T) * T ^ 2 * (∫ x : ℝ, |x| ^ 3 ∂ν) / h ^ 3 :=
      add_le_add (add_le_add hm (mul_le_mul hc hqb hq0 (div_nonneg hT (sq_nonneg h)))) hrb
    _ = _ := by unfold energyNormalizerErrorConstant; field_simp

end Shao.OQ4
