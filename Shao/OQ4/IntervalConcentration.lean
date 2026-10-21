import Shao.Probability.MeasurablePath
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Closed-interval concentration with atoms, from an explicit actual CDF error. -/

namespace Shao.OQ4

open MeasureTheory ProbabilityTheory

theorem real_Ioc_eq_real_Iic_sub (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℝ) (hab : a ≤ b) : μ.real (Set.Ioc a b) = μ.real (Set.Iic b) - μ.real (Set.Iic a) := by
  have heq : Set.Iic b \ Set.Iic a = Set.Ioc a b := by
    ext x
    simp [and_comm]
  rw [← heq, measureReal_sdiff (Set.Iic_subset_Iic.mpr hab) measurableSet_Iic]

/-- The left atom is retained by a strictly smaller cutoff, then a limiting inequality. -/
theorem closed_interval_mass_bound_from_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (L ε : ℝ) (G : ℝ → ℝ) (hL : 0 ≤ L) (_hε : 0 ≤ ε)
    (hLip : ∀ x y, |G x - G y| ≤ L * |x - y|)
    (hCDF : ∀ x, |μ.real (Set.Iic x) - G x| ≤ ε)
    (a b : ℝ) (hab : a ≤ b) : μ.real (Set.Icc a b) ≤ L * (b - a) + 2 * ε := by
  have hstep (δ : ℝ) (hδ : 0 < δ) :
      μ.real (Set.Icc a b) ≤ L * (b - a) + 2 * ε + L * δ := by
    have hsub : Set.Icc a b ⊆ Set.Ioc (a - δ) b := by
      intro x hx
      exact ⟨by linarith [hx.1], hx.2⟩
    have hdiff : μ.real (Set.Iic b) - μ.real (Set.Iic (a - δ)) ≤
        G b - G (a - δ) + 2 * ε := by
      have hb := abs_le.mp (hCDF b)
      have ha := abs_le.mp (hCDF (a - δ))
      linarith
    have hG := (le_abs_self (G b - G (a - δ))).trans (hLip b (a - δ))
    rw [abs_of_nonneg (by linarith : 0 ≤ b - (a - δ))] at hG
    calc
      _ ≤ μ.real (Set.Ioc (a - δ) b) := measureReal_mono hsub
      _ = μ.real (Set.Iic b) - μ.real (Set.Iic (a - δ)) :=
        real_Ioc_eq_real_Iic_sub μ _ _ (by linarith)
      _ ≤ G b - G (a - δ) + 2 * ε := hdiff
      _ ≤ L * (b - a) + 2 * ε + L * δ := by nlinarith
  apply le_of_forall_pos_le_add
  intro η hη
  let δ : ℝ := η / (L + 1)
  have hden : 0 < L + 1 := by linarith
  have hδ : 0 < δ := div_pos hη hden
  have hLδ : L * δ ≤ η := by
    calc
      _ ≤ (L + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = η := by dsimp [δ]; field_simp
  exact (hstep δ hδ).trans (by linarith)

noncomputable def standardNormalCDF (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

theorem standardNormalCDF_eq_real (x : ℝ) :
    standardNormalCDF x = (gaussianReal 0 1).real (Set.Iic x) := cdf_eq_real _ x

theorem standardGaussian_density_le_one (x : ℝ) : gaussianPDFReal 0 1 x ≤ 1 := by
  have hroot : 1 ≤ Real.sqrt (2 * Real.pi) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 2 * Real.pi by linarith [Real.two_le_pi])
  have hinv : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hroot
  have he : Real.exp (-(x ^ 2) / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  calc
    _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ ≤ 1 := by simpa using hinv

theorem standardGaussian_Ioc_mass_le_length (a b : ℝ) (hab : a ≤ b) :
    (gaussianReal 0 1).real (Set.Ioc a b) ≤ b - a := by
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 (by norm_num : (1 : NNReal) ≠ 0),
    ENNReal.toReal_ofReal (integral_nonneg (gaussianPDFReal_nonneg 0 1))]
  calc
    _ ≤ ∫ _x in Set.Ioc a b, (1 : ℝ) :=
      integral_mono_ae (integrable_gaussianPDFReal 0 1).restrict (integrableOn_const (by simp))
        (Filter.Eventually.of_forall standardGaussian_density_le_one)
    _ = b - a := by simp [Real.volume_real_Ioc_of_le hab]

/-- The comparison is the actual Mathlib standard Gaussian CDF, not a hypothesis. -/
theorem standardNormalCDF_lipschitz (x y : ℝ) : |standardNormalCDF x - standardNormalCDF y| ≤ |x - y| := by
  unfold standardNormalCDF
  rcases le_total x y with hxy | hyx
  · have hm := monotone_cdf (gaussianReal 0 1) hxy
    have hd := standardGaussian_Ioc_mass_le_length x y hxy
    rw [real_Ioc_eq_real_Iic_sub _ x y hxy, ← cdf_eq_real _ y, ← cdf_eq_real _ x] at hd
    rw [abs_of_nonpos (sub_nonpos.mpr hm), abs_of_nonpos (sub_nonpos.mpr hxy)]
    linarith
  · have hm := monotone_cdf (gaussianReal 0 1) hyx
    have hd := standardGaussian_Ioc_mass_le_length y x hyx
    rw [real_Ioc_eq_real_Iic_sub _ y x hyx, ← cdf_eq_real _ x, ← cdf_eq_real _ y] at hd
    rw [abs_of_nonneg (sub_nonneg.mpr hm), abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact hd

/-- A unit second moment forces the third absolute moment to be at least one. -/
theorem third_absolute_moment_ge_one (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun y : ℝ => y ^ 2) ν)
    (hCube : Integrable (fun y : ℝ => |y| ^ 3) ν)
    (hsecond : (∫ y : ℝ, y ^ 2 ∂ν) = 1) : 1 ≤ ∫ y : ℝ, |y| ^ 3 ∂ν := by
  have hpoint (y : ℝ) : 3 * y ^ 2 ≤ 2 * |y| ^ 3 + 1 := by
    have hp := mul_nonneg (sq_nonneg (|y| - 1)) (by positivity : 0 ≤ 2 * |y| + 1)
    nlinarith [sq_abs y]
  have hi := integral_mono (hSq.const_mul 3) ((hCube.const_mul 2).add (integrable_const 1)) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul, integral_add (hCube.const_mul 2) (integrable_const 1),
    integral_const_mul, hsecond] at hi
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, mul_one] at hi
  linarith

/-- Closed unit-interval AC from the displayed BE-type CDF premise on the actual standardized sum. -/
theorem iid_closed_unit_concentration_of_cdf_error (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun y : ℝ => y ^ 2) ν)
    (hCube : Integrable (fun y : ℝ => |y| ^ 3) ν)
    (hsecond : (∫ y : ℝ, y ^ 2 ∂ν) = 1) (t : ℕ) (ht : 1 ≤ t)
    (C_BE : ℝ) (hC : 0 ≤ C_BE)
    (hBE : ∀ x : ℝ, |(Measure.pi (fun _ : Fin t => ν)).real
        {a | Shao.prefixSum a t / Real.sqrt (t : ℝ) ≤ x} - standardNormalCDF x| ≤
      C_BE * (∫ y : ℝ, |y| ^ 3 ∂ν) / Real.sqrt (t : ℝ)) (a : ℝ) :
    (Measure.pi (fun _ : Fin t => ν)).real {b | Shao.prefixSum b t ∈ Set.Icc a (a + 1)} ≤
      (1 + 2 * C_BE) * (∫ y : ℝ, |y| ^ 3 ∂ν) / Real.sqrt (t : ℝ) := by
  let β : ℝ := ∫ y : ℝ, |y| ^ 3 ∂ν
  have hβ : 1 ≤ β := third_absolute_moment_ge_one ν hSq hCube hsecond
  have hs : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < t by omega))
  let X : Shao.Path t → ℝ := fun b => Shao.prefixSum b t / Real.sqrt (t : ℝ)
  have hX : Measurable X := (Shao.measurable_prefixSum t).div measurable_const
  let μ : Measure ℝ := (Measure.pi (fun _ : Fin t => ν)).map X
  have : IsProbabilityMeasure μ := by
    constructor
    change ((Measure.pi (fun _ : Fin t => ν)).map X) Set.univ = 1
    rw [Measure.map_apply hX MeasurableSet.univ]
    simp
  have hCDF (x : ℝ) : |μ.real (Set.Iic x) - standardNormalCDF x| ≤ C_BE * β / Real.sqrt (t : ℝ) := by
    change |(((Measure.pi (fun _ : Fin t => ν)).map X) (Set.Iic x)).toReal - standardNormalCDF x| ≤ _
    rw [Measure.map_apply hX measurableSet_Iic]
    exact hBE x
  have heq : X ⁻¹' Set.Icc (a / Real.sqrt (t : ℝ)) ((a + 1) / Real.sqrt (t : ℝ)) =
      {b | Shao.prefixSum b t ∈ Set.Icc a (a + 1)} := by
    ext b
    simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_ofPred_eq, X, div_le_div_iff_of_pos_right hs]
  have hlaw : (Measure.pi (fun _ : Fin t => ν)).real {b | Shao.prefixSum b t ∈ Set.Icc a (a + 1)} =
      μ.real (Set.Icc (a / Real.sqrt (t : ℝ)) ((a + 1) / Real.sqrt (t : ℝ))) := by
    simp only [μ, measureReal_def, Measure.map_apply hX measurableSet_Icc, heq]
  have hclosed := closed_interval_mass_bound_from_cdf μ 1 (C_BE * β / Real.sqrt (t : ℝ))
    standardNormalCDF (by norm_num) (by positivity)
    (fun x y => by simpa only [one_mul] using standardNormalCDF_lipschitz x y) hCDF
    (a / Real.sqrt (t : ℝ)) ((a + 1) / Real.sqrt (t : ℝ))
    ((div_le_div_iff_of_pos_right hs).2 (by linarith))
  rw [← hlaw] at hclosed
  calc
    _ ≤ 1 * ((a + 1) / Real.sqrt (t : ℝ) - a / Real.sqrt (t : ℝ)) +
        2 * (C_BE * β / Real.sqrt (t : ℝ)) := hclosed
    _ = (1 + 2 * C_BE * β) / Real.sqrt (t : ℝ) := by ring
    _ ≤ (1 + 2 * C_BE) * β / Real.sqrt (t : ℝ) :=
      div_le_div_of_nonneg_right (by nlinarith) hs.le

end Shao.OQ4
