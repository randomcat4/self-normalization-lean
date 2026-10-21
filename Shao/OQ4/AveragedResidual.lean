import Shao.OQ4.KilledCosine
import Shao.OQ4.OvershootMoment
import Shao.OQ4.OccupationPayment
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Analytic averaged residual payment

This is the frozen v2 analytic bridge from an explicit O0 layer-mass input to
the averaged residual estimate.  The layer-mass hypothesis remains independent.
The uniform numerical constant depends on both the moment bound and C.
-/

namespace Shao.OQ4

open MeasureTheory
open scoped BigOperators

noncomputable def cosineResidual (ν : Measure ℝ) (a h w : ℝ) : ℝ :=
  Kcos ν a h w - cosineCoefficient ν a * Real.cos (a * w)

noncomputable def overshootPotential (ν : Measure ℝ) (h w : ℝ) : ℝ :=
  ∫ y : ℝ, max (|y| - (h - |w|)) 0 ∂ν

/-- Joint measurability gives measurable killed-cosine parameter integrals. -/
theorem measurable_Kcos (ν : Measure ℝ) [IsProbabilityMeasure ν] (a h : ℝ) :
    Measurable (Kcos ν a h) := by
  have hjoint : Measurable (fun p : ℝ × ℝ =>
      if |p.1 + p.2| ≤ h then Real.cos (a * (p.1 + p.2)) else 0) := by
    exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
      (by fun_prop) measurable_const
  exact hjoint.stronglyMeasurable.integral_prod_right'.measurable

/-- The overshoot expectation is a measurable function of the endpoint. -/
theorem measurable_overshootPotential (ν : Measure ℝ) [IsProbabilityMeasure ν] (h : ℝ) :
    Measurable (overshootPotential ν h) := by
  have hjoint : Measurable (fun p : ℝ × ℝ => max (|p.2| - (h - |p.1|)) 0) := by
    fun_prop
  exact hjoint.stronglyMeasurable.integral_prod_right'.measurable

/-- Fixed-parameter overshoot integrals are genuine integrals under only a first moment. -/
theorem integrable_overshoot_integrand (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h w : ℝ) (hId : Integrable (fun y : ℝ => y) ν) :
    Integrable (fun y : ℝ => max (|y| - (h - |w|)) 0) ν := by
  apply (hId.abs.add (integrable_const |h - (|w|)|)).mono'
    (by fun_prop : Measurable (fun y : ℝ => max (|y| - (h - |w|)) 0)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    change max (|y| - (h - |w|)) 0 ≤ |y| + |h - (|w|)|
    exact max_le (by linarith [neg_le_abs (h - |w|)])
      (add_nonneg (abs_nonneg y) (abs_nonneg _))

/-- The absolute residual is globally bounded and hence integrable against any finite measure. -/
theorem integrable_abs_cosineResidual (ν κ : Measure ℝ) [IsProbabilityMeasure ν]
    [IsFiniteMeasure κ] (a h : ℝ) : Integrable (fun w => |cosineResidual ν a h w|) κ := by
  have hrmeas : Measurable (cosineResidual ν a h) := by
    exact (measurable_Kcos ν a h).sub (measurable_const.mul (by fun_prop))
  have hK (w : ℝ) : |Kcos ν a h w| ≤ 1 := by
    have hbound (y : ℝ) : |if |w + y| ≤ h then Real.cos (a * (w + y)) else 0| ≤ 1 := by
      by_cases hy : |w + y| ≤ h
      · simpa only [hy, ite_true] using Real.abs_cos_le_one (a * (w + y))
      · simp only [hy, ite_false, abs_zero]
        norm_num
    have hmeas : Measurable (fun y : ℝ =>
        if |w + y| ≤ h then Real.cos (a * (w + y)) else 0) :=
      Measurable.ite (measurableSet_le (by fun_prop) measurable_const) (by fun_prop) measurable_const
    have hint : Integrable (fun y : ℝ =>
        if |w + y| ≤ h then Real.cos (a * (w + y)) else 0) ν := by
      apply Integrable.of_bound hmeas.aestronglyMeasurable 1
      exact Filter.Eventually.of_forall fun y => by
        simpa only [Real.norm_eq_abs] using hbound y
    change |∫ y : ℝ, (if |w + y| ≤ h then Real.cos (a * (w + y)) else 0) ∂ν| ≤ 1
    calc
      _ ≤ ∫ y : ℝ, |if |w + y| ≤ h then Real.cos (a * (w + y)) else 0| ∂ν :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _ : ℝ, (1 : ℝ) ∂ν := integral_mono hint.abs (integrable_const 1) hbound
      _ = 1 := by simp
  have hρ : |cosineCoefficient ν a| ≤ 1 := by
    have hint : Integrable (fun y : ℝ => Real.cos (a * y)) ν := by
      apply Integrable.of_bound (by fun_prop : Measurable
        (fun y : ℝ => Real.cos (a * y))).aestronglyMeasurable 1
      exact Filter.Eventually.of_forall fun y => by
        simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (a * y)
    change |∫ y : ℝ, Real.cos (a * y) ∂ν| ≤ 1
    calc
      _ ≤ ∫ y : ℝ, |Real.cos (a * y)| ∂ν := abs_integral_le_integral_abs
      _ ≤ ∫ _ : ℝ, (1 : ℝ) ∂ν :=
        integral_mono hint.abs (integrable_const 1) (fun y => Real.abs_cos_le_one (a * y))
      _ = 1 := by simp
  have hrbound (w : ℝ) : |cosineResidual ν a h w| ≤ 2 := by
    calc
      _ = |Kcos ν a h w + -(cosineCoefficient ν a * Real.cos (a * w))| := by
        rw [cosineResidual, sub_eq_add_neg]
      _ ≤ |Kcos ν a h w| + |-(cosineCoefficient ν a * Real.cos (a * w))| := abs_add_le _ _
      _ = |Kcos ν a h w| + |cosineCoefficient ν a| * |Real.cos (a * w)| := by
        rw [abs_neg, abs_mul]
      _ ≤ 1 + 1 * 1 := add_le_add (hK w)
        (mul_le_mul hρ (Real.abs_cos_le_one _) (abs_nonneg _) (by norm_num))
      _ = 2 := by norm_num
  apply Integrable.of_bound ((by fun_prop : Measurable (fun x : ℝ => |x|)).comp
    hrmeas).aestronglyMeasurable 2
  exact Filter.Eventually.of_forall fun w => by
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_abs] using hrbound w

/-- Frozen v2 analytic averaged-residual payment, with explicit moment and layer constants. -/
theorem averaged_cosine_residual_bound (ν κ : Measure ℝ) [IsProbabilityMeasure ν]
    [IsFiniteMeasure κ] (h C : ℝ) (hh : 0 < h) (hC : 0 ≤ C)
    (hκmass : κ.real Set.univ ≤ 1) (hκsupport : ∀ᵐ w ∂κ, |w| ≤ h)
    (hId : Integrable (fun y : ℝ => y) ν)
    (hSq : Integrable (fun y : ℝ => y ^ 2) ν)
    (hCube : Integrable (fun y : ℝ => |y| ^ 3) ν)
    (hmean : (∫ y : ℝ, y ∂ν) = 0) (hsecond : (∫ y : ℝ, y ^ 2 ∂ν) = 1)
    (hmass : ∀ j, j < ⌊h⌋₊ + 1 →
      κ.real (boundaryLayer (fun w : ℝ => h - |w|) j) ≤ (C / h ^ 2) * ((j : ℝ) + 1)) :
    let β : ℝ := ∫ y : ℝ, |y| ^ 3 ∂ν
    Integrable (fun w => |cosineResidual ν (Real.pi / (2 * h)) h w|) κ ∧
      (∫ w, |cosineResidual ν (Real.pi / (2 * h)) h w| ∂κ) ≤
        (Real.pi ^ 3 * β / 48 + 2 * Real.pi * C * ((∫ y : ℝ, |y| ∂ν) + β)) / h ^ 3 ∧
      (∫ w, |cosineResidual ν (Real.pi / (2 * h)) h w| ∂κ) ≤
        (Real.pi ^ 3 * β / 48 + 2 * Real.pi * C * (1 + 2 * β)) / h ^ 3 := by
  let β : ℝ := ∫ y : ℝ, |y| ^ 3 ∂ν
  let I : ℝ := ∫ y : ℝ, |y| ∂ν
  let a : ℝ := Real.pi / (2 * h)
  let c : ℝ := Real.pi ^ 3 * β / (48 * h ^ 3)
  let b : ℕ → ℝ := fun j => ∫ y : ℝ, max (|y| - (j : ℝ)) 0 ∂ν
  change Integrable (fun w => |cosineResidual ν a h w|) κ ∧
    (∫ w, |cosineResidual ν a h w| ∂κ) ≤
      (Real.pi ^ 3 * β / 48 + 2 * Real.pi * C * (I + β)) / h ^ 3 ∧
    (∫ w, |cosineResidual ν a h w| ∂κ) ≤
      (Real.pi ^ 3 * β / 48 + 2 * Real.pi * C * (1 + 2 * β)) / h ^ 3
  have hβ : 0 ≤ β := integral_nonneg fun y => pow_nonneg (abs_nonneg y) 3
  have ha : 0 < a := div_pos Real.pi_pos (by positivity)
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hrint := integrable_abs_cosineResidual ν κ a h
  have hψnonneg (w : ℝ) : 0 ≤ overshootPotential ν h w :=
    integral_nonneg fun _ => le_max_right _ _
  have hψle (w : ℝ) (hw : |w| ≤ h) : overshootPotential ν h w ≤ I := by
    apply integral_mono (integrable_overshoot_integrand ν h w hId) hId.abs
    intro y
    exact max_le (sub_le_self _ (sub_nonneg.mpr hw)) (abs_nonneg y)
  have hψint : Integrable (overshootPotential ν h) κ := by
    apply (integrable_const I).mono' (measurable_overshootPotential ν h).aestronglyMeasurable
    exact hκsupport.mono fun w hw => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hψnonneg w)]
      exact hψle w hw
  have hcellint (j : ℕ) : Integrable (fun y : ℝ => max (|y| - (j : ℝ)) 0) ν := by
    apply hId.abs.mono' (by fun_prop : Measurable
      (fun y : ℝ => max (|y| - (j : ℝ)) 0)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (sub_le_self _ (Nat.cast_nonneg j)) (abs_nonneg y)
  have hbnonneg : ∀ j, j < ⌊h⌋₊ + 1 → 0 ≤ b j := by
    intro j _
    exact integral_nonneg fun _ => le_max_right _ _
  have hdepth : ∀ᵐ w ∂κ, 0 ≤ h - |w| ∧ h - |w| ≤ h :=
    hκsupport.mono fun w hw => ⟨sub_nonneg.mpr hw, sub_le_self h (abs_nonneg w)⟩
  have hcap : ∀ᵐ w ∂κ, ∀ j, j < ⌊h⌋₊ + 1 →
      w ∈ boundaryLayer (fun w : ℝ => h - |w|) j → overshootPotential ν h w ≤ b j := by
    exact Filter.Eventually.of_forall fun w j _ hj => by
      apply integral_mono (integrable_overshoot_integrand ν h w hId) (hcellint j)
      intro y
      apply max_le_max _ le_rfl
      have hjlower : (j : ℝ) ≤ h - |w| := hj.1
      linarith
  have hpay0 := finite_occupation_payment_of_le κ (fun w : ℝ => h - |w|)
    (overshootPotential ν h) h (C / h ^ 2) b (by fun_prop) hψint hh.le
    (div_nonneg hC (sq_nonneg h)) hbnonneg hdepth hcap hmass
  have hsum : (∑ j ∈ Finset.range (⌊h⌋₊ + 1), ((j : ℝ) + 1) * b j) ≤ 4 * (I + β) := by
    simpa only [overshootCell, integral_const_mul] using
      (sum_integral_overshootCell_le (μ := ν) (U := fun y : ℝ => |y|) hId.abs hCube
        (Filter.Eventually.of_forall fun y => abs_nonneg y) (⌊h⌋₊ + 1))
  have hpay : (∫ w, overshootPotential ν h w ∂κ) ≤ (C / h ^ 2) * (4 * (I + β)) :=
    hpay0.trans (mul_le_mul_of_nonneg_left hsum (div_nonneg hC (sq_nonneg h)))
  have hpoint : ∀ᵐ w ∂κ, |cosineResidual ν a h w| ≤ c + a * overshootPotential ν h w := by
    exact hκsupport.mono fun w hw => by
      have hb := (killed_cosine_residual_bound ν h w hh hw hId hSq hCube hmean hsecond).2
      have harg : Real.pi * w / (2 * h) = a * w := by dsimp only [a]; ring
      rw [harg] at hb
      exact hb
  have hfirst : (∫ w, |cosineResidual ν a h w| ∂κ) ≤
      (Real.pi ^ 3 * β / 48 + 2 * Real.pi * C * (I + β)) / h ^ 3 := by
    calc
      _ ≤ ∫ w, c + a * overshootPotential ν h w ∂κ :=
        integral_mono_ae hrint ((integrable_const c).add (hψint.const_mul a)) hpoint
      _ = κ.real Set.univ * c + a * ∫ w, overshootPotential ν h w ∂κ := by
        rw [integral_add (integrable_const c) (hψint.const_mul a), integral_const,
          integral_const_mul, smul_eq_mul]
      _ ≤ c + a * ∫ w, overshootPotential ν h w ∂κ := by
        exact add_le_add (by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hκmass hc) le_rfl
      _ ≤ c + a * ((C / h ^ 2) * (4 * (I + β))) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hpay ha.le)
      _ = _ := by dsimp only [c, a]; field_simp; ring
  have hI : I ≤ 1 + β := by
    calc
      _ ≤ ∫ y : ℝ, 1 + |y| ^ 3 ∂ν := by
        apply integral_mono hId.abs ((integrable_const 1).add hCube)
        intro y
        change |y| ≤ 1 + |y| ^ 3
        by_cases hy : |y| ≤ 1
        · nlinarith [pow_nonneg (abs_nonneg y) 3]
        · have h1 : 0 ≤ |y| - 1 := by linarith
          have h2 := mul_nonneg (abs_nonneg y) h1
          have h3 := mul_nonneg (sq_nonneg |y|) h1
          nlinarith
      _ = _ := by rw [integral_add (integrable_const 1) hCube]; simp [β]
  refine ⟨hrint, hfirst, hfirst.trans ?_⟩
  apply (div_le_div_iff_of_pos_right (pow_pos hh 3)).mpr
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 * Real.pi * C)
  linarith

end Shao.OQ4
