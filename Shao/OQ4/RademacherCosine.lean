import Shao.OQ4.KilledKernel

/-!
# Rademacher principal cosine for the genuine closed killed kernel

Only a one-step identity on the integer state class is asserted. The endpoints
of the closed strip retain their atomic mass; strict exits are not normalized.
-/

namespace Shao.OQ4.RademacherCosine

open MeasureTheory

/-- The actual finite extended nonnegative half weight. -/
noncomputable def halfENNReal : ENNReal := 1 / 2

/-- The fixed real Rademacher increment law. -/
noncomputable def law : Measure ℝ :=
  halfENNReal • Measure.dirac (1 : ℝ) + halfENNReal • Measure.dirac (-1 : ℝ)

private theorem half_ne_top : halfENNReal ≠ ⊤ := by
  norm_num [halfENNReal]

private theorem half_toReal : halfENNReal.toReal = (1 / 2 : ℝ) := by
  norm_num [halfENNReal, ENNReal.toReal_div]

/-- Probability is proved from the two actual half-weighted atoms. -/
instance law_isProbabilityMeasure : IsProbabilityMeasure law := by
  constructor
  norm_num [law, halfENNReal]
  simpa only [one_div] using ENNReal.add_halves (1 : ENNReal)

/-- The principal frequency uses the absorbing integer site m+1. -/
noncomputable def angle (m : ℕ) : ℝ := Real.pi / (2 * ((m : ℝ) + 1))

/-- The principal one-step multiplier at the frozen frequency. -/
noncomputable def rho (m : ℕ) : ℝ := Real.cos (angle m)

/-- The actual real closed condition is exactly the integer state condition. -/
theorem integer_closed_iff (m : ℕ) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) (s : ℤ) :
    |(s : ℝ)| ≤ h ↔ |s| ≤ (m : ℤ) := by
  constructor
  · intro hs
    by_contra hint
    have hi : (m : ℤ) + 1 ≤ |s| := by omega
    have hir : (m : ℝ) + 1 ≤ |(s : ℝ)| := by exact_mod_cast hi
    linarith
  · intro hs
    have hsr : |(s : ℝ)| ≤ (m : ℝ) := by exact_mod_cast hs
    exact hsr.trans hmh

private theorem law_map (z : ℝ) :
    law.map (fun y : ℝ => z + y) =
      halfENNReal • Measure.dirac (z + 1) + halfENNReal • Measure.dirac (z - 1) := by
  have hm : Measurable (fun y : ℝ => z + y) := by fun_prop
  rw [law, Measure.map_add _ _ hm, Measure.map_smul halfENNReal hm.aemeasurable,
    Measure.map_smul halfENNReal hm.aemeasurable, Measure.map_dirac, Measure.map_dirac]
  rfl

/-- Exact row measure of the actual closed killed kernel, without renormalization. -/
theorem killedKernel_row (m : ℕ) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) (r : ℤ) :
    killedKernel law h (r : ℝ) =
      (if |r + 1| ≤ (m : ℤ) then
        halfENNReal • Measure.dirac (((r + 1 : ℤ) : ℝ)) else 0) +
      (if |r - 1| ≤ (m : ℤ) then
        halfENNReal • Measure.dirac (((r - 1 : ℤ) : ℝ)) else 0) := by
  have hp : |(r : ℝ) + 1| ≤ h ↔ |r + 1| ≤ (m : ℤ) := by
    simpa only [Int.cast_add, Int.cast_one] using integer_closed_iff m h hmh hhm (r + 1)
  have hn : |(r : ℝ) - 1| ≤ h ↔ |r - 1| ≤ (m : ℤ) := by
    simpa only [Int.cast_sub, Int.cast_one] using integer_closed_iff m h hmh hhm (r - 1)
  rw [killedKernel_apply, law_map, Measure.restrict_add,
    Measure.restrict_smul, Measure.restrict_smul, restrict_dirac, restrict_dirac]
  simp only [Set.mem_Icc, ← abs_le, hp, hn, smul_ite, smul_zero,
    Int.cast_add, Int.cast_sub, Int.cast_one]

/-- The principal cosine is genuinely integrable against each actual kernel row. -/
theorem killedKernel_cos_integrable (m : ℕ) (h : ℝ) (r : ℤ) :
    Integrable (fun w : ℝ => Real.cos (angle m * w)) (killedKernel law h (r : ℝ)) := by
  exact (killedKernel_integral_bounded law h (r : ℝ)
    (fun w : ℝ => Real.cos (angle m * w)) (by fun_prop)
    ⟨1, fun w => Real.abs_cos_le_one (angle m * w)⟩).1

private theorem integral_law (f : ℝ → ℝ) :
    (∫ y : ℝ, f y ∂law) = (1 / 2 : ℝ) * f 1 + (1 / 2 : ℝ) * f (-1) := by
  have hp : Integrable f (halfENNReal • Measure.dirac (1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure half_ne_top
  have hn : Integrable f (halfENNReal • Measure.dirac (-1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure half_ne_top
  rw [law, integral_add_measure hp hn, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac, half_toReal]
  rfl

private theorem absorbing_cos_zero (m : ℕ) (hm : 1 ≤ m) (s : ℤ)
    (hs : |s| = (m : ℤ) + 1) : Real.cos (angle m * (s : ℝ)) = 0 := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hM : (m : ℝ) + 1 ≠ 0 := by linarith
  have hsR : |(s : ℝ)| = (m : ℝ) + 1 := by exact_mod_cast hs
  have haH : angle m * ((m : ℝ) + 1) = Real.pi / 2 := by
    unfold angle
    field_simp
  have hcosabs : Real.cos (angle m * |(s : ℝ)|) = Real.cos (angle m * (s : ℝ)) := by
    rcases le_total 0 (s : ℝ) with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, mul_neg, Real.cos_neg]
  rw [← hcosabs, hsR, haH, Real.cos_pi_div_two]

private theorem cut_cos_eq (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) (s : ℤ)
    (hs : |s| ≤ (m : ℤ) + 1) :
    (if |(s : ℝ)| ≤ h then Real.cos (angle m * (s : ℝ)) else 0) =
      Real.cos (angle m * (s : ℝ)) := by
  by_cases hc : |s| ≤ (m : ℤ)
  · have hcR := (integer_closed_iff m h hmh hhm s).2 hc
    simp only [hcR, ite_true]
  · have hcR : ¬ |(s : ℝ)| ≤ h := fun hcR => hc ((integer_closed_iff m h hmh hhm s).1 hcR)
    have habs : |s| = (m : ℤ) + 1 := by omega
    simp only [hcR, ite_false]
    exact (absorbing_cos_zero m hm s habs).symm

/-- Principal cosine identity for every frozen integer start in the closed strip. -/
theorem Kcos_principal (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) (r : ℤ)
    (hrlo : -(m : ℤ) ≤ r) (hrhi : r ≤ (m : ℤ)) :
    Kcos law (angle m) h (r : ℝ) = rho m * Real.cos (angle m * (r : ℝ)) := by
  have hp : |r + 1| ≤ (m : ℤ) + 1 := by
    apply abs_le.mpr
    constructor <;> omega
  have hn : |r - 1| ≤ (m : ℤ) + 1 := by
    apply abs_le.mpr
    constructor <;> omega
  have hpcut : (if |(r : ℝ) + 1| ≤ h then
      Real.cos (angle m * ((r : ℝ) + 1)) else 0) =
      Real.cos (angle m * ((r : ℝ) + 1)) := by
    simpa only [Int.cast_add, Int.cast_one] using cut_cos_eq m hm h hmh hhm (r + 1) hp
  have hncut : (if |(r : ℝ) + -1| ≤ h then
      Real.cos (angle m * ((r : ℝ) + -1)) else 0) =
      Real.cos (angle m * ((r : ℝ) - 1)) := by
    simpa only [Int.cast_sub, Int.cast_one, sub_eq_add_neg, Int.cast_add, Int.cast_neg] using
      cut_cos_eq m hm h hmh hhm (r - 1) hn
  unfold Kcos
  rw [integral_law, hpcut, hncut]
  have hadd : angle m * ((r : ℝ) + 1) = angle m * (r : ℝ) + angle m := by ring
  have hsub : angle m * ((r : ℝ) - 1) = angle m * (r : ℝ) - angle m := by ring
  rw [hadd, hsub, Real.cos_add, Real.cos_sub, rho]
  ring

/-- The same principal identity as an integral against the genuine killed row. -/
theorem killedKernel_integral_principal (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) (r : ℤ)
    (hrlo : -(m : ℤ) ≤ r) (hrhi : r ≤ (m : ℤ)) :
    (∫ w : ℝ, Real.cos (angle m * w) ∂killedKernel law h (r : ℝ)) =
      rho m * Real.cos (angle m * (r : ℝ)) := by
  rw [killedKernel_integral_cos]
  exact Kcos_principal m hm h hmh hhm r hrlo hrhi

/-- The principal angle is positive. -/
theorem angle_pos (m : ℕ) : 0 < angle m := by
  unfold angle
  positivity

/-- On the frozen nondegenerate range, the principal angle is below pi/2. -/
theorem angle_lt_pi_div_two (m : ℕ) (hm : 1 ≤ m) : angle m < Real.pi / 2 := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  calc
    angle m = (Real.pi / 2) / ((m : ℝ) + 1) := by rw [angle, div_div]
    _ < Real.pi / 2 := div_lt_self (by positivity) (by linarith)

/-- The actual principal multiplier is positive. -/
theorem rho_pos (m : ℕ) (hm : 1 ≤ m) : 0 < rho m := by
  unfold rho
  apply Real.cos_pos_of_mem_Ioo
  exact ⟨by linarith [angle_pos m, Real.pi_pos], angle_lt_pi_div_two m hm⟩

/-- The actual principal multiplier is strictly below one. -/
theorem rho_lt_one (m : ℕ) (hm : 1 ≤ m) : rho m < 1 := by
  have hangle : angle m ≤ Real.pi := by
    linarith [angle_lt_pi_div_two m hm, Real.pi_pos]
  simpa only [rho, Real.cos_zero] using
    Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 0) hangle (angle_pos m)

end Shao.OQ4.RademacherCosine
