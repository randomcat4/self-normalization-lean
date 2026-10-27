import Shao.Probability.GaussianTail
import Shao.OQ5.P51.BoundedPolylogWindow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

open Filter
open scoped Topology

namespace Shao.OQ6.OriginalExceptionalTailAbsorption

theorem eventually_original_exceptional_payment_absorbed
    (t0 cg : ℝ) (ht0 : 0 < t0) (hcg : 0 < cg) :
    let cWindow : ℝ := min (1 : ℝ) (Real.sqrt t0 / (2 : ℝ))
    0 < cWindow ∧
      ∀ᶠ n : ℕ in atTop,
        4 ≤ n ∧
          (1 : ℝ) ≤ cWindow * Real.rpow (n : ℝ) (1 / 6 : ℝ) ∧
          ∀ z : ℝ, (1 : ℝ) ≤ z →
            z ≤ cWindow * Real.rpow (n : ℝ) (1 / 6 : ℝ) →
            (6 : ℝ) *
                Real.exp (-Shao.OQ5.P51.boundedPolylogMomentOrder t0 n) +
              (2 : ℝ) * Real.exp (-cg * (n : ℝ)) +
              (8 : ℝ) * Real.exp (-(Real.sqrt (n : ℝ)) / (2 : ℝ)) ≤
              Real.exp (-(t0 / (2 : ℝ)) *
                Real.rpow (n : ℝ) (1 / 3 : ℝ)) *
                Shao.standardNormalTail z := by
  let cWindow : ℝ := min (1 : ℝ) (Real.sqrt t0 / (2 : ℝ))
  let b : ℝ := 3 * t0 / (8 : ℝ)
  change 0 < cWindow ∧ _
  have hcWindow : 0 < cWindow :=
    lt_min zero_lt_one (div_pos (Real.sqrt_pos.mpr ht0) (by norm_num))
  have hcWindow_one : cWindow ≤ (1 : ℝ) := min_le_left _ _
  have hcWindow_sqrt : cWindow ≤ Real.sqrt t0 / (2 : ℝ) := min_le_right _ _
  have hcWindow_sq : cWindow ^ (2 : ℕ) ≤ t0 / (4 : ℝ) := by
    have hproduct : 0 ≤
        (Real.sqrt t0 / (2 : ℝ) - cWindow) *
          (Real.sqrt t0 / (2 : ℝ) + cWindow) :=
      mul_nonneg (sub_nonneg.mpr hcWindow_sqrt)
        (add_nonneg (div_nonneg (Real.sqrt_nonneg _) (by norm_num)) hcWindow.le)
    nlinarith only [hproduct, Real.sq_sqrt ht0.le]
  have hb : 0 < b := by
    dsimp only [b]
    positivity
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hthird : Tendsto (fun n : ℕ => Real.rpow (n : ℝ) (1 / 3 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hnat
  have hsixth : Tendsto (fun n : ℕ => Real.rpow (n : ℝ) (1 / 6 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp hnat
  have htwothirds : Tendsto (fun n : ℕ => Real.rpow (n : ℝ) (2 / 3 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hnat
  have hexp : Tendsto
      (fun n : ℕ => Real.exp (-b * Real.rpow (n : ℝ) (1 / 3 : ℝ)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.rpow_zero, one_mul] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0 : ℝ) b hb).comp hthird
  have hlinearExp : Tendsto
      (fun n : ℕ => Real.rpow (n : ℝ) (1 / 3 : ℝ) *
        Real.exp (-b * Real.rpow (n : ℝ) (1 / 3 : ℝ)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.rpow_one] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) b hb).comp hthird
  have hsmallLimit : Tendsto
      (fun n : ℕ => (128 / 3 : ℝ) *
        (1 + Real.rpow (n : ℝ) (1 / 3 : ℝ)) *
          Real.exp (-b * Real.rpow (n : ℝ) (1 / 3 : ℝ)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [add_mul, one_mul, mul_one, mul_add, mul_assoc, zero_add, mul_zero] using
      (tendsto_const_nhds (x := (128 / 3 : ℝ))).mul (hexp.add hlinearExp)
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (128 / 3 : ℝ) * (1 + Real.rpow (n : ℝ) (1 / 3 : ℝ)) *
        Real.exp (-b * Real.rpow (n : ℝ) (1 / 3 : ℝ)) ≤ (1 : ℝ) :=
    (hsmallLimit.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
      (fun _ hn => hn.le)
  refine ⟨hcWindow, ?_⟩
  filter_upwards [eventually_ge_atTop (4 : ℕ),
    hsixth.eventually_ge_atTop (1 / cWindow),
    htwothirds.eventually_ge_atTop (t0 / cg),
    hsixth.eventually_ge_atTop (2 * t0), hsmall]
    with n hn hnonemptyBound hlinearBound hsqrtBound hsmalln
  let x : ℝ := (n : ℝ)
  let s : ℝ := Real.rpow x (1 / 3 : ℝ)
  let u : ℝ := Real.rpow x (1 / 6 : ℝ)
  change 1 / cWindow ≤ u at hnonemptyBound
  change t0 / cg ≤ Real.rpow x (2 / 3 : ℝ) at hlinearBound
  change 2 * t0 ≤ u at hsqrtBound
  change (128 / 3 : ℝ) * (1 + s) * Real.exp (-b * s) ≤ (1 : ℝ) at hsmalln
  have hxone : (1 : ℝ) ≤ x := by
    dsimp only [x]
    exact_mod_cast (Nat.le_trans (by norm_num : (1 : ℕ) ≤ 4) hn)
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hxone
  have hspos : 0 < s := Real.rpow_pos_of_pos hxpos _
  have hupos : 0 < u := Real.rpow_pos_of_pos hxpos _
  have husq : u ^ (2 : ℕ) = s := by
    calc
      u ^ (2 : ℕ) = Real.rpow u (2 : ℝ) := (Real.rpow_natCast u 2).symm
      _ = Real.rpow x ((1 / 6 : ℝ) * (2 : ℝ)) :=
        (Real.rpow_mul hxpos.le (1 / 6 : ℝ) (2 : ℝ)).symm
      _ = s := by norm_num [s]
  have hus : u ≤ s :=
    Real.rpow_le_rpow_of_exponent_le hxone (by norm_num : (1 / 6 : ℝ) ≤ 1 / 3)
  have hproduct : s * Real.rpow x (2 / 3 : ℝ) = x := by
    dsimp only [s]
    rw [← Real.rpow_add hxpos]
    norm_num
  have hsqrt : s * u = Real.sqrt x := by
    dsimp only [s, u]
    rw [← Real.rpow_add hxpos, Real.sqrt_eq_rpow]
    norm_num
  have hnonempty : (1 : ℝ) ≤ cWindow * u := by
    have h := (div_le_iff₀ hcWindow).mp hnonemptyBound
    nlinarith only [h]
  have hlinear : t0 * s ≤ cg * x := by
    have h := (div_le_iff₀ hcg).mp hlinearBound
    calc
      t0 * s ≤ (Real.rpow x (2 / 3 : ℝ) * cg) * s :=
        mul_le_mul_of_nonneg_right h hspos.le
      _ = cg * (s * Real.rpow x (2 / 3 : ℝ)) := by ring
      _ = cg * x := by rw [hproduct]
  have hsqrtRate : t0 * s ≤ Real.sqrt x / (2 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hsqrtBound hspos.le
    rw [mul_comm u s, hsqrt] at h
    linarith only [h]
  refine ⟨hn, hnonempty, ?_⟩
  intro z hz hzWindow
  change z ≤ cWindow * u at hzWindow
  change (6 : ℝ) * Real.exp (-(t0 * s)) +
      (2 : ℝ) * Real.exp (-cg * x) +
      (8 : ℝ) * Real.exp (-(Real.sqrt x) / (2 : ℝ)) ≤
    Real.exp (-(t0 / (2 : ℝ)) * s) * Shao.standardNormalTail z
  have hznonneg : 0 ≤ z := le_trans (by norm_num : (0 : ℝ) ≤ 1) hz
  have hzsquare : z ^ (2 : ℕ) ≤ cWindow ^ (2 : ℕ) * s := by
    calc
      z ^ (2 : ℕ) ≤ (cWindow * u) ^ (2 : ℕ) := by
        have h := mul_nonneg (sub_nonneg.mpr hzWindow)
          (add_nonneg (mul_nonneg hcWindow.le hupos.le) hznonneg)
        nlinarith only [h]
      _ = cWindow ^ (2 : ℕ) * s := by rw [mul_pow, husq]
  have hzexponent : z ^ (2 : ℕ) / (2 : ℝ) ≤ (t0 / (8 : ℝ)) * s := by
    have h := mul_le_mul_of_nonneg_right hcWindow_sq hspos.le
    nlinarith only [hzsquare, h]
  have hzdenom : 1 + z ≤ 1 + s := by
    have hcu : cWindow * u ≤ u := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hcWindow_one hupos.le
    linarith only [hzWindow, hcu, hus]
  have hzdenomPos : 0 < 1 + z := by linarith only [hz]
  have hsdenomPos : 0 < 1 + s := by linarith only [hspos]
  have hratio := Shao.standardNormalTail_ratio_bound z 0 hznonneg (by norm_num)
  rw [Shao.standardNormalTail_basic.2.1] at hratio
  norm_num only [add_zero, zero_pow, sub_zero, div_one] at hratio
  have hexpCancel :
      Real.exp (z ^ (2 : ℕ) / (2 : ℝ)) *
        Real.exp (-(z ^ (2 : ℕ)) / (2 : ℝ)) = 1 := by
    rw [← Real.exp_add]
    have hsum : z ^ (2 : ℕ) / (2 : ℝ) +
        -(z ^ (2 : ℕ)) / (2 : ℝ) = 0 := by ring
    rw [hsum, Real.exp_zero]
  have hratioScaled :
      (1 / 2 : ℝ) * Real.exp (-(z ^ (2 : ℕ)) / (2 : ℝ)) ≤
        (4 / 3 : ℝ) * (1 + z) * Shao.standardNormalTail z := by
    calc
      (1 / 2 : ℝ) * Real.exp (-(z ^ (2 : ℕ)) / (2 : ℝ)) ≤
          ((4 / 3 : ℝ) * (1 + z) *
            Real.exp (z ^ (2 : ℕ) / (2 : ℝ)) * Shao.standardNormalTail z) *
              Real.exp (-(z ^ (2 : ℕ)) / (2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hratio (Real.exp_pos _).le
      _ = (4 / 3 : ℝ) * (1 + z) * Shao.standardNormalTail z *
          (Real.exp (z ^ (2 : ℕ) / (2 : ℝ)) *
            Real.exp (-(z ^ (2 : ℕ)) / (2 : ℝ))) := by ring
      _ = (4 / 3 : ℝ) * (1 + z) * Shao.standardNormalTail z := by
        rw [hexpCancel, mul_one]
  have htailAtZ :
      (3 / 8 : ℝ) * Real.exp (-(z ^ (2 : ℕ)) / (2 : ℝ)) / (1 + z) ≤
        Shao.standardNormalTail z := by
    apply (div_le_iff₀ hzdenomPos).mpr
    nlinarith only [hratioScaled]
  have hexpWindow :
      Real.exp (-(t0 / (8 : ℝ)) * s) ≤
        Real.exp (-(z ^ (2 : ℕ)) / (2 : ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith only [hzexponent])
  have htailWindow :
      (3 / 8 : ℝ) * Real.exp (-(t0 / (8 : ℝ)) * s) / (1 + s) ≤
        Shao.standardNormalTail z := by
    apply (div_le_iff₀ hsdenomPos).mpr
    calc
      (3 / 8 : ℝ) * Real.exp (-(t0 / (8 : ℝ)) * s) ≤
          (3 / 8 : ℝ) * Real.exp (-(z ^ (2 : ℕ)) / (2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hexpWindow (by norm_num)
      _ ≤ Shao.standardNormalTail z * (1 + z) :=
        (div_le_iff₀ hzdenomPos).mp htailAtZ
      _ ≤ Shao.standardNormalTail z * (1 + s) :=
        mul_le_mul_of_nonneg_left hzdenom
          (Shao.standardNormalTail_basic.2.2.1 z).1.le
  have hcgExp : Real.exp (-cg * x) ≤ Real.exp (-(t0 * s)) :=
    Real.exp_le_exp.mpr (by nlinarith only [hlinear])
  have hsqrtExp : Real.exp (-(Real.sqrt x) / (2 : ℝ)) ≤
      Real.exp (-(t0 * s)) :=
    Real.exp_le_exp.mpr (by linarith only [hsqrtRate])
  have hnumerator :
      (6 : ℝ) * Real.exp (-(t0 * s)) +
        (2 : ℝ) * Real.exp (-cg * x) +
        (8 : ℝ) * Real.exp (-(Real.sqrt x) / (2 : ℝ)) ≤
          (16 : ℝ) * Real.exp (-(t0 * s)) := by
    linarith only [hcgExp, hsqrtExp]
  have hexpCombine :
      Real.exp (-b * s) * Real.exp (-(t0 / (2 : ℝ)) * s) *
        Real.exp (-(t0 / (8 : ℝ)) * s) = Real.exp (-(t0 * s)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp only [b]
    ring
  have hfactorIdentity :
      ((128 / 3 : ℝ) * (1 + s) * Real.exp (-b * s)) *
        (Real.exp (-(t0 / (2 : ℝ)) * s) *
          ((3 / 8 : ℝ) * Real.exp (-(t0 / (8 : ℝ)) * s) / (1 + s))) =
        (16 : ℝ) * Real.exp (-(t0 * s)) := by
    calc
      _ = (16 : ℝ) *
          (Real.exp (-b * s) * Real.exp (-(t0 / (2 : ℝ)) * s) *
            Real.exp (-(t0 / (8 : ℝ)) * s)) * ((1 + s) / (1 + s)) := by ring
      _ = (16 : ℝ) * Real.exp (-(t0 * s)) := by
        rw [div_self hsdenomPos.ne', mul_one, hexpCombine]
  have habsorb : (16 : ℝ) * Real.exp (-(t0 * s)) ≤
      Real.exp (-(t0 / (2 : ℝ)) * s) *
        ((3 / 8 : ℝ) * Real.exp (-(t0 / (8 : ℝ)) * s) / (1 + s)) := by
    have hnonneg : 0 ≤ Real.exp (-(t0 / (2 : ℝ)) * s) *
        ((3 / 8 : ℝ) * Real.exp (-(t0 / (8 : ℝ)) * s) / (1 + s)) := by
      positivity
    have h := mul_le_mul_of_nonneg_right hsmalln hnonneg
    rw [hfactorIdentity, one_mul] at h
    exact h
  exact hnumerator.trans (habsorb.trans
    (mul_le_mul_of_nonneg_left htailWindow (Real.exp_pos _).le))

end Shao.OQ6.OriginalExceptionalTailAbsorption
