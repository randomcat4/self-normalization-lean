import Shao.OQ4.RademacherScalarBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Private source draft of frozen DA1. Mechanical status is recorded in the separate receipt.
The fixed scalar definitions and certified estimates are imported above.
No sequence specialization or probabilistic assertion is part of this module.
-/

noncomputable section

namespace Shao.OQ4.RademacherLatticeShift

open Shao.OQ4.RademacherScalarBounds

/-- The displacement in the left-closed, right-open weak lattice cell. -/
def delta (m : ℕ) (h : ℝ) : ℝ := H m - h

/-- The numerical lower bound used in the internal logarithm estimate. -/
def cos_lower : ℝ := Real.cos (Real.pi / 8)

/-- An absolute constant, fixed before every lattice parameter. -/
def C_log : ℝ := (Real.pi * C_a / 4) / cos_lower

/-- The constant in the finite DA1 bound. -/
def C : ℝ := C_rho + 3 * lambda + C_log

private theorem lambda_pos : 0 < lambda := by
  change 0 < Real.pi ^ 2 / 8
  positivity

private theorem cos_lower_pos : 0 < cos_lower := by
  unfold cos_lower
  exact Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

private theorem cos_lower_le_one : cos_lower ≤ 1 :=
  Real.cos_le_one _

theorem C_log_pos : 0 < C_log := by
  unfold C_log
  exact div_pos (div_pos (mul_pos Real.pi_pos C_a_pos) (by norm_num)) cos_lower_pos

theorem C_pos : 0 < C := by
  unfold C
  exact add_pos (add_pos C_rho_pos (mul_pos (by norm_num) lambda_pos)) C_log_pos

/-- Cell geometry includes the weak integer endpoint. -/
theorem cell_legality {m : ℕ} (hm : 1 ≤ m) {h : ℝ}
    (hmh : (m : ℝ) ≤ h) (hmh1 : h < (m : ℝ) + 1) :
    1 ≤ h ∧ 0 < h ∧ 2 ≤ H m ∧ 0 < H m ∧
      H m = h + delta m h ∧ 0 < delta m h ∧ delta m h ≤ 1 := by
  have hmreal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hh1 : 1 ≤ h := hmreal.trans hmh
  have hh : 0 < h := lt_of_lt_of_le (by norm_num) hh1
  have hd : 0 < delta m h := by
    change 0 < ((m : ℝ) + 1) - h
    linarith
  have hd1 : delta m h ≤ 1 := by
    change ((m : ℝ) + 1) - h ≤ 1
    linarith
  refine ⟨hh1, hh, H_ge_two hm, H_pos hm, ?_, hd, hd1⟩
  dsimp [delta]
  ring

/-- At a weak integer threshold the displacement is exactly one. -/
theorem delta_at_left (m : ℕ) : delta m (m : ℝ) = 1 := by
  change ((m : ℝ) + 1) - (m : ℝ) = 1
  ring

/-- All displayed denominators and logarithm arguments are legitimate. -/
theorem DA0 {m : ℕ} (hm : 1 ≤ m) {h : ℝ}
    (hmh : (m : ℝ) ≤ h) (hmh1 : h < (m : ℝ) + 1) :
    1 ≤ h ∧ 0 < h ∧ 2 ≤ H m ∧ 0 < H m ∧
      H m = h + delta m h ∧ 0 < delta m h ∧ delta m h ≤ 1 ∧
      h ^ 2 ≠ 0 ∧ h ^ 3 ≠ 0 ∧ h ^ 4 ≠ 0 ∧
      (H m) ^ 2 ≠ 0 ∧ (H m) ^ 4 ≠ 0 ∧
      4 * H m ≠ 0 ∧ 2 * H m ≠ 0 ∧ Real.sin (u m) ≠ 0 ∧
      0 < a m ∧ 0 < rho m ∧ rho m < 1 ∧ 0 < Real.pi * a m / 4 := by
  rcases cell_legality hm hmh hmh1 with ⟨hh1, hh, hH2, hH, hEq, hd, hd1⟩
  exact ⟨hh1, hh, hH2, hH, hEq, hd, hd1,
    pow_ne_zero 2 hh.ne', pow_ne_zero 3 hh.ne', pow_ne_zero 4 hh.ne',
    pow_ne_zero 2 hH.ne', pow_ne_zero 4 hH.ne',
    mul_ne_zero (by norm_num) hH.ne', mul_ne_zero (by norm_num) hH.ne',
    (sin_u_pos hm).ne', a_pos hm, rho_pos hm, rho_lt_one hm,
    pi_mul_a_div_four_pos hm⟩

private theorem normalized_a_lower_bound {m : ℕ} (hm : 1 ≤ m) :
    cos_lower ≤ Real.pi * a m / 4 := by
  have hu : 0 < u m := u_pos hm
  have hsu : 0 < Real.sin (u m) := sin_u_pos hm
  have hcu : 0 < Real.cos (u m) := cos_u_pos hm
  have hsin : Real.sin (u m) ≤ u m := Real.sin_le hu.le
  have hcos : cos_lower ≤ Real.cos (u m) := by
    exact Real.cos_le_cos_of_nonneg_of_le_pi hu.le
      (by linarith [Real.pi_pos] : Real.pi / 8 ≤ Real.pi)
      (u_le_pi_div_eight hm)
  have hratio : Real.cos (u m) ≤ u m * Real.cos (u m) / Real.sin (u m) := by
    apply (le_div_iff₀ hsu).2
    nlinarith [mul_le_mul_of_nonneg_right hsin hcu.le]
  calc
    cos_lower ≤ Real.cos (u m) := hcos
    _ ≤ u m * Real.cos (u m) / Real.sin (u m) := hratio
    _ = Real.pi * a m / 4 := by
      change (Real.pi / (4 * H m)) * Real.cos (u m) / Real.sin (u m) =
        Real.pi * ((1 / H m) * (Real.cos (u m) / Real.sin (u m))) / 4
      field_simp [(H_pos hm).ne', hsu.ne']

private theorem normalized_a_error_bound {m : ℕ} (hm : 1 ≤ m) :
    |Real.pi * a m / 4 - 1| ≤ (Real.pi * C_a / 4) / (H m) ^ 2 := by
  have hpi4 : 0 < Real.pi / 4 := by positivity
  have heq : Real.pi * a m / 4 - 1 =
      (Real.pi / 4) * (a m - 4 / Real.pi) := by
    field_simp [Real.pi_ne_zero]
  calc
    |Real.pi * a m / 4 - 1| = (Real.pi / 4) * |a m - 4 / Real.pi| := by
      rw [heq, abs_mul, abs_of_pos hpi4]
    _ ≤ (Real.pi / 4) * (C_a / (H m) ^ 2) :=
      mul_le_mul_of_nonneg_left (SCA1 hm) hpi4.le
    _ = (Real.pi * C_a / 4) / (H m) ^ 2 := by ring

/-- Mean-value estimate on the positive half-line beginning at `c`. -/
private theorem log_abs_le_of_lower {q c : ℝ} (hc : 0 < c)
    (hc1 : c ≤ 1) (hcq : c ≤ q) :
    |Real.log q| ≤ c⁻¹ * |q - 1| := by
  have hderiv : ∀ x ∈ Set.Ici c,
      HasDerivWithinAt Real.log x⁻¹ (Set.Ici c) x := by
    intro x hx
    exact (Real.hasDerivAt_log (ne_of_gt (lt_of_lt_of_le hc hx))).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ici c, ‖x⁻¹‖ ≤ c⁻¹ := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hc hx
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxpos)]
    simpa only [one_div] using one_div_le_one_div_of_le hc hx
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := Real.log) (f' := fun x : ℝ => x⁻¹) (s := Set.Ici c)
    (x := (1 : ℝ)) (y := q) hderiv hbound (convex_Ici c) hc1 hcq
  simpa only [Real.norm_eq_abs, Real.log_one, sub_zero] using h

/-- The internal logarithm bound is proved from the actual Scalar interface. -/
theorem normalized_log_bound {m : ℕ} (hm : 1 ≤ m) :
    |Real.log (Real.pi * a m / 4)| ≤ C_log / (H m) ^ 2 := by
  calc
    |Real.log (Real.pi * a m / 4)| ≤
        cos_lower⁻¹ * |Real.pi * a m / 4 - 1| :=
      log_abs_le_of_lower cos_lower_pos cos_lower_le_one (normalized_a_lower_bound hm)
    _ ≤ cos_lower⁻¹ * ((Real.pi * C_a / 4) / (H m) ^ 2) :=
      mul_le_mul_of_nonneg_left (normalized_a_error_bound hm) (inv_pos.mpr cos_lower_pos).le
    _ = C_log / (H m) ^ 2 := by
      unfold C_log
      ring

private theorem displacement_identity (m : ℕ) (h : ℝ)
    (hh : h ≠ 0) (hH : H m ≠ 0) :
    1 / h ^ 2 - 1 / (H m) ^ 2 - 2 * delta m h / h ^ 3 =
      -(delta m h ^ 2 * (3 * h + 2 * delta m h)) / (h ^ 3 * (H m) ^ 2) := by
  dsimp [delta]
  field_simp [hh, hH]
  ring

/-- A uniform second-order displacement remainder on every weak cell. -/
theorem displacement_remainder_bound {m : ℕ} (hm : 1 ≤ m) {h : ℝ}
    (hmh : (m : ℝ) ≤ h) (hmh1 : h < (m : ℝ) + 1) :
    |1 / h ^ 2 - 1 / (H m) ^ 2 - 2 * delta m h / h ^ 3| ≤ 3 / h ^ 4 := by
  rcases cell_legality hm hmh hmh1 with ⟨_, hh, _, hH, hEq, hd, hd1⟩
  have hfactor : 0 < 3 * h + 2 * delta m h := by positivity
  have hd2 : delta m h ^ 2 ≤ 1 := by
    calc
      delta m h ^ 2 = delta m h * delta m h := by ring
      _ ≤ 1 * 1 := mul_le_mul hd1 hd1 hd.le (by norm_num)
      _ = 1 := by norm_num
  have hbase : h * (3 * h + 2 * delta m h) ≤ 3 * (H m) ^ 2 := by
    rw [hEq]
    nlinarith [mul_nonneg hh.le hd.le, sq_nonneg (delta m h)]
  have hcore : delta m h ^ 2 * (h * (3 * h + 2 * delta m h)) ≤
      3 * (H m) ^ 2 := by
    calc
      delta m h ^ 2 * (h * (3 * h + 2 * delta m h)) ≤
          1 * (h * (3 * h + 2 * delta m h)) :=
        mul_le_mul_of_nonneg_right hd2 (mul_nonneg hh.le hfactor.le)
      _ = h * (3 * h + 2 * delta m h) := one_mul _
      _ ≤ 3 * (H m) ^ 2 := hbase
  calc
    |1 / h ^ 2 - 1 / (H m) ^ 2 - 2 * delta m h / h ^ 3| =
        delta m h ^ 2 * (3 * h + 2 * delta m h) / (h ^ 3 * (H m) ^ 2) := by
      rw [displacement_identity m h hh.ne' hH.ne']
      simp only [abs_div, abs_neg, abs_mul,
        abs_of_nonneg (sq_nonneg (delta m h)), abs_of_pos hfactor,
        abs_of_pos (pow_pos hh 3), abs_of_pos (pow_pos hH 2)]
    _ ≤ 3 / h ^ 4 := by
      apply (div_le_div_iff₀ (mul_pos (pow_pos hh 3) (pow_pos hH 2)) (pow_pos hh 4)).2
      calc
        delta m h ^ 2 * (3 * h + 2 * delta m h) * h ^ 4 =
            h ^ 3 * (delta m h ^ 2 * (h * (3 * h + 2 * delta m h))) := by ring
        _ ≤ h ^ 3 * (3 * (H m) ^ 2) :=
          mul_le_mul_of_nonneg_left hcore (pow_pos hh 3).le
        _ = 3 * (h ^ 3 * (H m) ^ 2) := by ring

/-- DA1 with the explicitly selected absolute constant. Natural time may be zero. -/
theorem finite_bound {m : ℕ} (hm : 1 ≤ m) {h : ℝ}
    (hmh : (m : ℝ) ≤ h) (hmh1 : h < (m : ℝ) + 1) (n : ℕ) :
    |lambda * (n : ℝ) / h ^ 2 + (n : ℝ) * Real.log (rho m) +
        Real.log (Real.pi * a m / 4) -
        (2 * lambda) * ((n : ℝ) / h ^ 3) * delta m h| ≤
      C * ((n : ℝ) / h ^ 4 + 1 / (H m) ^ 2) := by
  rcases cell_legality hm hmh hmh1 with ⟨_, hh, _, hH, _, _, _⟩
  have hN : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hhH : h ≤ H m := by
    change h ≤ (m : ℝ) + 1
    exact hmh1.le
  have hpow : h ^ 4 ≤ (H m) ^ 4 := pow_le_pow_left₀ hh.le hhH 4
  have hinv : 1 / (H m) ^ 4 ≤ 1 / h ^ 4 :=
    one_div_le_one_div_of_le (pow_pos hh 4) hpow
  have hrho : |(n : ℝ) * (Real.log (rho m) + lambda / (H m) ^ 2)| ≤
      C_rho * ((n : ℝ) / h ^ 4) := by
    calc
      |(n : ℝ) * (Real.log (rho m) + lambda / (H m) ^ 2)| =
          (n : ℝ) * |Real.log (rho m) + lambda / (H m) ^ 2| := by
        rw [abs_mul, abs_of_nonneg hN]
      _ ≤ (n : ℝ) * (C_rho / (H m) ^ 4) :=
        mul_le_mul_of_nonneg_left (SCA2 hm) hN
      _ = (C_rho * (n : ℝ)) * (1 / (H m) ^ 4) := by ring
      _ ≤ (C_rho * (n : ℝ)) * (1 / h ^ 4) :=
        mul_le_mul_of_nonneg_left hinv (mul_nonneg C_rho_pos.le hN)
      _ = C_rho * ((n : ℝ) / h ^ 4) := by ring
  have hshift : |lambda * (n : ℝ) *
      (1 / h ^ 2 - 1 / (H m) ^ 2 - 2 * delta m h / h ^ 3)| ≤
      (3 * lambda) * ((n : ℝ) / h ^ 4) := by
    calc
      |lambda * (n : ℝ) *
          (1 / h ^ 2 - 1 / (H m) ^ 2 - 2 * delta m h / h ^ 3)| =
          (lambda * (n : ℝ)) *
            |1 / h ^ 2 - 1 / (H m) ^ 2 - 2 * delta m h / h ^ 3| := by
        rw [abs_mul, abs_of_nonneg (mul_nonneg lambda_pos.le hN)]
      _ ≤ (lambda * (n : ℝ)) * (3 / h ^ 4) :=
        mul_le_mul_of_nonneg_left (displacement_remainder_bound hm hmh hmh1)
          (mul_nonneg lambda_pos.le hN)
      _ = (3 * lambda) * ((n : ℝ) / h ^ 4) := by ring
  have hdecomp :
      lambda * (n : ℝ) / h ^ 2 + (n : ℝ) * Real.log (rho m) +
          Real.log (Real.pi * a m / 4) -
          (2 * lambda) * ((n : ℝ) / h ^ 3) * delta m h =
        (n : ℝ) * (Real.log (rho m) + lambda / (H m) ^ 2) +
          lambda * (n : ℝ) *
            (1 / h ^ 2 - 1 / (H m) ^ 2 - 2 * delta m h / h ^ 3) +
          Real.log (Real.pi * a m / 4) := by ring
  have hX : 0 ≤ (n : ℝ) / h ^ 4 := div_nonneg hN (pow_pos hh 4).le
  have hY : 0 ≤ 1 / (H m) ^ 2 := by positivity
  have hA : 0 ≤ C_rho + 3 * lambda :=
    (add_pos C_rho_pos (mul_pos (by norm_num) lambda_pos)).le
  calc
    |lambda * (n : ℝ) / h ^ 2 + (n : ℝ) * Real.log (rho m) +
        Real.log (Real.pi * a m / 4) -
        (2 * lambda) * ((n : ℝ) / h ^ 3) * delta m h| =
        |(n : ℝ) * (Real.log (rho m) + lambda / (H m) ^ 2) +
          lambda * (n : ℝ) *
            (1 / h ^ 2 - 1 / (H m) ^ 2 - 2 * delta m h / h ^ 3) +
          Real.log (Real.pi * a m / 4)| := by rw [hdecomp]
    _ ≤ (|(n : ℝ) * (Real.log (rho m) + lambda / (H m) ^ 2)| +
          |lambda * (n : ℝ) *
            (1 / h ^ 2 - 1 / (H m) ^ 2 - 2 * delta m h / h ^ 3)|) +
          |Real.log (Real.pi * a m / 4)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (C_rho * ((n : ℝ) / h ^ 4) +
          (3 * lambda) * ((n : ℝ) / h ^ 4)) + C_log / (H m) ^ 2 :=
      add_le_add (add_le_add hrho hshift) (normalized_log_bound hm)
    _ = (C_rho + 3 * lambda) * ((n : ℝ) / h ^ 4) +
          C_log * (1 / (H m) ^ 2) := by ring
    _ ≤ C * ((n : ℝ) / h ^ 4 + 1 / (H m) ^ 2) := by
      unfold C
      nlinarith [mul_nonneg hA hY, mul_nonneg C_log_pos.le hX]

/-- The frozen finite quantitative statement, with the original coefficient and quantifiers. -/
theorem DA1 : ∃ K : ℝ, 0 < K ∧
    ∀ m : ℕ, 1 ≤ m →
      ∀ h : ℝ, (m : ℝ) ≤ h → h < (m : ℝ) + 1 →
        ∀ n : ℕ,
          |(Real.pi ^ 2 / 8) * (n : ℝ) / h ^ 2 +
              (n : ℝ) * Real.log (rho m) + Real.log (Real.pi * a m / 4) -
              (Real.pi ^ 2 / 4) * ((n : ℝ) / h ^ 3) * (H m - h)| ≤
            K * ((n : ℝ) / h ^ 4 + 1 / (H m) ^ 2) := by
  refine ⟨C, C_pos, ?_⟩
  intro m hm h hmh hmh1 n
  have hcoef : 2 * lambda = Real.pi ^ 2 / 4 := by
    change 2 * (Real.pi ^ 2 / 8) = Real.pi ^ 2 / 4
    ring
  have hb := finite_bound hm hmh hmh1 n
  rw [hcoef] at hb
  exact hb

end Shao.OQ4.RademacherLatticeShift
