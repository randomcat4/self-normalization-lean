import Shao.OQ4.RademacherCosine
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Private complete source for frozen SCA0, SCA1 and SCA2. -/

noncomputable section

namespace Shao.OQ4.RademacherScalarBounds

def H (m : ℕ) : ℝ := (m : ℝ) + 1
def u (m : ℕ) : ℝ := Real.pi / (4 * H m)
def z (m : ℕ) : ℝ := Real.pi / (2 * H m)
def a (m : ℕ) : ℝ := (1 / H m) * (Real.cos (u m) / Real.sin (u m))
def rho (m : ℕ) : ℝ := Real.cos (z m)
def lambda : ℝ := Real.pi ^ 2 / 8
def C_a : ℝ := Real.pi / 3
def C_rho : ℝ := Real.pi ^ 4 / 48

theorem z_eq_angle (m : ℕ) : z m = RademacherCosine.angle m := by
  rw [RademacherCosine.angle.eq_1]
  rfl

theorem rho_eq_cosine_rho (m : ℕ) : rho m = RademacherCosine.rho m := by
  rw [RademacherCosine.rho.eq_1, ← z_eq_angle]
  rfl

theorem H_ge_two {m : ℕ} (hm : 1 ≤ m) : 2 ≤ H m := by
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  dsimp [H]
  linarith

theorem H_pos {m : ℕ} (hm : 1 ≤ m) : 0 < H m := by
  linarith [H_ge_two hm]

theorem u_pos {m : ℕ} (hm : 1 ≤ m) : 0 < u m := by
  unfold u
  exact div_pos Real.pi_pos (mul_pos (by norm_num) (H_pos hm))

theorem u_le_pi_div_eight {m : ℕ} (hm : 1 ≤ m) : u m ≤ Real.pi / 8 := by
  unfold u
  apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num)
  linarith [H_ge_two hm]

theorem z_pos {m : ℕ} (hm : 1 ≤ m) : 0 < z m := by
  unfold z
  exact div_pos Real.pi_pos (mul_pos (by norm_num) (H_pos hm))

theorem z_le_pi_div_four {m : ℕ} (hm : 1 ≤ m) : z m ≤ Real.pi / 4 := by
  unfold z
  apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num)
  linarith [H_ge_two hm]

theorem sin_u_pos {m : ℕ} (hm : 1 ≤ m) : 0 < Real.sin (u m) := by
  apply Real.sin_pos_of_pos_of_lt_pi (u_pos hm)
  linarith [u_le_pi_div_eight hm, Real.pi_pos]

theorem cos_u_pos {m : ℕ} (hm : 1 ≤ m) : 0 < Real.cos (u m) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [u_pos hm, u_le_pi_div_eight hm, Real.pi_pos]

theorem cos_z_pos {m : ℕ} (hm : 1 ≤ m) : 0 < Real.cos (z m) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [z_pos hm, z_le_pi_div_four hm, Real.pi_pos]

theorem a_pos {m : ℕ} (hm : 1 ≤ m) : 0 < a m := by
  exact mul_pos (div_pos (by norm_num) (H_pos hm))
    (div_pos (cos_u_pos hm) (sin_u_pos hm))

theorem rho_pos {m : ℕ} (hm : 1 ≤ m) : 0 < rho m := cos_z_pos hm

theorem rho_lt_one {m : ℕ} (hm : 1 ≤ m) : rho m < 1 := by
  have hs : 0 < Real.sin (z m) := by
    apply Real.sin_pos_of_pos_of_lt_pi (z_pos hm)
    linarith [z_le_pi_div_four hm, Real.pi_pos]
  have hc := cos_z_pos hm
  have hid := Real.sin_sq_add_cos_sq (z m)
  have hs2 := sq_pos_of_pos hs
  dsimp [rho]
  nlinarith

theorem pi_mul_a_div_four_pos {m : ℕ} (hm : 1 ≤ m) : 0 < Real.pi * a m / 4 := by
  exact div_pos (mul_pos Real.pi_pos (a_pos hm)) (by norm_num)

theorem SCA0 {m : ℕ} (hm : 1 ≤ m) :
    2 ≤ H m ∧ 0 < H m ∧ 0 < H m ^ 2 ∧ 0 < H m ^ 4 ∧
    0 < u m ∧ u m ≤ Real.pi / 8 ∧ Real.pi / 8 < Real.pi / 2 ∧
    0 < z m ∧ z m ≤ Real.pi / 4 ∧ Real.pi / 4 < Real.pi / 2 ∧
    0 < Real.sin (u m) ∧ 0 < Real.cos (u m) ∧ 0 < Real.cos (z m) ∧
    0 < a m ∧ 0 < rho m ∧ rho m < 1 ∧ 0 < Real.pi * a m / 4 := by
  exact ⟨H_ge_two hm, H_pos hm, pow_pos (H_pos hm) 2, pow_pos (H_pos hm) 4,
    u_pos hm, u_le_pi_div_eight hm, by linarith [Real.pi_pos],
    z_pos hm, z_le_pi_div_four hm, by linarith [Real.pi_pos],
    sin_u_pos hm, cos_u_pos hm, cos_z_pos hm, a_pos hm, rho_pos hm,
    rho_lt_one hm, pi_mul_a_div_four_pos hm⟩

private theorem eval_nonneg_of_deriv {f f' : ℝ → ℝ} {t : ℝ}
    (ht : 0 ≤ t) (hzero : f 0 = 0)
    (hd : ∀ x ∈ Set.Icc 0 t, HasDerivAt f (f' x) x)
    (hn : ∀ x ∈ Set.Icc 0 t, 0 ≤ f' x) : 0 ≤ f t := by
  have hc : ContinuousOn f (Set.Icc 0 t) :=
    fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t) hc
    (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => hn x (interior_subset hx))
  have h := hm ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  simpa only [hzero] using h

private theorem cos_pos_on_quarter {t : ℝ} (ht : t ∈ Set.Icc 0 (Real.pi / 4)) :
    0 < Real.cos t := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [ht.1, ht.2, Real.pi_pos]

private theorem cos_sq_half_le {t : ℝ} (ht : t ∈ Set.Icc 0 (Real.pi / 4)) :
    (1 / 2 : ℝ) ≤ Real.cos t ^ 2 := by
  have hc : 0 ≤ Real.cos (2 * t) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> linarith [ht.1, ht.2, Real.pi_pos]
  rw [Real.cos_two_mul] at hc
  linarith

private theorem tan_sub_id_hasDeriv {x : ℝ} (hx : Real.cos x ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.tan t - t) (Real.tan x ^ 2) x := by
  convert (Real.hasDerivAt_tan hx).fun_sub (hasDerivAt_id x) using 1
  · rfl
  · rw [Real.tan_eq_sin_div_cos]
    field_simp [hx]
    nlinarith [Real.sin_sq_add_cos_sq x]

private theorem tan_ge_id {t : ℝ} (ht : t ∈ Set.Icc 0 (Real.pi / 4)) :
    t ≤ Real.tan t := by
  have h := eval_nonneg_of_deriv (f := fun x : ℝ => Real.tan x - x)
    (f' := fun x => Real.tan x ^ 2) ht.1 (by simp)
    (fun x hx => tan_sub_id_hasDeriv
      (ne_of_gt (cos_pos_on_quarter ⟨hx.1, hx.2.trans ht.2⟩)))
    (fun x _ => sq_nonneg (Real.tan x))
  linarith

private theorem tan_le_two_mul {t : ℝ} (ht : t ∈ Set.Icc 0 (Real.pi / 4)) :
    Real.tan t ≤ 2 * t := by
  have h := eval_nonneg_of_deriv (f := fun x : ℝ => 2 * x - Real.tan x)
    (f' := fun x => 2 - 1 / Real.cos x ^ 2) ht.1 (by simp)
    (by
      intro x hx
      convert ((hasDerivAt_id x).const_mul 2).fun_sub
        (Real.hasDerivAt_tan
          (ne_of_gt (cos_pos_on_quarter ⟨hx.1, hx.2.trans ht.2⟩))) using 1
      · rfl
      · ring)
    (by
      intro x hx
      have hb := cos_sq_half_le ⟨hx.1, hx.2.trans ht.2⟩
      have hp : 0 < Real.cos x ^ 2 := by linarith
      have hq : 1 / Real.cos x ^ 2 ≤ (2 : ℝ) := (div_le_iff₀ hp).2 (by linarith)
      linarith)
  linarith

private theorem tan_cubic_remainder {t : ℝ} (ht : t ∈ Set.Icc 0 (Real.pi / 4)) :
    0 ≤ Real.tan t - t ∧ Real.tan t - t ≤ (4 / 3 : ℝ) * t ^ 3 := by
  refine ⟨sub_nonneg.mpr (tan_ge_id ht), ?_⟩
  have h := eval_nonneg_of_deriv
    (f := fun x : ℝ => (4 / 3 : ℝ) * x ^ 3 - (Real.tan x - x))
    (f' := fun x => 4 * x ^ 2 - Real.tan x ^ 2) ht.1 (by simp)
    (by
      intro x hx
      convert (((hasDerivAt_id x).pow 3).const_mul (4 / 3 : ℝ)).fun_sub
        (tan_sub_id_hasDeriv
          (ne_of_gt (cos_pos_on_quarter ⟨hx.1, hx.2.trans ht.2⟩))) using 1
      · rfl
      · dsimp only [id]
        ring)
    (by
      intro x hx
      have hg := tan_ge_id ⟨hx.1, hx.2.trans ht.2⟩
      have hl := tan_le_two_mul ⟨hx.1, hx.2.trans ht.2⟩
      nlinarith [hx.1])
  linarith

private theorem log_cos_remainder_hasDeriv {x : ℝ} (hx : Real.cos x ≠ 0) :
    HasDerivAt (fun t : ℝ => -Real.log (Real.cos t) - t ^ 2 / 2)
      (Real.tan x - x) x := by
  convert (((Real.hasDerivAt_cos x).log hx).neg).fun_sub
    (((hasDerivAt_id x).pow 2).div_const 2) using 1
  · rfl
  · rw [Real.tan_eq_sin_div_cos]
    simp only [id_eq]
    ring

private theorem log_cos_quartic_remainder {t : ℝ}
    (ht : t ∈ Set.Icc 0 (Real.pi / 4)) :
    0 ≤ -Real.log (Real.cos t) - t ^ 2 / 2 ∧
      -Real.log (Real.cos t) - t ^ 2 / 2 ≤ t ^ 4 / 3 := by
  constructor
  · apply eval_nonneg_of_deriv (f' := fun x => Real.tan x - x) ht.1 (by simp)
    · intro x hx
      exact log_cos_remainder_hasDeriv
        (ne_of_gt (cos_pos_on_quarter ⟨hx.1, hx.2.trans ht.2⟩))
    · intro x hx
      exact (tan_cubic_remainder ⟨hx.1, hx.2.trans ht.2⟩).1
  · have h := eval_nonneg_of_deriv
      (f := fun x : ℝ => x ^ 4 / 3 - (-Real.log (Real.cos x) - x ^ 2 / 2))
      (f' := fun x => (4 / 3 : ℝ) * x ^ 3 - (Real.tan x - x)) ht.1 (by simp)
      (by
        intro x hx
        convert (((hasDerivAt_id x).pow 4).div_const 3).fun_sub
          (log_cos_remainder_hasDeriv
            (ne_of_gt (cos_pos_on_quarter ⟨hx.1, hx.2.trans ht.2⟩))) using 1
        · rfl
        · dsimp only [id]
          ring)
      (by
        intro x hx
        exact sub_nonneg.mpr (tan_cubic_remainder ⟨hx.1, hx.2.trans ht.2⟩).2)
    linarith

theorem C_a_pos : 0 < C_a := div_pos Real.pi_pos (by norm_num)
theorem C_rho_pos : 0 < C_rho := div_pos (pow_pos Real.pi_pos 4) (by norm_num)

theorem SCA1 {m : ℕ} (hm : 1 ≤ m) : |a m - 4 / Real.pi| ≤ C_a / H m ^ 2 := by
  have hu := u_pos hm
  have huI : u m ∈ Set.Icc 0 (Real.pi / 4) := by
    constructor
    · exact hu.le
    · linarith [u_le_pi_div_eight hm, Real.pi_pos]
  have hge := tan_ge_id huI
  have htpos : 0 < Real.tan (u m) := hu.trans_le hge
  have hthird := (tan_cubic_remainder huI).2
  have hid : a m = (4 / Real.pi) * (u m / Real.tan (u m)) := by
    unfold a
    rw [Real.tan_eq_sin_div_cos]
    unfold u
    field_simp [ne_of_gt (H_pos hm), Real.pi_ne_zero,
      ne_of_gt (sin_u_pos hm), ne_of_gt (cos_u_pos hm)]
  have hratio : u m / Real.tan (u m) ≤ 1 := (div_le_one htpos).2 hge
  have hale : a m ≤ 4 / Real.pi := by
    rw [hid]
    nlinarith [mul_le_mul_of_nonneg_left hratio
      (show 0 ≤ 4 / Real.pi by positivity)]
  have hr : (Real.tan (u m) - u m) / Real.tan (u m) ≤ (4 / 3 : ℝ) * u m ^ 2 := by
    calc
      _ ≤ ((4 / 3 : ℝ) * u m ^ 3) / Real.tan (u m) :=
        div_le_div_of_nonneg_right hthird htpos.le
      _ ≤ ((4 / 3 : ℝ) * u m ^ 3) / u m :=
        div_le_div_of_nonneg_left (by positivity) hu hge
      _ = (4 / 3 : ℝ) * u m ^ 2 := by field_simp
  calc
    |a m - 4 / Real.pi| = (4 / Real.pi) *
        ((Real.tan (u m) - u m) / Real.tan (u m)) := by
      rw [abs_of_nonpos (sub_nonpos.mpr hale), hid]
      field_simp
      ring
    _ ≤ (4 / Real.pi) * ((4 / 3 : ℝ) * u m ^ 2) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ = C_a / H m ^ 2 := by
      unfold C_a u
      field_simp

theorem SCA2 {m : ℕ} (hm : 1 ≤ m) :
    |Real.log (rho m) + lambda / H m ^ 2| ≤ C_rho / H m ^ 4 := by
  have hzI : z m ∈ Set.Icc 0 (Real.pi / 4) := ⟨(z_pos hm).le, z_le_pi_div_four hm⟩
  have hb := log_cos_quartic_remainder hzI
  have hlead : lambda / H m ^ 2 = z m ^ 2 / 2 := by
    unfold lambda z
    field_simp
    ring
  rw [hlead, rho, abs_of_nonpos (by linarith [hb.1])]
  calc
    _ = -Real.log (Real.cos (z m)) - z m ^ 2 / 2 := by ring
    _ ≤ z m ^ 4 / 3 := hb.2
    _ = C_rho / H m ^ 4 := by
      unfold C_rho z
      field_simp
      ring

theorem scalar_bounds : ∃ Ca : ℝ, ∃ Crho : ℝ, 0 < Ca ∧ 0 < Crho ∧
    ∀ m : ℕ, 1 ≤ m →
      (|a m - 4 / Real.pi| ≤ Ca / ((m : ℝ) + 1) ^ 2 ∧
       |Real.log (rho m) + (Real.pi ^ 2 / 8) / ((m : ℝ) + 1) ^ 2| ≤
         Crho / ((m : ℝ) + 1) ^ 4) := by
  exact ⟨C_a, C_rho, C_a_pos, C_rho_pos, fun _ hm => ⟨SCA1 hm, SCA2 hm⟩⟩

end Shao.OQ4.RademacherScalarBounds
