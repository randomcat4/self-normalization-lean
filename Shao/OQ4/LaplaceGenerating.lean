import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Shao.OQ4
open Finset Filter
open scoped Topology

noncomputable def laplaceW (A : ℕ → ℝ) (s : ℝ) : ℝ :=
  ∑' n : ℕ, s ^ (n + 1) * A (n + 1) / (n + 1)

noncomputable def laplaceG (a : ℕ → ℝ) (s : ℝ) : ℝ := ∑' j : ℕ, s ^ j * a j

theorem summable_laplaceW (A : ℕ → ℝ) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hA : ∀ k, 1 ≤ k → 0 ≤ A k ∧ A k ≤ 1) :
    Summable (fun n : ℕ => s ^ (n + 1) * A (n + 1) / (n + 1)) := by
  apply Summable.of_norm_bounded (summable_geometric_of_norm_lt_one (by
    rwa [Real.norm_eq_abs, abs_of_pos hs0]))
  intro n
  have hAn := hA (n + 1) (by omega)
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg (pow_nonneg hs0.le _) hAn.1) (by positivity))]
  calc
    _ ≤ s ^ (n + 1) / (n + 1) := div_le_div_of_nonneg_right
      (mul_le_of_le_one_right (pow_nonneg hs0.le _) hAn.2) (by positivity)
    _ ≤ s ^ (n + 1) := div_le_self (pow_nonneg hs0.le _) hn
    _ ≤ s ^ n := by simpa [pow_succ] using mul_le_of_le_one_right (pow_nonneg hs0.le n) hs1.le

theorem summable_laplaceG (a : ℕ → ℝ) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ 1) : Summable (fun j : ℕ => s ^ j * a j) := by
  apply Summable.of_norm_bounded (summable_geometric_of_norm_lt_one (by
    rwa [Real.norm_eq_abs, abs_of_pos hs0]))
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hs0.le _) (ha j).1)]
  exact mul_le_of_le_one_right (pow_nonneg hs0.le _) (ha j).2

theorem exp_neg_reciprocal_gap (m : ℕ) (hm : 1 ≤ m) :
    0 < Real.exp (-1 / (m : ℝ)) ∧ Real.exp (-1 / (m : ℝ)) < 1 ∧
      1 / (2 * (m : ℝ)) ≤ 1 - Real.exp (-1 / (m : ℝ)) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hx : 0 < (m : ℝ)⁻¹ := inv_pos.mpr hmpos
  have hx1 : (m : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hmpos).mpr hmone
  have he := Real.add_one_le_exp ((m : ℝ)⁻¹)
  have hep : 0 < Real.exp (-(m : ℝ)⁻¹) := Real.exp_pos _
  have hprod : ((m : ℝ)⁻¹ + 1) * Real.exp (-(m : ℝ)⁻¹) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right he hep.le
    rw [← Real.exp_add] at hh
    simpa using hh
  have hbound : Real.exp (-(m : ℝ)⁻¹) ≤ 1 - (m : ℝ)⁻¹ / 2 := by
    have hdiv : Real.exp (-(m : ℝ)⁻¹) ≤ 1 / ((m : ℝ)⁻¹ + 1) :=
      (le_div_iff₀ (by positivity)).mpr (by nlinarith [hprod])
    have hi : 1 / ((m : ℝ)⁻¹ + 1) ≤ 1 - (m : ℝ)⁻¹ / 2 := by
      apply (div_le_iff₀ (by positivity : 0 < (m : ℝ)⁻¹ + 1)).mpr
      nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hx1)]
    exact hdiv.trans hi
  refine ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) hmpos), ?_⟩
  have heq : -1 / (m : ℝ) = -(m : ℝ)⁻¹ := by ring_nf
  rw [heq]
  have hr : 1 / (2 * (m : ℝ)) = (m : ℝ)⁻¹ / 2 := by ring_nf
  rw [hr]
  linarith


theorem generating_upper_of_W_lower (G W L C s : ℝ) (hL : 0 < L) (_hs0 : 0 < s) (hs1 : s < 1)
    (hW : -(1 / 2) * Real.log (1 - s) - Real.log L - (1 + 3 * C) ≤ W)
    (hSP : G = (1 - s)⁻¹ * Real.exp (-W)) :
    G ≤ Real.exp (1 + 3 * C) * L / Real.sqrt (1 - s) := by
  have ht : 0 < 1 - s := by linarith
  have hroot : 0 < Real.sqrt (1 - s) := Real.sqrt_pos.mpr ht
  have he := Real.exp_le_exp.mpr (show -W ≤ (1 / 2) * Real.log (1 - s) + Real.log L + (1 + 3 * C) by linarith)
  have hlog : (1 / 2) * Real.log (1 - s) = Real.log (Real.sqrt (1 - s)) := by
    rw [Real.log_sqrt ht.le]
    ring_nf
  rw [hlog, Real.exp_add, Real.exp_add, Real.exp_log hroot, Real.exp_log hL] at he
  have hid : (1 - s)⁻¹ * Real.sqrt (1 - s) = (Real.sqrt (1 - s))⁻¹ := by
    apply (mul_right_cancel₀ hroot.ne')
    rw [mul_assoc, Real.mul_self_sqrt ht.le, inv_mul_cancel₀ ht.ne', inv_mul_cancel₀ hroot.ne']
  rw [hSP]
  calc
    _ ≤ (1 - s)⁻¹ * (Real.sqrt (1 - s) * L * Real.exp (1 + 3 * C)) :=
      mul_le_mul_of_nonneg_left he (inv_nonneg.mpr ht.le)
    _ = (Real.exp (1 + 3 * C) * L) * ((1 - s)⁻¹ * Real.sqrt (1 - s)) := by ring_nf
    _ = Real.exp (1 + 3 * C) * L / Real.sqrt (1 - s) := by rw [hid]; rfl

/-- A deterministic coefficient estimate for any genuinely summable bounded sequence. -/
theorem antitone_coefficient_bound_of_generating_bound (a : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ 1) (hanti : Antitone a)
    (hG : ∀ s : ℝ, 0 < s → s < 1 → laplaceG a s ≤ B / Real.sqrt (1 - s))
    (m : ℕ) (hm : 1 ≤ m) :
    a m ≤ Real.sqrt 2 * Real.exp 1 * B / Real.sqrt m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hmroot : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmpos
  let s := Real.exp (-1 / (m : ℝ))
  obtain ⟨hs0, hs1, hgap⟩ := exp_neg_reciprocal_gap m hm
  change 0 < s at hs0
  change s < 1 at hs1
  change 1 / (2 * (m : ℝ)) ≤ 1 - s at hgap
  have hspow : s ^ m = Real.exp (-1) := by
    dsimp [s]
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  have hsum := summable_laplaceG a hs0 hs1 ha
  have hprefix : (m : ℝ) * s ^ m * a m ≤ laplaceG a s := by
    calc
      _ = ∑ j ∈ range m, s ^ m * a m := by simp; ring_nf
      _ ≤ ∑ j ∈ range m, s ^ j * a j := by
        apply sum_le_sum
        intro j hj
        have hjm : j ≤ m := (mem_range.mp hj).le
        exact mul_le_mul (pow_le_pow_of_le_one hs0.le hs1.le hjm) (hanti hjm)
          (ha m).1 (pow_nonneg hs0.le j)
      _ ≤ laplaceG a s := Summable.sum_le_tsum (range m)
        (fun j _ => mul_nonneg (pow_nonneg hs0.le j) (ha j).1) hsum
  rw [hspow] at hprefix
  have hcancel : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
  have haG : a m ≤ Real.exp 1 * laplaceG a s / (m : ℝ) := by
    apply (le_div_iff₀ hmpos).mpr
    calc
      _ = (Real.exp 1 * Real.exp (-1)) * ((m : ℝ) * a m) := by rw [hcancel]; ring_nf
      _ = Real.exp 1 * ((m : ℝ) * Real.exp (-1) * a m) := by ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left hprefix (Real.exp_pos 1).le
  have hroot2 : 0 < Real.sqrt (2 * (m : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hgroot := Real.sqrt_le_sqrt hgap
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one] at hgroot
  have hinv : 1 / Real.sqrt (1 - s) ≤ Real.sqrt (2 * (m : ℝ)) := by
    have hi := one_div_le_one_div_of_le (div_pos (by norm_num : (0 : ℝ) < 1) hroot2) hgroot
    simpa using hi
  have hG' : laplaceG a s ≤ B * Real.sqrt (2 * (m : ℝ)) := by
    calc
      _ ≤ B / Real.sqrt (1 - s) := hG s hs0 hs1
      _ = B * (1 / Real.sqrt (1 - s)) := by ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left hinv hB
  have hid : Real.sqrt (m : ℝ) / (m : ℝ) = (Real.sqrt (m : ℝ))⁻¹ := by
    apply (mul_right_cancel₀ hmroot.ne')
    rw [div_mul_eq_mul_div, Real.mul_self_sqrt hmpos.le, div_self hmpos.ne', inv_mul_cancel₀ hmroot.ne']
  calc
    _ ≤ Real.exp 1 * laplaceG a s / (m : ℝ) := haG
    _ ≤ Real.exp 1 * (B * Real.sqrt (2 * (m : ℝ))) / (m : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hG' (Real.exp_pos 1).le) hmpos.le
    _ = (Real.sqrt 2 * Real.exp 1 * B) * (Real.sqrt (m : ℝ) / (m : ℝ)) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      ring_nf
    _ = _ := by rw [hid]; rfl

theorem reciprocal_log_step (x : ℝ) (hx : 0 < x) :
    (x + 1)⁻¹ ≤ Real.log (x + 1) - Real.log x := by
  have hxp : 0 < x + 1 := by linarith
  have hh := Real.one_sub_inv_le_log_of_pos (div_pos hxp hx)
  rw [Real.log_div hxp.ne' hx.ne'] at hh
  have he : 1 - ((x + 1) / x)⁻¹ = (x + 1)⁻¹ := by field_simp; ring_nf
  rwa [he] at hh

theorem finite_harmonic_log_bound (J : ℕ) :
    (∑ n ∈ range J, ((n : ℝ) + 1)⁻¹) ≤ 1 + Real.log (J : ℝ) := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    by_cases hJ : J = 0
    · simp [hJ]
    have hj : (0 : ℝ) < J := by exact_mod_cast Nat.pos_of_ne_zero hJ
    rw [sum_range_succ]
    have hh := reciprocal_log_step (J : ℝ) hj
    push_cast
    linarith

theorem sqrt_reciprocal_step (x : ℝ) (hx : 0 < x) :
    1 / ((x + 1) * Real.sqrt (x + 1)) ≤
      2 * ((Real.sqrt x)⁻¹ - (Real.sqrt (x + 1))⁻¹) := by
  let a := Real.sqrt x
  let b := Real.sqrt (x + 1)
  have ha : 0 < a := Real.sqrt_pos.mpr hx
  have hb : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have ha2 : a ^ 2 = x := Real.sq_sqrt hx.le
  have hb2 : b ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
  have hcancel : (a + b) * (b - a) = 1 := by nlinarith
  have hcoef : a * (a + b) ≤ 2 * b ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hab hb.le
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hcoef (sub_nonneg.mpr hab)
  have hleft : a * (a + b) * (b - a) = a := by rw [mul_assoc, hcancel, mul_one]
  rw [hleft] at hh
  have hf : 2 * (a⁻¹ - b⁻¹) = (2 * (b - a)) / (a * b) := by field_simp
  change 1 / ((x + 1) * b) ≤ 2 * (a⁻¹ - b⁻¹)
  rw [hf]
  apply (div_le_div_iff₀ (mul_pos (by linarith : 0 < x + 1) hb) (mul_pos ha hb)).mpr
  have heq : (2 * (b - a)) * ((x + 1) * b) = (2 * b ^ 2 * (b - a)) * b := by rw [hb2]; ring_nf
  rw [one_mul, heq]
  exact mul_le_mul_of_nonneg_right hh hb.le

theorem finite_sqrt_tail_bound (J N : ℕ) (hJ : 1 ≤ J) :
    (∑ n ∈ range N, 1 / ((((n + J + 1 : ℕ) : ℝ)) * Real.sqrt (n + J + 1 : ℕ))) ≤
      2 * ((Real.sqrt (J : ℝ))⁻¹ - (Real.sqrt (N + J : ℕ))⁻¹) := by
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hJ)
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have hx : 0 < (N : ℝ) + (J : ℝ) := by positivity
    have hh := sqrt_reciprocal_step ((N : ℝ) + (J : ℝ)) hx
    push_cast at ih ⊢
    have hsum := add_le_add ih hh
    convert hsum using 1
    ring_nf

theorem reciprocal_sqrt_tail (J : ℕ) (hJ : 1 ≤ J) :
    Summable (fun n : ℕ => 1 / (((n + J + 1 : ℕ) : ℝ) * Real.sqrt (n + J + 1 : ℕ))) ∧
      (∑' n : ℕ, 1 / (((n + J + 1 : ℕ) : ℝ) * Real.sqrt (n + J + 1 : ℕ))) ≤ 2 / Real.sqrt (J : ℝ) := by
  let f : ℕ → ℝ := fun n => 1 / (((n + J + 1 : ℕ) : ℝ) * Real.sqrt (n + J + 1 : ℕ))
  have hnon : ∀ n, 0 ≤ f n := by intro n; dsimp [f]; positivity
  have hb (N : ℕ) : (∑ n ∈ range N, f n) ≤ 2 / Real.sqrt (J : ℝ) := by
    have hh := finite_sqrt_tail_bound J N hJ
    change (∑ n ∈ range N, f n) ≤ _ at hh
    have hi : 0 ≤ (Real.sqrt (N + J : ℕ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    rw [div_eq_mul_inv]
    linarith
  have hs : Summable f := summable_of_sum_range_le hnon hb
  refine ⟨hs, ?_⟩
  exact le_of_tendsto hs.tendsto_sum_tsum_nat (Eventually.of_forall hb)

/-- S2 with the frozen safe constant, from the explicit S1 sequence input. -/
theorem laplaceW_lower_bound (A : ℕ → ℝ) (L C : ℝ) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (hA : ∀ k, 1 ≤ k → 0 ≤ A k ∧ A k ≤ 1)
    (hS1 : ∀ k : ℕ, 1 ≤ k → 1 / 2 - C * L / Real.sqrt k ≤ A k)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    -(1 / 2) * Real.log (1 - s) - Real.log L - (1 + 3 * C) ≤ laplaceW A s := by
  have hLpos : 0 < L := by linarith
  have hLsq : 1 ≤ L ^ 2 := by nlinarith
  let J := Nat.floor (L ^ 2)
  have hJ : 1 ≤ J := Nat.floor_pos.mpr hLsq
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJpos : (0 : ℝ) < J := by linarith
  have hJlt : L ^ 2 < (J : ℝ) + 1 := Nat.lt_floor_add_one (L ^ 2)
  have hroot : 0 < Real.sqrt (J : ℝ) := Real.sqrt_pos.mpr hJpos
  have hcut : 2 * L / Real.sqrt (J : ℝ) ≤ 3 := by
    apply (div_le_iff₀ hroot).mpr
    apply (sq_le_sq₀ (by positivity : 0 ≤ 2 * L) (by positivity : 0 ≤ 3 * Real.sqrt (J : ℝ))).mp
    nlinarith [Real.sq_sqrt hJpos.le]
  have hharm : (∑ n ∈ range J, ((n : ℝ) + 1)⁻¹) ≤ 1 + 2 * Real.log L := by
    have hh := finite_harmonic_log_bound J
    have hJle : (J : ℝ) ≤ L ^ 2 := Nat.floor_le (sq_nonneg L)
    have hl := Real.log_le_log hJpos hJle
    rw [Real.log_pow] at hl
    norm_num at hl
    linarith
  have hw := summable_laplaceW A hs0 hs1 hA
  have hlog := Real.hasSum_pow_div_log_of_abs_lt_one (show |s| < 1 by rwa [abs_of_pos hs0])
  let D : ℕ → ℝ := fun n => (1 / 2) * (s ^ (n + 1) / (n + 1)) - s ^ (n + 1) * A (n + 1) / (n + 1)
  have hhalf : HasSum (fun n : ℕ => (1 / 2) * (s ^ (n + 1) / (n + 1))) (-(1 / 2) * Real.log (1 - s)) := by
    convert hlog.mul_left (1 / 2) using 1
    ring_nf
  have hD : HasSum D (-(1 / 2) * Real.log (1 - s) - laplaceW A s) := hhalf.sub hw.hasSum
  have hhead : (∑ n ∈ range J, D n) ≤ (1 / 2) * (∑ n ∈ range J, ((n : ℝ) + 1)⁻¹) := by
    calc
      _ ≤ ∑ n ∈ range J, (1 / 2) * ((n : ℝ) + 1)⁻¹ := by
        apply sum_le_sum
        intro n hn
        have hAn := hA (n + 1) (by omega)
        have hnn : 0 ≤ s ^ (n + 1) * A (n + 1) / ((n : ℝ) + 1) :=
          div_nonneg (mul_nonneg (pow_nonneg hs0.le _) hAn.1) (by positivity)
        have hpow : s ^ (n + 1) ≤ 1 := pow_le_one₀ hs0.le hs1.le
        dsimp [D]
        calc
          _ ≤ (1 / 2) * (s ^ (n + 1) / ((n : ℝ) + 1)) := sub_le_self _ hnn
          _ ≤ (1 / 2) * ((n : ℝ) + 1)⁻¹ := by
            have hdv := div_le_div_of_nonneg_right hpow (by positivity : 0 ≤ (n : ℝ) + 1)
            simpa only [one_div] using mul_le_mul_of_nonneg_left hdv (by norm_num : (0 : ℝ) ≤ 1 / 2)
      _ = (1 / 2) * (∑ n ∈ range J, ((n : ℝ) + 1)⁻¹) := by
        rw [mul_sum]
  obtain ⟨hptail, hptail_le⟩ := reciprocal_sqrt_tail J hJ
  have hDtail := (summable_nat_add_iff J).mpr hD.summable
  have hmajor := hptail.mul_left (C * L)
  have htailpoint (n : ℕ) : D (n + J) ≤ C * L * (1 / (((n + J + 1 : ℕ) : ℝ) * Real.sqrt (n + J + 1 : ℕ))) := by
    have hk : 0 < (n : ℝ) + (J : ℝ) + 1 := by positivity
    have hS := hS1 (n + J + 1) (by omega)
    simp only [Nat.cast_add, Nat.cast_one] at hS ⊢
    have hd : 1 / 2 - A (n + J + 1) ≤ C * L / Real.sqrt ((n : ℝ) + (J : ℝ) + 1) := by linarith
    have hpow0 : 0 ≤ s ^ (n + J + 1) := pow_nonneg hs0.le _
    have hpow1 : s ^ (n + J + 1) ≤ 1 := pow_le_one₀ hs0.le hs1.le
    calc
      _ = s ^ (n + J + 1) * (1 / 2 - A (n + J + 1)) / ((n : ℝ) + (J : ℝ) + 1) := by
        dsimp [D]
        push_cast
        ring_nf
      _ ≤ s ^ (n + J + 1) * (C * L / Real.sqrt ((n : ℝ) + (J : ℝ) + 1)) /
          ((n : ℝ) + (J : ℝ) + 1) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hd hpow0) hk.le
      _ ≤ (C * L / Real.sqrt ((n : ℝ) + (J : ℝ) + 1)) / ((n : ℝ) + (J : ℝ) + 1) :=
        div_le_div_of_nonneg_right (mul_le_of_le_one_left (by positivity) hpow1) hk.le
      _ = C * L * (1 / (((n : ℝ) + (J : ℝ) + 1) * Real.sqrt ((n : ℝ) + (J : ℝ) + 1))) := by
        rw [div_div, mul_comm (Real.sqrt ((n : ℝ) + (J : ℝ) + 1)) ((n : ℝ) + (J : ℝ) + 1), mul_one_div]
  have htail : (∑' n : ℕ, D (n + J)) ≤ 3 * C := by
    calc
      _ ≤ ∑' n : ℕ, C * L * (1 / (((n + J + 1 : ℕ) : ℝ) * Real.sqrt (n + J + 1 : ℕ))) :=
        Summable.tsum_le_tsum htailpoint hDtail hmajor
      _ = C * L * (∑' n : ℕ, (1 / (((n + J + 1 : ℕ) : ℝ) * Real.sqrt (n + J + 1 : ℕ)))) :=
        (hptail.hasSum.mul_left (C * L)).tsum_eq
      _ ≤ C * L * (2 / Real.sqrt (J : ℝ)) :=
        mul_le_mul_of_nonneg_left hptail_le (mul_nonneg hC hLpos.le)
      _ = C * (2 * L / Real.sqrt (J : ℝ)) := by ring_nf
      _ ≤ 3 * C := by nlinarith [mul_le_mul_of_nonneg_left hcut hC]
  have hsplit := Summable.sum_add_tsum_nat_add J hD.summable
  rw [hD.tsum_eq] at hsplit
  nlinarith

/-- S3 retains the explicit SP identity as a hypothesis. -/
theorem laplaceG_upper_bound (A a : ℕ → ℝ) (L C : ℝ) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (hA : ∀ k, 1 ≤ k → 0 ≤ A k ∧ A k ≤ 1)
    (hS1 : ∀ k : ℕ, 1 ≤ k → 1 / 2 - C * L / Real.sqrt k ≤ A k)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ 1) (_hanti : Antitone a)
    (hSP : ∀ s : ℝ, 0 < s → s < 1 → laplaceG a s = (1 - s)⁻¹ * Real.exp (-laplaceW A s))
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    laplaceG a s ≤ Real.exp (1 + 3 * C) * L / Real.sqrt (1 - s) := by
  have _hsum := summable_laplaceG a hs0 hs1 ha
  exact generating_upper_of_W_lower _ _ L C s (by linarith) hs0 hs1
    (laplaceW_lower_bound A L C hL hC hA hS1 hs0 hs1) (hSP s hs0 hs1)

/-- The frozen square-root coefficient estimate, including m=1 and a_0. -/
theorem laplace_coefficient_bound (A a : ℕ → ℝ) (L C : ℝ) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (hA : ∀ k, 1 ≤ k → 0 ≤ A k ∧ A k ≤ 1)
    (hS1 : ∀ k : ℕ, 1 ≤ k → 1 / 2 - C * L / Real.sqrt k ≤ A k)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ 1) (hanti : Antitone a)
    (hSP : ∀ s : ℝ, 0 < s → s < 1 → laplaceG a s = (1 - s)⁻¹ * Real.exp (-laplaceW A s))
    (m : ℕ) (hm : 1 ≤ m) :
    a m ≤ Real.sqrt 2 * Real.exp (2 + 3 * C) * L / Real.sqrt m := by
  have hb : 0 ≤ Real.exp (1 + 3 * C) * L := mul_nonneg (Real.exp_pos _).le (by linarith)
  have hh := antitone_coefficient_bound_of_generating_bound a (Real.exp (1 + 3 * C) * L) hb ha hanti
    (fun s hs0 hs1 => laplaceG_upper_bound A a L C hL hC hA hS1 ha hanti hSP hs0 hs1) m hm
  have he : Real.exp 1 * Real.exp (1 + 3 * C) = Real.exp (2 + 3 * C) := by
    rw [← Real.exp_add]
    congr 1
    ring_nf
  calc
    _ ≤ Real.sqrt 2 * Real.exp 1 * (Real.exp (1 + 3 * C) * L) / Real.sqrt m := hh
    _ = Real.sqrt 2 * (Real.exp 1 * Real.exp (1 + 3 * C)) * L / Real.sqrt m := by ring_nf
    _ = _ := by rw [he]

end Shao.OQ4
