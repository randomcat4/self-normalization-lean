import Shao.OQ4.RademacherLatticeShift
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

namespace Shao.OQ4.RademacherScaleAssembly

open Filter
open scoped Topology

open Shao.OQ4.RademacherScalarBounds
open Shao.OQ4.RademacherLatticeShift

def eta3 (n : ℕ) (h : ℝ) : ℝ := (n : ℝ) / h ^ 3

private theorem zero_of_abs_le {f g : ℕ → ℝ}
    (hg : Tendsto g atTop (𝓝 0))
    (hb : ∀ᶠ k in atTop, |f k| ≤ g k) :
    Tendsto f atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero f).2
  exact squeeze_zero' (Eventually.of_forall (fun k => abs_nonneg (f k))) hb hg

private theorem cube_gap_bound {m : ℕ} (hm : 1 ≤ m) {h : ℝ}
    (hmh : (m : ℝ) ≤ h) (hmh1 : h < (m : ℝ) + 1) (n : ℕ) :
    0 ≤ eta3 n h - eta3 n (H m) ∧
      eta3 n h - eta3 n (H m) ≤ 3 * ((n : ℝ) / h ^ 4) := by
  rcases cell_legality hm hmh hmh1 with ⟨_, hh, _, hH, hEq, hd, hd1⟩
  have hhH : h ≤ H m := by linarith
  have hB : 0 ≤ eta3 n h :=
    div_nonneg (Nat.cast_nonneg n) (pow_pos hh 3).le
  have hcmp : eta3 n (H m) ≤ eta3 n h :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg n) (pow_pos hh 3)
      (pow_le_pow_left₀ hh.le hhH 3)
  have hr0 : 0 ≤ h / H m := div_nonneg hh.le hH.le
  have hr1 : h / H m ≤ 1 := (div_le_one hH).2 hhH
  have hQ0 : 0 ≤ 1 + h / H m + (h / H m) ^ 2 := by positivity
  have hQ1 : 1 + h / H m + (h / H m) ^ 2 ≤ 3 := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1)]
  have hdinv : delta m h / H m ≤ 1 / h :=
    (div_le_div_of_nonneg_right hd1 hH.le).trans
      (one_div_le_one_div_of_le hh hhH)
  have hleft : eta3 n h * (delta m h / H m) ≤ eta3 n h * (1 / h) :=
    mul_le_mul_of_nonneg_left hdinv hB
  have hid : eta3 n h - eta3 n (H m) =
      eta3 n h * (delta m h / H m) *
        (1 + h / H m + (h / H m) ^ 2) := by
    unfold eta3 delta
    field_simp [hh.ne', hH.ne']; ring
  refine ⟨sub_nonneg.mpr hcmp, ?_⟩
  calc
    eta3 n h - eta3 n (H m) =
        eta3 n h * (delta m h / H m) *
          (1 + h / H m + (h / H m) ^ 2) := hid
    _ ≤ (eta3 n h * (1 / h)) * 3 :=
      mul_le_mul hleft hQ1 hQ0 (mul_nonneg hB (by positivity))
    _ = 3 * ((n : ℝ) / h ^ 4) := by
      unfold eta3
      field_simp [hh.ne']

theorem DA2
    (m n : ℕ → ℕ) (h : ℕ → ℝ)
    (hm : ∀ k : ℕ, 1 ≤ m k)
    (hmh : ∀ k : ℕ, (m k : ℝ) ≤ h k)
    (hmh1 : ∀ k : ℕ, h k < (m k : ℝ) + 1)
    (hh : Tendsto h atTop atTop)
    (hscale2 :
      Tendsto (fun k : ℕ => (n k : ℝ) / (h k) ^ 2) atTop atTop)
    (hscale3 :
      ∃ M : ℝ, 0 < M ∧
        ∃ K : ℕ, ∀ k : ℕ, K ≤ k → eta3 (n k) (h k) ≤ M) :
    (∀ k : ℕ,
      1 ≤ h k ∧
      0 < h k ∧
      2 ≤ H (m k) ∧
      0 < H (m k) ∧
      H (m k) = h k + delta (m k) (h k) ∧
      0 < delta (m k) (h k) ∧
      delta (m k) (h k) ≤ 1 ∧
      (h k = (m k : ℝ) → delta (m k) (h k) = 1) ∧
      h k ≠ 0 ∧
      H (m k) ≠ 0 ∧
      (h k) ^ 2 ≠ 0 ∧
      (h k) ^ 3 ≠ 0 ∧
      (h k) ^ 4 ≠ 0 ∧
      (H (m k)) ^ 2 ≠ 0 ∧
      (H (m k)) ^ 3 ≠ 0 ∧
      (H (m k)) ^ 4 ≠ 0 ∧
      4 * H (m k) ≠ 0 ∧
      2 * H (m k) ≠ 0 ∧
      0 < Real.sin (u (m k)) ∧
      Real.sin (u (m k)) ≠ 0 ∧
      0 < a (m k) ∧
      0 < rho (m k) ∧
      rho (m k) < 1 ∧
      0 < Real.pi * a (m k) / 4) ∧
    (Tendsto (fun k : ℕ => H (m k)) atTop atTop ∧
      Tendsto (fun k : ℕ => H (m k) / h k) atTop (𝓝 (1 : ℝ)) ∧
      Tendsto (fun k : ℕ => (n k : ℝ) / (H (m k)) ^ 2)
        atTop atTop ∧
      (∃ K_T : ℕ, ∀ k : ℕ, K_T ≤ k →
        (H (m k)) ^ 2 ≤ (n k : ℝ)) ∧
      (∃ K_pos : ℕ, ∀ k : ℕ, K_pos ≤ k → 0 < n k)) ∧
    (Tendsto (fun k : ℕ => (n k : ℝ) / (h k) ^ 4)
        atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun k : ℕ => 1 / (H (m k)) ^ 2)
        atTop (𝓝 (0 : ℝ)) ∧
      (∃ M' : ℝ, 0 < M' ∧
        ∃ K' : ℕ, ∀ k : ℕ, K' ≤ k →
          0 ≤ eta3 (n k) (H (m k)) ∧
          eta3 (n k) (H (m k)) ≤ M') ∧
      Tendsto
        (fun k : ℕ => eta3 (n k) (h k) -
          eta3 (n k) (H (m k)))
        atTop (𝓝 (0 : ℝ))) ∧
    Tendsto
      (fun k : ℕ =>
        lambda * (n k : ℝ) / (h k) ^ 2 +
          (n k : ℝ) * Real.log (rho (m k)) +
          Real.log (Real.pi * a (m k) / 4) -
          (Real.pi ^ 2 / 4) * eta3 (n k) (h k) *
            delta (m k) (h k))
      atTop (𝓝 (0 : ℝ)) := by
  have hgeom (k : ℕ) := cell_legality (hm k) (hmh k) (hmh1 k)
  have hhpos (k : ℕ) : 0 < h k := (hgeom k).2.1
  have hHpos (k : ℕ) : 0 < H (m k) := H_pos (hm k)
  have hhH (k : ℕ) : h k ≤ H (m k) := by
    change h k ≤ (m k : ℝ) + 1
    exact (hmh1 k).le
  have hHupper (k : ℕ) : H (m k) ≤ 2 * h k := by
    rcases hgeom k with ⟨hh1, _, _, _, hEq, _, hd1⟩
    linarith
  have hdelt (k : ℕ) :
      0 < delta (m k) (h k) ∧ delta (m k) (h k) ≤ 1 := by
    rcases hgeom k with ⟨_, _, _, _, _, hd, hd1⟩
    exact ⟨hd, hd1⟩
  have hHinf : Tendsto (fun k : ℕ => H (m k)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hh.eventually_ge_atTop b] with k hk
    exact hk.trans (hhH k)
  have hinv : Tendsto (fun k : ℕ => 1 / h k) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hh
  have hdeltlim :
      Tendsto (fun k : ℕ => delta (m k) (h k) / h k)
        atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero'
      (Eventually.of_forall (fun k => div_nonneg (hdelt k).1.le (hhpos k).le))
      (Eventually.of_forall (fun k =>
        div_le_div_of_nonneg_right (hdelt k).2 (hhpos k).le)) hinv
  have hratio :
      Tendsto (fun k : ℕ => H (m k) / h k) atTop (𝓝 (1 : ℝ)) := by
    have hl := hdeltlim.add_const (1 : ℝ)
    have heq : (fun k : ℕ => delta (m k) (h k) / h k + 1) =
        (fun k : ℕ => H (m k) / h k) := by
      funext k
      unfold delta
      field_simp [(hhpos k).ne'] <;> ring
    rw [heq] at hl
    simpa only [zero_add] using hl
  have hHtime :
      Tendsto (fun k : ℕ => (n k : ℝ) / (H (m k)) ^ 2) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hscale2.eventually_ge_atTop (4 * b)] with k hk
    have hsquare : (H (m k)) ^ 2 ≤ 4 * (h k) ^ 2 := by
      nlinarith [hHupper k, hHpos k, hhpos k]
    have hc : (n k : ℝ) / (4 * (h k) ^ 2) ≤
        (n k : ℝ) / (H (m k)) ^ 2 :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg (n k))
        (pow_pos (hHpos k) 2) hsquare
    have heq : (n k : ℝ) / (4 * (h k) ^ 2) =
        ((n k : ℝ) / (h k) ^ 2) / 4 := by ring
    rw [heq] at hc
    linarith
  have htime : ∃ K_T : ℕ, ∀ k : ℕ, K_T ≤ k →
      (H (m k)) ^ 2 ≤ (n k : ℝ) := by
    rcases eventually_atTop.1 (hHtime.eventually_ge_atTop (1 : ℝ)) with ⟨K_T, hK⟩
    refine ⟨K_T, fun k hk => ?_⟩
    have hb := (le_div_iff₀ (pow_pos (hHpos k) 2)).1 (hK k hk)
    simpa only [one_mul] using hb
  have hpos : ∃ K_pos : ℕ, ∀ k : ℕ, K_pos ≤ k → 0 < n k := by
    rcases htime with ⟨K_T, hK⟩
    refine ⟨K_T, fun k hk => ?_⟩
    have hnr : (0 : ℝ) < (n k : ℝ) :=
      lt_of_lt_of_le (pow_pos (hHpos k) 2) (hK k hk)
    exact_mod_cast hnr
  rcases hscale3 with ⟨M, hM, K, hBK⟩
  have hMlim : Tendsto (fun k : ℕ => M / h k) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, div_eq_mul_inv, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hh).const_mul M
  have h4 :
      Tendsto (fun k : ℕ => (n k : ℝ) / (h k) ^ 4)
        atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero'
      (Eventually.of_forall (fun k =>
        div_nonneg (Nat.cast_nonneg (n k)) (pow_pos (hhpos k) 4).le)) ?_ hMlim
    filter_upwards [eventually_ge_atTop K] with k hk
    calc
      (n k : ℝ) / (h k) ^ 4 = eta3 (n k) (h k) / h k := by
        unfold eta3
        field_simp [(hhpos k).ne'] <;> ring
      _ ≤ M / h k := div_le_div_of_nonneg_right (hBK k hk) (hhpos k).le
  have hHinv2 :
      Tendsto (fun k : ℕ => 1 / (H (m k)) ^ 2)
        atTop (𝓝 (0 : ℝ)) := by
    simpa [one_div, inv_pow] using (tendsto_inv_atTop_zero.comp hHinf).pow 2
  have hBH :
      ∃ M' : ℝ, 0 < M' ∧
        ∃ K' : ℕ, ∀ k : ℕ, K' ≤ k →
          0 ≤ eta3 (n k) (H (m k)) ∧
          eta3 (n k) (H (m k)) ≤ M' := by
    refine ⟨M, hM, K, fun k hk => ?_⟩
    refine ⟨div_nonneg (Nat.cast_nonneg (n k)) (pow_pos (hHpos k) 3).le, ?_⟩
    exact (div_le_div_of_nonneg_left (Nat.cast_nonneg (n k))
      (pow_pos (hhpos k) 3) (pow_le_pow_left₀ (hhpos k).le (hhH k) 3)).trans (hBK k hk)
  have hgap :
      Tendsto
        (fun k : ℕ => eta3 (n k) (h k) - eta3 (n k) (H (m k)))
        atTop (𝓝 (0 : ℝ)) := by
    apply zero_of_abs_le (by simpa only [mul_zero] using h4.const_mul 3)
    exact Eventually.of_forall (fun k => by
      have hg := cube_gap_bound (hm k) (hmh k) (hmh1 k) (n k)
      rw [abs_of_nonneg hg.1]
      exact hg.2)
  rcases Shao.OQ4.RademacherLatticeShift.DA1 with ⟨C, _, hDA1⟩
  have herrlim :
      Tendsto
        (fun k : ℕ => C * ((n k : ℝ) / (h k) ^ 4 + 1 / (H (m k)) ^ 2))
        atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_add, mul_zero] using (h4.add hHinv2).const_mul C
  have hres :
      Tendsto
        (fun k : ℕ =>
          lambda * (n k : ℝ) / (h k) ^ 2 +
            (n k : ℝ) * Real.log (rho (m k)) +
            Real.log (Real.pi * a (m k) / 4) -
            (Real.pi ^ 2 / 4) * eta3 (n k) (h k) *
              delta (m k) (h k))
        atTop (𝓝 (0 : ℝ)) := by
    apply zero_of_abs_le herrlim
    exact Eventually.of_forall (fun k => by
      simpa only [lambda, eta3, delta] using
        hDA1 (m k) (hm k) (h k) (hmh k) (hmh1 k) (n k))
  refine ⟨?_, ⟨hHinf, hratio, hHtime, htime, hpos⟩,
    ⟨h4, hHinv2, hBH, hgap⟩, hres⟩
  intro k
  rcases hgeom k with ⟨hh1, hh0, hH2, hH0, hEq, hd0, hd1⟩
  exact ⟨hh1, hh0, hH2, hH0, hEq, hd0, hd1,
    (fun hleft => by simpa only [hleft] using delta_at_left (m k)),
    hh0.ne', hH0.ne',
    pow_ne_zero 2 hh0.ne', pow_ne_zero 3 hh0.ne', pow_ne_zero 4 hh0.ne',
    pow_ne_zero 2 hH0.ne', pow_ne_zero 3 hH0.ne', pow_ne_zero 4 hH0.ne',
    mul_ne_zero (by norm_num) hH0.ne', mul_ne_zero (by norm_num) hH0.ne',
    sin_u_pos (hm k), (sin_u_pos (hm k)).ne',
    a_pos (hm k), rho_pos (hm k), rho_lt_one (hm k), pi_mul_a_div_four_pos (hm k)⟩

theorem DA2_subcritical
    (m n : ℕ → ℕ) (h : ℕ → ℝ)
    (hm : ∀ k : ℕ, 1 ≤ m k)
    (hmh : ∀ k : ℕ, (m k : ℝ) ≤ h k)
    (hmh1 : ∀ k : ℕ, h k < (m k : ℝ) + 1)
    (hh : Tendsto h atTop atTop)
    (hscale2 :
      Tendsto (fun k : ℕ => (n k : ℝ) / (h k) ^ 2) atTop atTop)
    (hscale3 :
      ∃ M : ℝ, 0 < M ∧
        ∃ K : ℕ, ∀ k : ℕ, K ≤ k → eta3 (n k) (h k) ≤ M)
    (hsubcritical :
      Tendsto (fun k : ℕ => eta3 (n k) (h k))
        atTop (𝓝 (0 : ℝ))) :
    Tendsto
      (fun k : ℕ =>
        lambda * (n k : ℝ) / (h k) ^ 2 +
          (n k : ℝ) * Real.log (rho (m k)) +
          Real.log (Real.pi * a (m k) / 4))
      atTop (𝓝 (0 : ℝ)) := by
  have hres := (DA2 m n h hm hmh hmh1 hh hscale2 hscale3).2.2.2
  have hshift :
      Tendsto
        (fun k : ℕ => (Real.pi ^ 2 / 4) * eta3 (n k) (h k) *
          delta (m k) (h k))
        atTop (𝓝 (0 : ℝ)) := by
    apply zero_of_abs_le
      (by simpa only [mul_zero] using hsubcritical.const_mul (Real.pi ^ 2 / 4))
    exact Eventually.of_forall (fun k => by
      rcases cell_legality (hm k) (hmh k) (hmh1 k) with ⟨_, hhpos, _, _, _, hd, hd1⟩
      have hB : 0 ≤ eta3 (n k) (h k) :=
        div_nonneg (Nat.cast_nonneg (n k)) (pow_pos hhpos 3).le
      have hc : 0 ≤ Real.pi ^ 2 / 4 := by positivity
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg hc hB) hd.le)]
      exact mul_le_of_le_one_right (mul_nonneg hc hB) hd1)
  simpa only [sub_add_cancel, add_zero] using hres.add hshift

end Shao.OQ4.RademacherScaleAssembly
