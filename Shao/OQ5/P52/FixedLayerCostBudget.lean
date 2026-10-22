import Shao.OQ5.P52.FixedLayerAtomicCost
import Shao.OQ5.P52.FixedLayerCostScales

/-!
# A summable budget for the actual fixed-layer excess costs

The five estimates below start from the actual atomic formula. Compensation
factors are bounded before the small diagonal profile is used.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace Shao.OQ5.P52

noncomputable section

private theorem exp_excess_small (u eta L : ℝ)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (heta : 0 < eta) (hL : 0 < L) :
    Real.exp (L * u ^ eta) - 1 ≤ L * Real.exp L * u ^ eta := by
  have hv0 : 0 ≤ u ^ eta := Real.rpow_nonneg hu eta
  have hv1 : u ^ eta ≤ 1 := Real.rpow_le_one hu hu1 heta.le
  have hx0 : 0 ≤ L * u ^ eta := mul_nonneg hL.le hv0
  have hx1 : L * u ^ eta ≤ L := by nlinarith
  have hs := mul_le_mul_of_nonneg_right
    (Real.one_sub_le_exp_neg (L * u ^ eta))
    (Real.exp_pos (L * u ^ eta)).le
  have hc : Real.exp (-(L * u ^ eta)) * Real.exp (L * u ^ eta) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [hc] at hs
  calc
    Real.exp (L * u ^ eta) - 1 ≤
        (L * u ^ eta) * Real.exp (L * u ^ eta) := by nlinarith
    _ ≤ (L * u ^ eta) * Real.exp L :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx1) hx0
    _ = L * Real.exp L * u ^ eta := by ring

private theorem weighted_excess_le (w W x y : ℝ)
    (hw0 : 0 ≤ w) (hw : w ≤ W) (hxy : x ≤ y) :
    w * (Real.exp x - 1) ≤ W * Real.exp y := by
  calc
    w * (Real.exp x - 1) ≤ w * Real.exp x :=
      mul_le_mul_of_nonneg_left (by linarith) hw0
    _ ≤ W * Real.exp x := mul_le_mul_of_nonneg_right hw (Real.exp_pos _).le
    _ ≤ W * Real.exp y :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hxy) (hw0.trans hw)

theorem fixedLayer_compensation_bounds :
    ∀ᶠ j in atTop,
      |1 - fixedLayerP j - fixedLayerQ j -
        fixedLayerP j * ((fixedLayerN j : ℝ) - 4)| ≤ 2 ∧
      |2 - 2 * fixedLayerQ j -
        fixedLayerP j * ((fixedLayerN j : ℝ) - 2)| ≤ 3 := by
  have he := fixedLayer_N_mul_P_tendsto_zero.eventually_le_const
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [he] with j hj
  have hN : (8 : ℝ) ≤ (fixedLayerN j : ℝ) := by
    exact_mod_cast fixedLayerN_ge_eight j
  have hp := (fixedLayerP_bounds j).1
  have hq := (fixedLayerQ_bounds j).1
  have hq1 := (fixedLayerQ_bounds j).2
  have hpq := fixedLayerP_add_Q_lt_one j
  constructor <;> apply abs_le.mpr <;> constructor <;> nlinarith

/-- All five actual atom estimates, before half-rate absorption. -/
private theorem five_atomic_bounds
    (N t p q C X eta L : ℝ)
    (hN : 8 ≤ N) (ht : 0 < t) (hp : 0 < p) (hq : 0 < q)
    (hpq : p + q ≤ 1)
    (hT : t = N ^ (2 / 3 : ℝ)) (hP : p = Real.exp (-X))
    (hQ : q = N ^ (-C))
    (heta : 0 < eta) (heta1 : eta < 1) (hL : 0 < L)
    (hc1 : |1 - p - q - p * (N - 4)| ≤ 2)
    (hc2 : |2 - 2 * q - p * (N - 2)| ≤ 3)
    (hs0 : p * t / q ≤ 1) (hsC : 3 * p * t / q ^ 2 ≤ 1) :
    2 * (1 - p - q) * p * (Real.exp (L * t ^ eta) - 1) ≤
        2 * Real.exp (-X + L * N ^ (2 * eta / 3)) ∧
    p ^ 2 * (Real.exp (L * ((N - 4) * t) ^ eta) - 1) ≤
        Real.exp (-2 * X + L * N ^ (5 * eta / 3)) ∧
    2 * p * q *
        (Real.exp (L * (t * |1 - p - q - p * (N - 4)| / q) ^ eta) - 1) ≤
        2 * q * Real.exp (-X + L * (2 : ℝ) ^ eta * N ^ (eta * (C + 2 / 3))) ∧
    2 * (1 - p - q) * q * (Real.exp (L * (p * t / q) ^ eta) - 1) ≤
        2 * L * Real.exp L * Real.exp (-eta * X) *
          N ^ (2 * eta / 3 - C * (1 - eta)) ∧
    q ^ 2 *
        (Real.exp (L * (p * t * |2 - 2 * q - p * (N - 2)| / q ^ 2) ^ eta) - 1) ≤
        3 * L * Real.exp L * Real.exp (-eta * X) *
          N ^ (2 * eta / 3 - 2 * C * (1 - eta)) := by
  have hNpos : 0 < N := by linarith
  have hp00 : 0 ≤ 1 - p - q := by linarith
  have hp01 : 1 - p - q ≤ 1 := by linarith
  have hq2 : 0 < q ^ 2 := sq_pos_of_pos hq
  have hLexp : 0 ≤ L * Real.exp L := (mul_pos hL (Real.exp_pos L)).le
  have hw0 : 2 * (1 - p - q) * p ≤ 2 * p := by
    calc
      2 * (1 - p - q) * p = (1 - p - q) * (2 * p) := by ring
      _ ≤ 1 * (2 * p) := mul_le_mul_of_nonneg_right hp01 (by positivity)
      _ = 2 * p := by ring
  have hwC : 2 * (1 - p - q) * q ≤ 2 * q := by
    calc
      2 * (1 - p - q) * q = (1 - p - q) * (2 * q) := by ring
      _ ≤ 1 * (2 * q) := mul_le_mul_of_nonneg_right hp01 (by positivity)
      _ = 2 * q := by ring
  have hteta : t ^ eta = N ^ (2 * eta / 3) := by
    rw [hT, ← Real.rpow_mul hNpos.le]
    congr 1
    ring
  have hNt : N * t = N ^ (5 / 3 : ℝ) := by
    calc
      N * t = N ^ (1 : ℝ) * N ^ (2 / 3 : ℝ) := by rw [Real.rpow_one, hT]
      _ = N ^ (5 / 3 : ℝ) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        norm_num
  have hAAeta : ((N - 4) * t) ^ eta ≤ N ^ (5 * eta / 3) := by
    calc
      ((N - 4) * t) ^ eta ≤ (N * t) ^ eta :=
        Real.rpow_le_rpow (mul_nonneg (by linarith) ht.le)
          (mul_le_mul_of_nonneg_right (by linarith) ht.le) heta.le
      _ = N ^ (5 * eta / 3) := by
        rw [hNt, ← Real.rpow_mul hNpos.le]
        congr 1
        ring
  have htq : t / q = N ^ (C + 2 / 3) := by
    rw [hT, hQ, ← Real.rpow_sub hNpos]
    congr 1
    ring
  have hac : t * |1 - p - q - p * (N - 4)| / q ≤ 2 * t / q := by
    apply (div_le_div_iff_of_pos_right hq).2
    nlinarith [mul_le_mul_of_nonneg_left hc1 ht.le]
  have haceta :
      (t * |1 - p - q - p * (N - 4)| / q) ^ eta ≤
        (2 : ℝ) ^ eta * N ^ (eta * (C + 2 / 3)) := by
    calc
      (t * |1 - p - q - p * (N - 4)| / q) ^ eta ≤ (2 * t / q) ^ eta :=
        Real.rpow_le_rpow (by positivity) hac heta.le
      _ = (2 : ℝ) ^ eta * N ^ (eta * (C + 2 / 3)) := by
        rw [show 2 * t / q = 2 * (t / q) by ring,
          Real.mul_rpow (by norm_num) (div_pos ht hq).le, htq,
          ← Real.rpow_mul hNpos.le]
        congr 2
        ring
  have hpeta : p ^ eta = Real.exp (-eta * X) := by
    rw [hP, ← Real.exp_mul]
    congr 1
    ring
  have hqeta : q ^ eta = N ^ (-C * eta) := by
    rw [hQ, ← Real.rpow_mul hNpos.le]
  have hq_sq : q ^ 2 = N ^ (-2 * C) := by
    rw [hQ, ← Real.rpow_natCast (N ^ (-C)) 2,
      ← Real.rpow_mul hNpos.le]
    congr 1
    ring
  have hq_sq_eta : (q ^ 2) ^ eta = N ^ (-2 * C * eta) := by
    rw [hq_sq, ← Real.rpow_mul hNpos.le]
  have hid0 :
      q * (p * t / q) ^ eta =
        Real.exp (-eta * X) * N ^ (2 * eta / 3 - C * (1 - eta)) := by
    calc
      q * (p * t / q) ^ eta =
          Real.exp (-eta * X) *
            (N ^ (-C) * N ^ (2 * eta / 3) / N ^ (-C * eta)) := by
        rw [Real.div_rpow (mul_pos hp ht).le hq.le,
          Real.mul_rpow hp.le ht.le, hpeta, hteta, hqeta, hQ]
        ring
      _ = _ := by
        rw [← Real.rpow_add hNpos, ← Real.rpow_sub hNpos]
        congr 2
        ring
  have hidC :
      q ^ 2 * (3 * p * t / q ^ 2) ^ eta =
        (3 : ℝ) ^ eta * Real.exp (-eta * X) *
          N ^ (2 * eta / 3 - 2 * C * (1 - eta)) := by
    calc
      q ^ 2 * (3 * p * t / q ^ 2) ^ eta =
          (3 : ℝ) ^ eta * Real.exp (-eta * X) *
            (N ^ (-2 * C) * N ^ (2 * eta / 3) / N ^ (-2 * C * eta)) := by
        rw [show 3 * p * t / q ^ 2 = 3 * (p * t / q ^ 2) by ring,
          Real.mul_rpow (by norm_num) (div_pos (mul_pos hp ht) hq2).le,
          Real.div_rpow (mul_pos hp ht).le hq2.le,
          Real.mul_rpow hp.le ht.le, hpeta, hteta, hq_sq_eta, hq_sq]
        ring
      _ = _ := by
        rw [← Real.rpow_add hNpos, ← Real.rpow_sub hNpos]
        congr 2
        ring
  have h3eta : (3 : ℝ) ^ eta ≤ 3 := by
    calc
      (3 : ℝ) ^ eta ≤ (3 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) heta1.le
      _ = 3 := Real.rpow_one 3
  have hCC : p * t * |2 - 2 * q - p * (N - 2)| / q ^ 2 ≤ 3 * p * t / q ^ 2 := by
    apply (div_le_div_iff_of_pos_right hq2).2
    nlinarith [mul_le_mul_of_nonneg_left hc2 (mul_pos hp ht).le]
  have hs0ex := exp_excess_small (p * t / q) eta L
    (div_pos (mul_pos hp ht) hq).le hs0 heta hL
  have hsCex := exp_excess_small
    (p * t * |2 - 2 * q - p * (N - 2)| / q ^ 2) eta L
    (by positivity) (hCC.trans hsC) heta hL
  have hsCpow :
      (p * t * |2 - 2 * q - p * (N - 2)| / q ^ 2) ^ eta ≤
        (3 * p * t / q ^ 2) ^ eta :=
    Real.rpow_le_rpow (by positivity) hCC heta.le
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc
      2 * (1 - p - q) * p * (Real.exp (L * t ^ eta) - 1) ≤
          (2 * p) * Real.exp (L * N ^ (2 * eta / 3)) :=
        weighted_excess_le _ _ _ _ (by positivity) hw0 (by rw [hteta])
      _ = 2 * Real.exp (-X + L * N ^ (2 * eta / 3)) := by
        rw [hP, Real.exp_add]
        ring
  · calc
      p ^ 2 * (Real.exp (L * ((N - 4) * t) ^ eta) - 1) ≤
          p ^ 2 * Real.exp (L * N ^ (5 * eta / 3)) :=
        weighted_excess_le _ _ _ _ (sq_nonneg _) le_rfl
          (mul_le_mul_of_nonneg_left hAAeta hL.le)
      _ = Real.exp (-2 * X + L * N ^ (5 * eta / 3)) := by
        rw [hP, pow_two, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  · calc
      2 * p * q *
          (Real.exp (L * (t * |1 - p - q - p * (N - 4)| / q) ^ eta) - 1) ≤
          (2 * p * q) *
            Real.exp (L * ((2 : ℝ) ^ eta * N ^ (eta * (C + 2 / 3)))) :=
        weighted_excess_le _ _ _ _ (by positivity) le_rfl
          (mul_le_mul_of_nonneg_left haceta hL.le)
      _ = 2 * q * Real.exp (-X + L * (2 : ℝ) ^ eta * N ^ (eta * (C + 2 / 3))) := by
        rw [show L * ((2 : ℝ) ^ eta * N ^ (eta * (C + 2 / 3))) =
            L * (2 : ℝ) ^ eta * N ^ (eta * (C + 2 / 3)) by ring,
          hP, Real.exp_add]
        ring
  · calc
      2 * (1 - p - q) * q * (Real.exp (L * (p * t / q) ^ eta) - 1) ≤
          (2 * (1 - p - q) * q) * (L * Real.exp L * (p * t / q) ^ eta) :=
        mul_le_mul_of_nonneg_left hs0ex (by positivity)
      _ ≤ (2 * q) * (L * Real.exp L * (p * t / q) ^ eta) :=
        mul_le_mul_of_nonneg_right hwC (by positivity)
      _ = 2 * L * Real.exp L * (q * (p * t / q) ^ eta) := by ring
      _ = 2 * L * Real.exp L * Real.exp (-eta * X) *
          N ^ (2 * eta / 3 - C * (1 - eta)) := by rw [hid0]; ring
  · calc
      q ^ 2 *
          (Real.exp (L * (p * t * |2 - 2 * q - p * (N - 2)| / q ^ 2) ^ eta) - 1) ≤
          q ^ 2 * (L * Real.exp L * (3 * p * t / q ^ 2) ^ eta) :=
        mul_le_mul_of_nonneg_left
          (hsCex.trans (mul_le_mul_of_nonneg_left hsCpow hLexp)) (sq_nonneg _)
      _ = L * Real.exp L * (q ^ 2 * (3 * p * t / q ^ 2) ^ eta) := by ring
      _ = (3 : ℝ) ^ eta * (L * Real.exp L * Real.exp (-eta * X) *
          N ^ (2 * eta / 3 - 2 * C * (1 - eta))) := by rw [hidC]; ring
      _ ≤ 3 * (L * Real.exp L * Real.exp (-eta * X) *
          N ^ (2 * eta / 3 - 2 * C * (1 - eta))) :=
        mul_le_mul_of_nonneg_right h3eta (by positivity)
      _ = 3 * L * Real.exp L * Real.exp (-eta * X) *
          N ^ (2 * eta / 3 - 2 * C * (1 - eta)) := by ring

theorem fixedLayerExcessCost_eventually_le (η «λ» : ℝ)
    (hη0 : 0 < η) (hη : η < 1 / 5) («hλ» : 0 < «λ») :
    ∀ᶠ j in atTop, fixedLayerExcessCost j η «λ» ≤
      5 * Real.exp (-(1 / 2 : ℝ) * ((fixedLayerN j : ℝ) ^ fixedLayerTau j)) +
      6 * «λ» * Real.exp «λ» *
        Real.exp (-η * ((fixedLayerN j : ℝ) ^ fixedLayerTau j)) := by
  have hs0 := fixedLayer_small_entry_scale_tendsto_zero.eventually_le_const
    (by norm_num : (0 : ℝ) < 1)
  have hsC := fixedLayer_diag_scale_tendsto_zero.eventually_le_const
    (by norm_num : (0 : ℝ) < 1)
  have habs := fixedLayer_eventually_absorbs_positive_powers η «λ» hη0 hη «hλ»
  filter_upwards [fixedLayer_compensation_bounds, hs0, hsC, habs] with j hc hs0j hsCj ha
  let N : ℝ := (fixedLayerN j : ℝ)
  let t := fixedLayerT j
  let p := fixedLayerP j
  let q := fixedLayerQ j
  let C := fixedLayerC j
  let X := N ^ fixedLayerTau j
  have hN : (8 : ℝ) ≤ N := Nat.cast_le.mpr (fixedLayerN_ge_eight j)
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have ht : 0 < t := fixedLayerT_pos j
  have hp : 0 < p := (fixedLayerP_bounds j).1
  have hq : 0 < q := (fixedLayerQ_bounds j).1
  have hq1 : q ≤ 1 := by
    have hh := (fixedLayerQ_bounds j).2
    change q < 1 / 8 at hh
    linarith
  have hX : 0 ≤ X := (Real.rpow_pos_of_pos hN0 (fixedLayerTau j)).le
  have hb := five_atomic_bounds N t p q C X η «λ» hN ht hp hq
    (fixedLayerP_add_Q_lt_one j).le (fixedLayerT_eq_rpow_N j) rfl rfl
    hη0 (by linarith) «hλ» hc.1 hc.2 hs0j hsCj
  rcases hb with ⟨hb0, hbAA, hbAC, hb0C, hbCC⟩
  change «λ» * N ^ (2 * η / 3) ≤ X / 2 ∧
    «λ» * N ^ (5 * η / 3) ≤ X / 2 ∧
    «λ» * (2 : ℝ) ^ η * N ^ (η * (C + 2 / 3)) ≤ X / 2 at ha
  have hneg := fixedLayer_small_cost_exponents_neg j η hη0 hη
  have hpow0 : N ^ (2 * η / 3 - C * (1 - η)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 hneg.1.le
  have hpowC : N ^ (2 * η / 3 - 2 * C * (1 - η)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 hneg.2.le
  have h0 :
      2 * (1 - p - q) * p * (Real.exp («λ» * t ^ η) - 1) ≤
        2 * Real.exp (-(1 / 2 : ℝ) * X) := by
    apply hb0.trans
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith [ha.1])) (by norm_num)
  have hAA :
      p ^ 2 * (Real.exp («λ» * ((N - 4) * t) ^ η) - 1) ≤
        Real.exp (-(1 / 2 : ℝ) * X) := by
    exact hbAA.trans (Real.exp_le_exp.mpr (by linarith [ha.2.1]))
  have hAC :
      2 * p * q *
        (Real.exp («λ» * (t * |1 - p - q - p * (N - 4)| / q) ^ η) - 1) ≤
        2 * Real.exp (-(1 / 2 : ℝ) * X) := by
    apply hbAC.trans
    calc
      2 * q * Real.exp (-X + «λ» * (2 : ℝ) ^ η * N ^ (η * (C + 2 / 3))) ≤
          2 * q * Real.exp (-(1 / 2 : ℝ) * X) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by linarith [ha.2.2])) (by positivity)
      _ ≤ 2 * Real.exp (-(1 / 2 : ℝ) * X) := by
        nlinarith [mul_le_mul_of_nonneg_right hq1
          (Real.exp_pos (-(1 / 2 : ℝ) * X)).le]
  have h0C :
      2 * (1 - p - q) * q * (Real.exp («λ» * (p * t / q) ^ η) - 1) ≤
        2 * «λ» * Real.exp «λ» * Real.exp (-η * X) := by
    apply hb0C.trans
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow0
      (by positivity : 0 ≤ 2 * «λ» * Real.exp «λ» * Real.exp (-η * X))
  have hCC :
      q ^ 2 *
        (Real.exp («λ» * (p * t * |2 - 2 * q - p * (N - 2)| / q ^ 2) ^ η) - 1) ≤
        3 * «λ» * Real.exp «λ» * Real.exp (-η * X) := by
    apply hbCC.trans
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpowC
      (by positivity : 0 ≤ 3 * «λ» * Real.exp «λ» * Real.exp (-η * X))
  change fixedLayerExcessCost j η «λ» ≤
    5 * Real.exp (-(1 / 2 : ℝ) * X) +
      6 * «λ» * Real.exp «λ» * Real.exp (-η * X)
  calc
    fixedLayerExcessCost j η «λ» = _ := fixedLayerExcessCost_eq_five_atoms j η «λ» hη0
    _ ≤ 2 * Real.exp (-(1 / 2 : ℝ) * X) +
        Real.exp (-(1 / 2 : ℝ) * X) +
        2 * Real.exp (-(1 / 2 : ℝ) * X) +
        2 * «λ» * Real.exp «λ» * Real.exp (-η * X) +
        3 * «λ» * Real.exp «λ» * Real.exp (-η * X) :=
      add_le_add (add_le_add (add_le_add (add_le_add h0 hAA) hAC) h0C) hCC
    _ ≤ _ := by
      nlinarith [show 0 ≤ «λ» * Real.exp «λ» * Real.exp (-η * X) by positivity]

theorem summable_fixedLayerExcessCost (η «λ» : ℝ)
    (hη0 : 0 < η) (hη : η < 1 / 5) («hλ» : 0 < «λ») :
    Summable (fun j : ℕ => fixedLayerExcessCost j η «λ») := by
  have h1 := Summable.mul_left 5
    (summable_fixedLayer_exp_neg (1 / 2) (by norm_num))
  have h2 := Summable.mul_left (6 * «λ» * Real.exp «λ»)
    (summable_fixedLayer_exp_neg η hη0)
  apply (h1.add h2).of_norm_bounded_eventually_nat
  filter_upwards [fixedLayerExcessCost_eventually_le η «λ» hη0 hη «hλ»] with j hj
  rw [Real.norm_eq_abs,
    abs_of_nonneg (fixedLayerExcessCost_nonneg j η «λ» «hλ».le)]
  exact hj

end
end Shao.OQ5.P52
