import Shao.OQ4.WeightedThirdMomentB2
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Third moments for the actual finite polygonal path

The finite ramp representation is identified with prefix sums on the grid
and with their affine interpolation on each grid interval.  Its actual
increment coefficients have squared sum at most the elapsed time, so the
weighted third-moment theorem applies at every time scale.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace Shao.OQ4.PolygonalThirdMoment

def polygonalPath (n : ℕ) (h : ℝ) (a : Shao.Path n) (t : ℝ) : ℝ :=
  ∑ i : Fin n, max 0 (min 1 (t * h ^ 2 - (i.val : ℝ))) * a i / h

private def ramp (x : ℝ) : ℝ := max 0 (min 1 x)

private def incrementCoeff (n : ℕ) (h s t : ℝ) (i : Fin n) : ℝ :=
  (ramp (t * h ^ 2 - (i.val : ℝ)) -
    ramp (s * h ^ 2 - (i.val : ℝ))) / h

private theorem ramp_bounds (x : ℝ) : 0 ≤ ramp x ∧ ramp x ≤ 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

private theorem ramp_monotone : Monotone ramp := by
  intro x y hxy
  exact max_le_max le_rfl (min_le_min le_rfl hxy)

private theorem ramp_eq_pos_sub (x : ℝ) :
    ramp x = max 0 x - max 0 (x - 1) := by
  by_cases hx0 : x ≤ 0
  · have hx1 : x ≤ 1 := hx0.trans (by norm_num)
    have hxsub : x - 1 ≤ 0 := by linarith
    simp only [ramp, min_eq_right hx1, max_eq_left hx0,
      max_eq_left hxsub, sub_zero]
  · have h0x : 0 ≤ x := le_of_lt (lt_of_not_ge hx0)
    by_cases hx1 : x ≤ 1
    · have hxsub : x - 1 ≤ 0 := sub_nonpos.mpr hx1
      simp only [ramp, min_eq_right hx1, max_eq_right h0x,
        max_eq_left hxsub, sub_zero]
    · have h1x : 1 ≤ x := le_of_lt (lt_of_not_ge hx1)
      have hxsub : 0 ≤ x - 1 := sub_nonneg.mpr h1x
      rw [ramp, min_eq_left h1x, max_eq_right (by norm_num : (0 : ℝ) ≤ 1),
        max_eq_right h0x, max_eq_right hxsub]
      ring

private theorem sum_ramp (n : ℕ) (u : ℝ) :
    (∑ i : Fin n, ramp (u - (i.val : ℝ))) =
      max 0 u - max 0 (u - (n : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih, ramp_eq_pos_sub]
      have hshift : u - (n : ℝ) - 1 = u - ((n + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      rw [hshift]
      ring

private theorem ramp_grid_affine
    (k i : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ramp ((k : ℝ) + u - (i : ℝ)) =
      (1 - u) * (if i < k then 1 else 0) +
        u * (if i < k + 1 then 1 else 0) := by
  by_cases hik : i < k
  · have hik' : i + 1 ≤ k := Nat.succ_le_of_lt hik
    have hikR : (i : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hik'
    have hx : 1 ≤ (k : ℝ) + u - (i : ℝ) := by linarith
    have hik1 : i < k + 1 := Nat.lt_succ_of_lt hik
    rw [ramp, min_eq_left hx, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
    simp only [ite_eq_left hik, ite_eq_left hik1, mul_one]
    ring
  · by_cases hieq : i = k
    · subst i
      have hk1 : k < k + 1 := Nat.lt_succ_self k
      have hx : (k : ℝ) + u - (k : ℝ) = u := by ring
      rw [hx, ramp, min_eq_right hu1, max_eq_right hu0]
      simp only [lt_self_iff_false, ite_false, ite_eq_left hk1, mul_zero,
        mul_one, zero_add]
    · have hki : k < i := by
        rcases lt_trichotomy i k with hi | hi | hi
        · exact False.elim (hik hi)
        · exact False.elim (hieq hi)
        · exact hi
      have hki' : k + 1 ≤ i := Nat.succ_le_of_lt hki
      have hkiR : (k : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hki'
      have hx0 : (k : ℝ) + u - (i : ℝ) ≤ 0 := by linarith
      have hx1 : (k : ℝ) + u - (i : ℝ) ≤ 1 := hx0.trans (by norm_num)
      have hik1 : ¬i < k + 1 := not_lt_of_ge hki'
      rw [ramp, min_eq_right hx1, max_eq_left hx0]
      simp only [ite_eq_right hik, ite_eq_right hik1, mul_zero, add_zero]

private theorem polygonal_increment_eq_sum
    (n : ℕ) (h : ℝ) (a : Shao.Path n) (s t : ℝ) :
    polygonalPath n h a t - polygonalPath n h a s =
      ∑ i : Fin n, incrementCoeff n h s t i * a i := by
  unfold polygonalPath incrementCoeff ramp
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem incrementCoeff_energy_le
    (n : ℕ) (h s t : ℝ) (hh : 0 < h) (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t * h ^ 2 ≤ (n : ℝ)) :
    (∑ i : Fin n, incrementCoeff n h s t i ^ 2) ≤ t - s := by
  have hh2 : 0 < h ^ 2 := sq_pos_of_pos hh
  have hs0 : 0 ≤ s * h ^ 2 := mul_nonneg hs hh2.le
  have hst2 : s * h ^ 2 ≤ t * h ^ 2 :=
    mul_le_mul_of_nonneg_right hst hh2.le
  have ht0 : 0 ≤ t * h ^ 2 := hs0.trans hst2
  have hsN : s * h ^ 2 ≤ (n : ℝ) := hst2.trans ht
  have hsum (v : ℝ) (hv0 : 0 ≤ v) (hvN : v ≤ (n : ℝ)) :
      (∑ i : Fin n, ramp (v - (i.val : ℝ))) = v := by
    rw [sum_ramp, max_eq_right hv0, max_eq_left (sub_nonpos.mpr hvN), sub_zero]
  have hdiff :
      (∑ i : Fin n, (ramp (t * h ^ 2 - (i.val : ℝ)) -
        ramp (s * h ^ 2 - (i.val : ℝ)))) = (t - s) * h ^ 2 := by
    rw [Finset.sum_sub_distrib, hsum (t * h ^ 2) ht0 ht,
      hsum (s * h ^ 2) hs0 hsN]
    ring
  have hpoint (i : Fin n) :
      (ramp (t * h ^ 2 - (i.val : ℝ)) -
        ramp (s * h ^ 2 - (i.val : ℝ))) ^ 2 ≤
      ramp (t * h ^ 2 - (i.val : ℝ)) -
        ramp (s * h ^ 2 - (i.val : ℝ)) := by
    have hmono := ramp_monotone (sub_le_sub_right hst2 (i.val : ℝ))
    have hd0 : 0 ≤ ramp (t * h ^ 2 - (i.val : ℝ)) -
        ramp (s * h ^ 2 - (i.val : ℝ)) := sub_nonneg.mpr hmono
    have hd1 : ramp (t * h ^ 2 - (i.val : ℝ)) -
        ramp (s * h ^ 2 - (i.val : ℝ)) ≤ 1 := by
      have hu := (ramp_bounds (t * h ^ 2 - (i.val : ℝ))).2
      have hl := (ramp_bounds (s * h ^ 2 - (i.val : ℝ))).1
      linarith
    nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hd1)]
  calc
    (∑ i : Fin n, incrementCoeff n h s t i ^ 2) =
        (∑ i : Fin n, (ramp (t * h ^ 2 - (i.val : ℝ)) -
          ramp (s * h ^ 2 - (i.val : ℝ))) ^ 2) / h ^ 2 := by
      simp only [incrementCoeff, div_pow, Finset.sum_div]
    _ ≤ (∑ i : Fin n, (ramp (t * h ^ 2 - (i.val : ℝ)) -
          ramp (s * h ^ 2 - (i.val : ℝ)))) / h ^ 2 :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => hpoint i)) hh2.le
    _ = t - s := by
      rw [hdiff, mul_div_assoc, div_self (ne_of_gt hh2), mul_one]

theorem polygonalPath_at_grid
    (n : ℕ) (h : ℝ) (hh : 0 < h) (a : Shao.Path n)
    (k : ℕ) (hk : k ≤ n) :
    polygonalPath n h a ((k : ℝ) / h ^ 2) = Shao.prefixSum a k / h := by
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hh)
  have htime : ((k : ℝ) / h ^ 2) * h ^ 2 = (k : ℝ) :=
    div_mul_cancel₀ _ hh2
  have hr (i : Fin n) : ramp ((k : ℝ) - (i.val : ℝ)) =
      (if i.val < k then 1 else 0) := by
    simpa using ramp_grid_affine k i.val 0 (by norm_num) (by norm_num)
  change (∑ i : Fin n, ramp (((k : ℝ) / h ^ 2) * h ^ 2 -
    (i.val : ℝ)) * a i / h) = Shao.prefixSum a k / h
  rw [htime]
  simp_rw [hr]
  rw [← Finset.sum_div]
  congr 1
  simp [Shao.prefixSum, Finset.sum_filter, ite_mul]

theorem polygonalPath_on_grid_interval
    (n : ℕ) (h : ℝ) (hh : 0 < h) (a : Shao.Path n)
    (k : ℕ) (hk : k < n) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    polygonalPath n h a (((k : ℝ) + u) / h ^ 2) =
      (1 - u) * (Shao.prefixSum a k / h) +
        u * (Shao.prefixSum a (k + 1) / h) := by
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hh)
  have htime : (((k : ℝ) + u) / h ^ 2) * h ^ 2 = (k : ℝ) + u :=
    div_mul_cancel₀ _ hh2
  have hr (i : Fin n) : ramp ((k : ℝ) + u - (i.val : ℝ)) =
      (1 - u) * (if i.val < k then 1 else 0) +
        u * (if i.val < k + 1 then 1 else 0) :=
    ramp_grid_affine k i.val u hu0 hu1
  have hprefix (j : ℕ) :
      (∑ i : Fin n, (if i.val < j then 1 else 0) * a i) =
        Shao.prefixSum a j := by
    simp [Shao.prefixSum, Finset.sum_filter, ite_mul]
  change (∑ i : Fin n, ramp ((((k : ℝ) + u) / h ^ 2) * h ^ 2 -
    (i.val : ℝ)) * a i / h) = _
  rw [htime]
  simp_rw [hr]
  rw [← hprefix k, ← hprefix (k + 1)]
  simp only [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem polygonal_increment_abs_cube_integrable
    (n : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (h s t : ℝ) (hh : 0 < h) (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t * h ^ 2 ≤ (n : ℝ)) :
    Integrable (fun a : Shao.Path n =>
      |polygonalPath n h a t - polygonalPath n h a s| ^ 3)
      (Measure.pi (fun _ : Fin n => ν)) := by
  simpa only [polygonal_increment_eq_sum] using
    WeightedThirdMoment.weighted_sum_abs_cube_integrable n ν h3
      (incrementCoeff n h s t)

theorem polygonal_increment_abs_cube_le
    (n : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (h s t : ℝ) (hh : 0 < h) (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t * h ^ 2 ≤ (n : ℝ)) :
    (∫ a : Shao.Path n,
      |polygonalPath n h a t - polygonalPath n h a s| ^ 3
      ∂(Measure.pi (fun _ : Fin n => ν))) ≤
      24 * (∫ x : ℝ, |x| ^ 3 ∂ν) * (Real.sqrt (t - s)) ^ 3 := by
  have hB2 := WeightedThirdMoment.weighted_sum_abs_cube_le n ν h3 hmean
    (incrementCoeff n h s t)
  have hβ : 0 ≤ ∫ x : ℝ, |x| ^ 3 ∂ν :=
    integral_nonneg (fun x => pow_nonneg (abs_nonneg x) 3)
  have hroot :
      Real.sqrt (∑ i : Fin n, incrementCoeff n h s t i ^ 2) ≤
        Real.sqrt (t - s) :=
    Real.sqrt_le_sqrt (incrementCoeff_energy_le n h s t hh hs hst ht)
  have hpow :
      (Real.sqrt (∑ i : Fin n, incrementCoeff n h s t i ^ 2)) ^ 3 ≤
        (Real.sqrt (t - s)) ^ 3 := by
    have hx := Real.sqrt_nonneg (∑ i : Fin n, incrementCoeff n h s t i ^ 2)
    have hy := Real.sqrt_nonneg (t - s)
    have hsq := mul_le_mul hroot hroot hx hy
    calc
      (Real.sqrt (∑ i : Fin n, incrementCoeff n h s t i ^ 2)) ^ 3 =
          (Real.sqrt (∑ i : Fin n, incrementCoeff n h s t i ^ 2) *
            Real.sqrt (∑ i : Fin n, incrementCoeff n h s t i ^ 2)) *
            Real.sqrt (∑ i : Fin n, incrementCoeff n h s t i ^ 2) := by ring
      _ ≤ (Real.sqrt (t - s) * Real.sqrt (t - s)) * Real.sqrt (t - s) :=
        mul_le_mul hsq hroot hx (mul_self_nonneg _)
      _ = (Real.sqrt (t - s)) ^ 3 := by ring
  have hscale :
      24 * (∫ x : ℝ, |x| ^ 3 ∂ν) *
          (Real.sqrt (∑ i : Fin n, incrementCoeff n h s t i ^ 2)) ^ 3 ≤
        24 * (∫ x : ℝ, |x| ^ 3 ∂ν) * (Real.sqrt (t - s)) ^ 3 :=
    mul_le_mul_of_nonneg_left hpow (mul_nonneg (by norm_num) hβ)
  simpa only [polygonal_increment_eq_sum] using hB2.trans hscale

end Shao.OQ4.PolygonalThirdMoment
