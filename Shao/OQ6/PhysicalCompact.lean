import Shao.OQ6.FiniteRows
import Shao.OQ6.ActualQuadraticTiltMoments
import Shao.OQ6.FiniteTiltedMoments
import Shao.OQ6.CompactGoodEvent
import Shao.Probability.FiniteIIDMoments
import Shao.OQ4.IntervalConcentration
import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false

namespace Shao.OQ6.PhysicalCompact

noncomputable section

open MeasureTheory
open scoped BigOperators

private theorem tau_order_and_bounds
    (c : ℝ) (hc : 0 < c) :
    let τ : ℝ → ℝ := fun x => x / Real.sqrt (1 + c * x ^ 2)
    StrictMono τ ∧
      (∀ x : ℝ,
        -(1 / Real.sqrt c) < τ x ∧ τ x < 1 / Real.sqrt c) ∧
      (∀ x : ℝ,
        |τ x| ≤ |x| ∧ |τ x - x| ≤ c * |x| ^ 3 / 2) := by
  classical
  let q : ℝ → ℝ := fun x => Real.sqrt (1 + c * x ^ 2)
  let τ : ℝ → ℝ := fun x => x / q x
  change StrictMono τ ∧
    (∀ x : ℝ, -(1 / Real.sqrt c) < τ x ∧ τ x < 1 / Real.sqrt c) ∧
    (∀ x : ℝ, |τ x| ≤ |x| ∧ |τ x - x| ≤ c * |x| ^ 3 / 2)
  have hqnon (x : ℝ) : 0 ≤ q x := Real.sqrt_nonneg _
  have hqsq (x : ℝ) : q x ^ 2 = 1 + c * x ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hqone (x : ℝ) : 1 ≤ q x := by
    have hu : 0 ≤ c * x ^ 2 := mul_nonneg hc.le (sq_nonneg x)
    by_contra hnot
    have hlt : q x < 1 := lt_of_not_ge hnot
    have hprod : 0 < (1 - q x) * (1 + q x) :=
      mul_pos (by linarith) (by have hh := hqnon x; linarith)
    nlinarith [hqsq x]
  have hqpos (x : ℝ) : 0 < q x := by linarith [hqone x]
  have hodd (x : ℝ) : τ (-x) = -τ x := by
    dsimp only [τ, q]
    rw [neg_sq, neg_div]
  have hnonneg (x y : ℝ) (hx : 0 ≤ x) (hxy : x < y) : τ x < τ y := by
    have hy : 0 < y := lt_of_le_of_lt hx hxy
    have hleft : 0 ≤ x * q y := mul_nonneg hx (hqnon y)
    have hright : 0 ≤ y * q x := mul_nonneg hy.le (hqnon x)
    have hsq : (x * q y) ^ 2 < (y * q x) ^ 2 := by
      rw [mul_pow, mul_pow, hqsq x, hqsq y]
      have hdiff := mul_pos (sub_pos.mpr hxy) (by linarith : 0 < y + x)
      nlinarith
    have hcross : x * q y < y * q x := by
      by_contra hnot
      have hprod := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hnot))
        (add_nonneg hleft hright)
      nlinarith
    exact (div_lt_div_iff₀ (hqpos x) (hqpos y)).2 hcross
  have hmono : StrictMono τ := by
    intro x y hxy
    by_cases hx : 0 ≤ x
    · exact hnonneg x y hx hxy
    · have hxneg : x < 0 := lt_of_not_ge hx
      by_cases hy : 0 ≤ y
      · have htx : τ x < 0 := div_neg_of_neg_of_pos hxneg (hqpos x)
        have hty : 0 ≤ τ y := div_nonneg hy (hqnon y)
        exact lt_of_lt_of_le htx hty
      · have hyneg : y < 0 := lt_of_not_ge hy
        have hm := hnonneg (-y) (-x) (by linarith) (by linarith)
        rw [hodd, hodd] at hm
        linarith
  have hcr : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hcrsq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  have hrange (x : ℝ) :
      -(1 / Real.sqrt c) < τ x ∧ τ x < 1 / Real.sqrt c := by
    have hleftnon : 0 ≤ |x| * Real.sqrt c :=
      mul_nonneg (abs_nonneg x) hcr.le
    have hleftsq : (|x| * Real.sqrt c) ^ 2 = c * x ^ 2 := by
      rw [mul_pow, sq_abs, hcrsq]
      ring
    have hcross : |x| * Real.sqrt c < q x := by
      by_contra hnot
      have hprod := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hnot))
        (add_nonneg hleftnon (hqnon x))
      nlinarith [hqsq x]
    have habs : |τ x| < 1 / Real.sqrt c := by
      change |x / q x| < 1 / Real.sqrt c
      rw [abs_div, abs_of_pos (hqpos x)]
      exact (div_lt_div_iff₀ (hqpos x) hcr).2 (by simpa using hcross)
    exact abs_lt.mp habs
  refine ⟨hmono, hrange, ?_⟩
  intro x
  have hratio : 1 - 1 / q x ≤ c * x ^ 2 / 2 := by
    have hden : 0 < q x * (q x + 1) := by positivity
    have heq : 1 - 1 / q x = c * x ^ 2 / (q x * (q x + 1)) := by
      field_simp [(hqpos x).ne', (by linarith [hqone x] : q x + 1 ≠ 0)]
      nlinarith [hqsq x]
    rw [heq]
    apply (div_le_iff₀ hden).2
    have hden2 : 2 ≤ q x * (q x + 1) := by nlinarith [hqone x]
    have hprod := mul_nonneg (mul_nonneg hc.le (sq_nonneg x))
      (sub_nonneg.mpr hden2)
    nlinarith
  have hinv : 1 / q x ≤ 1 := (div_le_iff₀ (hqpos x)).2 (by linarith [hqone x])
  constructor
  · change |x / q x| ≤ |x|
    rw [abs_div, abs_of_pos (hqpos x)]
    apply (div_le_iff₀ (hqpos x)).2
    nlinarith [mul_nonneg (abs_nonneg x) (sub_nonneg.mpr (hqone x))]
  · calc
      |τ x - x| = |x| * (1 - 1 / q x) := by
        have heq : τ x - x = x * (1 / q x - 1) := by
          dsimp only [τ]
          ring
        rw [heq, abs_mul, abs_of_nonpos (by linarith : 1 / q x - 1 ≤ 0)]
        ring
      _ ≤ |x| * (c * x ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hratio (abs_nonneg x)
      _ = c * |x| ^ 3 / 2 := by rw [← sq_abs x]; ring

theorem finite_physical_studentizer_conversion
    {n : ℕ} (H : Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hn : 3 ≤ n) :
    let N : ℝ := (n : ℝ)
    let U : ℝ := Shao.OQ6.FiniteRows.uStatistic H
    let J : ℝ := Shao.OQ6.FiniteRows.uncenteredSq H
    let R2 : ℝ := Shao.OQ6.FiniteRows.jackknifeSq H
    let c : ℝ := 4 * (N - 1) / (N - 2) ^ 2
    let τ : ℝ → ℝ := fun x => x / Real.sqrt (1 + c * x ^ 2)
    let T : ℝ :=
      if 0 < R2 then Real.sqrt N * U / Real.sqrt R2 else 0
    let Tstar : ℝ :=
      if 0 < J then Real.sqrt N * U / (2 * Real.sqrt J) else 0
    0 < c ∧ 0 ≤ R2 ∧ 0 ≤ J ∧
      (0 < R2 →
        0 < J ∧ Tstar = τ T ∧
          ∀ x : ℝ,
            (T ≤ x ↔ Tstar ≤ τ x) ∧
            (T < x ↔ Tstar < τ x) ∧
            (x ≤ T ↔ τ x ≤ Tstar) ∧
            (x < T ↔ τ x < Tstar) ∧
            (T = x ↔ Tstar = τ x)) ∧
      (R2 = 0 →
        T = 0 ∧
          (U = 0 → J = 0 ∧ Tstar = 0) ∧
          (0 < U → Tstar = 1 / Real.sqrt c) ∧
          (U < 0 → Tstar = -(1 / Real.sqrt c)) ∧
          ∀ x : ℝ,
            (Tstar ≤ τ x ↔ U < 0 ∨ (U = 0 ∧ 0 ≤ x)) ∧
            (Tstar < τ x ↔ U < 0 ∨ (U = 0 ∧ 0 < x)) ∧
            (τ x ≤ Tstar ↔ 0 < U ∨ (U = 0 ∧ x ≤ 0)) ∧
            (τ x < Tstar ↔ 0 < U ∨ (U = 0 ∧ x < 0))) ∧
      (∀ x : ℝ,
        |τ x| ≤ |x| ∧ |τ x - x| ≤ c * |x| ^ 3 / 2) ∧
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ τ x ∧ τ x ≤ 1) ∧
      (∀ x : ℝ, |x| ≤ 1 →
        |Shao.OQ4.standardNormalCDF (τ x) -
          Shao.OQ4.standardNormalCDF x| ≤ 12 / N) := by
  classical
  let N : ℝ := (n : ℝ)
  let U : ℝ := Shao.OQ6.FiniteRows.uStatistic H
  let J : ℝ := Shao.OQ6.FiniteRows.uncenteredSq H
  let R2 : ℝ := Shao.OQ6.FiniteRows.jackknifeSq H
  let c : ℝ := 4 * (N - 1) / (N - 2) ^ 2
  let τ : ℝ → ℝ := fun x => x / Real.sqrt (1 + c * x ^ 2)
  let T : ℝ := if 0 < R2 then Real.sqrt N * U / Real.sqrt R2 else 0
  let Tstar : ℝ := if 0 < J then Real.sqrt N * U / (2 * Real.sqrt J) else 0
  change 0 < c ∧ 0 ≤ R2 ∧ 0 ≤ J ∧
      (0 < R2 →
        0 < J ∧ Tstar = τ T ∧
          ∀ x : ℝ,
            (T ≤ x ↔ Tstar ≤ τ x) ∧
            (T < x ↔ Tstar < τ x) ∧
            (x ≤ T ↔ τ x ≤ Tstar) ∧
            (x < T ↔ τ x < Tstar) ∧
            (T = x ↔ Tstar = τ x)) ∧
      (R2 = 0 →
        T = 0 ∧
          (U = 0 → J = 0 ∧ Tstar = 0) ∧
          (0 < U → Tstar = 1 / Real.sqrt c) ∧
          (U < 0 → Tstar = -(1 / Real.sqrt c)) ∧
          ∀ x : ℝ,
            (Tstar ≤ τ x ↔ U < 0 ∨ (U = 0 ∧ 0 ≤ x)) ∧
            (Tstar < τ x ↔ U < 0 ∨ (U = 0 ∧ 0 < x)) ∧
            (τ x ≤ Tstar ↔ 0 < U ∨ (U = 0 ∧ x ≤ 0)) ∧
            (τ x < Tstar ↔ 0 < U ∨ (U = 0 ∧ x < 0))) ∧
      (∀ x : ℝ,
        |τ x| ≤ |x| ∧ |τ x - x| ≤ c * |x| ^ 3 / 2) ∧
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ τ x ∧ τ x ≤ 1) ∧
      (∀ x : ℝ, |x| ≤ 1 →
        |Shao.OQ4.standardNormalCDF (τ x) -
          Shao.OQ4.standardNormalCDF x| ≤ 12 / N)
  have hN3 : 3 ≤ N := by
    change (3 : ℝ) ≤ (n : ℝ)
    exact_mod_cast hn
  have hN : 0 < N := by linarith
  have hN1 : 0 < N - 1 := by linarith
  have hN2 : 0 < N - 2 := by linarith
  have hc : 0 < c := by dsimp only [c]; positivity
  have hR : 0 ≤ R2 := Shao.OQ6.FiniteRows.jackknifeSq_nonneg H hn
  have hJ : 0 ≤ J := Shao.OQ6.FiniteRows.uncenteredSq_nonneg H hn
  have hcent := Shao.OQ6.FiniteRows.uncenteredSq_eq_jackknifeSq_add H hH hn
  change J = R2 / 4 + ((N - 1) / (N - 2) ^ 2) * N * U ^ 2 at hcent
  have hcent4 : 4 * J = R2 + c * N * U ^ 2 := by
    calc
      4 * J = 4 * (R2 / 4 + ((N - 1) / (N - 2) ^ 2) * N * U ^ 2) :=
        congrArg (fun z : ℝ => 4 * z) hcent
      _ = R2 + c * N * U ^ 2 := by dsimp only [c]; ring
  have ht := tau_order_and_bounds c hc
  change StrictMono τ ∧
    (∀ x : ℝ, -(1 / Real.sqrt c) < τ x ∧ τ x < 1 / Real.sqrt c) ∧
    (∀ x : ℝ, |τ x| ≤ |x| ∧ |τ x - x| ≤ c * |x| ^ 3 / 2) at ht
  have ht0 : τ 0 = 0 := by simp [τ]
  have hle (x y : ℝ) : τ x ≤ τ y ↔ x ≤ y := by
    constructor
    · intro hxy
      by_contra hnot
      have hlt := ht.1 (lt_of_not_ge hnot)
      linarith
    · intro hxy
      exact ht.1.monotone hxy
  have hlt (x y : ℝ) : τ x < τ y ↔ x < y := by
    constructor
    · intro hxy
      by_contra hnot
      have hrev := ht.1.monotone (le_of_not_gt hnot)
      linarith
    · intro hxy
      exact ht.1 hxy
  have huniq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hsq : a ^ 2 = b ^ 2) :
      a = b := by
    have hp : (a - b) * (a + b) = 0 := by nlinarith [hsq]
    have hnz : a + b ≠ 0 := ne_of_gt (by linarith)
    have hab := (mul_eq_zero.mp hp).resolve_right hnz
    linarith
  let qN : ℝ := Real.sqrt N
  have hqN : 0 < qN := Real.sqrt_pos.mpr hN
  have hqNsq : qN ^ 2 = N := Real.sq_sqrt hN.le
  refine ⟨hc, hR, hJ, ?_, ?_, ht.2.2, ?_, ?_⟩
  · intro hRp
    have hJp : 0 < J := by
      have hh := mul_nonneg (mul_nonneg hc.le hN.le) (sq_nonneg U)
      nlinarith [hcent4]
    let qR : ℝ := Real.sqrt R2
    let qJ : ℝ := Real.sqrt J
    have hqR : 0 < qR := Real.sqrt_pos.mpr hRp
    have hqJ : 0 < qJ := Real.sqrt_pos.mpr hJp
    have hqRsq : qR ^ 2 = R2 := Real.sq_sqrt hR
    have hqJsq : qJ ^ 2 = J := Real.sq_sqrt hJ
    have hT : T = qN * U / qR := by exact if_pos hRp
    have hTsq : R2 * T ^ 2 = N * U ^ 2 := by
      rw [hT, div_pow, mul_pow, hqNsq, hqRsq]
      field_simp [hRp.ne'] <;> ring
    have hratioSq : (2 * qJ / qR) ^ 2 = 1 + c * T ^ 2 := by
      rw [div_pow, mul_pow, hqJsq, hqRsq]
      apply (div_eq_iff hRp.ne').2
      have hh := congrArg (fun z : ℝ => c * z) hTsq
      nlinarith [hcent4]
    have hratio : Real.sqrt (1 + c * T ^ 2) = 2 * qJ / qR := by
      apply huniq _ _ (Real.sqrt_nonneg _) (by positivity)
      exact (Real.sq_sqrt (by positivity)).trans hratioSq.symm
    have hconv : Tstar = τ T := by
      change (if 0 < J then qN * U / (2 * qJ) else 0) =
        T / Real.sqrt (1 + c * T ^ 2)
      rw [if_pos hJp, hratio, hT]
      field_simp [hqJ.ne', hqR.ne'] <;> ring
    refine ⟨hJp, hconv, ?_⟩
    intro x
    rw [hconv]
    exact ⟨(hle T x).symm, (hlt T x).symm,
      (hle x T).symm, (hlt x T).symm,
      ⟨fun htx => congrArg τ htx, fun htx => ht.1.injective htx⟩⟩
  · intro hR0
    have hT0 : T = 0 := by simp [T, hR0]
    have hJ0 (hU : U = 0) : J = 0 ∧ Tstar = 0 := by
      have hj : J = 0 := by
        have hcent0 : 4 * J = 0 := by
          simpa only [hR0, hU, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
            using hcent4
        linarith only [hcent0]
      exact ⟨hj, by simp [Tstar, hj]⟩
    have hzformula (hU : U ≠ 0) : Tstar = U / (Real.sqrt c * |U|) := by
      have hUsq : 0 < U ^ 2 := sq_pos_of_ne_zero hU
      have hJp : 0 < J := by
        have hh := mul_pos (mul_pos hc hN) hUsq
        nlinarith [hcent4]
      have hqJ : 0 < Real.sqrt J := Real.sqrt_pos.mpr hJp
      have hcr : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
      have habs : 0 < |U| := abs_pos.mpr hU
      have hsqrt :
          2 * Real.sqrt J = Real.sqrt c * qN * |U| := by
        apply huniq _ _ (by positivity) (by positivity)
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hJ,
          Real.sq_sqrt hc.le, hqNsq, sq_abs]
        nlinarith [hcent4]
      change (if 0 < J then qN * U / (2 * Real.sqrt J) else 0) =
        U / (Real.sqrt c * |U|)
      rw [if_pos hJp, hsqrt]
      field_simp [hcr.ne', hqN.ne', habs.ne'] <;> ring
    have hUp (hU : 0 < U) : Tstar = 1 / Real.sqrt c := by
      rw [hzformula (ne_of_gt hU), abs_of_pos hU]
      field_simp [hU.ne', (Real.sqrt_pos.mpr hc).ne']
    have hUn (hU : U < 0) : Tstar = -(1 / Real.sqrt c) := by
      rw [hzformula (ne_of_lt hU), abs_of_neg hU]
      field_simp [hU.ne, (Real.sqrt_pos.mpr hc).ne'] <;> ring
    refine ⟨hT0, hJ0, hUp, hUn, ?_⟩
    intro x
    have hrange := ht.2.1 x
    by_cases hpos : 0 < U
    · rw [hUp hpos]
      simp only [hpos, ne_of_gt hpos, false_and, or_false, or_true, false_or, true_or, and_false, and_true,
        not_lt.mpr hpos.le, not_le.mpr hrange.2, not_lt.mpr hrange.2.le,
        hrange.2, hrange.2.le, iff_self, and_self]
    · by_cases hneg : U < 0
      · rw [hUn hneg]
        simp only [hneg, ne_of_lt hneg, false_and, true_or, false_or, or_false, or_true, and_false, and_true,
          not_lt.mpr hneg.le, not_le.mpr hrange.1, not_lt.mpr hrange.1.le,
          hrange.1, hrange.1.le, iff_self, and_self]
      · have hzero : U = 0 := by linarith
        rw [(hJ0 hzero).2]
        have h1 : 0 ≤ τ x ↔ 0 ≤ x := by simpa only [ht0] using hle 0 x
        have h2 : 0 < τ x ↔ 0 < x := by simpa only [ht0] using hlt 0 x
        have h3 : τ x ≤ 0 ↔ x ≤ 0 := by simpa only [ht0] using hle x 0
        have h4 : τ x < 0 ↔ x < 0 := by simpa only [ht0] using hlt x 0
        simpa only [hzero, lt_self_iff_false, true_and, false_or] using
          And.intro h1 (And.intro h2 (And.intro h3 h4))
  · intro x hx hx1
    have htx : 0 ≤ τ x := by
      have hh := (hle 0 x).2 hx
      simpa only [ht0] using hh
    refine ⟨htx, ?_⟩
    calc
      τ x ≤ |τ x| := le_abs_self _
      _ ≤ |x| := (ht.2.2 x).1
      _ ≤ 1 := by simpa only [abs_of_nonneg hx] using hx1
  · intro x hx
    have hcN : c ≤ 24 / N := by
      change 4 * (N - 1) / (N - 2) ^ 2 ≤ 24 / N
      apply (div_le_div_iff₀ (sq_pos_of_pos hN2) hN).2
      have hp := mul_nonneg (sub_nonneg.mpr hN3)
        (by linarith : 0 ≤ 5 * N - 8)
      nlinarith
    have hx3 : |x| ^ 3 ≤ 1 := by
      simpa using pow_le_pow_left₀ (abs_nonneg x) hx 3
    calc
      |Shao.OQ4.standardNormalCDF (τ x) - Shao.OQ4.standardNormalCDF x|
          ≤ |τ x - x| := Shao.OQ4.standardNormalCDF_lipschitz _ _
      _ ≤ c * |x| ^ 3 / 2 := (ht.2.2 x).2
      _ ≤ c / 2 := by
        have hh := mul_le_mul_of_nonneg_left hx3 hc.le
        linarith
      _ ≤ 12 / N := by
        calc
          c / 2 ≤ (24 / N) / 2 := div_le_div_of_nonneg_right hcN (by norm_num)
          _ = 12 / N := by ring

private theorem uStatistic_add_projection
    {n : ℕ} (g : Fin n → ℝ) (r : Fin n → Fin n → ℝ)
    (hn : 3 ≤ n) :
    Shao.OQ6.FiniteRows.uStatistic
        (fun i j => g i + g j + r i j) =
      2 * (∑ i : Fin n, g i) / (n : ℝ) +
        2 * Shao.OQ5.P35.unorderedPairSum r /
          ((n : ℝ) * ((n : ℝ) - 1)) := by
  classical
  let N : ℝ := (n : ℝ)
  let S : ℝ := ∑ i : Fin n, g i
  let H0 : Fin n → Fin n → ℝ := fun i j => g i + g j
  have hN3 : 3 ≤ N := by
    change (3 : ℝ) ≤ (n : ℝ)
    exact_mod_cast hn
  have hN : N ≠ 0 := by linarith
  have hN1 : N - 1 ≠ 0 := by linarith
  have herase (i : Fin n) :
      (∑ j ∈ Finset.univ.erase i, H0 i j) = (N - 2) * g i + S := by
    have hsumg : (∑ j ∈ Finset.univ.erase i, g j) = S - g i := by
      have hh := Finset.sum_erase_add Finset.univ g (Finset.mem_univ i)
      change (∑ j ∈ Finset.univ.erase i, g j) + g i = S at hh
      linarith
    have hsumc : (∑ j ∈ Finset.univ.erase i, g i) = (N - 1) * g i := by
      have hh := Finset.sum_erase_add Finset.univ (fun _ : Fin n => g i)
        (Finset.mem_univ i)
      have hfull : (∑ _j : Fin n, g i) = N * g i := by simp [N]
      rw [hfull] at hh
      linarith
    dsimp only [H0]
    rw [Finset.sum_add_distrib, hsumc, hsumg]
    ring
  have hpair0 :
      Shao.OQ5.P35.unorderedPairSum H0 = (N - 1) * S := by
    have hh := Shao.OQ5.P35.offDiagonalSum_eq_two_unordered H0
      (fun i j => add_comm (g i) (g j))
    simp_rw [herase] at hh
    have hsum :
        (∑ i : Fin n, ((N - 2) * g i + S)) = 2 * (N - 1) * S := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      change (N - 2) * S + N * S = 2 * (N - 1) * S
      ring
    rw [hsum] at hh
    linarith
  have hsplit :
      Shao.OQ5.P35.unorderedPairSum (fun i j => g i + g j + r i j) =
        Shao.OQ5.P35.unorderedPairSum H0 + Shao.OQ5.P35.unorderedPairSum r := by
    unfold Shao.OQ5.P35.unorderedPairSum
    simp only [H0]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> ring
  have hchoose : (n.choose 2 : ℝ) = N * (N - 1) / 2 := by
    have hh := Shao.OQ5.P35.pairCount_eq_choose n
    simpa only [Shao.OQ5.P35.pairCount, N] using hh.symm
  unfold Shao.OQ6.FiniteRows.uStatistic
  rw [hsplit, hpair0, hchoose]
  change (N * (N - 1) / 2)⁻¹ *
      ((N - 1) * S + Shao.OQ5.P35.unorderedPairSum r) =
    2 * S / N + 2 * Shao.OQ5.P35.unorderedPairSum r / (N * (N - 1))
  field_simp [hN, hN1] <;> ring

theorem actual_physical_zero_probability_and_compact_transport
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
    (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
    let s : ℝ := 1 + Real.sqrt v
    ∃ c_g : ℝ, 0 < c_g ∧
      ∀ (n : ℕ), 3 ≤ n →
        let N : ℝ := (n : ℝ)
        let P₀ : Measure (Fin n → Ω) :=
          Measure.pi (fun _ : Fin n => μ)
        let U : (Fin n → Ω) → ℝ := fun ξ =>
          Shao.OQ6.FiniteRows.uStatistic
            (fun i j => h (ξ i) (ξ j))
        let J : (Fin n → Ω) → ℝ := fun ξ =>
          Shao.OQ6.FiniteRows.uncenteredSq
            (fun i j => h (ξ i) (ξ j))
        let R2 : (Fin n → Ω) → ℝ := fun ξ =>
          Shao.OQ6.FiniteRows.jackknifeSq
            (fun i j => h (ξ i) (ξ j))
        let a : ℝ := (N - 1) / (N - 2) ^ 2
        let c_n : ℝ := 4 * (N - 1) / (N - 2) ^ 2
        let τ : ℝ → ℝ := fun x =>
          x / Real.sqrt (1 + c_n * x ^ 2)
        let Vsq : (Fin n → Ω) → ℝ := fun ξ =>
          (∑ i : Fin n, g (ξ i) ^ 2) / N
        let W : (Fin n → Ω) → ℝ := fun ξ =>
          (∑ i : Fin n, g (ξ i)) / Real.sqrt N
        let D₂ : (Fin n → Ω) → ℝ := fun ξ =>
          if 0 < Vsq ξ then J ξ / Vsq ξ - 1 else 0
        let G : Set (Fin n → Ω) := {ξ |
          (1 / 2 : ℝ) ≤ Vsq ξ ∧
          |W ξ| ≤ Real.sqrt (Real.sqrt N) *
            (4 + Real.sqrt (Vsq ξ))}
        let Hcpt : Set (Fin n → Ω) := {ξ |
          ξ ∈ G ∧ -(1 / 2 : ℝ) ≤ D₂ ξ}
        let T : (Fin n → Ω) → ℝ := fun ξ =>
          if 0 < R2 ξ then
            Real.sqrt N * U ξ / Real.sqrt (R2 ξ) else 0
        let Tstar : (Fin n → Ω) → ℝ := fun ξ =>
          if 0 < J ξ then
            Real.sqrt N * U ξ / (2 * Real.sqrt (J ξ)) else 0
        let Z : Set (Fin n → Ω) := {ξ | R2 ξ = 0}
        let Zplus : Set (Fin n → Ω) := {ξ |
          R2 ξ = 0 ∧ 0 < U ξ}
        let Zminus : Set (Fin n → Ω) := {ξ |
          R2 ξ = 0 ∧ U ξ < 0}
        Measurable U ∧ Measurable J ∧ Measurable R2 ∧
          Measurable T ∧ Measurable Tstar ∧
          MeasurableSet Hcpt ∧ MeasurableSet Z ∧
          MeasurableSet Zplus ∧ MeasurableSet Zminus ∧
          Integrable (fun ξ => U ξ ^ 2) P₀ ∧
          (∫ ξ, U ξ ^ 2 ∂P₀) ≤
            8 / N + 4 * v / (N * (N - 1)) ∧
          P₀.real (Hcpt ∩ Z) ≤
            32 * a + 16 * a * v / (N - 1) ∧
          P₀.real (Hcpt ∩ Z) ≤
            336 * s / Real.sqrt N ∧
          P₀.real Z ≤ Real.exp (-c_g * N) +
            ((1 / 16 : ℝ) + 16720 * s) / Real.sqrt N ∧
          (∀ x : ℝ,
            P₀.real {ξ | T ξ ≤ x} =
              P₀.real {ξ | Tstar ξ ≤ τ x} +
                (if 0 ≤ x then P₀.real Zplus else -P₀.real Zminus)) ∧
          (∀ x : ℝ,
            P₀.real {ξ | T ξ < x} =
              P₀.real {ξ | Tstar ξ < τ x} +
                (if 0 < x then P₀.real Zplus else -P₀.real Zminus)) ∧
          (∀ x : ℝ,
            P₀.real {ξ | x ≤ T ξ} =
              P₀.real {ξ | τ x ≤ Tstar ξ} +
                (if 0 < x then -P₀.real Zplus else P₀.real Zminus)) ∧
          (∀ x : ℝ,
            P₀.real {ξ | x < T ξ} =
              P₀.real {ξ | τ x < Tstar ξ} +
                (if 0 ≤ x then -P₀.real Zplus else P₀.real Zminus)) ∧
          (∀ x : ℝ,
            |P₀.real {ξ | T ξ ≤ x} -
              P₀.real {ξ | Tstar ξ ≤ τ x}| ≤ P₀.real Z) ∧
          (∀ x : ℝ,
            |P₀.real {ξ | T ξ < x} -
              P₀.real {ξ | Tstar ξ < τ x}| ≤ P₀.real Z) ∧
          (∀ x : ℝ, |x| ≤ 1 →
            |P₀.real {ξ | T ξ ≤ x} - Shao.OQ4.standardNormalCDF x| ≤
              |P₀.real {ξ | Tstar ξ ≤ τ x} -
                Shao.OQ4.standardNormalCDF (τ x)| +
              Real.exp (-c_g * N) +
                ((1 / 16 : ℝ) + 16720 * s) / Real.sqrt N + 12 / N) ∧
          (∀ x : ℝ, |x| ≤ 1 →
            |P₀.real {ξ | T ξ < x} - Shao.OQ4.standardNormalCDF x| ≤
              |P₀.real {ξ | Tstar ξ < τ x} -
                Shao.OQ4.standardNormalCDF (τ x)| +
              Real.exp (-c_g * N) +
                ((1 / 16 : ℝ) + 16720 * s) / Real.sqrt N + 12 / N) := by
  classical
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
  let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
  let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
  let s : ℝ := 1 + Real.sqrt v
  have hdata := Shao.OQ6.ActualQuadraticTiltMoments.actual_quadratic_source_moments
    μ h hh hh2 hhsymm hcenter hprojectionsecond 3 (by omega) 0 (by norm_num) (by positivity)
  dsimp only at hdata
  rcases hdata with ⟨hg, hg2, hgmean, hgsecond, hr, hr2, hrsymm, hrcan,
    hv, hs, hvs, hrest⟩
  change Measurable g at hg
  change MemLp g 2 μ at hg2
  change (∫ o, g o ∂μ) = 0 at hgmean
  change (∫ o, g o ^ 2 ∂μ) = 1 at hgsecond
  change Measurable (fun t : Ω × Ω => r t.1 t.2) at hr
  change MemLp (fun t : Ω × Ω => r t.1 t.2) 2 (μ.prod μ) at hr2
  change (∀ o y, r o y = r y o) at hrsymm
  change (∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0) at hrcan
  change 0 ≤ v at hv
  change 1 ≤ s at hs
  change v ≤ s ^ 2 at hvs
  obtain ⟨c_g, hc_g, hcompact⟩ :=
    Shao.OQ6.CompactGoodEvent.actual_uncentered_compact_localization_events
      μ h hh hh2 hhsymm hcenter hprojectionsecond
  obtain ⟨c_w, hc_w, hprojection⟩ :=
    Shao.OQ6.CompactGoodEvent.original_projection_compact_good_event
      μ g hg hg2 hgmean hgsecond
  refine ⟨c_g, hc_g, ?_⟩
  intro n hn
  let N : ℝ := (n : ℝ)
  let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  let U : (Fin n → Ω) → ℝ := fun ξ =>
    Shao.OQ6.FiniteRows.uStatistic (fun i j => h (ξ i) (ξ j))
  let J : (Fin n → Ω) → ℝ := fun ξ =>
    Shao.OQ6.FiniteRows.uncenteredSq (fun i j => h (ξ i) (ξ j))
  let R2 : (Fin n → Ω) → ℝ := fun ξ =>
    Shao.OQ6.FiniteRows.jackknifeSq (fun i j => h (ξ i) (ξ j))
  let a : ℝ := (N - 1) / (N - 2) ^ 2
  let c_n : ℝ := 4 * (N - 1) / (N - 2) ^ 2
  let τ : ℝ → ℝ := fun x => x / Real.sqrt (1 + c_n * x ^ 2)
  let Vsq : (Fin n → Ω) → ℝ := fun ξ => (∑ i : Fin n, g (ξ i) ^ 2) / N
  let W : (Fin n → Ω) → ℝ := fun ξ => (∑ i : Fin n, g (ξ i)) / Real.sqrt N
  let D₂ : (Fin n → Ω) → ℝ := fun ξ => if 0 < Vsq ξ then J ξ / Vsq ξ - 1 else 0
  let G : Set (Fin n → Ω) := {ξ |
    (1 / 2 : ℝ) ≤ Vsq ξ ∧
      |W ξ| ≤ Real.sqrt (Real.sqrt N) * (4 + Real.sqrt (Vsq ξ))}
  let Hcpt : Set (Fin n → Ω) := {ξ | ξ ∈ G ∧ -(1 / 2 : ℝ) ≤ D₂ ξ}
  let T : (Fin n → Ω) → ℝ := fun ξ =>
    if 0 < R2 ξ then Real.sqrt N * U ξ / Real.sqrt (R2 ξ) else 0
  let Tstar : (Fin n → Ω) → ℝ := fun ξ =>
    if 0 < J ξ then Real.sqrt N * U ξ / (2 * Real.sqrt (J ξ)) else 0
  let Z : Set (Fin n → Ω) := {ξ | R2 ξ = 0}
  let Zplus : Set (Fin n → Ω) := {ξ | R2 ξ = 0 ∧ 0 < U ξ}
  let Zminus : Set (Fin n → Ω) := {ξ | R2 ξ = 0 ∧ U ξ < 0}
  change Measurable U ∧ Measurable J ∧ Measurable R2 ∧
          Measurable T ∧ Measurable Tstar ∧
          MeasurableSet Hcpt ∧ MeasurableSet Z ∧
          MeasurableSet Zplus ∧ MeasurableSet Zminus ∧
          Integrable (fun ξ => U ξ ^ 2) P₀ ∧
          (∫ ξ, U ξ ^ 2 ∂P₀) ≤
            8 / N + 4 * v / (N * (N - 1)) ∧
          P₀.real (Hcpt ∩ Z) ≤
            32 * a + 16 * a * v / (N - 1) ∧
          P₀.real (Hcpt ∩ Z) ≤
            336 * s / Real.sqrt N ∧
          P₀.real Z ≤ Real.exp (-c_g * N) +
            ((1 / 16 : ℝ) + 16720 * s) / Real.sqrt N ∧
          (∀ x : ℝ,
            P₀.real {ξ | T ξ ≤ x} =
              P₀.real {ξ | Tstar ξ ≤ τ x} +
                (if 0 ≤ x then P₀.real Zplus else -P₀.real Zminus)) ∧
          (∀ x : ℝ,
            P₀.real {ξ | T ξ < x} =
              P₀.real {ξ | Tstar ξ < τ x} +
                (if 0 < x then P₀.real Zplus else -P₀.real Zminus)) ∧
          (∀ x : ℝ,
            P₀.real {ξ | x ≤ T ξ} =
              P₀.real {ξ | τ x ≤ Tstar ξ} +
                (if 0 < x then -P₀.real Zplus else P₀.real Zminus)) ∧
          (∀ x : ℝ,
            P₀.real {ξ | x < T ξ} =
              P₀.real {ξ | τ x < Tstar ξ} +
                (if 0 ≤ x then -P₀.real Zplus else P₀.real Zminus)) ∧
          (∀ x : ℝ,
            |P₀.real {ξ | T ξ ≤ x} -
              P₀.real {ξ | Tstar ξ ≤ τ x}| ≤ P₀.real Z) ∧
          (∀ x : ℝ,
            |P₀.real {ξ | T ξ < x} -
              P₀.real {ξ | Tstar ξ < τ x}| ≤ P₀.real Z) ∧
          (∀ x : ℝ, |x| ≤ 1 →
            |P₀.real {ξ | T ξ ≤ x} - Shao.OQ4.standardNormalCDF x| ≤
              |P₀.real {ξ | Tstar ξ ≤ τ x} -
                Shao.OQ4.standardNormalCDF (τ x)| +
              Real.exp (-c_g * N) +
                ((1 / 16 : ℝ) + 16720 * s) / Real.sqrt N + 12 / N) ∧
          (∀ x : ℝ, |x| ≤ 1 →
            |P₀.real {ξ | T ξ < x} - Shao.OQ4.standardNormalCDF x| ≤
              |P₀.real {ξ | Tstar ξ < τ x} -
                Shao.OQ4.standardNormalCDF (τ x)| +
              Real.exp (-c_g * N) +
                ((1 / 16 : ℝ) + 16720 * s) / Real.sqrt N + 12 / N)
  letI : IsProbabilityMeasure P₀ := inferInstance
  let q : ℝ := Real.sqrt N
  have hN3 : 3 ≤ N := by
    change (3 : ℝ) ≤ (n : ℝ)
    exact_mod_cast hn
  have hN : 0 < N := by linarith
  have hN1 : 0 < N - 1 := by linarith
  have hN2 : 0 < N - 2 := by linarith
  have hq : 0 < q := Real.sqrt_pos.mpr hN
  have hqsq : q ^ 2 = N := Real.sq_sqrt hN.le
  have ha : 0 < a := by dsimp only [a]; positivity
  have hUm : Measurable U := by
    dsimp [U, Shao.OQ6.FiniteRows.uStatistic, Shao.OQ5.P35.unorderedPairSum]
    fun_prop
  have hJm : Measurable J := by
    dsimp [J, Shao.OQ6.FiniteRows.uncenteredSq, Shao.OQ6.FiniteRows.rowMean]
    fun_prop
  have hRm : Measurable R2 := by
    dsimp [R2, Shao.OQ6.FiniteRows.jackknifeSq, Shao.OQ6.FiniteRows.rowMean,
      Shao.OQ6.FiniteRows.uStatistic, Shao.OQ5.P35.unorderedPairSum]
    fun_prop
  have hTm : Measurable T :=
    Measurable.ite (measurableSet_lt measurable_const hRm)
      ((hUm.const_mul q).div hRm.sqrt) measurable_const
  have hTsm : Measurable Tstar :=
    Measurable.ite (measurableSet_lt measurable_const hJm)
      ((hUm.const_mul q).div (hJm.sqrt.const_mul 2)) measurable_const
  have hZm : MeasurableSet Z := measurableSet_eq_fun hRm measurable_const
  have hZpm : MeasurableSet Zplus :=
    hZm.inter (measurableSet_lt measurable_const hUm)
  have hZmm : MeasurableSet Zminus :=
    hZm.inter (measurableSet_lt hUm measurable_const)
  have hcn := hcompact n hn
  dsimp only at hcn
  rcases hcn with ⟨hGm, hHm, hΛi, hBi, hBint, hGprob, hDprob, hHprob, hJlower⟩
  change MeasurableSet Hcpt at hHm
  change P₀.real Hcptᶜ ≤ Real.exp (-c_g * N) +
    ((1 / 16 : ℝ) + 16384 * s) / q at hHprob
  have hJlow (ξ : Fin n → Ω) (hξ : ξ ∈ Hcpt) : (1 / 4 : ℝ) ≤ J ξ :=
    (hJlower ξ hξ).2.2
  have hw := hprojection n (by omega)
  dsimp only at hw
  have hWi := hw.2.1
  have hWsecond := hw.2.2.1
  change Integrable (fun ξ => W ξ ^ 2) P₀ at hWi
  change (∫ ξ, W ξ ^ 2 ∂P₀) = 1 at hWsecond
  let F : (Fin n → Ω) → ℝ := fun ξ =>
    Shao.OQ5.P35.unorderedPairSum (fun i j => r (ξ i) (ξ j))
  have hρeq : μ.withDensity (fun _ => ENNReal.ofReal (1 : ℝ)) = μ := by
    apply Measure.ext
    intro A hA
    rw [withDensity_apply _ hA]
    simp
  have hfm := Shao.OQ6.FiniteTiltedMoments.unordered_pair_sum_second_moment
    μ r hr hr2 hrsymm hrcan (Real.sqrt v) (Real.sqrt_nonneg v)
    (by simpa only [Real.sq_sqrt hv] using le_refl v)
    (fun _ => 1) measurable_const 1
    (fun _ => by norm_num) (fun _ => by norm_num) (by simp)
    0 (by norm_num) (by simp) n
  dsimp only at hfm
  rw [hρeq] at hfm
  simp only [one_pow, zero_pow (by decide : 2 ≠ 0),
    zero_pow (by decide : 4 ≠ 0), mul_zero, add_zero, mul_one,
    Real.sq_sqrt hv] at hfm
  rcases hfm with ⟨hρprob, hPprob, hF2, hFi, hFeq, hFb⟩
  change Integrable (fun ξ => F ξ ^ 2) P₀ at hFi
  change (∫ ξ, F ξ ^ 2 ∂P₀) ≤ (n.choose 2 : ℝ) * v at hFb
  have hchoose : (n.choose 2 : ℝ) = N * (N - 1) / 2 := by
    have hh' := Shao.OQ5.P35.pairCount_eq_choose n
    simpa only [Shao.OQ5.P35.pairCount, N] using hh'.symm
  have hUrep (ξ : Fin n → Ω) :
      U ξ = 2 * W ξ / q + 2 * F ξ / (N * (N - 1)) := by
    have hh' := uStatistic_add_projection (fun i => g (ξ i))
      (fun i j => r (ξ i) (ξ j)) hn
    have hmatrix :
        (fun i j : Fin n => g (ξ i) + g (ξ j) + r (ξ i) (ξ j)) =
          (fun i j : Fin n => h (ξ i) (ξ j)) := by
      funext i j
      dsimp only [r]
      ring
    rw [hmatrix] at hh'
    change U ξ = 2 * (∑ i : Fin n, g (ξ i)) / N +
      2 * F ξ / (N * (N - 1)) at hh'
    rw [hh']
    congr 1
    change 2 * (∑ i : Fin n, g (ξ i)) / N =
      2 * ((∑ i : Fin n, g (ξ i)) / q) / q
    rw [show N = q * q from by nlinarith only [hqsq]]
    field_simp [hq.ne'] <;> ring
  have hpoint (ξ : Fin n → Ω) :
      U ξ ^ 2 ≤ (8 / N) * W ξ ^ 2 +
        (8 / (N ^ 2 * (N - 1) ^ 2)) * F ξ ^ 2 := by
    have hfirst : (2 * W ξ / q) ^ 2 = (4 / N) * W ξ ^ 2 := by
      rw [div_pow, mul_pow, hqsq]
      ring
    have hsecond : (2 * F ξ / (N * (N - 1))) ^ 2 =
        (4 / (N ^ 2 * (N - 1) ^ 2)) * F ξ ^ 2 := by
      rw [div_pow, mul_pow, mul_pow]
      ring
    have htwo (A B : ℝ) : (A + B) ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 := by
      nlinarith only [sq_nonneg (A - B)]
    rw [hUrep]
    calc
      (2 * W ξ / q + 2 * F ξ / (N * (N - 1))) ^ 2 ≤
          2 * (2 * W ξ / q) ^ 2 + 2 * (2 * F ξ / (N * (N - 1))) ^ 2 :=
        htwo _ _
      _ = (8 / N) * W ξ ^ 2 +
          (8 / (N ^ 2 * (N - 1) ^ 2)) * F ξ ^ 2 := by
        rw [hfirst, hsecond]
        ring
  have hboundi : Integrable (fun ξ => (8 / N) * W ξ ^ 2 +
      (8 / (N ^ 2 * (N - 1) ^ 2)) * F ξ ^ 2) P₀ :=
    (hWi.const_mul _).add (hFi.const_mul _)
  have hUi : Integrable (fun ξ => U ξ ^ 2) P₀ := by
    apply hboundi.mono' (hUm.pow_const 2).aestronglyMeasurable
    exact ae_of_all P₀ fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint ξ
  have hUbound : (∫ ξ, U ξ ^ 2 ∂P₀) ≤
      8 / N + 4 * v / (N * (N - 1)) := by
    calc
      (∫ ξ, U ξ ^ 2 ∂P₀) ≤
          ∫ ξ, (8 / N) * W ξ ^ 2 +
            (8 / (N ^ 2 * (N - 1) ^ 2)) * F ξ ^ 2 ∂P₀ :=
        integral_mono hUi hboundi hpoint
      _ = 8 / N + (8 / (N ^ 2 * (N - 1) ^ 2)) *
          (∫ ξ, F ξ ^ 2 ∂P₀) := by
        rw [integral_add (hWi.const_mul _) (hFi.const_mul _),
          integral_const_mul, integral_const_mul, hWsecond]
        ring
      _ ≤ 8 / N + (8 / (N ^ 2 * (N - 1) ^ 2)) *
          ((n.choose 2 : ℝ) * v) := by
        have hcoef : 0 ≤ 8 / (N ^ 2 * (N - 1) ^ 2) :=
          div_nonneg (by norm_num) (mul_nonneg (sq_nonneg N) (sq_nonneg (N - 1)))
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hFb hcoef)
      _ = 8 / N + 4 * v / (N * (N - 1)) := by
        rw [hchoose]
        field_simp [hN.ne', hN1.ne'] <;> ring
  have hHZm : MeasurableSet (Hcpt ∩ Z) := hHm.inter hZm
  have hmark : (1 / 4 : ℝ) * P₀.real (Hcpt ∩ Z) ≤
      a * N * (∫ ξ, U ξ ^ 2 ∂P₀) := by
    calc
      (1 / 4 : ℝ) * P₀.real (Hcpt ∩ Z) =
          ∫ ξ, (Hcpt ∩ Z).indicator (fun _ => (1 / 4 : ℝ)) ξ ∂P₀ := by
        rw [integral_indicator_const _ hHZm, smul_eq_mul, mul_comm]
      _ ≤ ∫ ξ, a * N * U ξ ^ 2 ∂P₀ := by
        apply integral_mono ((integrable_const _).indicator hHZm) (hUi.const_mul _)
        intro ξ
        by_cases hξ : ξ ∈ Hcpt ∩ Z
        · rw [Set.indicator_of_mem hξ]
          have hc := Shao.OQ6.FiniteRows.uncenteredSq_eq_jackknifeSq_add
            (fun i j => h (ξ i) (ξ j)) (fun i j => hhsymm (ξ i) (ξ j)) hn
          change J ξ = R2 ξ / 4 + a * N * U ξ ^ 2 at hc
          have hz : R2 ξ = 0 := hξ.2
          have hj := hJlow ξ hξ.1
          rw [hz, zero_div, zero_add] at hc
          change (1 / 4 : ℝ) ≤ a * N * U ξ ^ 2
          rw [← hc]
          exact hj
        · rw [Set.indicator_of_notMem hξ]
          exact mul_nonneg (mul_nonneg ha.le hN.le) (sq_nonneg (U ξ))
      _ = a * N * (∫ ξ, U ξ ^ 2 ∂P₀) := integral_const_mul _ _
  have hHZbound : P₀.real (Hcpt ∩ Z) ≤ 32 * a + 16 * a * v / (N - 1) := by
    have hu := mul_le_mul_of_nonneg_left hUbound (mul_nonneg ha.le hN.le)
    have heq : a * N * (8 / N + 4 * v / (N * (N - 1))) =
        8 * a + 4 * a * v / (N - 1) := by
      field_simp [hN.ne', hN1.ne'] <;> ring
    rw [heq] at hu
    calc
      P₀.real (Hcpt ∩ Z) = 4 * ((1 / 4 : ℝ) * P₀.real (Hcpt ∩ Z)) := by ring
      _ ≤ 4 * (8 * a + 4 * a * v / (N - 1)) :=
        mul_le_mul_of_nonneg_left (hmark.trans hu) (by norm_num)
      _ = 32 * a + 16 * a * v / (N - 1) := by ring
  have haN : a ≤ 6 / N := by
    dsimp only [a]
    apply (div_le_div_iff₀ (sq_pos_of_pos hN2) hN).2
    have hp := mul_nonneg (sub_nonneg.mpr hN3)
      (by linarith only [hN3] : 0 ≤ 5 * N - 8)
    nlinarith only [hp]
  have hHZsmall : P₀.real (Hcpt ∩ Z) ≤ 336 * s / q := by
    by_cases hscale : s ≤ q
    · have hvN : v ≤ N := by
        have hp := pow_le_pow_left₀ (by linarith only [hs] : 0 ≤ s) hscale 2
        rw [hqsq] at hp
        exact hvs.trans hp
      have hav : a * v ≤ 6 := by
        calc
          a * v ≤ (6 / N) * N :=
            mul_le_mul haN hvN hv (div_nonneg (by norm_num) hN.le)
          _ = 6 := by field_simp [hN.ne']
      have hdiv : 16 * a * v / (N - 1) ≤ 96 / (N - 1) :=
        div_le_div_of_nonneg_right (by nlinarith only [hav]) hN1.le
      have h96 : 96 / (N - 1) ≤ 144 / N := by
        apply (div_le_div_iff₀ hN1 hN).2
        nlinarith only [hN3]
      have hprobN : P₀.real (Hcpt ∩ Z) ≤ 336 / N := by
        have h32 : 32 * a ≤ 192 / N := by
          calc
            32 * a ≤ 32 * (6 / N) :=
              mul_le_mul_of_nonneg_left haN (by norm_num)
            _ = 192 / N := by ring
        calc
          P₀.real (Hcpt ∩ Z) ≤ 32 * a + 16 * a * v / (N - 1) := hHZbound
          _ ≤ 192 / N + 144 / N := add_le_add h32 (hdiv.trans h96)
          _ = 336 / N := by ring
      have hqone : 1 ≤ q := by
        by_contra hnot
        have hlt : q < 1 := lt_of_not_ge hnot
        have hp : 0 < (1 - q) * (1 + q) :=
          mul_pos (by linarith only [hlt]) (by linarith only [hq])
        nlinarith only [hp, hqsq, hN3]
      have hqN : q ≤ N := by
        have hp := mul_nonneg hq.le (sub_nonneg.mpr hqone)
        nlinarith only [hp, hqsq]
      have hsN : N ≤ s * N := by
        nlinarith only [mul_nonneg (by linarith only [hs] : 0 ≤ s - 1) hN.le]
      have hlast : 336 / N ≤ 336 * s / q := by
        apply (div_le_div_iff₀ hN hq).2
        nlinarith only [hqN, hsN]
      exact hprobN.trans hlast
    · have hlarge : q < s := lt_of_not_ge hscale
      have hone : (1 : ℝ) ≤ 336 * s / q := by
        apply (le_div_iff₀ hq).2
        linarith only [hlarge, hs]
      exact (measureReal_le_one (μ := P₀) (s := Hcpt ∩ Z)).trans hone
  have hZbound : P₀.real Z ≤ Real.exp (-c_g * N) +
      ((1 / 16 : ℝ) + 16720 * s) / q := by
    have hsub : Z ⊆ Hcptᶜ ∪ (Hcpt ∩ Z) := by
      intro ξ hz
      by_cases hh' : ξ ∈ Hcpt
      · exact Or.inr ⟨hh', hz⟩
      · exact Or.inl hh'
    calc
      P₀.real Z ≤ P₀.real (Hcptᶜ ∪ (Hcpt ∩ Z)) := measureReal_mono hsub
      _ ≤ P₀.real Hcptᶜ + P₀.real (Hcpt ∩ Z) := measureReal_union_le _ _
      _ ≤ (Real.exp (-c_g * N) + ((1 / 16 : ℝ) + 16384 * s) / q) +
          336 * s / q := add_le_add hHprob hHZsmall
      _ = _ := by ring

  have hpositive (ξ : Fin n → Ω) (hz : ξ ∉ Z) (x : ℝ) :
      (T ξ ≤ x ↔ Tstar ξ ≤ τ x) ∧ (T ξ < x ↔ Tstar ξ < τ x) := by
    have hf := finite_physical_studentizer_conversion
      (fun i j => h (ξ i) (ξ j)) (fun i j => hhsymm (ξ i) (ξ j)) hn
    have hnon : 0 ≤ R2 ξ := hf.2.1
    have hne : R2 ξ ≠ 0 := hz
    have hp := hf.2.2.2.1 (lt_of_le_of_ne hnon (Ne.symm hne))
    exact ⟨(hp.2.2 x).1, (hp.2.2 x).2.1⟩
  have hzero (ξ : Fin n → Ω) (hz : ξ ∈ Z) :
      T ξ = 0 ∧ ∀ x : ℝ,
        (Tstar ξ ≤ τ x ↔ U ξ < 0 ∨ (U ξ = 0 ∧ 0 ≤ x)) ∧
        (Tstar ξ < τ x ↔ U ξ < 0 ∨ (U ξ = 0 ∧ 0 < x)) := by
    have hf := finite_physical_studentizer_conversion
      (fun i j => h (ξ i) (ξ j)) (fun i j => hhsymm (ξ i) (ξ j)) hn
    have hz' : R2 ξ = 0 := hz
    have hd := hf.2.2.2.2.1 hz'
    refine ⟨hd.1, ?_⟩
    intro x
    exact ⟨(hd.2.2.2.2 x).1, (hd.2.2.2.2 x).2.1⟩
  have hind_le (x : ℝ) (ξ : Fin n → Ω) :
      {η | T η ≤ x}.indicator (fun _ => (1 : ℝ)) ξ =
        {η | Tstar η ≤ τ x}.indicator (fun _ => (1 : ℝ)) ξ +
          (if 0 ≤ x then Zplus.indicator (fun _ => (1 : ℝ)) ξ
           else -Zminus.indicator (fun _ => (1 : ℝ)) ξ) := by
    by_cases hz : ξ ∈ Z
    · have hT0 := (hzero ξ hz).1
      have hb := ((hzero ξ hz).2 x).1
      have hR0 : R2 ξ = 0 := hz
      rcases lt_trichotomy (U ξ) 0 with hu | hu | hu
      · by_cases hx : 0 ≤ x <;>
          simp [Set.indicator, Zplus, Zminus, hT0, hb, hR0, hu,
            ne_of_lt hu, not_lt.mpr hu.le, hx]
      · by_cases hx : 0 ≤ x <;>
          simp [Set.indicator, Zplus, Zminus, hT0, hb, hR0, hu, hx]
      · by_cases hx : 0 ≤ x <;>
          simp [Set.indicator, Zplus, Zminus, hT0, hb, hR0, hu,
            ne_of_gt hu, not_lt.mpr hu.le, hx]
    · have hzplus : ξ ∉ Zplus := fun hξ => hz hξ.1
      have hzminus : ξ ∉ Zminus := fun hξ => hz hξ.1
      have hb := (hpositive ξ hz x).1
      by_cases hA : T ξ ≤ x
      · have hB := hb.mp hA
        simp [Set.indicator, hA, hB, hzplus, hzminus]
      · have hB : ¬Tstar ξ ≤ τ x := fun hξ => hA (hb.mpr hξ)
        simp [Set.indicator, hA, hB, hzplus, hzminus]
  have hind_lt (x : ℝ) (ξ : Fin n → Ω) :
      {η | T η < x}.indicator (fun _ => (1 : ℝ)) ξ =
        {η | Tstar η < τ x}.indicator (fun _ => (1 : ℝ)) ξ +
          (if 0 < x then Zplus.indicator (fun _ => (1 : ℝ)) ξ
           else -Zminus.indicator (fun _ => (1 : ℝ)) ξ) := by
    by_cases hz : ξ ∈ Z
    · have hT0 := (hzero ξ hz).1
      have hb := ((hzero ξ hz).2 x).2
      have hR0 : R2 ξ = 0 := hz
      rcases lt_trichotomy (U ξ) 0 with hu | hu | hu
      · by_cases hx : 0 < x <;>
          simp [Set.indicator, Zplus, Zminus, hT0, hb, hR0, hu,
            ne_of_lt hu, not_lt.mpr hu.le, hx]
      · by_cases hx : 0 < x <;>
          simp [Set.indicator, Zplus, Zminus, hT0, hb, hR0, hu, hx]
      · by_cases hx : 0 < x <;>
          simp [Set.indicator, Zplus, Zminus, hT0, hb, hR0, hu,
            ne_of_gt hu, not_lt.mpr hu.le, hx]
    · have hzplus : ξ ∉ Zplus := fun hξ => hz hξ.1
      have hzminus : ξ ∉ Zminus := fun hξ => hz hξ.1
      have hb := (hpositive ξ hz x).2
      by_cases hA : T ξ < x
      · have hB := hb.mp hA
        simp [Set.indicator, hA, hB, hzplus, hzminus]
      · have hB : ¬Tstar ξ < τ x := fun hξ => hA (hb.mpr hξ)
        simp [Set.indicator, hA, hB, hzplus, hzminus]
  have hind_integral (A : Set (Fin n → Ω)) (hA : MeasurableSet A) :
      (∫ ξ, A.indicator (fun _ => (1 : ℝ)) ξ ∂P₀) = P₀.real A := by
    rw [integral_indicator_const _ hA, smul_eq_mul, mul_one]
  have hdelta (A B C : Set (Fin n → Ω))
      (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
      (e : ℝ)
      (heq : ∀ ξ, A.indicator (fun _ => (1 : ℝ)) ξ =
        B.indicator (fun _ => (1 : ℝ)) ξ +
          e * C.indicator (fun _ => (1 : ℝ)) ξ) :
      P₀.real A = P₀.real B + e * P₀.real C := by
    calc
      P₀.real A = ∫ ξ, A.indicator (fun _ => (1 : ℝ)) ξ ∂P₀ :=
        (hind_integral A hA).symm
      _ = ∫ ξ, B.indicator (fun _ => (1 : ℝ)) ξ +
          e * C.indicator (fun _ => (1 : ℝ)) ξ ∂P₀ :=
        integral_congr_ae (ae_of_all P₀ heq)
      _ = P₀.real B + e * P₀.real C := by
        rw [integral_add ((integrable_const _).indicator hB)
          (((integrable_const _).indicator hC).const_mul e),
          integral_const_mul, hind_integral B hB, hind_integral C hC]
  have hclosed (x : ℝ) :
      P₀.real {ξ | T ξ ≤ x} =
        P₀.real {ξ | Tstar ξ ≤ τ x} +
          (if 0 ≤ x then P₀.real Zplus else -P₀.real Zminus) := by
    have hA : MeasurableSet {ξ | T ξ ≤ x} := measurableSet_le hTm measurable_const
    have hB : MeasurableSet {ξ | Tstar ξ ≤ τ x} := measurableSet_le hTsm measurable_const
    by_cases hx : 0 ≤ x
    · have hd := hdelta _ _ Zplus hA hB hZpm 1 (fun ξ => by
        simpa only [if_pos hx, one_mul] using hind_le x ξ)
      simpa only [if_pos hx, one_mul] using hd
    · have hd := hdelta _ _ Zminus hA hB hZmm (-1) (fun ξ => by
        simpa only [if_neg hx, neg_one_mul] using hind_le x ξ)
      simpa only [if_neg hx, neg_one_mul] using hd
  have hstrict (x : ℝ) :
      P₀.real {ξ | T ξ < x} =
        P₀.real {ξ | Tstar ξ < τ x} +
          (if 0 < x then P₀.real Zplus else -P₀.real Zminus) := by
    have hA : MeasurableSet {ξ | T ξ < x} := measurableSet_lt hTm measurable_const
    have hB : MeasurableSet {ξ | Tstar ξ < τ x} := measurableSet_lt hTsm measurable_const
    by_cases hx : 0 < x
    · have hd := hdelta _ _ Zplus hA hB hZpm 1 (fun ξ => by
        simpa only [if_pos hx, one_mul] using hind_lt x ξ)
      simpa only [if_pos hx, one_mul] using hd
    · have hd := hdelta _ _ Zminus hA hB hZmm (-1) (fun ξ => by
        simpa only [if_neg hx, neg_one_mul] using hind_lt x ξ)
      simpa only [if_neg hx, neg_one_mul] using hd
  have hcompl (A : Set (Fin n → Ω)) (hA : MeasurableSet A) :
      P₀.real Aᶜ = 1 - P₀.real A := by
    have hd := hdelta Set.univ A Aᶜ MeasurableSet.univ hA hA.compl 1
      (fun ξ => by
        by_cases hξ : ξ ∈ A <;> simp [Set.indicator, hξ])
    rw [probReal_univ] at hd
    linarith only [hd]
  have hupperle (x : ℝ) :
      P₀.real {ξ | x ≤ T ξ} =
        P₀.real {ξ | τ x ≤ Tstar ξ} +
          (if 0 < x then -P₀.real Zplus else P₀.real Zminus) := by
    have heqA : {ξ | x ≤ T ξ} = {ξ | T ξ < x}ᶜ := by ext ξ; simp
    have heqB : {ξ | τ x ≤ Tstar ξ} = {ξ | Tstar ξ < τ x}ᶜ := by ext ξ; simp
    rw [heqA, heqB, hcompl _ (measurableSet_lt hTm measurable_const),
      hcompl _ (measurableSet_lt hTsm measurable_const), hstrict x]
    split_ifs <;> ring
  have hupperlt (x : ℝ) :
      P₀.real {ξ | x < T ξ} =
        P₀.real {ξ | τ x < Tstar ξ} +
          (if 0 ≤ x then -P₀.real Zplus else P₀.real Zminus) := by
    have heqA : {ξ | x < T ξ} = {ξ | T ξ ≤ x}ᶜ := by ext ξ; simp
    have heqB : {ξ | τ x < Tstar ξ} = {ξ | Tstar ξ ≤ τ x}ᶜ := by ext ξ; simp
    rw [heqA, heqB, hcompl _ (measurableSet_le hTm measurable_const),
      hcompl _ (measurableSet_le hTsm measurable_const), hclosed x]
    split_ifs <;> ring
  have hZpn : 0 ≤ P₀.real Zplus := ENNReal.toReal_nonneg
  have hZmn : 0 ≤ P₀.real Zminus := ENNReal.toReal_nonneg
  have hZpsub : P₀.real Zplus ≤ P₀.real Z :=
    measureReal_mono (fun ξ hξ => hξ.1)
  have hZmsub : P₀.real Zminus ≤ P₀.real Z :=
    measureReal_mono (fun ξ hξ => hξ.1)
  have hpaid (b : Prop) :
      |if b then P₀.real Zplus else -P₀.real Zminus| ≤ P₀.real Z := by
    by_cases hb : b
    · simpa only [if_pos hb, abs_of_nonneg hZpn] using hZpsub
    · simpa only [if_neg hb, abs_neg, abs_of_nonneg hZmn] using hZmsub
  have hdiscle (x : ℝ) :
      |P₀.real {ξ | T ξ ≤ x} - P₀.real {ξ | Tstar ξ ≤ τ x}| ≤ P₀.real Z := by
    rw [hclosed x]
    convert hpaid (0 ≤ x) using 1 <;> congr 1 <;> ring
  have hdisclt (x : ℝ) :
      |P₀.real {ξ | T ξ < x} - P₀.real {ξ | Tstar ξ < τ x}| ≤ P₀.real Z := by
    rw [hstrict x]
    convert hpaid (0 < x) using 1 <;> congr 1 <;> ring
  have hgauss (x : ℝ) (hx : |x| ≤ 1) :
      |Shao.OQ4.standardNormalCDF (τ x) - Shao.OQ4.standardNormalCDF x| ≤ 12 / N := by
    have hf := finite_physical_studentizer_conversion
      (fun _ _ : Fin n => (0 : ℝ)) (by intros; rfl) hn
    rcases hf with ⟨hfc, hfR, hfJ, hfp, hfz, hfa, hfi, hfg⟩
    exact hfg x hx
  have htriangle (A B p t : ℝ) :
      |A - p| ≤ |B - t| + |A - B| + |t - p| := by
    calc
      |A - p| = |(B - t) + (A - B) + (t - p)| := by congr 1; ring
      _ ≤ |(B - t) + (A - B)| + |t - p| := abs_add_le _ _
      _ ≤ (|B - t| + |A - B|) + |t - p| :=
        add_le_add (abs_add_le _ _) le_rfl
  refine ⟨hUm, hJm, hRm, hTm, hTsm, hHm, hZm, hZpm, hZmm,
    hUi, hUbound, hHZbound, hHZsmall, hZbound, hclosed, hstrict,
    hupperle, hupperlt, hdiscle, hdisclt, ?_, ?_⟩
  · intro x hx
    have hh' := htriangle (P₀.real {ξ | T ξ ≤ x})
      (P₀.real {ξ | Tstar ξ ≤ τ x})
      (Shao.OQ4.standardNormalCDF x) (Shao.OQ4.standardNormalCDF (τ x))
    have hd := hdiscle x
    have hg' := hgauss x hx
    have hzb := hZbound
    dsimp only [q] at hzb
    linarith only [hh', hd, hg', hzb]
  · intro x hx
    have hh' := htriangle (P₀.real {ξ | T ξ < x})
      (P₀.real {ξ | Tstar ξ < τ x})
      (Shao.OQ4.standardNormalCDF x) (Shao.OQ4.standardNormalCDF (τ x))
    have hd := hdisclt x
    have hg' := hgauss x hx
    have hzb := hZbound
    dsimp only [q] at hzb
    linarith only [hh', hd, hg', hzb]

end

end Shao.OQ6.PhysicalCompact
