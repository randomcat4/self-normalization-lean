import Shao.OQ5.P51.BoundedStudentizerGeometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

universe u

open scoped BigOperators

namespace Shao.OQ5.P51

theorem literal_studentizer_budget_domination
    (n : ℕ) {Ω : Type u} (g : Ω → ℝ) (r : Ω → Ω → ℝ)
    (x : Fin n → Ω) (sigma y : ℝ)
    (hsym : ∀ a b : Ω, r a b = r b a)
    (hn : 4 ≤ n) (hsigma : (1 : ℝ) ≤ sigma) (hy : (1 : ℝ) ≤ y)
    (hwindow : sigma * y ≤ Real.sqrt (n : ℝ))
    (hGood : x ∈ Shao.OQ5.P51.projectionGood n g y) :
    |Shao.OQ5.P51.centeredDelta n g r x| ≤
      512 * (sigma * y / Real.sqrt (n : ℝ) +
        Shao.OQ5.P51.residualEnergyJ n r x /
          (sigma * y * Real.sqrt (n : ℝ))) := by
  let N : ℝ := (n : ℝ)
  let s : ℝ := Real.sqrt N
  let V : ℝ := Shao.OQ5.P51.projectionV n g x
  let W : ℝ := Shao.OQ5.P51.projectionW n g x
  let J : ℝ := Shao.OQ5.P51.residualEnergyJ n r x
  let C : ℝ := ∑ i : Fin n,
    (@Shao.OQ5.P35.center n (fun j : Fin n => g (x j)) i) *
      (@Shao.OQ5.P35.center n (Shao.OQ5.P51.residualU n r x) i)
  let E : ℝ := ∑ i : Fin n,
    (@Shao.OQ5.P35.center n (Shao.OQ5.P51.residualU n r x) i) ^ 2
  let t : ℝ := Real.sqrt J
  let Dden : ℝ := (N - 1) * V ^ 2
  let k : ℝ := sigma * y
  let A : ℝ := k / s
  let B : ℝ := J / (k * s)
  let R : ℝ := t / s
  have hN4 : (4 : ℝ) ≤ N := by
    dsimp only [N]
    exact_mod_cast hn
  have hNpos : 0 < N := by
    linarith only [hN4]
  have hNm1pos : 0 < N - 1 := by
    linarith only [hN4]
  have hs0 : 0 ≤ s := Real.sqrt_nonneg N
  have hspos : 0 < s := Real.sqrt_pos.2 hNpos
  have hsq : s ^ 2 = N := Real.sq_sqrt (le_of_lt hNpos)
  have hs2 : (2 : ℝ) ≤ s := by
    nlinarith only [hsq, hs0, hN4]
  have hsN : s ≤ N := by
    have hsOne : (1 : ℝ) ≤ s := by
      linarith only [hs2]
    have hsProduct : 1 * s ≤ s * s :=
      mul_le_mul_of_nonneg_right hsOne hs0
    nlinarith only [hsProduct, hsq]
  have hy0 : (0 : ℝ) ≤ y := by
    linarith only [hy]
  have hVpos : 0 < V := by
    simpa only [V] using (projectionGood_bounds n g x y hn hy hGood).1
  have hVhalf : (1 / 2 : ℝ) ≤ V := by
    simpa only [V] using (projectionGood_bounds n g x y hn hy hGood).2.1
  have hV2 : (1 / 2 : ℝ) ≤ V ^ 2 := by
    change (1 / 2 : ℝ) ≤ (projectionV n g x) ^ 2
    rw [projectionV_sq n g x]
    exact hGood.1
  have hWratio : W ^ 2 / V ^ 2 ≤ 81 * y * s := by
    simpa only [W, V, s, N] using
      (projectionGood_bounds n g x y hn hy hGood).2.2
  have hJ0 : 0 ≤ J := by
    dsimp only [J, residualEnergyJ]
    exact Finset.sum_nonneg (fun i _hi => sq_nonneg (residualU n r x i))
  have hE0 : 0 ≤ E := by
    dsimp only [E]
    exact Finset.sum_nonneg (fun i _hi => sq_nonneg
      (@Shao.OQ5.P35.center n (Shao.OQ5.P51.residualU n r x) i))
  have hEJ : E ≤ J := by
    simpa only [E, J] using (centered_geometry n g r x hn).2.1
  have hCabs : |C| ≤ s * V * t := by
    simpa only [C, s, N, V, t, J] using (centered_geometry n g r x hn).2.2
  have ht0 : 0 ≤ t := Real.sqrt_nonneg J
  have htsq : t ^ 2 = J := Real.sq_sqrt hJ0
  have hDpos : 0 < Dden := by
    exact mul_pos hNm1pos (lt_of_lt_of_le (by norm_num) hV2)
  have hidentity : Shao.OQ5.P51.centeredDelta n g r x =
      (V ^ 2 - W ^ 2 + 2 * C + E) / Dden := by
    simpa only [V, W, C, E, Dden, N] using
      (centered_denominator_identity n g r x hsym hn hVpos)
  have hNum : |V ^ 2 - W ^ 2 + 2 * C + E| ≤
      V ^ 2 + W ^ 2 + 2 * |C| + E := by
    apply abs_le.mpr
    constructor
    · nlinarith only [sq_nonneg V, hE0, neg_abs_le C]
    · nlinarith only [sq_nonneg W, le_abs_self C]
  have hBase : |Shao.OQ5.P51.centeredDelta n g r x| ≤
      (V ^ 2 + W ^ 2 + 2 * |C| + E) / Dden := by
    rw [hidentity]
    apply abs_le.mpr
    constructor
    · have hLower : -(V ^ 2 + W ^ 2 + 2 * |C| + E) / Dden ≤
          (V ^ 2 - W ^ 2 + 2 * C + E) / Dden :=
        div_le_div_of_nonneg_right (abs_le.mp hNum).1 (le_of_lt hDpos)
      simpa only [neg_div] using hLower
    · exact div_le_div_of_nonneg_right (abs_le.mp hNum).2 (le_of_lt hDpos)
  have hVterm : V ^ 2 / Dden ≤ 2 / N := by
    have hCancel : V ^ 2 / Dden = 1 / (N - 1) := by
      dsimp only [Dden]
      field_simp [ne_of_gt hVpos, ne_of_gt hNm1pos] <;> ring
    rw [hCancel]
    apply (div_le_div_iff₀ hNm1pos hNpos).2
    nlinarith only [hN4]
  have hWcoefficient : 81 * s / (N - 1) ≤ 128 / s := by
    apply (div_le_div_iff₀ hNm1pos hspos).2
    nlinarith only [hsq, hN4]
  have hWterm : W ^ 2 / Dden ≤ 128 * y / s := by
    calc
      W ^ 2 / Dden = (W ^ 2 / V ^ 2) / (N - 1) := by
        dsimp only [Dden]
        field_simp [ne_of_gt hVpos, ne_of_gt hNm1pos] <;> ring
      _ ≤ (81 * y * s) / (N - 1) :=
        div_le_div_of_nonneg_right hWratio (le_of_lt hNm1pos)
      _ = y * (81 * s / (N - 1)) := by ring
      _ ≤ y * (128 / s) :=
        mul_le_mul_of_nonneg_left hWcoefficient hy0
      _ = 128 * y / s := by ring
  have hCrossCoefficient : 2 * N ≤ 6 * (N - 1) * V := by
    have hLow : (N - 1) * (1 / 2 : ℝ) ≤ (N - 1) * V :=
      mul_le_mul_of_nonneg_left hVhalf (le_of_lt hNm1pos)
    nlinarith only [hLow, hN4]
  have hCterm : 2 * |C| / Dden ≤ 6 * R := by
    have hCrossProduct : (2 * N) * (V * t) ≤
        (6 * (N - 1) * V) * (V * t) :=
      mul_le_mul_of_nonneg_right hCrossCoefficient
        (mul_nonneg (le_of_lt hVpos) ht0)
    calc
      2 * |C| / Dden ≤ (2 * s * V * t) / Dden :=
        div_le_div_of_nonneg_right (by nlinarith only [hCabs]) (le_of_lt hDpos)
      _ ≤ (6 * t) / s := by
        apply (div_le_div_iff₀ hDpos hspos).2
        calc
          (2 * s * V * t) * s = (2 * N) * (V * t) := by
            calc
              (2 * s * V * t) * s = 2 * (s ^ 2) * (V * t) := by ring
              _ = (2 * N) * (V * t) := by rw [hsq]
          _ ≤ (6 * (N - 1) * V) * (V * t) := hCrossProduct
          _ = (6 * t) * Dden := by dsimp only [Dden]; ring
      _ = 6 * R := by dsimp only [R]; ring
  have hJcoefficient : N ≤ 4 * (N - 1) * V ^ 2 := by
    have hLow : (N - 1) * (1 / 2 : ℝ) ≤ (N - 1) * V ^ 2 :=
      mul_le_mul_of_nonneg_left hV2 (le_of_lt hNm1pos)
    nlinarith only [hLow, hN4]
  have hEterm : E / Dden ≤ 4 * J / N := by
    have hJProduct : J * N ≤ J * (4 * (N - 1) * V ^ 2) :=
      mul_le_mul_of_nonneg_left hJcoefficient hJ0
    calc
      E / Dden ≤ J / Dden :=
        div_le_div_of_nonneg_right hEJ (le_of_lt hDpos)
      _ ≤ (4 * J) / N := by
        apply (div_le_div_iff₀ hDpos hNpos).2
        calc
          J * N ≤ J * (4 * (N - 1) * V ^ 2) := hJProduct
          _ = (4 * J) * Dden := by dsimp only [Dden]; ring
  have hLoose : |Shao.OQ5.P51.centeredDelta n g r x| ≤
      2 / N + 128 * y / s + 6 * R + 4 * J / N := by
    calc
      |Shao.OQ5.P51.centeredDelta n g r x| ≤
          (V ^ 2 + W ^ 2 + 2 * |C| + E) / Dden := hBase
      _ = V ^ 2 / Dden + W ^ 2 / Dden +
          2 * |C| / Dden + E / Dden := by ring
      _ ≤ 2 / N + 128 * y / s + 6 * R + 4 * J / N := by
        linarith only [hVterm, hWterm, hCterm, hEterm]
  have hk1 : (1 : ℝ) ≤ k := by
    dsimp only [k]
    nlinarith only [mul_le_mul_of_nonneg_right hsigma hy0, hy]
  have hkpos : 0 < k := by
    linarith only [hk1]
  have hkWindow : k ≤ s := by
    simpa only [k, s, N] using hwindow
  have hApos : 0 < A := div_pos hkpos hspos
  have hA1 : A ≤ 1 := by
    dsimp only [A]
    apply (div_le_iff₀ hspos).2
    simpa only [one_mul] using hkWindow
  have hB0 : 0 ≤ B := div_nonneg hJ0 (le_of_lt (mul_pos hkpos hspos))
  have hR0 : 0 ≤ R := div_nonneg ht0 hs0
  have hAB : A * B = J / N := by
    calc
      A * B = J / s ^ 2 := by
        dsimp only [A, B]
        field_simp [ne_of_gt hkpos, ne_of_gt hspos] <;> ring
      _ = J / N := by rw [hsq]
  have hR2 : R ^ 2 = J / N := by
    dsimp only [R]
    rw [div_pow, htsq, hsq]
  have hYoungPolynomial : A * (A + B - 2 * R) = (A - R) ^ 2 := by
    nlinarith only [hAB, hR2]
  have hYoung : 2 * R ≤ A + B := by
    by_contra hNotYoung
    have hYoungNegative : A + B - 2 * R < 0 := by
      linarith only [lt_of_not_ge hNotYoung]
    have hYoungProductNegative : A * (A + B - 2 * R) < 0 :=
      mul_neg_of_pos_of_neg hApos hYoungNegative
    have hYoungNonnegative : 0 ≤ A * (A + B - 2 * R) := by
      rw [hYoungPolynomial]
      exact sq_nonneg (A - R)
    exact (not_lt_of_ge hYoungNonnegative) hYoungProductNegative
  have hJabsorb : J / N ≤ B := by
    calc
      J / N = A * B := hAB.symm
      _ ≤ 1 * B := mul_le_mul_of_nonneg_right hA1 hB0
      _ = B := one_mul B
  have hyAbsorb : y / s ≤ A := by
    change y / s ≤ (sigma * y) / s
    simpa only [one_mul] using
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsigma hy0) hs0)
  have hSmall : 2 / N ≤ 2 * A := by
    have hOne : (1 : ℝ) / N ≤ 1 / s :=
      div_le_div_of_nonneg_left (by norm_num) hspos hsN
    have hY : (1 : ℝ) / s ≤ y / s :=
      div_le_div_of_nonneg_right hy hs0
    calc
      2 / N = 2 * ((1 : ℝ) / N) := by ring
      _ ≤ 2 * A := mul_le_mul_of_nonneg_left
        (le_trans hOne (le_trans hY hyAbsorb)) (by norm_num)
  have h133 : |Shao.OQ5.P51.centeredDelta n g r x| ≤ 133 * A + 7 * B := by
    have hLooseLinear : |Shao.OQ5.P51.centeredDelta n g r x| ≤
        2 / N + 128 * (y / s) + 6 * R + 4 * (J / N) := by
      simpa only [mul_div_assoc] using hLoose
    linarith only [hLooseLinear, hSmall, hyAbsorb, hYoung, hJabsorb]
  have h512 : 133 * A + 7 * B ≤ 512 * (A + B) := by
    nlinarith only [le_of_lt hApos, hB0]
  simpa only [A, B, k, s, N, J] using (le_trans h133 h512)

end Shao.OQ5.P51
