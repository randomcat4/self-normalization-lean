import Shao.OQ3.ComplexWeightedMonomialRemainderBounds
import Mathlib.Data.Fin.VecNotation

namespace Shao.OQ3
open scoped BigOperators
noncomputable section

theorem complex_log_taylor_octic_correction_bound
    (A B C D E F G : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hE : 0 ≤ E) (hF : 0 ≤ F) (hG : 0 ≤ G) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ a b c d e f g : ℂ,
      ‖a‖ ≤ A * r ^ 2 → ‖b‖ ≤ B * r ^ 3 → ‖c‖ ≤ C * r ^ 4 →
      ‖d‖ ≤ D * r ^ 5 → ‖e‖ ≤ E * r ^ 6 → ‖f‖ ≤ F * r ^ 7 →
      ‖g‖ ≤ G * r ^ 8 →
      let P : ℂ := a + b + c + d + e + f + g
      let Q : ℂ := a + b + c + d + e + f + g -
        (a ^ 2 + 2 * a * b + 2 * a * c + b ^ 2 + 2 * a * d +
          2 * b * c + 2 * a * e + 2 * b * d + c ^ 2) / 2 +
        (a ^ 3 + 3 * a ^ 2 * b + 3 * a ^ 2 * c + 3 * a * b ^ 2) / 3 - a ^ 4 / 4
      ‖Complex.logTaylor 5 P - Q‖ ≤ K * r ^ 9 := by
  classical
  let weights : Fin 9 → ℕ := ![2, 3, 4, 5, 6, 7, 3, 4, 3]
  let bounds : Fin 9 → ℝ := ![A, B, C, D + E + F + G, E + F + G, F + G,
    B + C + D + E + F + G, C + D + E + F + G, 2 * B + (C + D + E + F + G)]
  let coeff : Fin 11 → ℂ := ![-1, -1, -1, -(1 : ℂ) / 2, 1, 1, (1 : ℂ) / 3,
    -1, -(3 : ℂ) / 2, -1, -(1 : ℂ) / 4]
  let powers : Fin 11 → Fin 9 → ℕ := ![
    ![1, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 1, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 2, 0, 0, 0, 0, 0],
    ![2, 0, 0, 1, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 3, 0, 0],
    ![3, 0, 0, 0, 0, 0, 1, 0, 0],
    ![2, 0, 0, 0, 0, 0, 2, 0, 0],
    ![1, 0, 0, 0, 0, 0, 3, 0, 0],
    ![0, 0, 0, 0, 0, 0, 4, 0, 0]]
  have hbounds (j : Fin 9) : 0 ≤ bounds j := by
    fin_cases j <;> simp [bounds] <;> positivity
  let K0 : ℝ := ∑ t : Fin 11, ‖coeff t‖ * ∏ j : Fin 9, bounds j ^ powers t j
  have hK0 : 0 ≤ K0 := by
    apply Finset.sum_nonneg
    intro t ht
    exact mul_nonneg (norm_nonneg _)
      (Finset.prod_nonneg (fun j hj => pow_nonneg (hbounds j) _))
  refine ⟨K0 + 1, by linarith, ?_⟩
  intro r hr0 hr1 a b c d e f g ha hb hc hd he hf hg P Q
  have hsum {m : ℕ} (zz : Fin m → ℂ) (ZZ : Fin m → ℝ) (ww : Fin m → ℕ)
      (s : ℕ) (hZZ : ∀ j, 0 ≤ ZZ j) (hzz : ∀ j, ‖zz j‖ ≤ ZZ j * r ^ ww j)
      (hww : ∀ j, s ≤ ww j) : ‖∑ j, zz j‖ ≤ (∑ j, ZZ j) * r ^ s := by
    calc
      _ ≤ ∑ j, ‖zz j‖ := norm_sum_le _ _
      _ ≤ ∑ j, ZZ j * r ^ s := by
        apply Finset.sum_le_sum
        intro j hj
        exact (hzz j).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one hr0 hr1 (hww j)) (hZZ j))
      _ = _ := (Finset.sum_mul _ _ _).symm
  have h5 : ‖d + e + f + g‖ ≤ (D + E + F + G) * r ^ 5 := by
    have hh := hsum ![d, e, f, g] ![D, E, F, G] ![5, 6, 7, 8] 5
      (by intro j; fin_cases j <;> simp <;> assumption)
      (by intro j; fin_cases j <;> simp <;> assumption)
      (by intro j; fin_cases j <;> norm_num)
    simpa [Fin.sum_univ_succ, add_assoc] using hh
  have h6 : ‖e + f + g‖ ≤ (E + F + G) * r ^ 6 := by
    have hh := hsum ![e, f, g] ![E, F, G] ![6, 7, 8] 6
      (by intro j; fin_cases j <;> simp <;> assumption)
      (by intro j; fin_cases j <;> simp <;> assumption)
      (by intro j; fin_cases j <;> norm_num)
    simpa [Fin.sum_univ_succ, add_assoc] using hh
  have h7 : ‖f + g‖ ≤ (F + G) * r ^ 7 := by
    have hh := hsum ![f, g] ![F, G] ![7, 8] 7
      (by intro j; fin_cases j <;> simp <;> assumption)
      (by intro j; fin_cases j <;> simp <;> assumption)
      (by intro j; fin_cases j <;> norm_num)
    simpa [Fin.sum_univ_succ, add_assoc] using hh
  have h3 : ‖b + c + d + e + f + g‖ ≤ (B + C + D + E + F + G) * r ^ 3 := by
    have hh := hsum ![b, c, d, e, f, g] ![B, C, D, E, F, G] ![3, 4, 5, 6, 7, 8] 3
      (by intro j; fin_cases j <;> simp <;> assumption)
      (by intro j; fin_cases j <;> simp <;> assumption)
      (by intro j; fin_cases j <;> norm_num)
    simpa [Fin.sum_univ_succ, add_assoc] using hh
  have h4 : ‖c + d + e + f + g‖ ≤ (C + D + E + F + G) * r ^ 4 := by
    have hh := hsum ![c, d, e, f, g] ![C, D, E, F, G] ![4, 5, 6, 7, 8] 4
      (by intro j; fin_cases j <;> simp <;> assumption)
      (by intro j; fin_cases j <;> simp <;> assumption)
      (by intro j; fin_cases j <;> norm_num)
    simpa [Fin.sum_univ_succ, add_assoc] using hh
  have ht : ‖2 * b + (c + d + e + f + g)‖ ≤
      (2 * B + (C + D + E + F + G)) * r ^ 3 := by
    calc
      _ ≤ ‖2 * b‖ + ‖c + d + e + f + g‖ := norm_add_le _ _
      _ = 2 * ‖b‖ + ‖c + d + e + f + g‖ := by norm_num [norm_mul]
      _ ≤ 2 * (B * r ^ 3) + (C + D + E + F + G) * r ^ 3 :=
        add_le_add (mul_le_mul_of_nonneg_left hb (by norm_num))
          (h4.trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one hr0 hr1 (by norm_num : 3 ≤ 4)) (by positivity)))
      _ = _ := by ring
  let z : Fin 9 → ℂ := ![a, b, c, d + e + f + g, e + f + g, f + g,
    b + c + d + e + f + g, c + d + e + f + g, 2 * b + (c + d + e + f + g)]
  have hz (j : Fin 9) : ‖z j‖ ≤ bounds j * r ^ weights j := by
    fin_cases j <;> simp [z, bounds, weights] <;> assumption
  have hdegree (t : Fin 11) : 9 ≤ ∑ j : Fin 9, weights j * powers t j := by
    fin_cases t <;> norm_num [weights, powers, Fin.sum_univ_succ]
  have hlog (z : ℂ) : Complex.logTaylor 5 z = z - z ^ 2 / 2 + z ^ 3 / 3 - z ^ 4 / 4 := by
    norm_num [Complex.logTaylor, Finset.sum_range_succ] <;> ring
  have heq : Complex.logTaylor 5 P - Q =
      ∑ t : Fin 11, coeff t * ∏ j : Fin 9, z j ^ powers t j := by
    rw [hlog]
    dsimp only [P, Q]
    norm_num [coeff, powers, z, Fin.sum_univ_succ, Fin.prod_univ_succ] <;> ring
  calc
    _ = ‖∑ t : Fin 11, coeff t * ∏ j : Fin 9, z j ^ powers t j‖ := congrArg norm heq
    _ ≤ K0 * r ^ 9 :=
      complex_weighted_polynomial_tail_bound z bounds weights coeff powers 9 r
        hr0 hr1 hbounds hz hdegree
    _ ≤ (K0 + 1) * r ^ 9 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end
end Shao.OQ3
