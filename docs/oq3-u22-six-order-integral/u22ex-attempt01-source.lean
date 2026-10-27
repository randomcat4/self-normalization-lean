import Shao.OQ3.ComplexSixOrderFilteredPolynomial

namespace Shao.OQ3
open scoped BigOperators
noncomputable section

set_option maxHeartbeats 2000000 in
theorem complex_six_letter_cutoff_word_recurrence (a : Fin 6 → ℂ) :
    let W : ℕ → ℕ → ℂ := fun q d =>
      ∑ sigma : Fin q → Fin 6,
        if (∑ i, ((sigma i).val + 1)) ≤ d then ∏ i, a (sigma i) else 0
    (∀ d, W 0 d = 1) ∧
      ∀ q d, W (q + 1) d =
        ∑ j : Fin 6, if j.val + 1 ≤ d then
          a j * W q (d - (j.val + 1)) else 0 := by
  classical
  intro W
  refine ⟨?_, ?_⟩
  · intro d
    simp [W]
  · intro q d
    let e : (Fin (q + 1) → Fin 6) ≃ Fin 6 × (Fin q → Fin 6) :=
      { toFun := fun sigma => (sigma 0, fun i => sigma i.succ)
        invFun := fun p => Fin.cons p.1 p.2
        left_inv := by
          intro sigma
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> rfl
        right_inv := by
          intro p
          rcases p with ⟨j, sigma⟩
          rfl }
    have hsplit : W (q + 1) d =
        ∑ j : Fin 6, ∑ sigma : Fin q → Fin 6,
          if j.val + 1 + (∑ i, ((sigma i).val + 1)) ≤ d then
            a j * ∏ i, a (sigma i) else 0 := by
      dsimp only [W]
      calc
        _ = ∑ p : Fin 6 × (Fin q → Fin 6),
            if p.1.val + 1 + (∑ i, ((p.2 i).val + 1)) ≤ d then
              a p.1 * ∏ i, a (p.2 i) else 0 := by
          apply Fintype.sum_equiv e
          intro sigma
          simp only [e, Fin.sum_univ_succ, Fin.prod_univ_succ]
        _ = _ := Fintype.sum_prod_type _
    rw [hsplit]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : j.val + 1 ≤ d
    · rw [if_pos h]
      dsimp only [W]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro sigma hsigma
      have he : j.val + 1 + (∑ i, ((sigma i).val + 1)) ≤ d ↔
          (∑ i, ((sigma i).val + 1)) ≤ d - (j.val + 1) := by omega
      simp only [he, mul_ite, mul_zero]
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro sigma hsigma
      have he : ¬j.val + 1 + (∑ i, ((sigma i).val + 1)) ≤ d := by omega
      simp only [if_neg he]

set_option maxHeartbeats 2000000 in
theorem complex_six_order_weighted_polynomial_coefficients
    (A : Fin 6 → ℂ) (t : ℂ) :
    let a : Fin 6 → ℂ := fun j => A j * t ^ (j.val + 1)
    let P : (Fin 6 → ℂ) → ℂ := fun b =>
      ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
        ∑ sigma : Fin q.val → Fin 6,
          if (∑ i, ((sigma i).val + 1)) ≤ 6 then ∏ i, b (sigma i) else 0
    let B1 := A 0
    let B2 := A 1 + A 0 ^ 2 / 2
    let B3 := A 2 + A 0 * A 1 + A 0 ^ 3 / 6
    let B4 := A 3 + A 0 * A 2 + A 1 ^ 2 / 2 +
      A 0 ^ 2 * A 1 / 2 + A 0 ^ 4 / 24
    let B5 := A 4 + A 0 * A 3 + A 1 * A 2 +
      A 0 ^ 2 * A 2 / 2 + A 0 * A 1 ^ 2 / 2 +
      A 0 ^ 3 * A 1 / 6 + A 0 ^ 5 / 120
    let B6 := A 5 + A 0 * A 4 + A 1 * A 3 + A 2 ^ 2 / 2 +
      A 0 ^ 2 * A 3 / 2 + A 0 * A 1 * A 2 + A 1 ^ 3 / 6 +
      A 0 ^ 3 * A 2 / 6 + A 0 ^ 2 * A 1 ^ 2 / 4 +
      A 0 ^ 4 * A 1 / 24 + A 0 ^ 6 / 720
    P a = 1 + B1 * t + B2 * t ^ 2 + B3 * t ^ 3 +
      B4 * t ^ 4 + B5 * t ^ 5 + B6 * t ^ 6 := by
  classical
  intro a P B1 B2 B3 B4 B5 B6
  let W : ℕ → ℕ → ℂ := fun q d =>
    ∑ sigma : Fin q → Fin 6,
      if (∑ i, ((sigma i).val + 1)) ≤ d then ∏ i, a (sigma i) else 0
  have hzero : ∀ d, W 0 d = 1 := (complex_six_letter_cutoff_word_recurrence a).1
  have hstep : ∀ q d, W (q + 1) d =
      ∑ j : Fin 6, if j.val + 1 ≤ d then
        a j * W q (d - (j.val + 1)) else 0 :=
    (complex_six_letter_cutoff_word_recurrence a).2
  change (∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) * W q.val 6) = _
  norm_num [Fin.sum_univ_succ, hstep, hzero, a, B1, B2, B3, B4, B5, B6]
  <;> ring

end
end Shao.OQ3
