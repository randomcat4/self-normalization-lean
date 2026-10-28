import Shao.OQ3.ActualCGFFirstWeightGaussianZero

namespace Shao.OQ3
open scoped BigOperators
noncomputable section

set_option maxHeartbeats 1000000 in
theorem six_order_word_higher_weight_decomposition (a : Fin 6 → ℂ) :
    (∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
      ∑ sigma : Fin q.val → Fin 6,
        if (∑ l, ((sigma l).val + 1)) ≤ 6 then ∏ l, a (sigma l) else 0) =
      1 + a 0 +
        (∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
          ∑ sigma : Fin q.val → Fin 6,
            if 2 ≤ (∑ l, ((sigma l).val + 1)) ∧
              (∑ l, ((sigma l).val + 1)) ≤ 6 then ∏ l, a (sigma l) else 0) := by
  classical
  have hzero : (∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
      ∑ sigma : Fin q.val → Fin 6,
        if (∑ l, ((sigma l).val + 1)) = 0 then ∏ l, a (sigma l) else 0) = 1 := by
    calc
      _ = (1 / ((0 : Fin 7).val.factorial : ℂ)) *
          ∑ sigma : Fin (0 : Fin 7).val → Fin 6,
            if (∑ l, ((sigma l).val + 1)) = 0 then ∏ l, a (sigma l) else 0 := by
        apply Finset.sum_eq_single (0 : Fin 7)
        · intro q hq hq0
          have hqv : q.val ≠ 0 := by
            intro h
            apply hq0
            exact Fin.ext h
          have hqpos : 1 ≤ q.val := by omega
          have hinner : (∑ sigma : Fin q.val → Fin 6,
              if (∑ l, ((sigma l).val + 1)) = 0 then ∏ l, a (sigma l) else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro sigma hsigma
            have hweight : q.val ≤ ∑ l : Fin q.val, ((sigma l).val + 1) := by
              calc
                q.val = ∑ _l : Fin q.val, 1 := by simp
                _ ≤ _ := Finset.sum_le_sum (by intro l hl; omega)
            have hne : (∑ l, ((sigma l).val + 1)) ≠ 0 := by omega
            rw [if_neg hne]
          rw [hinner, mul_zero]
        · intro h
          exact False.elim (h (Finset.mem_univ _))
      _ = 1 := by simp
  have hpart (q : Fin 7) (sigma : Fin q.val → Fin 6) :
      (if (∑ l, ((sigma l).val + 1)) ≤ 6 then ∏ l, a (sigma l) else 0) =
        (if (∑ l, ((sigma l).val + 1)) = 0 then ∏ l, a (sigma l) else 0) +
          (if (∑ l, ((sigma l).val + 1)) = 1 then ∏ l, a (sigma l) else 0) +
          (if 2 ≤ (∑ l, ((sigma l).val + 1)) ∧ (∑ l, ((sigma l).val + 1)) ≤ 6
            then ∏ l, a (sigma l) else 0) := by
    by_cases h0 : (∑ l, ((sigma l).val + 1)) = 0
    · simp [h0]
    by_cases h1 : (∑ l, ((sigma l).val + 1)) = 1
    · simp [h1]
    have h2 : 2 ≤ ∑ l, ((sigma l).val + 1) := by omega
    by_cases h6 : (∑ l, ((sigma l).val + 1)) ≤ 6 <;> simp [h0, h1, h2, h6]
  calc
    _ = (∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
          ∑ sigma : Fin q.val → Fin 6,
            if (∑ l, ((sigma l).val + 1)) = 0 then ∏ l, a (sigma l) else 0) +
        (∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
          ∑ sigma : Fin q.val → Fin 6,
            if (∑ l, ((sigma l).val + 1)) = 1 then ∏ l, a (sigma l) else 0) +
        (∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
          ∑ sigma : Fin q.val → Fin 6,
            if 2 ≤ (∑ l, ((sigma l).val + 1)) ∧ (∑ l, ((sigma l).val + 1)) ≤ 6
              then ∏ l, a (sigma l) else 0) := by
      simp_rw [hpart, Finset.sum_add_distrib, mul_add, Finset.sum_add_distrib]
    _ = _ := by rw [hzero, six_order_word_weight_one a]

end
end Shao.OQ3
