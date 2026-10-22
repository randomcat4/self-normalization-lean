import Shao.OQ3.SummableAtoms

/-!
# Positive masses under adaptive future-tail budgets

Source: current/oq3/proofs/r1/report.md, lines 484-550.
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U11a scope: 1c4faf77bf27b05d6e9e7fd3b37242b5e68352a39f700d8fbc279fe21480fe9f.
-/

namespace Shao.OQ3

noncomputable section

private structure TailBudgetState (B : ℝ) (F : (J : ℕ) → (Fin J → ℝ) → ℝ) (J : ℕ) where
  past : Fin J → ℝ
  past_pos : ∀ i, 0 < past i
  cap : ℝ
  cap_pos : 0 < cap
  cap_le_budget : cap ≤ F J past / 2
  reserve : (∑ i, past i) + cap ≤ B

private def advanceTailBudget (eps B : ℝ) (hB : B < eps)
    (F : (J : ℕ) → (Fin J → ℝ) → ℝ)
    (hF : ∀ (J : ℕ) (past : Fin J → ℝ),
      (∀ i, 0 < past i) → (∑ i, past i) < eps → 0 < F J past)
    {J : ℕ} (s : TailBudgetState B F J) : TailBudgetState B F (J + 1) := by
  let past : Fin (J + 1) → ℝ := Fin.snoc s.past (s.cap / 2)
  have hp : ∀ i, 0 < past i := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa only [past, Fin.snoc_last] using div_pos s.cap_pos (by norm_num : (0 : ℝ) < 2)
    · simpa only [past, Fin.snoc_castSucc] using s.past_pos i
  have hsum : (∑ i, past i) = (∑ i, s.past i) + s.cap / 2 := by
    simp only [past, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  have hmass : (∑ i, past i) < eps := by
    rw [hsum]
    have hr := s.reserve
    have hc := s.cap_pos
    linarith
  have hf := hF (J + 1) past hp hmass
  let c := min (s.cap / 2) (F (J + 1) past / 2)
  exact {
    past := past
    past_pos := hp
    cap := c
    cap_pos := lt_min (div_pos s.cap_pos (by norm_num)) (div_pos hf (by norm_num))
    cap_le_budget := min_le_right _ _
    reserve := by
      have hc : c ≤ s.cap / 2 := min_le_left _ _
      rw [hsum]
      have hr := s.reserve
      linarith }

private def tailBudgetTrace (eps B : ℝ) (hB : B < eps)
    (F : (J : ℕ) → (Fin J → ℝ) → ℝ)
    (hF : ∀ (J : ℕ) (past : Fin J → ℝ),
      (∀ i, 0 < past i) → (∑ i, past i) < eps → 0 < F J past)
    (s0 : TailBudgetState B F 0) : (J : ℕ) → TailBudgetState B F J
  | 0 => s0
  | J + 1 => advanceTailBudget eps B hB F hF (tailBudgetTrace eps B hB F hF s0 J)

private theorem tailBudgetTrace_past (eps B : ℝ) (hB : B < eps)
    (F : (J : ℕ) → (Fin J → ℝ) → ℝ)
    (hF : ∀ (J : ℕ) (past : Fin J → ℝ),
      (∀ i, 0 < past i) → (∑ i, past i) < eps → 0 < F J past)
    (s0 : TailBudgetState B F 0) :
    ∀ (J : ℕ) (i : Fin J), (tailBudgetTrace eps B hB F hF s0 J).past i =
      (tailBudgetTrace eps B hB F hF s0 i.val).cap / 2 := by
  intro J
  induction J with
  | zero => intro i; exact Fin.elim0 i
  | succ J ih =>
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [tailBudgetTrace, advanceTailBudget, Fin.snoc_last, Fin.val_last]
    · simpa only [tailBudgetTrace, advanceTailBudget, Fin.snoc_castSucc, Fin.val_castSucc]
        using ih i

theorem exists_positive_mass_with_adaptive_tail_caps (eps : ℝ) (heps : 0 < eps)
    (F : (J : ℕ) → (Fin J → ℝ) → ℝ)
    (hF : ∀ (J : ℕ) (past : Fin J → ℝ),
      (∀ i, 0 < past i) → (∑ i, past i) < eps → 0 < F J past) :
  ∃ r : ℕ → ℝ, (∀ j, 0 < r j) ∧ Summable r ∧ (∑' j, r j) < eps ∧
    ∀ J : ℕ, (∑' k, r (J + k)) < F J (fun i : Fin J => r i.val) := by
  let past0 : Fin 0 → ℝ := Fin.elim0
  have hp0 : ∀ i, 0 < past0 i := fun i => Fin.elim0 i
  have hm0 : (∑ i, past0 i) < eps := by simpa using heps
  have hf0 := hF 0 past0 hp0 hm0
  let B := min (eps / 2) (F 0 past0 / 2)
  have hBpos : 0 < B := lt_min (div_pos heps (by norm_num)) (div_pos hf0 (by norm_num))
  have hB : B < eps := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let s0 : TailBudgetState B F 0 := {
    past := past0
    past_pos := hp0
    cap := B
    cap_pos := hBpos
    cap_le_budget := min_le_right _ _
    reserve := by simp }
  let tr : (J : ℕ) → TailBudgetState B F J := tailBudgetTrace eps B hB F hF s0
  let b : ℕ → ℝ := fun J => (tr J).cap
  let r : ℕ → ℝ := fun J => b J / 2
  have hr : ∀ J, 0 < r J := fun J => div_pos (tr J).cap_pos (by norm_num)
  have hstep (J : ℕ) : b (J + 1) ≤ b J / 2 := min_le_left _ _
  have hgeom (J k : ℕ) : b (J + k) ≤ b J * (1 / 2 : ℝ) ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hs := hstep (J + k)
      rw [Nat.add_assoc] at hs
      rw [pow_succ]
      nlinarith only [hs, ih]
  have hbound (J k : ℕ) : r (J + k) ≤ (b J / 2) * (1 / 2 : ℝ) ^ k := by
    have hg := hgeom J k
    dsimp only [r]
    linarith
  have hsgeom (J : ℕ) : Summable (fun k : ℕ => (b J / 2) * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_left _
  have hsr (J : ℕ) : Summable (fun k : ℕ => r (J + k)) :=
    Summable.of_nonneg_of_le (fun k => (hr (J + k)).le) (hbound J) (hsgeom J)
  have htail (J : ℕ) : (∑' k, r (J + k)) ≤ b J := by
    calc
      _ ≤ ∑' k : ℕ, (b J / 2) * (1 / 2 : ℝ) ^ k :=
        Summable.tsum_le_tsum (hbound J) (hsr J) (hsgeom J)
      _ = b J := by
        rw [tsum_mul_left, tsum_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)]
        ring
  have hpast (J : ℕ) : (tr J).past = fun i : Fin J => r i.val := by
    funext i
    exact tailBudgetTrace_past eps B hB F hF s0 J i
  have hmass : (∑' k, r k) < eps := by
    have hb0 : b 0 = B := rfl
    have ht : (∑' k, r k) ≤ B := by simpa only [Nat.zero_add, hb0] using htail 0
    exact ht.trans_lt hB
  refine ⟨r, hr, by simpa only [Nat.zero_add] using hsr 0, hmass, ?_⟩
  intro J
  have hb := (tr J).cap_pos
  have hc := (tr J).cap_le_budget
  rw [hpast J] at hc
  have hbudget : b J < F J (fun i : Fin J => r i.val) := by
    change b J ≤ F J (fun i : Fin J => r i.val) / 2 at hc
    change 0 < b J at hb
    linarith
  exact (htail J).trans_lt hbudget

theorem exists_positive_mass_with_adaptive_and_fixed_tail_caps (eps : ℝ) (heps : 0 < eps)
    (F : (J : ℕ) → (Fin J → ℝ) → ℝ)
    (hF : ∀ (J : ℕ) (past : Fin J → ℝ),
      (∀ i, 0 < past i) → (∑ i, past i) < eps → 0 < F J past)
    (a : ℕ → ℝ) (ha : ∀ J, 0 < a J) :
  ∃ r : ℕ → ℝ, (∀ j, 0 < r j) ∧ Summable r ∧ (∑' j, r j) < eps ∧
    ∀ J : ℕ, (∑' k, r (J + k)) < F J (fun i : Fin J => r i.val) ∧
      (∑' k, r (J + k)) < a J := by
  obtain ⟨r, hr, hs, hm, ht⟩ := exists_positive_mass_with_adaptive_tail_caps eps heps
    (fun J past => min (F J past) (a J))
    (by intro J past hp hm; exact lt_min (hF J past hp hm) (ha J))
  refine ⟨r, hr, hs, hm, ?_⟩
  intro J
  exact ⟨(ht J).trans_le (min_le_left _ _), (ht J).trans_le (min_le_right _ _)⟩

theorem exists_witness_first_positive_mass_with_tail_caps (eps : ℝ) (heps : 0 < eps)
    (W : (J : ℕ) → (Fin J → ℝ) → ℕ → Prop)
    (hW : ∀ (J : ℕ) (past : Fin J → ℝ),
      (∀ i, 0 < past i) → (∑ i, past i) < eps → ∃ n : ℕ, W J past n)
    (cap : (J : ℕ) → (Fin J → ℝ) → ℕ → ℝ)
    (hcap : ∀ (J : ℕ) (past : Fin J → ℝ),
      (∀ i, 0 < past i) → (∑ i, past i) < eps →
      ∀ n : ℕ, W J past n → 0 < cap J past n) :
  ∃ chooseN : (J : ℕ) → (Fin J → ℝ) → ℕ,
    (∀ (J : ℕ) (past : Fin J → ℝ),
      (∀ i, 0 < past i) → (∑ i, past i) < eps → W J past (chooseN J past)) ∧
    ∃ r : ℕ → ℝ, (∀ j, 0 < r j) ∧ Summable r ∧ (∑' j, r j) < eps ∧
      ∀ J : ℕ, (∑' k, r (J + k)) <
        cap J (fun i : Fin J => r i.val) (chooseN J (fun i : Fin J => r i.val)) := by
  classical
  let chooseN : (J : ℕ) → (Fin J → ℝ) → ℕ := fun J past =>
    if h : (∀ i, 0 < past i) ∧ (∑ i, past i) < eps then
      Classical.choose (hW J past h.1 h.2) else 0
  have hn : ∀ (J : ℕ) (past : Fin J → ℝ),
      (∀ i, 0 < past i) → (∑ i, past i) < eps → W J past (chooseN J past) := by
    intro J past hp hm
    dsimp only [chooseN]
    split_ifs with h
    · exact Classical.choose_spec (hW J past h.1 h.2)
    · exact False.elim (h ⟨hp, hm⟩)
  refine ⟨chooseN, hn, ?_⟩
  exact exists_positive_mass_with_adaptive_tail_caps eps heps
    (fun J past => cap J past (chooseN J past))
    (by intro J past hp hm; exact hcap J past hp hm _ (hn J past hp hm))

end
end Shao.OQ3
