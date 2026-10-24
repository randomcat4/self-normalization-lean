import Shao.C2.BridgeHalfLineJointLaw

noncomputable section
namespace Shao.C2.FiniteWalkReflection

def boolStep (b : Bool) : ℤ := if b then 1 else -1

def walkPrefix {n : ℕ} (w : Fin n → Bool) : ℕ → ℤ
  | 0 => 0
  | k + 1 => walkPrefix w k + if hk : k < n then boolStep (w ⟨k, hk⟩) else 0

def reflectAfter {n : ℕ} (k : ℕ) (w : Fin n → Bool) : Fin n → Bool :=
  fun i => if k ≤ i.val then !(w i) else w i

def firstHit {n : ℕ} (h : ℤ) (w : Fin n → Bool) : ℕ :=
  if hex : ∃ k : ℕ, k ≤ n ∧ walkPrefix w k = h then Nat.find hex else n + 1

def reflectAtHit {n : ℕ} (h : ℤ) (w : Fin n → Bool) : Fin n → Bool :=
  reflectAfter (firstHit h w) w

theorem boolStep_not (b : Bool) : boolStep (!b) = -boolStep b := by
  cases b <;> simp [boolStep]

theorem walkPrefix_zero {n : ℕ} (w : Fin n → Bool) : walkPrefix w 0 = 0 := by
  rfl

theorem walkPrefix_step_le_one {n : ℕ} (w : Fin n → Bool) (k : ℕ) :
    walkPrefix w (k + 1) ≤ walkPrefix w k + 1 := by
  by_cases hk : k < n
  · cases hb : w ⟨k, hk⟩ <;> simp [walkPrefix, hk, boolStep, hb]
  · simp [walkPrefix, hk]

theorem walkPrefix_reaches_level {n : ℕ} (w : Fin n → Bool) (h : ℤ) (hh : 0 < h)
    (k : ℕ) (hk : k ≤ n) (hend : h ≤ walkPrefix w k) :
    ∃ j : ℕ, j ≤ k ∧ walkPrefix w j = h := by
  revert hk hend
  induction k with
  | zero =>
    intro hk hend
    simp only [walkPrefix] at hend
    omega
  | succ k ih =>
    intro hk hend
    by_cases hp : h ≤ walkPrefix w k
    · obtain ⟨j, hj, he⟩ := ih (by omega) hp
      exact ⟨j, by omega, he⟩
    · have hs := walkPrefix_step_le_one w k
      have he : walkPrefix w (k + 1) = h := by omega
      exact ⟨k + 1, le_rfl, he⟩

theorem reflectAfter_involutive {n : ℕ} (k : ℕ) :
    Function.Involutive (reflectAfter (n := n) k) := by
  intro w
  funext i
  by_cases hi : k ≤ i.val <;> simp [reflectAfter, hi]

theorem reflectAfter_eq_self_of_length_le {n : ℕ} (w : Fin n → Bool)
    (k : ℕ) (hk : n ≤ k) : reflectAfter k w = w := by
  funext i
  have hi : ¬k ≤ i.val := by omega
  simp only [reflectAfter, if_neg hi]

theorem walkPrefix_reflectAfter_of_le {n : ℕ} (w : Fin n → Bool)
    (k j : ℕ) (hj : j ≤ k) : walkPrefix (reflectAfter k w) j = walkPrefix w j := by
  revert hj
  induction j with
  | zero => intro hj; rfl
  | succ j ih =>
    intro hj
    have hp := ih (by omega : j ≤ k)
    simp only [walkPrefix, hp]
    by_cases hn : j < n
    · have hc : ¬k ≤ (⟨j, hn⟩ : Fin n).val := by change ¬k ≤ j; omega
      simp only [dif_pos hn, reflectAfter, if_neg hc]
    · simp only [dif_neg hn]

theorem walkPrefix_reflectAfter_of_ge {n : ℕ} (w : Fin n → Bool)
    (k j : ℕ) (hj : k ≤ j) :
    walkPrefix (reflectAfter k w) j = 2 * walkPrefix w k - walkPrefix w j := by
  induction j, hj using Nat.le_induction with
  | base =>
    rw [walkPrefix_reflectAfter_of_le w k k le_rfl]
    ring
  | succ j hkj ih =>
    simp only [walkPrefix, ih]
    by_cases hn : j < n
    · have hc : k ≤ (⟨j, hn⟩ : Fin n).val := hkj
      simp only [dif_pos hn, reflectAfter, if_pos hc, boolStep_not]
      ring
    · simp only [dif_neg hn, add_zero]

theorem firstHit_spec {n : ℕ} (h : ℤ) (w : Fin n → Bool)
    (hex : ∃ k : ℕ, k ≤ n ∧ walkPrefix w k = h) :
    firstHit h w ≤ n ∧ walkPrefix w (firstHit h w) = h := by
  unfold firstHit
  rw [dif_pos hex]
  exact Nat.find_spec hex

theorem firstHit_le_of_hit {n : ℕ} (h : ℤ) (w : Fin n → Bool)
    (j : ℕ) (hj : j ≤ n) (hreach : walkPrefix w j = h) : firstHit h w ≤ j := by
  have hex : ∃ k : ℕ, k ≤ n ∧ walkPrefix w k = h := ⟨j, hj, hreach⟩
  simp only [firstHit, dif_pos hex]
  exact Nat.find_min' hex ⟨hj, hreach⟩

theorem firstHit_min {n : ℕ} (h : ℤ) (w : Fin n → Bool)
    (hex : ∃ k : ℕ, k ≤ n ∧ walkPrefix w k = h)
    (j : ℕ) (hj : j < firstHit h w) : walkPrefix w j ≠ h := by
  intro heq
  have hs := firstHit_spec h w hex
  have hle := firstHit_le_of_hit h w j (by omega) heq
  omega

theorem firstHit_reflectAtHit {n : ℕ} (h : ℤ) (w : Fin n → Bool) :
    firstHit h (reflectAtHit h w) = firstHit h w := by
  by_cases hex : ∃ k : ℕ, k ≤ n ∧ walkPrefix w k = h
  · have hs := firstHit_spec h w hex
    have hh : walkPrefix (reflectAtHit h w) (firstHit h w) = h := by
      rw [reflectAtHit, walkPrefix_reflectAfter_of_le w (firstHit h w) (firstHit h w) le_rfl]
      exact hs.2
    have hr : ∃ k : ℕ, k ≤ n ∧ walkPrefix (reflectAtHit h w) k = h :=
      ⟨firstHit h w, hs.1, hh⟩
    have hle := firstHit_le_of_hit h (reflectAtHit h w) (firstHit h w) hs.1 hh
    apply le_antisymm hle
    by_contra hnot
    have hj : firstHit h (reflectAtHit h w) < firstHit h w := by omega
    have he : walkPrefix (reflectAtHit h w) (firstHit h (reflectAtHit h w)) =
        walkPrefix w (firstHit h (reflectAtHit h w)) := by
      exact walkPrefix_reflectAfter_of_le w (firstHit h w) _ (by omega)
    exact firstHit_min h w hex _ hj (he.symm.trans (firstHit_spec h (reflectAtHit h w) hr).2)
  · have hf : firstHit h w = n + 1 := by simp only [firstHit, dif_neg hex]
    have hr : reflectAtHit h w = w := by
      rw [reflectAtHit, hf]
      exact reflectAfter_eq_self_of_length_le w (n + 1) (Nat.le_succ n)
    rw [hr]

theorem reflectAtHit_involutive {n : ℕ} (h : ℤ) :
    Function.Involutive (reflectAtHit (n := n) h) := by
  intro w
  change reflectAfter (firstHit h (reflectAtHit h w)) (reflectAfter (firstHit h w) w) = w
  rw [firstHit_reflectAtHit]
  exact reflectAfter_involutive (firstHit h w) w

theorem reflectAtHit_endpoint {n : ℕ} (h : ℤ) (w : Fin n → Bool)
    (hex : ∃ k : ℕ, k ≤ n ∧ walkPrefix w k = h) :
    walkPrefix (reflectAtHit h w) n = 2 * h - walkPrefix w n := by
  have hs := firstHit_spec h w hex
  rw [reflectAtHit, walkPrefix_reflectAfter_of_ge w (firstHit h w) n hs.1, hs.2]

theorem reflectAtHit_bijective {n : ℕ} (h : ℤ) :
    Function.Bijective (reflectAtHit (n := n) h) := by
  exact (reflectAtHit_involutive h).bijective

end Shao.C2.FiniteWalkReflection
