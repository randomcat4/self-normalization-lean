import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!+# Finite delayed recurrence

This is the frozen finite numerical step F-D from OQ4, source `b01/proof01.md`,
Section 8 (D2--D8).  It does not supply the probabilistic hypotheses of D2/D3,
the fixed-time initial limit B1, or the full killed-kernel theorem K/Kv.

The proof uses strong induction and never assumes a global bound on `g`.
-/

namespace Shao.OQ4

/-- Finite delayed recurrence, including all zero-parameter and short-horizon cases.
The hypotheses are precisely the frozen F-D numerical interface. -/
theorem delayed_recurrence_bound
    (f g : ℕ → ℝ) (m N : ℕ) (A B D C : ℝ)
    (hm : 1 ≤ m) (_hmN : m ≤ N)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (_hgnonneg : ∀ k, k ≤ N → 0 ≤ g k)
    (hinit : ∀ k, k ≤ N → k ≤ 2 * m → g k ≤ C)
    (hfm : f m ≤ C)
    (hincrement : ∀ k, m ≤ k → k < N → |f (k + 1) - f k| ≤ D * g (k - m))
    (hdelay : ∀ k, k + m ≤ N → g (k + m) ≤ A * f k + B * g k)
    (hsmall : A * D * (N : ℝ) + B ≤ (1 / 2 : ℝ)) :
    let M : ℝ := 2 * (1 + A) * C
    (∀ k, k ≤ N → g k ≤ M) ∧
      (∀ k, m ≤ k → k ≤ N → |f k - f m| ≤ D * ((k - m : ℕ) : ℝ) * M) := by
  let M : ℝ := 2 * (1 + A) * C
  change (∀ k, k ≤ N → g k ≤ M) ∧
    (∀ k, m ≤ k → k ≤ N → |f k - f m| ≤ D * ((k - m : ℕ) : ℝ) * M)
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hCM : C ≤ M := by
    dsimp [M]
    nlinarith [mul_nonneg hA hC]
  have hmain : ∀ k : ℕ, k ≤ N →
      g k ≤ M ∧ (m ≤ k → |f k - f m| ≤ D * ((k - m : ℕ) : ℝ) * M) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hkN
      constructor
      · by_cases hshort : k ≤ 2 * m
        · exact (hinit k hkN hshort).trans hCM
        · let j := k - m
          have hjk : j < k := by dsimp [j]; omega
          have hjN : j ≤ N := (Nat.le_of_lt hjk).trans hkN
          have hmj : m ≤ j := by dsimp [j]; omega
          have hjadd : j + m = k := by dsimp [j]; omega
          obtain ⟨hgj, hfj⟩ := ih j hjk hjN
          have hfjabs := hfj hmj
          have hlen : ((j - m : ℕ) : ℝ) ≤ (N : ℝ) := by
            exact_mod_cast (Nat.sub_le j m).trans hjN
          have hfjupper : f j ≤ C + D * (N : ℝ) * M := by
            calc
              f j = f m + (f j - f m) := by ring
              _ ≤ C + |f j - f m| := add_le_add hfm (le_abs_self _)
              _ ≤ C + D * ((j - m : ℕ) : ℝ) * M := add_le_add (le_refl C) hfjabs
              _ ≤ C + D * (N : ℝ) * M := by
                exact add_le_add (le_refl C)
                  (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlen hD) hM)
          have hrec : g k ≤ A * f j + B * g j := by
            simpa only [hjadd] using hdelay j (hjadd ▸ hkN)
          calc
            g k ≤ A * f j + B * g j := hrec
            _ ≤ A * (C + D * (N : ℝ) * M) + B * M :=
              add_le_add (mul_le_mul_of_nonneg_left hfjupper hA)
                (mul_le_mul_of_nonneg_left hgj hB)
            _ = A * C + (A * D * (N : ℝ) + B) * M := by ring
            _ ≤ A * C + (1 / 2 : ℝ) * M :=
              add_le_add (le_refl (A * C)) (mul_le_mul_of_nonneg_right hsmall hM)
            _ ≤ M := by dsimp [M]; nlinarith
      · intro hmk
        by_cases heq : k = m
        · subst k
          simp
        · let p := k - 1
          have hpk : p < k := by dsimp [p]; omega
          have hpN : p ≤ N := (Nat.le_of_lt hpk).trans hkN
          have hmp : m ≤ p := by dsimp [p]; omega
          have hpsucc : p + 1 = k := by dsimp [p]; omega
          have hpmk : p - m < k := lt_of_le_of_lt (Nat.sub_le p m) hpk
          obtain ⟨_, hfp⟩ := ih p hpk hpN
          have hgpm := (ih (p - m) hpmk ((Nat.le_of_lt hpmk).trans hkN)).1
          have hinc : |f k - f p| ≤ D * M := by
            have hi := hincrement p hmp (lt_of_lt_of_le hpk hkN)
            rw [hpsucc] at hi
            exact hi.trans (mul_le_mul_of_nonneg_left hgpm hD)
          have hlength : k - m = (p - m) + 1 := by omega
          calc
            |f k - f m| = |(f k - f p) + (f p - f m)| := by congr 1; ring
            _ ≤ |f k - f p| + |f p - f m| := abs_add_le _ _
            _ ≤ D * M + D * ((p - m : ℕ) : ℝ) * M := add_le_add hinc (hfp hmp)
            _ = D * ((k - m : ℕ) : ℝ) * M := by
              rw [hlength, Nat.cast_add, Nat.cast_one]
              ring
  exact ⟨fun k hkN => (hmain k hkN).1, fun k hmk hkN => (hmain k hkN).2 hmk⟩

end Shao.OQ4
