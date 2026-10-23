import Shao.OQ4.RademacherRealThresholdBridge
import Shao.OQ4.RademacherAdjacentLogFinite

/-!
Candidate sequence consumer of the explicitly frozen finite long-time bound.
Not elaborated or compiled. Both new imports require their independent gates;
this file is not an accepted theorem or a closure certificate.
The public type is the exact general116 sequence freeze3926e18b.
-/

open Filter
open scoped Topology

namespace Shao.OQ4.RademacherAdjacentLog

theorem adjacent_log_bound
    (nSeq kSeq : ℕ → ℕ)
    (hk : Tendsto kSeq atTop atTop)
    (hscale2 : Tendsto
      (fun j : ℕ => (nSeq j : ℝ) / (kSeq j : ℝ) ^ 2) atTop atTop)
    (hscale3 : ∃ M : ℝ, 0 < M ∧ ∃ J_M : ℕ,
      ∀ j : ℕ, J_M ≤ j → (nSeq j : ℝ) / (kSeq j : ℝ) ^ 3 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      2 ≤ kSeq j ∧
      1 ≤ nSeq j ∧
      0 < Shao.OQ4.RademacherRealThresholdBridge.weakProbability
        (nSeq j) (kSeq j : ℝ) ∧
      0 < Shao.OQ4.RademacherRealThresholdBridge.weakProbability
        (nSeq j) ((kSeq j : ℝ) - 1) ∧
      0 < Shao.OQ4.RademacherRealThresholdBridge.strictProbability
        (nSeq j) (kSeq j : ℝ) ∧
      Shao.OQ4.RademacherRealThresholdBridge.strictProbability
        (nSeq j) (kSeq j : ℝ) =
        Shao.OQ4.RademacherRealThresholdBridge.weakProbability
          (nSeq j) ((kSeq j : ℝ) - 1) ∧
      0 ≤ Real.log (Shao.OQ4.RademacherRealThresholdBridge.weakProbability
          (nSeq j) (kSeq j : ℝ)) -
        Real.log (Shao.OQ4.RademacherRealThresholdBridge.weakProbability
          (nSeq j) ((kSeq j : ℝ) - 1)) ∧
      Real.log (Shao.OQ4.RademacherRealThresholdBridge.weakProbability
          (nSeq j) (kSeq j : ℝ)) -
        Real.log (Shao.OQ4.RademacherRealThresholdBridge.weakProbability
          (nSeq j) ((kSeq j : ℝ) - 1)) ≤
        C * ((nSeq j : ℝ) / (kSeq j : ℝ) ^ 3) := by
  obtain ⟨C, hC, K, hK, T, hT, hfinite⟩ :=
    Shao.OQ4.RademacherAdjacentLogFinite.finite_adjacent_log_bound
  have hkTail : ∀ᶠ j : ℕ in atTop, K ≤ kSeq j :=
    (tendsto_atTop.1 hk) K
  have htimeTail : ∀ᶠ j : ℕ in atTop,
      4 * T ≤ (nSeq j : ℝ) / (kSeq j : ℝ) ^ 2 :=
    (tendsto_atTop.1 hscale2) (4 * T)
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hkTail.and htimeTail)
  refine ⟨C, hC, J, ?_⟩
  intro j hj
  obtain ⟨hkj, htj⟩ := hJ j hj
  have hk2 : 2 ≤ kSeq j := hK.trans hkj
  have hk2R : (2 : ℝ) ≤ (kSeq j : ℝ) := by exact_mod_cast hk2
  have hk0 : (0 : ℝ) < (kSeq j : ℝ) := by linarith
  have hkSq0 : (0 : ℝ) < (kSeq j : ℝ) ^ 2 := sq_pos_of_pos hk0
  have htime : (4 * T) * (kSeq j : ℝ) ^ 2 ≤ (nSeq j : ℝ) :=
    (le_div_iff₀ hkSq0).mp htj
  have hsq : ((kSeq j : ℝ) + 1) ^ 2 ≤ 4 * (kSeq j : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((kSeq j : ℝ) - 1)]
  have hT0 : (0 : ℝ) ≤ T := le_trans (by norm_num) hT
  have hdomain : T * ((kSeq j : ℝ) + 1) ^ 2 ≤ (nSeq j : ℝ) := by
    calc
      T * ((kSeq j : ℝ) + 1) ^ 2 ≤ T * (4 * (kSeq j : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hT0
      _ = (4 * T) * (kSeq j : ℝ) ^ 2 := by ring
      _ ≤ (nSeq j : ℝ) := htime
  have hn1R : (1 : ℝ) ≤ (nSeq j : ℝ) := by
    have hsq1 : (1 : ℝ) ≤ ((kSeq j : ℝ) + 1) ^ 2 := by
      nlinarith [sq_nonneg (kSeq j : ℝ)]
    have hsqT : ((kSeq j : ℝ) + 1) ^ 2 ≤
        T * ((kSeq j : ℝ) + 1) ^ 2 := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right hT (sq_nonneg ((kSeq j : ℝ) + 1)))
    exact hsq1.trans (hsqT.trans hdomain)
  have hn1 : 1 ≤ nSeq j := by exact_mod_cast hn1R
  obtain ⟨hpHigh, hpLow, hlogNonneg, hlogUpper⟩ :=
    hfinite (nSeq j) (kSeq j) hkj hdomain
  have hweak (t : ℝ) (ht : 0 ≤ t) :
      Shao.OQ4.RademacherRealThresholdBridge.weakProbability (nSeq j) t =
        Shao.OQ4.RademacherS2Assembly.p (nSeq j) t := by
    unfold Shao.OQ4.RademacherRealThresholdBridge.weakProbability
      Shao.OQ4.RademacherRealThresholdBridge.pathMeasure
      Shao.OQ4.RademacherS2Assembly.p
    rw [Shao.OQ4.RademacherRealThresholdBridge.weakEvent_eq_closedStrip
      (nSeq j) t ht]
  have hhigh := hweak (kSeq j : ℝ) (le_of_lt hk0)
  have hlow := hweak ((kSeq j : ℝ) - 1) (by linarith)
  have hstrict :=
    Shao.OQ4.RademacherRealThresholdBridge.strictProbability_eq_integer
      (nSeq j) (kSeq j) (by omega)
  refine ⟨hk2, hn1, ?_, ?_, ?_, hstrict, ?_, ?_⟩
  · simpa only [hhigh] using hpHigh
  · simpa only [hlow] using hpLow
  · simpa only [hstrict, hlow] using hpLow
  · simpa only [hhigh, hlow] using hlogNonneg
  · simpa only [hhigh, hlow] using hlogUpper

end Shao.OQ4.RademacherAdjacentLog
