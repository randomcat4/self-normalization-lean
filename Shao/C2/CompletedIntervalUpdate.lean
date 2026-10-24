import Shao.C2.CompletedIntervalTelescope

noncomputable section
namespace Shao.C2.CompletedIntervalUpdate
open MeasureTheory
open Shao.C2.BridgeDomination Shao.C2.SourceIntervalCompletion
open Shao.C2.CompletedIntervalProcess Shao.C2.CompletedIntervalDerivative
open Shao.C1.PermutationEnergyEnvelope Shao.C1.GuardedPermutationIntegrability

def rawStepRemainder (ν : Measure BridgeNoise) (x : ℝ) {n : ℕ} (z : Shao.Path n)
    (σ : Equiv.Perm (Fin n)) (r : Fin n) : ℝ :=
  let a := x * Real.sqrt (Shao.energy z)
  let y := Shao.prefixSum (fun i => z (σ i)) r.val
  let T := revealRemainingEnergy z σ r
  let d := revealRemainingSum z σ r
  let endpoint := Shao.prefixSum z n
  let b := z (σ r)
  sourceIntervalCompletion ν a (y + b) (T - b ^ 2) endpoint -
    intervalCompletion ν a y T endpoint -
      (b - b ^ 2 * d / T) * spatialDerivative ν a y T endpoint

theorem revealed_prefix_sum_step (n : ℕ) (z : Shao.Path n)
    (σ : Equiv.Perm (Fin n)) (r : Fin n) :
    Shao.prefixSum (fun i => z (σ i)) (r.val + 1) =
      Shao.prefixSum (fun i => z (σ i)) r.val + z (σ r) := by
  have hf : Finset.univ.filter (fun i : Fin n => i.val < r.val + 1) =
      insert r (Finset.univ.filter (fun i : Fin n => i.val < r.val)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp h) with hi | hi
      · exact Or.inr hi
      · exact Or.inl (Fin.ext hi)
    · rintro (h | h)
      · subst i
        exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt h
  unfold Shao.prefixSum
  rw [hf, Finset.sum_insert]
  · exact add_comm _ _
  · simp

theorem revealed_prefix_squares_step (n : ℕ) (z : Shao.Path n)
    (σ : Equiv.Perm (Fin n)) (r : Fin n) :
    Shao.prefixSquares (fun i => z (σ i)) (r.val + 1) =
      Shao.prefixSquares (fun i => z (σ i)) r.val + (z (σ r)) ^ 2 := by
  have hf : Finset.univ.filter (fun i : Fin n => i.val < r.val + 1) =
      insert r (Finset.univ.filter (fun i : Fin n => i.val < r.val)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp h) with hi | hi
      · exact Or.inr hi
      · exact Or.inl (Fin.ext hi)
    · rintro (h | h)
      · subst i
        exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt h
  unfold Shao.prefixSquares
  rw [hf, Finset.sum_insert]
  · exact add_comm _ _
  · simp

theorem strictLive_step (n : ℕ) (x : ℝ) (z : Shao.Path n)
    (σ : Equiv.Perm (Fin n)) (r : Fin n) :
    strictLive x z σ (r.val + 1) ↔ strictLive x z σ r.val ∧
      |Shao.prefixSum (fun i => z (σ i)) r.val + z (σ r)| < x * Real.sqrt (Shao.energy z) := by
  constructor
  · intro h
    exact ⟨fun j hj => h j (hj.trans (Nat.le_succ _)), by
      simpa only [revealed_prefix_sum_step n z σ r] using h (r.val + 1) le_rfl⟩
  · rintro ⟨hLive, hNew⟩ j hj
    by_cases hjr : j ≤ r.val
    · exact hLive j hjr
    · have hjEq : j = r.val + 1 := le_antisymm hj (Nat.succ_le_of_lt (lt_of_not_ge hjr))
      subst j
      simpa only [revealed_prefix_sum_step n z σ r] using hNew

theorem completedValue_after_live_reveal (n : ℕ) (ν : Measure BridgeNoise)
    (x : ℝ) (z : Shao.Path n) (σ : Equiv.Perm (Fin n)) (r : Fin n)
    (hQ : 0 < Shao.energy z) (hLive : strictLive x z σ r.val)
    (hEnd : |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z)) :
    completedValue ν x z σ (r.val + 1) =
      sourceIntervalCompletion ν (x * Real.sqrt (Shao.energy z))
        (Shao.prefixSum (fun i => z (σ i)) r.val + z (σ r))
        (revealRemainingEnergy z σ r - (z (σ r)) ^ 2) (Shao.prefixSum z n) := by
  have hΔT : Shao.energy z - Shao.prefixSquares (fun i => z (σ i)) (r.val + 1) =
      revealRemainingEnergy z σ r - (z (σ r)) ^ 2 := by
    rw [revealed_prefix_squares_step]
    change Shao.energy z - (Shao.prefixSquares (fun i => z (σ i)) r.val + (z (σ r)) ^ 2) =
      (Shao.energy z - Shao.prefixSquares (fun i => z (σ i)) r.val) - (z (σ r)) ^ 2
    ring
  by_cases hNew : |Shao.prefixSum (fun i => z (σ i)) r.val + z (σ r)| <
      x * Real.sqrt (Shao.energy z)
  · have hl := (strictLive_step n x z σ r).2 ⟨hLive, hNew⟩
    rw [completedValue, if_pos ⟨hQ, hl, hEnd⟩, revealed_prefix_sum_step, hΔT]
  · have hl : ¬ strictLive x z σ (r.val + 1) :=
      fun h => hNew ((strictLive_step n x z σ r).1 h).2
    rw [completedValue_dead n ν x z σ (r.val + 1) hl]
    exact (sourceIntervalCompletion_exterior ν _ _ _ _ (fun h => hNew h.1)).symm

theorem completedValue_current_live (n : ℕ) (ν : Measure BridgeNoise)
    (x : ℝ) (z : Shao.Path n) (σ : Equiv.Perm (Fin n)) (r : Fin n)
    (hQ : 0 < Shao.energy z) (hLive : strictLive x z σ r.val)
    (hEnd : |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z))
    (hT : 0 < revealRemainingEnergy z σ r) :
    completedValue ν x z σ r.val =
      intervalCompletion ν (x * Real.sqrt (Shao.energy z))
        (Shao.prefixSum (fun i => z (σ i)) r.val)
        (revealRemainingEnergy z σ r) (Shao.prefixSum z n) := by
  rw [completedValue, if_pos ⟨hQ, hLive, hEnd⟩]
  change sourceIntervalCompletion ν (x * Real.sqrt (Shao.energy z))
    (Shao.prefixSum (fun i => z (σ i)) r.val) (revealRemainingEnergy z σ r) (Shao.prefixSum z n) = _
  exact sourceIntervalCompletion_pos ν _ _ _ _ hT

open scoped Classical in
theorem guarded_remainder_eq_live_rawStep (n : ℕ) (ν : Measure BridgeNoise)
    (x : ℝ) (z : Shao.Path n) (σ : Equiv.Perm (Fin n)) (r : Fin n)
    (H : ℝ) (hH : 0 < H) (hGuard : H ≤ revealRemainingEnergy z σ r) :
    guardedRemainder σ r H (fun a => completedDerivative ν x a σ r)
      (fun a => completedValue ν x a σ (r.val + 1))
      (fun a => completedValue ν x a σ r.val) z =
      if 0 < Shao.energy z ∧ strictLive x z σ r.val ∧
          |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z) then
        rawStepRemainder ν x z σ r else 0 := by
  have hT : 0 < revealRemainingEnergy z σ r := hH.trans_le hGuard
  unfold guardedRemainder
  rw [if_pos hGuard]
  dsimp only
  by_cases hActive : 0 < Shao.energy z ∧ strictLive x z σ r.val ∧
      |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z)
  · rw [if_pos hActive,
      completedValue_after_live_reveal n ν x z σ r hActive.1 hActive.2.1 hActive.2.2,
      completedValue_current_live n ν x z σ r hActive.1 hActive.2.1 hActive.2.2 hT,
      completedDerivative_live n ν x z σ r hActive.1 hActive.2.1 hActive.2.2 hT]
    rfl
  · have hNextInactive : ¬ (0 < Shao.energy z ∧ strictLive x z σ (r.val + 1) ∧
        |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z)) := by
      intro h
      exact hActive ⟨h.1, fun j hj => h.2.1 j (hj.trans (Nat.le_succ _)), h.2.2⟩
    have hn : completedValue ν x z σ (r.val + 1) = 0 := by
      unfold completedValue
      exact if_neg hNextInactive
    have hc : completedValue ν x z σ r.val = 0 := by
      unfold completedValue
      exact if_neg hActive
    rw [if_neg hActive, hn, hc, completedDerivative_inactive n ν x z σ r hActive]
    simp

end Shao.C2.CompletedIntervalUpdate
