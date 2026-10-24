import Shao.C2.CompletedIntervalProcess
import Shao.C1.PermutationEnergyEnvelope

noncomputable section
namespace Shao.C2.CompletedIntervalEnergy
open Shao.C2.CompletedIntervalProcess Shao.C2.SourceIntervalCompletion
open Shao.C2.BridgeDomination

theorem raw_remaining_bounds (n : ℕ) (z : Shao.Path n) (σ : Equiv.Perm (Fin n)) (r : Fin n) :
    0 ≤ Shao.energy z - Shao.prefixSquares (fun i => z (σ i)) r.val ∧
      (Shao.prefixSum z n - Shao.prefixSum (fun i => z (σ i)) r.val) ^ 2 ≤
        (n - r.val : ℕ) * (Shao.energy z - Shao.prefixSquares (fun i => z (σ i)) r.val) := by
  have hb := Shao.C1.PermutationEnergyEnvelope.remaining_energy_bounds z σ r
  constructor
  · exact (sq_nonneg (z (σ r))).trans hb.1
  · rw [Shao.prefixSum_length]
    exact hb.2

theorem raw_remaining_nonnegative (n : ℕ) (z : Shao.Path n) (σ : Equiv.Perm (Fin n))
    (k : ℕ) (hk : k ≤ n) :
    0 ≤ Shao.energy z - Shao.prefixSquares (fun i => z (σ i)) k := by
  by_cases hkn : k < n
  · exact (raw_remaining_bounds n z σ ⟨k, hkn⟩).1
  · have hke : k = n := le_antisymm hk (le_of_not_gt hkn)
    subst k
    have hq : Shao.prefixSquares (fun i => z (σ i)) n = Shao.energy z := by
      rw [Shao.prefixSquares_length]
      exact Equiv.sum_comp σ (fun i => (z i) ^ 2)
    rw [hq, sub_self]

theorem raw_zero_remaining_reachable (n : ℕ) (z : Shao.Path n) (σ : Equiv.Perm (Fin n))
    (k : ℕ) (hk : k ≤ n)
    (hT : Shao.energy z - Shao.prefixSquares (fun i => z (σ i)) k = 0) :
    Shao.prefixSum (fun i => z (σ i)) k = Shao.prefixSum z n := by
  by_cases hkn : k < n
  · have hb := (raw_remaining_bounds n z σ ⟨k, hkn⟩).2
    rw [hT, mul_zero] at hb
    nlinarith [sq_nonneg (Shao.prefixSum z n - Shao.prefixSum (fun i => z (σ i)) k)]
  · have hke : k = n := le_antisymm hk (le_of_not_gt hkn)
    subst k
    simp only [Shao.prefixSum_length]
    exact Equiv.sum_comp σ z

open scoped Classical in
theorem completedValue_zero_remaining (n : ℕ) (ν : MeasureTheory.Measure BridgeNoise)
    (x : ℝ) (z : Shao.Path n) (σ : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n)
    (hT : Shao.energy z - Shao.prefixSquares (fun i => z (σ i)) k = 0) :
    completedValue ν x z σ k = if 0 < Shao.energy z ∧ strictLive x z σ k then 1 else 0 := by
  have hs := raw_zero_remaining_reachable n z σ k hk hT
  by_cases hA : 0 < Shao.energy z ∧ strictLive x z σ k
  · have he : |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z) := by
      simpa only [hs] using hA.2 k le_rfl
    rw [if_pos hA, completedValue, if_pos ⟨hA.1, hA.2, he⟩, hT, hs,
      sourceIntervalCompletion_reachable_zero, if_pos he]
  · have hguard : ¬ (0 < Shao.energy z ∧ strictLive x z σ k ∧
        |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z)) := fun h => hA ⟨h.1, h.2.1⟩
    rw [completedValue, if_neg hguard, if_neg hA]

end Shao.C2.CompletedIntervalEnergy
