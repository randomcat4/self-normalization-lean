import Shao.C2.SourceIntervalCompletion
import Shao.C2.RawInitialCompletion
import Shao.C1.PermutationCompensation

noncomputable section
namespace Shao.C2.CompletedIntervalProcess
open MeasureTheory Set
open Shao.C2.BridgeDomination Shao.C2.SourceIntervalCompletion

def strictLive {n : ℕ} (x : ℝ) (z : Shao.Path n) (σ : Equiv.Perm (Fin n)) (k : ℕ) : Prop :=
  ∀ j : ℕ, j ≤ k →
    |Shao.prefixSum (fun i => z (σ i)) j| < x * Real.sqrt (Shao.energy z)

def completedValue (ν : Measure BridgeNoise) (x : ℝ) {n : ℕ} (z : Shao.Path n)
    (σ : Equiv.Perm (Fin n)) (k : ℕ) : ℝ := by
  classical
  exact if 0 < Shao.energy z ∧ strictLive x z σ k ∧
      |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z) then
    sourceIntervalCompletion ν (x * Real.sqrt (Shao.energy z))
      (Shao.prefixSum (fun i => z (σ i)) k)
      (Shao.energy z - Shao.prefixSquares (fun i => z (σ i)) k)
      (Shao.prefixSum z n)
  else 0

theorem measurableSet_strictLive (n : ℕ) (x : ℝ) (σ : Equiv.Perm (Fin n)) (k : ℕ) :
    MeasurableSet {z : Shao.Path n | strictLive x z σ k} := by
  have hσ : Measurable (fun z : Shao.Path n => fun i => z (σ i)) :=
    Measurable.of_eval (fun i => measurable_pi_apply (σ i))
  have hm : MeasurableSet (⋂ j : ℕ, ⋂ (_ : j ≤ k),
    {z : Shao.Path n | |Shao.prefixSum (fun i => z (σ i)) j| <
      x * Real.sqrt (Shao.energy z)}) :=
    MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_lt (continuous_abs.measurable.comp ((Shao.measurable_prefixSum j).comp hσ))
      (Shao.measurable_energyWall x)
  simpa only [strictLive, Set.setOf_forall] using hm

set_option maxHeartbeats 1500000 in
theorem measurable_completedValue (n : ℕ) (ν : Measure BridgeNoise) [SFinite ν]
    (x : ℝ) (σ : Equiv.Perm (Fin n)) (k : ℕ) :
    Measurable (fun z : Shao.Path n => completedValue ν x z σ k) := by
  have hσ : Measurable (fun z : Shao.Path n => fun i => z (σ i)) :=
    Measurable.of_eval (fun i => measurable_pi_apply (σ i))
  have hy := (Shao.measurable_prefixSum k).comp hσ
  have hT := Shao.measurable_energy.sub ((Shao.measurable_prefixSquares k).comp hσ)
  have hz := Shao.measurable_prefixSum (n := n) n
  have hp : Measurable (fun z : Shao.Path n =>
      ((x * Real.sqrt (Shao.energy z),
        (Shao.prefixSum (fun i => z (σ i)) k,
          (Shao.energy z - Shao.prefixSquares (fun i => z (σ i)) k, Shao.prefixSum z n))) :
        CompletionMeasurability.CompletionParameters)) :=
    (Shao.measurable_energyWall x).prodMk (hy.prodMk (hT.prodMk hz))
  unfold completedValue
  exact Measurable.ite
    ((measurableSet_lt measurable_const Shao.measurable_energy).inter
      ((measurableSet_strictLive n x σ k).inter
        (measurableSet_lt (continuous_abs.measurable.comp hz) (Shao.measurable_energyWall x))))
    ((measurable_sourceIntervalCompletion_parameters ν).comp hp) measurable_const

theorem completedValue_bounds (n : ℕ) (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (x : ℝ) (z : Shao.Path n) (σ : Equiv.Perm (Fin n)) (k : ℕ) :
    0 ≤ completedValue ν x z σ k ∧ completedValue ν x z σ k ≤ 1 := by
  unfold completedValue
  split_ifs
  · exact sourceIntervalCompletion_bounds ν _ _ _ _
  · exact ⟨le_rfl, zero_le_one⟩

theorem integrable_completedValue (n : ℕ) (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (P : Measure (Shao.Path n)) [IsProbabilityMeasure P]
    (x : ℝ) (σ : Equiv.Perm (Fin n)) (k : ℕ) :
    Integrable (fun z => completedValue ν x z σ k) P := by
  refine (integrable_const (1 : ℝ)).mono'
    (measurable_completedValue n ν x σ k).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (completedValue_bounds n ν x z σ k).1]
    exact (completedValue_bounds n ν x z σ k).2

theorem completedValue_initial (n : ℕ) (ν : Measure BridgeNoise)
    (x : ℝ) (hx : 0 < x) (z : Shao.Path n) (σ : Equiv.Perm (Fin n)) :
    completedValue ν x z σ 0 = RawInitialCompletion.rawInitial ν x z := by
  by_cases hQ : 0 < Shao.energy z
  · have hw : 0 < x * Real.sqrt (Shao.energy z) := mul_pos hx (Real.sqrt_pos.mpr hQ)
    have hl : strictLive x z σ 0 := by
      intro j hj
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
      subst j
      simpa only [Shao.prefixSum_zero, abs_zero] using hw
    by_cases he : |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z)
    · rw [completedValue, if_pos ⟨hQ, hl, he⟩,
        RawInitialCompletion.rawInitial, if_pos hQ]
      simp only [Shao.prefixSum_zero, Shao.prefixSquares_zero, sub_zero]
      exact sourceIntervalCompletion_pos ν _ _ _ _ hQ
    · have hguard : ¬ (0 < Shao.energy z ∧ strictLive x z σ 0 ∧
          |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z)) := fun h => he h.2.2
      rw [completedValue, if_neg hguard, RawInitialCompletion.rawInitial, if_pos hQ]
      have hext := sourceIntervalCompletion_exterior ν
        (x * Real.sqrt (Shao.energy z)) 0 (Shao.energy z) (Shao.prefixSum z n)
        (fun h => he h.2)
      rw [sourceIntervalCompletion_pos ν _ _ _ _ hQ] at hext
      exact hext.symm
  · simp only [completedValue, RawInitialCompletion.rawInitial, hQ, false_and, if_false]

theorem completedValue_dead (n : ℕ) (ν : Measure BridgeNoise)
    (x : ℝ) (z : Shao.Path n) (σ : Equiv.Perm (Fin n)) (k : ℕ)
    (h : ¬ strictLive x z σ k) :
    completedValue ν x z σ k = 0 := by
  simp [completedValue, h]

theorem completedValue_exterior (n : ℕ) (ν : Measure BridgeNoise)
    (x : ℝ) (z : Shao.Path n) (σ : Equiv.Perm (Fin n)) (k : ℕ)
    (h : ¬ |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z)) :
    completedValue ν x z σ k = 0 := by
  unfold completedValue
  exact if_neg (fun hg => h hg.2.2)

theorem completedValue_zero_energy (n : ℕ) (ν : Measure BridgeNoise)
    (x : ℝ) (z : Shao.Path n) (σ : Equiv.Perm (Fin n)) (k : ℕ)
    (h : Shao.energy z = 0) :
    completedValue ν x z σ k = 0 := by
  simp [completedValue, h]

open scoped Classical in
theorem completedValue_terminal (n : ℕ) (ν : Measure BridgeNoise)
    (x : ℝ) (z : Shao.Path n) (σ : Equiv.Perm (Fin n)) :
    completedValue ν x z σ n = if 0 < Shao.energy z ∧ strictLive x z σ n then 1 else 0 := by
  have hs : Shao.prefixSum (fun i => z (σ i)) n = Shao.prefixSum z n := by
    simp only [Shao.prefixSum_length]
    exact Equiv.sum_comp σ z
  have hq : Shao.prefixSquares (fun i => z (σ i)) n = Shao.energy z := by
    rw [Shao.prefixSquares_length]
    exact Equiv.sum_comp σ (fun i => (z i) ^ 2)
  by_cases hA : 0 < Shao.energy z ∧ strictLive x z σ n
  · have he : |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z) := by
      simpa only [hs] using hA.2 n le_rfl
    simp only [completedValue, hA.1, hA.2, he, and_self, if_true,
      hs, hq, sub_self, sourceIntervalCompletion_reachable_zero]
  · have hguard : ¬ (0 < Shao.energy z ∧ strictLive x z σ n ∧
        |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z)) := fun h => hA ⟨h.1, h.2.1⟩
    simp only [completedValue, if_neg hguard, if_neg hA]

theorem completedValue_reveal_observable (n : ℕ) (ν : Measure BridgeNoise)
    (x : ℝ) (z : Shao.Path n) (k : ℕ) (σ τ : Equiv.Perm (Fin n))
    (hστ : ∀ i : Fin n, i.val < k → σ i = τ i) :
    completedValue ν x z σ k = completedValue ν x z τ k := by
  have hp (j : ℕ) (hj : j ≤ k) :
      Shao.prefixSum (fun i => z (σ i)) j = Shao.prefixSum (fun i => z (τ i)) j := by
    apply Finset.sum_congr rfl
    intro i hi
    change z (σ i) = z (τ i)
    rw [hστ i (lt_of_lt_of_le (Finset.mem_filter.mp hi).2 hj)]
  have hq : Shao.prefixSquares (fun i => z (σ i)) k =
      Shao.prefixSquares (fun i => z (τ i)) k := by
    apply Finset.sum_congr rfl
    intro i hi
    change (z (σ i)) ^ 2 = (z (τ i)) ^ 2
    rw [hστ i (Finset.mem_filter.mp hi).2]
  have hl : strictLive x z σ k ↔ strictLive x z τ k := by
    constructor
    · intro h j hj
      rw [← hp j hj]
      exact h j hj
    · intro h j hj
      rw [hp j hj]
      exact h j hj
  by_cases hG : 0 < Shao.energy z ∧ strictLive x z σ k ∧
      |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z)
  · have hG' : 0 < Shao.energy z ∧ strictLive x z τ k ∧
        |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z) :=
      ⟨hG.1, hl.mp hG.2.1, hG.2.2⟩
    rw [completedValue, if_pos hG, completedValue, if_pos hG', hp k le_rfl, hq]
  · have hG' : ¬ (0 < Shao.energy z ∧ strictLive x z τ k ∧
        |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z)) :=
      fun h => hG ⟨h.1, hl.mpr h.2.1, h.2.2⟩
    rw [completedValue, if_neg hG, completedValue, if_neg hG']

end Shao.C2.CompletedIntervalProcess
