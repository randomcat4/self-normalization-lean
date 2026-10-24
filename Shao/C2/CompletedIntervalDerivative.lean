import Shao.C2.CompletedIntervalEnergy

noncomputable section
namespace Shao.C2.CompletedIntervalDerivative
open MeasureTheory
open Shao.C2.BridgeDomination Shao.C2.CompletionMeasurability
open Shao.C2.CompletedIntervalProcess Shao.C1.PermutationEnergyEnvelope

def spatialDerivative (ν : Measure BridgeNoise) (a y T z : ℝ) : ℝ :=
  deriv (fun u : ℝ => intervalCompletion ν a u T z) y

def completedDerivative (ν : Measure BridgeNoise) (x : ℝ) {n : ℕ} (z : Shao.Path n)
    (σ : Equiv.Perm (Fin n)) (r : Fin n) : ℝ := by
  classical
  exact if 0 < Shao.energy z ∧ strictLive x z σ r.val ∧
      |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z) ∧
      0 < Shao.energy z - Shao.prefixSquares (fun i => z (σ i)) r.val then
    spatialDerivative ν (x * Real.sqrt (Shao.energy z))
      (Shao.prefixSum (fun i => z (σ i)) r.val)
      (Shao.energy z - Shao.prefixSquares (fun i => z (σ i)) r.val)
      (Shao.prefixSum z n)
  else 0

set_option maxHeartbeats 1500000 in
theorem measurable_completedDerivative (n : ℕ) (ν : Measure BridgeNoise)
    (hD : Measurable (fun p : CompletionParameters => spatialDerivative ν p.1 p.2.1 p.2.2.1 p.2.2.2))
    (x : ℝ) (σ : Equiv.Perm (Fin n)) (r : Fin n) :
    Measurable (fun z : Shao.Path n => completedDerivative ν x z σ r) := by
  have hσ : Measurable (fun z : Shao.Path n => fun i => z (σ i)) :=
    Measurable.of_eval (fun i => measurable_pi_apply (σ i))
  have hy := (Shao.measurable_prefixSum r.val).comp hσ
  have hT := Shao.measurable_energy.sub ((Shao.measurable_prefixSquares r.val).comp hσ)
  have hz := Shao.measurable_prefixSum (n := n) n
  have hp : Measurable (fun z : Shao.Path n =>
      ((x * Real.sqrt (Shao.energy z),
        (Shao.prefixSum (fun i => z (σ i)) r.val,
          (Shao.energy z - Shao.prefixSquares (fun i => z (σ i)) r.val, Shao.prefixSum z n))) :
        CompletionParameters)) :=
    (Shao.measurable_energyWall x).prodMk (hy.prodMk (hT.prodMk hz))
  have hm := hD.comp hp
  dsimp only [Function.comp_def] at hm
  unfold completedDerivative
  exact Measurable.ite
    ((measurableSet_lt measurable_const Shao.measurable_energy).inter
      ((measurableSet_strictLive n x σ r.val).inter
        ((measurableSet_lt (continuous_abs.measurable.comp hz) (Shao.measurable_energyWall x)).inter
          (measurableSet_lt measurable_const hT))))
    hm measurable_const

theorem completedDerivative_reveal_observable (n : ℕ) (ν : Measure BridgeNoise)
    (x : ℝ) (z : Shao.Path n) (r : Fin n) (σ τ : Equiv.Perm (Fin n))
    (hστ : ∀ i : Fin n, i.val < r.val → σ i = τ i) :
    completedDerivative ν x z σ r = completedDerivative ν x z τ r := by
  have hp (j : ℕ) (hj : j ≤ r.val) :
      Shao.prefixSum (fun i => z (σ i)) j = Shao.prefixSum (fun i => z (τ i)) j := by
    apply Finset.sum_congr rfl
    intro i hi
    change z (σ i) = z (τ i)
    rw [hστ i (lt_of_lt_of_le (Finset.mem_filter.mp hi).2 hj)]
  have hq : Shao.prefixSquares (fun i => z (σ i)) r.val =
      Shao.prefixSquares (fun i => z (τ i)) r.val := by
    apply Finset.sum_congr rfl
    intro i hi
    change (z (σ i)) ^ 2 = (z (τ i)) ^ 2
    rw [hστ i (Finset.mem_filter.mp hi).2]
  have hl : strictLive x z σ r.val ↔ strictLive x z τ r.val := by
    constructor
    · intro h j hj
      rw [← hp j hj]
      exact h j hj
    · intro h j hj
      rw [hp j hj]
      exact h j hj
  by_cases hG : 0 < Shao.energy z ∧ strictLive x z σ r.val ∧
      |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z) ∧
      0 < Shao.energy z - Shao.prefixSquares (fun i => z (σ i)) r.val
  · have hG' : 0 < Shao.energy z ∧ strictLive x z τ r.val ∧
        |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z) ∧
        0 < Shao.energy z - Shao.prefixSquares (fun i => z (τ i)) r.val :=
      ⟨hG.1, hl.mp hG.2.1, hG.2.2.1, by rw [← hq]; exact hG.2.2.2⟩
    rw [completedDerivative, if_pos hG, completedDerivative, if_pos hG', hp r.val le_rfl, hq]
  · have hG' : ¬ (0 < Shao.energy z ∧ strictLive x z τ r.val ∧
        |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z) ∧
        0 < Shao.energy z - Shao.prefixSquares (fun i => z (τ i)) r.val) := by
      intro h
      apply hG
      exact ⟨h.1, hl.mpr h.2.1, h.2.2.1, by rw [hq]; exact h.2.2.2⟩
    rw [completedDerivative, if_neg hG, completedDerivative, if_neg hG']

theorem completedDerivative_live (n : ℕ) (ν : Measure BridgeNoise)
    (x : ℝ) (z : Shao.Path n) (σ : Equiv.Perm (Fin n)) (r : Fin n)
    (hQ : 0 < Shao.energy z) (hLive : strictLive x z σ r.val)
    (hEnd : |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z))
    (hT : 0 < Shao.energy z - Shao.prefixSquares (fun i => z (σ i)) r.val) :
    completedDerivative ν x z σ r =
      spatialDerivative ν (x * Real.sqrt (Shao.energy z))
        (Shao.prefixSum (fun i => z (σ i)) r.val)
        (Shao.energy z - Shao.prefixSquares (fun i => z (σ i)) r.val)
        (Shao.prefixSum z n) := by
  exact if_pos ⟨hQ, hLive, hEnd, hT⟩

theorem completedDerivative_live_hasDerivAt (n : ℕ) (ν : Measure BridgeNoise)
    (hRegular : ∀ a y T z : ℝ, 0 < a → 0 < T → |y| < a → |z| < a →
      HasDerivAt (fun u : ℝ => intervalCompletion ν a u T z) (spatialDerivative ν a y T z) y)
    (x : ℝ) (hx : 0 < x) (z : Shao.Path n) (σ : Equiv.Perm (Fin n)) (r : Fin n)
    (hQ : 0 < Shao.energy z) (hLive : strictLive x z σ r.val)
    (hEnd : |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z))
    (hT : 0 < Shao.energy z - Shao.prefixSquares (fun i => z (σ i)) r.val) :
    HasDerivAt (fun u : ℝ => intervalCompletion ν (x * Real.sqrt (Shao.energy z)) u
        (Shao.energy z - Shao.prefixSquares (fun i => z (σ i)) r.val) (Shao.prefixSum z n))
      (completedDerivative ν x z σ r) (Shao.prefixSum (fun i => z (σ i)) r.val) := by
  rw [completedDerivative_live n ν x z σ r hQ hLive hEnd hT]
  exact hRegular _ _ _ _ (mul_pos hx (Real.sqrt_pos.mpr hQ)) hT (hLive r.val le_rfl) hEnd

theorem completedDerivative_inactive (n : ℕ) (ν : Measure BridgeNoise)
    (x : ℝ) (z : Shao.Path n) (σ : Equiv.Perm (Fin n)) (r : Fin n)
    (h : ¬ (0 < Shao.energy z ∧ strictLive x z σ r.val ∧
      |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z))) :
    completedDerivative ν x z σ r = 0 := by
  unfold completedDerivative
  exact if_neg (fun hg => h ⟨hg.1, hg.2.1, hg.2.2.1⟩)

theorem completedDerivative_guarded_bound (n : ℕ) (ν : Measure BridgeNoise)
    (x : ℝ) (hx : 0 < x) (H C : ℝ) (hH : 0 < H) (hC : 0 ≤ C)
    (hBound : ∀ a y T z : ℝ, 0 < a → 0 < T → |y| < a → |z| < a →
      |spatialDerivative ν a y T z| ≤ C / Real.sqrt T * (1 + |z - y| / Real.sqrt T))
    (z : Shao.Path n) (σ : Equiv.Perm (Fin n)) (r : Fin n)
    (hGuard : H ≤ revealRemainingEnergy z σ r) :
    |completedDerivative ν x z σ r| ≤
      C / Real.sqrt (revealRemainingEnergy z σ r) *
        (1 + |revealRemainingSum z σ r| / Real.sqrt (revealRemainingEnergy z σ r)) := by
  have hR : revealRemainingEnergy z σ r =
      Shao.energy z - Shao.prefixSquares (fun i => z (σ i)) r.val := rfl
  have hd : revealRemainingSum z σ r =
      Shao.prefixSum z n - Shao.prefixSum (fun i => z (σ i)) r.val := by
    rw [Shao.prefixSum_length]
    rfl
  have hT : 0 < Shao.energy z - Shao.prefixSquares (fun i => z (σ i)) r.val :=
    hH.trans_le hGuard
  by_cases hLive : 0 < Shao.energy z ∧ strictLive x z σ r.val ∧
      |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z)
  · rw [completedDerivative_live n ν x z σ r hLive.1 hLive.2.1 hLive.2.2 hT, hR, hd]
    exact hBound _ _ _ _ (mul_pos hx (Real.sqrt_pos.mpr hLive.1)) hT
      (hLive.2.1 r.val le_rfl) hLive.2.2
  · rw [completedDerivative_inactive n ν x z σ r hLive, abs_zero]
    exact mul_nonneg (div_nonneg hC (Real.sqrt_nonneg _))
      (add_nonneg zero_le_one (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)))

end Shao.C2.CompletedIntervalDerivative
