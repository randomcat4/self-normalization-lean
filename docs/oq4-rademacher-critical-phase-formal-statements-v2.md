/-
FROZEN_STATEMENTS_V2; NOT_A_COMPILABLE_IMPLEMENTATION.
Expected module: Shao/OQ4/RademacherCriticalPhase.lean
The definitions are transparent. The theorem entries contain complete heads only.
Scope: frozen deterministic CP0--CP3, fixed c > 0.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Monotone.Basic

open Filter
open scoped Topology
noncomputable section

namespace Shao.OQ4.RademacherCriticalPhase

def root (n : ℕ) : ℝ := Real.rpow (n : ℝ) ((1 : ℝ) / 3)
def height (c : ℝ) (n : ℕ) : ℝ := c * root n
def phaseFloor (c : ℝ) (n : ℕ) : ℕ := Nat.floor (height c n)
def upperHeight (c : ℝ) (n : ℕ) : ℝ := (phaseFloor c n : ℝ) + 1
def delta (c : ℝ) (n : ℕ) : ℝ := upperHeight c n - height c n
def q (c : ℝ) : ℝ := Real.pi ^ 2 / (4 * c ^ 3)
def exponent (c : ℝ) (n : ℕ) : ℝ := q c * delta c n
def factor (c : ℝ) (n : ℕ) : ℝ := Real.exp (exponent c n)
def cutoff (c : ℝ) : ℕ := max 1 (Nat.ceil (1 / c ^ 3))

def WeakCell (c : ℝ) (n : ℕ) : Prop :=
  1 ≤ height c n ∧ 1 ≤ phaseFloor c n ∧
  (phaseFloor c n : ℝ) ≤ height c n ∧ height c n < upperHeight c n ∧
  upperHeight c n = height c n + delta c n ∧ 0 < delta c n ∧ delta c n ≤ 1

def Cluster (z : ℕ → ℝ) : Set ℝ :=
  {L | ∃ σ : ℕ → ℕ, StrictMono σ ∧ Tendsto (fun j => z (σ j)) atTop (𝓝 L)}

def target (c β : ℝ) (k : ℕ) : ℝ := (((k : ℝ) + β) / c) ^ 3
def upIndex (c : ℝ) (k : ℕ) : ℕ := Nat.ceil (target c 0 k)
def downIndex (c : ℝ) (k : ℕ) : ℕ := Nat.ceil (target c 0 k) - 1
def nearestIndex (c α : ℝ) (k : ℕ) : ℕ := Nat.floor (target c α k + (1 : ℝ) / 2)
def cubeIndex (k : ℕ) : ℕ := k ^ 3
def belowCubeIndex (k : ℕ) : ℕ := k ^ 3 - 1

def phaseIndex (c d : ℝ) (k : ℕ) : ℕ :=
  letI : DecidableEq ℝ := Classical.decEq ℝ
  if d = 0 then downIndex c k
  else if d = 1 then upIndex c k
  else nearestIndex c (1 - d) k

/- CP0: root, finite prefix, the same weak cell, and all three scales. -/

theorem root_spec (n : ℕ) :
    0 ≤ root n ∧ root n ^ 3 = (n : ℝ) ∧
    (∀ x : ℝ, 0 ≤ x → x ^ 3 = (n : ℝ) → x = root n)

theorem zero_prefix (c : ℝ) :
    root 0 = 0 ∧ height c 0 = 0 ∧ phaseFloor c 0 = 0 ∧
    upperHeight c 0 = 1 ∧ delta c 0 = 1 ∧ (0 : ℝ) / height c 0 ^ 3 = 0

theorem positive_time {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 1 ≤ n) :
    0 < root n ∧ 0 < height c n ∧ height c n ^ 3 = c ^ 3 * (n : ℝ) ∧
    (n : ℝ) / height c n ^ 3 = 1 / c ^ 3 ∧ 0 < 1 / c ^ 3

theorem finite_phase {c : ℝ} (hc : 0 < c) (n : ℕ) :
    0 ≤ height c n ∧ (phaseFloor c n : ℤ) = Int.floor (height c n) ∧
    (phaseFloor c n : ℝ) ≤ height c n ∧ height c n < upperHeight c n ∧
    upperHeight c n = height c n + delta c n ∧
    0 < delta c n ∧ delta c n ≤ 1 ∧ 0 < q c ∧
    0 < exponent c n ∧ exponent c n ≤ q c ∧
    1 < factor c n ∧ factor c n ≤ Real.exp (q c) ∧
    (∀ z : ℤ, height c n = (z : ℝ) → delta c n = 1)

theorem cutoff_spec {c : ℝ} (hc : 0 < c) :
    1 ≤ cutoff c ∧ (∀ n : ℕ, cutoff c ≤ n → WeakCell c n)

theorem scales {c : ℝ} (hc : 0 < c) :
    Tendsto (height c) atTop atTop ∧
    Tendsto (fun n : ℕ => (n : ℝ) / height c n ^ 2) atTop atTop

theorem scales_on_strict_subsequence {c : ℝ} (hc : 0 < c)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) :
    Tendsto (fun j => height c (σ j)) atTop atTop ∧
    Tendsto (fun j => (σ j : ℝ) / height c (σ j) ^ 2) atTop atTop ∧
    (∀ᶠ j in atTop, cutoff c ≤ σ j ∧ WeakCell c (σ j) ∧
      1 ≤ σ j ∧ 0 < height c (σ j) ∧
      (σ j : ℝ) / height c (σ j) ^ 3 = 1 / c ^ 3 ∧ 0 < 1 / c ^ 3)

/- CP1: the two exact, fully legal c = 1 subsequences. -/

theorem exact_cube {k : ℕ} (hk : 1 ≤ k) :
    WeakCell 1 (cubeIndex k) ∧ height 1 (cubeIndex k) = (k : ℝ) ∧
    phaseFloor 1 (cubeIndex k) = k ∧ upperHeight 1 (cubeIndex k) = (k : ℝ) + 1 ∧
    delta 1 (cubeIndex k) = 1

theorem exact_below_cube {k : ℕ} (hk : 2 ≤ k) :
    1 ≤ belowCubeIndex k ∧
    (belowCubeIndex k : ℤ) = (k : ℤ) ^ 3 - 1 ∧
    (belowCubeIndex k : ℝ) = (k : ℝ) ^ 3 - 1 ∧
    ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 ∧
    ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 ∧
    WeakCell 1 (belowCubeIndex k) ∧
    (k : ℝ) - 1 < height 1 (belowCubeIndex k) ∧
    height 1 (belowCubeIndex k) < (k : ℝ) ∧
    phaseFloor 1 (belowCubeIndex k) = k - 1 ∧
    upperHeight 1 (belowCubeIndex k) = (k : ℝ) ∧
    delta 1 (belowCubeIndex k) = (k : ℝ) - height 1 (belowCubeIndex k)

theorem cube_subsequence :
    StrictMono (fun j : ℕ => cubeIndex (j + 1)) ∧
    (∀ j : ℕ, cutoff 1 ≤ cubeIndex (j + 1) ∧ WeakCell 1 (cubeIndex (j + 1))) ∧
    Tendsto (fun j : ℕ => delta 1 (cubeIndex (j + 1))) atTop (𝓝 1) ∧
    Tendsto (fun j : ℕ => exponent 1 (cubeIndex (j + 1))) atTop (𝓝 (Real.pi ^ 2 / 4)) ∧
    Tendsto (fun j : ℕ => factor 1 (cubeIndex (j + 1))) atTop
      (𝓝 (Real.exp (Real.pi ^ 2 / 4)))

theorem below_cube_subsequence :
    Tendsto (fun k : ℕ => delta 1 (belowCubeIndex k)) atTop (𝓝 0) ∧
    StrictMono (fun j : ℕ => belowCubeIndex (j + 2)) ∧
    (∀ j : ℕ, cutoff 1 ≤ belowCubeIndex (j + 2) ∧ WeakCell 1 (belowCubeIndex (j + 2))) ∧
    Tendsto (fun j : ℕ => delta 1 (belowCubeIndex (j + 2))) atTop (𝓝 0) ∧
    Tendsto (fun j : ℕ => exponent 1 (belowCubeIndex (j + 2))) atTop (𝓝 0) ∧
    Tendsto (fun j : ℕ => factor 1 (belowCubeIndex (j + 2))) atTop (𝓝 1)

/- CP2: actual rounded integers; rounding and stability are conclusions. -/

theorem up_rounding {c : ℝ} (hc : 0 < c) :
    upIndex c 0 = 0 ∧
    (∀ k : ℕ, 0 ≤ (upIndex c k : ℝ) - target c 0 k ∧
      (upIndex c k : ℝ) - target c 0 k < 1)

theorem down_rounding {c : ℝ} (hc : 0 < c) :
    downIndex c 0 = 0 ∧
    (∀ k : ℕ, 1 ≤ k → 1 ≤ upIndex c k ∧
      (downIndex c k : ℤ) = (upIndex c k : ℤ) - 1 ∧
      (downIndex c k : ℝ) = (upIndex c k : ℝ) - 1 ∧
      -1 ≤ (downIndex c k : ℝ) - target c 0 k ∧
      (downIndex c k : ℝ) - target c 0 k < 0)

theorem nearest_rounding {c α : ℝ} (hc : 0 < c) (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ k : ℕ, -(1 / 2 : ℝ) < (nearestIndex c α k : ℝ) - target c α k ∧
      (nearestIndex c α k : ℝ) - target c α k ≤ 1 / 2 ∧
      |(nearestIndex c α k : ℝ) - target c α k| ≤ 1 / 2 ∧
      (∀ l : ℕ, target c α k = (l : ℝ) + 1 / 2 → nearestIndex c α k = l + 1)

theorem up_phase {c : ℝ} (hc : 0 < c) :
    Tendsto (fun k : ℕ => height c (upIndex c k) - (k : ℝ)) atTop (𝓝 0) ∧
    (∀ᶠ (k : ℕ) in atTop, 1 ≤ k ∧ (k : ℝ) ≤ height c (upIndex c k) ∧
      height c (upIndex c k) < (k : ℝ) + 1 ∧ phaseFloor c (upIndex c k) = k) ∧
    Tendsto (fun k : ℕ => delta c (upIndex c k)) atTop (𝓝 1)

theorem down_phase {c : ℝ} (hc : 0 < c) :
    Tendsto (fun k : ℕ => height c (downIndex c k) - (k : ℝ)) atTop (𝓝 0) ∧
    (∀ᶠ k in atTop, 2 ≤ k ∧ ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 ∧
      ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 ∧
      (k : ℝ) - 1 < height c (downIndex c k) ∧
      height c (downIndex c k) < (k : ℝ) ∧ phaseFloor c (downIndex c k) = k - 1) ∧
    Tendsto (fun k : ℕ => delta c (downIndex c k)) atTop (𝓝 0)

theorem nearest_phase {c α : ℝ} (hc : 0 < c) (hα0 : 0 < α) (hα1 : α < 1) :
    Tendsto (fun k : ℕ => height c (nearestIndex c α k) - ((k : ℝ) + α))
      atTop (𝓝 0) ∧
    (∀ᶠ (k : ℕ) in atTop, (k : ℝ) < height c (nearestIndex c α k) ∧
      height c (nearestIndex c α k) < (k : ℝ) + 1 ∧ phaseFloor c (nearestIndex c α k) = k) ∧
    Tendsto (fun k : ℕ => delta c (nearestIndex c α k)) atTop (𝓝 (1 - α))

theorem up_subsequence {c : ℝ} (hc : 0 < c) :
    ∃ K : ℕ, 1 ≤ K ∧ StrictMono (fun j : ℕ => upIndex c (j + K)) ∧
      (∀ j : ℕ, cutoff c ≤ upIndex c (j + K) ∧ WeakCell c (upIndex c (j + K))) ∧
      Tendsto (fun j : ℕ => delta c (upIndex c (j + K))) atTop (𝓝 1) ∧
      Tendsto (fun j : ℕ => exponent c (upIndex c (j + K))) atTop (𝓝 (q c)) ∧
      Tendsto (fun j : ℕ => factor c (upIndex c (j + K))) atTop (𝓝 (Real.exp (q c)))

theorem down_subsequence {c : ℝ} (hc : 0 < c) :
    ∃ K : ℕ, 2 ≤ K ∧ StrictMono (fun j : ℕ => downIndex c (j + K)) ∧
      (∀ j : ℕ, cutoff c ≤ downIndex c (j + K) ∧ WeakCell c (downIndex c (j + K))) ∧
      Tendsto (fun j : ℕ => delta c (downIndex c (j + K))) atTop (𝓝 0) ∧
      Tendsto (fun j : ℕ => exponent c (downIndex c (j + K))) atTop (𝓝 0) ∧
      Tendsto (fun j : ℕ => factor c (downIndex c (j + K))) atTop (𝓝 1)

theorem nearest_subsequence {c α : ℝ} (hc : 0 < c) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ K : ℕ, 1 ≤ K ∧ StrictMono (fun j : ℕ => nearestIndex c α (j + K)) ∧
      (∀ j : ℕ, cutoff c ≤ nearestIndex c α (j + K) ∧ WeakCell c (nearestIndex c α (j + K))) ∧
      Tendsto (fun j : ℕ => delta c (nearestIndex c α (j + K))) atTop (𝓝 (1 - α)) ∧
      Tendsto (fun j : ℕ => exponent c (nearestIndex c α (j + K))) atTop (𝓝 (q c * (1 - α))) ∧
      Tendsto (fun j : ℕ => factor c (nearestIndex c α (j + K))) atTop
        (𝓝 (Real.exp (q c * (1 - α))))

/- CP3: actual phase-index tails, full two-way cluster sets, no real limit. -/

theorem phase_realization {c d : ℝ} (hc : 0 < c) (hd : d ∈ Set.Icc (0 : ℝ) 1) :
    ∃ K : ℕ, 2 ≤ K ∧ StrictMono (fun j : ℕ => phaseIndex c d (j + K)) ∧
      (∀ j : ℕ, cutoff c ≤ phaseIndex c d (j + K) ∧
        WeakCell c (phaseIndex c d (j + K)) ∧ 1 ≤ phaseIndex c d (j + K) ∧
        0 < height c (phaseIndex c d (j + K)) ∧
        (phaseIndex c d (j + K) : ℝ) / height c (phaseIndex c d (j + K)) ^ 3 = 1 / c ^ 3 ∧
        0 < 1 / c ^ 3) ∧
      Tendsto (fun j : ℕ => delta c (phaseIndex c d (j + K))) atTop (𝓝 d) ∧
      Tendsto (fun j : ℕ => exponent c (phaseIndex c d (j + K))) atTop (𝓝 (q c * d)) ∧
      Tendsto (fun j : ℕ => factor c (phaseIndex c d (j + K))) atTop (𝓝 (Real.exp (q c * d)))

theorem cluster_sets {c : ℝ} (hc : 0 < c) :
    Cluster (delta c) = Set.Icc (0 : ℝ) 1 ∧
    Cluster (exponent c) = Set.Icc (0 : ℝ) (q c) ∧
    Cluster (factor c) = Set.Icc (1 : ℝ) (Real.exp (q c))

theorem not_convergent {c : ℝ} (hc : 0 < c) :
    (¬ ∃ L : ℝ, Tendsto (delta c) atTop (𝓝 L)) ∧
    (¬ ∃ L : ℝ, Tendsto (exponent c) atTop (𝓝 L)) ∧
    (¬ ∃ L : ℝ, Tendsto (factor c) atTop (𝓝 L))

end Shao.OQ4.RademacherCriticalPhase
