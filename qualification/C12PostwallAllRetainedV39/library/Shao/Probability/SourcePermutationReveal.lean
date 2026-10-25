/-
Frozen v2 definitions; formal proof implementation in progress.
Exact frozen transparent values; completed theorems only below.
目标生产模块：Shao.Probability.SourcePermutationReveal。
来源：c12/main.tex 869--955；supplement.tex 4192--4237。
本清单不声称完成任何 C1/C2/compact/joint 根定理。
-/
import Shao.Probability.FiniteIID
import Shao.Probability.SpitzerFinite
import Shao.C1.StoppedPermutationTelescope
import Shao.C2.BridgeDomination
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Order.Interval.Finset.Fin

set_option autoImplicit false

noncomputable section

namespace Shao.Probability.SourcePermutationReveal

open MeasureTheory ProbabilityTheory
open Shao.C2.BridgeDomination
open scoped BigOperators

abbrev LabelPerm (n : ℕ) := Equiv.Perm (Fin n)
abbrev BridgeKernel := (ℝ × ℝ × ℝ × ℝ) → ℝ

/-- 本模块内排列种子使用离散可测空间；定义的测度都绑定这个空间。 -/
local instance labelPermMeasurableSpace (n : ℕ) : MeasurableSpace (LabelPerm n) := ⊤

def PrefixMeasurable {n : ℕ} {α : Sort*} (r : ℕ)
    (f : LabelPerm n → α) : Prop :=
  ∀ σ τ : LabelPerm n,
    (∀ i : Fin n, i.val < r → σ i = τ i) → f σ = f τ

def remainingSum {n : ℕ} (a : Shao.Path n) (r : ℕ) (σ : LabelPerm n) : ℝ :=
  Shao.prefixSum a n - Shao.prefixSum (Spitzer.reorder a σ) r

def remainingEnergy {n : ℕ} (a : Shao.Path n) (r : ℕ)
    (σ : LabelPerm n) : ℝ :=
  Shao.energy a - Shao.prefixSquares (Spitzer.reorder a σ) r

def uniformMean {n : ℕ} (f : LabelPerm n → ℝ) : ℝ :=
  (∑ σ : LabelPerm n, f σ) / (Fintype.card (LabelPerm n) : ℝ)

def compensationCoefficient (b d T : ℝ) : ℝ := b - b ^ 2 * d / T

/-- 是原文条件揭示信息结构中的有界停秩；不是自然 iid 滤过停时。 -/
def IsRevealStoppingRank {n : ℕ} (ν : LabelPerm n → ℕ) : Prop :=
  (∀ σ, ν σ ≤ n) ∧
  ∀ (r : ℕ) (σ τ : LabelPerm n),
    (∀ i : Fin n, i.val < r → σ i = τ i) → (ν σ ≤ r ↔ ν τ ≤ r)

/-- H>0 时为原文首次严格低于 H 的秩；空集合仅作总化，值为 n。 -/
def energyCutoff {n : ℕ} (a : Shao.Path n) (H : ℝ)
    (σ : LabelPerm n) : ℕ := by
  classical
  exact if hex : ∃ r : ℕ, r ≤ n ∧ remainingEnergy a r σ < H then Nat.find hex else n

inductive MonitoredDomain : Type
  | upper
  | lower
  | interval
  deriving DecidableEq

def Interior (J : MonitoredDomain) (w y : ℝ) : Prop :=
  match J with
  | .upper => y < w
  | .lower => -w < y
  | .interval => -w < y ∧ y < w

/-- 直接消费 C12 的实际桥路径生存概率，而非新造任意有界 completion。 -/
def eventCompletionKernel (J : MonitoredDomain)
    (P : Measure Shao.C2.BridgeDomination.BridgeNoise) : BridgeKernel :=
  match J with
  | .upper => fun p => Shao.C2.BridgeDomination.upperCompletion P
      p.1 p.2.1 p.2.2.1 p.2.2.2
  | .lower => fun p => Shao.C2.BridgeDomination.lowerCompletion P
      p.1 p.2.1 p.2.2.1 p.2.2.2
  | .interval => fun p => Shao.C2.BridgeDomination.intervalCompletion P
      p.1 p.2.1 p.2.2.1 p.2.2.2

def actualWall {n : ℕ} (a : Shao.Path n) (x : ℝ) : ℝ :=
  x * Real.sqrt (Shao.energy a)

/-- 只规定真实可达 T=0；不同端点的 T=0 默认零，不是 terminal-envelope 定义。 -/
def completionExt (J : MonitoredDomain) (F : BridgeKernel)
    (w y T z : ℝ) : ℝ := by
  classical
  exact if 0 < w ∧ Interior J w y ∧ Interior J w z then
    if 0 < T then F (w, y, T, z)
    else if T = 0 ∧ y = z then 1 else 0
  else 0

/-- 已包含原文 live、endpoint 和 Q>0 指标；初始点 0 也接受严格壁检查。 -/
def sourceAlive {n : ℕ} (J : MonitoredDomain) (a : Shao.Path n)
    (x : ℝ) (r : ℕ) (σ : LabelPerm n) : Prop :=
  0 < Shao.energy a ∧
    Interior J (actualWall a x) (Shao.prefixSum a n) ∧
    ∀ k : ℕ, k ≤ r →
      Interior J (actualWall a x) (Shao.prefixSum (Spitzer.reorder a σ) k)

def sourceValue {n : ℕ} (J : MonitoredDomain) (F : BridgeKernel)
    (a : Shao.Path n) (x : ℝ) (r : ℕ) (σ : LabelPerm n) : ℝ := by
  classical
  exact if sourceAlive J a x r σ then
    completionExt J F (actualWall a x)
      (Shao.prefixSum (Spitzer.reorder a σ) r)
      (remainingEnergy a r σ) (Shao.prefixSum a n)
  else 0

/-- G 是可实例化为实际 f_y 的槽位；代数恒等式对任意 G 都成立。 -/
def localRemainder (J : MonitoredDomain) (F G : BridgeKernel)
    (w y T z b : ℝ) : ℝ :=
  completionExt J F w (y + b) (T - b ^ 2) z - F (w, y, T, z) -
    compensationCoefficient b (z - y) T * G (w, y, T, z)

/-- 死状态、外端点、零能量状态不进入导数槽位。 -/
def sourceDerivativeWeight {n : ℕ} (J : MonitoredDomain) (G : BridgeKernel)
    (a : Shao.Path n) (x : ℝ) (r : ℕ) (σ : LabelPerm n) : ℝ := by
  classical
  exact if sourceAlive J a x r σ ∧ 0 < remainingEnergy a r σ then
    G (actualWall a x, Shao.prefixSum (Spitzer.reorder a σ) r,
      remainingEnergy a r σ, Shao.prefixSum a n)
  else 0

/-- 已把 1_A 1_endpoint 融入此函数；r≥n 或 T≤0 总化为零。 -/
def sourceRemainder {n : ℕ} (J : MonitoredDomain) (F G : BridgeKernel)
    (a : Shao.Path n) (x : ℝ) (r : ℕ) (σ : LabelPerm n) : ℝ := by
  classical
  exact if hr : r < n then
    if sourceAlive J a x r σ ∧ 0 < remainingEnergy a r σ then
      localRemainder J F G (actualWall a x)
        (Shao.prefixSum (Spitzer.reorder a σ) r)
        (remainingEnergy a r σ) (Shao.prefixSum a n) (a (σ ⟨r, hr⟩))
    else 0
  else 0

def stoppedRemainderSum {n : ℕ} (J : MonitoredDomain) (F G : BridgeKernel)
    (a : Shao.Path n) (x : ℝ) (ν : LabelPerm n → ℕ)
    (σ : LabelPerm n) : ℝ :=
  ∑ r ∈ Finset.range n, if r < ν σ then sourceRemainder J F G a x r σ else 0

/-- 正时间的源导数大小合同；没有目标平均等式、鞅或概率比较前提。 -/
structure KernelBounds (J : MonitoredDomain) (F G : BridgeKernel) (C : ℝ) : Prop where
  nonnegC : 0 ≤ C
  completion_bounds : ∀ w y T z : ℝ,
    0 < w → 0 < T → Interior J w y → Interior J w z →
      0 ≤ F (w, y, T, z) ∧ F (w, y, T, z) ≤ 1
  derivative_bound : ∀ w y T z : ℝ,
    0 < w → 0 < T → Interior J w y → Interior J w z →
      |G (w, y, T, z)| ≤ C / Real.sqrt T * (1 + |z - y| / Real.sqrt T)

def PermutationInvariant {n : ℕ} (m : Shao.Path n → ℝ) : Prop :=
  ∀ (a : Shao.Path n) (σ : LabelPerm n), m (Spitzer.reorder a σ) = m a

/-- 实际独立均匀排列测度，不是固定排列或任意不明权重。 -/
def uniformPermutationLaw (n : ℕ) : Measure (LabelPerm n) :=
  ((Fintype.card (LabelPerm n) : ENNReal)⁻¹) • Measure.count

def revealLaw {n : ℕ} (P : Measure (Shao.Path n)) :
    Measure (Shao.Path n × LabelPerm n) :=
  P.prod (uniformPermutationLaw n)

def randomReorder {n : ℕ} (p : Shao.Path n × LabelPerm n) : Shao.Path n :=
  Spitzer.reorder p.1 p.2


private theorem remaining_terminal {n : ℕ} (a : Shao.Path n) (r : ℕ)
    (hr : n ≤ r) (σ : LabelPerm n) : remainingSum a r σ = 0 ∧ remainingEnergy a r σ = 0 := by
  have hf : Finset.univ.filter (fun i : Fin n => i.val < r) = Finset.univ :=
    Finset.filter_eq_self.mpr (fun i _ => i.is_lt.trans_le hr)
  have hs := Equiv.sum_comp σ a
  have hq := Equiv.sum_comp σ (fun i => (a i) ^ 2)
  simp only [remainingSum, remainingEnergy, Shao.prefixSum, Shao.prefixSquares,
    Spitzer.reorder, hf, Shao.energy]
  have hf' : Finset.univ.filter (fun i : Fin n => i.val < n) = Finset.univ :=
    Finset.filter_eq_self.mpr (fun i _ => i.is_lt)
  simp only [hf', hs, hq, sub_self, and_self]

private theorem tail_data {n : ℕ} (a : Shao.Path n) (r : ℕ) (hr : r ≤ n)
    (σ : LabelPerm n) :
    remainingSum a r σ = ∑ i ∈ Finset.univ.filter (fun i : Fin n => r ≤ i.val), a (σ i) ∧
    remainingEnergy a r σ = ∑ i ∈ Finset.univ.filter (fun i : Fin n => r ≤ i.val), (a (σ i)) ^ 2 := by
  by_cases h : r < n
  · constructor
    · unfold remainingSum
      rw [Shao.prefixSum_length]
      exact (Shao.C1.PermutationCompensation.remaining_sum n a ⟨r, h⟩ σ).symm
    · simpa only [remainingEnergy, Shao.energy, Shao.prefixSquares, Spitzer.reorder] using
        (Shao.C1.PermutationCompensation.remaining_square_sum n a ⟨r, h⟩ σ).symm
  · have he : r = n := by omega
    subst r
    have ht := remaining_terminal a n le_rfl σ
    have hf : Finset.univ.filter (fun i : Fin n => n ≤ i.val) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i _ hi
      exact (Nat.not_le_of_lt i.is_lt) hi
    simp only [hf, Finset.sum_empty, ht.1, ht.2, and_self]

private theorem remaining_antitone {n : ℕ} (a : Shao.Path n) (σ : LabelPerm n) :
    Antitone (fun r : ℕ => remainingEnergy a r σ) := by
  intro r s hrs
  apply sub_le_sub_left
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.trans_le hrs⟩
  · intro i _ _
    exact sq_nonneg _

private theorem prefix_step {n : ℕ} (a : Shao.Path n) (r : Fin n) :
    Shao.prefixSum a (r.val + 1) = Shao.prefixSum a r.val + a r ∧
    Shao.prefixSquares a (r.val + 1) = Shao.prefixSquares a r.val + (a r) ^ 2 := by
  classical
  have hf : Finset.univ.filter (fun i : Fin n => i.val < r.val + 1) =
      insert r (Finset.univ.filter (fun i : Fin n => i.val < r.val)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hn : r ∉ Finset.univ.filter (fun i : Fin n => i.val < r.val) := by simp
  constructor
  · unfold Shao.prefixSum
    rw [hf, Finset.sum_insert hn]
    exact add_comm _ _
  · unfold Shao.prefixSquares
    rw [hf, Finset.sum_insert hn]
    exact add_comm _ _

private theorem completionExt_bounds (J : MonitoredDomain) (F G : BridgeKernel)
    (C : ℝ) (hK : KernelBounds J F G C) (w y T z : ℝ) :
    0 ≤ completionExt J F w y T z ∧ completionExt J F w y T z ≤ 1 := by
  classical
  unfold completionExt
  split_ifs with h hT hzero
  · exact hK.completion_bounds w y T z h.1 hT h.2.1 h.2.2
  all_goals norm_num

theorem remaining_population_geometry {n : ℕ} (a : Shao.Path n)
    (r : ℕ) (hr : r ≤ n) (σ : LabelPerm n) :
    0 ≤ remainingEnergy a r σ ∧
      (remainingSum a r σ) ^ 2 ≤ ((n - r : ℕ) : ℝ) * remainingEnergy a r σ ∧
      (∀ j : Fin n, r ≤ j.val → (a (σ j)) ^ 2 ≤ remainingEnergy a r σ) ∧
      (remainingEnergy a r σ = 0 → remainingSum a r σ = 0 ∧
        ∀ j : Fin n, r ≤ j.val → a (σ j) = 0) := by
  classical
  let U : Finset (Fin n) := Finset.univ.filter (fun i => r ≤ i.val)
  have ht := tail_data a r hr σ
  have hcard : U.card = n - r := by
    by_cases h : r < n
    · have he : U = Finset.Ici (⟨r, h⟩ : Fin n) := by
        ext i
        simp only [U, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici]
        rfl
      rw [he, Fin.card_Ici]
    · have he : r = n := by omega
      subst r
      have heU : U = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro i _ hi
        exact (Nat.not_le_of_lt i.is_lt) hi
      simp [heU]
  have hnon : 0 ≤ remainingEnergy a r σ := by
    rw [ht.2]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsingle (j : Fin n) (hj : r ≤ j.val) : (a (σ j)) ^ 2 ≤ remainingEnergy a r σ := by
    rw [ht.2]
    exact Finset.single_le_sum (s := U) (f := fun i : Fin n => (a (σ i)) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
  refine ⟨hnon, ?_, hsingle, ?_⟩
  · have hcs := sq_sum_le_card_mul_sum_sq (s := U) (f := fun i => a (σ i))
    simpa only [ht.1, ht.2, hcard, U] using hcs
  · intro hzero
    have hall (j : Fin n) (hj : r ≤ j.val) : a (σ j) = 0 := by
      have hs : (a (σ j)) ^ 2 = 0 := le_antisymm (hzero ▸ hsingle j hj) (sq_nonneg _)
      exact sq_eq_zero_iff.mp hs
    refine ⟨?_, hall⟩
    rw [ht.1]
    apply Finset.sum_eq_zero
    intro j hj
    exact hall j (Finset.mem_filter.mp hj).2

instance uniformPermutationLaw_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (uniformPermutationLaw n) := by
  constructor
  have hN : (Fintype.card (LabelPerm n) : ENNReal) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (show Nonempty (LabelPerm n) from inferInstance)).ne'
  simp only [uniformPermutationLaw, Measure.smul_apply, smul_eq_mul]
  have hc : (Measure.count : Measure (LabelPerm n)) Set.univ = (Fintype.card (LabelPerm n) : ENNReal) := by
    simpa using Measure.count_apply_finset (α := LabelPerm n) Finset.univ
  rw [hc, ENNReal.inv_mul_cancel hN (ENNReal.natCast_ne_top _)]

theorem uniformPermutationLaw_integral {n : ℕ} (f : LabelPerm n → ℝ) :
    (∫ σ, f σ ∂uniformPermutationLaw n) = uniformMean f := by
  rw [uniformPermutationLaw, integral_smul_measure, integral_count]
  simp [uniformMean, ENNReal.toReal_inv, div_eq_mul_inv, mul_comm]

private theorem path_prefix_data {n : ℕ} (a : Shao.Path n) (r : ℕ)
    (σ τ : LabelPerm n) (h : ∀ i : Fin n, i.val < r → σ i = τ i) :
    ∀ k : ℕ, k ≤ r →
      Shao.prefixSum (Spitzer.reorder a σ) k = Shao.prefixSum (Spitzer.reorder a τ) k ∧
      Shao.prefixSquares (Spitzer.reorder a σ) k = Shao.prefixSquares (Spitzer.reorder a τ) k := by
  intro k hk
  constructor
  · apply Finset.sum_congr rfl
    intro i hi
    change a (σ i) = a (τ i)
    rw [h i ((Finset.mem_filter.mp hi).2.trans_le hk)]
  · apply Finset.sum_congr rfl
    intro i hi
    change (a (σ i)) ^ 2 = (a (τ i)) ^ 2
    rw [h i ((Finset.mem_filter.mp hi).2.trans_le hk)]

theorem source_observables_prefix {n : ℕ} (J : MonitoredDomain)
    (F G : BridgeKernel) (a : Shao.Path n) (x : ℝ) (r : ℕ) :
    PrefixMeasurable r (remainingSum a r) ∧
      PrefixMeasurable r (remainingEnergy a r) ∧
      PrefixMeasurable r (sourceAlive J a x r) ∧
      PrefixMeasurable r (sourceValue J F a x r) ∧
      PrefixMeasurable r (sourceDerivativeWeight J G a x r) := by
  classical
  have hm (σ τ : LabelPerm n) (h : ∀ i : Fin n, i.val < r → σ i = τ i) :
      remainingSum a r σ = remainingSum a r τ ∧
      remainingEnergy a r σ = remainingEnergy a r τ ∧
      sourceAlive J a x r σ = sourceAlive J a x r τ ∧
      sourceValue J F a x r σ = sourceValue J F a x r τ ∧
      sourceDerivativeWeight J G a x r σ = sourceDerivativeWeight J G a x r τ := by
    have hp := path_prefix_data a r σ τ h
    have hd : remainingSum a r σ = remainingSum a r τ := by
      simp only [remainingSum, (hp r le_rfl).1]
    have hT : remainingEnergy a r σ = remainingEnergy a r τ := by
      simp only [remainingEnergy, (hp r le_rfl).2]
    have ha : sourceAlive J a x r σ = sourceAlive J a x r τ := by
      apply propext
      constructor
      · rintro ⟨hQ, hz, hs⟩
        exact ⟨hQ, hz, fun k hk => by rw [← (hp k hk).1]; exact hs k hk⟩
      · rintro ⟨hQ, hz, hs⟩
        exact ⟨hQ, hz, fun k hk => by rw [(hp k hk).1]; exact hs k hk⟩
    refine ⟨hd, hT, ha, ?_, ?_⟩
    · simp only [sourceValue, ha, (hp r le_rfl).1, hT]
    · simp only [sourceDerivativeWeight, ha, (hp r le_rfl).1, hT]
  exact ⟨fun σ τ h => (hm σ τ h).1,
    fun σ τ h => (hm σ τ h).2.1,
    fun σ τ h => (hm σ τ h).2.2.1,
    fun σ τ h => (hm σ τ h).2.2.2.1,
    fun σ τ h => (hm σ τ h).2.2.2.2⟩

theorem energy_cutoff_data {n : ℕ} (a : Shao.Path n) (H : ℝ) (hH : 0 < H) :
    IsRevealStoppingRank (energyCutoff a H) ∧
      (∀ (σ : LabelPerm n) (r : ℕ), r ≤ n →
        (energyCutoff a H σ ≤ r ↔ remainingEnergy a r σ < H)) ∧
      ∀ (σ : LabelPerm n) (r : ℕ), r < energyCutoff a H σ →
        r < n ∧ H ≤ remainingEnergy a r σ := by
  classical
  have hex (σ : LabelPerm n) : ∃ r : ℕ, r ≤ n ∧ remainingEnergy a r σ < H :=
    ⟨n, le_rfl, by rw [(remaining_terminal a n le_rfl σ).2]; exact hH⟩
  have he (σ : LabelPerm n) : energyCutoff a H σ = Nat.find (hex σ) := by
    simp only [energyCutoff, dif_pos (hex σ)]
  have hb (σ : LabelPerm n) : energyCutoff a H σ ≤ n := by
    rw [he]
    exact (Nat.find_spec (hex σ)).1
  have hl (σ : LabelPerm n) (r : ℕ) (hr : r ≤ n) :
      energyCutoff a H σ ≤ r ↔ remainingEnergy a r σ < H := by
    rw [he]
    constructor
    · intro h
      exact (remaining_antitone a σ h).trans_lt (Nat.find_spec (hex σ)).2
    · intro h
      exact Nat.find_min' (hex σ) ⟨hr, h⟩
  refine ⟨⟨hb, ?_⟩, hl, ?_⟩
  · intro r σ τ h
    by_cases hr : r ≤ n
    · rw [hl σ r hr, hl τ r hr]
      have hp := (path_prefix_data a r σ τ h r le_rfl).2
      simp only [remainingEnergy, hp]
    · exact iff_of_true (le_trans (hb σ) (by omega)) (le_trans (hb τ) (by omega))
  · intro σ r hr
    have hrn : r < n := hr.trans_le (hb σ)
    refine ⟨hrn, ?_⟩
    by_contra h
    exact (Nat.not_le_of_lt hr) ((hl σ r hrn.le).mpr (lt_of_not_ge h))

private theorem interior_prefix {n : ℕ} (J : MonitoredDomain) (a : Shao.Path n)
    (x : ℝ) (r : Fin n) (σ : LabelPerm n) :
    sourceAlive J a x (r.val + 1) σ ↔
      sourceAlive J a x r.val σ ∧
        Interior J (actualWall a x)
          (Shao.prefixSum (Spitzer.reorder a σ) r.val + a (σ r)) := by
  have hs := (prefix_step (Spitzer.reorder a σ) r).1
  change Shao.prefixSum (Spitzer.reorder a σ) (r.val + 1) =
    Shao.prefixSum (Spitzer.reorder a σ) r.val + a (σ r) at hs
  constructor
  · rintro ⟨hQ, hz, hsurv⟩
    refine ⟨⟨hQ, hz, fun k hk => hsurv k (hk.trans (Nat.le_succ _))⟩, ?_⟩
    rw [← hs]
    exact hsurv (r.val + 1) le_rfl
  · rintro ⟨⟨hQ, hz, hsurv⟩, hnew⟩
    refine ⟨hQ, hz, fun k hk => ?_⟩
    by_cases hkr : k ≤ r.val
    · exact hsurv k hkr
    · have he : k = r.val + 1 := by omega
      subst k
      rw [hs]
      exact hnew

private theorem source_step {n : ℕ} (J : MonitoredDomain) (F G : BridgeKernel)
    (a : Shao.Path n) (x : ℝ) (hx : 0 < x) (r : Fin n)
    (σ : LabelPerm n) (hT : 0 < remainingEnergy a r.val σ) :
    sourceValue J F a x (r.val + 1) σ - sourceValue J F a x r.val σ -
      sourceDerivativeWeight J G a x r.val σ *
        compensationCoefficient (a (σ r)) (remainingSum a r.val σ)
          (remainingEnergy a r.val σ) = sourceRemainder J F G a x r.val σ := by
  classical
  have hs := (prefix_step (Spitzer.reorder a σ) r).1
  change Shao.prefixSum (Spitzer.reorder a σ) (r.val + 1) =
    Shao.prefixSum (Spitzer.reorder a σ) r.val + a (σ r) at hs
  have hTs : remainingEnergy a (r.val + 1) σ =
      remainingEnergy a r.val σ - (a (σ r)) ^ 2 := by
    unfold remainingEnergy
    rw [(prefix_step (Spitzer.reorder a σ) r).2]
    change Shao.energy a - (Shao.prefixSquares (Spitzer.reorder a σ) r.val + (a (σ r)) ^ 2) = _
    ring
  by_cases ha : sourceAlive J a x r.val σ
  · have hw : 0 < actualWall a x := mul_pos hx (Real.sqrt_pos.mpr ha.1)
    have hy := ha.2.2 r.val le_rfl
    have hz := ha.2.1
    have hinside : 0 < actualWall a x ∧
        Interior J (actualWall a x) (Shao.prefixSum (Spitzer.reorder a σ) r.val) ∧
        Interior J (actualWall a x) (Shao.prefixSum a n) := ⟨hw, hy, hz⟩
    have hguard : sourceAlive J a x r.val σ ∧ 0 < remainingEnergy a r.val σ := ⟨ha, hT⟩
    have hv : sourceValue J F a x r.val σ =
        F (actualWall a x, Shao.prefixSum (Spitzer.reorder a σ) r.val,
          remainingEnergy a r.val σ, Shao.prefixSum a n) := by
      simp only [sourceValue, if_pos ha, completionExt, if_pos hinside, if_pos hT]
    have hvn : sourceValue J F a x (r.val + 1) σ =
        completionExt J F (actualWall a x)
          (Shao.prefixSum (Spitzer.reorder a σ) r.val + a (σ r))
          (remainingEnergy a r.val σ - (a (σ r)) ^ 2) (Shao.prefixSum a n) := by
      by_cases hn : Interior J (actualWall a x)
          (Shao.prefixSum (Spitzer.reorder a σ) r.val + a (σ r))
      · have han := (interior_prefix J a x r σ).mpr ⟨ha, hn⟩
        simp only [sourceValue, if_pos han, hs, hTs]
      · have han : ¬sourceAlive J a x (r.val + 1) σ :=
          fun h => hn ((interior_prefix J a x r σ).mp h).2
        simp only [sourceValue, if_neg han, completionExt]
        rw [if_neg (fun h => hn h.2.1)]
    rw [hvn, hv]
    simp only [sourceDerivativeWeight, if_pos hguard,
      sourceRemainder, dif_pos r.is_lt, if_pos hguard, localRemainder, remainingSum]
    ring
  · have han : ¬sourceAlive J a x (r.val + 1) σ :=
      fun h => ha ((interior_prefix J a x r σ).mp h).1
    simp [sourceValue, ha, han, sourceDerivativeWeight, sourceRemainder, r.is_lt]

theorem masked_stopped_telescope {n : ℕ} (J : MonitoredDomain)
    (F G : BridgeKernel) (a : Shao.Path n) (x : ℝ) (hx : 0 < x)
    (H : ℝ) (hH : 0 < H) (ν : LabelPerm n → ℕ)
    (hν : IsRevealStoppingRank ν) (hcap : ∀ σ, ν σ ≤ energyCutoff a H σ)
    (m : ℝ) :
    uniformMean (fun σ => m * sourceValue J F a x (ν σ) σ) -
      uniformMean (fun σ => m * sourceValue J F a x 0 σ) =
    uniformMean (fun σ => m * stoppedRemainderSum J F G a x ν σ) := by
  classical
  have hcut (σ : LabelPerm n) (r : Fin n) (hr : r.val < ν σ) :
      H ≤ remainingEnergy a r.val σ :=
    ((energy_cutoff_data a H hH).2.2 σ r.val (hr.trans_le (hcap σ))).2
  have hobs (r : Fin n) (σ τ : LabelPerm n)
      (h : ∀ i : Fin n, i.val < r.val → σ i = τ i) :
      (r.val < ν σ ↔ r.val < ν τ) := by
    simpa only [not_le] using not_congr (hν.2 r.val σ τ h)
  have hW (r : Fin n) (σ τ : LabelPerm n)
      (h : ∀ i : Fin n, i.val < r.val → σ i = τ i) :
      m * sourceDerivativeWeight J G a x r.val σ =
        m * sourceDerivativeWeight J G a x r.val τ := by
    rw [(source_observables_prefix J F G a x r.val).2.2.2.2 σ τ h]
  have hbase := Shao.C1.PermutationCompensation.finite_stopped_compensation n a ν hν.1 hobs
    (fun σ r => m * sourceDerivativeWeight J G a x r.val σ) hW H hH hcut
    (fun σ k => m * sourceValue J F a x k σ)
  have hsum : (∑ σ : LabelPerm n,
      (m * sourceValue J F a x (ν σ) σ - m * sourceValue J F a x 0 σ)) =
      ∑ σ : LabelPerm n, m * stoppedRemainderSum J F G a x ν σ := by
    calc
      _ = _ := hbase
      _ = _ := by
        apply Finset.sum_congr rfl
        intro σ _
        calc
          _ = ∑ r : Fin n, if r.val < ν σ then m * sourceRemainder J F G a x r.val σ else 0 := by
            apply Finset.sum_congr rfl
            intro r _
            split_ifs with hr
            · have hs := source_step J F G a x hx r σ (hH.trans_le (hcut σ r hr))
              have hd : (∑ i : Fin n, a i) -
                  (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < r.val), a (σ i)) =
                  remainingSum a r.val σ := by
                unfold remainingSum
                rw [Shao.prefixSum_length]
                rfl
              have ht : (∑ i : Fin n, (a i) ^ 2) -
                  (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < r.val), (a (σ i)) ^ 2) =
                  remainingEnergy a r.val σ := rfl
              dsimp only
              rw [hd, ht]
              change m * sourceValue J F a x (r.val + 1) σ - m * sourceValue J F a x r.val σ -
                  (m * sourceDerivativeWeight J G a x r.val σ) *
                    compensationCoefficient (a (σ r)) (remainingSum a r.val σ) (remainingEnergy a r.val σ) =
                m * sourceRemainder J F G a x r.val σ
              calc
                _ = m * (sourceValue J F a x (r.val + 1) σ - sourceValue J F a x r.val σ -
                  sourceDerivativeWeight J G a x r.val σ *
                    compensationCoefficient (a (σ r)) (remainingSum a r.val σ) (remainingEnergy a r.val σ)) := by ring
                _ = _ := by rw [hs]
            · rfl
          _ = m * stoppedRemainderSum J F G a x ν σ := by
            calc
              _ = ∑ k ∈ Finset.range n, if k < ν σ then m * sourceRemainder J F G a x k σ else 0 :=
                Fin.sum_univ_eq_sum_range (fun k => if k < ν σ then m * sourceRemainder J F G a x k σ else 0) n
              _ = _ := by simp only [stoppedRemainderSum, Finset.mul_sum, mul_ite, mul_zero]
  unfold uniformMean
  rw [← sub_div, ← Finset.sum_sub_distrib, hsum]

theorem source_remainder_uniform_bound {n : ℕ} (J : MonitoredDomain)
    (F G : BridgeKernel) (C : ℝ) (hK : KernelBounds J F G C)
    (a : Shao.Path n) (x : ℝ) (hx : 0 < x) (r : ℕ) (σ : LabelPerm n) :
    |sourceValue J F a x r σ| ≤ 1 ∧
      |sourceRemainder J F G a x r σ| ≤ 1 + 2 * C * (1 + (n : ℝ)) := by
  classical
  have hC : 0 ≤ C := hK.nonnegC
  have hB : 0 ≤ 1 + 2 * C * (1 + (n : ℝ)) := by positivity
  constructor
  · unfold sourceValue
    split_ifs
    · have hb := completionExt_bounds J F G C hK (actualWall a x)
        (Shao.prefixSum (Spitzer.reorder a σ) r) (remainingEnergy a r σ) (Shao.prefixSum a n)
      rw [abs_of_nonneg hb.1]
      exact hb.2
    · norm_num
  · by_cases hr : r < n
    · by_cases hg : sourceAlive J a x r σ ∧ 0 < remainingEnergy a r σ
      · let T := remainingEnergy a r σ
        let d := remainingSum a r σ
        let b := a (σ ⟨r, hr⟩)
        let s := Real.sqrt T
        let D := 1 + |d| / s
        have hT : 0 < T := hg.2
        have hs : 0 < s := Real.sqrt_pos.mpr hT
        have hs2 : s ^ 2 = T := Real.sq_sqrt hT.le
        have hgeo := remaining_population_geometry a r hr.le σ
        have hb2 : b ^ 2 ≤ T := hgeo.2.2.1 ⟨r, hr⟩ le_rfl
        have hab : |b| ≤ s := by nlinarith [sq_abs b, abs_nonneg b]
        have hfrac : b ^ 2 / T ≤ 1 := (div_le_one hT).mpr hb2
        have hD0 : 0 ≤ D := by dsimp [D]; positivity
        have hco : |compensationCoefficient b d T| ≤ s * D := by
          calc
            _ ≤ |b| + |b ^ 2 * d / T| := by
              simpa only [compensationCoefficient, sub_zero, zero_sub, abs_neg] using
                (abs_sub_le b 0 (b ^ 2 * d / T))
            _ = |b| + (b ^ 2 / T) * |d| := by
              rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg b), abs_of_pos hT]
              ring
            _ ≤ s + |d| := add_le_add hab (mul_le_of_le_one_left (abs_nonneg d) hfrac)
            _ = s * D := by dsimp [D]; field_simp [ne_of_gt hs]
        have hq2 : (|d| / s) ^ 2 ≤ ((n - r : ℕ) : ℝ) := by
          rw [div_pow, sq_abs, hs2]
          exact (div_le_iff₀ hT).mpr hgeo.2.1
        have htn : ((n - r : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n r
        have hD2 : D ^ 2 ≤ 2 * (1 + (n : ℝ)) := by
          dsimp only [D]
          nlinarith [sq_nonneg (1 - |d| / s)]
        have hw : 0 < actualWall a x := mul_pos hx (Real.sqrt_pos.mpr hg.1.1)
        have hy := hg.1.2.2 r le_rfl
        have hz := hg.1.2.1
        have hGb := hK.derivative_bound (actualWall a x)
          (Shao.prefixSum (Spitzer.reorder a σ) r) T (Shao.prefixSum a n) hw hT hy hz
        change |G (actualWall a x, Shao.prefixSum (Spitzer.reorder a σ) r, T, Shao.prefixSum a n)| ≤ C / s * D at hGb
        have hp : |compensationCoefficient b d T *
            G (actualWall a x, Shao.prefixSum (Spitzer.reorder a σ) r, T, Shao.prefixSum a n)| ≤
            2 * C * (1 + (n : ℝ)) := by
          calc
            _ = |compensationCoefficient b d T| *
                |G (actualWall a x, Shao.prefixSum (Spitzer.reorder a σ) r, T, Shao.prefixSum a n)| := abs_mul _ _
            _ ≤ (s * D) * (C / s * D) :=
              mul_le_mul hco hGb (abs_nonneg _) (mul_nonneg hs.le hD0)
            _ = C * D ^ 2 := by field_simp [ne_of_gt hs]
            _ ≤ C * (2 * (1 + (n : ℝ))) := mul_le_mul_of_nonneg_left hD2 hK.nonnegC
            _ = _ := by ring
        have hF := hK.completion_bounds (actualWall a x)
          (Shao.prefixSum (Spitzer.reorder a σ) r) T (Shao.prefixSum a n) hw hT hy hz
        have hE := completionExt_bounds J F G C hK (actualWall a x)
          (Shao.prefixSum (Spitzer.reorder a σ) r + b) (T - b ^ 2) (Shao.prefixSum a n)
        have hdiff : |completionExt J F (actualWall a x)
            (Shao.prefixSum (Spitzer.reorder a σ) r + b) (T - b ^ 2) (Shao.prefixSum a n) -
            F (actualWall a x, Shao.prefixSum (Spitzer.reorder a σ) r, T, Shao.prefixSum a n)| ≤ 1 :=
          abs_le.mpr ⟨by linarith, by linarith⟩
        simp only [sourceRemainder, dif_pos hr, if_pos hg, localRemainder]
        change |(completionExt J F (actualWall a x)
          (Shao.prefixSum (Spitzer.reorder a σ) r + b) (T - b ^ 2) (Shao.prefixSum a n) -
          F (actualWall a x, Shao.prefixSum (Spitzer.reorder a σ) r, T, Shao.prefixSum a n)) -
          compensationCoefficient b d T *
            G (actualWall a x, Shao.prefixSum (Spitzer.reorder a σ) r, T, Shao.prefixSum a n)| ≤ _
        exact (abs_sub _ _).trans (add_le_add hdiff hp)
      · simpa only [sourceRemainder, dif_pos hr, if_neg hg, abs_zero] using hB
    · simpa only [sourceRemainder, dif_neg hr, abs_zero] using hB

private theorem measurable_random_sample {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) :
    Measurable (fun p : Ω × LabelPerm n => Spitzer.reorder (samplePath X p.1) p.2) := by
  apply measurable_from_prod_countable_left
  intro σ
  exact measurable_samplePath (fun i => hX (σ i))

theorem iid_randomPermutation_map_eq_pi {n : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (ρ : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ]
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ρ) :
    Measure.map
      (fun p : Ω × LabelPerm n => Spitzer.reorder (samplePath X p.1) p.2)
      (μ.prod (uniformPermutationLaw n)) = Measure.pi (fun _ : Fin n => ρ) := by
  have hR := measurable_random_sample X hX
  have hfixed (σ : LabelPerm n) :
      Measure.map (fun ω => Spitzer.reorder (samplePath X ω) σ) μ =
        Measure.pi (fun _ : Fin n => ρ) :=
    iid_samplePath_map_eq_pi (fun i => hX (σ i))
      (hIndep.precomp σ.injective) (fun i => hLaw (σ i))
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply hR hB, Measure.prod_apply_symm (hB.preimage hR)]
  have hs (σ : LabelPerm n) :
      μ {ω | Spitzer.reorder (samplePath X ω) σ ∈ B} =
        (Measure.pi (fun _ : Fin n => ρ)) B := by
    rw [← hfixed σ]
    have hm : Measurable (fun ω => Spitzer.reorder (samplePath X ω) σ) :=
      measurable_samplePath (fun i => hX (σ i))
    exact (Measure.map_apply hm hB).symm
  change (∫⁻ σ : LabelPerm n, μ {ω | Spitzer.reorder (samplePath X ω) σ ∈ B}
    ∂uniformPermutationLaw n) = _
  simp only [hs, lintegral_const, measure_univ, mul_one]

theorem iid_randomPermutation_invariant_mask_map {n : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (ρ : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ]
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ρ)
    (m : Shao.Path n → ℝ) (hmm : Measurable m) (hInv : PermutationInvariant m) :
    Measure.map
      (fun p : Ω × LabelPerm n =>
        (m (samplePath X p.1), Spitzer.reorder (samplePath X p.1) p.2))
      (μ.prod (uniformPermutationLaw n)) =
    Measure.map (fun ω : Ω => (m (samplePath X ω), samplePath X ω)) μ := by
  have hψ : Measurable (fun v : Shao.Path n => (m v, v)) := hmm.prodMk measurable_id
  have hR := measurable_random_sample X hX
  calc
    _ = Measure.map (fun v : Shao.Path n => (m v, v))
        (Measure.map (fun p : Ω × LabelPerm n => Spitzer.reorder (samplePath X p.1) p.2)
          (μ.prod (uniformPermutationLaw n))) := by
      rw [Measure.map_map hψ hR]
      congr 1
      funext p
      exact Prod.ext (hInv (samplePath X p.1) p.2).symm rfl
    _ = Measure.map (fun v : Shao.Path n => (m v, v)) (Measure.pi (fun _ : Fin n => ρ)) := by
      rw [iid_randomPermutation_map_eq_pi μ ρ X hX hIndep hLaw]
    _ = Measure.map (fun v : Shao.Path n => (m v, v)) (Measure.map (samplePath X) μ) := by
      rw [iid_samplePath_map_eq_pi hX hIndep hLaw]
    _ = _ := Measure.map_map hψ (measurable_samplePath hX)

private theorem joint_strict_events :
    MeasurableSet {p : (ℝ × ℝ × ℝ × ℝ) × BridgeNoise |
      p.2 ∈ strictUpper p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2} ∧
    MeasurableSet {p : (ℝ × ℝ × ℝ × ℝ) × BridgeNoise |
      p.2 ∈ strictLower p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2} := by
  let u : ((ℝ × ℝ × ℝ × ℝ) × BridgeNoise) → C(BridgeTime, ℝ) := fun p =>
    ⟨fun t => bridgePath p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2 t - p.1.1, by fun_prop⟩
  let l : ((ℝ × ℝ × ℝ × ℝ) × BridgeNoise) → C(BridgeTime, ℝ) := fun p =>
    ⟨fun t => -p.1.1 - bridgePath p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2 t, by fun_prop⟩
  have hcu : Continuous u := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : (((ℝ × ℝ × ℝ × ℝ) × BridgeNoise) × BridgeTime) =>
      (1 - (p.2 : ℝ)) * p.1.1.2.1 + (p.2 : ℝ) * p.1.1.2.2.2 +
        Real.sqrt p.1.1.2.2.1 * p.1.2.val p.2 - p.1.1.1)
    fun_prop
  have hcl : Continuous l := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : (((ℝ × ℝ × ℝ × ℝ) × BridgeNoise) × BridgeTime) =>
      -p.1.1.1 - ((1 - (p.2 : ℝ)) * p.1.1.2.1 + (p.2 : ℝ) * p.1.1.2.2.2 +
        Real.sqrt p.1.1.2.2.1 * p.1.2.val p.2))
    fun_prop
  have ho := ContinuousMap.isOpen_setOfPred_mapsTo (X := BridgeTime)
    isCompact_univ (isOpen_Iio (a := (0 : ℝ)))
  have hu : IsOpen {p | ∀ t : BridgeTime, u p t < 0} := by
    simpa [Set.MapsTo] using ho.preimage hcu
  have hl : IsOpen {p | ∀ t : BridgeTime, l p t < 0} := by
    simpa [Set.MapsTo] using ho.preimage hcl
  constructor
  · convert hu.measurableSet using 1
    ext p
    change (∀ t : BridgeTime, bridgePath p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2 t < p.1.1) ↔
      (∀ t : BridgeTime, bridgePath p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2 t - p.1.1 < 0)
    simp only [sub_neg]
  · convert hl.measurableSet using 1
    ext p
    change (∀ t : BridgeTime, -p.1.1 < bridgePath p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2 t) ↔
      (∀ t : BridgeTime, -p.1.1 - bridgePath p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2 t < 0)
    simp only [sub_neg]

private theorem event_exterior (J : MonitoredDomain)
    (P : Measure BridgeNoise) (w y T z : ℝ)
    (h : ¬Interior J w y ∨ ¬Interior J w z) : eventCompletionKernel J P (w, y, T, z) = 0 := by
  cases J with
  | upper =>
    change P.real (strictUpper w y T z) = 0
    have he : strictUpper w y T z = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro g hg
      have hp := bridgePath_endpoints y T z g
      rcases h with hy | hz
      · exact hy (by simpa only [Interior, hp.1] using hg 0)
      · exact hz (by simpa only [Interior, hp.2] using hg 1)
    rw [he, measureReal_empty]
  | lower =>
    change P.real (strictLower w y T z) = 0
    have he : strictLower w y T z = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro g hg
      have hp := bridgePath_endpoints y T z g
      rcases h with hy | hz
      · exact hy (by simpa only [Interior, hp.1] using hg 0)
      · exact hz (by simpa only [Interior, hp.2] using hg 1)
    rw [he, measureReal_empty]
  | interval =>
    change P.real (strictInterval w y T z) = 0
    have he : strictInterval w y T z = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro g hg
      have hp := bridgePath_endpoints y T z g
      rcases h with hy | hz
      · exact hy ⟨by simpa only [hp.1] using hg.2 0, by simpa only [hp.1] using hg.1 0⟩
      · exact hz ⟨by simpa only [hp.2] using hg.2 1, by simpa only [hp.2] using hg.1 1⟩
    rw [he, measureReal_empty]

private theorem event_zero_reachable (J : MonitoredDomain)
    (P : Measure BridgeNoise) [IsProbabilityMeasure P]
    (w y : ℝ) (hy : Interior J w y) : eventCompletionKernel J P (w, y, 0, y) = 1 := by
  have hp (g : BridgeNoise) (t : BridgeTime) : bridgePath y 0 y g t = y := by
    simp only [bridgePath, ContinuousMap.coe_mk, Real.sqrt_zero, zero_mul, add_zero]
    ring
  cases J with
  | upper =>
    change P.real (strictUpper w y 0 y) = 1
    have he : strictUpper w y 0 y = Set.univ := by
      ext g
      simp only [strictUpper, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro t
      rw [hp]
      exact hy
    rw [he, probReal_univ]
  | lower =>
    change P.real (strictLower w y 0 y) = 1
    have he : strictLower w y 0 y = Set.univ := by
      ext g
      simp only [strictLower, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro t
      rw [hp]
      exact hy
    rw [he, probReal_univ]
  | interval =>
    change P.real (strictInterval w y 0 y) = 1
    have he : strictInterval w y 0 y = Set.univ := by
      ext g
      simp only [strictInterval, strictUpper, strictLower, Set.mem_inter_iff,
        Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact ⟨fun t => by rw [hp]; exact hy.2, fun t => by rw [hp]; exact hy.1⟩
    rw [he, probReal_univ]

theorem eventCompletionKernel_data (J : MonitoredDomain)
    (P : Measure Shao.C2.BridgeDomination.BridgeNoise) [IsProbabilityMeasure P] :
    Measurable (eventCompletionKernel J P) ∧
      (∀ p : ℝ × ℝ × ℝ × ℝ,
        0 ≤ eventCompletionKernel J P p ∧ eventCompletionKernel J P p ≤ 1) ∧
      ∀ w y T z : ℝ, 0 < w → 0 ≤ T → (T = 0 → y = z) →
        completionExt J (eventCompletionKernel J P) w y T z =
          eventCompletionKernel J P (w, y, T, z) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · cases J with
    | upper =>
      exact (measurable_measure_prodMk_left (ν := P) joint_strict_events.1).ennreal_toReal
    | lower =>
      exact (measurable_measure_prodMk_left (ν := P) joint_strict_events.2).ennreal_toReal
    | interval =>
      exact (measurable_measure_prodMk_left (ν := P)
        (joint_strict_events.1.inter joint_strict_events.2)).ennreal_toReal
  · intro p
    have hb := completion_bounds P p.1 p.2.1 p.2.2.1 p.2.2.2
    cases J with
    | upper => exact ⟨hb.1, hb.2.1⟩
    | lower => exact ⟨hb.2.2.1, hb.2.2.2.1⟩
    | interval => exact ⟨hb.2.2.2.2.1, hb.2.2.2.2.2⟩
  · intro w y T z hw hT hreach
    by_cases hi : Interior J w y ∧ Interior J w z
    · by_cases ht : T = 0
      · have hz := hreach ht
        subst T
        subst z
        have hinside : 0 < w ∧ Interior J w y ∧ Interior J w y := ⟨hw, hi.1, hi.1⟩
        simp [completionExt, hw, hi.1, event_zero_reachable J P w y hi.1]
      · have hTp : 0 < T := lt_of_le_of_ne hT (Ne.symm ht)
        have hinside : 0 < w ∧ Interior J w y ∧ Interior J w z := ⟨hw, hi⟩
        simp only [completionExt, if_pos hinside, if_pos hTp]
    · have hbad : ¬Interior J w y ∨ ¬Interior J w z := not_and_or.mp hi
      rw [event_exterior J P w y T z hbad]
      exact if_neg (fun h => hi h.2)

private theorem measurable_interior {α : Type*} [MeasurableSpace α]
    (J : MonitoredDomain) (f g : α → ℝ) (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet {a : α | Interior J (f a) (g a)} := by
  cases J with
  | upper => exact measurableSet_lt hg hf
  | lower => exact measurableSet_lt hf.neg hg
  | interval => exact (measurableSet_lt hf.neg hg).inter (measurableSet_lt hg hf)

private theorem measurable_completionExt (J : MonitoredDomain) (F : BridgeKernel)
    (hF : Measurable F) :
    Measurable (fun p : ℝ × ℝ × ℝ × ℝ => completionExt J F p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  classical
  have hw : MeasurableSet {p : ℝ × ℝ × ℝ × ℝ | 0 < p.1} :=
    measurableSet_lt measurable_const measurable_fst
  have hy := measurable_interior J (fun p : ℝ × ℝ × ℝ × ℝ => p.1)
    (fun p => p.2.1) measurable_fst measurable_snd.fst
  have hz := measurable_interior J (fun p : ℝ × ℝ × ℝ × ℝ => p.1)
    (fun p => p.2.2.2) measurable_fst measurable_snd.snd.snd
  have hT : MeasurableSet {p : ℝ × ℝ × ℝ × ℝ | 0 < p.2.2.1} :=
    measurableSet_lt measurable_const measurable_snd.snd.fst
  have he : MeasurableSet {p : ℝ × ℝ × ℝ × ℝ | p.2.2.1 = 0 ∧ p.2.1 = p.2.2.2} :=
    (measurableSet_eq_fun measurable_snd.snd.fst measurable_const).inter
      (measurableSet_eq_fun measurable_snd.fst measurable_snd.snd.snd)
  exact Measurable.ite (hw.inter (hy.inter hz))
    (Measurable.ite hT hF (Measurable.ite he measurable_const measurable_const)) measurable_const

private theorem measurable_sourceAlive {n : ℕ} (J : MonitoredDomain)
    (x : ℝ) (r : ℕ) (σ : LabelPerm n) : MeasurableSet {a : Shao.Path n | sourceAlive J a x r σ} := by
  have hw : Measurable (fun a : Shao.Path n => actualWall a x) :=
    (Real.continuous_sqrt.measurable.comp Shao.measurable_energy).const_mul x
  have hm : Measurable (fun a : Shao.Path n => Spitzer.reorder a σ) :=
    Measurable.of_eval (fun i => measurable_pi_apply (σ i))
  have hz := measurable_interior J (fun a : Shao.Path n => actualWall a x)
    (fun a => Shao.prefixSum a n) hw (Shao.measurable_prefixSum n)
  have hs : MeasurableSet {a : Shao.Path n | ∀ k : Fin (r + 1),
      Interior J (actualWall a x) (Shao.prefixSum (Spitzer.reorder a σ) k.val)} :=
    by
      simpa only [Set.setOf_forall, Function.comp_apply] using MeasurableSet.iInter
        (fun k : Fin (r + 1) => measurable_interior J _ _ hw ((Shao.measurable_prefixSum k.val).comp hm))
  convert (measurableSet_lt measurable_const Shao.measurable_energy).inter (hz.inter hs) using 1
  ext a
  change (0 < Shao.energy a ∧ Interior J (actualWall a x) (Shao.prefixSum a n) ∧
    ∀ k : ℕ, k ≤ r → Interior J (actualWall a x) (Shao.prefixSum (Spitzer.reorder a σ) k)) ↔ _
  constructor
  · rintro ⟨hQ, hZ, hS⟩
    exact ⟨hQ, hZ, fun k => hS k.val (by omega)⟩
  · rintro ⟨hQ, hZ, hS⟩
    exact ⟨hQ, hZ, fun k hk => hS ⟨k, by omega⟩⟩

private theorem measurable_sourceValue {n : ℕ} (J : MonitoredDomain)
    (F : BridgeKernel) (hF : Measurable F) (x : ℝ) (r : ℕ) (σ : LabelPerm n) :
    Measurable (fun a : Shao.Path n => sourceValue J F a x r σ) := by
  classical
  have hm : Measurable (fun a : Shao.Path n => Spitzer.reorder a σ) :=
    Measurable.of_eval (fun i => measurable_pi_apply (σ i))
  have hw : Measurable (fun a : Shao.Path n => actualWall a x) :=
    (Real.continuous_sqrt.measurable.comp Shao.measurable_energy).const_mul x
  have hy := (Shao.measurable_prefixSum r).comp hm
  have hT := Shao.measurable_energy.sub ((Shao.measurable_prefixSquares r).comp hm)
  have hz : Measurable (fun a : Shao.Path n => Shao.prefixSum a n) := Shao.measurable_prefixSum n
  exact Measurable.ite (measurable_sourceAlive J x r σ)
    ((measurable_completionExt J F hF).comp (hw.prodMk (hy.prodMk (hT.prodMk hz)))) measurable_const

private theorem measurable_sourceRemainder {n : ℕ} (J : MonitoredDomain)
    (F G : BridgeKernel) (hF : Measurable F) (hG : Measurable G)
    (x : ℝ) (r : ℕ) (σ : LabelPerm n) :
    Measurable (fun a : Shao.Path n => sourceRemainder J F G a x r σ) := by
  classical
  by_cases hr : r < n
  · have hm : Measurable (fun a : Shao.Path n => Spitzer.reorder a σ) :=
      Measurable.of_eval (fun i => measurable_pi_apply (σ i))
    have hw : Measurable (fun a : Shao.Path n => actualWall a x) :=
      (Real.continuous_sqrt.measurable.comp Shao.measurable_energy).const_mul x
    have hy := (Shao.measurable_prefixSum r).comp hm
    have hT := Shao.measurable_energy.sub ((Shao.measurable_prefixSquares r).comp hm)
    have hz : Measurable (fun a : Shao.Path n => Shao.prefixSum a n) := Shao.measurable_prefixSum n
    have hb : Measurable (fun a : Shao.Path n => a (σ ⟨r, hr⟩)) := measurable_pi_apply _
    have hc := hw.prodMk (hy.prodMk (hT.prodMk hz))
    have hn := hw.prodMk ((hy.add hb).prodMk ((hT.sub (hb.pow_const 2)).prodMk hz))
    have hl := (((measurable_completionExt J F hF).comp hn).sub (hF.comp hc)).sub
      ((hb.sub (((hb.pow_const 2).mul (hz.sub hy)).div hT)).mul (hG.comp hc))
    have hguard : MeasurableSet {a : Shao.Path n |
        sourceAlive J a x r σ ∧ 0 < remainingEnergy a r σ} :=
      (measurable_sourceAlive J x r σ).inter
        (measurableSet_lt (measurable_const (a := (0 : ℝ))) hT)
    simpa only [sourceRemainder, dif_pos hr, localRemainder, compensationCoefficient,
      remainingEnergy, Function.comp_apply, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.div_apply] using
      Measurable.ite hguard hl (measurable_const (a := (0 : ℝ)))
  · simpa only [sourceRemainder, dif_neg hr] using
      (measurable_const : Measurable (fun _ : Shao.Path n => (0 : ℝ)))

theorem source_stopped_integrability {n : ℕ} (J : MonitoredDomain)
    (F G : BridgeKernel) (hFm : Measurable F) (hGm : Measurable G)
    (C : ℝ) (hK : KernelBounds J F G C)
    (P : Measure (Shao.Path n)) [IsProbabilityMeasure P]
    (x : ℝ) (hx : 0 < x) (ν : Shao.Path n → LabelPerm n → ℕ)
    (hνm : ∀ σ, Measurable (fun a => ν a σ)) (hνbound : ∀ a σ, ν a σ ≤ n)
    (m : Shao.Path n → ℝ) (hmm : Measurable m) (hmb : ∀ a, |m a| ≤ 1) :
    Integrable (fun p : Shao.Path n × LabelPerm n =>
      m p.1 * sourceValue J F p.1 x (ν p.1 p.2) p.2) (revealLaw P) ∧
    Integrable (fun p : Shao.Path n × LabelPerm n =>
      m p.1 * sourceValue J F p.1 x 0 p.2) (revealLaw P) ∧
    Integrable (fun p : Shao.Path n × LabelPerm n =>
      m p.1 * stoppedRemainderSum J F G p.1 x (ν p.1) p.2) (revealLaw P) := by
  classical
  unfold revealLaw
  have hC := hK.nonnegC
  have hB : 0 ≤ 1 + 2 * C * (1 + (n : ℝ)) := by positivity
  have hstop (σ : LabelPerm n) :
      Measurable (fun a : Shao.Path n => sourceValue J F a x (ν a σ) σ) := by
    have hp : Measurable (fun p : Shao.Path n × ℕ => sourceValue J F p.1 x p.2 σ) :=
      measurable_from_prod_countable_left (fun r => measurable_sourceValue J F hFm x r σ)
    exact hp.comp (measurable_id.prodMk (hνm σ))
  have hsum (σ : LabelPerm n) :
      Measurable (fun a : Shao.Path n => stoppedRemainderSum J F G a x (ν a) σ) := by
    apply Finset.measurable_sum
    intro r _
    exact Measurable.ite (measurableSet_lt measurable_const (hνm σ))
      (measurable_sourceRemainder J F G hFm hGm x r σ) measurable_const
  have hms : Measurable (fun p : Shao.Path n × LabelPerm n =>
      m p.1 * sourceValue J F p.1 x (ν p.1 p.2) p.2) :=
    measurable_from_prod_countable_left (fun σ => hmm.mul (hstop σ))
  have hm0 : Measurable (fun p : Shao.Path n × LabelPerm n =>
      m p.1 * sourceValue J F p.1 x 0 p.2) :=
    measurable_from_prod_countable_left (fun σ => hmm.mul (measurable_sourceValue J F hFm x 0 σ))
  have hmr : Measurable (fun p : Shao.Path n × LabelPerm n =>
      m p.1 * stoppedRemainderSum J F G p.1 x (ν p.1) p.2) :=
    measurable_from_prod_countable_left (fun σ => hmm.mul (hsum σ))
  have hv (a : Shao.Path n) (r : ℕ) (σ : LabelPerm n) :
      |m a * sourceValue J F a x r σ| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (hmb a) (source_remainder_uniform_bound J F G C hK a x hx r σ).1
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans (by norm_num)
  refine ⟨Integrable.of_bound hms.aestronglyMeasurable 1 (ae_of_all _ (fun p => ?_)),
    Integrable.of_bound hm0.aestronglyMeasurable 1 (ae_of_all _ (fun p => ?_)),
    Integrable.of_bound hmr.aestronglyMeasurable
      ((n : ℝ) * (1 + 2 * C * (1 + (n : ℝ)))) (ae_of_all _ (fun p => ?_))⟩
  · simpa only [Real.norm_eq_abs] using hv p.1 (ν p.1 p.2) p.2
  · simpa only [Real.norm_eq_abs] using hv p.1 0 p.2
  · rw [Real.norm_eq_abs, abs_mul]
    apply le_trans (mul_le_of_le_one_left (abs_nonneg _) (hmb p.1))
    unfold stoppedRemainderSum
    calc
      _ ≤ ∑ r ∈ Finset.range n, |if r < ν p.1 p.2 then sourceRemainder J F G p.1 x r p.2 else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r ∈ Finset.range n, (1 + 2 * C * (1 + (n : ℝ))) := by
        apply Finset.sum_le_sum
        intro r _
        split_ifs
        · exact (source_remainder_uniform_bound J F G C hK p.1 x hx r p.2).2
        · simpa only [abs_zero] using hB
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem source_masked_stopped_telescope_integral {n : ℕ} (J : MonitoredDomain)
    (F G : BridgeKernel) (hFm : Measurable F) (hGm : Measurable G)
    (C : ℝ) (hK : KernelBounds J F G C)
    (P : Measure (Shao.Path n)) [IsProbabilityMeasure P]
    (x : ℝ) (hx : 0 < x) (H : ℝ) (hH : 0 < H)
    (ν : Shao.Path n → LabelPerm n → ℕ)
    (hνm : ∀ σ, Measurable (fun a => ν a σ))
    (hν : ∀ a, IsRevealStoppingRank (ν a))
    (hcap : ∀ a σ, ν a σ ≤ energyCutoff a H σ)
    (m : Shao.Path n → ℝ) (hmm : Measurable m) (hmb : ∀ a, |m a| ≤ 1) :
    (∫ p : Shao.Path n × LabelPerm n,
      m p.1 * sourceValue J F p.1 x (ν p.1 p.2) p.2 ∂revealLaw P) -
    (∫ p : Shao.Path n × LabelPerm n,
      m p.1 * sourceValue J F p.1 x 0 p.2 ∂revealLaw P) =
    ∫ p : Shao.Path n × LabelPerm n,
      m p.1 * stoppedRemainderSum J F G p.1 x (ν p.1) p.2 ∂revealLaw P := by
  have hi := source_stopped_integrability J F G hFm hGm C hK P x hx ν hνm
    (fun a σ => (hν a).1 σ) m hmm hmb
  rw [← integral_sub hi.1 hi.2.1]
  change (∫ p : Shao.Path n × LabelPerm n,
    (m p.1 * sourceValue J F p.1 x (ν p.1 p.2) p.2 - m p.1 * sourceValue J F p.1 x 0 p.2)
      ∂P.prod (uniformPermutationLaw n)) =
    ∫ p : Shao.Path n × LabelPerm n,
      m p.1 * stoppedRemainderSum J F G p.1 x (ν p.1) p.2 ∂P.prod (uniformPermutationLaw n)
  have hdiff : Integrable (fun p : Shao.Path n × LabelPerm n =>
      m p.1 * sourceValue J F p.1 x (ν p.1 p.2) p.2 - m p.1 * sourceValue J F p.1 x 0 p.2)
      (P.prod (uniformPermutationLaw n)) := hi.1.sub hi.2.1
  have hrem : Integrable (fun p : Shao.Path n × LabelPerm n =>
      m p.1 * stoppedRemainderSum J F G p.1 x (ν p.1) p.2)
      (P.prod (uniformPermutationLaw n)) := hi.2.2
  rw [integral_prod _ hdiff, integral_prod _ hrem]
  apply integral_congr_ae
  apply ae_of_all
  intro a
  dsimp only
  rw [uniformPermutationLaw_integral, uniformPermutationLaw_integral]
  have hf := masked_stopped_telescope J F G a x hx H hH (ν a) (hν a) (hcap a) (m a)
  simpa only [uniformMean, Finset.sum_sub_distrib, sub_div] using hf

end Shao.Probability.SourcePermutationReveal
