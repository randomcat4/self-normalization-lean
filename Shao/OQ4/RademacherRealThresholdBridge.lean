import Shao.OQ4.RademacherCosine
import Shao.Basic.ClosedSurvival
import Shao.Probability.MeasurablePath
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.Order.Floor.Ring

/-!
实际 Rademacher 路径的实数阈值事件桥。
作者候选完整实现；本轮未运行 Lean、服务器或 Git。
公开定义与定理类型逐项保持冻结的 7 + 20 项声明。
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Shao.OQ4.RademacherRealThresholdBridge

def pathMeasure (N : ℕ) : Measure (Shao.Path N) :=
  Measure.pi (fun _ : Fin N => Shao.OQ4.RademacherCosine.law)

def weakEvent (N : ℕ) (t : ℝ) : Set (Shao.Path N) :=
  {a | ∀ j : ℕ, 1 ≤ j → j ≤ N → |Shao.prefixSum a j| ≤ t}

def strictEvent (N : ℕ) (t : ℝ) : Set (Shao.Path N) :=
  {a | ∀ j : ℕ, 1 ≤ j → j ≤ N → |Shao.prefixSum a j| < t}

def weakProbability (N : ℕ) (t : ℝ) : ℝ :=
  (pathMeasure N).real (weakEvent N t)

def strictProbability (N : ℕ) (t : ℝ) : ℝ :=
  (pathMeasure N).real (strictEvent N t)

def weakIndex (h : ℝ) : ℤ :=
  ⌊h⌋

def strictIndex (h : ℝ) : ℤ :=
  ⌈h⌉ - 1

private instance pathMeasure_isProbabilityMeasure (N : ℕ) :
    IsProbabilityMeasure (pathMeasure N) := by
  dsimp [pathMeasure]
  infer_instance

private theorem measurableSet_sign :
    MeasurableSet {x : ℝ | x = (-1 : ℝ) ∨ x = (1 : ℝ)} := by
  have heq :
      {x : ℝ | x = (-1 : ℝ) ∨ x = (1 : ℝ)} =
        ({(-1 : ℝ)} ∪ {(1 : ℝ)}) := by
    ext x
    simp [or_comm]
  rw [heq]
  exact (measurableSet_singleton (-1 : ℝ)).union
    (measurableSet_singleton (1 : ℝ))

private theorem ae_law_sign :
    ∀ᵐ x ∂Shao.OQ4.RademacherCosine.law,
      x = (-1 : ℝ) ∨ x = (1 : ℝ) := by
  rw [ae_iff]
  have hs :
      MeasurableSet {x : ℝ | ¬ (x = (-1 : ℝ) ∨ x = (1 : ℝ))} :=
    measurableSet_sign.compl
  rw [Shao.OQ4.RademacherCosine.law, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' (1 : ℝ) hs, Measure.dirac_apply' (-1 : ℝ) hs]
  simp

private theorem prefixSum_integer_of_sign
    (N : ℕ) (a : Shao.Path N)
    (ha : ∀ i : Fin N, a i = (-1 : ℝ) ∨ a i = (1 : ℝ))
    (j : ℕ) :
    ∃ z : ℤ, Shao.prefixSum a j = (z : ℝ) := by
  classical
  have hsum (s : Finset (Fin N)) :
      ∃ z : ℤ, (∑ i ∈ s, a i) = (z : ℝ) := by
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨0, by simp⟩
    | @insert i s hi ih =>
        obtain ⟨z, hz⟩ := ih
        rcases ha i with hneg | hpos
        · refine ⟨(-1 : ℤ) + z, ?_⟩
          simp [hi, hneg, hz]
        · refine ⟨(1 : ℤ) + z, ?_⟩
          simp [hi, hpos, hz]
  exact hsum (Finset.univ.filter (fun i : Fin N => i.val < j))

private theorem intCast_le_floor_iff (q : ℤ) (h : ℝ) :
    (q : ℝ) ≤ h ↔ (q : ℝ) ≤ (weakIndex h : ℝ) := by
  change (q : ℝ) ≤ h ↔ (q : ℝ) ≤ ((⌊h⌋ : ℤ) : ℝ)
  constructor
  · intro hqh
    have hq : q ≤ ⌊h⌋ := Int.le_floor.mpr hqh
    exact_mod_cast hq
  · intro hqh
    exact hqh.trans (Int.floor_le h)

private theorem intCast_lt_ceil_sub_one_iff (q : ℤ) (h : ℝ) :
    (q : ℝ) < h ↔ (q : ℝ) ≤ (strictIndex h : ℝ) := by
  change (q : ℝ) < h ↔ (q : ℝ) ≤ ((⌈h⌉ - 1 : ℤ) : ℝ)
  constructor
  · intro hqh
    have hq : q < ⌈h⌉ := Int.lt_ceil.mpr hqh
    have hq' : q ≤ ⌈h⌉ - 1 := by omega
    exact_mod_cast hq'
  · intro hqh
    have hq : q ≤ ⌈h⌉ - 1 := by exact_mod_cast hqh
    have hq' : q < ⌈h⌉ := by omega
    exact Int.lt_ceil.mp hq'

private theorem real_eq_of_ae_membership_iff
    {N : ℕ} (A B : Set (Shao.Path N))
    (hAB : ∀ᵐ a ∂(pathMeasure N), a ∈ A ↔ a ∈ B) :
    (pathMeasure N).real A = (pathMeasure N).real B := by
  change ((pathMeasure N) A).toReal = ((pathMeasure N) B).toReal
  apply congrArg ENNReal.toReal
  exact measure_congr (hAB.mono (fun _ h => propext h))

private theorem prefixSum_one_eq_zero_coordinate
    (N : ℕ) (a : Shao.Path N) (i0 : Fin N) (hi0 : i0.val = 0) :
    Shao.prefixSum a 1 = a i0 := by
  classical
  have hf :
      Finset.univ.filter (fun i : Fin N => i.val < 1) = {i0} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hi
      apply Fin.ext
      omega
    · intro hi
      subst i
      simpa [hi0]
  rw [Shao.prefixSum, hf]
  simp

theorem measurableSet_weakEvent (N : ℕ) (t : ℝ) :
    MeasurableSet (weakEvent N t) := by
  have hm (j : ℕ) :
      MeasurableSet
        {a : Shao.Path N | 1 ≤ j → j ≤ N → |Shao.prefixSum a j| ≤ t} := by
    by_cases hj : 1 ≤ j
    · by_cases hjN : j ≤ N
      · have habs : Measurable (fun a : Shao.Path N => |Shao.prefixSum a j|) :=
          (Shao.continuous_prefixSum (n := N) j).abs.measurable
        simpa only [hj, hjN, true_implies] using
          (measurableSet_le habs measurable_const)
      · simp [hjN]
    · simp [hj]
  have heq :
      weakEvent N t =
        ⋂ j : ℕ, {a : Shao.Path N |
          1 ≤ j → j ≤ N → |Shao.prefixSum a j| ≤ t} := by
    ext a
    simp [weakEvent]
  rw [heq]
  exact MeasurableSet.iInter hm

theorem measurableSet_strictEvent (N : ℕ) (t : ℝ) :
    MeasurableSet (strictEvent N t) := by
  have hm (j : ℕ) :
      MeasurableSet
        {a : Shao.Path N | 1 ≤ j → j ≤ N → |Shao.prefixSum a j| < t} := by
    by_cases hj : 1 ≤ j
    · by_cases hjN : j ≤ N
      · have habs : Measurable (fun a : Shao.Path N => |Shao.prefixSum a j|) :=
          (Shao.continuous_prefixSum (n := N) j).abs.measurable
        simpa only [hj, hjN, true_implies] using
          (measurableSet_lt habs measurable_const)
      · simp [hjN]
    · simp [hj]
  have heq :
      strictEvent N t =
        ⋂ j : ℕ, {a : Shao.Path N |
          1 ≤ j → j ≤ N → |Shao.prefixSum a j| < t} := by
    ext a
    simp [strictEvent]
  rw [heq]
  exact MeasurableSet.iInter hm

theorem ae_coordinates_sign (N : ℕ) :
    ∀ᵐ a ∂(pathMeasure N),
      ∀ i : Fin N, a i = (-1 : ℝ) ∨ a i = (1 : ℝ) := by
  have hcoord (i : Fin N) :
      ∀ᵐ a ∂(pathMeasure N),
        a i = (-1 : ℝ) ∨ a i = (1 : ℝ) := by
    have hmap :
        (pathMeasure N).map (Function.eval i) =
          Shao.OQ4.RademacherCosine.law := by
      simpa [pathMeasure] using
        (Measure.pi_map_eval
          (fun _ : Fin N => Shao.OQ4.RademacherCosine.law) i)
    have hmap_ae :
        ∀ᵐ x ∂(pathMeasure N).map (Function.eval i),
          x = (-1 : ℝ) ∨ x = (1 : ℝ) := by
      rw [hmap]
      exact ae_law_sign
    exact (ae_map_iff (measurable_pi_apply i).aemeasurable
      measurableSet_sign).mp hmap_ae
  exact ae_all_iff.mpr hcoord

theorem ae_prefixSum_integer (N : ℕ) :
    ∀ᵐ a ∂(pathMeasure N),
      ∀ j : ℕ, 1 ≤ j → j ≤ N →
        ∃ z : ℤ, Shao.prefixSum a j = (z : ℝ) := by
  filter_upwards [ae_coordinates_sign N] with a ha
  intro j _ _
  exact prefixSum_integer_of_sign N a ha j

theorem weakIndex_one_le (h : ℝ) (hh : 1 ≤ h) :
    (1 : ℤ) ≤ weakIndex h := by
  have hcast :=
    (intCast_le_floor_iff (1 : ℤ) h).mp (by simpa using hh)
  exact_mod_cast hcast

theorem weakEvent_ae_floor (N : ℕ) (h : ℝ) (hh : 1 ≤ h) :
    ∀ᵐ a ∂(pathMeasure N),
      a ∈ weakEvent N h ↔ a ∈ weakEvent N (weakIndex h : ℝ) := by
  filter_upwards [ae_prefixSum_integer N] with a ha
  have hj (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N) :
      |Shao.prefixSum a j| ≤ h ↔
        |Shao.prefixSum a j| ≤ (weakIndex h : ℝ) := by
    obtain ⟨z, hz⟩ := ha j hj hjN
    simpa only [hz, Int.cast_abs] using (intCast_le_floor_iff |z| h)
  constructor
  · intro hmem j hj1 hjN
    exact (hj j hj1 hjN).mp (hmem j hj1 hjN)
  · intro hmem j hj1 hjN
    exact (hj j hj1 hjN).mpr (hmem j hj1 hjN)

theorem weakProbability_eq_floor (N : ℕ) (h : ℝ) (hh : 1 ≤ h) :
    weakProbability N h = weakProbability N (weakIndex h : ℝ) := by
  exact real_eq_of_ae_membership_iff
    (weakEvent N h) (weakEvent N (weakIndex h : ℝ))
    (weakEvent_ae_floor N h hh)

theorem weakEvent_eq_closedStrip (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    weakEvent N t = (@Shao.closedStrip N t) := by
  ext a
  constructor
  · intro hmem
    change ∀ j : ℕ, j ≤ N → |Shao.prefixSum a j| ≤ t
    intro j hjN
    by_cases hj0 : j = 0
    · subst j
      simpa only [Shao.prefixSum_zero, abs_zero] using ht
    · exact hmem j (by omega) hjN
  · intro hmem
    change ∀ j : ℕ, 1 ≤ j → j ≤ N → |Shao.prefixSum a j| ≤ t
    intro j _ hjN
    exact hmem j hjN

theorem strictIndex_nonneg (h : ℝ) (hh : 1 ≤ h) :
    (0 : ℤ) ≤ strictIndex h := by
  have h0 : ((0 : ℤ) : ℝ) < h :=
    lt_of_lt_of_le (by norm_num) hh
  have hcast := (intCast_lt_ceil_sub_one_iff (0 : ℤ) h).mp h0
  exact_mod_cast hcast

theorem strictIndex_one :
    strictIndex (1 : ℝ) = (0 : ℤ) := by
  norm_num [strictIndex]

theorem strictEvent_ae_ceil_sub_one (N : ℕ) (h : ℝ) (hh : 1 ≤ h) :
    ∀ᵐ a ∂(pathMeasure N),
      a ∈ strictEvent N h ↔ a ∈ weakEvent N (strictIndex h : ℝ) := by
  filter_upwards [ae_prefixSum_integer N] with a ha
  have hj (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N) :
      |Shao.prefixSum a j| < h ↔
        |Shao.prefixSum a j| ≤ (strictIndex h : ℝ) := by
    obtain ⟨z, hz⟩ := ha j hj hjN
    simpa only [hz, Int.cast_abs] using (intCast_lt_ceil_sub_one_iff |z| h)
  constructor
  · intro hmem j hj1 hjN
    exact (hj j hj1 hjN).mp (hmem j hj1 hjN)
  · intro hmem j hj1 hjN
    exact (hj j hj1 hjN).mpr (hmem j hj1 hjN)

theorem strictProbability_eq_ceil_sub_one (N : ℕ) (h : ℝ) (hh : 1 ≤ h) :
    strictProbability N h = weakProbability N (strictIndex h : ℝ) := by
  exact real_eq_of_ae_membership_iff
    (strictEvent N h) (weakEvent N (strictIndex h : ℝ))
    (strictEvent_ae_ceil_sub_one N h hh)

theorem strictEvent_ae_weak_of_noninteger
    (N : ℕ) (h : ℝ) (hh : 1 ≤ h)
    (hnonint : ¬ ∃ z : ℤ, h = (z : ℝ)) :
    ∀ᵐ a ∂(pathMeasure N),
      a ∈ strictEvent N h ↔ a ∈ weakEvent N h := by
  filter_upwards [ae_prefixSum_integer N] with a ha
  constructor
  · intro hmem j hj hjN
    exact le_of_lt (hmem j hj hjN)
  · intro hmem j hj hjN
    have hle := hmem j hj hjN
    obtain ⟨z, hz⟩ := ha j hj hjN
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exfalso
      apply hnonint
      refine ⟨|z|, ?_⟩
      calc
        h = |Shao.prefixSum a j| := heq.symm
        _ = |(z : ℝ)| := congrArg abs hz
        _ = ((|z| : ℤ) : ℝ) := by rw [Int.cast_abs]

theorem strictProbability_eq_weak_of_noninteger
    (N : ℕ) (h : ℝ) (hh : 1 ≤ h)
    (hnonint : ¬ ∃ z : ℤ, h = (z : ℝ)) :
    strictProbability N h = weakProbability N h := by
  exact real_eq_of_ae_membership_iff
    (strictEvent N h) (weakEvent N h)
    (strictEvent_ae_weak_of_noninteger N h hh hnonint)

theorem strictEvent_ae_integer (N k : ℕ) (hk : 1 ≤ k) :
    ∀ᵐ a ∂(pathMeasure N),
      a ∈ strictEvent N (k : ℝ) ↔
        a ∈ weakEvent N ((k : ℝ) - 1) := by
  have hkreal : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  simpa only [strictIndex, Int.ceil_natCast, Int.cast_sub, Int.cast_natCast,
    Int.cast_one] using
      (strictEvent_ae_ceil_sub_one N (k : ℝ) hkreal)

theorem strictProbability_eq_integer (N k : ℕ) (hk : 1 ≤ k) :
    strictProbability N (k : ℝ) = weakProbability N ((k : ℝ) - 1) := by
  exact real_eq_of_ae_membership_iff
    (strictEvent N (k : ℝ)) (weakEvent N ((k : ℝ) - 1))
    (strictEvent_ae_integer N k hk)

theorem weakProbability_zero_time (t : ℝ) :
    weakProbability 0 t = (1 : ℝ) := by
  have heq : weakEvent 0 t = Set.univ := by
    ext a
    change
      (∀ j : ℕ, 1 ≤ j → j ≤ 0 → |Shao.prefixSum a j| ≤ t) ↔ True
    constructor
    · intro _
      trivial
    · intro _ j hj hj0
      omega
  change ((pathMeasure 0) (weakEvent 0 t)).toReal = (1 : ℝ)
  rw [heq]
  simp

theorem strictProbability_zero_time (t : ℝ) :
    strictProbability 0 t = (1 : ℝ) := by
  have heq : strictEvent 0 t = Set.univ := by
    ext a
    change
      (∀ j : ℕ, 1 ≤ j → j ≤ 0 → |Shao.prefixSum a j| < t) ↔ True
    constructor
    · intro _
      trivial
    · intro _ j hj hj0
      omega
  change ((pathMeasure 0) (strictEvent 0 t)).toReal = (1 : ℝ)
  rw [heq]
  simp

theorem strictProbability_one (N : ℕ) (hN : 1 ≤ N) :
    strictProbability N (1 : ℝ) = (0 : ℝ) := by
  let i0 : Fin N := ⟨0, by omega⟩
  have hbad :
      ∀ᵐ a ∂(pathMeasure N), a ∉ strictEvent N (1 : ℝ) := by
    filter_upwards [ae_coordinates_sign N] with a ha
    intro hmem
    have hfirst : |Shao.prefixSum a 1| < (1 : ℝ) :=
      hmem 1 (by omega) hN
    have hsum : Shao.prefixSum a 1 = a i0 :=
      prefixSum_one_eq_zero_coordinate N a i0 rfl
    rw [hsum] at hfirst
    rcases ha i0 with hneg | hpos
    · rw [hneg] at hfirst
      norm_num at hfirst
    · rw [hpos] at hfirst
      norm_num at hfirst
  have hzero : (pathMeasure N) (strictEvent N (1 : ℝ)) = 0 := by
    simpa only [not_not, Set.setOf_mem_eq] using (ae_iff.mp hbad)
  change ((pathMeasure N) (strictEvent N (1 : ℝ))).toReal = (0 : ℝ)
  rw [hzero]
  simp

theorem weakProbability_zero (N : ℕ) (hN : 1 ≤ N) :
    weakProbability N (0 : ℝ) = (0 : ℝ) := by
  have hbridge := strictProbability_eq_integer N 1 (by omega)
  norm_num at hbridge
  rw [← hbridge]
  exact strictProbability_one N hN

end Shao.OQ4.RademacherRealThresholdBridge

end