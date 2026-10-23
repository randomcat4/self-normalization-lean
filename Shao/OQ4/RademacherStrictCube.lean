import Shao.OQ4.RademacherS5Assembly
import Shao.Probability.BrownianSup
import Shao.Probability.BrownianFirstTerm
import Shao.Probability.MeasurablePath
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Aesop
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Declaration-only freeze for the fixed Rademacher strict perfect-cube target,
mathematical freeze frozen-rademacher-strict-cube-v1.md, F1--F4.
Expected future module: Shao/OQ4/RademacherStrictCube.lean.
Local complete implementation draft; all frozen public definitions and types are retained.
No Lean command, remote action or canonical emission has been performed.
The scope is this fixed law and this fixed subsequence, with rawleaf increment zero.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal Topology

namespace Shao.OQ4.RademacherStrictCube

-- These are the actual finite-path events, with positive observation indices.
-- The strict event is defined for every real threshold, including at time zero.
def strictEvent (N : ℕ) (h : ℝ) : Set (Shao.Path N) :=
  {a | ∀ r : ℕ, 1 ≤ r → r ≤ N → |Shao.prefixSum a r| < h}

def strictP (N : ℕ) (h : ℝ) : ℝ :=
  (RademacherS5Assembly.pathLaw N).real (strictEvent N h)

def strictSelfNormalizedEvent (N : ℕ) (s : ℝ) : Set (Shao.Path N) :=
  {a | ∀ r : ℕ, 1 ≤ r → r ≤ N →
    |Shao.prefixSum a r| < s * RademacherS5Assembly.V a}

-- All additions and the cube below are in Nat before any cast to Real.
def k (j : ℕ) : ℕ := j + 2

def n (j : ℕ) : ℕ := k j ^ 3

def x (j : ℕ) : ℝ := (k j : ℝ) / Real.sqrt (n j : ℝ)

def a : ℝ := Real.pi ^ 2 / 4

-- No free probability or tail function is introduced.
def b {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (s : ℝ) : ℝ :=
  Shao.Probability.BrownianSup.probability B P hB s

def strictRatio {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (j : ℕ) : ℝ :=
  strictP (n j) (k j : ℝ) / b B P hB (x j)

def weakRatio {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (j : ℕ) : ℝ :=
  RademacherS5Assembly.p (n j) (k j : ℝ) / b B P hB (x j)

def sourceRatio {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (j : ℕ) : ℝ :=
  (RademacherS5Assembly.pathLaw (n j)).real
      (strictSelfNormalizedEvent (n j) (x j)) / b B P hB (x j)

def mainRate (j : ℕ) : ℝ := (n j : ℝ) / (k j : ℝ) ^ 2

-- This transparent predicate contains only conclusions on one common tail.
def CommonTailAt {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (j : ℕ) : Prop :=
  0 < strictP (n j) (k j : ℝ) ∧
  0 < RademacherS5Assembly.p (n j) (k j : ℝ) ∧
  0 < b B P hB (x j) ∧
  0 < strictRatio B P hB j ∧ 0 < weakRatio B P hB j ∧
  0 < RademacherS5Assembly.p (n j) (k j : ℝ) /
    strictP (n j) (k j : ℝ) ∧
  Real.log (strictRatio B P hB j) =
    Real.log (strictP (n j) (k j : ℝ)) - Real.log (b B P hB (x j)) ∧
  Real.log (weakRatio B P hB j) =
    Real.log (RademacherS5Assembly.p (n j) (k j : ℝ)) -
      Real.log (b B P hB (x j)) ∧
  RademacherS5Assembly.p (n j) (k j : ℝ) / strictP (n j) (k j : ℝ) =
    weakRatio B P hB j / strictRatio B P hB j ∧
  Real.log (RademacherS5Assembly.p (n j) (k j : ℝ) /
      strictP (n j) (k j : ℝ)) =
    Real.log (RademacherS5Assembly.p (n j) (k j : ℝ)) -
      Real.log (strictP (n j) (k j : ℝ)) ∧
  Real.log (RademacherS5Assembly.p (n j) (k j : ℝ)) -
      Real.log (strictP (n j) (k j : ℝ)) =
    Real.log (weakRatio B P hB j) - Real.log (strictRatio B P hB j)

-- F1: one common full-measure set supplies actual coordinate support,
-- integer partial sums, genuine energy, and the actual normalizer identity.
local notation "mSeq" => (fun j : ℕ => j + 1)
local notation "hSeq" => (fun j : ℕ => ((j + 1 : ℕ) : ℝ))
local notation "ySeq" =>
  (fun j : ℕ => ((j + 1 : ℕ) : ℝ) / Real.sqrt (n j : ℝ))

private lemma cube_index_eq (j : ℕ) :
    n j = RademacherS5Assembly.cubeSeq (j + 1) := by
  simp [n, k, RademacherS5Assembly.cubeSeq,
    RademacherCriticalPhase.cubeIndex, Nat.add_assoc]

private lemma cube_mono : StrictMono n := by
  intro i j hij
  simpa only [cube_index_eq] using
    RademacherS5Assembly.S5_CUBE_GEOMETRY.1 (Nat.add_lt_add_right hij 1)

private lemma cube_height_eq (j : ℕ) :
    RademacherS5Assembly.height 1 (n j) = (k j : ℝ) := by
  have hh := (RademacherS5Assembly.S5_CUBE_GEOMETRY.2.2.1 (j + 1)).2.2.1
  rw [← cube_index_eq j] at hh
  simpa [k, Nat.add_assoc] using hh

private lemma cube_scale_eq (j : ℕ) :
    x j = RademacherS5Assembly.x 1 (n j) := by
  have hn : 1 ≤ n j := by
    have hp : 0 < n j := by dsimp [n, k]; positivity
    omega
  have hp := RademacherS5Assembly.positive_time (c := (1 : ℝ))
    (by norm_num) (n := n j) hn
  rcases hp with ⟨_, _, _, _, _, _, _, _, _, _, hx, _⟩
  have hN : RademacherS5Assembly.N (n j) = (n j : ℝ) := rfl
  rw [cube_height_eq, hN] at hx
  exact hx.symm

private lemma k_tendsto_atTop :
    Tendsto (fun j : ℕ => (k j : ℝ)) atTop atTop := by
  have hs : StrictMono (fun j : ℕ => j + 2) :=
    fun _ _ hij => Nat.add_lt_add_right hij 2
  exact (tendsto_natCast_atTop_atTop :
    Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop).comp hs.tendsto_atTop

private lemma h_tendsto_atTop : Tendsto hSeq atTop atTop := by
  have hs : StrictMono (fun j : ℕ => j + 1) :=
    fun _ _ hij => Nat.add_lt_add_right hij 1
  exact (tendsto_natCast_atTop_atTop :
    Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop).comp hs.tendsto_atTop

private lemma x_inv_sqrt (j : ℕ) : x j = (Real.sqrt (k j : ℝ))⁻¹ := by
  have hk : 0 < (k j : ℝ) := by dsimp [k]; positivity
  have hN : (n j : ℝ) = (k j : ℝ) ^ 2 * (k j : ℝ) := by
    simp only [n, Nat.cast_pow]
    ring
  have hs : Real.sqrt (n j : ℝ) = (k j : ℝ) * Real.sqrt (k j : ℝ) := by
    rw [hN, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_pos hk]
  unfold x
  rw [hs]
  field_simp [hk.ne', (Real.sqrt_pos.2 hk).ne'] <;> ring

private lemma x_tendsto_zero : Tendsto x atTop (𝓝 (0 : ℝ)) := by
  have ht := tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp k_tendsto_atTop)
  exact ht.congr' (Filter.Eventually.of_forall fun j => (x_inv_sqrt j).symm)

theorem actual_path_support (N : ℕ) :
    IsProbabilityMeasure (RademacherS5Assembly.pathLaw N) ∧
    RademacherS5Assembly.pathLaw N =
      Measure.pi (fun _ : Fin N => RademacherCosine.law) ∧
    (∀ᵐ v ∂(RademacherS5Assembly.pathLaw N),
      (∀ i : Fin N, v i = 1 ∨ v i = -1) ∧
      (∀ r : ℕ, r ≤ N → ∃ z : ℤ, Shao.prefixSum v r = (z : ℝ)) ∧
      Shao.energy v = (N : ℝ) ∧
      RademacherS5Assembly.V v = Real.sqrt (N : ℝ)) := by
  classical
  rcases RademacherS5Assembly.actual_path_energy N with ⟨hprob, hs⟩
  refine ⟨hprob, rfl, ?_⟩
  filter_upwards [hs] with v hv
  refine ⟨hv.1, ?_, ?_, ?_⟩
  · intro r _
    let z : Fin N → ℤ := fun i => if v i = 1 then 1 else -1
    have hz : ∀ i : Fin N, v i = (z i : ℝ) := by
      intro i
      dsimp [z]
      split_ifs with hi
      · simpa using hi
      · rcases hv.1 i with h | h
        · exact (hi h).elim
        · simpa using h
    refine ⟨∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < r), z i, ?_⟩
    simp only [Shao.prefixSum, Int.cast_sum]
    exact Finset.sum_congr rfl fun i _ => hz i
  · simpa only [show RademacherS5Assembly.N N = (N : ℝ) from rfl] using hv.2.1
  · simpa only [show RademacherS5Assembly.N N = (N : ℝ) from rfl] using hv.2.2

theorem measurable_events (N : ℕ) (h s : ℝ) :
    MeasurableSet (strictEvent N h) ∧
    MeasurableSet (@Shao.closedStrip N h) ∧
    MeasurableSet (strictSelfNormalizedEvent N s) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · change MeasurableSet {v : Shao.Path N | ∀ r : ℕ,
      1 ≤ r → r ≤ N → |Shao.prefixSum v r| < h}
    rw [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro r
    by_cases h1 : 1 ≤ r
    · by_cases h2 : r ≤ N
      · simpa only [h1, h2, true_implies, Function.comp_def] using
          measurableSet_lt (continuous_abs.measurable.comp (Shao.measurable_prefixSum r)) measurable_const
      · simp [h2]
    · simp [h1]
  · change MeasurableSet {v : Shao.Path N | ∀ r : ℕ,
      r ≤ N → |Shao.prefixSum v r| ≤ h}
    rw [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro r
    by_cases h2 : r ≤ N
    · simpa only [h2, true_implies, Function.comp_def] using
        measurableSet_le (continuous_abs.measurable.comp (Shao.measurable_prefixSum r)) measurable_const
    · simp [h2]
  · change MeasurableSet {v : Shao.Path N | ∀ r : ℕ,
      1 ≤ r → r ≤ N → |Shao.prefixSum v r| < s * RademacherS5Assembly.V v}
    rw [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro r
    by_cases h1 : 1 ≤ r
    · by_cases h2 : r ≤ N
      · simpa only [h1, h2, true_implies, Function.comp_def, RademacherS5Assembly.V] using
          measurableSet_lt (continuous_abs.measurable.comp (Shao.measurable_prefixSum r))
            ((Shao.measurable_sqrt_energy (n := N)).const_mul s)
      · simp [h2]
    · simp [h1]

theorem zero_time (h s : ℝ) :
    strictEvent 0 h = Set.univ ∧ strictP 0 h = 1 ∧
    strictSelfNormalizedEvent 0 s = Set.univ ∧
    (RademacherS5Assembly.pathLaw 0).real
      (strictSelfNormalizedEvent 0 s) = 1 := by
  have he : strictEvent 0 h = Set.univ := by
    ext v
    simp only [strictEvent, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    intro r hr h0
    omega
  have hs : strictSelfNormalizedEvent 0 s = Set.univ := by
    ext v
    simp only [strictSelfNormalizedEvent, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    intro r hr h0
    omega
  letI : IsProbabilityMeasure (RademacherS5Assembly.pathLaw 0) :=
    (RademacherS5Assembly.actual_path_energy 0).1
  refine ⟨he, ?_, hs, ?_⟩
  · simp [strictP, he]
  · simp [hs]

-- The predecessor is Nat subtraction followed by a cast; its Real alignment
-- is an output. No support, integer-valuedness, or event bridge is assumed.
theorem integer_boundary_bridge (N K : ℕ) (hK : 2 ≤ K) :
    ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 ∧
    RademacherS5Assembly.p N ((K - 1 : ℕ) : ℝ) =
      (RademacherS5Assembly.pathLaw N).real
        (@Shao.closedStrip N ((K - 1 : ℕ) : ℝ)) ∧
    (∀ᵐ v ∂(RademacherS5Assembly.pathLaw N),
      v ∈ strictEvent N (K : ℝ) ↔
        v ∈ @Shao.closedStrip N ((K - 1 : ℕ) : ℝ)) ∧
    strictP N (K : ℝ) = RademacherS5Assembly.p N ((K - 1 : ℕ) : ℝ) := by
  have hcast : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ K)]
    norm_num
  have hp : RademacherS5Assembly.p N ((K - 1 : ℕ) : ℝ) =
      (RademacherS5Assembly.pathLaw N).real
        (@Shao.closedStrip N ((K - 1 : ℕ) : ℝ)) := rfl
  have he : ∀ᵐ v ∂(RademacherS5Assembly.pathLaw N),
      v ∈ strictEvent N (K : ℝ) ↔
        v ∈ @Shao.closedStrip N ((K - 1 : ℕ) : ℝ) := by
    filter_upwards [(actual_path_support N).2.2] with v hv
    have hi (r : ℕ) (hr : r ≤ N) :
        |Shao.prefixSum v r| < (K : ℝ) ↔
          |Shao.prefixSum v r| ≤ ((K - 1 : ℕ) : ℝ) := by
      rcases hv.2.1 r hr with ⟨z, hz⟩
      rw [hz, hcast, ← Int.cast_abs]
      constructor
      · intro h
        have hzK : |z| < (K : ℤ) := by exact_mod_cast h
        have hzK' : |z| ≤ (K : ℤ) - 1 := by omega
        exact_mod_cast hzK'
      · intro h
        have hzK : |z| ≤ (K : ℤ) - 1 := by exact_mod_cast h
        have hzK' : |z| < (K : ℤ) := by omega
        exact_mod_cast hzK'
    change (∀ r : ℕ, 1 ≤ r → r ≤ N → |Shao.prefixSum v r| < (K : ℝ)) ↔
      ∀ r : ℕ, r ≤ N → |Shao.prefixSum v r| ≤ ((K - 1 : ℕ) : ℝ)
    constructor
    · intro hv' r hr
      by_cases h0 : r = 0
      · subst r
        simp [Shao.prefixSum]
      · exact (hi r hr).1 (hv' r (by omega) hr)
    · intro hv' r _ hr
      exact (hi r hr).2 (hv' r hr)
  refine ⟨hcast, hp, he, ?_⟩
  rw [hp]
  change ((RademacherS5Assembly.pathLaw N) (strictEvent N (K : ℝ))).toReal = _
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [he] with v hv
  first | exact hv | exact propext hv

-- F2: the fixed all-j geometry includes j=0, with no removed initial terms.
theorem cube_geometry :
    StrictMono n ∧
    (∀ j : ℕ,
      2 ≤ k j ∧ 8 ≤ n j ∧ 0 < (k j : ℝ) ∧ 0 < (n j : ℝ) ∧
      0 < Real.sqrt (n j : ℝ) ∧ (Real.sqrt (n j : ℝ)) ^ 2 = (n j : ℝ) ∧
      (n j : ℝ) = (k j : ℝ) ^ 3 ∧ 0 < x j ∧
      x j * Real.sqrt (n j : ℝ) = (k j : ℝ) ∧
      x j = Real.rpow (n j : ℝ) (-((1 : ℝ) / 6)) ∧
      x j = RademacherS5Assembly.x 1 (n j) ∧
      mainRate j = (k j : ℝ)) ∧
    Tendsto mainRate atTop atTop ∧
    Tendsto x atTop (𝓝 (0 : ℝ)) := by
  have hpoint : ∀ j : ℕ,
      2 ≤ k j ∧ 8 ≤ n j ∧ 0 < (k j : ℝ) ∧ 0 < (n j : ℝ) ∧
      0 < Real.sqrt (n j : ℝ) ∧ (Real.sqrt (n j : ℝ)) ^ 2 = (n j : ℝ) ∧
      (n j : ℝ) = (k j : ℝ) ^ 3 ∧ 0 < x j ∧
      x j * Real.sqrt (n j : ℝ) = (k j : ℝ) ∧
      x j = Real.rpow (n j : ℝ) (-((1 : ℝ) / 6)) ∧
      x j = RademacherS5Assembly.x 1 (n j) ∧
      mainRate j = (k j : ℝ) := by
    intro j
    have hkN : 2 ≤ k j := by simp [k]
    have hn8 : 8 ≤ n j := by
      have hh := cube_mono.monotone (Nat.zero_le j)
      simpa [n, k] using hh
    have hk : 0 < (k j : ℝ) := by exact_mod_cast (show 0 < k j by omega)
    have hn : 0 < (n j : ℝ) := by exact_mod_cast (show 0 < n j by omega)
    have hs := Real.sqrt_pos.2 hn
    have hN : (n j : ℝ) = (k j : ℝ) ^ 3 := by simp [n]
    refine ⟨hkN, hn8, hk, hn, hs, Real.sq_sqrt hn.le, hN,
      div_pos hk hs, div_mul_cancel₀ _ hs.ne', ?_, cube_scale_eq j, ?_⟩
    · simpa only [RademacherS5Assembly.x, one_mul] using cube_scale_eq j
    · unfold mainRate
      rw [hN]
      field_simp [hk.ne'] <;> ring
  refine ⟨cube_mono, hpoint, ?_, x_tendsto_zero⟩
  apply k_tendsto_atTop.congr'
  apply Filter.Eventually.of_forall
  intro j
  have hh := hpoint j
  have he : mainRate j = (k j : ℝ) := by aesop
  exact he.symm

-- F3's weak input is exactly S5's perfect-cube sequence shifted by one in Nat.
theorem weak_cube_shift {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    n = RademacherS5Assembly.shift RademacherS5Assembly.cubeSeq 1 ∧
    (∀ j : ℕ,
      n j = RademacherS5Assembly.cubeSeq (j + 1) ∧
      RademacherS5Assembly.height 1 (n j) = (k j : ℝ) ∧
      RademacherS5Assembly.x 1 (n j) = x j ∧
      b B P hB (x j) = RademacherS5Assembly.b B P hB
        (RademacherS5Assembly.x 1 (RademacherS5Assembly.cubeSeq (j + 1))) ∧
      RademacherS5Assembly.p (n j) (k j : ℝ) =
        RademacherS5Assembly.p (RademacherS5Assembly.cubeSeq (j + 1))
          (RademacherS5Assembly.height 1 (RademacherS5Assembly.cubeSeq (j + 1))) ∧
      weakRatio B P hB j =
        RademacherS5Assembly.Q B P hB 1 (RademacherS5Assembly.cubeSeq (j + 1))) := by
  refine ⟨?_, ?_⟩
  · funext j
    simpa only [RademacherS5Assembly.shift, RademacherS4Assembly.shift] using
      cube_index_eq j
  · intro j
    refine ⟨cube_index_eq j, cube_height_eq j, (cube_scale_eq j).symm, ?_, ?_, ?_⟩
    · rw [← cube_index_eq j, ← cube_scale_eq j]
      rfl
    · rw [← cube_index_eq j, cube_height_eq j]
    · unfold weakRatio RademacherS5Assembly.Q
      rw [← cube_index_eq j, cube_height_eq j, ← cube_scale_eq j]
      rfl

-- F1: the original strict self-normalized event and its actual probability
-- are identified on every fixed subsequence index, before any limiting use.
theorem strict_source_bridge {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (j : ℕ) :
    MeasurableSet (strictSelfNormalizedEvent (n j) (x j)) ∧
    MeasurableSet (strictEvent (n j) (k j : ℝ)) ∧
    (∀ᵐ v ∂(RademacherS5Assembly.pathLaw (n j)),
      RademacherS5Assembly.V v = Real.sqrt (n j : ℝ) ∧
      (v ∈ strictSelfNormalizedEvent (n j) (x j) ↔
        v ∈ strictEvent (n j) (k j : ℝ))) ∧
    (RademacherS5Assembly.pathLaw (n j)).real
      (strictSelfNormalizedEvent (n j) (x j)) = strictP (n j) (k j : ℝ) ∧
    sourceRatio B P hB j = strictRatio B P hB j := by
  have hx : x j * Real.sqrt (n j : ℝ) = (k j : ℝ) := by
    have hg := cube_geometry.2.1 j
    aesop
  have he : ∀ᵐ v ∂(RademacherS5Assembly.pathLaw (n j)),
      RademacherS5Assembly.V v = Real.sqrt (n j : ℝ) ∧
      (v ∈ strictSelfNormalizedEvent (n j) (x j) ↔
        v ∈ strictEvent (n j) (k j : ℝ)) := by
    filter_upwards [(actual_path_support (n j)).2.2] with v hv
    have hV := hv.2.2.2
    refine ⟨hV, ?_⟩
    change (∀ r : ℕ, 1 ≤ r → r ≤ n j →
      |Shao.prefixSum v r| < x j * RademacherS5Assembly.V v) ↔ _
    rw [hV, hx]
    rfl
  have hp : (RademacherS5Assembly.pathLaw (n j)).real
      (strictSelfNormalizedEvent (n j) (x j)) = strictP (n j) (k j : ℝ) := by
    change ((RademacherS5Assembly.pathLaw (n j))
      (strictSelfNormalizedEvent (n j) (x j))).toReal = _
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [he] with v hv
    first | exact hv.2 | exact propext hv.2
  refine ⟨(measurable_events (n j) (k j : ℝ) (x j)).2.2,
    (measurable_events (n j) (k j : ℝ) (x j)).1, he, hp, ?_⟩
  unfold sourceRatio strictRatio
  rw [hp]

-- F2: positivity and the ordinary logarithm meanings are conclusions only.
private lemma eventually_positive_of_limit {f : ℕ → ℝ} {L : ℝ}
    (hL : 0 < L) (hf : Tendsto f atTop (𝓝 L)) :
    ∀ᶠ j in atTop, 0 < f j := by
  rcases Metric.tendsto_atTop.1 hf (L / 2) (half_pos hL) with ⟨J, hJ⟩
  filter_upwards [eventually_ge_atTop J] with j hj
  have hd : |f j - L| < L / 2 := by
    simpa only [Real.dist_eq] using hJ j hj
  linarith [(abs_lt.1 hd).1]

private lemma y_geometry (j : ℕ) :
    0 < hSeq j ∧ 0 < ySeq j ∧ ySeq j ≤ x j ∧
    (k j : ℝ) = hSeq j + 1 ∧ (n j : ℝ) = (k j : ℝ) ^ 3 := by
  have hh : 0 < hSeq j := by positivity
  have hN : 0 < (n j : ℝ) := by
    have hp : 0 < n j := by dsimp [n, k]; positivity
    exact_mod_cast hp
  have hs := Real.sqrt_pos.2 hN
  refine ⟨hh, div_pos hh hs, ?_, ?_, ?_⟩
  · exact (div_le_div_iff_of_pos_right hs).2 (by exact_mod_cast (by omega : j + 1 ≤ j + 2))
  · simp [k, Nat.cast_add]
    ring
  · simp [n]

private lemma y_tendsto_zero : Tendsto ySeq atTop (𝓝 (0 : ℝ)) := by
  exact squeeze_zero (fun j => (y_geometry j).2.1.le)
    (fun j => (y_geometry j).2.2.1) x_tendsto_zero

private lemma h_reciprocal_limit :
    Tendsto (fun j : ℕ => (hSeq j)⁻¹) atTop (𝓝 (0 : ℝ)) := by
  exact tendsto_inv_atTop_zero.comp h_tendsto_atTop

private lemma adjacent_scale_limits :
    Tendsto (fun j : ℕ => (n j : ℝ) / (hSeq j) ^ 2) atTop atTop ∧
    Tendsto (fun j : ℕ => (n j : ℝ) / (hSeq j) ^ 3) atTop (𝓝 (1 : ℝ)) ∧
    (∀ j : ℕ, (n j : ℝ) / (hSeq j) ^ 3 ≤ 8) := by
  have hrat : ∀ j : ℕ, (k j : ℝ) / hSeq j = 1 + (hSeq j)⁻¹ := by
    intro j
    have hh := (y_geometry j).1
    rw [(y_geometry j).2.2.2.1]
    field_simp [hh.ne'] <;> ring
  have hscale : ∀ j : ℕ,
      (n j : ℝ) / (hSeq j) ^ 3 = ((k j : ℝ) / hSeq j) ^ 3 := by
    intro j
    rw [(y_geometry j).2.2.2.2, div_pow]
  have hratlim : Tendsto (fun j : ℕ => (k j : ℝ) / hSeq j)
      atTop (𝓝 (1 : ℝ)) := by
    have ht : Tendsto (fun j : ℕ => 1 + (hSeq j)⁻¹) atTop
        (𝓝 ((1 : ℝ) + 0)) := tendsto_const_nhds.add h_reciprocal_limit
    simpa only [add_zero] using
      ht.congr' (Filter.Eventually.of_forall fun j => (hrat j).symm)
  refine ⟨?_, ?_, ?_⟩
  · apply Filter.tendsto_atTop.2
    intro c
    filter_upwards [Filter.tendsto_atTop.1 k_tendsto_atTop c] with j hj
    apply hj.trans
    have hh := (y_geometry j).1
    have hk := (cube_geometry.2.1 j).2.2.1
    have hhk : hSeq j ≤ (k j : ℝ) := by
      rw [(y_geometry j).2.2.2.1]
      linarith
    apply (le_div_iff₀ (sq_pos_of_pos hh)).2
    rw [(y_geometry j).2.2.2.2]
    have hsq : (hSeq j) ^ 2 ≤ (k j : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hhk)
        (show 0 ≤ (k j : ℝ) + hSeq j by positivity)]
    calc
      (k j : ℝ) * (hSeq j) ^ 2 ≤ (k j : ℝ) * (k j : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hk.le
      _ = (k j : ℝ) ^ 3 := by ring
  · have ht := hratlim.pow 3
    simpa only [one_pow] using
      ht.congr' (Filter.Eventually.of_forall fun j => (hscale j).symm)
  · intro j
    have hh : 1 ≤ hSeq j := by
      change (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ)
      exact_mod_cast (show 1 ≤ j + 1 by omega)
    have hrat2 : (k j : ℝ) / hSeq j ≤ 2 := by
      apply (div_le_iff₀ (by positivity : 0 < hSeq j)).2
      rw [(y_geometry j).2.2.2.1]
      linarith
    have hrat0 : 0 ≤ (k j : ℝ) / hSeq j := by positivity
    rw [hscale j]
    have hf : 0 ≤ (2 - (k j : ℝ) / hSeq j) *
        (((k j : ℝ) / hSeq j) ^ 2 + 2 * ((k j : ℝ) / hSeq j) + 4) := by
      apply mul_nonneg (by linarith)
      positivity
    nlinarith [hf]

private lemma adjacent_log_data {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    Tendsto (fun j : ℕ => Real.log
      (RademacherS4Assembly.Q B P hB (n j) (hSeq j))) atTop (𝓝 a) ∧
    (∀ᶠ j in atTop, 0 < RademacherS4Assembly.Q B P hB (n j) (hSeq j)) := by
  have hs := RademacherS4Assembly.S4_ALL B P hB mSeq n hSeq
    (fun j => by omega) (fun _ => le_rfl)
    (fun j => by change hSeq j < hSeq j + 1; linarith) h_tendsto_atTop adjacent_scale_limits.1
    ⟨8, by norm_num, 0, fun j _ => by
      change RademacherS4Assembly.scale3 (n j) (hSeq j) ≤ 8
      have he := RademacherS4Assembly.definition_bridges (mSeq j) (n j) (hSeq j)
      have hsc : RademacherS4Assembly.scale3 (n j) (hSeq j) =
          RademacherS4Assembly.N (n j) / (hSeq j) ^ 3 := by aesop
      rw [hsc]
      exact adjacent_scale_limits.2.2 j⟩
  rcases hs with ⟨_, _, _, _, _, _, _, hlog, _, Kt, Kp, _, _, hp, _⟩
  have hw : ∀ j : ℕ, RademacherS4Assembly.w (mSeq j) (n j) (hSeq j) =
      a * ((n j : ℝ) / (hSeq j) ^ 3) := by
    intro j
    have he := RademacherS4Assembly.definition_bridges (mSeq j) (n j) (hSeq j)
    have hw' : RademacherS4Assembly.w (mSeq j) (n j) (hSeq j) =
        (Real.pi ^ 2 / 4) * (RademacherS4Assembly.N (n j) / (hSeq j) ^ 3) *
          (RademacherS4Assembly.H (mSeq j) - hSeq j) := by aesop
    have hH : RademacherS4Assembly.H (mSeq j) = hSeq j + 1 := he.1
    rw [hw', hH]
    change (Real.pi ^ 2 / 4) * ((n j : ℝ) / (hSeq j) ^ 3) *
      (hSeq j + 1 - hSeq j) = a * ((n j : ℝ) / (hSeq j) ^ 3)
    unfold a
    ring
  have hwlim : Tendsto (fun j : ℕ => RademacherS4Assembly.w
      (mSeq j) (n j) (hSeq j)) atTop (𝓝 a) := by
    have ht : Tendsto (fun j : ℕ => a * ((n j : ℝ) / (hSeq j) ^ 3))
        atTop (𝓝 (a * 1)) := tendsto_const_nhds.mul adjacent_scale_limits.2.1
    simpa only [mul_one] using
      ht.congr' (Filter.Eventually.of_forall fun j => (hw j).symm)
  have hsum := hlog.add hwlim
  refine ⟨?_, ?_⟩
  · convert hsum using 1 <;> simp only [sub_add_cancel, zero_add]
  · filter_upwards [eventually_ge_atTop Kp] with j hj
    have hlegal := (hp j hj).1
    have hq : 0 < RademacherS4Assembly.Q B P hB (n j) (hSeq j) := by
      dsimp [RademacherS4Assembly.ProbabilityLegal] at hlegal
      aesop
    exact hq

private lemma adjacent_ratio_limit {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    Tendsto (fun j : ℕ => RademacherS4Assembly.Q B P hB (n j) (hSeq j))
      atTop (𝓝 (Real.exp a)) := by
  have hd := adjacent_log_data B P hB
  have he := Real.continuous_exp.continuousAt.tendsto.comp hd.1
  exact he.congr' (hd.2.mono fun j hj => Real.exp_log hj)

private lemma brownian_normalized_limit {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (z : ℕ → ℝ)
    (hzpos : ∀ j : ℕ, 0 < z j) (hz : Tendsto z atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun j : ℕ => RademacherS4Assembly.T B P hB (z j))
      atTop (𝓝 (1 : ℝ)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  rcases Shao.Probability.BrownianSup.actual_brownian_firstTerm
      B P hB ε hε with ⟨δ, hδ, hbound⟩
  rcases Metric.tendsto_atTop.1 hz δ hδ with ⟨J, hJ⟩
  refine ⟨J, fun j hj => ?_⟩
  have hzδ : z j < δ := by
    have hd := hJ j hj
    simpa only [Real.dist_eq, sub_zero, abs_of_pos (hzpos j)] using hd
  change |b B P hB (z j) / Shao.Probability.BrownianSup.firstTerm (z j) - 1| < ε
  exact hbound (z j) (hzpos j) hzδ

private lemma brownian_positive_tail {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (z : ℕ → ℝ)
    (hzpos : ∀ j : ℕ, 0 < z j) (hz : Tendsto z atTop (𝓝 (0 : ℝ))) :
    ∀ᶠ j in atTop, 0 < b B P hB (z j) := by
  rcases Shao.Probability.BrownianSup.actual_brownian_eventually_positive
      B P hB with ⟨δ, hδ, hbound⟩
  rcases Metric.tendsto_atTop.1 hz δ hδ with ⟨J, hJ⟩
  filter_upwards [eventually_ge_atTop J] with j hj
  have hzδ : z j < δ := by
    have hd := hJ j hj
    simpa only [Real.dist_eq, sub_zero, abs_of_pos (hzpos j)] using hd
  exact (hbound (z j) (hzpos j) hzδ).1

private lemma inverse_square_shift (j : ℕ) :
    1 / (ySeq j) ^ 2 - 1 / (x j) ^ 2 =
      2 + 3 / hSeq j + 1 / (hSeq j) ^ 2 := by
  have hh := (y_geometry j).1
  have hk : 0 < (k j : ℝ) := by dsimp [k]; positivity
  have hN : 0 ≤ (n j : ℝ) := Nat.cast_nonneg _
  have hy : 1 / (ySeq j) ^ 2 = (n j : ℝ) / (hSeq j) ^ 2 := by
    simp only [div_pow, one_div_div, Real.sq_sqrt hN]
  have hx : 1 / (x j) ^ 2 = (n j : ℝ) / (k j : ℝ) ^ 2 := by
    simp only [x, div_pow, one_div_div, Real.sq_sqrt hN]
  rw [hy, hx, (y_geometry j).2.2.2.2, (y_geometry j).2.2.2.1]
  have hp : hSeq j + 1 ≠ 0 := by positivity
  field_simp [hh.ne', hp] <;> ring

private lemma inverse_square_shift_limit :
    Tendsto (fun j : ℕ => 1 / (ySeq j) ^ 2 - 1 / (x j) ^ 2)
      atTop (𝓝 (2 : ℝ)) := by
  have h3 : Tendsto (fun j : ℕ => 3 / hSeq j) atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul h_reciprocal_limit)
  have h2 : Tendsto (fun j : ℕ => 1 / (hSeq j) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa [one_div, inv_pow] using
      h_reciprocal_limit.pow 2
  have ht : Tendsto (fun j : ℕ => (2 + 3 / hSeq j) + 1 / (hSeq j) ^ 2)
      atTop (𝓝 (((2 : ℝ) + 0) + 0)) := (tendsto_const_nhds.add h3).add h2
  simpa only [zero_add, add_zero] using
    ht.congr' (Filter.Eventually.of_forall fun j => (inverse_square_shift j).symm)

private lemma firstTerm_ratio (u v : ℝ) :
    RademacherS4Assembly.g u / RademacherS4Assembly.g v =
      Real.exp (-(Real.pi ^ 2 / 8) * (1 / u ^ 2 - 1 / v ^ 2)) := by
  change ((4 / Real.pi) * Real.exp (-(Real.pi ^ 2 / 8) / u ^ 2)) /
      ((4 / Real.pi) * Real.exp (-(Real.pi ^ 2 / 8) / v ^ 2)) = _
  have he : -(Real.pi ^ 2 / 8) * (1 / u ^ 2 - 1 / v ^ 2) =
      -(Real.pi ^ 2 / 8) / u ^ 2 - (-(Real.pi ^ 2 / 8) / v ^ 2) := by ring
  rw [he, Real.exp_sub]
  field_simp [Real.pi_ne_zero, Real.exp_ne_zero] <;> ring

private lemma brownian_shift_limit {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    Tendsto (fun j : ℕ => b B P hB (ySeq j) / b B P hB (x j))
      atTop (𝓝 (Real.exp (-a))) := by
  have hxpos : ∀ j : ℕ, 0 < x j := by
    intro j
    have hg := cube_geometry.2.1 j
    aesop
  have htx := brownian_normalized_limit B P hB x hxpos x_tendsto_zero
  have hty := brownian_normalized_limit B P hB ySeq
    (fun j => (y_geometry j).2.1) y_tendsto_zero
  have ht := hty.div htx (by norm_num : (1 : ℝ) ≠ 0)
  have hd : Tendsto (fun j : ℕ =>
      -(Real.pi ^ 2 / 8) * (1 / (ySeq j) ^ 2 - 1 / (x j) ^ 2))
      atTop (𝓝 (-(Real.pi ^ 2 / 8) * (2 : ℝ))) :=
    tendsto_const_nhds.mul inverse_square_shift_limit
  have he := Real.continuous_exp.continuousAt.tendsto.comp hd
  have hprod := ht.mul he
  have hb := brownian_positive_tail B P hB x hxpos x_tendsto_zero
  have heq : (fun j : ℕ =>
      (RademacherS4Assembly.T B P hB (ySeq j) /
        RademacherS4Assembly.T B P hB (x j)) *
        Real.exp (-(Real.pi ^ 2 / 8) * (1 / (ySeq j) ^ 2 - 1 / (x j) ^ 2)))
      =ᶠ[atTop] (fun j : ℕ => b B P hB (ySeq j) / b B P hB (x j)) := by
    filter_upwards [hb] with j hj
    rw [← firstTerm_ratio]
    have hgx : 0 < RademacherS4Assembly.g (x j) := by
      change 0 < (4 / Real.pi) * Real.exp (-(Real.pi ^ 2 / 8) / (x j) ^ 2)
      positivity
    have hgy : 0 < RademacherS4Assembly.g (ySeq j) := by
      change 0 < (4 / Real.pi) * Real.exp (-(Real.pi ^ 2 / 8) / (ySeq j) ^ 2)
      positivity
    change ((b B P hB (ySeq j) / RademacherS4Assembly.g (ySeq j)) /
        (b B P hB (x j) / RademacherS4Assembly.g (x j))) *
        (RademacherS4Assembly.g (ySeq j) / RademacherS4Assembly.g (x j)) = _
    field_simp [hj.ne', hgx.ne', hgy.ne'] <;> ring
  have ha : -(Real.pi ^ 2 / 8) * (2 : ℝ) = -a := by unfold a; ring
  simpa only [one_div_one, one_mul, ha] using hprod.congr' heq

private lemma weak_limit_data {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    Tendsto (weakRatio B P hB) atTop (𝓝 (Real.exp a)) ∧
    Tendsto (fun j : ℕ => Real.log (weakRatio B P hB j)) atTop (𝓝 a) := by
  have hs := RademacherS5Assembly.S5_CUBE B P hB
  have hc : RademacherS5Assembly.coeff 1 = a := by simpa only [a] using hs.1
  have hp := (hs.2.1.2 1).1
  rcases hp with ⟨_, _, hlog, _, hq, _, _⟩
  have heq : (fun j : ℕ => RademacherS5Assembly.Q B P hB 1
      (RademacherS5Assembly.shift RademacherS5Assembly.cubeSeq 1 j))
      =ᶠ[atTop] weakRatio B P hB := by
    apply Filter.Eventually.of_forall
    intro j
    have hh := (weak_cube_shift B P hB).2 j
    have hr : weakRatio B P hB j =
        RademacherS5Assembly.Q B P hB 1 (RademacherS5Assembly.cubeSeq (j + 1)) := by
      aesop
    simpa only [RademacherS5Assembly.shift, RademacherS4Assembly.shift] using hr.symm
  refine ⟨?_, ?_⟩
  · simpa only [hc, mul_one] using hq.congr' heq
  · simpa only [hc, mul_one] using
      hlog.congr' (heq.mono fun j hj => congrArg Real.log hj)

private lemma strict_limit_data {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    Tendsto (strictRatio B P hB) atTop (𝓝 (1 : ℝ)) ∧
    Tendsto (fun j : ℕ => Real.log (strictRatio B P hB j))
      atTop (𝓝 (0 : ℝ)) := by
  have hq := adjacent_ratio_limit B P hB
  have hb := brownian_shift_limit B P hB
  have hprod := hq.mul hb
  have hxpos : ∀ j : ℕ, 0 < x j := by
    intro j
    have hg := cube_geometry.2.1 j
    aesop
  have hpx := brownian_positive_tail B P hB x hxpos x_tendsto_zero
  have hpy := brownian_positive_tail B P hB ySeq
    (fun j => (y_geometry j).2.1) y_tendsto_zero
  have heq : (fun j : ℕ => RademacherS4Assembly.Q B P hB (n j) (hSeq j) *
      (b B P hB (ySeq j) / b B P hB (x j))) =ᶠ[atTop] strictRatio B P hB := by
    filter_upwards [hpx, hpy] with j hjx hjy
    have hk : 2 ≤ k j := by simp [k]
    have hn : k j - 1 = j + 1 := by unfold k; omega
    have hp := (integer_boundary_bridge (n j) (k j) hk).2.2.2
    rw [hn] at hp
    unfold strictRatio
    rw [hp]
    change ((RademacherS5Assembly.p (n j) (hSeq j) / b B P hB (ySeq j)) *
      (b B P hB (ySeq j) / b B P hB (x j))) =
      RademacherS5Assembly.p (n j) (hSeq j) / b B P hB (x j)
    field_simp [hjx.ne', hjy.ne'] <;> ring
  have hlim : Tendsto (strictRatio B P hB) atTop (𝓝 (1 : ℝ)) := by
    have hexp : Real.exp a * Real.exp (-a) = 1 := by
      rw [← Real.exp_add]
      simp
    simpa only [hexp] using hprod.congr' heq
  refine ⟨hlim, ?_⟩
  have hl := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hlim
  simpa only [Function.comp_def, Real.log_one] using hl

theorem common_positive_tail {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → CommonTailAt B P hB j := by
  have hxpos : ∀ j : ℕ, 0 < x j := by
    intro j
    have hg := cube_geometry.2.1 j
    aesop
  have hBpos := brownian_positive_tail B P hB x hxpos x_tendsto_zero
  have hSpos := eventually_positive_of_limit (by norm_num : (0 : ℝ) < 1)
    (strict_limit_data B P hB).1
  have hWpos := eventually_positive_of_limit (Real.exp_pos a) (weak_limit_data B P hB).1
  have hall : ∀ᶠ j in atTop, CommonTailAt B P hB j := by
    filter_upwards [hBpos, hSpos, hWpos] with j hb hs hw
    have hps : 0 < strictP (n j) (k j : ℝ) := by
      have hh := mul_pos hs hb
      rwa [strictRatio, div_mul_cancel₀ _ hb.ne'] at hh
    have hpw : 0 < RademacherS5Assembly.p (n j) (k j : ℝ) := by
      have hh := mul_pos hw hb
      rwa [weakRatio, div_mul_cancel₀ _ hb.ne'] at hh
    have hls : Real.log (strictRatio B P hB j) =
        Real.log (strictP (n j) (k j : ℝ)) - Real.log (b B P hB (x j)) := by
      exact Real.log_div hps.ne' hb.ne'
    have hlw : Real.log (weakRatio B P hB j) =
        Real.log (RademacherS5Assembly.p (n j) (k j : ℝ)) -
          Real.log (b B P hB (x j)) := by
      exact Real.log_div hpw.ne' hb.ne'
    refine ⟨hps, hpw, hb, hs, hw, div_pos hpw hps, hls, hlw, ?_, ?_, ?_⟩
    · unfold weakRatio strictRatio
      field_simp [hb.ne', hps.ne'] <;> ring
    · exact Real.log_div hpw.ne' hps.ne'
    · rw [hlw, hls]
      ring
  exact eventually_atTop.1 hall

theorem F3_STRICT {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    Tendsto (strictRatio B P hB) atTop (𝓝 (1 : ℝ)) ∧
    Tendsto (fun j : ℕ => Real.log (strictRatio B P hB j))
      atTop (𝓝 (0 : ℝ)) := by
  exact strict_limit_data B P hB

theorem F3_WEAK {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    Tendsto (weakRatio B P hB) atTop (𝓝 (Real.exp a)) ∧
    Tendsto (fun j : ℕ => Real.log (weakRatio B P hB j)) atTop (𝓝 a) := by
  exact weak_limit_data B P hB

-- F4: adjacent probabilities use this same time n j and unchanged height k j.
theorem F4_ADJACENT {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    Tendsto (fun j : ℕ =>
      RademacherS5Assembly.p (n j) (k j : ℝ) / strictP (n j) (k j : ℝ))
      atTop (𝓝 (Real.exp a)) ∧
    Tendsto (fun j : ℕ =>
      Real.log (RademacherS5Assembly.p (n j) (k j : ℝ)) -
        Real.log (strictP (n j) (k j : ℝ))) atTop (𝓝 a) := by
  rcases common_positive_tail B P hB with ⟨J, hJ⟩
  have hq := (F3_WEAK B P hB).1.div (F3_STRICT B P hB).1
    (by norm_num : (1 : ℝ) ≠ 0)
  have hl := (F3_WEAK B P hB).2.sub (F3_STRICT B P hB).2
  refine ⟨?_, ?_⟩
  · have he : (fun j : ℕ => weakRatio B P hB j / strictRatio B P hB j)
        =ᶠ[atTop] (fun j : ℕ =>
          RademacherS5Assembly.p (n j) (k j : ℝ) / strictP (n j) (k j : ℝ)) := by
      filter_upwards [eventually_ge_atTop J] with j hj
      rcases hJ j hj with ⟨_, _, _, _, _, _, _, _, hr, _, _⟩
      exact hr.symm
    simpa only [div_one] using hq.congr' he
  · have he : (fun j : ℕ => Real.log (weakRatio B P hB j) -
        Real.log (strictRatio B P hB j)) =ᶠ[atTop] (fun j : ℕ =>
          Real.log (RademacherS5Assembly.p (n j) (k j : ℝ)) -
            Real.log (strictP (n j) (k j : ℝ))) := by
      filter_upwards [eventually_ge_atTop J] with j hj
      rcases hJ j hj with ⟨_, _, _, _, _, _, _, _, _, _, hr⟩
      exact hr.symm
    simpa only [sub_zero] using hl.congr' he

theorem F4_NORMALIZED {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    Tendsto (fun j : ℕ => Real.log (strictRatio B P hB j) / mainRate j)
      atTop (𝓝 (0 : ℝ)) ∧
    Tendsto (fun j : ℕ => Real.log (weakRatio B P hB j) / mainRate j)
      atTop (𝓝 (0 : ℝ)) := by
  have hi := tendsto_inv_atTop_zero.comp cube_geometry.2.2.1
  have hs := (F3_STRICT B P hB).2.mul hi
  have hw := (F3_WEAK B P hB).2.mul hi
  constructor
  · simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using hs
  · simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using hw

end Shao.OQ4.RademacherStrictCube

end
