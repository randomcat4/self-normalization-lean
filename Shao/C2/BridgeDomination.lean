import Mathlib.Topology.UnitInterval
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.EMetricSpace.BoundedVariation

noncomputable section
namespace Shao.C2.BridgeDomination
open MeasureTheory Set
open scoped BigOperators ENNReal

abbrev BridgeTime := unitInterval
abbrev BridgeNoise := {g : C(BridgeTime, ℝ) // g 0 = 0 ∧ g 1 = 0}

def bridgePath (y T z : ℝ) (g : BridgeNoise) : C(BridgeTime, ℝ) :=
  ⟨fun t => (1 - (t : ℝ)) * y + (t : ℝ) * z + Real.sqrt T * g.val t,
    by fun_prop⟩

def strictUpper (a y T z : ℝ) : Set BridgeNoise :=
  {g | ∀ t : BridgeTime, bridgePath y T z g t < a}

def strictLower (a y T z : ℝ) : Set BridgeNoise :=
  {g | ∀ t : BridgeTime, -a < bridgePath y T z g t}

def strictInterval (a y T z : ℝ) : Set BridgeNoise :=
  strictUpper a y T z ∩ strictLower a y T z

def upperCompletion (P : Measure BridgeNoise) (a y T z : ℝ) : ℝ :=
  P.real (strictUpper a y T z)

def lowerCompletion (P : Measure BridgeNoise) (a y T z : ℝ) : ℝ :=
  P.real (strictLower a y T z)

def intervalCompletion (P : Measure BridgeNoise) (a y T z : ℝ) : ℝ :=
  P.real (strictInterval a y T z)

theorem bridgePath_endpoints (y T z : ℝ) (g : BridgeNoise) :
    bridgePath y T z g 0 = y ∧ bridgePath y T z g 1 = z := by
  simp [bridgePath, g.property.1, g.property.2]

theorem bridgePath_mono (y y' T z z' : ℝ) (hyy : y ≤ y') (hzz : z ≤ z')
    (g : BridgeNoise) (t : BridgeTime) :
    bridgePath y T z g t ≤ bridgePath y' T z' g t := by
  exact add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left hyy (sub_nonneg.mpr t.property.2))
      (mul_le_mul_of_nonneg_left hzz t.property.1)) le_rfl

theorem measurableSet_strictUpper (a y T z : ℝ) :
    MeasurableSet (strictUpper a y T z) := by
  have hc : Continuous (fun g : BridgeNoise => bridgePath y T z g) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : BridgeNoise × BridgeTime =>
      (1 - (p.2 : ℝ)) * y + (p.2 : ℝ) * z + Real.sqrt T * p.1.val p.2)
    fun_prop
  have ho := ContinuousMap.isOpen_setOfPred_mapsTo
    (X := BridgeTime) isCompact_univ (isOpen_Iio (a := a))
  simpa [strictUpper, Set.MapsTo] using (ho.preimage hc).measurableSet

theorem measurableSet_strictLower (a y T z : ℝ) :
    MeasurableSet (strictLower a y T z) := by
  have hc : Continuous (fun g : BridgeNoise => bridgePath y T z g) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : BridgeNoise × BridgeTime =>
      (1 - (p.2 : ℝ)) * y + (p.2 : ℝ) * z + Real.sqrt T * p.1.val p.2)
    fun_prop
  have ho := ContinuousMap.isOpen_setOfPred_mapsTo
    (X := BridgeTime) isCompact_univ (isOpen_Ioi (a := -a))
  simpa [strictLower, Set.MapsTo] using (ho.preimage hc).measurableSet

theorem measurableSet_strictInterval (a y T z : ℝ) :
    MeasurableSet (strictInterval a y T z) := by
  exact (measurableSet_strictUpper a y T z).inter (measurableSet_strictLower a y T z)

theorem strictInterval_zero_time (a y z : ℝ) :
    strictInterval a y 0 z =
      if -a < y ∧ y < a ∧ -a < z ∧ z < a then Set.univ else ∅ := by
  classical
  ext g
  split_ifs with h
  · simp only [Set.mem_univ, iff_true]
    rcases h with ⟨hly, huy, hlz, huz⟩
    have hp (t : BridgeTime) : -a < bridgePath y 0 z g t ∧
        bridgePath y 0 z g t < a := by
      change -a < (1 - (t : ℝ)) * y + (t : ℝ) * z + Real.sqrt 0 * g.val t ∧
        (1 - (t : ℝ)) * y + (t : ℝ) * z + Real.sqrt 0 * g.val t < a
      simp only [Real.sqrt_zero, zero_mul, add_zero]
      have h1 := mul_le_mul_of_nonneg_left (le_max_left y z)
        (sub_nonneg.mpr t.property.2)
      have h2 := mul_le_mul_of_nonneg_left (le_max_right y z) t.property.1
      have h3 := mul_le_mul_of_nonneg_left (min_le_left y z)
        (sub_nonneg.mpr t.property.2)
      have h4 := mul_le_mul_of_nonneg_left (min_le_right y z) t.property.1
      have hmax : max y z < a := max_lt huy huz
      have hmin : -a < min y z := lt_min hly hlz
      constructor <;> nlinarith
    exact ⟨fun t => (hp t).2, fun t => (hp t).1⟩
  · simp only [Set.mem_empty_iff_false, iff_false]
    intro hg
    apply h
    have hy := bridgePath_endpoints y 0 z g
    exact ⟨by simpa [hy.1] using hg.2 0, by simpa [hy.1] using hg.1 0,
      by simpa [hy.2] using hg.2 1, by simpa [hy.2] using hg.1 1⟩

theorem strictInterval_exterior (a y T z : ℝ)
    (h : y ≤ -a ∨ a ≤ y ∨ z ≤ -a ∨ a ≤ z) :
    strictInterval a y T z = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro g hg
  have hy := bridgePath_endpoints y T z g
  have hly : -a < y := by simpa [hy.1] using hg.2 0
  have huy : y < a := by simpa [hy.1] using hg.1 0
  have hlz : -a < z := by simpa [hy.2] using hg.2 1
  have huz : z < a := by simpa [hy.2] using hg.1 1
  rcases h with h | h | h | h <;> linarith

theorem completion_bounds (P : Measure BridgeNoise) [IsProbabilityMeasure P]
    (a y T z : ℝ) :
    0 ≤ upperCompletion P a y T z ∧ upperCompletion P a y T z ≤ 1 ∧
    0 ≤ lowerCompletion P a y T z ∧ lowerCompletion P a y T z ≤ 1 ∧
    0 ≤ intervalCompletion P a y T z ∧ intervalCompletion P a y T z ≤ 1 := by
  have hb (s : Set BridgeNoise) : P.real s ≤ 1 := by
    calc
      P.real s ≤ P.real Set.univ := measureReal_mono (Set.subset_univ s)
      _ = 1 := probReal_univ
  exact ⟨measureReal_nonneg, hb _, measureReal_nonneg, hb _, measureReal_nonneg, hb _⟩

theorem upper_deficit_eq (P : Measure BridgeNoise) [IsProbabilityMeasure P]
    (a y T z : ℝ) :
    upperCompletion P a y T z - intervalCompletion P a y T z =
      P.real (strictUpper a y T z \ strictLower a y T z) := by
  have h := measureReal_inter_add_sdiff (μ := P) (s := strictUpper a y T z)
    (measurableSet_strictLower a y T z)
  change P.real (strictUpper a y T z) -
    P.real (strictUpper a y T z ∩ strictLower a y T z) = _
  linarith

theorem lower_deficit_eq (P : Measure BridgeNoise) [IsProbabilityMeasure P]
    (a y T z : ℝ) :
    lowerCompletion P a y T z - intervalCompletion P a y T z =
      P.real (strictLower a y T z \ strictUpper a y T z) := by
  have h := measureReal_inter_add_sdiff (μ := P) (s := strictLower a y T z)
    (measurableSet_strictUpper a y T z)
  change P.real (strictLower a y T z) -
    P.real (strictUpper a y T z ∩ strictLower a y T z) = _
  rw [Set.inter_comm] at h
  linarith

theorem upper_deficit_antitone (P : Measure BridgeNoise) [IsProbabilityMeasure P]
    (a y y' T z z' : ℝ) (hyy : y ≤ y') (hzz : z ≤ z') :
    upperCompletion P a y' T z' - intervalCompletion P a y' T z' ≤
      upperCompletion P a y T z - intervalCompletion P a y T z := by
  rw [upper_deficit_eq, upper_deficit_eq]
  refine measureReal_mono ?_ (by finiteness)
  intro g hg
  refine ⟨fun t => (bridgePath_mono y y' T z z' hyy hzz g t).trans_lt (hg.1 t), ?_⟩
  intro hl
  exact hg.2 (fun t => (hl t).trans_le (bridgePath_mono y y' T z z' hyy hzz g t))

theorem lower_deficit_monotone (P : Measure BridgeNoise) [IsProbabilityMeasure P]
    (a y y' T z z' : ℝ) (hyy : y ≤ y') (hzz : z ≤ z') :
    lowerCompletion P a y T z - intervalCompletion P a y T z ≤
      lowerCompletion P a y' T z' - intervalCompletion P a y' T z' := by
  rw [lower_deficit_eq, lower_deficit_eq]
  refine measureReal_mono ?_ (by finiteness)
  intro g hg
  refine ⟨fun t => (hg.1 t).trans_le (bridgePath_mono y y' T z z' hyy hzz g t), ?_⟩
  intro hu
  exact hg.2 (fun t => (bridgePath_mono y y' T z z' hyy hzz g t).trans_lt (hu t))

theorem signed_derivative_domination_of_hasDerivAt
    (P : Measure BridgeNoise) [IsProbabilityMeasure P]
    (a y T z du di dl : ℝ)
    (hu : HasDerivAt (fun s => upperCompletion P a s T z) du y)
    (hi : HasDerivAt (fun s => intervalCompletion P a s T z) di y)
    (hl : HasDerivAt (fun s => lowerCompletion P a s T z) dl y) :
    du ≤ di ∧ di ≤ dl := by
  have hupper : Antitone (fun s => upperCompletion P a s T z -
      intervalCompletion P a s T z) := fun x x' hxx =>
    upper_deficit_antitone P a x x' T z z hxx le_rfl
  have hlower : Monotone (fun s => lowerCompletion P a s T z -
      intervalCompletion P a s T z) := fun x x' hxx =>
    lower_deficit_monotone P a x x' T z z hxx le_rfl
  have h1 := (hu.sub hi).nonpos_of_antitone hupper
  have h2 := (hl.sub hi).nonneg_of_monotone hlower
  constructor <;> linarith

private theorem variation_le_two_of_antitone_difference
    (f u v : ℝ → ℝ) (hu : Antitone u) (hv : Antitone v)
    (hu0 : ∀ w, 0 ≤ u w) (hu1 : ∀ w, u w ≤ 1)
    (hv0 : ∀ w, 0 ≤ v w) (hv1 : ∀ w, v w ≤ 1)
    (h : ∀ w, f w = u w - v w) :
    eVariationOn f Set.univ ≤ 2 := by
  apply iSup_le
  rintro ⟨n, w, hw, hmem⟩
  have ht (k : ℝ → ℝ) (m : ℕ) :
      (∑ i ∈ Finset.range m, (k (w i) - k (w (i + 1)))) = k (w 0) - k (w m) := by
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; ring
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        ENNReal.ofReal ((u (w i) - u (w (i + 1))) + (v (w i) - v (w (i + 1)))) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [edist_dist, Real.dist_eq, h, h]
      apply ENNReal.ofReal_le_ofReal
      apply abs_le.mpr
      have h1 := hu (hw (Nat.le_succ i))
      have h2 := hv (hw (Nat.le_succ i))
      constructor <;> linarith
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n,
        ((u (w i) - u (w (i + 1))) + (v (w i) - v (w (i + 1))))) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro i hi
      exact add_nonneg (sub_nonneg.mpr (hu (hw (Nat.le_succ i))))
        (sub_nonneg.mpr (hv (hw (Nat.le_succ i))))
    _ = ENNReal.ofReal ((u (w 0) - u (w n)) + (v (w 0) - v (w n))) := by
      rw [Finset.sum_add_distrib, ht, ht]
    _ ≤ 2 := by
      have hb : (u (w 0) - u (w n)) + (v (w 0) - v (w n)) ≤ 2 := by
        linarith [hu1 (w 0), hv1 (w 0), hu0 (w n), hv0 (w n)]
      simpa using ENNReal.ofReal_le_ofReal hb

theorem initial_interval_variation (P : Measure BridgeNoise) [IsProbabilityMeasure P]
    (a : ℝ) :
    eVariationOn (fun w : ℝ => intervalCompletion P a 0 1 w) Set.univ ≤ 2 := by
  let u : ℝ → ℝ := fun w => upperCompletion P a 0 1 w
  let v : ℝ → ℝ := fun w => upperCompletion P a 0 1 w - intervalCompletion P a 0 1 w
  have hu : Antitone u := by
    intro w w' hww
    refine measureReal_mono ?_ (by finiteness)
    intro g hg t
    exact (bridgePath_mono 0 0 1 w w' le_rfl hww g t).trans_lt (hg t)
  have hv : Antitone v := fun w w' hww =>
    upper_deficit_antitone P a 0 0 1 w w' le_rfl hww
  have hv0 (w : ℝ) : 0 ≤ v w := by
    dsimp [v]
    rw [upper_deficit_eq]
    exact measureReal_nonneg
  have hv1 (w : ℝ) : v w ≤ 1 := by
    dsimp [v]
    rw [upper_deficit_eq]
    calc
      _ ≤ P.real Set.univ := measureReal_mono (Set.subset_univ _)
      _ = 1 := probReal_univ
  apply variation_le_two_of_antitone_difference _ u v hu hv
    (fun w => (completion_bounds P a 0 1 w).1)
    (fun w => (completion_bounds P a 0 1 w).2.1) hv0 hv1
  intro w
  dsimp [u, v]
  ring

end Shao.C2.BridgeDomination
