import Shao.C2.HalfLinePhysicalGaussian
import Shao.C2.BridgeDomination

noncomputable section
namespace Shao.C2.SourceHalfLineCompletion
open MeasureTheory Set
open Shao.C2.BridgeDomination Shao.C2.HalfLineReflectionFormula

def sourceUpperCompletion (ν : Measure BridgeNoise) (a y T z : ℝ) : ℝ :=
  if 0 < a then
    if 0 < T then Shao.C2.BridgeDomination.upperCompletion ν a y T z
    else if T = 0 ∧ y = z ∧ y < a then 1 else 0
  else 0

def sourceLowerCompletion (ν : Measure BridgeNoise) (a y T z : ℝ) : ℝ :=
  if 0 < a then
    if 0 < T then Shao.C2.BridgeDomination.lowerCompletion ν a y T z
    else if T = 0 ∧ y = z ∧ -a < y then 1 else 0
  else 0

theorem sourceHalfLineCompletion_nonpositive_wall (ν : Measure BridgeNoise)
    (a y T z : ℝ) (ha : a ≤ 0) :
    sourceUpperCompletion ν a y T z = 0 ∧ sourceLowerCompletion ν a y T z = 0 := by
  simp [sourceUpperCompletion, sourceLowerCompletion, not_lt.mpr ha]

theorem sourceUpperCompletion_reachable_zero (ν : Measure BridgeNoise) (a y : ℝ)
    (ha : 0 < a) :
    sourceUpperCompletion ν a y 0 y = if y < a then 1 else 0 := by
  simp [sourceUpperCompletion, ha]

theorem sourceLowerCompletion_reachable_zero (ν : Measure BridgeNoise) (a y : ℝ)
    (ha : 0 < a) :
    sourceLowerCompletion ν a y 0 y = if -a < y then 1 else 0 := by
  simp [sourceLowerCompletion, ha]

theorem sourceUpperCompletion_bounds (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (a y T z : ℝ) :
    0 ≤ sourceUpperCompletion ν a y T z ∧ sourceUpperCompletion ν a y T z ≤ 1 := by
  unfold sourceUpperCompletion
  split_ifs
  · have h := completion_bounds ν a y T z
    exact ⟨h.1, h.2.1⟩
  all_goals norm_num

theorem sourceLowerCompletion_bounds (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (a y T z : ℝ) :
    0 ≤ sourceLowerCompletion ν a y T z ∧ sourceLowerCompletion ν a y T z ≤ 1 := by
  unfold sourceLowerCompletion
  split_ifs
  · have h := completion_bounds ν a y T z
    exact ⟨h.2.2.1, h.2.2.2.1⟩
  all_goals norm_num

theorem sourceUpperCompletion_exterior (ν : Measure BridgeNoise) (a y T z : ℝ)
    (h : ¬ (y < a ∧ z < a)) : sourceUpperCompletion ν a y T z = 0 := by
  have he : strictUpper a y T z = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro g hg
    have hp := bridgePath_endpoints y T z g
    apply h
    exact ⟨by simpa only [hp.1] using hg 0, by simpa only [hp.2] using hg 1⟩
  unfold sourceUpperCompletion
  split_ifs with ha hT hZ
  · simp [Shao.C2.BridgeDomination.upperCompletion, he]
  · exact False.elim (h ⟨hZ.2.2, hZ.2.1 ▸ hZ.2.2⟩)
  · rfl
  · rfl

theorem sourceLowerCompletion_exterior (ν : Measure BridgeNoise) (a y T z : ℝ)
    (h : ¬ (-a < y ∧ -a < z)) : sourceLowerCompletion ν a y T z = 0 := by
  have he : strictLower a y T z = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro g hg
    have hp := bridgePath_endpoints y T z g
    apply h
    exact ⟨by simpa only [hp.1] using hg 0, by simpa only [hp.2] using hg 1⟩
  unfold sourceLowerCompletion
  split_ifs with ha hT hZ
  · simp [Shao.C2.BridgeDomination.lowerCompletion, he]
  · exact False.elim (h ⟨hZ.2.2, hZ.2.1 ▸ hZ.2.2⟩)
  · rfl
  · rfl

theorem sourceUpperCompletion_eq_scalar_of_reflection (ν : Measure BridgeNoise)
    (a z : ℝ) (ha : 0 < a) (hz : z < a)
    (hReflection : ∀ T : ℝ, 0 < T → ∀ y : ℝ, y < a →
      Shao.C2.BridgeDomination.upperCompletion ν a y T z = upperReflection a y T z) :
    (fun y T => sourceUpperCompletion ν a y T z) =
      (fun y T => Shao.C2.HalfLinePhysicalGaussian.upperCompletion a y T z) := by
  funext y T
  by_cases hy : y < a
  · have hu : 0 < a - y := sub_pos.mpr hy
    have hv : 0 < a - z := sub_pos.mpr hz
    by_cases ht : 0 < T
    · rw [sourceUpperCompletion, if_pos ha, if_pos ht, hReflection T ht y hy]
      rw [Shao.C2.HalfLinePhysicalGaussian.upperCompletion,
        Shao.C2.HalfLineGaussianStep.completion_positive_time (a - y) (a - z) T hu.le hv ht]
      rfl
    · have hd : (a - y = a - z) = (y = z) := by
        apply propext
        constructor <;> intro h <;> linarith only [h]
      simp [sourceUpperCompletion, Shao.C2.HalfLinePhysicalGaussian.upperCompletion,
        Shao.C2.HalfLineGaussianStep.completion, ha, hy, hu, hv, ht, hd]
  · rw [sourceUpperCompletion_exterior ν a y T z (by intro h; exact hy h.1)]
    have hu : ¬0 < a - y := by linarith only [hy]
    simp [Shao.C2.HalfLinePhysicalGaussian.upperCompletion,
      Shao.C2.HalfLineGaussianStep.completion, hu]

theorem sourceLowerCompletion_eq_scalar_of_reflection (ν : Measure BridgeNoise)
    (a z : ℝ) (ha : 0 < a) (hz : -a < z)
    (hReflection : ∀ T : ℝ, 0 < T → ∀ y : ℝ, -a < y →
      Shao.C2.BridgeDomination.lowerCompletion ν a y T z = lowerReflection a y T z) :
    (fun y T => sourceLowerCompletion ν a y T z) =
      (fun y T => Shao.C2.HalfLinePhysicalGaussian.lowerCompletion a y T z) := by
  funext y T
  by_cases hy : -a < y
  · have hu : 0 < a + y := by linarith only [hy]
    have hv : 0 < a + z := by linarith only [hz]
    by_cases ht : 0 < T
    · rw [sourceLowerCompletion, if_pos ha, if_pos ht, hReflection T ht y hy]
      rw [Shao.C2.HalfLinePhysicalGaussian.lowerCompletion,
        Shao.C2.HalfLineGaussianStep.completion_positive_time (a + y) (a + z) T hu.le hv ht]
      rfl
    · have hd : (a + y = a + z) = (y = z) := by
        apply propext
        constructor <;> intro h <;> linarith only [h]
      simp [sourceLowerCompletion, Shao.C2.HalfLinePhysicalGaussian.lowerCompletion,
        Shao.C2.HalfLineGaussianStep.completion, ha, hy, hu, hv, ht, hd]
  · rw [sourceLowerCompletion_exterior ν a y T z (by intro h; exact hy h.1)]
    have hu : ¬0 < a + y := by linarith only [hy]
    simp [Shao.C2.HalfLinePhysicalGaussian.lowerCompletion,
      Shao.C2.HalfLineGaussianStep.completion, hu]

theorem actual_upper_retained_bound_of_reflection (ν : Measure BridgeNoise)
    (a y T z b : ℝ) (ha : 0 < a) (hy : y < a) (hz : z < a) (hT : 0 < T)
    (hb : b ^ 2 ≤ T) (hzero : T - b ^ 2 = 0 → y + b = z)
    (hReflection : ∀ S : ℝ, 0 < S → ∀ w : ℝ, w < a →
      Shao.C2.BridgeDomination.upperCompletion ν a w S z = upperReflection a w S z) :
    let F := fun w S : ℝ => sourceUpperCompletion ν a w S z
    let R := fun β : ℝ => F (y + β) (T - β ^ 2) - F y T -
      (β - β ^ 2 * (z - y) / T) * deriv (fun w => F w T) y
    |if b ^ 2 ≤ T / 2 ∧ a ≤ y + b then R (a - y) else R b| ≤
      8000100 * (|b| / Real.sqrt T) ^ 3 * (1 + |z - y| / Real.sqrt T) ^ 3 *
        Real.exp (-((max (a - y - (|b| + max (z - y) 0)) 0) ^ 2) / T) := by
  have hF := sourceUpperCompletion_eq_scalar_of_reflection ν a z ha hz hReflection
  have hp (w S : ℝ) : sourceUpperCompletion ν a w S z =
      Shao.C2.HalfLinePhysicalGaussian.upperCompletion a w S z :=
    congrFun (congrFun hF w) S
  dsimp only
  simp only [hp]
  exact Shao.C2.HalfLinePhysicalGaussian.upper_retained_gaussian_bound a y T z b ha hy hz hT hb hzero

theorem actual_lower_retained_bound_of_reflection (ν : Measure BridgeNoise)
    (a y T z b : ℝ) (ha : 0 < a) (hy : -a < y) (hz : -a < z) (hT : 0 < T)
    (hb : b ^ 2 ≤ T) (hzero : T - b ^ 2 = 0 → y + b = z)
    (hReflection : ∀ S : ℝ, 0 < S → ∀ w : ℝ, -a < w →
      Shao.C2.BridgeDomination.lowerCompletion ν a w S z = lowerReflection a w S z) :
    let F := fun w S : ℝ => sourceLowerCompletion ν a w S z
    let R := fun β : ℝ => F (y + β) (T - β ^ 2) - F y T -
      (β - β ^ 2 * (z - y) / T) * deriv (fun w => F w T) y
    |if b ^ 2 ≤ T / 2 ∧ y + b ≤ -a then R (-a - y) else R b| ≤
      8000100 * (|b| / Real.sqrt T) ^ 3 * (1 + |z - y| / Real.sqrt T) ^ 3 *
        Real.exp (-((max (a + y - (|b| + max (y - z) 0)) 0) ^ 2) / T) := by
  have hF := sourceLowerCompletion_eq_scalar_of_reflection ν a z ha hz hReflection
  have hp (w S : ℝ) : sourceLowerCompletion ν a w S z =
      Shao.C2.HalfLinePhysicalGaussian.lowerCompletion a w S z :=
    congrFun (congrFun hF w) S
  dsimp only
  simp only [hp]
  exact Shao.C2.HalfLinePhysicalGaussian.lower_retained_gaussian_bound a y T z b ha hy hz hT hb hzero

end Shao.C2.SourceHalfLineCompletion
