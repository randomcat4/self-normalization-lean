import Shao.C1.Normalization
import Shao.C2.TwoSided
import Mathlib.Tactic.NormNum

/-!
# Boundary certificates for the finite-path conventions
These cover a single monitored time, all-zero paths, zero and positive
thresholds, equality hits, a negative threshold, and sign-sensitive maxima.
-/

namespace Shao.Checks

variable {n : ℕ}

def singletonPath (z : ℝ) : Path 1 := fun _ => z

theorem singletonPath_energy (z : ℝ) :
    energy (singletonPath z) = z ^ 2 := by
  simpa only [singletonPath] using energy_one (singletonPath z)

theorem singletonPath_prefixSum (z : ℝ) :
    prefixSum (singletonPath z) 1 = z := by
  simpa only [singletonPath] using prefixSum_one (singletonPath z)

theorem singletonPath_upperMax (z : ℝ) :
    upperMax (singletonPath z) (by decide) = z := by
  simpa only [singletonPath] using upperMax_one (singletonPath z)

theorem neg_singletonPath (z : ℝ) :
    -singletonPath z = singletonPath (-z) := by
  rfl

theorem singletonPath_lowerMax (z : ℝ) :
    lowerMax (singletonPath z) (by decide) = -z := by
  change upperMax (-singletonPath z) (by decide) = -z
  rw [neg_singletonPath, singletonPath_upperMax]

theorem zeroPath_energy (n : ℕ) : energy (0 : Path n) = 0 := by
  exact (energy_eq_zero_iff (0 : Path n)).2 (fun _ => rfl)

theorem zeroPath_weak_crossings (hn : 0 < n) (x : ℝ) :
    (0 : Path n) ∈ upperCrossing hn x ∧
    (0 : Path n) ∈ lowerCrossing hn x ∧
    (0 : Path n) ∈ absoluteCrossing hn x ∧
    (0 : Path n) ∈ C2.doubleCrossing hn x := by
  have hQ := zeroPath_energy n
  exact ⟨mem_upperCrossing_of_energy_eq_zero _ hn x hQ,
    mem_lowerCrossing_of_energy_eq_zero _ hn x hQ,
    C2.mem_absoluteCrossing_of_energy_eq_zero _ hn x hQ,
    C2.mem_doubleCrossing_of_energy_eq_zero _ hn x hQ⟩

theorem zeroPath_no_strict_survival (hn : 0 < n) (x : ℝ) :
    (0 : Path n) ∉ upperStrictSurvival hn x ∧
    (0 : Path n) ∉ lowerStrictSurvival hn x ∧
    (0 : Path n) ∉ absoluteStrictSurvival hn x := by
  have hQ := zeroPath_energy n
  refine ⟨not_mem_upperStrictSurvival_of_energy_eq_zero _ hn x hQ,
    not_mem_lowerStrictSurvival_of_energy_eq_zero _ hn x hQ,
    ?_⟩
  change ¬ absMax (0 : Path n) hn < x * Real.sqrt (energy (0 : Path n))
  have hcross := C2.mem_absoluteCrossing_of_energy_eq_zero (0 : Path n) hn x hQ
  change x * Real.sqrt (energy (0 : Path n)) ≤ absMax (0 : Path n) hn at hcross
  exact not_lt_of_ge hcross

theorem zeroPath_normalizedEndpoint (n : ℕ) :
    C1.normalizedEndpoint (0 : Path n) = 0 := by
  exact C1.normalizedEndpoint_of_energy_eq_zero _ (zeroPath_energy n)

theorem zeroPath_upperNormalizedCDF (hn : 0 < n) (t : ℝ) :
    (0 : Path n) ∈ C1.upperNormalizedCDF hn t ↔ 0 < t := by
  simp [C1.upperNormalizedCDF, C1.normalizedUpperMax, zeroPath_energy]

theorem zeroPath_positive_CDF_difference (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    (0 : Path n) ∈ C1.upperNormalizedCDF hn t ∧
    (0 : Path n) ∉ upperStrictSurvival hn t := by
  exact ⟨(zeroPath_upperNormalizedCDF hn t).2 ht,
    not_mem_upperStrictSurvival_of_energy_eq_zero _ hn t (zeroPath_energy n)⟩

theorem singleton_positive_equality_hit :
    singletonPath 1 ∈ upperCrossing (by decide) 1 ∧
    singletonPath 1 ∉ upperStrictSurvival (by decide) 1 := by
  norm_num [upperCrossing, upperStrictSurvival,
    singletonPath_energy, singletonPath_upperMax, singletonPath]

theorem singleton_positive_strictly_above {x : ℝ} (hx : 1 < x) :
    singletonPath 1 ∉ upperCrossing (by decide) x ∧
    singletonPath 1 ∈ upperStrictSurvival (by decide) x := by
  constructor
  · change ¬ x * Real.sqrt (energy (singletonPath 1)) ≤
      upperMax (singletonPath 1) (by decide)
    simpa [singletonPath_energy, singletonPath_upperMax, singletonPath] using not_le_of_gt hx
  · change upperMax (singletonPath 1) (by decide) <
      x * Real.sqrt (energy (singletonPath 1))
    simpa [singletonPath_energy, singletonPath_upperMax, singletonPath] using hx

theorem singleton_negative_zero_threshold :
    singletonPath (-1) ∉ upperCrossing (by decide) 0 ∧
    singletonPath (-1) ∈ upperStrictSurvival (by decide) 0 ∧
    singletonPath (-1) ∈ absoluteCrossing (by decide) 0 ∧
    singletonPath (-1) ∉ C2.doubleCrossing (by decide) 0 := by
  norm_num [upperCrossing, lowerCrossing, upperStrictSurvival,
    absoluteCrossing, absMax, C2.doubleCrossing,
    singletonPath_energy, singletonPath_upperMax, singletonPath_lowerMax,
    singletonPath]

theorem singleton_negative_timeZero_changes_event :
    singletonPath (-1) ∈ upperStrictSurvival (by decide) 0 ∧
    ¬ maxWithZero (singletonPath (-1)) < 0 := by
  norm_num [upperStrictSurvival,
    maxWithZero_eq (singletonPath (-1)) (by decide),
    singletonPath_energy, singletonPath_upperMax, singletonPath]

theorem singleton_negative_threshold_equality :
    singletonPath (-1) ∈ upperCrossing (by decide) (-1) := by
  norm_num [upperCrossing, singletonPath_energy, singletonPath_upperMax,
    singletonPath]

end Shao.Checks

