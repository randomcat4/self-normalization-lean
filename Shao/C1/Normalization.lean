import Shao.Basic.Events

/-!
# Zero energy and positive-threshold strict CDF events
These are deterministic sets of finite paths. Probability measures and
distributional comparisons are separate interfaces.
-/

noncomputable section

namespace Shao.C1

variable {n : ℕ}

def normalizedEndpoint (a : Path n) : ℝ :=
  if energy a = 0 then 0 else prefixSum a n / Real.sqrt (energy a)

def normalizedUpperMax (a : Path n) (hn : 0 < n) : ℝ :=
  if energy a = 0 then 0 else upperMax a hn / Real.sqrt (energy a)

def upperNormalizedCDF (hn : 0 < n) (t : ℝ) : Set (Path n) :=
  {a | normalizedUpperMax a hn < t}

def endpointRawCDF (t : ℝ) : Set (Path n) :=
  {a | |prefixSum a n| < t * Real.sqrt (energy a)}

def endpointNormalizedCDF (t : ℝ) : Set (Path n) :=
  {a | |normalizedEndpoint a| < t}

@[simp] theorem normalizedEndpoint_of_energy_eq_zero (a : Path n)
    (hQ : energy a = 0) : normalizedEndpoint a = 0 := by
  simp [normalizedEndpoint, hQ]

@[simp] theorem normalizedUpperMax_of_energy_eq_zero (a : Path n)
    (hn : 0 < n) (hQ : energy a = 0) : normalizedUpperMax a hn = 0 := by
  simp [normalizedUpperMax, hQ]

theorem normalizedEndpoint_of_energy_pos (a : Path n) (hQ : 0 < energy a) :
    normalizedEndpoint a = prefixSum a n / Real.sqrt (energy a) := by
  simp [normalizedEndpoint, ne_of_gt hQ]

theorem normalizedUpperMax_of_energy_pos (a : Path n) (hn : 0 < n)
    (hQ : 0 < energy a) :
    normalizedUpperMax a hn = upperMax a hn / Real.sqrt (energy a) := by
  simp [normalizedUpperMax, ne_of_gt hQ]

theorem upperStrictSurvival_iff_pos_normalized (a : Path n) (hn : 0 < n)
    (t : ℝ) :
    a ∈ upperStrictSurvival hn t ↔
      0 < energy a ∧ normalizedUpperMax a hn < t := by
  by_cases hQ : energy a = 0
  · simp [upperStrictSurvival, hQ,
      upperMax_eq_zero_of_energy_eq_zero a hn hQ]
  · have hpos : 0 < energy a :=
      lt_of_le_of_ne (energy_nonneg a) (Ne.symm hQ)
    have hsqrt : 0 < Real.sqrt (energy a) := Real.sqrt_pos.2 hpos
    simp [upperStrictSurvival, normalizedUpperMax, hQ, hpos,
      div_lt_iff₀ hsqrt]

theorem upperCrossing_iff_zero_or_normalized (a : Path n) (hn : 0 < n)
    (t : ℝ) :
    a ∈ upperCrossing hn t ↔
      energy a = 0 ∨ t ≤ normalizedUpperMax a hn := by
  by_cases hQ : energy a = 0
  · simp [upperCrossing, hQ, upperMax_eq_zero_of_energy_eq_zero a hn hQ]
  · have hpos : 0 < energy a :=
      lt_of_le_of_ne (energy_nonneg a) (Ne.symm hQ)
    have hsqrt : 0 < Real.sqrt (energy a) := Real.sqrt_pos.2 hpos
    simp [upperCrossing, normalizedUpperMax, hQ, le_div_iff₀ hsqrt]

theorem upperNormalizedCDF_eq_union_zeroEnergy (hn : 0 < n) {t : ℝ}
    (ht : 0 < t) :
    upperNormalizedCDF hn t = upperStrictSurvival hn t ∪ zeroEnergy := by
  ext a
  by_cases hQ : energy a = 0
  · simp [upperNormalizedCDF, normalizedUpperMax, upperStrictSurvival,
      zeroEnergy, hQ, upperMax_eq_zero_of_energy_eq_zero a hn hQ, ht]
  · have hpos : 0 < energy a :=
      lt_of_le_of_ne (energy_nonneg a) (Ne.symm hQ)
    have hsqrt : 0 < Real.sqrt (energy a) := Real.sqrt_pos.2 hpos
    simp [upperNormalizedCDF, normalizedUpperMax, upperStrictSurvival,
      zeroEnergy, hQ, div_lt_iff₀ hsqrt]

theorem upperStrictSurvival_disjoint_zeroEnergy (hn : 0 < n) (t : ℝ) :
    Disjoint (upperStrictSurvival hn t) (zeroEnergy : Set (Path n)) := by
  rw [Set.disjoint_left]
  intro a ha hQ
  exact not_mem_upperStrictSurvival_of_energy_eq_zero a hn t hQ ha

theorem endpointRawCDF_iff_pos_normalized (a : Path n) (t : ℝ) :
    a ∈ endpointRawCDF t ↔
      0 < energy a ∧ |normalizedEndpoint a| < t := by
  by_cases hQ : energy a = 0
  · simp [endpointRawCDF, hQ]
  · have hpos : 0 < energy a :=
      lt_of_le_of_ne (energy_nonneg a) (Ne.symm hQ)
    have hsqrt : 0 < Real.sqrt (energy a) := Real.sqrt_pos.2 hpos
    simp [endpointRawCDF, normalizedEndpoint, hQ, hpos, abs_div,
      abs_of_nonneg (Real.sqrt_nonneg (energy a)), div_lt_iff₀ hsqrt]

theorem endpointNormalizedCDF_eq_union_zeroEnergy {t : ℝ} (ht : 0 < t) :
    (endpointNormalizedCDF t : Set (Path n)) = endpointRawCDF t ∪ zeroEnergy := by
  ext a
  by_cases hQ : energy a = 0
  · simp [endpointNormalizedCDF, normalizedEndpoint, endpointRawCDF,
      zeroEnergy, hQ, ht]
  · have hpos : 0 < energy a :=
      lt_of_le_of_ne (energy_nonneg a) (Ne.symm hQ)
    have hsqrt : 0 < Real.sqrt (energy a) := Real.sqrt_pos.2 hpos
    simp [endpointNormalizedCDF, normalizedEndpoint, endpointRawCDF,
      zeroEnergy, hQ, abs_div, abs_of_nonneg (Real.sqrt_nonneg (energy a)),
      div_lt_iff₀ hsqrt]

theorem endpointRawCDF_disjoint_zeroEnergy (t : ℝ) :
    Disjoint (endpointRawCDF t) (zeroEnergy : Set (Path n)) := by
  rw [Set.disjoint_left]
  intro a ha hQ
  have hpos := (endpointRawCDF_iff_pos_normalized a t).1 ha
  have hzero : energy a = 0 := hQ
  exact (ne_of_gt hpos.1) hzero

theorem maxWithZero_strict_event_eq (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    {a : Path n | maxWithZero a < t * Real.sqrt (energy a)} =
      upperStrictSurvival hn t := by
  ext a
  by_cases hQ : energy a = 0
  · simp [maxWithZero_eq a hn, upperStrictSurvival, hQ,
      upperMax_eq_zero_of_energy_eq_zero a hn hQ]
  · have hpos : 0 < energy a :=
      lt_of_le_of_ne (energy_nonneg a) (Ne.symm hQ)
    have hwall : 0 < t * Real.sqrt (energy a) :=
      mul_pos ht (Real.sqrt_pos.2 hpos)
    simp [maxWithZero_eq a hn, upperStrictSurvival, max_lt_iff, hwall]

end Shao.C1

