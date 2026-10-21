import Shao.Basic.FinitePath
import Mathlib.Analysis.Real.Sqrt

/-!
# Deterministic multiplication events
The monitored times are 1 through n. Equality is a crossing, and the wall
uses the actual final sum of squares.
-/

namespace Shao

variable {n : ℕ}

def zeroEnergy : Set (Path n) := {a | energy a = 0}

def upperCrossing (hn : 0 < n) (x : ℝ) : Set (Path n) :=
  {a | x * Real.sqrt (energy a) ≤ upperMax a hn}

def lowerCrossing (hn : 0 < n) (x : ℝ) : Set (Path n) :=
  {a | x * Real.sqrt (energy a) ≤ lowerMax a hn}

def absoluteCrossing (hn : 0 < n) (x : ℝ) : Set (Path n) :=
  {a | x * Real.sqrt (energy a) ≤ absMax a hn}

def upperStrictSurvival (hn : 0 < n) (x : ℝ) : Set (Path n) :=
  {a | upperMax a hn < x * Real.sqrt (energy a)}

def lowerStrictSurvival (hn : 0 < n) (x : ℝ) : Set (Path n) :=
  {a | lowerMax a hn < x * Real.sqrt (energy a)}

def absoluteStrictSurvival (hn : 0 < n) (x : ℝ) : Set (Path n) :=
  {a | absMax a hn < x * Real.sqrt (energy a)}

theorem upperStrictSurvival_eq_compl (hn : 0 < n) (x : ℝ) :
    upperStrictSurvival hn x = (upperCrossing hn x)ᶜ := by
  ext a
  simp [upperStrictSurvival, upperCrossing]

theorem lowerStrictSurvival_eq_compl (hn : 0 < n) (x : ℝ) :
    lowerStrictSurvival hn x = (lowerCrossing hn x)ᶜ := by
  ext a
  simp [lowerStrictSurvival, lowerCrossing]

theorem absoluteStrictSurvival_eq_compl (hn : 0 < n) (x : ℝ) :
    absoluteStrictSurvival hn x = (absoluteCrossing hn x)ᶜ := by
  ext a
  simp [absoluteStrictSurvival, absoluteCrossing]

theorem mem_upperCrossing_of_energy_eq_zero (a : Path n) (hn : 0 < n)
    (x : ℝ) (hQ : energy a = 0) : a ∈ upperCrossing hn x := by
  change x * Real.sqrt (energy a) ≤ upperMax a hn
  rw [upperMax_eq_zero_of_energy_eq_zero a hn hQ, hQ]
  simp

theorem mem_lowerCrossing_of_energy_eq_zero (a : Path n) (hn : 0 < n)
    (x : ℝ) (hQ : energy a = 0) : a ∈ lowerCrossing hn x := by
  change x * Real.sqrt (energy a) ≤ lowerMax a hn
  rw [lowerMax_eq_zero_of_energy_eq_zero a hn hQ, hQ]
  simp

theorem not_mem_upperStrictSurvival_of_energy_eq_zero (a : Path n)
    (hn : 0 < n) (x : ℝ) (hQ : energy a = 0) :
    a ∉ upperStrictSurvival hn x := by
  change ¬ upperMax a hn < x * Real.sqrt (energy a)
  have hcross := mem_upperCrossing_of_energy_eq_zero a hn x hQ
  change x * Real.sqrt (energy a) ≤ upperMax a hn at hcross
  exact not_lt_of_ge hcross

theorem not_mem_lowerStrictSurvival_of_energy_eq_zero (a : Path n)
    (hn : 0 < n) (x : ℝ) (hQ : energy a = 0) :
    a ∉ lowerStrictSurvival hn x := by
  change ¬ lowerMax a hn < x * Real.sqrt (energy a)
  have hcross := mem_lowerCrossing_of_energy_eq_zero a hn x hQ
  change x * Real.sqrt (energy a) ≤ lowerMax a hn at hcross
  exact not_lt_of_ge hcross

theorem neg_mem_upperCrossing_iff (a : Path n) (hn : 0 < n) (x : ℝ) :
    -a ∈ upperCrossing hn x ↔ a ∈ lowerCrossing hn x := by
  change x * Real.sqrt (energy (-a)) ≤ upperMax (-a) hn ↔
    x * Real.sqrt (energy a) ≤ lowerMax a hn
  rw [energy_neg a, upperMax_neg a hn]

theorem neg_mem_lowerCrossing_iff (a : Path n) (hn : 0 < n) (x : ℝ) :
    -a ∈ lowerCrossing hn x ↔ a ∈ upperCrossing hn x := by
  change x * Real.sqrt (energy (-a)) ≤ lowerMax (-a) hn ↔
    x * Real.sqrt (energy a) ≤ upperMax a hn
  rw [energy_neg a, lowerMax_neg a hn]

end Shao

