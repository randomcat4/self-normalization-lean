import Shao.Basic.Events

/-!
# Two-sided finite-path event identities
The intersection records hitting both walls. The union records crossing
at least one wall, with the same final energy in both events.
-/

namespace Shao.C2

variable {n : ℕ}

def doubleCrossing (hn : 0 < n) (x : ℝ) : Set (Path n) :=
  upperCrossing hn x ∩ lowerCrossing hn x

theorem absoluteCrossing_eq_union (hn : 0 < n) (x : ℝ) :
    absoluteCrossing hn x = upperCrossing hn x ∪ lowerCrossing hn x := by
  ext a
  simp [absoluteCrossing, upperCrossing, lowerCrossing, absMax, le_max_iff]

theorem absoluteStrictSurvival_eq_inter (hn : 0 < n) (x : ℝ) :
    absoluteStrictSurvival hn x =
      upperStrictSurvival hn x ∩ lowerStrictSurvival hn x := by
  ext a
  simp [absoluteStrictSurvival, upperStrictSurvival, lowerStrictSurvival,
    absMax, max_lt_iff]

theorem doubleCrossing_compl_eq_union_survival (hn : 0 < n) (x : ℝ) :
    (doubleCrossing hn x)ᶜ =
      upperStrictSurvival hn x ∪ lowerStrictSurvival hn x := by
  rw [upperStrictSurvival_eq_compl, lowerStrictSurvival_eq_compl]
  exact Set.compl_inter _ _

theorem absoluteStrictSurvival_eq_compl_union (hn : 0 < n) (x : ℝ) :
    absoluteStrictSurvival hn x =
      (upperCrossing hn x ∪ lowerCrossing hn x)ᶜ := by
  rw [← absoluteCrossing_eq_union, absoluteStrictSurvival_eq_compl]

theorem mem_doubleCrossing_of_energy_eq_zero (a : Path n) (hn : 0 < n)
    (x : ℝ) (hQ : energy a = 0) : a ∈ doubleCrossing hn x :=
  ⟨mem_upperCrossing_of_energy_eq_zero a hn x hQ,
    mem_lowerCrossing_of_energy_eq_zero a hn x hQ⟩

theorem mem_absoluteCrossing_of_energy_eq_zero (a : Path n) (hn : 0 < n)
    (x : ℝ) (hQ : energy a = 0) : a ∈ absoluteCrossing hn x := by
  rw [absoluteCrossing_eq_union]
  exact Or.inl (mem_upperCrossing_of_energy_eq_zero a hn x hQ)

theorem neg_mem_doubleCrossing_iff (a : Path n) (hn : 0 < n) (x : ℝ) :
    -a ∈ doubleCrossing hn x ↔ a ∈ doubleCrossing hn x := by
  change (-a ∈ upperCrossing hn x ∧ -a ∈ lowerCrossing hn x) ↔
    (a ∈ upperCrossing hn x ∧ a ∈ lowerCrossing hn x)
  rw [neg_mem_upperCrossing_iff, neg_mem_lowerCrossing_iff]
  exact and_comm

theorem neg_mem_absoluteCrossing_iff (a : Path n) (hn : 0 < n) (x : ℝ) :
    -a ∈ absoluteCrossing hn x ↔ a ∈ absoluteCrossing hn x := by
  change x * Real.sqrt (energy (-a)) ≤ absMax (-a) hn ↔
    x * Real.sqrt (energy a) ≤ absMax a hn
  rw [energy_neg a, absMax_neg a hn]

end Shao.C2

