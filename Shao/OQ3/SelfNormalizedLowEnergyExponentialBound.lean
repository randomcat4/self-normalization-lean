import Shao.OQ3.SelfNormalizedLowEnergyCount
import Shao.OQ3.SmallNonzeroIIDCountExponentialBound

namespace Shao.OQ3
open Classical MeasureTheory
open scoped BigOperators
noncomputable section

theorem exists_self_normalized_low_energy_arbitrary_exponential_bound
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (level R : ℝ) (hlevel : 0 < level) (hR : 0 < R) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ n : ℕ, 1 ≤ n →
      let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
      let T : Set (Shao.Path n) := {z | level * Real.sqrt (n : ℝ) ≤
        (if Shao.energy z = 0 then 0 else
          (∑ i : Fin n, z i) / Real.sqrt (Shao.energy z))}
      P.real (T ∩ {z | Shao.energy z ≤ eta * (n : ℝ)}) ≤
        Real.exp (-R * (n : ℝ)) := by
  classical
  have halpha : 0 < level ^ 2 / 2 := by positivity
  obtain ⟨eps, heps, hCount⟩ :=
    exists_small_nonzero_iid_count_arbitrary_exponential_bound mu
      (level ^ 2 / 2) R halpha hR
  refine ⟨level ^ 2 * eps ^ 2 / 2, by positivity, ?_⟩
  intro n hn P T
  let SmallCount : Shao.Path n → ℕ := fun z =>
    (Finset.univ.filter (fun i : Fin n => z i ≠ 0 ∧ |z i| ≤ eps)).card
  have hSub : T ∩ {z | Shao.energy z ≤ (level ^ 2 * eps ^ 2 / 2) * (n : ℝ)} ⊆
      {z | (level ^ 2 / 2) * (n : ℝ) ≤ (SmallCount z : ℝ)} := by
    intro z hz
    exact self_normalized_low_energy_many_small_nonzero level eps hlevel heps n hn z
      hz.1 hz.2
  have hProb : P.real {z | (level ^ 2 / 2) * (n : ℝ) ≤ (SmallCount z : ℝ)} ≤
      Real.exp (-R * (n : ℝ)) := by
    convert hCount n using 1
  exact (measureReal_mono hSub (measure_ne_top P _)).trans hProb

end
end Shao.OQ3
