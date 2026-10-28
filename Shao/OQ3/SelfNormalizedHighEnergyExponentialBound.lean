import Shao.OQ3.SelfNormalizedHighEnergyCount
import Shao.OQ3.LargeIIDCountExponentialBound

namespace Shao.OQ3
open Classical MeasureTheory
open scoped BigOperators
noncomputable section

theorem exists_self_normalized_high_energy_arbitrary_exponential_bound
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (level R : ℝ) (hlevel : 0 < level) (hR : 0 < R) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n →
      let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
      let T : Set (Shao.Path n) := {z | level * Real.sqrt (n : ℝ) ≤
        (if Shao.energy z = 0 then 0 else
          (∑ i : Fin n, z i) / Real.sqrt (Shao.energy z))}
      P.real (T ∩ {z | Q * (n : ℝ) ≤ Shao.energy z}) ≤
        Real.exp (-R * (n : ℝ)) := by
  classical
  have halpha : 0 < level ^ 2 / 4 := by positivity
  obtain ⟨B, hB, hCount⟩ :=
    exists_large_iid_count_arbitrary_exponential_bound mu (level ^ 2 / 4) R halpha hR
  refine ⟨4 * B ^ 2 / level ^ 2, by positivity, ?_⟩
  intro n hn P T
  let LargeCount : Shao.Path n → ℕ := fun z =>
    (Finset.univ.filter (fun i : Fin n => B < |z i|)).card
  have hSub : T ∩ {z | (4 * B ^ 2 / level ^ 2) * (n : ℝ) ≤ Shao.energy z} ⊆
      {z | (level ^ 2 / 4) * (n : ℝ) ≤ (LargeCount z : ℝ)} := by
    intro z hz
    exact self_normalized_high_energy_many_large level B hlevel hB n hn z hz.1 hz.2
  have hProb : P.real {z | (level ^ 2 / 4) * (n : ℝ) ≤ (LargeCount z : ℝ)} ≤
      Real.exp (-R * (n : ℝ)) := by
    convert hCount n using 1
  exact (measureReal_mono hSub (measure_ne_top P _)).trans hProb

end
end Shao.OQ3
