import Shao.Basic.Lindley
import Shao.Probability.FiniteIID
import Shao.Probability.MeasurablePath

/-!
# Joint law of the final Lindley state and genuine sample energy

A fixed reversal preserves the joint law of a finite iid sample. Its prefix
maximum is the original sample's genuine recursive Lindley terminal state.
This is an equality in distribution of pairs, not a pathwise equality of the
original sample's Lindley state and its own prefix maximum.
-/

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- Under a finite iid law, the terminal Lindley state and genuine energy have
the same joint distribution as the prefix maximum with zero and that energy.
The statement includes an empty sample and zero-energy samples. -/
theorem iid_lindley_energy_identDistrib_maxWithZero
    {μ : Measure Ω} {ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Fin n → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν) :
    IdentDistrib
      (fun ω => (Shao.lindleyState (samplePath X ω) n le_rfl,
        Shao.energy (samplePath X ω)))
      (fun ω => (Shao.maxWithZero (samplePath X ω),
        Shao.energy (samplePath X ω))) μ μ := by
  have hperm := iid_observable_identDistrib_perm hX hIndep hLaw Fin.revPerm
    (F := fun a : Shao.Path n => (Shao.maxWithZero a, Shao.energy a))
    (Shao.measurable_maxWithZero.prodMk Shao.measurable_energy)
  have hrev :
      (fun ω => (Shao.maxWithZero (samplePath (fun i => X (Fin.revPerm i)) ω),
        Shao.energy (samplePath (fun i => X (Fin.revPerm i)) ω))) =
      (fun ω => (Shao.lindleyState (samplePath X ω) n le_rfl,
        Shao.energy (samplePath X ω))) := by
    funext ω
    change (Shao.maxWithZero (Shao.reversePath (samplePath X ω)),
        Shao.energy (Shao.reversePath (samplePath X ω))) = _
    rw [Shao.lindleyState_length, Shao.energy_reversePath]
  rw [hrev] at hperm
  exact hperm.symm

end Shao.Probability
