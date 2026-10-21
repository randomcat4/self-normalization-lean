import Shao.OQ5.P50.ThreeStateLayer
import Shao.OQ5.P52.FixedLayerCoefficients
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

open MeasureTheory
open Classical
open scoped BigOperators

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

/-- The actual fixed layer matrix on the two complete observations. -/
def fixedLayerTerm (j : ℕ) (z : LayerObs × LayerObs) : ℝ :=
  Shao.OQ5.P50.layerKernel (fixedLayerN j) (fixedLayerT j) (fixedLayerP j) (fixedLayerQ j)
    (z.1.2 j) (z.2.2 j)

/-- Exactly the source absolute-convergence set, with all layers retained. -/
def fixedAbsoluteConvergenceSet : Set (LayerObs × LayerObs) :=
  {z | Summable (fun j : ℕ => |fixedLayerTerm j z|)}

/-- The actual residual series on absolute convergence, zero everywhere else. -/
def fixedResidualKernel (z : LayerObs × LayerObs) : ℝ :=
  if z ∈ fixedAbsoluteConvergenceSet then ∑' j, fixedLayerTerm j z else 0

/-- The everywhere-real source kernel, before any real-encoding transport. -/
def fixedKernel (z : LayerObs × LayerObs) : ℝ :=
  z.1.1 + z.2.1 + fixedResidualKernel z

theorem measurable_fixedLayerTerm (j : ℕ) : Measurable (fixedLayerTerm j) := by
  have htab : Measurable (fun s : Fin 3 × Fin 3 =>
      Shao.OQ5.P50.layerKernel (fixedLayerN j) (fixedLayerT j)
        (fixedLayerP j) (fixedLayerQ j) s.1 s.2) := measurable_of_finite _
  have hleft : Measurable (fun z : LayerObs × LayerObs => z.1.2 j) :=
    (measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)
  have hright : Measurable (fun z : LayerObs × LayerObs => z.2.2 j) :=
    (measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)
  exact htab.comp (hleft.prodMk hright)

theorem fixedLayerTerm_symmetric (j : ℕ) (o o' : LayerObs) :
    fixedLayerTerm j (o, o') = fixedLayerTerm j (o', o) := by
  exact Shao.OQ5.P50.layerKernel_symmetric _ _ _ _ _ _

theorem measurableSet_fixedAbsoluteConvergenceSet :
    MeasurableSet fixedAbsoluteConvergenceSet := by
  have hs : Measurable (fun z : LayerObs × LayerObs =>
      ∑' j : ℕ, ‖fixedLayerTerm j z‖ₑ) :=
    Measurable.tsum (fun j => (measurable_fixedLayerTerm j).enorm)
  have hset := measurableSet_lt hs (measurable_const (a := (⊤ : ENNReal)))
  simpa only [fixedAbsoluteConvergenceSet, lt_top_iff_ne_top,
    tsum_enorm_ne_top_iff_summable_norm, Real.norm_eq_abs] using hset

theorem fixedAbsoluteConvergenceSet_swap (o o' : LayerObs) :
    (o, o') ∈ fixedAbsoluteConvergenceSet ↔ (o', o) ∈ fixedAbsoluteConvergenceSet := by
  have he : (fun j : ℕ => |fixedLayerTerm j (o, o')|) =
      (fun j : ℕ => |fixedLayerTerm j (o', o)|) :=
    funext fun j => congrArg abs (fixedLayerTerm_symmetric j o o')
  change Summable (fun j : ℕ => |fixedLayerTerm j (o, o')|) ↔
    Summable (fun j : ℕ => |fixedLayerTerm j (o', o)|)
  rw [he]

theorem fixedResidualKernel_eq_tsum (z : LayerObs × LayerObs)
    (hz : z ∈ fixedAbsoluteConvergenceSet) :
    fixedResidualKernel z = ∑' j, fixedLayerTerm j z := by
  simp only [fixedResidualKernel, ite_eq_left hz]

theorem fixedResidualKernel_eq_zero (z : LayerObs × LayerObs)
    (hz : z ∉ fixedAbsoluteConvergenceSet) : fixedResidualKernel z = 0 := by
  simp only [fixedResidualKernel, ite_eq_right hz]

theorem measurable_fixedResidualKernel : Measurable fixedResidualKernel := by
  have hs : Measurable (fun z : LayerObs × LayerObs => ∑' j : ℕ, fixedLayerTerm j z) :=
    Measurable.tsum measurable_fixedLayerTerm
  exact Measurable.ite measurableSet_fixedAbsoluteConvergenceSet hs measurable_const

theorem fixedResidualKernel_symmetric (o o' : LayerObs) :
    fixedResidualKernel (o, o') = fixedResidualKernel (o', o) := by
  unfold fixedResidualKernel
  by_cases h : (o, o') ∈ fixedAbsoluteConvergenceSet
  · rw [ite_eq_left h, ite_eq_left ((fixedAbsoluteConvergenceSet_swap o o').mp h)]
    exact tsum_congr fun j => fixedLayerTerm_symmetric j o o'
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ((fixedAbsoluteConvergenceSet_swap o o').mpr h'))]

theorem measurable_fixedKernel : Measurable fixedKernel := by
  exact ((measurable_fst.comp measurable_fst).add
    (measurable_fst.comp measurable_snd)).add measurable_fixedResidualKernel

theorem fixedKernel_symmetric (o o' : LayerObs) :
    fixedKernel (o, o') = fixedKernel (o', o) := by
  dsimp only [fixedKernel]
  rw [fixedResidualKernel_symmetric]
  ring

end
end Shao.OQ5.P52
