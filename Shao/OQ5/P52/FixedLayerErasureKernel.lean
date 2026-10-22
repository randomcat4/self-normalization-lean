import Shao.OQ5.P52.FixedLayerErasureLaw
import Shao.OQ5.P52.FixedLayerAbsoluteMoments

/-!
# Deleting one layer from the actual masked kernel

Finite deletion preserves the exact absolute-convergence set. Subtraction
identities are pointwise on that set and almost everywhere under the actual
original pair law; the source mask is retained everywhere else.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped BigOperators

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

theorem fixedLayerTerm_erase_pair (j k : ℕ) (z : LayerObs × LayerObs) :
    fixedLayerTerm k (fixedEraseLayer j z.1, fixedEraseLayer j z.2) =
      if k = j then 0 else fixedLayerTerm k z := by
  by_cases hk : k = j
  · subst k
    simp [fixedLayerTerm, fixedEraseLayer, Shao.OQ5.P50.layerKernel]
  · simp only [fixedLayerTerm, fixedEraseLayer, ite_eq_right hk]

private theorem summable_replace_zero_iff (f : ℕ → ℝ) (j : ℕ) :
    Summable (fun k : ℕ => if k = j then 0 else f k) ↔ Summable f := by
  constructor
  · intro hs
    have hu := hs.update j (f j)
    apply hu.congr
    intro k
    by_cases hk : k = j <;> simp [hk]
  · intro hs
    apply (hs.update j 0).congr
    intro k
    by_cases hk : k = j <;> simp [hk]

theorem fixedAbsoluteConvergenceSet_erase_pair_iff
    (j : ℕ) (z : LayerObs × LayerObs) :
    (fixedEraseLayer j z.1, fixedEraseLayer j z.2) ∈ fixedAbsoluteConvergenceSet ↔
      z ∈ fixedAbsoluteConvergenceSet := by
  change Summable (fun k : ℕ =>
      |fixedLayerTerm k (fixedEraseLayer j z.1, fixedEraseLayer j z.2)|) ↔
    Summable (fun k : ℕ => |fixedLayerTerm k z|)
  have he : (fun k : ℕ =>
      |fixedLayerTerm k (fixedEraseLayer j z.1, fixedEraseLayer j z.2)|) =
      (fun k : ℕ => if k = j then 0 else |fixedLayerTerm k z|) := by
    funext k
    rw [fixedLayerTerm_erase_pair]
    split_ifs <;> simp only [abs_zero]
  rw [he]
  exact summable_replace_zero_iff (fun k => |fixedLayerTerm k z|) j

theorem fixedResidualKernel_erase_pair_eq_sub (j : ℕ) (z : LayerObs × LayerObs)
    (hz : z ∈ fixedAbsoluteConvergenceSet) :
    fixedResidualKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2) =
      fixedResidualKernel z - fixedLayerTerm j z := by
  have hez := (fixedAbsoluteConvergenceSet_erase_pair_iff j z).mpr hz
  have hsabs := hz
  change Summable (fun k : ℕ => |fixedLayerTerm k z|) at hsabs
  have hs : Summable (fun k : ℕ => fixedLayerTerm k z) :=
    Summable.of_norm (by simpa only [Real.norm_eq_abs] using hsabs)
  have he : (fun k : ℕ =>
      fixedLayerTerm k (fixedEraseLayer j z.1, fixedEraseLayer j z.2)) =
      Function.update (fun k : ℕ => fixedLayerTerm k z) j 0 := by
    funext k
    rw [fixedLayerTerm_erase_pair]
    simp only [Function.update_apply]
  rw [fixedResidualKernel_eq_tsum _ hez, fixedResidualKernel_eq_tsum z hz, he]
  have hu := (hs.hasSum.update j (0 : ℝ)).tsum_eq
  calc
    _ = (0 - fixedLayerTerm j z) + ∑' k : ℕ, fixedLayerTerm k z := hu
    _ = _ := by ring

theorem fixedKernel_erase_pair_eq_sub (j : ℕ) (z : LayerObs × LayerObs)
    (hz : z ∈ fixedAbsoluteConvergenceSet) :
    fixedKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2) =
      fixedKernel z - fixedLayerTerm j z := by
  change z.1.1 + z.2.1 +
      fixedResidualKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2) =
    (z.1.1 + z.2.1 + fixedResidualKernel z) - fixedLayerTerm j z
  rw [fixedResidualKernel_erase_pair_eq_sub j z hz]
  ring

theorem fixedResidualKernel_erase_pair_ae_eq_sub (j : ℕ) :
    (fun z : LayerObs × LayerObs =>
      fixedResidualKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2))
      =ᵐ[fixedObservationLaw.prod fixedObservationLaw]
        (fun z : LayerObs × LayerObs => fixedResidualKernel z - fixedLayerTerm j z) := by
  filter_upwards [ae_mem_fixedAbsoluteConvergenceSet] with z hz
  exact fixedResidualKernel_erase_pair_eq_sub j z hz

theorem fixedKernel_erase_pair_ae_eq_sub (j : ℕ) :
    (fun z : LayerObs × LayerObs =>
      fixedKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2))
      =ᵐ[fixedObservationLaw.prod fixedObservationLaw]
        (fun z : LayerObs × LayerObs => fixedKernel z - fixedLayerTerm j z) := by
  filter_upwards [ae_mem_fixedAbsoluteConvergenceSet] with z hz
  exact fixedKernel_erase_pair_eq_sub j z hz

end
end Shao.OQ5.P52
