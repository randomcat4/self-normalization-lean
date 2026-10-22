# Actual erased finite rows and unordered pair sums — frozen catalogs

ACCEPTED FROZEN CATALOGS. Exactly9 public theorems and2 public definitions. Future51/75/76 excluded.

## Unit73: FixedLayerErasedRowMoments

Original freeze SHA256 a3a212b4e1cc5825ec61e1a8d95be43f4c1cd0f9dcab76c6dabaa34fb324468c;6publictheorems,1definition.

```lean
import Shao.OQ5.P52.FixedLayerErasedEdgeMoments

open MeasureTheory
open scoped BigOperators

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

def fixedErasedResidualRow {n : ℕ} (i : Fin n) (x : Fin n → LayerObs) : ℝ :=
  ∑ k ∈ Finset.univ.erase i, fixedResidualKernel (x i, x k)

theorem fixedErasedResidualRow_memLp_two (j n : ℕ) (i : Fin n) :
    MemLp (fixedErasedResidualRow i) 2
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j))

theorem integral_fixedErasedResidualRow_eq_zero (j n : ℕ) (i : Fin n) :
    (∫ x : Fin n → LayerObs, fixedErasedResidualRow i x
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) = 0

theorem integrable_fixedErasedResidualRow_mul
    (j n : ℕ) (i k : Fin n) :
    Integrable (fun x : Fin n → LayerObs =>
      fixedErasedResidualRow i x * fixedErasedResidualRow k x)
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j))

theorem integral_fixedErasedResidualRow_mul (j n : ℕ) (i k : Fin n) :
    (∫ x : Fin n → LayerObs,
      fixedErasedResidualRow i x * fixedErasedResidualRow k x
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) =
      (if i = k then ((n - 1 : ℕ) : ℝ) else 1) *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂(fixedErasedLaw j).prod (fixedErasedLaw j))

theorem integrable_fixedErasedResidualCenteredRows_sq (j n : ℕ) :
    Integrable (fun x : Fin n → LayerObs =>
      ∑ i : Fin n,
        (fixedErasedResidualRow i x -
          (n : ℝ)⁻¹ * ∑ k : Fin n, fixedErasedResidualRow k x) ^ 2)
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j))

theorem integral_fixedErasedResidualCenteredRows_sq
    (j n : ℕ) (hn : 3 ≤ n) :
    (∫ x : Fin n → LayerObs,
      ∑ i : Fin n,
        (fixedErasedResidualRow i x -
          (n : ℝ)⁻¹ * ∑ k : Fin n, fixedErasedResidualRow k x) ^ 2
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) =
      ((n - 1 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ) *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂(fixedErasedLaw j).prod (fixedErasedLaw j))

end
end Shao.OQ5.P52
```

## Unit74: FixedLayerErasedPairMoments

Original freeze SHA256 68050d1a463260592a6e05e82c33364168566362f1307eb85dd704bf2ced53db;3publictheorems,1definition.

```lean
import Shao.OQ5.P52.FixedLayerErasedEdgeMoments

open MeasureTheory
open scoped BigOperators

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

def fixedErasedResidualPairSum {n : ℕ} (x : Fin n → LayerObs) : ℝ :=
  Shao.OQ5.P35.unorderedPairSum
    (fun i k => fixedResidualKernel (x i, x k))

theorem fixedErasedResidualPairSum_memLp_two (j n : ℕ) :
    MemLp (fixedErasedResidualPairSum (n := n)) 2
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j))

theorem integral_fixedErasedResidualPairSum_eq_zero (j n : ℕ) :
    (∫ x : Fin n → LayerObs, fixedErasedResidualPairSum x
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) = 0

theorem integral_fixedErasedResidualPairSum_sq (j n : ℕ) :
    (∫ x : Fin n → LayerObs, (fixedErasedResidualPairSum x) ^ 2
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) =
      (n.choose 2 : ℝ) *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂(fixedErasedLaw j).prod (fixedErasedLaw j))

end
end Shao.OQ5.P52
```
