import Shao.OQ3.NormalLayerWeakConvergence
import Shao.OQ3.StageLayerSeriesLimit

namespace Shao.OQ3

open MeasureTheory Filter
open scoped Topology BigOperators

noncomputable section

theorem normalizedTailCoefficient_stage_subsequence_tendsto_of_stage
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1)
    (J : ℕ) (q : ℝ) (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (hmeanY : (∫ x : ℝ, normalValue x ∂atomicMeasure w) = q)
    (hmeanX : (∫ x : ℝ, x ∂atomicMeasure w) = q / 4)
    (hrange : ∀ᵐ x ∂atomicMeasure w, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < (atomicMeasure w).real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (hphase : Tendsto (fun j : ℕ => Int.fract ((m j : ℝ) * q / dyadicMesh J))
      atTop (nhds 0)) :
    Summable (fun k : ℤ => sourceGaussianLayerWeight (atomicMeasure w) q sourceEll
        (dyadicMesh J * (k : ℝ))) ∧
      Tendsto (fun j : ℕ => normalizedTailCoefficient sourceEll q w (m j))
        atTop (nhds ((dyadicMesh J / Real.sqrt (normalVariance (atomicMeasure w))) *
          ∑' k : ℤ, sourceGaussianLayerWeight (atomicMeasure w) q sourceEll
            (dyadicMesh J * (k : ℝ)))) := by
  letI : IsProbabilityMeasure (atomicMeasure w) :=
    atomicMeasure_isProbabilityMeasure w hw hs
  have hb : ∀ᵐ x ∂atomicMeasure w, |x| ≤ 4 + Real.sqrt 10 := by
    filter_upwards [atomicMeasure_ae_bounds w] with x hx
    exact hx.2
  have hbase : ∀ i : Fin 4, 0 < (atomicMeasure w).real {baseAtom i} :=
    fun i => hpos (Sum.inl i)
  have hS := normalVariance_pos (atomicMeasure w) hb hbase
  have hD := parabolaCovariance_det_pos (atomicMeasure w) hb hbase
  apply normalizedTailCoefficient_stage_subsequence_tendsto
    w hw hs J q hq0 hq1 hmeanY hmeanX hrange hpos m hm hphase
  intro d hd hlayer A hfrontier
  exact stage_normalLayerConditionalLaw_real_tendsto
    (atomicMeasure w) J q (q / 4) hb hmeanY hmeanX hS hD
    hrange hpos d hd hlayer A hfrontier

end
end Shao.OQ3
