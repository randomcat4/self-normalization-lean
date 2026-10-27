import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.Normed.Group.Constructions

namespace Shao.OQ3
open MeasureTheory
noncomputable section

theorem independent_sum_source_set_le
    (nu eta : Measure (ℝ × ℝ)) [IsProbabilityMeasure nu] [IsProbabilityMeasure eta]
    (s t : Set (ℝ × ℝ)) (hs : MeasurableSet s) (ht : MeasurableSet t) (eps : ℝ)
    (hshift : ∀ x ∈ s, ∀ y : ℝ × ℝ, ‖y‖ ≤ eps → x + y ∈ t) :
    let rho : Measure (ℝ × ℝ) := (nu.prod eta).map (fun q => q.1 + q.2)
    nu s ≤ rho t + eta {y : ℝ × ℝ | eps < ‖y‖} := by
  intro rho
  have hm : Measurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => q.1 + q.2) := by fun_prop
  have hsub : s ×ˢ (Set.univ : Set (ℝ × ℝ)) ⊆
      (fun q : (ℝ × ℝ) × (ℝ × ℝ) => q.1 + q.2) ⁻¹' t ∪
        (Set.univ ×ˢ {y : ℝ × ℝ | eps < ‖y‖}) := by
    intro q hq
    by_cases hy : ‖q.2‖ ≤ eps
    · exact Or.inl (hshift q.1 hq.1 q.2 hy)
    · exact Or.inr ⟨Set.mem_univ _, lt_of_not_ge hy⟩
  have h := (measure_mono (μ := nu.prod eta) hsub).trans (measure_union_le _ _)
  simpa only [Measure.prod_prod, measure_univ, mul_one, one_mul,
    ← Measure.map_apply hm ht] using h

theorem independent_sum_image_set_le
    (nu eta : Measure (ℝ × ℝ)) [IsProbabilityMeasure nu] [IsProbabilityMeasure eta]
    (s t : Set (ℝ × ℝ)) (hs : MeasurableSet s) (ht : MeasurableSet t) (eps : ℝ)
    (hshift : ∀ x y : ℝ × ℝ, x + y ∈ s → ‖y‖ ≤ eps → x ∈ t) :
    let rho : Measure (ℝ × ℝ) := (nu.prod eta).map (fun q => q.1 + q.2)
    rho s ≤ nu t + eta {y : ℝ × ℝ | eps < ‖y‖} := by
  intro rho
  have hm : Measurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => q.1 + q.2) := by fun_prop
  have hsub :
      (fun q : (ℝ × ℝ) × (ℝ × ℝ) => q.1 + q.2) ⁻¹' s ⊆
        (t ×ˢ (Set.univ : Set (ℝ × ℝ))) ∪
          (Set.univ ×ˢ {y : ℝ × ℝ | eps < ‖y‖}) := by
    intro q hq
    by_cases hy : ‖q.2‖ ≤ eps
    · exact Or.inl ⟨hshift q.1 q.2 hq hy, Set.mem_univ _⟩
    · exact Or.inr ⟨Set.mem_univ _, lt_of_not_ge hy⟩
  have h := (measure_mono (μ := nu.prod eta) hsub).trans (measure_union_le _ _)
  simpa only [Measure.prod_prod, measure_univ, mul_one, one_mul,
    ← Measure.map_apply hm hs] using h

end
end Shao.OQ3
