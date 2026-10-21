import Shao.OQ5.P35.FixedCategoryLaw

/-!
# Centered feature moments for the fixed p35 category law

Source: `current/oq56/inputs02/p35.md`, §3, lines 73–99.
This module proves only the scalar centered first and second moments under the
fixed category law. No fourth moment or feature/offset independence is assumed.
-/

namespace Shao.OQ5.P35

open MeasureTheory

noncomputable section

/-- The exact second moment of the centered category feature. -/
def featureVariance : ℝ := 1 / 15 - featureMean ^ 2

theorem integrable_categoryFeature : Integrable categoryFeature categoryMeasure := by
  change Integrable (fun c => categoryValue c - featureMean) categoryMeasure
  exact integrable_categoryValue.sub (integrable_const featureMean)

theorem integral_categoryFeature :
    (∫ c, categoryFeature c ∂categoryMeasure) = 0 := by
  change (∫ c, categoryValue c - featureMean ∂categoryMeasure) = 0
  rw [integral_sub integrable_categoryValue (integrable_const featureMean),
    integral_categoryValue, integral_const, probReal_univ, one_smul]
  norm_num [featureMean]

private theorem categoryFeature_sq_expand :
    (fun c => categoryFeature c ^ 2) =
      (fun c => categoryValue c ^ 2 -
        (2 * featureMean) * categoryValue c + featureMean ^ 2) := by
  funext c
  unfold categoryFeature
  ring

theorem integrable_categoryFeature_sq :
    Integrable (fun c => categoryFeature c ^ 2) categoryMeasure := by
  rw [categoryFeature_sq_expand]
  exact (integrable_categoryValue_sq.sub
    (integrable_categoryValue.const_mul (2 * featureMean))).add
    (integrable_const (featureMean ^ 2))

theorem integral_categoryFeature_sq :
    (∫ c, categoryFeature c ^ 2 ∂categoryMeasure) = featureVariance := by
  have hlin : Integrable (fun c => (2 * featureMean) * categoryValue c)
      categoryMeasure := integrable_categoryValue.const_mul (2 * featureMean)
  have hpoly : Integrable (fun c => categoryValue c ^ 2 -
      (2 * featureMean) * categoryValue c) categoryMeasure :=
    integrable_categoryValue_sq.sub hlin
  rw [categoryFeature_sq_expand,
    integral_add hpoly (integrable_const (featureMean ^ 2)),
    integral_sub integrable_categoryValue_sq hlin,
    integral_const_mul, integral_categoryValue_sq, integral_categoryValue,
    integral_const, probReal_univ, one_smul]
  norm_num [featureVariance, featureMean]

theorem featureVariance_pos : 0 < featureVariance := by
  norm_num [featureVariance, featureMean]

end
end Shao.OQ5.P35
