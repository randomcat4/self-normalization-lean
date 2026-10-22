import Shao.OQ5.P52.FixedLayerRealProjection

/-!
# The actual real canonical residual and its full category representation

The actual row-integral projection is retained in the real residual. Its
pair L2 and row L1 are paid before canonical row integration. The source
category identity is pointwise, including both branches of the residual
mask; the corresponding real identity has its exact pair-law AE scope.
-/

set_option autoImplicit false

open MeasureTheory Filter

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

attribute [local instance] fixedObservationLaw_isProbabilityMeasure
attribute [local instance] fixedRealObservationLaw_isProbabilityMeasure

def fixedRealCanonicalResidual (z : ℝ × ℝ) : ℝ :=
  fixedRealKernel z - fixedRealFirstProjection z.1 - fixedRealFirstProjection z.2

def fixedCategoryResidualKernel (z : (ℕ → Fin 3) × (ℕ → Fin 3)) : ℝ :=
  fixedResidualKernel ((0, z.1), (0, z.2))

theorem measurable_fixedRealCanonicalResidual :
    Measurable fixedRealCanonicalResidual := by
  exact (measurable_fixedRealKernel.sub
    (measurable_fixedRealFirstProjection.comp measurable_fst)).sub
    (measurable_fixedRealFirstProjection.comp measurable_snd)

theorem measurable_fixedCategoryResidualKernel :
    Measurable fixedCategoryResidualKernel := by
  exact measurable_fixedResidualKernel.comp
    ((measurable_const.prodMk measurable_fst).prodMk
      (measurable_const.prodMk measurable_snd))

theorem fixedCategoryResidualKernel_symmetric (c d : ℕ → Fin 3) :
    fixedCategoryResidualKernel (c, d) = fixedCategoryResidualKernel (d, c) := by
  exact fixedResidualKernel_symmetric (0, c) (0, d)

theorem fixedResidualKernel_eq_categoryResidual (o o' : LayerObs) :
    fixedResidualKernel (o, o') = fixedCategoryResidualKernel (o.2, o'.2) := by
  rfl

theorem fixedRealCanonicalResidual_symmetric (x y : ℝ) :
    fixedRealCanonicalResidual (x, y) = fixedRealCanonicalResidual (y, x) := by
  dsimp only [fixedRealCanonicalResidual]
  rw [fixedRealKernel_symmetric x y]
  ring

theorem fixedRealKernel_hoeffding (x y : ℝ) :
    fixedRealKernel (x, y) = fixedRealFirstProjection x +
      fixedRealFirstProjection y + fixedRealCanonicalResidual (x, y) := by
  dsimp only [fixedRealCanonicalResidual]
  ring

theorem fixedRealCanonicalResidual_memLp_two :
    MemLp fixedRealCanonicalResidual 2
      (fixedRealObservationLaw.prod fixedRealObservationLaw) := by
  have hH : MemLp fixedRealKernel 2
      (fixedRealObservationLaw.prod fixedRealObservationLaw) := by
    simpa using fixedRealKernel_memLp 2 (by norm_num)
  have hfst : (fixedRealObservationLaw.prod fixedRealObservationLaw).map
      (Prod.fst : ℝ × ℝ → ℝ) = fixedRealObservationLaw :=
    measurePreserving_fst.map_eq
  have hsnd : (fixedRealObservationLaw.prod fixedRealObservationLaw).map
      (Prod.snd : ℝ × ℝ → ℝ) = fixedRealObservationLaw :=
    measurePreserving_snd.map_eq
  have hfg : MemLp fixedRealFirstProjection 2
      ((fixedRealObservationLaw.prod fixedRealObservationLaw).map
        (Prod.fst : ℝ × ℝ → ℝ)) := by
    rw [hfst]
    exact fixedRealFirstProjection_memLp_two
  have hsg : MemLp fixedRealFirstProjection 2
      ((fixedRealObservationLaw.prod fixedRealObservationLaw).map
        (Prod.snd : ℝ × ℝ → ℝ)) := by
    rw [hsnd]
    exact fixedRealFirstProjection_memLp_two
  have hf : MemLp (fun z : ℝ × ℝ => fixedRealFirstProjection z.1) 2
      (fixedRealObservationLaw.prod fixedRealObservationLaw) :=
    hfg.comp_of_map measurable_fst.aemeasurable
  have hs : MemLp (fun z : ℝ × ℝ => fixedRealFirstProjection z.2) 2
      (fixedRealObservationLaw.prod fixedRealObservationLaw) :=
    hsg.comp_of_map measurable_snd.aemeasurable
  change MemLp ((fixedRealKernel - (fun z : ℝ × ℝ => fixedRealFirstProjection z.1)) -
    (fun z : ℝ × ℝ => fixedRealFirstProjection z.2)) 2
      (fixedRealObservationLaw.prod fixedRealObservationLaw)
  exact (hH.sub hf).sub hs

theorem integrable_fixedRealCanonicalResidual :
    Integrable fixedRealCanonicalResidual
      (fixedRealObservationLaw.prod fixedRealObservationLaw) := by
  exact MemLp.integrable (by norm_num) fixedRealCanonicalResidual_memLp_two

theorem integrable_fixedRealCanonicalResidual_row_ae :
    ∀ᵐ x : ℝ ∂fixedRealObservationLaw,
      Integrable (fun y : ℝ => fixedRealCanonicalResidual (x, y))
        fixedRealObservationLaw := by
  exact integrable_fixedRealCanonicalResidual.prod_right_ae

theorem integral_fixedRealCanonicalResidual_row_eq_zero_ae :
    ∀ᵐ x : ℝ ∂fixedRealObservationLaw,
      (∫ y : ℝ, fixedRealCanonicalResidual (x, y)
        ∂fixedRealObservationLaw) = 0 := by
  filter_upwards [integrable_fixedRealCanonicalResidual_row_ae] with x hr
  have hc : Integrable (fun _ : ℝ => fixedRealFirstProjection x)
      fixedRealObservationLaw := integrable_const _
  have hsum : Integrable (fun y : ℝ => fixedRealCanonicalResidual (x, y) +
      fixedRealFirstProjection x) fixedRealObservationLaw := hr.add hc
  have hfun : (fun y : ℝ => fixedRealCanonicalResidual (x, y) +
      fixedRealFirstProjection x + fixedRealFirstProjection y) =
      (fun y : ℝ => fixedRealKernel (x, y)) := by
    funext y
    dsimp only [fixedRealCanonicalResidual]
    ring
  have hi : (∫ y : ℝ, fixedRealKernel (x, y) ∂fixedRealObservationLaw) =
      (∫ y : ℝ, fixedRealCanonicalResidual (x, y) ∂fixedRealObservationLaw) +
        fixedRealFirstProjection x := by
    rw [← hfun, integral_add hsum integrable_fixedRealFirstProjection,
      integral_add hr hc, integral_fixedRealFirstProjection_eq_zero]
    simp
  change fixedRealFirstProjection x =
    (∫ y : ℝ, fixedRealCanonicalResidual (x, y) ∂fixedRealObservationLaw) +
      fixedRealFirstProjection x at hi
  linarith

theorem fixedRealCanonicalResidual_ae_eq_categoryResidual :
    fixedRealCanonicalResidual =ᵐ[fixedRealObservationLaw.prod fixedRealObservationLaw]
      (fun z : ℝ × ℝ => fixedCategoryResidualKernel
        ((Shao.OQ5.P50.layerDecode z.1).2,
          (Shao.OQ5.P50.layerDecode z.2).2)) := by
  have henc : (fun o : LayerObs =>
      fixedRealFirstProjection (Shao.OQ5.P50.layerEncode o)) =ᵐ[fixedObservationLaw]
        (fun o : LayerObs => o.1) := by
    filter_upwards [fixedRealFirstProjection_encode_ae,
      fixedFirstProjection_ae_eq_first] with o he hg
    exact he.trans hg
  have hfst : (fixedObservationLaw.prod fixedObservationLaw).map
      (Prod.fst : LayerObs × LayerObs → LayerObs) = fixedObservationLaw :=
    measurePreserving_fst.map_eq
  have hsnd : (fixedObservationLaw.prod fixedObservationLaw).map
      (Prod.snd : LayerObs × LayerObs → LayerObs) = fixedObservationLaw :=
    measurePreserving_snd.map_eq
  have hf : ∀ᵐ z : LayerObs × LayerObs ∂fixedObservationLaw.prod fixedObservationLaw,
      fixedRealFirstProjection (Shao.OQ5.P50.layerEncode z.1) = z.1.1 := by
    have h : ∀ᵐ o : LayerObs ∂(fixedObservationLaw.prod fixedObservationLaw).map
        (Prod.fst : LayerObs × LayerObs → LayerObs),
        fixedRealFirstProjection (Shao.OQ5.P50.layerEncode o) = o.1 := by
      rw [hfst]
      exact henc
    exact ae_of_ae_map measurable_fst.aemeasurable h
  have hs : ∀ᵐ z : LayerObs × LayerObs ∂fixedObservationLaw.prod fixedObservationLaw,
      fixedRealFirstProjection (Shao.OQ5.P50.layerEncode z.2) = z.2.1 := by
    have h : ∀ᵐ o : LayerObs ∂(fixedObservationLaw.prod fixedObservationLaw).map
        (Prod.snd : LayerObs × LayerObs → LayerObs),
        fixedRealFirstProjection (Shao.OQ5.P50.layerEncode o) = o.1 := by
      rw [hsnd]
      exact henc
    exact ae_of_ae_map measurable_snd.aemeasurable h
  have hcat : Measurable (fun z : ℝ × ℝ => fixedCategoryResidualKernel
      ((Shao.OQ5.P50.layerDecode z.1).2,
        (Shao.OQ5.P50.layerDecode z.2).2)) :=
    measurable_fixedCategoryResidualKernel.comp
      (((measurable_snd.comp Shao.OQ5.P50.measurable_layerDecode).comp measurable_fst).prodMk
        ((measurable_snd.comp Shao.OQ5.P50.measurable_layerDecode).comp measurable_snd))
  have hpair : fixedRealObservationLaw.prod fixedRealObservationLaw =
      (fixedObservationLaw.prod fixedObservationLaw).map
        (Prod.map Shao.OQ5.P50.layerEncode Shao.OQ5.P50.layerEncode) :=
    Shao.OQ5.P50.layerRealLaw_pair fixedObservationLaw
  have hm : Measurable
      (Prod.map Shao.OQ5.P50.layerEncode Shao.OQ5.P50.layerEncode) :=
    Shao.OQ5.P50.measurable_layerEncode.prodMap Shao.OQ5.P50.measurable_layerEncode
  rw [hpair]
  apply (ae_map_iff hm.aemeasurable
    (measurableSet_eq_fun measurable_fixedRealCanonicalResidual hcat)).mpr
  filter_upwards [hf, hs] with z hfz hsz
  change fixedRealCanonicalResidual
    (Shao.OQ5.P50.layerEncode z.1, Shao.OQ5.P50.layerEncode z.2) =
      fixedCategoryResidualKernel
        ((Shao.OQ5.P50.layerDecode (Shao.OQ5.P50.layerEncode z.1)).2,
          (Shao.OQ5.P50.layerDecode (Shao.OQ5.P50.layerEncode z.2)).2)
  simp only [Shao.OQ5.P50.layerDecode_encode]
  change fixedRealKernel (Shao.OQ5.P50.layerEncode z.1, Shao.OQ5.P50.layerEncode z.2) -
    fixedRealFirstProjection (Shao.OQ5.P50.layerEncode z.1) -
      fixedRealFirstProjection (Shao.OQ5.P50.layerEncode z.2) =
        fixedCategoryResidualKernel (z.1.2, z.2.2)
  rw [fixedRealKernel_encode, hfz, hsz]
  calc
    _ = fixedResidualKernel (z.1, z.2) := by
      dsimp only [fixedKernel]
      ring
    _ = _ := fixedResidualKernel_eq_categoryResidual z.1 z.2

end
end Shao.OQ5.P52
