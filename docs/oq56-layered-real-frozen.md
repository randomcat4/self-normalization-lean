# Frozen public declarations: layered real representation

Source authority: original p50.md SHAde553dc827eeadbc1e863c1778caa9bdeb00bca84110b4666b06cab053d7b768 lines85–95,149; p52.md SHA615209f8501e14a6bfaee220899c30891510fef5987c9abf7f74ac52b6538b45 lines53,84–86. Exact unit freezes:35 SHA f914a5ebe96a662ad4fc5359eb21da0a0ef5629f34fc43eb6d796533b2142541;36 SHA f76e959f227e00c15248bca9e7f6d6ccb1c7ce2254d8d407ec0b6ba1307f6b4e. The following catalogs omit proof bodies, retain exact definitions/types/assumptions, and contain no extra public aliases. Full frozen scope and independent verdicts are recorded in the review document.

## LayeredEncoding —3 definitions,8 theorem types
```lean
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal

open MeasureTheory

namespace Shao.OQ5.P50

noncomputable section

/-- A single fixed real encoding of the full observation and all layer coordinates. -/
def layerEncode : (ℝ × (ℕ → Fin 3)) → ℝ :=
  embeddingReal (ℝ × (ℕ → Fin 3))

/-- A total measurable decoder; its off-image anchor is fixed but unspecified. -/
def layerDecode : ℝ → (ℝ × (ℕ → Fin 3)) :=
  (measurableEmbedding_embeddingReal (ℝ × (ℕ → Fin 3))).invFun

/-- The Borel real image of the full layered observation space. -/
def layerEncodedSet : Set ℝ := Set.range layerEncode

theorem measurable_layerEncode : Measurable layerEncode

theorem layerEncode_injective : Function.Injective layerEncode

theorem measurableSet_layerEncodedSet : MeasurableSet layerEncodedSet

theorem measurable_layerDecode : Measurable layerDecode

theorem layerDecode_encode (o : ℝ × (ℕ → Fin 3)) :
    layerDecode (layerEncode o) = o

theorem layerEncode_decode (x : ℝ) (hx : x ∈ layerEncodedSet) :
    layerEncode (layerDecode x) = x

theorem layerDecode_encode_first (o : ℝ × (ℕ → Fin 3)) :
    (layerDecode (layerEncode o)).1 = o.1

theorem layerDecode_encode_layer (o : ℝ × (ℕ → Fin 3)) (j : ℕ) :
    (layerDecode (layerEncode o)).2 j = o.2 j

end
end Shao.OQ5.P50
```

## LayeredRealTransport —2 definitions,13 theorem types

```lean
import Shao.OQ5.P50.LayeredEncoding
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory

namespace Shao.OQ5.P50

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

/-- The actual supplied source law pushed through the single fixed encoder. -/
def layerRealLaw (μ : Measure LayerObs) : Measure ℝ := μ.map layerEncode

/-- The decoded source kernel on the encoded pair image, zero elsewhere. -/
def layerRealKernel (H : LayerObs × LayerObs → ℝ) (z : ℝ × ℝ) : ℝ :=
  if z ∈ layerEncodedSet ×ˢ layerEncodedSet then
    H (layerDecode z.1, layerDecode z.2)
  else 0

theorem layerRealLaw_isProbabilityMeasure (μ : Measure LayerObs)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (layerRealLaw μ)

theorem layerRealLaw_ae_image (μ : Measure LayerObs) :
    ∀ᵐ x ∂layerRealLaw μ, x ∈ layerEncodedSet

theorem layerRealLaw_decode (μ : Measure LayerObs) :
    (layerRealLaw μ).map layerDecode = μ

theorem layerRealLaw_pair (μ : Measure LayerObs) [SFinite μ] :
    (layerRealLaw μ).prod (layerRealLaw μ) =
      (μ.prod μ).map (Prod.map layerEncode layerEncode)

theorem measurable_layerRealKernel (H : LayerObs × LayerObs → ℝ)
    (hH : Measurable H) : Measurable (layerRealKernel H)

theorem layerRealKernel_encode (H : LayerObs × LayerObs → ℝ) (o o' : LayerObs) :
    layerRealKernel H (layerEncode o, layerEncode o') = H (o, o')

theorem layerRealKernel_eq_zero (H : LayerObs × LayerObs → ℝ) (z : ℝ × ℝ)
    (hz : z ∉ layerEncodedSet ×ˢ layerEncodedSet) : layerRealKernel H z = 0

theorem layerRealKernel_symmetric (H : LayerObs × LayerObs → ℝ)
    (hH : ∀ o o', H (o, o') = H (o', o)) (x y : ℝ) :
    layerRealKernel H (x, y) = layerRealKernel H (y, x)

theorem layerRealKernel_integral (μ : Measure LayerObs) [SFinite μ]
    (H : LayerObs × LayerObs → ℝ) :
    (∫ z, layerRealKernel H z ∂(layerRealLaw μ).prod (layerRealLaw μ)) =
      ∫ z, H z ∂μ.prod μ

theorem layerRealKernel_integrable_iff (μ : Measure LayerObs) [SFinite μ]
    (H : LayerObs × LayerObs → ℝ) :
    Integrable (layerRealKernel H) ((layerRealLaw μ).prod (layerRealLaw μ)) ↔
      Integrable H (μ.prod μ)

theorem layerRealKernel_memLp_iff (μ : Measure LayerObs) [SFinite μ]
    (H : LayerObs × LayerObs → ℝ) (p : ℝ≥0∞) :
    MemLp (layerRealKernel H) p ((layerRealLaw μ).prod (layerRealLaw μ)) ↔
      MemLp H p (μ.prod μ)

theorem layerRealKernel_integral_sq (μ : Measure LayerObs) [SFinite μ]
    (H : LayerObs × LayerObs → ℝ) :
    (∫ z, layerRealKernel H z ^ 2 ∂(layerRealLaw μ).prod (layerRealLaw μ)) =
      ∫ z, H z ^ 2 ∂μ.prod μ

theorem layerRealKernel_integrable_sq (μ : Measure LayerObs) [SFinite μ]
    (H : LayerObs × LayerObs → ℝ) (hH : MemLp H 2 (μ.prod μ)) :
    Integrable (fun z => H z ^ 2) (μ.prod μ) ∧
      Integrable (fun z => layerRealKernel H z ^ 2)
        ((layerRealLaw μ).prod (layerRealLaw μ))

end
end Shao.OQ5.P50
```
