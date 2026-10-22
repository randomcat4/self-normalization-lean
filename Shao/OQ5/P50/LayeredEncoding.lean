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

theorem measurable_layerEncode : Measurable layerEncode :=
  measurable_embeddingReal _

theorem layerEncode_injective : Function.Injective layerEncode :=
  (measurableEmbedding_embeddingReal _).injective

theorem measurableSet_layerEncodedSet : MeasurableSet layerEncodedSet :=
  (measurableEmbedding_embeddingReal _).measurableSet_range

theorem measurable_layerDecode : Measurable layerDecode :=
  (measurableEmbedding_embeddingReal _).measurable_invFun

theorem layerDecode_encode (o : ℝ × (ℕ → Fin 3)) :
    layerDecode (layerEncode o) = o :=
  (measurableEmbedding_embeddingReal _).leftInverse_invFun o

theorem layerEncode_decode (x : ℝ) (hx : x ∈ layerEncodedSet) :
    layerEncode (layerDecode x) = x := by
  obtain ⟨o, rfl⟩ := hx
  rw [layerDecode_encode]

theorem layerDecode_encode_first (o : ℝ × (ℕ → Fin 3)) :
    (layerDecode (layerEncode o)).1 = o.1 := by
  rw [layerDecode_encode]

theorem layerDecode_encode_layer (o : ℝ × (ℕ → Fin 3)) (j : ℕ) :
    (layerDecode (layerEncode o)).2 j = o.2 j := by
  rw [layerDecode_encode]

end
end Shao.OQ5.P50
