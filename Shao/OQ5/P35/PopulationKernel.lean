import Shao.OQ5.P35.FixedLawCoefficients
import Shao.OQ5.P35.RealEncoding
import Shao.OQ5.P35.RowIdentity

/-!
# The fixed Borel kernel from the original p35 construction

Source: current/oq56/inputs02/p35.md §3, formula (8). This is the raw,
uncentered, unscaled kernel. The finite-row bridge uses the previously proved
matrix definition without changing the population kernel with sample size.
-/

set_option autoImplicit false

namespace Shao.OQ5.P35

noncomputable section

/-- The category offset, decoded from a real observation. -/
def observationOffset (x : ℝ) : ℝ := categoryOffset (decodeCategory x)

/-- The centered category feature, decoded from a real observation. -/
def observationFeature (x : ℝ) : ℝ := categoryFeature (decodeCategory x)

/-- The raw fixed symmetric p35 population kernel. -/
def populationKernel (x y : ℝ) : ℝ :=
  decodeNoise x + decodeNoise y + observationOffset x + observationOffset y -
    observationFeature x * observationFeature y

theorem measurable_observationOffset : Measurable observationOffset :=
  (measurable_of_countable categoryOffset).comp measurable_decodeCategory

theorem measurable_observationFeature : Measurable observationFeature :=
  (measurable_of_countable categoryFeature).comp measurable_decodeCategory

theorem measurable_populationKernel :
    Measurable (fun xy : ℝ × ℝ => populationKernel xy.1 xy.2) := by
  exact ((((measurable_decodeNoise.comp measurable_fst).add
    (measurable_decodeNoise.comp measurable_snd)).add
    (measurable_observationOffset.comp measurable_fst)).add
    (measurable_observationOffset.comp measurable_snd)).sub
    ((measurable_observationFeature.comp measurable_fst).mul
      (measurable_observationFeature.comp measurable_snd))

theorem populationKernel_symmetric (x y : ℝ) :
    populationKernel x y = populationKernel y x := by
  unfold populationKernel
  ring

theorem observationOffset_encode (c : ℕ) (a : ℝ)
    (ha : a ∈ Set.Icc (-1 : ℝ) 1) :
    observationOffset (encodeObservation c a) = categoryOffset c := by
  unfold observationOffset
  rw [decodeCategory_encode c a ha]

theorem observationFeature_encode (c : ℕ) (a : ℝ)
    (ha : a ∈ Set.Icc (-1 : ℝ) 1) :
    observationFeature (encodeObservation c a) = categoryFeature c := by
  unfold observationFeature
  rw [decodeCategory_encode c a ha]

theorem populationKernel_encode (c d : ℕ) (a b : ℝ)
    (ha : a ∈ Set.Icc (-1 : ℝ) 1) (hb : b ∈ Set.Icc (-1 : ℝ) 1) :
    populationKernel (encodeObservation c a) (encodeObservation d b) =
      a + b + categoryOffset c + categoryOffset d - categoryFeature c * categoryFeature d := by
  simp only [populationKernel, decodeNoise_encode c a ha, decodeNoise_encode d b hb,
    observationOffset_encode c a ha, observationOffset_encode d b hb,
    observationFeature_encode c a ha, observationFeature_encode d b hb]

/-- Evaluate the same fixed kernel in the exact finite matrix from RowIdentity. -/
theorem populationKernel_sample {n : ℕ} (X : Fin n → ℝ) (i j : Fin n) :
    populationKernel (X i) (X j) =
      kernel (fun i => decodeNoise (X i)) (fun i => observationOffset (X i))
        (fun i => observationFeature (X i)) i j := rfl

end

end Shao.OQ5.P35
