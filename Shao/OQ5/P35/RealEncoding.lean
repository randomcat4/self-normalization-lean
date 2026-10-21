import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Borel coding of the p35 category and continuous coordinate

Source: current/oq56/inputs02/p35.md §3, X = 3C + A with A ∈ [-1,1].
The formulas outside these support intervals are a fixed Borel extension.
This file contains deterministic coding only, without a probability claim.
-/

set_option autoImplicit false

namespace Shao.OQ5.P35

noncomputable section

/-- Encode a natural category and a real noise coordinate by one real value. -/
def encodeObservation (c : ℕ) (a : ℝ) : ℝ := 3 * (c : ℝ) + a

/-- The category decoder, defined on all real observations. -/
def decodeCategory (x : ℝ) : ℕ := Nat.floor ((x + 1) / 3)

/-- The noise decoder, defined on all real observations. -/
def decodeNoise (x : ℝ) : ℝ := x - 3 * (decodeCategory x : ℝ)

theorem measurable_encodeObservation :
    Measurable (fun ca : ℕ × ℝ => encodeObservation ca.1 ca.2) := by
  have hc : Measurable (fun c : ℕ => (c : ℝ)) := measurable_of_countable _
  exact (measurable_const.mul (hc.comp measurable_fst)).add measurable_snd

theorem measurable_decodeCategory : Measurable decodeCategory := by
  exact ((measurable_id.add_const 1).div_const 3).nat_floor

theorem measurable_decodeNoise : Measurable decodeNoise := by
  have hc : Measurable (fun c : ℕ => (c : ℝ)) := measurable_of_countable _
  exact measurable_id.sub (measurable_const.mul (hc.comp measurable_decodeCategory))

/-- Recovery includes both endpoints of the closed noise interval. -/
theorem decodeCategory_encode (c : ℕ) (a : ℝ)
    (ha : a ∈ Set.Icc (-1 : ℝ) 1) :
    decodeCategory (encodeObservation c a) = c := by
  have hc : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
  have hnonneg : 0 ≤ (3 * (c : ℝ) + a + 1) / 3 := by linarith [ha.1]
  apply (Nat.floor_eq_iff hnonneg).2
  constructor <;> linarith [ha.1, ha.2]

theorem decodeNoise_encode (c : ℕ) (a : ℝ)
    (ha : a ∈ Set.Icc (-1 : ℝ) 1) :
    decodeNoise (encodeObservation c a) = a := by
  unfold decodeNoise
  rw [decodeCategory_encode c a ha]
  unfold encodeObservation
  ring

/-- Global reconstruction does not claim that the decoded noise is in [-1,1]. -/
theorem encode_decode (x : ℝ) :
    encodeObservation (decodeCategory x) (decodeNoise x) = x := by
  unfold encodeObservation decodeNoise
  ring

end

end Shao.OQ5.P35
