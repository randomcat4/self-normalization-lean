import Shao.C1.Normalization
import Shao.C2.TwoSided
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Measurability of finite paths and their events

The measurable structure on `Path n` is the product of the real Borel structures.
All unnormalized path statistics below are continuous. The normalized statistics
are measurable with their original explicit zero-energy branch.
-/

namespace Shao

variable {n : ℕ}

theorem continuous_prefixSum (k : ℕ) :
    Continuous (fun a : Path n => prefixSum a k) := by
  exact continuous_finsetSum _ (fun i _ => continuous_apply i)

theorem continuous_prefixSquares (k : ℕ) :
    Continuous (fun a : Path n => prefixSquares a k) := by
  exact continuous_finsetSum _ (fun i _ => (continuous_apply i).pow 2)

theorem continuous_energy : Continuous (energy : Path n → ℝ) := by
  exact continuous_finsetSum _ (fun i _ => (continuous_apply i).pow 2)

theorem continuous_upperMax (hn : 0 < n) :
    Continuous (fun a : Path n => upperMax a hn) := by
  unfold upperMax
  exact Continuous.finset_sup'_apply _ (fun k _ => continuous_prefixSum k)

theorem continuous_lowerMax (hn : 0 < n) :
    Continuous (fun a : Path n => lowerMax a hn) := by
  exact (continuous_upperMax hn).comp continuous_neg

theorem continuous_absMax (hn : 0 < n) :
    Continuous (fun a : Path n => absMax a hn) := by
  exact (continuous_upperMax hn).max (continuous_lowerMax hn)

theorem continuous_maxWithZero : Continuous (maxWithZero : Path n → ℝ) := by
  unfold maxWithZero
  exact Continuous.finset_sup'_apply _ (fun k _ => continuous_prefixSum k)

theorem continuous_sqrt_energy :
    Continuous (fun a : Path n => Real.sqrt (energy a)) :=
  Real.continuous_sqrt.comp continuous_energy

theorem continuous_energyWall (x : ℝ) :
    Continuous (fun a : Path n => x * Real.sqrt (energy a)) :=
  continuous_const.mul continuous_sqrt_energy

theorem measurable_prefixSum (k : ℕ) :
    Measurable (fun a : Path n => prefixSum a k) :=
  (continuous_prefixSum k).measurable

theorem measurable_prefixSquares (k : ℕ) :
    Measurable (fun a : Path n => prefixSquares a k) :=
  (continuous_prefixSquares k).measurable

theorem measurable_energy : Measurable (energy : Path n → ℝ) :=
  continuous_energy.measurable

theorem measurable_upperMax (hn : 0 < n) :
    Measurable (fun a : Path n => upperMax a hn) :=
  (continuous_upperMax hn).measurable

theorem measurable_lowerMax (hn : 0 < n) :
    Measurable (fun a : Path n => lowerMax a hn) :=
  (continuous_lowerMax hn).measurable

theorem measurable_absMax (hn : 0 < n) :
    Measurable (fun a : Path n => absMax a hn) :=
  (continuous_absMax hn).measurable

theorem measurable_maxWithZero : Measurable (maxWithZero : Path n → ℝ) :=
  continuous_maxWithZero.measurable

theorem measurable_sqrt_energy :
    Measurable (fun a : Path n => Real.sqrt (energy a)) :=
  continuous_sqrt_energy.measurable

theorem measurable_energyWall (x : ℝ) :
    Measurable (fun a : Path n => x * Real.sqrt (energy a)) :=
  (continuous_energyWall x).measurable

theorem measurableSet_zeroEnergy : MeasurableSet (zeroEnergy : Set (Path n)) :=
  (isClosed_eq continuous_energy continuous_const).measurableSet

theorem measurableSet_upperCrossing (hn : 0 < n) (x : ℝ) :
    MeasurableSet (upperCrossing hn x) :=
  measurableSet_le (measurable_energyWall x) (measurable_upperMax hn)

theorem measurableSet_lowerCrossing (hn : 0 < n) (x : ℝ) :
    MeasurableSet (lowerCrossing hn x) :=
  measurableSet_le (measurable_energyWall x) (measurable_lowerMax hn)

theorem measurableSet_absoluteCrossing (hn : 0 < n) (x : ℝ) :
    MeasurableSet (absoluteCrossing hn x) :=
  measurableSet_le (measurable_energyWall x) (measurable_absMax hn)

theorem measurableSet_upperStrictSurvival (hn : 0 < n) (x : ℝ) :
    MeasurableSet (upperStrictSurvival hn x) :=
  measurableSet_lt (measurable_upperMax hn) (measurable_energyWall x)

theorem measurableSet_lowerStrictSurvival (hn : 0 < n) (x : ℝ) :
    MeasurableSet (lowerStrictSurvival hn x) :=
  measurableSet_lt (measurable_lowerMax hn) (measurable_energyWall x)

theorem measurableSet_absoluteStrictSurvival (hn : 0 < n) (x : ℝ) :
    MeasurableSet (absoluteStrictSurvival hn x) :=
  measurableSet_lt (measurable_absMax hn) (measurable_energyWall x)

namespace C1

theorem measurable_normalizedEndpoint :
    Measurable (normalizedEndpoint : Path n → ℝ) := by
  unfold normalizedEndpoint
  exact Measurable.ite measurableSet_zeroEnergy measurable_const
    ((measurable_prefixSum n).div measurable_sqrt_energy)

theorem measurable_normalizedUpperMax (hn : 0 < n) :
    Measurable (fun a : Path n => normalizedUpperMax a hn) := by
  unfold normalizedUpperMax
  exact Measurable.ite measurableSet_zeroEnergy measurable_const
    ((measurable_upperMax hn).div measurable_sqrt_energy)

theorem measurableSet_upperNormalizedCDF (hn : 0 < n) (t : ℝ) :
    MeasurableSet (upperNormalizedCDF hn t) :=
  measurableSet_lt (measurable_normalizedUpperMax hn) measurable_const

theorem measurableSet_endpointRawCDF (t : ℝ) :
    MeasurableSet (endpointRawCDF t : Set (Path n)) :=
  measurableSet_lt (continuous_prefixSum n).abs.measurable (measurable_energyWall t)

theorem measurableSet_endpointNormalizedCDF (t : ℝ) :
    MeasurableSet (endpointNormalizedCDF t : Set (Path n)) :=
  measurableSet_lt (continuous_abs.measurable.comp measurable_normalizedEndpoint)
    measurable_const

end C1

namespace C2

theorem measurableSet_doubleCrossing (hn : 0 < n) (x : ℝ) :
    MeasurableSet (doubleCrossing hn x) :=
  (measurableSet_upperCrossing hn x).inter (measurableSet_lowerCrossing hn x)

end C2

section RandomPaths

variable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → Path n}

/-- Coordinatewise measurable random variables form a measurable random path. -/
theorem measurable_path_of_coordinates (hX : ∀ i, Measurable (fun ω => X ω i)) :
    Measurable X :=
  Measurable.of_eval hX

theorem measurable_prefixSum_comp (hX : Measurable X) (k : ℕ) :
    Measurable (fun ω => prefixSum (X ω) k) :=
  (measurable_prefixSum k).comp hX

theorem measurable_energy_comp (hX : Measurable X) :
    Measurable (fun ω => energy (X ω)) :=
  measurable_energy.comp hX

theorem measurable_upperMax_comp (hX : Measurable X) (hn : 0 < n) :
    Measurable (fun ω => upperMax (X ω) hn) :=
  (measurable_upperMax hn).comp hX

theorem measurable_absMax_comp (hX : Measurable X) (hn : 0 < n) :
    Measurable (fun ω => absMax (X ω) hn) :=
  (measurable_absMax hn).comp hX

theorem measurableSet_upperCrossing_preimage (hX : Measurable X)
    (hn : 0 < n) (x : ℝ) : MeasurableSet (X ⁻¹' upperCrossing hn x) :=
  (measurableSet_upperCrossing hn x).preimage hX

theorem measurableSet_absoluteCrossing_preimage (hX : Measurable X)
    (hn : 0 < n) (x : ℝ) : MeasurableSet (X ⁻¹' absoluteCrossing hn x) :=
  (measurableSet_absoluteCrossing hn x).preimage hX

end RandomPaths

end Shao
