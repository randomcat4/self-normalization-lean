import Shao.OQ6.ScalarObservationCoding
import Mathlib.MeasureTheory.Function.Floor

set_option autoImplicit false

namespace Shao.OQ6.QuantizedObservationCoding

noncomputable section

open MeasureTheory
open scoped Classical

noncomputable def quantizedObservation
    {X : Type*} (ε : ℝ) (ξ c : X → ℝ) (x : X) : ℝ :=
  ε * ((Int.floor (ξ x / ε) : ℝ) + c x)

def deterministicAffineObservation
    {X : Type*} (a s : ℝ) (Y : X → ℝ) (x : X) : ℝ :=
  (Y x - a) / s

private theorem quantized_numerical_spec
    (ε r b : ℝ) (hε : 0 < ε)
    (hb : (1 / 3 : ℝ) ≤ b ∧ b ≤ (2 / 3 : ℝ)) :
    let y : ℝ := ε * ((Int.floor (r / ε) : ℝ) + b)
    |y - r| ≤ ε ∧
    Int.floor (y / ε) = Int.floor (r / ε) ∧
    y / ε - (Int.floor (y / ε) : ℝ) = b := by
  dsimp only
  let k : ℤ := Int.floor (r / ε)
  have hε0 : ε ≠ 0 := ne_of_gt hε
  have hklo : (k : ℝ) ≤ r / ε := Int.floor_le (r / ε)
  have hkhi : r / ε < (k : ℝ) + 1 := Int.lt_floor_add_one (r / ε)
  have hscale : ε * (r / ε) = r := by
    field_simp [hε0] <;> ring
  have hmullo : ε * (k : ℝ) ≤ r := by
    have h := mul_le_mul_of_nonneg_left hklo hε.le
    rw [hscale] at h
    exact h
  have hmulhi : r < ε * ((k : ℝ) + 1) := by
    have h := mul_lt_mul_of_pos_left hkhi hε
    rw [hscale] at h
    exact h
  have hblo : ε * (1 / 3 : ℝ) ≤ ε * b :=
    mul_le_mul_of_nonneg_left hb.1 hε.le
  have hbhi : ε * b ≤ ε * (2 / 3 : ℝ) :=
    mul_le_mul_of_nonneg_left hb.2 hε.le
  have herr : |ε * ((k : ℝ) + b) - r| ≤ ε := by
    apply abs_le.mpr
    constructor <;> nlinarith only [hmullo, hmulhi, hblo, hbhi, hε]
  have hratio : ε * ((k : ℝ) + b) / ε = (k : ℝ) + b := by
    field_simp [hε0] <;> ring
  have hfloor : Int.floor (ε * ((k : ℝ) + b) / ε) = k := by
    rw [hratio]
    apply Int.floor_eq_iff.mpr
    constructor <;> linarith [hb.1, hb.2]
  have hdecode :
      ε * ((k : ℝ) + b) / ε -
        (Int.floor (ε * ((k : ℝ) + b) / ε) : ℝ) = b := by
    rw [hfloor, hratio]
    ring
  exact ⟨herr, hfloor, hdecode⟩

private theorem comap_eq_of_measurable_recovery
    {X : Type*} [mX : MeasurableSpace X]
    (c Y : X → ℝ) (hY : Measurable Y)
    (hc : MeasurableSpace.comap c (borel ℝ) = mX)
    (d : ℝ → ℝ) (hd : Measurable d)
    (hrecover : ∀ x : X, d (Y x) = c x) :
    MeasurableSpace.comap Y (borel ℝ) = mX := by
  have heq : c = d ∘ Y := by
    funext x
    exact (hrecover x).symm
  apply le_antisymm
  · exact hY.comap_le
  · rw [← hc]
    exact MeasurableSpace.comap_le_comap_of_eq_comp d hd heq

private theorem level_null_of_recovery
    {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (c Y : X → ℝ) (d : ℝ → ℝ)
    (hrecover : ∀ x : X, d (Y x) = c x)
    (hnull : ∀ t : ℝ, ν ({x : X | c x = t}) = 0)
    (t : ℝ) :
    ν ({x : X | Y x = t}) = 0 := by
  have hsub : {x : X | Y x = t} ⊆ {x : X | c x = d t} := by
    intro x hx
    exact (hrecover x).symm.trans (congrArg d hx)
  apply le_antisymm _ bot_le
  calc
    ν ({x : X | Y x = t}) ≤ ν ({x : X | c x = d t}) :=
      measure_mono hsub
    _ = 0 := hnull (d t)

theorem quantized_observation_spec
    {X : Type*} [mX : MeasurableSpace X]
    (ξ c : X → ℝ) (hξ : Measurable ξ) (hc : Measurable c)
    (hrange : ∀ x : X, (1 / 3 : ℝ) ≤ c x ∧ c x ≤ (2 / 3 : ℝ))
    (hcomap : MeasurableSpace.comap c (borel ℝ) = mX)
    (ε : ℝ) (hε : 0 < ε) :
    let Y : X → ℝ := quantizedObservation ε ξ c
    let D : ℝ → ℝ := fun y : ℝ => y / ε - (Int.floor (y / ε) : ℝ)
    Measurable Y ∧
    Measurable D ∧
    (∀ x : X, |Y x - ξ x| ≤ ε) ∧
    (∀ x : X, Int.floor (Y x / ε) = Int.floor (ξ x / ε)) ∧
    (∀ x : X, D (Y x) = c x) ∧
    MeasurableSpace.comap Y (borel ℝ) = mX ∧
    (∀ (ν : Measure X),
      (∀ t : ℝ, ν ({x : X | c x = t}) = 0) →
      ∀ t : ℝ, ν ({x : X | Y x = t}) = 0) := by
  dsimp only
  let Y : X → ℝ := quantizedObservation ε ξ c
  let D : ℝ → ℝ := fun y : ℝ => y / ε - (Int.floor (y / ε) : ℝ)
  have hε0 : ε ≠ 0 := ne_of_gt hε
  have hnum (x : X) :
      |Y x - ξ x| ≤ ε ∧
      Int.floor (Y x / ε) = Int.floor (ξ x / ε) ∧
      D (Y x) = c x := by
    simpa only [Y, D, quantizedObservation] using
      quantized_numerical_spec ε (ξ x) (c x) hε (hrange x)
  have hfrac : Measurable (fun x : X => Int.fract (ξ x / ε)) :=
    (hξ.div_const ε).fract
  have hYeq :
      Y = fun x : X => ξ x + ε * (c x - Int.fract (ξ x / ε)) := by
    funext x
    dsimp only [Y, quantizedObservation, Int.fract]
    have hcancel : ε * (ξ x / ε) = ξ x := by
      field_simp [hε0] <;> ring
    calc
      ε * ((Int.floor (ξ x / ε) : ℝ) + c x) =
          ε * (ξ x / ε) +
            ε * (c x - (ξ x / ε - (Int.floor (ξ x / ε) : ℝ))) := by ring
      _ = ξ x +
          ε * (c x - (ξ x / ε - (Int.floor (ξ x / ε) : ℝ))) := by
        rw [hcancel]
  have hY : Measurable Y := by
    rw [hYeq]
    exact hξ.add (measurable_const.mul (hc.sub hfrac))
  have hD : Measurable D := by
    simpa only [D, Int.fract, id_eq] using
      (((measurable_id : Measurable (fun y : ℝ => y)).div_const ε).fract)
  have hdecode : ∀ x : X, D (Y x) = c x :=
    fun x => (hnum x).2.2
  refine ⟨hY, hD, (fun x => (hnum x).1), (fun x => (hnum x).2.1),
    hdecode, ?_, ?_⟩
  · exact comap_eq_of_measurable_recovery c Y hY hcomap D hD hdecode
  · intro ν hnull t
    exact level_null_of_recovery ν c Y D hdecode hnull t

theorem deterministic_affine_observation_spec
    {X : Type*} [mX : MeasurableSpace X]
    (Y : X → ℝ) (hY : Measurable Y)
    (hcomap : MeasurableSpace.comap Y (borel ℝ) = mX)
    (a s : ℝ) (hs : 0 < s) :
    let η : X → ℝ := deterministicAffineObservation a s Y
    let R : ℝ → ℝ := fun t : ℝ => s * t + a
    Measurable η ∧
    Measurable R ∧
    (∀ x : X, R (η x) = Y x) ∧
    MeasurableSpace.comap η (borel ℝ) = mX ∧
    (∀ (ν : Measure X),
      (∀ t : ℝ, ν ({x : X | Y x = t}) = 0) →
      ∀ t : ℝ, ν ({x : X | η x = t}) = 0) := by
  dsimp only
  let η : X → ℝ := deterministicAffineObservation a s Y
  let R : ℝ → ℝ := fun t : ℝ => s * t + a
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hη : Measurable η := by
    exact (hY.sub_const a).div_const s
  have hR : Measurable R := by
    change Measurable (fun t : ℝ => s * t + a)
    exact (measurable_const.mul measurable_id).add measurable_const
  have hrecover : ∀ x : X, R (η x) = Y x := by
    intro x
    dsimp only [R, η, deterministicAffineObservation]
    field_simp [hs0] <;> ring
  refine ⟨hη, hR, hrecover, ?_, ?_⟩
  · exact comap_eq_of_measurable_recovery Y η hη hcomap R hR hrecover
  · intro ν hnull t
    exact level_null_of_recovery ν Y η R hrecover hnull t

end

end Shao.OQ6.QuantizedObservationCoding
