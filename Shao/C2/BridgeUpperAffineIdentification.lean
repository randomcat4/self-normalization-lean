import Shao.C2.BridgeUpperPointwise
import Shao.C2.SourceHalfLineCompletion

noncomputable section
namespace Shao.C2.BridgeUpperAffineIdentification
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.BridgeUpperPointwise Shao.C2.SourceHalfLineCompletion

theorem upperCompletion_affine (ν : Measure BridgeNoise) (a y T z : ℝ) (hT : 0 < T) :
    upperCompletion ν a y T z =
      upperCompletion ν ((a - y) / Real.sqrt T) 0 1 ((z - y) / Real.sqrt T) := by
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hp (g : BridgeNoise) (t : BridgeTime) :
      bridgePath y T z g t = y + Real.sqrt T * bridgePath 0 1 ((z - y) / Real.sqrt T) g t := by
    change (1 - (t : ℝ)) * y + (t : ℝ) * z + Real.sqrt T * g.val t =
      y + Real.sqrt T * ((1 - (t : ℝ)) * 0 + (t : ℝ) * ((z - y) / Real.sqrt T) +
        Real.sqrt 1 * g.val t)
    rw [Real.sqrt_one]
    field_simp [ne_of_gt hs]
    <;> ring
  unfold upperCompletion
  apply congrArg (fun S : Set BridgeNoise => ν.real S)
  ext g
  change (∀ t : BridgeTime, bridgePath y T z g t < a) ↔
    ∀ t : BridgeTime, bridgePath 0 1 ((z - y) / Real.sqrt T) g t < (a - y) / Real.sqrt T
  constructor
  · intro h t
    have ht := h t
    rw [hp g t] at ht
    apply (lt_div_iff₀ hs).mpr
    nlinarith
  · intro h t
    have ht := (lt_div_iff₀ hs).mp (h t)
    rw [hp g t]
    nlinarith

theorem bridge_upper_formula {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y T z : ℝ)
    (hT : 0 < T) (hy : y < a) (hz : z < a) :
    upperCompletion (bridgeLaw B P) a y T z =
      1 - Real.exp (-2 * (a - y) * (a - z) / T) := by
  let s : ℝ := Real.sqrt T
  have hs : 0 < s := Real.sqrt_pos.mpr hT
  have hs2 : s ^ 2 = T := Real.sq_sqrt hT.le
  have hwall : 0 < (a - y) / s := div_pos (sub_pos.mpr hy) hs
  have hend : (z - y) / s < (a - y) / s :=
    (div_lt_div_iff_of_pos_right hs).mpr (by linarith)
  rw [upperCompletion_affine (bridgeLaw B P) a y T z hT,
    bridge_upper_unit_formula B P hB _ _ hwall hend]
  apply congrArg (fun r : ℝ => 1 - Real.exp r)
  change -2 * ((a - y) / s) * ((a - y) / s - (z - y) / s) = -2 * (a - y) * (a - z) / T
  calc
    _ = (-2 * (a - y) * (a - z)) / (s ^ 2) := by
      field_simp [ne_of_gt hs]
      <;> ring
    _ = _ := by rw [hs2]

theorem source_upper_eq_scalar {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a z : ℝ) (ha : 0 < a) (hz : z < a) :
    (fun y T : ℝ => sourceUpperCompletion (bridgeLaw B P) a y T z) =
      (fun y T : ℝ => Shao.C2.HalfLinePhysicalGaussian.upperCompletion a y T z) := by
  apply sourceUpperCompletion_eq_scalar_of_reflection (bridgeLaw B P) a z ha hz
  intro T hT y hy
  exact bridge_upper_formula B P hB a y T z hT hy hz

end Shao.C2.BridgeUpperAffineIdentification
