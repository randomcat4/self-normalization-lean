import Shao.C2.ScaledBrownianEndpointDensity

noncomputable section
namespace Shao.C2.PhysicalBrownianEndpointDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.ScaledBrownianEndpointDensity

def normalizedPhysicalBrownian {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) :
    ℝ≥0 → Ω → ℝ := fun t ω => (Real.sqrt (T : ℝ))⁻¹ * B (T * t) ω

theorem isBrownianReal_normalizedPhysicalBrownian {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) (hT : T ≠ 0) :
    IsBrownianReal (normalizedPhysicalBrownian B T) P := by
  exact hB.smul hT

private theorem normalizedPhysicalBrownian_reconstruct {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (hT : T ≠ 0) (t : ℝ≥0) (ω : Ω) :
    Real.sqrt (T : ℝ) * normalizedPhysicalBrownian B T t ω = B (T * t) ω := by
  have hTpos : 0 < (T : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hT : 0 < T)
  have hs : Real.sqrt (T : ℝ) ≠ 0 := (Real.sqrt_pos.2 hTpos).ne'
  unfold normalizedPhysicalBrownian
  rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]

theorem brownian_physical_interval_joint_hasDerivAt {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y z : ℝ) (T : ℝ≥0) (hT : T ≠ 0) :
    HasDerivAt (fun v : ℝ => P.real {ω |
      (∀ t : BridgeTime, |y + B (T * ⟨(t : ℝ), t.property.1⟩) ω| < a) ∧ y + B T ω ≤ v})
      (gaussianPDFReal y T z *
        intervalCompletion (bridgeLaw (normalizedPhysicalBrownian B T) P) a y (T : ℝ) z) z := by
  have hTpos : 0 < (T : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hT : 0 < T)
  have hC := isBrownianReal_normalizedPhysicalBrownian B P hB T hT
  have hd := brownian_scaled_interval_joint_hasDerivAt
    (normalizedPhysicalBrownian B T) P hC a y (T : ℝ) z hTpos
  have heq : (fun v : ℝ => P.real {ω |
      (∀ t : BridgeTime, |y + Real.sqrt (T : ℝ) * normalizedPhysicalBrownian B T ⟨(t : ℝ), t.property.1⟩ ω| < a) ∧
        y + Real.sqrt (T : ℝ) * normalizedPhysicalBrownian B T 1 ω ≤ v}) =
      (fun v : ℝ => P.real {ω |
        (∀ t : BridgeTime, |y + B (T * ⟨(t : ℝ), t.property.1⟩) ω| < a) ∧ y + B T ω ≤ v}) := by
    funext v
    congr 1
    ext ω
    change ((∀ t : BridgeTime,
        |y + Real.sqrt (T : ℝ) * normalizedPhysicalBrownian B T ⟨(t : ℝ), t.property.1⟩ ω| < a) ∧
        y + Real.sqrt (T : ℝ) * normalizedPhysicalBrownian B T 1 ω ≤ v) ↔ _
    rw [normalizedPhysicalBrownian_reconstruct B T hT 1 ω, mul_one]
    refine and_congr ?_ Iff.rfl
    apply forall_congr'
    intro t
    rw [normalizedPhysicalBrownian_reconstruct B T hT ⟨(t : ℝ), t.property.1⟩ ω]
  rw [heq] at hd
  exact hd

theorem brownian_physical_interval_density_ratio {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y z : ℝ) (T : ℝ≥0) (hT : T ≠ 0) :
    deriv (fun v : ℝ => P.real {ω |
      (∀ t : BridgeTime, |y + B (T * ⟨(t : ℝ), t.property.1⟩) ω| < a) ∧ y + B T ω ≤ v}) z /
      gaussianPDFReal y T z =
        intervalCompletion (bridgeLaw (normalizedPhysicalBrownian B T) P) a y (T : ℝ) z := by
  rw [(brownian_physical_interval_joint_hasDerivAt B P hB a y z T hT).deriv]
  have hp : gaussianPDFReal y T z ≠ 0 := (gaussianPDFReal_pos y T z hT).ne'
  field_simp [hp]

end Shao.C2.PhysicalBrownianEndpointDensity
