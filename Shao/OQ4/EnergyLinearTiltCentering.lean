import Shao.OQ4.EnergyLinearTiltVarianceWindow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-! A zero parameter for the same actual linear energy family, with a common explicit range. -/

namespace Shao.OQ4

open MeasureTheory

noncomputable def energyLinearCenteringK (M T : ℝ) : ℝ :=
  1 + 4 * energyLinearVarianceA M T

noncomputable def energyLinearCenteringThreshold (M T : ℝ) : ℝ :=
  energyLinearVarianceThreshold M T (energyLinearCenteringK M T)

theorem energyLinearCentering_K_pos (M T : ℝ) (hM : 0 ≤ M) (hT : 0 ≤ T) :
    0 < energyLinearCenteringK M T := by
  have hP : 0 ≤ energyE1Constant T := le_trans (by norm_num) (energyE1Constant_dominates T hT).1
  unfold energyLinearCenteringK energyLinearVarianceA
  positivity

theorem energyLinearCentering_height_bounds (M T h : ℝ) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hh : energyLinearCenteringThreshold M T ≤ h) :
    0 < energyLinearCenteringK M T ∧ energyLogThreshold M T ≤ h ∧ 2 ≤ h ∧
      0 < energyLinearCenteringK M T / h ^ 2 := by
  have hK := energyLinearCentering_K_pos M T hM hT
  have hheight := energyLinearVariance_height_bounds M T (energyLinearCenteringK M T) h hM hT hK.le hh
  exact ⟨hK, hheight.1, hheight.2.1, div_pos hK (pow_pos (by linarith [hheight.2.1]) 2)⟩

section Admissible

variable (ν : Measure ℝ) [IsProbabilityMeasure ν] (M T h s : ℝ)
  (hM : 0 ≤ M) (hT : 0 ≤ T) (hh : energyLinearCenteringThreshold M T ≤ h) (hs : |s| ≤ T)
  (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν)
  (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) (hmean : (∫ x : ℝ, x ∂ν) = 0)
  (hβM : (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ M)

include hM hT hh hs hSq hCube hsecond hmean hβM

/-- The true parameter-zero identity and the E1 error are distinct supplied facts. -/
theorem energyLinearCentering_initial_mean :
    energyLinearMean ν h s 0 = (∫ x : ℝ, x ∂energyTiltedLaw ν h s) ∧
    |∫ x : ℝ, x ∂energyTiltedLaw ν h s| ≤ energyLinearVarianceA M T / h ^ 2 := by
  have hK := energyLinearCentering_K_pos M T hM hT
  have hh2 := (energyLinearCentering_height_bounds M T h hM hT hh).2.2.1
  have hi := energyLinearVariance_initial_bounds ν M T (energyLinearCenteringK M T) h s
    hM hT hK.le hh hs hSq hCube hsecond hmean hβM
  exact ⟨energyLinearMean_zero ν T h s hT (by linarith) hs hSq hsecond, hi.2.2.1⟩

/-- Lagrange's mean value theorem is applied only inside the certified closed window. -/
theorem energyLinearCentering_interval_growth (x y : ℝ) (hxy : x < y)
    (hx : -(energyLinearCenteringK M T / h ^ 2) ≤ x) (hy : y ≤ energyLinearCenteringK M T / h ^ 2) :
    (1 / 2 : ℝ) * (y - x) ≤ energyLinearMean ν h s y - energyLinearMean ν h s x := by
  have hK := energyLinearCentering_K_pos M T hM hT
  have hh2 := (energyLinearCentering_height_bounds M T h hM hT hh).2.2.1
  have hcont := (energyLinear_family_continuous ν T h s hT (by linarith) hs hSq hsecond hCube).2.2.1
  let v : ℝ → ℝ := fun u => ∫ z : ℝ, (z - energyLinearMean ν h s u) ^ 2 ∂energyLinearTiltLaw ν h s u
  have hw (u : ℝ) (hu : u ∈ Set.Ioo x y) :
      (1 / 2 : ℝ) ≤ v u ∧ HasDerivAt (energyLinearMean ν h s) (v u) u := by
    have hu' : |u| ≤ energyLinearCenteringK M T / h ^ 2 := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hW := energyLinearVariance_window ν M T (energyLinearCenteringK M T) h s
      hM hT hK.le hh hs hSq hCube hsecond hmean hβM u hu'
    exact ⟨hW.2.2.2.2.2.1.1, hW.2.2.2.2.2.2⟩
  obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope (energyLinearMean ν h s) v hxy hcont.continuousOn
    (fun u hu => (hw u hu).2)
  apply (le_div_iff₀ (sub_pos.mpr hxy)).1
  rw [← heq]
  exact (hw c hc).1

/-- The constant's positive margin yields strict signs, without centering μ in advance. -/
theorem energyLinearCentering_endpoints :
    energyLinearMean ν h s (-(energyLinearCenteringK M T / h ^ 2)) < 0 ∧
    0 < energyLinearMean ν h s (energyLinearCenteringK M T / h ^ 2) := by
  let a : ℝ := energyLinearCenteringK M T / h ^ 2
  have hheight := energyLinearCentering_height_bounds M T h hM hT hh
  have ha : 0 < a := hheight.2.2.2
  have hA : 0 ≤ energyLinearVarianceA M T :=
    (energyLinearVariance_constants_nonneg M T (energyLinearCenteringK M T) hM hT hheight.1.le).1
  obtain ⟨hzero, hinit⟩ := energyLinearCentering_initial_mean ν M T h s hM hT hh hs hSq hCube hsecond hmean hβM
  rw [← hzero] at hinit
  have hi := abs_le.mp hinit
  have hright := energyLinearCentering_interval_growth ν M T h s hM hT hh hs hSq hCube hsecond hmean hβM
    0 a ha (by linarith) le_rfl
  have hleft := energyLinearCentering_interval_growth ν M T h s hM hT hh hs hSq hCube hsecond hmean hβM
    (-a) 0 (by linarith) le_rfl (by linarith)
  have hmargin : 0 < (1 / 2 : ℝ) * a - energyLinearVarianceA M T / h ^ 2 := by
    have heq : (1 / 2 : ℝ) * a - energyLinearVarianceA M T / h ^ 2 =
        ((1 / 2 : ℝ) + energyLinearVarianceA M T) / h ^ 2 := by
      dsimp only [a, energyLinearCenteringK]
      ring
    rw [heq]
    exact div_pos (by linarith) (pow_pos (by linarith [hheight.2.2.1]) 2)
  change energyLinearMean ν h s (-a) < 0 ∧ 0 < energyLinearMean ν h s a
  constructor <;> linarith

/-- A zero exists for the same real function and explicit parameter interval. -/
theorem energyLinearCentering_exists :
    ∃ θ : ℝ, |θ| ≤ energyLinearCenteringK M T / h ^ 2 ∧ energyLinearMean ν h s θ = 0 := by
  let a : ℝ := energyLinearCenteringK M T / h ^ 2
  have hheight := energyLinearCentering_height_bounds M T h hM hT hh
  have ha : 0 < a := hheight.2.2.2
  have hcont := (energyLinear_family_continuous ν T h s hT (by linarith [hheight.2.2.1]) hs hSq hsecond hCube).2.2.1
  have he := energyLinearCentering_endpoints ν M T h s hM hT hh hs hSq hCube hsecond hmean hβM
  have hmem : (0 : ℝ) ∈ Set.Icc (energyLinearMean ν h s (-a)) (energyLinearMean ν h s a) := ⟨he.1.le, he.2.le⟩
  obtain ⟨θ, hθ, hzero⟩ := intermediate_value_Icc (by linarith : -a ≤ a) hcont.continuousOn hmem
  exact ⟨θ, abs_le.mpr hθ, hzero⟩

/-- This is the actual law with the same θ and actual exp(θx)/L(θ) density. -/
theorem energyLinearCentering_law :
    ∃ θ : ℝ, |θ| ≤ energyLinearCenteringK M T / h ^ 2 ∧ energyLinearMean ν h s θ = 0 ∧
      IsProbabilityMeasure (energyLinearTiltLaw ν h s θ) ∧
      (∀ᵐ x ∂energyLinearTiltLaw ν h s θ, |x| ≤ 2 * h) ∧
      Integrable (fun x : ℝ => x) (energyLinearTiltLaw ν h s θ) ∧
      Integrable (fun x : ℝ => x ^ 2) (energyLinearTiltLaw ν h s θ) ∧
      Integrable (fun x : ℝ => |x| ^ 3) (energyLinearTiltLaw ν h s θ) ∧
      (∫ x : ℝ, x ∂energyLinearTiltLaw ν h s θ) = 0 := by
  obtain ⟨θ, hθ, hzero⟩ := energyLinearCentering_exists ν M T h s hM hT hh hs hSq hCube hsecond hmean hβM
  have hh2 := (energyLinearCentering_height_bounds M T h hM hT hh).2.2.1
  have hh1 : 1 ≤ h := by linarith
  have hmom := energyLinearTiltLaw_moments ν T h s hT hh1 hs hSq hsecond θ
  exact ⟨θ, hθ, hzero, energyLinearTiltLaw_isProbabilityMeasure ν T h s hT hh1 hs hSq hsecond θ,
    energyLinearTiltLaw_ae_support ν h s θ, hmom.1, hmom.2.1, hmom.2.2.1, hmom.2.2.2.2.1.trans hzero⟩

end Admissible

end Shao.OQ4
