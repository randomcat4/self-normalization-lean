import Shao.Basic.FinitePath
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact finite variance standardization

This is the frozen OQ4 finite K-to-Kv scaling interface from `b01/proof01.md`,
Section 1.  The weak survival event includes the empty prefix and permits paths
of length zero.  The moment statements apply to arbitrary measures with explicit
integrability hypotheses.  They do not establish the long-time theorem K or Kv.
-/

namespace Shao.OQ4

open MeasureTheory

/-- Exact finite path standardization and its closed-boundary survival event. -/
theorem path_variance_scaling {n : ℕ} (a : Path n) (σ h : ℝ)
    (hσ : 0 < σ) (_hh : 0 ≤ h) :
    (∀ k : ℕ, prefixSum (σ⁻¹ • a) k = prefixSum a k / σ) ∧
      energy (σ⁻¹ • a) = energy a / σ ^ 2 ∧
      ((∀ k : ℕ, k ≤ n → |prefixSum (σ⁻¹ • a) k| ≤ h / σ) ↔
        ∀ k : ℕ, k ≤ n → |prefixSum a k| ≤ h) := by
  have hp : ∀ k : ℕ, prefixSum (σ⁻¹ • a) k = prefixSum a k / σ := by
    intro k
    rw [prefixSum_smul, div_eq_mul_inv]
    ring
  refine ⟨hp, ?_, ?_⟩
  · rw [energy_smul, div_eq_mul_inv, inv_pow]
    ring
  · constructor
    · intro hs k hk
      have hsk := hs k hk
      rw [hp k, abs_div, abs_of_pos hσ] at hsk
      exact (div_le_div_iff_of_pos_right hσ).mp hsk
    · intro hs k hk
      rw [hp k, abs_div, abs_of_pos hσ]
      exact (div_le_div_iff_of_pos_right hσ).mpr (hs k hk)

/-- First, second, and third absolute moments after standardization.
No finiteness or probability normalization of the measure is required. -/
theorem standardized_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hY : Integrable Y μ)
    (hYsq : Integrable (fun ω => (Y ω) ^ 2) μ)
    (hYcube : Integrable (fun ω => |Y ω| ^ 3) μ)
    (hmean : (∫ ω, Y ω ∂μ) = 0)
    (hsecond : (∫ ω, (Y ω) ^ 2 ∂μ) = σ ^ 2) :
    let Z : Ω → ℝ := fun ω => Y ω / σ
    Integrable Z μ ∧
      Integrable (fun ω => (Z ω) ^ 2) μ ∧
      Integrable (fun ω => |Z ω| ^ 3) μ ∧
      (∫ ω, Z ω ∂μ) = 0 ∧
      (∫ ω, (Z ω) ^ 2 ∂μ) = 1 ∧
      (∫ ω, |Z ω| ^ 3 ∂μ) = (σ⁻¹) ^ 3 * (∫ ω, |Y ω| ^ 3 ∂μ) := by
  dsimp only
  have hZ : (fun ω => Y ω / σ) = (fun ω => σ⁻¹ * Y ω) := by
    funext ω
    rw [div_eq_mul_inv]
    ring
  have hZsq : (fun ω => (Y ω / σ) ^ 2) =
      (fun ω => (σ⁻¹) ^ 2 * (Y ω) ^ 2) := by
    funext ω
    rw [div_eq_mul_inv, mul_pow]
    ring
  have hZcube : (fun ω => |Y ω / σ| ^ 3) =
      (fun ω => (σ⁻¹) ^ 3 * |Y ω| ^ 3) := by
    funext ω
    rw [abs_div, abs_of_pos hσ, div_eq_mul_inv, mul_pow]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hZ]
    exact hY.const_mul σ⁻¹
  · rw [hZsq]
    exact hYsq.const_mul ((σ⁻¹) ^ 2)
  · rw [hZcube]
    exact hYcube.const_mul ((σ⁻¹) ^ 3)
  · rw [hZ, integral_const_mul, hmean, mul_zero]
  · rw [hZsq, integral_const_mul, hsecond]
    field_simp
  · rw [hZcube, integral_const_mul]

/-- A common third-moment bound remains bounded by the explicit safe constant 8. -/
theorem standardized_third_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) (σ M : ℝ)
    (hσ : (1 / 2 : ℝ) ≤ σ) (hM : 0 ≤ M)
    (_hYcube : Integrable (fun ω => |Y ω| ^ 3) μ)
    (hthird : (∫ ω, |Y ω| ^ 3 ∂μ) ≤ M) :
    (∫ ω, |Y ω / σ| ^ 3 ∂μ) ≤ 8 * M := by
  have hσpos : 0 < σ := by linarith
  have hinvnonneg : 0 ≤ σ⁻¹ := (inv_pos.mpr hσpos).le
  have hinv : σ⁻¹ ≤ (2 : ℝ) := by
    have hprod : σ * σ⁻¹ = 1 := by field_simp
    nlinarith [mul_nonneg (sub_nonneg.mpr hσ) hinvnonneg]
  have hsquare : σ⁻¹ * σ⁻¹ ≤ (2 : ℝ) * 2 :=
    mul_le_mul hinv hinv hinvnonneg (by norm_num)
  have hcube : (σ⁻¹) ^ 3 ≤ (8 : ℝ) := by
    have hh := mul_le_mul hsquare hinv hinvnonneg (by norm_num : (0 : ℝ) ≤ 2 * 2)
    nlinarith only [hh]
  have heq : (fun ω => |Y ω / σ| ^ 3) =
      (fun ω => (σ⁻¹) ^ 3 * |Y ω| ^ 3) := by
    funext ω
    rw [abs_div, abs_of_pos hσpos, div_eq_mul_inv, mul_pow]
    ring
  rw [heq, integral_const_mul]
  calc
    (σ⁻¹) ^ 3 * (∫ ω, |Y ω| ^ 3 ∂μ) ≤ (σ⁻¹) ^ 3 * M :=
      mul_le_mul_of_nonneg_left hthird (pow_nonneg hinvnonneg 3)
    _ ≤ 8 * M := mul_le_mul_of_nonneg_right hcube hM

/-- The standard deviation is positive and has a uniform positive lower bound. -/
theorem sqrt_variance_parameters (v : ℝ)
    (hvlower : (1 / 2 : ℝ) ≤ v) (_hvupper : v ≤ 2) :
    0 < Real.sqrt v ∧ (Real.sqrt v) ^ 2 = v ∧ (1 / 2 : ℝ) ≤ Real.sqrt v := by
  have hvpos : 0 < v := by linarith
  have hsqrtpos := Real.sqrt_pos.mpr hvpos
  have hsquare := Real.sq_sqrt hvpos.le
  refine ⟨hsqrtpos, hsquare, ?_⟩
  nlinarith

/-- The frozen finite variance-v moment interface, instantiated at sqrt(v). -/
theorem sqrt_variance_standardization {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) (v M : ℝ)
    (hvlower : (1 / 2 : ℝ) ≤ v) (hvupper : v ≤ 2) (hM : 0 ≤ M)
    (hY : Integrable Y μ)
    (hYsq : Integrable (fun ω => (Y ω) ^ 2) μ)
    (hYcube : Integrable (fun ω => |Y ω| ^ 3) μ)
    (hmean : (∫ ω, Y ω ∂μ) = 0)
    (hsecond : (∫ ω, (Y ω) ^ 2 ∂μ) = v)
    (hthird : (∫ ω, |Y ω| ^ 3 ∂μ) ≤ M) :
    let σ : ℝ := Real.sqrt v
    let Z : Ω → ℝ := fun ω => Y ω / σ
    0 < σ ∧ σ ^ 2 = v ∧ (1 / 2 : ℝ) ≤ σ ∧
      Integrable Z μ ∧
      Integrable (fun ω => (Z ω) ^ 2) μ ∧
      Integrable (fun ω => |Z ω| ^ 3) μ ∧
      (∫ ω, Z ω ∂μ) = 0 ∧
      (∫ ω, (Z ω) ^ 2 ∂μ) = 1 ∧
      (∫ ω, |Z ω| ^ 3 ∂μ) = (σ⁻¹) ^ 3 * (∫ ω, |Y ω| ^ 3 ∂μ) ∧
      (∫ ω, |Z ω| ^ 3 ∂μ) ≤ 8 * M := by
  dsimp only
  obtain ⟨hσpos, hσsquare, hσlower⟩ := sqrt_variance_parameters v hvlower hvupper
  have hsecond' : (∫ ω, (Y ω) ^ 2 ∂μ) = (Real.sqrt v) ^ 2 :=
    hsecond.trans hσsquare.symm
  obtain ⟨hZ, hZsq, hZcube, hZmean, hZsecond, hZthird⟩ :=
    standardized_moments μ Y (Real.sqrt v) hσpos hY hYsq hYcube hmean hsecond'
  exact ⟨hσpos, hσsquare, hσlower, hZ, hZsq, hZcube, hZmean, hZsecond, hZthird,
    standardized_third_moment_bound μ Y (Real.sqrt v) M hσlower hM hYcube hthird⟩

/-- Exact quadratic and cubic scale ratios, including the zero horizon. -/
theorem normalized_scale_ratios (N : ℕ) (σ h : ℝ) (hσ : 0 < σ) (hh : 0 < h) :
    (N : ℝ) / (h / σ) ^ 2 = σ ^ 2 * (N : ℝ) / h ^ 2 ∧
      (N : ℝ) / (h / σ) ^ 3 = σ ^ 3 * (N : ℝ) / h ^ 3 := by
  constructor <;> field_simp

/-- The variance-v form of the two exact ratios required by the K-to-Kv interface. -/
theorem sqrt_variance_scale_ratios (N : ℕ) (v h : ℝ)
    (hvlower : (1 / 2 : ℝ) ≤ v) (hvupper : v ≤ 2) (hh : 0 < h) :
    (N : ℝ) / (h / Real.sqrt v) ^ 2 = v * (N : ℝ) / h ^ 2 ∧
      (N : ℝ) / (h / Real.sqrt v) ^ 3 = (Real.sqrt v) ^ 3 * (N : ℝ) / h ^ 3 := by
  obtain ⟨hσpos, hσsquare, _⟩ := sqrt_variance_parameters v hvlower hvupper
  simpa only [hσsquare] using normalized_scale_ratios N (Real.sqrt v) h hσpos hh

end Shao.OQ4
