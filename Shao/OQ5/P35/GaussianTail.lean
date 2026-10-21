import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF

/-!
# The actual standard Gaussian comparison tail for p35

Source: original p35 section7, lines215-223. Phi is the actual standard
Gaussian CDF, and Psi=1-Phi is its strict upper tail probability.
-/

set_option autoImplicit false

namespace Shao.OQ5.P35

noncomputable section

open MeasureTheory ProbabilityTheory

/-- The CDF of the actual mean-zero, variance-one Gaussian measure. -/
def standardNormalCDF (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- The source comparison tail Psi=1-Phi. -/
def standardNormalUpperTail (x : ℝ) : ℝ := 1 - standardNormalCDF x

theorem standardNormalCDF_eq (x : ℝ) :
    standardNormalCDF x = (gaussianReal 0 1).real (Set.Iic x) :=
  cdf_eq_real (gaussianReal 0 1) x

theorem standardNormalUpperTail_eq (x : ℝ) :
    standardNormalUpperTail x = (gaussianReal 0 1).real (Set.Ioi x) := by
  have h := measureReal_add_measureReal_compl (μ := gaussianReal 0 1)
    (measurableSet_Iic : MeasurableSet (Set.Iic x))
  simp only [Set.compl_Iic, probReal_univ] at h
  rw [standardNormalUpperTail, standardNormalCDF_eq]
  linarith

theorem standardNormalUpperTail_pos (x : ℝ) : 0 < standardNormalUpperTail x := by
  rw [standardNormalUpperTail_eq, measureReal_def]
  have hz : gaussianReal 0 1 (Set.Ioi x) ≠ 0 := by
    intro hzero
    have hv := gaussianReal_absolutelyContinuous' (0 : ℝ) (v := 1) (by norm_num) hzero
    simp only [Real.volume_Ioi] at hv
    exact ENNReal.top_ne_zero hv
  exact ENNReal.toReal_pos_iff.mpr
    ⟨pos_iff_ne_zero.mpr hz, lt_top_iff_ne_top.mpr (measure_ne_top _ _)⟩

theorem standardNormalUpperTail_le_exp (x : ℝ) (hx : 0 ≤ x) :
    standardNormalUpperTail x ≤ Real.exp (-(x ^ 2) / 2) := by
  have h := measure_ge_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := id) (t := x) x hx
    (integrable_exp_mul_gaussianReal x)
  calc
    standardNormalUpperTail x = (gaussianReal 0 1).real (Set.Ioi x) :=
      standardNormalUpperTail_eq x
    _ ≤ (gaussianReal 0 1).real {y : ℝ | x ≤ id y} :=
      measureReal_mono (fun y hy => (show x ≤ id y from le_of_lt hy))
    _ ≤ Real.exp (-x * x) * mgf id (gaussianReal 0 1) x := h
    _ = Real.exp (-(x ^ 2) / 2) := by
      rw [mgf_id_gaussianReal]
      norm_num only [zero_mul, NNReal.coe_one, one_mul, zero_add]
      rw [← Real.exp_add]
      congr 1
      ring

end

end Shao.OQ5.P35
