import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.C2.AuxiliaryEnergyTilt
open MeasureTheory ProbabilityTheory

theorem auxiliary_energy_tilt_normalizer_and_drift
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (s : ℝ) (hs : 0 ≤ s) :
    let V : ℝ → ℝ := fun z => Real.exp (-s * z ^ 2)
    let Z : ℝ := ∫ z : ℝ, V z ∂nu
    let rho : Measure ℝ := nu.tilted (fun z => -s * z ^ 2)
    let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂nu
    Integrable V nu ∧ 0 < Z ∧ Real.exp (-s) ≤ Z ∧ Z ≤ 1 ∧
      IsProbabilityMeasure rho ∧ Integrable (id : ℝ → ℝ) rho ∧
      |(∫ z : ℝ, z ∂rho)| ≤ s * Real.exp s * beta := by
  intro V Z rho beta
  have hVpos (z : ℝ) : 0 < V z := Real.exp_pos _
  have hVle (z : ℝ) : V z ≤ 1 := by
    change Real.exp (-s * z ^ 2) ≤ 1
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (sq_nonneg z))
  have hVm : Measurable V := by dsimp [V]; fun_prop
  have hV : Integrable V nu :=
    (integrable_const (1 : ℝ)).mono' hVm.aestronglyMeasurable
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_pos (hVpos z)]
        exact hVle z)
  have hZpos : 0 < Z := integral_exp_pos hV
  have hZle : Z ≤ 1 := by
    calc
      Z ≤ ∫ _z : ℝ, (1 : ℝ) ∂nu :=
        integral_mono hV (integrable_const _) hVle
      _ = 1 := by simp
  have hTangent (z : ℝ) : Real.exp (-s) * (1 + s - s * z ^ 2) ≤ V z := by
    calc
      Real.exp (-s) * (1 + s - s * z ^ 2) =
          Real.exp (-s) * ((s - s * z ^ 2) + 1) := by ring
      _ ≤ Real.exp (-s) * Real.exp (s - s * z ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (Real.exp_pos _).le
      _ = V z := by
        rw [← Real.exp_add]
        change Real.exp (-s + (s - s * z ^ 2)) = Real.exp (-s * z ^ 2)
        congr 1
        ring
  have hTangentInt : Integrable (fun z : ℝ =>
      Real.exp (-s) * (1 + s - s * z ^ 2)) nu :=
    ((integrable_const (1 + s)).sub (h2.const_mul s)).const_mul _
  have hTangentIntegral : (∫ z : ℝ, Real.exp (-s) * (1 + s - s * z ^ 2) ∂nu) =
      Real.exp (-s) := by
    rw [integral_const_mul, integral_sub (integrable_const _) (h2.const_mul s),
      integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, hnorm]
    ring
  have hZlower : Real.exp (-s) ≤ Z := by
    have hh := integral_mono hTangentInt hV hTangent
    rwa [hTangentIntegral] at hh
  have hRho : IsProbabilityMeasure rho := isProbabilityMeasure_tilted hV
  have hId : Integrable (id : ℝ → ℝ) nu :=
    ((memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 h2).integrable
      (by norm_num)
  have hProd : Integrable (fun z : ℝ => V z * z) nu :=
    hId.norm.mono' (hVm.mul measurable_id).aestronglyMeasurable
      (ae_of_all _ fun z => by
        simpa only [Real.norm_eq_abs, id_eq, abs_mul, abs_of_pos (hVpos z), one_mul] using
          mul_le_mul_of_nonneg_right (hVle z) (abs_nonneg z))
  have hIdRho : Integrable (id : ℝ → ℝ) rho :=
    (integrable_tilted_iff hV (id : ℝ → ℝ)).2
      (by simpa only [smul_eq_mul, id_eq] using hProd)
  have hMeanRho : (∫ z : ℝ, z ∂rho) = (∫ z : ℝ, V z * z ∂nu) / Z := by
    change (∫ z : ℝ, z ∂(nu.tilted (fun z => -s * z ^ 2))) = _
    rw [integral_tilted]
    change (∫ z : ℝ, (V z / Z) * z ∂nu) = _
    calc
      (∫ z : ℝ, (V z / Z) * z ∂nu) = ∫ z : ℝ, (V z * z) / Z ∂nu :=
        integral_congr_ae (ae_of_all _ fun z => by ring)
      _ = _ := by rw [integral_div]
  have hCentInt : Integrable (fun z : ℝ => z * (V z - 1)) nu :=
    (hProd.sub hId).congr (ae_of_all _ fun z => by dsimp; ring)
  have hCentered : (∫ z : ℝ, V z * z ∂nu) = ∫ z : ℝ, z * (V z - 1) ∂nu := by
    calc
      (∫ z : ℝ, V z * z ∂nu) = (∫ z : ℝ, V z * z ∂nu) - ∫ z : ℝ, z ∂nu := by
        rw [hmean, sub_zero]
      _ = ∫ z : ℝ, V z * z - z ∂nu := (integral_sub hProd hId).symm
      _ = _ := integral_congr_ae (ae_of_all _ fun z => by ring)
  have hPoint (z : ℝ) : |z * (V z - 1)| ≤ s * |z| ^ 3 := by
    have hOne : 1 - s * z ^ 2 ≤ V z := by
      simpa only [V, neg_mul] using Real.one_sub_le_exp_neg (s * z ^ 2)
    have hd0 : 0 ≤ 1 - V z := sub_nonneg.mpr (hVle z)
    have hd1 : 1 - V z ≤ s * z ^ 2 := by linarith
    rw [abs_mul, abs_sub_comm (V z) 1, abs_of_nonneg hd0]
    calc
      |z| * (1 - V z) ≤ |z| * (s * z ^ 2) :=
        mul_le_mul_of_nonneg_left hd1 (abs_nonneg z)
      _ = s * |z| ^ 3 := by rw [← sq_abs z]; ring
  have hNum : |(∫ z : ℝ, z * (V z - 1) ∂nu)| ≤ s * beta := by
    calc
      |(∫ z : ℝ, z * (V z - 1) ∂nu)| ≤ ∫ z : ℝ, |z * (V z - 1)| ∂nu :=
        abs_integral_le_integral_abs
      _ ≤ ∫ z : ℝ, s * |z| ^ 3 ∂nu := integral_mono hCentInt.abs (h3.const_mul s) hPoint
      _ = s * beta := integral_const_mul _ _
  have hBeta : 0 ≤ beta := integral_nonneg (fun z => pow_nonneg (abs_nonneg z) 3)
  have hDrift : |(∫ z : ℝ, z ∂rho)| ≤ s * Real.exp s * beta := by
    rw [hMeanRho, hCentered, abs_div, abs_of_pos hZpos]
    calc
      |(∫ z : ℝ, z * (V z - 1) ∂nu)| / Z ≤ (s * beta) / Z :=
        div_le_div_of_nonneg_right hNum hZpos.le
      _ ≤ (s * beta) / Real.exp (-s) :=
        div_le_div_of_nonneg_left (mul_nonneg hs hBeta) (Real.exp_pos _) hZlower
      _ = (s * beta) * Real.exp s := by rw [div_eq_mul_inv, ← Real.exp_neg, neg_neg]
      _ = s * Real.exp s * beta := by ring
  exact ⟨hV, hZpos, hZlower, hZle, hRho, hIdRho, hDrift⟩

end Shao.C2.AuxiliaryEnergyTilt
