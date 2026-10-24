import Shao.C2.AuxiliaryEnergyTilt

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.C2.AuxiliaryEnergyMoments
open MeasureTheory ProbabilityTheory

theorem auxiliary_energy_tilt_moments_and_variance
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (s : ℝ) (hs : 0 ≤ s) :
    let rho : Measure ℝ := nu.tilted (fun z => -s * z ^ 2)
    let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂nu
    let mu : ℝ := ∫ z : ℝ, z ∂rho
    IsProbabilityMeasure rho ∧
      Integrable (fun z : ℝ => z ^ 2) rho ∧
      Integrable (fun z : ℝ => |z| ^ 3) rho ∧
      1 - Real.sqrt s * beta ≤ (∫ z : ℝ, z ^ 2 ∂rho) ∧
      (∫ z : ℝ, z ^ 2 ∂rho) ≤ Real.exp s ∧
      (∫ z : ℝ, |z| ^ 3 ∂rho) ≤ Real.exp s * beta ∧
      variance (id : ℝ → ℝ) rho = (∫ z : ℝ, z ^ 2 ∂rho) - mu ^ 2 ∧
      1 - Real.sqrt s * beta - (s * Real.exp s * beta) ^ 2 ≤
        variance (id : ℝ → ℝ) rho ∧
      variance (id : ℝ → ℝ) rho ≤ Real.exp s := by
  intro rho beta mu
  let V : ℝ → ℝ := fun z => Real.exp (-s * z ^ 2)
  let Z : ℝ := ∫ z : ℝ, V z ∂nu
  rcases Shao.C2.AuxiliaryEnergyTilt.auxiliary_energy_tilt_normalizer_and_drift
      nu h2 h3 hmean hnorm s hs with
    ⟨hV, hZpos, hZlower, hZle, hRho, _hId, hDrift⟩
  letI : IsProbabilityMeasure rho := hRho
  have hVpos (z : ℝ) : 0 < V z := Real.exp_pos _
  have hVle (z : ℝ) : V z ≤ 1 := by
    change Real.exp (-s * z ^ 2) ≤ 1
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (sq_nonneg z))
  have hVm : Measurable V := by dsimp [V]; fun_prop
  have hW2 : Integrable (fun z : ℝ => V z * z ^ 2) nu :=
    h2.mono' (hVm.mul (measurable_id.pow_const 2)).aestronglyMeasurable
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hVpos z),
          abs_of_nonneg (sq_nonneg z)]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (hVle z) (sq_nonneg z))
  have hW3 : Integrable (fun z : ℝ => V z * |z| ^ 3) nu :=
    h3.mono' (by fun_prop)
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hVpos z),
          abs_of_nonneg (pow_nonneg (abs_nonneg z) 3)]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (hVle z) (pow_nonneg (abs_nonneg z) 3))
  have h2Rho : Integrable (fun z : ℝ => z ^ 2) rho :=
    (integrable_tilted_iff hV (fun z : ℝ => z ^ 2)).2
      (by simpa only [smul_eq_mul] using hW2)
  have h3Rho : Integrable (fun z : ℝ => |z| ^ 3) rho :=
    (integrable_tilted_iff hV (fun z : ℝ => |z| ^ 3)).2
      (by simpa only [smul_eq_mul] using hW3)
  have hIntegral (g : ℝ → ℝ) :
      (∫ z : ℝ, g z ∂rho) = (∫ z : ℝ, V z * g z ∂nu) / Z := by
    change (∫ z : ℝ, g z ∂(nu.tilted (fun z => -s * z ^ 2))) = _
    rw [integral_tilted]
    change (∫ z : ℝ, (V z / Z) * g z ∂nu) = _
    calc
      (∫ z : ℝ, (V z / Z) * g z ∂nu) = ∫ z : ℝ, (V z * g z) / Z ∂nu :=
        integral_congr_ae (ae_of_all _ fun z => by ring)
      _ = _ := by rw [integral_div]
  have hPoint (z : ℝ) : 1 - V z ≤ Real.sqrt s * |z| := by
    let t := Real.sqrt s * |z|
    have ht0 : 0 ≤ t := mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
    have ht2 : t ^ 2 = s * z ^ 2 := by
      dsimp [t]
      rw [mul_pow, Real.sq_sqrt hs, sq_abs]
    have hOne : 1 - s * z ^ 2 ≤ V z := by
      simpa only [V, neg_mul] using Real.one_sub_le_exp_neg (s * z ^ 2)
    change 1 - V z ≤ t
    by_cases ht : t ≤ 1
    · have hh := mul_le_mul_of_nonneg_left ht ht0
      nlinarith
    · have ht1 : 1 ≤ t := (lt_of_not_ge ht).le
      linarith [hVpos z]
  have hLossInt : Integrable (fun z : ℝ => z ^ 2 * (1 - V z)) nu :=
    (h2.sub hW2).congr (ae_of_all _ fun z => by dsimp; ring)
  have hLoss : (∫ z : ℝ, z ^ 2 * (1 - V z) ∂nu) ≤ Real.sqrt s * beta := by
    calc
      (∫ z : ℝ, z ^ 2 * (1 - V z) ∂nu) ≤
          ∫ z : ℝ, Real.sqrt s * |z| ^ 3 ∂nu :=
        integral_mono hLossInt (h3.const_mul _) (fun z => by
          calc
            z ^ 2 * (1 - V z) ≤ z ^ 2 * (Real.sqrt s * |z|) :=
              mul_le_mul_of_nonneg_left (hPoint z) (sq_nonneg z)
            _ = Real.sqrt s * |z| ^ 3 := by rw [← sq_abs z]; ring)
      _ = Real.sqrt s * beta := integral_const_mul _ _
  have hN2lower : 1 - Real.sqrt s * beta ≤ ∫ z : ℝ, V z * z ^ 2 ∂nu := by
    have hh : (∫ z : ℝ, z ^ 2 * (1 - V z) ∂nu) =
        1 - ∫ z : ℝ, V z * z ^ 2 ∂nu := by
      calc
        (∫ z : ℝ, z ^ 2 * (1 - V z) ∂nu) =
            ∫ z : ℝ, z ^ 2 - V z * z ^ 2 ∂nu :=
          integral_congr_ae (ae_of_all _ fun z => by ring)
        _ = _ := by rw [integral_sub h2 hW2, hnorm]
    linarith
  have hN2nonneg : 0 ≤ ∫ z : ℝ, V z * z ^ 2 ∂nu :=
    integral_nonneg (fun z => mul_nonneg (hVpos z).le (sq_nonneg z))
  have h2lower : 1 - Real.sqrt s * beta ≤ ∫ z : ℝ, z ^ 2 ∂rho := by
    rw [hIntegral]
    apply hN2lower.trans
    apply (le_div_iff₀ hZpos).2
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hZle hN2nonneg
  have hN2upper : (∫ z : ℝ, V z * z ^ 2 ∂nu) ≤ 1 := by
    rw [← hnorm]
    exact integral_mono hW2 h2 (fun z => by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hVle z) (sq_nonneg z))
  have h2upper : (∫ z : ℝ, z ^ 2 ∂rho) ≤ Real.exp s := by
    rw [hIntegral]
    calc
      (∫ z : ℝ, V z * z ^ 2 ∂nu) / Z ≤ 1 / Z :=
        div_le_div_of_nonneg_right hN2upper hZpos.le
      _ ≤ 1 / Real.exp (-s) :=
        div_le_div_of_nonneg_left zero_le_one (Real.exp_pos _) hZlower
      _ = _ := by rw [one_div, ← Real.exp_neg, neg_neg]
  have hBeta : 0 ≤ beta := integral_nonneg (fun z => pow_nonneg (abs_nonneg z) 3)
  have hN3upper : (∫ z : ℝ, V z * |z| ^ 3 ∂nu) ≤ beta :=
    integral_mono hW3 h3 (fun z => by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (hVle z) (pow_nonneg (abs_nonneg z) 3))
  have h3upper : (∫ z : ℝ, |z| ^ 3 ∂rho) ≤ Real.exp s * beta := by
    rw [hIntegral]
    calc
      (∫ z : ℝ, V z * |z| ^ 3 ∂nu) / Z ≤ beta / Z :=
        div_le_div_of_nonneg_right hN3upper hZpos.le
      _ ≤ beta / Real.exp (-s) :=
        div_le_div_of_nonneg_left hBeta (Real.exp_pos _) hZlower
      _ = _ := by rw [div_eq_mul_inv, ← Real.exp_neg, neg_neg]; ring
  have hL2 : MemLp (id : ℝ → ℝ) 2 rho :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 h2Rho
  have hVar : variance (id : ℝ → ℝ) rho =
      (∫ z : ℝ, z ^ 2 ∂rho) - mu ^ 2 := by
    simpa only [Pi.pow_apply, id_eq] using variance_eq_sub hL2
  have hD0 : 0 ≤ s * Real.exp s * beta :=
    mul_nonneg (mul_nonneg hs (Real.exp_pos _).le) hBeta
  have hMuSq : mu ^ 2 ≤ (s * Real.exp s * beta) ^ 2 := by
    have hh := mul_nonneg (sub_nonneg.mpr hDrift)
      (add_nonneg (abs_nonneg mu) hD0)
    nlinarith [sq_abs mu]
  refine ⟨hRho, h2Rho, h3Rho, h2lower, h2upper, h3upper, hVar, ?_, ?_⟩
  · rw [hVar]
    linarith
  · rw [hVar]
    linarith [sq_nonneg mu]

end Shao.C2.AuxiliaryEnergyMoments
