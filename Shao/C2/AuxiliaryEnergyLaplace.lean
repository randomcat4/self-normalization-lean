import Shao.C2.AuxiliaryEnergyCentered

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.C2.AuxiliaryEnergyLaplace
open MeasureTheory ProbabilityTheory

theorem auxiliary_energy_laplace_loss
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (a : ℝ) (ha : 0 ≤ a) :
    let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂nu
    a - a * Real.sqrt a * beta ≤
      1 - ∫ z : ℝ, Real.exp (-a * z ^ 2) ∂nu := by
  intro beta
  let V : ℝ → ℝ := fun z => Real.exp (-a * z ^ 2)
  have hVI : Integrable V nu :=
    (Shao.C2.AuxiliaryEnergyTilt.auxiliary_energy_tilt_normalizer_and_drift
      nu h2 h3 hmean hnorm a ha).1
  have hPoint (z : ℝ) : a * z ^ 2 - (a * Real.sqrt a) * |z| ^ 3 ≤ 1 - V z := by
    let t := Real.sqrt a * |z|
    have ht0 : 0 ≤ t := mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
    have ht2 : t ^ 2 = a * z ^ 2 := by
      dsimp [t]
      rw [mul_pow, Real.sq_sqrt ha, sq_abs]
    have hSqrt3 : (Real.sqrt a) ^ 3 = a * Real.sqrt a := by
      calc
        (Real.sqrt a) ^ 3 = (Real.sqrt a) ^ 2 * Real.sqrt a := by ring
        _ = _ := by rw [Real.sq_sqrt ha]
    have ht3 : t ^ 3 = (a * Real.sqrt a) * |z| ^ 3 := by
      dsimp [t]
      rw [mul_pow, hSqrt3]
    have hLoss : t ^ 2 - t ^ 3 ≤ 1 - Real.exp (-(t ^ 2)) := by
      by_cases ht : t ≤ 1
      · have ht2le : t ^ 2 ≤ 1 := by
          have hh := mul_nonneg ht0 (sub_nonneg.mpr ht)
          nlinarith
        have hRemainder := Real.abs_exp_sub_one_sub_id_le
          (x := -(t ^ 2)) (by
            rw [abs_neg, abs_of_nonneg (sq_nonneg t)]
            exact ht2le)
        have hUpper := (le_abs_self (Real.exp (-(t ^ 2)) - 1 - (-(t ^ 2)))).trans
          hRemainder
        have h4 := mul_le_mul_of_nonneg_left ht (pow_nonneg ht0 3)
        nlinarith
      · have ht1 : 1 ≤ t := (lt_of_not_ge ht).le
        have hh := mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht1)
        have hExp : Real.exp (-(t ^ 2)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg t))
        nlinarith
    calc
      a * z ^ 2 - (a * Real.sqrt a) * |z| ^ 3 = t ^ 2 - t ^ 3 := by
        rw [ht2, ht3]
      _ ≤ 1 - Real.exp (-(t ^ 2)) := hLoss
      _ = 1 - V z := by simp only [ht2, V, neg_mul]
  have hLower : Integrable (fun z : ℝ =>
      a * z ^ 2 - (a * Real.sqrt a) * |z| ^ 3) nu :=
    (h2.const_mul a).sub (h3.const_mul (a * Real.sqrt a))
  have hUpper : Integrable (fun z : ℝ => 1 - V z) nu :=
    (integrable_const (1 : ℝ)).sub hVI
  calc
    a - a * Real.sqrt a * beta =
        ∫ z : ℝ, a * z ^ 2 - (a * Real.sqrt a) * |z| ^ 3 ∂nu := by
      rw [integral_sub (h2.const_mul a) (h3.const_mul (a * Real.sqrt a)),
        integral_const_mul, integral_const_mul, hnorm]
      ring
    _ ≤ ∫ z : ℝ, 1 - V z ∂nu := integral_mono hLower hUpper hPoint
    _ = _ := by
      rw [integral_sub (integrable_const (1 : ℝ)) hVI]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      rfl

theorem auxiliary_energy_laplace_decay
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (a : ℝ) (ha : 0 ≤ a)
    (hsmall : a * (∫ z : ℝ, |z| ^ 3 ∂nu) ^ 2 ≤ 1 / 64) :
    (∫ z : ℝ, Real.exp (-a * z ^ 2) ∂nu) ≤ Real.exp (-(7 / 8) * a) := by
  let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂nu
  have hBeta0 : 0 ≤ beta := integral_nonneg (fun z => pow_nonneg (abs_nonneg z) 3)
  change a * beta ^ 2 ≤ 1 / 64 at hsmall
  have hSqrt : Real.sqrt a * beta ≤ 1 / 8 := by
    have ht0 := mul_nonneg (Real.sqrt_nonneg a) hBeta0
    have hh : (Real.sqrt a * beta) ^ 2 ≤ 1 / 64 := by
      rwa [mul_pow, Real.sq_sqrt ha]
    nlinarith
  have hLoss := auxiliary_energy_laplace_loss nu h2 h3 hmean hnorm a ha
  have hProduct := mul_le_mul_of_nonneg_left hSqrt ha
  have hPhi : (∫ z : ℝ, Real.exp (-a * z ^ 2) ∂nu) ≤ 1 - (7 / 8) * a := by
    change a - a * Real.sqrt a * beta ≤ _ at hLoss
    nlinarith
  exact hPhi.trans (by simpa only [neg_mul, sub_eq_add_neg, add_comm] using
    Real.add_one_le_exp (-(7 / 8) * a))

theorem auxiliary_tilted_energy_laplace
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (s q : ℝ) (hs : 0 ≤ s) (hq : 0 ≤ q) (hsq : s ≤ q)
    (hsmall : (s + q) * (∫ z : ℝ, |z| ^ 3 ∂nu) ^ 2 ≤ 1 / 64) :
    let rho : Measure ℝ := nu.tilted (fun z => -s * z ^ 2)
    Integrable (fun z : ℝ => Real.exp (-q * z ^ 2)) rho ∧
      (∫ z : ℝ, Real.exp (-q * z ^ 2) ∂rho) ≤ Real.exp (-(3 / 4) * q) := by
  intro rho
  let Z : ℝ := ∫ z : ℝ, Real.exp (-s * z ^ 2) ∂nu
  rcases Shao.C2.AuxiliaryEnergyTilt.auxiliary_energy_tilt_normalizer_and_drift
      nu h2 h3 hmean hnorm s hs with
    ⟨hV, hZpos, hZlower, _hZle, _hRho, _hId, _hDrift⟩
  have hVsum : Integrable (fun z : ℝ => Real.exp (-(s + q) * z ^ 2)) nu :=
    (Shao.C2.AuxiliaryEnergyTilt.auxiliary_energy_tilt_normalizer_and_drift
      nu h2 h3 hmean hnorm (s + q) (add_nonneg hs hq)).1
  have hProd : Integrable (fun z : ℝ =>
      Real.exp (-s * z ^ 2) * Real.exp (-q * z ^ 2)) nu := by
    convert hVsum using 1
    funext z
    rw [← Real.exp_add]
    congr 1
    ring
  have hInt : Integrable (fun z : ℝ => Real.exp (-q * z ^ 2)) rho :=
    (integrable_tilted_iff hV (fun z : ℝ => Real.exp (-q * z ^ 2))).2
      (by simpa only [smul_eq_mul] using hProd)
  have hFormula : (∫ z : ℝ, Real.exp (-q * z ^ 2) ∂rho) =
      (∫ z : ℝ, Real.exp (-(s + q) * z ^ 2) ∂nu) / Z := by
    change (∫ z : ℝ, Real.exp (-q * z ^ 2) ∂(nu.tilted (fun z => -s * z ^ 2))) = _
    rw [integral_tilted]
    change (∫ z : ℝ, (Real.exp (-s * z ^ 2) / Z) * Real.exp (-q * z ^ 2) ∂nu) = _
    calc
      (∫ z : ℝ, (Real.exp (-s * z ^ 2) / Z) * Real.exp (-q * z ^ 2) ∂nu) =
          ∫ z : ℝ, Real.exp (-(s + q) * z ^ 2) / Z ∂nu :=
        integral_congr_ae (ae_of_all _ fun z => by
          calc
            (Real.exp (-s * z ^ 2) / Z) * Real.exp (-q * z ^ 2) =
                (Real.exp (-s * z ^ 2) * Real.exp (-q * z ^ 2)) / Z := by ring
            _ = _ := by rw [← Real.exp_add]; congr 2; ring)
      _ = _ := by rw [integral_div]
  have hNum := auxiliary_energy_laplace_decay nu h2 h3 hmean hnorm
    (s + q) (add_nonneg hs hq) hsmall
  refine ⟨hInt, ?_⟩
  rw [hFormula]
  calc
    (∫ z : ℝ, Real.exp (-(s + q) * z ^ 2) ∂nu) / Z ≤
        Real.exp (-(7 / 8) * (s + q)) / Z :=
      div_le_div_of_nonneg_right hNum hZpos.le
    _ ≤ Real.exp (-(7 / 8) * (s + q)) / Real.exp (-s) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hZlower
    _ = Real.exp (s - (7 / 8) * (s + q)) := by
      rw [div_eq_mul_inv, ← Real.exp_neg, neg_neg, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(3 / 4) * q) := Real.exp_le_exp.mpr (by linarith)

end Shao.C2.AuxiliaryEnergyLaplace
