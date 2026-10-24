import Shao.C2.AuxiliarySourceParameters
import Shao.Probability.TruncationIntegrals

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Shao.C2.AuxiliaryOwnC1Budget
open MeasureTheory ProbabilityTheory

theorem auxiliary_normalized_cubic_budget
    (chi : Measure ℝ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) chi)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) chi)
    (hSecond : 1 / 2 ≤ ∫ z : ℝ, z ^ 2 ∂chi)
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (hThird : (∫ z : ℝ, |z| ^ 3 ∂chi) ≤ 12 * beta)
    (n : ℕ) (hn : 0 < n) (y : ℝ) (hy : 0 ≤ y) :
    let sigma : ℝ := Real.sqrt (∫ z : ℝ, z ^ 2 ∂chi)
    let eta : Measure ℝ := Measure.map
      (fun z : ℝ => z / (sigma * Real.sqrt (n : ℝ))) chi
    Shao.truncationBudget eta n y ≤
      48 * beta * (1 + y) ^ 3 / Real.sqrt (n : ℝ) := by
  intro sigma eta
  let t : ℝ := Real.sqrt (n : ℝ)
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have ht : 0 < t := Real.sqrt_pos.2 hN
  have ht2 : t ^ 2 = (n : ℝ) := Real.sq_sqrt hN.le
  have hSecond0 : 0 < ∫ z : ℝ, z ^ 2 ∂chi := by linarith
  have hSigma : 0 < sigma := Real.sqrt_pos.2 hSecond0
  have hSigma2 : sigma ^ 2 = ∫ z : ℝ, z ^ 2 ∂chi := Real.sq_sqrt hSecond0.le
  have hSigmaHalf : 1 / 2 ≤ sigma := by nlinarith
  have hSigmaCube : (1 / 4 : ℝ) ≤ sigma ^ 3 := by
    have hh := mul_le_mul hSecond hSigmaHalf (by norm_num : (0 : ℝ) ≤ 1 / 2)
      hSecond0.le
    nlinarith
  let c : ℝ := (1 + y) / (sigma * t)
  have hc : 0 ≤ c := div_nonneg (by linarith) (mul_pos hSigma ht).le
  have hpoint (z : ℝ) : Shao.truncationF (c * z) ≤ c ^ 3 * |z| ^ 3 := by
    calc
      Shao.truncationF (c * z) = (c * z) ^ 2 * min |c * z| 1 := rfl
      _ ≤ (c * z) ^ 2 * |c * z| :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) (sq_nonneg _)
      _ = |c * z| ^ 3 := by rw [← sq_abs (c * z)]; ring
      _ = c ^ 3 * |z| ^ 3 := by rw [abs_mul, abs_of_nonneg hc, mul_pow]
  have hI := integral_mono (Shao.integrable_truncationF_mul chi h2 c)
    (h3.const_mul (c ^ 3)) hpoint
  rw [integral_const_mul] at hI
  have hMap : Measurable (fun z : ℝ => z / (sigma * Real.sqrt (n : ℝ))) := by
    fun_prop
  have hBudget : Shao.truncationBudget eta n y =
      (n : ℝ) * ∫ z : ℝ, Shao.truncationF (c * z) ∂chi := by
    dsimp only [Shao.truncationBudget, eta]
    have hCont : Continuous (fun z : ℝ => Shao.truncationF ((1 + y) * z)) :=
      Shao.continuous_truncationF.comp (continuous_const.mul continuous_id)
    rw [integral_map hMap.aemeasurable hCont.aestronglyMeasurable]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ (fun z => by congr 1; dsimp [c, t]; ring)
  have hCancel : (n : ℝ) * c ^ 3 * (12 * beta) =
      (12 * beta * (1 + y) ^ 3) / (sigma ^ 3 * t) := by
    change (n : ℝ) * ((1 + y) / (sigma * t)) ^ 3 * (12 * beta) = _
    rw [← ht2]
    field_simp
    <;> ring
  have hLast : (12 * beta * (1 + y) ^ 3) / (sigma ^ 3 * t) ≤
      48 * beta * (1 + y) ^ 3 / t := by
    apply (div_le_iff₀ (mul_pos (pow_pos hSigma 3) ht)).2
    have hh := mul_le_mul_of_nonneg_right hSigmaCube
      (show 0 ≤ 48 * beta * (1 + y) ^ 3 by positivity)
    have heq : (48 * beta * (1 + y) ^ 3 / t) * (sigma ^ 3 * t) =
        (48 * beta * (1 + y) ^ 3) * sigma ^ 3 := by field_simp
    rw [heq]
    nlinarith
  rw [hBudget]
  calc
    (n : ℝ) * (∫ z : ℝ, Shao.truncationF (c * z) ∂chi) ≤
        (n : ℝ) * (c ^ 3 * ∫ z : ℝ, |z| ^ 3 ∂chi) :=
      mul_le_mul_of_nonneg_left hI hN.le
    _ ≤ (n : ℝ) * (c ^ 3 * (12 * beta)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hThird (pow_nonneg hc 3)) hN.le
    _ = (12 * beta * (1 + y) ^ 3) / (sigma ^ 3 * t) := by
      simpa only [mul_assoc] using hCancel
    _ ≤ _ := hLast

theorem auxiliary_centered_law_and_own_budget
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (s : ℝ) (hs : 0 ≤ s)
    (hsmall : s * (∫ z : ℝ, |z| ^ 3 ∂nu) ^ 2 ≤ 1 / 128)
    (n : ℕ) (hn : 0 < n) :
    let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂nu
    let rho : Measure ℝ := nu.tilted (fun z => -s * z ^ 2)
    let mu : ℝ := ∫ z : ℝ, z ∂rho
    let chi : Measure ℝ := Measure.map (fun z : ℝ => z - mu) rho
    let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂chi
    let eta : Measure ℝ := Measure.map
      (fun z : ℝ => z / (Real.sqrt sigmaSq * Real.sqrt (n : ℝ))) chi
    IsProbabilityMeasure chi ∧
      Integrable (id : ℝ → ℝ) chi ∧
      (∫ z : ℝ, z ∂chi) = 0 ∧
      Integrable (fun z : ℝ => z ^ 2) chi ∧
      Integrable (fun z : ℝ => |z| ^ 3) chi ∧
      sigmaSq = variance (id : ℝ → ℝ) rho ∧
      1 / 2 ≤ sigmaSq ∧ sigmaSq ≤ 2 ∧
      (∫ z : ℝ, |z| ^ 3 ∂chi) ≤ 12 * beta ∧
      ∀ y : ℝ, 0 ≤ y → Shao.truncationBudget eta n y ≤
        48 * beta * (1 + y) ^ 3 / Real.sqrt (n : ℝ) := by
  intro beta rho mu chi sigmaSq eta
  rcases Shao.C2.AuxiliaryEnergyCentered.auxiliary_energy_tilt_small_parameter
      nu h2 h3 hmean hnorm s hs hsmall with
    ⟨hRho, _hId, hCentered, hZero, hSquare, hCube, _hDrift, hVarL, hVarU, hThird⟩
  letI : IsProbabilityMeasure rho := hRho
  have hMap : Measurable (fun z : ℝ => z - mu) := by fun_prop
  have hChi : IsProbabilityMeasure chi := by dsimp [chi]; infer_instance
  have hIdChi : Integrable (id : ℝ → ℝ) chi :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hMap.aemeasurable).2 hCentered
  have h2Chi : Integrable (fun z : ℝ => z ^ 2) chi :=
    (integrable_map_measure (by fun_prop) hMap.aemeasurable).2 hSquare
  have h3Chi : Integrable (fun z : ℝ => |z| ^ 3) chi :=
    (integrable_map_measure (by fun_prop) hMap.aemeasurable).2 hCube
  have hMeanChi : (∫ z : ℝ, z ∂chi) = 0 := by
    change (∫ z : ℝ, z ∂Measure.map (fun z : ℝ => z - mu) rho) = 0
    rw [integral_map hMap.aemeasurable (by fun_prop)]
    exact hZero
  have hVar : sigmaSq = variance (id : ℝ → ℝ) rho := by
    change (∫ z : ℝ, z ^ 2 ∂Measure.map (fun z : ℝ => z - mu) rho) = _
    rw [integral_map hMap.aemeasurable (by fun_prop)]
    simpa only [id_eq] using
      (variance_eq_integral (X := (id : ℝ → ℝ)) measurable_id.aemeasurable).symm
  have hThirdChi : (∫ z : ℝ, |z| ^ 3 ∂chi) ≤ 12 * beta := by
    change (∫ z : ℝ, |z| ^ 3 ∂Measure.map (fun z : ℝ => z - mu) rho) ≤ _
    rw [integral_map hMap.aemeasurable (by fun_prop)]
    exact hThird
  have hBeta : 0 ≤ beta := zero_le_one.trans
    (Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one nu h2 h3 hnorm)
  have hLower : 1 / 2 ≤ sigmaSq := by rw [hVar]; exact hVarL
  have hUpper : sigmaSq ≤ 2 := by rw [hVar]; exact hVarU
  refine ⟨hChi, hIdChi, hMeanChi, h2Chi, h3Chi, hVar, hLower, hUpper, hThirdChi, ?_⟩
  intro y hy
  exact auxiliary_normalized_cubic_budget chi h2Chi h3Chi hLower beta hBeta hThirdChi n hn y hy

theorem auxiliary_own_budget_rank_payment
    (beta rhoStar x y : ℝ) (hBeta : 0 ≤ beta) (hRho : 0 < rhoStar)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hyx : y ≤ 2 * x)
    (n : ℕ) (hn : 0 < n)
    (hRank : (768 / rhoStar) ^ 2 * beta ^ 2 * (1 + x) ^ 6 ≤ (n : ℝ)) :
    48 * beta * (1 + y) ^ 3 / Real.sqrt (n : ℝ) ≤ rhoStar / 2 := by
  let d : ℝ := 1 + x
  let t : ℝ := Real.sqrt (n : ℝ)
  let w : ℝ := (768 / rhoStar) * beta * d ^ 3
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have ht : 0 < t := Real.sqrt_pos.2 hN
  have hd : 0 ≤ d := by dsimp [d]; linarith
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hSquare : w ^ 2 ≤ t ^ 2 := by
    rw [show t ^ 2 = (n : ℝ) from Real.sq_sqrt hN.le]
    convert hRank using 1 <;> dsimp [w, d] <;> ring
  have hRoot : w ≤ t := (sq_le_sq₀ hw ht.le).1 hSquare
  have hPaid : 384 * beta * d ^ 3 ≤ (rhoStar / 2) * t := by
    have hh := mul_le_mul_of_nonneg_left hRoot hRho.le
    have heq : rhoStar * w = 768 * beta * d ^ 3 := by
      dsimp [w]
      field_simp
    rw [heq] at hh
    linarith
  have hPower : (1 + y) ^ 3 ≤ 8 * d ^ 3 := by
    have hh := pow_le_pow_left₀ (show 0 ≤ 1 + y by linarith)
      (show 1 + y ≤ 2 * d by dsimp [d]; linarith) 3
    nlinarith
  apply (div_le_iff₀ ht).2
  calc
    48 * beta * (1 + y) ^ 3 ≤ 48 * beta * (8 * d ^ 3) :=
      mul_le_mul_of_nonneg_left hPower (mul_nonneg (by norm_num) hBeta)
    _ = 384 * beta * d ^ 3 := by ring
    _ ≤ _ := hPaid

end Shao.C2.AuxiliaryOwnC1Budget
