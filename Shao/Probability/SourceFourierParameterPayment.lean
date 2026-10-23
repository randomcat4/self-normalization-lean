import Shao.Probability.SourceFourierScale

/-!
The original comparison-threshold window pays the Fourier support scale and
the three outside-integral smallness conditions for the same conditional law.
This is parameter payment only; it does not identify a probability or close
the source normal-approximation theorem.
-/

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

theorem sourceTruncation_threshold_fourier_parameter_payment
    (kappa delta : ℝ) (hkappa : 0 < kappa) (hdelta : 0 < delta) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 4 : ℝ) ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun z : ℝ => z ^ 2) ν0 →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν0) = 1 →
          (∫ z : ℝ, z ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ epsilon0 / 2 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            ∀ y : ℝ, 0 < y → |y - x| ≤ 1 / (2 * (1 + x)) →
              let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
              let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
              let h : ℝ := epsilon0 / (1 + y)
              0 < h ∧ h ≤ (1 / 4 : ℝ) ∧ epsilon / (1 + x) ≤ h ∧
                (∀ᵐ z : ℝ ∂ρ, |z| ≤ h) ∧
                0 < gamma ∧ gamma ≤ 2 * h ∧
                h * y ≤ delta ∧ (gamma / kappa) * y ≤ delta ∧ (4 * h) * y ≤ delta ∧
                ∀ u v : ℝ, u ≠ 0 → |v| ≤ |u| / (4 * h) →
                  |v| ≤ |u| / (4 * (epsilon / (1 + x))) := by
  let epsilon0 : ℝ := min (1 / 4) (min (kappa * delta / 2) (delta / 4))
  have he0 : 0 < epsilon0 := by
    dsimp [epsilon0]
    exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have he0quarter : epsilon0 ≤ (1 / 4 : ℝ) := min_le_left _ _
  have he0k : epsilon0 ≤ kappa * delta / 2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have he0d : epsilon0 ≤ delta / 4 :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨epsilon0, he0, he0quarter, ?_⟩
  intro ν0 hprob n h2 hnorm hmean x epsilon hx hepsilon hepsilon0 hR y hy hwindow
  letI : IsProbabilityMeasure ν0 := hprob
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
  let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
  let h : ℝ := epsilon0 / (1 + y)
  have hxp : 0 < 1 + x := by linarith only [hx]
  have hyp : 0 < 1 + y := by linarith only [hy]
  have hepsilonHalf : epsilon ≤ (1 / 2 : ℝ) := by
    linarith only [hepsilon0, he0quarter]
  have hwindowOne : 1 / (2 * (1 + x)) ≤ (1 : ℝ) := by
    apply (div_le_iff₀ (show 0 < 2 * (1 + x) by positivity)).2
    nlinarith only [hx]
  have hcompare : 1 + y ≤ 2 * (1 + x) := by
    have hu := (abs_le.mp hwindow).2
    linarith only [hu, hwindowOne, hx]
  have hscale : epsilon / (1 + x) ≤ h := by
    apply (div_le_div_iff₀ hxp hyp).2
    calc
      epsilon * (1 + y) ≤ (epsilon0 / 2) * (1 + y) :=
        mul_le_mul_of_nonneg_right hepsilon0 hyp.le
      _ ≤ (epsilon0 / 2) * (2 * (1 + x)) :=
        mul_le_mul_of_nonneg_left hcompare (by positivity)
      _ = epsilon0 * (1 + x) := by ring
  have hh : 0 < h := div_pos he0 hyp
  have hhle0 : h ≤ epsilon0 := by
    apply (div_le_iff₀ hyp).2
    nlinarith only [mul_nonneg he0.le hy.le]
  have hhquarter : h ≤ (1 / 4 : ℝ) := hhle0.trans he0quarter
  obtain ⟨_, _, _, hs, _, _, _, _⟩ :=
    Shao.sourceTruncation_law_data ν0 n h2 hnorm x epsilon hx
      hepsilon hepsilonHalf hR
  have hsupport : ∀ᵐ z : ℝ ∂ρ, |z| ≤ h := by
    filter_upwards [hs] with z hz
    exact hz.trans hscale
  obtain ⟨_, hgamma, _, _, hgammaCutoff, _, _, _, _⟩ :=
    Shao.sourceTruncation_gamma_bounds ν0 n h2 hnorm hmean x epsilon hx
      hepsilon hepsilonHalf hR
  change 0 < gamma at hgamma
  change gamma ≤ 2 * (epsilon / (1 + x)) at hgammaCutoff
  have hgammaH : gamma ≤ 2 * h := by
    linarith only [hgammaCutoff, hscale]
  have hhidentity : h * (1 + y) = epsilon0 := div_mul_cancel₀ epsilon0 hyp.ne'
  have hhy : h * y ≤ epsilon0 := by
    nlinarith only [hhidentity, hh.le]
  have hhyDelta : h * y ≤ delta := by linarith only [hhy, he0d, hdelta]
  have hgammaDelta : (gamma / kappa) * y ≤ delta := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hkappa).2
    have hgy := mul_le_mul_of_nonneg_right hgammaH hy.le
    nlinarith only [hgy, hhy, he0k]
  have hfourDelta : (4 * h) * y ≤ delta := by
    nlinarith only [hhy, he0d]
  change 0 < h ∧ h ≤ (1 / 4 : ℝ) ∧ epsilon / (1 + x) ≤ h ∧
    (∀ᵐ z : ℝ ∂ρ, |z| ≤ h) ∧ 0 < gamma ∧ gamma ≤ 2 * h ∧
    h * y ≤ delta ∧ (gamma / kappa) * y ≤ delta ∧ (4 * h) * y ≤ delta ∧ _
  refine ⟨hh, hhquarter, hscale, hsupport, hgamma, hgammaH,
    hhyDelta, hgammaDelta, hfourDelta, ?_⟩
  intro u v _ hv
  apply hv.trans
  apply (div_le_div_iff₀ (show 0 < 4 * h by positivity)
    (show 0 < 4 * (epsilon / (1 + x)) by positivity)).2
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hscale (by norm_num)) (abs_nonneg u)

end Shao.Probability
