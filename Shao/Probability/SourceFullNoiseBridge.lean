import Shao.Probability.QuadraticFullNoise
import Shao.Probability.SourceFourierScale

set_option autoImplicit false

namespace Shao

open MeasureTheory ProbabilityTheory

theorem sourceTruncation_fullNoise
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (hmean : (∫ z : ℝ, z ∂ν) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hR : truncationBudget ν n x ≤ epsilon ^ 3 / 8) :
    let h := epsilon / (1 + x)
    let rho := ProbabilityTheory.cond ν {z | |z| ≤ h}
    let gamma := (∫ z : ℝ, |z| ^ 3 ∂rho) / variance (id : ℝ → ℝ) rho
    let law := Probability.quadraticFullNoiseLaw rho
    IsProbabilityMeasure law ∧
    IndepFun (fun p : (Fin n → ℝ) × (ℝ × ℝ) => p.1) (fun p => p.2)
      ((Measure.pi (fun _ : Fin n => rho)).prod law) ∧
    (∀ᵐ z : ℝ × ℝ ∂law, |z.1| + (1 + x) * |z.2| ≤ 100 * h) ∧
    (∫ z : ℝ × ℝ, |z.1| ∂law) +
      (1 + x) * (∫ z : ℝ × ℝ, |z.2| ∂law) ≤ 100 * gamma ∧
    gamma ≤ 4 * truncationBudget ν n 0 := by
  let h := epsilon / (1 + x)
  let rho := ProbabilityTheory.cond ν {z | |z| ≤ h}
  let gamma := (∫ z : ℝ, |z| ^ 3 ∂rho) / variance (id : ℝ → ℝ) rho
  let law := Probability.quadraticFullNoiseLaw rho
  have ha : 0 < 1 + x := by linarith
  have hh : 0 < h := div_pos hepsilon ha
  have hscale : (1 + x) * h = epsilon := by
    dsimp [h]
    exact mul_div_cancel₀ epsilon ha.ne'
  obtain ⟨_, _, hp, hs, _, _, h3rho, _⟩ :=
    sourceTruncation_law_data ν n h2 hnorm x epsilon hx hepsilon hepsilonHalf hR
  change IsProbabilityMeasure rho at hp
  let := hp
  change (∀ᵐ z : ℝ ∂rho, |z| ≤ h) at hs
  change Integrable (fun z : ℝ => |z| ^ 3) rho at h3rho
  obtain ⟨_, _, _, _, _, hV, _, _⟩ :=
    sourceTruncation_variance_bounds ν n h2 hnorm hmean x epsilon hx
      hepsilon hepsilonHalf hR
  change 0 < variance (id : ℝ → ℝ) rho at hV
  obtain ⟨_, hg, _, _, hgh, _, _, _, hgr⟩ :=
    sourceTruncation_gamma_bounds ν n h2 hnorm hmean x epsilon hx
      hepsilon hepsilonHalf hR
  change 0 < gamma at hg
  change gamma ≤ 2 * h at hgh
  change gamma ≤ 4 * truncationBudget ν n 0 at hgr
  have hl := (Probability.quadraticFullNoise_law_data rho h3rho hV h hh hs).2.2.1
  change IsProbabilityMeasure law at hl
  let := hl
  obtain ⟨hsupport, _, _, _, hz, hy, _, _⟩ :=
    Probability.quadraticFullNoise_support_moments rho h3rho hV h hh hs hgh
  change (∀ᵐ z : ℝ × ℝ ∂law, |z.1| ≤ 34 * h ∧ |z.2| ≤ 64 * h ^ 2) at hsupport
  change (∫ z : ℝ × ℝ, |z.1| ∂law) ≤ (67 / 3 : ℝ) * gamma at hz
  change (∫ z : ℝ × ℝ, |z.2| ∂law) ≤ (128 / 3 : ℝ) * h * gamma at hy
  have hind := (Probability.quadraticFullNoise_independent_sample rho h3rho hV h hh hs
    (Measure.pi (fun _ : Fin n => rho))).1
  refine ⟨hl, hind, ?_, ?_, hgr⟩
  · filter_upwards [hsupport] with z hz
    calc
      _ ≤ 34 * h + (1 + x) * (64 * h ^ 2) :=
        add_le_add hz.1 (mul_le_mul_of_nonneg_left hz.2 ha.le)
      _ = (34 + 64 * epsilon) * h := by
        calc
          _ = 34 * h + 64 * ((1 + x) * h) * h := by ring
          _ = _ := by rw [hscale]; ring
      _ ≤ 100 * h := mul_le_mul_of_nonneg_right (by linarith only [hepsilonHalf]) hh.le
  · calc
      _ ≤ (67 / 3 : ℝ) * gamma + (1 + x) * ((128 / 3 : ℝ) * h * gamma) :=
        add_le_add hz (mul_le_mul_of_nonneg_left hy ha.le)
      _ = ((67 + 128 * epsilon) / 3) * gamma := by
        calc
          _ = (67 / 3 : ℝ) * gamma + (128 / 3 : ℝ) * ((1 + x) * h) * gamma := by ring
          _ = _ := by rw [hscale]; ring
      _ ≤ 100 * gamma := mul_le_mul_of_nonneg_right (by linarith only [hepsilonHalf]) hg.le

end Shao
