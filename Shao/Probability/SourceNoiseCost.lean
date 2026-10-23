import Shao.Probability.SourceNoiseSandwich
import Shao.Probability.SourceClockBridge
import Shao.Probability.SourceTruncationBridge
import Shao.Probability.GaussianTail

set_option autoImplicit false
namespace Shao
open MeasureTheory ProbabilityTheory Probability

-- Frozen exact selected public head; proof implementation is separate.
theorem sourceTruncation_noise_badClock_weighted_cost
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (hmean : (∫ z : ℝ, z ∂ν) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 800)
    (hR : truncationBudget ν n x ≤ epsilon ^ 3 / 8) :
    let h := epsilon / (1 + x)
    let rho := ProbabilityTheory.cond ν {z | |z| ≤ h}
    let P := Measure.pi (fun _ : Fin n => rho)
    let law := Probability.quadraticFullNoiseLaw rho
    let delta := fun z : ℝ × ℝ => 4 * (|z.1| + (1 + x) * |z.2|)
    let bad := P.real {a : Fin n → ℝ | energy a ∉ Set.Icc (1 / 4 : ℝ) 2}
    let R := truncationBudget ν n x
    Integrable delta law ∧
      bad + standardNormalDensity x * (∫ z, delta z ∂law) ≤
        (32768 * Real.sqrt (2 * Real.pi) + 1 / standardNormalTail 2 + 1600) *
          R * standardNormalTail x
 := by
  let h := epsilon / (1 + x)
  let rho := ProbabilityTheory.cond ν {z | |z| ≤ h}
  let P := Measure.pi (fun _ : Fin n => rho)
  let law := Probability.quadraticFullNoiseLaw rho
  let delta := fun z : ℝ × ℝ => 4 * (|z.1| + (1 + x) * |z.2|)
  let R := truncationBudget ν n x
  let gamma := (∫ z : ℝ, |z| ^ 3 ∂rho) / variance (id : ℝ → ℝ) rho
  let m3 := ∫ z : ℝ, |z| ^ 3 ∂rho
  have heHalf : epsilon ≤ 1 / 2 := by linarith
  have heEighth : epsilon ≤ 1 / 8 := by linarith
  have heOne : epsilon ≤ 1 := by linarith
  have ha : 0 < 1 + x := by linarith
  have hR0 : 0 ≤ R := truncationBudget_nonneg ν n h2 x
  have hs := sourceTruncation_actual_noise_cdf_sandwich ν n h2 hnorm hmean
    x epsilon hx hepsilon hepsilonSmall hR
  have hd : Integrable delta law := hs.2.2.1
  have hdelta : (∫ z, delta z ∂law) ≤ 400 * gamma := hs.2.2.2.2.1
  obtain ⟨_, _, _, _, _, _, hgamma, _, _⟩ :=
    sourceTruncation_gamma_bounds ν n h2 hnorm hmean x epsilon hx
      hepsilon heHalf hR
  change gamma ≤ 2 * (n : ℝ) * m3 at hgamma
  have hpaid := (sourceTruncation_paid_moments ν n h2 hnorm hmean
    x epsilon hx hepsilon heHalf hR).2.1
  change (n : ℝ) * m3 ≤ 2 * R / (1 + x) ^ 3 at hpaid
  have hmoment : (∫ z, delta z ∂law) ≤ 1600 * R / (1 + x) ^ 3 := by
    calc
      _ ≤ 400 * gamma := hdelta
      _ ≤ 800 * ((n : ℝ) * m3) := by nlinarith only [hgamma]
      _ ≤ 800 * (2 * R / (1 + x) ^ 3) :=
        mul_le_mul_of_nonneg_left hpaid (by norm_num)
      _ = _ := by ring
  have ha3 : 1 + x ≤ (1 + x) ^ 3 := by
    nlinarith [sq_nonneg x, pow_nonneg hx 3]
  have hmoment' : (∫ z, delta z ∂law) ≤ 1600 * R / (1 + x) :=
    hmoment.trans (div_le_div_of_nonneg_left (by positivity) ha ha3)
  have hdensity : 0 ≤ standardNormalDensity x :=
    (ProbabilityTheory.gaussianPDFReal_pos 0 1 x (by norm_num)).le
  have hnoise : standardNormalDensity x * (∫ z, delta z ∂law) ≤
      1600 * R * standardNormalTail x := by
    calc
      _ ≤ standardNormalDensity x * (1600 * R / (1 + x)) :=
        mul_le_mul_of_nonneg_left hmoment' hdensity
      _ = (1600 * R) * (standardNormalDensity x / (1 + x)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (standardNormal_mills_bounds x hx).1
        (by positivity)
  let μ := Measure.pi (fun _ : Fin n => ν)
  let X : Fin n → (Fin n → ℝ) → ℝ := fun i a => a i
  let A : Set (Fin n → ℝ) := ⋂ i : Fin n, X i ⁻¹' {z | |z| ≤ h}
  let μx := ProbabilityTheory.cond μ A
  have hX : ∀ i, Measurable (X i) := fun i => measurable_pi_apply i
  have hIndep : iIndepFun X μ :=
    iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable)
  have hLaw (i : Fin n) : IdentDistrib (X i) (id : ℝ → ℝ) μ ν := by
    refine ⟨(hX i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa only [Measure.map_id] using
      (measurePreserving_eval (fun _ : Fin n => ν) i).map_eq
  have hsample := sourceTruncation_conditioned_sample hX hIndep hLaw h2
    x epsilon hx hepsilon heOne hR
  have hmap := hsample.2.2.2.1
  change Measure.map (id : (Fin n → ℝ) → (Fin n → ℝ)) μx = P at hmap
  have hcond : μx = P := by simpa only [Measure.map_id] using hmap
  have hclock := (sourceTruncation_final_clock_probability_le hX hIndep hLaw
    h2 hnorm hmean x epsilon hx hepsilon heEighth hR).2.2
  change μx.real {a : Fin n → ℝ | energy a ∉ Set.Icc (1 / 4 : ℝ) 2} ≤
    (32768 * Real.sqrt (2 * Real.pi) + 1 / standardNormalTail 2) *
      R * standardNormalTail x at hclock
  rw [hcond] at hclock
  change Integrable delta law ∧
    P.real {a : Fin n → ℝ | energy a ∉ Set.Icc (1 / 4 : ℝ) 2} +
      standardNormalDensity x * (∫ z, delta z ∂law) ≤ _
  refine ⟨hd, ?_⟩
  calc
    _ ≤ (32768 * Real.sqrt (2 * Real.pi) + 1 / standardNormalTail 2) *
        R * standardNormalTail x + 1600 * R * standardNormalTail x :=
      add_le_add hclock hnoise
    _ = _ := by ring

end Shao
