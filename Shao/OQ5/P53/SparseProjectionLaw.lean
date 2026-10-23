import Shao.OQ5.P53.SparseSignedShift
import Shao.OQ5.P35.NoiseMoments
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace Shao.OQ5.P53

def sparseGBaseMeasure (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) : Measure (ℝ × (ℕ × Bool)) :=
  Shao.OQ5.P35.noiseLaw.prod (sparseSignedLabelMeasure α x N)

def sparseG (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (z : ℝ × (ℕ × Bool)) : ℝ :=
  z.1 + sparseSignedShift α x N z.2

private theorem projection_square_terms_integrable
    (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (hα : 0 < α) (hN : SparseSelectionCore α x N) :
    Integrable (fun z : ℝ × (ℕ × Bool) => z.1 ^ 2)
      (sparseGBaseMeasure α x N) ∧
    Integrable (fun z : ℝ × (ℕ × Bool) => (sparseSignedShift α x N z.2) ^ 2)
      (sparseGBaseMeasure α x N) ∧
    Integrable (fun z : ℝ × (ℕ × Bool) => z.1 * sparseSignedShift α x N z.2)
      (sparseGBaseMeasure α x N) := by
  let : IsProbabilityMeasure (sparseSignedLabelMeasure α x N) :=
    sparseSignedLabelMeasure_probability α x N
  refine ⟨?_, ?_, ?_⟩
  · exact Shao.OQ5.P35.integrable_noiseLaw_sq.comp_fst _
  · exact (integrable_sparseSignedShift_sq α x N hα hN).comp_snd _
  · exact Shao.OQ5.P35.integrable_noiseLaw_id.mul_prod
      (integrable_sparseSignedShift α x N hα hN)

private theorem bounded_noise_add_rpow (a d q : ℝ) (ha : |a| ≤ 1) (hq : 0 ≤ q) :
    |a + d| ^ q ≤ (2 : ℝ) ^ q * (1 + |d| ^ q) := by
  have htwo : 0 ≤ (2 : ℝ) ^ q := Real.rpow_nonneg (by norm_num) q
  have hdq : 0 ≤ |d| ^ q := Real.rpow_nonneg (abs_nonneg d) q
  have htri : |a + d| ≤ |a| + |d| := by
    simpa only [Real.norm_eq_abs] using norm_add_le a d
  rcases le_total |d| 1 with hd | hd
  · have hab : |a + d| ≤ (2 : ℝ) := htri.trans (by linarith)
    calc
      |a + d| ^ q ≤ (2 : ℝ) ^ q := Real.rpow_le_rpow (abs_nonneg _) hab hq
      _ ≤ (2 : ℝ) ^ q * (1 + |d| ^ q) := by
        nlinarith [mul_nonneg htwo hdq]
  · have hab : |a + d| ≤ 2 * |d| := htri.trans (by linarith)
    calc
      |a + d| ^ q ≤ (2 * |d|) ^ q := Real.rpow_le_rpow (abs_nonneg _) hab hq
      _ = (2 : ℝ) ^ q * |d| ^ q := Real.mul_rpow (by norm_num) (abs_nonneg d)
      _ ≤ (2 : ℝ) ^ q * (1 + |d| ^ q) := by nlinarith

theorem sparseGBaseMeasure_probability :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  IsProbabilityMeasure (sparseGBaseMeasure α x N) := by
  intro α x N
  let : IsProbabilityMeasure (sparseSignedLabelMeasure α x N) :=
    sparseSignedLabelMeasure_probability α x N
  unfold sparseGBaseMeasure
  infer_instance

theorem measurable_sparseG :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), Measurable (sparseG α x N) := by
  intro α x N
  exact measurable_fst.add ((measurable_sparseSignedShift α x N).comp measurable_snd)

theorem integrable_sparseG :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  Integrable (sparseG α x N) (sparseGBaseMeasure α x N) := by
  intro α x N hα hN
  let : IsProbabilityMeasure (sparseSignedLabelMeasure α x N) :=
    sparseSignedLabelMeasure_probability α x N
  exact (Shao.OQ5.P35.integrable_noiseLaw_id.comp_fst _).add
    ((integrable_sparseSignedShift α x N hα hN).comp_snd _)

theorem integral_sparseG_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (∫ z, sparseG α x N z ∂(sparseGBaseMeasure α x N)) = 0 := by
  intro α x N hα hN
  let : IsProbabilityMeasure (sparseSignedLabelMeasure α x N) :=
    sparseSignedLabelMeasure_probability α x N
  have hA : Integrable (fun z : ℝ × (ℕ × Bool) => z.1)
      (Shao.OQ5.P35.noiseLaw.prod (sparseSignedLabelMeasure α x N)) :=
    Shao.OQ5.P35.integrable_noiseLaw_id.comp_fst _
  have hD : Integrable (fun z : ℝ × (ℕ × Bool) => sparseSignedShift α x N z.2)
      (Shao.OQ5.P35.noiseLaw.prod (sparseSignedLabelMeasure α x N)) :=
    (integrable_sparseSignedShift α x N hα hN).comp_snd _
  have hG := integrable_sparseG α x N hα hN
  change (∫ z : ℝ × (ℕ × Bool), z.1 + sparseSignedShift α x N z.2
    ∂(Shao.OQ5.P35.noiseLaw.prod (sparseSignedLabelMeasure α x N))) = 0
  rw [integral_add hA hD,
    integral_fun_fst (μ := Shao.OQ5.P35.noiseLaw) (ν := sparseSignedLabelMeasure α x N)
      (fun a : ℝ => a),
    integral_fun_snd (μ := Shao.OQ5.P35.noiseLaw) (ν := sparseSignedLabelMeasure α x N)
      (sparseSignedShift α x N),
    Shao.OQ5.P35.integral_noiseLaw_id, integral_sparseSignedShift_zero α x N hα hN]
  simp

theorem integrable_sparseG_sq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  Integrable (fun z => (sparseG α x N z) ^ 2) (sparseGBaseMeasure α x N) := by
  intro α x N hα hN
  rcases projection_square_terms_integrable α x N hα hN with ⟨hA, hD, hAD⟩
  have heq : (fun z => (sparseG α x N z) ^ 2) =
      (fun z : ℝ × (ℕ × Bool) =>
        z.1 ^ 2 + (sparseSignedShift α x N z.2) ^ 2 +
          2 * (z.1 * sparseSignedShift α x N z.2)) := by
    funext z
    dsimp only [sparseG]
    ring
  rw [heq]
  exact (hA.add hD).add (hAD.const_mul 2)

theorem integral_sparseG_sq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (∫ z, (sparseG α x N z) ^ 2 ∂(sparseGBaseMeasure α x N)) =
    (1 / 3 : ℝ) + ∫ w, (sparseSignedShift α x N w) ^ 2 ∂(sparseSignedLabelMeasure α x N) := by
  intro α x N hα hN
  let : IsProbabilityMeasure (sparseSignedLabelMeasure α x N) :=
    sparseSignedLabelMeasure_probability α x N
  have hGsq := integrable_sparseG_sq α x N hα hN
  rcases projection_square_terms_integrable α x N hα hN with ⟨hA, hD, hAD⟩
  change Integrable _ (Shao.OQ5.P35.noiseLaw.prod (sparseSignedLabelMeasure α x N)) at hA hD hAD
  have hAplusD : Integrable
      (fun z : ℝ × (ℕ × Bool) => z.1 ^ 2 + (sparseSignedShift α x N z.2) ^ 2)
      (Shao.OQ5.P35.noiseLaw.prod (sparseSignedLabelMeasure α x N)) := hA.add hD
  have hcross :
      (∫ z : ℝ × (ℕ × Bool), z.1 * sparseSignedShift α x N z.2
        ∂(Shao.OQ5.P35.noiseLaw.prod (sparseSignedLabelMeasure α x N))) = 0 := by
    rw [integral_prod_mul (μ := Shao.OQ5.P35.noiseLaw) (ν := sparseSignedLabelMeasure α x N)
      (fun a : ℝ => a) (sparseSignedShift α x N),
      Shao.OQ5.P35.integral_noiseLaw_id, zero_mul]
  change (∫ z : ℝ × (ℕ × Bool), (sparseG α x N z) ^ 2
    ∂(Shao.OQ5.P35.noiseLaw.prod (sparseSignedLabelMeasure α x N))) = _
  calc
    (∫ z : ℝ × (ℕ × Bool), (sparseG α x N z) ^ 2
        ∂(Shao.OQ5.P35.noiseLaw.prod (sparseSignedLabelMeasure α x N))) =
        ∫ z : ℝ × (ℕ × Bool),
          z.1 ^ 2 + (sparseSignedShift α x N z.2) ^ 2 +
            2 * (z.1 * sparseSignedShift α x N z.2)
          ∂(Shao.OQ5.P35.noiseLaw.prod (sparseSignedLabelMeasure α x N)) := by
      apply integral_congr_ae
      filter_upwards with z
      dsimp only [sparseG]
      ring
    _ = (∫ z : ℝ × (ℕ × Bool), z.1 ^ 2
          ∂(Shao.OQ5.P35.noiseLaw.prod (sparseSignedLabelMeasure α x N))) +
        (∫ z : ℝ × (ℕ × Bool), (sparseSignedShift α x N z.2) ^ 2
          ∂(Shao.OQ5.P35.noiseLaw.prod (sparseSignedLabelMeasure α x N))) +
        2 * (∫ z : ℝ × (ℕ × Bool), z.1 * sparseSignedShift α x N z.2
          ∂(Shao.OQ5.P35.noiseLaw.prod (sparseSignedLabelMeasure α x N))) := by
      rw [integral_add hAplusD (hAD.const_mul 2),
        integral_add hA hD, integral_const_mul]
    _ = (1 / 3 : ℝ) +
        ∫ w, (sparseSignedShift α x N w) ^ 2 ∂(sparseSignedLabelMeasure α x N) := by
      rw [integral_fun_fst (μ := Shao.OQ5.P35.noiseLaw) (ν := sparseSignedLabelMeasure α x N)
        (fun a : ℝ => a ^ 2),
        integral_fun_snd (μ := Shao.OQ5.P35.noiseLaw) (ν := sparseSignedLabelMeasure α x N)
          (fun w : ℕ × Bool => (sparseSignedShift α x N w) ^ 2),
        Shao.OQ5.P35.integral_noiseLaw_sq, hcross]
      simp

theorem integral_sparseG_sq_ge :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (1 / 3 : ℝ) ≤ ∫ z, (sparseG α x N z) ^ 2 ∂(sparseGBaseMeasure α x N) := by
  intro α x N hα hN
  rw [integral_sparseG_sq α x N hα hN]
  exact le_add_of_nonneg_right (integral_nonneg (fun w => sq_nonneg _))

theorem integrable_sparseG_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ q : ℝ, 0 < q →
  Integrable (fun z => |sparseG α x N z| ^ q) (sparseGBaseMeasure α x N) := by
  intro α x N hα hN q hq
  let : IsProbabilityMeasure (sparseSignedLabelMeasure α x N) :=
    sparseSignedLabelMeasure_probability α x N
  have hnoise : ∀ᵐ z : ℝ × (ℕ × Bool)
      ∂(Shao.OQ5.P35.noiseLaw.prod (sparseSignedLabelMeasure α x N)),
      z.1 ∈ Set.Icc (-1 : ℝ) 1 := by
    apply (Measure.ae_prod_iff_ae_ae (measurable_fst measurableSet_Icc)).2
    filter_upwards [Shao.OQ5.P35.noiseLaw_ae_mem] with a ha
    exact Filter.Eventually.of_forall (fun _ => ha)
  have hD : Integrable (fun z : ℝ × (ℕ × Bool) => |sparseSignedShift α x N z.2| ^ q)
      (Shao.OQ5.P35.noiseLaw.prod (sparseSignedLabelMeasure α x N)) :=
    (integrable_sparseSignedShift_rpow α x N hα hN q hq).comp_snd _
  have hone : Integrable (fun _ : ℝ × (ℕ × Bool) => (1 : ℝ))
      (Shao.OQ5.P35.noiseLaw.prod (sparseSignedLabelMeasure α x N)) := integrable_const 1
  have hdom := (hone.add hD).const_mul ((2 : ℝ) ^ q)
  have hc : Continuous (fun t : ℝ => |t| ^ q) :=
    continuous_abs.rpow_const (fun _ => Or.inr hq.le)
  have hm : AEStronglyMeasurable (fun z => |sparseG α x N z| ^ q)
      (Shao.OQ5.P35.noiseLaw.prod (sparseSignedLabelMeasure α x N)) :=
    (hc.measurable.comp (measurable_sparseG α x N)).aestronglyMeasurable
  change Integrable _ (Shao.OQ5.P35.noiseLaw.prod (sparseSignedLabelMeasure α x N))
  apply hdom.mono' hm
  filter_upwards [hnoise] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) q)]
  exact bounded_noise_add_rpow z.1 (sparseSignedShift α x N z.2) q
    (abs_le.mpr hz) hq.le

end Shao.OQ5.P53
