import Shao.OQ3.GaussianSmoothedFourierTail
import Shao.OQ3.GaussianSmoothedRealDensity

namespace Shao.OQ3
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

theorem gaussian_smoothed_pair_absolute_tail_bound
    (nu : Measure (ℝ × ℝ)) [IsProbabilityMeasure nu]
    (b R : ℝ) (hb : 0 < b) (hR : 0 ≤ R)
    (s : Set (ℝ × ℝ)) (hs : MeasurableSet s)
    (hout : ∀ z ∈ s, R ^ 2 ≤ z.1 ^ 2 + z.2 ^ 2) :
    let v : ℝ≥0 := Real.toNNReal (2 * b)
    let gamma : Measure (ℝ × ℝ) :=
      (ProbabilityTheory.gaussianReal 0 v).prod (ProbabilityTheory.gaussianReal 0 v)
    let rho : Measure (ℝ × ℝ) := (nu.prod gamma).map (fun q => q.1 + q.2)
    let Phi : (ℝ × ℝ) → ℂ := fun z =>
      ∫ w : ℝ × ℝ, Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho
    Integrable Phi ∧ IntegrableOn Phi s ∧
      (∫ z in s, ‖Phi z‖) ≤ (2 * Real.pi / b) * Real.exp (-b * R ^ 2 / 2) := by
  intro v gamma rho Phi
  obtain ⟨hrho, hcf, hall⟩ := gaussian_smoothed_pair_law_fourier_integral nu b hb
  have hi : Integrable Phi := by simpa [Phi, rho, gamma, v] using (hall (0, 0)).1
  have hnu := (pair_characteristic_measurable_norm_le_one nu).2
  obtain ⟨hig, hvg⟩ := pair_real_gaussian_integral (b / 2) (half_pos hb)
  let envelope : (ℝ × ℝ) → ℝ := fun z =>
    Real.exp (-b * R ^ 2 / 2) * Real.exp (-(b / 2) * (z.1 ^ 2 + z.2 ^ 2))
  have hie : Integrable envelope := hig.const_mul _
  have hen (z : ℝ × ℝ) : 0 ≤ envelope z := by dsimp only [envelope]; positivity
  have hdom (z : ℝ × ℝ) (hz : z ∈ s) : ‖Phi z‖ ≤ envelope z := by
    have hgauss : ‖Complex.exp (-(b : ℂ) * ((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ))‖ =
        Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2)) := by
      rw [← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hn : ‖Phi z‖ ≤ Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2)) := by
      dsimp only [Phi]
      rw [hcf z, norm_mul, hgauss]
      exact mul_le_of_le_one_left (Real.exp_nonneg _) (hnu z)
    have he : Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2)) ≤ envelope z := by
      dsimp only [envelope]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hb.le (sub_nonneg.mpr (hout z hz))]
    exact hn.trans he
  refine ⟨hi, hi.integrableOn, ?_⟩
  calc
    (∫ z in s, ‖Phi z‖) ≤ ∫ z in s, envelope z :=
      integral_mono_ae hi.norm.integrableOn hie.integrableOn
        ((ae_restrict_mem hs).mono (fun z hz => hdom z hz))
    _ ≤ ∫ z : ℝ × ℝ, envelope z :=
      setIntegral_le_integral hie (Filter.Eventually.of_forall hen)
    _ = (2 * Real.pi / b) * Real.exp (-b * R ^ 2 / 2) := by
      dsimp only [envelope]
      rw [integral_const_mul, hvg]
      ring

theorem gaussian_smoothed_pair_density_damped_reference_bound
    (nu : Measure (ℝ × ℝ)) [IsProbabilityMeasure nu]
    (P : (ℝ × ℝ) → ℂ) (hPc : Continuous P) (hP : Integrable P)
    (b R : ℝ) (hb : 0 < b) (hR : 0 ≤ R) :
    let v : ℝ≥0 := Real.toNNReal (2 * b)
    let gamma : Measure (ℝ × ℝ) :=
      (ProbabilityTheory.gaussianReal 0 v).prod (ProbabilityTheory.gaussianReal 0 v)
    let rho : Measure (ℝ × ℝ) := (nu.prod gamma).map (fun q => q.1 + q.2)
    let k : (ℝ × ℝ) → ℝ := fun x => (1 / (4 * Real.pi * b)) *
      ∫ w : ℝ × ℝ, Real.exp (-((x.1 - w.1) ^ 2 + (x.2 - w.2) ^ 2) / (4 * b)) ∂nu
    let damping : (ℝ × ℝ) → ℝ := fun z => Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2))
    let Phi : (ℝ × ℝ) → ℂ := fun z =>
      ∫ w : ℝ × ℝ, Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂nu
    let error : (ℝ × ℝ) → ℂ := fun z => (damping z : ℂ) * (Phi z - P z)
    let window : Set (ℝ × ℝ) := {z | Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ≤ R}
    let kernel : (ℝ × ℝ) → (ℝ × ℝ) → ℂ := fun x z =>
      Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ))
    IsProbabilityMeasure rho ∧ rho = volume.withDensity (fun x => ENNReal.ofReal (k x)) ∧
      Integrable k ∧ (∫ x : ℝ × ℝ, k x) = 1 ∧ Integrable error ∧
      ∀ x : ℝ × ℝ,
        Integrable (fun z => kernel x z * ((damping z : ℂ) * P z)) ∧
          ‖((k x : ℝ) : ℂ) - (((1 / (2 * Real.pi) ^ 2 : ℝ) : ℂ) *
            ∫ z : ℝ × ℝ, kernel x z * ((damping z : ℂ) * P z))‖ ≤
            (1 / (2 * Real.pi) ^ 2) *
              ((∫ z in window, ‖error z‖) +
                (2 * Real.pi / b) * Real.exp (-b * R ^ 2 / 2) +
                  ∫ z in windowᶜ, ‖P z‖) := by
  intro v gamma rho k damping Phi error window kernel
  have hd : Continuous damping := by dsimp [damping]; fun_prop
  have hd0 (z : ℝ × ℝ) : 0 ≤ damping z := (Real.exp_pos _).le
  have hd1 (z : ℝ × ℝ) : damping z ≤ 1 := by
    apply Real.exp_le_one_iff.2
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb.le)
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hcexp (z : ℝ × ℝ) :
      Complex.exp (-(b : ℂ) * ((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ)) = (damping z : ℂ) := by
    dsimp only [damping]
    rw [← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
  have hdNorm (z : ℝ × ℝ) : ‖(damping z : ℂ) * P z‖ ≤ ‖P z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd0 z)]
    exact mul_le_of_le_one_left (norm_nonneg _) (hd1 z)
  have hdP : Integrable (fun z => (damping z : ℂ) * P z) := by
    apply hP.norm.mono' (by
      have h : Continuous (fun z => (damping z : ℂ) * P z) := by fun_prop
      exact h.aestronglyMeasurable)
    exact Filter.Eventually.of_forall hdNorm
  have hw : MeasurableSet window := by
    dsimp only [window]
    apply measurableSet_le _ measurable_const
    fun_prop
  have hout (z : ℝ × ℝ) (hz : z ∈ windowᶜ) : R ^ 2 ≤ z.1 ^ 2 + z.2 ^ 2 := by
    have hl : R < Real.sqrt (z.1 ^ 2 + z.2 ^ 2) := lt_of_not_ge hz
    nlinarith [Real.sq_sqrt (add_nonneg (sq_nonneg z.1) (sq_nonneg z.2))]
  have ht := gaussian_smoothed_pair_absolute_tail_bound nu b R hb hR windowᶜ hw.compl hout
  let F : (ℝ × ℝ) → ℂ := fun z =>
    ∫ w : ℝ × ℝ, Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho
  have hF : Integrable F := ht.1
  have hcf := (gaussian_smoothed_pair_law_fourier_integral nu b hb).2.1
  have hid (z : ℝ × ℝ) : F z - (damping z : ℂ) * P z = error z := by
    dsimp only [F]
    rw [hcf z, hcexp]
    dsimp only [error, Phi]
    ring
  have he : Integrable error := (hF.sub hdP).congr (Filter.Eventually.of_forall hid)
  have hden := gaussian_smoothed_pair_real_density nu b hb
  refine ⟨hden.1, hden.2.1, hden.2.2.2.2.1, hden.2.2.2.2.2, he, ?_⟩
  intro x
  have hk : Continuous (kernel x) := by dsimp [kernel]; fun_prop
  have hkNorm (z : ℝ × ℝ) : ‖kernel x z‖ = 1 := by
    simp [kernel, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  let f : (ℝ × ℝ) → ℂ := fun z => kernel x z * F z
  let g : (ℝ × ℝ) → ℂ := fun z => kernel x z * ((damping z : ℂ) * P z)
  let e : (ℝ × ℝ) → ℂ := fun z => kernel x z * error z
  have hnormf (z : ℝ × ℝ) : ‖f z‖ = ‖F z‖ := by
    dsimp only [f]; rw [norm_mul, hkNorm, one_mul]
  have hnormg (z : ℝ × ℝ) : ‖g z‖ ≤ ‖P z‖ := by
    dsimp only [g]; rw [norm_mul, hkNorm, one_mul]; exact hdNorm z
  have hnorme (z : ℝ × ℝ) : ‖e z‖ = ‖error z‖ := by
    dsimp only [e]; rw [norm_mul, hkNorm, one_mul]
  have hi := gaussian_smoothed_pair_normalized_inverse nu b hb x
  have hf : Integrable f := hi.1
  have hg : Integrable g := by
    apply hP.norm.mono' (by
      have hc : Continuous g := by dsimp [g]; fun_prop
      exact hc.aestronglyMeasurable)
    exact Filter.Eventually.of_forall hnormg
  have hfg (z : ℝ × ℝ) : f z - g z = e z := by
    dsimp only [f, g, e]
    rw [← mul_sub, hid]
  have hei : Integrable e := (hf.sub hg).congr (Filter.Eventually.of_forall hfg)
  have hcentral : ‖∫ z in window, e z‖ ≤ ∫ z in window, ‖error z‖ := by
    calc
      _ ≤ ∫ z in window, ‖e z‖ := norm_integral_le_integral_norm _
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall hnorme)
  have htailf : ‖∫ z in windowᶜ, f z‖ ≤
      (2 * Real.pi / b) * Real.exp (-b * R ^ 2 / 2) := by
    calc
      _ ≤ ∫ z in windowᶜ, ‖f z‖ := norm_integral_le_integral_norm _
      _ = ∫ z in windowᶜ, ‖F z‖ :=
        integral_congr_ae (Filter.Eventually.of_forall hnormf)
      _ ≤ _ := ht.2.2
  have htailg : ‖∫ z in windowᶜ, g z‖ ≤ ∫ z in windowᶜ, ‖P z‖ :=
    (norm_integral_le_integral_norm _).trans
      (integral_mono hg.norm.integrableOn hP.norm.integrableOn hnormg)
  have hsplit : (∫ z : ℝ × ℝ, f z) - (∫ z : ℝ × ℝ, g z) =
      (∫ z in window, e z) + (∫ z in windowᶜ, f z) - (∫ z in windowᶜ, g z) := by
    have hc : (∫ z in window, e z) =
        (∫ z in window, f z) - (∫ z in window, g z) := by
      rw [← integral_sub hf.integrableOn hg.integrableOn]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun z => (hfg z).symm))
    rw [hc, ← integral_add_compl hw hf, ← integral_add_compl hw hg]
    ring
  have hbound : ‖(∫ z : ℝ × ℝ, f z) - (∫ z : ℝ × ℝ, g z)‖ ≤
      (∫ z in window, ‖error z‖) +
        (2 * Real.pi / b) * Real.exp (-b * R ^ 2 / 2) + ∫ z in windowᶜ, ‖P z‖ := by
    rw [hsplit]
    calc
      _ ≤ ‖(∫ z in window, e z) + (∫ z in windowᶜ, f z)‖ +
          ‖∫ z in windowᶜ, g z‖ := norm_sub_le _ _
      _ ≤ (‖∫ z in window, e z‖ + ‖∫ z in windowᶜ, f z‖) +
          ‖∫ z in windowᶜ, g z‖ := add_le_add_right (norm_add_le _ _) _
      _ ≤ _ := add_le_add (add_le_add hcentral htailf) htailg
  have hc : 0 ≤ (1 / (2 * Real.pi) ^ 2 : ℝ) := by positivity
  refine ⟨hg, ?_⟩
  calc
    _ = ‖(((1 / (2 * Real.pi) ^ 2 : ℝ) : ℂ) *
        ((∫ z : ℝ × ℝ, f z) - (∫ z : ℝ × ℝ, g z)))‖ := by
      rw [← hi.2]
      congr 1
      ring
    _ = (1 / (2 * Real.pi) ^ 2) *
        ‖(∫ z : ℝ × ℝ, f z) - (∫ z : ℝ × ℝ, g z)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound hc

end
end Shao.OQ3
