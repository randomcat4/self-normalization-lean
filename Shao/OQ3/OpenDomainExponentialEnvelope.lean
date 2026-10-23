import Shao.Probability.BivariateLegendre

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem open_domain_local_exponential_envelope
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))) :
    ∃ r : ℝ, 0 < r ∧
      (theta.1 + r, theta.2 + r) ∈
        Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)) ∧
      (theta.1 - r, theta.2 + r) ∈
        Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)) ∧
      let g : ℝ → ℝ := fun x =>
        Real.exp ((theta.1 + r) * x + (theta.2 + r) * x ^ 2) +
          Real.exp ((theta.1 - r) * x + (theta.2 + r) * x ^ 2)
      Integrable g mu ∧ (∀ x : ℝ, 0 ≤ g x) ∧
        ∀ p : ℝ × ℝ, ‖p - theta‖ < r →
          Integrable (fun x : ℝ => Real.exp (p.1 * x + p.2 * x ^ 2)) mu ∧
            ∀ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ≤ g x := by
  obtain ⟨delta, hdelta, hball⟩ := Metric.isOpen_iff.1 isOpen_interior theta htheta
  let r : ℝ := delta / 2
  have hr : 0 < r := half_pos hdelta
  have hrdelta : r < delta := by dsimp [r]; linarith
  have hplusNorm : ‖((theta.1 + r, theta.2 + r) : ℝ × ℝ) - theta‖ = r := by
    change max |theta.1 + r - theta.1| |theta.2 + r - theta.2| = r
    rw [show theta.1 + r - theta.1 = r by ring,
      show theta.2 + r - theta.2 = r by ring, abs_of_pos hr, max_self]
  have hminusNorm : ‖((theta.1 - r, theta.2 + r) : ℝ × ℝ) - theta‖ = r := by
    change max |theta.1 - r - theta.1| |theta.2 + r - theta.2| = r
    rw [show theta.1 - r - theta.1 = -r by ring,
      show theta.2 + r - theta.2 = r by ring, abs_neg, abs_of_pos hr, max_self]
  have hplus : (theta.1 + r, theta.2 + r) ∈
      Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)) := by
    apply interior_subset
    apply hball
    change dist (theta.1 + r, theta.2 + r) theta < delta
    rw [dist_eq_norm, hplusNorm]
    exact hrdelta
  have hminus : (theta.1 - r, theta.2 + r) ∈
      Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)) := by
    apply interior_subset
    apply hball
    change dist (theta.1 - r, theta.2 + r) theta < delta
    rw [dist_eq_norm, hminusNorm]
    exact hrdelta
  have hiPlus : Integrable (fun x : ℝ =>
      Real.exp ((theta.1 + r) * x + (theta.2 + r) * x ^ 2)) mu := hplus
  have hiMinus : Integrable (fun x : ℝ =>
      Real.exp ((theta.1 - r) * x + (theta.2 + r) * x ^ 2)) mu := hminus
  refine ⟨r, hr, hplus, hminus, ?_⟩
  dsimp only
  let g : ℝ → ℝ := fun x =>
    Real.exp ((theta.1 + r) * x + (theta.2 + r) * x ^ 2) +
      Real.exp ((theta.1 - r) * x + (theta.2 + r) * x ^ 2)
  have hg : Integrable g mu := hiPlus.add hiMinus
  refine ⟨hg, fun x => add_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _), ?_⟩
  intro p hp
  change max |p.1 - theta.1| |p.2 - theta.2| < r at hp
  have hp0 : |p.1 - theta.1| < r := lt_of_le_of_lt (le_max_left _ _) hp
  have hp1 : |p.2 - theta.2| < r := lt_of_le_of_lt (le_max_right _ _) hp
  have huUpper : p.1 ≤ theta.1 + r := by linarith [(abs_lt.mp hp0).2]
  have huLower : theta.1 - r ≤ p.1 := by linarith [(abs_lt.mp hp0).1]
  have hvUpper : p.2 ≤ theta.2 + r := by linarith [(abs_lt.mp hp1).2]
  have hbound : ∀ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ≤ g x := by
    intro x
    by_cases hx : 0 ≤ x
    · have hphase : p.1 * x + p.2 * x ^ 2 ≤
          (theta.1 + r) * x + (theta.2 + r) * x ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_right huUpper hx)
          (mul_le_mul_of_nonneg_right hvUpper (sq_nonneg x))
      exact (Real.exp_le_exp.mpr hphase).trans
        (le_add_of_nonneg_right (Real.exp_nonneg _))
    · have hphase : p.1 * x + p.2 * x ^ 2 ≤
          (theta.1 - r) * x + (theta.2 + r) * x ^ 2 :=
        add_le_add (mul_le_mul_of_nonpos_right huLower (le_of_not_ge hx))
          (mul_le_mul_of_nonneg_right hvUpper (sq_nonneg x))
      exact (Real.exp_le_exp.mpr hphase).trans
        (le_add_of_nonneg_left (Real.exp_nonneg _))
  have hcont : Continuous (fun x : ℝ => Real.exp (p.1 * x + p.2 * x ^ 2)) := by
    fun_prop
  refine ⟨hg.mono' hcont.aestronglyMeasurable ?_, hbound⟩
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hbound x)

end
end Shao.OQ3
