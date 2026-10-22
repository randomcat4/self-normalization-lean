import Shao.OQ3.SourceGlobalExponentialTests
import Shao.Probability.BivariateLegendre

/-!
# Canonical global Legendre minimum for the same source law

Source: current/oq3/proofs/r1/report.md, lines 161–237.
Source SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U20c scope: d716c2d9c356f3e3562605885394e75f95565c8649bc66c40a88853d11d1e351.
-/

namespace Shao.OQ3
open MeasureTheory Shao.Probability
open scoped Matrix
noncomputable section

theorem source_canonical_rate_unique_minimizer
    (q : ℝ) (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k : Fin 4,
      HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
        (constraintTarget q k)) :
    let P : Measure ℝ := originalMeasure sourceEll w
    letI : IsProbabilityMeasure P := originalMeasure_isProbabilityMeasure sourceEll w hw
      (by simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one]
        using hm 0)
    let W : ℝ → ℝ × ℝ := fun x => (x, x ^ 2)
    let D : Set (ℝ × ℝ) :=
      {z | 0 < z.2 ∧ (Real.sqrt q / 4) * Real.sqrt z.2 ≤ z.1}
    bivariateMGFDomain P W = Set.univ ∧
      (∀ theta : bivariateMGFDomain P W,
        (0 < ∫ x : ℝ, Real.exp
          ((theta : ℝ × ℝ).1 * x + (theta : ℝ × ℝ).2 * x ^ 2) ∂P) ∧
        bivariateLogMGF P W theta =
          Real.log (∫ x : ℝ, Real.exp
            ((theta : ℝ × ℝ).1 * x + (theta : ℝ × ℝ).2 * x ^ 2) ∂P)) ∧
      ∃ theta0 : bivariateMGFDomain P W,
        (theta0 : ℝ × ℝ) = (8 * sourceEll, -sourceEll) ∧
        ((theta0 : ℝ × ℝ).1 * (q / 4) + (theta0 : ℝ × ℝ).2 * q -
          bivariateLogMGF P W theta0 = saddleRate sourceEll q w) ∧
        (q / 4, q) ∈ D ∧
        bivariateLegendreRate P W (q / 4, q) = (saddleRate sourceEll q w : EReal) ∧
        ∀ z ∈ D,
          bivariateLegendreRate P W (q / 4, q) ≤ bivariateLegendreRate P W z ∧
          (bivariateLegendreRate P W z = bivariateLegendreRate P W (q / 4, q) ↔
            z = (q / 4, q)) := by
  classical
  have hs : HasSum w 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  let P : Measure ℝ := originalMeasure sourceEll w
  letI : IsProbabilityMeasure P := originalMeasure_isProbabilityMeasure sourceEll w hw hs
  let W : ℝ → ℝ × ℝ := fun x => (x, x ^ 2)
  let D : Set (ℝ × ℝ) :=
    {z | 0 < z.2 ∧ (Real.sqrt q / 4) * Real.sqrt z.2 ≤ z.1}
  obtain ⟨hvalue, hattainRaw⟩ := source_saddle_exponential_value_bound q w hw hm
  have hmem (theta : ℝ × ℝ) : theta ∈ bivariateMGFDomain P W :=
    (hvalue theta.1 theta.2).1
  have hdomain : bivariateMGFDomain P W = Set.univ := by
    apply Set.ext
    intro theta
    exact ⟨fun _ => Set.mem_univ theta, fun _ => hmem theta⟩
  let theta0 : bivariateMGFDomain P W :=
    ⟨(8 * sourceEll, -sourceEll), hmem (8 * sourceEll, -sourceEll)⟩
  have hupper (theta : bivariateMGFDomain P W) :
      (theta : ℝ × ℝ).1 * (q / 4) + (theta : ℝ × ℝ).2 * q -
        bivariateLogMGF P W theta ≤ saddleRate sourceEll q w :=
    (hvalue (theta : ℝ × ℝ).1 (theta : ℝ × ℝ).2).2.2
  have hattain :
      (theta0 : ℝ × ℝ).1 * (q / 4) + (theta0 : ℝ × ℝ).2 * q -
        bivariateLogMGF P W theta0 = saddleRate sourceEll q w := hattainRaw
  have hq : 0 < q := lt_trans zero_lt_one hq0
  have hz0 : (q / 4, q) ∈ D := by
    change 0 < q ∧ (Real.sqrt q / 4) * Real.sqrt q ≤ q / 4
    refine ⟨hq, le_of_eq ?_⟩
    calc
      _ = (Real.sqrt q * Real.sqrt q) / 4 := by ring
      _ = q / 4 := by rw [Real.mul_self_sqrt hq.le]
  have hsep : ∀ z ∈ D, z ≠ (q / 4, q) →
      ∃ theta : bivariateMGFDomain P W,
        saddleRate sourceEll q w <
          (theta : ℝ × ℝ).1 * z.1 + (theta : ℝ × ℝ).2 * z.2 -
            bivariateLogMGF P W theta := by
    intro z hz hne
    have hne' : z.1 ≠ q / 4 ∨ z.2 ≠ q := by
      by_cases ha : z.1 = q / 4
      · exact Or.inr (fun hc => hne (Prod.ext ha hc))
      · exact Or.inl ha
    obtain ⟨s, t, hi, _, hstrict⟩ := exists_source_tail_exponential_separator
      q hq0 hq1 w hw hm z.1 z.2 hz.1 hz.2 hne'
    let theta : bivariateMGFDomain P W := ⟨(s, t), hi⟩
    exact ⟨theta, hstrict⟩
  have hcanonical := bivariateLegendreRate_unique_minimizer_of_tests P W D
    (q / 4, q) (saddleRate sourceEll q w) hz0 hupper theta0 hattain hsep
  refine ⟨hdomain, ?_, theta0, rfl, hattain, hz0, hcanonical.1, hcanonical.2⟩
  intro theta
  exact ⟨(bivariateLogMGF_spec P W theta).1, rfl⟩

end
end Shao.OQ3
