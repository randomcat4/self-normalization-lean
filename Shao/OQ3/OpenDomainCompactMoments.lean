import Shao.OQ3.OpenDomainSmoothMean

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem open_domain_tilted_moment_contDiffOn
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (k : ℕ) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ => ∫ x : ℝ, x ^ k
        ∂mu.tilted (fun x => p.1 * x + p.2 * x ^ 2))
      (interior (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))) := by
  let Omega : Set (ℝ × ℝ) := interior
    (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
  let I : ℕ → (ℝ × ℝ) → ℝ := fun j p =>
    ∫ x : ℝ, x ^ j * Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu
  have hI (j : ℕ) : ContDiffOn ℝ ∞ (I j) Omega := open_domain_weighted_moment_contDiffOn mu j
  have hpos (p : ℝ × ℝ) (hp : p ∈ Omega) : 0 < I 0 p := by
    simpa only [I, pow_zero, one_mul] using integral_exp_pos (show Integrable
      (fun x : ℝ => Real.exp (p.1 * x + p.2 * x ^ 2)) mu from interior_subset hp)
  have hn := (hI k).div (hI 0) (fun p hp => (hpos p hp).ne')
  apply hn.congr
  intro p _
  rw [integral_tilted]
  change (∫ x : ℝ, (Real.exp (p.1 * x + p.2 * x ^ 2) /
    (∫ y, Real.exp (p.1 * y + p.2 * y ^ 2) ∂mu)) * x ^ k ∂mu) = I k p / I 0 p
  have hf : (fun x : ℝ => (Real.exp (p.1 * x + p.2 * x ^ 2) /
      (∫ y, Real.exp (p.1 * y + p.2 * y ^ 2) ∂mu)) * x ^ k) =
      (fun x => (x ^ k * Real.exp (p.1 * x + p.2 * x ^ 2)) /
        (∫ y, Real.exp (p.1 * y + p.2 * y ^ 2) ∂mu)) := by
    funext x
    ring
  rw [hf, integral_div]
  simp only [I, pow_zero, one_mul]

theorem compact_open_domain_uniform_tilted_moments
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (Theta : Set (ℝ × ℝ))
    (hcompact : IsCompact Theta)
    (hTheta : Theta ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))) :
    let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    (∀ theta ∈ Theta, IsProbabilityMeasure (nu theta)) ∧
      ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ theta ∈ Theta,
        Integrable (fun x : ℝ => |x| ^ k) (nu theta) ∧
          0 ≤ (∫ x : ℝ, |x| ^ k ∂nu theta) ∧
          (∫ x : ℝ, |x| ^ k ∂nu theta) ≤ C := by
  let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
    mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
  have hprob (theta : ℝ × ℝ) (htheta : theta ∈ Theta) : IsProbabilityMeasure (nu theta) :=
    (open_domain_quadratic_tilt_directional_cumulants mu theta (hTheta htheta)).1
  refine ⟨hprob, ?_⟩
  intro k
  let M : (ℝ × ℝ) → ℝ := fun p => ∫ x : ℝ, x ^ (2 * k) ∂nu p
  have hc : ContinuousOn M Theta :=
    (open_domain_tilted_moment_contDiffOn mu (2 * k)).continuousOn.mono hTheta
  have hb : BddAbove (M '' Theta) := (hcompact.image_of_continuousOn hc).bddAbove
  obtain ⟨B, hB⟩ := hb
  refine ⟨|B| + 2, by positivity, ?_⟩
  intro theta htheta
  letI : IsProbabilityMeasure (nu theta) := hprob theta htheta
  have hi (j : ℕ) : Integrable (fun x : ℝ => x ^ j) (nu theta) := by
    have h := (open_domain_quadratic_tilt_directional_cumulants mu theta (hTheta htheta)).2.2.2 (1, 0)
    simpa using h.2.2.1 j
  have ha : Integrable (fun x : ℝ => |x| ^ k) (nu theta) := by
    simpa only [Real.norm_eq_abs, abs_pow] using (hi k).norm
  have heven := hi (2 * k)
  have hpoint (x : ℝ) : |x| ^ k ≤ 1 + x ^ (2 * k) := by
    have heq : (|x| ^ k) ^ 2 = x ^ (2 * k) := by
      calc
        (|x| ^ k) ^ 2 = |x ^ k| ^ 2 := by rw [abs_pow]
        _ = (x ^ k) ^ 2 := sq_abs _
        _ = x ^ (2 * k) := by rw [← pow_mul, Nat.mul_comm k 2]
    nlinarith [sq_nonneg (|x| ^ k - 1), pow_nonneg (abs_nonneg x) k]
  refine ⟨ha, integral_nonneg (fun x => pow_nonneg (abs_nonneg x) k), ?_⟩
  calc
    (∫ x : ℝ, |x| ^ k ∂nu theta) ≤ ∫ x : ℝ, (1 + x ^ (2 * k)) ∂nu theta :=
      integral_mono ha ((integrable_const 1).add heven) hpoint
    _ = 1 + M theta := by rw [integral_add (integrable_const 1) heven]; simp [M]
    _ ≤ 1 + B := by linarith [hB ⟨theta, htheta, rfl⟩]
    _ ≤ |B| + 2 := by linarith [le_abs_self B]

end
end Shao.OQ3
