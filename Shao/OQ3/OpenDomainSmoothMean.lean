import Shao.OQ3.OpenDomainFrechetCumulants
import Mathlib.Analysis.Calculus.ContDiff.RCLike

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem open_domain_weighted_moment_contDiffOn
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (k : ℕ) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ => ∫ x : ℝ, x ^ k * Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu)
      (interior (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))) := by
  let Omega : Set (ℝ × ℝ) := interior
    (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
  let I : ℕ → (ℝ × ℝ) → ℝ := fun j p =>
    ∫ x : ℝ, x ^ j * Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu
  let slope : ℕ → (ℝ × ℝ) → ((ℝ × ℝ) →L[ℝ] ℝ) := fun j p =>
    I (j + 1) p • ContinuousLinearMap.fst ℝ ℝ ℝ +
      I (j + 2) p • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hder (j : ℕ) (p : ℝ × ℝ) (hp : p ∈ Omega) : HasFDerivAt (I j) (slope j p) p :=
    (open_domain_weighted_moment_hasFDerivAt mu j p hp).2
  have hfinite : ∀ n : ℕ, ∀ j : ℕ, ContDiffOn ℝ n (I j) Omega := by
    intro n
    induction n with
    | zero =>
        intro j
        apply contDiffOn_zero.mpr
        exact fun p hp => (hder j p hp).continuousAt.continuousWithinAt
    | succ n ih =>
        intro j
        have hh : ContDiffOn ℝ ((n : WithTop ENat) + 1) (I j) Omega := by
          apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
            (show UniqueDiffOn ℝ Omega from isOpen_interior.uniqueDiffOn)).mpr
          refine ⟨by simp, slope j, ?_, fun p hp => (hder j p hp).hasFDerivWithinAt⟩
          exact ((ih (j + 1)).smul_const (ContinuousLinearMap.fst ℝ ℝ ℝ)).add
            ((ih (j + 2)).smul_const (ContinuousLinearMap.snd ℝ ℝ ℝ))
        simpa only [Nat.cast_add, Nat.cast_one] using hh
  exact contDiffOn_infty.mpr fun n => hfinite n k

theorem open_domain_quadratic_tilt_smooth_and_strict
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    let Omega : Set (ℝ × ℝ) := interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
    let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    let Z : (ℝ × ℝ) → ℝ := fun p =>
      ∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu
    let K : (ℝ × ℝ) → ℝ := fun p => Real.log (Z p)
    let means : (ℝ × ℝ) → (ℝ × ℝ) := fun p =>
      (∫ x : ℝ, x ∂nu p, ∫ x : ℝ, x ^ 2 ∂nu p)
    ContDiffOn ℝ ∞ Z Omega ∧ ContDiffOn ℝ ∞ K Omega ∧
      ContDiffOn ℝ ∞ means Omega ∧
      ∀ theta ∈ Omega,
        let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (nu theta)
        let pr0 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
        let pr1 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
        let row0 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 0 • pr0 + D 0 1 • pr1
        let row1 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 1 • pr0 + D 1 1 • pr1
        HasStrictFDerivAt means (row0.prod row1) theta := by
  let Omega : Set (ℝ × ℝ) := interior
    (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
  let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
    mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
  let Z : (ℝ × ℝ) → ℝ := fun p =>
    ∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu
  let K : (ℝ × ℝ) → ℝ := fun p => Real.log (Z p)
  let means : (ℝ × ℝ) → (ℝ × ℝ) := fun p =>
    (∫ x : ℝ, x ∂nu p, ∫ x : ℝ, x ^ 2 ∂nu p)
  let I : ℕ → (ℝ × ℝ) → ℝ := fun j p =>
    ∫ x : ℝ, x ^ j * Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu
  have hI (j : ℕ) : ContDiffOn ℝ ∞ (I j) Omega := open_domain_weighted_moment_contDiffOn mu j
  have hI0 : I 0 = Z := by funext p; simp only [I, Z, pow_zero, one_mul]
  have hZpos (p : ℝ × ℝ) (hp : p ∈ Omega) : 0 < Z p :=
    integral_exp_pos (show Integrable
      (fun x : ℝ => Real.exp (p.1 * x + p.2 * x ^ 2)) mu from interior_subset hp)
  have hZ : ContDiffOn ℝ ∞ Z Omega := by rw [← hI0]; exact hI 0
  have hK : ContDiffOn ℝ ∞ K Omega := hZ.log fun p hp => (hZpos p hp).ne'
  have hN (j : ℕ) : ContDiffOn ℝ ∞ (fun p => I j p / Z p) Omega :=
    (hI j).div hZ fun p hp => (hZpos p hp).ne'
  have hR (j : ℕ) (p : ℝ × ℝ) : (∫ x : ℝ, x ^ j ∂nu p) = I j p / Z p := by
    rw [integral_tilted]
    change (∫ x : ℝ, (Real.exp (p.1 * x + p.2 * x ^ 2) / Z p) * x ^ j ∂mu) = _
    have hf : (fun x : ℝ => (Real.exp (p.1 * x + p.2 * x ^ 2) / Z p) * x ^ j) =
        (fun x => (x ^ j * Real.exp (p.1 * x + p.2 * x ^ 2)) / Z p) := by
      funext x
      ring
    rw [hf, integral_div]
  have hmeans : means = fun p => (I 1 p / Z p, I 2 p / Z p) := by
    funext p
    apply Prod.ext
    · simpa only [means, pow_one] using hR 1 p
    · exact hR 2 p
  have hm : ContDiffOn ℝ ∞ means Omega := by
    rw [hmeans]
    exact (hN 1).prodMk (hN 2)
  refine ⟨hZ, hK, hm, ?_⟩
  intro theta htheta
  have hd := (open_domain_quadratic_tilt_frechet_cumulants mu theta htheta).2.2.2.1
  exact ((hm theta htheta).contDiffAt (isOpen_interior.mem_nhds htheta)).hasStrictFDerivAt' hd (by simp)

end
end Shao.OQ3
