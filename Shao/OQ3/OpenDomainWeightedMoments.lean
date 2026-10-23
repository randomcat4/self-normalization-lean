import Shao.OQ3.QuadraticTiltCumulants
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace Shao.OQ3
open MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section

private theorem open_domain_weighted_integrable
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (k : ℕ) (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))) :
    Integrable (fun x : ℝ => x ^ k * Real.exp (theta.1 * x + theta.2 * x ^ 2)) mu := by
  have h := open_domain_quadratic_tilt_directional_cumulants mu theta htheta
  have hp := (h.2.2.2 (1, 0)).2.2.1 k
  have hi : Integrable (fun x : ℝ => x ^ k)
      (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)) := by simpa using hp
  have hw := (integrable_tilted_iff (show Integrable
    (fun x : ℝ => Real.exp (theta.1 * x + theta.2 * x ^ 2)) mu from interior_subset htheta) _).mp hi
  simpa only [smul_eq_mul, mul_comm] using hw

private theorem open_domain_abs_weighted_integrable
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (k : ℕ) (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))) :
    Integrable (fun x : ℝ => |x| ^ k * Real.exp (theta.1 * x + theta.2 * x ^ 2)) mu := by
  convert (open_domain_weighted_integrable mu k theta htheta).norm using 1
  funext x
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]

theorem open_domain_weighted_moment_hasFDerivAt
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (k : ℕ) (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))) :
    let I : ℕ → (ℝ × ℝ) → ℝ := fun n p =>
      ∫ x : ℝ, x ^ n * Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu
    let pr0 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
    let pr1 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
    Integrable (fun x : ℝ => x ^ k * Real.exp (theta.1 * x + theta.2 * x ^ 2)) mu ∧
      HasFDerivAt (I k) ((I (k + 1) theta) • pr0 + (I (k + 2) theta) • pr1) theta := by
  let I : ℕ → (ℝ × ℝ) → ℝ := fun n p =>
    ∫ x : ℝ, x ^ n * Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu
  let pr0 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let pr1 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  refine ⟨open_domain_weighted_integrable mu k theta htheta, ?_⟩
  have hline : Filter.Tendsto (fun s : ℝ => (theta.1, theta.2 + s)) (𝓝 0) (𝓝 theta) := by
    have hc : Continuous (fun s : ℝ => (theta.1, theta.2 + s)) := by fun_prop
    simpa [ContinuousAt] using hc.continuousAt (x := 0)
  have hnear := hline.eventually (isOpen_interior.mem_nhds htheta)
  obtain ⟨r, hr, hrad⟩ := Metric.eventually_nhds_iff.mp hnear
  let delta : ℝ := r / 2
  have hdelta : 0 < delta := div_pos hr (by norm_num)
  have hdr : dist delta (0 : ℝ) < r := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hdelta]
    dsimp [delta]
    linarith
  let thetaPlus : ℝ × ℝ := (theta.1, theta.2 + delta)
  have hplus : thetaPlus ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))) := hrad hdr
  let eps : ℝ := delta / 4
  have heps : 0 < eps := div_pos hdelta (by norm_num)
  let S : Set (ℝ × ℝ) := Set.Ioo (theta.1 - eps) (theta.1 + eps) ×ˢ
    Set.Ioo (theta.2 - eps) (theta.2 + eps)
  have hS : S ∈ 𝓝 theta := by
    apply (isOpen_Ioo.prod isOpen_Ioo).mem_nhds
    constructor <;> constructor <;> linarith
  have hexp (t : ℝ × ℝ) (ht : t ∈ S) (x : ℝ) :
      Real.exp (t.1 * x + t.2 * x ^ 2) ≤
        Real.exp (eps / 2) * Real.exp (thetaPlus.1 * x + thetaPlus.2 * x ^ 2) := by
    have ht0 : |t.1 - theta.1| ≤ eps := abs_le.mpr ⟨by linarith [ht.1.1], by linarith [ht.1.2]⟩
    have ht1 : t.2 - theta.2 ≤ eps := by linarith [ht.2.2]
    have hl : (t.1 - theta.1) * x ≤ eps * |x| := by
      calc
        _ ≤ |(t.1 - theta.1) * x| := le_abs_self _
        _ = |t.1 - theta.1| * |x| := abs_mul _ _
        _ ≤ eps * |x| := mul_le_mul_of_nonneg_right ht0 (abs_nonneg _)
    have hq : (t.2 - theta.2) * x ^ 2 ≤ eps * x ^ 2 :=
      mul_le_mul_of_nonneg_right ht1 (sq_nonneg _)
    have hx : 2 * |x| ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg (|x| - 1), sq_abs x]
    have hxeps : eps * |x| ≤ eps / 2 + eps / 2 * x ^ 2 := by
      have hh := mul_le_mul_of_nonneg_left hx heps.le
      nlinarith only [hh]
    have hed : 3 * eps / 2 ≤ delta := by dsimp [eps]; linarith
    have hexponent : t.1 * x + t.2 * x ^ 2 ≤ eps / 2 +
        (thetaPlus.1 * x + thetaPlus.2 * x ^ 2) := by
      dsimp [thetaPlus]
      nlinarith only [hl, hq, hxeps, mul_nonneg (sub_nonneg.mpr hed) (sq_nonneg x)]
    calc
      _ ≤ Real.exp (eps / 2 + (thetaPlus.1 * x + thetaPlus.2 * x ^ 2)) :=
        Real.exp_le_exp.mpr hexponent
      _ = _ := Real.exp_add _ _
  let F : (ℝ × ℝ) → ℝ → ℝ := fun t x =>
    x ^ k * Real.exp (t.1 * x + t.2 * x ^ 2)
  let F' : (ℝ × ℝ) → ℝ → ((ℝ × ℝ) →L[ℝ] ℝ) := fun t x =>
    (x ^ (k + 1) * Real.exp (t.1 * x + t.2 * x ^ 2)) • pr0 +
      (x ^ (k + 2) * Real.exp (t.1 * x + t.2 * x ^ 2)) • pr1
  let B : ℝ → ℝ := fun x => Real.exp (eps / 2) *
    ((|x| ^ (k + 1) * Real.exp (thetaPlus.1 * x + thetaPlus.2 * x ^ 2)) * ‖pr0‖ +
     (|x| ^ (k + 2) * Real.exp (thetaPlus.1 * x + thetaPlus.2 * x ^ 2)) * ‖pr1‖)
  have hB : Integrable B mu :=
    (((open_domain_abs_weighted_integrable mu (k + 1) thetaPlus hplus).mul_const ‖pr0‖).add
      ((open_domain_abs_weighted_integrable mu (k + 2) thetaPlus hplus).mul_const ‖pr1‖)).const_mul
        (Real.exp (eps / 2))
  have hbound : ∀ᵐ x ∂mu, ∀ t ∈ S, ‖F' t x‖ ≤ B x := by
    apply Filter.Eventually.of_forall
    intro x t ht
    have hc (j : ℕ) : ‖x ^ j * Real.exp (t.1 * x + t.2 * x ^ 2)‖ ≤
        Real.exp (eps / 2) * (|x| ^ j * Real.exp (thetaPlus.1 * x + thetaPlus.2 * x ^ 2)) := by
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
      calc
        _ ≤ |x| ^ j * (Real.exp (eps / 2) * Real.exp (thetaPlus.1 * x + thetaPlus.2 * x ^ 2)) :=
          mul_le_mul_of_nonneg_left (hexp t ht x) (pow_nonneg (abs_nonneg _) _)
        _ = _ := by ring
    calc
      ‖F' t x‖ ≤ ‖x ^ (k + 1) * Real.exp (t.1 * x + t.2 * x ^ 2)‖ * ‖pr0‖ +
          ‖x ^ (k + 2) * Real.exp (t.1 * x + t.2 * x ^ 2)‖ * ‖pr1‖ := by
        dsimp [F']
        simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le
          ((x ^ (k + 1) * Real.exp (t.1 * x + t.2 * x ^ 2)) • pr0)
          ((x ^ (k + 2) * Real.exp (t.1 * x + t.2 * x ^ 2)) • pr1)
      _ ≤ (Real.exp (eps / 2) * (|x| ^ (k + 1) * Real.exp (thetaPlus.1 * x + thetaPlus.2 * x ^ 2))) * ‖pr0‖ +
          (Real.exp (eps / 2) * (|x| ^ (k + 2) * Real.exp (thetaPlus.1 * x + thetaPlus.2 * x ^ 2))) * ‖pr1‖ :=
        add_le_add (mul_le_mul_of_nonneg_right (hc (k + 1)) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hc (k + 2)) (norm_nonneg _))
      _ = B x := by dsimp [B]; ring
  have hdiff (x : ℝ) (t : ℝ × ℝ) : HasFDerivAt (fun t => F t x) (F' t x) t := by
    have hlin : HasFDerivAt (fun t : ℝ × ℝ => t.1 * x + t.2 * x ^ 2)
        (x • pr0 + x ^ 2 • pr1) t := by
      convert (pr0.hasFDerivAt.mul_const x).add (pr1.hasFDerivAt.mul_const (x ^ 2)) using 1 <;>
        ext v <;> simp [pr0, pr1, mul_comm]
    have hh := hlin.exp.const_mul (x ^ k)
    have hs : x ^ k • (Real.exp (t.1 * x + t.2 * x ^ 2) • (x • pr0 + x ^ 2 • pr1)) =
        F' t x := by
      apply ContinuousLinearMap.ext
      intro v
      change x ^ k * (Real.exp (t.1 * x + t.2 * x ^ 2) * (x * v.1 + x ^ 2 * v.2)) =
        (x ^ (k + 1) * Real.exp (t.1 * x + t.2 * x ^ 2)) * v.1 +
          (x ^ (k + 2) * Real.exp (t.1 * x + t.2 * x ^ 2)) * v.2
      simp only [pow_add, pow_one]
      ring
    rw [hs] at hh
    exact hh
  have hmeas (t : ℝ × ℝ) : AEStronglyMeasurable (F t) mu := by
    have hc : Continuous (F t) := by dsimp [F]; fun_prop
    exact hc.aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (F' theta) mu := by
    have hc : Continuous (F' theta) := by dsimp [F']; fun_prop
    exact hc.aestronglyMeasurable
  have hd := hasFDerivAt_integral_of_dominated_of_fderiv_le hS
    (Filter.Eventually.of_forall hmeas) (open_domain_weighted_integrable mu k theta htheta)
    hmeas' hbound hB (Filter.Eventually.of_forall fun x t _ => hdiff x t)
  have hi0 := (open_domain_weighted_integrable mu (k + 1) theta htheta).smul_const pr0
  have hi1 := (open_domain_weighted_integrable mu (k + 2) theta htheta).smul_const pr1
  have heq : (∫ x, F' theta x ∂mu) = I (k + 1) theta • pr0 + I (k + 2) theta • pr1 := by
    dsimp [F', I]
    rw [integral_add hi0 hi1, integral_smul_const, integral_smul_const]
  rw [heq] at hd
  exact hd

end
end Shao.OQ3
