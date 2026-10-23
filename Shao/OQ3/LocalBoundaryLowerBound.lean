import Shao.OQ3.LocalBoundaryTaylor

namespace Shao.OQ3
open scoped Topology ContDiff
noncomputable section

theorem exists_positive_boundary_lower_bound_of_taylor
    (F : (ℝ × ℝ) → ℝ) (lambda Lambda1 rho C : ℝ)
    (hlambda : 0 < lambda) (hLambda1 : 0 < Lambda1)
    (hrho : 0 < rho) (hC : 0 < C)
    (hbound : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      |F (r, z) - F (0, 0) - lambda * z - Lambda1 / 2 * r ^ 2| ≤
        C * (|r| ^ 3 + |r| * z + z ^ 2)) :
    ∃ delta c : ℝ, 0 < delta ∧ delta ≤ rho ∧ 0 < c ∧ ∀ r z : ℝ,
      |r| ≤ delta → 0 ≤ z → z ≤ delta →
      c * (z + r ^ 2) ≤ F (r, z) - F (0, 0) := by
  let delta : ℝ := min rho (min (lambda / (4 * C)) (Lambda1 / (4 * C)))
  let c : ℝ := min (lambda / 2) (Lambda1 / 4)
  have hden : 0 < 4 * C := by positivity
  have hdelta : 0 < delta := lt_min hrho (lt_min (div_pos hlambda hden) (div_pos hLambda1 hden))
  have hdeltaR : delta ≤ rho := min_le_left _ _
  have hdeltaL : delta ≤ lambda / (4 * C) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hdeltaK : delta ≤ Lambda1 / (4 * C) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hCL : 4 * C * delta ≤ lambda := by
    have hh := (le_div_iff₀ hden).mp hdeltaL
    nlinarith
  have hCK : 4 * C * delta ≤ Lambda1 := by
    have hh := (le_div_iff₀ hden).mp hdeltaK
    nlinarith
  refine ⟨delta, c, hdelta, hdeltaR, lt_min (by positivity) (by positivity), ?_⟩
  intro r z hr hz hzd
  have hcube : |r| ^ 3 ≤ delta * r ^ 2 := by
    calc
      _ = |r| * r ^ 2 := by rw [pow_succ, sq_abs]; ring
      _ ≤ delta * r ^ 2 := mul_le_mul_of_nonneg_right hr (sq_nonneg r)
  have hmix : |r| * z ≤ delta * z := mul_le_mul_of_nonneg_right hr hz
  have hzsq : z ^ 2 ≤ delta * z := by nlinarith
  have herr : C * (|r| ^ 3 + |r| * z + z ^ 2) ≤
      C * delta * r ^ 2 + 2 * C * delta * z := by
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add (add_le_add hcube hmix) hzsq) hC.le]
  have hlin : 2 * C * delta * z ≤ (lambda / 2) * z := by
    nlinarith [mul_le_mul_of_nonneg_right hCL hz]
  have hquad : C * delta * r ^ 2 ≤ (Lambda1 / 4) * r ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hCK (sq_nonneg r)]
  have hcZ : c * z ≤ (lambda / 2) * z :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) hz
  have hcR : c * r ^ 2 ≤ (Lambda1 / 4) * r ^ 2 :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg r)
  have hrem := (abs_le.mp (hbound r z (hr.trans hdeltaR) hz (hzd.trans hdeltaR))).1
  nlinarith

theorem exists_positive_boundary_lower_bound_of_contDiffAt
    (F : (ℝ × ℝ) → ℝ) (hF : ContDiffAt ℝ 3 F (0, 0))
    (htangent : deriv (fun t : ℝ => F (t, 0)) 0 = 0)
    (hnormal : 0 < fderiv ℝ F (0, 0) (0, 1))
    (hcurvature : 0 < deriv (deriv (fun t : ℝ => F (t, 0))) 0) :
    ∃ delta c : ℝ, 0 < delta ∧ 0 < c ∧ ∀ r z : ℝ,
      |r| ≤ delta → 0 ≤ z → z ≤ delta →
      c * (z + r ^ 2) ≤ F (r, z) - F (0, 0) := by
  obtain ⟨rho, C, hrho, hC, hbound⟩ := exists_uniform_boundary_taylor_bound_at_zero F hF
  have hb : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      |F (r, z) - F (0, 0) - (fderiv ℝ F (0, 0) (0, 1)) * z -
        (deriv (deriv (fun t : ℝ => F (t, 0))) 0) / 2 * r ^ 2| ≤
        C * (|r| ^ 3 + |r| * z + z ^ 2) := by
    intro r z hr hz hzr
    simpa only [htangent, zero_mul, sub_zero] using hbound r z hr hz hzr
  obtain ⟨delta, c, hd, _, hc, hb⟩ := exists_positive_boundary_lower_bound_of_taylor F
    (fderiv ℝ F (0, 0) (0, 1)) (deriv (deriv (fun t : ℝ => F (t, 0))) 0)
    rho C hnormal hcurvature hrho hC hb
  exact ⟨delta, c, hd, hc, hb⟩

end
end Shao.OQ3
