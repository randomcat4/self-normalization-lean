import Shao.OQ3.BoundaryLaplaceScaledError

namespace Shao.OQ3
open scoped Topology
noncomputable section

theorem boundary_weighted_scaled_cutoff_error
    (F A : (ℝ × ℝ) → ℝ) (lambda Lambda1 rho CF CA c d : ℝ)
    (hCF : 0 ≤ CF) (hCA : 0 ≤ CA) (hrho : 0 < rho) (hd : 0 < d)
    (hdc : d ≤ c) (hdl : d ≤ lambda) (hdq : d ≤ Lambda1 / 2)
    (hbound : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      |F (r, z) - F (0, 0) - lambda * z - Lambda1 / 2 * r ^ 2| ≤
        CF * (|r| ^ 3 + |r| * z + z ^ 2))
    (hmargin : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      c * (z + r ^ 2) ≤ F (r, z) - F (0, 0))
    (hamplitude : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      |A (r, z) - A (0, 0)| ≤ CA * (|r| + z))
    (t u v : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (hv : 0 ≤ v) :
    |(if |t * u| ≤ rho ∧ t ^ 2 * v ≤ rho then
        A (t * u, t ^ 2 * v) *
          Real.exp (-((F (t * u, t ^ 2 * v) - F (0, 0)) / t ^ 2)) else 0) -
      A (0, 0) * Real.exp (-(lambda * v + Lambda1 / 2 * u ^ 2))| ≤
      t * (CA * (|u| + v) + |A (0, 0)| * CF * (|u| ^ 3 + |u| * v + v ^ 2) +
        |A (0, 0)| / rho * (|u| + v)) *
        Real.exp (-d * (v + u ^ 2))

 := by
  let B : ℝ := CA * (|u| + v) + |A (0, 0)| * CF * (|u| ^ 3 + |u| * v + v ^ 2)
  let T : ℝ := |A (0, 0)| / rho * (|u| + v)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  change |(if |t * u| ≤ rho ∧ t ^ 2 * v ≤ rho then
      A (t * u, t ^ 2 * v) * Real.exp (-((F (t * u, t ^ 2 * v) - F (0, 0)) / t ^ 2)) else 0) -
    A (0, 0) * Real.exp (-(lambda * v + Lambda1 / 2 * u ^ 2))| ≤
      t * (B + T) * Real.exp (-d * (v + u ^ 2))
  by_cases hrect : |t * u| ≤ rho ∧ t ^ 2 * v ≤ rho
  · rw [if_pos hrect]
    have hh : |A (t * u, t ^ 2 * v) * Real.exp (-((F (t * u, t ^ 2 * v) - F (0, 0)) / t ^ 2)) -
        A (0, 0) * Real.exp (-(lambda * v + Lambda1 / 2 * u ^ 2))| ≤
        t * B * Real.exp (-d * (v + u ^ 2)) :=
      boundary_weighted_scaled_kernel_error F A lambda Lambda1 rho CF CA c d hCF hCA hd
        hdc hdl hdq hbound hmargin hamplitude t u v ht ht1 hv hrect.1 hrect.2
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hT) ht.le) (Real.exp_pos _).le)
  · rw [if_neg hrect, zero_sub, abs_neg, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hout : rho ≤ t * (|u| + v) := by
      by_cases hu : |t * u| ≤ rho
      · have hb : rho < t ^ 2 * v := lt_of_not_ge (fun hz => hrect ⟨hu, hz⟩)
        have htV : t ^ 2 * v ≤ t * v := by
          nlinarith [mul_le_mul_of_nonneg_right ht1 (mul_nonneg ht.le hv)]
        nlinarith [mul_nonneg ht.le (abs_nonneg u)]
      · have hb : rho < |t * u| := lt_of_not_ge hu
        rw [abs_mul, abs_of_pos ht] at hb
        nlinarith [mul_nonneg ht.le hv]
    have hratio : (1 : ℝ) ≤ t * (|u| + v) / rho :=
      (le_div_iff₀ hrho).mpr (by simpa only [one_mul] using hout)
    have hscale : |A (0, 0)| ≤ t * T := by
      calc
        _ ≤ |A (0, 0)| * (t * (|u| + v) / rho) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio (abs_nonneg (A (0, 0)))
        _ = t * T := by dsimp [T]; ring
    have hlead : d * (v + u ^ 2) ≤ lambda * v + Lambda1 / 2 * u ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hdl hv,
        mul_le_mul_of_nonneg_right hdq (sq_nonneg u)]
    have hexp : Real.exp (-(lambda * v + Lambda1 / 2 * u ^ 2)) ≤
        Real.exp (-d * (v + u ^ 2)) := Real.exp_le_exp.mpr (by linarith)
    calc
      _ ≤ (t * T) * Real.exp (-d * (v + u ^ 2)) :=
        mul_le_mul hscale hexp (Real.exp_pos _).le (mul_nonneg ht.le hT)
      _ ≤ t * (B + T) * Real.exp (-d * (v + u ^ 2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left hB) ht.le) (Real.exp_pos _).le

end
end Shao.OQ3
