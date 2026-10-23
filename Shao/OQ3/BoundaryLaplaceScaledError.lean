import Shao.OQ3.BoundaryLaplaceExponential

namespace Shao.OQ3
open scoped Topology
noncomputable section

theorem boundary_taylor_scaled_error
    (F : (ℝ × ℝ) → ℝ) (lambda Lambda1 rho CF : ℝ) (hCF : 0 ≤ CF)
    (hbound : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      |F (r, z) - F (0, 0) - lambda * z - Lambda1 / 2 * r ^ 2| ≤
        CF * (|r| ^ 3 + |r| * z + z ^ 2))
    (t u v : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (hv : 0 ≤ v)
    (hru : |t * u| ≤ rho) (hzv : t ^ 2 * v ≤ rho) :
    |(F (t * u, t ^ 2 * v) - F (0, 0)) / t ^ 2 -
      (lambda * v + Lambda1 / 2 * u ^ 2)| ≤
      CF * t * (|u| ^ 3 + |u| * v + v ^ 2)
 := by
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  have hscale : (F (t * u, t ^ 2 * v) - F (0, 0)) / t ^ 2 -
      (lambda * v + Lambda1 / 2 * u ^ 2) =
      (F (t * u, t ^ 2 * v) - F (0, 0) - lambda * (t ^ 2 * v) -
        Lambda1 / 2 * (t * u) ^ 2) / t ^ 2 := by
    field_simp [ht.ne']
    ring
  rw [hscale, abs_div, abs_of_pos ht2]
  apply (div_le_iff₀ ht2).mpr
  have hb := hbound (t * u) (t ^ 2 * v) hru (mul_nonneg ht2.le hv) hzv
  have htv : t * v ^ 2 ≤ v ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right ht1 (sq_nonneg v)]
  calc
    _ ≤ CF * ((t * |u|) ^ 3 + (t * |u|) * (t ^ 2 * v) + (t ^ 2 * v) ^ 2) := by
      simpa only [abs_mul, abs_of_pos ht] using hb
    _ = (CF * t ^ 3) * (|u| ^ 3 + |u| * v + t * v ^ 2) := by ring
    _ ≤ (CF * t ^ 3) * (|u| ^ 3 + |u| * v + v ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hCF (pow_nonneg ht.le 3))
    _ = CF * t * (|u| ^ 3 + |u| * v + v ^ 2) * t ^ 2 := by ring

theorem boundary_weighted_scaled_kernel_error
    (F A : (ℝ × ℝ) → ℝ) (lambda Lambda1 rho CF CA c d : ℝ)
    (hCF : 0 ≤ CF) (hCA : 0 ≤ CA) (hd : 0 < d)
    (hdc : d ≤ c) (hdl : d ≤ lambda) (hdq : d ≤ Lambda1 / 2)
    (hbound : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      |F (r, z) - F (0, 0) - lambda * z - Lambda1 / 2 * r ^ 2| ≤
        CF * (|r| ^ 3 + |r| * z + z ^ 2))
    (hmargin : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      c * (z + r ^ 2) ≤ F (r, z) - F (0, 0))
    (hamplitude : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      |A (r, z) - A (0, 0)| ≤ CA * (|r| + z))
    (t u v : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (hv : 0 ≤ v)
    (hru : |t * u| ≤ rho) (hzv : t ^ 2 * v ≤ rho) :
    |A (t * u, t ^ 2 * v) *
        Real.exp (-((F (t * u, t ^ 2 * v) - F (0, 0)) / t ^ 2)) -
      A (0, 0) * Real.exp (-(lambda * v + Lambda1 / 2 * u ^ 2))| ≤
      t * (CA * (|u| + v) + |A (0, 0)| * CF * (|u| ^ 3 + |u| * v + v ^ 2)) *
        Real.exp (-d * (v + u ^ 2))
 := by
  let a : ℝ := (F (t * u, t ^ 2 * v) - F (0, 0)) / t ^ 2
  let b : ℝ := lambda * v + Lambda1 / 2 * u ^ 2
  let D : ℝ := d * (v + u ^ 2)
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  have hz : 0 ≤ t ^ 2 * v := mul_nonneg ht2.le hv
  have hlow : c * (v + u ^ 2) ≤ a := by
    apply (le_div_iff₀ ht2).mpr
    calc
      _ = c * (t ^ 2 * v + (t * u) ^ 2) := by ring
      _ ≤ F (t * u, t ^ 2 * v) - F (0, 0) := hmargin _ _ hru hz hzv
  have hDa : D ≤ a :=
    (mul_le_mul_of_nonneg_right hdc (add_nonneg hv (sq_nonneg u))).trans hlow
  have hDb : D ≤ b := by
    dsimp [D, b]
    nlinarith [mul_le_mul_of_nonneg_right hdl hv,
      mul_le_mul_of_nonneg_right hdq (sq_nonneg u)]
  have hE : |a - b| ≤ CF * t * (|u| ^ 3 + |u| * v + v ^ 2) :=
    boundary_taylor_scaled_error F lambda Lambda1 rho CF hCF hbound t u v ht ht1 hv hru hzv
  have htv : t * v ≤ v := by nlinarith [mul_le_mul_of_nonneg_right ht1 hv]
  have hA : |A (t * u, t ^ 2 * v) - A (0, 0)| ≤ CA * t * (|u| + v) := by
    calc
      _ ≤ CA * (|t * u| + t ^ 2 * v) := hamplitude _ _ hru hz hzv
      _ = (CA * t) * (|u| + t * v) := by rw [abs_mul, abs_of_pos ht]; ring
      _ ≤ (CA * t) * (|u| + v) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hCA ht.le)
  have hh := abs_weighted_exp_neg_sub_le a b (A (t * u, t ^ 2 * v)) (A (0, 0)) D
    (CF * t * (|u| ^ 3 + |u| * v + v ^ 2)) (CA * t * (|u| + v)) hDa hDb hE hA
  change |A (t * u, t ^ 2 * v) * Real.exp (-a) - A (0, 0) * Real.exp (-b)| ≤ _
  calc
    _ ≤ (CA * t * (|u| + v) + |A (0, 0)| * (CF * t * (|u| ^ 3 + |u| * v + v ^ 2))) *
        Real.exp (-D) := hh
    _ = t * (CA * (|u| + v) + |A (0, 0)| * CF * (|u| ^ 3 + |u| * v + v ^ 2)) *
        Real.exp (-d * (v + u ^ 2)) := by dsimp [D]; ring

end
end Shao.OQ3
