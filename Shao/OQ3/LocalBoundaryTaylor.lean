import Shao.OQ3.LocalCubicTaylor
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue

namespace Shao.OQ3
open scoped Topology ContDiff
noncomputable section

theorem exists_uniform_normal_increment_bound_at_zero
    (F : (ℝ × ℝ) → ℝ) (hF : ContDiffAt ℝ 2 F (0, 0)) :
    ∃ rho C : ℝ, 0 < rho ∧ 0 < C ∧ ∀ r z : ℝ,
      |r| ≤ rho → 0 ≤ z → z ≤ rho →
      |F (r, z) - F (r, 0) - (fderiv ℝ F (0, 0) (0, 1)) * z| ≤
        C * (|r| * z + z ^ 2) := by
  let H : (ℝ × ℝ) → ℝ := fun w => fderiv ℝ F w (0, 1)
  have hH : DifferentiableAt ℝ H (0, 0) :=
    ((hF.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt_one
  obtain ⟨K, hK, hbound⟩ := hH.isBigO_sub.exists_pos
  have hdiff : ∀ᶠ w in 𝓝 (0, 0), DifferentiableAt ℝ F w :=
    (hF.eventually (by norm_num)).mono fun _ hw => hw.differentiableAt (by norm_num)
  have hnear : ∀ᶠ w in 𝓝 (0, 0),
      |H w - H (0, 0)| ≤ K * ‖w‖ ∧ DifferentiableAt ℝ F w := by
    filter_upwards [hbound.bound, hdiff] with w hw hd
    exact ⟨by simpa only [show (0, 0) = (0 : ℝ × ℝ) from rfl,
      Real.norm_eq_abs, sub_zero] using hw, hd⟩
  obtain ⟨delta, hdelta, hpoint⟩ := Metric.eventually_nhds_iff.mp hnear
  let rho : ℝ := delta / 2
  have hrho : 0 < rho := by dsimp [rho]; linarith
  have hinside (r t : ℝ) (hr : |r| ≤ rho) (ht0 : 0 ≤ t) (ht : t ≤ rho) :
      dist (r, t) (0, 0) < delta := by
    rw [show (0, 0) = (0 : ℝ × ℝ) from rfl, dist_zero_right, Prod.norm_def,
      Real.norm_eq_abs, Real.norm_eq_abs, max_lt_iff]
    dsimp [rho] at hr ht
    constructor
    · linarith
    · rw [abs_of_nonneg ht0]; linarith
  refine ⟨rho, K, hrho, hK, ?_⟩
  intro r z hr hz hzr
  let g : ℝ → ℝ := fun t => F (r, t) - H (0, 0) * t
  have hg (t : ℝ) (ht : t ∈ Set.Icc 0 z) :
      HasDerivAt g (H (r, t) - H (0, 0)) t := by
    have hp : HasDerivAt (fun s : ℝ => (r, s)) (0, 1) t :=
      (hasDerivAt_const t r).prodMk (hasDerivAt_id t)
    have hf := (hpoint (hinside r t hr ht.1 (ht.2.trans hzr))).2.hasFDerivAt.comp_hasDerivAt t hp
    convert! hf.sub ((hasDerivAt_id t).const_mul (H (0, 0))) using 1
    simp [H]
  have hb (t : ℝ) (ht : t ∈ Set.Icc 0 z) :
      ‖H (r, t) - H (0, 0)‖ ≤ K * (|r| + z) := by
    have hn : ‖(r, t)‖ ≤ |r| + z := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
      exact max_le (by linarith) (by rw [abs_of_nonneg ht.1]; linarith [ht.2, abs_nonneg r])
    rw [Real.norm_eq_abs]
    exact ((hpoint (hinside r t hr ht.1 (ht.2.trans hzr))).1).trans
      (mul_le_mul_of_nonneg_left hn hK.le)
  have hm := (convex_Icc (0 : ℝ) z).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hg t ht).hasDerivWithinAt) hb (by exact ⟨le_rfl, hz⟩) (by exact ⟨hz, le_rfl⟩)
  have heq : g z - g 0 = F (r, z) - F (r, 0) - H (0, 0) * z := by
    dsimp [g]; ring
  rw [heq, Real.norm_eq_abs, sub_zero, Real.norm_eq_abs, abs_of_nonneg hz] at hm
  calc
    _ ≤ K * (|r| + z) * z := hm
    _ = K * (|r| * z + z ^ 2) := by ring

theorem exists_uniform_boundary_taylor_bound_at_zero
    (F : (ℝ × ℝ) → ℝ) (hF : ContDiffAt ℝ 3 F (0, 0)) :
    ∃ rho C : ℝ, 0 < rho ∧ 0 < C ∧ ∀ r z : ℝ,
      |r| ≤ rho → 0 ≤ z → z ≤ rho →
      |F (r, z) - F (0, 0) - (deriv (fun t : ℝ => F (t, 0)) 0) * r -
        (fderiv ℝ F (0, 0) (0, 1)) * z -
        (deriv (deriv (fun t : ℝ => F (t, 0))) 0) / 2 * r ^ 2| ≤
        C * (|r| ^ 3 + |r| * z + z ^ 2) := by
  let g : ℝ → ℝ := fun t => F (t, 0)
  have hg : ContDiffAt ℝ 3 g 0 := by
    have hp : ContDiffAt ℝ 3 (fun t : ℝ => (t, (0 : ℝ))) 0 :=
      contDiffAt_id.prodMk contDiffAt_const
    exact hF.comp (f := fun t : ℝ => (t, (0 : ℝ))) (0 : ℝ) hp
  obtain ⟨rhoT, CT, hrt, hct, hT⟩ := exists_uniform_cubic_taylor_bound_at_zero g hg
  obtain ⟨rhoN, CN, hrn, hcn, hN⟩ :=
    exists_uniform_normal_increment_bound_at_zero F (hF.of_le (by norm_num))
  refine ⟨min rhoT rhoN, CT + CN, lt_min hrt hrn, add_pos hct hcn, ?_⟩
  intro r z hr hz hzr
  have ht := hT r (hr.trans (min_le_left _ _))
  have hn := hN r z (hr.trans (min_le_right _ _)) hz (hzr.trans (min_le_right _ _))
  have heq : F (r, z) - F (0, 0) - deriv g 0 * r -
      (fderiv ℝ F (0, 0) (0, 1)) * z - deriv (deriv g) 0 / 2 * r ^ 2 =
      (F (r, z) - F (r, 0) - (fderiv ℝ F (0, 0) (0, 1)) * z) +
      (g r - g 0 - deriv g 0 * r - deriv (deriv g) 0 / 2 * r ^ 2) := by
    dsimp [g]; ring
  change |F (r, z) - F (0, 0) - deriv g 0 * r -
    (fderiv ℝ F (0, 0) (0, 1)) * z - deriv (deriv g) 0 / 2 * r ^ 2| ≤ _
  rw [heq]
  calc
    _ ≤ |F (r, z) - F (r, 0) - (fderiv ℝ F (0, 0) (0, 1)) * z| +
        |g r - g 0 - deriv g 0 * r - deriv (deriv g) 0 / 2 * r ^ 2| := abs_add_le _ _
    _ ≤ CN * (|r| * z + z ^ 2) + CT * |r| ^ 3 := add_le_add hn ht
    _ ≤ (CT + CN) * (|r| ^ 3 + |r| * z + z ^ 2) := by
      nlinarith [mul_nonneg hct.le (add_nonneg (mul_nonneg (abs_nonneg r) hz) (sq_nonneg z)),
        mul_nonneg hcn.le (pow_nonneg (abs_nonneg r) 3)]

end
end Shao.OQ3
