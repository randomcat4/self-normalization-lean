import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.MetricSpace.ProperSpace

namespace Shao.OQ3
open MeasureTheory
open scoped Topology ContDiff
noncomputable section

theorem exists_uniform_cubic_taylor_bound_at_zero
    (g : ℝ → ℝ) (hg : ContDiffAt ℝ 3 g 0) :
    ∃ rho C : ℝ, 0 < rho ∧ 0 < C ∧ ∀ r : ℝ, |r| ≤ rho →
      |g r - g 0 - (deriv g 0) * r - (deriv (deriv g) 0) / 2 * r ^ 2| ≤
        C * |r| ^ 3 := by
  obtain ⟨u, hu, hgu⟩ := hg.contDiffOn (m := (3 : WithTop ENat)) le_rfl (by norm_num)
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp hu
  let s : Set ℝ := Set.Ioo (-a) a
  have h0 : (0 : ℝ) ∈ s := by constructor <;> linarith
  have hs : s ⊆ u := by
    intro r hr
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact hr
  have hgs : ContDiffOn ℝ 3 g s := hgu.mono hs
  have hsmall : (fun r => g r - taylorWithinEval g 3 s 0 r) =o[𝓝 (0 : ℝ)]
      (fun r => r ^ 3) := by
    have hh := taylor_isLittleO (convex_Ioo (-a) a) h0 hgs
    rw [nhdsWithin_eq_nhds.mpr (isOpen_Ioo.mem_nhds h0)] at hh
    simpa only [sub_zero] using hh
  have hiter (k : ℕ) : iteratedDerivWithin k g s 0 = iteratedDeriv k g 0 :=
    iteratedDerivWithin_of_isOpen isOpen_Ioo h0
  let A : ℝ := iteratedDeriv 3 g 0 / 6
  have hpoly (r : ℝ) : taylorWithinEval g 3 s 0 r =
      g 0 + deriv g 0 * r + deriv (deriv g) 0 / 2 * r ^ 2 + A * r ^ 3 := by
    rw [taylorWithinEval_succ g 2 s 0 r, taylorWithinEval_succ g 1 s 0 r,
      taylorWithinEval_succ g 0 s 0 r, taylor_within_zero_eval]
    rw [hiter 1, hiter 2, hiter 3]
    norm_num [Nat.factorial, iteratedDeriv_succ, iteratedDeriv_zero, smul_eq_mul, A]
    ring
  have hb : ∀ᶠ r in 𝓝 (0 : ℝ),
      |g r - taylorWithinEval g 3 s 0 r| ≤ |r| ^ 3 := by
    simpa only [Real.norm_eq_abs, one_mul, abs_pow] using hsmall.isBigOWith.bound
  obtain ⟨delta, hdelta, hbound⟩ := Metric.eventually_nhds_iff.mp hb
  let rho : ℝ := delta / 2
  refine ⟨rho, 1 + |A|, by dsimp [rho]; linarith, by positivity, ?_⟩
  intro r hr
  have hnear : dist r 0 < delta := by
    rw [Real.dist_eq, sub_zero]
    dsimp [rho] at hr
    linarith
  have hrem := hbound hnear
  rw [hpoly] at hrem
  have heq : g r - g 0 - deriv g 0 * r - deriv (deriv g) 0 / 2 * r ^ 2 =
      (g r - (g 0 + deriv g 0 * r + deriv (deriv g) 0 / 2 * r ^ 2 + A * r ^ 3)) + A * r ^ 3 := by
    ring
  rw [heq]
  calc
    _ ≤ |g r - (g 0 + deriv g 0 * r + deriv (deriv g) 0 / 2 * r ^ 2 + A * r ^ 3)| + |A * r ^ 3| :=
      abs_add_le _ _
    _ ≤ |r| ^ 3 + |A| * |r| ^ 3 := by
      rw [abs_mul, abs_pow]
      exact add_le_add hrem le_rfl
    _ = (1 + |A|) * |r| ^ 3 := by ring

end
end Shao.OQ3
