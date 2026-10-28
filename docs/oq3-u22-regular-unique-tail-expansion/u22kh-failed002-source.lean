import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

namespace Shao.OQ3
open scoped Topology
noncomputable section

theorem joint_energy_positive_curvature_neighborhood
    (F : (ℝ × ℝ) → ℝ) (q0 : ℝ)
    (hsmooth : ContDiffAt ℝ (3 : WithTop ENat) F (0, q0))
    (hcurvature : 0 < deriv (deriv (fun q : ℝ => F (0, q))) q0) :
    ∃ eta rho : ℝ, 0 < eta ∧ 0 < rho ∧ ∀ level q : ℝ,
      |level| ≤ eta → |q - q0| ≤ rho →
        ContDiffAt ℝ (2 : WithTop ENat) (fun energy : ℝ => F (level, energy)) q ∧
          0 < deriv (deriv (fun energy : ℝ => F (level, energy))) q := by
  have hpartial (n : ℕ) (G : (ℝ × ℝ) → ℝ) (p : ℝ × ℝ)
      (hG : ContDiffAt ℝ ((n : WithTop ENat) + 1) G p) :
      ContDiffAt ℝ (n : WithTop ENat)
        (fun v : ℝ × ℝ => deriv (fun q : ℝ => G (v.1, q)) v.2) p := by
    have huncurry : ContDiffAt ℝ ((n : WithTop ENat) + 1)
        (fun v : (ℝ × ℝ) × ℝ => G (v.1.1, v.2)) (p, p.2) :=
      hG.comp (p, p.2) (by fun_prop)
    have hpart : ContDiffAt ℝ (n : WithTop ENat)
        (fun v : ℝ × ℝ => fderiv ℝ (fun q : ℝ => G (v.1, q)) v.2) p :=
      ContDiffAt.fderiv_succ huncurry contDiffAt_snd
    have heval := hpart.clm_apply (contDiffAt_const :
      ContDiffAt ℝ (n : WithTop ENat) (fun _ : ℝ × ℝ => (1 : ℝ)) p)
    simpa only [deriv] using heval
  let D1 : (ℝ × ℝ) → ℝ := fun p => deriv (fun q : ℝ => F (p.1, q)) p.2
  let D2 : (ℝ × ℝ) → ℝ := fun p => deriv (deriv (fun q : ℝ => F (p.1, q))) p.2
  have hD1 : ContDiffAt ℝ (2 : WithTop ENat) D1 (0, q0) :=
    hpartial 2 F (0, q0) (by convert hsmooth using 1 <;> norm_num)
  have hD2 : ContDiffAt ℝ (1 : WithTop ENat) D2 (0, q0) := by
    simpa only [D1, D2] using hpartial 1 D1 (0, q0) (by convert hD1 using 1 <;> norm_num)
  have hpositive : ∀ᶠ p in 𝓝 ((0 : ℝ), q0), 0 < D2 p :=
    hD2.continuousAt (lt_mem_nhds hcurvature)
  have hnear : ∀ᶠ p in 𝓝 ((0 : ℝ), q0),
      ContDiffAt ℝ (3 : WithTop ENat) F p ∧ 0 < D2 p :=
    (hsmooth.eventually (by norm_num)).and hpositive
  obtain ⟨d, hd, hpoint⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨d / 2, d / 2, half_pos hd, half_pos hd, ?_⟩
  intro level q hlevel hq
  have hdist : dist (level, q) ((0 : ℝ), q0) < d := by
    rw [Prod.dist_eq, max_lt_iff]
    constructor
    · simpa only [Real.dist_eq, sub_zero] using hlevel.trans_lt (half_lt_self hd)
    · simpa only [Real.dist_eq] using hq.trans_lt (half_lt_self hd)
  have hp := hpoint hdist
  refine ⟨?_, hp.2⟩
  have hF2 : ContDiffAt ℝ (2 : WithTop ENat) F (level, q) := hp.1.of_le (by norm_num)
  exact hF2.comp q (show ContDiffAt ℝ (2 : WithTop ENat)
    (fun energy : ℝ => (level, energy)) q from by fun_prop)

end
end Shao.OQ3
