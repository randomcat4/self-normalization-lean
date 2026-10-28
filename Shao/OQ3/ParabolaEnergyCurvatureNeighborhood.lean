import Shao.OQ3.JointEnergyCurvatureNeighborhood
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace Shao.OQ3
open scoped Topology
noncomputable section

theorem parabola_energy_positive_curvature_neighborhood
    (J : (ℝ × ℝ) → ℝ) (q0 : ℝ) (hq0 : 0 < q0)
    (hsmooth : ContDiffAt ℝ (3 : WithTop ENat) J (0, q0))
    (hcurvature : 0 <
      (fderiv ℝ (fun z => fderiv ℝ J z) (0, q0) (0, 1)) (0, 1)) :
    ∃ eta rho : ℝ, 0 < eta ∧ 0 < rho ∧ rho < q0 ∧ ∀ level q : ℝ,
      |level| ≤ eta → |q - q0| ≤ rho →
        ContDiffAt ℝ (2 : WithTop ENat)
          (fun energy : ℝ => J (level * Real.sqrt energy, energy)) q ∧
          0 < deriv (deriv
            (fun energy : ℝ => J (level * Real.sqrt energy, energy))) q := by
  have hline (q : ℝ) : HasDerivAt (fun t : ℝ => ((0 : ℝ), t)) (0, 1) q :=
    (hasDerivAt_const q (0 : ℝ)).prodMk (hasDerivAt_id q)
  have hlineCont : ContinuousAt (fun t : ℝ => ((0 : ℝ), t)) q0 := by fun_prop
  have hJ1 : ContDiffAt ℝ (1 : WithTop ENat) J (0, q0) :=
    hsmooth.of_le (by norm_num)
  have hnear : ∀ᶠ q in 𝓝 q0, DifferentiableAt ℝ J (0, q) :=
    (hlineCont.eventually (hJ1.eventually (by norm_num))).mono
      (fun _ h => h.differentiableAt (by norm_num))
  have heq : deriv (fun q : ℝ => J (0, q)) =ᶠ[𝓝 q0]
      (fun q : ℝ => fderiv ℝ J (0, q) (0, 1)) := by
    filter_upwards [hnear] with q hq
    exact (hq.hasFDerivAt.comp_hasDerivAt q (hline q)).deriv
  have hgrad : DifferentiableAt ℝ (fun z => fderiv ℝ J z) (0, q0) :=
    (hsmooth.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hgradLine := hgrad.hasFDerivAt.comp_hasDerivAt q0 (hline q0)
  have hscalar : HasDerivAt
      (fun q : ℝ => fderiv ℝ J (0, q) (0, 1))
      ((fderiv ℝ (fun z => fderiv ℝ J z) (0, q0) (0, 1)) (0, 1)) q0 := by
    simpa only [Function.comp_apply, map_zero, add_zero] using
      hgradLine.clm_apply (hasDerivAt_const q0 ((0 : ℝ), (1 : ℝ)))
  have hsecond : 0 < deriv (deriv (fun q : ℝ => J (0, q))) q0 := by
    rw [heq.deriv_eq, hscalar.deriv]
    exact hcurvature
  let F : (ℝ × ℝ) → ℝ := fun p => J (p.1 * Real.sqrt p.2, p.2)
  have hmap : ContDiffAt ℝ (3 : WithTop ENat)
      (fun p : ℝ × ℝ => (p.1 * Real.sqrt p.2, p.2)) (0, q0) :=
    (contDiffAt_fst.mul (contDiffAt_snd.sqrt hq0.ne')).prodMk contDiffAt_snd
  have hJs : ContDiffAt ℝ (3 : WithTop ENat) J
      ((0 : ℝ) * Real.sqrt q0, q0) := by simpa only [zero_mul] using hsmooth
  have hF : ContDiffAt ℝ (3 : WithTop ENat) F (0, q0) := hJs.comp (0, q0) hmap
  have hFsecond : 0 < deriv (deriv (fun q : ℝ => F (0, q))) q0 := by
    simpa only [F, zero_mul] using hsecond
  obtain ⟨eta, rho, heta, hrho, hrect⟩ :=
    joint_energy_positive_curvature_neighborhood F q0 hF hFsecond
  refine ⟨eta, min rho (q0 / 2), heta, lt_min hrho (half_pos hq0),
    (min_le_right _ _).trans_lt (half_lt_self hq0), ?_⟩
  intro level q hlevel hq
  exact hrect level q hlevel (hq.trans (min_le_left _ _))

end
end Shao.OQ3
