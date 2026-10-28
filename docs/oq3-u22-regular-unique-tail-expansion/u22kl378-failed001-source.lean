import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

namespace Shao.OQ3
open scoped Topology
noncomputable section

theorem scaled_tangent_positive_curvature_neighborhood
    (J : (ℝ × ℝ) → ℝ) (P : (ℝ × ℝ) → (ℝ × ℝ))
    (q0 : ℝ) (hq0 : 0 < q0)
    (hsmooth : ContDiffAt ℝ (3 : WithTop ENat) J (0, q0))
    (hP : ContinuousAt P (0, q0)) (hP0 : P (0, q0) = (0, 0))
    (hcurvature : 0 <
      (fderiv ℝ (fun z => fderiv ℝ J z) (0, q0) (0, 1)) (0, 1)) :
    ∃ eta rho : ℝ, 0 < eta ∧ 0 < rho ∧ rho < q0 ∧ ∀ (level : ℝ) (z : ℝ × ℝ),
      |level| ≤ eta → dist z (0, q0) ≤ rho →
        0 < 2 * (P z).2 +
          (fderiv ℝ (fun w => fderiv ℝ J w) z
            (level, 2 * Real.sqrt z.2)) (level, 2 * Real.sqrt z.2) := by
  let H : (ℝ × ℝ) → ((ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ)) :=
    fun z => fderiv ℝ (fun w => fderiv ℝ J w) z
  let v : (ℝ × (ℝ × ℝ)) → (ℝ × ℝ) :=
    fun p => (p.1, 2 * Real.sqrt p.2.2)
  let S : (ℝ × (ℝ × ℝ)) → ℝ :=
    fun p => 2 * (P p.2).2 + H p.2 (v p) (v p)
  have hH : ContinuousAt H ((0 : ℝ), q0) :=
    ((hsmooth.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).continuousAt
  have hHP : ContinuousAt (fun p : ℝ × (ℝ × ℝ) => H p.2) (0, (0, q0)) :=
    hH.comp continuousAt_snd
  have hv : ContinuousAt v (0, (0, q0)) := by dsimp only [v]; fun_prop
  have hS : ContinuousAt S (0, (0, q0)) :=
    ((hP.snd.comp continuousAt_snd).const_mul 2).add
      ((hHP.clm_apply hv).clm_apply hv)
  have hv0 : ((0 : ℝ), 2 * Real.sqrt q0) =
      (2 * Real.sqrt q0) • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  have hscaled : H (0, q0) (0, 2 * Real.sqrt q0) (0, 2 * Real.sqrt q0) =
      (2 * Real.sqrt q0) ^ 2 * H (0, q0) (0, 1) (0, 1) := by
    rw [hv0]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hS0 : 0 < S (0, (0, q0)) := by
    change 0 < 2 * (P (0, q0)).2 +
      H (0, q0) (0, 2 * Real.sqrt q0) (0, 2 * Real.sqrt q0)
    rw [hP0, hscaled]
    simpa only [mul_zero, zero_add] using
      mul_pos (sq_pos_of_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr hq0))) hcurvature
  have hpositive : ∀ᶠ p in 𝓝 ((0 : ℝ), ((0 : ℝ), q0)), 0 < S p :=
    hS.eventually (lt_mem_nhds hS0)
  obtain ⟨d, hd, hpoint⟩ := Metric.eventually_nhds_iff.mp hpositive
  refine ⟨d / 2, min (d / 2) (q0 / 2), half_pos hd,
    lt_min (half_pos hd) (half_pos hq0),
    (min_le_right _ _).trans_lt (half_lt_self hq0), ?_⟩
  intro level z hlevel hz
  apply hpoint
  rw [Prod.dist_eq, max_lt_iff]
  exact ⟨by simpa only [Real.dist_eq, sub_zero] using
    hlevel.trans_lt (half_lt_self hd),
    (hz.trans (min_le_left _ _)).trans_lt (half_lt_self hd)⟩

end
end Shao.OQ3
