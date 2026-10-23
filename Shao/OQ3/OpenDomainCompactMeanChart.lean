import Shao.OQ3.OpenDomainMeanInverse
import Mathlib.Topology.MetricSpace.ProperSpace

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem open_domain_quadratic_tilt_compact_mean_chart
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (hdet : (parabolaCovariance
      (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))).det ≠ 0) :
    let Omega : Set (ℝ × ℝ) := interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
    let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    let means : (ℝ × ℝ) → (ℝ × ℝ) := fun p =>
      (∫ x : ℝ, x ∂nu p, ∫ x : ℝ, x ^ 2 ∂nu p)
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ), ∃ epsilon : ℝ,
      0 < epsilon ∧
      (e : (ℝ × ℝ) → (ℝ × ℝ)) = means ∧
      theta ∈ e.source ∧ e.source ⊆ Omega ∧
      Metric.closedBall (means theta) epsilon ⊆ e.target ∧
      ContDiffAt ℝ ∞ (e.symm : (ℝ × ℝ) → (ℝ × ℝ)) (means theta) ∧
      let U : Set (ℝ × ℝ) := Metric.ball (means theta) epsilon
      let Theta : Set (ℝ × ℝ) := e.symm '' Metric.closedBall (means theta) epsilon
      IsOpen U ∧ means theta ∈ U ∧ IsCompact Theta ∧ theta ∈ Theta ∧
        Theta ⊆ Omega ∧
        ContinuousOn (e.symm : (ℝ × ℝ) → (ℝ × ℝ))
          (Metric.closedBall (means theta) epsilon) ∧
        (∀ m ∈ Metric.closedBall (means theta) epsilon,
          e.symm m ∈ Theta ∧ means (e.symm m) = m) ∧
        (∀ p ∈ Theta, e.symm (means p) = p) ∧
        means '' Theta = Metric.closedBall (means theta) epsilon ∧
        e.symm '' U ⊆ Theta := by
  let Omega : Set (ℝ × ℝ) := interior
    (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
  let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
    mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
  let means : (ℝ × ℝ) → (ℝ × ℝ) := fun p =>
    (∫ x : ℝ, x ∂nu p, ∫ x : ℝ, x ^ 2 ∂nu p)
  obtain ⟨L, e, _hL, he, hs, ht, hOmega, hinverse, _hderiv⟩ :=
    open_domain_quadratic_tilt_local_mean_inverse mu theta htheta hdet
  have hmeans : (e : (ℝ × ℝ) → (ℝ × ℝ)) = means := he
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds ht)
  let epsilon : ℝ := r / 2
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; linarith
  have hclosed : Metric.closedBall (means theta) epsilon ⊆ e.target :=
    Set.Subset.trans (Metric.closedBall_subset_ball (by dsimp [epsilon]; linarith)) hball
  let U : Set (ℝ × ℝ) := Metric.ball (means theta) epsilon
  let Theta : Set (ℝ × ℝ) := e.symm '' Metric.closedBall (means theta) epsilon
  have hcontinuous : ContinuousOn (e.symm : (ℝ × ℝ) → (ℝ × ℝ))
      (Metric.closedBall (means theta) epsilon) := e.continuousOn_symm.mono hclosed
  have hcompact : IsCompact Theta :=
    (isCompact_closedBall (means theta) epsilon).image_of_continuousOn hcontinuous
  have hcenter : theta ∈ Theta := by
    refine ⟨means theta, Metric.mem_closedBall_self hepsilon.le, ?_⟩
    rw [← hmeans]
    exact e.left_inv hs
  have hsubset : Theta ⊆ Omega := by
    rintro p ⟨m, hm, rfl⟩
    exact hOmega (e.map_target (hclosed hm))
  have hright (m : ℝ × ℝ) (hm : m ∈ Metric.closedBall (means theta) epsilon) :
      means (e.symm m) = m := by
    rw [← hmeans]
    exact e.right_inv (hclosed hm)
  have hleft : ∀ p ∈ Theta, e.symm (means p) = p := by
    rintro p ⟨m, hm, rfl⟩
    rw [← hmeans]
    exact e.left_inv (e.map_target (hclosed hm))
  have himage : means '' Theta = Metric.closedBall (means theta) epsilon := by
    apply Set.Subset.antisymm
    · rintro m ⟨p, ⟨q, hq, rfl⟩, rfl⟩
      rw [hright q hq]
      exact hq
    · intro m hm
      exact ⟨e.symm m, ⟨m, hm, rfl⟩, hright m hm⟩
  refine ⟨e, epsilon, hepsilon, he, hs, hOmega, hclosed, hinverse, ?_⟩
  exact ⟨Metric.isOpen_ball, Metric.mem_ball_self hepsilon, hcompact, hcenter, hsubset,
    hcontinuous, (fun m hm => ⟨⟨m, hm, rfl⟩, hright m hm⟩), hleft, himage,
    Set.image_mono Metric.ball_subset_closedBall⟩

end
end Shao.OQ3
