import Shao.OQ3.OpenDomainLegendre

namespace Shao.OQ3
open MeasureTheory Filter
open scoped Matrix Topology
noncomputable section

theorem actual_mean_chart_local_compatibility
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (e f : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ))
    (he : (e : (ℝ × ℝ) → (ℝ × ℝ)) = fun p =>
      (∫ x : ℝ, x ∂mu.tilted (fun x => p.1 * x + p.2 * x ^ 2),
        ∫ x : ℝ, x ^ 2 ∂mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)))
    (hf : (f : (ℝ × ℝ) → (ℝ × ℝ)) = fun p =>
      (∫ x : ℝ, x ∂mu.tilted (fun x => p.1 * x + p.2 * x ^ 2),
        ∫ x : ℝ, x ^ 2 ∂mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)))
    (hte : theta ∈ e.source) (htf : theta ∈ f.source) :
    let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    let means : (ℝ × ℝ) → (ℝ × ℝ) := fun p =>
      (∫ x : ℝ, x ∂nu p, ∫ x : ℝ, x ^ 2 ∂nu p)
    let K : (ℝ × ℝ) → ℝ := fun p => Real.log
      (∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu)
    let Je : (ℝ × ℝ) → ℝ := fun w =>
      (e.symm w).1 * w.1 + (e.symm w).2 * w.2 - K (e.symm w)
    let Jf : (ℝ × ℝ) → ℝ := fun w =>
      (f.symm w).1 * w.1 + (f.symm w).2 * w.2 - K (f.symm w)
    let Ae : (ℝ × ℝ) → ℝ := fun w =>
      (Real.sqrt (parabolaCovariance (nu (e.symm w))).det)⁻¹
    let Af : (ℝ × ℝ) → ℝ := fun w =>
      (Real.sqrt (parabolaCovariance (nu (f.symm w))).det)⁻¹
    e.symm (means theta) = theta ∧ f.symm (means theta) = theta ∧
      ∀ᶠ w in 𝓝 (means theta), w ∈ e.target ∧ w ∈ f.target ∧
        e.symm w = f.symm w ∧ Je w = Jf w ∧ Ae w = Af w := by
  intro nu means K Je Jf Ae Af
  have hE : (e : (ℝ × ℝ) → (ℝ × ℝ)) = means := he
  have hF : (f : (ℝ × ℝ) → (ℝ × ℝ)) = means := hf
  have heCenter : e.symm (means theta) = theta := by
    rw [← hE]
    exact e.left_inv hte
  have hfCenter : f.symm (means theta) = theta := by
    rw [← hF]
    exact f.left_inv htf
  have heTarget : means theta ∈ e.target := by
    rw [← hE]
    exact e.map_source hte
  have hfTarget : means theta ∈ f.target := by
    rw [← hF]
    exact f.map_source htf
  have hcont : ContinuousAt (e.symm : (ℝ × ℝ) → (ℝ × ℝ)) (means theta) :=
    e.continuousOn_symm.continuousAt (e.open_target.mem_nhds heTarget)
  have hPre : ∀ᶠ w in 𝓝 (means theta), e.symm w ∈ f.source := by
    apply hcont.tendsto.eventually
    rw [heCenter]
    exact f.open_source.mem_nhds htf
  refine ⟨heCenter, hfCenter, ?_⟩
  filter_upwards [e.open_target.mem_nhds heTarget,
    f.open_target.mem_nhds hfTarget, hPre] with w hwe hwf hwSource
  have hMap : f (e.symm w) = w := by
    rw [hF, ← hE]
    exact e.right_inv hwe
  have hInverse : e.symm w = f.symm w := by
    calc
      e.symm w = f.symm (f (e.symm w)) := (f.left_inv hwSource).symm
      _ = f.symm w := congrArg f.symm hMap
  refine ⟨hwe, hwf, hInverse, ?_, ?_⟩
  · dsimp only [Je, Jf]
    rw [hInverse]
  · dsimp only [Ae, Af]
    rw [hInverse]

end
end Shao.OQ3
