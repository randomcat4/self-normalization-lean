import Shao.OQ3.OpenDomainSmoothMean
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem open_domain_quadratic_tilt_local_mean_inverse
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
    let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (nu theta)
    let pr0 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
    let pr1 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
    let row0 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 0 • pr0 + D 0 1 • pr1
    let row1 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 1 • pr0 + D 1 1 • pr1
    ∃ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ), ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = row0.prod row1 ∧
      (e : (ℝ × ℝ) → (ℝ × ℝ)) = means ∧
      theta ∈ e.source ∧ means theta ∈ e.target ∧ e.source ⊆ Omega ∧
      ContDiffAt ℝ ∞ (e.symm : (ℝ × ℝ) → (ℝ × ℝ)) (means theta) ∧
      HasStrictFDerivAt (e.symm : (ℝ × ℝ) → (ℝ × ℝ))
        (L.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (means theta) := by
  let Omega : Set (ℝ × ℝ) := interior
    (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
  let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
    mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
  let means : (ℝ × ℝ) → (ℝ × ℝ) := fun p =>
    (∫ x : ℝ, x ∂nu p, ∫ x : ℝ, x ^ 2 ∂nu p)
  let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (nu theta)
  let pr0 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let pr1 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  let row0 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 0 • pr0 + D 0 1 • pr1
  let row1 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 1 • pr0 + D 1 1 • pr1
  let A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := row0.prod row1
  let delta : ℝ := D 0 0 * D 1 1 - (D 0 1) ^ 2
  have h10 : D 1 0 = D 0 1 := rfl
  have hD : D.det = delta := by
    rw [Matrix.det_fin_two, h10]
    dsimp [delta]
    ring
  have hdelta : delta ≠ 0 := by rw [← hD]; exact hdet
  let inv : (ℝ × ℝ) → (ℝ × ℝ) := fun v =>
    ((D 1 1 * v.1 - D 0 1 * v.2) / delta,
      (D 0 0 * v.2 - D 0 1 * v.1) / delta)
  have hleft (v : ℝ × ℝ) : inv (A v) = v := by
    apply Prod.ext
    · change (D 1 1 * (D 0 0 * v.1 + D 0 1 * v.2) -
        D 0 1 * (D 0 1 * v.1 + D 1 1 * v.2)) / delta = v.1
      apply (div_eq_iff hdelta).mpr
      dsimp [delta]
      ring
    · change (D 0 0 * (D 0 1 * v.1 + D 1 1 * v.2) -
        D 0 1 * (D 0 0 * v.1 + D 0 1 * v.2)) / delta = v.2
      apply (div_eq_iff hdelta).mpr
      dsimp [delta]
      ring
  have hright (v : ℝ × ℝ) : A (inv v) = v := by
    apply Prod.ext
    · change D 0 0 * ((D 1 1 * v.1 - D 0 1 * v.2) / delta) +
        D 0 1 * ((D 0 0 * v.2 - D 0 1 * v.1) / delta) = v.1
      field_simp [hdelta]
      dsimp [delta]
      ring
    · change D 0 1 * ((D 1 1 * v.1 - D 0 1 * v.2) / delta) +
        D 1 1 * ((D 0 0 * v.2 - D 0 1 * v.1) / delta) = v.2
      field_simp [hdelta]
      dsimp [delta]
      ring
  let E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
    { toLinearEquiv :=
        { A.toLinearMap with invFun := inv, left_inv := hleft, right_inv := hright }
      continuous_toFun := A.continuous
      continuous_invFun := by dsimp [inv]; fun_prop }
  have hE : (E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = A := rfl
  have hd : HasFDerivAt means A theta :=
    (open_domain_quadratic_tilt_frechet_cumulants mu theta htheta).2.2.2.1
  have hdE : HasFDerivAt means (E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) theta := by
    rw [hE]
    exact hd
  have hm : ContDiffAt ℝ ∞ means theta :=
    ((open_domain_quadratic_tilt_smooth_and_strict mu).2.2.1 theta htheta).contDiffAt
      (isOpen_interior.mem_nhds htheta)
  let f : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
    hm.toOpenPartialHomeomorph means hdE (by simp)
  let e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
    f.restrOpen Omega isOpen_interior
  have hs : theta ∈ e.source := by
    change theta ∈ f.source ∩ Omega
    exact ⟨hm.mem_toOpenPartialHomeomorph_source hdE (by simp), htheta⟩
  have ht : means theta ∈ e.target := e.map_source hs
  refine ⟨E, e, hE, rfl, hs, ht, ?_, ?_, ?_⟩
  · exact Set.inter_subset_right
  · change ContDiffAt ℝ ∞ (hm.localInverse hdE (by simp)) (means theta)
    exact hm.to_localInverse hdE (by simp)
  · let hstrict := hm.hasStrictFDerivAt' hdE (by simp)
    change HasStrictFDerivAt (hstrict.localInverse means E theta)
      (E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (means theta)
    exact hstrict.to_localInverse

end
end Shao.OQ3
