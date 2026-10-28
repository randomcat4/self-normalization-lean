import Shao.OQ3.ActualMeanChartRateDerivatives
import Shao.OQ3.CompactPlaneTaylorAmplitude

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

set_option maxHeartbeats 2000000 in
theorem actual_mean_chart_compact_taylor_amplitude
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ))
    (he : (e : (ℝ × ℝ) → (ℝ × ℝ)) = fun p =>
      (∫ x : ℝ, x ∂mu.tilted (fun x => p.1 * x + p.2 * x ^ 2),
        ∫ x : ℝ, x ^ 2 ∂mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)))
    (hsource : e.source ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (V : Set (ℝ × ℝ)) (hCompact : IsCompact V) (hTarget : V ⊆ e.target)
    (hPositive : ∀ y ∈ V, 0 < (parabolaCovariance
      (mu.tilted (fun x => (e.symm y).1 * x + (e.symm y).2 * x ^ 2))).det) :
    let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    let D : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun y =>
      parabolaCovariance (nu (e.symm y))
    let K : (ℝ × ℝ) → ℝ := fun p => Real.log
      (∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu)
    let J : (ℝ × ℝ) → ℝ := fun y =>
      (e.symm y).1 * y.1 + (e.symm y).2 * y.2 - K (e.symm y)
    let A : (ℝ × ℝ) → ℝ := fun y => (Real.sqrt (D y).det)⁻¹
    let Q : (ℝ × ℝ) → (ℝ × ℝ) → ℝ := fun y v =>
      (D y 1 1 * v.1 ^ 2 - 2 * D y 0 1 * v.1 * v.2 + D y 0 0 * v.2 ^ 2) /
        (D y).det
    ∃ delta C amin amax : ℝ, 0 < delta ∧ 0 < C ∧ 0 < amin ∧ 0 < amax ∧
      (∀ y ∈ V, amin ≤ A y ∧ A y ≤ amax) ∧
      (∀ y ∈ V, ∀ v : ℝ × ℝ, |Q y v| ≤ C * ‖v‖ ^ 2) ∧
      ∀ y ∈ V, ∀ w : ℝ × ℝ, ‖w - y‖ ≤ delta →
        w ∈ e.target ∧ 0 < (D w).det ∧
        |J w - J y - ((e.symm y).1 * (w - y).1 + (e.symm y).2 * (w - y).2)| ≤
          C * ‖w - y‖ ^ 2 ∧
        |A w - A y| ≤ C * ‖w - y‖ := by
  intro nu D K J A Q
  let U : Set (ℝ × ℝ) := {z | z ∈ e.target ∧ 0 < (D z).det}
  have hDetAt (z : ℝ × ℝ) (hz : z ∈ e.target) :
      ContinuousAt (fun w => (D w).det) z := by
    have hp := hsource (e.map_target hz)
    have hdp : ContDiffAt ℝ ∞ (fun p => (parabolaCovariance (nu p)).det) (e.symm z) :=
      ((open_domain_quadratic_covariance_det_contDiffOn mu) (e.symm z) hp).contDiffAt
        (isOpen_interior.mem_nhds hp)
    exact hdp.continuousAt.comp (e.symm.continuousAt hz)
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    filter_upwards [e.open_target.mem_nhds hz.1,
      (hDetAt z hz.1).eventually (lt_mem_nhds hz.2)] with q hq hpos
    exact ⟨hq, hpos⟩
  have hVU : V ⊆ U := fun z hz => ⟨hTarget hz, hPositive z hz⟩
  have hAt (z : ℝ × ℝ) (hz : z ∈ U) :=
    actual_mean_chart_rate_covariance_derivatives mu e he hsource z hz.1 hz.2
  have hSmooth (z : ℝ × ℝ) (hz : z ∈ U) :
      ContDiffAt ℝ ∞ J z ∧ ContDiffAt ℝ ∞ A z := by
    obtain ⟨_, _, _, _, hJ, _, _, _, hA, _⟩ := hAt z hz
    exact ⟨hJ, hA⟩
  obtain ⟨delta, C0, hdelta, hC0, hTaylor⟩ :=
    compact_plane_uniform_quadratic_taylor_and_amplitude J A U V hU hCompact hVU
      (fun z hz => (hSmooth z hz).1.of_le (by simp))
      (fun z hz => (hSmooth z hz).2.of_le (by simp))
  have hContH : ContinuousOn (fun y => fderiv ℝ (fun z => fderiv ℝ J z) y) V := by
    intro y hy
    exact (((hSmooth y (hVU hy)).1.fderiv_right (m := 1) (by simp)).fderiv_right
      (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hContA : ContinuousOn A V := fun y hy =>
    (hSmooth y (hVU hy)).2.continuousAt.continuousWithinAt
  have hContRoot : ContinuousOn (fun y => Real.sqrt (D y).det) V := fun y hy =>
    ((hDetAt y (hTarget hy)).sqrt).continuousWithinAt
  obtain ⟨H, hH⟩ := hCompact.exists_bound_of_continuousOn
    (f := fun y : ℝ × ℝ => fderiv ℝ (fun z => fderiv ℝ J z) y) hContH
  obtain ⟨BA, hBA⟩ := hCompact.exists_bound_of_continuousOn (f := A) hContA
  obtain ⟨BR, hBR⟩ := hCompact.exists_bound_of_continuousOn
    (f := fun y : ℝ × ℝ => Real.sqrt (D y).det) hContRoot
  let C : ℝ := 1 + C0 + |H|
  let amin : ℝ := 1 / (1 + |BR|)
  let amax : ℝ := 1 + |BA|
  have hC : 0 < C := by dsimp [C]; positivity
  have hC0le : C0 ≤ C := by dsimp [C]; linarith [abs_nonneg H]
  have hHle : H ≤ C := by dsimp [C]; linarith [le_abs_self H]
  have hamin : 0 < amin := by dsimp [amin]; positivity
  have hamax : 0 < amax := by dsimp [amax]; positivity
  refine ⟨delta, C, amin, amax, hdelta, hC, hamin, hamax, ?_, ?_, ?_⟩
  · intro y hy
    have hRoot : 0 < Real.sqrt (D y).det := Real.sqrt_pos.mpr (hPositive y hy)
    have hRootBound : Real.sqrt (D y).det ≤ 1 + |BR| := by
      have hb := hBR y hy
      rw [Real.norm_eq_abs, abs_of_pos hRoot] at hb
      linarith [le_abs_self BR]
    constructor
    · have hh := one_div_le_one_div_of_le hRoot hRootBound
      simpa only [amin, A, one_div] using hh
    · have hb := hBA y hy
      rw [Real.norm_eq_abs] at hb
      dsimp [amax]
      linarith [le_abs_self (A y), le_abs_self BA]
  · intro y hy v
    obtain ⟨_, _, _, _, _, _, _, hQuad, _, _⟩ := hAt y (hVU hy)
    change (∀ v : ℝ × ℝ, (fderiv ℝ (fun z => fderiv ℝ J z) y v) v = Q y v) at hQuad
    rw [← hQuad v]
    let Hmap := fderiv ℝ (fun z => fderiv ℝ J z) y
    have hNorm : ‖Hmap‖ ≤ C := (hH y hy).trans hHle
    calc
      |Hmap v v| = ‖Hmap v v‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖Hmap v‖ * ‖v‖ := (Hmap v).le_opNorm v
      _ ≤ (‖Hmap‖ * ‖v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (Hmap.le_opNorm v) (norm_nonneg v)
      _ ≤ (C * ‖v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hNorm (norm_nonneg v)) (norm_nonneg v)
      _ = C * ‖v‖ ^ 2 := by ring
  · intro y hy w hw
    obtain ⟨hDomain, hRemainder, hAmplitude⟩ := hTaylor y hy w hw
    obtain ⟨_, _, _, _, _, hFirst, _, _, _, _⟩ := hAt y (hVU hy)
    have hLinear : fderiv ℝ J y (w - y) =
        (e.symm y).1 * (w - y).1 + (e.symm y).2 * (w - y).2 := by
      rw [hFirst.fderiv]
      rfl
    rw [hLinear] at hRemainder
    exact ⟨hDomain.1, hDomain.2,
      hRemainder.trans (mul_le_mul_of_nonneg_right hC0le (sq_nonneg _)),
      hAmplitude.trans (mul_le_mul_of_nonneg_right hC0le (norm_nonneg _))⟩

end
end Shao.OQ3
