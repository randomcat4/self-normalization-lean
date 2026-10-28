import Shao.OQ3.ActualMeanChartLaplaceCutoff
import Shao.OQ3.BoundaryLaplaceNatNormalization

namespace Shao.OQ3
open MeasureTheory Filter
open scoped Matrix Topology ContDiff
noncomputable section

set_option maxHeartbeats 2000000 in
theorem actual_mean_chart_laplace_nat_physical_windows
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (hdet : 0 < (parabolaCovariance
      (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))).det)
    (level a0 : ℝ) (hlevel : 0 < level) (ha0 : 0 < a0) (hnegative : theta.2 < 0)
    (hmean : (∫ x : ℝ, x ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2),
      ∫ x : ℝ, x ^ 2 ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)) =
        (a0, a0 ^ 2 / level ^ 2))
    (hsaddle : theta.1 = -2 * a0 * theta.2 / level ^ 2)
    (e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ))
    (he : (e : (ℝ × ℝ) → (ℝ × ℝ)) = fun p =>
      (∫ x : ℝ, x ∂mu.tilted (fun x => p.1 * x + p.2 * x ^ 2),
        ∫ x : ℝ, x ^ 2 ∂mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)))
    (hte : theta ∈ e.source)
    (hsource : e.source ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (rmax : ℝ) (hrmax : 0 < rmax) :
    let Omega : Set (ℝ × ℝ) := interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
    let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    let means : (ℝ × ℝ) → (ℝ × ℝ) := fun p =>
      (∫ x : ℝ, x ∂nu p, ∫ x : ℝ, x ^ 2 ∂nu p)
    let K : (ℝ × ℝ) → ℝ := fun p => Real.log
      (∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu)
    let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (nu theta)
    let pr0 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
    let pr1 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
    let row0 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 0 • pr0 + D 0 1 • pr1
    let row1 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 1 • pr0 + D 1 1 • pr1
    ∀ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = row0.prod row1 →
      let J : (ℝ × ℝ) → ℝ := fun w =>
        (e.symm w).1 * w.1 + (e.symm w).2 * w.2 - K (e.symm w)
      let B : (ℝ × ℝ) → ℝ := fun w =>
        (Real.sqrt (parabolaCovariance (nu (e.symm w))).det)⁻¹
      let v : ℝ × ℝ := (1, 2 * a0 / level ^ 2)
      let Lambda1 : ℝ := 2 * theta.2 / level ^ 2 +
        (L.symm v).1 + (2 * a0 / level ^ 2) * (L.symm v).2
      let C0 : ℝ := (Real.sqrt D.det)⁻¹ * (Real.sqrt (2 * Real.pi / Lambda1) / (-theta.2))
      let J0 : ℝ := J (a0, a0 ^ 2 / level ^ 2)
      let m0 : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (volume : Measure ℝ)
      0 < -theta.2 ∧ (0 < Lambda1 →
        ∃ cap : ℝ, 0 < cap ∧ cap ≤ rmax ∧ 0 < C0 ∧
          ∀ rho : ℝ, 0 < rho → rho ≤ cap →
            let V : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
              w.1 ^ 2 / level ^ 2 - rho ≤ w.2 ∧ w.2 ≤ w.1 ^ 2 / level ^ 2}
            (∀ w ∈ V, w ∈ e.target ∧ e.symm w ∈ e.source ∧ e.symm w ∈ Omega ∧
              means (e.symm w) = w ∧ 0 < (parabolaCovariance (nu (e.symm w))).det ∧
              Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w =
                (J w : EReal)) ∧
            ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
              let W : (ℝ × ℝ) → ℝ := fun w => B w * Real.exp (-(n : ℝ) * J w)
              let T : (ℝ × ℝ) → ℝ := fun w => B w * Real.exp (-(n : ℝ) * (J w - J0))
              let Ln : ℝ := ((n : ℝ) / (2 * Real.pi)) * ∫ w : ℝ × ℝ in V, T w ∂m0
              let main : ℝ := 1 /
                (Real.sqrt (2 * Real.pi * (n : ℝ)) * (-theta.2) * Real.sqrt D.det *
                  Real.sqrt Lambda1)
              IntegrableOn W V m0 ∧ IntegrableOn T V m0 ∧ 0 ≤ Ln ∧ 0 < main ∧
                |Ln / main - 1| ≤ C / Real.sqrt (n : ℝ)) := by
  classical
  intro Omega nu means K D pr0 pr1 row0 row1 L hL J B v Lambda1 C0 J0 m0
  let G : (ℝ × ℝ) → (ℝ × ℝ) := fun w =>
    (a0 + w.1, (a0 + w.1) ^ 2 / level ^ 2 - w.2)
  let Cs : ℝ := B (G (0, 0)) * (Real.sqrt (2 * Real.pi / Lambda1) / (-theta.2))
  obtain ⟨hlambda, _, hA0, _, H⟩ :=
    actual_mean_chart_laplace_cutoff_all_small_windows mu theta htheta hdet
      level a0 hlevel ha0 hnegative hmean hsaddle e he hte hsource rmax hrmax L hL
  have hA0exact : B (G (0, 0)) = (Real.sqrt D.det)⁻¹ := hA0
  have hCs : Cs = C0 := by dsimp only [Cs, C0]; rw [hA0exact]
  refine ⟨hlambda, ?_⟩
  intro hcurvature
  obtain ⟨cap, hcap, hcapMax, hCsPos, hAll⟩ := H hcurvature
  have hCsPositive : 0 < Cs := hCsPos
  have hC0 : 0 < C0 := by rw [← hCs]; exact hCsPositive
  refine ⟨cap, hcap, hcapMax, hC0, ?_⟩
  intro rho hrho hrhocap V
  obtain ⟨hWindow, C, hC, hScaled⟩ := hAll rho hrho hrhocap
  have hreal := boundary_laplace_original_strip_transfer J B a0 level rho Cs C hCsPositive (by
    intro t ht ht1
    obtain ⟨hI, _, hRel⟩ := hScaled t ht ht1
    exact ⟨hI, hRel⟩)
  have hnat := boundary_laplace_nat_normalization J B V J0 Cs C hreal
  refine ⟨?_, C, hC, ?_⟩
  · intro w hw
    let R : Set (ℝ × ℝ) := {u | |u.1| ≤ rho ∧ 0 ≤ u.2 ∧ u.2 ≤ rho}
    have himage : G '' R = V := boundary_rate_chart_rectangle_image a0 level rho
    rw [← himage] at hw
    obtain ⟨u, hu, huEq⟩ := hw
    rw [← huEq]
    exact hWindow u.1 u.2 hu.1 hu.2.1 hu.2.2
  · intro n hn W T Ln main
    obtain ⟨hW, hPos, hError⟩ := hnat n hn
    let Gnat : ℝ := ((n : ℝ) / (2 * Real.pi)) * ∫ w : ℝ × ℝ in V, W w ∂m0
    let Mnat : ℝ := Real.exp (-(n : ℝ) * J0) * (Cs / (2 * Real.pi)) / Real.sqrt (n : ℝ)
    have hMnat : 0 < Mnat := hPos
    have hNatError : |Gnat / Mnat - 1| ≤ C / Real.sqrt (n : ℝ) := hError
    let E : ℝ := Real.exp ((n : ℝ) * J0)
    have hE : 0 < E := Real.exp_pos _
    have hT : T = fun w => E * W w := by
      funext w
      dsimp only [T, W, E]
      rw [show -(n : ℝ) * (J w - J0) = (n : ℝ) * J0 + -(n : ℝ) * J w by ring,
        Real.exp_add]
      ring
    have hTV : IntegrableOn T V m0 := by
      rw [hT]
      exact hW.const_mul E
    have hLn : Ln = E * Gnat := by
      change ((n : ℝ) / (2 * Real.pi)) * (∫ w : ℝ × ℝ in V, T w ∂m0) = _
      rw [hT, integral_const_mul]
      dsimp only [Gnat]
      ring
    have hExp : E * Real.exp (-(n : ℝ) * J0) = 1 := by
      dsimp only [E]
      rw [← Real.exp_add, show (n : ℝ) * J0 + -(n : ℝ) * J0 = 0 by ring, Real.exp_zero]
    have hConstant : Mnat = Real.exp (-(n : ℝ) * J0) /
        (Real.sqrt (2 * Real.pi * (n : ℝ)) * (-theta.2) * Real.sqrt D.det *
          Real.sqrt Lambda1) := by
      dsimp only [Mnat]
      rw [hCs]
      exact (boundary_laplace_source_leading_constant D.det (-theta.2) Lambda1).2 n J0
    have hMain : E * Mnat = main := by
      rw [hConstant]
      change E * (Real.exp (-(n : ℝ) * J0) / _) = 1 / _
      rw [← mul_div_assoc, hExp]
    have hMainPos : 0 < main := by rw [← hMain]; exact mul_pos hE hMnat
    have hRatio : Ln / main = Gnat / Mnat := by
      rw [← hMain, hLn]
      field_simp [hE.ne', hMnat.ne']
    have hLnNonneg : 0 ≤ Ln := by
      have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hScale : 0 ≤ (n : ℝ) / (2 * Real.pi) :=
        div_nonneg hnR (mul_pos (by norm_num) Real.pi_pos).le
      exact mul_nonneg hScale (integral_nonneg (fun w =>
        mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (Real.exp_pos _).le))
    refine ⟨hW, hTV, hLnNonneg, hMainPos, ?_⟩
    rw [hRatio]
    exact hNatError

end
end Shao.OQ3
