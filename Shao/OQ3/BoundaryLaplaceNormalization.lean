import Shao.OQ3.BoundaryLaplaceScaling

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem boundary_laplace_original_strip_transfer
    (J B : (ℝ × ℝ) → ℝ) (a0 level rho C0 C : ℝ) (hC0 : 0 < C0)
    (hscaled : ∀ t : ℝ, 0 < t → t ≤ 1 →
      let G : (ℝ × ℝ) → (ℝ × ℝ) := fun w =>
        (a0 + w.1, (a0 + w.1) ^ 2 / level ^ 2 - w.2)
      let m : Measure (ℝ × ℝ) :=
        (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0))
      let H : (ℝ × ℝ) → ℝ := fun p =>
        if |t * p.1| ≤ rho ∧ t ^ 2 * p.2 ≤ rho then
          B (G (t * p.1, t ^ 2 * p.2)) *
            Real.exp (-((J (G (t * p.1, t ^ 2 * p.2)) - J (G (0, 0))) / t ^ 2)) else 0
      Integrable H m ∧ |(∫ p : ℝ × ℝ, H p ∂m) / C0 - 1| ≤ C * t) :
    let m0 : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (volume : Measure ℝ)
    let V : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
      w.1 ^ 2 / level ^ 2 - rho ≤ w.2 ∧ w.2 ≤ w.1 ^ 2 / level ^ 2}
    let J0 : ℝ := J (a0, a0 ^ 2 / level ^ 2)
    ∀ t : ℝ, 0 < t → t ≤ 1 →
      let W : (ℝ × ℝ) → ℝ := fun w => B w * Real.exp (-J w / t ^ 2)
      let Ln : ℝ := (1 / (2 * Real.pi * t ^ 2)) * ∫ w : ℝ × ℝ in V, W w ∂m0
      let main : ℝ := t * Real.exp (-J0 / t ^ 2) * (C0 / (2 * Real.pi))
      IntegrableOn W V m0 ∧ 0 < main ∧ |Ln / main - 1| ≤ C * t := by
  let m0 : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (volume : Measure ℝ)
  let V : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
    w.1 ^ 2 / level ^ 2 - rho ≤ w.2 ∧ w.2 ≤ w.1 ^ 2 / level ^ 2}
  let J0 : ℝ := J (a0, a0 ^ 2 / level ^ 2)
  dsimp only
  intro t ht ht1
  let W : (ℝ × ℝ) → ℝ := fun w => B w * Real.exp (-J w / t ^ 2)
  let G : (ℝ × ℝ) → (ℝ × ℝ) := fun w =>
    (a0 + w.1, (a0 + w.1) ^ 2 / level ^ 2 - w.2)
  let R : Set (ℝ × ℝ) := {w | |w.1| ≤ rho ∧ 0 ≤ w.2 ∧ w.2 ≤ rho}
  let m : Measure (ℝ × ℝ) :=
    (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0))
  let center : (ℝ × ℝ) → ℝ := fun w => B (G w) *
    Real.exp (-((J (G w) - J (G (0, 0))) / t ^ 2))
  let H : (ℝ × ℝ) → ℝ := fun p =>
    if |t * p.1| ≤ rho ∧ t ^ 2 * p.2 ≤ rho then center (t * p.1, t ^ 2 * p.2) else 0
  have hs : Integrable H m ∧ |(∫ p : ℝ × ℝ, H p ∂m) / C0 - 1| ≤ C * t := hscaled t ht ht1
  obtain ⟨hc, hscale⟩ := boundary_cutoff_rectangle_integral_scaling center rho t ht
  have hRint : IntegrableOn center R m0 := hc.mp hs.1
  have hRscale : (∫ w : ℝ × ℝ in R, center w ∂m0) =
      t ^ 3 * ∫ p : ℝ × ℝ, H p ∂m := hscale
  have hG0 : J (G (0, 0)) = J0 := by simp [G, J0]
  let E : ℝ := Real.exp (-J0 / t ^ 2)
  have hWpull : (fun w => W (G w)) = fun w => E * center w := by
    funext w
    dsimp only [W, center, E]
    rw [hG0]
    rw [show -J (G w) / t ^ 2 = -J0 / t ^ 2 + -((J (G w) - J0) / t ^ 2) from by ring,
      Real.exp_add]
    ring
  have hWpullint : IntegrableOn (fun w => W (G w)) R m0 := by
    rw [hWpull]
    exact hRint.const_mul E
  have himage : G '' R = V := boundary_rate_chart_rectangle_image a0 level rho
  have hchart :
      (IntegrableOn W (G '' R) m0 ↔ IntegrableOn (fun w => W (G w)) R m0) ∧
      (∫ w : ℝ × ℝ in G '' R, W w ∂m0) = ∫ w : ℝ × ℝ in R, W (G w) ∂m0 :=
    (boundary_rate_chart_measure_and_integral a0 level).2.2 R W
  rw [himage] at hchart
  have hWorig : IntegrableOn W V m0 := hchart.1.mpr hWpullint
  have hWint : (∫ w : ℝ × ℝ in V, W w ∂m0) =
      E * (t ^ 3 * ∫ p : ℝ × ℝ, H p ∂m) := by
    calc
      _ = ∫ w : ℝ × ℝ in R, W (G w) ∂m0 := hchart.2
      _ = E * ∫ w : ℝ × ℝ in R, center w ∂m0 := by rw [hWpull, integral_const_mul]
      _ = _ := congrArg (fun x : ℝ => E * x) hRscale
  let factor : ℝ := t * E / (2 * Real.pi)
  have hfactor : 0 < factor := div_pos (mul_pos ht (Real.exp_pos _))
    (mul_pos (by norm_num) Real.pi_pos)
  have hmain : t * E * (C0 / (2 * Real.pi)) = factor * C0 := by dsimp [factor]; ring
  have hLn : (1 / (2 * Real.pi * t ^ 2)) * (∫ w : ℝ × ℝ in V, W w ∂m0) =
      factor * (∫ p : ℝ × ℝ, H p ∂m) := by
    rw [hWint]
    dsimp only [factor]
    field_simp [ht.ne', Real.pi_ne_zero] <;> ring
  refine ⟨hWorig, ?_, ?_⟩
  · change 0 < t * E * (C0 / (2 * Real.pi))
    rw [hmain]
    exact mul_pos hfactor hC0
  · change |((1 / (2 * Real.pi * t ^ 2)) * (∫ w : ℝ × ℝ in V, W w ∂m0)) /
      (t * E * (C0 / (2 * Real.pi))) - 1| ≤ C * t
    rw [hLn, hmain]
    have hratio : factor * (∫ p : ℝ × ℝ, H p ∂m) / (factor * C0) =
        (∫ p : ℝ × ℝ, H p ∂m) / C0 := by
      field_simp [hfactor.ne', hC0.ne']
    rw [hratio]
    exact hs.2

end
end Shao.OQ3
