import Shao.OQ3.CompactParabolaGaussianOscillation
import Shao.OQ3.ParabolaCellLogCubicOscillation

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory
open scoped Matrix Topology
noncomputable section

theorem compact_parabola_pair_log_cubic_gaussian_oscillation
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (Theta : Set (ℝ × ℝ))
    (hcompact : IsCompact Theta) (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 < hi)
    (hspec : ∀ p ∈ Theta,
      let D : Matrix (Fin 2) (Fin 2) ℝ :=
        parabolaCovariance (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2))
      ∀ xi eta : ℝ,
        lo * (xi ^ 2 + eta ^ 2) ≤
          xi ^ 2 * D 0 0 + 2 * xi * eta * D 0 1 + eta ^ 2 * D 1 1 ∧
        xi ^ 2 * D 0 0 + 2 * xi * eta * D 0 1 + eta ^ 2 * D 1 1 ≤
          hi * (xi ^ 2 + eta ^ 2))
    (level a0 rho : ℝ) (hrho : 0 ≤ rho) :
    let tilt : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    let D : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p => parabolaCovariance (tilt p)
    let s : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (D p 0 0 * D p 1 1 - (D p 0 1) ^ 2)
    let t : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (D p 0 0 + D p 1 1 + 2 * s p)
    let A : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p =>
      ![![(D p 1 1 + s p) / (s p * t p), -(D p 0 1) / (s p * t p)],
        ![-(D p 0 1) / (s p * t p), (D p 0 0 + s p) / (s p * t p)]]
    ∃ E : Theta → ((ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)),
      (∀ p : Theta, A p * D p * A p = 1 ∧
        (∀ w : ℝ × ℝ, E p w =
          (A p 0 0 * w.1 + A p 0 1 * w.2, A p 1 0 * w.1 + A p 1 1 * w.2)) ∧
        ‖(E p : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 2 * (1 / Real.sqrt lo) ∧
        ‖((E p).symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 4 * hi * (1 / Real.sqrt lo)) ∧
      ∃ M : ℝ, 0 < M ∧ (∀ p : Theta, ‖(p : ℝ × ℝ)‖ ≤ M) ∧
        let U : ℝ := 1 / Real.sqrt lo
        let R0 : ℝ := 2 * U
        let kappa0 : ℝ := (2 * M) * (4 * hi * U)
        let G0 : ℝ := R0 * (1 + 2 * (|a0| + rho) / level ^ 2)
        let Cstar : ℝ := Real.exp (kappa0 * R0) *
          (8 * kappa0 * (R0 + 1) ^ 2 + 768 * (G0 + 1))
        0 < Cstar ∧
        ∀ (p : Theta) (n : ℕ), 2 ≤ n → ∀ (y : ℝ × ℝ) (aL aR qL qR : ℝ),
          y ∈ Set.Icc aL aR ×ˢ Set.Icc qL qR →
          aR - aL ≤ 1 / (n : ℝ) → qR - qL ≤ 1 / (n : ℝ) →
          let h : ℝ := Real.log (n : ℝ) / (n : ℝ) ^ 3
          let cellA : Set (ℝ × ℝ) := (Set.Ioc aL aR ×ˢ Set.Ioc qL qR) ∩
            {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
              0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
          let stdCell : Set (ℝ × ℝ) :=
            (fun w : ℝ × ℝ => Real.sqrt (n : ℝ) • E p (w - y)) '' cellA
          let g : (ℝ × ℝ) → ℝ := fun v => Real.exp (-Real.sqrt (n : ℝ) *
            ((p : ℝ × ℝ).1 * ((E p).symm v).1 +
              (p : ℝ × ℝ).2 * ((E p).symm v).2))
          let Φ : Measure (ℝ × ℝ) :=
            (gaussianReal 0 1).prod (gaussianReal 0 1)
          Integrable (openBallOscillation (stdCell.indicator g) h) Φ ∧
            (∫ z, openBallOscillation (stdCell.indicator g) h z ∂Φ) ≤
              Cstar * Real.log (n : ℝ) / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) := by
  classical
  dsimp only
  let tilt : (ℝ × ℝ) → Measure ℝ := fun p =>
  mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
  let D : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p => parabolaCovariance (tilt p)
  let s : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (D p 0 0 * D p 1 1 - (D p 0 1) ^ 2)
  let t : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (D p 0 0 + D p 1 1 + 2 * s p)
  let A : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p =>
  ![![(D p 1 1 + s p) / (s p * t p), -(D p 0 1) / (s p * t p)],
    ![-(D p 0 1) / (s p * t p), (D p 0 0 + s p) / (s p * t p)]]
  obtain ⟨E, hE, M, hM, hMbound, hCstar, _hold⟩ :=
  compact_parabola_pair_ncube_gaussian_oscillation mu Theta hcompact lo hi hlo hhi hspec
    level a0 rho hrho
  refine ⟨E, hE, M, hM, hMbound, ?_⟩
  let U : ℝ := 1 / Real.sqrt lo
  let R0 : ℝ := 2 * U
  let kappa0 : ℝ := (2 * M) * (4 * hi * U)
  let G0 : ℝ := R0 * (1 + 2 * (|a0| + rho) / level ^ 2)
  let Cstar : ℝ := Real.exp (kappa0 * R0) *
    (8 * kappa0 * (R0 + 1) ^ 2 + 768 * (G0 + 1))
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hR0 : 0 ≤ R0 := by dsimp only [R0]; positivity
  have hkappa0 : 0 ≤ kappa0 := by dsimp only [kappa0]; positivity
  have hfactor : 0 ≤ 1 + 2 * (|a0| + rho) / level ^ 2 := by positivity
  refine ⟨hCstar, ?_⟩
  intro p n hn y aL aR qL qR hy ha hq
  have hb := actual_parabola_cell_log_cubic_gaussian_oscillation_bound
  n hn (p : ℝ × ℝ) (E p) y aL aR qL qR level a0 rho hrho hy ha hq
  let kappa : ℝ := (|(p : ℝ × ℝ).1| + |(p : ℝ × ℝ).2|) *
    ‖((E p).symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖
  let R : ℝ := ‖(E p : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖
  let C : ℝ := Real.exp (kappa * R)
  let G : ℝ := R * (1 + 2 * (|a0| + rho) / level ^ 2)
  have hR : R ≤ R0 := (hE p).2.2.1
  have hInv := (hE p).2.2.2
  have hpcoords : |(p : ℝ × ℝ).1| ≤ M ∧ |(p : ℝ × ℝ).2| ≤ M := by
    have hp := hMbound p
    change max |(p : ℝ × ℝ).1| |(p : ℝ × ℝ).2| ≤ M at hp
    exact ⟨(le_max_left _ _).trans hp, (le_max_right _ _).trans hp⟩
  have hkappa : kappa ≤ kappa0 := by
    apply mul_le_mul (show |(p : ℝ × ℝ).1| + |(p : ℝ × ℝ).2| ≤ 2 * M by
      linarith [hpcoords.1, hpcoords.2]) hInv (norm_nonneg _) (by positivity)
  have hkappa_nonneg : 0 ≤ kappa := by dsimp only [kappa]; positivity
  have hR_nonneg : 0 ≤ R := norm_nonneg _
  have hG : G ≤ G0 := mul_le_mul_of_nonneg_right hR hfactor
  have hG_nonneg : 0 ≤ G := mul_nonneg hR_nonneg hfactor
  have hC : C ≤ Real.exp (kappa0 * R0) :=
    Real.exp_le_exp.mpr (mul_le_mul hkappa hR hR_nonneg hkappa0)
  have hsquare : (R + 1) ^ 2 ≤ (R0 + 1) ^ 2 := by
    apply sq_le_sq.mpr
    rw [abs_of_nonneg (by linarith : 0 ≤ R + 1),
      abs_of_nonneg (by linarith : 0 ≤ R0 + 1)]
    linarith
  have hfirst : 8 * kappa * (R + 1) ^ 2 ≤ 8 * kappa0 * (R0 + 1) ^ 2 :=
    mul_le_mul (mul_le_mul_of_nonneg_left hkappa (by norm_num))
      hsquare (sq_nonneg _) (by positivity)
  have hsecond : 768 * (G + 1) ≤ 768 * (G0 + 1) :=
    mul_le_mul_of_nonneg_left (add_le_add hG le_rfl) (by norm_num)
  have hinner0 : 0 ≤ 8 * kappa * (R + 1) ^ 2 + 768 * (G + 1) := by positivity
  have hcoefficient :
      C * (8 * kappa * (R + 1) ^ 2 + 768 * (G + 1)) ≤ Cstar :=
    mul_le_mul hC (add_le_add hfirst hsecond) hinner0 (Real.exp_pos _).le
  refine ⟨hb.1, le_trans hb.2 ?_⟩
  change C * (8 * kappa * (R + 1) ^ 2 + 768 * (G + 1)) * Real.log (n : ℝ) /
  ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) ≤
  Cstar * Real.log (n : ℝ) / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ))
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right hcoefficient
  exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))

end
end Shao.OQ3
