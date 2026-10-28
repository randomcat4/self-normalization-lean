import Shao.OQ3.ActualMeanChartCompactTaylor
import Shao.OQ3.BoundaryLaplaceExponential

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

set_option maxHeartbeats 2000000 in
theorem weighted_exponential_mesh_relative_error
    (r C D amin amax u v a b : ℝ)
    (hr : 1 ≤ r) (hC : 0 ≤ C) (hD : 0 ≤ D) (hamin : 0 < amin)
    (hvmin : amin ≤ v) (hvmax : v ≤ amax)
    (hamplitude : |u - v| ≤ C / r) (hexponent : |a - b| ≤ D / r) :
    |u * Real.exp (-a) - v * Real.exp (-b)| ≤
      (((C + amax * D) * Real.exp D / amin) / r) * (v * Real.exp (-b)) := by
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hvpos : 0 < v := hamin.trans_le hvmin
  have hmax : 0 ≤ amax := hvpos.le.trans hvmax
  have hDr : 0 ≤ D / r := div_nonneg hD hrpos.le
  have hDrLe : D / r ≤ D := div_le_self hD hr
  have ha : b - D / r ≤ a := by linarith [(abs_le.mp hexponent).1]
  have hb : b - D / r ≤ b := by linarith
  have hcomp := abs_weighted_exp_neg_sub_le a b u v (b - D / r)
    (D / r) (C / r) ha hb hexponent hamplitude
  have hNum : 0 ≤ C + amax * D := add_nonneg hC (mul_nonneg hmax hD)
  have hCoef : C / r + |v| * (D / r) ≤ (C + amax * D) / r := by
    rw [abs_of_pos hvpos]
    calc
      _ = (C + v * D) / r := by ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (add_le_add_left (mul_le_mul_of_nonneg_right hvmax hD) C) hrpos.le
  have hExp : Real.exp (-(b - D / r)) ≤ Real.exp D * Real.exp (-b) := by
    calc
      _ = Real.exp (D / r) * Real.exp (-b) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr hDrLe) (Real.exp_pos _).le
  calc
    |u * Real.exp (-a) - v * Real.exp (-b)|
        ≤ (C / r + |v| * (D / r)) * Real.exp (-(b - D / r)) := hcomp
    _ ≤ ((C + amax * D) / r) * (Real.exp D * Real.exp (-b)) :=
      mul_le_mul hCoef hExp (Real.exp_pos _).le (div_nonneg hNum hrpos.le)
    _ = (((C + amax * D) * Real.exp D / amin) / r) * (amin * Real.exp (-b)) := by
      field_simp [hamin.ne', hrpos.ne']
      <;> ring
    _ ≤ (((C + amax * D) * Real.exp D / amin) / r) * (v * Real.exp (-b)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hvmin (Real.exp_pos _).le)
        (div_nonneg (div_nonneg (mul_nonneg hNum (Real.exp_pos _).le) hamin.le) hrpos.le)

set_option maxHeartbeats 2000000 in
theorem actual_mean_chart_uniform_gaussian_kernel_comparison
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
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ y ∈ V, ∀ w ∈ V,
        ‖w - y‖ ≤ 1 / (n : ℝ) → ∀ J0 : ℝ,
          |A y * Real.exp (-(n : ℝ) * (J y +
              ((e.symm y).1 * (w - y).1 + (e.symm y).2 * (w - y).2) +
                Q y (w - y) / 2 - J0)) -
            A w * Real.exp (-(n : ℝ) * (J w - J0))| ≤
              (C / (n : ℝ)) * (A w * Real.exp (-(n : ℝ) * (J w - J0))) := by
  intro nu D K J A Q
  obtain ⟨delta, C0, amin, amax, hdelta, hC0, hamin, hamax, hAmplitude,
      hQuadratic, hNear⟩ :=
    actual_mean_chart_compact_taylor_amplitude mu e he hsource V hCompact hTarget hPositive
  let D0 : ℝ := 3 * C0 / 2
  let C : ℝ := (C0 + amax * D0) * Real.exp D0 / amin
  have hD0 : 0 < D0 := by dsimp [D0]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (1 / delta))
  have hNr : 1 ≤ (N : ℝ) := (le_max_left 1 (1 / delta)).trans hN.le
  have hNnat : 1 ≤ N := by exact_mod_cast hNr
  refine ⟨C, hC, N, hNnat, ?_⟩
  intro n hn y hy w hw hMesh J0
  have hnR : 1 ≤ (n : ℝ) := hNr.trans (by exact_mod_cast hn)
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hnR
  have hSmall : 1 / (n : ℝ) ≤ delta := by
    apply (div_le_iff₀ hnpos).mpr
    have hh : 1 / delta < (n : ℝ) :=
      lt_of_lt_of_le ((le_max_right 1 (1 / delta)).trans_lt hN)
        (by exact_mod_cast hn)
    have hh' := (div_lt_iff₀ hdelta).mp hh
    nlinarith
  obtain ⟨_, _, hRemainder, hAmp⟩ := hNear y hy w (hMesh.trans hSmall)
  let ell : ℝ := (e.symm y).1 * (w - y).1 + (e.symm y).2 * (w - y).2
  let q : ℝ := Q y (w - y)
  let rem : ℝ := J w - J y - ell
  let a : ℝ := (n : ℝ) * (J y + ell + q / 2 - J0)
  let b : ℝ := (n : ℝ) * (J w - J0)
  have hRem : |rem| ≤ C0 * ‖w - y‖ ^ 2 := hRemainder
  have hQ : |q| ≤ C0 * ‖w - y‖ ^ 2 := hQuadratic y hy (w - y)
  have hInner : |q / 2 - rem| ≤ D0 * ‖w - y‖ ^ 2 := by
    calc
      _ ≤ |q / 2| + |rem| := abs_sub_le _ _
      _ = |q| / 2 + |rem| := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (C0 * ‖w - y‖ ^ 2) / 2 + C0 * ‖w - y‖ ^ 2 :=
        add_le_add (div_le_div_of_nonneg_right hQ (by norm_num)) hRem
      _ = D0 * ‖w - y‖ ^ 2 := by dsimp [D0]; ring
  have hSquare : ‖w - y‖ ^ 2 ≤ (1 / (n : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hMesh 2
  have hAB : |a - b| ≤ D0 / (n : ℝ) := by
    have hEq : a - b = (n : ℝ) * (q / 2 - rem) := by dsimp [a, b, rem]; ring
    rw [hEq, abs_mul, abs_of_pos hnpos]
    calc
      _ ≤ (n : ℝ) * (D0 * ‖w - y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hInner hnpos.le
      _ ≤ (n : ℝ) * (D0 * (1 / (n : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSquare hD0.le) hnpos.le
      _ = D0 / (n : ℝ) := by
        field_simp [hnpos.ne']
        <;> ring
  have hAmpMesh : |A y - A w| ≤ C0 / (n : ℝ) := by
    rw [abs_sub_comm]
    calc
      _ ≤ C0 * ‖w - y‖ := hAmp
      _ ≤ C0 * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_left hMesh hC0.le
      _ = _ := by ring
  have h := weighted_exponential_mesh_relative_error (n : ℝ) C0 D0 amin amax
    (A y) (A w) a b hnR hC0.le hD0.le hamin (hAmplitude w hw).1
      (hAmplitude w hw).2 hAmpMesh hAB
  simpa only [a, b, ell, q, C, neg_mul] using h

end
end Shao.OQ3
