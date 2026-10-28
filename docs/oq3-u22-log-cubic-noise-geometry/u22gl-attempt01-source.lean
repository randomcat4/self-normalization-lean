import Shao.OQ3.GaussianSmoothedFourierTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Shao.OQ3
open MeasureTheory Filter
open scoped NNReal Topology
noncomputable section

theorem log_square_gaussian_six_power_le_rpow
    (a c x : ℝ) (ha : 0 ≤ a) (hc : 0 < c) (hx : 0 < x)
    (hlogone : 1 ≤ Real.log x)
    (hloglarge : 4 * (a + 6 + |Real.log c|) ≤ Real.log x) :
    c * x ^ 6 * Real.exp (-(Real.log x) ^ 2 / 4) ≤ Real.rpow x (-a) := by
  have hL : 0 ≤ Real.log x := by linarith
  have hp := mul_nonneg (sub_nonneg.mpr hloglarge) hL
  have hq := mul_nonneg (abs_nonneg (Real.log c)) (sub_nonneg.mpr hlogone)
  have hcL : Real.log c ≤ |Real.log c| := le_abs_self _
  calc
    c * x ^ 6 * Real.exp (-(Real.log x) ^ 2 / 4) =
        (Real.exp (Real.log c) * (Real.exp (Real.log x)) ^ 6) *
          Real.exp (-(Real.log x) ^ 2 / 4) := by
      rw [Real.exp_log hc, Real.exp_log hx]
    _ = Real.exp (Real.log c + 6 * Real.log x - (Real.log x) ^ 2 / 4) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp ((-a) * Real.log x) := Real.exp_le_exp.mpr (by nlinarith)
    _ = Real.rpow x (-a) := by rw [Real.rpow_def_of_pos hx]; congr 1; ring

theorem cubic_gaussian_smoothed_inverse_window_tail_bound
    (nu : Measure (ℝ × ℝ)) [IsProbabilityMeasure nu]
    (n : ℕ) (hn : 1 ≤ n) (x : ℝ × ℝ) :
    let b : ℝ := 1 / (2 * (n : ℝ) ^ 6)
    let R : ℝ := (n : ℝ) ^ 3 * Real.log (n : ℝ)
    let v : ℝ≥0 := Real.toNNReal (2 * b)
    let gamma : Measure (ℝ × ℝ) :=
      (ProbabilityTheory.gaussianReal 0 v).prod (ProbabilityTheory.gaussianReal 0 v)
    let rho : Measure (ℝ × ℝ) := (nu.prod gamma).map (fun q => q.1 + q.2)
    let tail : Set (ℝ × ℝ) := {z | R ^ 2 ≤ z.1 ^ 2 + z.2 ^ 2}
    let f : (ℝ × ℝ) → ℂ := fun z =>
      Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
        ∫ w : ℝ × ℝ, Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho
    Integrable f ∧ IntegrableOn f tail ∧
      ‖∫ z in tail, f z‖ ≤
        (4 * Real.pi) * (n : ℝ) ^ 6 * Real.exp (-(Real.log (n : ℝ)) ^ 2 / 4) := by
  intro b R v gamma rho tail f
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnp : (0 : ℝ) < (n : ℝ) := by linarith
  have hb : 0 < b := by dsimp only [b]; positivity
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact mul_nonneg (pow_nonneg hnp.le 3) (Real.log_nonneg hn1)
  have hgen := gaussian_smoothed_pair_inverse_tail_bound nu b R hb hR x
  change Integrable f ∧ IntegrableOn f tail ∧
    ‖∫ z in tail, f z‖ ≤ (2 * Real.pi / b) * Real.exp (-b * R ^ 2 / 2) at hgen
  have hpref : 2 * Real.pi / b = (4 * Real.pi) * (n : ℝ) ^ 6 := by
    dsimp only [b]
    field_simp
    ring
  have harg : -b * R ^ 2 / 2 = -(Real.log (n : ℝ)) ^ 2 / 4 := by
    dsimp only [b, R]
    field_simp [hnp.ne']
    ring
  rw [hpref, harg] at hgen
  exact hgen

theorem eventually_cubic_gaussian_smoothed_inverse_window_tail
    (a : ℝ) (ha : 0 ≤ a) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ (nu : Measure (ℝ × ℝ)) (_hnu : IsProbabilityMeasure nu) (x : ℝ × ℝ),
      let b : ℝ := 1 / (2 * (n : ℝ) ^ 6)
      let R : ℝ := (n : ℝ) ^ 3 * Real.log (n : ℝ)
      let v : ℝ≥0 := Real.toNNReal (2 * b)
      let gamma : Measure (ℝ × ℝ) :=
        (ProbabilityTheory.gaussianReal 0 v).prod (ProbabilityTheory.gaussianReal 0 v)
      let rho : Measure (ℝ × ℝ) := (nu.prod gamma).map (fun q => q.1 + q.2)
      let tail : Set (ℝ × ℝ) := {z | R ^ 2 ≤ z.1 ^ 2 + z.2 ^ 2}
      let f : (ℝ × ℝ) → ℂ := fun z =>
        Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
          ∫ w : ℝ × ℝ, Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho
      Integrable f ∧ IntegrableOn f tail ∧
        ‖∫ z in tail, f z‖ ≤ Real.rpow (n : ℝ) (-a) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ 1 ≤ Real.log (n : ℝ) ∧
      4 * (a + 6 + |Real.log (4 * Real.pi)|) ≤ Real.log (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1,
      hlog.eventually (eventually_ge_atTop 1),
      hlog.eventually (eventually_ge_atTop (4 * (a + 6 + |Real.log (4 * Real.pi)|)))]
      with n hn hl1 hl2
    exact ⟨hn, hl1, hl2⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, (hN N le_rfl).1, ?_⟩
  intro n hn nu hnu x
  letI : IsProbabilityMeasure nu := hnu
  intro b R v gamma rho tail f
  have hn1 : 1 ≤ n := (hN n hn).1
  have hnp : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hi := cubic_gaussian_smoothed_inverse_window_tail_bound nu n hn1 x
  change Integrable f ∧ IntegrableOn f tail ∧
    ‖∫ z in tail, f z‖ ≤
      (4 * Real.pi) * (n : ℝ) ^ 6 * Real.exp (-(Real.log (n : ℝ)) ^ 2 / 4) at hi
  have hb := log_square_gaussian_six_power_le_rpow a (4 * Real.pi) (n : ℝ)
    ha (by positivity) hnp (hN n hn).2.1 (hN n hn).2.2
  exact ⟨hi.1, hi.2.1, hi.2.2.trans hb⟩

end
end Shao.OQ3
