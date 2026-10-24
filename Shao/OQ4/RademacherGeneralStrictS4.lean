import Shao.OQ4.RademacherRealStrictBoundary
import Shao.OQ4.RademacherBrownianBoundaryShift
import Shao.OQ4.RademacherS4Assembly
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
universe uB

namespace Shao.OQ4.RademacherGeneralStrictS4

def delta (h : ℝ) : ℝ := (Nat.ceil h : ℝ) - h

def correction (n : ℕ) (h : ℝ) : ℝ :=
  (Real.pi ^ 2 / 4) * ((n : ℝ) / h ^ 3) * delta h

def Q {ΩB : Type uB} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (n : ℕ) (h : ℝ) : ℝ :=
  RademacherStrictCube.strictP n h /
    Shao.Probability.BrownianSup.probability B P hB
      (h / Real.sqrt (n : ℝ))

private theorem center_remainder_bound (n : ℕ) (h a : ℝ)
    (hh : 2 ≤ h) (ha : h - 1 ≤ a) (hah : a < h) :
    |(Real.pi ^ 2 / 4) * ((n : ℝ) / a ^ 3) +
      (Real.pi ^ 2 / 8) * ((n : ℝ) / h ^ 2 - (n : ℝ) / a ^ 2) -
      (Real.pi ^ 2 / 4) * ((n : ℝ) / h ^ 3) * (a + 1 - h)| ≤
    (60 * (Real.pi ^ 2 / 8)) * ((n : ℝ) / h ^ 4)
 := by
  have hh0 : 0 < h := by linarith
  have ha0 : 0 < a := by linarith
  have h2a : h ≤ 2 * a := by linarith
  have hd0 : 0 ≤ h - a := by linarith
  have hd1 : h - a ≤ 1 := by linarith
  have hc2 : h ^ 2 ≤ 4 * a ^ 2 := by nlinarith
  have hc3 : h ^ 3 ≤ 8 * a ^ 3 := by
    calc
      h ^ 3 ≤ (2 * a) ^ 3 := by gcongr
      _ = 8 * a ^ 3 := by ring
  have hsum : h ^ 2 + h * a + a ^ 2 ≤ 3 * h ^ 2 := by
    nlinarith [mul_nonneg hh0.le hd0, mul_nonneg hd0 (by linarith : 0 ≤ h + a)]
  have hA : |1 / a ^ 3 - 1 / h ^ 3| ≤ 24 / h ^ 4 := by
    have heq : 1 / a ^ 3 - 1 / h ^ 3 =
        (h - a) * (h ^ 2 + h * a + a ^ 2) / (a ^ 3 * h ^ 3) := by
      field_simp [ha0.ne', hh0.ne'] <;> ring
    rw [heq, abs_of_nonneg (div_nonneg (mul_nonneg hd0 (by positivity))
      (by positivity))]
    calc
      (h - a) * (h ^ 2 + h * a + a ^ 2) / (a ^ 3 * h ^ 3) ≤
          (3 * h ^ 2) / (a ^ 3 * h ^ 3) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact (mul_le_of_le_one_left (by positivity) hd1).trans hsum
      _ = 3 / (a ^ 3 * h) := by field_simp [ha0.ne', hh0.ne'] <;> ring
      _ ≤ 24 / h ^ 4 := by
        apply (div_le_div_iff₀ (by positivity : 0 < a ^ 3 * h)
          (by positivity : 0 < h ^ 4)).2
        nlinarith [mul_le_mul_of_nonneg_right hc3 hh0.le]
  have hB : |1 / h ^ 2 - 1 / a ^ 2 + 2 * (h - a) / h ^ 3| ≤
      12 / h ^ 4 := by
    have heq : 1 / h ^ 2 - 1 / a ^ 2 + 2 * (h - a) / h ^ 3 =
        -((h - a) ^ 2 * (h + 2 * a) / (h ^ 3 * a ^ 2)) := by
      field_simp [ha0.ne', hh0.ne'] <;> ring
    rw [heq, abs_neg, abs_of_nonneg (by positivity)]
    have hd2 : (h - a) ^ 2 ≤ 1 := by nlinarith
    calc
      (h - a) ^ 2 * (h + 2 * a) / (h ^ 3 * a ^ 2) ≤
          (3 * h) / (h ^ 3 * a ^ 2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact (mul_le_of_le_one_left (by positivity) hd2).trans (by linarith)
      _ = 3 / (h ^ 2 * a ^ 2) := by field_simp [ha0.ne', hh0.ne'] <;> ring
      _ ≤ 12 / h ^ 4 := by
        apply (div_le_div_iff₀ (by positivity : 0 < h ^ 2 * a ^ 2)
          (by positivity : 0 < h ^ 4)).2
        nlinarith [mul_le_mul_of_nonneg_right hc2 (sq_nonneg h)]
  have hsplit :
      (Real.pi ^ 2 / 4) * ((n : ℝ) / a ^ 3) +
        (Real.pi ^ 2 / 8) * ((n : ℝ) / h ^ 2 - (n : ℝ) / a ^ 2) -
        (Real.pi ^ 2 / 4) * ((n : ℝ) / h ^ 3) * (a + 1 - h) =
      (Real.pi ^ 2 / 8) * (n : ℝ) *
        (2 * (1 / a ^ 3 - 1 / h ^ 3) +
          (1 / h ^ 2 - 1 / a ^ 2 + 2 * (h - a) / h ^ 3)) := by ring
  rw [hsplit, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (Real.pi ^ 2 / 8) * (n : ℝ))]
  calc
    (Real.pi ^ 2 / 8) * (n : ℝ) *
        |2 * (1 / a ^ 3 - 1 / h ^ 3) +
          (1 / h ^ 2 - 1 / a ^ 2 + 2 * (h - a) / h ^ 3)| ≤
      (Real.pi ^ 2 / 8) * (n : ℝ) *
        (2 * (24 / h ^ 4) + 12 / h ^ 4) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (abs_add_le _ _).trans (add_le_add
        (by simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 2)) hB)
    _ = (60 * (Real.pi ^ 2 / 8)) * ((n : ℝ) / h ^ 4) := by ring

theorem strict_S4_EVENTUAL
    {ΩB : Type uB} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (n_ : ℕ → ℕ) (h_ : ℕ → ℝ)
    (hh : Tendsto h_ atTop atTop)
    (hscale2 : Tendsto
      (fun k : ℕ => (n_ k : ℝ) / (h_ k) ^ 2) atTop atTop)
    (hscale3 : ∃ M : ℝ, 0 < M ∧
      ∃ K_M : ℕ, ∀ k : ℕ, K_M ≤ k →
        (n_ k : ℝ) / (h_ k) ^ 3 ≤ M) :
    (∀ᶠ k : ℕ in atTop,
      0 < RademacherStrictCube.strictP (n_ k) (h_ k) ∧
      0 < Shao.Probability.BrownianSup.probability B P hB
        (h_ k / Real.sqrt (n_ k : ℝ)) ∧
      0 < Q B P hB (n_ k) (h_ k)) ∧
    Tendsto (fun k : ℕ =>
      Real.log (Q B P hB (n_ k) (h_ k)) -
        correction (n_ k) (h_ k)) atTop (𝓝 (0 : ℝ)) ∧
    Tendsto (fun k : ℕ =>
      Q B P hB (n_ k) (h_ k) /
        Real.exp (correction (n_ k) (h_ k))) atTop (𝓝 (1 : ℝ))
 := by
  classical
  let m : ℕ → ℕ := fun k => Nat.ceil (h_ k) - 1
  let a : ℕ → ℝ := fun k => (m k : ℝ)
  let b : ℝ → ℝ := Shao.Probability.BrownianSup.probability B P hB
  let x : ℕ → ℝ := fun k => h_ k / Real.sqrt (n_ k : ℝ)
  let y : ℕ → ℝ := fun k => a k / Real.sqrt (n_ k : ℝ)
  have hgeom : ∀ᶠ k : ℕ in atTop,
      2 ≤ h_ k ∧ h_ k - 1 ≤ a k ∧ a k < h_ k ∧
      h_ k ≤ 2 * a k ∧ 1 ≤ m k ∧
      RademacherStrictCube.strictP (n_ k) (h_ k) =
        RademacherS4Assembly.p (n_ k) (a k) ∧
      delta (h_ k) = a k + 1 - h_ k := by
    filter_upwards [hh.eventually_ge_atTop (2 : ℝ)] with k hk
    have hb := RademacherRealStrictBoundary.ceil_boundary_bridge
      (n_ k) (h_ k) (by linarith)
    have hcast : a k = (Nat.ceil (h_ k) : ℝ) - 1 := hb.2.1
    have ha : h_ k - 1 ≤ a k := by linarith [hb.2.2.2.1]
    have hlt : a k < h_ k := hb.2.2.1
    have hm : 1 ≤ m k := by
      have hreal : (1 : ℝ) ≤ (m k : ℝ) := by change 1 ≤ a k; linarith
      exact_mod_cast hreal
    refine ⟨hk, ha, hlt, by linarith, hm, ?_, ?_⟩
    · exact hb.2.2.2.2.2.2
    · dsimp only [delta]; linarith
  have haInf : Tendsto a atTop atTop := by
    apply tendsto_atTop.2
    intro c
    filter_upwards [hgeom, hh.eventually_ge_atTop (c + 1)] with k hg hk
    linarith [hg.2.1]
  have hcell : ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      1 ≤ m k ∧ (m k : ℝ) ≤ a k ∧ a k < (m k : ℝ) + 1 := by
    obtain ⟨K, hK⟩ := eventually_atTop.1 hgeom
    exact ⟨K, fun k hk => ⟨(hK k hk).2.2.2.2.1, le_rfl, by dsimp only [a]; linarith⟩⟩
  have hscale2a : Tendsto
      (fun k : ℕ => RademacherS4Assembly.N (n_ k) / (a k) ^ 2) atTop atTop := by
    apply tendsto_atTop.2
    intro c
    filter_upwards [hgeom, hscale2.eventually_ge_atTop c] with k hg hk
    have ha0 : 0 < a k := by linarith [hg.1, hg.2.1]
    have hh0 : 0 < h_ k := by linarith [hg.1]
    have hsq : (a k) ^ 2 ≤ (h_ k) ^ 2 := by nlinarith [hg.2.2.1]
    exact hk.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (pow_pos ha0 2) hsq)
  obtain ⟨M, hM, KM, hKM⟩ := hscale3
  have hscale3a : ∃ M' : ℝ, 0 < M' ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      RademacherS4Assembly.scale3 (n_ k) (a k) ≤ M' := by
    refine ⟨8 * M, by positivity, ?_⟩
    obtain ⟨K, hK⟩ := eventually_atTop.1 (hgeom.and (eventually_ge_atTop KM))
    refine ⟨K, fun k hk => ?_⟩
    rcases hK k hk with ⟨hg, hkM⟩
    have ha0 : 0 < a k := by linarith [hg.1, hg.2.1]
    have hh0 : 0 < h_ k := by linarith [hg.1]
    have hc : (h_ k) ^ 3 ≤ 8 * (a k) ^ 3 := by
      calc
        (h_ k) ^ 3 ≤ (2 * a k) ^ 3 := by gcongr; exact hg.2.2.2.1
        _ = 8 * (a k) ^ 3 := by ring
    change (n_ k : ℝ) / (a k) ^ 3 ≤ 8 * M
    calc
      (n_ k : ℝ) / (a k) ^ 3 ≤ (n_ k : ℝ) / ((h_ k) ^ 3 / 8) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) (by linarith)
      _ = 8 * ((n_ k : ℝ) / (h_ k) ^ 3) := by ring
      _ ≤ 8 * M := mul_le_mul_of_nonneg_left (hKM k hkM) (by norm_num)
  have hs := RademacherS4Assembly.S4_EVENTUAL B P hB m n_ a
    hcell haInf hscale2a hscale3a
  rcases hs with ⟨_, _, _, _, hy, _, _, hwlog, _, Kt, Kp, _, htime, hprob, _⟩
  change Tendsto y atTop (𝓝 (0 : ℝ)) at hy
  have hlegal : ∀ᶠ k : ℕ in atTop,
      0 < a k ∧ 0 < Real.sqrt (n_ k : ℝ) ∧
      (Real.sqrt (n_ k : ℝ)) ^ 2 = (n_ k : ℝ) ∧
      0 < RademacherS4Assembly.p (n_ k) (a k) ∧
      0 < b (y k) ∧ 0 < RademacherS4Assembly.Q B P hB (n_ k) (a k) := by
    filter_upwards [eventually_ge_atTop Kt, eventually_ge_atTop Kp] with k hkt hkp
    rcases htime k hkt with ⟨_, _, _, _, _, hsqrt, hsquare, _, hapos, _, _⟩
    rcases (hprob k hkp).1 with ⟨_, _, _, _, _, _, _, _, _, hp, _, _, hb, _, _, _, hq, _⟩
    exact ⟨hapos, hsqrt, hsquare, hp, hb, hq⟩
  have hxpos : ∀ᶠ k : ℕ in atTop, 0 < x k := by
    filter_upwards [hgeom, hlegal] with k hg hl
    exact div_pos (by linarith [hg.1]) hl.2.1
  have hypos : ∀ᶠ k : ℕ in atTop, 0 < y k := by
    filter_upwards [hlegal] with k hl
    exact div_pos hl.1 hl.2.1
  have hx : Tendsto x atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero' (hxpos.mono fun _ h => h.le) ?_
      (by simpa only [mul_zero] using hy.const_mul 2)
    filter_upwards [hgeom, hlegal] with k hg hl
    change h_ k / Real.sqrt (n_ k : ℝ) ≤ 2 * (a k / Real.sqrt (n_ k : ℝ))
    calc
      h_ k / Real.sqrt (n_ k : ℝ) ≤ (2 * a k) / Real.sqrt (n_ k : ℝ) :=
        div_le_div_of_nonneg_right hg.2.2.2.1 hl.2.1.le
      _ = 2 * (a k / Real.sqrt (n_ k : ℝ)) := by ring
  have hshift := RademacherBrownianBoundaryShift.actual_brownian_boundary_shift
    B P hB x y hx hy hxpos hypos
  have hpositive : ∀ᶠ k : ℕ in atTop,
      0 < RademacherStrictCube.strictP (n_ k) (h_ k) ∧
      0 < b (x k) ∧ 0 < Q B P hB (n_ k) (h_ k) := by
    filter_upwards [hgeom, hlegal, hshift.1] with k hg hl hb
    have hp : 0 < RademacherStrictCube.strictP (n_ k) (h_ k) :=
      hg.2.2.2.2.2.1 ▸ hl.2.2.2.1
    exact ⟨hp, hb.1, div_pos hp hb.1⟩
  have hweak : Tendsto (fun k : ℕ =>
      Real.log (RademacherS4Assembly.Q B P hB (n_ k) (a k)) -
        (Real.pi ^ 2 / 4) * ((n_ k : ℝ) / (a k) ^ 3)) atTop (𝓝 (0 : ℝ)) := by
    have hw (k : ℕ) : RademacherS4Assembly.w (m k) (n_ k) (a k) =
        (Real.pi ^ 2 / 4) * ((n_ k : ℝ) / (a k) ^ 3) := by
      change (Real.pi ^ 2 / 4) * ((n_ k : ℝ) / (a k) ^ 3) *
        (((m k : ℝ) + 1) - a k) = _
      dsimp only [a]
      ring
    simpa only [hw] using hwlog
  have hblog : Tendsto (fun k : ℕ =>
      Real.log (b (y k) / b (x k)) - (Real.pi ^ 2 / 8) *
        ((n_ k : ℝ) / (h_ k) ^ 2 - (n_ k : ℝ) / (a k) ^ 2))
      atTop (𝓝 (0 : ℝ)) := by
    apply hshift.2.1.congr'
    filter_upwards [hgeom, hlegal] with k hg hl
    have hh0 : h_ k ≠ 0 := by linarith [hg.1]
    have ha0 : a k ≠ 0 := hl.1.ne'
    dsimp only [x, y, b]
    have heq (z : ℝ) (hz : z ≠ 0) :
        1 / (z / Real.sqrt (n_ k : ℝ)) ^ 2 = (n_ k : ℝ) / z ^ 2 := by
      rw [div_pow, one_div_div, hl.2.2.1]
    rw [heq _ hh0, heq _ ha0]
  have hMlim : Tendsto (fun k : ℕ => M / h_ k) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, div_eq_mul_inv, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hh).const_mul M
  have hfour : Tendsto (fun k : ℕ => (n_ k : ℝ) / (h_ k) ^ 4)
      atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero' ?_ ?_ hMlim
    · exact Eventually.of_forall fun k => div_nonneg (Nat.cast_nonneg _) (by positivity)
    · filter_upwards [hgeom, eventually_ge_atTop KM] with k hg hk
      have hh0 : 0 < h_ k := by linarith [hg.1]
      calc
        (n_ k : ℝ) / (h_ k) ^ 4 = ((n_ k : ℝ) / (h_ k) ^ 3) / h_ k := by ring
        _ ≤ M / h_ k := div_le_div_of_nonneg_right (hKM k hk) hh0.le
  let R : ℕ → ℝ := fun k =>
    (Real.pi ^ 2 / 4) * ((n_ k : ℝ) / (a k) ^ 3) +
      (Real.pi ^ 2 / 8) * ((n_ k : ℝ) / (h_ k) ^ 2 - (n_ k : ℝ) / (a k) ^ 2) -
      correction (n_ k) (h_ k)
  have hR : Tendsto R atTop (𝓝 (0 : ℝ)) := by
    apply (tendsto_zero_iff_abs_tendsto_zero R).2
    apply squeeze_zero' (Eventually.of_forall fun k => abs_nonneg (R k)) ?_
      (by simpa only [mul_zero] using hfour.const_mul (60 * (Real.pi ^ 2 / 8)))
    filter_upwards [hgeom] with k hg
    simpa only [R, correction, hg.2.2.2.2.2.2] using
      center_remainder_bound (n_ k) (h_ k) (a k) hg.1 hg.2.1 hg.2.2.1
  have hlog : Tendsto (fun k : ℕ =>
      Real.log (Q B P hB (n_ k) (h_ k)) - correction (n_ k) (h_ k))
      atTop (𝓝 (0 : ℝ)) := by
    have hsum := (hweak.add hblog).add hR
    have heq : (fun k : ℕ =>
        (Real.log (RademacherS4Assembly.Q B P hB (n_ k) (a k)) -
          (Real.pi ^ 2 / 4) * ((n_ k : ℝ) / (a k) ^ 3)) +
        (Real.log (b (y k) / b (x k)) - (Real.pi ^ 2 / 8) *
          ((n_ k : ℝ) / (h_ k) ^ 2 - (n_ k : ℝ) / (a k) ^ 2)) + R k) =ᶠ[atTop]
        (fun k : ℕ => Real.log (Q B P hB (n_ k) (h_ k)) -
          correction (n_ k) (h_ k)) := by
      filter_upwards [hgeom, hlegal, hshift.1] with k hg hl hb
      have hfactor : Q B P hB (n_ k) (h_ k) =
          RademacherS4Assembly.Q B P hB (n_ k) (a k) * (b (y k) / b (x k)) := by
        change RademacherStrictCube.strictP (n_ k) (h_ k) / b (x k) =
          (RademacherS4Assembly.p (n_ k) (a k) / b (y k)) * (b (y k) / b (x k))
        rw [hg.2.2.2.2.2.1]
        have hbx : b (x k) ≠ 0 := hb.1.ne'
        have hby : b (y k) ≠ 0 := hb.2.1.ne'
        field_simp [hbx, hby]
      rw [hfactor, Real.log_mul hl.2.2.2.2.2.ne' hb.2.2.ne']
      dsimp only [R]
      ring
    simpa only [zero_add] using hsum.congr' heq
  have hexp := (Real.continuous_exp.tendsto (0 : ℝ)).comp hlog
  have heqexp : (fun k : ℕ =>
      Real.exp (Real.log (Q B P hB (n_ k) (h_ k)) - correction (n_ k) (h_ k))) =ᶠ[atTop]
      (fun k : ℕ => Q B P hB (n_ k) (h_ k) / Real.exp (correction (n_ k) (h_ k))) := by
    filter_upwards [hpositive] with k hk
    rw [Real.exp_sub, Real.exp_log hk.2.2]
  refine ⟨hpositive, hlog, ?_⟩
  simpa only [Real.exp_zero, Function.comp_def] using hexp.congr' heqexp

end Shao.OQ4.RademacherGeneralStrictS4
end
