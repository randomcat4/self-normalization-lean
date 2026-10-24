import Shao.OQ4.RademacherS4Assembly
import Shao.OQ4.RademacherGeneralStrictS4
import Shao.OQ4.RademacherBrownianBoundaryShift
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
universe uB

namespace Shao.OQ4.RademacherCorrectedBrownianBoundary

def weakHeight (h : ℝ) : ℝ := (Nat.floor h : ℝ) + 1

def strictHeight (h : ℝ) : ℝ := (Nat.ceil h : ℝ)

private theorem inverse_square_remainder_bound (n : ℕ) (h d : ℝ)
    (hh : 0 < h) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    |(Real.pi ^ 2 / 8) *
        ((n : ℝ) / h ^ 2 - (n : ℝ) / (h + d) ^ 2) -
      (Real.pi ^ 2 / 4) * ((n : ℝ) / h ^ 3) * d| ≤
    (3 * (Real.pi ^ 2 / 8)) * ((n : ℝ) / h ^ 4) := by
  have hH : 0 < h + d := by linarith
  have hd2 : d ^ 2 ≤ 1 := by nlinarith
  have hratio : h * (3 * h + 2 * d) / (h + d) ^ 2 ≤ 3 := by
    apply (div_le_iff₀ (pow_pos hH 2)).2
    nlinarith [mul_nonneg hh.le hd0, sq_nonneg d]
  have hfactor : 0 ≤ h * (3 * h + 2 * d) / (h + d) ^ 2 := by positivity
  have hbound : d ^ 2 * (h * (3 * h + 2 * d) / (h + d) ^ 2) ≤ 3 :=
    (mul_le_of_le_one_left hfactor hd2).trans hratio
  have heq : (Real.pi ^ 2 / 8) *
        ((n : ℝ) / h ^ 2 - (n : ℝ) / (h + d) ^ 2) -
      (Real.pi ^ 2 / 4) * ((n : ℝ) / h ^ 3) * d =
      -(((Real.pi ^ 2 / 8) * ((n : ℝ) / h ^ 4)) *
        (d ^ 2 * (h * (3 * h + 2 * d) / (h + d) ^ 2))) := by
    field_simp [hh.ne', hH.ne'] <;> ring
  rw [heq, abs_neg, abs_of_nonneg (by positivity)]
  calc
    ((Real.pi ^ 2 / 8) * ((n : ℝ) / h ^ 4)) *
        (d ^ 2 * (h * (3 * h + 2 * d) / (h + d) ^ 2)) ≤
      ((Real.pi ^ 2 / 8) * ((n : ℝ) / h ^ 4)) * 3 :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (3 * (Real.pi ^ 2 / 8)) * ((n : ℝ) / h ^ 4) := by ring

-- Body of the preceding head: proof.md §3, exact identity (2), bound (3).

private theorem corrected_boundary_of_S4
    {ΩB : Type uB} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (n_ : ℕ → ℕ) (h_ H_ A_ : ℕ → ℝ)
    (hh : Tendsto h_ atTop atTop)
    (hscale2 : Tendsto
      (fun k : ℕ => (n_ k : ℝ) / (h_ k) ^ 2) atTop atTop)
    (hscale3 : ∃ M : ℝ, 0 < M ∧
      ∃ K_M : ℕ, ∀ k : ℕ, K_M ≤ k →
        (n_ k : ℝ) / (h_ k) ^ 3 ≤ M)
    (hwall : ∀ᶠ k : ℕ in atTop,
      h_ k ≤ H_ k ∧ H_ k ≤ h_ k + 1)
    (hApos : ∀ᶠ k : ℕ in atTop, 0 < A_ k)
    (hS4 : Tendsto (fun k : ℕ =>
      Real.log (A_ k /
        Shao.Probability.BrownianSup.probability B P hB
          (h_ k / Real.sqrt (n_ k : ℝ))) -
      (Real.pi ^ 2 / 4) * ((n_ k : ℝ) / (h_ k) ^ 3) *
        (H_ k - h_ k)) atTop (𝓝 (0 : ℝ))) :
    (∀ᶠ k : ℕ in atTop,
      0 < A_ k ∧
      0 < Shao.Probability.BrownianSup.probability B P hB
        (H_ k / Real.sqrt (n_ k : ℝ))) ∧
    Tendsto (fun k : ℕ =>
      A_ k / Shao.Probability.BrownianSup.probability B P hB
        (H_ k / Real.sqrt (n_ k : ℝ))) atTop (𝓝 (1 : ℝ)) := by
  let b : ℝ → ℝ := Shao.Probability.BrownianSup.probability B P hB
  let x : ℕ → ℝ := fun k => h_ k / Real.sqrt (n_ k : ℝ)
  let y : ℕ → ℝ := fun k => H_ k / Real.sqrt (n_ k : ℝ)
  let w : ℕ → ℝ := fun k =>
    (Real.pi ^ 2 / 4) * ((n_ k : ℝ) / (h_ k) ^ 3) * (H_ k - h_ k)
  let E : ℕ → ℝ := fun k => (Real.pi ^ 2 / 8) *
    ((n_ k : ℝ) / (h_ k) ^ 2 - (n_ k : ℝ) / (H_ k) ^ 2)
  have hlegal : ∀ᶠ k : ℕ in atTop,
      1 ≤ h_ k ∧ 0 < Real.sqrt (n_ k : ℝ) ∧
      (Real.sqrt (n_ k : ℝ)) ^ 2 = (n_ k : ℝ) := by
    filter_upwards [hh.eventually_ge_atTop (1 : ℝ),
      hscale2.eventually_ge_atTop (1 : ℝ)] with k hk ht
    have hh0 : 0 < h_ k := by linarith
    have hn : 0 < (n_ k : ℝ) := by
      have hsq : (h_ k) ^ 2 ≤ (n_ k : ℝ) := by
        simpa only [one_mul] using (le_div_iff₀ (pow_pos hh0 2)).mp ht
      exact lt_of_lt_of_le (pow_pos hh0 2) hsq
    exact ⟨hk, Real.sqrt_pos.2 hn, Real.sq_sqrt hn.le⟩
  have hxpos : ∀ᶠ k : ℕ in atTop, 0 < x k := by
    filter_upwards [hlegal] with k hk
    exact div_pos (by linarith [hk.1]) hk.2.1
  have hypos : ∀ᶠ k : ℕ in atTop, 0 < y k := by
    filter_upwards [hlegal, hwall] with k hk hw
    exact div_pos (by linarith [hk.1, hw.1]) hk.2.1
  have hx : Tendsto x atTop (𝓝 (0 : ℝ)) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨K, hK⟩ := eventually_atTop.1
      (hlegal.and (hscale2.eventually_ge_atTop (1 / ε ^ 2 + 1)))
    refine ⟨K, fun k hk => ?_⟩
    rcases hK k hk with ⟨hl, ht⟩
    have hh0 : 0 < h_ k := by linarith [hl.1]
    have ht' : 1 / ε ^ 2 < (n_ k : ℝ) / (h_ k) ^ 2 := by linarith
    have hs : (h_ k) ^ 2 < (ε * Real.sqrt (n_ k : ℝ)) ^ 2 := by
      rw [mul_pow, hl.2.2]
      have ht'' := (div_lt_div_iff₀ (pow_pos hε 2) (pow_pos hh0 2)).mp ht'
      simpa only [one_mul, mul_one, mul_comm] using ht''
    have hxlt : x k < ε := by
      apply (div_lt_iff₀ hl.2.1).2
      exact (sq_lt_sq₀ hh0.le (mul_pos hε hl.2.1).le).mp hs
    rw [Real.dist_eq, sub_zero, abs_of_pos (div_pos hh0 hl.2.1)]
    exact hxlt
  have hy : Tendsto y atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero' (hypos.mono fun _ hk => hk.le) ?_
      (by simpa only [mul_zero] using hx.const_mul 2)
    filter_upwards [hlegal, hwall] with k hk hw
    change H_ k / Real.sqrt (n_ k : ℝ) ≤
      2 * (h_ k / Real.sqrt (n_ k : ℝ))
    calc
      H_ k / Real.sqrt (n_ k : ℝ) ≤
          (2 * h_ k) / Real.sqrt (n_ k : ℝ) :=
        div_le_div_of_nonneg_right (by linarith [hk.1, hw.2]) hk.2.1.le
      _ = 2 * (h_ k / Real.sqrt (n_ k : ℝ)) := by ring
  have hshift := RademacherBrownianBoundaryShift.actual_brownian_boundary_shift
    B P hB x y hx hy hxpos hypos
  have hblog : Tendsto (fun k : ℕ => Real.log (b (y k) / b (x k)) - E k)
      atTop (𝓝 (0 : ℝ)) := by
    apply hshift.2.1.congr'
    filter_upwards [hlegal, hwall] with k hk hw
    have heq (z : ℝ) :
        1 / (z / Real.sqrt (n_ k : ℝ)) ^ 2 = (n_ k : ℝ) / z ^ 2 := by
      rw [div_pow, one_div_div, hk.2.2]
    dsimp only [x, y, b, E]
    rw [heq, heq]
  obtain ⟨M, hM, KM, hKM⟩ := hscale3
  have hMlim : Tendsto (fun k : ℕ => M / h_ k) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, div_eq_mul_inv, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hh).const_mul M
  have hfour : Tendsto (fun k : ℕ => (n_ k : ℝ) / (h_ k) ^ 4)
      atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero' ?_ ?_ hMlim
    · exact Eventually.of_forall fun k => div_nonneg (Nat.cast_nonneg _) (by positivity)
    · filter_upwards [hlegal, eventually_ge_atTop KM] with k hk hkm
      have hh0 : 0 < h_ k := by linarith [hk.1]
      calc
        (n_ k : ℝ) / (h_ k) ^ 4 = ((n_ k : ℝ) / (h_ k) ^ 3) / h_ k := by ring
        _ ≤ M / h_ k := div_le_div_of_nonneg_right (hKM k hkm) hh0.le
  have hR : Tendsto (fun k : ℕ => E k - w k) atTop (𝓝 (0 : ℝ)) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).2
    apply squeeze_zero' (Eventually.of_forall fun k => abs_nonneg (E k - w k)) ?_
      (by simpa only [mul_zero] using hfour.const_mul (3 * (Real.pi ^ 2 / 8)))
    filter_upwards [hlegal, hwall] with k hk hw
    have hh0 : 0 < h_ k := by linarith [hk.1]
    have hbound := inverse_square_remainder_bound (n_ k) (h_ k) (H_ k - h_ k)
      hh0 (by linarith [hw.1]) (by linarith [hw.2])
    simpa only [add_sub_cancel] using hbound
  have hs4 : Tendsto (fun k : ℕ => Real.log (A_ k / b (x k)) - w k)
      atTop (𝓝 (0 : ℝ)) := hS4
  have hlog : Tendsto (fun k : ℕ => Real.log (A_ k / b (y k)))
      atTop (𝓝 (0 : ℝ)) := by
    have hsum := (hs4.sub hblog).sub hR
    have heq : (fun k : ℕ =>
        (Real.log (A_ k / b (x k)) - w k) -
        (Real.log (b (y k) / b (x k)) - E k) - (E k - w k)) =ᶠ[atTop]
        (fun k : ℕ => Real.log (A_ k / b (y k))) := by
      filter_upwards [hApos, hshift.1] with k ha hb
      rw [Real.log_div ha.ne' hb.1.ne',
        Real.log_div hb.2.1.ne' hb.1.ne', Real.log_div ha.ne' hb.2.1.ne']
      ring
    simpa only [sub_self, sub_zero] using hsum.congr' heq
  have hpositive : ∀ᶠ k : ℕ in atTop, 0 < A_ k ∧ 0 < b (y k) := by
    filter_upwards [hApos, hshift.1] with k ha hb
    exact ⟨ha, hb.2.1⟩
  refine ⟨hpositive, ?_⟩
  have hexp := (Real.continuous_exp.tendsto (0 : ℝ)).comp hlog
  have heqexp : (fun k : ℕ => Real.exp (Real.log (A_ k / b (y k)))) =ᶠ[atTop]
      (fun k : ℕ => A_ k / b (y k)) := by
    filter_upwards [hpositive] with k hk
    exact Real.exp_log (div_pos hk.1 hk.2)
  simpa only [Real.exp_zero, Function.comp_def] using hexp.congr' heqexp

-- Body of the preceding head: proof.md §§2--4. The log residual is established
-- as an internal have; the theorem returns only positivity and the ratio.
-- A_ is instantiated with an actual qualified finite probability in BOTH
-- public wrappers below. hS4 is never a new public probability hypothesis.

theorem weak_corrected_boundary
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
      0 < RademacherS4Assembly.p (n_ k) (h_ k) ∧
      0 < Shao.Probability.BrownianSup.probability B P hB
        (weakHeight (h_ k) / Real.sqrt (n_ k : ℝ))) ∧
    Tendsto (fun k : ℕ =>
      RademacherS4Assembly.p (n_ k) (h_ k) /
        Shao.Probability.BrownianSup.probability B P hB
          (weakHeight (h_ k) / Real.sqrt (n_ k : ℝ)))
      atTop (𝓝 (1 : ℝ)) := by
  let m : ℕ → ℕ := fun k => Nat.floor (h_ k)
  have hgeom : ∀ᶠ k : ℕ in atTop,
      1 ≤ m k ∧ (m k : ℝ) ≤ h_ k ∧ h_ k < (m k : ℝ) + 1 := by
    filter_upwards [hh.eventually_ge_atTop (2 : ℝ)] with k hk
    exact ⟨Nat.floor_pos.mpr (by linarith),
      Nat.floor_le (by linarith), Nat.lt_floor_add_one _⟩
  have hcell := eventually_atTop.1 hgeom
  have hs := RademacherS4Assembly.S4_EVENTUAL B P hB m n_ h_
    hcell hh hscale2 hscale3
  rcases hs with ⟨_, _, _, _, _, _, _, hwlog, _, Kt, Kp, _, _, hprob, _⟩
  have hApos : ∀ᶠ k : ℕ in atTop, 0 < RademacherS4Assembly.p (n_ k) (h_ k) := by
    filter_upwards [eventually_ge_atTop Kp] with k hk
    rcases (hprob k hk).1 with ⟨_, _, _, _, _, _, _, _, _, hp, _⟩
    exact hp
  have hwall : ∀ᶠ k : ℕ in atTop,
      h_ k ≤ weakHeight (h_ k) ∧ weakHeight (h_ k) ≤ h_ k + 1 := by
    filter_upwards [hgeom] with k hk
    change h_ k ≤ (m k : ℝ) + 1 ∧ (m k : ℝ) + 1 ≤ h_ k + 1
    exact ⟨hk.2.2.le, by linarith [hk.2.1]⟩
  exact corrected_boundary_of_S4 B P hB n_ h_ (fun k => weakHeight (h_ k))
    (fun k => RademacherS4Assembly.p (n_ k) (h_ k)) hh hscale2 hscale3 hwall hApos hwlog

-- Body of the preceding head: proof.md §5. Obtain floor-cell S4_EVENTUAL,
-- its log residual, and actual p positivity, then instantiate the helper.

theorem strict_corrected_boundary
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
        (strictHeight (h_ k) / Real.sqrt (n_ k : ℝ))) ∧
    Tendsto (fun k : ℕ =>
      RademacherStrictCube.strictP (n_ k) (h_ k) /
        Shao.Probability.BrownianSup.probability B P hB
          (strictHeight (h_ k) / Real.sqrt (n_ k : ℝ)))
      atTop (𝓝 (1 : ℝ)) := by
  have hs := RademacherGeneralStrictS4.strict_S4_EVENTUAL B P hB n_ h_
    hh hscale2 hscale3
  have hApos : ∀ᶠ k : ℕ in atTop,
      0 < RademacherStrictCube.strictP (n_ k) (h_ k) := hs.1.mono fun _ hk => hk.1
  have hwall : ∀ᶠ k : ℕ in atTop,
      h_ k ≤ strictHeight (h_ k) ∧ strictHeight (h_ k) ≤ h_ k + 1 := by
    filter_upwards [hh.eventually_ge_atTop (1 : ℝ)] with k hk
    have hb := RademacherRealStrictBoundary.ceil_boundary_bridge
      (n_ k) (h_ k) (by linarith)
    change h_ k ≤ (Nat.ceil (h_ k) : ℝ) ∧ (Nat.ceil (h_ k) : ℝ) ≤ h_ k + 1
    exact ⟨hb.2.2.2.1, by linarith [hb.2.1, hb.2.2.1]⟩
  exact corrected_boundary_of_S4 B P hB n_ h_ (fun k => strictHeight (h_ k))
    (fun k => RademacherStrictCube.strictP (n_ k) (h_ k))
    hh hscale2 hscale3 hwall hApos hs.2.1

-- Body of the preceding head: proof.md §6. Obtain strict_S4_EVENTUAL,
-- unfold only its Q/correction/delta and strictHeight, instantiate helper.

end Shao.OQ4.RademacherCorrectedBrownianBoundary
end
