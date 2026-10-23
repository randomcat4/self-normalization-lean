import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace Shao.OQ3
open scoped Topology
noncomputable section

theorem self_normalized_boundary_event_iff
    (level a q : ℝ) (hlevel : 0 < level) (hq : 0 < q) :
    level * Real.sqrt q ≤ a ↔ 0 < a ∧ q ≤ a ^ 2 / level ^ 2
 := by
  have hl2 : 0 < level ^ 2 := pow_pos hlevel 2
  have hleft : 0 ≤ level * Real.sqrt q := mul_nonneg hlevel.le (Real.sqrt_nonneg q)
  constructor
  · intro h
    have ha : 0 < a := (mul_pos hlevel (Real.sqrt_pos.mpr hq)).trans_le h
    refine ⟨ha, (le_div_iff₀ hl2).mpr ?_⟩
    have hh := (sq_le_sq₀ hleft ha.le).2 h
    rw [mul_pow, Real.sq_sqrt hq.le] at hh
    nlinarith
  · rintro ⟨ha, hb⟩
    apply (sq_le_sq₀ hleft ha.le).mp
    rw [mul_pow, Real.sq_sqrt hq.le]
    nlinarith [(le_div_iff₀ hl2).mp hb]

theorem exists_positive_parabola_window
    (level a0 cap : ℝ) (hlevel : 0 < level) (ha0 : 0 < a0) (hcap : 0 < cap) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ cap ∧ ∀ r z : ℝ, |r| ≤ rho → |z| ≤ rho →
      0 < a0 + r ∧ 0 < (a0 + r) ^ 2 / level ^ 2 - z ∧
        (level * Real.sqrt ((a0 + r) ^ 2 / level ^ 2 - z) ≤ a0 + r ↔ 0 ≤ z) := by
  have hA : Continuous (fun w : ℝ × ℝ => a0 + w.1) := by fun_prop
  have hQ : Continuous (fun w : ℝ × ℝ => (a0 + w.1) ^ 2 / level ^ 2 - w.2) := by fun_prop
  have hQ0 : 0 < (a0 + (0 : ℝ × ℝ).1) ^ 2 / level ^ 2 - (0 : ℝ × ℝ).2 := by
    simpa using div_pos (pow_pos ha0 2) (pow_pos hlevel 2)
  have hA0 : 0 < (fun w : ℝ × ℝ => a0 + w.1) (0 : ℝ × ℝ) := by simpa using ha0
  have hnearA : ∀ᶠ w in 𝓝 (0 : ℝ × ℝ), 0 < a0 + w.1 :=
    hA.continuousAt.eventually (lt_mem_nhds hA0)
  have hnearQ : ∀ᶠ w in 𝓝 (0 : ℝ × ℝ), 0 < (a0 + w.1) ^ 2 / level ^ 2 - w.2 :=
    hQ.continuousAt.eventually (lt_mem_nhds hQ0)
  have hnear : ∀ᶠ w in 𝓝 (0 : ℝ × ℝ), 0 < a0 + w.1 ∧ 0 < (a0 + w.1) ^ 2 / level ^ 2 - w.2 := by
    filter_upwards [hnearA, hnearQ] with w ha hq
    exact ⟨ha, hq⟩
  obtain ⟨delta, hdelta, hpoint⟩ := Metric.eventually_nhds_iff.mp hnear
  let rho : ℝ := min cap (delta / 2)
  refine ⟨rho, lt_min hcap (by linarith), min_le_left _ _, ?_⟩
  intro r z hr hz
  have hinside : dist (r, z) (0, 0) < delta := by
    rw [show (0, 0) = (0 : ℝ × ℝ) from rfl, dist_zero_right, Prod.norm_def,
      Real.norm_eq_abs, Real.norm_eq_abs, max_lt_iff]
    have hrd : rho ≤ delta / 2 := min_le_right _ _
    exact ⟨by linarith, by linarith⟩
  obtain ⟨ha, hq⟩ := hpoint hinside
  refine ⟨ha, hq, ?_⟩
  rw [self_normalized_boundary_event_iff level (a0 + r) ((a0 + r) ^ 2 / level ^ 2 - z) hlevel hq]
  simp only [ha, true_and]
  constructor <;> intro h <;> linarith

end
end Shao.OQ3
