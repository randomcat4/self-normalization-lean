import Shao.OQ3.OpenDomainBoundaryLowerBound

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology
noncomputable section

theorem actual_parabola_rate_floor_of_boundary_lower_bound
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (level a0 cap delta c : ℝ)
    (hcap : 0 < cap) (hdelta : 0 < delta) (hc : 0 < c)
    (F : (ℝ × ℝ) → ℝ)
    (heq : ∀ᶠ u : ℝ × ℝ in 𝓝 (0, 0),
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
        (a0 + u.1, (a0 + u.1) ^ 2 / level ^ 2 - u.2) = (F u : EReal))
    (hgrowth : ∀ r z : ℝ, |r| ≤ delta → 0 ≤ z → z ≤ delta →
      c * (z + r ^ 2) ≤ F (r, z) - F (0, 0)) :
    let I : (ℝ × ℝ) → EReal :=
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
    let V : ℝ → Set (ℝ × ℝ) := fun eta =>
      {w | |w.1 - a0| ≤ eta ∧
        0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ eta}
    I (a0, a0 ^ 2 / level ^ 2) = (F (0, 0) : EReal) ∧
      ∃ eta : ℝ, 0 < eta ∧ eta ≤ cap ∧ eta ≤ delta ∧ ∀ w ∈ V eta,
        I w = (F (w.1 - a0, w.1 ^ 2 / level ^ 2 - w.2) : EReal) ∧
        I (a0, a0 ^ 2 / level ^ 2) ≤ I w
 := by
  dsimp only
  let I : (ℝ × ℝ) → EReal :=
    Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
  obtain ⟨eps, heps, hlocal⟩ := Metric.eventually_nhds_iff.mp heq
  have hcenter : I (a0, a0 ^ 2 / level ^ 2) = (F (0, 0) : EReal) := by
    have h := hlocal (y := (0, 0)) (by simpa only [dist_self] using heps)
    simpa only [add_zero, sub_zero] using h
  let eta : ℝ := min cap (min delta (eps / 2))
  have heta : 0 < eta := lt_min hcap (lt_min hdelta (half_pos heps))
  have hcapeta : eta ≤ cap := min_le_left _ _
  have hdeltaeta : eta ≤ delta := le_trans (min_le_right _ _) (min_le_left _ _)
  have hepseta : eta ≤ eps / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hsmall : eta < eps := lt_of_le_of_lt hepseta (by linarith)
  refine ⟨hcenter, eta, heta, hcapeta, hdeltaeta, ?_⟩
  intro w hw
  let r : ℝ := w.1 - a0
  let z : ℝ := w.1 ^ 2 / level ^ 2 - w.2
  have hr : |r| ≤ eta := hw.1
  have hz : 0 ≤ z := hw.2.1
  have hzeta : z ≤ eta := hw.2.2
  have hdist : dist (r, z) (0, 0) < eps := by
    simp only [Prod.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg hz]
    exact max_lt_iff.mpr ⟨hr.trans_lt hsmall, hzeta.trans_lt hsmall⟩
  have hpoint : I w = (F (r, z) : EReal) := by
    have h := hlocal (y := (r, z)) hdist
    have hG : (a0 + r, (a0 + r) ^ 2 / level ^ 2 - z) = w := by
      dsimp [r, z]
      ext <;> ring
    change I (a0 + r, (a0 + r) ^ 2 / level ^ 2 - z) = _ at h
    rw [hG] at h
    exact h
  have hF : F (0, 0) ≤ F (r, z) := by
    have h := hgrowth r z (hr.trans hdeltaeta) hz (hzeta.trans hdeltaeta)
    have hn : 0 ≤ c * (z + r ^ 2) := mul_nonneg hc.le (add_nonneg hz (sq_nonneg r))
    linarith
  refine ⟨hpoint, ?_⟩
  change I (a0, a0 ^ 2 / level ^ 2) ≤ I w
  rw [hcenter, hpoint]
  exact EReal.coe_le_coe_iff.mpr hF

theorem actual_parabola_analytic_rate_floor_of_boundary_lower_bound
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (level a0 cap delta c : ℝ)
    (hcap : 0 < cap) (hdelta : 0 < delta) (hc : 0 < c)
    (F : (ℝ × ℝ) → ℝ)
    (heq : ∀ᶠ u : ℝ × ℝ in 𝓝 (0, 0),
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
        (a0 + u.1, (a0 + u.1) ^ 2 / level ^ 2 - u.2) = (F u : EReal))
    (hgrowth : ∀ r z : ℝ, |r| ≤ delta → 0 ≤ z → z ≤ delta →
      c * (z + r ^ 2) ≤ F (r, z) - F (0, 0))
    (J : (ℝ × ℝ) → ℝ)
    (hJ : ∀ w : ℝ × ℝ,
      |w.1 - a0| ≤ cap ∧
        0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ cap →
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w =
        (J w : EReal)) :
    let V : ℝ → Set (ℝ × ℝ) := fun eta =>
      {w | |w.1 - a0| ≤ eta ∧
        0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ eta}
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ cap ∧ eta ≤ delta ∧
      ∀ w ∈ V eta, J (a0, a0 ^ 2 / level ^ 2) ≤ J w := by
  dsimp only
  obtain ⟨_, eta, heta, hcapeta, hdeltaeta, hfloor⟩ :=
    actual_parabola_rate_floor_of_boundary_lower_bound
      mu level a0 cap delta c hcap hdelta hc F heq hgrowth
  have hJcenter := hJ (a0, a0 ^ 2 / level ^ 2) (by
    simp only [sub_self, abs_zero]
    exact ⟨hcap.le, le_rfl, hcap.le⟩)
  refine ⟨eta, heta, hcapeta, hdeltaeta, ?_⟩
  intro w hw
  have hwcap : |w.1 - a0| ≤ cap ∧
      0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ cap :=
    ⟨hw.1.trans hcapeta, hw.2.1, hw.2.2.trans hcapeta⟩
  have hJw := hJ w hwcap
  have hle := (hfloor w hw).2
  have hle' : (J (a0, a0 ^ 2 / level ^ 2) : EReal) ≤ (J w : EReal) := by
    calc
      _ = Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
          (a0, a0 ^ 2 / level ^ 2) := hJcenter.symm
      _ ≤ Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w := hle
      _ = (J w : EReal) := hJw
  exact EReal.coe_le_coe_iff.mp hle'

end
end Shao.OQ3
