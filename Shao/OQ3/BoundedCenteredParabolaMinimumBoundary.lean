import Shao.OQ3.BoundedParabolaLegendreZeroSet

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem bounded_centered_parabola_global_minimum_on_boundary
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (hmean : (∫ x : ℝ, x ∂mu) = 0)
    (level : ℝ) (hlevel : 0 < level) (z : ℝ × ℝ)
    (hzq : 0 < z.2) (hzcone : level * Real.sqrt z.2 ≤ z.1)
    (hfinite : Shao.Probability.bivariateLegendreRate mu
      (fun x : ℝ => (x, x ^ 2)) z < ⊤)
    (hglobal : ∀ y : ℝ × ℝ, 0 < y.2 → level * Real.sqrt y.2 ≤ y.1 →
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z ≤
        Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y) :
    z.1 = level * Real.sqrt z.2 := by
  let I : (ℝ × ℝ) → EReal :=
    Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
  let q : ℝ := ∫ x : ℝ, x ^ 2 ∂mu
  let m : ℝ × ℝ := (0, q)
  have hmeanrate : I m = 0 := by
    have h := (bounded_parabola_legendre_zero_and_strictly_positive mu M hM hb
      (∫ x : ℝ, x ∂mu, ∫ x : ℝ, x ^ 2 ∂mu)).2.1.mpr rfl
    simpa only [hmean] using h
  have hpos : 0 < I z := bounded_centered_parabola_positive_tail_rate mu M hM hb hmean
    level hlevel z hzq hzcone
  have hbot : I z ≠ ⊥ := ne_of_gt ((EReal.bot_lt_coe (0 : ℝ)).trans hpos)
  let j : ℝ := (I z).toReal
  have hjcoe : (j : EReal) = I z := EReal.coe_toReal hfinite.ne hbot
  have hj : 0 < j := by
    have h : ((0 : ℝ) : EReal) < (j : EReal) := by rw [hjcoe]; exact hpos
    exact_mod_cast h
  by_contra hboundary
  have hstrict : level * Real.sqrt z.2 < z.1 :=
    lt_of_le_of_ne hzcone (Ne.symm hboundary)
  let gamma : ℝ → ℝ × ℝ := fun t => (t * z.1, t * z.2 + (1 - t) * q)
  have hgamma : Continuous gamma := by dsimp [gamma]; fun_prop
  have hgamma1 : gamma 1 = z := by ext <;> simp [gamma]
  have hopenq : IsOpen {y : ℝ × ℝ | 0 < y.2} := isOpen_lt continuous_const continuous_snd
  have hopencone : IsOpen {y : ℝ × ℝ | level * Real.sqrt y.2 < y.1} :=
    isOpen_lt (continuous_const.mul (Real.continuous_sqrt.comp continuous_snd)) continuous_fst
  have hopen : IsOpen {y : ℝ × ℝ | 0 < y.2 ∧ level * Real.sqrt y.2 < y.1} :=
    hopenq.inter hopencone
  have htend : Filter.Tendsto gamma (𝓝 1) (𝓝 z) := by
    rw [← hgamma1]
    exact hgamma.continuousAt
  have hnear : {t : ℝ | 0 < (gamma t).2 ∧
      level * Real.sqrt (gamma t).2 < (gamma t).1} ∈ 𝓝 1 :=
    htend (hopen.mem_nhds ⟨hzq, hstrict⟩)
  obtain ⟨d, hd, hsub⟩ := Metric.mem_nhds_iff.mp hnear
  let s : ℝ := min (d / 2) (1 / 2)
  have hs : 0 < s := lt_min (half_pos hd) (by norm_num)
  have hsHalf : s ≤ 1 / 2 := min_le_right _ _
  have hsD : s < d := (min_le_left _ _).trans_lt (half_lt_self hd)
  let t : ℝ := 1 - s
  have ht : 0 < t := by dsimp only [t]; linarith only [hsHalf]
  have ht1 : t < 1 := by dsimp only [t]; linarith only [hs]
  have hdist : dist t 1 = s := by
    rw [Real.dist_eq, show t - 1 = -s by dsimp only [t]; ring, abs_neg, abs_of_pos hs]
  have hfeasible := hsub (Metric.mem_ball.mpr (by rw [hdist]; exact hsD))
  have hupper : I (gamma t) ≤ ((t * j : ℝ) : EReal) := by
    change (⨆ theta : Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)),
      (((theta : ℝ × ℝ).1 * (gamma t).1 + (theta : ℝ × ℝ).2 * (gamma t).2 -
        Shao.Probability.bivariateLogMGF mu (fun x : ℝ => (x, x ^ 2)) theta : ℝ) : EReal)) ≤ _
    apply iSup_le
    intro theta
    have hztest := Shao.Probability.bivariateLegendreRate_test_le mu
      (fun x : ℝ => (x, x ^ 2)) z theta
    change _ ≤ I z at hztest
    rw [← hjcoe] at hztest
    have hmtest := Shao.Probability.bivariateLegendreRate_test_le mu
      (fun x : ℝ => (x, x ^ 2)) m theta
    change _ ≤ I m at hmtest
    rw [hmeanrate] at hmtest
    have hzreal : (theta : ℝ × ℝ).1 * z.1 + (theta : ℝ × ℝ).2 * z.2 -
        Shao.Probability.bivariateLogMGF mu (fun x : ℝ => (x, x ^ 2)) theta ≤ j := by
      exact_mod_cast hztest
    have hmreal : (theta : ℝ × ℝ).1 * 0 + (theta : ℝ × ℝ).2 * q -
        Shao.Probability.bivariateLogMGF mu (fun x : ℝ => (x, x ^ 2)) theta ≤ (0 : ℝ) := by
      exact_mod_cast hmtest
    have hbound := add_le_add (mul_le_mul_of_nonneg_left hzreal ht.le)
      (mul_le_mul_of_nonneg_left hmreal (sub_nonneg.mpr ht1.le))
    apply EReal.coe_le_coe_iff.mpr
    dsimp only [gamma, Prod.fst, Prod.snd]
    nlinarith only [hbound]
  have hdecrease : ((t * j : ℝ) : EReal) < I z := by
    rw [← hjcoe]
    apply EReal.coe_lt_coe_iff.mpr
    nlinarith only [mul_pos (sub_pos.mpr ht1) hj]
  exact hdecrease.not_ge ((hglobal (gamma t) hfeasible.1 hfeasible.2.le).trans hupper)

end
end Shao.OQ3
