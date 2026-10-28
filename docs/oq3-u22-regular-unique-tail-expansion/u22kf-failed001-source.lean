import Shao.OQ3.BoundedParabolaLegendreZeroSet
import Shao.OQ3.OpenDomainRateDerivatives
import Mathlib.Analysis.Calculus.LocalExtr.Basic

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem bounded_centered_parabola_global_boundary_tilt_sign
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (hmean : (∫ x : ℝ, x ∂mu) = 0)
    (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (hdet : (parabolaCovariance
      (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))).det ≠ 0)
    (level a0 : ℝ) (hlevel : 0 < level) (ha0 : 0 < a0)
    (htiltMean : (∫ x : ℝ, x ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2),
      ∫ x : ℝ, x ^ 2 ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)) =
        (a0, a0 ^ 2 / level ^ 2))
    (hglobal : ∀ y : ℝ × ℝ, 0 < y.2 → level * Real.sqrt y.2 ≤ y.1 →
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
          (a0, a0 ^ 2 / level ^ 2) ≤
        Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y) :
    theta.1 = -2 * a0 * theta.2 / level ^ 2 ∧ 0 < theta.1 ∧ theta.2 < 0 := by
  let I : (ℝ × ℝ) → EReal :=
    Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
  let K : (ℝ × ℝ) → ℝ := fun p =>
    Real.log (∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu)
  let q : ℝ := ∫ x : ℝ, x ^ 2 ∂mu
  let z0 : ℝ × ℝ := (a0, a0 ^ 2 / level ^ 2)
  obtain ⟨L, e, _hL, _he, _hs, ht, _hsource, _hSmooth, hFirst, _hSecond, hGlobal⟩ :=
    open_domain_quadratic_tilt_local_rate_derivatives mu theta htheta hdet
  let J : (ℝ × ℝ) → ℝ := fun z =>
    (e.symm z).1 * z.1 + (e.symm z).2 * z.2 - K (e.symm z)
  have ht0 : z0 ∈ e.target := by simpa only [htiltMean] using ht
  have hfirst : HasFDerivAt J (theta.1 • ContinuousLinearMap.fst ℝ ℝ ℝ +
      theta.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) z0 := by
    simpa only [htiltMean] using hFirst
  have hvalue (w : ℝ × ℝ) (hw : w ∈ e.target) : I w = ((J w : ℝ) : EReal) :=
    hGlobal w hw
  let gamma : ℝ → ℝ × ℝ := fun a => (a, a ^ 2 / level ^ 2)
  let f : ℝ → ℝ := fun a => J (gamma a)
  have hboundary (a : ℝ) (ha : 0 < a) :
      0 < (gamma a).2 ∧ level * Real.sqrt (gamma a).2 = (gamma a).1 := by
    refine ⟨div_pos (sq_pos_of_pos ha) (sq_pos_of_pos hlevel), ?_⟩
    dsimp only [gamma, Prod.fst, Prod.snd]
    rw [Real.sqrt_div (sq_nonneg a), Real.sqrt_sq ha.le, Real.sqrt_sq hlevel.le]
    field_simp [hlevel.ne']
  have hgamma : Continuous gamma := by dsimp [gamma]; fun_prop
  have hnear : ∀ᶠ a in 𝓝 a0, 0 < a ∧ gamma a ∈ e.target := by
    have htarget : ∀ᶠ a in 𝓝 a0, gamma a ∈ e.target :=
      hgamma.continuousAt (e.open_target.mem_nhds ht0)
    exact (lt_mem_nhds ha0).and htarget
  have hmin : IsLocalMin f a0 := by
    filter_upwards [hnear] with a ha
    have hh := hglobal (gamma a) (hboundary a ha.1).1 (hboundary a ha.1).2.le
    change I z0 ≤ I (gamma a) at hh
    rw [hvalue z0 ht0, hvalue (gamma a) ha.2] at hh
    exact_mod_cast hh
  have hgammaD : HasDerivAt gamma (1, 2 * a0 / level ^ 2) a0 := by
    simpa [gamma] using (hasDerivAt_id a0).prodMk
      (((hasDerivAt_id a0).pow 2).div_const (level ^ 2))
  have hd : HasDerivAt f (theta.1 + theta.2 * (2 * a0 / level ^ 2)) a0 := by
    have hh := hfirst.comp_hasDerivAt a0 hgammaD
    change HasDerivAt f (theta.1 * 1 + theta.2 * (2 * a0 / level ^ 2)) a0 at hh
    simpa only [mul_one] using hh
  have hstation : theta.1 + theta.2 * (2 * a0 / level ^ 2) = 0 :=
    hmin.hasDerivAt_eq_zero hd
  have hsaddle : theta.1 = -2 * a0 * theta.2 / level ^ 2 := by
    calc
      theta.1 = -(theta.2 * (2 * a0 / level ^ 2)) := by linarith only [hstation]
      _ = -2 * a0 * theta.2 / level ^ 2 := by ring
  have hmeanrate : I (0, q) = 0 := by
    have hh := (bounded_parabola_legendre_zero_and_strictly_positive mu M hM hb
      (∫ x : ℝ, x ∂mu, ∫ x : ℝ, x ^ 2 ∂mu)).2.1.mpr rfl
    simpa only [hmean] using hh
  have hKlower : theta.2 * q ≤ K theta := by
    have hh := Shao.Probability.bivariateLegendreRate_test_le mu
      (fun x : ℝ => (x, x ^ 2)) (0, q) ⟨theta, interior_subset htheta⟩
    change _ ≤ I (0, q) at hh
    rw [hmeanrate] at hh
    have hreal : theta.1 * 0 + theta.2 * q - K theta ≤ (0 : ℝ) := by
      exact_mod_cast hh
    linarith only [hreal]
  have hIvalue : I z0 = ((theta.1 * a0 + theta.2 * (a0 ^ 2 / level ^ 2) -
      K theta : ℝ) : EReal) := by
    simpa only [htiltMean] using
      (open_domain_quadratic_tilt_legendre_attained mu theta htheta).2
  have hzpos : 0 < I z0 := bounded_centered_parabola_positive_tail_rate mu M hM hb hmean
    level hlevel z0 (hboundary a0 ha0).1 (hboundary a0 ha0).2.le
  have hratepos : 0 < theta.1 * a0 + theta.2 * (a0 ^ 2 / level ^ 2) - K theta := by
    rw [hIvalue] at hzpos
    exact_mod_cast hzpos
  have hsum : theta.1 * a0 + theta.2 * (a0 ^ 2 / level ^ 2) =
      -theta.2 * (a0 ^ 2 / level ^ 2) := by rw [hsaddle]; ring
  rw [hsum] at hratepos
  have hq : 0 ≤ q := integral_nonneg fun x => sq_nonneg x
  have hnegative : theta.2 < 0 := by
    by_contra hnot
    have htheta2 : 0 ≤ theta.2 := le_of_not_gt hnot
    have hK : 0 ≤ K theta := (mul_nonneg htheta2 hq).trans hKlower
    have hterm : 0 ≤ theta.2 * (a0 ^ 2 / level ^ 2) := mul_nonneg htheta2 (by positivity)
    linarith only [hratepos, hK, hterm]
  refine ⟨hsaddle, ?_, hnegative⟩
  rw [hsaddle]
  exact div_pos (by positivity) (sq_pos_of_pos hlevel)

end
end Shao.OQ3
