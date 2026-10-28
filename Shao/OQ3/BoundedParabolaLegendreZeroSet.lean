import Shao.OQ3.OpenDomainLegendre
import Shao.OQ3.TiltedMeasureDomination
import Mathlib.Analysis.Calculus.LocalExtr.Basic

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem bounded_parabola_legendre_zero_and_strictly_positive
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) :
    ∀ z : ℝ × ℝ,
      0 ≤ Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z ∧
        (Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z = 0 ↔
          z = (∫ x : ℝ, x ∂mu, ∫ x : ℝ, x ^ 2 ∂mu)) ∧
        (z ≠ (∫ x : ℝ, x ∂mu, ∫ x : ℝ, x ^ 2 ∂mu) →
          0 < Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z) := by
  let K : (ℝ × ℝ) → ℝ := fun p =>
    Real.log (∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu)
  let m : ℝ × ℝ := (∫ x : ℝ, x ∂mu, ∫ x : ℝ, x ^ 2 ∂mu)
  let G : (ℝ × ℝ) →L[ℝ] ℝ := m.1 • ContinuousLinearMap.fst ℝ ℝ ℝ +
    m.2 • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hmem (p : ℝ × ℝ) : p ∈ Shao.Probability.bivariateMGFDomain mu
      (fun x : ℝ => (x, x ^ 2)) :=
    quadratic_exp_integrable_of_ae_abs_le mu M hM hb p.1 p.2
  have hdomain : Shao.Probability.bivariateMGFDomain mu
      (fun x : ℝ => (x, x ^ 2)) = Set.univ := Set.eq_univ_of_forall hmem
  have hzero : ((0 : ℝ), (0 : ℝ)) ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))) := by
    rw [hdomain, interior_univ]
    exact Set.mem_univ _
  have htilt0 : mu.tilted (fun x => (0 : ℝ) * x + 0 * x ^ 2) = mu := by
    simpa only [zero_mul, add_zero] using (tilted_const mu 0)
  have hK : HasFDerivAt K G (0, 0) := by
    simpa only [K, G, m, htilt0] using
      (open_domain_quadratic_tilt_frechet_cumulants mu (0, 0) hzero).2.2.2.2.1
  have hmeanrate : Shao.Probability.bivariateLegendreRate mu
      (fun x : ℝ => (x, x ^ 2)) m = 0 := by
    simpa [m, htilt0] using
      (open_domain_quadratic_tilt_legendre_attained mu (0, 0) hzero).2
  have hnonneg (z : ℝ × ℝ) : 0 ≤ Shao.Probability.bivariateLegendreRate mu
      (fun x : ℝ => (x, x ^ 2)) z := by
    have ht := Shao.Probability.bivariateLegendreRate_test_le mu
      (fun x : ℝ => (x, x ^ 2)) z ⟨(0, 0), hmem (0, 0)⟩
    simpa [Shao.Probability.bivariateLogMGF] using ht
  have hleZero (z : ℝ × ℝ) (hz : Shao.Probability.bivariateLegendreRate mu
      (fun x : ℝ => (x, x ^ 2)) z ≤ 0) : z = m := by
    let Q : (ℝ × ℝ) →L[ℝ] ℝ := z.1 • ContinuousLinearMap.fst ℝ ℝ ℝ +
      z.2 • ContinuousLinearMap.snd ℝ ℝ ℝ
    let F : (ℝ × ℝ) → ℝ := fun p => Q p - K p
    have hF : HasFDerivAt F (Q - G) (0, 0) := Q.hasFDerivAt.sub hK
    have hF0 : F (0, 0) = 0 := by simp [F, Q, K]
    have hupper (p : ℝ × ℝ) : F p ≤ 0 := by
      have ht := (Shao.Probability.bivariateLegendreRate_test_le mu
        (fun x : ℝ => (x, x ^ 2)) z ⟨p, hmem p⟩).trans hz
      have ht' : p.1 * z.1 + p.2 * z.2 - K p ≤ (0 : ℝ) := by
        exact_mod_cast ht
      simpa [F, Q, mul_comm] using ht'
    have hmax : IsLocalMax F (0, 0) :=
      Filter.Eventually.of_forall fun p => (hupper p).trans_eq hF0.symm
    have hgrad : Q - G = 0 := hmax.hasFDerivAt_eq_zero hF
    have h1 := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1, 0)) hgrad
    have h2 := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0, 1)) hgrad
    apply Prod.ext
    · simpa [Q, G, sub_eq_zero] using h1
    · simpa [Q, G, sub_eq_zero] using h2
  intro z
  refine ⟨hnonneg z, ⟨fun hz => hleZero z hz.le, ?_⟩, ?_⟩
  · intro hz
    simpa only [hz] using hmeanrate
  · intro hne
    exact lt_of_not_ge fun hle => hne (hleZero z hle)

theorem bounded_centered_parabola_positive_tail_rate
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (hmean : (∫ x : ℝ, x ∂mu) = 0)
    (level : ℝ) (hlevel : 0 < level) (z : ℝ × ℝ)
    (hzq : 0 < z.2) (hzcone : level * Real.sqrt z.2 ≤ z.1) :
    0 < Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z := by
  have hzfirst : 0 < z.1 := (mul_pos hlevel (Real.sqrt_pos.2 hzq)).trans_le hzcone
  have hne : z ≠ (∫ x : ℝ, x ∂mu, ∫ x : ℝ, x ^ 2 ∂mu) := by
    intro heq
    have hfirst := congrArg Prod.fst heq
    simp only [hmean] at hfirst
    exact hzfirst.ne' hfirst
  exact (bounded_parabola_legendre_zero_and_strictly_positive mu M hM hb z).2.2 hne

end
end Shao.OQ3
