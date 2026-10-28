import Shao.OQ3.BoundedCenteredParabolaRateCurvature
import Shao.OQ3.BoundedCenteredParabolaMinimumLocalization
import Shao.OQ3.BoundedCenteredParabolaMinimumBoundary
import Mathlib.Analysis.Convex.Deriv

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem bounded_centered_parabola_small_positive_unique_global_minimum
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (lower upper : ℝ) (hlower : 0 < lower)
    (henergy : ∀ᵐ x ∂mu, lower ≤ x ^ 2 ∧ x ^ 2 ≤ upper)
    (hmean : (∫ x : ℝ, x ∂mu) = 0) (hdet : 0 < (parabolaCovariance mu).det) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧
      ∀ level : ℝ, 0 < level → level < epsilon → ∃ z : ℝ × ℝ,
        0 < z.2 ∧ z.1 = level * Real.sqrt z.2 ∧
          0 < Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z ∧
          Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z < ⊤ ∧
          (∀ y : ℝ × ℝ, 0 < y.2 → level * Real.sqrt y.2 ≤ y.1 →
            Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z ≤
              Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y) ∧
          ∀ y : ℝ × ℝ, 0 < y.2 → level * Real.sqrt y.2 ≤ y.1 →
            Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y ≤
              Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z → y = z := by
  let q0 : ℝ := ∫ x : ℝ, x ^ 2 ∂mu
  obtain ⟨F, eta, rho, heta, hrho, hrhoq, hcurv⟩ :=
    bounded_centered_parabola_uniform_energy_curvature mu M hM hb lower upper hlower
      henergy hmean hdet
  obtain ⟨epsilon, hepsilon, heps1, hmins⟩ :=
    bounded_centered_parabola_global_minima_localize mu M hM hb lower upper hlower
      henergy hmean hdet.ne' (rho / 2) (half_pos hrho)
  refine ⟨min epsilon eta, lt_min hepsilon heta,
    (min_le_left _ _).trans heps1, ?_⟩
  intro level hlevel hsmall
  have hlevelBound : |level| ≤ eta := by
    rw [abs_of_pos hlevel]
    exact (hsmall.trans_le (min_le_right _ _)).le
  obtain ⟨z, hzq, hzcone, hzpos, hzfinite, hzglobal, hlocal⟩ :=
    hmins level hlevel (hsmall.trans_le (min_le_left _ _))
  have hzb := bounded_centered_parabola_global_minimum_on_boundary mu M hM hb hmean
    level hlevel z hzq hzcone hzfinite hzglobal
  let Q : Set ℝ := Set.Icc (q0 - rho) (q0 + rho)
  have henergy_mem (y : ℝ × ℝ)
      (hy : Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y ≤
        Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z) :
      y.2 ∈ Q := by
    have hd := hlocal y hy
    have hh : max |y.1| |y.2 - q0| < rho / 2 := by
      simpa only [Prod.dist_eq, Real.dist_eq, sub_zero] using hd
    have habs : |y.2 - q0| < rho :=
      (max_lt_iff.mp hh).2.trans (half_lt_self hrho)
    obtain ⟨hlo, hhi⟩ := abs_lt.mp habs
    exact ⟨by linarith, by linarith⟩
  have habs (q : ℝ) (hq : q ∈ Q) : |q - q0| ≤ rho :=
    abs_le.mpr ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hqpos (q : ℝ) (hq : q ∈ Q) : 0 < q := by
    have hlo := hq.1
    change q0 - rho ≤ q at hlo
    change rho < q0 at hrhoq
    linarith
  have hinfo (q : ℝ) (hq : q ∈ Q) :
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
          (level * Real.sqrt q, q) = (F (level, q) : EReal) ∧
      ContDiffAt ℝ (2 : WithTop ENat) (fun energy : ℝ => F (level, energy)) q ∧
        0 < deriv (deriv (fun energy : ℝ => F (level, energy))) q :=
    hcurv level q hlevelBound (habs q hq)
  have hstrict : StrictConvexOn ℝ Q (fun q : ℝ => F (level, q)) := by
    apply strictConvexOn_of_deriv2_pos (convex_Icc _ _)
    · intro q hq
      exact (hinfo q hq).2.1.continuousAt.continuousWithinAt
    · intro q hq
      exact (hinfo q (interior_subset hq)).2.2
  have hminimum (w : ℝ × ℝ) (hw : w.2 ∈ Q)
      (hwb : w.1 = level * Real.sqrt w.2)
      (hglobal : ∀ y : ℝ × ℝ, 0 < y.2 → level * Real.sqrt y.2 ≤ y.1 →
        Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w ≤
          Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y) :
      IsMinOn (fun q : ℝ => F (level, q)) Q w.2 := by
    intro q hq
    have hwpoint : (level * Real.sqrt w.2, w.2) = w := Prod.ext hwb.symm rfl
    have hwvalue : Shao.Probability.bivariateLegendreRate mu
        (fun x : ℝ => (x, x ^ 2)) w = (F (level, w.2) : EReal) := by
      simpa only [hwpoint] using (hinfo w.2 hw).1
    have hi := hglobal (level * Real.sqrt q, q) (hqpos q hq) (le_refl _)
    rw [hwvalue, (hinfo q hq).1] at hi
    exact_mod_cast hi
  have hzmem := henergy_mem z (le_refl _)
  have hzmin := hminimum z hzmem hzb hzglobal
  refine ⟨z, hzq, hzb, hzpos, hzfinite, hzglobal, ?_⟩
  intro y hyq hycone hyle
  have hyglobal : ∀ w : ℝ × ℝ, 0 < w.2 → level * Real.sqrt w.2 ≤ w.1 →
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y ≤
        Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w :=
    fun w hwq hwcone => hyle.trans (hzglobal w hwq hwcone)
  have hyfinite := hyle.trans_lt hzfinite
  have hyb := bounded_centered_parabola_global_minimum_on_boundary mu M hM hb hmean
    level hlevel y hyq hycone hyfinite hyglobal
  have hymem := henergy_mem y hyle
  have hymin := hminimum y hymem hyb hyglobal
  have heq : y.2 = z.2 := hstrict.eq_of_isMinOn hymin hzmin hymem hzmem
  exact Prod.ext (by rw [hyb, hzb, heq]) heq

end
end Shao.OQ3
