import Shao.OQ3.SymmetricEightAtomSmallPositiveMinimum
import Shao.OQ3.BoundedCenteredParabolaRegularUniqueSaddle
import Shao.OQ3.BoundedParabolaWholeTailRateGap

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators Topology
noncomputable section

theorem exists_symmetric_eight_atom_regular_unique_saddle_witness :
    ∃ a : Fin 8 → ℝ, a 0 = 1 ∧ StrictMono a ∧ (∀ i, 0 < a i) ∧
      let A : Fin (8 + 8) → ℝ := Fin.append a (fun i => -a i)
      let mu : Measure ℝ := Measure.sum fun k : Fin (8 + 8) =>
        ENNReal.ofReal ((1 : ℝ) / 16) • Measure.dirac (A k)
      letI : IsProbabilityMeasure mu := (symmetric_eight_atom_law_and_phase_gap a).1
      Function.Injective A ∧ IsProbabilityMeasure mu ∧ Integrable (fun x : ℝ => x) mu ∧
        (∫ x : ℝ, x ∂mu) = 0 ∧ (∃ B : ℝ, 0 < B ∧ (∀ᵐ x ∂mu, 1 ≤ |x| ∧ |x| ≤ B) ∧
          (∀ᵐ x ∂mu, 1 ≤ x ^ 2 ∧ x ^ 2 ≤ B ^ 2)) ∧ 0 < mu (Set.Ioi 0) ∧
        (∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 → ‖jointCharacteristic mu xi eta‖ < 1) ∧
        (∃ c : ℝ, 0 < c ∧ ∃ R : ℝ, 0 ≤ R ∧
          (∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
            ‖jointCharacteristic mu xi eta‖ ≤
              1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-(3 : ℝ) / 8)) ∧
          ∀ K : Set (ℝ × ℝ), IsCompact K → ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧
            0 < m ^ 2 * c / 2 ∧ ∀ p ∈ K,
              (ENNReal.ofReal m • mu ≤
                mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) ∧
              (∀ xi eta : ℝ, m ^ 2 * (1 - ‖jointCharacteristic mu xi eta‖ ^ 2) ≤
                1 - ‖jointCharacteristic
                  (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) xi eta‖ ^ 2) ∧
              ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
                ‖jointCharacteristic
                  (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) xi eta‖ ≤
                    1 - (m ^ 2 * c / 2) *
                      Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-(3 : ℝ) / 8)) ∧
        (∀ R eps : ℝ, 0 < eps → ∃ xi : ℝ, R < xi ∧
          ‖jointCharacteristic mu xi 0 - 1‖ < eps ∧ 1 - eps < ‖jointCharacteristic mu xi 0‖) ∧
        ¬(∃ delta : ℝ, 0 < delta ∧ ∃ R : ℝ, 0 ≤ R ∧ ∀ xi eta : ℝ,
          R < Real.sqrt (xi ^ 2 + eta ^ 2) → ‖jointCharacteristic mu xi eta‖ ≤ 1 - delta) ∧
        0 < (parabolaCovariance mu).det ∧
        ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧
          ∀ level : ℝ, 0 < level → level < epsilon →
            ∃ (a0 : ℝ) (theta : ℝ × ℝ) (L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)),
              let D := parabolaCovariance
                (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))
              0 < a0 ∧ theta ∈ interior
                (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))) ∧
              0 < D.det ∧
              (∫ x : ℝ, x ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2),
                ∫ x : ℝ, x ^ 2 ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)) =
                  (a0, a0 ^ 2 / level ^ 2) ∧
              theta.1 = -2 * a0 * theta.2 / level ^ 2 ∧ 0 < theta.1 ∧ theta.2 < 0 ∧
              (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) =
                (D 0 0 • ContinuousLinearMap.fst ℝ ℝ ℝ +
                  D 0 1 • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
                (D 0 1 • ContinuousLinearMap.fst ℝ ℝ ℝ +
                  D 1 1 • ContinuousLinearMap.snd ℝ ℝ ℝ) ∧
              0 < 2 * theta.2 / level ^ 2 +
                (L.symm (1, 2 * a0 / level ^ 2)).1 +
                  (2 * a0 / level ^ 2) * (L.symm (1, 2 * a0 / level ^ 2)).2 ∧
              0 < Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
                (a0, a0 ^ 2 / level ^ 2) ∧
              Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
                (a0, a0 ^ 2 / level ^ 2) < ⊤ ∧
              (∀ y : ℝ × ℝ, 0 < y.2 → level * Real.sqrt y.2 ≤ y.1 →
                Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
                  (a0, a0 ^ 2 / level ^ 2) ≤
                  Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y) ∧
              (∀ y : ℝ × ℝ, 0 < y.2 → level * Real.sqrt y.2 ≤ y.1 →
                Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y ≤
                  Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
                    (a0, a0 ^ 2 / level ^ 2) → y = (a0, a0 ^ 2 / level ^ 2)) ∧
              ∀ rho : ℝ, 0 < rho → ∃ delta : ℝ, 0 < delta ∧ ∀ y : ℝ × ℝ,
                0 < y.2 → level * Real.sqrt y.2 ≤ y.1 →
                  (rho < |y.1 - a0| ∨ rho < |y.1 ^ 2 / level ^ 2 - y.2|) →
                    (((Shao.Probability.bivariateLegendreRate mu
                      (fun x : ℝ => (x, x ^ 2)) (a0, a0 ^ 2 / level ^ 2)).toReal + delta : ℝ) : EReal) <
                      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y := by
  classical
  obtain ⟨a, ha0, hmono, hpos, hlaw⟩ := exists_symmetric_eight_atom_small_positive_minimum
  let A : Fin (8 + 8) → ℝ := Fin.append a (fun i => -a i)
  let mu : Measure ℝ := Measure.sum fun k : Fin (8 + 8) =>
    ENNReal.ofReal ((1 : ℝ) / 16) • Measure.dirac (A k)
  obtain ⟨hAinj, hprob, hint, hmean, hbounded, hright, hnonlattice, hweak, hnear,
      hnotStrong, hdet, _hOldGlobal⟩ := hlaw
  letI : IsProbabilityMeasure mu := hprob
  obtain ⟨B, hB, habs, henergy⟩ := hbounded
  obtain ⟨epsilon, hepsilon, heps1, hregular⟩ :=
    bounded_centered_parabola_small_positive_regular_unique_saddle mu B hB.le
      (habs.mono fun _ hx => hx.2) 1 (B ^ 2) (by norm_num) henergy hmean hdet
  refine ⟨a, ha0, hmono, hpos, ?_⟩
  dsimp only
  refine ⟨hAinj, hprob, hint, hmean, ⟨B, hB, habs, henergy⟩, hright, hnonlattice,
    hweak, hnear, hnotStrong, hdet, epsilon, hepsilon, heps1, ?_⟩
  intro level hlevel hsmall
  obtain ⟨a0, theta, L, ha0s, htheta, hcov, hmeanPoint, hstationary, htheta1, htheta2,
      hL, hlambda, hIpos, hIfinite, hglobal, hunique⟩ := hregular level hlevel hsmall
  refine ⟨a0, theta, L, ha0s, htheta, hcov, hmeanPoint, hstationary, htheta1, htheta2,
    hL, hlambda, hIpos, hIfinite, hglobal, hunique, ?_⟩
  intro rho hrho
  let I : (ℝ × ℝ) → EReal :=
    Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
  let center : ℝ × ℝ := (a0, a0 ^ 2 / level ^ 2)
  have hNoBot : I center ≠ ⊥ := ne_of_gt (lt_of_le_of_lt bot_le hIpos)
  have hRate : I center = ((I center).toReal : EReal) :=
    (EReal.coe_toReal hIfinite.ne hNoBot).symm
  have hTrueUnique (w : ℝ × ℝ) (hw : 0 < w.2 ∧ level * Real.sqrt w.2 ≤ w.1) :
      I center ≤ I w ∧ (I w = I center ↔ w = center) := by
    refine ⟨hglobal w hw.1 hw.2, ?_⟩
    constructor
    · intro heq
      exact hunique w hw.1 hw.2 heq.le
    · intro heq
      rw [heq]
  obtain ⟨delta, hdelta, hgap⟩ := bounded_parabola_whole_tail_rate_gap_of_unique_minimum
    mu B hB.le (habs.mono fun _ hx => hx.2) 1 (B ^ 2) (by norm_num) henergy
      level a0 rho (I center).toReal hrho hRate hTrueUnique
  refine ⟨delta, hdelta, ?_⟩
  intro y hyq hycone hout
  apply hgap y
  refine ⟨⟨hyq, hycone⟩, ?_⟩
  intro hU
  rcases hout with hleft | hright
  · exact (not_lt_of_ge hU.1) hleft
  · exact (not_lt_of_ge hU.2) hright

end
end Shao.OQ3
