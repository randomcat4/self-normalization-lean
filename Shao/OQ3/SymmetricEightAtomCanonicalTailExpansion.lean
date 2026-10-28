import Shao.OQ3.SymmetricEightAtomRegularUniqueSaddleWitness
import Shao.OQ3.BoundedCanonicalActualTailScaledExpansion
import Shao.OQ3.CovarianceRowInverseQuadratic

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators Matrix Topology
noncomputable section

theorem exists_symmetric_eight_atom_canonical_tail_expansion :
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
              (∀ rho : ℝ, 0 < rho → ∃ delta : ℝ, 0 < delta ∧ ∀ y : ℝ × ℝ,
                0 < y.2 → level * Real.sqrt y.2 ≤ y.1 →
                  (rho < |y.1 - a0| ∨ rho < |y.1 ^ 2 / level ^ 2 - y.2|) →
                    (((Shao.Probability.bivariateLegendreRate mu
                      (fun x : ℝ => (x, x ^ 2)) (a0, a0 ^ 2 / level ^ 2)).toReal + delta : ℝ) : EReal) <
                      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y) ∧
              let v : Fin 2 → ℝ := ![1, 2 * a0 / level ^ 2]
              let Lambda1 : ℝ := 2 * theta.2 / level ^ 2 + dotProduct v (D⁻¹ *ᵥ v)
              let J0 : ℝ := theta.1 * a0 + theta.2 * (a0 ^ 2 / level ^ 2) -
                Real.log (∫ x : ℝ, Real.exp (theta.1 * x + theta.2 * x ^ 2) ∂mu)
              let vCorr : ℝ := (-theta.2) * Real.sqrt D.det * Real.sqrt Lambda1
              Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
                  (a0, a0 ^ 2 / level ^ 2) = (J0 : EReal) ∧
              0 < Lambda1 ∧ 0 < vCorr ∧ ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧
                ∀ n : ℕ, N ≤ n →
                  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
                  let T : Set (Shao.Path n) := {z |
                    level * Real.sqrt (n : ℝ) ≤
                      (if Shao.energy z = 0 then 0 else
                        (∑ i : Fin n, z i) / Real.sqrt (Shao.energy z))}
                  |Real.sqrt (2 * Real.pi * (n : ℝ)) *
                      Real.exp ((n : ℝ) * J0) * P.real T - vCorr⁻¹| ≤
                    C / Real.sqrt (n : ℝ) := by
  classical
  obtain ⟨a, ha0, hmono, hpos, hlaw⟩ :=
    exists_symmetric_eight_atom_regular_unique_saddle_witness
  let A : Fin (8 + 8) → ℝ := Fin.append a (fun i => -a i)
  let mu : Measure ℝ := Measure.sum fun k : Fin (8 + 8) =>
    ENNReal.ofReal ((1 : ℝ) / 16) • Measure.dirac (A k)
  obtain ⟨hAinj, hprob, hint, hmean, hbounded, hright, hnonlattice, hweak, hnear,
      hnotStrong, hdet, epsilon, hepsilon, heps1, hregular⟩ := hlaw
  letI : IsProbabilityMeasure mu := hprob
  obtain ⟨B, hB, habs, henergy⟩ := hbounded
  refine ⟨a, ha0, hmono, hpos, ?_⟩
  dsimp only
  refine ⟨hAinj, hprob, hint, hmean, ⟨B, hB, habs, henergy⟩, hright, hnonlattice,
    hweak, hnear, hnotStrong, hdet, epsilon, hepsilon, heps1, ?_⟩
  intro level hlevel hsmall
  obtain ⟨a0, theta, L, ha0s, htheta, hcov, hmeanPoint, hstationary, htheta1, htheta2,
      hL, hlambda, hIpos, hIfinite, hglobal, hunique, hfar⟩ := hregular level hlevel hsmall
  refine ⟨a0, theta, L, ha0s, htheta, hcov, hmeanPoint, hstationary, htheta1, htheta2,
    hL, hlambda, hIpos, hIfinite, hglobal, hunique, hfar, ?_⟩
  let D := parabolaCovariance
    (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))
  let v : Fin 2 → ℝ := ![1, 2 * a0 / level ^ 2]
  let Lambda1 : ℝ := 2 * theta.2 / level ^ 2 + dotProduct v (D⁻¹ *ᵥ v)
  let J0 : ℝ := theta.1 * a0 + theta.2 * (a0 ^ 2 / level ^ 2) -
    Real.log (∫ x : ℝ, Real.exp (theta.1 * x + theta.2 * x ^ 2) ∂mu)
  have h10 : D 1 0 = D 0 1 := rfl
  have hRows : ∀ w : ℝ × ℝ, L w =
      (D 0 0 * w.1 + D 0 1 * w.2, D 1 0 * w.1 + D 1 1 * w.2) := by
    intro w
    have h := congrArg (fun A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) => A w) hL
    change L w = (D 0 0 * w.1 + D 0 1 * w.2,
      D 0 1 * w.1 + D 1 1 * w.2) at h
    simpa only [h10] using h
  have hLambdaEq : 2 * theta.2 / level ^ 2 +
      (L.symm (1, 2 * a0 / level ^ 2)).1 +
        (2 * a0 / level ^ 2) * (L.symm (1, 2 * a0 / level ^ 2)).2 = Lambda1 := by
    have hq := (covariance_row_equivalence_inverse_quadratic D hcov.ne' L hRows
      (1, 2 * a0 / level ^ 2)).2
    dsimp only [Lambda1, v]
    simpa only [Prod.fst, Prod.snd, one_mul, add_assoc] using
      congrArg (fun x : ℝ => 2 * theta.2 / level ^ 2 + x) hq
  have hLambda : 0 < Lambda1 := by rw [← hLambdaEq]; exact hlambda
  have hRate : Shao.Probability.bivariateLegendreRate mu
      (fun x : ℝ => (x, x ^ 2)) (a0, a0 ^ 2 / level ^ 2) = (J0 : EReal) := by
    have h := (open_domain_quadratic_tilt_legendre_attained mu theta htheta).2
    change Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
      (∫ x : ℝ, x ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2),
        ∫ x : ℝ, x ^ 2 ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)) =
      ((theta.1 * (∫ x : ℝ, x ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)) +
        theta.2 * (∫ x : ℝ, x ^ 2 ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)) -
        Real.log (∫ x : ℝ, Real.exp (theta.1 * x + theta.2 * x ^ 2) ∂mu) : ℝ) : EReal) at h
    have hm1 := congrArg Prod.fst hmeanPoint
    have hm2 := congrArg Prod.snd hmeanPoint
    dsimp only [Prod.fst, Prod.snd] at hm1 hm2
    rw [hmeanPoint, hm1, hm2] at h
    exact h
  have hTrueUnique (w : ℝ × ℝ) (hw : 0 < w.2 ∧ level * Real.sqrt w.2 ≤ w.1) :
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
          (a0, a0 ^ 2 / level ^ 2) ≤
        Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w ∧
      (Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w =
        Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
          (a0, a0 ^ 2 / level ^ 2) ↔ w = (a0, a0 ^ 2 / level ^ 2)) := by
    refine ⟨hglobal w hw.1 hw.2, ?_⟩
    constructor
    · intro heq
      exact hunique w hw.1 hw.2 heq.le
    · intro heq
      rw [heq]
  obtain ⟨c, hc, R, hR, _hBaseWC, hcompact⟩ := hweak
  obtain ⟨m, _hm, _hm1, hnewc, hFamily⟩ := hcompact {theta} isCompact_singleton
  have hWC := (hFamily theta (by simp)).2.2
  have hWCtheta : ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic
        (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)) xi eta‖ ≤
          1 - (m ^ 2 * c / 2) *
            Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-((3 : ℝ) / 8)) := by
    simpa only [neg_div] using hWC
  refine ⟨hRate, hLambda, ?_⟩
  exact bounded_canonical_actual_tail_scaled_expansion mu theta htheta hcov
    level a0 hlevel ha0s htheta2 hmeanPoint hstationary B hB.le
      (habs.mono fun _ hx => hx.2) ((3 : ℝ) / 8) (m ^ 2 * c / 2) R
        (by norm_num) (by norm_num) hnewc hR hWCtheta hLambda hTrueUnique

end
end Shao.OQ3
