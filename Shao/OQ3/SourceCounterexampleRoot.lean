import Shao.OQ3.SourceRemainderNotBigO
import Shao.OQ3.SourceCanonicalSaddle

/-!
# One fixed jointly nonlattice law violating the saddle remainder bound

Source: current/oq3/proofs/r1/report.md, 141–307 and 495–558, equation (31).
Source SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U22a scope: 69ed5bbb5bccadc3b552c75f09b090f775164d4eb0fe9eaa8a1cf0f65f59308b.
-/

namespace Shao.OQ3
open MeasureTheory Shao.Probability
open scoped Matrix Topology BigOperators
noncomputable section

private theorem ratio_tail_measurable (x : ℝ) (n : ℕ) :
    MeasurableSet {z : Shao.Path n |
      x ≤ (∑ i, z i) / (Real.sqrt (n : ℝ) * Real.sqrt (Shao.energy z))} := by
  have hratio : Measurable (fun z : Shao.Path n =>
      (∑ i, z i) / (Real.sqrt (n : ℝ) * Real.sqrt (Shao.energy z))) := by
    unfold Shao.energy
    fun_prop
  exact measurableSet_le measurable_const hratio

private theorem product_energy_pos_ae (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, 1 ≤ |x|) (n : ℕ) (hn : 0 < n) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin n => mu), 0 < Shao.energy z := by
  have hcoords : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => mu), ∀ i : Fin n, 1 ≤ |z i| := by
    rw [ae_all_iff]
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => mu) (i := i)).eventually hb
  filter_upwards [hcoords] with z hz
  have hsq (i : Fin n) : 1 ≤ (z i) ^ 2 := by
    calc
      (1 : ℝ) = (1 : ℝ) ^ 2 := by norm_num
      _ ≤ |z i| ^ 2 := (sq_le_sq₀ (by norm_num) (abs_nonneg _)).mpr (hz i)
      _ = (z i) ^ 2 := sq_abs _
  have hsum : (n : ℝ) ≤ Shao.energy z := by
    calc
      (n : ℝ) = ∑ _i : Fin n, (1 : ℝ) := by simp
      _ ≤ ∑ i : Fin n, (z i) ^ 2 := Finset.sum_le_sum (fun i _ => hsq i)
      _ = Shao.energy z := rfl
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  exact hnR.trans_le hsum

private theorem sourceTail_ae_ratio (q : ℝ) (n : ℕ) (hn : 0 < n)
    (nu : Measure (Shao.Path n)) (hE : ∀ᵐ z ∂nu, 0 < Shao.energy z) :
    sourceTail q n =ᵐ[nu] {z : Shao.Path n |
      Real.sqrt q / 4 ≤ (∑ i, z i) /
        (Real.sqrt (n : ℝ) * Real.sqrt (Shao.energy z))} := by
  filter_upwards [hE] with z hz
  apply propext
  change (0 < Shao.energy z ∧
    Real.sqrt q / 4 * Real.sqrt ((n : ℝ) * Shao.energy z) ≤ ∑ i, z i) ↔ _
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hden : 0 < Real.sqrt (n : ℝ) * Real.sqrt (Shao.energy z) :=
    mul_pos (Real.sqrt_pos.mpr hnR) (Real.sqrt_pos.mpr hz)
  constructor
  · intro h
    apply (le_div_iff₀ hden).mpr
    simpa only [Real.sqrt_mul (Nat.cast_nonneg n)] using h.2
  · intro h
    refine ⟨hz, ?_⟩
    simpa only [Real.sqrt_mul (Nat.cast_nonneg n)] using (le_div_iff₀ hden).mp h

theorem exists_fixed_jointNonlattice_saddleExpansion_counterexample :
    ∃ (q : ℝ) (w : AtomicIndex → ℝ),
      (1 < q ∧ q < 103 / 100 ∧ (∀ i, 0 < w i) ∧
        ∀ k : Fin 4,
          HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
            (constraintTarget q k)) ∧
      let P : Measure ℝ := originalMeasure sourceEll w
      ∃ hP : IsProbabilityMeasure P,
        letI : IsProbabilityMeasure P := hP
        let W : ℝ → ℝ × ℝ := fun x => (x, x ^ 2)
        let x0 : ℝ := Real.sqrt q / 4
        let a0 : ℝ := q / 4
        let s0 : ℝ := 8 * sourceEll
        let t0 : ℝ := -sourceEll
        let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (atomicMeasure w)
        let Dtail : Set (ℝ × ℝ) := {z | 0 < z.2 ∧ x0 * Real.sqrt z.2 ≤ z.1}
        (Integrable (fun x : ℝ => x) P ∧ (∫ x : ℝ, x ∂P) = 0) ∧
          (∀ᵐ x ∂P, 1 ≤ |x| ∧ |x| ≤ 4 + Real.sqrt 10) ∧
          0 < P.real (Set.Ioi 0) ∧
          (∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 → ‖jointCharacteristic P xi eta‖ < 1) ∧
          Filter.Tendsto (fun J => |resonanceXi J| + |resonanceEta J|)
            Filter.atTop Filter.atTop ∧
          Filter.Tendsto (fun J => ‖jointCharacteristic P (resonanceXi J) (resonanceEta J)‖)
            Filter.atTop (nhds (1 : ℝ)) ∧
          bivariateMGFDomain P W = Set.univ ∧
          (∀ theta : bivariateMGFDomain P W,
            (0 < ∫ x : ℝ, Real.exp
              ((theta : ℝ × ℝ).1 * x + (theta : ℝ × ℝ).2 * x ^ 2) ∂P) ∧
            bivariateLogMGF P W theta =
              Real.log (∫ x : ℝ, Real.exp
                ((theta : ℝ × ℝ).1 * x + (theta : ℝ × ℝ).2 * x ^ 2) ∂P)) ∧
          ∃ lift : (Fin 2 → ℝ) → bivariateMGFDomain P W,
            (∀ theta, (lift theta : ℝ × ℝ) = (theta 0, theta 1)) ∧
            let K : (Fin 2 → ℝ) → ℝ := fun theta => bivariateLogMGF P W (lift theta)
            let theta0 : Fin 2 → ℝ := ![s0, t0]
            let pr : Fin 2 → ((Fin 2 → ℝ) →L[ℝ] ℝ) := fun i => ContinuousLinearMap.proj i
            let gradient : (Fin 2 → ℝ) →L[ℝ] ℝ :=
              (pr 0).smulRight a0 + (pr 1).smulRight q
            let hessian : (Fin 2 → ℝ) →L[ℝ] ((Fin 2 → ℝ) →L[ℝ] ℝ) :=
              ∑ i : Fin 2, ∑ j : Fin 2, (pr i).smulRight ((pr j).smulRight (D i j))
            let v : Fin 2 → ℝ := ![1, 2 * a0 / x0 ^ 2]
            let lambda0 : ℝ := s0 * a0 + t0 * q - K theta0
            let lambda1 : ℝ := 2 * t0 / x0 ^ 2 + dotProduct v (D⁻¹ *ᵥ v)
            let vCorr : ℝ := (-t0) * Real.sqrt D.det * Real.sqrt lambda1
            let nu : (n : ℕ) → Measure (Shao.Path n) :=
              fun n => Measure.pi (fun _ : Fin n => P)
            let Tail : (n : ℕ) → Set (Shao.Path n) := fun n =>
              {z | x0 ≤ (∑ i, z i) / (Real.sqrt (n : ℝ) * Real.sqrt (Shao.energy z))}
            let C : ℕ → ℝ := fun n =>
              Real.sqrt (2 * Real.pi * (n : ℝ)) * Real.exp ((n : ℝ) * lambda0) *
                (nu n).real (Tail n)
            (∀ theta, K theta =
              Real.log (∫ x : ℝ, Real.exp (theta 0 * x + theta 1 * x ^ 2) ∂P)) ∧
            HasFDerivAt K gradient theta0 ∧
            HasFDerivAt (fun theta => fderiv ℝ K theta) hessian theta0 ∧
            (∀ u : Fin 2 → ℝ, u ≠ 0 → 0 < dotProduct u (D *ᵥ u)) ∧
            0 < x0 ∧ x0 < 1 / 2 ∧ 0 < a0 ∧
            q = a0 ^ 2 / x0 ^ 2 ∧ s0 = -2 * a0 * t0 / x0 ^ 2 ∧ t0 < 0 ∧
            lambda0 = saddleRate sourceEll q w ∧ 0 < lambda0 ∧
            0 < D.det ∧ 0 < lambda1 ∧ 0 < vCorr ∧
            correctedInverseScale sourceEll q (atomicMeasure w) = vCorr⁻¹ ∧
            (a0, q) ∈ Dtail ∧
            bivariateLegendreRate P W (a0, q) = (lambda0 : EReal) ∧
            (∀ z ∈ Dtail,
              bivariateLegendreRate P W (a0, q) ≤ bivariateLegendreRate P W z ∧
              (bivariateLegendreRate P W z = bivariateLegendreRate P W (a0, q) ↔
                z = (a0, q))) ∧
            (∀ n : ℕ, MeasurableSet (Tail n)) ∧
            (∀ n : ℕ, 0 < n → ∀ᵐ z ∂nu n, 0 < Shao.energy z) ∧
            (∀ n : ℕ, 0 < n → sourceTail q n =ᵐ[nu n] Tail n) ∧
            (∀ n : ℕ, normalizedTailCoefficient sourceEll q w n = C n) ∧
            (∃ nseq : ℕ → ℕ, StrictMono nseq ∧
              Filter.Tendsto nseq Filter.atTop Filter.atTop ∧
              ∀ J : ℕ, 0 < nseq J ∧
                (J : ℝ) < Real.sqrt (nseq J : ℝ) * (C (nseq J) - vCorr⁻¹)) ∧
            ¬ Asymptotics.IsBigO Filter.atTop
              (fun n : ℕ => C n - vCorr⁻¹)
              (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) := by
  obtain ⟨q, w, hq0, hq1, hw, hm, hP, hcenter, hb, hpositive, hnonlattice,
      hescape, hresonance, hxpos, hxupper, _hrate, _hscale,
      ⟨nseq, hmono, htop, hn⟩, hnot⟩ := exists_source_fixed_law_not_isBigO
  refine ⟨q, w, ⟨hq0, hq1, hw, hm⟩, hP, ?_⟩
  let P : Measure ℝ := originalMeasure sourceEll w
  letI : IsProbabilityMeasure P := hP
  let W : ℝ → ℝ × ℝ := fun x => (x, x ^ 2)
  let x0 : ℝ := Real.sqrt q / 4
  let a0 : ℝ := q / 4
  let s0 : ℝ := 8 * sourceEll
  let t0 : ℝ := -sourceEll
  let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (atomicMeasure w)
  let Dtail : Set (ℝ × ℝ) := {z | 0 < z.2 ∧ x0 * Real.sqrt z.2 ≤ z.1}
  have hw0 : ∀ i, 0 ≤ w i := fun i => (hw i).le
  obtain ⟨hdom, hlog, _thetaStar, _hStar, _htest, hcand, hRate, hUnique⟩ :=
    source_canonical_rate_unique_minimizer q hq0 hq1 w hw0 hm
  obtain ⟨lift, hlift, hK, hfirst, hsecond, hpd, _hxpos, hqeq, hseq, ht0,
      hvalue, hlambda0, hdet, hlambda1, hv, hscaleeq⟩ :=
    source_canonical_saddle_hessian_and_scale q hq0 hq1 w hw hm
  refine ⟨hcenter, hb, hpositive, hnonlattice, hescape, hresonance, hdom, hlog,
    lift, hlift, ?_⟩
  let K : (Fin 2 → ℝ) → ℝ := fun theta => bivariateLogMGF P W (lift theta)
  let theta0 : Fin 2 → ℝ := ![s0, t0]
  let pr : Fin 2 → ((Fin 2 → ℝ) →L[ℝ] ℝ) := fun i => ContinuousLinearMap.proj i
  let gradient : (Fin 2 → ℝ) →L[ℝ] ℝ := (pr 0).smulRight a0 + (pr 1).smulRight q
  let hessian : (Fin 2 → ℝ) →L[ℝ] ((Fin 2 → ℝ) →L[ℝ] ℝ) :=
    ∑ i : Fin 2, ∑ j : Fin 2, (pr i).smulRight ((pr j).smulRight (D i j))
  let v : Fin 2 → ℝ := ![1, 2 * a0 / x0 ^ 2]
  let lambda0 : ℝ := s0 * a0 + t0 * q - K theta0
  let lambda1 : ℝ := 2 * t0 / x0 ^ 2 + dotProduct v (D⁻¹ *ᵥ v)
  let vCorr : ℝ := (-t0) * Real.sqrt D.det * Real.sqrt lambda1
  change lambda0 = saddleRate sourceEll q w at hvalue
  change correctedInverseScale sourceEll q (atomicMeasure w) = vCorr⁻¹ at hscaleeq
  let nu : (n : ℕ) → Measure (Shao.Path n) := fun n => Measure.pi (fun _ : Fin n => P)
  let Tail : (n : ℕ) → Set (Shao.Path n) := fun n =>
    {z | x0 ≤ (∑ i, z i) / (Real.sqrt (n : ℝ) * Real.sqrt (Shao.energy z))}
  let C : ℕ → ℝ := fun n =>
    Real.sqrt (2 * Real.pi * (n : ℝ)) * Real.exp ((n : ℝ) * lambda0) *
      (nu n).real (Tail n)
  have hE (n : ℕ) (hn0 : 0 < n) : ∀ᵐ z ∂nu n, 0 < Shao.energy z :=
    product_energy_pos_ae P (hb.mono fun _ hx => hx.1) n hn0
  have hTail (n : ℕ) (hn0 : 0 < n) : sourceTail q n =ᵐ[nu n] Tail n :=
    sourceTail_ae_ratio q n hn0 (nu n) (hE n hn0)
  have hcoeff (n : ℕ) : normalizedTailCoefficient sourceEll q w n = C n := by
    by_cases hn0 : n = 0
    · subst n
      simp only [normalizedTailCoefficient, C, Nat.cast_zero, mul_zero,
        Real.sqrt_zero, zero_mul]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      dsimp only [normalizedTailCoefficient, C, nu]
      rw [hvalue, measureReal_congr (hTail n hnpos)]
  have hRate0 : bivariateLegendreRate P W (a0, q) = (lambda0 : EReal) := by
    rw [hvalue]
    exact hRate
  refine ⟨hK, hfirst, hsecond, hpd, hxpos, hxupper,
    div_pos (lt_trans zero_lt_one hq0) (by norm_num), hqeq, hseq, ht0,
    hvalue, hlambda0, hdet, hlambda1, hv, hscaleeq, hcand, hRate0, hUnique,
    (fun n => ratio_tail_measurable x0 n), hE, hTail, hcoeff,
    ⟨nseq, hmono, htop, ?_⟩, ?_⟩
  · intro J
    simpa only [hcoeff, hscaleeq] using hn J
  · simpa only [hcoeff, hscaleeq] using hnot

end
end Shao.OQ3
