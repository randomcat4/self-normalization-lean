import Shao.OQ3.SourceCanonicalRate
import Shao.OQ3.SourceLogPartitionDerivatives
import Shao.OQ3.SourceGeometricScale
import Shao.OQ3.PositiveRate

/-!
# Same-source canonical saddle, actual Hessian and geometric scale

Source: current/oq3/proofs/r1/report.md 141–159, 239–257 and 431–443.
Source SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U20d scope: d38dd216682cb45f1bffe2641c441d6e4ca08affa320c272e77740821a516c5f.
-/

namespace Shao.OQ3
open MeasureTheory Shao.Probability
open scoped Matrix Topology BigOperators
noncomputable section

theorem source_canonical_saddle_hessian_and_scale
    (q : ℝ) (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 < w i)
    (hm : ∀ k : Fin 4,
      HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
        (constraintTarget q k)) :
    let P : Measure ℝ := originalMeasure sourceEll w
    letI : IsProbabilityMeasure P := originalMeasure_isProbabilityMeasure sourceEll w
      (fun i => (hw i).le)
      (by simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one]
        using hm 0)
    let W : ℝ → ℝ × ℝ := fun x => (x, x ^ 2)
    ∃ lift : (Fin 2 → ℝ) → bivariateMGFDomain P W,
      (∀ theta, (lift theta : ℝ × ℝ) = (theta 0, theta 1)) ∧
      let K : (Fin 2 → ℝ) → ℝ := fun theta => bivariateLogMGF P W (lift theta)
      let theta0 : Fin 2 → ℝ := ![8 * sourceEll, -sourceEll]
      let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (atomicMeasure w)
      let pr : Fin 2 → ((Fin 2 → ℝ) →L[ℝ] ℝ) := fun i => ContinuousLinearMap.proj i
      let gradient : (Fin 2 → ℝ) →L[ℝ] ℝ :=
        (pr 0).smulRight (q / 4) + (pr 1).smulRight q
      let hessian : (Fin 2 → ℝ) →L[ℝ] ((Fin 2 → ℝ) →L[ℝ] ℝ) :=
        ∑ i : Fin 2, ∑ j : Fin 2, (pr i).smulRight ((pr j).smulRight (D i j))
      let x0 : ℝ := Real.sqrt q / 4
      let a0 : ℝ := q / 4
      let s0 : ℝ := 8 * sourceEll
      let t0 : ℝ := -sourceEll
      let v : Fin 2 → ℝ := ![1, 2 * a0 / x0 ^ 2]
      let lambda0 : ℝ := s0 * a0 + t0 * q - K theta0
      let lambda1 : ℝ := 2 * t0 / x0 ^ 2 + dotProduct v (D⁻¹ *ᵥ v)
      let vCorr : ℝ := (-t0) * Real.sqrt D.det * Real.sqrt lambda1
      (∀ theta, K theta =
        Real.log (∫ x : ℝ, Real.exp (theta 0 * x + theta 1 * x ^ 2) ∂P)) ∧
      HasFDerivAt K gradient theta0 ∧
      HasFDerivAt (fun theta => fderiv ℝ K theta) hessian theta0 ∧
      (∀ u : Fin 2 → ℝ, u ≠ 0 → 0 < dotProduct u (D *ᵥ u)) ∧
      0 < x0 ∧ q = a0 ^ 2 / x0 ^ 2 ∧ s0 = -2 * a0 * t0 / x0 ^ 2 ∧ t0 < 0 ∧
      lambda0 = saddleRate sourceEll q w ∧ 0 < lambda0 ∧
      0 < D.det ∧ 0 < lambda1 ∧ 0 < vCorr ∧
      correctedInverseScale sourceEll q (atomicMeasure w) = vCorr⁻¹ := by
  have hw0 : ∀ i, 0 ≤ w i := fun i => (hw i).le
  have hs : HasSum w 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  let P : Measure ℝ := originalMeasure sourceEll w
  letI : IsProbabilityMeasure P := originalMeasure_isProbabilityMeasure sourceEll w hw0 hs
  letI : IsProbabilityMeasure (atomicMeasure w) := atomicMeasure_isProbabilityMeasure w hw0 hs
  let W : ℝ → ℝ × ℝ := fun x => (x, x ^ 2)
  obtain ⟨hdom, hlog, thetaStar, hthetaStar, htest, _⟩ :=
    source_canonical_rate_unique_minimizer q hq0 hq1 w hw0 hm
  let lift : (Fin 2 → ℝ) → bivariateMGFDomain P W := fun theta =>
    ⟨(theta 0, theta 1), by rw [hdom]; exact Set.mem_univ _⟩
  refine ⟨lift, fun _ => rfl, ?_⟩
  let K : (Fin 2 → ℝ) → ℝ := fun theta => bivariateLogMGF P W (lift theta)
  let theta0 : Fin 2 → ℝ := ![8 * sourceEll, -sourceEll]
  let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (atomicMeasure w)
  let pr : Fin 2 → ((Fin 2 → ℝ) →L[ℝ] ℝ) := fun i => ContinuousLinearMap.proj i
  let gradient : (Fin 2 → ℝ) →L[ℝ] ℝ :=
    (pr 0).smulRight (q / 4) + (pr 1).smulRight q
  let hessian : (Fin 2 → ℝ) →L[ℝ] ((Fin 2 → ℝ) →L[ℝ] ℝ) :=
    ∑ i : Fin 2, ∑ j : Fin 2, (pr i).smulRight ((pr j).smulRight (D i j))
  let x0 : ℝ := Real.sqrt q / 4
  let a0 : ℝ := q / 4
  let s0 : ℝ := 8 * sourceEll
  let t0 : ℝ := -sourceEll
  let v : Fin 2 → ℝ := ![1, 2 * a0 / x0 ^ 2]
  let lambda0 : ℝ := s0 * a0 + t0 * q - K theta0
  let lambda1 : ℝ := 2 * t0 / x0 ^ 2 + dotProduct v (D⁻¹ *ᵥ v)
  let vCorr : ℝ := (-t0) * Real.sqrt D.det * Real.sqrt lambda1
  change (∀ theta, K theta =
      Real.log (∫ x : ℝ, Real.exp (theta 0 * x + theta 1 * x ^ 2) ∂P)) ∧
    HasFDerivAt K gradient theta0 ∧
    HasFDerivAt (fun theta => fderiv ℝ K theta) hessian theta0 ∧
    (∀ u : Fin 2 → ℝ, u ≠ 0 → 0 < dotProduct u (D *ᵥ u)) ∧
    0 < x0 ∧ q = a0 ^ 2 / x0 ^ 2 ∧ s0 = -2 * a0 * t0 / x0 ^ 2 ∧ t0 < 0 ∧
    lambda0 = saddleRate sourceEll q w ∧ 0 < lambda0 ∧
    0 < D.det ∧ 0 < lambda1 ∧ 0 < vCorr ∧
    correctedInverseScale sourceEll q (atomicMeasure w) = vCorr⁻¹
  have hK : K = fun theta : Fin 2 → ℝ =>
      Real.log (∫ x : ℝ, Real.exp (theta 0 * x + theta 1 * x ^ 2) ∂P) := by
    funext theta
    exact (hlog (lift theta)).2
  have hd := source_log_partition_first_and_second_derivatives q w hw0 hm
  have hfirst : HasFDerivAt K gradient theta0 := by
    rw [hK]
    exact hd.1
  have hsecond : HasFDerivAt (fun theta => fderiv ℝ K theta) hessian theta0 := by
    rw [hK]
    exact hd.2
  have hb : ∀ᵐ x ∂atomicMeasure w, |x| ≤ 4 + Real.sqrt 10 :=
    (atomicMeasure_ae_bounds w).mono fun _ hx => hx.2
  have hbp (i : Fin 4) : 0 < (atomicMeasure w).real {baseAtom i} := by
    change 0 < (atomicMeasure w).real {fixedAtom (Sum.inl i)}
    rw [atomicMeasure_real_singleton w hw0]
    exact hw (Sum.inl i)
  have hposdef (u : Fin 2 → ℝ) (hu : u ≠ 0) : 0 < dotProduct u (D *ᵥ u) := by
    have hne : u 0 ≠ 0 ∨ u 1 ≠ 0 := by
      by_cases h0 : u 0 = 0
      · right
        intro h1
        apply hu
        ext i
        fin_cases i <;> simp_all
      · exact Or.inl h0
    have hp := centered_parabola_integral_pos (atomicMeasure w) hb hbp (u 0) (u 1) hne
    rw [centered_parabola_integral_eq (atomicMeasure w) hb] at hp
    have hsym : D 1 0 = D 0 1 := rfl
    have heq : dotProduct u (D *ᵥ u) =
        u 0 ^ 2 * D 0 0 + 2 * u 0 * u 1 * D 0 1 + u 1 ^ 2 * D 1 1 := by
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      rw [hsym]
      ring
    rw [heq]
    exact hp
  have hq : 0 < q := lt_trans zero_lt_one hq0
  have hx0 : 0 < x0 := div_pos (Real.sqrt_pos.mpr hq) (by norm_num)
  have hx0sq : x0 ^ 2 = q / 16 := by
    dsimp [x0]
    rw [div_pow, Real.sq_sqrt hq.le]
    norm_num
  have hqeq : q = a0 ^ 2 / x0 ^ 2 := by
    rw [hx0sq]
    dsimp [a0]
    field_simp [hq.ne']
    <;> ring
  have hseq : s0 = -2 * a0 * t0 / x0 ^ 2 := by
    rw [hx0sq]
    dsimp [s0, a0, t0]
    field_simp [hq.ne']
    <;> ring
  have ht0 : t0 < 0 := neg_neg_of_pos sourceEll_pos
  have hlift0 : lift theta0 = thetaStar := by
    apply Subtype.ext
    exact hthetaStar.symm
  have hvalue : lambda0 = saddleRate sourceEll q w := by
    dsimp only [lambda0, K]
    rw [hlift0]
    rw [hthetaStar] at htest
    exact htest
  have hlambda0 : 0 < lambda0 := by
    rw [hvalue]
    exact saddleRate_pos sourceEll q sourceEll_pos.ne' w hw hm
  have hgeo := source_corrected_scale_geometric_identity q hq0 hq1 w hw0
    (fun i => hw (Sum.inl i)) hm
  change 0 < D.det ∧ 0 < lambda1 ∧
    0 < sourceEll * Real.sqrt D.det * Real.sqrt lambda1 ∧
    correctedInverseScale sourceEll q (atomicMeasure w) =
      (sourceEll * Real.sqrt D.det * Real.sqrt lambda1)⁻¹ at hgeo
  refine ⟨fun theta => congrFun hK theta, hfirst, hsecond, hposdef, hx0, hqeq, hseq,
    ht0, hvalue, hlambda0, hgeo.1, hgeo.2.1, ?_, ?_⟩
  · simpa only [vCorr, t0, neg_neg] using hgeo.2.2.1
  · simpa only [vCorr, t0, neg_neg] using hgeo.2.2.2

end
end Shao.OQ3
