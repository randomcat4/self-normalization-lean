import Shao.OQ3.CorrectedScaleContinuity

/-!
The literal source geometric curvature and its positive corrected scale.
Source: current/oq3/proofs/r1/report.md, 239-257 and 431-443; frozen scope 69.
-/

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology BigOperators
noncomputable section

private theorem inverse_tangent_quadratic (D : Matrix (Fin 2) (Fin 2) ℝ)
    (hs : D 1 0 = D 0 1) :
    dotProduct (![1, 8] : Fin 2 → ℝ) (D⁻¹ *ᵥ ![1, 8]) =
      (64 * D 0 0 - 16 * D 0 1 + D 1 1) / D.det := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hs]
  ring

theorem source_corrected_scale_geometric_identity
    (q : ℝ) (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hbase : ∀ i : Fin 4, 0 < w (Sum.inl i))
    (hm : ∀ k : Fin 4,
      HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
        (constraintTarget q k)) :
    let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (atomicMeasure w)
    let x0 : ℝ := Real.sqrt q / 4
    let a0 : ℝ := q / 4
    let v : Fin 2 → ℝ := ![1, 2 * a0 / x0 ^ 2]
    let curvature : ℝ := 2 * (-sourceEll) / x0 ^ 2 + dotProduct v (D⁻¹ *ᵥ v)
    0 < D.det ∧ 0 < curvature ∧
      0 < sourceEll * Real.sqrt D.det * Real.sqrt curvature ∧
      correctedInverseScale sourceEll q (atomicMeasure w) =
        (sourceEll * Real.sqrt D.det * Real.sqrt curvature)⁻¹ := by
  have hmass : HasSum w 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  let := atomicMeasure_isProbabilityMeasure w hw hmass
  have hb := (atomicMeasure_ae_bounds w).mono fun _ hx => hx.2
  have hbp (i : Fin 4) : 0 < (atomicMeasure w).real {baseAtom i} := by
    change 0 < (atomicMeasure w).real {fixedAtom (Sum.inl i)}
    rw [atomicMeasure_real_singleton w hw]
    exact hbase i
  let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (atomicMeasure w)
  let x0 : ℝ := Real.sqrt q / 4
  let a0 : ℝ := q / 4
  let v : Fin 2 → ℝ := ![1, 2 * a0 / x0 ^ 2]
  let curvature : ℝ := 2 * (-sourceEll) / x0 ^ 2 + dotProduct v (D⁻¹ *ᵥ v)
  change 0 < D.det ∧ 0 < curvature ∧
    0 < sourceEll * Real.sqrt D.det * Real.sqrt curvature ∧
    correctedInverseScale sourceEll q (atomicMeasure w) =
      (sourceEll * Real.sqrt D.det * Real.sqrt curvature)⁻¹
  have hD : 0 < D.det := parabolaCovariance_det_pos (atomicMeasure w) hb hbp
  have hq : 0 < q := lt_trans zero_lt_one hq0
  have hsqrtq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hx0 : 0 < x0 := div_pos hsqrtq (by norm_num)
  have hx0sq : x0 ^ 2 = q / 16 := by
    dsimp [x0]
    rw [div_pow, Real.sq_sqrt hq.le]
    norm_num
  have hv2 : 2 * a0 / x0 ^ 2 = 8 := by
    rw [hx0sq]
    dsimp [a0]
    field_simp [hq.ne']
    norm_num
  have hv : v = ![1, 8] := by dsimp only [v]; rw [hv2]
  have hneg : 2 * (-sourceEll) / x0 ^ 2 = -32 * sourceEll / q := by
    rw [hx0sq]
    field_simp [hq.ne']
    <;> ring
  have hquad : dotProduct (![1, 8] : Fin 2 → ℝ) (D⁻¹ *ᵥ ![1, 8]) =
      normalVariance (atomicMeasure w) / D.det := by
    rw [inverse_tangent_quadratic D (by rfl), normalVariance_eq_covariance (atomicMeasure w) hb]
  have hcurvature : curvature = normalVariance (atomicMeasure w) / D.det -
      32 * sourceEll / q := by
    dsimp only [curvature]
    rw [hv, hneg, hquad]
    ring
  have hcurv : 0 < curvature := by
    rw [hcurvature]
    exact atomic_curvature_pos q hq0 hq1 w hw hbase hm
  have hprod : D.det * curvature = normalVariance (atomicMeasure w) -
      (32 * sourceEll / q) * D.det := by
    calc
      D.det * curvature =
          (normalVariance (atomicMeasure w) / D.det - 32 * sourceEll / q) * D.det := by
        rw [hcurvature]
        ring
      _ = _ := by rw [sub_mul, div_mul_cancel₀ _ hD.ne']
  have hsqrt : Real.sqrt (normalVariance (atomicMeasure w) -
      (32 * sourceEll / q) * D.det) = Real.sqrt D.det * Real.sqrt curvature := by
    rw [← hprod, Real.sqrt_mul hD.le]
  refine ⟨hD, hcurv, mul_pos (mul_pos sourceEll_pos (Real.sqrt_pos.mpr hD))
    (Real.sqrt_pos.mpr hcurv), ?_⟩
  unfold correctedInverseScale
  change (sourceEll * Real.sqrt (normalVariance (atomicMeasure w) -
    (32 * sourceEll / q) * D.det))⁻¹ = _
  simp only [hsqrt, mul_assoc]

end
end Shao.OQ3
