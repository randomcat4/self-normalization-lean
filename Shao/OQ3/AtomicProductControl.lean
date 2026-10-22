import Shao.OQ3.AtomicTailControl
import Shao.OQ3.SampleBoundary
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Finite product expectation errors on the actual common atom support

Source: current/oq3/proofs/r1/report.md, lines 499-520.
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U11c scope: 7308b8a152c069b947ec8e26d7d9cc4524e8711b9893b7bb8d9e05a8354ccf11.
This compares tilted-law expectations directly through weight L1.
-/

namespace Shao.OQ3

open MeasureTheory
open scoped Matrix

noncomputable section

private theorem summable_atomic_weighted (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : Summable w) (B : ℝ)
    (f : ℝ → ℝ) (hf : ∀ i, |f (fixedAtom i)| ≤ B) :
    Summable (fun i => w i * f (fixedAtom i)) := by
  apply (hs.mul_right B).of_norm_bounded
  intro i
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw i)]
  exact mul_le_mul_of_nonneg_left (hf i) (hw i)

theorem atomicMeasure_integrable_of_atom_bound (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : Summable w) (B : ℝ) (hB : 0 ≤ B)
    (f : ℝ → ℝ) (hf : ∀ i, |f (fixedAtom i)| ≤ B) :
  Integrable f (atomicMeasure w) := by
  apply (integrable_atomicMeasure_iff w hw f).mpr
  have hnorm : ‖B‖ = B := Real.norm_of_nonneg hB
  apply (hs.mul_right ‖B‖).of_norm_bounded
  intro i
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw i), Real.norm_eq_abs,
    abs_abs, hnorm]
  exact mul_le_mul_of_nonneg_left (hf i) (hw i)

theorem atomicMeasure_integral_sub_le (w v : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hsw : Summable w) (hsv : Summable v) (B : ℝ) (hB : 0 ≤ B)
    (f : ℝ → ℝ) (hf : ∀ i, |f (fixedAtom i)| ≤ B) :
  |(∫ x, f x ∂atomicMeasure w) - (∫ x, f x ∂atomicMeasure v)| ≤
    B * atomicMassL1 w v := by
  have hfw := atomicMeasure_integrable_of_atom_bound w hw hsw B hB f hf
  have hfv := atomicMeasure_integrable_of_atom_bound v hv hsv B hB f hf
  have hswf := summable_atomic_weighted w hw hsw B f hf
  have hsvf := summable_atomic_weighted v hv hsv B f hf
  have hdiff : Summable (fun i => (w i - v i) * f (fixedAtom i)) := by
    simpa only [sub_mul] using hswf.sub hsvf
  rw [integral_atomicMeasure w hw f hfw, integral_atomicMeasure v hv f hfv,
    ← (hswf.hasSum.sub hsvf.hasSum).tsum_eq]
  simp_rw [← sub_mul]
  calc
    |∑' i, (w i - v i) * f (fixedAtom i)| ≤
        ∑' i, |(w i - v i) * f (fixedAtom i)| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hdiff.norm
    _ ≤ ∑' i, B * |w i - v i| := by
      apply Summable.tsum_le_tsum _ hdiff.abs ((hsw.sub hsv).abs.mul_left B)
      intro i
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hf i) (abs_nonneg _)).trans_eq (mul_comm _ _)
    _ = B * atomicMassL1 w v := by rw [tsum_mul_left, atomicMassL1]

private theorem atomic_product_ae_bound (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (n : ℕ) (B : ℝ)
    (f : Shao.Path n → ℝ)
    (hbound : ∀ z : Fin n → AtomicIndex, |f (fun i => fixedAtom (z i))| ≤ B) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin n => atomicMeasure w), |f z| ≤ B := by
  classical
  let := atomicMeasure_isProbabilityMeasure w hw hs
  have hcoords (i : Fin n) : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => atomicMeasure w),
      z i ∈ Set.range fixedAtom :=
    (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => atomicMeasure w)
      (i := i)).eventually (atomicMeasure_ae_range w)
  filter_upwards [ae_all_iff.mpr hcoords] with z hz
  choose a ha using hz
  have heq : (fun i => fixedAtom (a i)) = z := funext ha
  simpa only [heq] using hbound a

private theorem atom_cons_bound {n : ℕ} (B : ℝ) (f : Shao.Path (n + 1) → ℝ)
    (hbound : ∀ z : Fin (n + 1) → AtomicIndex,
      |f (fun i => fixedAtom (z i))| ≤ B) (a : AtomicIndex) :
    ∀ z : Fin n → AtomicIndex,
      |f (Fin.cons (fixedAtom a) (fun i => fixedAtom (z i)))| ≤ B := by
  intro z
  have h := hbound (Fin.cons a z)
  change |f (fixedAtom ∘ Fin.cons a z)| ≤ B at h
  rw [Fin.comp_cons] at h
  exact h

private theorem measurable_atom_cons {n : ℕ} (f : Shao.Path (n + 1) → ℝ)
    (hf : Measurable f) :
    Measurable (fun t : ℝ × Shao.Path n => f (Fin.cons t.1 t.2)) := by
  have h := hf.comp (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm.measurable
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Equiv.coe_fn_mk, Function.comp_def, cast_eq] using h

private theorem atomic_product_integral_split (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (n : ℕ) (B : ℝ)
    (f : Shao.Path (n + 1) → ℝ) (hf : Measurable f)
    (hbound : ∀ z : Fin (n + 1) → AtomicIndex,
      |f (fun i => fixedAtom (z i))| ≤ B) :
    (∫ z, f z ∂Measure.pi (fun _ : Fin (n + 1) => atomicMeasure w)) =
      ∫ x, ∫ z, f (Fin.cons x z) ∂Measure.pi (fun _ : Fin n => atomicMeasure w)
        ∂atomicMeasure w := by
  let := atomicMeasure_isProbabilityMeasure w hw hs
  let F : ℝ × Shao.Path n → ℝ := fun t => f (Fin.cons t.1 t.2)
  have hF := measurable_atom_cons f hf
  have hFb : ∀ᵐ t ∂(atomicMeasure w).prod
      (Measure.pi (fun _ : Fin n => atomicMeasure w)), ‖F t‖ ≤ B := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hF.norm measurable_const)).mpr
    filter_upwards [atomicMeasure_ae_range w] with x hx
    obtain ⟨a, rfl⟩ := hx
    simpa only [Real.norm_eq_abs, F] using
      atomic_product_ae_bound w hw hs n B (fun z => f (Fin.cons (fixedAtom a) z))
        (atom_cons_bound B f hbound a)
  have hFi : Integrable F ((atomicMeasure w).prod
      (Measure.pi (fun _ : Fin n => atomicMeasure w))) :=
    Integrable.of_bound hF.aestronglyMeasurable B hFb
  calc
    _ = ∫ t, F t ∂(atomicMeasure w).prod
        (Measure.pi (fun _ : Fin n => atomicMeasure w)) := by
      have h := ((measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => atomicMeasure w) 0).symm).integral_comp' f
      simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk,
        Function.comp_def, cast_eq, F] using h.symm
    _ = _ := integral_prod F hFi

theorem atomic_iid_integral_sub_le (w v : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hsw : HasSum w 1) (hsv : HasSum v 1) (n : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (f : Shao.Path n → ℝ) (hf : Measurable f)
    (hbound : ∀ z : Fin n → AtomicIndex, |f (fun i => fixedAtom (z i))| ≤ B) :
  |(∫ z, f z ∂Measure.pi (fun _ : Fin n => atomicMeasure w)) -
      (∫ z, f z ∂Measure.pi (fun _ : Fin n => atomicMeasure v))| ≤
    B * (n : ℝ) * atomicMassL1 w v := by
  let := atomicMeasure_isProbabilityMeasure w hw hsw
  let := atomicMeasure_isProbabilityMeasure v hv hsv
  induction n with
  | zero =>
    have heq : Measure.pi (fun _ : Fin 0 => atomicMeasure w) =
        Measure.pi (fun _ : Fin 0 => atomicMeasure v) := by
      rw [Measure.pi_of_empty, Measure.pi_of_empty]
    rw [heq, sub_self, abs_zero]
    simp
  | succ n ih =>
    let g (x : ℝ) : ℝ :=
      ∫ z, f (Fin.cons x z) ∂Measure.pi (fun _ : Fin n => atomicMeasure w)
    let h (x : ℝ) : ℝ :=
      ∫ z, f (Fin.cons x z) ∂Measure.pi (fun _ : Fin n => atomicMeasure v)
    have hF := measurable_atom_cons f hf
    have hslices (x : ℝ) : Measurable (fun z : Shao.Path n => f (Fin.cons x z)) :=
      hF.comp (measurable_const.prodMk measurable_id)
    have hg (a : AtomicIndex) : |g (fixedAtom a)| ≤ B := by
      have hh := norm_integral_le_of_norm_le_const
        (μ := Measure.pi (fun _ : Fin n => atomicMeasure w))
        (f := fun z => f (Fin.cons (fixedAtom a) z)) (C := B)
        ((atomic_product_ae_bound w hw hsw n B
          (fun z => f (Fin.cons (fixedAtom a) z)) (atom_cons_bound B f hbound a)).mono
          (fun _ hx => by simpa only [Real.norm_eq_abs] using hx))
      simpa [g, Real.norm_eq_abs, measureReal_def] using hh
    have hh (a : AtomicIndex) : |h (fixedAtom a)| ≤ B := by
      have hh := norm_integral_le_of_norm_le_const
        (μ := Measure.pi (fun _ : Fin n => atomicMeasure v))
        (f := fun z => f (Fin.cons (fixedAtom a) z)) (C := B)
        ((atomic_product_ae_bound v hv hsv n B
          (fun z => f (Fin.cons (fixedAtom a) z)) (atom_cons_bound B f hbound a)).mono
          (fun _ hx => by simpa only [Real.norm_eq_abs] using hx))
      simpa [h, Real.norm_eq_abs, measureReal_def] using hh
    have hgi := atomicMeasure_integrable_of_atom_bound w hw hsw.summable B hB g hg
    have hhi := atomicMeasure_integrable_of_atom_bound w hw hsw.summable B hB h hh
    have hgh : ∀ a, |g (fixedAtom a) - h (fixedAtom a)| ≤
        B * (n : ℝ) * atomicMassL1 w v := by
      intro a
      exact ih (fun z => f (Fin.cons (fixedAtom a) z)) (hslices _) (atom_cons_bound B f hbound a)
    have hrest : |(∫ x, g x ∂atomicMeasure w) - (∫ x, h x ∂atomicMeasure w)| ≤
        B * (n : ℝ) * atomicMassL1 w v := by
      rw [← integral_sub hgi hhi]
      have hb : ∀ᵐ x ∂atomicMeasure w, ‖g x - h x‖ ≤
          B * (n : ℝ) * atomicMassL1 w v := by
        filter_upwards [atomicMeasure_ae_range w] with x hx
        obtain ⟨a, rfl⟩ := hx
        simpa only [Real.norm_eq_abs] using hgh a
      simpa [Real.norm_eq_abs, measureReal_def] using
        norm_integral_le_of_norm_le_const hb
    have hfirst := atomicMeasure_integral_sub_le w v hw hv hsw.summable hsv.summable B hB h hh
    rw [atomic_product_integral_split w hw hsw n B f hf hbound,
      atomic_product_integral_split v hv hsv n B f hf hbound]
    change |(∫ x, g x ∂atomicMeasure w) - (∫ x, h x ∂atomicMeasure v)| ≤ _
    calc
      _ ≤ |(∫ x, g x ∂atomicMeasure w) - (∫ x, h x ∂atomicMeasure w)| +
          |(∫ x, h x ∂atomicMeasure w) - (∫ x, h x ∂atomicMeasure v)| := abs_sub_le _ _ _
      _ ≤ B * (n : ℝ) * atomicMassL1 w v + B * atomicMassL1 w v := add_le_add hrest hfirst
      _ = B * ((n + 1 : ℕ) : ℝ) * atomicMassL1 w v := by push_cast; ring

theorem finite_limit_iid_integral_tail_le (ell : ℝ) (hell : 0 ≤ ell) (q : ℝ)
    (p : Fin 4 → ℝ) (r : ℕ → ℝ) (hr : ∀ j, 0 ≤ r j) (hs : Summable r) (J : ℕ)
    (hM : (constraintMatrix ell).det ≠ 0)
    (hc : (constraintMatrix ell) *ᵥ p = constraintTarget q)
    (hl : ∀ i, 0 ≤ limitingBase ell p r i) (hj : ∀ i, 0 ≤ finiteBase ell p r J i)
    (n : ℕ) (B : ℝ) (hB : 0 ≤ B) (f : Shao.Path n → ℝ) (hf : Measurable f)
    (hbound : ∀ z : Fin n → AtomicIndex, |f (fun i => fixedAtom (z i))| ≤ B) :
  |(∫ z, f z ∂Measure.pi (fun _ : Fin n => atomicMeasure (limitingMass ell p r))) -
      (∫ z, f z ∂Measure.pi (fun _ : Fin n => atomicMeasure (finiteMass ell p r J)))| ≤
    B * (n : ℝ) * compensationTailConstant ell * (∑' j, r (J + j)) := by
  have hwl : ∀ i, 0 ≤ limitingMass ell p r i := by
    intro i
    cases i with
    | inl i => exact hl i
    | inr j => exact hr j
  have hwj := finiteMass_nonneg ell p r J hj hr
  have hml : HasSum (limitingMass ell p r) 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using
      limitingMoment_hasSum ell q hell p r hM hc hr hs 0
  have hmj : HasSum (finiteMass ell p r J) 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using
      finiteMass_constraints ell q p r J hM hc 0
  have h := atomic_iid_integral_sub_le _ _ hwl hwj hml hmj n B hB f hf hbound
  exact h.trans ((mul_le_mul_of_nonneg_left
    (atomicMassL1_limiting_finite_le ell hell p r hr hs J)
    (mul_nonneg hB (Nat.cast_nonneg n))).trans_eq (by ring))

theorem finite_limit_likelihood_tail_le (ell : ℝ) (hell : 0 ≤ ell) (q : ℝ) (hq : q ≤ 2)
    (p : Fin 4 → ℝ) (r : ℕ → ℝ) (hr : ∀ j, 0 ≤ r j) (hs : Summable r) (J : ℕ)
    (hM : (constraintMatrix ell).det ≠ 0)
    (hc : (constraintMatrix ell) *ᵥ p = constraintTarget q)
    (hl : ∀ i, 0 ≤ limitingBase ell p r i) (hj : ∀ i, 0 ≤ finiteBase ell p r J i)
    (n : ℕ) :
  |(∫ z, (sourceTail q n).indicator (fun z => Real.exp (-ell * normalDeviation q z)) z
      ∂Measure.pi (fun _ : Fin n => atomicMeasure (limitingMass ell p r))) -
    (∫ z, (sourceTail q n).indicator (fun z => Real.exp (-ell * normalDeviation q z)) z
      ∂Measure.pi (fun _ : Fin n => atomicMeasure (finiteMass ell p r J)))| ≤
    Real.exp (11 * ell * (n : ℝ)) * (n : ℝ) * compensationTailConstant ell *
      (∑' j, r (J + j)) := by
  classical
  have hf : Measurable (fun z : Shao.Path n => Real.exp (-ell * normalDeviation q z)) := by
    unfold normalDeviation normalValue
    fun_prop
  apply finite_limit_iid_integral_tail_le ell hell q p r hr hs J hM hc hl hj n _
    (Real.exp_pos _).le _ (hf.indicator (sourceTail_measurable q n))
  intro z
  by_cases hz : (fun i => fixedAtom (z i)) ∈ sourceTail q n
  · rw [Set.indicator_of_mem hz, abs_of_pos (Real.exp_pos _)]
    exact normal_likelihood_weight_bound ell q hell hq n _
      (fun i => fixedAtom_normalValue_lower (z i))
  · rw [Set.indicator_of_notMem hz, abs_zero]
    exact (Real.exp_pos _).le

end
end Shao.OQ3
