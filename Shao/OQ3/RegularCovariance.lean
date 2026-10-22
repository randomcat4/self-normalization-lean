import Shao.OQ3.FiniteStageMeasure
import Shao.OQ3.PositiveRate
import Mathlib.Probability.Moments.Variance

/-!
# Actual covariance regularity and positive transverse curvature

Source: current/oq3/proofs/r1/report.md, lines 238-258.
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U7 scope: 0fd62d524bbe643f076f153b9b7a898b5eb34d756fc631c483ded0508ed44ee8.
-/

namespace Shao.OQ3

open MeasureTheory
open scoped Matrix

noncomputable section

def parabolaCovariance (mu : Measure ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![ProbabilityTheory.variance (fun x : ℝ => x) mu,
      ProbabilityTheory.covariance (fun x : ℝ => x) (fun x : ℝ => x ^ 2) mu],
    ![ProbabilityTheory.covariance (fun x : ℝ => x) (fun x : ℝ => x ^ 2) mu,
      ProbabilityTheory.variance (fun x : ℝ => x ^ 2) mu]]

def normalVariance (mu : Measure ℝ) : ℝ :=
  ProbabilityTheory.variance normalValue mu

def transverseVariance (mu : Measure ℝ) : ℝ :=
  (parabolaCovariance mu).det / normalVariance mu

theorem centered_parabola_integral_eq (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (a b : ℝ) :
  (∫ x, (a * (x - ∫ y, y ∂mu) + b * (x ^ 2 - ∫ y, y ^ 2 ∂mu)) ^ 2 ∂mu) =
    a ^ 2 * parabolaCovariance mu 0 0 +
      2 * a * b * parabolaCovariance mu 0 1 + b ^ 2 * parabolaCovariance mu 1 1 := by
  have hm1 : AEMeasurable (fun x : ℝ => x) mu := measurable_id.aemeasurable
  have hm2 : AEMeasurable (fun x : ℝ => x ^ 2) mu := by fun_prop
  have h1 : Integrable (fun x : ℝ => (x - ∫ y, y ∂mu) ^ 2) mu := by
    apply integrable_continuous_of_fixed_bounds mu hb
    fun_prop
  have h12 : Integrable (fun x : ℝ => (x - ∫ y, y ∂mu) * (x ^ 2 - ∫ y, y ^ 2 ∂mu)) mu := by
    apply integrable_continuous_of_fixed_bounds mu hb
    fun_prop
  have h2 : Integrable (fun x : ℝ => (x ^ 2 - ∫ y, y ^ 2 ∂mu) ^ 2) mu := by
    apply integrable_continuous_of_fixed_bounds mu hb
    fun_prop
  change (∫ x, (a * (x - ∫ y, y ∂mu) + b * (x ^ 2 - ∫ y, y ^ 2 ∂mu)) ^ 2 ∂mu) =
    a ^ 2 * ProbabilityTheory.variance (fun x : ℝ => x) mu +
      2 * a * b * ProbabilityTheory.covariance (fun x : ℝ => x) (fun x : ℝ => x ^ 2) mu +
      b ^ 2 * ProbabilityTheory.variance (fun x : ℝ => x ^ 2) mu
  rw [ProbabilityTheory.variance_eq_integral hm1, ProbabilityTheory.variance_eq_integral hm2]
  unfold ProbabilityTheory.covariance
  have hfun :
      (fun x : ℝ => (a * (x - ∫ y, y ∂mu) + b * (x ^ 2 - ∫ y, y ^ 2 ∂mu)) ^ 2) =
      (fun x : ℝ => a ^ 2 * (x - ∫ y, y ∂mu) ^ 2 +
        (2 * a * b) * ((x - ∫ y, y ∂mu) * (x ^ 2 - ∫ y, y ^ 2 ∂mu)) +
        b ^ 2 * (x ^ 2 - ∫ y, y ^ 2 ∂mu) ^ 2) := by
    funext x
    ring
  have hsum : Integrable (fun x : ℝ => a ^ 2 * (x - ∫ y, y ∂mu) ^ 2 +
      (2 * a * b) * ((x - ∫ y, y ∂mu) * (x ^ 2 - ∫ y, y ^ 2 ∂mu))) mu :=
    (h1.const_mul (a ^ 2)).add (h12.const_mul (2 * a * b))
  rw [hfun, integral_add hsum (h2.const_mul (b ^ 2)),
    integral_add (h1.const_mul (a ^ 2)) (h12.const_mul (2 * a * b)),
    integral_const_mul, integral_const_mul, integral_const_mul]

private theorem ae_zero_at_positive_atom (mu : Measure ℝ) (f : ℝ → ℝ)
    (hae : ∀ᵐ x ∂mu, f x = 0) (x : ℝ) (hx : 0 < mu.real {x}) : f x = 0 := by
  by_contra hbad
  have hsub : ({x} : Set ℝ) ⊆ {y | f y ≠ 0} := by
    intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact hbad
  have hnull : mu {y | f y ≠ 0} = 0 := ae_iff.mp hae
  have hzero : mu {x} = 0 := le_antisymm ((measure_mono hsub).trans_eq hnull) (by positivity)
  have hreal : mu.real {x} = 0 := by simp only [measureReal_def, hzero, ENNReal.toReal_zero]
  exact (ne_of_gt hx) hreal

theorem centered_parabola_integral_pos (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hbase : ∀ i : Fin 4, 0 < mu.real {baseAtom i})
    (a b : ℝ) (hne : a ≠ 0 ∨ b ≠ 0) :
  0 < ∫ x, (a * (x - ∫ y, y ∂mu) + b * (x ^ 2 - ∫ y, y ^ 2 ∂mu)) ^ 2 ∂mu := by
  have hint : Integrable (fun x : ℝ =>
      (a * (x - ∫ y, y ∂mu) + b * (x ^ 2 - ∫ y, y ^ 2 ∂mu)) ^ 2) mu := by
    apply integrable_continuous_of_fixed_bounds mu hb
    fun_prop
  have hnonneg : 0 ≤ ∫ x,
      (a * (x - ∫ y, y ∂mu) + b * (x ^ 2 - ∫ y, y ^ 2 ∂mu)) ^ 2 ∂mu :=
    integral_nonneg fun _ => sq_nonneg _
  by_contra hnpos
  have hzero := le_antisymm (not_lt.mp hnpos) hnonneg
  have hae := (integral_eq_zero_iff_of_nonneg (fun x : ℝ =>
    sq_nonneg (a * (x - ∫ y, y ∂mu) + b * (x ^ 2 - ∫ y, y ^ 2 ∂mu))) hint).mp hzero
  have hpoint (i : Fin 4) :
      a * (baseAtom i - ∫ y, y ∂mu) + b * ((baseAtom i) ^ 2 - ∫ y, y ^ 2 ∂mu) = 0 :=
    ae_zero_at_positive_atom mu _ (hae.mono fun _ hx => sq_eq_zero_iff.mp hx) _ (hbase i)
  have h0 := hpoint 0
  have h1 := hpoint 1
  have h3 := hpoint 3
  norm_num [baseAtom] at h0 h1 h3
  have ha : a = 0 := by nlinarith [h0, h1]
  have hbzero : b = 0 := by nlinarith [h1, h3]
  rcases hne with hne | hne
  · exact hne ha
  · exact hne hbzero

theorem parabolaCovariance_det_pos (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hbase : ∀ i : Fin 4, 0 < mu.real {baseAtom i}) :
  0 < (parabolaCovariance mu).det := by
  have hA : 0 < parabolaCovariance mu 0 0 := by
    have h := centered_parabola_integral_pos mu hb hbase 1 0 (Or.inl one_ne_zero)
    rw [centered_parabola_integral_eq mu hb 1 0] at h
    simpa using h
  have hq := centered_parabola_integral_pos mu hb hbase
    (-parabolaCovariance mu 0 1) (parabolaCovariance mu 0 0) (Or.inr (ne_of_gt hA))
  rw [centered_parabola_integral_eq mu hb] at hq
  have hsymm : parabolaCovariance mu 1 0 = parabolaCovariance mu 0 1 := rfl
  have hD : (parabolaCovariance mu).det =
      parabolaCovariance mu 0 0 * parabolaCovariance mu 1 1 - (parabolaCovariance mu 0 1) ^ 2 := by
    rw [Matrix.det_fin_two, hsymm]
    ring
  have hprod : 0 < parabolaCovariance mu 0 0 * (parabolaCovariance mu).det := by
    rw [hD]
    nlinarith [hq]
  rcases mul_pos_iff.mp hprod with ⟨_, hdet⟩ | ⟨hneg, _⟩
  · exact hdet
  · linarith

theorem normalVariance_eq_covariance (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) :
  normalVariance mu = 64 * parabolaCovariance mu 0 0 -
    16 * parabolaCovariance mu 0 1 + parabolaCovariance mu 1 1 := by
  have h1 : Integrable (fun x : ℝ => x) mu :=
    integrable_continuous_of_fixed_bounds mu hb _ continuous_id
  have h2 : Integrable (fun x : ℝ => x ^ 2) mu := by
    apply integrable_continuous_of_fixed_bounds mu hb
    fun_prop
  have hmean : (∫ x, normalValue x ∂mu) = 8 * (∫ x, x ∂mu) - ∫ x, x ^ 2 ∂mu := by
    change (∫ x, 8 * x - x ^ 2 ∂mu) = _
    rw [integral_sub (h1.const_mul 8) h2, integral_const_mul]
  have hmeas : AEMeasurable normalValue mu := by
    unfold normalValue
    fun_prop
  rw [normalVariance, ProbabilityTheory.variance_eq_integral hmeas, hmean]
  have hfun :
      (fun x : ℝ => (normalValue x - (8 * (∫ y, y ∂mu) - ∫ y, y ^ 2 ∂mu)) ^ 2) =
      (fun x : ℝ => (8 * (x - ∫ y, y ∂mu) + (-1) * (x ^ 2 - ∫ y, y ^ 2 ∂mu)) ^ 2) := by
    funext x
    unfold normalValue
    ring
  rw [hfun, centered_parabola_integral_eq mu hb 8 (-1)]
  ring

theorem normalVariance_pos (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hbase : ∀ i : Fin 4, 0 < mu.real {baseAtom i}) :
  0 < normalVariance mu := by
  have hq := centered_parabola_integral_pos mu hb hbase 8 (-1) (Or.inl (by norm_num))
  rw [centered_parabola_integral_eq mu hb 8 (-1)] at hq
  rw [normalVariance_eq_covariance mu hb]
  nlinarith [hq]

theorem transverseVariance_pos (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hbase : ∀ i : Fin 4, 0 < mu.real {baseAtom i}) :
  0 < transverseVariance mu := by
  exact div_pos (parabolaCovariance_det_pos mu hb hbase) (normalVariance_pos mu hb hbase)

theorem transverseVariance_le_variance_id (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hbase : ∀ i : Fin 4, 0 < mu.real {baseAtom i}) :
  transverseVariance mu ≤ ProbabilityTheory.variance (fun x : ℝ => x) mu := by
  rw [transverseVariance, div_le_iff₀ (normalVariance_pos mu hb hbase)]
  change (parabolaCovariance mu).det ≤ parabolaCovariance mu 0 0 * normalVariance mu
  have hsymm : parabolaCovariance mu 1 0 = parabolaCovariance mu 0 1 := rfl
  rw [Matrix.det_fin_two, hsymm, normalVariance_eq_covariance mu hb]
  nlinarith [sq_nonneg (8 * parabolaCovariance mu 0 0 - parabolaCovariance mu 0 1)]

theorem atomic_id_variance (ell q : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature ell (fixedAtom i) k)
      (constraintTarget q k)) :
  ProbabilityTheory.variance (fun x : ℝ => x) (atomicMeasure w) = q - q ^ 2 / 16 := by
  have hmass : HasSum w 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  let := atomicMeasure_isProbabilityMeasure w hw hmass
  have hLp : MemLp (fun x : ℝ => x) 2 (atomicMeasure w) :=
    MemLp.of_bound continuous_id.aestronglyMeasurable (4 + Real.sqrt 10)
      (by simpa only [Real.norm_eq_abs] using ((atomicMeasure_ae_bounds w).mono fun _ hx => hx.2))
  rw [ProbabilityTheory.variance_eq_sub hLp]
  change (∫ x, x ^ 2 ∂atomicMeasure w) - (∫ x, x ∂atomicMeasure w) ^ 2 = _
  have hq : (∫ x, x ^ 2 ∂atomicMeasure w) = q := by
    simpa [constraintFeature, constraintTarget] using (atomicMeasure_constraints ell q w hw hm 3).2
  rw [hq, (atomicMeasure_mean ell q w hw hm).2]
  ring

theorem sourceEll_lt_one_div_thirty : sourceEll < (1 : ℝ) / 30 := by
  have h := Real.log_lt_sub_one_of_pos (x := sourceU)
    (by norm_num [sourceU]) (by norm_num [sourceU])
  unfold sourceEll
  convert h using 1
  norm_num [sourceU]

theorem atomic_transverse_bounds (q : ℝ) (hlo : 1 < q) (hhi : q < 103 / 100)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i) (hbase : ∀ i : Fin 4, 0 < w (Sum.inl i))
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
      (constraintTarget q k)) :
  0 < transverseVariance (atomicMeasure w) ∧
    transverseVariance (atomicMeasure w) ≤ q - q ^ 2 / 16 ∧
    (1 : ℝ) / 30 < q / (32 * transverseVariance (atomicMeasure w)) := by
  have hqrange : q ∈ Set.Ioo (1 : ℝ) (103 / 100) := ⟨hlo, hhi⟩
  have hmass : HasSum w 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  let := atomicMeasure_isProbabilityMeasure w hw hmass
  have hb := (atomicMeasure_ae_bounds w).mono fun _ hx => hx.2
  have hbpos (i : Fin 4) : 0 < (atomicMeasure w).real {baseAtom i} := by
    change 0 < (atomicMeasure w).real {fixedAtom (Sum.inl i)}
    rw [atomicMeasure_real_singleton w hw]
    exact hbase i
  have ht := transverseVariance_pos (atomicMeasure w) hb hbpos
  have hle := transverseVariance_le_variance_id (atomicMeasure w) hb hbpos
  rw [atomic_id_variance sourceEll q w hw hm] at hle
  refine ⟨ht, hle, ?_⟩
  apply (lt_div_iff₀ (mul_pos (by norm_num) ht)).mpr
  nlinarith [sq_nonneg (q - 1), hqrange.1]

theorem atomic_curvature_pos (q : ℝ) (hlo : 1 < q) (hhi : q < 103 / 100)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i) (hbase : ∀ i : Fin 4, 0 < w (Sum.inl i))
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
      (constraintTarget q k)) :
  0 < normalVariance (atomicMeasure w) / (parabolaCovariance (atomicMeasure w)).det -
    32 * sourceEll / q := by
  have hmass : HasSum w 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  let := atomicMeasure_isProbabilityMeasure w hw hmass
  have hb := (atomicMeasure_ae_bounds w).mono fun _ hx => hx.2
  have hbpos (i : Fin 4) : 0 < (atomicMeasure w).real {baseAtom i} := by
    change 0 < (atomicMeasure w).real {fixedAtom (Sum.inl i)}
    rw [atomicMeasure_real_singleton w hw]
    exact hbase i
  have hS := normalVariance_pos (atomicMeasure w) hb hbpos
  have hD := parabolaCovariance_det_pos (atomicMeasure w) hb hbpos
  have ht := atomic_transverse_bounds q hlo hhi w hw hbase hm
  have hfrac := sourceEll_lt_one_div_thirty.trans ht.2.2
  have hmul := (lt_div_iff₀ (mul_pos (by norm_num) ht.1)).mp hfrac
  unfold transverseVariance at hmul
  have hdiv : (32 * sourceEll * (parabolaCovariance (atomicMeasure w)).det) /
      normalVariance (atomicMeasure w) < q := by
    convert hmul using 1
    ring
  have hcross := (div_lt_iff₀ hS).mp hdiv
  apply sub_pos.mpr
  apply (div_lt_div_iff₀ (show 0 < q by linarith) hD).mpr
  simpa only [mul_comm] using hcross

theorem exists_source_finite_and_limit_regular_family :
  ∃ (p : Fin 4 → ℝ) (q eps : ℝ), (∀ i, 0 < p i) ∧ 1 < q ∧ q < 103 / 100 ∧
    0 < eps ∧ (constraintMatrix sourceEll) *ᵥ p = constraintTarget q ∧
    ∀ (r : ℕ → ℝ), (∀ j, 0 < r j) → Summable r → (∑' j, r j) < eps →
      IsProbabilityMeasure (atomicMeasure (limitingMass sourceEll p r)) ∧
      0 < normalVariance (atomicMeasure (limitingMass sourceEll p r)) ∧
      0 < (parabolaCovariance (atomicMeasure (limitingMass sourceEll p r))).det ∧
      (0 < normalVariance (atomicMeasure (limitingMass sourceEll p r)) /
        (parabolaCovariance (atomicMeasure (limitingMass sourceEll p r))).det - 32 * sourceEll / q) ∧
      ∀ J : ℕ, IsProbabilityMeasure (atomicMeasure (finiteMass sourceEll p r J)) ∧
        0 < normalVariance (atomicMeasure (finiteMass sourceEll p r J)) ∧
        0 < (parabolaCovariance (atomicMeasure (finiteMass sourceEll p r J))).det ∧
        (0 < normalVariance (atomicMeasure (finiteMass sourceEll p r J)) /
          (parabolaCovariance (atomicMeasure (finiteMass sourceEll p r J))).det - 32 * sourceEll / q) := by
  obtain ⟨p, q, eps, hp, hlo, hhi, heps, hc, hfamily⟩ := exists_source_finite_and_limit_family
  refine ⟨p, q, eps, hp, hlo, hhi, heps, hc, ?_⟩
  intro r hr hs ht
  obtain ⟨hpos, hm, hstages⟩ := hfamily r hr hs ht
  have hw := fun i => (hpos i).le
  have hmass : HasSum (limitingMass sourceEll p r) 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  have hprob := atomicMeasure_isProbabilityMeasure _ hw hmass
  let := hprob
  have hb := (atomicMeasure_ae_bounds (limitingMass sourceEll p r)).mono fun _ hx => hx.2
  have hbpos (i : Fin 4) : 0 < (atomicMeasure (limitingMass sourceEll p r)).real {baseAtom i} := by
    change 0 < (atomicMeasure (limitingMass sourceEll p r)).real {fixedAtom (Sum.inl i)}
    rw [atomicMeasure_real_singleton _ hw]
    exact hpos (Sum.inl i)
  refine ⟨hprob, normalVariance_pos _ hb hbpos, parabolaCovariance_det_pos _ hb hbpos,
    atomic_curvature_pos q hlo hhi _ hw (fun i => hpos (Sum.inl i)) hm, ?_⟩
  intro J
  obtain ⟨hpJ, hmJ, _, _, _⟩ := hstages J
  have hwJ := finiteMass_nonneg sourceEll p r J (fun i => (hpJ i).le) (fun j => (hr j).le)
  have hmassJ : HasSum (finiteMass sourceEll p r J) 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hmJ 0
  have hprobJ := atomicMeasure_isProbabilityMeasure _ hwJ hmassJ
  let := hprobJ
  have hbJ := (atomicMeasure_ae_bounds (finiteMass sourceEll p r J)).mono fun _ hx => hx.2
  have hbposJ (i : Fin 4) : 0 < (atomicMeasure (finiteMass sourceEll p r J)).real {baseAtom i} := by
    change 0 < (atomicMeasure (finiteMass sourceEll p r J)).real {fixedAtom (Sum.inl i)}
    rw [atomicMeasure_real_singleton _ hwJ]
    exact hpJ i
  exact ⟨hprobJ, normalVariance_pos _ hbJ hbposJ, parabolaCovariance_det_pos _ hbJ hbposJ,
    atomic_curvature_pos q hlo hhi _ hwJ (fun i => hpJ i) hmJ⟩

end
end Shao.OQ3
