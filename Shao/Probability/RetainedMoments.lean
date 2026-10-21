import Shao.Probability.TruncationIntegrals
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp

/-!
# The true retained cutoff law and its first two raw moments

The retained region is the closed set `|z| ≤ 1/x`; its complement is the
strict large-observation region. The law is the actual normalized restriction
`ProbabilityTheory.cond`, and its positive mass is derived from the source
budget `n ∫ F(xz) ≤ 1`. This is weaker than requiring `Rₙ(x) ≤ 1`.

Only the first batch is proved here. In particular, the second moment below
is a raw second moment, and is not identified with the centered variance.
-/

set_option autoImplicit false

namespace Shao

open MeasureTheory

def retainedCutoffSet (x : ℝ) : Set ℝ := {z | |z| ≤ 1 / x}

noncomputable def retainedCutoffMass (ν : Measure ℝ) (x : ℝ) : ℝ :=
  (ν (retainedCutoffSet x)).toReal

noncomputable def retainedCutoffLaw (ν : Measure ℝ) (x : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond ν (retainedCutoffSet x)

theorem measurableSet_retainedCutoffSet (x : ℝ) :
    MeasurableSet (retainedCutoffSet x) :=
  measurableSet_le continuous_abs.measurable measurable_const

theorem retainedCutoffLaw_isProbabilityMeasure (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (x : ℝ) (hq : 0 < retainedCutoffMass ν x) :
    IsProbabilityMeasure (retainedCutoffLaw ν x) := by
  have hzero : ν (retainedCutoffSet x) ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos_iff.mp hq).1
  exact ProbabilityTheory.cond_isProbabilityMeasure hzero

theorem ae_abs_le_retainedCutoffLaw (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (x : ℝ) (hq : 0 < retainedCutoffMass ν x) :
    ∀ᵐ z : ℝ ∂retainedCutoffLaw ν x, |z| ≤ 1 / x := by
  rw [ae_iff]
  change (ProbabilityTheory.cond ν (retainedCutoffSet x)) (retainedCutoffSet x)ᶜ = 0
  rw [ProbabilityTheory.cond_apply (measurableSet_retainedCutoffSet x) ν]
  simp

theorem integrable_retainedCutoffLaw (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (x : ℝ) (hq : 0 < retainedCutoffMass ν x)
    (f : ℝ → ℝ) (hf : Integrable f (ν.restrict (retainedCutoffSet x))) :
    Integrable f (retainedCutoffLaw ν x) := by
  have hzero : ν (retainedCutoffSet x) ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos_iff.mp hq).1
  exact hf.smul_measure (ENNReal.inv_ne_top.mpr hzero)

theorem integral_retainedCutoffLaw (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (x : ℝ) (hq : 0 < retainedCutoffMass ν x)
    (f : ℝ → ℝ) (hf : Integrable f (ν.restrict (retainedCutoffSet x))) :
    (∫ z : ℝ, f z ∂retainedCutoffLaw ν x) =
      (∫ z : ℝ in retainedCutoffSet x, f z ∂ν) / retainedCutoffMass ν x := by
  change (∫ z : ℝ, f z ∂(ν (retainedCutoffSet x))⁻¹ •
      ν.restrict (retainedCutoffSet x)) = _
  rw [integral_smul_measure, ENNReal.toReal_inv]
  simp only [smul_eq_mul, retainedCutoffMass, div_eq_mul_inv]
  ring

private theorem retained_integrable_id_of_sq (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) : Integrable (fun z : ℝ => z) ν := by
  apply ((integrable_const (1 : ℝ)).add h2).mono' continuous_id.aestronglyMeasurable
  exact ae_of_all ν (fun z => by
    change ‖z‖ ≤ 1 + z ^ 2
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (|z| - 1), sq_abs z, abs_nonneg z])

private theorem integral_compl_retainedCutoffSet (ν : Measure ℝ) (x : ℝ) (f : ℝ → ℝ) :
    (∫ z : ℝ in (retainedCutoffSet x)ᶜ, f z ∂ν) =
      ∫ z : ℝ, if 1 / x < |z| then f z else 0 ∂ν := by
  rw [← integral_indicator (measurableSet_retainedCutoffSet x).compl]
  apply integral_congr_ae
  exact ae_of_all ν (fun z => by
    simp only [Set.indicator, Set.mem_compl_iff, retainedCutoffSet, Set.mem_ofPred_eq, not_le])

theorem retainedCutoffMass_bounds (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : 0 < x)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hcut : (n : ℝ) * (∫ z : ℝ, truncationF (x * z) ∂ν) ≤ 1) :
    1 - 1 / (n : ℝ) ≤ retainedCutoffMass ν x ∧
      1 / 2 ≤ retainedCutoffMass ν x ∧ retainedCutoffMass ν x ≤ 1 := by
  have hB := measurableSet_retainedCutoffSet x
  have htailEq : (∫ z : ℝ, (retainedCutoffSet x)ᶜ.indicator (fun _z : ℝ => (1 : ℝ)) z ∂ν) =
      1 - retainedCutoffMass ν x := by
    have h := integral_indicator_one (μ := ν) hB.compl
    rw [measureReal_compl hB] at h
    simpa [Set.indicator, Pi.one_apply, retainedCutoffMass, measureReal_def] using h
  have hpoint : (retainedCutoffSet x)ᶜ.indicator (fun _z : ℝ => (1 : ℝ)) ≤
      (fun z : ℝ => truncationF (x * z)) := by
    intro z
    simp only [Set.indicator, Set.mem_compl_iff, retainedCutoffSet, Set.mem_ofPred_eq, not_le]
    split_ifs with hl
    · have hlarge : 1 ≤ |x * z| := by
        rw [abs_mul, abs_of_nonneg hx.le]
        nlinarith [(div_lt_iff₀ hx).mp hl]
      rw [truncationF_of_one_le_abs _ hlarge]
      simpa only [one_pow, sq_abs] using pow_le_pow_left₀ zero_le_one hlarge 2
    · exact truncationF_nonneg _
  have hI := integral_mono ((integrable_const (1 : ℝ)).indicator hB.compl)
    (integrable_truncationF_mul ν h2 x) hpoint
  have hmass : (n : ℝ) * (1 - retainedCutoffMass ν x) ≤ 1 := by
    rw [← htailEq]
    exact (mul_le_mul_of_nonneg_left hI (Nat.cast_nonneg n)).trans hcut
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have htail : 1 - retainedCutoffMass ν x ≤ 1 / (n : ℝ) :=
    (le_div_iff₀ hnpos).mpr (by nlinarith only [hmass])
  have hhalf : 1 / (n : ℝ) ≤ (1 / 2 : ℝ) :=
    (div_le_iff₀ hnpos).mpr (by linarith only [hnR])
  have hupp : retainedCutoffMass ν x ≤ 1 := by
    simpa only [retainedCutoffMass, measureReal_def] using
      (measureReal_le_one (μ := ν) (s := retainedCutoffSet x))
  exact ⟨by linarith, by linarith, hupp⟩

theorem integrable_retainedCutoffLaw_id_sq (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (x : ℝ) (hq : 0 < retainedCutoffMass ν x)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) :
    Integrable (fun z : ℝ => z) (retainedCutoffLaw ν x) ∧
      Integrable (fun z : ℝ => z ^ 2) (retainedCutoffLaw ν x) := by
  exact ⟨integrable_retainedCutoffLaw ν x hq _ (retained_integrable_id_of_sq ν h2).restrict,
    integrable_retainedCutoffLaw ν x hq _ h2.restrict⟩

theorem retainedCutoffLaw_mean_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : 0 < x)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hmean : (∫ z : ℝ, z ∂ν) = 0)
    (hcut : (n : ℝ) * (∫ z : ℝ, truncationF (x * z) ∂ν) ≤ 1) :
    (n : ℝ) * |∫ z : ℝ, z ∂retainedCutoffLaw ν x| ≤ 2 / x := by
  obtain ⟨_, hqhalf, _⟩ := retainedCutoffMass_bounds ν n hn x hx h2 hcut
  have hq : 0 < retainedCutoffMass ν x := by linarith
  have h1 := retained_integrable_id_of_sq ν h2
  have hsplit := integral_add_compl (measurableSet_retainedCutoffSet x) h1
  rw [hmean] at hsplit
  have hnum : (∫ z : ℝ in retainedCutoffSet x, z ∂ν) =
      -(∫ z : ℝ in (retainedCutoffSet x)ᶜ, z ∂ν) := by linarith only [hsplit]
  have hnumabs : |∫ z : ℝ in retainedCutoffSet x, z ∂ν| ≤
      ∫ z : ℝ, if 1 / x < |z| then |z| else 0 ∂ν := by
    calc
      _ = |∫ z : ℝ in (retainedCutoffSet x)ᶜ, z ∂ν| := by rw [hnum, abs_neg]
      _ ≤ ∫ z : ℝ in (retainedCutoffSet x)ᶜ, |z| ∂ν := by
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (μ := ν.restrict (retainedCutoffSet x)ᶜ)
            (fun z : ℝ => z))
      _ = _ := integral_compl_retainedCutoffSet ν x (fun z : ℝ => |z|)
  have hraw := mul_le_mul_of_nonneg_left (integral_truncation_tail_one_le ν h2 x hx)
    (Nat.cast_nonneg n)
  have htail : (n : ℝ) * (∫ z : ℝ, if 1 / x < |z| then |z| else 0 ∂ν) ≤ 1 / x :=
    (le_div_iff₀ hx).mpr (by nlinarith only [hraw, hcut])
  have hnumBound : (n : ℝ) * |∫ z : ℝ in retainedCutoffSet x, z ∂ν| ≤ 1 / x :=
    (mul_le_mul_of_nonneg_left hnumabs (Nat.cast_nonneg n)).trans htail
  calc
    _ = ((n : ℝ) * |∫ z : ℝ in retainedCutoffSet x, z ∂ν|) / retainedCutoffMass ν x := by
      rw [integral_retainedCutoffLaw ν x hq (fun z : ℝ => z) h1.restrict,
        abs_div, abs_of_nonneg hq.le]
      ring
    _ ≤ (1 / x) / retainedCutoffMass ν x := div_le_div_of_nonneg_right hnumBound hq.le
    _ ≤ 2 / x := by
      apply (div_le_iff₀ hq).mpr
      have hq2 : 1 ≤ 2 * retainedCutoffMass ν x := by linarith only [hqhalf]
      have h := mul_le_mul_of_nonneg_left hq2 (div_nonneg zero_le_one hx.le)
      simpa only [div_eq_mul_inv, one_mul, mul_one, mul_assoc, mul_comm, mul_left_comm] using h

theorem retainedCutoffLaw_second_moment_bounds
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : 0 < x)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (hcut : (n : ℝ) * (∫ z : ℝ, truncationF (x * z) ∂ν) ≤ 1) :
    1 - 1 / x ^ 2 ≤ (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂retainedCutoffLaw ν x) ∧
      (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂retainedCutoffLaw ν x) ≤ 1 + 2 / (n : ℝ) := by
  obtain ⟨hqlo, hqhalf, hqone⟩ := retainedCutoffMass_bounds ν n hn x hx h2 hcut
  have hq : 0 < retainedCutoffMass ν x := by linarith
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hsplit := integral_add_compl (measurableSet_retainedCutoffSet x) h2
  rw [integral_compl_retainedCutoffSet ν x (fun z : ℝ => z ^ 2)] at hsplit
  have hsum : (n : ℝ) * (∫ z : ℝ in retainedCutoffSet x, z ^ 2 ∂ν) +
      (n : ℝ) * (∫ z : ℝ, if 1 / x < |z| then z ^ 2 else 0 ∂ν) = 1 := by
    rw [← mul_add, hsplit]
    exact hnorm
  have hraw := mul_le_mul_of_nonneg_left (integral_truncation_tail_two_le ν h2 x hx)
    (Nat.cast_nonneg n)
  have htail : (n : ℝ) * (∫ z : ℝ, if 1 / x < |z| then z ^ 2 else 0 ∂ν) ≤ 1 / x ^ 2 :=
    (le_div_iff₀ (sq_pos_of_ne_zero hx.ne')).mpr (by nlinarith only [hraw, hcut])
  have hA0 : 0 ≤ (n : ℝ) * (∫ z : ℝ in retainedCutoffSet x, z ^ 2 ∂ν) :=
    mul_nonneg (Nat.cast_nonneg n) (integral_nonneg (fun z => sq_nonneg z))
  have hT0 : 0 ≤ (n : ℝ) * (∫ z : ℝ, if 1 / x < |z| then z ^ 2 else 0 ∂ν) := by
    apply mul_nonneg (Nat.cast_nonneg n)
    apply integral_nonneg
    intro z
    change 0 ≤ if 1 / x < |z| then z ^ 2 else 0
    split_ifs <;> positivity
  have hAlo : 1 - 1 / x ^ 2 ≤ (n : ℝ) * (∫ z : ℝ in retainedCutoffSet x, z ^ 2 ∂ν) :=
    by linarith only [hsum, htail]
  have hAhi : (n : ℝ) * (∫ z : ℝ in retainedCutoffSet x, z ^ 2 ∂ν) ≤ 1 :=
    by linarith only [hsum, hT0]
  have hcond : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂retainedCutoffLaw ν x) =
      ((n : ℝ) * (∫ z : ℝ in retainedCutoffSet x, z ^ 2 ∂ν)) / retainedCutoffMass ν x := by
    rw [integral_retainedCutoffLaw ν x hq (fun z : ℝ => z ^ 2) h2.restrict]
    ring
  constructor
  · rw [hcond]
    apply hAlo.trans
    apply (le_div_iff₀ hq).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hqone hA0
  · rw [hcond]
    apply (div_le_div_of_nonneg_right hAhi hq.le).trans
    apply (div_le_iff₀ hq).mpr
    have hNcancel : (n : ℝ) * (1 / (n : ℝ)) = 1 := by field_simp [hnpos.ne']
    have hNq : (n : ℝ) - 1 ≤ (n : ℝ) * retainedCutoffMass ν x := by
      have h := mul_le_mul_of_nonneg_left hqlo (Nat.cast_nonneg n)
      nlinarith only [h, hNcancel]
    have hcross : (n : ℝ) ≤ ((n : ℝ) + 2) * retainedCutoffMass ν x :=
      by nlinarith only [hNq, hqhalf]
    have hid : (1 + 2 / (n : ℝ)) * retainedCutoffMass ν x =
        (((n : ℝ) + 2) * retainedCutoffMass ν x) / (n : ℝ) := by
      field_simp [hnpos.ne']
    rw [hid]
    apply (le_div_iff₀ hnpos).mpr
    simpa only [one_mul] using hcross

end Shao
