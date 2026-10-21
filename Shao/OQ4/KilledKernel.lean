import Shao.OQ4.KilledCosine
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Integral

/-!
# The genuine one-step killed kernel

The whole-real-line extension is the translated increment law restricted to the
closed target interval.  No row is renormalized, and no path or long-time result
is assumed in constructing this measurable kernel.
-/

namespace Shao.OQ4

open MeasureTheory ProbabilityTheory

/-- Translate the fixed increment law by the current starting point. -/
noncomputable def translationKernel (ν : Measure ℝ) [IsProbabilityMeasure ν] : Kernel ℝ ℝ :=
  ((Kernel.deterministic (id : ℝ → ℝ) measurable_id).prod (Kernel.const ℝ ν)).map
    (fun p : ℝ × ℝ => p.1 + p.2)

/-- Kill only on strict exit from the closed interval; the row is not normalized. -/
noncomputable def killedKernel (ν : Measure ℝ) [IsProbabilityMeasure ν] (h : ℝ) : Kernel ℝ ℝ :=
  (translationKernel ν).restrict (measurableSet_Icc : MeasurableSet (Set.Icc (-h) h))

theorem translationKernel_apply (ν : Measure ℝ) [IsProbabilityMeasure ν] (z : ℝ) :
    translationKernel ν z = ν.map (fun y : ℝ => z + y) := by
  unfold translationKernel
  rw [Kernel.map_apply _ (by fun_prop), Kernel.prod_apply, Kernel.deterministic_apply,
    Kernel.const_apply, Measure.dirac_prod, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- The exact row measure, for every real start and every real interval parameter. -/
theorem killedKernel_apply (ν : Measure ℝ) [IsProbabilityMeasure ν] (h z : ℝ) :
    killedKernel ν h z = (ν.map (fun y : ℝ => z + y)).restrict (Set.Icc (-h) h) := by
  rw [killedKernel, Kernel.restrict_apply, translationKernel_apply]

/-- Restriction preserves a uniform finite kernel bound. -/
instance killedKernel_isFiniteKernel (ν : Measure ℝ) [IsProbabilityMeasure ν] (h : ℝ) :
    IsFiniteKernel (killedKernel ν h) := by
  unfold killedKernel translationKernel
  infer_instance

/-- The explicit uniform subprobability bound is one, without renormalization. -/
theorem killedKernel_mass_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν] (h z : ℝ) :
    killedKernel ν h z Set.univ ≤ 1 := by
  rw [killedKernel_apply, Measure.restrict_apply_univ]
  calc
    (ν.map (fun y : ℝ => z + y)) (Set.Icc (-h) h) ≤
        (ν.map (fun y : ℝ => z + y)) Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := by rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]; simp

theorem killedKernel_real_mass_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν] (h z : ℝ) :
    (killedKernel ν h z).real Set.univ ≤ 1 := by
  simpa only [measureReal_def, ENNReal.toReal_one] using
    ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ⊤) (killedKernel_mass_le_one ν h z)

/-- Each row is supported on the closed interval in its own almost-everywhere sense. -/
theorem killedKernel_ae_support (ν : Measure ℝ) [IsProbabilityMeasure ν] (h z : ℝ) :
    ∀ᵐ w ∂killedKernel ν h z, |w| ≤ h := by
  rw [killedKernel_apply]
  exact (ae_restrict_mem (measurableSet_Icc : MeasurableSet (Set.Icc (-h) h))).mono
    fun _ hw => abs_le.mpr hw

/-- Both sides of the bounded Borel test formula are genuine integrable functions. -/
theorem killedKernel_integral_bounded (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h z : ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (hbound : ∃ M : ℝ, ∀ w, |f w| ≤ M) :
    Integrable f (killedKernel ν h z) ∧
      Integrable (fun y : ℝ => if |z + y| ≤ h then f (z + y) else 0) ν ∧
      (∫ w, f w ∂killedKernel ν h z) =
        ∫ y : ℝ, if |z + y| ≤ h then f (z + y) else 0 ∂ν := by
  obtain ⟨M, hMbound⟩ := hbound
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hMbound 0)
  have hleft : Integrable f (killedKernel ν h z) := by
    apply Integrable.of_bound hf.aestronglyMeasurable M
    exact Filter.Eventually.of_forall fun w => by
      simpa only [Real.norm_eq_abs] using hMbound w
  have hcutmeas : Measurable (fun y : ℝ => if |z + y| ≤ h then f (z + y) else 0) :=
    Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
      (hf.comp (by fun_prop)) measurable_const
  have hright : Integrable (fun y : ℝ => if |z + y| ≤ h then f (z + y) else 0) ν := by
    apply Integrable.of_bound hcutmeas.aestronglyMeasurable M
    exact Filter.Eventually.of_forall fun y => by
      by_cases hy : |z + y| ≤ h
      · simpa only [hy, ite_true, Real.norm_eq_abs] using hMbound (z + y)
      · simpa only [hy, ite_false, norm_zero] using hM
  refine ⟨hleft, hright, ?_⟩
  rw [killedKernel_apply, ← integral_indicator (measurableSet_Icc : MeasurableSet (Set.Icc (-h) h))]
  rw [integral_map (by fun_prop : Measurable (fun y : ℝ => z + y)).aemeasurable
    (hf.indicator measurableSet_Icc).aestronglyMeasurable]
  congr 1
  funext y
  simp only [Set.indicator, Set.mem_Icc, ← abs_le]

/-- The cosine test is exactly the previously certified Kcos interface. -/
theorem killedKernel_integral_cos (ν : Measure ℝ) [IsProbabilityMeasure ν] (a h z : ℝ) :
    (∫ w : ℝ, Real.cos (a * w) ∂killedKernel ν h z) = Kcos ν a h z := by
  exact (killedKernel_integral_bounded ν h z (fun w : ℝ => Real.cos (a * w)) (by fun_prop)
    ⟨1, fun w => Real.abs_cos_le_one (a * w)⟩).2.2

end Shao.OQ4
