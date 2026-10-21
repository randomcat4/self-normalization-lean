import Shao.OQ4.KilledIteration
import Shao.Probability.FiniteIID
import Shao.Probability.MeasurablePath
import Shao.Basic.ClosedSurvival
import Mathlib.MeasureTheory.Integral.Prod

/-! Exact finite iid path laws for the genuine, unnormalized killed kernel. -/

namespace Shao.OQ4

open MeasureTheory ProbabilityTheory
open scoped Classical

/-- Monitor positive times only; there is no additional time-zero kill. -/
def shiftedClosedSurvival {n : ℕ} (h z : ℝ) : Set (Shao.Path n) :=
  {a | ∀ k : ℕ, 1 ≤ k → k ≤ n → |z + Shao.prefixSum a k| ≤ h}

def shiftedEndpoint {n : ℕ} (z : ℝ) (a : Shao.Path n) : ℝ :=
  z + Shao.prefixSum a n

theorem measurable_shiftedEndpoint (n : ℕ) (z : ℝ) :
    Measurable (shiftedEndpoint (n := n) z) :=
  measurable_const.add (Shao.measurable_prefixSum n)

theorem measurableSet_shiftedClosedSurvival (n : ℕ) (h z : ℝ) :
    MeasurableSet (shiftedClosedSurvival (n := n) h z) := by
  simp only [shiftedClosedSurvival, Set.ofPred_forall]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ => measurableSet_le
      ((by fun_prop : Measurable (fun x : ℝ => |x|)).comp
        (measurable_const.add (Shao.measurable_prefixSum k))) measurable_const

theorem shiftedClosedSurvival_zero (h z : ℝ) :
    shiftedClosedSurvival (n := 0) h z = Set.univ := by
  ext a
  simp only [shiftedClosedSurvival, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  intro k hk hkn
  omega

theorem prefixSum_cons (n : ℕ) (y : ℝ) (a : Shao.Path n) (k : ℕ) :
    Shao.prefixSum (Fin.cons y a) (k + 1) = y + Shao.prefixSum a k := by
  simp [Shao.prefixSum, Finset.sum_filter, Fin.sum_univ_succ]

theorem shiftedEndpoint_cons (n : ℕ) (z y : ℝ) (a : Shao.Path n) :
    shiftedEndpoint z (Fin.cons y a) = shiftedEndpoint (z + y) a := by
  simp only [shiftedEndpoint, prefixSum_cons]
  ring

theorem shiftedClosedSurvival_cons (n : ℕ) (h z y : ℝ) (a : Shao.Path n) :
    Fin.cons y a ∈ shiftedClosedSurvival h z ↔
      |z + y| ≤ h ∧ a ∈ shiftedClosedSurvival h (z + y) := by
  constructor
  · intro hs
    constructor
    · simpa [prefixSum_cons] using hs 1 (by omega) (by omega)
    · intro k hk hkn
      have ht := hs (k + 1) (by omega) (by omega)
      simpa only [prefixSum_cons, add_assoc] using ht
  · rintro ⟨hy, ha⟩ k hk hkn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    change |z + Shao.prefixSum (Fin.cons y a) (j + 1)| ≤ h
    rw [prefixSum_cons, ← add_assoc]
    by_cases hj : j = 0
    · simpa [hj] using hy
    · exact ha j (by omega) (by omega)

variable (ν : Measure ℝ) [IsProbabilityMeasure ν]

/-- The ordinary unconditioned product law splits into first coordinate and tail. -/
theorem path_pi_lintegral_cons (n : ℕ) (F : Shao.Path (n + 1) → ENNReal)
    (hF : Measurable F) :
    (∫⁻ a, F a ∂Measure.pi (fun _ : Fin (n + 1) => ν)) =
      ∫⁻ y, ∫⁻ a, F (Fin.cons y a) ∂Measure.pi (fun _ : Fin n => ν) ∂ν := by
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0).symm
  have hc : Measurable (fun p : ℝ × Shao.Path n => (Fin.cons p.1 p.2 : Shao.Path (n + 1))) := by
    simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero] using hp.measurable
  calc
    _ = ∫⁻ p : ℝ × Shao.Path n, F (Fin.cons p.1 p.2)
        ∂ν.prod (Measure.pi (fun _ : Fin n => ν)) := by
      simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero] using (hp.lintegral_comp hF).symm
    _ = _ := lintegral_prod _ (hF.comp hc).aemeasurable

theorem killedKernel_lintegral_shift (h z : ℝ) (F : ℝ → ENNReal) (hF : Measurable F) :
    (∫⁻ w, F w ∂killedKernel ν h z) =
      ∫⁻ y, if |z + y| ≤ h then F (z + y) else 0 ∂ν := by
  rw [killedKernel_apply, ← lintegral_indicator measurableSet_Icc,
    lintegral_map (hF.indicator measurableSet_Icc) (by fun_prop)]
  apply lintegral_congr
  intro y
  simp only [Set.indicator, Set.mem_Icc, ← abs_le]

/-- Nonnegative measurable tests identify the whole finite row measure. -/
theorem killedIterKernel_lintegral_path (n : ℕ) (h z : ℝ)
    (F : ℝ → ENNReal) (hF : Measurable F) :
    (∫⁻ w, F w ∂killedIterKernel ν h n z) =
      ∫⁻ a, if a ∈ shiftedClosedSurvival h z then F (shiftedEndpoint z a) else 0
        ∂Measure.pi (fun _ : Fin n => ν) := by
  induction n generalizing z with
  | zero =>
    rw [killedIterKernel_zero, lintegral_dirac' z hF]
    simp [shiftedClosedSurvival_zero, shiftedEndpoint]
  | succ n ih =>
    have heq : killedIterKernel ν h (n + 1) =
        (killedIterKernel ν h n) ∘ₖ (killedKernel ν h) := by
      unfold killedIterKernel
      rw [Kernel.pow_add, pow_one]
    have hg : Measurable (fun w => ∫⁻ v, F v ∂killedIterKernel ν h n w) := hF.lintegral_kernel
    have ht : Measurable (fun a : Shao.Path (n + 1) =>
        if a ∈ shiftedClosedSurvival h z then F (shiftedEndpoint z a) else 0) :=
      Measurable.ite (measurableSet_shiftedClosedSurvival _ h z)
        (hF.comp (measurable_shiftedEndpoint _ z)) measurable_const
    rw [heq, Kernel.lintegral_comp _ _ _ hF, killedKernel_lintegral_shift ν h z _ hg,
      path_pi_lintegral_cons ν n _ ht]
    apply lintegral_congr
    intro y
    by_cases hy : |z + y| ≤ h
    · simp only [hy, ite_true]
      rw [ih (z + y)]
      apply lintegral_congr
      intro a
      simp only [shiftedClosedSurvival_cons, hy, true_and, shiftedEndpoint_cons]
    · simp [shiftedClosedSurvival_cons, hy]

theorem killedIterKernel_eq_path_law (n : ℕ) (h z : ℝ) :
    killedIterKernel ν h n z =
      Measure.map (shiftedEndpoint z)
        ((Measure.pi (fun _ : Fin n => ν)).restrict (shiftedClosedSurvival h z)) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [killedIterKernel_lintegral_path ν n h z F hF,
    lintegral_map hF (measurable_shiftedEndpoint n z),
    ← lintegral_indicator (measurableSet_shiftedClosedSurvival n h z)]
  rfl

theorem killedIterKernel_integral_path (n : ℕ) (h z : ℝ) (f : ℝ → ℝ)
    (hf : Measurable f) (hbound : ∃ M : ℝ, ∀ w, |f w| ≤ M) :
    Integrable f (killedIterKernel ν h n z) ∧
      Integrable (fun a : Shao.Path n => if a ∈ shiftedClosedSurvival h z then
        f (shiftedEndpoint z a) else 0) (Measure.pi (fun _ : Fin n => ν)) ∧
      killedAction ν h n f z = ∫ a : Shao.Path n,
        if a ∈ shiftedClosedSurvival h z then f (shiftedEndpoint z a) else 0
          ∂Measure.pi (fun _ : Fin n => ν) := by
  have hleft := killedAction_integrable ν h n z f hf hbound
  have hcut : Measurable (fun a : Shao.Path n => if a ∈ shiftedClosedSurvival h z then
      f (shiftedEndpoint z a) else 0) :=
    Measurable.ite (measurableSet_shiftedClosedSurvival n h z)
      (hf.comp (measurable_shiftedEndpoint n z)) measurable_const
  obtain ⟨M, hM⟩ := hbound
  have hM0 : 0 ≤ M := (abs_nonneg (f 0)).trans (hM 0)
  have hright : Integrable (fun a : Shao.Path n => if a ∈ shiftedClosedSurvival h z then
      f (shiftedEndpoint z a) else 0) (Measure.pi (fun _ : Fin n => ν)) := by
    apply Integrable.of_bound hcut.aestronglyMeasurable M
    exact Filter.Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs]
      split_ifs <;> simp_all
  refine ⟨hleft, hright, ?_⟩
  unfold killedAction
  rw [killedIterKernel_eq_path_law ν n h z,
    integral_map (measurable_shiftedEndpoint n z).aemeasurable hf.aestronglyMeasurable,
    ← integral_indicator (measurableSet_shiftedClosedSurvival n h z)]
  rfl

theorem killedMass_eq_path_probability (n : ℕ) (h z : ℝ) :
    killedMass ν h n z = (Measure.pi (fun _ : Fin n => ν)).real (shiftedClosedSurvival h z) := by
  have ht := (killedIterKernel_integral_path ν n h z (fun _ => 1)
    measurable_const ⟨1, by simp⟩).2.2
  change killedMass ν h n z = _ at ht
  rw [ht]
  change (∫ a, (shiftedClosedSurvival h z).indicator (fun _ => (1 : ℝ)) a
    ∂Measure.pi (fun _ : Fin n => ν)) = _
  rw [integral_indicator (measurableSet_shiftedClosedSurvival n h z)]
  simp

section IID

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Transfer the shared unconditioned iid joint law through restriction and endpoint. -/
theorem killedIterKernel_eq_iid_path_law (n : ℕ) (h z : ℝ) (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν) :
    killedIterKernel ν h n z =
      Measure.map (fun ω => shiftedEndpoint z (Shao.Probability.samplePath X ω))
        (μ.restrict {ω | Shao.Probability.samplePath X ω ∈ shiftedClosedSurvival h z}) := by
  have hsample := Shao.Probability.measurable_samplePath hX
  have hmap := Shao.Probability.iid_samplePath_map_eq_pi hX hIndep hLaw
  rw [killedIterKernel_eq_path_law ν n h z, ← hmap,
    Measure.restrict_map hsample (measurableSet_shiftedClosedSurvival n h z),
    Measure.map_map (measurable_shiftedEndpoint n z) hsample]
  rfl

theorem killedIterKernel_integral_iid_path (n : ℕ) (h z : ℝ) (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (f : ℝ → ℝ) (hf : Measurable f) (hbound : ∃ M : ℝ, ∀ w, |f w| ≤ M) :
    Integrable f (killedIterKernel ν h n z) ∧
      Integrable (fun ω => if Shao.Probability.samplePath X ω ∈ shiftedClosedSurvival h z then
        f (shiftedEndpoint z (Shao.Probability.samplePath X ω)) else 0) μ ∧
      killedAction ν h n f z = ∫ ω,
        if Shao.Probability.samplePath X ω ∈ shiftedClosedSurvival h z then
          f (shiftedEndpoint z (Shao.Probability.samplePath X ω)) else 0 ∂μ := by
  have hsample := Shao.Probability.measurable_samplePath hX
  have hevent : MeasurableSet {ω | Shao.Probability.samplePath X ω ∈ shiftedClosedSurvival h z} :=
    (measurableSet_shiftedClosedSurvival n h z).preimage hsample
  have hend : Measurable (fun ω => shiftedEndpoint z (Shao.Probability.samplePath X ω)) :=
    (measurable_shiftedEndpoint n z).comp hsample
  have hleft := killedAction_integrable ν h n z f hf hbound
  have hcut : Measurable (fun ω =>
      if Shao.Probability.samplePath X ω ∈ shiftedClosedSurvival h z then
        f (shiftedEndpoint z (Shao.Probability.samplePath X ω)) else 0) :=
    Measurable.ite hevent (hf.comp hend) measurable_const
  obtain ⟨M, hM⟩ := hbound
  have hM0 : 0 ≤ M := (abs_nonneg (f 0)).trans (hM 0)
  have hright : Integrable (fun ω =>
      if Shao.Probability.samplePath X ω ∈ shiftedClosedSurvival h z then
        f (shiftedEndpoint z (Shao.Probability.samplePath X ω)) else 0) μ := by
    apply Integrable.of_bound hcut.aestronglyMeasurable M
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      split_ifs <;> simp_all
  refine ⟨hleft, hright, ?_⟩
  unfold killedAction
  rw [killedIterKernel_eq_iid_path_law ν μ n h z X hX hIndep hLaw,
    integral_map hend.aemeasurable hf.aestronglyMeasurable, ← integral_indicator hevent]
  rfl

theorem killedMass_eq_iid_path_probability (n : ℕ) (h z : ℝ) (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν) :
    killedMass ν h n z =
      μ.real {ω | Shao.Probability.samplePath X ω ∈ shiftedClosedSurvival h z} := by
  have hevent : MeasurableSet {ω | Shao.Probability.samplePath X ω ∈ shiftedClosedSurvival h z} :=
    (measurableSet_shiftedClosedSurvival n h z).preimage (Shao.Probability.measurable_samplePath hX)
  have ht := (killedIterKernel_integral_iid_path ν μ n h z X hX hIndep hLaw
    (fun _ => 1) measurable_const ⟨1, by simp⟩).2.2
  change killedMass ν h n z = _ at ht
  rw [ht]
  change (∫ ω, ({ω | Shao.Probability.samplePath X ω ∈ shiftedClosedSurvival h z}).indicator
    (fun _ => (1 : ℝ)) ω ∂μ) = _
  rw [integral_indicator hevent]
  simp

end IID

/-- At a nonnegative radius the shared zero-prefix condition adds no restriction. -/
theorem shiftedClosedSurvival_eq_closedStrip (n : ℕ) (h : ℝ) (hh : 0 ≤ h) :
    shiftedClosedSurvival (n := n) h 0 = Shao.closedStrip h := by
  ext a
  constructor
  · intro ha k hkn
    by_cases hk : k = 0
    · simpa [hk] using hh
    · simpa only [zero_add] using ha k (by omega) hkn
  · intro ha k _hk hkn
    simpa only [zero_add] using ha k hkn

theorem killedMass_eq_closedStrip_probability (n : ℕ) (h : ℝ) (hh : 0 ≤ h) :
    killedMass ν h n 0 = (Measure.pi (fun _ : Fin n => ν)).real (Shao.closedStrip h) := by
  rw [← shiftedClosedSurvival_eq_closedStrip n h hh]
  exact killedMass_eq_path_probability ν n h 0

theorem killedMass_eq_iid_closedStrip_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (h : ℝ) (hh : 0 ≤ h)
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν) :
    killedMass ν h n 0 = μ.real {ω | Shao.Probability.samplePath X ω ∈ Shao.closedStrip h} := by
  rw [← shiftedClosedSurvival_eq_closedStrip n h hh]
  exact killedMass_eq_iid_path_probability ν μ n h 0 X hX hIndep hLaw

end Shao.OQ4
