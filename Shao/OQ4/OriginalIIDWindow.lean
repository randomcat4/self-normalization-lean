import Shao.OQ4.OriginalWindowProduct
import Shao.OQ4.VarianceScaling
import Shao.Probability.FiniteIID
import Shao.Probability.MeasurablePath
import Shao.Basic.ClosedSurvival
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

noncomputable section
namespace Shao.OQ4.OriginalIIDWindow
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal BigOperators Topology
set_option autoImplicit false
variable {ΩB ΩX : Type*} [MeasurableSpace ΩB] [MeasurableSpace ΩX]

-- B01 PUBLIC full value. Literal source X_1,...,X_n; X_0 is unused.
def sourcePath (n : ℕ) (X : ℕ → ΩX → ℝ) (ω : ΩX) : Shao.Path n :=
  fun i => X (i.val + 1) ω

-- B02 PUBLIC full value. Actual sum of squares, without normalization.
def sourceEnergy (n : ℕ) (X : ℕ → ΩX → ℝ) (ω : ΩX) : ℝ :=
  Shao.energy (sourcePath n X ω)

-- B03 PUBLIC full value. M_n is max over positive prefixes when n>0.
-- At n=0 the chosen extension is zero; no empty positive-index max is invented.
def sourceMaximum (n : ℕ) (X : ℕ → ΩX → ℝ) (ω : ΩX) : ℝ :=
  if hn : 0 < n then Shao.absMax (sourcePath n X ω) hn else 0

-- B04 PUBLIC full value. Weak multiplicative event, including Q=0.
def sourceEvent (n : ℕ) (X : ℕ → ΩX → ℝ) (x : ℝ) : Set ΩX :=
  {ω | sourceMaximum n X ω ≤ x * Real.sqrt (sourceEnergy n X ω)}

-- B05 PUBLIC full value. Exact original probability and actual chosen Brownian CDF.
def sourceWindowError
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (μ : Measure ΩX) (X : ℕ → ΩX → ℝ)
    (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  sSup ((fun x : ℝ => |μ.real (sourceEvent n X x) /
    Shao.Probability.BrownianSup.probability B P hB x - 1|) '' Ioo (a n) 1)

-- B06 PRIVATE head. Exact source partial-sum identification, including k=0.
private theorem source_prefix_eq (n k : ℕ) (hk : k ≤ n)
    (X : ℕ → ΩX → ℝ) (ω : ΩX) :
    Shao.prefixSum (sourcePath n X ω) k =
      ∑ i ∈ Finset.range k, X (i + 1) ω := by
  classical
  unfold Shao.prefixSum sourcePath
  apply Finset.sum_bij (fun i _ => i.val)
  · intro i hi
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  · intro i hi j hj hij
    exact Fin.ext hij
  · intro j hj
    have hjk := Finset.mem_range.mp hj
    refine ⟨⟨j, lt_of_lt_of_le hjk hk⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjk⟩
  · intro i hi
    rfl


-- B07 PUBLIC head. The energy includes precisely source coordinates 1 through n.
theorem sourceEnergy_eq_sum (n : ℕ) (X : ℕ → ΩX → ℝ) (ω : ΩX) :
    sourceEnergy n X ω = ∑ i ∈ Finset.range n, (X (i + 1) ω) ^ 2 := by
  simpa only [sourceEnergy, Shao.energy, sourcePath] using
    (Finset.sum_range (n := n) (fun i : ℕ => (X (i + 1) ω) ^ 2)).symm


-- B08 PUBLIC head. Genuine M_n, with its nonempty maximum premise.
theorem sourceMaximum_le_iff (n : ℕ) (hn : 0 < n)
    (X : ℕ → ΩX → ℝ) (ω : ΩX) (w : ℝ) :
    sourceMaximum n X ω ≤ w ↔
      ∀ k : ℕ, 1 ≤ k → k ≤ n → |∑ i ∈ Finset.range k, X (i + 1) ω| ≤ w := by
  rw [sourceMaximum, dif_pos hn, Shao.absMax_le_iff]
  constructor
  · intro h k hk hkn
    rw [← source_prefix_eq n k hkn X ω]
    exact h k hk hkn
  · intro h k hk hkn
    rw [source_prefix_eq n k hkn X ω]
    exact h k hk hkn


-- B09 PRIVATE head.
private theorem measurable_sourcePath (n : ℕ) (X : ℕ → ΩX → ℝ)
    (hX : ∀ i : ℕ, Measurable (X (i + 1))) : Measurable (sourcePath n X) := by
  exact Measurable.of_eval fun i => hX i.val


-- B10 PRIVATE head. No law or moment restriction.
private theorem measurableSet_sourceEvent (n : ℕ) (X : ℕ → ΩX → ℝ)
    (hX : ∀ i : ℕ, Measurable (X (i + 1))) (x : ℝ) :
    MeasurableSet (sourceEvent n X x) := by
  have hp := measurable_sourcePath n X hX
  by_cases hn : 0 < n
  · unfold sourceEvent sourceMaximum sourceEnergy
    simp only [dif_pos hn]
    exact measurableSet_le ((Shao.measurable_absMax hn).comp hp)
      (measurable_const.mul (Shao.measurable_sqrt_energy.comp hp))
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simpa [sourceEvent, sourceMaximum, sourceEnergy, Shao.energy] using
      (MeasurableSet.univ : MeasurableSet (Set.univ : Set ΩX))


-- B11 PRIVATE head. All x, all n, with n=0 proved separately.
private theorem sourceEvent_eq_closedStrip (n : ℕ) (X : ℕ → ΩX → ℝ) (x : ℝ) :
    sourceEvent n X x =
      {ω | sourcePath n X ω ∈ Shao.closedStrip (x * Real.sqrt (sourceEnergy n X ω))} := by
  classical
  by_cases hn : 0 < n
  · ext ω
    simp only [sourceEvent, Set.mem_setOf_eq, sourceMaximum, dif_pos hn]
    by_cases hw : 0 ≤ x * Real.sqrt (sourceEnergy n X ω)
    · exact (Shao.mem_closedStrip_iff_absMax_le (sourcePath n X ω) hn _ hw).symm
    · constructor
      · intro h
        exact False.elim (hw ((Shao.absMax_nonneg _ hn).trans h))
      · intro h
        exact False.elim (hw (Shao.nonneg_of_mem_closedStrip _ _ h))
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    ext ω
    simp [sourceEvent, sourceMaximum, sourceEnergy, Shao.energy,
      Shao.closedStrip, Shao.prefixSum]


-- B12 PUBLIC head. Exact event scaling for every path, including zero energy.
theorem sourceEvent_scale (n : ℕ) (X : ℕ → ΩX → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (x : ℝ) :
    sourceEvent n (fun i ω => X i ω / σ) x = sourceEvent n X x := by
  classical
  by_cases hn : 0 < n
  · ext ω
    have hpath : sourcePath n (fun i ω => X i ω / σ) ω =
        σ⁻¹ • sourcePath n X ω := by
      ext i
      simp only [sourcePath, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    have henergy : sourceEnergy n (fun i ω => X i ω / σ) ω =
        σ⁻¹ ^ 2 * sourceEnergy n X ω := by
      unfold sourceEnergy
      rw [hpath, Shao.energy_smul]
    have hmax : sourceMaximum n (fun i ω => X i ω / σ) ω =
        sourceMaximum n X ω / σ := by
      simp only [sourceMaximum, dif_pos hn]
      rw [hpath, Shao.absMax_smul_of_nonneg σ⁻¹ (inv_nonneg.mpr hσ.le)]
      rw [div_eq_mul_inv, mul_comm]
    have hroot : Real.sqrt (sourceEnergy n (fun i ω => X i ω / σ) ω) =
        Real.sqrt (sourceEnergy n X ω) / σ := by
      rw [henergy, Real.sqrt_mul (sq_nonneg σ⁻¹), Real.sqrt_sq_eq_abs,
        abs_of_pos (inv_pos.mpr hσ)]
      rw [div_eq_mul_inv, mul_comm]
    simp only [sourceEvent, Set.mem_setOf_eq, hmax, hroot]
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hσ]
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    ext ω
    simp [sourceEvent, sourceMaximum, sourceEnergy, Shao.energy]


-- B13 PRIVATE head. Lower moments are conclusions, never additional assumptions.
private theorem integrable_lower_moments
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (Y : ΩX → ℝ)
    (hY : AEMeasurable Y μ) (h3 : Integrable (fun ω => |Y ω| ^ 3) μ) :
    Integrable Y μ ∧ Integrable (fun ω => (Y ω) ^ 2) μ := by
  have hbound : Integrable (fun ω => 1 + |Y ω| ^ 3) μ :=
    (integrable_const (1 : ℝ)).add h3
  have hpoint (y : ℝ) : |y| ≤ 1 + |y| ^ 3 ∧ y ^ 2 ≤ 1 + |y| ^ 3 := by
    have hy := abs_nonneg y
    have hy3 : 0 ≤ |y| ^ 3 := pow_nonneg hy _
    by_cases h : |y| ≤ 1
    · have hs : |y| ^ 2 ≤ 1 := by
        nlinarith [mul_nonneg hy (sub_nonneg.mpr h)]
      constructor
      · linarith
      · nlinarith [sq_abs y]
    · have hge : 1 ≤ |y| := (lt_of_not_ge h).le
      have h12 : |y| ≤ |y| ^ 2 := by
        nlinarith [mul_nonneg hy (sub_nonneg.mpr hge)]
      have h23 : |y| ^ 2 ≤ |y| ^ 3 := by
        nlinarith [mul_nonneg (sq_nonneg |y|) (sub_nonneg.mpr hge)]
      constructor
      · linarith
      · nlinarith [sq_abs y]
  constructor
  · apply hbound.mono' hY.aestronglyMeasurable
    exact Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs] using (hpoint (Y ω)).1
  · apply hbound.mono' (hY.pow_const 2).aestronglyMeasurable
    exact Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Y ω))] using
        (hpoint (Y ω)).2


-- B14 PRIVATE head. Uses the actual mapped standardized law, not an abstract law.
private theorem standardized_law_moments
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (Y : ΩX → ℝ)
    (hY : Measurable Y) (h3 : Integrable (fun ω => |Y ω| ^ 3) μ)
    (hmean : (∫ ω, Y ω ∂μ) = 0)
    (hsecond : 0 < ∫ ω, (Y ω) ^ 2 ∂μ) :
    let σ : ℝ := Real.sqrt (∫ ω, (Y ω) ^ 2 ∂μ)
    let ν : Measure ℝ := μ.map (fun ω => Y ω / σ)
    0 < σ ∧ IsProbabilityMeasure ν ∧
      Integrable (fun z : ℝ => |z| ^ 3) ν ∧
      (∫ z : ℝ, z ∂ν) = 0 ∧ (∫ z : ℝ, z ^ 2 ∂ν) = 1 := by
  let σ : ℝ := Real.sqrt (∫ ω, (Y ω) ^ 2 ∂μ)
  let Z : ΩX → ℝ := fun ω => Y ω / σ
  let ν : Measure ℝ := μ.map Z
  have hσ : 0 < σ := Real.sqrt_pos.mpr hsecond
  have hsquare : (∫ ω, (Y ω) ^ 2 ∂μ) = σ ^ 2 :=
    (Real.sq_sqrt hsecond.le).symm
  have hlo := integrable_lower_moments μ Y hY.aemeasurable h3
  have hm := Shao.OQ4.standardized_moments μ Y σ hσ hlo.1 hlo.2 h3 hmean hsquare
  have hZ : Measurable Z := hY.div_const σ
  have hν : IsProbabilityMeasure ν := ⟨by
    change (μ.map Z) Set.univ = 1
    rw [Measure.map_apply hZ MeasurableSet.univ]
    simp⟩
  have hid : IdentDistrib Z (id : ℝ → ℝ) μ ν :=
    ⟨hZ.aemeasurable, measurable_id.aemeasurable, by simp only [ν, Measure.map_id]⟩
  have hid3 := hid.comp (show Measurable (fun z : ℝ => |z| ^ 3) by fun_prop)
  have hid2 := hid.comp (show Measurable (fun z : ℝ => z ^ 2) by fun_prop)
  refine ⟨hσ, hν, ?_, ?_, ?_⟩
  · exact hid3.integrable_iff.mp hm.2.2.1
  · exact hid.integral_eq.symm.trans hm.2.2.2.1
  · exact hid2.integral_eq.symm.trans hm.2.2.2.2.1


-- B15 PRIVATE head. Actual finite map equality, including Fin0.
private theorem standardized_sample_map_eq_pi
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hX : ∀ i : ℕ, Measurable (X (i + 1)))
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hIdent : ∀ i : ℕ, IdentDistrib (X (i + 1)) (X 1) μ μ)
    (σ : ℝ) (hσ : 0 < σ) (n : ℕ) :
    μ.map (sourcePath n (fun i ω => X i ω / σ)) =
      Measure.pi (fun _ : Fin n => μ.map (fun ω => X 1 ω / σ)) := by
  let Z : ℕ → ΩX → ℝ := fun i ω => X i ω / σ
  let ν : Measure ℝ := μ.map (Z 1)
  have hZ : ∀ i : ℕ, Measurable (Z (i + 1)) := fun i => (hX i).div_const σ
  have hZ1 : Measurable (Z 1) := by simpa only [zero_add] using hZ 0
  letI : IsProbabilityMeasure ν := ⟨by
    change (μ.map (Z 1)) Set.univ = 1
    rw [Measure.map_apply hZ1 MeasurableSet.univ]
    simp⟩
  have hbase : IdentDistrib (Z 1) (id : ℝ → ℝ) μ ν :=
    ⟨hZ1.aemeasurable, measurable_id.aemeasurable, by simp only [ν, Measure.map_id]⟩
  have hind : iIndepFun (fun i : ℕ => Z (i + 1)) μ := by
    simpa only [Z, Function.comp_def] using hIndep.comp
      (fun _ : ℕ => fun z : ℝ => z / σ) (fun _ => measurable_id.div_const σ)
  have hlaw : ∀ i : Fin n, IdentDistrib (Z (i.val + 1)) (id : ℝ → ℝ) μ ν :=
    fun i => ((hIdent i.val).div_const σ).trans hbase
  change μ.map (Shao.Probability.samplePath (fun i : Fin n => Z (i.val + 1))) =
    Measure.pi (fun _ : Fin n => ν)
  exact Shao.Probability.iid_samplePath_map_eq_pi (fun i : Fin n => hZ i.val)
    (hind.precomp (fun i j hij => Fin.ext hij)) hlaw


-- B16 PUBLIC head. Exact probability, before taking any limit.
theorem source_probability_eq_product
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hX : ∀ i : ℕ, Measurable (X (i + 1)))
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hIdent : ∀ i : ℕ, IdentDistrib (X (i + 1)) (X 1) μ μ)
    (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (x : ℝ) :
    μ.real (sourceEvent n X x) =
      OriginalWindowProduct.productProbability (μ.map (fun ω => X 1 ω / σ)) n x := by
  let Z : ℕ → ΩX → ℝ := fun i ω => X i ω / σ
  let ν : Measure ℝ := μ.map (fun ω => X 1 ω / σ)
  let A : Set (Shao.Path n) :=
    {a | a ∈ Shao.closedStrip (x * Real.sqrt (Shao.energy a))}
  have hsp : Measurable (sourcePath n Z) :=
    measurable_sourcePath n Z (fun i => (hX i).div_const σ)
  have hA : MeasurableSet A := by
    change MeasurableSet {a : Shao.Path n | ∀ k : ℕ, k ≤ n →
      |Shao.prefixSum a k| ≤ x * Real.sqrt (Shao.energy a)}
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun (k : ℕ) => MeasurableSet.iInter fun (_ : k ≤ n) =>
      measurableSet_le (continuous_abs.measurable.comp (Shao.measurable_prefixSum k))
        (measurable_const.mul Shao.measurable_sqrt_energy)
  have hmap := standardized_sample_map_eq_pi μ X hX hIndep hIdent σ hσ n
  have heq : sourceEvent n X x = sourcePath n Z ⁻¹' A := by
    rw [← sourceEvent_scale n X σ hσ x, sourceEvent_eq_closedStrip]
    rfl
  calc
    μ.real (sourceEvent n X x) = μ.real (sourcePath n Z ⁻¹' A) := congrArg μ.real heq
    _ = (μ.map (sourcePath n Z)).real A :=
      (map_measureReal_apply hsp hA).symm
    _ = (Measure.pi (fun _ : Fin n => ν)).real A := by rw [hmap]
    _ = OriginalWindowProduct.productProbability ν n x := by
      rw [OriginalWindowProduct.productProbability,
        PositiveBoundaryStudentized.randomDenominatorEvent_eq]


-- B17 PRIVATE head. Explicit measurable versions, without restricting the law.
private theorem measurable_versions
    (μ : Measure ΩX) (X : ℕ → ΩX → ℝ)
    (hX : ∀ i : ℕ, AEMeasurable (X (i + 1)) μ) :
    ∃ Y : ℕ → ΩX → ℝ,
      (∀ i : ℕ, Measurable (Y (i + 1))) ∧
      (∀ i : ℕ, X (i + 1) =ᵐ[μ] Y (i + 1)) := by
  let Y : ℕ → ΩX → ℝ := fun k => match k with
    | 0 => X 0
    | i + 1 => (hX i).mk (X (i + 1))
  refine ⟨Y, ?_, ?_⟩
  · intro i
    exact (hX i).measurable_mk
  · intro i
    exact (hX i).ae_eq_mk


-- B18 PRIVATE head. Finite event equality holds modulo the actual measure.
private theorem sourceEvent_ae_congr
    (μ : Measure ΩX) (X Y : ℕ → ΩX → ℝ)
    (hXY : ∀ i : ℕ, X (i + 1) =ᵐ[μ] Y (i + 1)) (n : ℕ) (x : ℝ) :
    ∀ᵐ ω ∂μ, ω ∈ sourceEvent n X x ↔ ω ∈ sourceEvent n Y x := by
  have hfin : ∀ᵐ ω ∂μ, ∀ i : Fin n, X (i.val + 1) ω = Y (i.val + 1) ω :=
    ae_all_iff.mpr fun i => hXY i.val
  filter_upwards [hfin] with ω hω
  have hp : sourcePath n X ω = sourcePath n Y ω := funext hω
  simp only [sourceEvent, Set.mem_setOf_eq, sourceMaximum, sourceEnergy, hp]


-- B19 PRIVATE head. Independence and common law survive the actual AE changes.
private theorem iid_congr_ae
    (μ : Measure ΩX) (X Y : ℕ → ΩX → ℝ)
    (hXY : ∀ i : ℕ, X (i + 1) =ᵐ[μ] Y (i + 1))
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hIdent : ∀ i : ℕ, IdentDistrib (X (i + 1)) (X 1) μ μ) :
    iIndepFun (fun i : ℕ => Y (i + 1)) μ ∧
      (∀ i : ℕ, IdentDistrib (Y (i + 1)) (Y 1) μ μ) := by
  refine ⟨hIndep.congr hXY, ?_⟩
  intro i
  have hi : IdentDistrib (X (i + 1)) (Y (i + 1)) μ μ :=
    IdentDistrib.of_ae_eq (hIdent i).aemeasurable_fst (hXY i)
  have h1 : IdentDistrib (X 1) (Y 1) μ μ := by
    simpa only [zero_add] using
      IdentDistrib.of_ae_eq (hIdent 0).aemeasurable_snd (hXY 0)
  exact hi.symm.trans ((hIdent i).trans h1)


-- B20 PUBLIC head. Pays the AE-measurable original random-variable interface.
theorem nullMeasurableSet_sourceEvent
    (μ : Measure ΩX) (X : ℕ → ΩX → ℝ)
    (hX : ∀ i : ℕ, AEMeasurable (X (i + 1)) μ) (n : ℕ) (x : ℝ) :
    NullMeasurableSet (sourceEvent n X x) μ := by
  obtain ⟨Y, hY, hXY⟩ := measurable_versions μ X hX
  refine ⟨sourceEvent n Y x, measurableSet_sourceEvent n Y hY x, ?_⟩
  filter_upwards [sourceEvent_ae_congr μ X Y hXY n x] with ω hω
  exact propext hω


-- B21 PUBLIC head. Exact equality includes early empty/unbounded image sets.
theorem sourceWindowError_congr_ae
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (μ : Measure ΩX) (X Y : ℕ → ΩX → ℝ)
    (hXY : ∀ i : ℕ, X (i + 1) =ᵐ[μ] Y (i + 1)) (a : ℕ → ℝ) (n : ℕ) :
    sourceWindowError B P hB μ X a n = sourceWindowError B P hB μ Y a n := by
  have hp : ∀ x : ℝ, μ.real (sourceEvent n X x) = μ.real (sourceEvent n Y x) := by
    intro x
    unfold Measure.real
    congr 1
    apply measure_congr
    filter_upwards [sourceEvent_ae_congr μ X Y hXY n x] with ω hω
    exact propext hω
  have hf : (fun x : ℝ => |μ.real (sourceEvent n X x) /
      Shao.Probability.BrownianSup.probability B P hB x - 1|) =
      (fun x : ℝ => |μ.real (sourceEvent n Y x) /
      Shao.Probability.BrownianSup.probability B P hB x - 1|) := by
    funext x
    rw [hp x]
  unfold sourceWindowError
  rw [hf]


-- B22 PUBLIC head. Genuine finite original-event supremum, no global CDF bound.
theorem sourceWindowError_spec
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (μ : Measure ΩX) [IsProbabilityMeasure μ]
    (X : ℕ → ΩX → ℝ) (a : ℕ → ℝ) (n : ℕ)
    (ha0 : 0 < a n) (ha1 : a n < 1) :
    ((fun x : ℝ => |μ.real (sourceEvent n X x) /
      Shao.Probability.BrownianSup.probability B P hB x - 1|) '' Ioo (a n) 1).Nonempty ∧
    BddAbove ((fun x : ℝ => |μ.real (sourceEvent n X x) /
      Shao.Probability.BrownianSup.probability B P hB x - 1|) '' Ioo (a n) 1) ∧
    IsLUB ((fun x : ℝ => |μ.real (sourceEvent n X x) /
      Shao.Probability.BrownianSup.probability B P hB x - 1|) '' Ioo (a n) 1)
      (sourceWindowError B P hB μ X a n) ∧
    0 ≤ sourceWindowError B P hB μ X a n := by
  let S : Set ℝ := (fun x : ℝ => |μ.real (sourceEvent n X x) /
    Shao.Probability.BrownianSup.probability B P hB x - 1|) '' Ioo (a n) 1
  have hne : S.Nonempty := by
    refine ⟨_, (a n + 1) / 2, ⟨by linarith, by linarith⟩, rfl⟩
  have hc := BrownianPositiveCDF.probability_pos B P hB (a n) ha0
  have hbound : ∀ y ∈ S,
      y ≤ 1 + 1 / Shao.Probability.BrownianSup.probability B P hB (a n) := by
    rintro y ⟨x, hx, rfl⟩
    have hFx := BrownianPositiveCDF.probability_pos B P hB x (ha0.trans hx.1)
    have hmono := BrownianPositiveCDF.probability_mono B P hB hx.1.le
    have hp0 : 0 ≤ μ.real (sourceEvent n X x) := measureReal_nonneg
    have hp1 : μ.real (sourceEvent n X x) ≤ 1 := by
      simpa only [Measure.real, measure_univ, ENNReal.toReal_one] using
        (measureReal_mono (μ := μ) (Set.subset_univ (sourceEvent n X x)))
    have hr : 0 ≤ μ.real (sourceEvent n X x) /
        Shao.Probability.BrownianSup.probability B P hB x := div_nonneg hp0 hFx.le
    have hrb : μ.real (sourceEvent n X x) /
        Shao.Probability.BrownianSup.probability B P hB x ≤
        1 / Shao.Probability.BrownianSup.probability B P hB (a n) :=
      (div_le_div_of_nonneg_right hp1 hFx.le).trans
        (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hc hmono)
    calc
      _ ≤ |μ.real (sourceEvent n X x) /
          Shao.Probability.BrownianSup.probability B P hB x| + |(1 : ℝ)| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (μ.real (sourceEvent n X x) /
            Shao.Probability.BrownianSup.probability B P hB x) (0 : ℝ) 1)
      _ = μ.real (sourceEvent n X x) /
          Shao.Probability.BrownianSup.probability B P hB x + 1 := by
        rw [abs_of_nonneg hr, abs_one]
      _ ≤ _ := by linarith
  have hb : BddAbove S := ⟨_, hbound⟩
  have hlub : IsLUB S (sSup S) := isLUB_csSup hne hb
  have hnonneg : 0 ≤ sSup S := by
    obtain ⟨y, hy⟩ := hne
    have hy0 : 0 ≤ y := by
      obtain ⟨x, hx, rfl⟩ := hy
      exact abs_nonneg _
    exact hy0.trans (hlub.1 hy)
  exact ⟨hne, hb, hlub, hnonneg⟩


-- B23 PUBLIC head. Full original fixed iid law, ordinary measurable variables.
theorem source_window_measurable_tendsto
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (μ : Measure ΩX) [IsProbabilityMeasure μ]
    (X : ℕ → ΩX → ℝ) (hX : ∀ i : ℕ, Measurable (X (i + 1)))
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hIdent : ∀ i : ℕ, IdentDistrib (X (i + 1)) (X 1) μ μ)
    (h3 : Integrable (fun ω => |X 1 ω| ^ 3) μ)
    (hmean : (∫ ω, X 1 ω ∂μ) = 0)
    (hsecond : 0 < ∫ ω, (X 1 ω) ^ 2 ∂μ)
    (a : ℕ → ℝ) (haAnti : Antitone a)
    (ha : Tendsto a atTop (𝓝 (0 : ℝ)))
    (hslow : Tendsto (fun n => a n * (n : ℝ) ^ ((1 : ℝ) / 6)) atTop atTop) :
    Tendsto (sourceWindowError B P hB μ X a) atTop (𝓝 (0 : ℝ)) := by
  let σ : ℝ := Real.sqrt (∫ ω, (X 1 ω) ^ 2 ∂μ)
  let ν : Measure ℝ := μ.map (fun ω => X 1 ω / σ)
  have hX1 : Measurable (X 1) := by simpa only [zero_add] using hX 0
  have hm : 0 < σ ∧ IsProbabilityMeasure ν ∧
      Integrable (fun z : ℝ => |z| ^ 3) ν ∧
      (∫ z : ℝ, z ∂ν) = 0 ∧ (∫ z : ℝ, z ^ 2 ∂ν) = 1 :=
    standardized_law_moments μ (X 1) hX1 h3 hmean hsecond
  letI : IsProbabilityMeasure ν := hm.2.1
  have hp := OriginalWindowProduct.product_window_tendsto B P hB ν hm.2.2.1
    hm.2.2.2.1 hm.2.2.2.2 a haAnti ha hslow
  have heq : ∀ n : ℕ, sourceWindowError B P hB μ X a n =
      OriginalWindowProduct.windowError B P hB ν a n := by
    intro n
    have hprob : ∀ x : ℝ, μ.real (sourceEvent n X x) =
        OriginalWindowProduct.productProbability ν n x :=
      fun x => source_probability_eq_product μ X hX hIndep hIdent σ hm.1 n x
    unfold sourceWindowError OriginalWindowProduct.windowError
      OriginalWindowProduct.windowValues OriginalWindowProduct.relativeError
    simp_rw [hprob]
  exact hp.congr' (Eventually.of_forall fun n => (heq n).symm)


-- B24 PUBLIC head. Exact AE extension; no atomlessness or space restriction.
theorem source_window_ae_tendsto
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (μ : Measure ΩX) [IsProbabilityMeasure μ]
    (X : ℕ → ΩX → ℝ) (hX : ∀ i : ℕ, AEMeasurable (X (i + 1)) μ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hIdent : ∀ i : ℕ, IdentDistrib (X (i + 1)) (X 1) μ μ)
    (h3 : Integrable (fun ω => |X 1 ω| ^ 3) μ)
    (hmean : (∫ ω, X 1 ω ∂μ) = 0)
    (hsecond : 0 < ∫ ω, (X 1 ω) ^ 2 ∂μ)
    (a : ℕ → ℝ) (haAnti : Antitone a)
    (ha : Tendsto a atTop (𝓝 (0 : ℝ)))
    (hslow : Tendsto (fun n => a n * (n : ℝ) ^ ((1 : ℝ) / 6)) atTop atTop) :
    Tendsto (sourceWindowError B P hB μ X a) atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨Y, hY, hXY⟩ := measurable_versions μ X hX
  have hiid := iid_congr_ae μ X Y hXY hIndep hIdent
  have heq1 : X 1 =ᵐ[μ] Y 1 := by simpa only [zero_add] using hXY 0
  have hc : (fun ω => |X 1 ω| ^ 3) =ᵐ[μ] (fun ω => |Y 1 ω| ^ 3) :=
    heq1.fun_comp (fun z : ℝ => |z| ^ 3)
  have h3Y : Integrable (fun ω => |Y 1 ω| ^ 3) μ := h3.congr hc
  have hmeanY : (∫ ω, Y 1 ω ∂μ) = 0 :=
    (integral_congr_ae heq1.symm).trans hmean
  have hsquare : (∫ ω, (Y 1 ω) ^ 2 ∂μ) = (∫ ω, (X 1 ω) ^ 2 ∂μ) :=
    integral_congr_ae ((heq1.fun_comp (fun z : ℝ => z ^ 2)).symm)
  have hsecondY : 0 < ∫ ω, (Y 1 ω) ^ 2 ∂μ := hsquare.symm ▸ hsecond
  have hp := source_window_measurable_tendsto B P hB μ Y hY hiid.1 hiid.2
    h3Y hmeanY hsecondY a haAnti ha hslow
  exact hp.congr' (Eventually.of_forall fun n =>
    (sourceWindowError_congr_ae B P hB μ X Y hXY a n).symm)


-- B25 PUBLIC ORIGINAL ROOT head. The actual iid M<=xV probability is displayed.
theorem original_iid_sSup_tendsto
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (μ : Measure ΩX) [IsProbabilityMeasure μ]
    (X : ℕ → ΩX → ℝ) (hX : ∀ i : ℕ, AEMeasurable (X (i + 1)) μ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hIdent : ∀ i : ℕ, IdentDistrib (X (i + 1)) (X 1) μ μ)
    (h3 : Integrable (fun ω => |X 1 ω| ^ 3) μ)
    (hmean : (∫ ω, X 1 ω ∂μ) = 0)
    (hsecond : 0 < ∫ ω, (X 1 ω) ^ 2 ∂μ)
    (a : ℕ → ℝ) (haAnti : Antitone a)
    (ha : Tendsto a atTop (𝓝 (0 : ℝ)))
    (hslow : Tendsto (fun n => a n * (n : ℝ) ^ ((1 : ℝ) / 6)) atTop atTop) :
    Tendsto (fun n : ℕ => sSup ((fun x : ℝ =>
      |μ.real {ω | sourceMaximum n X ω ≤ x * Real.sqrt (sourceEnergy n X ω)} /
        Shao.Probability.BrownianSup.probability B P hB x - 1|) '' Ioo (a n) 1))
      atTop (𝓝 (0 : ℝ)) := by
  change Tendsto (sourceWindowError B P hB μ X a) atTop (𝓝 (0 : ℝ))
  exact source_window_ae_tendsto B P hB μ X hX hIndep hIdent h3 hmean hsecond
    a haAnti ha hslow


end Shao.OQ4.OriginalIIDWindow
end
