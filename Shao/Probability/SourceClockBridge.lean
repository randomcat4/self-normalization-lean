import Shao.Probability.SourceTruncationBridge
import Shao.Probability.ClockControl
import Shao.Probability.ConditionalIID
import Mathlib.Probability.Moments.Variance

/-!
The actual all-coordinate source cutoff, its genuine fixed-event conditional
sample, and the bad-clock probabilities paid by the original truncation budget.
-/

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem sourceTruncation_conditioned_sample
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hR : Shao.truncationBudget ν n x ≤ epsilon ^ 3 / 8) :
    let h : ℝ := epsilon / (1 + x)
    let B : Set ℝ := {z | |z| ≤ h}
    let A : Set Ω := ⋂ i : Fin n, X i ⁻¹' B
    let μx : Measure Ω := ProbabilityTheory.cond μ A
    let rho : Measure ℝ := ProbabilityTheory.cond ν B
    μ.real (Aᶜ) ≤ Shao.truncationBudget ν n x / epsilon ^ 3 ∧
      (7 / 8 : ℝ) ≤ μ.real A ∧
      IsProbabilityMeasure μx ∧
      Measure.map (samplePath X) μx = Measure.pi (fun _ : Fin n => rho) ∧
      iIndepFun X μx ∧
      (∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μx rho) := by
  classical
  let h : ℝ := epsilon / (1 + x)
  let B : Set ℝ := {z | |z| ≤ h}
  let A : Set Ω := ⋂ i : Fin n, X i ⁻¹' B
  let μx : Measure Ω := ProbabilityTheory.cond μ A
  let rho : Measure ℝ := ProbabilityTheory.cond ν B
  have hB : MeasurableSet B := (isClosed_le continuous_abs continuous_const).measurableSet
  have hAm : MeasurableSet A := MeasurableSet.iInter (fun i => hX i hB)
  have htail : MeasurableSet {z : ℝ | h < |z|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hmap (i : Fin n) : Measure.map (X i) μ = ν := by
    simpa only [Measure.map_id] using (hLaw i).map_eq
  have htailEq (i : Fin n) : μ.real {ω | h < |X i ω|} = ν.real {z | h < |z|} := by
    change (μ (X i ⁻¹' {z : ℝ | h < |z|})).toReal = _
    rw [← Measure.map_apply (hX i) htail, hmap i]
    rfl
  have hcompl : Aᶜ = ⋃ i : Fin n, {ω | h < |X i ω|} := by
    ext ω
    simp only [A, B, Set.mem_compl_iff, Set.mem_iInter, Set.mem_preimage,
      Set.mem_ofPred_eq, Set.mem_iUnion, not_forall, not_le]
  have hcomp : μ.real (Aᶜ) ≤ Shao.truncationBudget ν n x / epsilon ^ 3 := by
    calc
      _ = μ.real (⋃ i : Fin n, {ω | h < |X i ω|}) := by rw [hcompl]
      _ ≤ ∑ i : Fin n, μ.real {ω | h < |X i ω|} := measureReal_iUnion_fintype_le _
      _ = (n : ℝ) * ν.real {z | h < |z|} := by simp only [htailEq, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ _ := (Shao.sourceTruncation_tail_budget ν n h2 x epsilon hx hepsilon hepsilon1).1
  have he3 : 0 < epsilon ^ 3 := pow_pos hepsilon 3
  have hbudget : Shao.truncationBudget ν n x / epsilon ^ 3 ≤ (1 / 8 : ℝ) :=
    (div_le_iff₀ he3).2 (by nlinarith only [hR])
  have hmass : (7 / 8 : ℝ) ≤ μ.real A := by
    have hc := measureReal_compl (μ := μ) hAm
    simp only [Measure.real, measure_univ, ENNReal.toReal_one] at hc
    change μ.real (Aᶜ) = 1 - μ.real A at hc
    linarith [hcomp.trans hbudget]
  have hA : μ A ≠ 0 := by
    intro hz
    have hzreal : μ.real A = 0 := by simp only [Measure.real, hz, ENNReal.toReal_zero]
    linarith
  have instμx : IsProbabilityMeasure μx := cond_isProbabilityMeasure hA
  have hBpos (i : Fin n) : ν B ≠ 0 := by
    have hs : μ A ≤ μ (X i ⁻¹' B) :=
      measure_mono (Set.iInter_subset (fun j : Fin n => X j ⁻¹' B) i)
    have hm : μ (X i ⁻¹' B) = ν B := by rw [← Measure.map_apply (hX i) hB, hmap i]
    intro hz
    rw [hm, hz] at hs
    exact hA (le_antisymm hs bot_le)
  have hjoint : Measure.map (samplePath X) μx = Measure.pi (fun _ : Fin n => rho) := by
    change Measure.map (fun ω i => X i ω) (ProbabilityTheory.cond μ A) = _
    simpa only [hmap] using
      indep_cond_joint_map_eq_pi hX hIndep (fun _ => B) (fun _ => hB) hA
  have hcoord (i : Fin n) : Measure.map (X i) μx = rho := by
    have instRho : IsProbabilityMeasure rho := cond_isProbabilityMeasure (hBpos i)
    calc
      _ = Measure.map (Function.eval i) (Measure.map (samplePath X) μx) := by
        rw [Measure.map_map (measurable_pi_apply i) (measurable_samplePath hX)]
        rfl
      _ = rho := by
        rw [hjoint]
        exact (measurePreserving_eval (fun _ : Fin n => rho) i).map_eq
  have hindc : iIndepFun X μx := by
    apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX i).aemeasurable)).2
    change Measure.map (samplePath X) μx = Measure.pi (fun i => Measure.map (X i) μx)
    simp_rw [hcoord]
    exact hjoint
  dsimp only
  refine ⟨hcomp, hmass, instμx, hjoint, hindc, ?_⟩
  intro i
  refine ⟨(hX i).aemeasurable, measurable_id.aemeasurable, ?_⟩
  simpa only [Measure.map_id] using hcoord i

theorem sourceTruncation_clock_bad_probability_le
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (hmean : (∫ z : ℝ, z ∂ν) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonEighth : epsilon ≤ 1 / 8)
    (hR : Shao.truncationBudget ν n x ≤ epsilon ^ 3 / 8)
    (y : ℝ) (hy : 2 ≤ y)
    (hneigh : |y - x| ≤ 1 / (2 * (1 + x))) :
    let h : ℝ := epsilon / (1 + x)
    let B : Set ℝ := {z | |z| ≤ h}
    let A : Set Ω := ⋂ i : Fin n, X i ⁻¹' B
    let μx : Measure Ω := ProbabilityTheory.cond μ A
    let rho : Measure ℝ := ProbabilityTheory.cond ν B
    let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
    let R : ℝ := Shao.truncationBudget ν n x
    let bad : ℝ :=
      μx.real {ω | Shao.prefixSquares (samplePath X ω) (n / 2) < (1 / 16 : ℝ)} +
        μx.real {ω | Shao.energy (samplePath X ω) ∉ Set.Icc (1 / 4 : ℝ) 2}
    bad ≤ 2048 * Real.sqrt (2 * Real.pi) *
        ((1 + y) ^ 3 * (n : ℝ) * m3) * Shao.standardNormalTail y ∧
      bad ≤ 32768 * Real.sqrt (2 * Real.pi) * R * Shao.standardNormalTail y ∧
      bad ≤ 32768 * Real.sqrt (2 * Real.pi) * Real.exp 2 *
        R * Shao.standardNormalTail x := by
  let h : ℝ := epsilon / (1 + x)
  let B : Set ℝ := {z | |z| ≤ h}
  let A : Set Ω := ⋂ i : Fin n, X i ⁻¹' B
  let μx : Measure Ω := ProbabilityTheory.cond μ A
  let rho : Measure ℝ := ProbabilityTheory.cond ν B
  let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
  let R : ℝ := Shao.truncationBudget ν n x
  let bad : ℝ :=
    μx.real {ω | Shao.prefixSquares (samplePath X ω) (n / 2) < (1 / 16 : ℝ)} +
      μx.real {ω | Shao.energy (samplePath X ω) ∉ Set.Icc (1 / 4 : ℝ) 2}
  have heHalf : epsilon ≤ 1 / 2 := by linarith
  have he1 : epsilon ≤ 1 := by linarith
  have ha : 0 < 1 + x := by linarith
  have hweak : |y - x| ≤ 1 / (1 + x) := by
    apply hneigh.trans
    apply (div_le_div_iff₀ (by linarith : 0 < 2 * (1 + x)) ha).2
    linarith
  have hy0 : 0 ≤ y := by linarith
  obtain ⟨_, _, hprob, _, hcond, hcondLaw⟩ :=
    sourceTruncation_conditioned_sample hX hIndep hLaw h2 x epsilon hx hepsilon he1 hR
  have instMu : IsProbabilityMeasure μx := hprob
  obtain ⟨_, _, hprobRho, hsupp, _, _, _, _⟩ :=
    Shao.sourceTruncation_law_data ν n h2 hnorm x epsilon hx hepsilon heHalf hR
  have instRho : IsProbabilityMeasure rho := hprobRho
  have hv := Shao.sourceTruncation_variance_bounds ν n h2 hnorm hmean x epsilon hx
    hepsilon heHalf hR
  have hnum := Shao.sourceTruncation_clock_inputs ν n h2 hnorm x epsilon hx hepsilon
    hepsilonEighth hR y hy0 hweak
  have hb : bad ≤ 2048 * Real.sqrt (2 * Real.pi) *
      ((1 + y) ^ 3 * (n : ℝ) * m3) * Shao.standardNormalTail y :=
    iid_bounded_clock_bad_probability_le (μ := μx) (ν := rho)
      hX hcond hcondLaw h y (div_nonneg hepsilon.le ha.le) hy hsupp
      hv.1 hv.2.1 hnum.1 hnum.2.1 hnum.2.2
  have hcube := (Shao.sourceTruncation_nearby_payment ν n h2 hnorm hmean x epsilon hx
    hepsilon heHalf hR y hy0 hweak).2.1
  have hR0 : 0 ≤ R := Shao.truncationBudget_nonneg ν n h2 x
  have hpay : bad ≤ 32768 * Real.sqrt (2 * Real.pi) * R * Shao.standardNormalTail y := by
    calc
      _ ≤ 2048 * Real.sqrt (2 * Real.pi) *
          ((1 + y) ^ 3 * (n : ℝ) * m3) * Shao.standardNormalTail y := hb
      _ ≤ 2048 * Real.sqrt (2 * Real.pi) * (16 * R) * Shao.standardNormalTail y := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcube (by positivity))
          (Shao.standardNormalTail_basic.2.2.1 y).1.le
      _ = _ := by ring
  have htail := (Shao.standardNormalTail_local_comparison x y hx hy0 hweak).2
  have hfinal : bad ≤ 32768 * Real.sqrt (2 * Real.pi) * Real.exp 2 *
      R * Shao.standardNormalTail x := by
    apply hpay.trans
    have hh := mul_le_mul_of_nonneg_left htail
      (show 0 ≤ 32768 * Real.sqrt (2 * Real.pi) * R by positivity)
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hh
  exact ⟨hb, hpay, hfinal⟩

private theorem sc_final_clock_chebyshev
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Fin n → Ω → ℝ}
    (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (h4 : Integrable (fun z : ℝ => z ^ 4) ν)
    (hlower : (3 / 4 : ℝ) ≤ (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν))
    (hupper : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) ≤ (4 / 3 : ℝ)) :
    μ.real {ω | Shao.energy (samplePath X ω) ∉ Set.Icc (1 / 4 : ℝ) 2} ≤
      4 * (n : ℝ) * (∫ z : ℝ, z ^ 4 ∂ν) := by
  classical
  let Y : Fin n → Ω → ℝ := fun i ω => X i ω ^ 2
  let Q : Ω → ℝ := fun ω => Shao.energy (samplePath X ω)
  have hLawY (i : Fin n) : IdentDistrib (Y i) (fun z : ℝ => z ^ 2) μ ν :=
    (hLaw i).comp (show Measurable (fun z : ℝ => z ^ 2) by fun_prop)
  have hν2 : MemLp (fun z : ℝ => z ^ 2) 2 ν := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).2
    simpa only [← pow_mul] using h4
  have hY2 (i : Fin n) : MemLp (Y i) 2 μ := (hLawY i).memLp_iff.mpr hν2
  have hQ2 : MemLp Q 2 μ := by
    simpa only [Q, Y, Shao.energy, samplePath] using
      memLp_finsetSum Finset.univ (fun i _ => hY2 i)
  have hmeanY (i : Fin n) : (∫ ω, Y i ω ∂μ) = ∫ z : ℝ, z ^ 2 ∂ν :=
    (hLawY i).integral_eq
  have hmeanQ : (∫ ω, Q ω ∂μ) = (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) := by
    change (∫ ω, ∑ i : Fin n, Y i ω ∂μ) = _
    rw [integral_finsetSum Finset.univ (fun i _ => (hY2 i).integrable (by norm_num))]
    simp only [hmeanY, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hindY : iIndepFun Y μ := hIndep.comp (fun _ z => z ^ 2) (fun _ => by fun_prop)
  have hvarY (i : Fin n) : variance (Y i) μ = variance (fun z : ℝ => z ^ 2) ν :=
    (hLawY i).variance_eq
  have hvarQ : variance Q μ = (n : ℝ) * variance (fun z : ℝ => z ^ 2) ν := by
    have hv := IndepFun.variance_sum (s := (Finset.univ : Finset (Fin n)))
      (fun i _ => hY2 i) (fun i _ j _ hij => hindY.indepFun hij)
    have hsum : Q = ∑ i : Fin n, Y i := by
      funext ω
      simp only [Q, Shao.energy, samplePath, Y, Finset.sum_apply]
    rw [hsum, hv]
    simp only [hvarY, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hvarν : variance (fun z : ℝ => z ^ 2) ν ≤ ∫ z : ℝ, z ^ 4 ∂ν := by
    rw [variance_eq_sub hν2]
    simpa only [Pi.pow_apply, ← pow_mul] using
      sub_le_self (∫ z : ℝ, z ^ 4 ∂ν) (sq_nonneg (∫ z : ℝ, z ^ 2 ∂ν))
  have hvar : variance Q μ ≤ (n : ℝ) * (∫ z : ℝ, z ^ 4 ∂ν) := by
    rw [hvarQ]
    exact mul_le_mul_of_nonneg_left hvarν (Nat.cast_nonneg n)
  have hsub : {ω | Q ω ∉ Set.Icc (1 / 4 : ℝ) 2} ⊆
      {ω | (1 / 2 : ℝ) ≤ |Q ω - (∫ ω, Q ω ∂μ)|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, not_and_or, not_le] at hω
    change (1 / 2 : ℝ) ≤ _
    rw [hmeanQ]
    rcases hω with hlo | hhi
    · have hh := neg_le_abs (Q ω - (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν))
      linarith
    · have hh := le_abs_self (Q ω - (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν))
      linarith
  have hdev : μ.real {ω | (1 / 2 : ℝ) ≤ |Q ω - (∫ ω, Q ω ∂μ)|} ≤
      4 * variance Q μ := by
    have hc := meas_ge_le_variance_div_sq hQ2 (show (0 : ℝ) < 1 / 2 by norm_num)
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hc
    rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg Q μ) (sq_nonneg _))] at hr
    change μ.real _ ≤ _ at hr
    norm_num at hr ⊢
    nlinarith only [hr]
  exact ((ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub)).trans hdev).trans
    (by nlinarith only [hvar])

theorem sourceTruncation_final_clock_probability_le
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (hmean : (∫ z : ℝ, z ∂ν) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonEighth : epsilon ≤ 1 / 8)
    (hR : Shao.truncationBudget ν n x ≤ epsilon ^ 3 / 8) :
    let h : ℝ := epsilon / (1 + x)
    let B : Set ℝ := {z | |z| ≤ h}
    let A : Set Ω := ⋂ i : Fin n, X i ⁻¹' B
    let μx : Measure Ω := ProbabilityTheory.cond μ A
    let rho : Measure ℝ := ProbabilityTheory.cond ν B
    let R : ℝ := Shao.truncationBudget ν n x
    let bad : ℝ :=
      μx.real {ω | Shao.energy (samplePath X ω) ∉ Set.Icc (1 / 4 : ℝ) 2}
    bad ≤ 4 * (n : ℝ) * (∫ z : ℝ, z ^ 4 ∂rho) ∧
      bad ≤ 8 * epsilon * R / (1 + x) ^ 4 ∧
      bad ≤ (32768 * Real.sqrt (2 * Real.pi) +
        1 / Shao.standardNormalTail 2) * R * Shao.standardNormalTail x := by
  let h : ℝ := epsilon / (1 + x)
  let B : Set ℝ := {z | |z| ≤ h}
  let A : Set Ω := ⋂ i : Fin n, X i ⁻¹' B
  let μx : Measure Ω := ProbabilityTheory.cond μ A
  let rho : Measure ℝ := ProbabilityTheory.cond ν B
  let R : ℝ := Shao.truncationBudget ν n x
  let bad : ℝ := μx.real {ω | Shao.energy (samplePath X ω) ∉ Set.Icc (1 / 4 : ℝ) 2}
  have ha : 0 < 1 + x := by linarith
  have ha1 : 1 ≤ 1 + x := by linarith
  have hh : 0 ≤ h := div_nonneg hepsilon.le ha.le
  have heHalf : epsilon ≤ 1 / 2 := by linarith
  have he1 : epsilon ≤ 1 := by linarith
  obtain ⟨_, _, hprob, _, hcond, hcondLaw⟩ :=
    sourceTruncation_conditioned_sample hX hIndep hLaw h2 x epsilon hx hepsilon he1 hR
  have instMu : IsProbabilityMeasure μx := hprob
  obtain ⟨_, _, hprobRho, _, _, _, _, h4⟩ :=
    Shao.sourceTruncation_law_data ν n h2 hnorm x epsilon hx hepsilon heHalf hR
  have instRho : IsProbabilityMeasure rho := hprobRho
  have hv := Shao.sourceTruncation_variance_bounds ν n h2 hnorm hmean x epsilon hx
    hepsilon heHalf hR
  have hc : bad ≤ 4 * (n : ℝ) * (∫ z : ℝ, z ^ 4 ∂rho) :=
    sc_final_clock_chebyshev hcond hcondLaw h4 hv.1 hv.2.1
  have hp := Shao.sourceTruncation_paid_moments ν n h2 hnorm hmean x epsilon hx
    hepsilon heHalf hR
  have hR0 : 0 ≤ R := Shao.truncationBudget_nonneg ν n h2 x
  have hfour : (n : ℝ) * (∫ z : ℝ, z ^ 4 ∂rho) ≤ 2 * epsilon * R / (1 + x) ^ 4 := by
    calc
      _ ≤ h * ((n : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂rho)) := hp.2.2.1
      _ ≤ h * (2 * R / (1 + x) ^ 3) := mul_le_mul_of_nonneg_left hp.2.1 hh
      _ = _ := by dsimp only [h]; field_simp
  have hpay : bad ≤ 8 * epsilon * R / (1 + x) ^ 4 := by
    apply hc.trans
    have hh' := mul_le_mul_of_nonneg_left hfour (show (0 : ℝ) ≤ 4 by norm_num)
    convert hh' using 1 <;> ring
  have hsmall : bad ≤ R := by
    apply hpay.trans
    apply (div_le_iff₀ (pow_pos ha 4)).2
    have he : 8 * epsilon * R ≤ R := by
      nlinarith only [mul_nonneg (show 0 ≤ 1 - 8 * epsilon by linarith) hR0]
    have ha4 : (1 : ℝ) ≤ (1 + x) ^ 4 := by
      simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) ha1 4
    exact he.trans (by nlinarith only [mul_nonneg hR0 (sub_nonneg.mpr ha4)])
  have ht2 : 0 < Shao.standardNormalTail 2 := (Shao.standardNormalTail_basic.2.2.1 2).1
  have htx : 0 ≤ Shao.standardNormalTail x := (Shao.standardNormalTail_basic.2.2.1 x).1.le
  have hfinal : bad ≤ (32768 * Real.sqrt (2 * Real.pi) +
      1 / Shao.standardNormalTail 2) * R * Shao.standardNormalTail x := by
    by_cases hx2 : 2 ≤ x
    · have hpclock := (sourceTruncation_clock_bad_probability_le hX hIndep hLaw h2 hnorm
        hmean x epsilon hx hepsilon hepsilonEighth hR x hx2
        (by rw [sub_self, abs_zero]; positivity)).2.1
      have hlo : 0 ≤ μx.real {ω |
          Shao.prefixSquares (samplePath X ω) (n / 2) < (1 / 16 : ℝ)} := ENNReal.toReal_nonneg
      have hlarge : bad ≤ 32768 * Real.sqrt (2 * Real.pi) * R * Shao.standardNormalTail x := by
        linarith only [hpclock, hlo]
      have hadd := mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) ht2.le)
        (mul_nonneg hR0 htx)
      nlinarith only [hlarge, hadd]
    · have hmono : Shao.standardNormalTail 2 ≤ Shao.standardNormalTail x :=
        Shao.standardNormalTail_basic.1 (le_of_not_ge hx2)
      have hratio : (1 : ℝ) ≤ Shao.standardNormalTail x / Shao.standardNormalTail 2 :=
        (le_div_iff₀ ht2).2 (by simpa using hmono)
      have hscaled : bad ≤ (1 / Shao.standardNormalTail 2) * R * Shao.standardNormalTail x := by
        apply hsmall.trans
        have hh' := mul_le_mul_of_nonneg_left hratio hR0
        simpa only [div_eq_mul_inv, one_mul, mul_one, mul_assoc, mul_comm, mul_left_comm] using hh'
      have hadd := mul_nonneg (show 0 ≤ 32768 * Real.sqrt (2 * Real.pi) by positivity)
        (mul_nonneg hR0 htx)
      nlinarith only [hscaled, hadd]
  exact ⟨hc, hpay, hfinal⟩

end Shao.Probability
