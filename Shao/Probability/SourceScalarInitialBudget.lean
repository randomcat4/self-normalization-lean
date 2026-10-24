/- Source-bound finite-second-moment scalar and analytic initial budgets. -/
import Mathlib.Topology.Order.IntermediateValue
import Shao.Probability.EndpointRelativeError
import Shao.Probability.OriginalCDFPullback
import Shao.Probability.SourceOriginalZeroEnergyBudget
import Shao.Probability.SourceFiniteSecondCompactBudget
import Shao.C1.Normalization
import Shao.C2.EndpointCDFTransfer
import Shao.C2.HalfLinePhysicalGaussian

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.Probability.SourceScalarInitialBudget
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

private theorem sib_gaussian_cubic_tail_weight :
    ∃ B : ℝ, 0 < B ∧
      ∀ t : ℝ, 0 ≤ t → (1 + t) ^ 3 * Shao.standardNormalTail t ≤ B := by
  let G : Measure ℝ := gaussianReal 0 1
  have h3 : Integrable (fun z : ℝ => |z| ^ 3) G := by
    simpa only [Real.norm_eq_abs, id_eq] using
      (show MemLp (id : ℝ → ℝ) (3 : ℝ≥0∞) G from
        memLp_id_gaussianReal (μ := 0) (v := 1) 3).integrable_norm_pow'
  let m : ℝ := ∫ z : ℝ, |z| ^ 3 ∂G
  have hm : 0 ≤ m := integral_nonneg fun z => pow_nonneg (abs_nonneg z) 3
  refine ⟨8 * (1 + m), by positivity, ?_⟩
  intro t ht
  have hPsi : 0 ≤ Shao.standardNormalTail t := (Shao.standardNormalTail_basic.2.2.1 t).1.le
  have hPsi1 : Shao.standardNormalTail t ≤ 1 := (Shao.standardNormalTail_basic.2.2.1 t).2.le
  by_cases ht1 : t ≤ 1
  · have hpow : (1 + t) ^ 3 ≤ 8 := by
      have hp := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + t)
        (by linarith : 1 + t ≤ 2) 3
      norm_num at hp
      exact hp
    have hprod := mul_le_mul_of_nonneg_left hPsi1 (pow_nonneg (by linarith : (0 : ℝ) ≤ 1+t) 3)
    nlinarith
  · have htpos : 0 < t := by linarith
    have hind : (∫ z : ℝ, (Set.Ioi t).indicator (fun _ : ℝ => (1 : ℝ)) z ∂G) = G.real (Set.Ioi t) := by
      rw [integral_indicator measurableSet_Ioi, setIntegral_const]
      simp only [smul_eq_mul, mul_one]
    have hmark : t ^ 3 * Shao.standardNormalTail t ≤ m := by
      calc
        _ = ∫ z : ℝ, t ^ 3 * (Set.Ioi t).indicator (fun _ : ℝ => (1 : ℝ)) z ∂G := by
          rw [integral_const_mul, hind]
          rfl
        _ ≤ m := integral_mono
          (((integrable_const (1 : ℝ)).indicator measurableSet_Ioi).const_mul (t ^ 3)) h3
          (fun z => by
            by_cases hz : z ∈ Set.Ioi t
            · rw [Set.indicator_of_mem hz, mul_one]
              have habs : t ≤ |z| := (le_of_lt hz).trans (le_abs_self z)
              exact pow_le_pow_left₀ htpos.le habs 3
            · rw [Set.indicator_of_notMem hz, mul_zero]
              positivity)
    have hpow : (1 + t) ^ 3 ≤ 8 * t ^ 3 := by
      have hp := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + t)
        (by linarith : 1 + t ≤ 2 * t) 3
      nlinarith only [hp]
    have hp := mul_le_mul_of_nonneg_right hpow hPsi
    nlinarith

private theorem sib_normalized_zero_energy
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (n : ℕ) (hn : 0 < n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1) :
    (Measure.pi (fun _ : Fin n => nu)).real
      {a : Shao.Path n | Shao.energy a = 0} ≤
      16 * Shao.truncationBudget nu n 0 := by
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  have hpos : 0 < ∫ z : ℝ, z ^ 2 ∂nu := by
    by_contra hh
    have hh' := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (le_of_not_gt hh)
    rw [hnorm] at hh'
    norm_num at hh'
  have hI : iIndepFun (fun i : Fin n => Function.eval i) P :=
    iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable)
  have hLaw (i : Fin n) : IdentDistrib (Function.eval i) (id : ℝ → ℝ) P nu := by
    refine ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    exact (measurePreserving_eval (fun _ : Fin n => nu) i).map_eq.trans Measure.map_id.symm
  have h := SourceOriginalZeroEnergyBudget.original_iid_zero_energy_budget P nu n hn
    (fun i : Fin n => Function.eval i) (fun i => (measurable_pi_apply i).aemeasurable) hI hLaw h2 hpos
  dsimp only at h
  have hmap : Measure.map (fun z : ℝ => z) nu = nu := Measure.map_id
  simpa only [hnorm, Real.sqrt_one, div_one, hmap, Shao.energy, Function.eval] using h

private theorem sib_raw_conditional_weak_tail :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu]
        (n : ℕ) (hn : 0 < n),
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 →
        (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        ∀ t : ℝ, 0 < t →
          Shao.truncationBudget nu n t ≤ (1 / 800 : ℝ) ^ 3 / 8 →
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
          ∀ s : ℝ, (s = 1 ∨ s = -1) →
            |P.real {a : Shao.Path n |
                t * Real.sqrt (Shao.energy a) ≤ s * Shao.prefixSum a n} -
              Shao.standardNormalTail t| ≤
              C * Shao.truncationBudget nu n t * Shao.standardNormalTail t := by
  classical
  obtain ⟨Cb, hCb, hbad⟩ := sourceTruncation_original_two_signs_bad_crossing
  let e : ℝ := 1 / 800
  let K : ℝ := 4 / e ^ 2 + 12 / e + 16
  let Cw : ℝ := ((2 : ℝ) ^ 20 + (2 : ℝ) ^ 18) * Real.sqrt (2 * Real.pi)
  let C : ℝ := Cw * K + (1 + Cb) / e ^ 3
  have he : 0 < e := by norm_num [e]
  have hCw : 0 < Cw := by dsimp [Cw]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro nu hnu n hn h2 hmean hnorm t ht hR
  letI : IsProbabilityMeasure nu := hnu
  dsimp only
  let r : ℝ := Shao.truncationBudget nu n t
  let h : ℝ := e / (1 + t)
  let rho : Measure ℝ := ProbabilityTheory.cond nu {z : ℝ | |z| ≤ h}
  let P0 : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
  let N : Set (Shao.Path n) := {a | ∀ i : Fin n, |a i| ≤ h}
  let p : ℝ := P0.real N
  let z : ℝ := (1 + t) * ((n : ℝ) * |∫ a : ℝ, a ∂rho|) +
    (1 + t) ^ 2 * |(n : ℝ) * (∫ a : ℝ, a ^ 2 ∂rho) - 1| +
    (1 + t) ^ 3 * ((n : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂rho))
  have hi := (by_elab return Lean.mkConst (Lean.Name.num `_private.Shao.Probability.EndpointRelativeError 0 ++ `Shao.Probability.er_source_endpoint_inputs))
    nu n h2 hnorm hmean t e ht.le he (by norm_num [e]) hR t ht (by simp; positivity)
  dsimp only at hi
  change IsProbabilityMeasure rho ∧ 1 ≤ n ∧ 0 < h ∧
    (∀ᵐ a : ℝ ∂rho, |a| ≤ h) ∧ t * h ≤ 1 / 800 ∧ z ≤ 1 / 1000 ∧ z ≤ K * r at hi
  obtain ⟨hrho, hn1, hh, hsupp, hthin, hsmall, hz⟩ := hi
  letI : IsProbabilityMeasure rho := hrho
  have hPsi : 0 ≤ Shao.standardNormalTail t := (Shao.standardNormalTail_basic.2.2.1 t).1.le
  have hr : 0 ≤ r := Shao.truncationBudget_nonneg nu n h2 t
  have hcondErr (s : ℝ) (hs : s = 1 ∨ s = -1) :
      |P.real {a : Shao.Path n | t * Real.sqrt (Shao.energy a) ≤ s * Shao.prefixSum a n} -
        Shao.standardNormalTail t| ≤ Cw * K * r * Shao.standardNormalTail t := by
    have hpay : Cw * z * Shao.standardNormalTail t ≤ Cw * K * r * Shao.standardNormalTail t := by
      have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz hCw.le) hPsi
      nlinarith only [hm]
    rcases hs with hs | hs
    · subst s
      have hw := (by_elab return Lean.mkConst (Lean.Name.num `_private.Shao.Probability.EndpointRelativeError 0 ++ `Shao.Probability.er_bounded_weak_tail))
        rho n hn1 h t hh ht hsupp hthin hsmall
      dsimp only at hw
      change |P.real {a : Shao.Path n | t * Real.sqrt (Shao.energy a) ≤ Shao.prefixSum a n} -
        Shao.standardNormalTail t| ≤ Cw * z * Shao.standardNormalTail t at hw
      simpa only [one_mul] using hw.trans hpay
    · subst s
      have hw := (by_elab return Lean.mkConst (Lean.Name.num `_private.Shao.Probability.EndpointRelativeError 0 ++ `Shao.Probability.er_reflected_weak_tail))
        rho n hn1 h t hh ht hsupp hthin hsmall
      dsimp only at hw
      change |P.real {a : Shao.Path n | t * Real.sqrt (Shao.energy a) ≤ -Shao.prefixSum a n} -
        Shao.standardNormalTail t| ≤ Cw * z * Shao.standardNormalTail t at hw
      simpa only [neg_one_mul] using hw.trans hpay
  have hNm : MeasurableSet N := by
    have him (i : Fin n) : MeasurableSet {a : Shao.Path n | |a i| ≤ h} :=
      measurableSet_le (continuous_abs.measurable.comp
        (measurable_pi_apply i : Measurable (fun a : Shao.Path n => a i))) measurable_const
    have heq : N = ⋂ i : Fin n, {a : Shao.Path n | |a i| ≤ h} := by
      ext a; simp only [N, Set.mem_iInter, Set.mem_setOf_eq]
    rw [heq]
    exact MeasurableSet.iInter him
  have hNrepr : (⋂ i : Fin n, (Function.eval i) ⁻¹' {z : ℝ | |z| ≤ h}) = N := by
    ext a; simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq, N]
  have hI : iIndepFun (fun i : Fin n => Function.eval i) P0 :=
    iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable)
  have hLaw (i : Fin n) : IdentDistrib (Function.eval i) (id : ℝ → ℝ) P0 nu := by
    refine ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    exact (measurePreserving_eval (fun _ : Fin n => nu) i).map_eq.trans Measure.map_id.symm
  have hd := sourceTruncation_conditioned_sample (fun i : Fin n => measurable_pi_apply i)
    hI hLaw h2 t e ht.le he (by norm_num [e]) hR
  dsimp only at hd
  change P0.real ((⋂ i : Fin n, (Function.eval i) ⁻¹' {z : ℝ | |z| ≤ h})ᶜ) ≤ r / e ^ 3 ∧ _ at hd
  rw [hNrepr] at hd
  have hp : (7 / 8 : ℝ) ≤ p := hd.2.1
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hp1 : p ≤ 1 := measureReal_le_one
  have hcomp : 1 - p ≤ r / e ^ 3 := by
    have hc := hd.1
    rw [measureReal_compl hNm, probReal_univ] at hc
    exact hc
  have hcnd : ProbabilityTheory.cond P0 N = P := by
    have hm := hd.2.2.2.1
    change Measure.map (id : Shao.Path n → Shao.Path n) (ProbabilityTheory.cond P0 N) = P at hm
    simpa only [Measure.map_id] using hm
  intro s hs
  let E : Set (Shao.Path n) := {a | t * Real.sqrt (Shao.energy a) ≤ s * Shao.prefixSum a n}
  have hEm : MeasurableSet E := measurableSet_le
    (Shao.measurable_energyWall t) ((Shao.measurable_prefixSum n).const_mul s)
  have hmul : P.real E * p = P0.real (N ∩ E) := by
    simpa only [hcnd, p, Measure.real_def, ENNReal.toReal_mul] using
      congrArg ENNReal.toReal (cond_mul_eq_inter hNm E P0)
  have hsplit := measureReal_inter_add_sdiff (μ := P0) (s := E) hNm
  have hdif : E \ N = E ∩ Nᶜ := rfl
  rw [hdif, Set.inter_comm E N, ← hmul] at hsplit
  have hb := (hbad nu n hn h2 hmean hnorm t e ht.le he (by norm_num [e]) hR
    t ht (by simp; positivity)).2.1
  have hsub : E ∩ Nᶜ ⊆ {a : Shao.Path n |
      t * Real.sqrt (Shao.energy a) ≤ |Shao.prefixSum a n|} ∩ Nᶜ := by
    intro a ha
    refine ⟨?_, ha.2⟩
    change t * Real.sqrt (Shao.energy a) ≤ |Shao.prefixSum a n|
    have hea : t * Real.sqrt (Shao.energy a) ≤ s * Shao.prefixSum a n := ha.1
    apply hea.trans
    rcases hs with hs | hs
    · simpa only [hs, one_mul] using le_abs_self (Shao.prefixSum a n)
    · simpa only [hs, neg_one_mul] using neg_le_abs (Shao.prefixSum a n)
  have hbadE : P0.real (E ∩ Nᶜ) ≤ Cb / e ^ 3 * (r * Shao.standardNormalTail t) :=
    (measureReal_mono hsub).trans hb
  have hc := hcondErr s hs
  change |P.real E - Shao.standardNormalTail t| ≤ Cw * K * r * Shao.standardNormalTail t at hc
  have hscaled : p * |P.real E - Shao.standardNormalTail t| ≤ Cw * K * r * Shao.standardNormalTail t := by
    exact (mul_le_mul_of_nonneg_left hc hp0).trans
      (mul_le_of_le_one_left (by positivity) hp1)
  have hbias := mul_le_mul_of_nonneg_right hcomp hPsi
  have hid : P0.real E - Shao.standardNormalTail t =
      p * (P.real E - Shao.standardNormalTail t) +
        (p - 1) * Shao.standardNormalTail t + P0.real (E ∩ Nᶜ) := by nlinarith only [hsplit]
  have htri : |P0.real E - Shao.standardNormalTail t| ≤
      p * |P.real E - Shao.standardNormalTail t| +
        (1 - p) * Shao.standardNormalTail t + P0.real (E ∩ Nᶜ) := by
    rw [hid]
    have ha := abs_add_le (p * (P.real E - Shao.standardNormalTail t) +
      (p - 1) * Shao.standardNormalTail t) (P0.real (E ∩ Nᶜ))
    have hb' := abs_add_le (p * (P.real E - Shao.standardNormalTail t))
      ((p - 1) * Shao.standardNormalTail t)
    rw [abs_mul, abs_of_nonneg hp0] at hb'
    rw [abs_mul, abs_of_nonpos (by linarith : p - 1 ≤ 0), abs_of_nonneg hPsi] at hb'
    rw [abs_of_nonneg measureReal_nonneg] at ha
    linarith
  change |P0.real E - Shao.standardNormalTail t| ≤ C * r * Shao.standardNormalTail t
  have hsum : Cw * K * r * Shao.standardNormalTail t +
      r / e ^ 3 * Shao.standardNormalTail t +
      Cb / e ^ 3 * (r * Shao.standardNormalTail t) = C * r * Shao.standardNormalTail t := by
    dsimp only [C]
    ring
  rw [← hsum]
  exact htri.trans (add_le_add (add_le_add hscaled hbias) hbadE)

private theorem sib_normalized_positive_tail_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu]
        (n : ℕ) (hn : 0 < n),
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 →
        (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        let R : ℝ := Shao.truncationBudget nu n 0
        let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
        let W : Shao.Path n → ℝ := Shao.C1.normalizedEndpoint
        ∀ t : ℝ, 0 < t → ∀ s : ℝ, (s = 1 ∨ s = -1) →
          |P.real {a : Shao.Path n | t ≤ s * W a} -
            Shao.standardNormalTail t| ≤ C * R := by
  classical
  obtain ⟨A, hA, hraw⟩ := sib_raw_conditional_weak_tail
  obtain ⟨B, hB, hweight⟩ := sib_gaussian_cubic_tail_weight
  let delta : ℝ := (1 / 800 : ℝ) ^ 3 / 8
  let D : ℝ := A * B + 16
  let C : ℝ := 8 / delta + D + B / delta + 1
  have hd : 0 < delta := by norm_num [delta]
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro nu hnu n hn h2 hmean hnorm
  letI : IsProbabilityMeasure nu := hnu
  dsimp only
  let R : ℝ := Shao.truncationBudget nu n 0
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let W : Shao.Path n → ℝ := Shao.C1.normalizedEndpoint
  have hsecond : 0 < ∫ z : ℝ, z ^ 2 ∂nu := by
    by_contra hh
    have hm := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (le_of_not_gt hh)
    rw [hnorm] at hm
    norm_num at hm
  have hRp : 0 < R := Shao.truncationBudget_pos nu n h2 hn hsecond 0 (by norm_num)
  have hzero : P.real {a : Shao.Path n | Shao.energy a = 0} ≤ 16 * R :=
    sib_normalized_zero_energy nu n hn h2 hnorm
  have hlocal (t : ℝ) (ht : 0 < t) (hsml : Shao.truncationBudget nu n t ≤ delta)
      (s : ℝ) (hs : s = 1 ∨ s = -1) :
      |P.real {a : Shao.Path n | t ≤ s * W a} - Shao.standardNormalTail t| ≤ D * R := by
    let E : Set (Shao.Path n) := {a | t * Real.sqrt (Shao.energy a) ≤ s * Shao.prefixSum a n}
    let F : Set (Shao.Path n) := {a | t ≤ s * W a}
    let Z : Set (Shao.Path n) := {a | Shao.energy a = 0}
    have hZm : MeasurableSet Z := measurableSet_eq_fun Shao.measurable_energy measurable_const
    have hset : E = F ∪ Z := by
      ext a
      by_cases ha : Shao.energy a = 0
      · have hS := Shao.prefixSum_eq_zero_of_energy_eq_zero a ha n
        have hW : W a = 0 := Shao.C1.normalizedEndpoint_of_energy_eq_zero a ha
        simp only [E, F, Z, Set.mem_setOf_eq, Set.mem_union, ha, hS, hW,
          Real.sqrt_zero, mul_zero, le_refl, or_true]
      · have hQ : 0 < Shao.energy a := lt_of_le_of_ne (Shao.energy_nonneg a) (Ne.symm ha)
        have hW : W a = Shao.prefixSum a n / Real.sqrt (Shao.energy a) :=
          Shao.C1.normalizedEndpoint_of_energy_pos a hQ
        simp only [E, F, Z, Set.mem_setOf_eq, Set.mem_union, ha, or_false, hW]
        rw [← mul_div_assoc, le_div_iff₀ (Real.sqrt_pos.mpr hQ)]
    have hdisj : F ∩ Z = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro a ha
      have hW : W a = 0 := Shao.C1.normalizedEndpoint_of_energy_eq_zero a ha.2
      have hh : t ≤ s * W a := ha.1
      rw [hW, mul_zero] at hh
      exact (not_le_of_gt ht) hh
    have hsplit : P.real E = P.real F + P.real Z := by
      have hm := measureReal_union_add_inter (μ := P) (s := F) hZm
      rw [hdisj, measureReal_empty, ← hset] at hm
      linarith
    have he := hraw nu n hn h2 hmean hnorm t ht hsml s hs
    change |P.real E - Shao.standardNormalTail t| ≤
      A * Shao.truncationBudget nu n t * Shao.standardNormalTail t at he
    have hid : P.real F - Shao.standardNormalTail t =
      (P.real E - Shao.standardNormalTail t) - P.real Z := by linarith only [hsplit]
    have htri : |P.real F - Shao.standardNormalTail t| ≤
      |P.real E - Shao.standardNormalTail t| + P.real Z := by
      rw [hid]
      simpa only [sub_eq_add_neg, abs_neg, abs_of_nonneg measureReal_nonneg] using
        abs_add_le (P.real E - Shao.standardNormalTail t) (-P.real Z)
    have hscale : Shao.truncationBudget nu n t ≤ (1 + t) ^ 3 * R := by
      have hh := (Shao.truncationBudget_scale_one_le nu n h2 0 (1+t) (by linarith)).2
      simpa only [add_zero, mul_one, add_sub_cancel_left] using hh
    have hPsi : 0 ≤ Shao.standardNormalTail t := (Shao.standardNormalTail_basic.2.2.1 t).1.le
    have hw : A * Shao.truncationBudget nu n t * Shao.standardNormalTail t ≤ A * B * R := by
      calc
        _ ≤ A * ((1+t)^3 * R) * Shao.standardNormalTail t :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale hA.le) hPsi
        _ = A * ((1+t)^3 * Shao.standardNormalTail t) * R := by ring
        _ ≤ A * B * R := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hweight t ht.le) hA.le) hRp.le
    change |P.real F - Shao.standardNormalTail t| ≤ D * R
    calc
      _ ≤ A * B * R + 16 * R := htri.trans (add_le_add (he.trans hw) hzero)
      _ = D * R := by dsimp only [D]; ring
  intro t ht s hs
  have hPsi : 0 ≤ Shao.standardNormalTail t := (Shao.standardNormalTail_basic.2.2.1 t).1.le
  have hC8 : 8 / delta ≤ C := by dsimp only [C]; linarith [div_pos hB hd]
  have hCD : D + B / delta ≤ C := by dsimp only [C]; linarith [div_pos (by norm_num : (0 : ℝ) < 8) hd]
  by_cases hlarge : delta / 8 ≤ R
  · have he : |P.real {a : Shao.Path n | t ≤ s * W a} - Shao.standardNormalTail t| ≤ 1 := by
      have hp0 : 0 ≤ P.real {a : Shao.Path n | t ≤ s * W a} := measureReal_nonneg
      have hp1 : P.real {a : Shao.Path n | t ≤ s * W a} ≤ 1 := measureReal_le_one
      have hPsi1 := (Shao.standardNormalTail_basic.2.2.1 t).2.le
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have h1 : 1 ≤ (8 / delta) * R := by
      have hh := mul_le_mul_of_nonneg_left hlarge (show (0 : ℝ) ≤ 8 / delta by positivity)
      have heq : (8 / delta) * (delta / 8) = (1 : ℝ)  := by field_simp [hd.ne']
      simpa only [heq] using hh
    exact he.trans (h1.trans (mul_le_mul_of_nonneg_right hC8 hRp.le))
  have hsmall : R < delta / 8 := lt_of_not_ge hlarge
  let M : ℝ := delta / R
  have hM : 0 ≤ M := (div_pos hd hRp).le
  have hMR : M * R = delta := by dsimp only [M]; exact div_mul_cancel₀ delta hRp.ne'
  have hright : delta ≤ (1 + M) ^ 3 * R := by
    have hc : M ≤ (1 + M) ^ 3 := by nlinarith [pow_nonneg hM 3]
    have hm := mul_le_mul_of_nonneg_right hc hRp.le
    rw [hMR] at hm
    exact hm
  have hleft : (1 + (0 : ℝ)) ^ 3 * R ≤ delta := by norm_num; linarith
  obtain ⟨L, hLmem, hLeq⟩ := intermediate_value_Icc hM
    (show ContinuousOn (fun u : ℝ => (1+u)^3 * R) (Set.Icc 0 M) by fun_prop) ⟨hleft, hright⟩
  change (1+L)^3 * R = delta at hLeq
  have hL1 : 1 < L := by
    by_contra hh
    have hpow : (1 + L) ^ 3 ≤ 8 := by
      have hp := pow_le_pow_left₀ (by linarith [hLmem.1] : (0 : ℝ) ≤ 1+L)
        (by linarith : 1+L ≤ 2) 3
      norm_num at hp
      exact hp
    have hp := mul_le_mul_of_nonneg_right hpow hRp.le
    rw [hLeq] at hp
    have hsmall' : 8 * R < delta := by
      simpa only [mul_comm] using (lt_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mp hsmall
    exact (not_lt_of_ge hp) hsmall'
  have hLpos : 0 < L := by linarith
  have hdomain (u : ℝ) (hu : 0 ≤ u) (huL : u ≤ L) :
      Shao.truncationBudget nu n u ≤ delta := by
    have hh := (Shao.truncationBudget_scale_one_le nu n h2 0 (1+u) (by linarith)).2
    have hs : Shao.truncationBudget nu n u ≤ (1+u)^3 * R := by
      simpa only [add_zero, mul_one, add_sub_cancel_left] using hh
    calc
      _ ≤ (1+u)^3 * R := hs
      _ ≤ (1+L)^3 * R := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1+u) (by linarith : 1+u ≤ 1+L) 3) hRp.le
      _ = delta := hLeq
  have hPsiL : Shao.standardNormalTail L ≤ B / delta * R := by
    have hh : delta * Shao.standardNormalTail L ≤ B * R := by
      calc
        _ = ((1+L)^3 * Shao.standardNormalTail L) * R := by rw [← hLeq]; ring
        _ ≤ B * R := mul_le_mul_of_nonneg_right (hweight L hLpos.le) hRp.le
    calc
      _ = (delta * Shao.standardNormalTail L) / delta  := by field_simp [hd.ne']
      _ ≤ (B * R) / delta := div_le_div_of_nonneg_right hh hd.le
      _ = B / delta * R := by ring
  by_cases htL : t ≤ L
  · have he := hlocal t ht (hdomain t ht.le htL) s hs
    exact he.trans (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith [div_pos hB hd, div_pos (by norm_num : (0 : ℝ) < 8) hd] : D ≤ C) hRp.le)
  have hLt : L ≤ t := le_of_not_ge htL
  have htailL := (abs_le.mp (hlocal L hLpos (hdomain L hLpos.le le_rfl) s hs)).2
  have hmono : P.real {a : Shao.Path n | t ≤ s * W a} ≤
      P.real {a : Shao.Path n | L ≤ s * W a} :=
    measureReal_mono (fun a ha => hLt.trans ha)
  have hPbound : P.real {a : Shao.Path n | t ≤ s * W a} ≤ (D+B/delta)*R := by
    nlinarith only [hmono, htailL, hPsiL]
  have hPsibound : Shao.standardNormalTail t ≤ (D+B/delta)*R := by
    have hm := Shao.standardNormalTail_basic.1 hLt
    have hDR : 0 ≤ D * R := mul_nonneg hD.le hRp.le
    nlinarith only [hm, hPsiL, hDR]
  have he : |P.real {a : Shao.Path n | t ≤ s * W a} - Shao.standardNormalTail t| ≤
      (D+B/delta)*R := by
    have hp : 0 ≤ P.real {a : Shao.Path n | t ≤ s * W a} := measureReal_nonneg
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  exact he.trans (mul_le_mul_of_nonneg_right hCD hRp.le)

private theorem sib_normalized_closed_cdf_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu]
        (n : ℕ) (hn : 0 < n),
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 →
        (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        let R : ℝ := Shao.truncationBudget nu n 0
        let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
        ∀ v : ℝ,
          |P.real {a : Shao.Path n | Shao.C1.normalizedEndpoint a ≤ v} -
            (gaussianReal 0 1).real (Set.Iic v)| ≤ C * R := by
  classical
  obtain ⟨C, hC, htail⟩ := sib_normalized_positive_tail_budget
  refine ⟨C, hC, ?_⟩
  intro nu hnu n hn h2 hmean hnorm
  letI : IsProbabilityMeasure nu := hnu
  dsimp only
  let R : ℝ := Shao.truncationBudget nu n 0
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let W : Shao.Path n → ℝ := Shao.C1.normalizedEndpoint
  have hCDFid (v : ℝ) : (gaussianReal 0 1).real (Set.Iic v) = 1 - Shao.standardNormalTail v := by
    have hh := (Shao.standardNormalTail_representation v).2.1
    rw [ProbabilityTheory.cdf_eq_real] at hh
    linarith
  intro v
  change |P.real {a : Shao.Path n | W a ≤ v} - (gaussianReal 0 1).real (Set.Iic v)| ≤ C * R
  by_cases hv : v < 0
  · have he := htail nu n hn h2 hmean hnorm (-v) (by linarith) (-1) (Or.inr rfl)
    have hset : {a : Shao.Path n | -v ≤ (-1 : ℝ) * W a} = {a : Shao.Path n | W a ≤ v} := by
      ext a
      simp only [Set.mem_setOf_eq, neg_one_mul]
      constructor <;> intro ha <;> linarith
    have hgamma : (gaussianReal 0 1).real (Set.Iic v) = Shao.standardNormalTail (-v) := by
      rw [hCDFid]
      exact (Shao.standardNormalTail_basic.2.2.2 v).symm
    rw [hgamma]
    change |P.real {a : Shao.Path n | -v ≤ (-1 : ℝ) * W a} - Shao.standardNormalTail (-v)| ≤ C * R at he
    simpa only [hset] using he
  have hv0 : 0 ≤ v := le_of_not_gt hv
  let u : ℕ → ℝ := fun k => v + 1 / (k+1 : ℝ)
  let E : ℕ → Set (Shao.Path n) := fun k => {a | u k ≤ W a}
  have hu0 (k : ℕ) : 0 < u k := by dsimp only [u]; positivity
  have hEmono : Monotone E := by
    intro i j hij a ha
    have hcast : (i+1 : ℝ) ≤ j+1 := by exact_mod_cast Nat.add_le_add_right hij 1
    have hdiv := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < i+1) hcast
    change u j ≤ W a
    change u i ≤ W a at ha
    dsimp only [u] at *
    linarith
  have hUnion : (⋃ k : ℕ, E k) = {a : Shao.Path n | v < W a} := by
    ext a
    constructor
    · intro ha
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp ha
      change v + 1 / (k+1 : ℝ) ≤ W a at hk
      have hp : (0 : ℝ) < 1 / (k+1 : ℝ) := by positivity
      change v < W a
      linarith
    · intro ha
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0 : ℝ) < W a - v from sub_pos.mpr ha)
      refine Set.mem_iUnion.mpr ⟨k, ?_⟩
      change v + 1 / (k+1 : ℝ) ≤ W a
      linarith
  have hlimP : Filter.Tendsto (fun k : ℕ => P.real (E k)) Filter.atTop
      (nhds (P.real {a : Shao.Path n | v < W a})) := by
    have hh := tendsto_measure_iUnion_atTop (fun i j hij => hEmono hij) (μ := P)
    rw [hUnion] at hh
    exact (ENNReal.continuousAt_toReal (measure_ne_top P _)).tendsto.comp hh
  have hulim : Filter.Tendsto u Filter.atTop (nhds v) := by
    simpa only [add_zero] using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlimPsi : Filter.Tendsto (fun k : ℕ => Shao.standardNormalTail (u k)) Filter.atTop
      (nhds (Shao.standardNormalTail v)) :=
    (Shao.standardNormal_derivatives v).2.continuousAt.tendsto.comp hulim
  have he (k : ℕ) : |P.real (E k) - Shao.standardNormalTail (u k)| ≤ C * R := by
    have hh := htail nu n hn h2 hmean hnorm (u k) (hu0 k) 1 (Or.inl rfl)
    simpa only [one_mul] using hh
  have hstrict : |P.real {a : Shao.Path n | v < W a} - Shao.standardNormalTail v| ≤ C * R :=
    le_of_tendsto (hlimP.sub hlimPsi).abs (Filter.Eventually.of_forall he)
  have hcompl : P.real {a : Shao.Path n | W a ≤ v} =
      1 - P.real {a : Shao.Path n | v < W a} := by
    have hm := measureReal_compl (μ := P) (s := {a : Shao.Path n | v < W a})
      (measurableSet_lt measurable_const Shao.C1.measurable_normalizedEndpoint)
    have hset : {a : Shao.Path n | W a ≤ v} = {a : Shao.Path n | v < W a}ᶜ := by
      ext a; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
    rw [← hset, probReal_univ] at hm
    exact hm
  rw [hcompl, hCDFid]
  have hid : (1 - P.real {a : Shao.Path n | v < W a}) - (1 - Shao.standardNormalTail v) =
      -(P.real {a : Shao.Path n | v < W a} - Shao.standardNormalTail v) := by ring
  rw [hid, abs_neg]
  exact hstrict

theorem finite_second_scalar_closed_cdf_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ (mu : Measure ℝ) [IsProbabilityMeasure mu]
        (n : ℕ) (hn : 0 < n),
        Integrable (fun z : ℝ => z ^ 2) mu →
        (∫ z : ℝ, z ∂mu) = 0 →
        (0 < ∫ z : ℝ, z ^ 2 ∂mu) →
        let sigma : ℝ := Real.sqrt (∫ z : ℝ, z ^ 2 ∂mu)
        let normalizedLaw : Measure ℝ := Measure.map
          (fun z : ℝ => z / (sigma * Real.sqrt (n : ℝ))) mu
        let R : ℝ := Shao.truncationBudget normalizedLaw n 0
        let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
        let W : Shao.Path n → ℝ := Shao.C1.normalizedEndpoint
        ∀ v : ℝ,
          |P.real {a : Shao.Path n | W a ≤ v} -
            (gaussianReal 0 1).real (Set.Iic v)| ≤ C * R := by
  classical
  obtain ⟨C, hC, hnormCDF⟩ := sib_normalized_closed_cdf_budget
  refine ⟨C, hC, ?_⟩
  intro mu hmu n hn h2 hmean hpos
  letI : IsProbabilityMeasure mu := hmu
  dsimp only
  let sigma : ℝ := Real.sqrt (∫ z : ℝ, z ^ 2 ∂mu)
  let c : ℝ := sigma * Real.sqrt (n : ℝ)
  let nu : Measure ℝ := Measure.map (fun z : ℝ => z / c) mu
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
  let W : Shao.Path n → ℝ := Shao.C1.normalizedEndpoint
  have hN : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsigma : 0 < sigma := Real.sqrt_pos.mpr hpos
  have hc : 0 < c := mul_pos hsigma (Real.sqrt_pos.mpr hN)
  have hc2 : c ^ 2 = (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂mu) := by
    dsimp only [c, sigma]
    rw [mul_pow, Real.sq_sqrt hpos.le, Real.sq_sqrt hN.le]
    ring
  have hm : Measurable (fun z : ℝ => z / c) := by fun_prop
  letI : IsProbabilityMeasure nu := (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr hmu
  have hnu2 : Integrable (fun z : ℝ => z ^ 2) nu := by
    apply (integrable_map_measure (by fun_prop) hm.aemeasurable).2
    simpa only [Function.comp_def, div_pow] using h2.div_const (c ^ 2)
  have hnu0 : (∫ z : ℝ, z ∂nu) = 0 := by
    rw [show nu = Measure.map (fun z : ℝ => z / c) mu from rfl,
      integral_map (f := fun z : ℝ => z) hm.aemeasurable (by fun_prop), integral_div, hmean, zero_div]
  have hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 := by
    rw [show nu = Measure.map (fun z : ℝ => z / c) mu from rfl,
      integral_map hm.aemeasurable (by fun_prop)]
    simp_rw [div_pow]
    rw [integral_div, hc2]
    field_simp [hN.ne', hpos.ne']
  let A : Shao.Path n → Shao.Path n := fun a i => a i / c
  have hAm : Measurable A := Measurable.of_eval fun i => hm.comp (measurable_pi_apply i)
  have hmap : Measure.map A P = Measure.pi (fun _ : Fin n => nu) :=
    Measure.pi_map_pi (fun _ : Fin n => hm.aemeasurable)
  have hW (a : Shao.Path n) : W (A a) = W a := by
    have hAs : A a = (1 / c) • a := by
      funext i
      simp only [A, Pi.smul_apply, smul_eq_mul, one_div_mul_eq_div]
    have hQ : Shao.energy (A a) = (1 / c) ^ 2 * Shao.energy a := by
      rw [hAs, Shao.energy_smul]
    have hS : Shao.prefixSum (A a) n = (1 / c) * Shao.prefixSum a n := by
      rw [hAs, Shao.prefixSum_smul]
    have hcoef : 0 < (1 / c : ℝ) := one_div_pos.mpr hc
    by_cases ha : Shao.energy a = 0
    · have hz : Shao.energy (A a) = 0 := by rw [hQ, ha, mul_zero]
      rw [show W (A a) = 0 from Shao.C1.normalizedEndpoint_of_energy_eq_zero (A a) hz,
        show W a = 0 from Shao.C1.normalizedEndpoint_of_energy_eq_zero a ha]
    · have hQa : 0 < Shao.energy a := lt_of_le_of_ne (Shao.energy_nonneg a) (Ne.symm ha)
      have hQA : 0 < Shao.energy (A a) := by rw [hQ]; exact mul_pos (sq_pos_of_pos hcoef) hQa
      have hroot : Real.sqrt (Shao.energy (A a)) = (1 / c) * Real.sqrt (Shao.energy a) := by
        rw [hQ, Real.sqrt_mul (sq_nonneg (1/c)), Real.sqrt_sq_eq_abs, abs_of_pos hcoef]
      change Shao.C1.normalizedEndpoint (A a) = Shao.C1.normalizedEndpoint a
      rw [Shao.C1.normalizedEndpoint_of_energy_pos (A a) hQA,
        Shao.C1.normalizedEndpoint_of_energy_pos a hQa, hS, hroot]
      field_simp [hc.ne', (Real.sqrt_pos.mpr hQa).ne']
  intro v
  have he := hnormCDF nu n hn hnu2 hnu0 hnorm v
  have hEm : MeasurableSet {a : Shao.Path n | W a ≤ v} :=
    measurableSet_le Shao.C1.measurable_normalizedEndpoint measurable_const
  have hset : A ⁻¹' {a : Shao.Path n | W a ≤ v} = {a : Shao.Path n | W a ≤ v} := by
    ext a
    change (W (A a) ≤ v) ↔ W a ≤ v
    rw [hW]
  change |(Measure.pi (fun _ : Fin n => nu)).real {a : Shao.Path n | W a ≤ v} -
    (gaussianReal 0 1).real (Set.Iic v)| ≤ C * Shao.truncationBudget nu n 0 at he
  rw [← hmap, Measure.real_def, Measure.map_apply hAm hEm, hset] at he
  exact he

private theorem sib_analytic_profile_properties (x : ℝ) (hx : 0 < x) :
    let g : ℝ → ℝ := fun w =>
      if w < x then 1 - Real.exp (-2 * x * (x - w)) else 0
    Antitone g ∧ (∀ w : ℝ, 0 ≤ g w) ∧ (∀ w : ℝ, g w ≤ 1) := by
  let g : ℝ → ℝ := fun w => if w < x then 1 - Real.exp (-2*x*(x-w)) else 0
  change Antitone g ∧ (∀ w : ℝ, 0 ≤ g w) ∧ (∀ w : ℝ, g w ≤ 1)
  have h0 (w : ℝ) : 0 ≤ g w := by
    by_cases hw : w < x
    · have hp : 0 ≤ x * (x-w) := mul_nonneg hx.le (sub_nonneg.mpr hw.le)
      have he : Real.exp (-2*x*(x-w)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [hp])
      dsimp only [g]
      rw [if_pos hw]
      linarith
    · simp only [g, if_neg hw, le_refl]
  have h1 (w : ℝ) : g w ≤ 1 := by
    dsimp only [g]
    split_ifs
    · linarith [Real.exp_pos (-2*x*(x-w))]
    · norm_num
  refine ⟨?_, h0, h1⟩
  intro w w' hww
  by_cases hw' : w' < x
  · have hw : w < x := lt_of_le_of_lt hww hw'
    dsimp only [g]
    rw [if_pos hw', if_pos hw]
    have he : Real.exp (-2*x*(x-w)) ≤ Real.exp (-2*x*(x-w')) :=
      Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg hx.le (sub_nonneg.mpr hww)])
    linarith
  · change g w' ≤ g w
    rw [show g w' = 0 by simp only [g, if_neg hw']]
    exact h0 w

private theorem sib_analytic_raw_profile_identity
    {n : ℕ} (x : ℝ) (hx : 0 < x) (s : ℝ) (a : Shao.Path n) :
    let g : ℝ → ℝ := fun w =>
      if w < x then 1 - Real.exp (-2 * x * (x - w)) else 0
    (if 0 < Shao.energy a then g (s * Shao.C1.normalizedEndpoint a) else 0) =
      (if 0 < Shao.energy a then
        Shao.C2.HalfLinePhysicalGaussian.upperCompletion
          (x * Real.sqrt (Shao.energy a)) 0 (Shao.energy a)
          (s * Shao.prefixSum a n)
        else 0) := by
  dsimp only
  by_cases hQ : 0 < Shao.energy a
  · rw [if_pos hQ, if_pos hQ, Shao.C1.normalizedEndpoint_of_energy_pos a hQ]
    set q : ℝ := Real.sqrt (Shao.energy a) with hq
    have hqp : 0 < q := Real.sqrt_pos.mpr hQ
    have hq2 : q ^ 2 = Shao.energy a := Real.sq_sqrt hQ.le
    have hwall : 0 < x * q := mul_pos hx hqp
    by_cases hend : s * (Shao.prefixSum a n / q) < x
    · have hend' : s * Shao.prefixSum a n < x * q := by
        apply (div_lt_iff₀ hqp).mp
        simpa only [mul_div_assoc] using hend
      have hdist : 0 < x * q - s * Shao.prefixSum a n := sub_pos.mpr hend'
      have hexp : -2*x*(x-s*(Shao.prefixSum a n/q)) =
          -2*(x*q)*(x*q-s*Shao.prefixSum a n)/Shao.energy a := by
        rw [← hq2]
        field_simp [hqp.ne']
      have hboth : 0 < x*q ∧ 0 < x*q-s*Shao.prefixSum a n := ⟨hwall, hdist⟩
      simp only [if_pos hend, Shao.C2.HalfLinePhysicalGaussian.upperCompletion, sub_zero,
        Shao.C2.HalfLineGaussianStep.completion, if_pos hboth, if_pos hQ]
      rw [hexp]
    · have hend' : x * q ≤ s * Shao.prefixSum a n := by
        apply (le_div_iff₀ hqp).mp
        simpa only [mul_div_assoc] using le_of_not_gt hend
      have hdist : ¬0 < x * q - s * Shao.prefixSum a n := by linarith
      simp only [if_neg hend, Shao.C2.HalfLinePhysicalGaussian.upperCompletion, sub_zero,
        Shao.C2.HalfLineGaussianStep.completion, hdist, and_false, if_false]
  · simp only [if_neg hQ]

private theorem sib_analytic_profile_gaussian_integral (x : ℝ) (hx : 0 < x) :
    let g : ℝ → ℝ := fun w =>
      if w < x then 1 - Real.exp (-2 * x * (x - w)) else 0
    Integrable g (gaussianReal 0 1) ∧
      (∫ w : ℝ, g w ∂gaussianReal 0 1) = 1 - 2 * Shao.standardNormalTail x := by
  classical
  let g : ℝ → ℝ := fun w => if w < x then 1 - Real.exp (-2*x*(x-w)) else 0
  change Integrable g (gaussianReal 0 1) ∧ _
  obtain ⟨hg, hg0, hg1⟩ := sib_analytic_profile_properties x hx
  change Antitone g at hg
  change (∀ w : ℝ, 0 ≤ g w) at hg0
  change (∀ w : ℝ, g w ≤ 1) at hg1
  have hgi : Integrable g (gaussianReal 0 1) := by
    refine (integrable_const (1 : ℝ)).mono' hg.measurable.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 w)]
      exact hg1 w
  refine ⟨hgi, ?_⟩
  let phi : ℝ → ℝ := Shao.standardNormalDensity
  have hphi : Integrable phi := integrable_gaussianPDFReal 0 1
  have hphi0 (w : ℝ) : 0 ≤ phi w := gaussianPDFReal_nonneg 0 1 w
  have hform (w : ℝ) : phi w = (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-w^2/2) := by
    simp [phi, Shao.standardNormalDensity, gaussianPDFReal]
  have hsquare (w : ℝ) : phi w * Real.exp (-2*x*(x-w)) = phi (w-2*x) := by
    rw [hform w, hform (w-2*x)]
    calc
      _ = (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-w^2/2 + -2*x*(x-w)) := by
        rw [Real.exp_add]; ring
      _ = _ := by congr 2; ring
  have hshifti : Integrable (fun w : ℝ => phi (w-2*x)) := by
    have heq : (fun w : ℝ => phi (w-2*x)) = gaussianPDFReal (2*x) 1 := by
      funext w
      simp [phi, Shao.standardNormalDensity, gaussianPDFReal]
    rw [heq]
    exact integrable_gaussianPDFReal (2*x) 1
  have hpoint (w : ℝ) : phi w * g w =
      (Set.Iio x).indicator phi w - (Set.Iio x).indicator (fun w : ℝ => phi (w-2*x)) w := by
    by_cases hw : w < x
    · have hwI : w ∈ Set.Iio x := hw
      rw [show g w = 1-Real.exp (-2*x*(x-w)) by simp only [g, if_pos hw],
        Set.indicator_of_mem hwI, Set.indicator_of_mem hwI]
      calc
        _ = phi w - phi w * Real.exp (-2*x*(x-w)) := by ring
        _ = _ := by rw [hsquare w]
    · have hwI : w ∉ Set.Iio x := hw
      simp only [g, if_neg hw, Set.indicator_of_notMem hwI, mul_zero, sub_self]
  have hcut (v : ℝ) : (∫ w : ℝ, (Set.Iio v).indicator phi w) = 1-Shao.standardNormalTail v := by
    have hdensity : (gaussianReal 0 1).real (Set.Iio v) = ∫ w : ℝ in Set.Iio v, phi w := by
      rw [Measure.real_def, gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
        ENNReal.toReal_ofReal (integral_nonneg (gaussianPDFReal_nonneg 0 1))]
      rfl
    have hc := measureReal_compl (μ := gaussianReal 0 1) (s := Set.Ici v) measurableSet_Ici
    simp only [Set.compl_Ici, probReal_univ] at hc
    have hrep : (gaussianReal 0 1).real (Set.Ici v) = Shao.standardNormalTail v :=
      (Shao.standardNormalTail_representation v).1.symm
    rw [hrep] at hc
    rw [integral_indicator measurableSet_Iio]
    exact hdensity.symm.trans hc
  have hshift : (∫ w : ℝ, (Set.Iio x).indicator (fun w : ℝ => phi (w-2*x)) w) =
      ∫ w : ℝ, (Set.Iio (-x)).indicator phi w := by
    calc
      _ = ∫ w : ℝ, (Set.Iio (-x)).indicator phi (w+(-2*x)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun w => by
          change (Set.Iio x).indicator (fun w : ℝ => phi (w-2*x)) w =
            (Set.Iio (-x)).indicator phi (w+(-2*x))
          by_cases hw : w < x
          · have hh : w+(-2*x) ∈ Set.Iio (-x) := by change w+(-2*x) < -x; linarith
            rw [Set.indicator_of_mem hw, Set.indicator_of_mem hh]
            congr 1
            ring
          · have hh : w+(-2*x) ∉ Set.Iio (-x) := by change ¬(w+(-2*x) < -x); linarith
            rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hh]
      _ = _ := integral_add_right_eq_self ((Set.Iio (-x)).indicator phi) (-2*x)
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  change (∫ w : ℝ, phi w * g w) = _
  simp_rw [hpoint]
  rw [integral_sub (hphi.indicator measurableSet_Iio) (hshifti.indicator measurableSet_Iio),
    hshift, hcut x, hcut (-x), Shao.standardNormalTail_basic.2.2.2 x]
  ring

private theorem sib_signed_cdf_transfer
    {n : ℕ} (P : Measure (Shao.Path n)) [IsProbabilityMeasure P]
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hCDF : ∀ v : ℝ,
      |P.real {a : Shao.Path n | Shao.C1.normalizedEndpoint a ≤ v} -
        (gaussianReal 0 1).real (Set.Iic v)| ≤ delta)
    (s : ℝ) (hs : s = 1 ∨ s = -1) :
    let signedLaw : Measure ℝ := Measure.map
      (fun a : Shao.Path n => s * Shao.C1.normalizedEndpoint a) P
    IsProbabilityMeasure signedLaw ∧
      ∀ v : ℝ, |signedLaw.real (Set.Iic v) -
        (gaussianReal 0 1).real (Set.Iic v)| ≤ delta := by
  classical
  dsimp only
  let W : Shao.Path n → ℝ := Shao.C1.normalizedEndpoint
  let rho : Measure ℝ := Measure.map W P
  let signedLaw : Measure ℝ := Measure.map (fun a : Shao.Path n => s * W a) P
  have hWm : Measurable W := Shao.C1.measurable_normalizedEndpoint
  have hSm : Measurable (fun a : Shao.Path n => s * W a) := measurable_const.mul hWm
  letI : IsProbabilityMeasure rho := (Measure.isProbabilityMeasure_map_iff hWm.aemeasurable).mpr inferInstance
  have hprob : IsProbabilityMeasure signedLaw :=
    (Measure.isProbabilityMeasure_map_iff hSm.aemeasurable).mpr inferInstance
  change IsProbabilityMeasure signedLaw ∧ _
  refine ⟨hprob, ?_⟩
  have hRhoCDF (v : ℝ) : |rho.real (Set.Iic v) - (gaussianReal 0 1).real (Set.Iic v)| ≤ delta := by
    change |(Measure.map W P).real (Set.Iic v) - _| ≤ delta
    rw [Measure.real_def, Measure.map_apply hWm measurableSet_Iic]
    exact hCDF v
  intro v
  rcases hs with hs | hs
  · subst s
    simpa only [signedLaw, one_mul, rho] using hRhoCDF v
  · subst s
    have hSigned : signedLaw = Measure.map (fun z : ℝ => -z) rho := by
      dsimp only [signedLaw, rho]
      rw [Measure.map_map measurable_neg hWm]
      congr 1
      funext a
      simp only [Function.comp_def, neg_one_mul]
    have hneg (kappa : Measure ℝ) :
        (Measure.map (fun z : ℝ => -z) kappa).real (Set.Iic v) = kappa.real (Set.Ici (-v)) := by
      have hset : (fun z : ℝ => -z) ⁻¹' Set.Iic v = Set.Ici (-v) := by
        ext z
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici]
        constructor <;> intro hz <;> linarith
      rw [Measure.real_def, Measure.map_apply measurable_neg measurableSet_Iic, hset]
      rfl
    have hGaussian : Measure.map (fun z : ℝ => -z) (gaussianReal 0 1) = gaussianReal 0 1 := by
      simpa only [neg_zero] using gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1)
    have hGCDF : (gaussianReal 0 1).real (Set.Iic v) = (gaussianReal 0 1).real (Set.Ici (-v)) := by
      calc
        _ = (Measure.map (fun z : ℝ => -z) (gaussianReal 0 1)).real (Set.Iic v) := by rw [hGaussian]
        _ = _ := hneg (gaussianReal 0 1)
    have hcompl (kappa : Measure ℝ) [IsProbabilityMeasure kappa] :
        kappa.real (Set.Ici (-v)) = 1-kappa.real (Set.Iio (-v)) := by
      simpa only [Set.compl_Iio, probReal_univ] using
        (measureReal_compl (μ := kappa) (s := Set.Iio (-v)) measurableSet_Iio)
    have ho := Shao.C2.EndpointCDFTransfer.lower_set_discrepancy rho (gaussianReal 0 1)
      delta hdelta hRhoCDF (Set.Iio (-v)) (IsLowerSet.Iio (-v))
    change |signedLaw.real (Set.Iic v) - (gaussianReal 0 1).real (Set.Iic v)| ≤ delta
    rw [hSigned, hneg rho, hGCDF, hcompl rho, hcompl (gaussianReal 0 1)]
    have hid : (1-rho.real (Set.Iio (-v))) - (1-(gaussianReal 0 1).real (Set.Iio (-v))) =
        -(rho.real (Set.Iio (-v))-(gaussianReal 0 1).real (Set.Iio (-v))) := by ring
    rw [hid, abs_neg]
    exact ho

theorem finite_second_analytic_initial_host_gap :
    ∃ C : ℝ, 0 < C ∧
      ∀ (mu : Measure ℝ) [IsProbabilityMeasure mu]
        (n : ℕ) (hn : 0 < n),
        Integrable (fun z : ℝ => z ^ 2) mu →
        (∫ z : ℝ, z ∂mu) = 0 →
        (0 < ∫ z : ℝ, z ^ 2 ∂mu) →
        let sigma : ℝ := Real.sqrt (∫ z : ℝ, z ^ 2 ∂mu)
        let normalizedLaw : Measure ℝ := Measure.map
          (fun z : ℝ => z / (sigma * Real.sqrt (n : ℝ))) mu
        let R : ℝ := Shao.truncationBudget normalizedLaw n 0
        let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
        let W : Shao.Path n → ℝ := Shao.C1.normalizedEndpoint
        ∀ x : ℝ, 0 < x → x ≤ 1 →
          ∀ s : ℝ, (s = 1 ∨ s = -1) →
            let g : ℝ → ℝ := fun w =>
              if w < x then 1 - Real.exp (-2 * x * (x - w)) else 0
            let V : Shao.Path n → ℝ := fun a =>
              if 0 < Shao.energy a then g (s * W a) else 0
            Integrable V P ∧
              (∀ a : Shao.Path n,
                V a = if 0 < Shao.energy a then
                  Shao.C2.HalfLinePhysicalGaussian.upperCompletion
                    (x * Real.sqrt (Shao.energy a)) 0 (Shao.energy a)
                    (s * Shao.prefixSum a n)
                  else 0) ∧
              |P.real {a : Shao.Path n |
                  Shao.maxWithZero (s • a) < x * Real.sqrt (Shao.energy a)} -
                (∫ a : Shao.Path n, V a ∂P)| ≤ C * R := by
  classical
  obtain ⟨CS, hCS, hScalar⟩ := finite_second_scalar_closed_cdf_budget
  obtain ⟨CH, hCH, hHost⟩ := finite_second_one_sided_compact_budget
  let C : ℝ := CH + CS + 16
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro mu hmu n hn h2 hmean hpos
  letI : IsProbabilityMeasure mu := hmu
  dsimp only
  let sigma : ℝ := Real.sqrt (∫ z : ℝ, z ^ 2 ∂mu)
  let nu : Measure ℝ := Measure.map (fun z : ℝ => z / (sigma * Real.sqrt (n : ℝ))) mu
  let R : ℝ := Shao.truncationBudget nu n 0
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
  let W : Shao.Path n → ℝ := Shao.C1.normalizedEndpoint
  have hR : 0 ≤ R := by
    dsimp only [R, Shao.truncationBudget]
    exact mul_nonneg (Nat.cast_nonneg n) (integral_nonneg fun z => Shao.truncationF_nonneg _)
  have hCDF (v : ℝ) : |P.real {a : Shao.Path n | W a ≤ v} -
      (gaussianReal 0 1).real (Set.Iic v)| ≤ CS * R :=
    hScalar mu n hn h2 hmean hpos v
  have hzero : P.real {a : Shao.Path n | Shao.energy a = 0} ≤ 16 * R := by
    have hI : iIndepFun (fun i : Fin n => Function.eval i) P :=
      iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable)
    have hLaw (i : Fin n) : IdentDistrib (Function.eval i) (id : ℝ → ℝ) P mu := by
      refine ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable, ?_⟩
      exact (measurePreserving_eval (fun _ : Fin n => mu) i).map_eq.trans Measure.map_id.symm
    have hh := SourceOriginalZeroEnergyBudget.original_iid_zero_energy_budget P mu n hn
      (fun i : Fin n => Function.eval i) (fun i => (measurable_pi_apply i).aemeasurable)
      hI hLaw h2 hpos
    have hscale : Real.sqrt ((n : ℝ) * ∫ z : ℝ, z ^ 2 ∂mu) = sigma * Real.sqrt (n : ℝ) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg n)]
      exact mul_comm _ _
    simpa only [hscale, Shao.energy, Function.eval] using hh
  intro x hx hx1 s hs
  let g : ℝ → ℝ := fun w => if w < x then 1 - Real.exp (-2*x*(x-w)) else 0
  let V : Shao.Path n → ℝ := fun a => if 0 < Shao.energy a then g (s * W a) else 0
  let signedLaw : Measure ℝ := Measure.map (fun a : Shao.Path n => s * W a) P
  have hSm : Measurable (fun a : Shao.Path n => s * W a) :=
    measurable_const.mul Shao.C1.measurable_normalizedEndpoint
  have hSigned := sib_signed_cdf_transfer P (CS*R) (mul_nonneg hCS.le hR) hCDF s hs
  change IsProbabilityMeasure signedLaw ∧ _ at hSigned
  obtain ⟨hSignedProb, hSignedCDF⟩ := hSigned
  letI : IsProbabilityMeasure signedLaw := hSignedProb
  obtain ⟨hg, hg0, hg1⟩ := sib_analytic_profile_properties x hx
  change Antitone g at hg
  change (∀ w : ℝ, 0 ≤ g w) at hg0
  change (∀ w : ℝ, g w ≤ 1) at hg1
  have hfi : Integrable (fun a : Shao.Path n => g (s * W a)) P := by
    refine (integrable_const (1 : ℝ)).mono' (hg.measurable.comp hSm).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 _)]
      exact hg1 _
  have hVm : Measurable V := Measurable.ite
    (measurableSet_lt measurable_const Shao.measurable_energy)
    (hg.measurable.comp hSm) measurable_const
  have hVi : Integrable V P := by
    refine (integrable_const (1 : ℝ)).mono' hVm.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun a => by
      dsimp only [V]
      split_ifs
      · rw [Real.norm_eq_abs, abs_of_nonneg (hg0 _)]
        exact hg1 _
      · norm_num
  have hValue (a : Shao.Path n) : V a = if 0 < Shao.energy a then
      Shao.C2.HalfLinePhysicalGaussian.upperCompletion
        (x * Real.sqrt (Shao.energy a)) 0 (Shao.energy a) (s * Shao.prefixSum a n) else 0 :=
    sib_analytic_raw_profile_identity x hx s a
  refine ⟨hVi, hValue, ?_⟩
  have hGauss : (∫ w : ℝ, g w ∂gaussianReal 0 1) = 1-2*Shao.standardNormalTail x :=
    (sib_analytic_profile_gaussian_integral x hx).2
  have hmapIntegral : (∫ w : ℝ, g w ∂signedLaw) = ∫ a : Shao.Path n, g (s*W a) ∂P :=
    integral_map hSm.aemeasurable hg.measurable.aestronglyMeasurable
  have herr := Shao.C2.EndpointCDFTransfer.antitone_unit_expectation_error signedLaw
    (gaussianReal 0 1) (CS*R) (mul_nonneg hCS.le hR) hSignedCDF g hg hg0 hg1
  rw [hmapIntegral, hGauss] at herr
  let Z : Set (Shao.Path n) := {a | Shao.energy a = 0}
  have hZm : MeasurableSet Z := measurableSet_eq_fun Shao.measurable_energy measurable_const
  have hZi : Integrable (Z.indicator (fun _ : Shao.Path n => g 0)) P :=
    (integrable_const (g 0)).indicator hZm
  have hfun : (fun a : Shao.Path n => g (s*W a)) =
      fun a : Shao.Path n => V a + Z.indicator (fun _ : Shao.Path n => g 0) a := by
    funext a
    by_cases hQ : 0 < Shao.energy a
    · have hz : a ∉ Z := ne_of_gt hQ
      simp only [V, if_pos hQ, Set.indicator_of_notMem hz, add_zero]
    · have hz : a ∈ Z := le_antisymm (le_of_not_gt hQ) (Shao.energy_nonneg a)
      have hW : W a = 0 := Shao.C1.normalizedEndpoint_of_energy_eq_zero a hz
      simp only [V, if_neg hQ, Set.indicator_of_mem hz, hW, mul_zero, zero_add]
  have hint : (∫ a : Shao.Path n, g (s*W a) ∂P) =
      (∫ a : Shao.Path n, V a ∂P) + P.real Z * g 0 := by
    rw [hfun, integral_add hVi hZi, integral_indicator_const (g 0) hZm, smul_eq_mul]
  have hcost : |(∫ a : Shao.Path n, g (s*W a) ∂P) - (∫ a : Shao.Path n, V a ∂P)| ≤ 16*R := by
    have hid : (∫ a : Shao.Path n, g (s*W a) ∂P) - (∫ a : Shao.Path n, V a ∂P) =
        P.real Z * g 0 := by rw [hint]; ring
    calc
      _ = P.real Z * g 0 := by rw [hid, abs_of_nonneg (mul_nonneg measureReal_nonneg (hg0 0))]
      _ ≤ P.real Z := mul_le_of_le_one_right measureReal_nonneg (hg1 0)
      _ ≤ 16*R := hzero
  let E : Set (Shao.Path n) := {a | x * Real.sqrt (Shao.energy a) ≤ Shao.maxWithZero (s • a)}
  have hsm : Measurable (fun a : Shao.Path n => s • a) :=
    Measurable.of_eval fun i => measurable_const.mul (measurable_pi_apply i)
  have hEm : MeasurableSet E := measurableSet_le
    (Shao.measurable_energyWall x) (Shao.measurable_maxWithZero.comp hsm)
  have hSurvival : P.real {a : Shao.Path n |
      Shao.maxWithZero (s • a) < x * Real.sqrt (Shao.energy a)} = 1-P.real E := by
    have hm := measureReal_compl (μ := P) hEm
    have heq : {a : Shao.Path n | Shao.maxWithZero (s • a) < x * Real.sqrt (Shao.energy a)} = Eᶜ := by
      ext a
      simp only [E, Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    rw [← heq, probReal_univ] at hm
    exact hm
  have hh := hHost mu n hn h2 hmean hpos x hx.le hx1 s hs
  change |P.real E - 2*Shao.standardNormalTail x| ≤ CH*R at hh
  have hSurvErr : |P.real {a : Shao.Path n |
      Shao.maxWithZero (s • a) < x * Real.sqrt (Shao.energy a)} -
      (1-2*Shao.standardNormalTail x)| ≤ CH*R := by
    rw [hSurvival]
    have hid : (1-P.real E)-(1-2*Shao.standardNormalTail x) =
        -(P.real E-2*Shao.standardNormalTail x) := by ring
    rw [hid, abs_neg]
    exact hh
  have hrev : |(1-2*Shao.standardNormalTail x) - (∫ a : Shao.Path n, g (s*W a) ∂P)| ≤ CS*R := by
    rw [abs_sub_comm]
    exact herr
  calc
    _ ≤ |P.real {a : Shao.Path n | Shao.maxWithZero (s • a) < x*Real.sqrt (Shao.energy a)} -
        (1-2*Shao.standardNormalTail x)| +
        |(1-2*Shao.standardNormalTail x)-(∫ a : Shao.Path n, V a ∂P)| := abs_sub_le _ _ _
    _ ≤ CH*R + (|(1-2*Shao.standardNormalTail x)-(∫ a : Shao.Path n, g (s*W a) ∂P)| +
        |(∫ a : Shao.Path n, g (s*W a) ∂P)-(∫ a : Shao.Path n, V a ∂P)|) :=
      add_le_add hSurvErr (abs_sub_le _ _ _)
    _ ≤ CH*R + (CS*R+16*R) := add_le_add (le_refl (CH*R)) (add_le_add hrev hcost)
    _ = C*R := by dsimp only [C]; ring

end Shao.Probability.SourceScalarInitialBudget
