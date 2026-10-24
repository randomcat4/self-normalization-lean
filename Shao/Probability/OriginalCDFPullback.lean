/-
Actual original-law strict CDF conditioning, signed marked bad-cutoff costs,
and the arbitrary-law endpoint identity with exact zero-energy correction.
Constants precede every law and parameter. Original endpoint relative error,
full-y desmoothing, contraction, and all original roots remain open.
-/
import Shao.Probability.OriginalGaussianTail
import Shao.Probability.SourceClockBridge
import Shao.Probability.SourceDesmoothing
import Shao.Probability.TruncationSampleSize
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace Shao.Probability
open MeasureTheory ProbabilityTheory
open scoped BigOperators


private theorem ocp_strict_compl (n : ℕ) (hn : 0 < n) (u : ℝ) (hu : 0 < u) :
    {v : Shao.Path n | 0 < Shao.energy v ∧
      Shao.maxWithZero v < u * Real.sqrt (Shao.energy v)} =
      (Shao.upperCrossing hn u)ᶜ := by
  ext v
  change (0 < Shao.energy v ∧ _) ↔ ¬ u * Real.sqrt (Shao.energy v) ≤ Shao.upperMax v hn
  constructor
  · intro hv
    rw [Shao.maxWithZero_eq v hn, max_lt_iff] at hv
    exact not_le.mpr hv.2.2
  · intro hv
    have hmax := not_le.mp hv
    have hQ : 0 < Shao.energy v := by
      by_contra h
      have hz := le_antisymm (le_of_not_gt h) (Shao.energy_nonneg v)
      have hc := Shao.mem_upperCrossing_of_energy_eq_zero v hn u hz
      exact hv hc
    refine ⟨hQ, ?_⟩
    rw [Shao.maxWithZero_eq v hn, max_lt_iff]
    exact ⟨mul_pos hu (Real.sqrt_pos.mpr hQ), hmax⟩

private theorem ocp_strict_nonpos (n : ℕ) (u : ℝ) (hu : u ≤ 0) :
    {v : Shao.Path n | 0 < Shao.energy v ∧
      Shao.maxWithZero v < u * Real.sqrt (Shao.energy v)} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hw : u * Real.sqrt (Shao.energy v) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hu (Real.sqrt_nonneg _)
  exact (not_lt_of_ge (hw.trans (Shao.maxWithZero_nonneg v))) hv.2

theorem sourceTruncation_original_two_signs_bad_crossing :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 0 < n),
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 →
        (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 800 →
          Shao.truncationBudget nu n x ≤ epsilon ^ 3 / 8 →
          let h : ℝ := epsilon / (1 + x)
          let N : Set (Shao.Path n) := {v | ∀ j : Fin n, |v j| ≤ h}
          let P0 : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
          let w : ℝ := Shao.truncationBudget nu n x * Shao.standardNormalTail x
          ∀ u : ℝ, 0 < u → |u - x| ≤ 1 / (1 + x) →
            (∀ s : ℝ, (s = 1 ∨ s = -1) →
              P0.real ({v : Shao.Path n |
                u * Real.sqrt (Shao.energy v) ≤ Shao.upperMax (s • v) hn} ∩ Nᶜ) ≤
                C / epsilon ^ 3 * w) ∧
            P0.real ({v : Shao.Path n |
              u * Real.sqrt (Shao.energy v) ≤ |Shao.prefixSum v n|} ∩ Nᶜ) ≤
                C / epsilon ^ 3 * w ∧
            P0.real (Shao.upperCrossing hn u ∩ Nᶜ) +
              P0.real ({v : Shao.Path n |
                u * Real.sqrt (Shao.energy v) ≤ |Shao.prefixSum v n|} ∩ Nᶜ) ≤
                  C / epsilon ^ 3 * w := by
  classical
  obtain ⟨Cm, hCm, hmarked⟩ := original_marked_crossing_gaussian_upper
  refine ⟨3 * Cm * Real.exp 2, by positivity, ?_⟩
  intro nu hnu n hn h2 hmean hnorm x epsilon hx he he800 hR
  letI : IsProbabilityMeasure nu := hnu
  dsimp only
  let h : ℝ := epsilon / (1 + x)
  let N : Set (Shao.Path n) := {v | ∀ j : Fin n, |v j| ≤ h}
  let P0 : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let w : ℝ := Shao.truncationBudget nu n x * Shao.standardNormalTail x
  change ∀ u : ℝ, 0 < u → |u - x| ≤ 1 / (1 + x) → _
  intro u hu hux
  have he1 : epsilon ≤ 1 := by linarith
  have he3 : 0 < epsilon ^ 3 := pow_pos he 3
  have hE : epsilon ^ 3 / 8 ≤ (1 / 16 : ℝ) := by
    have hc : epsilon ^ 3 ≤ 1 := pow_le_one₀ he.le he1
    have hsmall : epsilon ≤ (1 / 2 : ℝ) := by linarith
    have hc' := pow_le_pow_left₀ he.le hsmall 3
    norm_num at hc'
    linarith
  have hsize0 := Shao.truncationBudget_sample_size_lower nu n h2 hnorm x
    (epsilon ^ 3 / 8) hx hR hE
  have ha : 0 < 1 + x := by linarith
  have hdist : |u - x| ≤ 1 := hux.trans ((div_le_one ha).mpr (by linarith))
  have hua : u ≤ 1 + x := by linarith [le_abs_self (u - x)]
  have hsize : u ^ 6 ≤ (n : ℝ) :=
    (pow_le_pow_left₀ hu.le hua 6).trans (hsize0.1.trans hsize0.2)
  have hR1 : Shao.truncationBudget nu n x ≤ 1 := hR.trans (hE.trans (by norm_num))
  have hcut : (n : ℝ) * (∫ z : ℝ, Shao.truncationF (u * z) ∂nu) ≤ 1 := by
    apply le_trans _ hR1
    exact mul_le_mul_of_nonneg_left
      (integral_mono (Shao.integrable_truncationF_mul nu h2 u)
        (Shao.integrable_truncationF_mul nu h2 (1 + x))
        (fun z => Shao.truncationF_mono_scale u (1 + x) z hu.le hua))
      (Nat.cast_nonneg n)
  have htail := (Shao.sourceTruncation_tail_budget nu n h2 x epsilon hx he he1).1
  have hT := (Shao.standardNormalTail_local_comparison x u hx hu.le hux).2
  have hT0 : 0 ≤ Shao.standardNormalTail x :=
    (Shao.standardNormalTail_basic.2.2.1 x).1.le
  have hR0 := Shao.truncationBudget_nonneg nu n h2 x
  have hw : 0 ≤ w := mul_nonneg hR0 hT0
  have hmarked' (s : ℝ) (hs : s = 1 ∨ s = -1) :
      P0.real ({v : Shao.Path n |
        u * Real.sqrt (Shao.energy v) ≤ Shao.upperMax (s • v) hn} ∩ Nᶜ) ≤
        Cm * Real.exp 2 / epsilon ^ 3 * w := by
    have hm := hmarked nu inferInstance n hn h2 hmean hnorm u hu hsize hcut h
      (div_pos he ha) s hs
    have hset : {v : Shao.Path n |
        u * Real.sqrt (Shao.energy v) ≤ Shao.upperMax (s • v) hn ∧
          ∃ i : Fin n, h < |v i|} =
      {v : Shao.Path n |
        u * Real.sqrt (Shao.energy v) ≤ Shao.upperMax (s • v) hn} ∩ Nᶜ := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, N,
        not_forall, not_le]
    rw [hset] at hm
    apply hm.trans
    calc
      _ = Cm * ((n : ℝ) * nu.real {z : ℝ | h < |z|}) * Shao.standardNormalTail u := by ring
      _ ≤ Cm * (Shao.truncationBudget nu n x / epsilon ^ 3) *
          (Real.exp 2 * Shao.standardNormalTail x) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left htail hCm.le) hT
          (Shao.standardNormalTail_basic.2.2.1 u).1.le (by positivity)
      _ = _ := by dsimp [w]; ring
  have hp := hmarked' 1 (Or.inl rfl)
  have hm := hmarked' (-1) (Or.inr rfl)
  have hsub : {v : Shao.Path n |
      u * Real.sqrt (Shao.energy v) ≤ |Shao.prefixSum v n|} ∩ Nᶜ ⊆
      ({v : Shao.Path n | u * Real.sqrt (Shao.energy v) ≤ Shao.upperMax ((1 : ℝ) • v) hn} ∩ Nᶜ) ∪
      ({v : Shao.Path n | u * Real.sqrt (Shao.energy v) ≤ Shao.upperMax ((-1 : ℝ) • v) hn} ∩ Nᶜ) := by
    intro v hv
    have hab : u * Real.sqrt (Shao.energy v) ≤ Shao.prefixSum v n ∨
        u * Real.sqrt (Shao.energy v) ≤ -Shao.prefixSum v n := by
      by_cases hs : 0 ≤ Shao.prefixSum v n
      · left; simpa only [Set.mem_setOf_eq, abs_of_nonneg hs] using hv.1
      · right; simpa only [Set.mem_setOf_eq, abs_of_neg (lt_of_not_ge hs)] using hv.1
    rcases hab with hs | hs
    · left
      refine ⟨?_, hv.2⟩
      simpa only [Set.mem_setOf_eq, one_smul] using hs.trans (Shao.le_upperMax v hn n hn le_rfl)
    · right
      refine ⟨?_, hv.2⟩
      have hlast := Shao.le_upperMax ((-1 : ℝ) • v) hn n hn le_rfl
      rw [Shao.prefixSum_smul] at hlast
      change u * Real.sqrt (Shao.energy v) ≤ Shao.upperMax ((-1 : ℝ) • v) hn
      linarith
  have hend : P0.real ({v : Shao.Path n |
      u * Real.sqrt (Shao.energy v) ≤ |Shao.prefixSum v n|} ∩ Nᶜ) ≤
      2 * (Cm * Real.exp 2 / epsilon ^ 3 * w) := by
    apply (measureReal_mono hsub).trans
    apply (measureReal_union_le _ _).trans
    linarith
  have hb0 : 0 ≤ Cm * Real.exp 2 / epsilon ^ 3 * w := by positivity
  have hsingle : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      P0.real ({v : Shao.Path n |
        u * Real.sqrt (Shao.energy v) ≤ Shao.upperMax (s • v) hn} ∩ Nᶜ) ≤
        3 * Cm * Real.exp 2 / epsilon ^ 3 * w := by
    intro s hs
    have hh := hmarked' s hs
    calc
      _ ≤ Cm * Real.exp 2 / epsilon ^ 3 * w := hh
      _ ≤ 3 * (Cm * Real.exp 2 / epsilon ^ 3 * w) := by linarith only [hb0]
      _ = _ := by ring
  refine ⟨hsingle, ?_, ?_⟩
  · change P0.real ({v : Shao.Path n |
        u * Real.sqrt (Shao.energy v) ≤ |Shao.prefixSum v n|} ∩ Nᶜ) ≤
        3 * Cm * Real.exp 2 / epsilon ^ 3 * w
    calc
      _ ≤ 2 * (Cm * Real.exp 2 / epsilon ^ 3 * w) := hend
      _ ≤ 3 * (Cm * Real.exp 2 / epsilon ^ 3 * w) := by linarith only [hb0]
      _ = _ := by ring
  · have hp' : P0.real (Shao.upperCrossing hn u ∩ Nᶜ) ≤
        Cm * Real.exp 2 / epsilon ^ 3 * w := by
      simpa only [one_smul, Shao.upperCrossing] using hp
    change P0.real (Shao.upperCrossing hn u ∩ Nᶜ) +
      P0.real ({v : Shao.Path n |
        u * Real.sqrt (Shao.energy v) ≤ |Shao.prefixSum v n|} ∩ Nᶜ) ≤
        3 * Cm * Real.exp 2 / epsilon ^ 3 * w
    calc
      _ ≤ 3 * (Cm * Real.exp 2 / epsilon ^ 3 * w) := by linarith only [hp', hend]
      _ = _ := by ring

theorem endpoint_cdf_exact_zero_energy_identity
    (n : ℕ) (P : Measure (Shao.Path n)) [IsProbabilityMeasure P]
    (t : ℝ) (ht : 0 < t) :
    let Wplus : Set (Shao.Path n) :=
      {v | t * Real.sqrt (Shao.energy v) ≤ Shao.prefixSum v n}
    let Wminus : Set (Shao.Path n) :=
      {v | t * Real.sqrt (Shao.energy v) ≤ -Shao.prefixSum v n}
    P.real {v : Shao.Path n |
      0 < Shao.energy v ∧ |Shao.prefixSum v n| < t * Real.sqrt (Shao.energy v)} =
      1 - P.real Wplus - P.real Wminus + P.real {v : Shao.Path n | Shao.energy v = 0} := by
  classical
  dsimp only
  let Wplus : Set (Shao.Path n) :=
    {v | t * Real.sqrt (Shao.energy v) ≤ Shao.prefixSum v n}
  let Wminus : Set (Shao.Path n) :=
    {v | t * Real.sqrt (Shao.energy v) ≤ -Shao.prefixSum v n}
  have hm : MeasurableSet Wminus := measurableSet_le
    (Shao.measurable_energyWall t) (Shao.measurable_prefixSum n).neg
  have hcompl : {v : Shao.Path n |
      0 < Shao.energy v ∧ |Shao.prefixSum v n| < t * Real.sqrt (Shao.energy v)} =
      (Wplus ∪ Wminus)ᶜ := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_union, Wplus, Wminus]
    constructor
    · intro hv
      have hh := abs_lt.mp hv.2
      push_neg
      constructor <;> linarith
    · intro hv
      push_neg at hv
      have hQ : 0 < Shao.energy v := by
        by_contra h
        have hz := le_antisymm (le_of_not_gt h) (Shao.energy_nonneg v)
        have hs := Shao.prefixSum_eq_zero_of_energy_eq_zero v hz n
        simp only [hz, hs, Real.sqrt_zero, mul_zero, lt_self_iff_false, false_and] at hv
      exact ⟨hQ, abs_lt.mpr ⟨by linarith [hv.2], hv.1⟩⟩
  have hinter : Wplus ∩ Wminus = {v : Shao.Path n | Shao.energy v = 0} := by
    ext v
    change (t * Real.sqrt (Shao.energy v) ≤ Shao.prefixSum v n ∧
      t * Real.sqrt (Shao.energy v) ≤ -Shao.prefixSum v n) ↔ Shao.energy v = 0
    constructor
    · intro hv
      have hw : t * Real.sqrt (Shao.energy v) ≤ 0 := by linarith [hv.1, hv.2]
      have hs : Real.sqrt (Shao.energy v) = 0 := by
        have hs0 := Real.sqrt_nonneg (Shao.energy v)
        nlinarith
      exact (Real.sqrt_eq_zero (Shao.energy_nonneg v)).mp hs
    · intro hz
      have hs := Shao.prefixSum_eq_zero_of_energy_eq_zero v hz n
      rw [hz, hs]
      norm_num
  have hp : MeasurableSet Wplus := measurableSet_le
    (Shao.measurable_energyWall t) (Shao.measurable_prefixSum n)
  have hu := measureReal_union_add_inter (μ := P) (s := Wplus) hm
  rw [hcompl, measureReal_compl (hp.union hm), probReal_univ]
  rw [hinter] at hu
  linarith

theorem sourceTruncation_original_max_cdf_pullback :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 0 < n),
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 →
        (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 800 →
          Shao.truncationBudget nu n x ≤ epsilon ^ 3 / 8 →
          let h : ℝ := epsilon / (1 + x)
          let N : Set (Shao.Path n) := {v | ∀ j : Fin n, |v j| ≤ h}
          let P0 : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
          let rho : Measure ℝ := ProbabilityTheory.cond nu {z : ℝ | |z| ≤ h}
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
          let p : ℝ := P0.real N
          let R : ℝ := Shao.truncationBudget nu n x
          let w : ℝ := R * Shao.standardNormalTail x
          let G : ℝ → ℝ := fun u => if 0 < u then 1 - 2 * Shao.standardNormalTail u else 0
          let F0 : ℝ → ℝ := fun u => P0.real {v : Shao.Path n |
            0 < Shao.energy v ∧ Shao.maxWithZero v < u * Real.sqrt (Shao.energy v)}
          let F : ℝ → ℝ := fun u => P.real {v : Shao.Path n |
            0 < Shao.energy v ∧ Shao.maxWithZero v < u * Real.sqrt (Shao.energy v)}
          let E : ℝ → ℝ := fun u => F0 u - G u
          let bad : ℝ → ℝ := fun u =>
            if 0 < u then P0.real (Shao.upperCrossing hn u ∩ Nᶜ) else 0
          let bias : ℝ → ℝ := fun u =>
            if 0 < u then 2 * Shao.standardNormalTail u * (1 - p) else 0
          (7 / 8 : ℝ) ≤ p ∧ p ≤ 1 ∧ 1 - p ≤ R / epsilon ^ 3 ∧
            IsProbabilityMeasure rho ∧ IsProbabilityMeasure P ∧
            ProbabilityTheory.cond P0 N = P ∧
            (∀ u : ℝ, E u = p * (F u - G u) + bias u - bad u) ∧
            ∀ u : ℝ, |u - x| ≤ 1 / (1 + x) →
              0 ≤ bad u ∧ 0 ≤ bias u ∧
              bad u + bias u ≤ C / epsilon ^ 3 * w ∧
              |p * (F u - G u) - E u| ≤ C / epsilon ^ 3 * w ∧
              |F u - G u - E u / p| ≤ (4 / 3 : ℝ) * C / epsilon ^ 3 * w ∧
              (∀ s : ℝ, (s = 1 ∨ s = -1) →
                s * E u / p - C / epsilon ^ 3 * w / p ≤ s * (F u - G u) ∧
                s * (F u - G u) ≤ s * E u / p + C / epsilon ^ 3 * w / p) := by
  classical
  obtain ⟨Cb, hCb, hbad⟩ := sourceTruncation_original_two_signs_bad_crossing
  refine ⟨Cb + 2 * Real.exp 2, by positivity, ?_⟩
  intro nu hnu n hn h2 hmean hnorm x epsilon hx he he800 hR
  letI : IsProbabilityMeasure nu := hnu
  let h : ℝ := epsilon / (1 + x)
  let N : Set (Shao.Path n) := {v | ∀ j : Fin n, |v j| ≤ h}
  let P0 : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let rho : Measure ℝ := cond nu {z : ℝ | |z| ≤ h}
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
  let p : ℝ := P0.real N
  let R : ℝ := Shao.truncationBudget nu n x
  let w : ℝ := R * Shao.standardNormalTail x
  let G : ℝ → ℝ := fun u => if 0 < u then 1 - 2 * Shao.standardNormalTail u else 0
  let F0 : ℝ → ℝ := fun u => P0.real {v : Shao.Path n |
    0 < Shao.energy v ∧ Shao.maxWithZero v < u * Real.sqrt (Shao.energy v)}
  let F : ℝ → ℝ := fun u => P.real {v : Shao.Path n |
    0 < Shao.energy v ∧ Shao.maxWithZero v < u * Real.sqrt (Shao.energy v)}
  let E : ℝ → ℝ := fun u => F0 u - G u
  let bad : ℝ → ℝ := fun u => if 0 < u then P0.real (Shao.upperCrossing hn u ∩ Nᶜ) else 0
  let bias : ℝ → ℝ := fun u => if 0 < u then 2 * Shao.standardNormalTail u * (1 - p) else 0
  change (7 / 8 : ℝ) ≤ p ∧ p ≤ 1 ∧ 1 - p ≤ R / epsilon ^ 3 ∧
    IsProbabilityMeasure rho ∧ IsProbabilityMeasure P ∧ cond P0 N = P ∧
    (∀ u : ℝ, E u = p * (F u - G u) + bias u - bad u) ∧ _
  have he1 : epsilon ≤ 1 := by linarith
  have hNm : MeasurableSet N := by
    have hNset : N = ⋂ i : Fin n, {v : Shao.Path n | |v i| ≤ h} := by
      ext v; simp only [N, Set.mem_setOf_eq, Set.mem_iInter]
    rw [hNset]
    exact MeasurableSet.iInter (fun i : Fin n => measurableSet_le
      (continuous_abs.measurable.comp
        (measurable_pi_apply i : Measurable (fun v : Shao.Path n => v i))) measurable_const)
  have hNrepr : (⋂ i : Fin n, (Function.eval i) ⁻¹' {z : ℝ | |z| ≤ h}) = N := by
    ext v; simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq, N]
  have hIndep : iIndepFun (fun i : Fin n => Function.eval i) P0 :=
    iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable)
  have hLaw (i : Fin n) : IdentDistrib (Function.eval i) (id : ℝ → ℝ) P0 nu := by
    refine ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    exact (measurePreserving_eval (fun _ : Fin n => nu) i).map_eq.trans Measure.map_id.symm
  have hdata := sourceTruncation_conditioned_sample (fun i : Fin n => measurable_pi_apply i)
    hIndep hLaw h2 x epsilon hx he he1 hR
  dsimp only at hdata
  change P0.real ((⋂ i : Fin n, (Function.eval i) ⁻¹' {z : ℝ | |z| ≤ h})ᶜ) ≤ R / epsilon ^ 3 ∧ _ at hdata
  rw [hNrepr] at hdata
  have hp : (7 / 8 : ℝ) ≤ p := hdata.2.1
  have hp1 : p ≤ 1 := measureReal_le_one
  have hcomp : 1 - p ≤ R / epsilon ^ 3 := by
    have hh := hdata.1
    rw [measureReal_compl hNm, probReal_univ] at hh
    exact hh
  have hrho : IsProbabilityMeasure rho :=
    (Shao.sourceTruncation_law_data nu n h2 hnorm x epsilon hx he (by linarith) hR).2.2.1
  letI : IsProbabilityMeasure rho := hrho
  have hP : IsProbabilityMeasure P := inferInstance
  have hcond : cond P0 N = P := by
    have hm := hdata.2.2.2.1
    change Measure.map (id : Shao.Path n → Shao.Path n) (cond P0 N) = P at hm
    simpa only [Measure.map_id] using hm
  have hp0 : 0 < p := by linarith
  have he3 : 0 < epsilon ^ 3 := pow_pos he 3
  have hT0 : 0 ≤ Shao.standardNormalTail x := (Shao.standardNormalTail_basic.2.2.1 x).1.le
  have hR0 : 0 ≤ R := Shao.truncationBudget_nonneg nu n h2 x
  have hw : 0 ≤ w := mul_nonneg hR0 hT0
  have hzero (u : ℝ) (hu : u ≤ 0) : F0 u = 0 ∧ F u = 0 := by
    simp only [F0, F, ocp_strict_nonpos n u hu, measureReal_empty, and_self]
  have hid (u : ℝ) : E u = p * (F u - G u) + bias u - bad u := by
    by_cases hu : 0 < u
    · have hF0 : F0 u = 1 - P0.real (Shao.upperCrossing hn u) := by
        change P0.real {v : Shao.Path n | 0 < Shao.energy v ∧
          Shao.maxWithZero v < u * Real.sqrt (Shao.energy v)} = _
        rw [ocp_strict_compl n hn u hu,
          measureReal_compl (Shao.measurableSet_upperCrossing hn u), probReal_univ]
      have hF : F u = 1 - P.real (Shao.upperCrossing hn u) := by
        change P.real {v : Shao.Path n | 0 < Shao.energy v ∧
          Shao.maxWithZero v < u * Real.sqrt (Shao.energy v)} = _
        rw [ocp_strict_compl n hn u hu,
          measureReal_compl (Shao.measurableSet_upperCrossing hn u), probReal_univ]
      have hmul : P.real (Shao.upperCrossing hn u) * p =
          P0.real (N ∩ Shao.upperCrossing hn u) := by
        simpa only [hcond, p, Measure.real_def, ENNReal.toReal_mul] using
          congrArg ENNReal.toReal (cond_mul_eq_inter hNm (Shao.upperCrossing hn u) P0)
      have hsplit := measureReal_inter_add_sdiff (μ := P0)
        (s := Shao.upperCrossing hn u) hNm
      have hdiff : Shao.upperCrossing hn u \ N = Shao.upperCrossing hn u ∩ Nᶜ := rfl
      rw [hdiff, Set.inter_comm (Shao.upperCrossing hn u) N, ← hmul] at hsplit
      dsimp only [E, G, bias, bad]
      simp only [if_pos hu, hF0, hF]
      nlinarith only [hsplit]
    · have hz := hzero u (le_of_not_gt hu)
      simp only [E, G, bad, bias, if_neg hu, hz.1, hz.2, sub_zero, mul_zero, zero_add]
  refine ⟨hp, hp1, hcomp, hrho, hP, hcond, hid, ?_⟩
  intro u hux
  have hbad0 : 0 ≤ bad u := by dsimp [bad]; split_ifs <;> positivity
  have hbias0 : 0 ≤ bias u := by
    dsimp [bias]
    split_ifs with hu
    · exact mul_nonneg (mul_nonneg (by norm_num)
        (Shao.standardNormalTail_basic.2.2.1 u).1.le) (by linarith)
    · exact le_rfl
  have hpay : bad u + bias u ≤ (Cb + 2 * Real.exp 2) / epsilon ^ 3 * w := by
    by_cases hu : 0 < u
    · have hbad' := (hbad nu n hn h2 hmean hnorm x epsilon hx he he800 hR
          u hu hux).1 1 (Or.inl rfl)
      have hb : bad u ≤ Cb / epsilon ^ 3 * w := by
        simpa only [bad, if_pos hu, one_smul, Shao.upperCrossing, w, R, N, h] using hbad'
      have hT := (Shao.standardNormalTail_local_comparison x u hx hu.le hux).2
      have hbi : bias u ≤ 2 * Real.exp 2 / epsilon ^ 3 * w := by
        dsimp only [bias]; rw [if_pos hu]
        calc
          _ ≤ 2 * (Real.exp 2 * Shao.standardNormalTail x) * (R / epsilon ^ 3) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hT (by norm_num)) hcomp
              (by linarith) (by positivity)
          _ = _ := by dsimp [w]; ring
      calc
        _ ≤ Cb / epsilon ^ 3 * w + 2 * Real.exp 2 / epsilon ^ 3 * w := add_le_add hb hbi
        _ = _ := by ring
    · simp only [bad, bias, if_neg hu, zero_add]
      positivity
  have herr : |p * (F u - G u) - E u| ≤ (Cb + 2 * Real.exp 2) / epsilon ^ 3 * w := by
    rw [hid u]
    apply le_trans _ hpay
    apply abs_le.mpr
    constructor <;> linarith
  have hdiv : |F u - G u - E u / p| ≤
      (Cb + 2 * Real.exp 2) / epsilon ^ 3 * w / p := by
    have hh : F u - G u - E u / p = (p * (F u - G u) - E u) / p := by
      field_simp
    rw [hh, abs_div, abs_of_pos hp0]
    exact (div_le_div_iff_of_pos_right hp0).mpr herr
  have hpInv : 1 / p ≤ (4 / 3 : ℝ) := (div_le_iff₀ hp0).mpr (by linarith)
  have hrel : |F u - G u - E u / p| ≤
      (4 / 3 : ℝ) * (Cb + 2 * Real.exp 2) / epsilon ^ 3 * w := by
    apply hdiv.trans
    have hh := mul_le_mul_of_nonneg_left hpInv
      (show 0 ≤ (Cb + 2 * Real.exp 2) / epsilon ^ 3 * w by positivity)
    convert hh using 1 <;> ring
  refine ⟨hbad0, hbias0, hpay, herr, hrel, ?_⟩
  intro s hs
  change s * E u / p - (Cb + 2 * Real.exp 2) / epsilon ^ 3 * w / p ≤ s * (F u - G u) ∧
    s * (F u - G u) ≤ s * E u / p + (Cb + 2 * Real.exp 2) / epsilon ^ 3 * w / p
  have hh := abs_le.mp hdiv
  rcases hs with hs | hs
  · subst s
    simp only [one_mul]
    constructor <;> linarith only [hh.1, hh.2]
  · subst s
    simp only [neg_one_mul, neg_div]
    constructor <;> linarith only [hh.1, hh.2]

end Shao.Probability
