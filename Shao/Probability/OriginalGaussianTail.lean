import Shao.Probability.BoundedGaussianTail
import Shao.Probability.RetainedSample
import Shao.Probability.RetentionEvent
import Shao.Basic.Deletion
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
Original finite-second-law coarse and marked Gaussian upper bounds.
The actual weak crossing monitors times 1 through n and retains zero energy.
All conditioning is on the closed cutoff and an exact finite retained set.
The marked bound uses the actual signed scalar pushforward after one deletion.
No global original third moment or exponential moment is imposed.
These bounds do not close original endpoint relative error, CDF pullback,
D2, contraction, or the C1/C2 root assembly.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Shao.Probability
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

private theorem ogt_fiber_mass (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (n : ℕ) (B : Set ℝ) (s : Finset (Fin n)) :
    (Measure.pi (fun _ : Fin n => nu)).real
        {a : Shao.Path n | retentionSet (fun i a => a i) B a = s} =
      nu.real B ^ s.card * nu.real Bᶜ ^ (n - s.card) := by
  classical
  have hset : {a : Shao.Path n | retentionSet (fun i a => a i) B a = s} =
      Set.pi Set.univ (fun i => if i ∈ s then B else Bᶜ) := by
    rw [retentionSet_eq_event]
    ext a
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
  rw [Measure.real_def, hset, Measure.pi_pi, ENNReal.toReal_prod]
  simp only [apply_ite, ← Measure.real_def]
  rw [Finset.prod_ite]
  have hs : Finset.univ.filter (fun i : Fin n => i ∈ s) = s := by ext i; simp
  have hsc : Finset.univ.filter (fun i : Fin n => i ∉ s) = sᶜ := by ext i; simp
  simp only [hs, hsc, Finset.prod_const, Finset.card_compl, Fintype.card_fin]

private theorem ogt_binomial_weight (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (n : ℕ) (B : Set ℝ) (l : ℝ) :
    (∑ s : Finset (Fin n), Real.exp (l * ((n - s.card : ℕ) : ℝ)) *
      (Measure.pi (fun _ : Fin n => nu)).real
        {a : Shao.Path n | retentionSet (fun i a => a i) B a = s}) =
      (nu.real B + Real.exp l * nu.real Bᶜ) ^ n := by
  classical
  simp_rw [ogt_fiber_mass, mul_comm l, Real.exp_nat_mul]
  have h := Fintype.prod_add (fun _ : Fin n => nu.real B)
    (fun _ : Fin n => Real.exp l * nu.real Bᶜ)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.card_compl, mul_pow] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro s _
  ring

private theorem ogt_binomial_weight_le (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (n : ℕ) (B : Set ℝ) (hB : MeasurableSet B) (l : ℝ) (hl : 0 ≤ l)
    (hq : (n : ℝ) * nu.real Bᶜ ≤ 1) :
    (∑ s : Finset (Fin n), Real.exp (l * ((n - s.card : ℕ) : ℝ)) *
      (Measure.pi (fun _ : Fin n => nu)).real
        {a : Shao.Path n | retentionSet (fun i a => a i) B a = s}) ≤
      Real.exp (Real.exp l - 1) := by
  rw [ogt_binomial_weight]
  have hpq : nu.real B + nu.real Bᶜ = 1 := by
    rw [measureReal_compl hB, probReal_univ]
    ring
  have hel : 0 ≤ Real.exp l - 1 := by linarith [Real.one_le_exp_iff.mpr hl]
  have hbase : nu.real B + Real.exp l * nu.real Bᶜ =
      1 + nu.real Bᶜ * (Real.exp l - 1) := by nlinarith only [hpq]
  calc
    _ = (1 + nu.real Bᶜ * (Real.exp l - 1)) ^ n := by rw [hbase]
    _ ≤ (Real.exp (nu.real Bᶜ * (Real.exp l - 1))) ^ n := by
      apply pow_le_pow_left₀ (by positivity)
      simpa only [add_comm] using Real.add_one_le_exp (nu.real Bᶜ * (Real.exp l - 1))
    _ = Real.exp ((n : ℝ) * (nu.real Bᶜ * (Real.exp l - 1))) :=
      (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_right hq hel])

private theorem ogt_retained_fiber :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ), IsProbabilityMeasure nu →
        ∀ (n : ℕ) (hn : 0 < n),
          Integrable (fun z : ℝ => z ^ 2) nu →
          (∫ z : ℝ, z ∂nu) = 0 →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
          ∀ t : ℝ, 2 ≤ t → t ^ 6 ≤ (n : ℝ) →
            (n : ℝ) * (∫ z : ℝ, Shao.truncationF (t * z) ∂nu) ≤ 1 →
            ∀ s : Finset (Fin n), ((n - s.card : ℕ) : ℝ) ≤ t ^ 2 / 2 →
              (Measure.pi (fun _ : Fin n => nu)).real
                ({a : Shao.Path n | retentionSet (fun i a => a i)
                    (Shao.retainedCutoffSet t) a = s} ∩ Shao.upperCrossing hn t) ≤
                3 * C * Real.exp (((n - s.card : ℕ) : ℝ) / 2) *
                  Shao.standardNormalTail t *
                    (Measure.pi (fun _ : Fin n => nu)).real
                      {a : Shao.Path n | retentionSet (fun i a => a i)
                        (Shao.retainedCutoffSet t) a = s} := by
  classical
  obtain ⟨C, hC, hbound⟩ := bounded_random_denominator_gaussian_upper 2 (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro nu hnu n hn h2 hmean hnorm t ht hsize hcut s hj
  letI : IsProbabilityMeasure nu := hnu
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let j : ℕ := n - s.card
  let eta : Measure ℝ := Shao.retainedCutoffLaw nu t
  let y : ℝ := Real.sqrt (t ^ 2 - (j : ℝ))
  let A : Set (Shao.Path n) := {a | retentionSet (fun i a => a i)
    (Shao.retainedCutoffSet t) a = s}
  let Y : Shao.Path n → Shao.Path s.card := fun a => Shao.retainedPath a s
  have hAm : MeasurableSet A := measurableSet_retentionSet_eq
    (fun i => measurable_pi_apply i) _ (Shao.measurableSet_retainedCutoffSet t) s
  have hcard : s.card ≤ n := by simpa only [Fintype.card_fin] using s.card_le_univ
  have hret : n - j = s.card := Nat.sub_sub_self hcard
  obtain ⟨hn64, hjn, hm, _, _⟩ := Shao.retainedSample_size_bounds n j t ht hsize hj
  have hs : 0 < s.card := by omega
  have hn2 : 2 ≤ n := by omega
  have htpos : 0 < t := by linarith
  have hq : 0 < Shao.retainedCutoffMass nu t := by
    have h := (Shao.retainedCutoffMass_bounds nu n hn2 t htpos h2 hcut).2.1
    linarith
  letI : IsProbabilityMeasure eta := Shao.retainedCutoffLaw_isProbabilityMeasure nu t hq
  obtain ⟨hsupp, hclock, hmu, hthird⟩ :=
    Shao.retainedSample_raw_moment_bounds nu n j t ht hsize hj h2 hmean hnorm hcut
  rw [hret] at hclock hmu hthird
  have hy1 : 1 ≤ y := (Shao.retainedSample_threshold_bounds j t ht hj).2.2
  have hi2 := (Shao.integrable_retainedCutoffLaw_id_sq nu t hq h2).2
  have hi3 := Shao.integrable_retainedCutoffLaw_abs_cube nu t htpos hq h2
  have htail : (Measure.pi (fun _ : Fin s.card => eta)).real
      (Shao.upperCrossing hs y) ≤ 3 * C * Real.exp ((j : ℝ) / 2) *
        Shao.standardNormalTail t := by
    apply (hbound eta inferInstance s.card hs y hy1 hsupp hi2 hi3
      hclock.1 hclock.2 hmu hthird).trans
    have hdel := Shao.standardNormalTail_deletion_comparison j t htpos.le hj
    have hh := mul_le_mul_of_nonneg_left hdel hC.le
    convert hh using 1 <;> ring
  by_cases hA : P A = 0
  · have hz : P (A ∩ Shao.upperCrossing hn t) = 0 :=
      measure_inter_null_of_null_left _ hA
    change P.real (A ∩ Shao.upperCrossing hn t) ≤ _ * P.real A
    simp only [Measure.real_def, hz, hA, ENNReal.toReal_zero, mul_zero, le_refl]
  · letI : IsProbabilityMeasure (cond P A) := cond_isProbabilityMeasure hA
    have hI : iIndepFun (fun i : Fin n => Function.eval i) P :=
      iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable)
    have hLaw (i : Fin n) : IdentDistrib (Function.eval i) (id : ℝ → ℝ) P nu := by
      refine ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable, ?_⟩
      exact (measurePreserving_eval (fun _ : Fin n => nu) i).map_eq.trans Measure.map_id.symm
    obtain ⟨_, hIc, hLc⟩ := iid_retained_cond_retentionSet_eq
      (fun i => measurable_pi_apply i) hI hLaw s hs (Shao.retainedCutoffSet t)
        (Shao.measurableSet_retainedCutoffSet t) hA
    have hYm : Measurable Y := Measurable.of_eval
      (fun r => measurable_pi_apply (Shao.retainedIndex s r))
    have hmap : Measure.map Y (cond P A) = Measure.pi (fun _ : Fin s.card => eta) :=
      iid_samplePath_map_eq_pi (fun r => measurable_pi_apply (Shao.retainedIndex s r)) hIc hLc
    have hcomp : Finset.univ \ sᶜ = s := by ext i; simp
    have hsc : sᶜ.card = j := by simp only [Finset.card_compl, Fintype.card_fin, j]
    have hsub : Shao.upperCrossing hn t ⊆ Y ⁻¹' Shao.upperCrossing hs y := by
      intro a ha
      have hd := Shao.upperCrossing_retainedPath_of_deletion a sᶜ hn
        (by rw [hsc]; exact hjn) t htpos
        (by rw [hsc]; nlinarith only [hj, sq_pos_of_pos htpos]) ha
      have hd' : ∀ hh : 0 < (Finset.univ \ sᶜ).card,
          Shao.retainedPath a (Finset.univ \ sᶜ) ∈
            Shao.upperCrossing hh (Real.sqrt (t ^ 2 - (sᶜ.card : ℝ))) := fun _ => hd
      rw [hcomp, hsc] at hd'
      exact hd' hs
    have hcond : (cond P A).real (Shao.upperCrossing hn t) ≤
        (Measure.pi (fun _ : Fin s.card => eta)).real (Shao.upperCrossing hs y) := by
      rw [← hmap]
      simp only [Measure.real_def]
      rw [Measure.map_apply hYm (Shao.measurableSet_upperCrossing hs y)]
      exact measureReal_mono hsub
    have hid : (cond P A).real (Shao.upperCrossing hn t) * P.real A =
        P.real (A ∩ Shao.upperCrossing hn t) := by
      simpa only [Measure.real_def, ENNReal.toReal_mul] using
        congrArg ENNReal.toReal (cond_mul_eq_inter hAm (Shao.upperCrossing hn t) P)
    change P.real (A ∩ Shao.upperCrossing hn t) ≤ _ * P.real A
    rw [← hid]
    exact mul_le_mul_of_nonneg_right (hcond.trans htail) ENNReal.toReal_nonneg

private theorem ogt_exp_tail (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-(t ^ 2)) ≤
      2 * Real.sqrt (2 * Real.pi) * Shao.standardNormalTail t := by
  have hA : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hm := (Shao.standardNormal_mills_bounds t ht).1
  have hphi : Shao.standardNormalDensity t =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2) := by
    simp [Shao.standardNormalDensity, gaussianPDFReal]
  rw [hphi] at hm
  have hpoly : 1 + t ≤ 2 * Real.exp (t ^ 2 / 2) := by
    have he := Real.add_one_le_exp (t ^ 2 / 2)
    nlinarith [sq_nonneg (t - 1 / 2)]
  have hid : Real.exp (-(t ^ 2)) * Real.exp (t ^ 2 / 2) =
      Real.exp (-t ^ 2 / 2) := by rw [← Real.exp_add]; congr 1; ring
  have hscaled := mul_le_mul_of_nonneg_left hpoly (Real.exp_nonneg (-(t ^ 2)))
  have hbound : Real.exp (-(t ^ 2)) * (1 + t) ≤ 2 * Real.exp (-t ^ 2 / 2) := by
    nlinarith only [hscaled, hid]
  have hml : Real.exp (-t ^ 2 / 2) ≤
      Shao.standardNormalTail t * Real.sqrt (2 * Real.pi) * (1 + t) := by
    have hh := (div_le_iff₀ (show 0 < 1 + t by linarith)).mp hm
    have hh' := mul_le_mul_of_nonneg_left hh hA.le
    field_simp at hh'
    simpa only [neg_div, mul_comm, mul_left_comm, mul_assoc] using hh'
  apply (mul_le_mul_iff_right₀ (show 0 < 1 + t by linarith)).mp
  nlinarith only [hbound, hml]

theorem original_coarse_gaussian_upper :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ), IsProbabilityMeasure nu →
        ∀ (n : ℕ) (hn : 0 < n),
          Integrable (fun z : ℝ => z ^ 2) nu →
          (∫ z : ℝ, z ∂nu) = 0 →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
          ∀ t : ℝ, 0 < t → t ^ 6 ≤ (n : ℝ) →
            (n : ℝ) * (∫ z : ℝ, Shao.truncationF (t * z) ∂nu) ≤ 1 →
            (Measure.pi (fun _ : Fin n => nu)).real (Shao.upperCrossing hn t) ≤
              C * Shao.standardNormalTail t := by
  classical
  obtain ⟨Cb, hCb, hF⟩ := ogt_retained_fiber
  let C0 : ℝ := 1 / Shao.standardNormalTail 8 +
    3 * Cb * Real.exp (Real.exp (1 / 2) - 1) +
      2 * Real.sqrt (2 * Real.pi) * Real.exp (Real.exp 2 - 1)
  have hT8 : 0 < Shao.standardNormalTail 8 := (Shao.standardNormalTail_basic.2.2.1 8).1
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  refine ⟨C0, hC0, ?_⟩
  intro nu hnu n hn h2 hmean hnorm t ht hsize hcut
  letI : IsProbabilityMeasure nu := hnu
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  have hT : 0 ≤ Shao.standardNormalTail t := (Shao.standardNormalTail_basic.2.2.1 t).1.le
  by_cases ht8 : 8 ≤ t
  · have ht2 : 2 ≤ t := by linarith
    have hn2 : 2 ≤ n := (Shao.retainedSample_size_bounds n 0 t ht2 hsize
      (by simp; positivity)).1.trans' (by norm_num)
    let B : Set ℝ := Shao.retainedCutoffSet t
    let A : Finset (Fin n) → Set (Shao.Path n) := fun s =>
      {a | retentionSet (fun i a => a i) B a = s}
    let U : ℝ := 3 * Cb * Shao.standardNormalTail t
    let V : ℝ := Real.exp (-(t ^ 2))
    have hU : 0 ≤ U := by dsimp [U]; positivity
    have hV : 0 ≤ V := Real.exp_nonneg _
    have hB : MeasurableSet B := Shao.measurableSet_retainedCutoffSet t
    have hq : (n : ℝ) * nu.real Bᶜ ≤ 1 := by
      have hlo := (Shao.retainedCutoffMass_bounds nu n hn2 t ht h2 hcut).1
      have hnr : (0 : ℝ) < n := by exact_mod_cast hn
      have hc : (n : ℝ) * (1 / (n : ℝ)) = 1 := by field_simp
      have hh := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg n)
      rw [measureReal_compl hB, probReal_univ]
      change (n : ℝ) * (1 - Shao.retainedCutoffMass nu t) ≤ 1
      nlinarith only [hh, hc]
    have hrow (s : Finset (Fin n)) :
        P.real (A s ∩ Shao.upperCrossing hn t) ≤
          U * (Real.exp ((1 / 2 : ℝ) * ((n - s.card : ℕ) : ℝ)) * P.real (A s)) +
            V * (Real.exp (2 * ((n - s.card : ℕ) : ℝ)) * P.real (A s)) := by
      by_cases hj : ((n - s.card : ℕ) : ℝ) ≤ t ^ 2 / 2
      · have hh := hF nu hnu n hn h2 hmean hnorm t ht2 hsize hcut s hj
        have hh' : P.real (A s ∩ Shao.upperCrossing hn t) ≤
            U * (Real.exp ((1 / 2 : ℝ) * ((n - s.card : ℕ) : ℝ)) * P.real (A s)) := by
          have hex : (1 / 2 : ℝ) * ((n - s.card : ℕ) : ℝ) =
              ((n - s.card : ℕ) : ℝ) / 2 := by ring
          rw [hex]
          convert hh using 1 <;> dsimp only [U, A, B, P] <;> ring
        exact hh'.trans (le_add_of_nonneg_right (by positivity))
      · have he : 1 ≤ V * Real.exp (2 * ((n - s.card : ℕ) : ℝ)) := by
          dsimp [V]
          rw [← Real.exp_add]
          exact Real.one_le_exp_iff.mpr (by linarith only [lt_of_not_ge hj])
        have hh : P.real (A s ∩ Shao.upperCrossing hn t) ≤ P.real (A s) :=
          measureReal_mono Set.inter_subset_left
        have hh' := mul_le_mul_of_nonneg_right he (measureReal_nonneg (μ := P) (s := A s))
        have hb : P.real (A s ∩ Shao.upperCrossing hn t) ≤
            V * (Real.exp (2 * ((n - s.card : ℕ) : ℝ)) * P.real (A s)) := by
          nlinarith only [hh, hh']
        exact hb.trans (le_add_of_nonneg_left (by positivity))
    have hcover : (⋃ s : Finset (Fin n), A s ∩ Shao.upperCrossing hn t) =
        Shao.upperCrossing hn t := by
      ext a
      simp only [Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · rintro ⟨_, _, ha⟩
        exact ha
      · intro ha
        exact ⟨retentionSet (fun i a => a i) B a, rfl, ha⟩
    have hMGF1 := ogt_binomial_weight_le nu n B hB (1 / 2) (by norm_num) hq
    have hMGF2 := ogt_binomial_weight_le nu n B hB 2 (by norm_num) hq
    have hs : P.real (Shao.upperCrossing hn t) ≤
        U * Real.exp (Real.exp (1 / 2) - 1) + V * Real.exp (Real.exp 2 - 1) := by
      calc
        _ = P.real (⋃ s : Finset (Fin n), A s ∩ Shao.upperCrossing hn t) := by rw [hcover]
        _ ≤ ∑ s : Finset (Fin n), P.real (A s ∩ Shao.upperCrossing hn t) :=
          measureReal_iUnion_fintype_le _
        _ ≤ ∑ s : Finset (Fin n),
            (U * (Real.exp ((1 / 2 : ℝ) * ((n - s.card : ℕ) : ℝ)) * P.real (A s)) +
              V * (Real.exp (2 * ((n - s.card : ℕ) : ℝ)) * P.real (A s))) :=
          Finset.sum_le_sum (fun s _ => hrow s)
        _ = U * (∑ s : Finset (Fin n),
            Real.exp ((1 / 2 : ℝ) * ((n - s.card : ℕ) : ℝ)) * P.real (A s)) +
              V * (∑ s : Finset (Fin n),
                Real.exp (2 * ((n - s.card : ℕ) : ℝ)) * P.real (A s)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hMGF1 hU)
          (mul_le_mul_of_nonneg_left hMGF2 hV)
    have hv := mul_le_mul_of_nonneg_right (ogt_exp_tail t ht.le)
      (Real.exp_nonneg (Real.exp 2 - 1))
    have hextra : 0 ≤ (1 / Shao.standardNormalTail 8) * Shao.standardNormalTail t := by positivity
    change P.real (Shao.upperCrossing hn t) ≤ _
    dsimp only [U, V] at hs
    dsimp only [C0]
    nlinarith only [hs, hv, hextra]
  · have hmono : Shao.standardNormalTail 8 ≤ Shao.standardNormalTail t :=
      Shao.standardNormalTail_basic.1 (le_of_not_ge ht8)
    have hsmall : (1 : ℝ) ≤ (1 / Shao.standardNormalTail 8) * Shao.standardNormalTail t := by
      have hh : (1 : ℝ) ≤ Shao.standardNormalTail t / Shao.standardNormalTail 8 :=
        (le_div_iff₀ hT8).mpr (by simpa using hmono)
      convert hh using 1 <;> ring
    have hcoeff : 1 / Shao.standardNormalTail 8 ≤ C0 := by
      have h1 : 0 ≤ 3 * Cb * Real.exp (Real.exp (1 / 2) - 1) := by positivity
      have h2 : 0 ≤ 2 * Real.sqrt (2 * Real.pi) * Real.exp (Real.exp 2 - 1) := by positivity
      dsimp only [C0]
      linarith only [h1, h2]
    exact (measureReal_le_one (μ := P)).trans (hsmall.trans
      (mul_le_mul_of_nonneg_right hcoeff hT))

private theorem ogt_mark_retained_factor (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (n : ℕ) (i : Fin n) (s : Finset (Fin n)) (hi : i ∉ s)
    (H : Set ℝ) (hH : MeasurableSet H)
    (E : Set (Shao.Path s.card)) (hE : MeasurableSet E) :
    (Measure.pi (fun _ : Fin n => nu)).real
        ((fun a : Shao.Path n => a i) ⁻¹' H ∩
          (fun a : Shao.Path n => Shao.retainedPath a s) ⁻¹' E) =
      nu.real H * (Measure.pi (fun _ : Fin s.card => nu)).real E := by
  classical
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  have hI : iIndepFun (fun i : Fin n => Function.eval i) P :=
    iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable)
  have hdis : Disjoint ({i} : Finset (Fin n)) s := by simp [hi]
  have htuple := iIndepFun.indepFun_finset ({i} : Finset (Fin n)) s hdis hI
    (fun r => measurable_pi_apply r)
  have hInd : IndepFun (fun a : Shao.Path n => a i)
      (fun a : Shao.Path n => Shao.retainedPath a s) P := by
    exact htuple.comp (measurable_pi_apply (⟨i, by simp⟩ : ({i} : Finset (Fin n))))
      (Measurable.of_eval (fun r => measurable_pi_apply
        (⟨Shao.retainedIndex s r, Shao.retainedIndex_mem s r⟩ : s)))
  have hLaw (r : Fin n) : IdentDistrib (Function.eval r) (id : ℝ → ℝ) P nu := by
    refine ⟨(measurable_pi_apply r).aemeasurable, measurable_id.aemeasurable, ?_⟩
    exact (measurePreserving_eval (fun _ : Fin n => nu) r).map_eq.trans Measure.map_id.symm
  have hmap : Measure.map (fun a : Shao.Path n => Shao.retainedPath a s) P =
      Measure.pi (fun _ : Fin s.card => nu) := iid_samplePath_map_eq_pi
    (fun r => measurable_pi_apply (Shao.retainedIndex s r))
    (hI.precomp (Shao.retainedIndex s).injective) (fun r => hLaw (Shao.retainedIndex s r))
  have hM : Measurable (fun a : Shao.Path n => Shao.retainedPath a s) :=
    Measurable.of_eval (fun r => measurable_pi_apply (Shao.retainedIndex s r))
  have hmark : P ((fun a : Shao.Path n => a i) ⁻¹' H) = nu H := by
    rw [← Measure.map_apply (measurable_pi_apply i) hH,
      (measurePreserving_eval (fun _ : Fin n => nu) i).map_eq]
  have hret : P ((fun a : Shao.Path n => Shao.retainedPath a s) ⁻¹' E) =
      (Measure.pi (fun _ : Fin s.card => nu)) E := by
    rw [← Measure.map_apply hM hE, hmap]
  have hh := hInd.measure_inter_preimage_eq_mul H E hH hE
  change P.real _ = _
  simp only [Measure.real_def]
  rw [hh, ENNReal.toReal_mul, hmark, hret]

private theorem ogt_rescaled_law (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (n : ℕ) (hn : 2 ≤ n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (t : ℝ) (ht : 2 ≤ t) (hsize : t ^ 6 ≤ (n : ℝ))
    (hcut : (n : ℝ) * (∫ z : ℝ, Shao.truncationF (t * z) ∂nu) ≤ 1)
    (s : ℝ) (hs : s = 1 ∨ s = -1) :
    let m : ℕ := n - 1
    let y : ℝ := Real.sqrt (t ^ 2 - 1)
    let c : ℝ := Real.sqrt ((n : ℝ) / (m : ℝ))
    let rho : Measure ℝ := Measure.map (fun z : ℝ => s * c * z) nu
    IsProbabilityMeasure rho ∧
      Integrable (fun z : ℝ => z ^ 2) rho ∧
      (∫ z : ℝ, z ∂rho) = 0 ∧
      (m : ℝ) * (∫ z : ℝ, z ^ 2 ∂rho) = 1 ∧
      0 < y ∧ y ^ 6 ≤ (m : ℝ) ∧
      (m : ℝ) * (∫ z : ℝ, Shao.truncationF (y * z) ∂rho) ≤ 1 := by
  let m : ℕ := n - 1
  let y : ℝ := Real.sqrt (t ^ 2 - 1)
  let c : ℝ := Real.sqrt ((n : ℝ) / (m : ℝ))
  let rho : Measure ℝ := Measure.map (fun z : ℝ => s * c * z) nu
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm : 0 < m := by dsimp [m]; omega
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hmcast : (m : ℝ) = (n : ℝ) - 1 := by dsimp [m]; rw [Nat.cast_sub (by omega)]; norm_num
  have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hsabs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hc : 0 < c := Real.sqrt_pos.mpr (div_pos hnr hmr)
  have hc2 : c ^ 2 = (n : ℝ) / (m : ℝ) := Real.sq_sqrt (div_nonneg hnr.le hmr.le)
  have htpos : 0 < t := by linarith
  have htsq : 4 ≤ t ^ 2 := by nlinarith
  have hy : 0 < y := Real.sqrt_pos.mpr (by nlinarith)
  have hy2 : y ^ 2 = t ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have ht4 : 1 ≤ t ^ 4 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
      (show 1 ≤ t by linarith) 4
  have ht2n : t ^ 2 ≤ (n : ℝ) := by
    have hh := mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht4)
    nlinarith only [hh, hsize]
  have hcy : y * c ≤ t := by
    have heq : (y * c) ^ 2 = (t ^ 2 - 1) * ((n : ℝ) / (m : ℝ)) := by
      rw [mul_pow, hy2, hc2]
    have hsq : (y * c) ^ 2 ≤ t ^ 2 := by
      rw [heq]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hmr).mpr
      nlinarith only [ht2n, hmcast]
    nlinarith only [hsq, htpos, mul_pos hy hc]
  have hysize : y ^ 6 ≤ (m : ℝ) := by
    have hp := mul_nonneg (sq_nonneg t) (show 0 ≤ t ^ 2 - 1 by linarith only [htsq])
    calc
      y ^ 6 = (t ^ 2 - 1) ^ 3 := by calc
        _ = (y ^ 2) ^ 3 := by ring
        _ = _ := by rw [hy2]
      _ ≤ t ^ 6 - 1 := by nlinarith only [hp]
      _ ≤ (m : ℝ) := by linarith only [hsize, hmcast]
  have hscale : Measurable (fun z : ℝ => s * c * z) := by fun_prop
  letI : IsProbabilityMeasure rho :=
    (Measure.isProbabilityMeasure_map_iff hscale.aemeasurable).mpr inferInstance
  have h1 : Integrable (fun z : ℝ => z) nu := by
    apply ((integrable_const (1 : ℝ)).add h2).mono' continuous_id.aestronglyMeasurable
    exact ae_of_all nu (fun z => by
      change ‖z‖ ≤ 1 + z ^ 2
      rw [Real.norm_eq_abs]
      nlinarith [sq_nonneg (|z| - 1), sq_abs z, abs_nonneg z])
  have hscaled2 : Integrable (fun z : ℝ => (s * c * z) ^ 2) nu := by
    simpa only [mul_pow] using h2.const_mul (s ^ 2 * c ^ 2)
  have hr2 : Integrable (fun z : ℝ => z ^ 2) rho :=
    (integrable_map_measure (continuous_id.pow 2).aestronglyMeasurable
      hscale.aemeasurable).mpr hscaled2
  have hrmean : (∫ z : ℝ, z ∂rho) = 0 := by
    change (∫ z : ℝ, z ∂Measure.map (fun z : ℝ => s * c * z) nu) = 0
    rw [integral_map (f := fun z : ℝ => z) hscale.aemeasurable continuous_id.aestronglyMeasurable,
      integral_const_mul, hmean, mul_zero]
  have hrnorm : (m : ℝ) * (∫ z : ℝ, z ^ 2 ∂rho) = 1 := by
    change (m : ℝ) * (∫ z : ℝ, z ^ 2 ∂Measure.map (fun z : ℝ => s * c * z) nu) = 1
    rw [integral_map (f := fun z : ℝ => z ^ 2) hscale.aemeasurable
      (continuous_id.pow 2).aestronglyMeasurable]
    simp_rw [mul_pow]
    rw [integral_const_mul, hs2, one_mul, hc2]
    calc
      (m : ℝ) * ((n : ℝ) / (m : ℝ) * ∫ z : ℝ, z ^ 2 ∂nu) =
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) := by field_simp
      _ = 1 := hnorm
  have hF := Shao.integrable_truncationF_mul nu h2 t
  have hFr := Shao.integrable_truncationF_mul rho hr2 y
  have hFscaled : Integrable (fun z : ℝ => Shao.truncationF (y * (s * c * z))) nu :=
    (integrable_map_measure
      (Shao.continuous_truncationF.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
      hscale.aemeasurable).mp hFr
  have hpoint (z : ℝ) : Shao.truncationF (y * (s * c * z)) ≤ Shao.truncationF (t * z) := by
    apply Shao.truncationF_mono_abs
    simp only [abs_mul, abs_of_pos hy, abs_of_pos hc, hsabs, one_mul, abs_of_pos htpos]
    have hh := mul_le_mul_of_nonneg_right hcy (abs_nonneg z)
    nlinarith only [hh]
  have hpay : (m : ℝ) * (∫ z : ℝ, Shao.truncationF (y * z) ∂rho) ≤ 1 := by
    change (m : ℝ) * (∫ z : ℝ, Shao.truncationF (y * z)
      ∂Measure.map (fun z : ℝ => s * c * z) nu) ≤ 1
    rw [integral_map (f := fun z : ℝ => Shao.truncationF (y * z)) hscale.aemeasurable
      (Shao.continuous_truncationF.comp (continuous_const.mul continuous_id)).aestronglyMeasurable]
    apply (mul_le_mul_of_nonneg_left (integral_mono hFscaled hF hpoint) hmr.le).trans
    apply le_trans (b := (n : ℝ) * ∫ z : ℝ, Shao.truncationF (t * z) ∂nu) _ hcut
    apply mul_le_mul_of_nonneg_right (by linarith only [hmcast])
    exact integral_nonneg (fun z => Shao.truncationF_nonneg _)
  exact ⟨inferInstance, hr2, hrmean, hrnorm, hy, hysize, hpay⟩

theorem original_marked_crossing_gaussian_upper :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ), IsProbabilityMeasure nu →
        ∀ (n : ℕ) (hn : 0 < n),
          Integrable (fun z : ℝ => z ^ 2) nu →
          (∫ z : ℝ, z ∂nu) = 0 →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
          ∀ t : ℝ, 0 < t → t ^ 6 ≤ (n : ℝ) →
            (n : ℝ) * (∫ z : ℝ, Shao.truncationF (t * z) ∂nu) ≤ 1 →
            ∀ h : ℝ, 0 < h → ∀ s : ℝ, (s = 1 ∨ s = -1) →
              let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
              P.real {a : Shao.Path n |
                t * Real.sqrt (Shao.energy a) ≤ Shao.upperMax (s • a) hn ∧
                  ∃ i : Fin n, h < |a i|} ≤
                C * (n : ℝ) * nu.real {z : ℝ | h < |z|} *
                  Shao.standardNormalTail t := by
  classical
  obtain ⟨C0, hC0, hcoarse⟩ := original_coarse_gaussian_upper
  let Cm : ℝ := 3 * Real.exp (1 / 2) * C0 + 1 / Shao.standardNormalTail 2
  have hT2 : 0 < Shao.standardNormalTail 2 := (Shao.standardNormalTail_basic.2.2.1 2).1
  have hCm : 0 < Cm := by dsimp [Cm]; positivity
  refine ⟨Cm, hCm, ?_⟩
  intro nu hnu n hn h2 hmean hnorm t ht hsize hcut h hh s hs
  letI : IsProbabilityMeasure nu := hnu
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let H : Set ℝ := {z : ℝ | h < |z|}
  let E : Set (Shao.Path n) := {a : Shao.Path n |
    t * Real.sqrt (Shao.energy a) ≤ Shao.upperMax (s • a) hn ∧ ∃ i : Fin n, h < |a i|}
  have hHm : MeasurableSet H := measurableSet_lt measurable_const continuous_abs.measurable
  have hH0 : 0 ≤ nu.real H := measureReal_nonneg
  have hT : 0 ≤ Shao.standardNormalTail t := (Shao.standardNormalTail_basic.2.2.1 t).1.le
  have hunion : P.real E ≤ ∑ i : Fin n, P.real
      {a : Shao.Path n | t * Real.sqrt (Shao.energy a) ≤ Shao.upperMax (s • a) hn ∧
        h < |a i|} := by
    apply (measureReal_mono (μ := P) (s₁ := E) (s₂ := ⋃ i : Fin n,
      {a : Shao.Path n | t * Real.sqrt (Shao.energy a) ≤ Shao.upperMax (s • a) hn ∧
        h < |a i|}) (by
          rintro a ⟨ha, i, hi⟩
          exact Set.mem_iUnion.mpr ⟨i, ha, hi⟩)).trans
    exact measureReal_iUnion_fintype_le _
  change P.real E ≤ Cm * (n : ℝ) * nu.real H * Shao.standardNormalTail t
  by_cases ht2 : 2 ≤ t
  · have hn64 : 64 ≤ n := (Shao.retainedSample_size_bounds n 0 t ht2 hsize
      (by simp; positivity)).1
    have hn2 : 2 ≤ n := by omega
    let m : ℕ := n - 1
    let y : ℝ := Real.sqrt (t ^ 2 - 1)
    let c : ℝ := Real.sqrt ((n : ℝ) / (m : ℝ))
    let rho : Measure ℝ := Measure.map (fun z : ℝ => s * c * z) nu
    have hm : 0 < m := by dsimp [m]; omega
    have hmr : (0 : ℝ) < m := by exact_mod_cast hm
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    have hc : 0 < c := Real.sqrt_pos.mpr (div_pos hnr hmr)
    have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
    have hscale : Measurable (fun z : ℝ => s * c * z) := by fun_prop
    obtain ⟨hrprob, hr2, hrmean, hrnorm, hy, hysize, hpay⟩ :=
      ogt_rescaled_law nu n hn2 h2 hmean hnorm t ht2 hsize hcut s hs
    change IsProbabilityMeasure rho at hrprob
    change Integrable (fun z : ℝ => z ^ 2) rho at hr2
    change (∫ z : ℝ, z ∂rho) = 0 at hrmean
    change (m : ℝ) * (∫ z : ℝ, z ^ 2 ∂rho) = 1 at hrnorm
    change 0 < y at hy
    change y ^ 6 ≤ (m : ℝ) at hysize
    change (m : ℝ) * (∫ z : ℝ, Shao.truncationF (y * z) ∂rho) ≤ 1 at hpay
    letI : IsProbabilityMeasure rho := hrprob
    have hrow (i : Fin n) : P.real
        {a : Shao.Path n | t * Real.sqrt (Shao.energy a) ≤ Shao.upperMax (s • a) hn ∧
          h < |a i|} ≤ nu.real H * (C0 * Shao.standardNormalTail y) := by
      let r : Finset (Fin n) := Finset.univ \ {i}
      have hri : i ∉ r := by simp [r]
      have hrcard : r.card = m := by
        simp only [r, m, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
          Fintype.card_fin, Finset.card_singleton]
      have hrpos : 0 < r.card := by omega
      let G : Shao.Path r.card → Shao.Path r.card := fun b j => s * c * b j
      let F : Set (Shao.Path r.card) := G ⁻¹' Shao.upperCrossing hrpos y
      have hGm : Measurable G := Measurable.of_eval
        (fun j => measurable_const.mul (measurable_pi_apply j))
      have hFm : MeasurableSet F := (Shao.measurableSet_upperCrossing hrpos y).preimage hGm
      have hGmap : Measure.map G (Measure.pi (fun _ : Fin r.card => nu)) =
          Measure.pi (fun _ : Fin r.card => rho) :=
        Measure.pi_map_pi (fun _ => hscale.aemeasurable)
      have hFprob : (Measure.pi (fun _ : Fin r.card => nu)).real F =
          (Measure.pi (fun _ : Fin r.card => rho)).real (Shao.upperCrossing hrpos y) := by
        rw [← hGmap]
        simp only [Measure.real_def]
        rw [Measure.map_apply hGm (Shao.measurableSet_upperCrossing hrpos y)]
      have hcb : (Measure.pi (fun _ : Fin r.card => rho)).real
          (Shao.upperCrossing hrpos y) ≤ C0 * Shao.standardNormalTail y :=
        hcoarse rho hrprob r.card hrpos hr2 hrmean (by simpa only [hrcard] using hrnorm)
          y hy (by simpa only [hrcard] using hysize) (by simpa only [hrcard] using hpay)
      have hsub : {a : Shao.Path n |
          t * Real.sqrt (Shao.energy a) ≤ Shao.upperMax (s • a) hn ∧ h < |a i|} ⊆
          (fun a : Shao.Path n => a i) ⁻¹' H ∩
            (fun a : Shao.Path n => Shao.retainedPath a r) ⁻¹' F := by
        rintro a ⟨ha, hai⟩
        refine ⟨hai, ?_⟩
        have has : (s • a) ∈ Shao.upperCrossing hn t := by
          change t * Real.sqrt (Shao.energy (s • a)) ≤ Shao.upperMax (s • a) hn
          simpa only [Shao.energy_smul, hs2, one_mul] using ha
        have hd := Shao.upperCrossing_retainedPath_of_deletion (s • a) {i} hn
          (by simp; omega) t ht
          (by simpa only [Finset.card_singleton, Nat.cast_one] using
            (show (1 : ℝ) < t ^ 2 by nlinarith only [ht2])) has
        let b : Shao.Path r.card := Shao.retainedPath (s • a) r
        have hb : b ∈ Shao.upperCrossing hrpos y := by
          simpa only [Finset.card_singleton, Nat.cast_one] using hd
        have heq : G (Shao.retainedPath a r) = c • b := by
          funext j
          dsimp [G, b, Shao.retainedPath]
          ring
        change G (Shao.retainedPath a r) ∈ Shao.upperCrossing hrpos y
        rw [heq]
        change y * Real.sqrt (Shao.energy (c • b)) ≤ Shao.upperMax (c • b) hrpos
        rw [Shao.energy_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le,
          Shao.upperMax_smul_of_nonneg c hc.le]
        change y * Real.sqrt (Shao.energy b) ≤ Shao.upperMax b hrpos at hb
        nlinarith only [mul_le_mul_of_nonneg_left hb hc.le]
      calc
        _ ≤ P.real ((fun a : Shao.Path n => a i) ⁻¹' H ∩
            (fun a : Shao.Path n => Shao.retainedPath a r) ⁻¹' F) := measureReal_mono hsub
        _ = nu.real H * (Measure.pi (fun _ : Fin r.card => nu)).real F :=
          ogt_mark_retained_factor nu n i r hri H hHm F hFm
        _ ≤ _ := by rw [hFprob]; exact mul_le_mul_of_nonneg_left hcb hH0
    have htail : Shao.standardNormalTail y ≤
        3 * Real.exp (1 / 2) * Shao.standardNormalTail t := by
      simpa only [Nat.cast_one] using Shao.standardNormalTail_deletion_comparison 1 t ht.le
        (by norm_num; nlinarith only [ht2])
    have hsum : P.real E ≤ (n : ℝ) * (nu.real H * (C0 * Shao.standardNormalTail y)) := by
      apply hunion.trans
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
        Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hrow i)
    have hscaleTail := mul_le_mul_of_nonneg_left htail
      (show 0 ≤ (n : ℝ) * nu.real H * C0 by positivity)
    have hcoeff : 3 * Real.exp (1 / 2) * C0 ≤ Cm := by
      have hh : 0 ≤ 1 / Shao.standardNormalTail 2 := by positivity
      dsimp only [Cm]
      linarith only [hh]
    have hfinal := mul_le_mul_of_nonneg_right hcoeff
      (show 0 ≤ (n : ℝ) * nu.real H * Shao.standardNormalTail t by positivity)
    nlinarith only [hsum, hscaleTail, hfinal]
  · have hrow (i : Fin n) : P.real
        {a : Shao.Path n | t * Real.sqrt (Shao.energy a) ≤ Shao.upperMax (s • a) hn ∧
          h < |a i|} ≤ nu.real H := by
      have hm : P.real ((fun a : Shao.Path n => a i) ⁻¹' H) = nu.real H := by
        simp only [Measure.real_def]
        rw [← Measure.map_apply (measurable_pi_apply i) hHm,
          (measurePreserving_eval (fun _ : Fin n => nu) i).map_eq]
      rw [← hm]
      exact measureReal_mono (fun _ ha => ha.2)
    have hsum : P.real E ≤ (n : ℝ) * nu.real H := by
      apply hunion.trans
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
        Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hrow i)
    have hmono := Shao.standardNormalTail_basic.1 (le_of_not_ge ht2)
    have hsmall : (1 : ℝ) ≤ (1 / Shao.standardNormalTail 2) * Shao.standardNormalTail t := by
      have hh : (1 : ℝ) ≤ Shao.standardNormalTail t / Shao.standardNormalTail 2 :=
        (le_div_iff₀ hT2).mpr (by simpa using hmono)
      convert hh using 1 <;> ring
    have hcoeff : 1 / Shao.standardNormalTail 2 ≤ Cm := by
      have hh : 0 ≤ 3 * Real.exp (1 / 2) * C0 := by positivity
      dsimp only [Cm]
      linarith only [hh]
    have hpaid : 1 ≤ Cm * Shao.standardNormalTail t :=
      hsmall.trans (mul_le_mul_of_nonneg_right hcoeff hT)
    have hfinal := mul_le_mul_of_nonneg_left hpaid
      (show 0 ≤ (n : ℝ) * nu.real H by positivity)
    nlinarith only [hsum, hfinal]

end Shao.Probability
