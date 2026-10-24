/- Original one-sided relative-error estimates from the frozen source-faithful assembly. -/
import Shao.Probability.SourceDesmoothing
import Shao.Probability.OriginalGaussianTail
import Shao.Probability.OriginalCDFPullback
import Shao.Probability.SourceFullYReflection
import Shao.Probability.SourceSmallBoundary
import Shao.Probability.SourceMomentDomain
import Shao.Probability.EndpointRelativeError
import Shao.Probability.FiniteIID
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Shao.Probability
open MeasureTheory ProbabilityTheory
open scoped BigOperators

private theorem osre_domain_guards
    (p : ℝ) (hp2 : 2 < p) (hp3 : p ≤ 3)
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 0 < n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (hp : Integrable (fun z : ℝ => Real.rpow |z| p) nu)
    (rhoStar : ℝ) (hrho : rhoStar ≤ 1 / 16) :
    let beta : ℝ := (n : ℝ) * (∫ z : ℝ, Real.rpow |z| p ∂nu)
    ∀ x : ℝ, 0 ≤ x →
      (x ≤ Real.rpow beta (-1 / p) ∨ Shao.truncationBudget nu n x ≤ rhoStar) →
      x ^ 6 ≤ (n : ℝ) ∧
        (n : ℝ) * (∫ z : ℝ, Shao.truncationF (x * z) ∂nu) ≤ 1 := by
  intro beta x hx hdomain
  rcases hdomain with hmoment | hbudget
  · exact (original_moment_domain_coarse_guards p hp2 hp3 nu n hn h2 hnorm hp).2.2.2.2 x hx hmoment
  · have hsize := Shao.truncationBudget_sample_size_lower nu n h2 hnorm x rhoStar hx hbudget hrho
    have hpow : x ^ 6 ≤ (1 + x) ^ 6 :=
      pow_le_pow_left₀ hx (by linarith) 6
    have hintegral : (∫ z : ℝ, Shao.truncationF (x * z) ∂nu) ≤
        ∫ z : ℝ, Shao.truncationF ((1 + x) * z) ∂nu :=
      integral_mono (Shao.integrable_truncationF_mul nu h2 x)
        (Shao.integrable_truncationF_mul nu h2 (1 + x))
        (fun z => Shao.truncationF_mono_scale x (1 + x) z hx (by linarith))
    refine ⟨hpow.trans (hsize.1.trans hsize.2), ?_⟩
    have hpay := mul_le_mul_of_nonneg_left hintegral (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    change (n : ℝ) * (∫ z : ℝ, Shao.truncationF (x * z) ∂nu) ≤
      Shao.truncationBudget nu n x at hpay
    exact hpay.trans (hbudget.trans (hrho.trans (by norm_num)))

private theorem osre_cdf_error_bounds {n : ℕ}
    (P : Measure (Shao.Path n)) [IsProbabilityMeasure P] :
    let F0 : ℝ → ℝ := fun u => P.real {v : Shao.Path n |
      0 < Shao.energy v ∧ Shao.maxWithZero v < u * Real.sqrt (Shao.energy v)}
    let G : ℝ → ℝ := fun u => if 0 < u then 1 - 2 * Shao.standardNormalTail u else 0
    let E : ℝ → ℝ := fun u => F0 u - G u
    (∀ u : ℝ, u ≤ 0 → E u = 0) ∧ (∀ u : ℝ, |E u| ≤ 1) := by
  classical
  intro F0 G E
  have hzeroF (u : ℝ) (hu : u ≤ 0) : F0 u = 0 := by
    have hset : {v : Shao.Path n | 0 < Shao.energy v ∧
        Shao.maxWithZero v < u * Real.sqrt (Shao.energy v)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro v hv
      have hwall := mul_nonpos_of_nonpos_of_nonneg hu (Real.sqrt_nonneg (Shao.energy v))
      exact (not_lt_of_ge ((Shao.maxWithZero_nonneg v).trans' hwall)) hv.2
    change P.real _ = 0
    rw [hset, measureReal_empty]
  have hzero (u : ℝ) (hu : u ≤ 0) : E u = 0 := by
    change F0 u - G u = 0
    rw [hzeroF u hu]
    simp [G, not_lt_of_ge hu]
  refine ⟨hzero, ?_⟩
  intro u
  by_cases hu : 0 < u
  · have htail := Shao.standardNormalTail_basic.1 hu.le
    rw [Shao.standardNormalTail_basic.2.1] at htail
    have ht0 := (Shao.standardNormalTail_basic.2.2.1 u).1.le
    have hF0 : 0 ≤ F0 u := measureReal_nonneg
    have hF1 : F0 u ≤ 1 := measureReal_le_one
    change |F0 u - G u| ≤ 1
    simp only [G, if_pos hu]
    exact abs_le.2 ⟨by linarith, by linarith⟩
  · rw [hzero u (le_of_not_gt hu)]
    norm_num

private theorem osre_nearby_control
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (H rhoStar M L x : ℝ) (hrho : 0 ≤ rhoStar) (hM : 0 ≤ M)
    (hL : 1600 ≤ L) (hx : 0 ≤ x)
    (hRx : Shao.truncationBudget nu n x ≤ rhoStar / 32)
    (E : ℝ → ℝ) (hzero : ∀ u : ℝ, u ≤ 0 → E u = 0)
    (hbound : ∀ u : ℝ, 0 ≤ u →
      (u ≤ H ∨ Shao.truncationBudget nu n u ≤ rhoStar) → 0 < u →
      |E u| ≤ M * (Shao.truncationBudget nu n u * Shao.standardNormalTail u)) :
    ∀ u : ℝ, |u - x| ≤ 1 / (1 + x) →
      |E u| ≤ L * M *
        (Shao.truncationBudget nu n x * Shao.standardNormalTail x) := by
  intro u hnear
  have hw : 0 ≤ Shao.truncationBudget nu n x * Shao.standardNormalTail x :=
    mul_nonneg (Shao.truncationBudget_nonneg nu n h2 x)
      (Shao.standardNormalTail_basic.2.2.1 x).1.le
  by_cases hu : 0 < u
  · have hRu := (Shao.truncationBudget_local_comparison nu n h2 x u hx hu.le
      (by simpa only [one_div] using hnear)).2
    have hRurho : Shao.truncationBudget nu n u ≤ rhoStar := by
      linarith only [hRu, hRx, hrho]
    have hE := hbound u hu.le (Or.inr hRurho) hu
    have hweight := (sourceWeight_nearby_bound nu n h2 x u L hx hu.le hnear hL).2
    calc
      _ ≤ M * (Shao.truncationBudget nu n u * Shao.standardNormalTail u) := hE
      _ ≤ M * (L * (Shao.truncationBudget nu n x * Shao.standardNormalTail x)) :=
        mul_le_mul_of_nonneg_left hweight hM
      _ = _ := by ring
  · rw [hzero u (le_of_not_gt hu), abs_zero]
    exact mul_nonneg (mul_nonneg (by linarith only [hL]) hM) hw

private theorem osre_signed_law_data
    (p : ℝ) (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (n : ℕ) (hn : 0 < n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (hp : Integrable (fun z : ℝ => Real.rpow |z| p) nu)
    (s : ℝ) (hs : s = 1 ∨ s = -1) :
    let nus : Measure ℝ := Measure.map (fun z : ℝ => s * z) nu
    IsProbabilityMeasure nus ∧
      Integrable (fun z : ℝ => z ^ 2) nus ∧
      (∫ z : ℝ, z ∂nus) = 0 ∧
      (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nus) = 1 ∧
      Integrable (fun z : ℝ => Real.rpow |z| p) nus ∧
      (∫ z : ℝ, Real.rpow |z| p ∂nus) = (∫ z : ℝ, Real.rpow |z| p ∂nu) ∧
      (∀ t : ℝ, Shao.truncationBudget nus n t = Shao.truncationBudget nu n t) ∧
      (∀ x : ℝ,
        (Measure.pi (fun _ : Fin n => nus)).real (Shao.upperCrossing hn x) =
        (Measure.pi (fun _ : Fin n => nu)).real {v : Shao.Path n |
          x * Real.sqrt (Shao.energy v) ≤ Shao.upperMax (s • v) hn}) := by
  classical
  intro nus
  have hm : Measurable (fun z : ℝ => s * z) := measurable_const.mul measurable_id
  have hsabs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hsq (z : ℝ) : (s * z) ^ 2 = z ^ 2 := by
    rcases hs with rfl | rfl <;> ring
  have habs (z : ℝ) : |s * z| = |z| := by rw [abs_mul, hsabs, one_mul]
  have hprob : IsProbabilityMeasure nus := by dsimp [nus]; infer_instance
  letI : IsProbabilityMeasure nus := hprob
  have h2s : Integrable (fun z : ℝ => z ^ 2) nus := by
    apply (integrable_map_measure (by fun_prop) hm.aemeasurable).2
    simpa only [Function.comp_def, hsq] using h2
  have hmeans : (∫ z : ℝ, z ∂nus) = 0 := by
    rw [show nus = Measure.map (fun z : ℝ => s * z) nu from rfl,
      integral_map hm.aemeasurable (f := fun z : ℝ => z) (by fun_prop),
      integral_const_mul, hmean, mul_zero]
  have hsecond : (∫ z : ℝ, z ^ 2 ∂nus) = ∫ z : ℝ, z ^ 2 ∂nu := by
    rw [show nus = Measure.map (fun z : ℝ => s * z) nu from rfl,
      integral_map hm.aemeasurable (by fun_prop)]
    simp only [hsq]
  have hpm : Measurable (fun z : ℝ => Real.rpow |z| p) := by
    simp only [Real.rpow_eq_pow]
    fun_prop
  have hps : Integrable (fun z : ℝ => Real.rpow |z| p) nus := by
    apply (integrable_map_measure hpm.aestronglyMeasurable hm.aemeasurable).2
    simpa only [Function.comp_def, habs] using hp
  have hpEq : (∫ z : ℝ, Real.rpow |z| p ∂nus) = ∫ z : ℝ, Real.rpow |z| p ∂nu := by
    rw [show nus = Measure.map (fun z : ℝ => s * z) nu from rfl,
      integral_map hm.aemeasurable hpm.aestronglyMeasurable]
    simp only [habs]
  refine ⟨hprob, h2s, hmeans, by rw [hsecond]; exact hnorm, hps, hpEq, ?_, ?_⟩
  · intro t
    unfold Shao.truncationBudget
    congr 1
    rw [show nus = Measure.map (fun z : ℝ => s * z) nu from rfl,
      integral_map hm.aemeasurable (f := fun z : ℝ => Shao.truncationF ((1 + t) * z))
        ((Shao.continuous_truncationF.comp
          (continuous_const.mul continuous_id)).aestronglyMeasurable)]
    apply integral_congr_ae
    filter_upwards [] with z
    rcases hs with rfl | rfl
    · simp only [one_mul]
    · convert Shao.truncationF_neg ((1 + t) * z) using 1 <;> congr 1 <;> ring
  · intro x
    let T : Shao.Path n → Shao.Path n := fun v => s • v
    have hTm : Measurable T :=
      Measurable.of_eval (fun i => measurable_const.mul (measurable_pi_apply i))
    have hmap : Measure.map T (Measure.pi (fun _ : Fin n => nu)) =
        Measure.pi (fun _ : Fin n => nus) :=
      Measure.pi_map_pi (fun _ : Fin n => hm.aemeasurable)
    have henergy (v : Shao.Path n) : Shao.energy (T v) = Shao.energy v := by
      change Shao.energy (s • v) = Shao.energy v
      rw [Shao.energy_smul]
      have hss : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
      rw [hss, one_mul]
    have hpre : T ⁻¹' Shao.upperCrossing hn x = {v : Shao.Path n |
        x * Real.sqrt (Shao.energy v) ≤ Shao.upperMax (s • v) hn} := by
      ext v
      change (x * Real.sqrt (Shao.energy (T v)) ≤ Shao.upperMax (T v) hn) ↔ _
      rw [henergy]
      rfl
    rw [← hmap]
    simp only [Measure.real_def, Measure.map_apply hTm
      (Shao.measurableSet_upperCrossing hn x), hpre]

private theorem osre_upper_from_endpoint
    (hEnd : ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 / 800 →
      ∃ Ce : ℝ, 0 ≤ Ce ∧
        ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ),
          Integrable (fun z : ℝ => z ^ 2) nu →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
          (∫ z : ℝ, z ∂nu) = 0 →
          ∀ x : ℝ, 0 < x →
            Shao.truncationBudget nu n x ≤ epsilon ^ 3 / 8 →
            let rho : Measure ℝ := ProbabilityTheory.cond nu
              {z : ℝ | |z| ≤ epsilon / (1 + x)}
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
            let G : ℝ → ℝ := fun t =>
              if 0 < t then 1 - 2 * Shao.standardNormalTail t else 0
            ∀ t : ℝ, |t - x| ≤ 1 / (1 + x) →
              |P.real {v : Shao.Path n |
                0 < Shao.energy v ∧
                  |Shao.prefixSum v n| < t * Real.sqrt (Shao.energy v)} - G t| ≤
                Ce * Shao.truncationBudget nu n x * Shao.standardNormalTail x) :
    ∃ rhoStar C : ℝ, 0 < rhoStar ∧ rhoStar ≤ 1 / 16 ∧ 0 < C ∧
      ∀ p : ℝ, 2 < p → p ≤ 3 →
        ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu]
          (n : ℕ) (hn : 0 < n),
          Integrable (fun z : ℝ => z ^ 2) nu →
          (∫ z : ℝ, z ∂nu) = 0 →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
          Integrable (fun z : ℝ => Real.rpow |z| p) nu →
          let beta : ℝ := (n : ℝ) * (∫ z : ℝ, Real.rpow |z| p ∂nu)
          ∀ x : ℝ, 0 ≤ x →
            (x ≤ Real.rpow beta (-1 / p) ∨
              Shao.truncationBudget nu n x ≤ rhoStar) →
            |(Measure.pi (fun _ : Fin n => nu)).real (Shao.upperCrossing hn x) /
                Shao.standardNormalTail x - 2| ≤
              C * Shao.truncationBudget nu n x := by
  classical
  let L : ℝ := 1600
  let L2 : ℝ := 16384
  let alpha : ℝ := 1 / 1024
  let epsilon0 : ℝ := min (1 / (64 * Real.sqrt L2)) (alpha / (8 * L))
  let t0 : ℝ := Real.exp (-(48 * alpha / epsilon0))
  let eta0 : ℝ := min (1 / 16)
    (min (Real.sqrt t0 / (2 * Real.sqrt L2))
      (min ((epsilon0 / 20480) ^ 2)
        (1 / (16384 * (1 + 3 / t0) * Real.exp (24 * epsilon0 / t0)))))
  let K : ℝ := 8 * (1 + L)
  let A0 : ℝ := 4 * K * L
  let epsilon : ℝ := min (epsilon0 / 2) (1 / (4 * (K + 1) * L))
  have he0 : 0 < epsilon0 := by norm_num [epsilon0, L2, alpha, L]
  have ht0 : 0 < t0 := Real.exp_pos _
  have heta0 : 0 < eta0 := by
    dsimp [eta0, L2]
    positivity
  have hcut := sourceGrowingCutoff_exact_and_bounded_compatible
  change epsilon0 = (1 / 13107200 : ℝ) ∧ epsilon = (1 / 81977600 : ℝ) ∧
    0 < epsilon ∧ epsilon ≤ (1 / 16384 : ℝ) ∧ epsilon ≤ (1 / 800 : ℝ) at hcut
  obtain ⟨_, _, he, _, he800⟩ := hcut
  have hegeom : epsilon ≤ 1 / (4 * (8 * (1 + L) + 1) * L) := min_le_right _ _
  have hK : 1 < K := by norm_num [K, L]
  have hA : 0 < A0 := by norm_num [A0, K, L]
  let rhoStar : ℝ := min (epsilon ^ 3 / 64)
    (min (epsilon ^ 2 * eta0 / 320) (1 / (64 * K * L)))
  let eta : ℝ := rhoStar / 32
  have hrho : 0 < rhoStar := by dsimp [rhoStar, K, L]; positivity
  have hrhoCube : rhoStar ≤ epsilon ^ 3 / 64 := min_le_left _ _
  have hrhoEta : rhoStar ≤ epsilon ^ 2 * eta0 / 320 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hrhoKL : rhoStar ≤ 1 / (64 * K * L) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hrho16 : rhoStar ≤ 1 / 16 := by
    norm_num [K, L] at hrhoKL
    linarith only [hrhoKL]
  have heta : 0 < eta := div_pos hrho (by norm_num)
  have hetaCube : eta ≤ epsilon ^ 3 / 8 := by
    dsimp [eta]
    nlinarith only [hrhoCube, pow_pos he 3]
  have hetaEta : eta ≤ epsilon ^ 2 * eta0 / 40 := by
    dsimp [eta]
    nlinarith only [hrhoEta, mul_pos (sq_pos_of_pos he) heta0]
  have hAeta : A0 * eta ≤ 1 / 512 := by
    norm_num [K, L] at hrhoKL
    dsimp [A0, K, L, eta]
    linarith only [hrhoKL]
  obtain ⟨Cc, hCc, Hcoarse⟩ := original_coarse_gaussian_upper
  obtain ⟨Cp, hCp, HPB⟩ := sourceTruncation_original_max_cdf_pullback
  obtain ⟨Cs, hCs, HSM⟩ := sourceTruncation_full_y_smoothed_probability_comparison
  obtain ⟨Cz, hCz, Hzero⟩ := original_maximum_near_zero_cdf
  obtain ⟨Ce, hCe, HEND⟩ := hEnd epsilon he he800
  let D : ℝ := 32768 * Real.sqrt (2 * Real.pi) + 1 / Shao.standardNormalTail 2 + 1600
  let c : ℝ := 2 * Real.exp 2
  let B : ℝ := (4 / 3 : ℝ) * Cp / epsilon ^ 3
  let C1 : ℝ := (Cc + 2) / eta
  let C2 : ℝ := Cz * (A0 + 1) / Shao.standardNormalTail 1
  let C3 : ℝ := K / (K - 1) * (B + Ce + Cs + c * (K + 2) * D)
  let Cb : ℝ := max C1 (max C2 C3)
  let C : ℝ := max (4 * Cb / 3) (2 * Cz)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC1 : 0 < C1 := by dsimp [C1]; positivity
  have hCbpos : 0 < Cb := hC1.trans_le (le_max_left _ _)
  have hCb : 0 ≤ Cb := hC1.le.trans (le_max_left _ _)
  have hC : 0 < C := (by positivity : 0 < 4 * Cb / 3).trans_le (le_max_left _ _)
  refine ⟨rhoStar, C, hrho, hrho16, hC, ?_⟩
  intro p hp2 hp3 nu hnu n hn h2 hmean hnorm hp beta x hx hdomain
  letI : IsProbabilityMeasure nu := hnu
  let H : ℝ := Real.rpow beta (-1 / p)
  let I : Set ℝ := {t | 0 ≤ t ∧ (t ≤ H ∨ Shao.truncationBudget nu n t ≤ rhoStar)}
  let P0 : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let G : ℝ → ℝ := fun u => if 0 < u then 1 - 2 * Shao.standardNormalTail u else 0
  let F0 : ℝ → ℝ := fun u => P0.real {v : Shao.Path n |
    0 < Shao.energy v ∧ Shao.maxWithZero v < u * Real.sqrt (Shao.energy v)}
  let E : ℝ → ℝ := fun u => F0 u - G u
  let w : ℝ → ℝ := fun u => Shao.truncationBudget nu n u * Shao.standardNormalTail u
  let ratios : Set ℝ := {v | ∃ t : ℝ, t ∈ I ∧ 0 < t ∧ v = |E t| / w t}
  let M : ℝ := sSup (Set.insert 0 ratios)
  have hH : 0 ≤ H := (original_moment_domain_coarse_guards p hp2 hp3 nu n hn h2 hnorm hp).2.2.1.le
  obtain ⟨hI, _, hwc, hwp, _⟩ := sourceWeight_enlarged_domain_compact nu n h2 hnorm H rhoStar hH hrho
  have hEb := osre_cdf_error_bounds P0
  change (∀ u : ℝ, u ≤ 0 → E u = 0) ∧ (∀ u : ℝ, |E u| ≤ 1) at hEb
  have hsup := sourceWeight_compact_supremum_absorption I hI E w hwc hwp (fun t _ => hEb.2 t)
  change BddAbove ratios ∧ BddAbove (Set.insert 0 ratios) ∧ 0 ≤ M ∧
    (∀ t : ℝ, t ∈ I → 0 < t → |E t| ≤ M * w t) ∧
    (ratios.Nonempty → M = sSup ratios) ∧
    (∀ C : ℝ, 0 ≤ C →
      (∀ t : ℝ, t ∈ I → 0 < t → |E t| / w t ≤ C + M / 4) → M ≤ 4 * C / 3) at hsup
  have hM : 0 ≤ M := hsup.2.2.1
  have hpoint := hsup.2.2.2.1
  have hratio : ∀ t : ℝ, t ∈ I → 0 < t → |E t| / w t ≤ Cb + M / 4 := by
    intro t ht htp
    let R : ℝ := Shao.truncationBudget nu n t
    let r0 : ℝ := Shao.truncationBudget nu n 0
    have hR0 : 0 ≤ R := Shao.truncationBudget_nonneg nu n h2 t
    have hr0 : 0 ≤ r0 := Shao.truncationBudget_nonneg nu n h2 0
    have hr0R : r0 ≤ R := Shao.truncationBudget_mono nu n h2 0 t (by norm_num) htp.le
    have hT : 0 < Shao.standardNormalTail t := (Shao.standardNormalTail_basic.2.2.1 t).1
    have hwt : 0 < w t := hwp t ht
    by_cases hlarge : eta ≤ R
    · have hguards := osre_domain_guards p hp2 hp3 nu n hn h2 hnorm hp rhoStar hrho16 t ht.1 ht.2
      have hcoarse := Hcoarse nu hnu n hn h2 hmean hnorm t htp hguards.1 hguards.2
      change P0.real (Shao.upperCrossing hn t) ≤ Cc * Shao.standardNormalTail t at hcoarse
      have hid : E t = 2 * Shao.standardNormalTail t - P0.real (Shao.upperCrossing hn t) := by
        simpa only [E, G, ite_eq_left htp] using
          (sourcePositiveCDF_weak_tail_error_identity hn P0 t htp).1
      have hprob0 : 0 ≤ P0.real (Shao.upperCrossing hn t) := measureReal_nonneg
      have herror : |E t| ≤ (Cc + 2) * Shao.standardNormalTail t := by
        rw [hid]
        apply abs_le.2
        constructor <;> nlinarith only [hcoarse, hprob0, hT.le, mul_nonneg hCc.le hT.le]
      have hpay : |E t| / w t ≤ C1 := by
        apply (div_le_iff₀ hwt).2
        apply herror.trans
        have hh := mul_le_mul_of_nonneg_left hlarge
          (show 0 ≤ (Cc + 2) / eta from (div_pos (by linarith only [hCc]) heta).le)
        have heq : (Cc + 2) / eta * eta = Cc + 2 := div_mul_cancel₀ _ heta.ne'
        rw [heq] at hh
        change (Cc + 2) * Shao.standardNormalTail t ≤ C1 * (R * Shao.standardNormalTail t)
        dsimp [C1]
        nlinarith only [mul_le_mul_of_nonneg_right hh hT.le]
      exact hpay.trans (by linarith only [le_max_left C1 (max C2 C3), hM])
    · have hsmall : R < eta := lt_of_not_ge hlarge
      by_cases hnear : t ≤ A0 * r0
      · have htHalf : t ≤ 1 / 2 := by
          have hh := mul_le_mul_of_nonneg_left (hr0R.trans hsmall.le) hA.le
          linarith only [hnear, hh, hAeta]
        have herr := (Hzero nu n hn h2 hmean hnorm).2 t htp.le htHalf
        change |E t| ≤ Cz * (t + r0) at herr
        have htail1 : Shao.standardNormalTail 1 ≤ Shao.standardNormalTail t :=
          Shao.standardNormalTail_basic.1 (by linarith only [htHalf])
        have hT1 : 0 < Shao.standardNormalTail 1 := (Shao.standardNormalTail_basic.2.2.1 1).1
        have hpay : |E t| / w t ≤ C2 := by
          apply (div_le_iff₀ hwt).2
          have hfirst : |E t| ≤ Cz * (A0 + 1) * R := by
            have hh := mul_le_mul_of_nonneg_left hr0R (show 0 ≤ A0 + 1 by positivity)
            nlinarith only [herr, hnear, mul_le_mul_of_nonneg_left hh hCz.le,
              mul_le_mul_of_nonneg_left hnear hCz.le]
          apply hfirst.trans
          have hh := (div_le_iff₀ hT1).1 (le_refl (Cz * (A0 + 1) / Shao.standardNormalTail 1))
          have heq : C2 * Shao.standardNormalTail 1 = Cz * (A0 + 1) := div_mul_cancel₀ _ hT1.ne'
          have hC2 : 0 ≤ C2 := by dsimp [C2]; positivity
          have htail := mul_le_mul_of_nonneg_left htail1 hC2
          rw [heq] at htail
          change Cz * (A0 + 1) * R ≤ C2 * (R * Shao.standardNormalTail t)
          nlinarith only [mul_le_mul_of_nonneg_right htail hR0]
        have hC2b : C2 ≤ Cb := (le_max_left _ _).trans (le_max_right _ _)
        exact hpay.trans (by linarith only [hC2b, hM])
      · have hxD3 : 4 * (8 * (1 + L)) * L * Shao.truncationBudget nu n 0 < t :=
          lt_of_not_ge hnear
        have hcube : Shao.truncationBudget nu n t ≤ epsilon ^ 3 / 8 := hsmall.le.trans hetaCube
        have hetaGuard : Shao.truncationBudget nu n t ≤ epsilon ^ 2 * eta0 / 40 := hsmall.le.trans hetaEta
        have hpb := HPB nu n hn h2 hmean hnorm t epsilon htp.le he he800 hcube
        have hend := HEND nu n h2 hnorm hmean t htp hcube
        have hsm := HSM nu hnu n h2 hnorm hmean t htp.le hcube hetaGuard
        have hd := sourceTruncation_weighted_desmoothing_from_interfaces nu n h2 hnorm hmean
          t epsilon eta0 L htp he heta0 (le_refl L) he800 hegeom hcube hetaGuard hxD3
        have hdesmooth := hd.2.2.2.2.2.2.2.2.2.2.2
        have hpbBound : ∀ u : ℝ, |u - t| ≤ 1 / (1 + t) →
            |(Measure.pi (fun _ : Fin n => cond nu {z : ℝ | |z| ≤ epsilon / (1 + t)})).real
              {v : Shao.Path n | 0 < Shao.energy v ∧
                Shao.maxWithZero v < u * Real.sqrt (Shao.energy v)} - G u -
              E u / P0.real {v : Shao.Path n | ∀ j : Fin n, |v j| ≤ epsilon / (1 + t)}| ≤
                B * w t := by
          intro u hu
          exact (hpb.2.2.2.2.2.2.2 u hu).2.2.2.2.1
        have hnearE : ∀ u : ℝ, |u - t| ≤ 1 / (1 + t) → |E u| ≤ L * M * w t :=
          osre_nearby_control nu n h2 H rhoStar M L t hrho.le hM (le_refl L) htp.le
            hsmall.le E hEb.1 (fun u hu hdom hup => hpoint u ⟨hu, hdom⟩ hup)
        have hsmBound := fun y hy hyl => (hsm.2.2.2 y hy hyl).2.2.2.2.2.2
        have hdBound := (hdesmooth B Ce Cs M hB hCe hCs.le hM hpbBound
          (fun u hu => by simpa only [mul_assoc] using hend u hu)
          hsmBound hnearE).2
        have hC3b : C3 ≤ Cb := (le_max_right _ _).trans (le_max_right _ _)
        apply hdBound.trans
        change C3 + M / 4 ≤ Cb + M / 4
        linarith only [hC3b]
  have hMbound : M ≤ 4 * Cb / 3 := hsup.2.2.2.2.2 Cb hCb hratio
  by_cases hxp : 0 < x
  · have hxI : x ∈ I := ⟨hx, hdomain⟩
    have herr := hpoint x hxI hxp
    have hid : |E x| / Shao.standardNormalTail x =
        |P0.real (Shao.upperCrossing hn x) / Shao.standardNormalTail x - 2| := by
      simpa only [E, G, ite_eq_left hxp] using
        (sourcePositiveCDF_weak_tail_error_identity hn P0 x hxp).2
    rw [← hid]
    have hT := (Shao.standardNormalTail_basic.2.2.1 x).1
    have hR := Shao.truncationBudget_nonneg nu n h2 x
    have hh : |E x| ≤ C * Shao.truncationBudget nu n x * Shao.standardNormalTail x := by
      apply herr.trans
      have hMC : M ≤ C := hMbound.trans (le_max_left _ _)
      have hweight : 0 ≤ w x := (hwp x hxI).le
      simpa only [w, mul_assoc] using mul_le_mul_of_nonneg_right hMC hweight
    exact (div_le_iff₀ hT).2 hh
  · have hxzero : x = 0 := le_antisymm (le_of_not_gt hxp) hx
    subst x
    have hzero := (Hzero nu n hn h2 hmean hnorm).1
    have heq : {v : Shao.Path n | Shao.upperMax v hn < 0} = (Shao.upperCrossing hn 0)ᶜ := by
      ext v
      simp only [Shao.upperCrossing, zero_mul, Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    have hprob : P0.real {v : Shao.Path n | Shao.upperMax v hn < 0} =
        1 - P0.real (Shao.upperCrossing hn 0) := by
      rw [heq, measureReal_compl (Shao.measurableSet_upperCrossing hn 0), probReal_univ]
    have hnon : 0 ≤ P0.real {v : Shao.Path n | Shao.upperMax v hn < 0} := measureReal_nonneg
    have herr : |P0.real (Shao.upperCrossing hn 0) / Shao.standardNormalTail 0 - 2| =
        2 * P0.real {v : Shao.Path n | Shao.upperMax v hn < 0} := by
      rw [Shao.standardNormalTail_basic.2.1]
      have hexp : P0.real (Shao.upperCrossing hn 0) / (1 / 2 : ℝ) - 2 =
          -2 * P0.real {v : Shao.Path n | Shao.upperMax v hn < 0} := by linarith only [hprob]
      rw [hexp, abs_mul, abs_of_nonneg hnon]
      norm_num
    rw [herr]
    have hCzC : 2 * Cz ≤ C := le_max_right _ _
    have hR := Shao.truncationBudget_nonneg nu n h2 0
    nlinarith only [hzero, mul_le_mul_of_nonneg_right hCzC hR]


private theorem osre_signed_from_upper (rhoStar C : ℝ)
    (hUpper : ∀ p : ℝ, 2 < p → p ≤ 3 →
        ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu]
          (n : ℕ) (hn : 0 < n),
          Integrable (fun z : ℝ => z ^ 2) nu →
          (∫ z : ℝ, z ∂nu) = 0 →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
          Integrable (fun z : ℝ => Real.rpow |z| p) nu →
          let beta : ℝ := (n : ℝ) * (∫ z : ℝ, Real.rpow |z| p ∂nu)
          ∀ x : ℝ, 0 ≤ x →
            (x ≤ Real.rpow beta (-1 / p) ∨
              Shao.truncationBudget nu n x ≤ rhoStar) →
            |(Measure.pi (fun _ : Fin n => nu)).real (Shao.upperCrossing hn x) /
                Shao.standardNormalTail x - 2| ≤
              C * Shao.truncationBudget nu n x) :
    ∀ p : ℝ, 2 < p → p ≤ 3 →
        ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu]
          (n : ℕ) (hn : 0 < n),
          Integrable (fun z : ℝ => z ^ 2) nu →
          (∫ z : ℝ, z ∂nu) = 0 →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
          Integrable (fun z : ℝ => Real.rpow |z| p) nu →
          let beta : ℝ := (n : ℝ) * (∫ z : ℝ, Real.rpow |z| p ∂nu)
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
          ∀ x : ℝ, 0 ≤ x →
            (x ≤ Real.rpow beta (-1 / p) ∨
              Shao.truncationBudget nu n x ≤ rhoStar) →
            ∀ s : ℝ, (s = 1 ∨ s = -1) →
              |P.real {v : Shao.Path n |
                x * Real.sqrt (Shao.energy v) ≤ Shao.upperMax (s • v) hn} /
                  Shao.standardNormalTail x - 2| ≤
                C * Shao.truncationBudget nu n x := by
  classical
  intro p hp2 hp3 nu hnu n hn h2 hmean hnorm hp beta P x hx hdomain s hs
  letI : IsProbabilityMeasure nu := hnu
  let nus : Measure ℝ := Measure.map (fun z : ℝ => s * z) nu
  obtain ⟨hprob, h2s, hmeans, hnorms, hps, hpEq, hR, hevent⟩ :=
    osre_signed_law_data p nu n hn h2 hmean hnorm hp s hs
  letI : IsProbabilityMeasure nus := hprob
  have hdomain' : x ≤ Real.rpow
      ((n : ℝ) * (∫ z : ℝ, Real.rpow |z| p ∂nus)) (-1 / p) ∨
      Shao.truncationBudget nus n x ≤ rhoStar := by
    rw [hpEq, hR x]
    exact hdomain
  have hbound := hUpper p hp2 hp3 nus n hn h2s hmeans hnorms hps x hx hdomain'
  rw [hR x, hevent x] at hbound
  exact hbound

private theorem osre_raw_adapter (rhoStar C : ℝ)
    (hNorm : ∀ p : ℝ, 2 < p → p ≤ 3 →
        ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu]
          (n : ℕ) (hn : 0 < n),
          Integrable (fun z : ℝ => z ^ 2) nu →
          (∫ z : ℝ, z ∂nu) = 0 →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
          Integrable (fun z : ℝ => Real.rpow |z| p) nu →
          let beta : ℝ := (n : ℝ) * (∫ z : ℝ, Real.rpow |z| p ∂nu)
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
          ∀ x : ℝ, 0 ≤ x →
            (x ≤ Real.rpow beta (-1 / p) ∨
              Shao.truncationBudget nu n x ≤ rhoStar) →
            ∀ s : ℝ, (s = 1 ∨ s = -1) →
              |P.real {v : Shao.Path n |
                x * Real.sqrt (Shao.energy v) ≤ Shao.upperMax (s • v) hn} /
                  Shao.standardNormalTail x - 2| ≤
                C * Shao.truncationBudget nu n x) :
    ∀ p : ℝ, 2 < p → p ≤ 3 →
        ∀ (mu : Measure ℝ) [IsProbabilityMeasure mu]
          (n : ℕ) (hn : 0 < n),
          Integrable (fun z : ℝ => z ^ 2) mu →
          (∫ z : ℝ, z ∂mu) = 0 →
          (0 < ∫ z : ℝ, z ^ 2 ∂mu) →
          Integrable (fun z : ℝ => Real.rpow |z| p) mu →
          let sigma : ℝ := Real.sqrt (∫ z : ℝ, z ^ 2 ∂mu)
          let nu : Measure ℝ := Measure.map
            (fun z : ℝ => z / (sigma * Real.sqrt (n : ℝ))) mu
          let beta : ℝ := (∫ z : ℝ, Real.rpow |z| p ∂mu) /
            (Real.rpow sigma p * Real.rpow (n : ℝ) ((p - 2) / 2))
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
          ∀ x : ℝ, 0 ≤ x →
            (x ≤ Real.rpow beta (-1 / p) ∨
              Shao.truncationBudget nu n x ≤ rhoStar) →
            ∀ s : ℝ, (s = 1 ∨ s = -1) →
              |P.real {v : Shao.Path n |
                x * Real.sqrt (Shao.energy v) ≤ Shao.upperMax (s • v) hn} /
                  Shao.standardNormalTail x - 2| ≤
                C * Shao.truncationBudget nu n x := by
  classical
  intro p hp2 hp3 mu hmu n hn h2 hmean hsecond hp
  letI : IsProbabilityMeasure mu := hmu
  intro sigma nu beta P x hx hdomain s hs
  have hdata := original_raw_normalization_data p hp2 hp3 mu n hn h2 hmean hsecond hp
  change 0 < sigma ∧ IsProbabilityMeasure nu ∧
    Integrable (fun z : ℝ => z ^ 2) nu ∧
    (∫ z : ℝ, z ∂nu) = 0 ∧
    (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 ∧
    Integrable (fun z : ℝ => Real.rpow |z| p) nu ∧
    (∫ z : ℝ, Real.rpow |z| p ∂nu) =
      (∫ z : ℝ, Real.rpow |z| p ∂mu) /
        (Real.rpow sigma p * Real.rpow (n : ℝ) (p / 2)) ∧
    0 < beta ∧ beta = (n : ℝ) * (∫ z : ℝ, Real.rpow |z| p ∂nu) ∧
    Measure.map (fun a : Shao.Path n =>
      (fun i : Fin n => a i / (sigma * Real.sqrt (n : ℝ)))) P =
      Measure.pi (fun _ : Fin n => nu) ∧
    (∀ x s : ℝ, (s = 1 ∨ s = -1) →
      (Measure.pi (fun _ : Fin n => nu)).real {v : Shao.Path n |
        x * Real.sqrt (Shao.energy v) ≤ Shao.upperMax (s • v) hn} =
      P.real {v : Shao.Path n |
        x * Real.sqrt (Shao.energy v) ≤ Shao.upperMax (s • v) hn}) at hdata
  obtain ⟨_, hnu, h2nu, hmeannu, hnorm, hpnu, _, _, hbeta, _, hevent⟩ := hdata
  letI : IsProbabilityMeasure nu := hnu
  have hdomain' : x ≤ Real.rpow
      ((n : ℝ) * (∫ z : ℝ, Real.rpow |z| p ∂nu)) (-1 / p) ∨
      Shao.truncationBudget nu n x ≤ rhoStar := by
    simpa only [← hbeta] using hdomain
  have hbound := hNorm p hp2 hp3 nu n hn h2nu hmeannu hnorm hpnu x hx hdomain' s hs
  change |(Measure.pi (fun _ : Fin n => nu)).real {v : Shao.Path n |
    x * Real.sqrt (Shao.energy v) ≤ Shao.upperMax (s • v) hn} /
      Shao.standardNormalTail x - 2| ≤ C * Shao.truncationBudget nu n x at hbound
  rw [hevent x s hs] at hbound
  exact hbound

private theorem osre_iid_adapter (rhoStar C : ℝ)
    (hRaw : ∀ p : ℝ, 2 < p → p ≤ 3 →
        ∀ (mu : Measure ℝ) [IsProbabilityMeasure mu]
          (n : ℕ) (hn : 0 < n),
          Integrable (fun z : ℝ => z ^ 2) mu →
          (∫ z : ℝ, z ∂mu) = 0 →
          (0 < ∫ z : ℝ, z ^ 2 ∂mu) →
          Integrable (fun z : ℝ => Real.rpow |z| p) mu →
          let sigma : ℝ := Real.sqrt (∫ z : ℝ, z ^ 2 ∂mu)
          let nu : Measure ℝ := Measure.map
            (fun z : ℝ => z / (sigma * Real.sqrt (n : ℝ))) mu
          let beta : ℝ := (∫ z : ℝ, Real.rpow |z| p ∂mu) /
            (Real.rpow sigma p * Real.rpow (n : ℝ) ((p - 2) / 2))
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
          ∀ x : ℝ, 0 ≤ x →
            (x ≤ Real.rpow beta (-1 / p) ∨
              Shao.truncationBudget nu n x ≤ rhoStar) →
            ∀ s : ℝ, (s = 1 ∨ s = -1) →
              |P.real {v : Shao.Path n |
                x * Real.sqrt (Shao.energy v) ≤ Shao.upperMax (s • v) hn} /
                  Shao.standardNormalTail x - 2| ≤
                C * Shao.truncationBudget nu n x) :
    ∀ p : ℝ, 2 < p → p ≤ 3 →
        ∀ {Ω : Type*} [MeasurableSpace Ω]
          (P : Measure Ω) [IsProbabilityMeasure P]
          (n : ℕ) (hn : 0 < n)
          (X : Fin n → Ω → ℝ),
          (∀ i : Fin n, Measurable (X i)) →
          iIndepFun X P →
          (∀ i : Fin n, IdentDistrib (X i) (X ⟨0, hn⟩) P P) →
          let Y : Ω → ℝ := X ⟨0, hn⟩
          Integrable (fun omega : Ω => (Y omega) ^ 2) P →
          (∫ omega : Ω, Y omega ∂P) = 0 →
          (0 < ∫ omega : Ω, (Y omega) ^ 2 ∂P) →
          Integrable (fun omega : Ω => Real.rpow |Y omega| p) P →
          let sigma : ℝ := Real.sqrt (∫ omega : Ω, (Y omega) ^ 2 ∂P)
          let nu : Measure ℝ := Measure.map
            (fun omega : Ω => Y omega / (sigma * Real.sqrt (n : ℝ))) P
          let beta : ℝ := (∫ omega : Ω, Real.rpow |Y omega| p ∂P) /
            (Real.rpow sigma p * Real.rpow (n : ℝ) ((p - 2) / 2))
          ∀ x : ℝ, 0 ≤ x →
            (x ≤ Real.rpow beta (-1 / p) ∨
              Shao.truncationBudget nu n x ≤ rhoStar) →
            ∀ s : ℝ, (s = 1 ∨ s = -1) →
              |P.real {omega : Ω |
                x * Real.sqrt (Shao.energy (samplePath X omega)) ≤
                  Shao.upperMax (s • samplePath X omega) hn} /
                    Shao.standardNormalTail x - 2| ≤
                C * Shao.truncationBudget nu n x := by
  classical
  intro p hp2 hp3 Ω hΩ P hP n hn X hX hIndep hLaw Y h2 hmean hsecond hp
  letI : IsProbabilityMeasure P := hP
  intro sigma nu beta x hx hdomain s hs
  let mu : Measure ℝ := Measure.map Y P
  have hYm : Measurable Y := hX ⟨0, hn⟩
  letI : IsProbabilityMeasure mu := by dsimp [mu]; infer_instance
  have h2mu : Integrable (fun z : ℝ => z ^ 2) mu :=
    (integrable_map_measure (by fun_prop) hYm.aemeasurable).2 h2
  have hpm : Measurable (fun z : ℝ => Real.rpow |z| p) := by
    simp only [Real.rpow_eq_pow]
    fun_prop
  have hpmu : Integrable (fun z : ℝ => Real.rpow |z| p) mu :=
    (integrable_map_measure hpm.aestronglyMeasurable hYm.aemeasurable).2 hp
  have hfirst : (∫ z : ℝ, z ∂mu) = ∫ omega : Ω, Y omega ∂P :=
    integral_map hYm.aemeasurable measurable_id.aestronglyMeasurable
  have hsecondEq : (∫ z : ℝ, z ^ 2 ∂mu) = ∫ omega : Ω, (Y omega) ^ 2 ∂P :=
    integral_map hYm.aemeasurable (by fun_prop)
  have hpEq : (∫ z : ℝ, Real.rpow |z| p ∂mu) =
      ∫ omega : Ω, Real.rpow |Y omega| p ∂P :=
    integral_map hYm.aemeasurable hpm.aestronglyMeasurable
  have hmeannu : (∫ z : ℝ, z ∂mu) = 0 := hfirst.trans hmean
  have hsecondmu : 0 < ∫ z : ℝ, z ^ 2 ∂mu := hsecondEq ▸ hsecond
  have hsigma : Real.sqrt (∫ z : ℝ, z ^ 2 ∂mu) = sigma := congrArg Real.sqrt hsecondEq
  have hnu : Measure.map
      (fun z : ℝ => z / (sigma * Real.sqrt (n : ℝ))) mu = nu := by
    dsimp [mu, nu]
    rw [Measure.map_map (by fun_prop) hYm]
    rfl
  have hbeta : (∫ z : ℝ, Real.rpow |z| p ∂mu) /
      (Real.rpow (Real.sqrt (∫ z : ℝ, z ^ 2 ∂mu)) p *
        Real.rpow (n : ℝ) ((p - 2) / 2)) = beta := by
    rw [hpEq, hsigma]
  have hdomain' : x ≤ Real.rpow
      ((∫ z : ℝ, Real.rpow |z| p ∂mu) /
        (Real.rpow (Real.sqrt (∫ z : ℝ, z ^ 2 ∂mu)) p *
          Real.rpow (n : ℝ) ((p - 2) / 2))) (-1 / p) ∨
      Shao.truncationBudget
        (Measure.map (fun z : ℝ => z /
          (Real.sqrt (∫ z : ℝ, z ^ 2 ∂mu) * Real.sqrt (n : ℝ))) mu) n x ≤ rhoStar := by
    rw [hbeta, hsigma, hnu]
    exact hdomain
  have hbound := hRaw p hp2 hp3 mu n hn h2mu hmeannu hsecondmu hpmu x hx hdomain' s hs
  simp only [hsigma, hnu] at hbound
  have hcoord (i : Fin n) : IdentDistrib (X i) (id : ℝ → ℝ) P mu := by
    refine ⟨(hX i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa only [Measure.map_id] using (hLaw i).map_eq
  have hmap := iid_samplePath_map_eq_pi hX hIndep hcoord
  have hsm : Measurable (fun v : Shao.Path n => s • v) :=
    Measurable.of_eval (fun i => measurable_const.mul (measurable_pi_apply i))
  have hA : MeasurableSet {v : Shao.Path n |
      x * Real.sqrt (Shao.energy v) ≤ Shao.upperMax (s • v) hn} :=
    measurableSet_le (Shao.measurable_energyWall x) ((Shao.measurable_upperMax hn).comp hsm)
  have hevent : (Measure.pi (fun _ : Fin n => mu)).real {v : Shao.Path n |
      x * Real.sqrt (Shao.energy v) ≤ Shao.upperMax (s • v) hn} =
      P.real {omega : Ω | x * Real.sqrt (Shao.energy (samplePath X omega)) ≤
        Shao.upperMax (s • samplePath X omega) hn} := by
    rw [← hmap]
    simp only [Measure.real_def, Measure.map_apply (measurable_samplePath hX) hA,
      Set.preimage_setOf_eq]
  rw [hevent] at hbound
  exact hbound

theorem original_one_sided_relative_error_normalized :
    ∃ rhoStar C : ℝ, 0 < rhoStar ∧ rhoStar ≤ 1 / 16 ∧ 0 < C ∧
      ∀ p : ℝ, 2 < p → p ≤ 3 →
        ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu]
          (n : ℕ) (hn : 0 < n),
          Integrable (fun z : ℝ => z ^ 2) nu →
          (∫ z : ℝ, z ∂nu) = 0 →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
          Integrable (fun z : ℝ => Real.rpow |z| p) nu →
          let beta : ℝ := (n : ℝ) * (∫ z : ℝ, Real.rpow |z| p ∂nu)
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
          ∀ x : ℝ, 0 ≤ x →
            (x ≤ Real.rpow beta (-1 / p) ∨
              Shao.truncationBudget nu n x ≤ rhoStar) →
            ∀ s : ℝ, (s = 1 ∨ s = -1) →
              |P.real {v : Shao.Path n |
                x * Real.sqrt (Shao.energy v) ≤ Shao.upperMax (s • v) hn} /
                  Shao.standardNormalTail x - 2| ≤
                C * Shao.truncationBudget nu n x := by
  obtain ⟨rhoStar, C, hrho, hrho16, hC, hUpper⟩ :=
    osre_upper_from_endpoint sourceTruncation_endpoint_relative_error
  exact ⟨rhoStar, C, hrho, hrho16, hC, osre_signed_from_upper rhoStar C hUpper⟩

theorem original_one_sided_relative_error_raw :
    ∃ rhoStar C : ℝ, 0 < rhoStar ∧ rhoStar ≤ 1 / 16 ∧ 0 < C ∧
      ∀ p : ℝ, 2 < p → p ≤ 3 →
        ∀ (mu : Measure ℝ) [IsProbabilityMeasure mu]
          (n : ℕ) (hn : 0 < n),
          Integrable (fun z : ℝ => z ^ 2) mu →
          (∫ z : ℝ, z ∂mu) = 0 →
          (0 < ∫ z : ℝ, z ^ 2 ∂mu) →
          Integrable (fun z : ℝ => Real.rpow |z| p) mu →
          let sigma : ℝ := Real.sqrt (∫ z : ℝ, z ^ 2 ∂mu)
          let nu : Measure ℝ := Measure.map
            (fun z : ℝ => z / (sigma * Real.sqrt (n : ℝ))) mu
          let beta : ℝ := (∫ z : ℝ, Real.rpow |z| p ∂mu) /
            (Real.rpow sigma p * Real.rpow (n : ℝ) ((p - 2) / 2))
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
          ∀ x : ℝ, 0 ≤ x →
            (x ≤ Real.rpow beta (-1 / p) ∨
              Shao.truncationBudget nu n x ≤ rhoStar) →
            ∀ s : ℝ, (s = 1 ∨ s = -1) →
              |P.real {v : Shao.Path n |
                x * Real.sqrt (Shao.energy v) ≤ Shao.upperMax (s • v) hn} /
                  Shao.standardNormalTail x - 2| ≤
                C * Shao.truncationBudget nu n x := by
  obtain ⟨rhoStar, C, hrho, hrho16, hC, hNorm⟩ :=
    original_one_sided_relative_error_normalized
  exact ⟨rhoStar, C, hrho, hrho16, hC, osre_raw_adapter rhoStar C hNorm⟩

theorem original_one_sided_relative_error_iid :
    ∃ rhoStar C : ℝ, 0 < rhoStar ∧ rhoStar ≤ 1 / 16 ∧ 0 < C ∧
      ∀ p : ℝ, 2 < p → p ≤ 3 →
        ∀ {Ω : Type*} [MeasurableSpace Ω]
          (P : Measure Ω) [IsProbabilityMeasure P]
          (n : ℕ) (hn : 0 < n)
          (X : Fin n → Ω → ℝ),
          (∀ i : Fin n, Measurable (X i)) →
          iIndepFun X P →
          (∀ i : Fin n, IdentDistrib (X i) (X ⟨0, hn⟩) P P) →
          let Y : Ω → ℝ := X ⟨0, hn⟩
          Integrable (fun omega : Ω => (Y omega) ^ 2) P →
          (∫ omega : Ω, Y omega ∂P) = 0 →
          (0 < ∫ omega : Ω, (Y omega) ^ 2 ∂P) →
          Integrable (fun omega : Ω => Real.rpow |Y omega| p) P →
          let sigma : ℝ := Real.sqrt (∫ omega : Ω, (Y omega) ^ 2 ∂P)
          let nu : Measure ℝ := Measure.map
            (fun omega : Ω => Y omega / (sigma * Real.sqrt (n : ℝ))) P
          let beta : ℝ := (∫ omega : Ω, Real.rpow |Y omega| p ∂P) /
            (Real.rpow sigma p * Real.rpow (n : ℝ) ((p - 2) / 2))
          ∀ x : ℝ, 0 ≤ x →
            (x ≤ Real.rpow beta (-1 / p) ∨
              Shao.truncationBudget nu n x ≤ rhoStar) →
            ∀ s : ℝ, (s = 1 ∨ s = -1) →
              |P.real {omega : Ω |
                x * Real.sqrt (Shao.energy (samplePath X omega)) ≤
                  Shao.upperMax (s • samplePath X omega) hn} /
                    Shao.standardNormalTail x - 2| ≤
                C * Shao.truncationBudget nu n x := by
  obtain ⟨rhoStar, C, hrho, hrho16, hC, hRaw⟩ :=
    original_one_sided_relative_error_raw
  exact ⟨rhoStar, C, hrho, hrho16, hC, osre_iid_adapter rhoStar C hRaw⟩

end Shao.Probability
