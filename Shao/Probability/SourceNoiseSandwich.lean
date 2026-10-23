import Shao.Probability.SourceFullNoiseBridge
import Shao.Probability.SourceFourierTestKernel
import Shao.Basic.FinitePath

/-!
Actual fixed-source full-noise strict-CDF sandwich. Frozen interfaces:
coordination/public-source-noise-sandwich-declaration-freeze.md.
Both frozen public proofs are written; server kernel/axiom and independent review are pending.
-/

set_option autoImplicit false

namespace Shao

open MeasureTheory ProbabilityTheory
open Probability

private theorem sns_sqrt_shift
    (q t : ℝ) (hq : q ∈ Set.Icc (1 / 4 : ℝ) 2)
    (ht : |t| ≤ 1 / 8) :
    q + t ∈ Set.Icc (1 / 8 : ℝ) 3 ∧
      (1 / 2 : ℝ) ≤ Real.sqrt q ∧
      |Real.sqrt (q + t) - Real.sqrt q| ≤ 2 * |t| := by
  rcases abs_le.mp ht with ⟨htlo, hthi⟩
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hqt0 : 0 ≤ q + t := by linarith [hq.1]
  have ha := Real.sqrt_nonneg q
  have hb := Real.sqrt_nonneg (q + t)
  have hasq := Real.sq_sqrt hq0
  have hbsq := Real.sq_sqrt hqt0
  have haroot : (1 / 2 : ℝ) ≤ Real.sqrt q := by
    nlinarith [hq.1]
  have hsum : (1 / 2 : ℝ) ≤ Real.sqrt (q + t) + Real.sqrt q := by
    linarith
  have hprod :
      (Real.sqrt (q + t) - Real.sqrt q) *
        (Real.sqrt (q + t) + Real.sqrt q) = t := by
    nlinarith
  have habsprod :
      |Real.sqrt (q + t) - Real.sqrt q| *
        (Real.sqrt (q + t) + Real.sqrt q) = |t| := by
    calc
      _ = |(Real.sqrt (q + t) - Real.sqrt q) *
          (Real.sqrt (q + t) + Real.sqrt q)| := by
        rw [abs_mul, abs_of_nonneg (add_nonneg hb ha)]
      _ = |t| := congrArg abs hprod
  refine ⟨⟨by linarith [hq.1], by linarith [hq.2]⟩, haroot, ?_⟩
  have hnonneg := mul_nonneg
    (abs_nonneg (Real.sqrt (q + t) - Real.sqrt q))
    (sub_nonneg.mpr hsum)
  nlinarith

theorem sourceFourierTest_noise_sandwich_pointwise
    (x y u q z t : ℝ) (hx : 0 ≤ x) (hy : 0 < y)
    (hyUpper : y ≤ 1 + x)
    (hq : q ∈ Set.Icc (1 / 4 : ℝ) 2) (ht : |t| ≤ 1 / 8) :
    let delta := 4 * (|z| + (1 + x) * |t|)
    let lower : ℝ :=
      if 0 < q ∧ |u| < (y - delta) * Real.sqrt q then 1 else 0
    let upper : ℝ :=
      if 0 < q ∧ |u| < (y + delta) * Real.sqrt q then 1 else 0
    lower ≤ sourceFourierTest y (u + z, q + t) ∧
      sourceFourierTest y (u + z, q + t) ≤ upper := by
  classical
  dsimp only
  obtain ⟨hqt, hroot, hshift⟩ := sns_sqrt_shift q t hq ht
  have hcut := sourceKernelCutoff_data.2.2.2.1 (q + t) hqt
  have hqpos : 0 < q := by linarith [hq.1]
  have hx1 : 0 ≤ 1 + x := by linarith
  have hd0 : 0 ≤ 4 * (|z| + (1 + x) * |t|) := by positivity
  have hpay :
      |z| + y * |Real.sqrt (q + t) - Real.sqrt q| ≤
        (4 * (|z| + (1 + x) * |t|)) * Real.sqrt q := by
    have h1 := mul_le_mul_of_nonneg_left hshift hy.le
    have h2 := mul_le_mul_of_nonneg_right hyUpper (abs_nonneg t)
    have h3 := mul_le_mul_of_nonneg_left hroot hd0
    nlinarith [abs_nonneg z, abs_nonneg t]
  have hdifflo := neg_abs_le (Real.sqrt (q + t) - Real.sqrt q)
  have hdiffhi := le_abs_self (Real.sqrt (q + t) - Real.sqrt q)
  have hylo := mul_le_mul_of_nonneg_left hdifflo hy.le
  have hyhi := mul_le_mul_of_nonneg_left hdiffhi hy.le
  simp only [sourceFourierTest, hcut, one_mul]
  constructor
  · split_ifs with hl hn
    · norm_num
    · exfalso
      have habs := abs_add_le u z
      have hstrict := hl.2
      have hgoal : |u + z| < y * Real.sqrt (q + t) := by
        nlinarith
      exact hn hgoal
    · norm_num
    · norm_num
  · split_ifs with hn hu
    · norm_num
    · exfalso
      have habs : |u| ≤ |u + z| + |z| := by
        calc
          |u| = |(u + z) + (-z)| := by congr 1; ring
          _ ≤ |u + z| + |-z| := abs_add_le _ _
          _ = |u + z| + |z| := by rw [abs_neg]
      have hgoal : |u| <
          (y + 4 * (|z| + (1 + x) * |t|)) * Real.sqrt q := by
        nlinarith
      exact hu ⟨hqpos, hgoal⟩
    · norm_num
    · norm_num

private theorem sns_test_data (y : ℝ) :
    Measurable (sourceFourierTest y) ∧
      ∀ p : ℝ × ℝ, 0 ≤ sourceFourierTest y p ∧ sourceFourierTest y p ≤ 1 := by
  have hm : Measurable (sourceFourierTest y) := by
    let A : Set (ℝ × ℝ) := {p | |p.1| < y * Real.sqrt p.2}
    have hA : MeasurableSet A :=
      (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet
    have hc : Measurable (fun p : ℝ × ℝ => sourceKernelCutoff p.2) :=
      sourceKernelCutoff_data.1.continuous.measurable.comp measurable_snd
    have he : sourceFourierTest y = A.indicator (fun p => sourceKernelCutoff p.2) := by
      funext p
      by_cases h : p ∈ A <;> simp [sourceFourierTest, Set.indicator, A] at h ⊢
    rw [he]
    exact hc.indicator hA
  refine ⟨hm, ?_⟩
  intro p
  unfold sourceFourierTest
  split_ifs
  · simpa only [mul_one] using sourceKernelCutoff_data.2.2.1 p.2
  · simp

private theorem sns_indicator_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) :
    Integrable (A.indicator (fun _ : Ω => (1 : ℝ))) P ∧
      (∫ a : Ω, A.indicator (fun _ : Ω => (1 : ℝ)) a ∂P) = P.real A := by
  exact ⟨(integrable_const (1 : ℝ)).indicator hA, integral_indicator_one hA⟩

private theorem sns_bad_clock_sandwich
    (x y u q z t : ℝ) (hx : 0 ≤ x) (hy : 0 < y)
    (hyUpper : y ≤ 1 + x) (ht : |t| ≤ 1 / 8) :
    let delta := 4 * (|z| + (1 + x) * |t|)
    let lower : ℝ :=
      if 0 < q ∧ |u| < (y - delta) * Real.sqrt q then 1 else 0
    let upper : ℝ :=
      if 0 < q ∧ |u| < (y + delta) * Real.sqrt q then 1 else 0
    let bad : ℝ := if q ∈ Set.Icc (1 / 4 : ℝ) 2 then 0 else 1
    lower - bad ≤ sourceFourierTest y (u + z, q + t) ∧
      sourceFourierTest y (u + z, q + t) ≤ upper + bad := by
  classical
  dsimp only
  by_cases hq : q ∈ Set.Icc (1 / 4 : ℝ) 2
  · simpa only [if_pos hq, sub_zero, add_zero] using
      sourceFourierTest_noise_sandwich_pointwise x y u q z t hx hy hyUpper hq ht
  · simp only [if_neg hq]
    obtain ⟨hlo, hhi⟩ := (sns_test_data y).2 (u + z, q + t)
    constructor
    · split_ifs <;> linarith
    · split_ifs <;> linarith

private theorem sns_section_probability_integrable
    {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (P : Measure Ω) (L : Measure Z) [IsProbabilityMeasure P] [IsProbabilityMeasure L]
    (A : Set (Ω × Z)) (hA : MeasurableSet A) :
    Integrable (fun z : Z => P.real {a : Ω | (a, z) ∈ A}) L ∧
      (∫ z : Z, P.real {a : Ω | (a, z) ∈ A} ∂L) = (P.prod L).real A := by
  classical
  have hi : Integrable (A.indicator (fun _ : Ω × Z => (1 : ℝ))) (P.prod L) :=
    (integrable_const (1 : ℝ)).indicator hA
  have he (z : Z) :
      (∫ a : Ω, A.indicator (fun _ : Ω × Z => (1 : ℝ)) (a, z) ∂P) =
        P.real {a : Ω | (a, z) ∈ A} := by
    have hsection : MeasurableSet {a : Ω | (a, z) ∈ A} :=
      hA.preimage (measurable_id.prodMk measurable_const)
    simpa only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply] using
      (integral_indicator_one (μ := P) hsection)
  constructor
  · exact hi.integral_prod_right.congr (Filter.Eventually.of_forall he)
  · calc
      _ = ∫ z : Z, ∫ a : Ω,
          A.indicator (fun _ : Ω × Z => (1 : ℝ)) (a, z) ∂P ∂L := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => (he z).symm
      _ = ∫ p : Ω × Z, A.indicator (fun _ => (1 : ℝ)) p ∂P.prod L :=
        (integral_prod_symm _ hi).symm
      _ = (P.prod L).real A := integral_indicator_one hA

private theorem sns_product_test_integrable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (L : Measure (ℝ × ℝ))
    [IsProbabilityMeasure P] [IsProbabilityMeasure L]
    (U Q : Ω → ℝ) (hU : Measurable U) (hQ : Measurable Q) (y : ℝ) :
    Integrable (fun p : Ω × (ℝ × ℝ) =>
        sourceFourierTest y (U p.1 + p.2.1, Q p.1 + p.2.2)) (P.prod L) ∧
      Integrable (fun a : Ω => ∫ z : ℝ × ℝ,
        sourceFourierTest y (U a + z.1, Q a + z.2) ∂L) P := by
  have hm : Measurable (fun p : Ω × (ℝ × ℝ) =>
      sourceFourierTest y (U p.1 + p.2.1, Q p.1 + p.2.2)) :=
    (sns_test_data y).1.comp
      (((hU.comp measurable_fst).add (measurable_fst.comp measurable_snd)).prodMk
        ((hQ.comp measurable_fst).add (measurable_snd.comp measurable_snd)))
  have hi : Integrable (fun p : Ω × (ℝ × ℝ) =>
      sourceFourierTest y (U p.1 + p.2.1, Q p.1 + p.2.2)) (P.prod L) := by
    refine (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable ?_
    filter_upwards [] with p
    obtain ⟨hlo, hhi⟩ := (sns_test_data y).2 (U p.1 + p.2.1, Q p.1 + p.2.2)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlo] using hhi
  exact ⟨hi, hi.integral_prod_left⟩

private theorem sns_delta_support
    (x epsilon : ℝ) (hx : 0 ≤ x) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 800) (z : ℝ × ℝ)
    (hz : |z.1| + (1 + x) * |z.2| ≤ 100 * (epsilon / (1 + x))) :
    |z.2| ≤ 1 / 8 ∧
      0 ≤ 4 * (|z.1| + (1 + x) * |z.2|) ∧
      4 * (|z.1| + (1 + x) * |z.2|) ≤ 400 * (epsilon / (1 + x)) := by
  have hxpos : 0 < 1 + x := by linarith
  have hh : epsilon / (1 + x) ≤ 1 / 800 := by
    apply (div_le_iff₀ hxpos).2
    nlinarith
  have hxb := mul_nonneg hx (abs_nonneg z.2)
  refine ⟨by nlinarith [abs_nonneg z.1], ?_, by nlinarith⟩
  positivity

private theorem sns_averaged_sandwich
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (L : Measure (ℝ × ℝ))
    [IsProbabilityMeasure P] [IsProbabilityMeasure L]
    (U Q : Ω → ℝ) (hU : Measurable U) (hQ : Measurable Q)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) (hyUpper : y ≤ 1 + x)
    (hY : ∀ᵐ z : ℝ × ℝ ∂L, |z.2| ≤ 1 / 8) :
    let delta := fun z : ℝ × ℝ => 4 * (|z.1| + (1 + x) * |z.2|)
    let bad := P.real {a : Ω | Q a ∉ Set.Icc (1 / 4 : ℝ) 2}
    let F := fun v : ℝ => P.real {a : Ω | 0 < Q a ∧ |U a| < v * Real.sqrt (Q a)}
    let psi := fun p : ℝ × ℝ =>
      ∫ z : ℝ × ℝ, sourceFourierTest y (p.1 + z.1, p.2 + z.2) ∂L
    Integrable (fun z => F (y - delta z)) L ∧
      Integrable (fun z => F (y + delta z)) L ∧
      Integrable (fun a => psi (U a, Q a)) P ∧
      (∫ z, F (y - delta z) ∂L) - bad ≤ (∫ a, psi (U a, Q a) ∂P) ∧
      (∫ a, psi (U a, Q a) ∂P) ≤ (∫ z, F (y + delta z) ∂L) + bad := by
  classical
  dsimp only
  let delta := fun z : ℝ × ℝ => 4 * (|z.1| + (1 + x) * |z.2|)
  let badSet : Set Ω := {a : Ω | Q a ∉ Set.Icc (1 / 4 : ℝ) 2}
  let bad := P.real badSet
  let F := fun v : ℝ => P.real {a : Ω | 0 < Q a ∧ |U a| < v * Real.sqrt (Q a)}
  let T := fun p : Ω × (ℝ × ℝ) =>
    sourceFourierTest y (U p.1 + p.2.1, Q p.1 + p.2.2)
  let J := fun z : ℝ × ℝ => ∫ a : Ω, T (a, z) ∂P
  have hdelta : Measurable delta := by dsimp [delta]; fun_prop
  have hbadSet : MeasurableSet badSet := by
    exact (measurableSet_Icc.preimage hQ).compl
  obtain ⟨hBint, hBeq⟩ := sns_indicator_integral P badSet hbadSet
  have hT := (sns_product_test_integrable P L U Q hU hQ y).1
  have hJ : Integrable J L := hT.integral_prod_right
  have hpsi := (sns_product_test_integrable P L U Q hU hQ y).2
  let Aminus : Set (Ω × (ℝ × ℝ)) :=
    {p | 0 < Q p.1 ∧ |U p.1| < (y - delta p.2) * Real.sqrt (Q p.1)}
  let Aplus : Set (Ω × (ℝ × ℝ)) :=
    {p | 0 < Q p.1 ∧ |U p.1| < (y + delta p.2) * Real.sqrt (Q p.1)}
  have hAminus : MeasurableSet Aminus := by
    dsimp [Aminus]
    exact (measurableSet_lt measurable_const (hQ.comp measurable_fst)).inter
      (measurableSet_lt (continuous_abs.measurable.comp (hU.comp measurable_fst))
        ((measurable_const.sub (hdelta.comp measurable_snd)).mul
          ((hQ.comp measurable_fst).sqrt)))
  have hAplus : MeasurableSet Aplus := by
    dsimp [Aplus]
    exact (measurableSet_lt measurable_const (hQ.comp measurable_fst)).inter
      (measurableSet_lt (continuous_abs.measurable.comp (hU.comp measurable_fst))
        ((measurable_const.add (hdelta.comp measurable_snd)).mul
          ((hQ.comp measurable_fst).sqrt)))
  have hminus : Integrable (fun z => F (y - delta z)) L :=
    (sns_section_probability_integrable P L Aminus hAminus).1
  have hplus : Integrable (fun z => F (y + delta z)) L :=
    (sns_section_probability_integrable P L Aplus hAplus).1
  have hpoint : ∀ᵐ z : ℝ × ℝ ∂L,
      F (y - delta z) - bad ≤ J z ∧ J z ≤ F (y + delta z) + bad := by
    filter_upwards [hY] with z hz
    let Bminus : Set Ω := {a | 0 < Q a ∧ |U a| <
      (y - delta z) * Real.sqrt (Q a)}
    let Bplus : Set Ω := {a | 0 < Q a ∧ |U a| <
      (y + delta z) * Real.sqrt (Q a)}
    have hm : MeasurableSet Bminus := by
      dsimp [Bminus]
      exact (measurableSet_lt measurable_const hQ).inter
        (measurableSet_lt (continuous_abs.measurable.comp hU) (measurable_const.mul hQ.sqrt))
    have hp : MeasurableSet Bplus := by
      dsimp [Bplus]
      exact (measurableSet_lt measurable_const hQ).inter
        (measurableSet_lt (continuous_abs.measurable.comp hU) (measurable_const.mul hQ.sqrt))
    obtain ⟨him, hem⟩ := sns_indicator_integral P Bminus hm
    obtain ⟨hip, hep⟩ := sns_indicator_integral P Bplus hp
    have hiT : Integrable (fun a : Ω => T (a, z)) P := by
      refine (integrable_const (1 : ℝ)).mono' ?_ ?_
      · exact ((sns_test_data y).1.comp
          ((hU.add_const z.1).prodMk (hQ.add_const z.2))).aestronglyMeasurable
      · filter_upwards [] with a
        obtain ⟨hlo, hhi⟩ := (sns_test_data y).2 (U a + z.1, Q a + z.2)
        simpa only [T, Real.norm_eq_abs, abs_of_nonneg hlo] using hhi
    have hbad (a : Ω) :
        (if a ∈ badSet then (1 : ℝ) else 0) =
          (if Q a ∈ Set.Icc (1 / 4 : ℝ) 2 then (0 : ℝ) else 1) := by
      simp only [badSet, Set.mem_setOf_eq]
      split_ifs <;> rfl
    constructor
    · have hh := integral_mono_ae (him.sub hBint) hiT
        (Filter.Eventually.of_forall fun a => by
          simpa only [Pi.sub_apply, Set.indicator_apply, Bminus, Set.mem_setOf_eq, hbad, T, delta] using
            (sns_bad_clock_sandwich x y (U a) (Q a) z.1 z.2 hx hy hyUpper hz).1)
      simp only [Pi.sub_apply] at hh
      rw [integral_sub him hBint, hem, hBeq] at hh
      exact hh
    · have hh := integral_mono_ae hiT (hip.add hBint)
        (Filter.Eventually.of_forall fun a => by
          simpa only [Pi.add_apply, Set.indicator_apply, Bplus, Set.mem_setOf_eq, hbad, T, delta] using
            (sns_bad_clock_sandwich x y (U a) (Q a) z.1 z.2 hx hy hyUpper hz).2)
      simp only [Pi.add_apply] at hh
      rw [integral_add hip hBint, hep, hBeq] at hh
      exact hh
  have hswap : (∫ z, J z ∂L) =
      ∫ a : Ω, ∫ z : ℝ × ℝ,
        sourceFourierTest y (U a + z.1, Q a + z.2) ∂L ∂P := by
    calc
      _ = ∫ p : Ω × (ℝ × ℝ), T p ∂P.prod L := (integral_prod_symm _ hT).symm
      _ = _ := integral_prod _ hT
  have hlo := integral_mono_ae (hminus.sub (integrable_const bad)) hJ
    (hpoint.mono fun _ h => h.1)
  have hhi := integral_mono_ae hJ (hplus.add (integrable_const bad))
    (hpoint.mono fun _ h => h.2)
  simp only [Pi.sub_apply] at hlo
  simp only [Pi.add_apply] at hhi
  rw [integral_sub hminus (integrable_const bad), integral_const, hswap] at hlo
  rw [integral_add hplus (integrable_const bad), integral_const, hswap] at hhi
  have hL : L.real Set.univ = 1 := by
    change (L Set.univ).toReal = (1 : ℝ)
    simp
  simpa only [hL, one_smul] using
    And.intro hminus (And.intro hplus (And.intro hpsi (And.intro hlo hhi)))

theorem sourceTruncation_actual_noise_cdf_sandwich
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (hmean : (∫ z : ℝ, z ∂ν) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 800)
    (hR : truncationBudget ν n x ≤ epsilon ^ 3 / 8) :
    let h := epsilon / (1 + x)
    let rho := ProbabilityTheory.cond ν {z | |z| ≤ h}
    let P := Measure.pi (fun _ : Fin n => rho)
    let law := Probability.quadraticFullNoiseLaw rho
    let gamma := (∫ z : ℝ, |z| ^ 3 ∂rho) / variance (id : ℝ → ℝ) rho
    let delta := fun z : ℝ × ℝ => 4 * (|z.1| + (1 + x) * |z.2|)
    let bad := P.real {a : Fin n → ℝ | energy a ∉ Set.Icc (1 / 4 : ℝ) 2}
    IsProbabilityMeasure P ∧ IsProbabilityMeasure law ∧
      Integrable delta law ∧
      (∀ᵐ z ∂law, delta z ∈ Set.Icc 0 (400 * h)) ∧
      (∫ z, delta z ∂law) ≤ 400 * gamma ∧
      ∀ (U : (Fin n → ℝ) → ℝ), Measurable U →
        ∀ y : ℝ, 0 < y → y ≤ 1 + x →
          let F := fun v : ℝ =>
            P.real {a : Fin n → ℝ | 0 < energy a ∧ |U a| < v * Real.sqrt (energy a)}
          let psi := fun p : ℝ × ℝ =>
            ∫ z : ℝ × ℝ, sourceFourierTest y (p.1 + z.1, p.2 + z.2) ∂law
          Integrable (fun z => F (y - delta z)) law ∧
            Integrable (fun z => F (y + delta z)) law ∧
            Integrable (fun a => psi (U a, energy a)) P ∧
            (∫ z, F (y - delta z) ∂law) - bad ≤
              (∫ a, psi (U a, energy a) ∂P) ∧
            (∫ a, psi (U a, energy a) ∂P) ≤
              (∫ z, F (y + delta z) ∂law) + bad := by
  let h := epsilon / (1 + x)
  let rho := ProbabilityTheory.cond ν {z | |z| ≤ h}
  let P := Measure.pi (fun _ : Fin n => rho)
  let law := Probability.quadraticFullNoiseLaw rho
  let gamma := (∫ z : ℝ, |z| ^ 3 ∂rho) / variance (id : ℝ → ℝ) rho
  let delta := fun z : ℝ × ℝ => 4 * (|z.1| + (1 + x) * |z.2|)
  have hepsilonHalf : epsilon ≤ 1 / 2 := by linarith
  have hdata := sourceTruncation_law_data ν n h2 hnorm
    x epsilon hx hepsilon hepsilonHalf hR
  letI : IsProbabilityMeasure rho := hdata.2.2.1
  have hf := sourceTruncation_fullNoise ν n h2 hnorm hmean
    x epsilon hx hepsilon hepsilonHalf hR
  letI : IsProbabilityMeasure law := hf.1
  have hs : ∀ᵐ z : ℝ × ℝ ∂law, |z.1| + (1 + x) * |z.2| ≤ 100 * h := hf.2.2.1
  have hAE : ∀ᵐ z : ℝ × ℝ ∂law, delta z ∈ Set.Icc 0 (400 * h) := by
    filter_upwards [hs] with z hz
    exact (sns_delta_support x epsilon hx hepsilon hepsilonSmall z hz).2
  have hY : ∀ᵐ z : ℝ × ℝ ∂law, |z.2| ≤ 1 / 8 := by
    filter_upwards [hs] with z hz
    exact (sns_delta_support x epsilon hx hepsilon hepsilonSmall z hz).1
  have hi1 : Integrable (fun z : ℝ × ℝ => |z.1|) law := by
    refine (integrable_const (100 * h)).mono'
      (by fun_prop) ?_
    filter_upwards [hs] with z hz
    have hx1 : 0 ≤ 1 + x := by linarith
    have hb := mul_nonneg hx1 (abs_nonneg z.2)
    simpa only [Real.norm_eq_abs, abs_abs] using (show |z.1| ≤ 100 * h by linarith)
  have hi2 : Integrable (fun z : ℝ × ℝ => |z.2|) law := by
    refine (integrable_const (100 * h)).mono'
      (by fun_prop) ?_
    filter_upwards [hs] with z hz
    have hb := mul_nonneg hx (abs_nonneg z.2)
    simpa only [Real.norm_eq_abs, abs_abs] using
      (show |z.2| ≤ 100 * h by nlinarith [abs_nonneg z.1])
  have hd : Integrable delta law := (hi1.add (hi2.const_mul (1 + x))).const_mul 4
  have hmoment : (∫ z : ℝ × ℝ, delta z ∂law) ≤ 400 * gamma := by
    change (∫ z : ℝ × ℝ, 4 * (|z.1| + (1 + x) * |z.2|) ∂law) ≤ 400 * gamma
    rw [integral_const_mul, integral_add hi1 (hi2.const_mul (1 + x)), integral_const_mul]
    have hpaid := hf.2.2.2.1
    nlinarith only [hpaid]
  refine ⟨inferInstance, inferInstance, hd, hAE, hmoment, ?_⟩
  intro U hU y hy hyUpper
  have hQ : Measurable (fun a : Fin n → ℝ => energy a) := by
    unfold energy
    fun_prop
  exact sns_averaged_sandwich P law U (fun a => energy a) hU hQ x y hx hy hyUpper hY

end Shao
