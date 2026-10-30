import Shao.OQ6.ConditionalVarianceMean
import Shao.OQ5.P41.FiniteBackgroundPerturbation
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Shao.OQ5.P41.InteractionSectionMoments

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open Shao.OQ5.P41.FiniteBackgroundPerturbation

def interactionSum {ι Ω : Type*} [Fintype ι]
    (r : Ω → Ω → ℝ) (a : ι → Ω) : Ω → ℝ
:=
  fun o => ∑ i : ι, r (a i) o

def anomalyEnvelope {ι Ω : Type*} [Fintype ι]
    (w : Ω → ℝ) (a : ι → Ω) : ℝ
:=
  ∑ i : ι, w (a i)

def anomalyLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (w : Ω → ℝ) (R : ℝ) : Measure Ω
:=
  (μ {o : Ω | w o ≤ R}ᶜ)⁻¹ • μ.restrict {o : Ω | w o ≤ R}ᶜ

def validAnomalyVector {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (ν : Measure Ω) (r : Ω → Ω → ℝ) (w : Ω → ℝ)
    (c : ℝ) (a : ι → Ω) : Prop
:=
  ∀ i : ι, 0 ≤ w (a i) ∧ Measurable (r (a i)) ∧ Integrable (r (a i)) ν ∧
    |∫ o, r (a i) o ∂ν| ≤ c * w (a i) ∧
    (∀ᵐ o ∂ν, |r (a i) o| ≤ w (a i) * w o)

def interactionMomentBounds {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (ν : Measure Ω) (r : Ω → Ω → ℝ) (w : Ω → ℝ)
    (c R M : ℝ) (a : ι → Ω) : Prop
:=
  let ell : ℝ := anomalyEnvelope w a
  let cA : Ω → ℝ := interactionSum r a
  let mA : ℝ := ∫ o, cA o ∂ν
  let S2 : ℝ := ∫ o, cA o ^ 2 ∂ν
  let V2 : ℝ := ∫ o, (cA o - mA) ^ 2 ∂ν
  0 ≤ ell ∧ Measurable cA ∧ Integrable cA ν ∧ MemLp cA 2 ν ∧
    Integrable (fun o => cA o ^ 2) ν ∧
    (∀ᵐ o ∂ν, |cA o| ≤ ell * w o) ∧
    mA = (∑ i : ι, ∫ o, r (a i) o ∂ν) ∧
    |mA| ≤ c * ell ∧ |mA| ≤ ell * R ∧
    0 ≤ S2 ∧ S2 ≤ ell ^ 2 * M ∧ mA ^ 2 ≤ S2 ∧
    Measurable (fun o => cA o - mA) ∧
    Integrable (fun o => cA o - mA) ν ∧
    MemLp (fun o => cA o - mA) 2 ν ∧
    (∫ o, cA o - mA ∂ν) = 0 ∧
    Integrable (fun o => (cA o - mA) ^ 2) ν ∧
    V2 = S2 - mA ^ 2 ∧ 0 ≤ V2 ∧ V2 ≤ S2 ∧ V2 ≤ ell ^ 2 * M ∧
    (∀ᵐ o ∂ν, |cA o| ≤ ell * R ∧
      |cA o - mA| ≤ ell * (R + c) ∧ |cA o - mA| ≤ 2 * ell * R)

theorem interaction_moments_of_valid
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (r : Ω → Ω → ℝ) (w : Ω → ℝ)
    (c R M : ℝ) (hc : 0 ≤ c) (hR : 0 ≤ R)
    (hw2 : MemLp w 2 ν)
    (hw : ∀ᵐ o ∂ν, 0 ≤ w o ∧ w o ≤ R)
    (hM : (∫ o, w o ^ 2 ∂ν) ≤ M)
    (a : ι → Ω) (ha : validAnomalyVector ν r w c a) :
    interactionMomentBounds ν r w c R M a
:= by
  classical
  dsimp only [validAnomalyVector] at ha
  let ell : ℝ := anomalyEnvelope w a
  let cA : Ω → ℝ := interactionSum r a
  let mA : ℝ := ∫ o, cA o ∂ν
  let S2 : ℝ := ∫ o, cA o ^ 2 ∂ν
  let V2 : ℝ := ∫ o, (cA o - mA) ^ 2 ∂ν
  have hell : 0 ≤ ell := by
    exact Finset.sum_nonneg (fun i _ => (ha i).1)
  have hcm : Measurable cA := by
    simpa only [cA, interactionSum] using
      (Finset.measurable_fun_sum (Finset.univ : Finset ι)
        (fun i _ => (ha i).2.1))
  have hci : Integrable cA ν := by
    simpa only [cA, interactionSum] using
      (integrable_finsetSum (Finset.univ : Finset ι)
        (fun i _ => (ha i).2.2.1))
  have hrow : ∀ᵐ o ∂ν, ∀ i : ι,
      |r (a i) o| ≤ w (a i) * w o :=
    Filter.eventually_all.2 (fun i => (ha i).2.2.2.2)
  have henv : ∀ᵐ o ∂ν, |cA o| ≤ ell * w o := by
    filter_upwards [hrow] with o ho
    calc
      |cA o| ≤ ∑ i : ι, |r (a i) o| :=
        Finset.abs_sum_le_sum_abs (fun i : ι => r (a i) o) Finset.univ
      _ ≤ ∑ i : ι, w (a i) * w o := Finset.sum_le_sum (fun i _ => ho i)
      _ = ell * w o := by
        dsimp only [ell, anomalyEnvelope]
        rw [Finset.sum_mul]
  have hmean : mA = ∑ i : ι, ∫ o, r (a i) o ∂ν := by
    exact integral_finsetSum Finset.univ (fun i _ => (ha i).2.2.1)
  have hmeanB : |mA| ≤ c * ell := by
    calc
      |mA| = |∑ i : ι, ∫ o, r (a i) o ∂ν| := congrArg abs hmean
      _ ≤ ∑ i : ι, |∫ o, r (a i) o ∂ν| :=
        Finset.abs_sum_le_sum_abs (fun i : ι => ∫ o, r (a i) o ∂ν) Finset.univ
      _ ≤ ∑ i : ι, c * w (a i) :=
        Finset.sum_le_sum (fun i _ => (ha i).2.2.2.1)
      _ = c * ell := by
        dsimp only [ell, anomalyEnvelope]
        rw [Finset.mul_sum]
  have hsup : ∀ᵐ o ∂ν, |cA o| ≤ ell * R := by
    filter_upwards [henv, hw] with o ho hwo
    exact ho.trans (mul_le_mul_of_nonneg_left hwo.2 hell)
  have hmeanR : |mA| ≤ ell * R := by
    have hn : ∀ᵐ o ∂ν, ‖cA o‖ ≤ ell * R := by
      simpa only [Real.norm_eq_abs] using hsup
    simpa only [mA, Real.norm_eq_abs, probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := ν) (f := cA) hn)
  have hsqAE : ∀ᵐ o ∂ν, cA o ^ 2 ≤ ell ^ 2 * w o ^ 2 := by
    filter_upwards [henv, hw] with o ho hwo
    have hs := (sq_le_sq₀ (abs_nonneg (cA o)) (mul_nonneg hell hwo.1)).2 ho
    simpa only [sq_abs, mul_pow] using hs
  have hsq : Integrable (fun o => cA o ^ 2) ν := by
    apply (hw2.integrable_sq.const_mul (ell ^ 2)).mono'
      (hcm.pow_const 2).aestronglyMeasurable
    filter_upwards [hsqAE] with o ho
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (cA o))] using ho
  have hcl2 : MemLp cA 2 ν :=
    (memLp_two_iff_integrable_sq hcm.aestronglyMeasurable).2 hsq
  have hS0 : 0 ≤ S2 := integral_nonneg (fun o => sq_nonneg (cA o))
  have hSbound : S2 ≤ ell ^ 2 * M := by
    calc
      S2 ≤ ∫ o, ell ^ 2 * w o ^ 2 ∂ν :=
        integral_mono_ae hsq (hw2.integrable_sq.const_mul (ell ^ 2)) hsqAE
      _ = ell ^ 2 * (∫ o, w o ^ 2 ∂ν) := integral_const_mul _ _
      _ ≤ ell ^ 2 * M := mul_le_mul_of_nonneg_left hM (sq_nonneg ell)
  have hcentm : Measurable (fun o => cA o - mA) := hcm.sub measurable_const
  have hcenti : Integrable (fun o => cA o - mA) ν :=
    hci.sub (integrable_const mA)
  have hcentSq : Integrable (fun o => (cA o - mA) ^ 2) ν := by
    have hp := (hsq.sub (hci.const_mul (2 * mA))).add (integrable_const (mA ^ 2))
    apply hp.congr
    exact Filter.Eventually.of_forall (fun o => by
      change cA o ^ 2 - (2 * mA) * cA o + mA ^ 2 = (cA o - mA) ^ 2
      ring)
  have hcent2 : MemLp (fun o => cA o - mA) 2 ν :=
    (memLp_two_iff_integrable_sq hcentm.aestronglyMeasurable).2 hcentSq
  have hcent0 : (∫ o, cA o - mA ∂ν) = 0 := by
    rw [integral_sub hci (integrable_const mA), integral_const,
      probReal_univ, one_smul]
    change mA - mA = 0
    ring
  have hvar : V2 = S2 - mA ^ 2 := by
    calc
      V2 = ∫ o, cA o ^ 2 - (2 * mA) * cA o + mA ^ 2 ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun o => by ring)
      _ = S2 - (2 * mA) * (∫ o, cA o ∂ν) + mA ^ 2 := by
        rw [integral_add (f := fun o => cA o ^ 2 - (2 * mA) * cA o)
            (g := fun _ : Ω => mA ^ 2)
            (hsq.sub (hci.const_mul (2 * mA))) (integrable_const (mA ^ 2)),
          integral_sub (f := fun o => cA o ^ 2)
            (g := fun o => (2 * mA) * cA o)
            hsq (hci.const_mul (2 * mA)),
          integral_const_mul, integral_const, probReal_univ, one_smul]
      _ = S2 - mA ^ 2 := by
        change S2 - (2 * mA) * mA + mA ^ 2 = S2 - mA ^ 2
        ring
  have hV0 : 0 ≤ V2 := integral_nonneg (fun o => sq_nonneg (cA o - mA))
  have hmeanSq : mA ^ 2 ≤ S2 := by linarith only [hvar, hV0]
  have hVS : V2 ≤ S2 := by linarith only [hvar, sq_nonneg mA]
  have hVbound : V2 ≤ ell ^ 2 * M := hVS.trans hSbound
  have hbounded : ∀ᵐ o ∂ν, |cA o| ≤ ell * R ∧
      |cA o - mA| ≤ ell * (R + c) ∧ |cA o - mA| ≤ 2 * ell * R := by
    filter_upwards [hsup] with o ho
    refine ⟨ho, ?_, ?_⟩
    · calc
        |cA o - mA| ≤ |cA o| + |mA| := abs_sub _ _
        _ ≤ ell * R + c * ell := add_le_add ho hmeanB
        _ = ell * (R + c) := by ring
    · calc
        |cA o - mA| ≤ |cA o| + |mA| := abs_sub _ _
        _ ≤ ell * R + ell * R := add_le_add ho hmeanR
        _ = 2 * ell * R := by ring
  exact ⟨hell, hcm, hci, hcl2, hsq, henv, hmean, hmeanB, hmeanR,
    hS0, hSbound, hmeanSq, hcentm, hcenti, hcent2, hcent0, hcentSq,
    hvar, hV0, hVS, hVbound, hbounded⟩

theorem actual_interaction_section_moments
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun z : Ω × Ω => h z.1 z.2))
    (hh2 : MemLp (fun z : Ω × Ω => h z.1 z.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ z : Ω × Ω, h z.1 z.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond : (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (w : Ω → ℝ) (hw : Measurable w)
    (hwone : ∀ᵐ o ∂μ, 1 ≤ w o)
    (α τ : ℝ) (hα : 0 < α) (hτ : 0 < τ)
    (hwexp : Integrable (fun o => Real.exp (τ * Real.rpow (w o) α)) μ)
    (henvelope : ∀ᵐ z : Ω × Ω ∂(μ.prod μ),
      |h z.1 z.2 - (∫ y, h z.1 y ∂μ) - (∫ y, h z.2 y ∂μ)| ≤
        w z.1 * w z.2)
    (p : ℝ) (hp : 2 < p ∧ p ≤ 3)
    (hgp : Integrable (fun o => Real.rpow |∫ y, h o y ∂μ| p) μ)
    (R : ℝ) (hcutoff : (1 / 2 : ℝ) ≤ μ.real {o : Ω | w o ≤ R}) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let C : Set Ω := {o : Ω | w o ≤ R}
    let d : ℝ := μ.real C
    let ν : Measure Ω := (μ C)⁻¹ • μ.restrict C
    let η : Measure Ω := anomalyLaw μ w R
    let b : ℝ := ∫ o in Cᶜ, w o ∂μ
    let c : ℝ := b / d
    let W2 : ℝ := Real.sqrt (∫ o, w o ^ 2 ∂μ)
    let M : ℝ := W2 ^ 2 / d
    Measurable g ∧ Measurable (fun z : Ω × Ω => r z.1 z.2) ∧
      MeasurableSet C ∧ 0 < d ∧ 0 ≤ b ∧ 0 ≤ c ∧ 1 ≤ R ∧ 0 ≤ R ∧
      IsProbabilityMeasure ν ∧ ν ≪ μ ∧
      (∀ᵐ o ∂ν, 1 ≤ w o ∧ w o ≤ R) ∧
      MemLp w 2 μ ∧ MemLp w 2 ν ∧ (∫ o, w o ^ 2 ∂ν) ≤ M ∧ 0 ≤ M ∧
      η ≪ μ ∧ IsFiniteMeasure η ∧
      (μ Cᶜ = 0 → η = 0) ∧ (μ Cᶜ ≠ 0 → IsProbabilityMeasure η) ∧
      (∀ᵐ a : ι → Ω ∂Measure.pi (fun _ : ι => η),
        (∀ i : ι, R < w (a i) ∧ 1 ≤ w (a i) ∧
          Integrable (r (a i)) μ ∧
          (∫ o, r (a i) o ∂ν) = -(∫ o in Cᶜ, r (a i) o ∂μ) / d) ∧
        validAnomalyVector ν r w c a ∧
        interactionMomentBounds ν r w c R M a ∧
        (∫ o, interactionSum r a o ∂ν) =
          -(∑ i : ι, ∫ o in Cᶜ, r (a i) o ∂μ) / d)
:= by
  classical
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
  let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
  let C : Set Ω := {o : Ω | w o ≤ R}
  let d : ℝ := μ.real C
  let ν : Measure Ω := (μ C)⁻¹ • μ.restrict C
  let η : Measure Ω := anomalyLaw μ w R
  let b : ℝ := ∫ o in Cᶜ, w o ∂μ
  let c : ℝ := b / d
  let W2 : ℝ := Real.sqrt (∫ o, w o ^ 2 ∂μ)
  let M : ℝ := W2 ^ 2 / d
  have hsource :=
    Shao.OQ6.ConditionalVarianceMean.actual_conditional_variance_mean
      μ h hh hh2 hhsymm hcenter hprojectionsecond
      w hw hwone α τ hα hτ hwexp henvelope p hp hgp
  dsimp only at hsource
  rcases hsource with ⟨hβ, hB, hW2, hCvar, hCmean, hsource⟩
  have hdata := hsource R hcutoff 0 (by constructor <;> norm_num)
  dsimp only at hdata
  rcases hdata with
    ⟨hC, hdpi, hd, hπ0, hπlt, hb0, hνprob, hνac, hνprodac,
      hgm, hg2, hgν2, hgmean, hgsecond, hw2, hwν2, hwSecond,
      ham, haν2, hrows, hunused⟩
  clear hsource hβ hB hW2 hCvar hCmean hdpi hπ0 hπlt hνprodac
    hg2 hgν2 hgmean hgsecond ham haν2 hunused
  change MeasurableSet C at hC
  change 0 < d at hd
  change 0 ≤ b at hb0
  change IsProbabilityMeasure ν at hνprob
  change ν ≪ μ at hνac
  change Measurable g at hgm
  change MemLp w 2 μ at hw2
  change MemLp w 2 ν at hwν2
  change (∫ o, w o ^ 2 ∂ν) ≤ M at hwSecond
  change (∀ᵐ o ∂μ, Integrable (r o) μ ∧ Integrable (r o) ν ∧
    (∫ y, r o y ∂ν) = -(∫ y in Cᶜ, r o y ∂μ) / d ∧
    |∫ y, r o y ∂ν| ≤ c * w o) at hrows
  haveI : IsProbabilityMeasure ν := hνprob
  have hc0 : 0 ≤ c := div_nonneg hb0 hd.le
  have hM0 : 0 ≤ M := div_nonneg (sq_nonneg W2) hd.le
  have hrm : Measurable (fun z : Ω × Ω => r z.1 z.2) :=
    (hh.sub (hgm.comp measurable_fst)).sub (hgm.comp measurable_snd)
  have hrowm (o : Ω) : Measurable (r o) :=
    hrm.comp (measurable_const.prodMk measurable_id)
  have henv : ∀ᵐ z : Ω × Ω ∂(μ.prod μ),
      |r z.1 z.2| ≤ w z.1 * w z.2 := henvelope
  have hsections : ∀ᵐ o ∂μ, ∀ᵐ y ∂μ, |r o y| ≤ w o * w y :=
    Measure.ae_ae_of_ae_prod henv
  have hνmem : ∀ᵐ o ∂ν, o ∈ C :=
    Measure.ae_smul_measure (ae_restrict_mem hC) (μ C)⁻¹
  have hνW : ∀ᵐ o ∂ν, 1 ≤ w o ∧ w o ≤ R := by
    filter_upwards [hνac.ae_le hwone, hνmem] with o ho hCo
    exact ⟨ho, hCo⟩
  have hR1 : 1 ≤ R := by
    obtain ⟨o, ho⟩ := hνW.exists
    exact ho.1.trans ho.2
  have hR0 : 0 ≤ R := zero_le_one.trans hR1
  have hηac : η ≪ μ := by
    change ProbabilityTheory.cond μ Cᶜ ≪ μ
    exact ProbabilityTheory.cond_absolutelyContinuous
  have hηzero : μ Cᶜ = 0 → η = 0 := by
    intro hz
    change (μ Cᶜ)⁻¹ • μ.restrict Cᶜ = 0
    rw [Measure.restrict_eq_zero.2 hz]
    exact smul_zero _
  have hηprob : μ Cᶜ ≠ 0 → IsProbabilityMeasure η := by
    intro hz
    change IsProbabilityMeasure (ProbabilityTheory.cond μ Cᶜ)
    exact ProbabilityTheory.cond_isProbabilityMeasure hz
  have hηfinite : IsFiniteMeasure η := by
    by_cases hz : μ Cᶜ = 0
    · rw [hηzero hz]
      infer_instance
    · haveI : IsProbabilityMeasure η := hηprob hz
      infer_instance
  haveI : IsFiniteMeasure η := hηfinite
  have hηmem : ∀ᵐ o ∂η, o ∈ Cᶜ := by
    change ∀ᵐ o ∂((μ Cᶜ)⁻¹ • μ.restrict Cᶜ), o ∈ Cᶜ
    exact Measure.ae_smul_measure (ae_restrict_mem hC.compl) (μ Cᶜ)⁻¹
  have hηsupport : ∀ᵐ o ∂η, R < w o := by
    filter_upwards [hηmem] with o ho
    change ¬w o ≤ R at ho
    exact lt_of_not_ge ho
  let Good : Ω → Prop := fun o =>
    (R < w o ∧ 1 ≤ w o ∧ Integrable (r o) μ ∧
      (∫ y, r o y ∂ν) = -(∫ y in Cᶜ, r o y ∂μ) / d) ∧
    (0 ≤ w o ∧ Measurable (r o) ∧ Integrable (r o) ν ∧
      |∫ y, r o y ∂ν| ≤ c * w o ∧
      (∀ᵐ y ∂ν, |r o y| ≤ w o * w y))
  have hGood : ∀ᵐ o ∂η, Good o := by
    filter_upwards [hηac.ae_le hrows, hηac.ae_le hwone,
      hηac.ae_le hsections, hηsupport] with o ho hwo henvrow hsupport
    exact ⟨⟨hsupport, hwo, ho.1, ho.2.2.1⟩,
      ⟨zero_le_one.trans hwo, hrowm o, ho.2.1, ho.2.2.2,
        hνac.ae_le henvrow⟩⟩
  have hAll : ∀ᵐ a : ι → Ω ∂Measure.pi (fun _ : ι => η),
      ∀ i : ι, Good (a i) :=
    Filter.eventually_all.2 (fun i =>
      (Measure.quasiMeasurePreserving_eval (fun _ : ι => η) i).ae hGood)
  refine ⟨hgm, hrm, hC, hd, hb0, hc0, hR1, hR0, hνprob, hνac,
    hνW, hw2, hwν2, hwSecond, hM0, hηac, hηfinite, hηzero, hηprob, ?_⟩
  filter_upwards [hAll] with a ha
  have hA : ∀ i : ι, R < w (a i) ∧ 1 ≤ w (a i) ∧
      Integrable (r (a i)) μ ∧
      (∫ o, r (a i) o ∂ν) = -(∫ o in Cᶜ, r (a i) o ∂μ) / d :=
    fun i => (ha i).1
  have hvalid : validAnomalyVector ν r w c a := fun i => (ha i).2
  have hmom : interactionMomentBounds ν r w c R M a :=
    interaction_moments_of_valid ν r w c R M hc0 hR0 hwν2
      (hνW.mono (fun _ ho => ⟨zero_le_one.trans ho.1, ho.2⟩))
      hwSecond a hvalid
  refine ⟨hA, hvalid, hmom, ?_⟩
  calc
    (∫ o, interactionSum r a o ∂ν) = ∑ i : ι, ∫ o, r (a i) o ∂ν :=
      integral_finsetSum Finset.univ (fun i _ => (ha i).2.2.2.1)
    _ = ∑ i : ι, -(∫ o in Cᶜ, r (a i) o ∂μ) / d :=
      Finset.sum_congr rfl (fun i _ => (hA i).2.2.2)
    _ = -(∑ i : ι, ∫ o in Cᶜ, r (a i) o ∂μ) / d := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_neg_distrib]

theorem empty_interaction
    {Ω : Type*} [MeasurableSpace Ω]
    (ν η : Measure Ω) (r : Ω → Ω → ℝ) (w : Ω → ℝ)
    (c R M : ℝ) (a : Fin 0 → Ω) :
    interactionSum r a = (fun _ : Ω => 0) ∧
      anomalyEnvelope w a = 0 ∧ validAnomalyVector ν r w c a ∧
      interactionMomentBounds ν r w c R M a ∧
      (∫ o, interactionSum r a o ∂ν) = 0 ∧
      (∫ o, (interactionSum r a o) ^ 2 ∂ν) = 0 ∧
      (∫ o, (interactionSum r a o - (∫ y, interactionSum r a y ∂ν)) ^ 2 ∂ν) = 0 ∧
      Measure.pi (fun _ : Fin 0 => η) = Measure.dirac a
:= by
  classical
  have hsum : interactionSum r a = (fun _ : Ω => 0) := by
    funext o
    simp [interactionSum]
  have hell : anomalyEnvelope w a = 0 := by simp [anomalyEnvelope]
  have hvalid : validAnomalyVector ν r w c a := by
    intro i
    exact Fin.elim0 i
  have hzeroM : Measurable (fun _ : Ω => (0 : ℝ)) := measurable_const
  have hzeroI : Integrable (fun _ : Ω => (0 : ℝ)) ν := integrable_zero _ _ _
  have hzero2 : MemLp (fun _ : Ω => (0 : ℝ)) 2 ν :=
    (memLp_two_iff_integrable_sq hzeroM.aestronglyMeasurable).2 (by simpa using hzeroI)
  have hbounds : interactionMomentBounds ν r w c R M a := by
    simp [interactionMomentBounds, hsum, hell, hzeroM, hzeroI, hzero2]
  refine ⟨hsum, hell, hvalid, hbounds, ?_, ?_, ?_, ?_⟩
  · simp [hsum]
  · simp [hsum]
  · simp [hsum]
  · exact Measure.pi_of_empty (fun _ : Fin 0 => η) a

theorem anomaly_product_zero_of_null
    {ι Ω : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (w : Ω → ℝ) (R : ℝ)
    (hzero : μ {o : Ω | w o ≤ R}ᶜ = 0) :
    anomalyLaw μ w R = 0 ∧
      Measure.pi (fun _ : ι => anomalyLaw μ w R) = 0
:= by
  classical
  have hη : anomalyLaw μ w R = 0 := by
    unfold anomalyLaw
    rw [Measure.restrict_eq_zero.2 hzero]
    exact smul_zero _
  refine ⟨hη, ?_⟩
  rw [hη]
  apply measure_univ_eq_zero.mp
  rw [Measure.pi_univ]
  exact Finset.prod_eq_zero
    (Finset.mem_univ (Classical.choice (inferInstance : Nonempty ι))) (by simp)

theorem interaction_crossPairSum
    {n : ℕ} {Ω : Type*} (B : Finset (Fin n))
    (r : Ω → Ω → ℝ) (w : Ω → ℝ) (x : Fin n → Ω) :
    (∑ i ∈ B,
      interactionSum r (fun a : {a : Fin n // a ∈ anomaly B} => x a.1) (x i)) =
        crossPairSum B (fun a i : Fin n => r (x a) (x i)) ∧
      anomalyEnvelope w (fun a : {a : Fin n // a ∈ anomaly B} => x a.1) =
        anomalyWeight B (fun a : Fin n => w (x a))
:= by
  classical
  constructor
  · change (∑ i ∈ B,
      ∑ a : {a : Fin n // a ∈ anomaly B}, r (x a.1) (x i)) =
        crossPairSum B (fun a i : Fin n => r (x a) (x i))
    calc
      (∑ i ∈ B, ∑ a : {a : Fin n // a ∈ anomaly B}, r (x a.1) (x i)) =
          ∑ i ∈ B, ∑ a ∈ anomaly B, r (x a) (x i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Finset.sum_coe_sort (anomaly B) (fun a : Fin n => r (x a) (x i))
      _ = crossPairSum B (fun a i : Fin n => r (x a) (x i)) := by
        unfold crossPairSum
        rw [Finset.sum_comm]
  · exact Finset.sum_coe_sort (anomaly B) (fun a : Fin n => w (x a))

end

end Shao.OQ5.P41.InteractionSectionMoments
