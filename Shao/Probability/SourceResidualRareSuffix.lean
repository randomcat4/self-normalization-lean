import Shao.C2.AuxiliaryUnmarkedDampedMoments
import Shao.C2.AuxiliaryThirdMomentTruncation
import Shao.C2.AuxiliaryHigherMarkDamped
/- Mathematical candidates only. No formal implementation or Lean/AX authority.
   One quantitative real-suffix producer. The residual double comparison
   itself remains an explicitly unpaid target in a separate file. -/
import Shao.Probability.SourceSuffixMomentBudgets
import Shao.Probability.BoundedQuadraticTilt
import Shao.Probability.SourceMomentDomain
import Shao.C2.AuxiliaryEnergyTilt
import Shao.C2.AuxiliaryEnergyMoments
import Shao.C2.AuxiliaryEnergyCentered
import Shao.C2.AuxiliaryEnergyLaplace
import Shao.C2.AuxiliaryTiltedProductEnergy
import Shao.C2.AuxiliaryLowEnergyGaussian

import Shao.C2.AuxiliaryOriginalCutoffRare
import Shao.C2.AuxiliaryMarkedDeletion
import Shao.C2.AuxiliaryMarkedRareBase

import Shao.Probability.SourceSuffixScalarInterfaces

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace Shao.Probability.SourceResidualRareSuffix
open MeasureTheory ProbabilityTheory
open scoped BigOperators

private theorem rsb_rare_gaussian_damped_moments :
    let K : ℝ := (2 : ℝ) ^ 64
    let c1 : ℝ := (1 - Real.exp (-2)) / 16
    ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (B : ℝ), 0 < B → (∀ᵐ z : ℝ ∂rho, |z| ≤ B) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        ∀ x : ℝ, 16 ≤ x → ∀ t : ℕ,
          Nat.ceil (K * beta ^ 2 * (1 + x) ^ 6) ≤ t →
          ∀ s : ℝ, 0 < s → s ≤ 1 / (4 * beta ^ 2) →
            let P : Measure (Shao.Path t) := Measure.pi (fun _ : Fin t => rho)
            let T : Shao.Path t → ℝ := Shao.energy
            let d : Shao.Path t → ℝ := fun a => Shao.prefixSum a t
            let M : Shao.Path t → ℝ := fun a =>
              if ht : 0 < t then |a ⟨0, ht⟩| ^ 3 else 0
            let vx : ℝ := Real.sqrt (9 * x ^ 2 / 4 - 1)
            let Ax : ℝ := Real.sqrt (Shao.standardNormalTail (3 * x / 2)) +
              Real.exp (-x ^ 2)
            let marked : Shao.Path t → ℝ := fun a =>
              if 0 < T a ∧ (3 * x / 2) * Real.sqrt (T a) ≤ |d a| then
                M a * |d a| ^ k * Real.exp (-s * T a) else 0
            let unmarked : Shao.Path t → ℝ := fun a =>
              if 0 < T a ∧ vx * Real.sqrt (T a) ≤ |d a| then
                |d a| ^ k * Real.exp (-s * T a) else 0
            Integrable marked P ∧ Integrable unmarked P ∧
              (∫ a, marked a ∂P) ≤
                C * beta * Real.rpow s (-(k : ℝ) / 2) *
                  Real.exp (-c1 * s * ((t : ℝ) - 1)) * Ax ∧
              (∫ a, unmarked a ∂P) ≤
                C * Real.rpow s (-(k : ℝ) / 2) *
                  Real.exp (-c1 * s * (t : ℝ)) * Ax := by
  classical
  intro K c1 k
  let lambda : ℝ := (1 - Real.exp (-2)) / 16
  let c : ℝ := (1 - Real.exp (-2)) / 8
  obtain ⟨hlambda, hc, hcoordinate⟩ := raw_gaussian_damped_coordinate_factors
  obtain ⟨Cmark, hCmark, hmark⟩ := iid_marked_gaussian_damped_moments k
  obtain ⟨Cmark2, hCmark2, hmark2⟩ := iid_marked_gaussian_damped_moments (2 * k)
  obtain ⟨Crare, hCrare, hrare⟩ :=
    Shao.C2.AuxiliaryRareLaplace.auxiliary_original_cutoff_rare_laplace
  obtain ⟨Cbase, hCbase, hbase⟩ :=
    Shao.C2.AuxiliaryMarkedRareBase.auxiliary_original_cutoff_marked_rare_base
  have hKDrift : 8000000 * (1 + (128 : ℝ)) ^ 2 ≤ K := by norm_num [K]
  have hKBudget : 2 * (768 / (1 / 16 : ℝ)) ^ 2 ≤ K := by norm_num [K]
  have hRareFixed := hrare (1 / 16) (by norm_num) (by norm_num)
    128 (by norm_num) K hKDrift hKBudget
  have hBaseFixed := hbase (1 / 16) (by norm_num) (by norm_num)
    128 (by norm_num) K hKDrift hKBudget
  have hUnmarked :=
    Shao.C2.AuxiliaryUnmarkedDampedMoments.auxiliary_actual_unmarked_gaussian_damped_moments
  -- Proof-local weighted Cauchy: its two square-integrability inputs are
  -- supplied below by the old ordinary2k producer and new C12 actuala0.
  -- This uses the sqrt of the same weight; no square of a cubic mark occurs.
  have hWeightedCS (l : ℕ) (mu : Measure (Shao.Path l))
      (W f : Shao.Path l → ℝ) (hWm : Measurable W) (hfm : Measurable f)
      (hWnonneg : ∀ v, 0 ≤ W v) (R : Set (Shao.Path l)) (hR : MeasurableSet R)
      (hWf : Integrable (fun v => W v * (f v) ^ 2) mu)
      (hWR : Integrable (R.indicator W) mu) :
      (∫ v, R.indicator (fun a => W a * |f a|) v ∂mu) ≤
        Real.sqrt (∫ v, W v * (f v) ^ 2 ∂mu) *
          Real.sqrt (∫ v, R.indicator W v ∂mu) := by
    let F : Shao.Path l → ℝ := fun v => Real.sqrt (W v) * |f v|
    let G : Shao.Path l → ℝ := fun v => if v ∈ R then Real.sqrt (W v) else 0
    have hFm : Measurable F := hWm.sqrt.mul hfm.norm
    have hGm : Measurable G := Measurable.ite hR hWm.sqrt measurable_const
    have hFsq : (fun v => (F v) ^ 2) = fun v => W v * (f v) ^ 2 := by
      funext v
      dsimp [F]
      rw [mul_pow, Real.sq_sqrt (hWnonneg v), sq_abs]
    have hGsq : (fun v => (G v) ^ 2) = R.indicator W := by
      funext v
      by_cases hv : v ∈ R
      · simp only [G, if_pos hv, Set.indicator_of_mem hv,
          Real.sq_sqrt (hWnonneg v)]
      · simp [G, hv]
    have hFlp : MemLp F 2 mu :=
      (memLp_two_iff_integrable_sq hFm.aestronglyMeasurable).2 (hFsq.symm ▸ hWf)
    have hGlp : MemLp G 2 mu :=
      (memLp_two_iff_integrable_sq hGm.aestronglyMeasurable).2 (hGsq.symm ▸ hWR)
    have hFnonneg : ∀ v, 0 ≤ F v := fun v =>
      mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
    have hGnonneg : ∀ v, 0 ≤ G v := by
      intro v
      dsimp [G]
      split_ifs <;> positivity
    have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg
      (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ :
        (2 : ℝ).HolderConjugate 2)
      (ae_of_all _ hFnonneg) (ae_of_all _ hGnonneg)
      (by simpa using hFlp) (by simpa using hGlp)
    have hprod (v : Shao.Path l) : F v * G v =
        R.indicator (fun a => W a * |f a|) v := by
      by_cases hv : v ∈ R
      · simp only [F, G, if_pos hv, Set.indicator_of_mem hv]
        calc
          Real.sqrt (W v) * |f v| * Real.sqrt (W v) =
            (Real.sqrt (W v)) ^ 2 * |f v| := by ring
          _ = _ := by rw [Real.sq_sqrt (hWnonneg v)]
      · simp [G, hv]
    calc
      _ = ∫ v, F v * G v ∂mu :=
        integral_congr_ae (ae_of_all _ fun v => (hprod v).symm)
      _ ≤ _ := by
        have hcs' : (∫ v, F v * G v ∂mu) ≤
            Real.sqrt (∫ v, (F v) ^ 2 ∂mu) * Real.sqrt (∫ v, (G v) ^ 2 ∂mu) := by
          simpa only [Real.rpow_natCast, Real.rpow_ofNat, ← Real.sqrt_eq_rpow] using hcs
        rw [hFsq, hGsq] at hcs'
        exact hcs' 
  obtain ⟨Cu, hCu, hu⟩ := hUnmarked k
  obtain ⟨Cu2, hCu2, hu2⟩ := hUnmarked (2 * k)
  let S : ℝ := 1 + Cmark + Cmark2 + Cbase + Cu + Cu2 + Crare +
    (k.factorial : ℝ) * Real.exp 1
  let C : ℝ := 1000 * S ^ 2 * (2 : ℝ) ^ k
  have hS : 1 ≤ S := by
    dsimp [S]
    linarith [mul_nonneg (Nat.cast_nonneg k.factorial) (Real.exp_nonneg 1)]
  have hC : 0 < C := by dsimp [C, S]; positivity
  have hCgeS : S ≤ C := by
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    dsimp only [C]
    calc
      S ≤ S ^ 2 := by nlinarith only [hS]
      _ ≤ 1000 * S ^ 2 := by nlinarith only [sq_nonneg S]
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hp
  have hCMark : Cmark ≤ C := (show Cmark ≤ S by
      dsimp [S]
      linarith [mul_nonneg (Nat.cast_nonneg k.factorial) (Real.exp_nonneg 1)]).trans hCgeS
  have hCU : Cu ≤ C := (show Cu ≤ S by
      dsimp [S]
      linarith [mul_nonneg (Nat.cast_nonneg k.factorial) (Real.exp_nonneg 1)]).trans hCgeS
  have hCMark2 : Cmark2 ≤ C := (show Cmark2 ≤ S by
      dsimp [S]
      linarith [mul_nonneg (Nat.cast_nonneg k.factorial) (Real.exp_nonneg 1)]).trans hCgeS
  have hCBase : Cbase ≤ C := (show Cbase ≤ S by
      dsimp [S]
      linarith [mul_nonneg (Nat.cast_nonneg k.factorial) (Real.exp_nonneg 1)]).trans hCgeS
  have hCU2 : Cu2 ≤ C := (show Cu2 ≤ S by
      dsimp [S]
      linarith [mul_nonneg (Nat.cast_nonneg k.factorial) (Real.exp_nonneg 1)]).trans hCgeS
  have hCRare : Crare ≤ C := (show Crare ≤ S by
      dsimp [S]
      linarith [mul_nonneg (Nat.cast_nonneg k.factorial) (Real.exp_nonneg 1)]).trans hCgeS
  refine ⟨C, hC, ?_⟩
  intro rho hProb B hB hsupport hmean hsecond beta x hx t ht s hs hsb
    P T d M vx Ax marked unmarked
  have hmRaw := boundedQuadraticTilt_density_moments rho B 0 0 hB
    (show (0 : ℝ) ≤ 0 by rfl) hsupport
  rcases hmRaw with ⟨hW0, hZ0, hZlo0, hZhi0, hloglo0, hloghi0, hprob0,
    hac0, hca0, hbnd0, hw0, hiff0, hdensity0, hcmp0, hpowers, hrest0⟩
  have h2 : Integrable (fun z : ℝ => z ^ 2) rho := (hpowers 2).1
  have h3 : Integrable (fun z : ℝ => |z| ^ 3) rho := (hpowers 3).2.2.1
  have hbeta : 1 ≤ beta := by
    have h3r : Integrable (fun z : ℝ => Real.rpow |z| (3 : ℝ)) rho := by
      simpa only [Real.rpow_eq_pow, Real.rpow_natCast, Real.rpow_ofNat] using h3
    have hh := (original_moment_domain_coarse_guards 3 (by norm_num)
      (by norm_num) rho 1 (by norm_num) h2 (by simpa using hsecond) h3r).2.1
    simpa only [beta, Nat.cast_one, one_mul, Real.rpow_eq_pow, Real.one_rpow, Real.rpow_natCast, Real.rpow_ofNat] using hh
  have hbetapos : 0 < beta := lt_of_lt_of_le (by norm_num) hbeta
  have hbpos : 0 < 4 * beta ^ 2 := by positivity
  have hscoord : s ≤ 2 / (4 * beta ^ 2) := by
    have hh : (1 : ℝ) / (4 * beta ^ 2) ≤ 2 / (4 * beta ^ 2) := by
      apply div_le_div_of_nonneg_right (by norm_num) hbpos.le
    exact hsb.trans hh
  have hRank := Shao.C2.AuxiliarySourceCutoffPayment.auxiliary_original_cutoff_rank_payment
    beta 128 (1 / 16) K 0 x hbeta (by norm_num) (by norm_num) (by norm_num)
    (by linarith) hKDrift hKBudget t t ht (Or.inl rfl) (by simp only [zero_mul]; positivity)
  have hRetained : (1 / 2 : ℝ) ≤
      ∫ z : ℝ, if z ^ 2 ≤ 4 * beta ^ 2 then z ^ 2 else 0 ∂rho :=
    (Shao.C2.AuxiliaryThirdMomentTruncation.auxiliary_actual_third_moment_retains_half
      rho h2 h3 hsecond).2
  have htpos : 0 < t := hRank.2.1
  have ht4 : 4 ≤ t := hRank.1.trans ht
  have hTm : Measurable T := Shao.measurable_energy
  have hdm : Measurable d := Shao.measurable_prefixSum t
  have hMm : Measurable M := by
    have hcoord : Measurable (fun a : Shao.Path t => a ⟨0, htpos⟩) :=
      measurable_pi_apply _
    have habs : Measurable (fun a : Shao.Path t => |a ⟨0, htpos⟩|) := by
      simpa only [Real.norm_eq_abs] using hcoord.norm
    simpa only [M, dif_pos htpos] using habs.pow_const (3 : ℕ)
  have hsPow : 0 ≤ Real.rpow s (-(k : ℝ) / 2) := Real.rpow_nonneg hs.le _
  have hsPow2 : 0 ≤ Real.rpow s (-((2 * k : ℕ) : ℝ) / 2) := Real.rpow_nonneg hs.le _
  have hRmarked : MeasurableSet {v : Shao.Path t |
      0 < T v ∧ (3 * x / 2) * Real.sqrt (T v) ≤ |d v|} := by
    exact (measurableSet_lt measurable_const hTm).inter
      (measurableSet_le (hTm.sqrt.const_mul _) hdm.norm)
  have hRunmarked : MeasurableSet {v : Shao.Path t |
      0 < T v ∧ vx * Real.sqrt (T v) ≤ |d v|} := by
    exact (measurableSet_lt measurable_const hTm).inter
      (measurableSet_le (hTm.sqrt.const_mul _) hdm.norm)
  have hUi : Integrable (fun v : Shao.Path t =>
      |d v| ^ k * Real.exp (-s * T v)) P :=
    (hu rho h2 hmean hsecond t (4 * beta ^ 2) s hbpos hs hscoord).1
  have hMi : Integrable (fun v : Shao.Path t =>
      M v * |d v| ^ k * Real.exp (-s * T v)) P := by
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt htpos)
    have hm := (hmark rho h2 hmean hsecond l (4 * beta ^ 2) s
      hbpos hs hscoord).1
    simpa [P, T, d, M] using hm
  have hMarkedIntegrable : Integrable marked P := by
    apply (hMi.indicator hRmarked).congr
    exact ae_of_all _ fun v => by
      by_cases hv : 0 < T v ∧ (3 * x / 2) * Real.sqrt (T v) ≤ |d v|
      · simp [marked, hv]
      · simp [marked, hv]
  have hUnmarkedIntegrable : Integrable unmarked P := by
    apply (hUi.indicator hRunmarked).congr
    exact ae_of_all _ fun v => by
      by_cases hv : 0 < T v ∧ vx * Real.sqrt (T v) ≤ |d v|
      · simp [unmarked, hv]
      · simp [unmarked, hv]
  have hA3i : Integrable (fun z : ℝ =>
      |z| ^ 3 * Real.exp (-(s / 2) * z ^ 2)) rho :=
    (hcoordinate rho h2 hmean hsecond (4 * beta ^ 2) s hbpos hs hscoord).1
  have hA3 : (∫ z : ℝ, |z| ^ 3 * Real.exp (-(s / 2) * z ^ 2) ∂rho) ≤ beta := by
    apply integral_mono hA3i h3
    intro z
    apply mul_le_of_le_one_right (pow_nonneg (abs_nonneg z) 3)
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg z])
  have hMarkedOrdinary :
      (∫ v : Shao.Path t, M v * |d v| ^ k * Real.exp (-s * T v) ∂P) ≤
        Cmark * beta * Real.rpow s (-(k : ℝ) / 2) *
          Real.exp (-c * s * ((t : ℝ) - 1)) := by
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt htpos)
    have hh := (hmark rho h2 hmean hsecond l (4 * beta ^ 2) s
      hbpos hs hscoord).2
    have hstep : (∫ v : Shao.Path (l + 1),
        M v * |d v| ^ k * Real.exp (-s * T v) ∂P) ≤
        Cmark * Real.rpow s (-(k : ℝ) / 2) *
          (∫ z : ℝ, |z| ^ 3 * Real.exp (-(s / 2) * z ^ 2) ∂rho) *
            Real.exp (-c * s * (l : ℝ)) := by
      simpa only [P, T, d, M, dif_pos (Nat.succ_pos l), Nat.succ_eq_add_one,
        Fin.mk_zero, if_pos hRetained] using hh
    calc
      _ ≤ Cmark * Real.rpow s (-(k : ℝ) / 2) * beta *
          Real.exp (-c * s * (l : ℝ)) := by
        apply hstep.trans
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hA3 (by positivity)) (Real.exp_nonneg _)
      _ = _ := by push_cast; ring
  have hMarkedOrdinary2 :
      (∫ v : Shao.Path t, M v * |d v| ^ (2 * k) * Real.exp (-s * T v) ∂P) ≤
        Cmark2 * beta * Real.rpow s (-((2 * k : ℕ) : ℝ) / 2) *
          Real.exp (-c * s * ((t : ℝ) - 1)) := by
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt htpos)
    have hh := (hmark2 rho h2 hmean hsecond l (4 * beta ^ 2) s
      hbpos hs hscoord).2
    have hstep : (∫ v : Shao.Path (l + 1),
        M v * |d v| ^ (2 * k) * Real.exp (-s * T v) ∂P) ≤
        Cmark2 * Real.rpow s (-((2 * k : ℕ) : ℝ) / 2) *
          (∫ z : ℝ, |z| ^ 3 * Real.exp (-(s / 2) * z ^ 2) ∂rho) *
            Real.exp (-c * s * (l : ℝ)) := by
      simpa only [P, T, d, M, dif_pos (Nat.succ_pos l), Nat.succ_eq_add_one,
        Fin.mk_zero, if_pos hRetained] using hh
    calc
      _ ≤ Cmark2 * Real.rpow s (-((2 * k : ℕ) : ℝ) / 2) * beta *
          Real.exp (-c * s * (l : ℝ)) := by
        apply hstep.trans
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hA3 (by positivity)) (Real.exp_nonneg _)
      _ = _ := by push_cast; ring
  have hUnmarkedOrdinary :
      (∫ v : Shao.Path t, |d v| ^ k * Real.exp (-s * T v) ∂P) ≤
        Cu * Real.rpow s (-(k : ℝ) / 2) * Real.exp (-c * s * (t : ℝ)) := by
    simpa only [if_pos hRetained] using
      (hu rho h2 hmean hsecond t (4 * beta ^ 2) s hbpos hs hscoord).2
  have hUnmarkedOrdinary2 :
      (∫ v : Shao.Path t, |d v| ^ (2 * k) * Real.exp (-s * T v) ∂P) ≤
        Cu2 * Real.rpow s (-((2 * k : ℕ) : ℝ) / 2) *
          Real.exp (-c * s * (t : ℝ)) := by
    simpa only [if_pos hRetained] using
      (hu2 rho h2 hmean hsecond t (4 * beta ^ 2) s hbpos hs hscoord).2
  have hPsi0 : 0 ≤ Shao.standardNormalTail ((3 / 2) * x) :=
    (Shao.standardNormalTail_basic.2.2.1 _).1.le
  have hAx0 : 0 ≤ Ax := by dsimp [Ax]; positivity
  have hPsiAx : Shao.standardNormalTail ((3 / 2) * x) ≤ Ax ^ 2 := by
    have heq : (3 / 2 : ℝ) * x = 3 * x / 2 := by ring
    have hh : Real.sqrt (Shao.standardNormalTail ((3 / 2) * x)) ≤ Ax := by
      dsimp [Ax]
      rw [heq]
      exact le_add_of_nonneg_right (Real.exp_nonneg _)
    have hh0 := Real.sqrt_nonneg (Shao.standardNormalTail ((3 / 2) * x))
    have hsq := sq_le_sq₀ hh0 hAx0
    exact (Real.sq_sqrt hPsi0).symm.le.trans (hsq.mpr hh)
  have hSqrtBound (A B b u : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
      (hb : 0 ≤ b) (hu : 0 ≤ u) (hAC : A ≤ C) (hBC : B ≤ C) :
      Real.sqrt (A * b * Real.rpow s (-((2 * k : ℕ) : ℝ) / 2) * Real.exp (-c * u)) *
        Real.sqrt (B * b * Real.exp (-(7 / 8) * u) *
          Shao.standardNormalTail ((3 / 2) * x)) ≤
        C * b * Real.rpow s (-(k : ℝ) / 2) * Real.exp (-c1 * u) * Ax := by
    have hap : 0 ≤ Real.rpow s (-(k : ℝ) / 2) := Real.rpow_nonneg hs.le _
    have hpow : (Real.rpow s (-(k : ℝ) / 2)) ^ 2 =
        Real.rpow s (-((2 * k : ℕ) : ℝ) / 2) := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_mul_natCast hs.le]
      congr 1
      push_cast
      ring
    have hexp : (Real.exp (-c1 * u)) ^ 2 = Real.exp (-c * u) := by
      rw [← Real.exp_nat_mul]
      congr 1
      dsimp [c1, c]
      ring
    have heSmall : Real.exp (-(7 / 8) * u) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    have hAB : A * B ≤ C ^ 2 := by
      calc
        A * B ≤ C * B := mul_le_mul_of_nonneg_right hAC hB
        _ ≤ C * C := mul_le_mul_of_nonneg_left hBC hC.le
        _ = _ := by ring
    have hap2 : 0 ≤ Real.rpow s (-((2 * k : ℕ) : ℝ) / 2) := Real.rpow_nonneg hs.le _
    have hfirst : 0 ≤ A * b * Real.rpow s (-((2 * k : ℕ) : ℝ) / 2) *
        Real.exp (-c * u) := by positivity
    have hsecond : 0 ≤ B * b * Real.exp (-(7 / 8) * u) *
        Shao.standardNormalTail ((3 / 2) * x) := by positivity
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (by positivity : 0 ≤ C * b * Real.rpow s (-(k : ℝ) / 2) *
        Real.exp (-c1 * u) * Ax)).1
    rw [mul_pow, Real.sq_sqrt hfirst, Real.sq_sqrt hsecond]
    calc
      _ = (A * B) * b ^ 2 * (Real.rpow s (-(k : ℝ) / 2)) ^ 2 *
          Real.exp (-c * u) * Real.exp (-(7 / 8) * u) *
            Shao.standardNormalTail ((3 / 2) * x) := by rw [← hpow]; ring
      _ ≤ C ^ 2 * b ^ 2 * (Real.rpow s (-(k : ℝ) / 2)) ^ 2 *
          Real.exp (-c * u) * 1 * Ax ^ 2 := by gcongr
      _ = _ := by rw [← hexp]; ring
  let Rbase : Set (Shao.Path t) := {v |
    ((3 / 2 : ℝ) * x) * Real.sqrt (T v) ≤ |d v|}
  let Wbase : Shao.Path t → ℝ := fun v => M v * Real.exp (-s * T v)
  let Rzero : Set (Shao.Path t) := {v |
    0 < T v ∧ vx * Real.sqrt (T v) ≤ |d v|}
  let Wzero : Shao.Path t → ℝ := fun v => Real.exp (-s * T v)
  have hRbase : MeasurableSet Rbase := by
    exact measurableSet_le (hTm.sqrt.const_mul _) hdm.norm
  have hWbase : Measurable Wbase := by
    exact hMm.mul ((hTm.const_mul (-s)).exp)
  have hWbaseNonneg : ∀ v, 0 ≤ Wbase v := by
    intro v
    dsimp [Wbase, M]
    split_ifs <;> positivity
  have hBaseLow (hLow : s * (t : ℝ) ≤ 128 * x ^ 2) :
      Integrable (Rbase.indicator Wbase) P ∧
      (∫ v, Rbase.indicator Wbase v ∂P) ≤
        Cbase * beta * Real.exp (-(7 / 8) * s * ((t : ℝ) - 1)) *
          Shao.standardNormalTail ((3 / 2) * x) := by
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt htpos)
    have hh := hBaseFixed rho h2 h3 hmean hsecond s hs.le x (by linarith) l ht hLow
    simpa [P, T, d, M, Rbase, Wbase, Nat.cast_add, Nat.cast_one] using hh
  have hZeroLow (hLow : s * (t : ℝ) ≤ 128 * x ^ 2) :
      Integrable (Rzero.indicator Wzero) P ∧
      (∫ v, Rzero.indicator Wzero v ∂P) ≤
        Crare * Real.exp (-(7 / 8) * s * (t : ℝ)) *
          Shao.standardNormalTail ((3 / 2) * x) := by
    have hh := hRareFixed rho h2 h3 hmean hsecond s hs.le x (by linarith)
      t t ht (Or.inl rfl) hLow
    have hvx : vx = Real.sqrt ((9 / 4 : ℝ) * x ^ 2 - 1) := by
      dsimp [vx]
      congr 1
      ring
    simpa only [P, T, d, Rzero, Wzero, hvx] using hh
  have hMi2 : Integrable (fun v : Shao.Path t =>
      M v * |d v| ^ (2 * k) * Real.exp (-s * T v)) P := by
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt htpos)
    have hm := (hmark2 rho h2 hmean hsecond l (4 * beta ^ 2) s
      hbpos hs hscoord).1
    simpa [P, T, d, M] using hm
  have hUi2 : Integrable (fun v : Shao.Path t =>
      |d v| ^ (2 * k) * Real.exp (-s * T v)) P :=
    (hu2 rho h2 hmean hsecond t (4 * beta ^ 2) s hbpos hs hscoord).1
  have hSquareWeight : Integrable (fun v : Shao.Path t =>
      Wbase v * (|d v| ^ k) ^ 2) P := by
    apply hMi2.congr
    exact ae_of_all _ fun v => by
      have hp : (|d v| ^ k) ^ 2 = |d v| ^ (2 * k) := by
        rw [← pow_mul]
        congr 1
        omega
      change M v * |d v| ^ (2 * k) * Real.exp (-s * T v) =
        Wbase v * (|d v| ^ k) ^ 2
      rw [hp]
      dsimp only [Wbase]
      ring
  have hSquareZero : Integrable (fun v : Shao.Path t =>
      Wzero v * (|d v| ^ k) ^ 2) P := by
    apply hUi2.congr
    exact ae_of_all _ fun v => by
      have hp : (|d v| ^ k) ^ 2 = |d v| ^ (2 * k) := by
        rw [← pow_mul]
        congr 1
        omega
      change |d v| ^ (2 * k) * Real.exp (-s * T v) =
        Wzero v * (|d v| ^ k) ^ 2
      rw [hp]
      dsimp only [Wzero]
      ring
  have hMarkedCS (hLow : s * (t : ℝ) ≤ 128 * x ^ 2) :=
    hWeightedCS t P Wbase (fun v => |d v| ^ k) hWbase
      (hdm.norm.pow_const k) hWbaseNonneg Rbase hRbase hSquareWeight (hBaseLow hLow).1
  have hUnmarkedCS (hLow : s * (t : ℝ) ≤ 128 * x ^ 2) :=
    hWeightedCS t P Wzero (fun v => |d v| ^ k)
      ((hTm.const_mul (-s)).exp) (hdm.norm.pow_const k)
      (fun v => Real.exp_nonneg _) Rzero hRunmarked hSquareZero (hZeroLow hLow).1
  have htR : (4 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht4
  have hLowMarked (hLow : s * (t : ℝ) ≤ 128 * x ^ 2) :
      (∫ v, marked v ∂P) ≤ C * beta * Real.rpow s (-(k : ℝ) / 2) *
        Real.exp (-c1 * s * ((t : ℝ) - 1)) * Ax := by
    have hFull : Integrable (fun v : Shao.Path t => Wbase v * |(|d v| ^ k)|) P := by
      apply hMi.congr
      exact ae_of_all _ fun v => by
        change M v * |d v| ^ k * Real.exp (-s * T v) = Wbase v * |(|d v| ^ k)|
        rw [abs_of_nonneg (pow_nonneg (abs_nonneg (d v)) k)]
        dsimp only [Wbase]
        ring
    have hdom : (∫ v, marked v ∂P) ≤
        ∫ v, Rbase.indicator (fun a => Wbase a * |(|d a| ^ k)|) v ∂P := by
      apply integral_mono hMarkedIntegrable (hFull.indicator hRbase)
      intro v
      by_cases hh : 0 < T v ∧ (3 * x / 2) * Real.sqrt (T v) ≤ |d v|
      · have hr : v ∈ Rbase := by
          dsimp [Rbase]
          convert hh.2 using 1 <;> ring
        simp only [marked, if_pos hh, Set.indicator_of_mem hr]
        rw [abs_of_nonneg (pow_nonneg (abs_nonneg (d v)) k)]
        dsimp [Wbase]
        exact le_of_eq (by ring)
      · simp only [marked, if_neg hh]
        by_cases hr : v ∈ Rbase
        · rw [Set.indicator_of_mem hr]
          exact mul_nonneg (hWbaseNonneg v) (abs_nonneg _)
        · simp [hr]
    have hI2 : (∫ v : Shao.Path t, Wbase v * (|d v| ^ k) ^ 2 ∂P) ≤
        Cmark2 * beta * Real.rpow s (-((2 * k : ℕ) : ℝ) / 2) *
          Real.exp (-c * s * ((t : ℝ) - 1)) := by
      convert hMarkedOrdinary2 using 1
      congr 1
      funext v
      dsimp [Wbase]
      rw [← pow_mul]
      simp only [Nat.mul_comm k 2]
      ring
    calc
      _ ≤ ∫ v, Rbase.indicator (fun a => Wbase a * |(|d a| ^ k)|) v ∂P := hdom
      _ ≤ Real.sqrt (∫ v, Wbase v * (|d v| ^ k) ^ 2 ∂P) *
          Real.sqrt (∫ v, Rbase.indicator Wbase v ∂P) := hMarkedCS hLow
      _ ≤ Real.sqrt (Cmark2 * beta * Real.rpow s (-((2 * k : ℕ) : ℝ) / 2) *
            Real.exp (-c * s * ((t : ℝ) - 1))) *
          Real.sqrt (Cbase * beta * Real.exp (-(7 / 8) * s * ((t : ℝ) - 1)) *
            Shao.standardNormalTail ((3 / 2) * x)) :=
        mul_le_mul (Real.sqrt_le_sqrt hI2) (Real.sqrt_le_sqrt (hBaseLow hLow).2)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ ≤ _ := by
        simpa only [mul_assoc] using hSqrtBound Cmark2 Cbase beta
          (s * ((t : ℝ) - 1)) hCmark2.le hCbase.le hbetapos.le
          (mul_nonneg hs.le (by linarith)) hCMark2 hCBase
  have hLowUnmarked (hLow : s * (t : ℝ) ≤ 128 * x ^ 2) :
      (∫ v, unmarked v ∂P) ≤ C * Real.rpow s (-(k : ℝ) / 2) *
        Real.exp (-c1 * s * (t : ℝ)) * Ax := by
    have heq : (∫ v, unmarked v ∂P) =
        ∫ v, Rzero.indicator (fun a => Wzero a * |(|d a| ^ k)|) v ∂P := by
      apply integral_congr_ae
      exact ae_of_all _ fun v => by
        by_cases hv : 0 < T v ∧ vx * Real.sqrt (T v) ≤ |d v|
        · simp only [unmarked, Rzero, Set.indicator_apply, Set.mem_setOf_eq, if_pos hv]
          rw [abs_of_nonneg (pow_nonneg (abs_nonneg (d v)) k)]
          dsimp only [Wzero]
          ring
        · simp only [unmarked, Rzero, Set.indicator_apply, Set.mem_setOf_eq, if_neg hv]
    have hI2 : (∫ v : Shao.Path t, Wzero v * (|d v| ^ k) ^ 2 ∂P) ≤
        Cu2 * Real.rpow s (-((2 * k : ℕ) : ℝ) / 2) *
          Real.exp (-c * s * (t : ℝ)) := by
      convert hUnmarkedOrdinary2 using 1
      congr 1
      funext v
      dsimp [Wzero]
      rw [← pow_mul]
      simp only [Nat.mul_comm k 2]
      ring
    calc
      _ = ∫ v, Rzero.indicator (fun a => Wzero a * |(|d a| ^ k)|) v ∂P := heq
      _ ≤ Real.sqrt (∫ v, Wzero v * (|d v| ^ k) ^ 2 ∂P) *
          Real.sqrt (∫ v, Rzero.indicator Wzero v ∂P) := hUnmarkedCS hLow
      _ ≤ Real.sqrt (Cu2 * Real.rpow s (-((2 * k : ℕ) : ℝ) / 2) *
            Real.exp (-c * s * (t : ℝ))) *
          Real.sqrt (Crare * Real.exp (-(7 / 8) * s * (t : ℝ)) *
            Shao.standardNormalTail ((3 / 2) * x)) :=
        mul_le_mul (Real.sqrt_le_sqrt hI2) (Real.sqrt_le_sqrt (hZeroLow hLow).2)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ ≤ _ := by
        simpa only [mul_one, mul_assoc] using hSqrtBound Cu2 Crare 1
          (s * (t : ℝ)) hCu2.le hCrare.le (by norm_num)
          (mul_nonneg hs.le (Nat.cast_nonneg t)) hCU2 hCRare
  have hC1Lower : (1 / 32 : ℝ) ≤ c1 := by
    have he : Real.exp (-2) ≤ (1 / 2 : ℝ) := by
      have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
        (show 2 ≤ Real.exp 2 by linarith [Real.add_one_le_exp (2 : ℝ)])
      simpa only [one_div, Real.exp_neg] using hi
    dsimp [c1]
    linarith only [he]
  have hHighExp (v : ℝ) (hv : (t : ℝ) / 2 ≤ v)
      (hHigh : 128 * x ^ 2 < s * (t : ℝ)) :
      Real.exp (-c * s * v) ≤ Real.exp (-c1 * s * v) * Real.exp (-x ^ 2) := by
    have hsv : s * (t : ℝ) / 2 ≤ s * v := by
      nlinarith only [mul_le_mul_of_nonneg_left hv hs.le]
    have hrate : x ^ 2 ≤ c1 * (s * v) := by
      have hh := mul_le_mul_of_nonneg_right hC1Lower
        (mul_nonneg hs.le (show 0 ≤ v by linarith))
      nlinarith only [hh, hHigh, hsv, sq_nonneg x]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hcc : c = 2 * c1 := by dsimp [c, c1]; ring
    rw [hcc]
    nlinarith only [hrate]
  have hAxExp : Real.exp (-x ^ 2) ≤ Ax := by
    dsimp [Ax]
    exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have hDomMarkedOrdinary : (∫ v, marked v ∂P) ≤
      ∫ v : Shao.Path t, M v * |d v| ^ k * Real.exp (-s * T v) ∂P := by
    apply integral_mono hMarkedIntegrable hMi
    intro v
    dsimp only [marked]
    split_ifs
    · exact le_rfl
    · dsimp [M]
      split_ifs <;> positivity
  have hDomUnmarkedOrdinary : (∫ v, unmarked v ∂P) ≤
      ∫ v : Shao.Path t, |d v| ^ k * Real.exp (-s * T v) ∂P := by
    apply integral_mono hUnmarkedIntegrable hUi
    intro v
    dsimp only [unmarked]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (pow_nonneg (abs_nonneg _) _) (Real.exp_nonneg _)
  refine ⟨hMarkedIntegrable, hUnmarkedIntegrable, ?_, ?_⟩
  · by_cases hLow : s * (t : ℝ) ≤ 128 * x ^ 2
    · exact hLowMarked hLow
    · have he := hHighExp ((t : ℝ) - 1) (by linarith) (lt_of_not_ge hLow)
      calc
        _ ≤ Cmark * beta * Real.rpow s (-(k : ℝ) / 2) *
            Real.exp (-c * s * ((t : ℝ) - 1)) :=
          hDomMarkedOrdinary.trans hMarkedOrdinary
        _ ≤ C * beta * Real.rpow s (-(k : ℝ) / 2) *
            (Real.exp (-c1 * s * ((t : ℝ) - 1)) * Real.exp (-x ^ 2)) := by
          apply mul_le_mul _ he (Real.exp_nonneg _) (mul_nonneg (mul_nonneg hC.le hbetapos.le) hsPow)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCMark hbetapos.le) hsPow
        _ ≤ _ := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hAxExp
            (mul_nonneg (mul_nonneg (mul_nonneg hC.le hbetapos.le) hsPow)
              (Real.exp_nonneg _))
  · by_cases hLow : s * (t : ℝ) ≤ 128 * x ^ 2
    · exact hLowUnmarked hLow
    · have he := hHighExp (t : ℝ) (by linarith) (lt_of_not_ge hLow)
      calc
        _ ≤ Cu * Real.rpow s (-(k : ℝ) / 2) *
            Real.exp (-c * s * (t : ℝ)) := hDomUnmarkedOrdinary.trans hUnmarkedOrdinary
        _ ≤ C * Real.rpow s (-(k : ℝ) / 2) *
            (Real.exp (-c1 * s * (t : ℝ)) * Real.exp (-x ^ 2)) := by
          apply mul_le_mul _ he (Real.exp_nonneg _) (mul_nonneg hC.le hsPow)
          exact mul_le_mul_of_nonneg_right hCU hsPow
        _ ≤ _ := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hAxExp
            (mul_nonneg (mul_nonneg hC.le hsPow) (Real.exp_nonneg _))


private theorem rsb_rare_cutoff_inverse_moments :
    let K : ℝ := (2 : ℝ) ^ 64
    ∀ p q : ℕ, (q = 1 ∨ q = 3) → ∃ C : ℝ, 0 < C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (B : ℝ), 0 < B → (∀ᵐ z : ℝ ∂rho, |z| ≤ B) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        ∀ x : ℝ, 16 ≤ x → ∀ t : ℕ,
          Nat.ceil (K * beta ^ 2 * (1 + x) ^ 6) ≤ t →
          let h0 : ℝ := 4 * beta ^ 2
          let P : Measure (Shao.Path t) := Measure.pi (fun _ : Fin t => rho)
          let T : Shao.Path t → ℝ := Shao.energy
          let d : Shao.Path t → ℝ := fun a => Shao.prefixSum a t
          let M : Shao.Path t → ℝ := fun a =>
            if ht : 0 < t then |a ⟨0, ht⟩| ^ 3 else 0
          let D : Shao.Path t → ℝ := fun a =>
            if 0 < T a then 1 + |d a| / Real.sqrt (T a) else 1
          let vx : ℝ := Real.sqrt (9 * x ^ 2 / 4 - 1)
          let Ax : ℝ := Real.sqrt (Shao.standardNormalTail (3 * x / 2)) +
            Real.exp (-x ^ 2)
          let marked : Shao.Path t → ℝ := fun a =>
            if 0 < T a ∧ h0 ≤ T a ∧
                (3 * x / 2) * Real.sqrt (T a) ≤ |d a| then
              M a / (Real.sqrt (T a)) ^ q * D a ^ p else 0
          let unmarked : Shao.Path t → ℝ := fun a =>
            if 0 < T a ∧ h0 ≤ T a ∧ vx * Real.sqrt (T a) ≤ |d a| then
              1 / (Real.sqrt (T a)) ^ q * D a ^ p else 0
          Integrable marked P ∧ Integrable unmarked P ∧
            (∫ a, marked a ∂P) ≤
              C * beta * Real.rpow (t : ℝ) (-(q : ℝ) / 2) * Ax ∧
            (∫ a, unmarked a ∂P) ≤
              C * Real.rpow (t : ℝ) (-(q : ℝ) / 2) * Ax := by
  classical
  intro K p q hq
  choose Cmoment hCmoment hmomentFamily using rsb_rare_gaussian_damped_moments
  let C0 : ℝ := Cmoment 0
  let Cp : ℝ := Cmoment p
  have hC0 : 0 < C0 := hCmoment 0
  have hCp : 0 < Cp := hCmoment p
  have hqpos : 0 < (q : ℝ) := by rcases hq with rfl | rfl <;> norm_num
  have ha0 : 0 < (q : ℝ) / 2 := by positivity
  have hap : 0 < ((q : ℝ) + (p : ℝ)) / 2 := by positivity
  have hc1 : 0 < (1 - Real.exp (-2)) / 16 := by
    have hh : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    exact div_pos (sub_pos.mpr hh) (by norm_num)
  -- Proof-local inverse transfer. Its damped section hypotheses are supplied
  -- by the already frozen rare moment helper, not by the target inverse bound.
  have hInverse (l : ℕ) (P : Measure (Shao.Path l)) [IsProbabilityMeasure P]
      (T W : Shao.Path l → ℝ) (hTm : Measurable T) (hWm : Measurable W)
      (hWnonneg : ∀ v, 0 ≤ W v) (b alpha kappa A rate : ℝ)
      (hb : 0 < b) (ha : 0 < alpha) (hdelta : 0 < alpha - kappa)
      (hA : 0 ≤ A) (hrate : 0 < rate)
      (hDamped : ∀ s : ℝ, s ∈ Set.Ioo 0 (1 / b) →
        Integrable (fun v => W v * Real.exp (-s * T v)) P ∧
        (∫ v, W v * Real.exp (-s * T v) ∂P) ≤
          A * Real.rpow s (-kappa) * Real.exp (-rate * s)) :
      let selected : Shao.Path l → ℝ := fun v =>
        if b ≤ T v then W v * Real.rpow (T v) (-alpha) else 0
      Integrable selected P ∧ (∫ v, selected v ∂P) ≤
        Real.exp 1 * alpha * A * Real.rpow (1 / rate) (alpha - kappa) *
          Real.Gamma (alpha - kappa) := by
    intro selected
    let I : Set ℝ := Set.Ioo 0 (1 / b)
    let muI : Measure ℝ := volume.restrict I
    let cutW : Shao.Path l → ℝ := fun v => if b ≤ T v then W v else 0
    let K : ℝ × Shao.Path l → ℝ := fun z =>
      Real.rpow z.1 (alpha - 1) * cutW z.2 * Real.exp (-z.1 * T z.2)
    have hCutSet : MeasurableSet {v : Shao.Path l | b ≤ T v} :=
      measurableSet_le measurable_const hTm
    have hCutm : Measurable cutW := Measurable.ite hCutSet hWm measurable_const
    have hCutnonneg : ∀ v, 0 ≤ cutW v := by
      intro v
      dsimp [cutW]
      split_ifs
      · exact hWnonneg v
      · exact le_rfl
    have hKm : Measurable K := by dsimp [K]; fun_prop
    have hGamma :=
      Shao.Probability.SourceSuffixScalarInterfaces.gamma_kernel
        (alpha - kappa) rate hdelta hrate
    have hScalar : IntegrableOn (fun s : ℝ =>
        A * Real.rpow s (alpha - kappa - 1) * Real.exp (-rate * s)) I := by
      have hh := hGamma.1.mono_set (show I ⊆ Set.Ioi 0 from fun s hs => hs.1)
      apply (hh.const_mul A).congr
      exact ae_of_all _ fun s => by ring
    have hSection (s : ℝ) (hs : s ∈ I) : Integrable (fun v => K (s, v)) P := by
      have hh := (hDamped s hs).1.indicator hCutSet
      apply (hh.const_mul (Real.rpow s (alpha - 1))).congr
      exact ae_of_all _ fun v => by
        dsimp [K, cutW]
        by_cases hv : b ≤ T v <;> simp [hv, Set.indicator_apply] <;> ring
    have hSectionBound (s : ℝ) (hs : s ∈ I) :
        (∫ v, ‖K (s, v)‖ ∂P) ≤
          A * Real.rpow s (alpha - kappa - 1) * Real.exp (-rate * s) := by
      have hsp : 0 ≤ Real.rpow s (alpha - 1) := Real.rpow_nonneg hs.1.le _
      have hD := hDamped s hs
      have hCutI : Integrable (fun v => cutW v * Real.exp (-s * T v)) P := by
        apply (hD.1.indicator hCutSet).congr
        exact ae_of_all _ fun v => by
          dsimp [cutW]
          by_cases hv : b ≤ T v <;> simp [hv, Set.indicator_apply]
      have hCutInt : (∫ v, cutW v * Real.exp (-s * T v) ∂P) ≤
          ∫ v, W v * Real.exp (-s * T v) ∂P := by
        apply integral_mono hCutI hD.1
        intro v
        dsimp [cutW]
        split_ifs
        · exact le_rfl
        · simpa only [zero_mul] using mul_nonneg (hWnonneg v) (Real.exp_nonneg _)
      calc
        _ = ∫ v, Real.rpow s (alpha - 1) *
            (cutW v * Real.exp (-s * T v)) ∂P := by
          apply integral_congr_ae
          exact ae_of_all _ fun v => by
            change ‖K (s, v)‖ = Real.rpow s (alpha - 1) *
              (cutW v * Real.exp (-s * T v))
            have hKnonneg : 0 ≤ K (s, v) :=
              mul_nonneg (mul_nonneg hsp (hCutnonneg v)) (Real.exp_nonneg _)
            rw [Real.norm_eq_abs, abs_of_nonneg hKnonneg]
            dsimp only [K]
            ring
        _ = Real.rpow s (alpha - 1) *
            ∫ v, cutW v * Real.exp (-s * T v) ∂P := integral_const_mul _ _
        _ ≤ Real.rpow s (alpha - 1) *
            (A * Real.rpow s (-kappa) * Real.exp (-rate * s)) :=
          mul_le_mul_of_nonneg_left (hCutInt.trans hD.2) hsp
        _ = _ := by
          calc
            _ = A * (Real.rpow s (alpha - 1) * Real.rpow s (-kappa)) *
                Real.exp (-rate * s) := by ring
            _ = _ := by
              simp only [Real.rpow_eq_pow]
              rw [← Real.rpow_add hs.1]
              congr 2
              ring
    have hNormm : AEStronglyMeasurable
        (fun s : ℝ => ∫ v, ‖K (s, v)‖ ∂P) muI :=
      hKm.aestronglyMeasurable.norm.integral_prod_right'
    have hNormI : Integrable (fun s : ℝ => ∫ v, ‖K (s, v)‖ ∂P) muI := by
      apply hScalar.mono' hNormm
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun v => norm_nonneg _)]
      exact hSectionBound s hs
    have hJoint : Integrable K (muI.prod P) := by
      apply (integrable_prod_iff hKm.aestronglyMeasurable).2
      refine ⟨?_, hNormI⟩
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact hSection s hs
    have hSelm : Measurable selected :=
      Measurable.ite hCutSet (hWm.mul (hTm.pow_const (-alpha))) measurable_const
    have hSelnonneg : ∀ v, 0 ≤ selected v := by
      intro v
      dsimp [selected]
      split_ifs with hv
      · exact mul_nonneg (hWnonneg v) (Real.rpow_nonneg (hb.le.trans hv) _)
      · exact le_rfl
    have hPoint (v : Shao.Path l) : selected v ≤
        Real.exp 1 * alpha * ∫ s : ℝ, K (s, v) ∂muI := by
      by_cases hv : b ≤ T v
      · have hi :=
          Shao.Probability.SourceSuffixScalarInterfaces.inverse_laplace
            alpha (T v) b ha hb hv
        calc
          _ = W v * Real.rpow (T v) (-alpha) := by simp only [selected, if_pos hv]
          _ ≤ W v * (Real.exp 1 * alpha *
              ∫ s : ℝ in Set.Ioo 0 (1 / b),
                Real.rpow s (alpha - 1) * Real.exp (-s * T v)) :=
            mul_le_mul_of_nonneg_left hi (hWnonneg v)
          _ = _ := by
            have hPull : (∫ s : ℝ, K (s, v) ∂muI) =
                W v * ∫ s : ℝ in I,
                  Real.rpow s (alpha - 1) * Real.exp (-s * T v) := by
              calc
                _ = ∫ s : ℝ in I, W v *
                    (Real.rpow s (alpha - 1) * Real.exp (-s * T v)) := by
                  apply integral_congr_ae
                  exact ae_of_all _ fun s => by
                    simp only [K, cutW, if_pos hv]
                    ring
                _ = _ := integral_const_mul _ _
            rw [hPull]
            ring
      · simp [selected, hv, K, cutW, muI]
    have hSelI : Integrable selected P := by
      apply (hJoint.integral_prod_right.const_mul (Real.exp 1 * alpha)).mono'
        hSelm.aestronglyMeasurable
      exact ae_of_all _ fun v => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hSelnonneg v)] using hPoint v
    refine ⟨hSelI, ?_⟩
    have hKernelIntegral :
        (∫ s : ℝ, ∫ v, K (s, v) ∂P ∂muI) ≤
          ∫ s : ℝ in I, A * Real.rpow s (alpha - kappa - 1) * Real.exp (-rate * s) := by
      apply integral_mono_ae hJoint.integral_prod_left hScalar
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact (le_trans (le_abs_self (∫ v, K (s, v) ∂P))
          (by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun v => K (s, v)))).trans
            (hSectionBound s hs)
    have hScalarFull : (∫ s : ℝ in I,
        Real.rpow s (alpha - kappa - 1) * Real.exp (-rate * s)) ≤
          Real.rpow (1 / rate) (alpha - kappa) * Real.Gamma (alpha - kappa) := by
      calc
        _ ≤ ∫ s : ℝ in Set.Ioi 0,
            Real.rpow s (alpha - kappa - 1) * Real.exp (-rate * s) := by
          apply setIntegral_mono_set hGamma.1 _
            (ae_of_all _ fun s (hs : s ∈ I) => hs.1)
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
          exact mul_nonneg (Real.rpow_nonneg hs.le _) (Real.exp_nonneg _)
        _ = _ := hGamma.2
    calc
      _ ≤ ∫ v, Real.exp 1 * alpha * (∫ s, K (s, v) ∂muI) ∂P :=
        integral_mono hSelI (hJoint.integral_prod_right.const_mul _) hPoint
      _ = Real.exp 1 * alpha * (∫ s : ℝ, ∫ v, K (s, v) ∂P ∂muI) := by
        rw [integral_const_mul, ← integral_integral_swap hJoint]
      _ ≤ Real.exp 1 * alpha *
          (∫ s : ℝ in I, A * Real.rpow s (alpha - kappa - 1) * Real.exp (-rate * s)) :=
        mul_le_mul_of_nonneg_left hKernelIntegral (by positivity)
      _ = Real.exp 1 * alpha * A *
          (∫ s : ℝ in I, Real.rpow s (alpha - kappa - 1) * Real.exp (-rate * s)) := by
        rw [show (fun s : ℝ => A * Real.rpow s (alpha - kappa - 1) *
            Real.exp (-rate * s)) = fun s : ℝ =>
              A * (Real.rpow s (alpha - kappa - 1) * Real.exp (-rate * s)) by
                funext s; ring, integral_const_mul]
        ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hScalarFull
          (show 0 ≤ Real.exp 1 * alpha * A by positivity)
        simpa only [mul_assoc] using hh
  let c1 : ℝ := (1 - Real.exp (-2)) / 16
  let Gq : ℝ := Real.rpow (2 / c1) ((q : ℝ) / 2) * Real.Gamma ((q : ℝ) / 2)
  let C : ℝ := 100 * (2 : ℝ) ^ p * Real.exp 1 *
    (1 + (q : ℝ) + (p : ℝ)) * (1 + C0 + Cp) * (1 + |Gq|)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro rho hProb B hB hsupport hmean hsecond beta x hx t ht
    h0 P T d M D vx Ax marked unmarked
  have hmRaw := boundedQuadraticTilt_density_moments rho B 0 0 hB
    (show (0 : ℝ) ≤ 0 by rfl) hsupport
  rcases hmRaw with ⟨hW0, hZ0, hZlo0, hZhi0, hloglo0, hloghi0, hprob0,
    hac0, hca0, hbnd0, hw0, hiff0, hdensity0, hcmp0, hpowers, hrest0⟩
  have h2 : Integrable (fun z : ℝ => z ^ 2) rho := (hpowers 2).1
  have h3 : Integrable (fun z : ℝ => |z| ^ 3) rho := (hpowers 3).2.2.1
  have hbeta : 1 ≤ beta := by
    have h3r : Integrable (fun z : ℝ => Real.rpow |z| (3 : ℝ)) rho := by
      simpa only [Real.rpow_eq_pow, Real.rpow_natCast, Real.rpow_ofNat] using h3
    have hh := (original_moment_domain_coarse_guards 3 (by norm_num)
      (by norm_num) rho 1 (by norm_num) h2 (by simpa using hsecond) h3r).2.1
    simpa only [beta, Nat.cast_one, one_mul, Real.rpow_eq_pow, Real.one_rpow, Real.rpow_natCast, Real.rpow_ofNat] using hh
  have hbetapos : 0 < beta := lt_of_lt_of_le (by norm_num) hbeta
  have hh0 : 0 < h0 := by dsimp [h0]; positivity
  have hRank := Shao.C2.AuxiliarySourceCutoffPayment.auxiliary_original_cutoff_rank_payment
    beta 128 (1 / 16) K 0 x hbeta (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by norm_num [K]) (by norm_num [K]) t t ht (Or.inl rfl)
      (by simp only [zero_mul]; positivity)
  have htpos : 0 < t := hRank.2.1
  have ht4 : 4 ≤ t := hRank.1.trans ht
  have hTm : Measurable T := Shao.measurable_energy
  have hdm : Measurable d := Shao.measurable_prefixSum t
  have hMm : Measurable M := by
    have hcoord : Measurable (fun a : Shao.Path t => a ⟨0, htpos⟩) :=
      measurable_pi_apply _
    have habs : Measurable (fun a : Shao.Path t => |a ⟨0, htpos⟩|) := by
      simpa only [Real.norm_eq_abs] using hcoord.norm
    simpa only [M, dif_pos htpos] using habs.pow_const (3 : ℕ)
  have htR : (4 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht4
  have hc1' : 0 < c1 := hc1
  let rate : ℝ := c1 * (t : ℝ) / 2
  have hrate : 0 < rate := by dsimp [rate]; positivity
  have hAx : 0 ≤ Ax := by dsimp [Ax]; positivity
  have hMn : ∀ v, 0 ≤ M v := by intro v; dsimp [M]; split_ifs <;> positivity
  let V : ℕ → Shao.Path t → ℝ := fun j v =>
    if 0 < T v ∧ (3 * x / 2) * Real.sqrt (T v) ≤ |d v| then M v * |d v| ^ j else 0
  let U : ℕ → Shao.Path t → ℝ := fun j v =>
    if 0 < T v ∧ vx * Real.sqrt (T v) ≤ |d v| then |d v| ^ j else 0
  have hRM : MeasurableSet {v : Shao.Path t |
      0 < T v ∧ (3 * x / 2) * Real.sqrt (T v) ≤ |d v|} :=
    (measurableSet_lt measurable_const hTm).inter
      (measurableSet_le (hTm.sqrt.const_mul _) hdm.norm)
  have hRU : MeasurableSet {v : Shao.Path t |
      0 < T v ∧ vx * Real.sqrt (T v) ≤ |d v|} :=
    (measurableSet_lt measurable_const hTm).inter
      (measurableSet_le (hTm.sqrt.const_mul _) hdm.norm)
  have hVm (j : ℕ) : Measurable (V j) :=
    Measurable.ite hRM (hMm.mul (hdm.norm.pow_const j)) measurable_const
  have hUm (j : ℕ) : Measurable (U j) :=
    Measurable.ite hRU (hdm.norm.pow_const j) measurable_const
  have hVn (j : ℕ) : ∀ v, 0 ≤ V j v := by
    intro v
    dsimp [V]
    split_ifs
    · exact mul_nonneg (hMn v) (pow_nonneg (abs_nonneg _) _)
    · exact le_rfl
  have hUn (j : ℕ) : ∀ v, 0 ≤ U j v := by
    intro v
    dsimp [U]
    split_ifs <;> positivity
  have hRateM (s : ℝ) (hs : 0 ≤ s) :
      Real.exp (-c1 * s * ((t : ℝ) - 1)) ≤ Real.exp (-rate * s) := by
    apply Real.exp_le_exp.mpr
    dsimp [rate]
    nlinarith only [mul_nonneg (mul_nonneg hc1'.le hs)
      (show 0 ≤ (t : ℝ) / 2 - 1 by linarith only [htR])]
  have hRateU (s : ℝ) (hs : 0 ≤ s) :
      Real.exp (-c1 * s * (t : ℝ)) ≤ Real.exp (-rate * s) := by
    apply Real.exp_le_exp.mpr
    dsimp [rate]
    nlinarith only [mul_nonneg (mul_nonneg hc1'.le hs) (Nat.cast_nonneg t)]
  have hDampedM (j : ℕ) (s : ℝ) (hs : s ∈ Set.Ioo 0 (1 / h0)) :
      Integrable (fun v => V j v * Real.exp (-s * T v)) P ∧
      (∫ v, V j v * Real.exp (-s * T v) ∂P) ≤
        (Cmoment j * beta * Ax) * Real.rpow s (-(j : ℝ) / 2) * Real.exp (-rate * s) := by
    have hh := hmomentFamily j rho B hB hsupport hmean hsecond x hx t ht s hs.1 hs.2.le
    have hCj : 0 < Cmoment j := hCmoment j
    have hsPowj : 0 ≤ Real.rpow s (-(j : ℝ) / 2) := Real.rpow_nonneg hs.1.le _
    have heq : (fun v : Shao.Path t => V j v * Real.exp (-s * T v)) =
        fun v => if 0 < T v ∧ (3 * x / 2) * Real.sqrt (T v) ≤ |d v| then
          M v * |d v| ^ j * Real.exp (-s * T v) else 0 := by
      funext v
      dsimp [V]
      split_ifs <;> ring
    refine ⟨?_, ?_⟩
    · simpa only [heq] using hh.1
    · calc
        _ = ∫ v, (if 0 < T v ∧ (3 * x / 2) * Real.sqrt (T v) ≤ |d v| then
            M v * |d v| ^ j * Real.exp (-s * T v) else 0) ∂P := by rw [heq]
        _ ≤ Cmoment j * beta * Real.rpow s (-(j : ℝ) / 2) *
            Real.exp (-c1 * s * ((t : ℝ) - 1)) * Ax := hh.2.2.1
        _ ≤ Cmoment j * beta * Real.rpow s (-(j : ℝ) / 2) *
            Real.exp (-rate * s) * Ax := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hRateM s hs.1.le)
              (mul_nonneg (mul_nonneg hCj.le hbetapos.le) hsPowj)) hAx
        _ = _ := by ring
  have hDampedU (j : ℕ) (s : ℝ) (hs : s ∈ Set.Ioo 0 (1 / h0)) :
      Integrable (fun v => U j v * Real.exp (-s * T v)) P ∧
      (∫ v, U j v * Real.exp (-s * T v) ∂P) ≤
        (Cmoment j * Ax) * Real.rpow s (-(j : ℝ) / 2) * Real.exp (-rate * s) := by
    have hh := hmomentFamily j rho B hB hsupport hmean hsecond x hx t ht s hs.1 hs.2.le
    have hCj : 0 < Cmoment j := hCmoment j
    have hsPowj : 0 ≤ Real.rpow s (-(j : ℝ) / 2) := Real.rpow_nonneg hs.1.le _
    have heq : (fun v : Shao.Path t => U j v * Real.exp (-s * T v)) =
        fun v => if 0 < T v ∧ vx * Real.sqrt (T v) ≤ |d v| then
          |d v| ^ j * Real.exp (-s * T v) else 0 := by
      funext v
      dsimp [U]
      split_ifs <;> ring
    refine ⟨?_, ?_⟩
    · simpa only [heq] using hh.2.1
    · calc
        _ = ∫ v, (if 0 < T v ∧ vx * Real.sqrt (T v) ≤ |d v| then
            |d v| ^ j * Real.exp (-s * T v) else 0) ∂P := by rw [heq]
        _ ≤ Cmoment j * Real.rpow s (-(j : ℝ) / 2) *
            Real.exp (-c1 * s * (t : ℝ)) * Ax := hh.2.2.2
        _ ≤ Cmoment j * Real.rpow s (-(j : ℝ) / 2) *
            Real.exp (-rate * s) * Ax := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hRateU s hs.1.le)
              (mul_nonneg hCj.le hsPowj)) hAx
        _ = _ := by ring
  let YM : ℕ → Shao.Path t → ℝ := fun j v =>
    if h0 ≤ T v then V j v * Real.rpow (T v) (-((q : ℝ) + (j : ℝ)) / 2) else 0
  let YU : ℕ → Shao.Path t → ℝ := fun j v =>
    if h0 ≤ T v then U j v * Real.rpow (T v) (-((q : ℝ) + (j : ℝ)) / 2) else 0
  have hYM (j : ℕ) : Integrable (YM j) P ∧
      (∫ v, YM j v ∂P) ≤ Real.exp 1 * (((q : ℝ) + (j : ℝ)) / 2) *
        (Cmoment j * beta * Ax) * Real.rpow (1 / rate) ((q : ℝ) / 2) *
          Real.Gamma ((q : ℝ) / 2) := by
    have ha : 0 < ((q : ℝ) + (j : ℝ)) / 2 := by positivity
    have he : ((q : ℝ) + (j : ℝ)) / 2 - (j : ℝ) / 2 = (q : ℝ) / 2 := by ring
    have hCj : 0 < Cmoment j := hCmoment j
    have hh := hInverse t P T (V j) hTm (hVm j) (hVn j) h0
      (((q : ℝ) + (j : ℝ)) / 2) ((j : ℝ) / 2) (Cmoment j * beta * Ax) rate
      hh0 ha (by rw [he]; exact ha0) (by positivity) hrate
        (fun s hs => by simpa only [neg_div] using hDampedM j s hs)
    simpa only [YM, he, neg_div] using hh
  have hYU (j : ℕ) : Integrable (YU j) P ∧
      (∫ v, YU j v ∂P) ≤ Real.exp 1 * (((q : ℝ) + (j : ℝ)) / 2) *
        (Cmoment j * Ax) * Real.rpow (1 / rate) ((q : ℝ) / 2) *
          Real.Gamma ((q : ℝ) / 2) := by
    have ha : 0 < ((q : ℝ) + (j : ℝ)) / 2 := by positivity
    have he : ((q : ℝ) + (j : ℝ)) / 2 - (j : ℝ) / 2 = (q : ℝ) / 2 := by ring
    have hCj : 0 < Cmoment j := hCmoment j
    have hh := hInverse t P T (U j) hTm (hUm j) (hUn j) h0
      (((q : ℝ) + (j : ℝ)) / 2) ((j : ℝ) / 2) (Cmoment j * Ax) rate
      hh0 ha (by rw [he]; exact ha0) (by positivity) hrate
        (fun s hs => by simpa only [neg_div] using hDampedU j s hs)
    simpa only [YU, he, neg_div] using hh
  have hYMn (j : ℕ) : ∀ v, 0 ≤ YM j v := by
    intro v
    dsimp [YM]
    split_ifs with hv
    · exact mul_nonneg (hVn j v) (Real.rpow_nonneg (hh0.le.trans hv) _)
    · exact le_rfl
  have hYUn (j : ℕ) : ∀ v, 0 ≤ YU j v := by
    intro v
    dsimp [YU]
    split_ifs with hv
    · exact mul_nonneg (hUn j v) (Real.rpow_nonneg (hh0.le.trans hv) _)
    · exact le_rfl
  have hSqrtInverse (a : ℝ) (ha : 0 < a) (j : ℕ) :
      1 / (Real.sqrt a) ^ j = Real.rpow a (-(j : ℝ) / 2) := by
    rw [Real.rpow_eq_pow, Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast ha.le, one_div]
    rw [show -(j : ℝ) / 2 = -((1 / 2 : ℝ) * (j : ℝ)) by ring, Real.rpow_neg ha.le]
  have hDnonneg : ∀ v, 0 ≤ D v := by
    intro v
    dsimp [D]
    split_ifs <;> positivity
  have hMarkedNonneg : ∀ v, 0 ≤ marked v := by
    intro v
    dsimp [marked]
    split_ifs
    · exact mul_nonneg (div_nonneg (hMn v) (pow_nonneg (Real.sqrt_nonneg _) _))
        (pow_nonneg (hDnonneg v) _)
    · exact le_rfl
  have hUnmarkedNonneg : ∀ v, 0 ≤ unmarked v := by
    intro v
    dsimp [unmarked]
    split_ifs
    · exact mul_nonneg (div_nonneg (by norm_num) (pow_nonneg (Real.sqrt_nonneg _) _))
        (pow_nonneg (hDnonneg v) _)
    · exact le_rfl
  have hMarkedPoint (v : Shao.Path t) :
      marked v ≤ (2 : ℝ) ^ p * (YM 0 v + YM p v) := by
    by_cases hv : 0 < T v ∧ h0 ≤ T v ∧
        (3 * x / 2) * Real.sqrt (T v) ≤ |d v|
    · have hr : 0 < T v ∧ (3 * x / 2) * Real.sqrt (T v) ≤ |d v| := ⟨hv.1, hv.2.2⟩
      have hq := hSqrtInverse (T v) hv.1 q
      have hp := hSqrtInverse (T v) hv.1 p
      have hqp : Real.rpow (T v) (-((q : ℝ) + (p : ℝ)) / 2) =
          Real.rpow (T v) (-(q : ℝ) / 2) * Real.rpow (T v) (-(p : ℝ) / 2) := by
        simp only [Real.rpow_eq_pow]
        rw [← Real.rpow_add hv.1]
        congr 1
        ring
      have hdivp : (|d v| / Real.sqrt (T v)) ^ p =
          |d v| ^ p * Real.rpow (T v) (-(p : ℝ) / 2) := by
        rw [div_pow, div_eq_mul_one_div, hp]
      have hDpow : D v ^ p ≤ (2 : ℝ) ^ p *
          (1 + (|d v| / Real.sqrt (T v)) ^ p) := by
        simpa only [D, if_pos hv.1] using
          Shao.Probability.SourceSuffixScalarInterfaces.one_add_pow_bound
            (|d v| / Real.sqrt (T v)) (by positivity) p
      calc
        marked v = (M v * (1 / (Real.sqrt (T v)) ^ q)) * D v ^ p := by
          simp only [marked, if_pos hv]
          ring
        _ ≤ (M v * (1 / (Real.sqrt (T v)) ^ q)) *
            ((2 : ℝ) ^ p * (1 + (|d v| / Real.sqrt (T v)) ^ p)) :=
          mul_le_mul_of_nonneg_left hDpow
            (mul_nonneg (hMn v) (div_nonneg (by norm_num) (pow_nonneg (Real.sqrt_nonneg _) _)))
        _ = _ := by
          simp only [YM, V, if_pos hv.2.1, if_pos hr, Nat.cast_zero,
            add_zero, pow_zero, mul_one]
          rw [hq, hdivp, hqp]
          ring
    · simp only [marked, if_neg hv]
      exact mul_nonneg (pow_nonneg (by norm_num) _) (add_nonneg (hYMn 0 v) (hYMn p v))
  have hUnmarkedPoint (v : Shao.Path t) :
      unmarked v ≤ (2 : ℝ) ^ p * (YU 0 v + YU p v) := by
    by_cases hv : 0 < T v ∧ h0 ≤ T v ∧ vx * Real.sqrt (T v) ≤ |d v|
    · have hr : 0 < T v ∧ vx * Real.sqrt (T v) ≤ |d v| := ⟨hv.1, hv.2.2⟩
      have hq := hSqrtInverse (T v) hv.1 q
      have hp := hSqrtInverse (T v) hv.1 p
      have hqp : Real.rpow (T v) (-((q : ℝ) + (p : ℝ)) / 2) =
          Real.rpow (T v) (-(q : ℝ) / 2) * Real.rpow (T v) (-(p : ℝ) / 2) := by
        simp only [Real.rpow_eq_pow]
        rw [← Real.rpow_add hv.1]
        congr 1
        ring
      have hdivp : (|d v| / Real.sqrt (T v)) ^ p =
          |d v| ^ p * Real.rpow (T v) (-(p : ℝ) / 2) := by
        rw [div_pow, div_eq_mul_one_div, hp]
      have hDpow : D v ^ p ≤ (2 : ℝ) ^ p *
          (1 + (|d v| / Real.sqrt (T v)) ^ p) := by
        simpa only [D, if_pos hv.1] using
          Shao.Probability.SourceSuffixScalarInterfaces.one_add_pow_bound
            (|d v| / Real.sqrt (T v)) (by positivity) p
      calc
        unmarked v = (1 / (Real.sqrt (T v)) ^ q) * D v ^ p := by
          simp only [unmarked, if_pos hv]
        _ ≤ (1 / (Real.sqrt (T v)) ^ q) *
            ((2 : ℝ) ^ p * (1 + (|d v| / Real.sqrt (T v)) ^ p)) :=
          mul_le_mul_of_nonneg_left hDpow (by positivity)
        _ = _ := by
          simp only [YU, U, if_pos hv.2.1, if_pos hr, Nat.cast_zero,
            add_zero, pow_zero, one_mul]
          rw [hq, hdivp, hqp]
          ring
    · simp only [unmarked, if_neg hv]
      exact mul_nonneg (pow_nonneg (by norm_num) _) (add_nonneg (hYUn 0 v) (hYUn p v))
  have hDm : Measurable D := Measurable.ite
    (measurableSet_lt measurable_const hTm)
    ((hdm.norm.div hTm.sqrt).const_add 1) measurable_const
  have hMarkSet : MeasurableSet {v : Shao.Path t |
      0 < T v ∧ h0 ≤ T v ∧ (3 * x / 2) * Real.sqrt (T v) ≤ |d v|} :=
    (measurableSet_lt measurable_const hTm).inter
      ((measurableSet_le measurable_const hTm).inter
        (measurableSet_le (hTm.sqrt.const_mul _) hdm.norm))
  have hUnmarkSet : MeasurableSet {v : Shao.Path t |
      0 < T v ∧ h0 ≤ T v ∧ vx * Real.sqrt (T v) ≤ |d v|} :=
    (measurableSet_lt measurable_const hTm).inter
      ((measurableSet_le measurable_const hTm).inter
        (measurableSet_le (hTm.sqrt.const_mul _) hdm.norm))
  have hMarkedMeas : Measurable marked := Measurable.ite hMarkSet
    ((hMm.div (hTm.sqrt.pow_const q)).mul (hDm.pow_const p)) measurable_const
  have hUnmarkedMeas : Measurable unmarked := Measurable.ite hUnmarkSet
    ((measurable_const.div (hTm.sqrt.pow_const q)).mul (hDm.pow_const p)) measurable_const
  have hMarkedI : Integrable marked P := by
    apply (((hYM 0).1.add (hYM p).1).const_mul ((2 : ℝ) ^ p)).mono'
      hMarkedMeas.aestronglyMeasurable
    exact ae_of_all _ fun v => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hMarkedNonneg v), Pi.add_apply] using hMarkedPoint v
  have hUnmarkedI : Integrable unmarked P := by
    apply (((hYU 0).1.add (hYU p).1).const_mul ((2 : ℝ) ^ p)).mono'
      hUnmarkedMeas.aestronglyMeasurable
    exact ae_of_all _ fun v => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hUnmarkedNonneg v), Pi.add_apply] using hUnmarkedPoint v
  have htRpos : 0 < (t : ℝ) := by exact_mod_cast htpos
  have hRateScale : Real.rpow (1 / rate) ((q : ℝ) / 2) * Real.Gamma ((q : ℝ) / 2) =
      Gq * Real.rpow (t : ℝ) (-((q : ℝ) / 2)) := by
    have he : 1 / rate = (2 / c1) * (1 / (t : ℝ)) := by
      dsimp [rate]
      field_simp [ne_of_gt hc1', ne_of_gt htRpos]
    simp only [Real.rpow_eq_pow]
    rw [he, Real.mul_rpow (by positivity) (by positivity)]
    rw [one_div, Real.inv_rpow htRpos.le, Real.rpow_neg htRpos.le]
    dsimp only [Gq]
    simp only [Real.rpow_eq_pow]
    ring
  have hGq0 : 0 ≤ Gq := by
    dsimp [Gq]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.Gamma_pos_of_pos ha0).le
  have hCoeffC : (2 : ℝ) ^ p * Real.exp 1 *
      (((q : ℝ) / 2) * C0 + (((q : ℝ) + (p : ℝ)) / 2) * Cp) * Gq ≤ C := by
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    have hcoef : ((q : ℝ) / 2) * C0 + (((q : ℝ) + (p : ℝ)) / 2) * Cp ≤
        (1 + (q : ℝ) + (p : ℝ)) * (1 + C0 + Cp) := by
      have h0 := mul_nonneg hC0.le
        (show 0 ≤ 1 + (q : ℝ) + (p : ℝ) - (q : ℝ) / 2 by linarith)
      have h1 := mul_nonneg hCp.le
        (show 0 ≤ 1 + (q : ℝ) + (p : ℝ) - ((q : ℝ) + (p : ℝ)) / 2 by linarith)
      nlinarith only [h0, h1, hq0, hp0]
    have hGqUp : Gq ≤ 1 + |Gq| := by linarith [le_abs_self Gq]
    let Bcoef : ℝ := (2 : ℝ) ^ p * Real.exp 1 *
      (1 + (q : ℝ) + (p : ℝ)) * (1 + C0 + Cp) * (1 + |Gq|)
    have hBcoef : 0 ≤ Bcoef := by dsimp [Bcoef]; positivity
    calc
      _ ≤ Bcoef := by
        calc
          _ ≤ ((2 : ℝ) ^ p * Real.exp 1) *
              ((1 + (q : ℝ) + (p : ℝ)) * (1 + C0 + Cp)) * (1 + |Gq|) := by
            apply mul_le_mul
              (mul_le_mul_of_nonneg_left hcoef (by positivity)) hGqUp hGq0
            positivity
          _ = _ := by dsimp only [Bcoef]; ring
      _ ≤ 100 * Bcoef := by nlinarith only [hBcoef]
      _ = C := by dsimp [Bcoef, C]; ring
  have hneg : -(q : ℝ) / 2 = -((q : ℝ) / 2) := by ring
  have htPow : 0 ≤ Real.rpow (t : ℝ) (-((q : ℝ) / 2)) :=
    Real.rpow_nonneg (Nat.cast_nonneg t) _
  refine ⟨hMarkedI, hUnmarkedI, ?_, ?_⟩
  · rw [hneg]
    calc
      (∫ v, marked v ∂P) ≤ (2 : ℝ) ^ p * ((∫ v, YM 0 v ∂P) + ∫ v, YM p v ∂P) := by
        have hh := integral_mono hMarkedI
          (((hYM 0).1.add (hYM p).1).const_mul ((2 : ℝ) ^ p)) hMarkedPoint
        change (∫ v, marked v ∂P) ≤ ∫ v, (2 : ℝ) ^ p * (YM 0 v + YM p v) ∂P at hh
        simpa only [integral_const_mul, integral_add (hYM 0).1 (hYM p).1] using hh
      _ ≤ (2 : ℝ) ^ p *
          (Real.exp 1 * ((q : ℝ) / 2) * (C0 * beta * Ax) *
              Real.rpow (1 / rate) ((q : ℝ) / 2) * Real.Gamma ((q : ℝ) / 2) +
            Real.exp 1 * (((q : ℝ) + (p : ℝ)) / 2) * (Cp * beta * Ax) *
              Real.rpow (1 / rate) ((q : ℝ) / 2) * Real.Gamma ((q : ℝ) / 2)) := by
        have h0 := (hYM 0).2
        have hp := (hYM p).2
        simp only [Nat.cast_zero, add_zero] at h0
        exact mul_le_mul_of_nonneg_left (add_le_add h0 hp) (pow_nonneg (by norm_num) p)
      _ = ((2 : ℝ) ^ p * Real.exp 1 *
          (((q : ℝ) / 2) * C0 + (((q : ℝ) + (p : ℝ)) / 2) * Cp) * Gq) *
            beta * Real.rpow (t : ℝ) (-((q : ℝ) / 2)) * Ax := by
        calc
          _ = ((2 : ℝ) ^ p * Real.exp 1 *
              (((q : ℝ) / 2) * C0 + (((q : ℝ) + (p : ℝ)) / 2) * Cp)) * beta * Ax *
                (Real.rpow (1 / rate) ((q : ℝ) / 2) * Real.Gamma ((q : ℝ) / 2)) := by ring
          _ = _ := by rw [hRateScale]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCoeffC hbetapos.le) htPow) hAx
  · rw [hneg]
    calc
      (∫ v, unmarked v ∂P) ≤ (2 : ℝ) ^ p * ((∫ v, YU 0 v ∂P) + ∫ v, YU p v ∂P) := by
        have hh := integral_mono hUnmarkedI
          (((hYU 0).1.add (hYU p).1).const_mul ((2 : ℝ) ^ p)) hUnmarkedPoint
        change (∫ v, unmarked v ∂P) ≤ ∫ v, (2 : ℝ) ^ p * (YU 0 v + YU p v) ∂P at hh
        simpa only [integral_const_mul, integral_add (hYU 0).1 (hYU p).1] using hh
      _ ≤ (2 : ℝ) ^ p *
          (Real.exp 1 * ((q : ℝ) / 2) * (C0 * Ax) *
              Real.rpow (1 / rate) ((q : ℝ) / 2) * Real.Gamma ((q : ℝ) / 2) +
            Real.exp 1 * (((q : ℝ) + (p : ℝ)) / 2) * (Cp * Ax) *
              Real.rpow (1 / rate) ((q : ℝ) / 2) * Real.Gamma ((q : ℝ) / 2)) := by
        have h0 := (hYU 0).2
        have hp := (hYU p).2
        simp only [Nat.cast_zero, add_zero] at h0
        exact mul_le_mul_of_nonneg_left (add_le_add h0 hp) (pow_nonneg (by norm_num) p)
      _ = ((2 : ℝ) ^ p * Real.exp 1 *
          (((q : ℝ) / 2) * C0 + (((q : ℝ) + (p : ℝ)) / 2) * Cp) * Gq) *
            Real.rpow (t : ℝ) (-((q : ℝ) / 2)) * Ax := by
        calc
          _ = ((2 : ℝ) ^ p * Real.exp 1 *
              (((q : ℝ) / 2) * C0 + (((q : ℝ) + (p : ℝ)) / 2) * Cp)) * Ax *
                (Real.rpow (1 / rate) ((q : ℝ) / 2) * Real.Gamma ((q : ℝ) / 2)) := by ring
          _ = _ := by rw [hRateScale]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCoeffC htPow) hAx


theorem iid_marked_and_unmarked_rare_real_suffix_budgets :
    let K : ℝ := (2 : ℝ) ^ 64
    ∀ p : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (B : ℝ), 0 < B → (∀ᵐ z : ℝ ∂rho, |z| ≤ B) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        ∀ (n : ℕ), 0 < n → ∀ (x : ℝ), 16 ≤ x →
          let delta : ℝ := beta / Real.sqrt (n : ℝ)
          let u : ℝ := delta * (1 + x) ^ 3
          u ≤ Real.exp (-3 * x ^ 2) →
          let h0 : ℝ := 4 * beta ^ 2
          let H : ℝ := K * beta ^ 2 * (1 + x) ^ 6
          let m : ℕ := ⌈H⌉₊
          let vx : ℝ := Real.sqrt (9 * x ^ 2 / 4 - 1)
          let Ax : ℝ := Real.sqrt (Shao.standardNormalTail (3 * x / 2)) +
            Real.exp (-x ^ 2)
          let P : (t : ℕ) → Measure (Shao.Path t) :=
            fun t => Measure.pi (fun _ : Fin t => rho)
          let T : (t : ℕ) → Shao.Path t → ℝ := fun _ => Shao.energy
          let d : (t : ℕ) → Shao.Path t → ℝ := fun t a => Shao.prefixSum a t
          let M : (t : ℕ) → Shao.Path t → ℝ := fun t a =>
            if ht : 0 < t then |a ⟨0, ht⟩| ^ 3 else 0
          let D : (t : ℕ) → Shao.Path t → ℝ := fun t a =>
            if 0 < T t a then 1 + |d t a| / Real.sqrt (T t a) else 1
          let marked : ℕ → (t : ℕ) → Shao.Path t → ℝ := fun q t a =>
            if 0 < T t a ∧ h0 ≤ T t a ∧
                (3 * x / 2) * Real.sqrt (T t a) ≤ |d t a| then
              M t a / (Real.sqrt (T t a)) ^ q * D t a ^ p
            else 0
          let unmarked : ℕ → (t : ℕ) → Shao.Path t → ℝ := fun q t a =>
            if 0 < T t a ∧ h0 ≤ T t a ∧
                vx * Real.sqrt (T t a) ≤ |d t a| then
              1 / (Real.sqrt (T t a)) ^ q * D t a ^ p
            else 0
          let future : (t : ℕ) → Shao.Path t → ℝ := fun t a =>
            if 0 < T t a ∧ H / 2 ≤ T t a ∧
                vx * Real.sqrt (T t a) ≤ |d t a| then
              (1 / Real.sqrt (T t a)) *
                (1 + |d t a| / Real.sqrt (T t a)) ^ 2
            else 0
          1 ≤ beta ∧ 0 < h0 ∧ h0 ≤ H / 2 ∧ 4 ≤ m ∧
            h0 ≤ (m : ℝ) ∧ (m : ℝ) ≤ (n : ℝ) / 4 ∧
            (∀ t q : ℕ, (q = 1 ∨ q = 3) →
              Integrable (marked q t) (P t) ∧ Integrable (unmarked q t) (P t)) ∧
            (∀ t : ℕ, m ≤ t → ∀ q : ℕ, (q = 1 ∨ q = 3) →
              (∫ a, marked q t a ∂P t) ≤
                C * beta * Real.rpow (t : ℝ) (-(q : ℝ) / 2) * Ax ∧
              (∫ a, unmarked q t a ∂P t) ≤
                C * Real.rpow (t : ℝ) (-(q : ℝ) / 2) * Ax) ∧
            (∑ t ∈ Finset.Icc ((n + 1) / 2) n,
              ∫ a, marked 3 t a ∂P t) ≤ C * delta * Ax ∧
            (1 / (n : ℝ)) * (∑ t ∈ Finset.Icc 1 (n / 2),
              ∫ a, marked 1 t a ∂P t) ≤ C * delta * Shao.standardNormalTail x ∧
            (∀ t : ℕ, Integrable (future t) (P t)) ∧
            (∀ t : ℕ, m ≤ t →
              (∫ a, future t a ∂P t) ≤
                C * Real.rpow (t : ℝ) (-1 / 2 : ℝ) * Shao.standardNormalTail x)
 := by
  classical
  intro K p
  obtain ⟨Crare, hCrare, hRare⟩ :=
    Shao.C2.AuxiliaryOriginalCutoffRare.auxiliary_original_cutoff_rare_probability
  have hKDrift : 8000000 * (1 + (128 : ℝ)) ^ 2 ≤ K := by
    norm_num [K]
  have hKBudget : 2 * (768 / (1 / 16 : ℝ)) ^ 2 ≤ K := by
    norm_num [K]
  have hRareFixed := hRare (1 / 16) (by norm_num) (by norm_num)
    128 (by norm_num) K hKDrift hKBudget
  have hGaussian : ∀ x : ℝ, 16 ≤ x →
      Real.sqrt (Shao.standardNormalTail (3 * x / 2)) + Real.exp (-x ^ 2) ≤
        8 * Shao.standardNormalTail x ∧
      Real.exp (-3 * x ^ 2) ≤ 8 * Shao.standardNormalTail x := by
    intro x hx
    have hx0 : 0 ≤ x := by linarith
    have hP0 : 0 ≤ Shao.standardNormalTail x :=
      (Shao.standardNormalTail_basic.2.2.1 x).1.le
    have hpoly : 1 + x ≤ Real.exp (x ^ 2 / 8) := by
      calc
        1 + x ≤ 1 + x ^ 2 / 8 := by
          nlinarith [mul_nonneg hx0 (show 0 ≤ x - 8 by linarith)]
        _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (x ^ 2 / 8)
    have hrev : (1 / 2 : ℝ) ≤
        (4 / 3 : ℝ) * (1 + x) * Real.exp (x ^ 2 / 2) * Shao.standardNormalTail x := by
      simpa only [Shao.standardNormalTail_basic.2.1, zero_pow (by decide : (2 : ℕ) ≠ 0),
        add_zero, div_one, sub_zero] using
          Shao.standardNormalTail_ratio_bound x 0 hx0 (by norm_num)
    have hrevB : (1 / 2 : ℝ) ≤
        (4 / 3 : ℝ) * Real.exp (5 * x ^ 2 / 8) * Shao.standardNormalTail x := by
      apply hrev.trans
      calc
        _ ≤ (4 / 3 : ℝ) * Real.exp (x ^ 2 / 8) *
            Real.exp (x ^ 2 / 2) * Shao.standardNormalTail x := by gcongr
        _ = _ := by
          rw [mul_assoc (4 / 3 : ℝ), ← Real.exp_add]
          congr 2
          ring
    have hNeg : Real.exp (-5 * x ^ 2 / 8) ≤ (8 / 3 : ℝ) * Shao.standardNormalTail x := by
      have hh := mul_le_mul_of_nonneg_left hrevB (Real.exp_nonneg (-5 * x ^ 2 / 8))
      have he : Real.exp (-5 * x ^ 2 / 8) * Real.exp (5 * x ^ 2 / 8) = 1 := by
        rw [← Real.exp_add]
        convert Real.exp_zero using 1 <;> ring
      have hh' : Real.exp (-5 * x ^ 2 / 8) * (1 / 2 : ℝ) ≤
          (4 / 3 : ℝ) * Shao.standardNormalTail x := by
        calc
          _ ≤ Real.exp (-5 * x ^ 2 / 8) *
              ((4 / 3 : ℝ) * Real.exp (5 * x ^ 2 / 8) * Shao.standardNormalTail x) := hh
          _ = _ := by
            calc
              _ = (4 / 3 : ℝ) * (Real.exp (-5 * x ^ 2 / 8) *
                  Real.exp (5 * x ^ 2 / 8)) * Shao.standardNormalTail x := by ring
              _ = _ := by rw [he]; ring
      linarith
    have hratio : (1 + x) / (1 + 3 * x / 2) ≤ (1 : ℝ) := by
      apply (div_le_one (by positivity)).2
      linarith
    have hforward : Shao.standardNormalTail (3 * x / 2) ≤
        (4 / 3 : ℝ) * Real.exp (-5 * x ^ 2 / 8) * Shao.standardNormalTail x := by
      have hh := Shao.standardNormalTail_ratio_bound x (3 * x / 2) hx0 (by positivity)
      have he : (x ^ 2 - (3 * x / 2) ^ 2) / 2 = -5 * x ^ 2 / 8 := by ring
      rw [he] at hh
      apply hh.trans
      calc
        _ ≤ (4 / 3 : ℝ) * 1 * Real.exp (-5 * x ^ 2 / 8) * Shao.standardNormalTail x := by gcongr
        _ = _ := by ring
    have hsquare : Shao.standardNormalTail (3 * x / 2) ≤
        (2 * Shao.standardNormalTail x) ^ 2 := by
      have hh := mul_le_mul_of_nonneg_right hNeg hP0
      nlinarith [sq_nonneg (Shao.standardNormalTail x)]
    have hsqrt : Real.sqrt (Shao.standardNormalTail (3 * x / 2)) ≤
        2 * Shao.standardNormalTail x :=
      (Real.sqrt_le_iff).2 ⟨by positivity, hsquare⟩
    have heSmall : Real.exp (-x ^ 2) ≤ (8 / 3 : ℝ) * Shao.standardNormalTail x := by
      exact (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x] : -x ^ 2 ≤ -5 * x ^ 2 / 8)).trans hNeg
    constructor
    · nlinarith
    · have hh : Real.exp (-3 * x ^ 2) ≤ Real.exp (-x ^ 2) :=
        Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x])
      nlinarith
  have hRaw : ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
      (B : ℝ), 0 < B → (∀ᵐ z : ℝ ∂rho, |z| ≤ B) →
        Integrable (fun z : ℝ => z ^ 2) rho ∧
          Integrable (fun z : ℝ => |z| ^ 3) rho := by
    intro rho hProb B hB hsupport
    have hm := boundedQuadraticTilt_density_moments rho B 0 0 hB
      (show (0 : ℝ) ≤ 0 by rfl) hsupport
    rcases hm with ⟨hW, hZ, hZlo, hZhi, hloglo, hloghi, hprob,
      hac, hca, hbnd, hw, hiff, hdensity, hcmp, hpowers, hrest⟩
    exact ⟨(hpowers 2).1, (hpowers 3).2.2.1⟩
  have hBeta : ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
      (B : ℝ), 0 < B → (∀ᵐ z : ℝ ∂rho, |z| ≤ B) →
        (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
          1 ≤ ∫ z : ℝ, |z| ^ 3 ∂rho := by
    intro rho hProb B hB hsupport hsecond
    obtain ⟨h2, h3⟩ := hRaw rho B hB hsupport
    have h3r : Integrable (fun z : ℝ => Real.rpow |z| (3 : ℝ)) rho := by
      simpa only [Real.rpow_eq_pow, Real.rpow_natCast, Real.rpow_ofNat] using h3
    have hh := (original_moment_domain_coarse_guards 3 (by norm_num)
      (by norm_num) rho 1 (by norm_num) h2 (by simpa using hsecond) h3r).2.1
    simpa only [Nat.cast_one, one_mul, Real.rpow_eq_pow, Real.one_rpow, Real.rpow_natCast, Real.rpow_ofNat] using hh
  have hRawCutoff : ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
      (B : ℝ), 0 < B → (∀ᵐ z : ℝ ∂rho, |z| ≤ B) →
        (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        0 < 4 * beta ^ 2 ∧ 4 * beta ^ 2 ≤ K * beta ^ 2 * (1 + (16 : ℝ)) ^ 6 / 2 := by
    intro rho hProb B hB hsupport hsecond beta
    have hb : 1 ≤ beta := hBeta rho B hB hsupport hsecond
    have hbpos : 0 < beta := lt_of_lt_of_le (by norm_num) hb
    constructor
    · positivity
    · have hb2 : 0 ≤ beta ^ 2 := sq_nonneg beta
      norm_num [K]
      nlinarith
  have hCutoffNumber : ∀ x : ℝ, 16 ≤ x → 8 * K ≤ Real.exp (6 * x ^ 2) := by
    intro x hx
    have hx2 : (16 : ℝ) ^ 2 ≤ x ^ 2 :=
      (sq_le_sq₀ (by norm_num) (by linarith : 0 ≤ x)).2 hx
    have he : (97 : ℝ) ≤ Real.exp (6 * x ^ 2 / 16) := by
      calc
        97 ≤ 1 + 6 * x ^ 2 / 16 := by nlinarith
        _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (6 * x ^ 2 / 16)
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 97) he 16
    have hh : (Real.exp (6 * x ^ 2 / 16)) ^ (16 : ℕ) = Real.exp (6 * x ^ 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hh] at hp
    calc
      8 * K ≤ (97 : ℝ) ^ (16 : ℕ) := by norm_num [K]
      _ ≤ _ := hp
  have hSumInvSqrt : ∀ N : ℕ,
      (∑ t ∈ Finset.Icc 1 N, 1 / Real.sqrt (t : ℝ)) ≤ 2 * Real.sqrt (N : ℝ) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hroot : 0 < Real.sqrt ((N + 1 : ℕ) : ℝ) := by positivity
      have hs0 := Real.sq_sqrt (Nat.cast_nonneg N)
      have hs1 := Real.sq_sqrt (Nat.cast_nonneg (N + 1))
      have hstep : 1 / Real.sqrt ((N + 1 : ℕ) : ℝ) ≤
          2 * Real.sqrt ((N + 1 : ℕ) : ℝ) - 2 * Real.sqrt (N : ℝ) := by
        apply (div_le_iff₀ hroot).2
        have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by
          simp only [Nat.cast_add, Nat.cast_one]
        nlinarith only [hs0, hs1, hcast,
          sq_nonneg (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt (N : ℝ))]
      calc
        _ ≤ 2 * Real.sqrt (N : ℝ) + 1 / Real.sqrt ((N + 1 : ℕ) : ℝ) :=
          add_le_add ih (le_refl (1 / Real.sqrt ((N + 1 : ℕ) : ℝ)))
        _ ≤ _ := by linarith
  have hHalfRpow (z : ℝ) (hz : 0 < z) :
      Real.rpow z (-1 / 2 : ℝ) = 1 / Real.sqrt z := by
    simp only [Real.rpow_eq_pow]
    rw [show (-1 / 2 : ℝ) = -((1 / 2 : ℝ)) by ring,
      Real.rpow_neg hz.le, ← Real.sqrt_eq_rpow, one_div]
  obtain ⟨CL1, hCL1, hLong1⟩ := rsb_rare_cutoff_inverse_moments p 1 (Or.inl rfl)
  obtain ⟨CL3, hCL3, hLong3⟩ := rsb_rare_cutoff_inverse_moments p 3 (Or.inr rfl)
  obtain ⟨CF, hCF, hFuture⟩ := rsb_rare_cutoff_inverse_moments 2 1 (Or.inl rfl)
  obtain ⟨CS, hCS, hShort⟩ := iid_marked_cutoff_inverse_moments p 1 (Or.inl rfl)
  let c : ℝ := (1 - Real.exp (-2)) / 8
  have hc : 0 < c := raw_gaussian_damped_coordinate_factors.2.1
  let Gshort : ℝ := Real.Gamma (1 / 2) * Real.rpow (1 / c) (1 / 2)
  let E3 : ℝ := Real.rpow (1 / 2 : ℝ) (-(3 : ℝ) / 2)
  let C : ℝ := 100000 * (1 + CL1 + CL3 + CF + CS) *
    (1 + |Gshort|) * (1 + Real.sqrt K) * (1 + |E3|)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro rho hProb B hB hsupport hmean hsecond beta n hn x hx delta u hu
    h0 H m vx Ax P T d M D marked unmarked future
  obtain ⟨h2, h3⟩ := hRaw rho B hB hsupport
  have hbeta : 1 ≤ beta := hBeta rho B hB hsupport hsecond
  have hbetapos : 0 < beta := lt_of_lt_of_le (by norm_num) hbeta
  have hNpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hSqrtN : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hNpos
  have hKpos : 0 < K := by norm_num [K]
  have hxp : 0 < 1 + x := by linarith
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hup : 0 < u := by dsimp [u]; positivity
  have hh0 : 0 < h0 := by dsimp [h0]; positivity
  have hh0ge : (4 : ℝ) ≤ h0 := by dsimp [h0]; nlinarith [sq_nonneg (beta - 1)]
  have hHhalf : h0 ≤ H / 2 := by
    have hh := (hRawCutoff rho B hB hsupport hsecond).2
    change 4 * beta ^ 2 ≤ H / 2
    apply hh.trans
    dsimp [H]
    gcongr <;> linarith
  have hHge : (8 : ℝ) ≤ H := by linarith
  have hHpos : 0 < H := by linarith
  have hmlo : H ≤ (m : ℝ) := Nat.le_ceil H
  have hmhi : (m : ℝ) ≤ H + 1 := (Nat.ceil_lt_add_one hHpos.le).le
  have hm2H : (m : ℝ) ≤ 2 * H := by linarith
  have hm4 : 4 ≤ m := by
    have hh : (4 : ℝ) ≤ (m : ℝ) := by linarith
    exact_mod_cast hh
  have hh0m : h0 ≤ (m : ℝ) := by linarith
  have huSquare : u ^ 2 ≤ Real.exp (-6 * x ^ 2) := by
    calc
      _ ≤ (Real.exp (-3 * x ^ 2)) ^ (2 : ℕ) := pow_le_pow_left₀ hup.le hu 2
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hHu : H / (n : ℝ) = K * u ^ 2 := by
    dsimp [H, u, delta]
    rw [mul_pow, div_pow, Real.sq_sqrt hNpos.le]
    ring
  have hExpNumber : K * Real.exp (-6 * x ^ 2) ≤ (1 / 8 : ℝ) := by
    rw [show -6 * x ^ 2 = -(6 * x ^ 2) by ring, Real.exp_neg]
    change K / Real.exp (6 * x ^ 2) ≤ 1 / 8
    apply (div_le_iff₀ (Real.exp_pos _)).2
    linarith [hCutoffNumber x hx]
  have hmFrac : (m : ℝ) / (n : ℝ) ≤ (1 / 4 : ℝ) := by
    calc
      _ ≤ 2 * H / (n : ℝ) := div_le_div_of_nonneg_right hm2H hNpos.le
      _ = 2 * (H / (n : ℝ)) := by ring
      _ = 2 * K * u ^ 2 := by rw [hHu]; ring
      _ ≤ 2 * K * Real.exp (-6 * x ^ 2) := by gcongr
      _ ≤ _ := by linarith
  have hmn : (m : ℝ) ≤ (n : ℝ) / 4 := by
    have hh := (div_le_iff₀ hNpos).1 hmFrac
    linarith
  have h4mn : 4 * m ≤ n := by
    exact_mod_cast (show (4 : ℝ) * (m : ℝ) ≤ (n : ℝ) by linarith)
  have hn16 : 16 ≤ n := by omega
  have hmHalf : m ≤ n / 2 := by omega
  have hmEarly : m ≤ (n + 1) / 2 := by omega
  have hAx : 0 ≤ Ax := by dsimp [Ax]; positivity
  have hAxPsi : Ax ≤ 8 * Shao.standardNormalTail x := (hGaussian x hx).1
  have hSmallPsi : Real.exp (-3 * x ^ 2) ≤ 8 * Shao.standardNormalTail x := (hGaussian x hx).2
  have hDGeometry (t : ℕ) (a : Shao.Path t) :
      1 ≤ D t a ∧ D t a ≤ 1 + Real.sqrt (t : ℝ) := by
    have hh := (SourceMarkedSuffixAveraging.suffix_normalized_geometry a).2.2.2.2.2.1
    simpa only [D, T, d, SourceMarkedSuffixAveraging.suffixD] using hh
  have hDnonneg (t : ℕ) (a : Shao.Path t) : 0 ≤ D t a :=
    (show (0 : ℝ) ≤ 1 by norm_num).trans (hDGeometry t a).1
  have hTm (t : ℕ) : Measurable (T t) := Shao.measurable_energy
  have hdm (t : ℕ) : Measurable (d t) := Shao.measurable_prefixSum t
  have hDm (t : ℕ) : Measurable (D t) := Measurable.ite
    (measurableSet_lt measurable_const (hTm t))
    (((hdm t).norm.div (hTm t).sqrt).const_add 1) measurable_const
  have hUnmarkedWeightI (b : ℝ) (hb : 0 < b) (p' q' t : ℕ) :
      Integrable (fun a : Shao.Path t =>
        if 0 < T t a ∧ b ≤ T t a ∧ vx * Real.sqrt (T t a) ≤ |d t a| then
          1 / (Real.sqrt (T t a)) ^ q' * D t a ^ p' else 0) (P t) := by
    let F : Shao.Path t → ℝ := fun a =>
      if 0 < T t a ∧ b ≤ T t a ∧ vx * Real.sqrt (T t a) ≤ |d t a| then
        1 / (Real.sqrt (T t a)) ^ q' * D t a ^ p' else 0
    let B' : ℝ := (1 / (Real.sqrt b) ^ q') * (1 + Real.sqrt (t : ℝ)) ^ p'
    have hSet : MeasurableSet {a : Shao.Path t |
        0 < T t a ∧ b ≤ T t a ∧ vx * Real.sqrt (T t a) ≤ |d t a|} :=
      (measurableSet_lt measurable_const (hTm t)).inter
        ((measurableSet_le measurable_const (hTm t)).inter
          (measurableSet_le ((hTm t).sqrt.const_mul _) (hdm t).norm))
    have hFm : Measurable F := Measurable.ite hSet
      ((measurable_const.div ((hTm t).sqrt.pow_const q')).mul ((hDm t).pow_const p')) measurable_const
    have hFn : ∀ a, 0 ≤ F a := by
      intro a
      dsimp [F]
      split_ifs
      · exact mul_nonneg (div_nonneg (by norm_num) (pow_nonneg (Real.sqrt_nonneg _) _))
          (pow_nonneg (hDnonneg t a) _)
      · exact le_rfl
    have hFb (a : Shao.Path t) : F a ≤ B' := by
      by_cases ha : 0 < T t a ∧ b ≤ T t a ∧ vx * Real.sqrt (T t a) ≤ |d t a|
      · have hden : 0 < (Real.sqrt b) ^ q' := pow_pos (Real.sqrt_pos.mpr hb) q'
        have hdenle : (Real.sqrt b) ^ q' ≤ (Real.sqrt (T t a)) ^ q' :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt ha.2.1) q'
        have hinv : 1 / (Real.sqrt (T t a)) ^ q' ≤ 1 / (Real.sqrt b) ^ q' :=
          one_div_le_one_div_of_le hden hdenle
        have hpow : D t a ^ p' ≤ (1 + Real.sqrt (t : ℝ)) ^ p' :=
          pow_le_pow_left₀ (hDnonneg t a) (hDGeometry t a).2 p'
        simpa only [F, if_pos ha, B'] using
          mul_le_mul hinv hpow (pow_nonneg (hDnonneg t a) _) (by positivity)
      · simp only [F, if_neg ha]
        dsimp [B']
        positivity
    apply (integrable_const B').mono' hFm.aestronglyMeasurable
    exact ae_of_all _ fun a => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hFn a)] using hFb a
  have hUnmarkedI (t q : ℕ) : Integrable (unmarked q t) (P t) :=
    hUnmarkedWeightI h0 hh0 p q t
  have hMarkedI (t q : ℕ) (hq : q = 1 ∨ q = 3) : Integrable (marked q t) (P t) := by
    cases t with
    | zero =>
      have he (a : Shao.Path 0) : T 0 a = 0 := by simp [T, Shao.energy]
      simpa only [marked, he, lt_self_iff_false, false_and, ite_false] using
        (integrable_const (0 : ℝ) : Integrable (fun _ : Shao.Path 0 => (0 : ℝ)) (P 0))
    | succ l =>
      obtain ⟨CQ, hCQ, hQ⟩ := iid_marked_cutoff_inverse_moments p q hq
      have hh := hQ rho h2 hmean hsecond l h0 hh0
      let R : Set (Shao.Path (l + 1)) := {a |
        (3 * x / 2) * Real.sqrt (T (l + 1) a) ≤ |d (l + 1) a|}
      have hRm : MeasurableSet R :=
        measurableSet_le ((hTm (l + 1)).sqrt.const_mul _) (hdm (l + 1)).norm
      apply (hh.1.indicator hRm).congr
      exact ae_of_all _ fun a => by
        dsimp [marked, M, P, T, d, D, R]
        simp only [dif_pos (Nat.succ_pos l), Nat.succ_eq_add_one, Set.indicator_apply]
        split_ifs <;> simp_all
        all_goals (exfalso; linarith)
  have hFutureI (t : ℕ) : Integrable (future t) (P t) := by
    have hh := hUnmarkedWeightI (H / 2) (by positivity) 2 1 t
    apply hh.congr
    exact ae_of_all _ fun a => by
      dsimp [future, D]
      by_cases ha : 0 < T t a ∧ H / 2 ≤ T t a ∧
          vx * Real.sqrt (T t a) ≤ |d t a|
      · simp only [if_pos ha, if_pos ha.1, pow_one]
      · simp only [if_neg ha]
  have hGfactor : 1 ≤ 1 + |Gshort| := by linarith [abs_nonneg Gshort]
  have hKfactor : 1 ≤ 1 + Real.sqrt K := by linarith [Real.sqrt_nonneg K]
  have hEfactor : 1 ≤ 1 + |E3| := by linarith [abs_nonneg E3]
  have hCbase : 100000 * (1 + CL1 + CL3 + CF + CS) ≤ C := by
    calc
      _ ≤ (100000 * (1 + CL1 + CL3 + CF + CS)) * (1 + |Gshort|) :=
        le_mul_of_one_le_right (by positivity) hGfactor
      _ ≤ (100000 * (1 + CL1 + CL3 + CF + CS)) * (1 + |Gshort|) *
          (1 + Real.sqrt K) := le_mul_of_one_le_right (by positivity) hKfactor
      _ ≤ (100000 * (1 + CL1 + CL3 + CF + CS)) * (1 + |Gshort|) *
          (1 + Real.sqrt K) * (1 + |E3|) :=
        le_mul_of_one_le_right (by positivity) hEfactor
      _ = C := rfl
  have hCover1 : CL1 ≤ C := by
    nlinarith only [hCbase, hCL1, hCL3, hCF, hCS]
  have hCover3 : CL3 ≤ C := by
    nlinarith only [hCbase, hCL1, hCL3, hCF, hCS]
  have hCoverFuture : 8 * CF ≤ C := by
    nlinarith only [hCbase, hCL1, hCL3, hCF, hCS]
  have hRawLong1 (t : ℕ) (ht : m ≤ t) :=
    hLong1 rho B hB hsupport hmean hsecond x hx t ht
  have hRawLong3 (t : ℕ) (ht : m ≤ t) :=
    hLong3 rho B hB hsupport hmean hsecond x hx t ht
  have hLong : ∀ t : ℕ, m ≤ t → ∀ q : ℕ, (q = 1 ∨ q = 3) →
      (∫ a, marked q t a ∂P t) ≤ C * beta * Real.rpow (t : ℝ) (-(q : ℝ) / 2) * Ax ∧
      (∫ a, unmarked q t a ∂P t) ≤ C * Real.rpow (t : ℝ) (-(q : ℝ) / 2) * Ax := by
    intro t ht q hq
    have htp1 : 0 ≤ Real.rpow (t : ℝ) (-((1 : ℕ) : ℝ) / 2) :=
      Real.rpow_nonneg (Nat.cast_nonneg t) _
    have htp3 : 0 ≤ Real.rpow (t : ℝ) (-((3 : ℕ) : ℝ) / 2) :=
      Real.rpow_nonneg (Nat.cast_nonneg t) _
    rcases hq with rfl | rfl
    · constructor
      · apply (hRawLong1 t ht).2.2.1.trans
        gcongr
      · apply (hRawLong1 t ht).2.2.2.trans
        gcongr
    · constructor
      · apply (hRawLong3 t ht).2.2.1.trans
        gcongr
      · apply (hRawLong3 t ht).2.2.2.trans
        gcongr
  have hPsiX : 0 ≤ Shao.standardNormalTail x := (Shao.standardNormalTail_basic.2.2.1 x).1.le
  have hFutureBound (t : ℕ) (ht : m ≤ t) :
      (∫ a, future t a ∂P t) ≤ C * Real.rpow (t : ℝ) (-1 / 2 : ℝ) *
        Shao.standardNormalTail x := by
    have hh := hFuture rho B hB hsupport hmean hsecond x hx t ht
    let F : Shao.Path t → ℝ := fun a =>
      if 0 < T t a ∧ h0 ≤ T t a ∧ vx * Real.sqrt (T t a) ≤ |d t a| then
        1 / (Real.sqrt (T t a)) * D t a ^ 2 else 0
    have hFi : Integrable F (P t) := by simpa only [F, pow_one] using hh.2.1
    have hFb : (∫ a, F a ∂P t) ≤ CF * Real.rpow (t : ℝ) (-1 / 2 : ℝ) * Ax := by
      simpa only [F, pow_one, Nat.cast_one] using hh.2.2.2
    have hdom (a : Shao.Path t) : future t a ≤ F a := by
      by_cases ha : 0 < T t a ∧ H / 2 ≤ T t a ∧ vx * Real.sqrt (T t a) ≤ |d t a|
      · have hb : 0 < T t a ∧ h0 ≤ T t a ∧ vx * Real.sqrt (T t a) ≤ |d t a| :=
          ⟨ha.1, hHhalf.trans ha.2.1, ha.2.2⟩
        simp only [future, if_pos ha, F, if_pos hb, D, if_pos ha.1]
        exact le_rfl
      · simp only [future, if_neg ha]
        dsimp [F]
        split_ifs
        · exact mul_nonneg (div_nonneg (by norm_num) (Real.sqrt_nonneg _))
            (pow_nonneg (hDnonneg t a) _)
        · exact le_rfl
    have htp : 0 ≤ Real.rpow (t : ℝ) (-1 / 2 : ℝ) :=
      Real.rpow_nonneg (Nat.cast_nonneg t) _
    calc
      _ ≤ ∫ a, F a ∂P t := integral_mono (hFutureI t) hFi hdom
      _ ≤ CF * Real.rpow (t : ℝ) (-1 / 2 : ℝ) * Ax := hFb
      _ ≤ CF * Real.rpow (t : ℝ) (-1 / 2 : ℝ) *
          (8 * Shao.standardNormalTail x) := by gcongr
      _ = (8 * CF) * Real.rpow (t : ℝ) (-1 / 2 : ℝ) *
          Shao.standardNormalTail x := by ring
      _ ≤ _ := by gcongr
  have hE3 : 0 ≤ E3 := Real.rpow_nonneg (by norm_num) _
  have hCoverEarly : CL3 * E3 ≤ C := by
    calc
      _ ≤ (1 + CL1 + CL3 + CF + CS) * (1 + |E3|) := by
        apply mul_le_mul _ (show E3 ≤ 1 + |E3| by linarith [le_abs_self E3]) hE3
          (by positivity)
        linarith
      _ ≤ (100000 * (1 + CL1 + CL3 + CF + CS) * (1 + |Gshort|) *
          (1 + Real.sqrt K)) * (1 + |E3|) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        calc
          _ ≤ 100000 * (1 + CL1 + CL3 + CF + CS) := by nlinarith
          _ ≤ (100000 * (1 + CL1 + CL3 + CF + CS)) * (1 + |Gshort|) :=
            le_mul_of_one_le_right (by positivity) hGfactor
          _ ≤ _ := le_mul_of_one_le_right (by positivity) hKfactor
      _ = C := rfl
  have hEarlyScale : (n : ℝ) * Real.rpow ((n : ℝ) / 2) (-(3 : ℝ) / 2) =
      E3 / Real.sqrt (n : ℝ) := by
    simp only [Real.rpow_eq_pow]
    rw [div_eq_mul_one_div, Real.mul_rpow hNpos.le (by norm_num)]
    change (n : ℝ) * (Real.rpow (n : ℝ) (-(3 : ℝ) / 2) * E3) = _
    calc
      _ = E3 * (Real.rpow (n : ℝ) 1 * Real.rpow (n : ℝ) (-(3 : ℝ) / 2)) := by
        simp only [Real.rpow_eq_pow, Real.rpow_one]
        ring
      _ = E3 * Real.rpow (n : ℝ) (1 + (-(3 : ℝ) / 2)) := by
        simp only [Real.rpow_eq_pow]
        rw [← Real.rpow_add hNpos]
      _ = E3 * (1 / Real.sqrt (n : ℝ)) := by
        congr 1
        convert hHalfRpow (n : ℝ) hNpos using 1 <;> ring
      _ = _ := by ring
  have hEarly : (∑ t ∈ Finset.Icc ((n + 1) / 2) n,
      ∫ a, marked 3 t a ∂P t) ≤ C * delta * Ax := by
    let A : Finset ℕ := Finset.Icc ((n + 1) / 2) n
    have hcard : A.card ≤ n := by dsimp [A]; rw [Nat.card_Icc]; omega
    have hcardR : (A.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcard
    have hpoint (t : ℕ) (ht : t ∈ A) :
        (∫ a, marked 3 t a ∂P t) ≤
          CL3 * beta * Real.rpow ((n : ℝ) / 2) (-(3 : ℝ) / 2) * Ax := by
      obtain ⟨htlo, hthi⟩ := Finset.mem_Icc.mp ht
      have hmt : m ≤ t := hmEarly.trans htlo
      have hn2t : n ≤ 2 * t := by omega
      have htR : (n : ℝ) / 2 ≤ (t : ℝ) := by
        have hh : (n : ℝ) ≤ 2 * (t : ℝ) := by exact_mod_cast hn2t
        linarith
      apply (hRawLong3 t hmt).2.2.1.trans
      have hh := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (n : ℝ) / 2)
        htR (by norm_num : -(3 : ℝ) / 2 ≤ 0)
      simpa only [Nat.cast_ofNat, Real.rpow_eq_pow, beta, Ax] using
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hh (mul_nonneg hCL3.le hbetapos.le)) hAx)
    have hEarlyPow : 0 ≤ Real.rpow ((n : ℝ) / 2) (-(3 : ℝ) / 2) :=
      Real.rpow_nonneg (by positivity) _
    calc
      _ ≤ ∑ _t ∈ A, CL3 * beta * Real.rpow ((n : ℝ) / 2) (-(3 : ℝ) / 2) * Ax :=
        Finset.sum_le_sum hpoint
      _ = (A.card : ℝ) * (CL3 * beta * Real.rpow ((n : ℝ) / 2) (-(3 : ℝ) / 2) * Ax) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n : ℝ) * (CL3 * beta * Real.rpow ((n : ℝ) / 2) (-(3 : ℝ) / 2) * Ax) :=
        mul_le_mul_of_nonneg_right hcardR (by positivity)
      _ = (CL3 * E3) * delta * Ax := by
        calc
          _ = CL3 * beta * Ax * ((n : ℝ) * Real.rpow ((n : ℝ) / 2) (-(3 : ℝ) / 2)) := by ring
          _ = _ := by rw [hEarlyScale]; dsimp [delta]; ring
      _ ≤ _ := by gcongr
  have hGshort : 0 ≤ Gshort := by
    dsimp [Gshort]
    exact mul_nonneg (Real.Gamma_pos_of_pos (by norm_num)).le
      (Real.rpow_nonneg (by positivity) _)
  have hRetained : (1 / 2 : ℝ) ≤ ∫ z : ℝ, if z ^ 2 ≤ h0 then z ^ 2 else 0 ∂rho :=
    (Shao.C2.AuxiliaryThirdMomentTruncation.auxiliary_actual_third_moment_retains_half
      rho h2 h3 hsecond).2
  have hA3 (s : ℝ) (hs : 0 ≤ s) :
      Integrable (fun z : ℝ => |z| ^ 3 * Real.exp (-(s / 2) * z ^ 2)) rho ∧
      (∫ z : ℝ, |z| ^ 3 * Real.exp (-(s / 2) * z ^ 2) ∂rho) ≤ beta := by
    have hb (z : ℝ) : |z| ^ 3 * Real.exp (-(s / 2) * z ^ 2) ≤ |z| ^ 3 := by
      apply mul_le_of_le_one_right (pow_nonneg (abs_nonneg z) 3)
      exact Real.exp_le_one_iff.mpr (by
        nlinarith only [mul_nonneg hs (sq_nonneg z)])
    have hi : Integrable (fun z : ℝ => |z| ^ 3 * Real.exp (-(s / 2) * z ^ 2)) rho := by
      apply h3.mono' (((measurable_id.norm.pow_const (3 : ℕ)).mul
        (((measurable_id.pow_const (2 : ℕ)).const_mul (-(s / 2))).exp)).aestronglyMeasurable)
      exact ae_of_all _ fun z => by
        change ‖|z| ^ 3 * Real.exp (-(s / 2) * z ^ 2)‖ ≤ |z| ^ 3
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (pow_nonneg (abs_nonneg z) 3) (Real.exp_nonneg _))]
        exact hb z
    exact ⟨hi, integral_mono hi h3 hb⟩
  have hOneMarked : (fun a : Shao.Path 1 => marked 1 1 a) = fun _ => 0 := by
    funext a
    have ht1 : T 1 a = (a 0) ^ 2 := by simp [T, Shao.energy]
    have hd1 : d 1 a = a 0 := by simp [d, Shao.prefixSum_length]
    by_cases ha : 0 < T 1 a ∧ h0 ≤ T 1 a ∧
        (3 * x / 2) * Real.sqrt (T 1 a) ≤ |d 1 a|
    · have habs : 0 < |a 0| := by
        nlinarith only [ha.1, ht1, sq_abs (a 0), abs_nonneg (a 0)]
      have hh := ha.2.2
      rw [ht1, Real.sqrt_sq_eq_abs, hd1] at hh
      have hmul := mul_nonneg (show 0 ≤ x - 16 by linarith) (abs_nonneg (a 0))
      nlinarith only [hh, hmul, habs]
    · simp only [marked, if_neg ha]
  have hShortPoint (l : ℕ) (hl : 0 < l) :
      (∫ a, marked 1 (l + 1) a ∂P (l + 1)) ≤
        (CS * beta * Gshort) * (1 / Real.sqrt (l : ℝ)) := by
    have hlR : 0 < (l : ℝ) := by exact_mod_cast hl
    have hOld := hShort rho h2 hmean hsecond l h0 hh0
    let F : Shao.Path (l + 1) → ℝ := fun a =>
      if 0 < T (l + 1) a ∧ h0 ≤ T (l + 1) a then
        M (l + 1) a / Real.sqrt (T (l + 1) a) * D (l + 1) a ^ p else 0
    have hFeq : F = fun a : Shao.Path (l + 1) =>
        if 0 < Shao.energy a ∧ h0 ≤ Shao.energy a then
          |a 0| ^ 3 / (Real.sqrt (Shao.energy a)) ^ (1 : ℕ) *
            (1 + |Shao.prefixSum a (l + 1)| / Real.sqrt (Shao.energy a)) ^ p else 0 := by
      funext a
      dsimp [F, T, d, M, D]
      simp only [dif_pos (Nat.succ_pos l), Nat.succ_eq_add_one, pow_one]
      split_ifs <;> simp_all
    have hFi : Integrable F (P (l + 1)) := by rw [hFeq]; exact hOld.1
    let kernel : ℝ → ℝ := fun s =>
      Real.rpow s (-1 / 2 : ℝ) *
        (∫ z : ℝ, |z| ^ 3 * Real.exp (-(s / 2) * z ^ 2) ∂rho) *
          Real.exp (-c * s * (l : ℝ))
    have hKi : IntegrableOn kernel (Set.Ioo 0 (1 / h0)) := by
      simpa only [kernel, c, P, Nat.cast_one, if_pos hRetained,
        show (1 / 2 : ℝ) - 1 = -1 / 2 by ring] using hOld.2.1
    have hFb : (∫ a, F a ∂P (l + 1)) ≤ CS * ∫ s : ℝ in Set.Ioo 0 (1 / h0), kernel s := by
      rw [hFeq]
      simpa only [kernel, c, P, Nat.cast_one, if_pos hRetained,
        show (1 / 2 : ℝ) - 1 = -1 / 2 by ring] using hOld.2.2
    have hDom (a : Shao.Path (l + 1)) : marked 1 (l + 1) a ≤ F a := by
      dsimp [marked, F]
      by_cases ha : 0 < T (l + 1) a ∧ h0 ≤ T (l + 1) a
      · simp only [if_pos ha, pow_one]
        split_ifs
        · exact le_rfl
        · have hMn : 0 ≤ M (l + 1) a := by
            simp only [M, dif_pos (Nat.succ_pos l)]
            exact pow_nonneg (abs_nonneg _) 3
          exact mul_nonneg (div_nonneg hMn (Real.sqrt_nonneg _))
            (pow_nonneg (hDnonneg (l + 1) a) _)
      · have hb : ¬(0 < T (l + 1) a ∧ h0 ≤ T (l + 1) a ∧
            (3 * x / 2) * Real.sqrt (T (l + 1) a) ≤ |d (l + 1) a|) :=
          fun h => ha ⟨h.1, h.2.1⟩
        simp only [if_neg ha, if_neg hb, le_refl]
    have hGamma :=
      Shao.Probability.SourceSuffixScalarInterfaces.gamma_kernel
        (1 / 2) (c * (l : ℝ)) (by norm_num) (by positivity)
    let g : ℝ → ℝ := fun s => Real.rpow s (-1 / 2 : ℝ) * Real.exp (-(c * (l : ℝ)) * s)
    have hGiFull : IntegrableOn g (Set.Ioi 0) := by
      simpa only [g, show (1 / 2 : ℝ) - 1 = -1 / 2 by ring] using hGamma.1
    have hGi : IntegrableOn g (Set.Ioo 0 (1 / h0)) :=
      hGiFull.mono_set (fun s hs => hs.1)
    have hKernelBound : (∫ s : ℝ in Set.Ioo 0 (1 / h0), kernel s) ≤
        beta * (∫ s : ℝ in Set.Ioi 0, g s) := by
      calc
        _ ≤ ∫ s : ℝ in Set.Ioo 0 (1 / h0), beta * g s := by
          apply integral_mono_ae hKi (hGi.const_mul beta)
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
          have hh := (hA3 s hs.1.le).2
          dsimp [kernel, g]
          have he : -c * s * (l : ℝ) = -(c * (l : ℝ)) * s := by ring
          rw [he]
          calc
            _ = (Real.rpow s (-1 / 2 : ℝ) * Real.exp (-(c * (l : ℝ)) * s)) *
                (∫ z : ℝ, |z| ^ 3 * Real.exp (-(s / 2) * z ^ 2) ∂rho) := by
              simp only [Real.rpow_eq_pow]
              ring
            _ ≤ (Real.rpow s (-1 / 2 : ℝ) * Real.exp (-(c * (l : ℝ)) * s)) * beta :=
              mul_le_mul_of_nonneg_left hh (mul_nonneg
                (Real.rpow_nonneg hs.1.le _) (Real.exp_nonneg _))
            _ = _ := by
              simp only [Real.rpow_eq_pow]
              ring
        _ = beta * (∫ s : ℝ in Set.Ioo 0 (1 / h0), g s) := integral_const_mul _ _
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ hbetapos.le
          apply setIntegral_mono_set hGiFull
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
            exact mul_nonneg (Real.rpow_nonneg hs.le _) (Real.exp_nonneg _)
          · exact ae_of_all _ fun s (hs : s ∈ Set.Ioo 0 (1 / h0)) => hs.1
    have hHalfInv : Real.rpow (1 / (l : ℝ)) (1 / 2 : ℝ) = 1 / Real.sqrt (l : ℝ) := by
      simp only [Real.rpow_eq_pow]
      rw [one_div, Real.inv_rpow hlR.le, ← Real.sqrt_eq_rpow]
      simp only [one_div]
    have hScale : (∫ s : ℝ in Set.Ioi 0, g s) = Gshort / Real.sqrt (l : ℝ) := by
      calc
        _ = Real.rpow (1 / (c * (l : ℝ))) (1 / 2 : ℝ) * Real.Gamma (1 / 2) := by
          simpa only [g, show (1 / 2 : ℝ) - 1 = -1 / 2 by ring] using hGamma.2
        _ = _ := by
          simp only [Real.rpow_eq_pow]
          rw [show 1 / (c * (l : ℝ)) = (1 / c) * (1 / (l : ℝ)) by
            field_simp [ne_of_gt hc, ne_of_gt hlR],
            Real.mul_rpow (by positivity) (by positivity)]
          rw [show (1 / (l : ℝ)) ^ (1 / 2 : ℝ) = 1 / Real.sqrt (l : ℝ) from hHalfInv]
          dsimp [Gshort]
          ring
    calc
      _ ≤ ∫ a, F a ∂P (l + 1) := integral_mono (hMarkedI (l + 1) 1 (Or.inl rfl)) hFi hDom
      _ ≤ CS * ∫ s : ℝ in Set.Ioo 0 (1 / h0), kernel s := hFb
      _ ≤ CS * (beta * (∫ s : ℝ in Set.Ioi 0, g s)) :=
        mul_le_mul_of_nonneg_left hKernelBound hCS.le
      _ = _ := by rw [hScale]; ring
  have hMarkedN (q t : ℕ) (a : Shao.Path t) : 0 ≤ marked q t a := by
    dsimp [marked]
    split_ifs
    · exact mul_nonneg (div_nonneg (by dsimp [M]; split_ifs <;> positivity)
        (pow_nonneg (Real.sqrt_nonneg _) _)) (pow_nonneg (hDnonneg t a) _)
    · exact le_rfl
  let f : ℕ → ℝ := fun t => ∫ a, marked 1 t a ∂P t
  have hfNonneg (t : ℕ) : 0 ≤ f t := integral_nonneg (hMarkedN 1 t)
  have hfOne : f 1 = 0 := by
    dsimp [f]
    rw [hOneMarked]
    simp
  have hShiftShort : ∀ L : ℕ,
      (∑ t ∈ Finset.Icc 1 (L + 1), f t) =
        ∑ l ∈ Finset.Icc 1 L, f (l + 1) := by
    intro L
    induction L with
    | zero => simp [hfOne]
    | succ L ih =>
      change (∑ t ∈ Finset.Icc 1 ((L + 1) + 1), f t) =
        ∑ l ∈ Finset.Icc 1 (L + 1), f (l + 1)
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      exact (Finset.sum_Icc_succ_top (show 1 ≤ L + 1 by omega)
        (fun l => f (l + 1))).symm
  have hShortSum (N : ℕ) : (∑ t ∈ Finset.Icc 1 N, f t) ≤
      2 * CS * beta * Gshort * Real.sqrt (N : ℝ) := by
    cases N with
    | zero => simp
    | succ L =>
      change (∑ t ∈ Finset.Icc 1 (L + 1), f t) ≤ _
      rw [hShiftShort]
      calc
        _ ≤ ∑ l ∈ Finset.Icc 1 L,
            (CS * beta * Gshort) * (1 / Real.sqrt (l : ℝ)) := by
          apply Finset.sum_le_sum
          intro l hl
          exact hShortPoint l (Finset.mem_Icc.mp hl).1
        _ = (CS * beta * Gshort) *
            (∑ l ∈ Finset.Icc 1 L, 1 / Real.sqrt (l : ℝ)) := by
          rw [Finset.mul_sum]
        _ ≤ (CS * beta * Gshort) * (2 * Real.sqrt (L : ℝ)) :=
          mul_le_mul_of_nonneg_left (hSumInvSqrt L) (by positivity)
        _ ≤ 2 * CS * beta * Gshort * Real.sqrt ((L + 1 : ℕ) : ℝ) := by
          have hs : Real.sqrt (L : ℝ) ≤ Real.sqrt ((L + 1 : ℕ) : ℝ) :=
            Real.sqrt_le_sqrt (by exact_mod_cast (show L ≤ L + 1 by omega))
          calc
            _ = (2 * CS * beta * Gshort) * Real.sqrt (L : ℝ) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)
  have hSqrtH : Real.sqrt H = Real.sqrt K * beta * (1 + x) ^ 3 := by
    have he : H = K * (beta * (1 + x) ^ 3) ^ 2 := by dsimp [H]; ring
    rw [he, Real.sqrt_mul hKpos.le, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ beta * (1 + x) ^ 3)]
    ring
  have hSqrtM : Real.sqrt (m : ℝ) ≤ 2 * Real.sqrt K * beta * (1 + x) ^ 3 := by
    have hmH : (m : ℝ) ≤ (2 * Real.sqrt H) ^ 2 := by
      nlinarith only [Real.sq_sqrt hHpos.le, hm2H]
    have hs : Real.sqrt (m : ℝ) ≤ 2 * Real.sqrt H :=
      (Real.sqrt_le_iff).2 ⟨by positivity, hmH⟩
    rw [hSqrtH] at hs
    convert hs using 1 <;> ring
  have hLateSum : (∑ t ∈ Finset.Icc 1 (n / 2), f t) ≤
      2 * CL1 * beta * Ax * Real.sqrt (n : ℝ) +
        4 * CS * Gshort * Real.sqrt K * beta ^ 2 * (1 + x) ^ 3 := by
    let J : Finset ℕ := Finset.Icc 1 (n / 2)
    have hPoint (t : ℕ) (ht : t ∈ J) : f t ≤
        CL1 * beta * Ax * (1 / Real.sqrt (t : ℝ)) +
          (if t < m then f t else 0) := by
      by_cases htm : t < m
      · rw [if_pos htm]
        exact le_add_of_nonneg_left (by positivity)
      · rw [if_neg htm, add_zero]
        have htpos : 0 < (t : ℝ) := by
          exact_mod_cast (Finset.mem_Icc.mp ht).1
        have hh : f t ≤ CL1 * beta * Real.rpow (t : ℝ) (-1 / 2 : ℝ) * Ax := by
          simpa only [f, marked, M, T, d, D, P, beta, Ax, Nat.cast_one, pow_one] using
            (hRawLong1 t (by omega)).2.2.1
        rw [hHalfRpow (t : ℝ) htpos] at hh
        convert hh using 1 <;> ring
    have hSmallSubset : J.filter (fun t => t < m) ⊆ Finset.Icc 1 m := by
      intro t ht
      have htJ := (Finset.mem_filter.mp ht).1
      have htm := (Finset.mem_filter.mp ht).2
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp htJ).1, by omega⟩
    have hSmall : (∑ t ∈ J, if t < m then f t else 0) ≤
        4 * CS * Gshort * Real.sqrt K * beta ^ 2 * (1 + x) ^ 3 := by
      calc
        _ = ∑ t ∈ J.filter (fun t => t < m), f t := by rw [Finset.sum_filter]
        _ ≤ ∑ t ∈ Finset.Icc 1 m, f t := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hSmallSubset
          intro t ht hnot
          exact hfNonneg t
        _ ≤ 2 * CS * beta * Gshort * Real.sqrt (m : ℝ) := hShortSum m
        _ ≤ _ := by
          calc
            _ ≤ 2 * CS * beta * Gshort *
                (2 * Real.sqrt K * beta * (1 + x) ^ 3) :=
              mul_le_mul_of_nonneg_left hSqrtM (by positivity)
            _ = _ := by ring
    have hLongSum : (∑ t ∈ J,
        CL1 * beta * Ax * (1 / Real.sqrt (t : ℝ))) ≤
          2 * CL1 * beta * Ax * Real.sqrt (n : ℝ) := by
      calc
        _ = (CL1 * beta * Ax) *
            (∑ t ∈ Finset.Icc 1 (n / 2), 1 / Real.sqrt (t : ℝ)) := by
          dsimp [J]
          rw [Finset.mul_sum]
        _ ≤ (CL1 * beta * Ax) * (2 * Real.sqrt ((n / 2 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left (hSumInvSqrt (n / 2)) (by positivity)
        _ ≤ _ := by
          have hs : Real.sqrt ((n / 2 : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) :=
            Real.sqrt_le_sqrt (by exact_mod_cast (Nat.div_le_self n 2))
          calc
            _ = (2 * CL1 * beta * Ax) * Real.sqrt ((n / 2 : ℕ) : ℝ) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)
    calc
      _ ≤ ∑ t ∈ J,
          (CL1 * beta * Ax * (1 / Real.sqrt (t : ℝ)) +
            (if t < m then f t else 0)) := Finset.sum_le_sum hPoint
      _ = (∑ t ∈ J, CL1 * beta * Ax * (1 / Real.sqrt (t : ℝ))) +
          ∑ t ∈ J, if t < m then f t else 0 := Finset.sum_add_distrib
      _ ≤ _ := add_le_add hLongSum hSmall
  have hCoverLate : 16 * CL1 + 32 * CS * Gshort * Real.sqrt K ≤ C := by
    let F : ℝ := 1 + CL1 + CL3 + CF + CS
    let G : ℝ := 1 + |Gshort|
    let J : ℝ := 1 + Real.sqrt K
    have hF : 0 ≤ F := by dsimp [F]; positivity
    have hG : 1 ≤ G := by dsimp [G]; linarith [abs_nonneg Gshort]
    have hJ : 1 ≤ J := by dsimp [J]; linarith [Real.sqrt_nonneg K]
    have hL : CL1 ≤ F := by dsimp [F]; linarith
    have hS : CS ≤ F := by dsimp [F]; linarith
    have hGG : Gshort ≤ G := by dsimp [G]; linarith [le_abs_self Gshort]
    have hKJ : Real.sqrt K ≤ J := by dsimp [J]; linarith
    have hPart1 : 16 * CL1 ≤ 16 * F * G * J := by
      calc
        _ ≤ 16 * F := by gcongr
        _ ≤ (16 * F) * G := le_mul_of_one_le_right (by positivity) hG
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hJ
    have hPart2 : 32 * CS * Gshort * Real.sqrt K ≤ 32 * F * G * J := by
      gcongr
    calc
      _ ≤ 48 * F * G * J := by nlinarith only [hPart1, hPart2]
      _ = (48 * F * G * J) * 1 := by ring
      _ ≤ (100000 * F * G * J) * (1 + |E3|) := by
        apply mul_le_mul _ hEfactor (by norm_num) (by positivity)
        have hh : 0 ≤ F * G * J := by positivity
        nlinarith only [hh]
      _ = C := rfl
  have hLate : (1 / (n : ℝ)) * (∑ t ∈ Finset.Icc 1 (n / 2), f t) ≤
      C * delta * Shao.standardNormalTail x := by
    have hInvScale : (1 / (n : ℝ)) * Real.sqrt (n : ℝ) =
        1 / Real.sqrt (n : ℝ) := by
      apply (eq_div_iff (ne_of_gt hSqrtN)).2
      calc
        _ = (1 / (n : ℝ)) * (Real.sqrt (n : ℝ)) ^ 2 := by ring
        _ = 1 := by rw [Real.sq_sqrt hNpos.le]; field_simp
    have hDeltaU : delta * u = beta ^ 2 * (1 + x) ^ 3 / (n : ℝ) := by
      dsimp [u, delta]
      calc
        _ = beta ^ 2 * (1 + x) ^ 3 / (Real.sqrt (n : ℝ)) ^ 2 := by
          field_simp [ne_of_gt hSqrtN] <;> ring
        _ = _ := by rw [Real.sq_sqrt hNpos.le]
    have hScaleLong : (1 / (n : ℝ)) *
        (2 * CL1 * beta * Ax * Real.sqrt (n : ℝ)) = 2 * CL1 * delta * Ax := by
      calc
        _ = (2 * CL1 * beta * Ax) *
            ((1 / (n : ℝ)) * Real.sqrt (n : ℝ)) := by ring
        _ = _ := by rw [hInvScale]; dsimp [delta]; ring
    have hScaleShort : (1 / (n : ℝ)) *
        (4 * CS * Gshort * Real.sqrt K * beta ^ 2 * (1 + x) ^ 3) =
          (4 * CS * Gshort * Real.sqrt K) * delta * u := by
      calc
        _ = (4 * CS * Gshort * Real.sqrt K) *
            (beta ^ 2 * (1 + x) ^ 3 / (n : ℝ)) := by ring
        _ = _ := by rw [← hDeltaU]; ring
    calc
      _ ≤ (1 / (n : ℝ)) *
          (2 * CL1 * beta * Ax * Real.sqrt (n : ℝ) +
            4 * CS * Gshort * Real.sqrt K * beta ^ 2 * (1 + x) ^ 3) :=
        mul_le_mul_of_nonneg_left hLateSum (by positivity)
      _ = 2 * CL1 * delta * Ax +
          (4 * CS * Gshort * Real.sqrt K) * delta * u := by
        rw [mul_add, hScaleLong, hScaleShort]
      _ ≤ 2 * CL1 * delta * (8 * Shao.standardNormalTail x) +
          (4 * CS * Gshort * Real.sqrt K) * delta *
            (8 * Shao.standardNormalTail x) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hAxPsi (by positivity)
        · exact mul_le_mul_of_nonneg_left (hu.trans hSmallPsi) (by positivity)
      _ = (16 * CL1 + 32 * CS * Gshort * Real.sqrt K) *
          delta * Shao.standardNormalTail x := by ring
      _ ≤ _ := by gcongr
  refine ⟨hbeta, hh0, hHhalf, hm4, hh0m, hmn, ?_, hLong,
    hEarly, hLate, hFutureI, hFutureBound⟩
  intro t q hq
  exact ⟨hMarkedI t q hq, hUnmarkedI t q⟩

end Shao.Probability.SourceResidualRareSuffix
