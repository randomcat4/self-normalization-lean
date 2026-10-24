/-
Original-law small-boundary estimates from the accepted complete finite
survival, actual bad-clock payment, and exact conditional CDF pullback.
The maximum excludes time zero; all zero-energy paths and atoms are retained.
This auxiliary producer does not close any original root theorem.
-/
import Shao.Probability.SourceLindleySurvival
import Shao.Probability.OriginalCDFPullback
import Shao.Probability.SourceNoiseCost
import Shao.Probability.SourceDesmoothing
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Shao.Probability
open MeasureTheory ProbabilityTheory
open scoped BigOperators

private theorem sb_drift_bound
    (N : ℕ) (mu V : ℝ) (hN : 0 < (N : ℝ)) (hV : 0 < V)
    (hmu : (N : ℝ) * |mu| ≤ 1 / 8)
    (hNV : (1 / 2 : ℝ) ≤ (N : ℝ) * V) :
    |mu| * Real.sqrt (N : ℝ) / Real.sqrt V ≤ 1 / 4 := by
  have hmusq := pow_le_pow_left₀ (mul_nonneg hN.le (abs_nonneg mu)) hmu 2
  rw [mul_pow, sq_abs] at hmusq
  have hsmall : 16 * mu ^ 2 * (N : ℝ) ≤ V := by
    by_contra hh
    have hpos := mul_pos hN (sub_pos.mpr (lt_of_not_ge hh))
    nlinarith only [hmusq, hNV, hpos]
  have hroot : 0 < Real.sqrt V := Real.sqrt_pos.2 hV
  apply (div_le_iff₀ hroot).2
  apply (sq_le_sq₀ (by positivity) (by positivity)).1
  rw [mul_pow, sq_abs, Real.sq_sqrt (Nat.cast_nonneg N), mul_pow,
    Real.sq_sqrt hV.le]
  nlinarith only [hsmall]

private theorem sb_small_cdf
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 0 < n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (hR : Shao.truncationBudget nu n 0 ≤ (1 / 800 : ℝ) ^ 3 / 8) :
    let S : ℝ := 128 * Real.exp (7 + 3 * (1024 : ℝ))
    let D : ℝ := 32768 * Real.sqrt (2 * Real.pi) + 1 / Shao.standardNormalTail 2 + 1600
    let B : ℝ := S + D + 1 / (1 / 800 : ℝ) ^ 3
    ∀ t : ℝ, 0 ≤ t →
      (Measure.pi (fun _ : Fin n => nu)).real {v : Shao.Path n |
        0 < Shao.energy v ∧ Shao.maxWithZero v < t * Real.sqrt (Shao.energy v)} ≤
        B * (t + Shao.truncationBudget nu n 0) := by
  classical
  let e : ℝ := 1 / 800
  let R : ℝ := Shao.truncationBudget nu n 0
  let S : ℝ := 128 * Real.exp (7 + 3 * (1024 : ℝ))
  let D : ℝ := 32768 * Real.sqrt (2 * Real.pi) + 1 / Shao.standardNormalTail 2 + 1600
  let B : ℝ := S + D + 1 / e ^ 3
  let rho : Measure ℝ := cond nu {z : ℝ | |z| ≤ e}
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
  let P0 : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let mu : ℝ := ∫ z : ℝ, z ∂rho
  let V : ℝ := variance (id : ℝ → ℝ) rho
  let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
  let m3c : ℝ := ∫ z : ℝ, |z - mu| ^ 3 ∂rho
  have he : 0 < e := by norm_num [e]
  have heHalf : e ≤ 1 / 2 := by norm_num [e]
  have he800 : e ≤ 1 / 800 := le_rfl
  have hR' : R ≤ e ^ 3 / 8 := hR
  have hR0 : 0 ≤ R := Shao.truncationBudget_nonneg nu n h2 0
  have hNp : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlaw := Shao.sourceTruncation_law_data nu n h2 hnorm 0 e (by norm_num)
    he heHalf hR'
  simp only [add_zero, div_one] at hlaw
  have hp : IsProbabilityMeasure rho := hlaw.2.2.1
  letI : IsProbabilityMeasure rho := hp
  have h3r : Integrable (fun z : ℝ => |z| ^ 3) rho := hlaw.2.2.2.2.2.2.1
  have hpaid := Shao.sourceTruncation_paid_moments nu n h2 hnorm hmean 0 e
    (by norm_num) he heHalf hR'
  simp only [add_zero, div_one, mul_one, one_pow] at hpaid
  have hmu : (n : ℝ) * |mu| ≤ 2 * R / e ^ 2 := hpaid.1
  have hcentered : m3c ≤ 8 * m3 := hpaid.2.2.2.2
  have hvdata := Shao.sourceTruncation_variance_bounds nu n h2 hnorm hmean 0 e
    (by norm_num) he heHalf hR'
  simp only [add_zero, div_one] at hvdata
  have hV : 0 < V := hvdata.2.2.2.2.2.1
  have hNV : (1 / 2 : ℝ) ≤ (n : ℝ) * V := hvdata.2.2.2.2.2.2.1
  have hgdata := Shao.sourceTruncation_gamma_bounds nu n h2 hnorm hmean 0 e
    (by norm_num) he heHalf hR'
  simp only [add_zero, div_one] at hgdata
  have hgamma : m3 / V ≤ 4 * R := hgdata.2.2.2.2.2.2.2.2
  have hmuN : (n : ℝ) * |mu| ≤ 1 / 8 := by
    apply hmu.trans
    apply (div_le_iff₀ (pow_pos he 2)).2
    norm_num [e, R] at hR' ⊢
    linarith only [hR']
  have hdrift := sb_drift_bound n mu V hNp hV hmuN hNV
  have hden : 0 < Real.sqrt V * Real.sqrt ((n + 1 : ℕ) : ℝ) := by positivity
  have hdenLo : (1 / 2 : ℝ) ≤ Real.sqrt V * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    apply (sq_le_sq₀ (by norm_num) (by positivity)).1
    rw [mul_pow, Real.sq_sqrt hV.le, Real.sq_sqrt (by positivity)]
    push_cast
    nlinarith only [hNV, hV]
  have hc : m3c / V ≤ 32 * R := by
    have hh := div_le_div_of_nonneg_right hcentered hV.le
    calc
      _ ≤ 8 * (m3 / V) := by convert hh using 1 <;> ring
      _ ≤ 32 * R := by linarith only [hgamma]
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).1
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
  have hD : 0 ≤ D := by
    have ht := (Shao.standardNormalTail_basic.2.2.1 2).1
    dsimp [D]
    positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hclock := (Shao.sourceTruncation_noise_badClock_weighted_cost nu n h2 hnorm
    hmean 0 e (by norm_num) he he800 hR').2
  simp only [add_zero, div_one, one_mul] at hclock
  have hnoise0 : 0 ≤ Shao.standardNormalDensity 0 *
      (∫ z : ℝ × ℝ, 4 * (|z.1| + |z.2|) ∂Shao.Probability.quadraticFullNoiseLaw rho) := by
    apply mul_nonneg
    · exact (ProbabilityTheory.gaussianPDFReal_pos 0 1 0 (by norm_num)).le
    · exact integral_nonneg (fun z => by positivity)
  have hbad : P.real {v : Shao.Path n | Shao.energy v ∉ Set.Icc (1 / 4 : ℝ) 2} ≤ D * R := by
    change P.real {v : Shao.Path n | Shao.energy v ∉ Set.Icc (1 / 4 : ℝ) 2} +
      Shao.standardNormalDensity 0 *
        (∫ z : ℝ × ℝ, 4 * (|z.1| + |z.2|) ∂Shao.Probability.quadraticFullNoiseLaw rho) ≤
          D * R * Shao.standardNormalTail 0 at hclock
    rw [Shao.standardNormalTail_basic.2.1] at hclock
    nlinarith only [hclock, hnoise0, mul_nonneg hD hR0]
  obtain ⟨_, _, hPB⟩ := sourceTruncation_original_max_cdf_pullback
  have hpb := hPB nu n hn h2 hmean hnorm 0 e (by norm_num) he he800 hR'
  simp only [add_zero, div_one] at hpb
  let N : Set (Shao.Path n) := {v | ∀ j : Fin n, |v j| ≤ e}
  let p : ℝ := P0.real N
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hp1 : p ≤ 1 := hpb.2.1
  have hcomp : 1 - p ≤ R / e ^ 3 := hpb.2.2.1
  have hcond : cond P0 N = P := hpb.2.2.2.2.2.1
  have hNm : MeasurableSet N := by
    have hset : N = ⋂ i : Fin n, {v : Shao.Path n | |v i| ≤ e} := by
      ext v; simp only [N, Set.mem_setOf_eq, Set.mem_iInter]
    rw [hset]
    exact MeasurableSet.iInter (fun i : Fin n => measurableSet_le
      (continuous_abs.measurable.comp (measurable_pi_apply i)) measurable_const)
  change ∀ t : ℝ, 0 ≤ t → P0.real {v : Shao.Path n |
    0 < Shao.energy v ∧ Shao.maxWithZero v < t * Real.sqrt (Shao.energy v)} ≤ B * (t + R)
  intro t ht
  have hsurv := iid_closed_survival_nonzero_drift rho h3r hV n (t * Real.sqrt 2)
    (mul_nonneg ht (Real.sqrt_nonneg _))
  change P.real {v : Shao.Path n | Shao.maxWithZero v ≤ t * Real.sqrt 2} ≤
    (2 * Real.exp (6 + 3 * (1024 : ℝ))) *
      min 1 ((t * Real.sqrt 2 + m3c / V) /
        (Real.sqrt V * Real.sqrt ((n + 1 : ℕ) : ℝ))) *
      Real.exp (4 * (|mu| * Real.sqrt (n : ℝ) / Real.sqrt V)) at hsurv
  have hratio : (t * Real.sqrt 2 + m3c / V) /
      (Real.sqrt V * Real.sqrt ((n + 1 : ℕ) : ℝ)) ≤ 4 * t + 64 * R := by
    apply (div_le_iff₀ hden).2
    have hnumer : t * Real.sqrt 2 + m3c / V ≤ 2 * t + 32 * R := by
      simpa only [mul_comm t 2] using add_le_add (mul_le_mul_of_nonneg_left hsqrt2 ht) hc
    have hh := mul_le_mul_of_nonneg_left hdenLo
      (show 0 ≤ 4 * t + 64 * R by positivity)
    nlinarith only [hnumer, hh]
  have hmin := (min_le_right 1 _).trans hratio
  have hexp : Real.exp (4 * (|mu| * Real.sqrt (n : ℝ) / Real.sqrt V)) ≤ Real.exp 1 :=
    Real.exp_le_exp.2 (by linarith only [hdrift])
  have heq : Real.exp (6 + 3 * (1024 : ℝ)) * Real.exp 1 =
      Real.exp (7 + 3 * (1024 : ℝ)) := by rw [← Real.exp_add]; norm_num
  have hsurv' : P.real {v : Shao.Path n | Shao.maxWithZero v ≤ t * Real.sqrt 2} ≤
      S * (t + R) := by
    apply hsurv.trans
    calc
      _ ≤ (2 * Real.exp (6 + 3 * (1024 : ℝ))) * (4 * t + 64 * R) * Real.exp 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hmin (by positivity)) hexp
          (Real.exp_pos _).le (by positivity)
      _ = Real.exp (7 + 3 * (1024 : ℝ)) * (8 * t + 128 * R) := by
        calc
          _ = (Real.exp (6 + 3 * (1024 : ℝ)) * Real.exp 1) * (8 * t + 128 * R) := by ring
          _ = _ := by rw [heq]
      _ ≤ S * (t + R) := by dsimp [S]; nlinarith only [mul_nonneg (Real.exp_pos (7 + 3 * (1024 : ℝ))).le ht]
  let A : Set (Shao.Path n) := {v | 0 < Shao.energy v ∧
    Shao.maxWithZero v < t * Real.sqrt (Shao.energy v)}
  have hsub : A ⊆ {v : Shao.Path n | Shao.maxWithZero v ≤ t * Real.sqrt 2} ∪
      {v : Shao.Path n | Shao.energy v ∉ Set.Icc (1 / 4 : ℝ) 2} := by
    intro v hv
    by_cases hQ : Shao.energy v ≤ 2
    · left
      exact hv.2.le.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hQ) ht)
    · right
      intro hmem
      exact hQ hmem.2
  have hF : P.real A ≤ (S + D) * (t + R) := by
    apply (measureReal_mono hsub).trans
    apply (measureReal_union_le _ _).trans
    calc
      _ ≤ S * (t + R) + D * R := add_le_add hsurv' hbad
      _ ≤ (S + D) * (t + R) := by nlinarith only [mul_nonneg hD ht]
  have hmul : P.real A * p = P0.real (N ∩ A) := by
    simpa only [hcond, p, Measure.real_def, ENNReal.toReal_mul] using
      congrArg ENNReal.toReal (cond_mul_eq_inter hNm A P0)
  have hsplit := measureReal_inter_add_sdiff (μ := P0) (s := A) hNm
  have hrem : P0.real (A \ N) ≤ 1 - p := by
    have hh := measureReal_mono (μ := P0) (show A \ N ⊆ Nᶜ from fun _ hv => hv.2)
    rwa [measureReal_compl hNm, probReal_univ] at hh
  rw [Set.inter_comm A N, ← hmul] at hsplit
  have hpF : P.real A * p ≤ P.real A := by
    nlinarith only [hp1, measureReal_nonneg (μ := P) (s := A)]
  change P0.real A ≤ B * (t + R)
  calc
    _ ≤ P.real A + (1 - p) := by linarith only [hsplit, hpF, hrem]
    _ ≤ (S + D) * (t + R) + R / e ^ 3 := add_le_add hF hcomp
    _ ≤ B * (t + R) := by
      dsimp [B]
      have hh : 0 ≤ t / e ^ 3 := div_nonneg ht (pow_pos he 3).le
      calc
        _ = (S + D + 1 / e ^ 3) * (t + R) - t / e ^ 3 := by ring
        _ ≤ _ := sub_le_self _ hh

private theorem sb_reference_bounds (t : ℝ) (ht : 0 ≤ t) (htHalf : t ≤ 1 / 2) :
    let G : ℝ → ℝ := fun u => if 0 < u then 1 - 2 * Shao.standardNormalTail u else 0
    0 ≤ G t ∧ G t ≤ 1 ∧
      G t ≤ (2 * Real.exp 2 * Shao.standardNormalDensity 0) * t := by
  dsimp only
  have htail := Shao.standardNormalTail_basic.1 ht
  rw [Shao.standardNormalTail_basic.2.1] at htail
  have hT := (Shao.standardNormalTail_basic.2.2.1 t).1.le
  have hlip := sourceReferenceG_local_lipschitz 0 0 t (by norm_num)
    (by norm_num) (by rw [sub_zero, abs_of_nonneg ht]; norm_num; linarith)
  simp only [lt_self_iff_false, if_false, sub_zero, abs_of_nonneg ht] at hlip
  have hG0 : 0 ≤ (if 0 < t then 1 - 2 * Shao.standardNormalTail t else 0) := by
    split_ifs <;> linarith
  refine ⟨hG0, ?_, ?_⟩
  · split_ifs <;> linarith
  · rw [abs_of_nonneg hG0] at hlip
    exact hlip

theorem original_maximum_near_zero_cdf :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu]
        (n : ℕ) (hn : 0 < n),
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 →
        (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        let P0 : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
        let r0 : ℝ := Shao.truncationBudget nu n 0
        let G : ℝ → ℝ := fun t =>
          if 0 < t then 1 - 2 * Shao.standardNormalTail t else 0
        P0.real {v : Shao.Path n | Shao.upperMax v hn < 0} ≤ C * r0 ∧
          ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 →
            |P0.real {v : Shao.Path n |
              0 < Shao.energy v ∧
                Shao.maxWithZero v < t * Real.sqrt (Shao.energy v)} - G t| ≤
              C * (t + r0) := by
  classical
  let e : ℝ := 1 / 800
  let S : ℝ := 128 * Real.exp (7 + 3 * (1024 : ℝ))
  let D : ℝ := 32768 * Real.sqrt (2 * Real.pi) + 1 / Shao.standardNormalTail 2 + 1600
  let B : ℝ := S + D + 1 / e ^ 3
  let g : ℝ := 2 * Real.exp 2 * Shao.standardNormalDensity 0
  let C : ℝ := 2 * B + g + 8 / e ^ 3 + 1
  have he : 0 < e := by norm_num [e]
  have hB : 0 < B := by
    have hT := (Shao.standardNormalTail_basic.2.2.1 2).1
    dsimp [B, S, D]
    positivity
  have hg : 0 < g := by
    have hd : 0 < Shao.standardNormalDensity 0 :=
      ProbabilityTheory.gaussianPDFReal_pos 0 1 0 (by norm_num)
    dsimp [g]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have h8 : 0 < 8 / e ^ 3 := by positivity
  have hBC : 2 * B ≤ C := by dsimp [C]; linarith only [hg, h8]
  have hBgC : B + g ≤ C := by dsimp [C]; linarith only [hB, h8]
  have hlargeC : 8 / e ^ 3 ≤ C := by dsimp [C]; linarith only [hB, hg]
  refine ⟨C, hC, ?_⟩
  intro nu hnu n hn h2 hmean hnorm
  letI : IsProbabilityMeasure nu := hnu
  let P0 : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let R : ℝ := Shao.truncationBudget nu n 0
  let G : ℝ → ℝ := fun t => if 0 < t then 1 - 2 * Shao.standardNormalTail t else 0
  have hR0 : 0 ≤ R := Shao.truncationBudget_nonneg nu n h2 0
  change P0.real {v : Shao.Path n | Shao.upperMax v hn < 0} ≤ C * R ∧
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 → |P0.real {v : Shao.Path n |
      0 < Shao.energy v ∧ Shao.maxWithZero v < t * Real.sqrt (Shao.energy v)} - G t| ≤ C * (t + R)
  by_cases hbig : e ^ 3 / 8 ≤ R
  · have hpay : 1 ≤ C * R := by
      have hh : 1 ≤ (8 / e ^ 3) * R := by
        norm_num [e] at hbig ⊢
        linarith only [hbig]
      exact hh.trans (mul_le_mul_of_nonneg_right hlargeC hR0)
    refine ⟨(measureReal_le_one).trans hpay, ?_⟩
    intro t ht hth
    obtain ⟨hG0, hG1, _⟩ := sb_reference_bounds t ht hth
    have hF0 : 0 ≤ P0.real {v : Shao.Path n | 0 < Shao.energy v ∧
      Shao.maxWithZero v < t * Real.sqrt (Shao.energy v)} := measureReal_nonneg
    have hF1 : P0.real {v : Shao.Path n | 0 < Shao.energy v ∧
      Shao.maxWithZero v < t * Real.sqrt (Shao.energy v)} ≤ 1 := measureReal_le_one
    have herr : |P0.real {v : Shao.Path n | 0 < Shao.energy v ∧
      Shao.maxWithZero v < t * Real.sqrt (Shao.energy v)} - G t| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> linarith only [hF0, hF1, hG0, hG1]
    exact herr.trans (by nlinarith only [hpay, mul_nonneg hC.le ht])
  · have hsmall : R ≤ e ^ 3 / 8 := le_of_lt (lt_of_not_ge hbig)
    have hF := sb_small_cdf nu n hn h2 hmean hnorm hsmall
    change ∀ t : ℝ, 0 ≤ t → P0.real {v : Shao.Path n | 0 < Shao.energy v ∧
      Shao.maxWithZero v < t * Real.sqrt (Shao.energy v)} ≤ B * (t + R) at hF
    have hsecond : 0 < ∫ z : ℝ, z ^ 2 ∂nu := by
      by_contra h
      have hh := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (le_of_not_gt h)
      rw [hnorm] at hh
      norm_num at hh
    have hRp : 0 < R := Shao.truncationBudget_pos nu n h2 hn hsecond 0 (by norm_num)
    have hsub : {v : Shao.Path n | Shao.upperMax v hn < 0} ⊆
        {v : Shao.Path n | 0 < Shao.energy v ∧
          Shao.maxWithZero v < R * Real.sqrt (Shao.energy v)} := by
      intro v hv
      change Shao.upperMax v hn < 0 at hv
      have hQ : 0 < Shao.energy v := by
        by_contra h
        have hz := le_antisymm (le_of_not_gt h) (Shao.energy_nonneg v)
        rw [Shao.upperMax_eq_zero_of_energy_eq_zero v hn hz] at hv
        exact (lt_irrefl 0) hv
      refine ⟨hQ, ?_⟩
      rw [Shao.maxWithZero_eq v hn, max_eq_left hv.le]
      exact mul_pos hRp (Real.sqrt_pos.mpr hQ)
    refine ⟨?_, ?_⟩
    · calc
        _ ≤ P0.real {v : Shao.Path n | 0 < Shao.energy v ∧
            Shao.maxWithZero v < R * Real.sqrt (Shao.energy v)} := measureReal_mono hsub
        _ ≤ B * (R + R) := hF R hR0
        _ ≤ C * R := by nlinarith only [mul_le_mul_of_nonneg_right hBC hR0]
    · intro t ht hth
      obtain ⟨hG0, _, hG⟩ := sb_reference_bounds t ht hth
      have hFt := hF t ht
      have hF0 : 0 ≤ P0.real {v : Shao.Path n | 0 < Shao.energy v ∧
        Shao.maxWithZero v < t * Real.sqrt (Shao.energy v)} := measureReal_nonneg
      apply abs_le.mpr
      have hCg := mul_le_mul_of_nonneg_right hBgC (show 0 ≤ t + R by positivity)
      have hgR := mul_nonneg hg.le hR0
      constructor <;> nlinarith only [hG0, hG, hFt, hF0, hCg, hgR, mul_nonneg hB.le (show 0 ≤ t + R by positivity)]

theorem original_maximum_near_zero_weak_crossing :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu]
        (n : ℕ) (hn : 0 < n),
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 →
        (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 →
          |(Measure.pi (fun _ : Fin n => nu)).real (Shao.upperCrossing hn t) /
              Shao.standardNormalTail t - 2| ≤
            C * (t + Shao.truncationBudget nu n 0) := by
  classical
  obtain ⟨C, hC, hbound⟩ := original_maximum_near_zero_cdf
  let T : ℝ := Shao.standardNormalTail (1 / 2)
  have hT : 0 < T := (Shao.standardNormalTail_basic.2.2.1 (1 / 2)).1
  refine ⟨2 * C + C / T, by positivity, ?_⟩
  intro nu hnu n hn h2 hmean hnorm t ht hth
  letI : IsProbabilityMeasure nu := hnu
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let R : ℝ := Shao.truncationBudget nu n 0
  have hR : 0 ≤ R := Shao.truncationBudget_nonneg nu n h2 0
  obtain ⟨hzero, hnear⟩ := hbound nu n hn h2 hmean hnorm
  by_cases htp : 0 < t
  · have herr := hnear t ht hth
    simp only [if_pos htp] at herr
    have hid := (sourcePositiveCDF_weak_tail_error_identity hn P t htp).2
    have htail : T ≤ Shao.standardNormalTail t := Shao.standardNormalTail_basic.1 hth
    have htailp := (Shao.standardNormalTail_basic.2.2.1 t).1
    change |P.real (Shao.upperCrossing hn t) / Shao.standardNormalTail t - 2| ≤ _
    rw [← hid]
    calc
      _ ≤ (C * (t + R)) / Shao.standardNormalTail t :=
        div_le_div_of_nonneg_right herr htailp.le
      _ ≤ (C * (t + R)) / T :=
        div_le_div_of_nonneg_left (by positivity) hT htail
      _ ≤ (2 * C + C / T) * (t + R) := by
        have hh := mul_nonneg (show 0 ≤ 2 * C by positivity) (show 0 ≤ t + R by positivity)
        calc
          _ = (2 * C + C / T) * (t + R) - 2 * C * (t + R) := by ring
          _ ≤ _ := sub_le_self _ hh
  · have ht0 : t = 0 := le_antisymm (le_of_not_gt htp) ht
    subst t
    have heq : {v : Shao.Path n | Shao.upperMax v hn < 0} = (Shao.upperCrossing hn 0)ᶜ := by
      ext v
      simp only [Shao.upperCrossing, zero_mul, Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    have hprob : P.real {v : Shao.Path n | Shao.upperMax v hn < 0} =
        1 - P.real (Shao.upperCrossing hn 0) := by
      rw [heq, measureReal_compl (Shao.measurableSet_upperCrossing hn 0), probReal_univ]
    have hneg : 0 ≤ P.real {v : Shao.Path n | Shao.upperMax v hn < 0} := measureReal_nonneg
    have herr : |P.real (Shao.upperCrossing hn 0) / Shao.standardNormalTail 0 - 2| =
        2 * P.real {v : Shao.Path n | Shao.upperMax v hn < 0} := by
      rw [Shao.standardNormalTail_basic.2.1]
      have hexpr : P.real (Shao.upperCrossing hn 0) / (1 / 2 : ℝ) - 2 =
          -2 * P.real {v : Shao.Path n | Shao.upperMax v hn < 0} := by linarith only [hprob]
      rw [hexpr, abs_mul, abs_of_nonneg hneg]
      norm_num
    change |P.real (Shao.upperCrossing hn 0) / Shao.standardNormalTail 0 - 2| ≤ _
    rw [herr, zero_add]
    change P.real {v : Shao.Path n | Shao.upperMax v hn < 0} ≤ C * R at hzero
    have hh := mul_nonneg (show 0 ≤ C / T by positivity) hR
    nlinarith only [hzero, hh]

end Shao.Probability
