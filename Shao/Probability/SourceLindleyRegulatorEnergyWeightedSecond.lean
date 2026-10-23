import Shao.Probability.SourceLindleyRegulatorEnergyWeighted
import Shao.Probability.SourceLindleyRegulatorSecondMoment
import Shao.Probability.FiniteSurvival

/-!
Actual prefix-energy weighted sums of squared Lindley regulators. The fixed
source conditional law need not be centered, nor does its energy tilt. The
finite survival estimate and raw-second/variance comparison are paid here.
-/

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators

private theorem ews_min_one_mul
    (u v A : ℝ) (hA : 1 ≤ A) (hu : u ≤ A * v) :
    min 1 u ≤ A * min 1 v := by
  by_cases hv : v ≤ 1
  · rw [min_eq_right hv]
    exact (min_le_right 1 u).trans hu
  · rw [min_eq_left (le_of_not_ge hv)]
    exact (min_le_left 1 u).trans (by simpa using hA)

private theorem ews_tilted_second_moment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (N : ℕ) (h κ y : ℝ)
    (hh : 0 < h) (hκ : 0 < κ)
    (hκsmall : κ ≤ (1 / 16 : ℝ)) (hy : 1 ≤ y)
    (hsupport : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (hsmall : (κ * y ^ 2) * h ^ 2 ≤ 1)
    (hNV : (1 / 2 : ℝ) ≤
      (N : ℝ) * variance (id : ℝ → ℝ) ν)
    (hΛ : (1 + y) * (N : ℝ) * |∫ a : ℝ, a ∂ν| +
      (1 + y) ^ 3 * (N : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂ν) ≤
        (1 / 2 : ℝ)) :
    let s : ℝ := κ * y ^ 2
    let ρ : Measure ℝ := ν.tilted (fun a => -s * a ^ 2)
    let V : ℝ := variance (id : ℝ → ℝ) ν
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    let T : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ρ)
    IsProbabilityMeasure ρ ∧
      (∀ i : Fin N,
        Integrable (fun a : Shao.Path N => (lindleyRegulator a i) ^ 2) T ∧
          (∫ a : Shao.Path N, (lindleyRegulator a i) ^ 2 ∂T) ≤
            (48 * Real.exp (14 + 3 * (1024 : ℝ))) * m3 /
              (Real.sqrt V * Real.sqrt ((i.val + 1 : ℕ) : ℝ))) := by
  classical
  dsimp only
  let s : ℝ := κ * y ^ 2
  let S : ℝ := s * h ^ 2
  let E : ℝ := Real.exp S
  let ρ : Measure ℝ := ν.tilted (fun a => -s * a ^ 2)
  let μ : ℝ := ∫ a : ℝ, a ∂ν
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
  let V : ℝ := variance (id : ℝ → ℝ) ν
  let μρ : ℝ := ∫ a : ℝ, a ∂ρ
  let m2ρ : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
  let m3ρ : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
  let Vρ : ℝ := variance (id : ℝ → ℝ) ρ
  let m3cρ : ℝ := ∫ a : ℝ, |a - μρ| ^ 3 ∂ρ
  let b : ℝ := 1 + y
  let L : ℝ := b * (N : ℝ) * |μ| + b ^ 3 * (N : ℝ) * m3
  let M : ℝ := |μ| + 2 * s * E * m3
  let A : ℝ := 8 * Real.exp (2 : ℝ)
  let Csurv : ℝ := 16 * Real.exp (12 + 3 * (1024 : ℝ))
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hS1 : S ≤ 1 := hsmall
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : 1 ≤ E := Real.one_le_exp_iff.mpr hS0
  have hE3 : E ≤ 3 :=
    (Real.exp_le_exp.mpr hS1).trans Real.exp_one_lt_three.le
  have hEinv : E * Real.exp (-S) = 1 := by
    dsimp [E]
    rw [← Real.exp_add]
    simp
  have hm30 : 0 ≤ m3 := integral_nonneg (fun a => pow_nonneg (abs_nonneg a) 3)
  have hm3ρ0 : 0 ≤ m3ρ := integral_nonneg (fun a => pow_nonneg (abs_nonneg a) 3)
  have hm3cρ0 : 0 ≤ m3cρ := integral_nonneg (fun a => pow_nonneg (abs_nonneg _) 3)
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hN : 0 < N := by
    by_contra hn
    have hz : N = 0 := Nat.eq_zero_of_not_pos hn
    simp only [hz, Nat.cast_zero, zero_mul] at hNV
    norm_num at hNV
  have hNp : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hV : 0 < V := by
    change (1 / 2 : ℝ) ≤ (N : ℝ) * V at hNV
    by_contra hv
    have hle := mul_nonpos_of_nonneg_of_nonpos hN0 (le_of_not_gt hv)
    linarith only [hNV, hle]
  have hb : 0 < b := by dsimp [b]; linarith
  have hb2 : 2 ≤ b := by dsimp [b]; linarith
  have hL : L ≤ (1 / 2 : ℝ) := hΛ
  have ht := boundedEnergyTilt_drift_decay ν h s hh hs hsupport hsmall
  dsimp only at ht
  obtain ⟨_, hp, _, _, _, h3ρ, _, _, _, _, _, hVlo, _, _, _, hm3lo,
    hm3up, hVeq, _, _, hμ, hc, _, _, _, _⟩ := ht
  change IsProbabilityMeasure ρ at hp
  letI : IsProbabilityMeasure ρ := hp
  change Integrable (fun a : ℝ => |a| ^ 3) ρ at h3ρ
  change Real.exp (-S) * V ≤ Vρ at hVlo
  change Real.exp (-S) * m3 ≤ m3ρ at hm3lo
  change m3ρ ≤ E * m3 at hm3up
  change Vρ = m2ρ - μρ ^ 2 at hVeq
  change |μρ| ≤ M at hμ
  change m3cρ ≤ 8 * E * m3 at hc
  have hVρ0 : 0 ≤ Vρ := variance_nonneg _ _
  have hEV : V ≤ E * Vρ := by
    have he := mul_le_mul_of_nonneg_left hVlo hE0.le
    rwa [← mul_assoc, hEinv, one_mul] at he
  have hNVρ : (1 / 6 : ℝ) ≤ (N : ℝ) * Vρ := by
    have he := mul_le_mul_of_nonneg_left hEV hN0
    have he3 := mul_le_mul_of_nonneg_right hE3 (mul_nonneg hN0 hVρ0)
    change (1 / 2 : ℝ) ≤ (N : ℝ) * V at hNV
    nlinarith only [he, he3, hNV]
  have hVρ : 0 < Vρ := by
    by_contra hv
    have he := mul_nonpos_of_nonneg_of_nonpos hN0 (le_of_not_gt hv)
    linarith only [hNVρ, he]
  -- The same source budget pays the actual tilted drift and raw-second ratio.
  have hcoeff : 2 * s * E ≤ b ^ 2 := by
    have he := mul_le_mul_of_nonneg_right hκsmall hE0.le
    have he1 : 2 * κ * E ≤ 1 := by nlinarith only [he, hE3]
    have hey := mul_le_mul_of_nonneg_right he1 (sq_nonneg y)
    have hy0 : 0 ≤ y := by linarith
    dsimp [s, b] at *
    nlinarith only [hey, hy0]
  have hNM : (N : ℝ) * M ≤ (1 / 4 : ℝ) := by
    have he := mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hN0 hm30)
    have heb := mul_le_mul_of_nonneg_left he hb.le
    have hNL : b * ((N : ℝ) * M) ≤ L := by
      dsimp only [M, L]
      nlinarith only [heb]
    have hdiv : (N : ℝ) * M ≤ L / b := (le_div_iff₀ hb).mpr (by nlinarith only [hNL])
    have hquarter : L / b ≤ (1 / 4 : ℝ) :=
      (div_le_iff₀ hb).mpr (by nlinarith only [hL, hb2])
    exact hdiv.trans hquarter
  have hμN : (N : ℝ) * |μρ| ≤ (11 / 32 : ℝ) := by
    have he := mul_le_mul_of_nonneg_left hμ hN0
    linarith only [he, hNM]
  have hμNsq := pow_le_pow_left₀ (mul_nonneg hN0 (abs_nonneg μρ)) hμN 2
  rw [mul_pow, sq_abs] at hμNsq
  have hNμ2 : (N : ℝ) * μρ ^ 2 ≤ Vρ := by
    by_contra hh
    have hp := mul_pos hNp (sub_pos.mpr (lt_of_not_ge hh))
    nlinarith only [hμNsq, hNVρ, hp]
  have hμ2 : μρ ^ 2 ≤ Vρ := by
    have he := mul_le_mul_of_nonneg_right hN1 (sq_nonneg μρ)
    nlinarith only [he, hNμ2]
  have hM2 : m2ρ ≤ 2 * Vρ := by nlinarith only [hVeq, hμ2]
  have hdrift (k : ℕ) (hk : k ≤ N) :
      |μρ| * Real.sqrt (k : ℝ) / Real.sqrt Vρ ≤ 1 := by
    have hkr : (k : ℝ) ≤ N := by exact_mod_cast hk
    have he := mul_le_mul_of_nonneg_left hkr (sq_nonneg μρ)
    have hkμ : μρ ^ 2 * (k : ℝ) ≤ Vρ := by nlinarith only [he, hNμ2]
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hVρ)).mpr
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, sq_abs, Real.sq_sqrt (Nat.cast_nonneg k), one_mul,
      Real.sq_sqrt hVρ.le]
    exact hkμ
  have hE2 : E ^ 2 ≤ Real.exp (2 : ℝ) := by
    calc
      E ^ 2 = Real.exp (S + S) := by dsimp [E]; rw [Real.exp_add]; ring
      _ ≤ Real.exp 2 := Real.exp_le_exp.mpr (by linarith only [hS1])
  have hrawinv : m3 ≤ E * m3ρ := by
    have he := mul_le_mul_of_nonneg_left hm3lo hE0.le
    rwa [← mul_assoc, hEinv, one_mul] at he
  have hcenter : m3cρ ≤ A * m3ρ := by
    have he := mul_le_mul_of_nonneg_left hrawinv (show 0 ≤ 8 * E by positivity)
    have he2 := mul_le_mul_of_nonneg_right hE2 (show 0 ≤ 8 * m3ρ by positivity)
    dsimp only [A]
    nlinarith only [hc, he, he2]
  have hA : 1 ≤ A := by
    have he : 1 ≤ Real.exp (2 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
    dsimp only [A]
    linarith only [he]
  have hC0 : 0 ≤ Csurv := by dsimp [Csurv]; positivity
  have hSurvival : lindleyPrefixSurvivalBound ρ N Csurv := by
    unfold lindleyPrefixSurvivalBound
    change ∀ k : ℕ, 1 ≤ k → k < N → ∀ r : ℝ, 0 ≤ r →
      (Measure.pi (fun _ : Fin k => ρ)).real
        {a : Shao.Path k | Shao.maxWithZero a ≤ r} ≤
      Csurv * min 1 ((r + m3ρ / Vρ) /
        (Real.sqrt Vρ * Real.sqrt ((k + 1 : ℕ) : ℝ)))
    intro k _ hkN r hr
    have hden : 0 < Real.sqrt Vρ * Real.sqrt ((k + 1 : ℕ) : ℝ) := by positivity
    have hratio : (r + m3cρ / Vρ) / (Real.sqrt Vρ * Real.sqrt ((k + 1 : ℕ) : ℝ)) ≤
        A * ((r + m3ρ / Vρ) / (Real.sqrt Vρ * Real.sqrt ((k + 1 : ℕ) : ℝ))) := by
      have hcdiv : m3cρ / Vρ ≤ A * (m3ρ / Vρ) := by
        convert div_le_div_of_nonneg_right hcenter hVρ.le using 1 <;> ring
      have har := mul_le_mul_of_nonneg_right hA hr
      have he := div_le_div_of_nonneg_right
        (show r + m3cρ / Vρ ≤ A * (r + m3ρ / Vρ) by nlinarith only [hcdiv, har]) hden.le
      convert he using 1 <;> ring
    have hmin := ews_min_one_mul _ _ A hA hratio
    have hexp : Real.exp (4 * (|μρ| * Real.sqrt (k : ℝ) / Real.sqrt Vρ)) ≤ Real.exp 4 :=
      Real.exp_le_exp.mpr (by linarith only [hdrift k (Nat.le_of_lt hkN)])
    have hmin0 : 0 ≤ min 1 ((r + m3cρ / Vρ) /
        (Real.sqrt Vρ * Real.sqrt ((k + 1 : ℕ) : ℝ))) := by positivity
    have hminraw0 : 0 ≤ min 1 ((r + m3ρ / Vρ) /
        (Real.sqrt Vρ * Real.sqrt ((k + 1 : ℕ) : ℝ))) := by positivity
    have hfinite := iid_closed_survival_nonzero_drift ρ h3ρ hVρ k r hr
    change (Measure.pi (fun _ : Fin k => ρ)).real
      {a : Shao.Path k | Shao.maxWithZero a ≤ r} ≤
      (2 * Real.exp (6 + 3 * (1024 : ℝ))) *
        min 1 ((r + m3cρ / Vρ) / (Real.sqrt Vρ * Real.sqrt ((k + 1 : ℕ) : ℝ))) *
        Real.exp (4 * (|μρ| * Real.sqrt (k : ℝ) / Real.sqrt Vρ)) at hfinite
    have heq : Real.exp (6 + 3 * (1024 : ℝ)) * Real.exp 2 * Real.exp 4 =
        Real.exp (12 + 3 * (1024 : ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ (2 * Real.exp (6 + 3 * (1024 : ℝ))) *
          min 1 ((r + m3cρ / Vρ) / (Real.sqrt Vρ * Real.sqrt ((k + 1 : ℕ) : ℝ))) *
          Real.exp (4 * (|μρ| * Real.sqrt (k : ℝ) / Real.sqrt Vρ)) := hfinite
      _ ≤ (2 * Real.exp (6 + 3 * (1024 : ℝ))) *
          (A * min 1 ((r + m3ρ / Vρ) / (Real.sqrt Vρ * Real.sqrt ((k + 1 : ℕ) : ℝ)))) *
          Real.exp 4 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hmin (by positivity)) hexp
          (Real.exp_pos _).le (by positivity)
      _ = (16 * (Real.exp (6 + 3 * (1024 : ℝ)) * Real.exp 2 * Real.exp 4)) *
          min 1 ((r + m3ρ / Vρ) / (Real.sqrt Vρ * Real.sqrt ((k + 1 : ℕ) : ℝ))) := by
        dsimp only [A]
        ring
      _ = _ := by rw [heq]
  have hlarge : 1 ≤ 3 * Csurv := by
    have he : 1 ≤ Real.exp (12 + 3 * (1024 : ℝ)) := Real.one_le_exp_iff.mpr (by norm_num)
    dsimp only [Csurv]
    linarith only [he]
  have hpaid := iid_lindleyRegulator_second_moment_of_survival ρ h3ρ hVρ hM2 N Csurv hC0 hSurvival
  dsimp only at hpaid
  have hrootρ : 0 < Real.sqrt Vρ := Real.sqrt_pos.mpr hVρ
  have hroot : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
  have hrootcmp : Real.sqrt V ≤ E * Real.sqrt Vρ := by
    have hEsq : E ≤ E ^ 2 := by nlinarith only [hE1]
    have he := mul_le_mul_of_nonneg_right hEsq hVρ0
    apply (sq_le_sq₀ (Real.sqrt_nonneg V) (by positivity)).mp
    rw [Real.sq_sqrt hV.le, mul_pow, Real.sq_sqrt hVρ.le]
    exact hEV.trans he
  have hratio : m3ρ / Real.sqrt Vρ ≤ Real.exp 2 * m3 / Real.sqrt V := by
    apply (div_le_div_iff₀ hrootρ hroot).mpr
    calc
      m3ρ * Real.sqrt V ≤ m3ρ * (E * Real.sqrt Vρ) :=
        mul_le_mul_of_nonneg_left hrootcmp hm3ρ0
      _ ≤ (E * m3) * (E * Real.sqrt Vρ) :=
        mul_le_mul_of_nonneg_right hm3up (by positivity)
      _ = E ^ 2 * (m3 * Real.sqrt Vρ) := by ring
      _ ≤ Real.exp 2 * (m3 * Real.sqrt Vρ) :=
        mul_le_mul_of_nonneg_right hE2 (by positivity)
      _ = _ := by ring
  refine ⟨hp, ?_⟩
  intro i
  obtain ⟨hi, hbnd⟩ := hpaid i
  rw [max_eq_right hlarge] at hbnd
  refine ⟨hi, ?_⟩
  have hexp : Real.exp (12 + 3 * (1024 : ℝ)) * Real.exp 2 =
      Real.exp (14 + 3 * (1024 : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ (48 * Real.exp (12 + 3 * (1024 : ℝ))) *
        (m3ρ / Real.sqrt Vρ) / Real.sqrt ((i.val + 1 : ℕ) : ℝ) := by
      convert hbnd using 1 <;> dsimp only [Csurv] <;> ring
    _ ≤ (48 * Real.exp (12 + 3 * (1024 : ℝ))) *
        (Real.exp 2 * m3 / Real.sqrt V) / Real.sqrt ((i.val + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio (by positivity)) (Real.sqrt_nonneg _)
    _ = (48 * (Real.exp (12 + 3 * (1024 : ℝ)) * Real.exp 2)) * m3 /
        (Real.sqrt V * Real.sqrt ((i.val + 1 : ℕ) : ℝ)) := by ring
    _ = _ := by rw [hexp]

/-- The actual fixed-cutoff source law pays full and every first-K squared
regulator sum with its genuine current-coordinate-inclusive prefix energy. -/
theorem sourceTruncation_lindleyRegulator_energy_weighted_second_sum
    (ν0 : Measure ℝ) [IsProbabilityMeasure ν0] (N : ℕ)
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν0)
    (hnorm : (N : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1)
    (hmean : (∫ a : ℝ, a ∂ν0) = 0)
    (x ε ε0 κ y : ℝ) (hx : 0 ≤ x) (hε : 0 < ε)
    (hε0 : 0 < ε0) (hε01 : ε0 ≤ 1) (hεsmall : ε ≤ ε0 / 2)
    (hR : Shao.truncationBudget ν0 N x ≤ ε ^ 3 / 8)
    (hκ : 0 < κ) (hκsmall : κ ≤ (1 / 16 : ℝ)) (hy : 1 ≤ y)
    (hwindow : |y - x| ≤ 1 / (2 * (1 + x))) :
    let ν : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ ε / (1 + x)}
    let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ν)
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    let V : ℝ := variance (id : ℝ → ℝ) ν
    let Λ : ℝ := (1 + y) * (N : ℝ) * |μ| +
      (1 + y) ^ 3 * (N : ℝ) * m3
    let U : Fin N → Shao.Path N → ℝ := fun i a => lindleyRegulator a i
    let Q : Fin N → Shao.Path N → ℝ := fun i a =>
      Shao.prefixSquares a (i.val + 1)
    let C : ℝ := 1024 * Real.exp (16 + 3 * (1024 : ℝ))
    let F : Shao.Path N → ℝ := fun a =>
      ∑ i : Fin N, U i a ^ 2 * Real.exp (-(κ * y ^ 2) * Q i a)
    IsProbabilityMeasure ν ∧
      (∀ᵐ a : ℝ ∂ν, |a| ≤ ε / (1 + x)) ∧
      (κ * y ^ 2) * (ε / (1 + x)) ^ 2 ≤ 1 ∧
      (3 / 4 : ℝ) ≤ (N : ℝ) * m2 ∧
      (N : ℝ) * V ≤ (4 / 3 : ℝ) ∧
      0 ≤ Λ ∧ Λ ≤ (1 / 2 : ℝ) ∧
      Integrable F P ∧ 0 ≤ (∫ a : Shao.Path N, F a ∂P) ∧
      (∫ a : Shao.Path N, F a ∂P) ≤
        C * (N : ℝ) * m3 / (Real.sqrt κ * (1 + y)) ∧
      (∫ a : Shao.Path N, F a ∂P) ≤
        C * Λ / (Real.sqrt κ * (1 + y) ^ 4) ∧
      (∀ K : ℕ, K ≤ N →
        let FK : Shao.Path N → ℝ := fun a =>
          ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < K),
            U i a ^ 2 * Real.exp (-(κ * y ^ 2) * Q i a)
        Integrable FK P ∧ 0 ≤ (∫ a : Shao.Path N, FK a ∂P) ∧
          (∫ a : Shao.Path N, FK a ∂P) ≤
            C * (N : ℝ) * m3 / (Real.sqrt κ * (1 + y)) ∧
          (∫ a : Shao.Path N, FK a ∂P) ≤
            C * Λ / (Real.sqrt κ * (1 + y) ^ 4)) := by
  classical
  dsimp only
  let ν : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ ε / (1 + x)}
  let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ν)
  let μ : ℝ := ∫ a : ℝ, a ∂ν
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
  let V : ℝ := variance (id : ℝ → ℝ) ν
  let b : ℝ := 1 + y
  let Λ : ℝ := b * (N : ℝ) * |μ| + b ^ 3 * (N : ℝ) * m3
  let h : ℝ := ε / (1 + x)
  let s : ℝ := κ * y ^ 2
  let Z : ℝ := ∫ a : ℝ, Real.exp (-s * a ^ 2) ∂ν
  let ρ : Measure ℝ := ν.tilted (fun a => -s * a ^ 2)
  let T : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ρ)
  let Cp : ℝ := 48 * Real.exp (14 + 3 * (1024 : ℝ))
  let C : ℝ := 1024 * Real.exp (16 + 3 * (1024 : ℝ))
  let t : ℝ := (s * m2 / 2) * (N : ℝ)
  let f : Fin N → Shao.Path N → ℝ := fun i a =>
    lindleyRegulator a i ^ 2 * Real.exp (-s * Shao.prefixSquares a (i.val + 1))
  let F : Shao.Path N → ℝ := fun a => ∑ i : Fin N, f i a
  have hsource := sourceTruncation_lindleyRegulator_energy_weighted_first_sum
    ν0 N h2 hnorm hmean x ε ε0 κ y hx hε hε0 hε01 hεsmall hR hκ hκsmall hy hwindow
  dsimp only at hsource
  obtain ⟨hp, hsp, hS, hraw, hVup, hL0, hLhalf, _, _, _, _⟩ := hsource
  change IsProbabilityMeasure ν at hp
  letI : IsProbabilityMeasure ν := hp
  have hεhalf : ε ≤ (1 / 2 : ℝ) := by linarith
  obtain ⟨_, _, _, _, _, hVp, hVlo, _⟩ := Shao.sourceTruncation_variance_bounds
    ν0 N h2 hnorm hmean x ε hx hε hεhalf hR
  change 0 < V at hVp
  change (1 / 2 : ℝ) ≤ (N : ℝ) * V at hVlo
  change (3 / 4 : ℝ) ≤ (N : ℝ) * m2 at hraw
  change 0 ≤ Λ at hL0
  change Λ ≤ (1 / 2 : ℝ) at hLhalf
  change ∀ᵐ a : ℝ ∂ν, |a| ≤ h at hsp
  change s * h ^ 2 ≤ 1 at hS
  have hh : 0 < h := by dsimp [h]; positivity
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hb : 0 < b := by dsimp [b]; linarith
  have hy0 : 0 ≤ y := by linarith
  have hN : 0 < N := by
    by_contra hn
    have hz : N = 0 := Nat.eq_zero_of_not_pos hn
    simp only [hz, Nat.cast_zero, zero_mul, zero_ne_one] at hnorm
  have hNp : 0 < (N : ℝ) := by exact_mod_cast hN
  have hm20 : 0 ≤ m2 := integral_nonneg (fun a => sq_nonneg a)
  have hm30 : 0 ≤ m3 := integral_nonneg (fun a => pow_nonneg (abs_nonneg a) 3)
  have hCp : 0 ≤ Cp := by dsimp [Cp]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hq : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have htilted := ews_tilted_second_moment ν N h κ y hh hκ hκsmall hy hsp hS hVlo hLhalf
  dsimp only at htilted
  obtain ⟨hρp, hsecond⟩ := htilted
  change IsProbabilityMeasure ρ at hρp
  letI : IsProbabilityMeasure ρ := hρp
  have hbqt := boundedEnergyTilt_drift_decay ν h s hh hs hsp hS
  dsimp only at hbqt
  obtain ⟨_, _, _, _, _, _, _, hZp, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hZpow, _⟩ := hbqt
  change 0 < Z at hZp
  change ∀ j : ℕ, Z ^ j ≤ Real.exp (-(s * m2 / 2) * (j : ℝ)) at hZpow
  have hfi (i : Fin N) : Integrable (f i) P ∧
      (∫ a : Shao.Path N, f i a ∂P) ≤
        (Cp * m3 / Real.sqrt V) *
          (Real.exp (-(s * m2 / 2) * ((i.val + 1 : ℕ) : ℝ)) /
            Real.sqrt ((i.val + 1 : ℕ) : ℝ)) := by
    have hc := iid_lindleyRegulator_prefix_energy_change_of_measure ν h s hh hs hsp N i
    dsimp only at hc
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hmom⟩ := hc
    obtain ⟨_, _, hi, _, heq⟩ := hmom 2 (Or.inr rfl)
    have hsquare := (hsecond i).2
    change (∫ a : Shao.Path N, lindleyRegulator a i ^ 2 ∂T) ≤
      Cp * m3 / (Real.sqrt V * Real.sqrt ((i.val + 1 : ℕ) : ℝ)) at hsquare
    have hB0 : 0 ≤ Cp * m3 / (Real.sqrt V * Real.sqrt ((i.val + 1 : ℕ) : ℝ)) := by positivity
    refine ⟨hi, ?_⟩
    calc
      _ = Z ^ (i.val + 1) * (∫ a : Shao.Path N, lindleyRegulator a i ^ 2 ∂T) := heq
      _ ≤ Z ^ (i.val + 1) * (Cp * m3 / (Real.sqrt V * Real.sqrt ((i.val + 1 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hsquare (pow_nonneg hZp.le _)
      _ ≤ Real.exp (-(s * m2 / 2) * ((i.val + 1 : ℕ) : ℝ)) *
          (Cp * m3 / (Real.sqrt V * Real.sqrt ((i.val + 1 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_right (hZpow _) hB0
      _ = _ := by ring
  have hfn (i : Fin N) (a : Shao.Path N) : 0 ≤ f i a := by dsimp [f]; positivity
  have hFI : Integrable F P := integrable_finsetSum Finset.univ (fun i _ => (hfi i).1)
  have hFE : (∫ a : Shao.Path N, F a ∂P) = ∑ i : Fin N, ∫ a, f i a ∂P :=
    integral_finsetSum Finset.univ (fun i _ => (hfi i).1)
  have hclock := finite_energy_decay_clocks N t ht0
  dsimp only at hclock
  have htdiv : t / (N : ℝ) = s * m2 / 2 := by
    dsimp [t]
    exact mul_div_cancel_right₀ _ (ne_of_gt hNp)
  rw [htdiv] at hclock
  let H : ℝ := ∑ i : Fin N,
    Real.exp (-(s * m2 / 2) * ((i.val + 1 : ℕ) : ℝ)) / Real.sqrt ((i.val + 1 : ℕ) : ℝ)
  have hH : H ≤ 4 * Real.sqrt (N : ℝ) / (1 + Real.sqrt t) := hclock.2.2.2.2.2.2.2
  have hsum : (∫ a : Shao.Path N, F a ∂P) ≤
      (Cp * m3 / Real.sqrt V) * (4 * Real.sqrt (N : ℝ) / (1 + Real.sqrt t)) := by
    calc
      _ = ∑ i : Fin N, ∫ a, f i a ∂P := hFE
      _ ≤ ∑ i : Fin N, (Cp * m3 / Real.sqrt V) *
          (Real.exp (-(s * m2 / 2) * ((i.val + 1 : ℕ) : ℝ)) /
            Real.sqrt ((i.val + 1 : ℕ) : ℝ)) :=
        Finset.sum_le_sum (fun i _ => (hfi i).2)
      _ = (Cp * m3 / Real.sqrt V) * H := by dsimp [H]; rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hH (by positivity)
  have hsqrtratio : Real.sqrt (N : ℝ) / Real.sqrt V ≤ 2 * (N : ℝ) := by
    have he := mul_le_mul_of_nonneg_left hVlo hNp.le
    have hroots : Real.sqrt (N : ℝ) ≤ 2 * (N : ℝ) * Real.sqrt V := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
      rw [Real.sq_sqrt hNp.le, mul_pow, mul_pow, Real.sq_sqrt hVp.le]
      nlinarith only [he, hNp.le]
    exact (div_le_iff₀ (Real.sqrt_pos.mpr hVp)).mpr hroots
  have htlow : (3 * κ / 8) * y ^ 2 ≤ t := by
    have he := mul_le_mul_of_nonneg_left hraw (show 0 ≤ κ * y ^ 2 / 2 by positivity)
    dsimp [t, s]
    nlinarith only [he]
  have htsqrt : (Real.sqrt κ / 2) * y ≤ Real.sqrt t := by
    have hκsq := Real.sq_sqrt hκ.le
    have htsq := Real.sq_sqrt ht0
    have hleft : 0 ≤ (Real.sqrt κ / 2) * y := by positivity
    have hlsq : ((Real.sqrt κ / 2) * y) ^ 2 ≤ t := by
      calc
        _ = (κ / 4) * y ^ 2 := by rw [mul_pow, div_pow, hκsq]; ring
        _ ≤ (3 * κ / 8) * y ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith only [hκ]) (sq_nonneg y)
        _ ≤ t := htlow
    nlinarith only [hlsq, htsq, Real.sqrt_nonneg t, hleft]
  have hq1 : Real.sqrt κ ≤ 1 := by
    have he := Real.sqrt_le_sqrt (show κ ≤ 1 by linarith only [hκsmall])
    simpa using he
  have hden : (Real.sqrt κ / 2) * b ≤ 1 + Real.sqrt t := by
    dsimp [b]
    nlinarith only [htsqrt, hq1]
  have hCpC : 16 * Cp ≤ C := by
    have he := Real.exp_le_exp.mpr (show (14 + 3 * (1024 : ℝ)) ≤ 16 + 3 * 1024 by norm_num)
    have hp := Real.exp_pos (14 + 3 * (1024 : ℝ))
    dsimp only [Cp, C]
    nlinarith only [he, hp]
  have hfull : (∫ a : Shao.Path N, F a ∂P) ≤ C * (N : ℝ) * m3 / (Real.sqrt κ * b) := by
    calc
      _ ≤ (Cp * m3 / Real.sqrt V) * (4 * Real.sqrt (N : ℝ) / (1 + Real.sqrt t)) := hsum
      _ = (4 * Cp * m3) * (Real.sqrt (N : ℝ) / Real.sqrt V) / (1 + Real.sqrt t) := by ring
      _ ≤ (4 * Cp * m3) * (2 * (N : ℝ)) / (1 + Real.sqrt t) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsqrtratio (by positivity)) (by positivity)
      _ ≤ (4 * Cp * m3) * (2 * (N : ℝ)) / ((Real.sqrt κ / 2) * b) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        exact mul_le_mul_of_nonneg_left hden (by positivity)
      _ = (16 * Cp) * (N : ℝ) * m3 / (Real.sqrt κ * b) := by field_simp; ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCpC hNp.le) hm30) (by positivity)
  have hbudget : C * (N : ℝ) * m3 / (Real.sqrt κ * b) ≤ C * Λ / (Real.sqrt κ * b ^ 4) := by
    have hD : b ^ 3 * (N : ℝ) * m3 ≤ Λ := by
      dsimp only [Λ]
      exact le_add_of_nonneg_left (by positivity)
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have he := mul_le_mul_of_nonneg_left hD (show 0 ≤ C * Real.sqrt κ * b by positivity)
    nlinarith only [he]
  refine ⟨hp, hsp, hS, hraw, hVup, hL0, hLhalf, hFI,
    integral_nonneg (fun a => Finset.sum_nonneg (fun i _ => hfn i a)),
    hfull, hfull.trans hbudget, ?_⟩
  intro K _
  let I := Finset.univ.filter (fun i : Fin N => i.val < K)
  have hKI : Integrable (fun a : Shao.Path N => ∑ i ∈ I, f i a) P :=
    integrable_finsetSum I (fun i _ => (hfi i).1)
  have hpoint (a : Shao.Path N) : (∑ i ∈ I, f i a) ≤ F a :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => hfn i a)
  have hle := integral_mono hKI hFI hpoint
  exact ⟨hKI, integral_nonneg (fun a => Finset.sum_nonneg (fun i _ => hfn i a)),
    hle.trans hfull, hle.trans (hfull.trans hbudget)⟩

end Shao.Probability
