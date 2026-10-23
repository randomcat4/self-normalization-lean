import Shao.Probability.FiniteSurvival
import Shao.Probability.SourceLindleyRegulatorSecondMoment

/-!
The original source truncation budget pays the actual conditional-law survival
input and hence the accepted Lindley regulator square-moment bound. The law is
fixed at the original cutoff; its mean is allowed to be nonzero.
-/

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped Topology

private theorem sl_drift_bound
    (N k : ℕ) (mu V : ℝ) (hN : 0 < (N : ℝ)) (hV : 0 < V)
    (hmu : (N : ℝ) * |mu| ≤ 1 / 8)
    (hNV : (1 / 2 : ℝ) ≤ (N : ℝ) * V) (hk : k ≤ N) :
    |mu| * Real.sqrt (k : ℝ) / Real.sqrt V ≤ 1 / 4 := by
  have hmusq := pow_le_pow_left₀ (mul_nonneg hN.le (abs_nonneg mu)) hmu 2
  rw [mul_pow, sq_abs] at hmusq
  have hkr : (k : ℝ) ≤ N := by exact_mod_cast hk
  have hmk := mul_le_mul_of_nonneg_left hkr (sq_nonneg mu)
  have hmkN := mul_le_mul_of_nonneg_left hmk hN.le
  have hsmall : 16 * mu ^ 2 * (k : ℝ) ≤ V := by
    by_contra hh
    have hpos := mul_pos hN (sub_pos.mpr (lt_of_not_ge hh))
    nlinarith only [hmusq, hmkN, hNV, hpos]
  have hroot : 0 < Real.sqrt V := Real.sqrt_pos.2 hV
  apply (div_le_iff₀ hroot).2
  apply (sq_le_sq₀ (by positivity) (by positivity)).1
  rw [mul_pow, sq_abs, Real.sq_sqrt (Nat.cast_nonneg k), mul_pow,
    Real.sq_sqrt hV.le]
  nlinarith only [hsmall]

private theorem sl_min_one_eight (u v : ℝ) (hv : 0 ≤ v) (hu : u ≤ 8 * v) :
    min 1 u ≤ 8 * min 1 v := by
  by_cases h : v ≤ 1
  · rw [min_eq_right h]
    exact (min_le_right 1 u).trans hu
  · rw [min_eq_left (le_of_not_ge h)]
    exact (min_le_left 1 u).trans (by norm_num)

theorem sourceTruncation_lindleyPrefixSurvivalBound
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (N : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (N : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hR : Shao.truncationBudget nu N x ≤ epsilon ^ 3 / 8) :
    let rho : Measure ℝ :=
      ProbabilityTheory.cond nu {z | |z| ≤ epsilon / (1 + x)}
    lindleyPrefixSurvivalBound rho N
      (16 * Real.exp (7 + 3 * (1024 : ℝ))) := by
  let rho : Measure ℝ := ProbabilityTheory.cond nu {z | |z| ≤ epsilon / (1 + x)}
  let mu : ℝ := ∫ z : ℝ, z ∂rho
  let V : ℝ := variance (id : ℝ → ℝ) rho
  let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
  let m3c : ℝ := ∫ z : ℝ, |z - mu| ^ 3 ∂rho
  obtain ⟨_, _, hp, _, _, _, h3r, _⟩ :=
    Shao.sourceTruncation_law_data nu N h2 hnorm x epsilon hx hepsilon hepsilonHalf hR
  change IsProbabilityMeasure rho at hp
  change Integrable (fun z : ℝ => |z| ^ 3) rho at h3r
  letI : IsProbabilityMeasure rho := hp
  obtain ⟨hmu, _, _, _, hcentered⟩ :=
    Shao.sourceTruncation_paid_moments nu N h2 hnorm hmean x epsilon hx
      hepsilon hepsilonHalf hR
  change (N : ℝ) * |mu| ≤ 2 * Shao.truncationBudget nu N x /
    (epsilon ^ 2 * (1 + x)) at hmu
  change m3c ≤ 8 * m3 at hcentered
  obtain ⟨_, _, _, _, _, hVp, hVlo, _⟩ :=
    Shao.sourceTruncation_variance_bounds nu N h2 hnorm hmean x epsilon hx
      hepsilon hepsilonHalf hR
  change 0 < V at hVp
  change (1 / 2 : ℝ) ≤ (N : ℝ) * V at hVlo
  have hN : 0 < N := by
    by_contra hh
    have hz : N = 0 := Nat.eq_zero_of_not_pos hh
    simp only [hz, Nat.cast_zero, zero_mul, zero_ne_one] at hnorm
  have hNp : 0 < (N : ℝ) := by exact_mod_cast hN
  have ha : 0 < 1 + x := by linarith
  have hmuN : (N : ℝ) * |mu| ≤ 1 / 8 := by
    apply hmu.trans
    apply (div_le_iff₀ (mul_pos (pow_pos hepsilon 2) ha)).2
    have hh := mul_le_mul_of_nonneg_left
      (show 2 * epsilon ≤ 1 + x by linarith) (sq_nonneg epsilon)
    nlinarith only [hR, hh]
  change lindleyPrefixSurvivalBound rho N (16 * Real.exp (7 + 3 * (1024 : ℝ)))
  unfold lindleyPrefixSurvivalBound
  change ∀ k : ℕ, 1 ≤ k → k < N → ∀ r : ℝ, 0 ≤ r →
    (Measure.pi (fun _ : Fin k => rho)).real
      {a : Shao.Path k | Shao.maxWithZero a ≤ r} ≤
      (16 * Real.exp (7 + 3 * (1024 : ℝ))) *
        min 1 ((r + m3 / V) / (Real.sqrt V * Real.sqrt ((k + 1 : ℕ) : ℝ)))
  intro k hk hkN r hr
  have hden : 0 < Real.sqrt V * Real.sqrt ((k + 1 : ℕ) : ℝ) := by positivity
  have hraw : 0 ≤ (r + m3 / V) / (Real.sqrt V * Real.sqrt ((k + 1 : ℕ) : ℝ)) := by
    dsimp [m3]
    positivity
  have hratio : (r + m3c / V) / (Real.sqrt V * Real.sqrt ((k + 1 : ℕ) : ℝ)) ≤
      8 * ((r + m3 / V) / (Real.sqrt V * Real.sqrt ((k + 1 : ℕ) : ℝ))) := by
    have hc : m3c / V ≤ 8 * (m3 / V) := by
      convert div_le_div_of_nonneg_right hcentered hVp.le using 1 <;> ring
    have hh := div_le_div_of_nonneg_right
      (show r + m3c / V ≤ 8 * (r + m3 / V) by linarith) hden.le
    convert hh using 1 <;> ring
  have hmin := sl_min_one_eight _ _ hraw hratio
  have hdrift := sl_drift_bound N k mu V hNp hVp hmuN hVlo (Nat.le_of_lt hkN)
  have hexp : Real.exp (4 * (|mu| * Real.sqrt (k : ℝ) / Real.sqrt V)) ≤ Real.exp 1 :=
    Real.exp_le_exp.2 (by linarith)
  have hs := iid_closed_survival_nonzero_drift rho h3r hVp k r hr
  change (Measure.pi (fun _ : Fin k => rho)).real
    {a : Shao.Path k | Shao.maxWithZero a ≤ r} ≤
    (2 * Real.exp (6 + 3 * (1024 : ℝ))) *
      min 1 ((r + m3c / V) / (Real.sqrt V * Real.sqrt ((k + 1 : ℕ) : ℝ))) *
      Real.exp (4 * (|mu| * Real.sqrt (k : ℝ) / Real.sqrt V)) at hs
  have he : Real.exp (6 + 3 * (1024 : ℝ)) * Real.exp 1 =
      Real.exp (7 + 3 * (1024 : ℝ)) := by rw [← Real.exp_add]; norm_num
  calc
    _ ≤ (2 * Real.exp (6 + 3 * (1024 : ℝ))) *
        min 1 ((r + m3c / V) / (Real.sqrt V * Real.sqrt ((k + 1 : ℕ) : ℝ))) *
        Real.exp (4 * (|mu| * Real.sqrt (k : ℝ) / Real.sqrt V)) := hs
    _ ≤ (2 * Real.exp (6 + 3 * (1024 : ℝ))) *
        (8 * min 1 ((r + m3 / V) / (Real.sqrt V * Real.sqrt ((k + 1 : ℕ) : ℝ)))) *
        Real.exp 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hmin (by positivity)) hexp
        (Real.exp_pos _).le (by positivity)
    _ = (16 * (Real.exp (6 + 3 * (1024 : ℝ)) * Real.exp 1)) *
        min 1 ((r + m3 / V) / (Real.sqrt V * Real.sqrt ((k + 1 : ℕ) : ℝ))) := by ring
    _ = _ := by rw [he]

theorem sourceTruncation_lindleyRegulator_second_moment
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (N : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (N : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hR : Shao.truncationBudget nu N x ≤ epsilon ^ 3 / 8) :
    let rho : Measure ℝ :=
      ProbabilityTheory.cond nu {z | |z| ≤ epsilon / (1 + x)}
    let V : ℝ := variance (id : ℝ → ℝ) rho
    let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
    let P : Measure (Shao.Path N) :=
      Measure.pi (fun _ : Fin N => rho)
    ∀ j : Fin N,
      Integrable (fun a : Shao.Path N => (lindleyRegulator a j) ^ 2) P ∧
        (∫ a : Shao.Path N, (lindleyRegulator a j) ^ 2 ∂P) ≤
          (48 * Real.exp (7 + 3 * (1024 : ℝ))) * m3 /
            (Real.sqrt V * Real.sqrt ((j.val + 1 : ℕ) : ℝ)) := by
  dsimp only
  have hC : 0 ≤ 16 * Real.exp (7 + 3 * (1024 : ℝ)) := by positivity
  have hs := sourceTruncation_lindleyPrefixSurvivalBound nu N h2 hnorm hmean x epsilon hx
    hepsilon hepsilonHalf hR
  have hpaid := sourceTruncation_lindleyRegulator_second_moment_of_survival
    nu N h2 hnorm hmean x epsilon hx hepsilon hepsilonHalf hR
    (16 * Real.exp (7 + 3 * (1024 : ℝ))) hC hs
  have hlarge : 1 ≤ 3 * (16 * Real.exp (7 + 3 * (1024 : ℝ))) := by
    have hh : 1 ≤ Real.exp (7 + 3 * (1024 : ℝ)) := Real.one_le_exp_iff.2 (by norm_num)
    linarith
  intro j
  obtain ⟨hi, hb⟩ := hpaid j
  refine ⟨hi, ?_⟩
  rw [max_eq_right hlarge] at hb
  convert hb using 1 <;> ring

end Shao.Probability
