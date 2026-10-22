import Shao.OQ4.RademacherS2Assembly
import Shao.OQ4.RademacherLatticeShift
import Shao.Probability.BrownianSup
import Shao.Probability.BrownianFirstTerm
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Local source implementation for the frozen original S3 and actual Brownian object.
All public definitions and theorem types are frozen by the parent coordinator.
This local source has not yet been checked by Lean.
The actual Brownian first-term asymptotic B2 is accepted in PR140/v35.
Only its first-term ratio and eventual positivity APIs are consumed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Shao.OQ4.RademacherS3Assembly

def H (m : ℕ) : ℝ := RademacherS2Assembly.H m

def N (n : ℕ) : ℝ := RademacherS2Assembly.N n

def t (m n : ℕ) : ℝ := RademacherS2Assembly.t m n

def a (m : ℕ) : ℝ := RademacherS2Assembly.a m

def rho (m : ℕ) : ℝ := RademacherS2Assembly.rho m

def eps (m n : ℕ) : ℝ := RademacherS2Assembly.eps m n

def q (m : ℕ) : ℝ := RademacherS2Assembly.q m

def R (m n : ℕ) : ℝ := RademacherS2Assembly.R m n

-- A is exactly the S2 spectral normalizer; B denotes the Brownian process.
def A (m n : ℕ) : ℝ := RademacherS2Assembly.B m n

def p (n : ℕ) (h : ℝ) : ℝ := RademacherS2Assembly.p n h

def K (n : ℕ) (h : ℝ) : ℝ := RademacherS2Assembly.K n h

def D (m n : ℕ) (h : ℝ) : ℝ := RademacherS2Assembly.D m n h

def u (m : ℕ) : ℝ := RademacherScalarBounds.u m

def z (m : ℕ) : ℝ := RademacherScalarBounds.z m

def lambda : ℝ := RademacherScalarBounds.lambda

-- The total real expression is 0 at n = 0; the probability comparison is
-- interpreted on the positive-time tails supplied by S3_DOM.
def x (n : ℕ) (h : ℝ) : ℝ := h / Real.sqrt (N n)

def g (s : ℝ) : ℝ := Shao.Probability.BrownianSup.firstTerm s

def G (n : ℕ) (h : ℝ) : ℝ :=
  (4 / Real.pi) * Real.exp (-lambda * N n / h ^ 2)

def b {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (s : ℝ) : ℝ :=
  Shao.Probability.BrownianSup.probability B P hB s

def T {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (s : ℝ) : ℝ :=
  b B P hB s / g s

def W {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (n : ℕ) (h : ℝ) : ℝ :=
  b B P hB (x n h) / G n h

def C (m n : ℕ) (h : ℝ) : ℝ :=
  lambda * N n / h ^ 2 + N n * Real.log (rho m) +
    Real.log (Real.pi * a m / 4)

theorem definition_bridges (m : ℕ) :
    H m = (m : ℝ) + 1 ∧
    H m = RademacherScalarBounds.H m ∧
    u m = Real.pi / (4 * H m) ∧
    z m = Real.pi / (2 * H m) ∧
    RademacherSpectralPairing.alpha m 0 = u m ∧
    RademacherSpectralPairing.beta m 0 = z m ∧
    a m = (1 / H m) * (Real.cos (u m) / Real.sin (u m)) ∧
    a m = RademacherScalarBounds.a m ∧
    rho m = Real.cos (z m) ∧
    rho m = RademacherScalarBounds.rho m ∧
    lambda = Real.pi ^ 2 / 8 ∧
    (∀ n : ℕ, N n = (n : ℝ) ∧
      eps m n = (-1 : ℝ) ^ (n + m)) := by
  rcases RademacherS2Assembly.definition_bridges m with
    ⟨hα, hβ, ha, has, hr, hrs⟩
  refine ⟨rfl, rfl, rfl, rfl, hα, hβ, ha, has, hr, hrs, rfl, ?_⟩
  intro n
  exact ⟨rfl, rfl⟩

theorem finite_identities (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) (n : ℕ) :
    1 ≤ h ∧ 0 < h ∧ 2 ≤ H m ∧ 0 < H m ∧
    0 < a m ∧ 0 < rho m ∧ rho m < 1 ∧ 0 < A m n ∧
    p n h =
      (Measure.pi (fun _ : Fin n => RademacherCosine.law)).real
        (@Shao.closedStrip n h) ∧
    K n h =
      @Shao.OQ4.killedMass RademacherCosine.law
        RademacherCosine.law_isProbabilityMeasure h n (0 : ℝ) ∧
    p n h = K n h ∧
    p n h = A m n * (1 + eps m n * q m + R m n) ∧
    D m n h = p n h / A m n ∧
    D m n h = K n h / A m n ∧
    D m n h = 1 + eps m n * q m + R m n := by
  rcases RademacherLatticeShift.cell_legality hm hmh hhm with
    ⟨hh1, hhp, hH2, hHp, _, _, _⟩
  rcases RademacherS2Assembly.F0 m hm h hmh hhm n with
    ⟨ha, hr, hr1, hA, hpK, hpA, hDK, hD⟩
  exact ⟨hh1, hhp, hH2, hHp, ha, hr, hr1, hA,
    rfl, rfl, hpK, hpA, rfl, hDK, hD⟩

theorem zero_time (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) :
    p 0 h = 1 ∧ K 0 h = 1 ∧ x 0 h = 0 ∧
    RademacherSpectralPairing.zeroMode m 0 =
      (if Even m then (-1 : ℝ) ^ (m / 2) / H m else 0) := by
  rcases RademacherS2Assembly.F0_zero_time m hm h hmh hhm with
    ⟨hp, hK, hz⟩
  exact ⟨hp, hK, by simp [x, N, RademacherS2Assembly.N], hz⟩

theorem small_cells :
    (∀ n : ℕ, R 1 n = 0) ∧
    (∀ n : ℕ, 1 ≤ n → R 2 n = 0) ∧
    RademacherSpectralPairing.zeroMode 2 0 = -(1 / 3 : ℝ) ∧
    R 2 0 = -1 / (3 * a 2) ∧ R 2 0 ≠ 0 := by
  simpa only [R, a] using RademacherS2Assembly.F0_small_cells

theorem brownian_object {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    Measurable (Shao.Probability.BrownianSup.U B P hB) ∧
    Shao.Probability.BrownianSup.U B P hB =ᵐ[P]
      Shao.Probability.BrownianSup.pathSup B ∧
    (∀ s : ℝ,
      b B P hB s =
        P.real {ω | Shao.Probability.BrownianSup.U B P hB ω ≤ s} ∧
      b B P hB s =
        P.real (Shao.Probability.BrownianSup.fullStrip B s)) := by
  refine ⟨Shao.Probability.BrownianSup.measurable_U B P hB,
    Shao.Probability.BrownianSup.U_ae_eq_pathSup B P hB, ?_⟩
  intro s
  exact ⟨rfl, Shao.Probability.BrownianSup.probability_eq_fullStrip B P hB s⟩

theorem g_pos (s : ℝ) :
    g s = (4 / Real.pi) * Real.exp (-lambda / s ^ 2) ∧
    0 < lambda ∧ 0 < (4 / Real.pi : ℝ) ∧ 0 < g s := by
  have hLambda : 0 < lambda := by
    dsimp [lambda, RademacherScalarBounds.lambda]
    positivity
  have hc : 0 < (4 / Real.pi : ℝ) := div_pos (by norm_num) Real.pi_pos
  refine ⟨rfl, hLambda, hc, ?_⟩
  change 0 < (4 / Real.pi) * Real.exp (-(Real.pi ^ 2 / 8) / s ^ 2)
  exact mul_pos hc (Real.exp_pos _)

theorem finite_ALG (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1)
    (n : ℕ) (hn : 1 ≤ n) :
    0 < N n ∧ 0 < Real.sqrt (N n) ∧
    (Real.sqrt (N n)) ^ 2 = N n ∧ 0 < h ∧ 0 < x n h ∧
    (x n h) ^ 2 = h ^ 2 / N n ∧
    1 / (x n h) ^ 2 = N n / h ^ 2 ∧
    g (x n h) = G n h ∧ 0 < G n h ∧
    0 < rho m ^ n ∧ 0 < Real.pi * a m / 4 ∧
    Real.log (rho m ^ n) = N n * Real.log (rho m) ∧
    Real.log (g (x n h)) =
      Real.log (4 / Real.pi) - lambda * N n / h ^ 2 ∧
    Real.log (a m) - Real.log (4 / Real.pi) =
      Real.log (Real.pi * a m / 4) := by
  rcases finite_identities m hm h hmh hhm n with
    ⟨_, hh, _, _, ha, hr, _, _, _, _, _, _, _, _, _⟩
  have hN : 0 < N n := by
    dsimp only [N, RademacherS2Assembly.N]
    exact_mod_cast (show 0 < n from hn)
  have hsqrt : 0 < Real.sqrt (N n) := Real.sqrt_pos.2 hN
  have hsq : (Real.sqrt (N n)) ^ 2 = N n := Real.sq_sqrt hN.le
  have hx : 0 < x n h := div_pos hh hsqrt
  have hx2 : (x n h) ^ 2 = h ^ 2 / N n := by
    dsimp only [x]
    rw [div_pow, hsq]
  have hinv : 1 / (x n h) ^ 2 = N n / h ^ 2 := by
    rw [hx2, one_div_div]
  have hc : 0 < (4 / Real.pi : ℝ) := div_pos (by norm_num) Real.pi_pos
  have hgG : g (x n h) = G n h := by
    change (4 / Real.pi) * Real.exp (-lambda / (x n h) ^ 2) =
      (4 / Real.pi) * Real.exp (-lambda * N n / h ^ 2)
    have he : -lambda / (x n h) ^ 2 = -lambda * N n / h ^ 2 := by
      calc
        -lambda / (x n h) ^ 2 = -lambda * (1 / (x n h) ^ 2) := by ring
        _ = -lambda * (N n / h ^ 2) := by rw [hinv]
        _ = -lambda * N n / h ^ 2 := by ring
    rw [he]
  have hG : 0 < G n h := mul_pos hc (Real.exp_pos _)
  have hrpow : 0 < rho m ^ n := pow_pos hr n
  have hπa : 0 < Real.pi * a m / 4 :=
    div_pos (mul_pos Real.pi_pos ha) (by norm_num)
  have hlogrho : Real.log (rho m ^ n) = N n * Real.log (rho m) := by
    rw [Real.log_pow]
    rfl
  have hlogg : Real.log (g (x n h)) =
      Real.log (4 / Real.pi) - lambda * N n / h ^ 2 := by
    rw [hgG]
    change Real.log ((4 / Real.pi) * Real.exp (-lambda * N n / h ^ 2)) = _
    rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hquot : a m / (4 / Real.pi) = Real.pi * a m / 4 := by
    field_simp [Real.pi_ne_zero]
  have hloga : Real.log (a m) - Real.log (4 / Real.pi) =
      Real.log (Real.pi * a m / 4) := by
    calc
      Real.log (a m) - Real.log (4 / Real.pi) =
          Real.log (a m / (4 / Real.pi)) := (Real.log_div ha.ne' hc.ne').symm
      _ = Real.log (Real.pi * a m / 4) := congrArg Real.log hquot
  exact ⟨hN, hsqrt, hsq, hh, hx, hx2, hinv, hgG, hG, hrpow,
    hπa, hlogrho, hlogg, hloga⟩

private theorem scale_domain (m_ n_ : ℕ → ℕ) (h_ : ℕ → ℝ)
    (hm : ∀ k : ℕ, 1 ≤ m_ k)
    (hmh : ∀ k : ℕ, (m_ k : ℝ) ≤ h_ k)
    (hhm : ∀ k : ℕ, h_ k < (m_ k : ℝ) + 1)
    (hH : Tendsto (fun k : ℕ => H (m_ k)) atTop atTop)
    (ht : Tendsto (fun k : ℕ => t (m_ k) (n_ k)) atTop atTop) :
    Tendsto h_ atTop atTop ∧
    Tendsto (fun k : ℕ => N (n_ k) / (h_ k) ^ 2) atTop atTop ∧
    Tendsto (fun k : ℕ => x (n_ k) (h_ k)) atTop (𝓝 (0 : ℝ)) ∧
    (∀ d : ℝ, 0 < d → ∃ K_d : ℕ, ∀ k : ℕ, K_d ≤ k →
      0 < x (n_ k) (h_ k) ∧ x (n_ k) (h_ k) < d) ∧
    (∃ K_time : ℕ, ∀ k : ℕ, K_time ≤ k →
      1 ≤ n_ k ∧ 0 < N (n_ k) ∧ 0 < Real.sqrt (N (n_ k)) ∧
      0 < x (n_ k) (h_ k)) := by
  have hcell : ∀ k : ℕ,
      1 ≤ h_ k ∧ 0 < h_ k ∧ 2 ≤ H (m_ k) ∧ 0 < H (m_ k) := by
    intro k
    rcases RademacherLatticeShift.cell_legality (hm k) (hmh k) (hhm k) with
      ⟨hh1, hhp, hH2, hHp, _, _, _⟩
    exact ⟨hh1, hhp, hH2, hHp⟩
  have hhlim : Tendsto h_ atTop atTop := by
    apply tendsto_atTop.2
    intro c
    filter_upwards [hH.eventually (eventually_ge_atTop (c + 1))] with k hk
    have hmk := hmh k
    change c + 1 ≤ (m_ k : ℝ) + 1 at hk
    linarith only [hmk, hk]
  have hs : Tendsto (fun k : ℕ => N (n_ k) / (h_ k) ^ 2) atTop atTop := by
    apply tendsto_atTop.2
    intro c
    filter_upwards [ht.eventually (eventually_ge_atTop c)] with k hk
    change c ≤ N (n_ k) / H (m_ k) ^ 2 at hk
    have hN : 0 ≤ N (n_ k) := by
      dsimp only [N, RademacherS2Assembly.N]
      positivity
    have hh := (hcell k).2.1
    have hHp := (hcell k).2.2.2
    have hhH : h_ k ≤ H (m_ k) := (hhm k).le
    have hsq : (h_ k) ^ 2 ≤ H (m_ k) ^ 2 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hhH) (add_nonneg hHp.le hh.le)]
    exact hk.trans (div_le_div_of_nonneg_left hN (sq_pos_of_pos hh) hsq)
  obtain ⟨K_time, hKt⟩ :=
    eventually_atTop.mp (ht.eventually (eventually_ge_atTop (1 : ℝ)))
  have htime : ∀ k : ℕ, K_time ≤ k →
      1 ≤ n_ k ∧ 0 < N (n_ k) ∧ 0 < Real.sqrt (N (n_ k)) ∧
      0 < x (n_ k) (h_ k) := by
    intro k hk
    have hHsq : 0 < H (m_ k) ^ 2 := sq_pos_of_pos (hcell k).2.2.2
    have htk := hKt k hk
    change (1 : ℝ) ≤ N (n_ k) / H (m_ k) ^ 2 at htk
    have hbound := (le_div_iff₀ hHsq).mp htk
    simp only [one_mul] at hbound
    have hN : 0 < N (n_ k) := lt_of_lt_of_le hHsq hbound
    have hn : 1 ≤ n_ k :=
      (Nat.cast_pos (α := ℝ)).mp (by simpa only [N, RademacherS2Assembly.N] using hN)
    have hsqrt := Real.sqrt_pos.2 hN
    exact ⟨hn, hN, hsqrt, div_pos (hcell k).2.1 hsqrt⟩
  have hside : ∀ d : ℝ, 0 < d → ∃ K_d : ℕ, ∀ k : ℕ, K_d ≤ k →
      0 < x (n_ k) (h_ k) ∧ x (n_ k) (h_ k) < d := by
    intro d hd
    obtain ⟨K_s, hKs⟩ :=
      eventually_atTop.mp (hs.eventually (eventually_gt_atTop (1 / d ^ 2)))
    refine ⟨max K_time K_s, ?_⟩
    intro k hk
    rcases htime k ((le_max_left _ _).trans hk) with ⟨hn, hN, _, hx⟩
    rcases finite_ALG (m_ k) (hm k) (h_ k) (hmh k) (hhm k) (n_ k) hn with
      ⟨_, _, _, _, _, hx2, _, _, _, _, _, _, _, _⟩
    have hlarge := hKs k ((le_max_right _ _).trans hk)
    have hcross : (h_ k) ^ 2 < N (n_ k) * d ^ 2 := by
      have hh := (div_lt_div_iff₀ (sq_pos_of_pos hd)
        (sq_pos_of_pos (hcell k).2.1)).mp hlarge
      simpa only [one_mul] using hh
    have hxsq : (x (n_ k) (h_ k)) ^ 2 < d ^ 2 := by
      rw [hx2]
      exact (div_lt_iff₀ hN).2 (by simpa only [mul_comm] using hcross)
    have hxd : x (n_ k) (h_ k) < d := by
      by_contra hnot
      have hdx : d ≤ x (n_ k) (h_ k) := le_of_not_gt hnot
      have hprod := mul_nonneg (sub_nonneg.mpr hdx) (add_nonneg hx.le hd.le)
      nlinarith only [hxsq, hprod]
    exact ⟨hx, hxd⟩
  have hxlim : Tendsto (fun k : ℕ => x (n_ k) (h_ k)) atTop (𝓝 (0 : ℝ)) := by
    apply Metric.tendsto_atTop.2
    intro d hd
    obtain ⟨K_d, hKd⟩ := hside d hd
    refine ⟨K_d, ?_⟩
    intro k hk
    rcases hKd k hk with ⟨hx, hxd⟩
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hx] using hxd
  exact ⟨hhlim, hs, hxlim, hside, K_time, htime⟩

theorem S3_DOM {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (m_ n_ : ℕ → ℕ) (h_ : ℕ → ℝ)
    (hm : ∀ k : ℕ, 1 ≤ m_ k)
    (hmh : ∀ k : ℕ, (m_ k : ℝ) ≤ h_ k)
    (hhm : ∀ k : ℕ, h_ k < (m_ k : ℝ) + 1)
    (hH : Tendsto (fun k : ℕ => H (m_ k)) atTop atTop)
    (ht : Tendsto (fun k : ℕ => t (m_ k) (n_ k)) atTop atTop) :
    (∀ k : ℕ,
      1 ≤ h_ k ∧ 2 ≤ H (m_ k) ∧
      0 < a (m_ k) ∧ 0 < rho (m_ k) ∧ rho (m_ k) < 1 ∧
      0 < A (m_ k) (n_ k) ∧
      p (n_ k) (h_ k) = K (n_ k) (h_ k) ∧
      D (m_ k) (n_ k) (h_ k) =
        1 + eps (m_ k) (n_ k) * q (m_ k) + R (m_ k) (n_ k) ∧
      (n_ k = 0 → p (n_ k) (h_ k) = 1 ∧ K (n_ k) (h_ k) = 1)) ∧
    Tendsto h_ atTop atTop ∧
    Tendsto (fun k : ℕ => N (n_ k) / (h_ k) ^ 2) atTop atTop ∧
    Tendsto (fun k : ℕ => x (n_ k) (h_ k)) atTop (𝓝 (0 : ℝ)) ∧
    (∀ d : ℝ, 0 < d → ∃ K_d : ℕ, ∀ k : ℕ, K_d ≤ k →
      0 < x (n_ k) (h_ k) ∧ x (n_ k) (h_ k) < d) ∧
    Tendsto (fun k : ℕ => D (m_ k) (n_ k) (h_ k))
      atTop (𝓝 (1 : ℝ)) ∧
    Tendsto (fun k : ℕ => Real.log (D (m_ k) (n_ k) (h_ k)))
      atTop (𝓝 (0 : ℝ)) ∧
    Tendsto (fun k : ℕ => T B P hB (x (n_ k) (h_ k)))
      atTop (𝓝 (1 : ℝ)) ∧
    Tendsto (fun k : ℕ => W B P hB (n_ k) (h_ k))
      atTop (𝓝 (1 : ℝ)) ∧
    Tendsto (fun k : ℕ => Real.log (T B P hB (x (n_ k) (h_ k))))
      atTop (𝓝 (0 : ℝ)) ∧
    (∃ K_time : ℕ,
      (∀ k : ℕ, K_time ≤ k →
        1 ≤ n_ k ∧ 0 < N (n_ k) ∧ 0 < Real.sqrt (N (n_ k)) ∧
        0 < x (n_ k) (h_ k) ∧
        g (x (n_ k) (h_ k)) = G (n_ k) (h_ k) ∧
        W B P hB (n_ k) (h_ k) = T B P hB (x (n_ k) (h_ k))) ∧
      ∃ K_pos : ℕ, K_time ≤ K_pos ∧
        ∀ k : ℕ, K_pos ≤ k →
          p (n_ k) (h_ k) = K (n_ k) (h_ k) ∧
          0 < p (n_ k) (h_ k) ∧ 0 < K (n_ k) (h_ k) ∧
          0 < D (m_ k) (n_ k) (h_ k) ∧
          0 < b B P hB (x (n_ k) (h_ k)) ∧
          0 < T B P hB (x (n_ k) (h_ k)) ∧
          0 < W B P hB (n_ k) (h_ k) ∧
          0 < p (n_ k) (h_ k) / b B P hB (x (n_ k) (h_ k)) ∧
          0 < K (n_ k) (h_ k) / b B P hB (x (n_ k) (h_ k))) := by
  rcases scale_domain m_ n_ h_ hm hmh hhm hH ht with
    ⟨hhlim, hs, hxlim, hside, K_time, htime⟩
  rcases RademacherS2Assembly.Q1 m_ n_ h_ hm hmh hhm hH ht with
    ⟨_, _, _, _, hD2, _, ⟨K_2, hpos2⟩, hlogD2, _, _⟩
  have hDlim : Tendsto (fun k : ℕ => D (m_ k) (n_ k) (h_ k))
      atTop (𝓝 (1 : ℝ)) := hD2
  have hlogDlim : Tendsto (fun k : ℕ => Real.log (D (m_ k) (n_ k) (h_ k)))
      atTop (𝓝 (0 : ℝ)) := hlogD2
  have hTlim : Tendsto (fun k : ℕ => T B P hB (x (n_ k) (h_ k)))
      atTop (𝓝 (1 : ℝ)) := by
    apply Metric.tendsto_atTop.2
    intro e he
    obtain ⟨d, hd, hBd⟩ :=
      Shao.Probability.BrownianSup.actual_brownian_firstTerm B P hB e he
    obtain ⟨K_d, hKd⟩ := hside d hd
    refine ⟨K_d, ?_⟩
    intro k hk
    rcases hKd k hk with ⟨hx, hxd⟩
    have hbound := hBd (x (n_ k) (h_ k)) hx hxd
    simpa only [Real.dist_eq, T, b, g] using hbound
  have hlogTlim :
      Tendsto (fun k : ℕ => Real.log (T B P hB (x (n_ k) (h_ k))))
        atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hTlim
  have hWT : ∀ k : ℕ, K_time ≤ k →
      W B P hB (n_ k) (h_ k) = T B P hB (x (n_ k) (h_ k)) := by
    intro k hk
    have hn := (htime k hk).1
    rcases finite_ALG (m_ k) (hm k) (h_ k) (hmh k) (hhm k) (n_ k) hn with
      ⟨_, _, _, _, _, _, _, hgG, _, _, _, _, _, _⟩
    dsimp only [W, T]
    rw [hgG]
  have hWlim : Tendsto (fun k : ℕ => W B P hB (n_ k) (h_ k))
      atTop (𝓝 (1 : ℝ)) := by
    apply Filter.Tendsto.congr' _ hTlim
    filter_upwards [eventually_ge_atTop K_time] with k hk
    exact (hWT k hk).symm
  obtain ⟨d_pos, hdpos, hBpos⟩ :=
    Shao.Probability.BrownianSup.actual_brownian_eventually_positive B P hB
  obtain ⟨K_B, hKB⟩ := hside d_pos hdpos
  have hBtail : ∀ k : ℕ, K_B ≤ k →
      0 < b B P hB (x (n_ k) (h_ k)) ∧
      0 < T B P hB (x (n_ k) (h_ k)) := by
    intro k hk
    rcases hKB k hk with ⟨hx, hxd⟩
    simpa only [b, T, g] using hBpos (x (n_ k) (h_ k)) hx hxd
  let K_pos := max K_time (max K_2 K_B)
  have htime_pos : K_time ≤ K_pos := le_max_left _ _
  have h2_pos : K_2 ≤ K_pos := (le_max_left _ _).trans (le_max_right _ _)
  have hB_pos : K_B ≤ K_pos := (le_max_right _ _).trans (le_max_right _ _)
  have hall : ∀ k : ℕ,
      1 ≤ h_ k ∧ 2 ≤ H (m_ k) ∧
      0 < a (m_ k) ∧ 0 < rho (m_ k) ∧ rho (m_ k) < 1 ∧
      0 < A (m_ k) (n_ k) ∧
      p (n_ k) (h_ k) = K (n_ k) (h_ k) ∧
      D (m_ k) (n_ k) (h_ k) =
        1 + eps (m_ k) (n_ k) * q (m_ k) + R (m_ k) (n_ k) ∧
      (n_ k = 0 → p (n_ k) (h_ k) = 1 ∧ K (n_ k) (h_ k) = 1) := by
    intro k
    rcases finite_identities (m_ k) (hm k) (h_ k) (hmh k) (hhm k) (n_ k) with
      ⟨hh1, _, hH2, _, ha, hr, hr1, hA, _, _, hpK, _, _, _, hD⟩
    refine ⟨hh1, hH2, ha, hr, hr1, hA, hpK, hD, ?_⟩
    intro hn0
    rcases zero_time (m_ k) (hm k) (h_ k) (hmh k) (hhm k) with
      ⟨hp0, hK0, _, _⟩
    simpa only [hn0] using And.intro hp0 hK0
  refine ⟨hall, hhlim, hs, hxlim, hside, hDlim, hlogDlim, hTlim, hWlim,
    hlogTlim, K_time, ?_, K_pos, htime_pos, ?_⟩
  · intro k hk
    rcases htime k hk with ⟨hn, hN, hsqrt, hx⟩
    rcases finite_ALG (m_ k) (hm k) (h_ k) (hmh k) (hhm k) (n_ k) hn with
      ⟨_, _, _, _, _, _, _, hgG, _, _, _, _, _, _⟩
    exact ⟨hn, hN, hsqrt, hx, hgG, hWT k hk⟩
  · intro k hk
    rcases hpos2 k (h2_pos.trans hk) with ⟨hD, hp, hK, _, _⟩
    rcases hBtail k (hB_pos.trans hk) with ⟨hb, hT⟩
    have hW : 0 < W B P hB (n_ k) (h_ k) := by
      rw [hWT k (htime_pos.trans hk)]
      exact hT
    have hpK := (hall k).2.2.2.2.2.2.1
    exact ⟨hpK, hp, hK, hD, hb, hT, hW, div_pos hp hb, div_pos hK hb⟩

theorem S3_ALG {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (m_ n_ : ℕ → ℕ) (h_ : ℕ → ℝ)
    (hm : ∀ k : ℕ, 1 ≤ m_ k)
    (hmh : ∀ k : ℕ, (m_ k : ℝ) ≤ h_ k)
    (hhm : ∀ k : ℕ, h_ k < (m_ k : ℝ) + 1)
    (hH : Tendsto (fun k : ℕ => H (m_ k)) atTop atTop)
    (ht : Tendsto (fun k : ℕ => t (m_ k) (n_ k)) atTop atTop) :
    ∃ K_alg : ℕ, ∀ k : ℕ, K_alg ≤ k →
      1 ≤ n_ k ∧ 0 < N (n_ k) ∧ 0 < Real.sqrt (N (n_ k)) ∧
      0 < h_ k ∧ 0 < x (n_ k) (h_ k) ∧
      0 < a (m_ k) ∧ 0 < rho (m_ k) ∧
      0 < A (m_ k) (n_ k) ∧
      0 < Real.pi * a (m_ k) / 4 ∧
      0 < p (n_ k) (h_ k) ∧ 0 < K (n_ k) (h_ k) ∧
      0 < D (m_ k) (n_ k) (h_ k) ∧
      0 < b B P hB (x (n_ k) (h_ k)) ∧
      0 < g (x (n_ k) (h_ k)) ∧
      0 < T B P hB (x (n_ k) (h_ k)) ∧
      0 < p (n_ k) (h_ k) / b B P hB (x (n_ k) (h_ k)) ∧
      0 < K (n_ k) (h_ k) / b B P hB (x (n_ k) (h_ k)) ∧
      Real.log (p (n_ k) (h_ k)) - Real.log (a (m_ k)) -
          N (n_ k) * Real.log (rho (m_ k)) =
        Real.log (D (m_ k) (n_ k) (h_ k)) ∧
      Real.log (K (n_ k) (h_ k)) - Real.log (a (m_ k)) -
          N (n_ k) * Real.log (rho (m_ k)) =
        Real.log (D (m_ k) (n_ k) (h_ k)) ∧
      Real.log (b B P hB (x (n_ k) (h_ k))) -
          Real.log (g (x (n_ k) (h_ k))) =
        Real.log (T B P hB (x (n_ k) (h_ k))) ∧
      Real.log (p (n_ k) (h_ k) / b B P hB (x (n_ k) (h_ k))) =
        Real.log (p (n_ k) (h_ k)) -
          Real.log (b B P hB (x (n_ k) (h_ k))) ∧
      Real.log (K (n_ k) (h_ k) / b B P hB (x (n_ k) (h_ k))) =
        Real.log (K (n_ k) (h_ k)) -
          Real.log (b B P hB (x (n_ k) (h_ k))) ∧
      Real.log (p (n_ k) (h_ k) / b B P hB (x (n_ k) (h_ k))) -
          C (m_ k) (n_ k) (h_ k) =
        Real.log (D (m_ k) (n_ k) (h_ k)) -
          Real.log (T B P hB (x (n_ k) (h_ k))) ∧
      Real.log (K (n_ k) (h_ k) / b B P hB (x (n_ k) (h_ k))) -
          C (m_ k) (n_ k) (h_ k) =
        Real.log (D (m_ k) (n_ k) (h_ k)) -
          Real.log (T B P hB (x (n_ k) (h_ k))) := by
  rcases S3_DOM B P hB m_ n_ h_ hm hmh hhm hH ht with
    ⟨_, _, _, _, _, _, _, _, _, _, K_time, htime, K_pos, htime_pos, hpos⟩
  refine ⟨K_pos, ?_⟩
  intro k hk
  rcases htime k (htime_pos.trans hk) with ⟨hn, _, _, _, _, _⟩
  rcases hpos k hk with ⟨hpK, hp, hK, hD, hb, hT, _, hpq, hKq⟩
  rcases finite_identities (m_ k) (hm k) (h_ k) (hmh k) (hhm k) (n_ k) with
    ⟨_, _, _, _, ha, hr, _, hA, _, _, _, _, hDp, _, _⟩
  rcases finite_ALG (m_ k) (hm k) (h_ k) (hmh k) (hhm k) (n_ k) hn with
    ⟨hN, hsqrt, _, hh, hx, _, _, _, _, hrpow, hπa, hlogrho, hlogg, hloga⟩
  have hg : 0 < g (x (n_ k) (h_ k)) := (g_pos _).2.2.2
  have hlogA : Real.log (A (m_ k) (n_ k)) =
      Real.log (a (m_ k)) + N (n_ k) * Real.log (rho (m_ k)) := by
    change Real.log (a (m_ k) * rho (m_ k) ^ (n_ k)) = _
    rw [Real.log_mul ha.ne' hrpow.ne', hlogrho]
  have hlogD : Real.log (D (m_ k) (n_ k) (h_ k)) =
      Real.log (p (n_ k) (h_ k)) - Real.log (A (m_ k) (n_ k)) := by
    rw [hDp]
    exact Real.log_div hp.ne' hA.ne'
  have hlogp : Real.log (p (n_ k) (h_ k)) - Real.log (a (m_ k)) -
      N (n_ k) * Real.log (rho (m_ k)) =
      Real.log (D (m_ k) (n_ k) (h_ k)) := by
    rw [hlogA] at hlogD
    linarith only [hlogD]
  have hlogK : Real.log (K (n_ k) (h_ k)) - Real.log (a (m_ k)) -
      N (n_ k) * Real.log (rho (m_ k)) =
      Real.log (D (m_ k) (n_ k) (h_ k)) := by
    rw [← hpK]
    exact hlogp
  have hlogT : Real.log (b B P hB (x (n_ k) (h_ k))) -
      Real.log (g (x (n_ k) (h_ k))) =
      Real.log (T B P hB (x (n_ k) (h_ k))) := by
    exact (Real.log_div hb.ne' hg.ne').symm
  have hlogpq :
      Real.log (p (n_ k) (h_ k) / b B P hB (x (n_ k) (h_ k))) =
        Real.log (p (n_ k) (h_ k)) -
          Real.log (b B P hB (x (n_ k) (h_ k))) := Real.log_div hp.ne' hb.ne'
  have hlogKq :
      Real.log (K (n_ k) (h_ k) / b B P hB (x (n_ k) (h_ k))) =
        Real.log (K (n_ k) (h_ k)) -
          Real.log (b B P hB (x (n_ k) (h_ k))) := Real.log_div hK.ne' hb.ne'
  have hcenter :
      Real.log (p (n_ k) (h_ k) / b B P hB (x (n_ k) (h_ k))) -
          C (m_ k) (n_ k) (h_ k) =
        Real.log (D (m_ k) (n_ k) (h_ k)) -
          Real.log (T B P hB (x (n_ k) (h_ k))) := by
    rw [hlogpq]
    dsimp only [C]
    linarith only [hlogp, hlogT, hlogg, hloga]
  have hcenterK :
      Real.log (K (n_ k) (h_ k) / b B P hB (x (n_ k) (h_ k))) -
          C (m_ k) (n_ k) (h_ k) =
        Real.log (D (m_ k) (n_ k) (h_ k)) -
          Real.log (T B P hB (x (n_ k) (h_ k))) := by
    rw [← hpK]
    exact hcenter
  exact ⟨hn, hN, hsqrt, hh, hx, ha, hr, hA, hπa, hp, hK, hD, hb, hg,
    hT, hpq, hKq, hlogp, hlogK, hlogT, hlogpq, hlogKq, hcenter, hcenterK⟩

theorem S3_MAIN {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (m_ n_ : ℕ → ℕ) (h_ : ℕ → ℝ)
    (hm : ∀ k : ℕ, 1 ≤ m_ k)
    (hmh : ∀ k : ℕ, (m_ k : ℝ) ≤ h_ k)
    (hhm : ∀ k : ℕ, h_ k < (m_ k : ℝ) + 1)
    (hH : Tendsto (fun k : ℕ => H (m_ k)) atTop atTop)
    (ht : Tendsto (fun k : ℕ => t (m_ k) (n_ k)) atTop atTop) :
    Tendsto
      (fun k : ℕ =>
        Real.log (p (n_ k) (h_ k) /
          Shao.Probability.BrownianSup.probability B P hB
            (h_ k / Real.sqrt (N (n_ k)))) -
        (lambda * N (n_ k) / (h_ k) ^ 2 +
          N (n_ k) * Real.log (rho (m_ k)) +
          Real.log (Real.pi * a (m_ k) / 4)))
      atTop (𝓝 (0 : ℝ)) := by
  rcases S3_DOM B P hB m_ n_ h_ hm hmh hhm hH ht with
    ⟨_, _, _, _, _, _, hlogD, _, _, hlogT, _⟩
  have hresidual :
      Tendsto (fun k : ℕ => Real.log (D (m_ k) (n_ k) (h_ k)) -
        Real.log (T B P hB (x (n_ k) (h_ k)))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using hlogD.sub hlogT
  obtain ⟨K_alg, halg⟩ := S3_ALG B P hB m_ n_ h_ hm hmh hhm hH ht
  apply Filter.Tendsto.congr' _ hresidual
  filter_upwards [eventually_ge_atTop K_alg] with k hk
  rcases halg k hk with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc, _⟩
  simpa only [C, b, x] using hc.symm

theorem S3_MAIN_epsilon {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (m_ n_ : ℕ → ℕ) (h_ : ℕ → ℝ)
    (hm : ∀ k : ℕ, 1 ≤ m_ k)
    (hmh : ∀ k : ℕ, (m_ k : ℝ) ≤ h_ k)
    (hhm : ∀ k : ℕ, h_ k < (m_ k : ℝ) + 1)
    (hH : Tendsto (fun k : ℕ => H (m_ k)) atTop atTop)
    (ht : Tendsto (fun k : ℕ => t (m_ k) (n_ k)) atTop atTop) :
    ∃ K_time K_pos : ℕ, K_time ≤ K_pos ∧
        (∀ k : ℕ, K_time ≤ k →
          1 ≤ n_ k ∧ 0 < N (n_ k) ∧ 0 < Real.sqrt (N (n_ k)) ∧
          0 < x (n_ k) (h_ k)) ∧
        (∀ k : ℕ, K_pos ≤ k →
          0 < h_ k ∧ 0 < a (m_ k) ∧ 0 < rho (m_ k) ∧
          0 < Real.pi * a (m_ k) / 4 ∧
          p (n_ k) (h_ k) = K (n_ k) (h_ k) ∧
          0 < p (n_ k) (h_ k) ∧ 0 < K (n_ k) (h_ k) ∧
          0 < D (m_ k) (n_ k) (h_ k) ∧
          0 < b B P hB (x (n_ k) (h_ k)) ∧
          0 < T B P hB (x (n_ k) (h_ k)) ∧
          0 < p (n_ k) (h_ k) / b B P hB (x (n_ k) (h_ k)) ∧
          0 < K (n_ k) (h_ k) / b B P hB (x (n_ k) (h_ k))) ∧
        (∀ e : ℝ, 0 < e → ∃ K_e : ℕ, K_pos ≤ K_e ∧
          ∀ k : ℕ, K_e ≤ k →
          |Real.log (p (n_ k) (h_ k) /
            Shao.Probability.BrownianSup.probability B P hB
              (h_ k / Real.sqrt (N (n_ k)))) -
            (lambda * N (n_ k) / (h_ k) ^ 2 +
              N (n_ k) * Real.log (rho (m_ k)) +
              Real.log (Real.pi * a (m_ k) / 4))| < e) := by
  rcases S3_DOM B P hB m_ n_ h_ hm hmh hhm hH ht with
    ⟨_, _, _, _, _, _, _, _, _, _, K_time, htime, K_pos, htime_pos, hpos⟩
  refine ⟨K_time, K_pos, htime_pos, ?_, ?_, ?_⟩
  · intro k hk
    rcases htime k hk with ⟨hn, hN, hsqrt, hx, _, _⟩
    exact ⟨hn, hN, hsqrt, hx⟩
  · intro k hk
    rcases hpos k hk with ⟨hpK, hp, hK, hD, hb, hT, _, hpq, hKq⟩
    rcases finite_identities (m_ k) (hm k) (h_ k) (hmh k) (hhm k) (n_ k) with
      ⟨_, hh, _, _, ha, hr, _, _, _, _, _, _, _, _, _⟩
    have hπa : 0 < Real.pi * a (m_ k) / 4 :=
      div_pos (mul_pos Real.pi_pos ha) (by norm_num)
    exact ⟨hh, ha, hr, hπa, hpK, hp, hK, hD, hb, hT, hpq, hKq⟩
  · intro e he
    obtain ⟨K_0, hK0⟩ :=
      (Metric.tendsto_atTop.1 (S3_MAIN B P hB m_ n_ h_ hm hmh hhm hH ht)) e he
    refine ⟨max K_pos K_0, le_max_left _ _, ?_⟩
    intro k hk
    have hbnd := hK0 k ((le_max_right _ _).trans hk)
    simpa only [Real.dist_eq, sub_zero] using hbnd

end Shao.OQ4.RademacherS3Assembly

end
