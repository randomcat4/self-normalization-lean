import Shao.OQ4.RademacherSpectralTail
import Shao.OQ4.RademacherScalarBounds

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Shao.OQ4.RademacherS2Assembly

def H (m : ℕ) : ℝ := (m : ℝ) + 1

def N (n : ℕ) : ℝ := (n : ℝ)

def t (m n : ℕ) : ℝ := N n / H m ^ 2

def a (m : ℕ) : ℝ := RademacherSpectralPairing.amplitude m

def rho (m : ℕ) : ℝ := RademacherSpectralPairing.rho m

def eps (m n : ℕ) : ℝ := RademacherSpectralPairing.epsilon m n

def q (m : ℕ) : ℝ := (Real.tan (RademacherScalarBounds.u m)) ^ 2

def R (m n : ℕ) : ℝ := RademacherSpectralPairing.remainder m n

def B (m n : ℕ) : ℝ := a m * rho m ^ n

def p (n : ℕ) (h : ℝ) : ℝ :=
  (Measure.pi (fun _ : Fin n => RademacherCosine.law)).real
    (@Shao.closedStrip n h)

def K (n : ℕ) (h : ℝ) : ℝ :=
  @Shao.OQ4.killedMass RademacherCosine.law
    RademacherCosine.law_isProbabilityMeasure h n (0 : ℝ)

def D (m n : ℕ) (h : ℝ) : ℝ := p n h / B m n

def C_U : ℝ := RademacherSpectralTail.absoluteC

theorem definition_bridges (m : ℕ) :
    RademacherSpectralPairing.alpha m 0 = RademacherScalarBounds.u m ∧
    RademacherSpectralPairing.beta m 0 = RademacherScalarBounds.z m ∧
    a m =
      (1 / H m) *
        (Real.cos (RademacherScalarBounds.u m) /
          Real.sin (RademacherScalarBounds.u m)) ∧
    a m = RademacherScalarBounds.a m ∧
    rho m = Real.cos (RademacherScalarBounds.z m) ∧
    rho m = RademacherScalarBounds.rho m := by
  simp [a, rho, H, RademacherSpectralPairing.alpha,
    RademacherSpectralPairing.beta, RademacherSpectralPairing.amplitude,
    RademacherSpectralPairing.rho, RademacherFiniteS1.cotangent,
    RademacherScalarBounds.u, RademacherScalarBounds.z,
    RademacherScalarBounds.H, RademacherScalarBounds.a,
    RademacherScalarBounds.rho]

theorem F0 (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) (n : ℕ) :
    0 < a m ∧
    0 < rho m ∧
    rho m < 1 ∧
    0 < B m n ∧
    p n h = K n h ∧
    p n h = B m n * (1 + eps m n * q m + R m n) ∧
    D m n h = K n h / B m n ∧
    D m n h = 1 + eps m n * q m + R m n := by
  have ha : 0 < a m := RademacherSpectralPairing.amplitude_pos hm
  have hr : 0 < rho m := RademacherSpectralPairing.rho_pos hm
  have hr1 : rho m < 1 := RademacherSpectralPairing.rho_lt_one hm
  have hB : 0 < B m n := RademacherSpectralPairing.normalizer_pos hm n
  have hpK : p n h = K n h :=
    RademacherSpectralPairing.closedStrip_probability_eq_killedMass m hm h hmh hhm n
  have hp : p n h = B m n * (1 + eps m n * q m + R m n) := by
    simpa [p, B, a, rho, eps, q, R, RademacherScalarBounds.u,
      RademacherScalarBounds.H] using
      RademacherSpectralPairing.closedStrip_probability_normalized m hm h hmh hhm n
  have hDK : D m n h = K n h / B m n := by
    unfold D
    rw [hpK]
  have hD : D m n h = 1 + eps m n * q m + R m n := by
    unfold D
    rw [hp]
    exact mul_div_cancel_left₀ _ hB.ne'
  exact ⟨ha, hr, hr1, hB, hpK, hp, hDK, hD⟩

theorem F0_zero_time (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) :
    p 0 h = 1 ∧
    K 0 h = 1 ∧
    RademacherSpectralPairing.zeroMode m 0 =
      (if Even m then (-1 : ℝ) ^ (m / 2) / H m else 0) := by
  have hp : p 0 h = 1 :=
    RademacherSpectralPairing.closedStrip_probability_zero m hm h hmh hhm
  have hpK : p 0 h = K 0 h :=
    RademacherSpectralPairing.closedStrip_probability_eq_killedMass m hm h hmh hhm 0
  refine ⟨hp, hpK.symm.trans hp, ?_⟩
  simpa [H] using RademacherSpectralPairing.zeroMode_zero m

theorem F0_small_cells :
    (∀ n : ℕ, R 1 n = 0) ∧
    (∀ n : ℕ, 1 ≤ n → R 2 n = 0) ∧
    RademacherSpectralPairing.zeroMode 2 0 = -(1 / 3 : ℝ) ∧
    R 2 0 = -1 / (3 * a 2) ∧
    R 2 0 ≠ 0 := by
  have hr20 : R 2 0 = -1 / (3 * a 2) :=
    RademacherSpectralPairing.remainder_two_zero
  refine ⟨RademacherSpectralPairing.remainder_one,
    fun n hn => RademacherSpectralPairing.remainder_two_positive_time hn,
    RademacherSpectralPairing.zeroMode_two_zero, hr20, ?_⟩
  rw [hr20]
  exact div_ne_zero (by norm_num)
    (mul_ne_zero (by norm_num)
      (ne_of_gt (RademacherSpectralPairing.amplitude_pos (by norm_num : 1 ≤ 2))))

theorem T0 {m : ℕ} (hm : 1 ≤ m) :
    0 ≤ q m ∧
    q m ≤ Real.pi ^ 2 / (4 * H m ^ 2) ∧
    ∀ n : ℕ, |eps m n| = 1 := by
  rcases RademacherScalarBounds.SCA0 hm with
    ⟨hH2, hH, hHsq, hH4, hu, hu8, hpi8, hz, hz4, hpi4,
      hsin, hcos, hcosz, ha, hr, hr1, hpa⟩
  have hc : ∀ x ∈ Set.Icc (0 : ℝ) (RademacherScalarBounds.u m),
      0 < Real.cos x := by
    intro x hx
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos, hx.1, hx.2]
  have hcsq : ∀ x ∈ Set.Icc (0 : ℝ) (RademacherScalarBounds.u m),
      (1 / 2 : ℝ) ≤ Real.cos x ^ 2 := by
    intro x hx
    have hc2 : 0 ≤ Real.cos (2 * x) := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor <;> linarith [Real.pi_pos, hx.1, hx.2]
    nlinarith [Real.cos_two_mul x]
  have hcont : ContinuousOn Real.tan
      (Set.Icc (0 : ℝ) (RademacherScalarBounds.u m)) := by
    intro x hx
    exact (Real.hasDerivAt_tan (hc x hx).ne').continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ Real.tan
      (interior (Set.Icc (0 : ℝ) (RademacherScalarBounds.u m))) := by
    intro x hx
    exact (Real.hasDerivAt_tan (hc x (interior_subset hx)).ne').differentiableAt.differentiableWithinAt
  have hder : ∀ x ∈ interior (Set.Icc (0 : ℝ) (RademacherScalarBounds.u m)),
      deriv Real.tan x ≤ (2 : ℝ) := by
    intro x hx
    rw [Real.deriv_tan]
    apply (div_le_iff₀ (sq_pos_of_pos (hc x (interior_subset hx)))).2
    nlinarith [hcsq x (interior_subset hx)]
  have htan : Real.tan (RademacherScalarBounds.u m) ≤
      2 * RademacherScalarBounds.u m := by
    have hh := (convex_Icc (0 : ℝ) (RademacherScalarBounds.u m)).image_sub_le_mul_sub_of_deriv_le
      hcont hdiff hder 0 ⟨le_rfl, hu.le⟩
      (RademacherScalarBounds.u m) ⟨hu.le, le_rfl⟩ hu.le
    simpa only [Real.tan_zero, sub_zero] using hh
  have htan0 : 0 ≤ Real.tan (RademacherScalarBounds.u m) :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two hu.le (hu8.trans hpi8.le)
  have hbound : q m ≤ (2 * RademacherScalarBounds.u m) ^ 2 := by
    unfold q
    have hh := mul_nonneg (sub_nonneg.mpr htan)
      (show 0 ≤ 2 * RademacherScalarBounds.u m +
        Real.tan (RademacherScalarBounds.u m) by positivity)
    nlinarith
  have halg : (2 * RademacherScalarBounds.u m) ^ 2 =
      Real.pi ^ 2 / (4 * H m ^ 2) := by
    unfold RademacherScalarBounds.u RademacherScalarBounds.H H
    have hne : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    norm_num
  refine ⟨sq_nonneg _, hbound.trans halg.le, ?_⟩
  intro n
  simp [eps, RademacherSpectralPairing.epsilon, abs_pow]

theorem F1 :
    0 < C_U ∧
    ∀ m : ℕ, 1 ≤ m →
    ∀ h : ℝ, (m : ℝ) ≤ h → h < (m : ℝ) + 1 →
    ∀ n : ℕ, H m ^ 2 ≤ N n →
      |R m n| ≤
        C_U * Real.exp (-Real.pi ^ 2 * N n / H m ^ 2) ∧
      |D m n h - 1 - eps m n * q m| ≤
        C_U * Real.exp (-Real.pi ^ 2 * N n / H m ^ 2) ∧
      |D m n h - 1| ≤
        Real.pi ^ 2 / (4 * H m ^ 2) +
          C_U * Real.exp (-Real.pi ^ 2 * N n / H m ^ 2) := by
  refine ⟨RademacherSpectralTail.absoluteC_pos, ?_⟩
  intro m hm h hmh hhm n hn
  rcases F0 m hm h hmh hhm n with ⟨ha, hr, hr1, hB, hpK, hp, hDK, hD⟩
  rcases T0 hm with ⟨hq0, hq, heps⟩
  have hR : |R m n| ≤
      C_U * Real.exp (-Real.pi ^ 2 * N n / H m ^ 2) := by
    simpa [R, C_U, H, N] using
      RademacherSpectralTail.remainder_uniform hm (by simpa [H, N] using hn)
  have hcorrect : D m n h - 1 - eps m n * q m = R m n := by
    rw [hD]
    ring
  have htotal : D m n h - 1 = eps m n * q m + R m n := by
    rw [hD]
    ring
  refine ⟨hR, ?_, ?_⟩
  · rw [hcorrect]
    exact hR
  · calc
      |D m n h - 1| = |eps m n * q m + R m n| := congrArg abs htotal
      _ ≤ |eps m n * q m| + |R m n| := abs_add_le _ _
      _ = q m + |R m n| := by
        rw [abs_mul, heps n, one_mul, abs_of_nonneg hq0]
      _ ≤ Real.pi ^ 2 / (4 * H m ^ 2) +
          C_U * Real.exp (-Real.pi ^ 2 * N n / H m ^ 2) :=
        add_le_add hq hR

theorem Q1 (m_ n_ : ℕ → ℕ) (h_ : ℕ → ℝ)
    (hm : ∀ k : ℕ, 1 ≤ m_ k)
    (hmh : ∀ k : ℕ, (m_ k : ℝ) ≤ h_ k)
    (hhm : ∀ k : ℕ, h_ k < (m_ k : ℝ) + 1)
    (hH : Tendsto (fun k : ℕ => H (m_ k)) atTop atTop)
    (ht : Tendsto (fun k : ℕ => t (m_ k) (n_ k)) atTop atTop) :
    (∀ k : ℕ,
      0 < a (m_ k) ∧
      0 < rho (m_ k) ∧
      rho (m_ k) < 1 ∧
      0 < B (m_ k) (n_ k) ∧
      p (n_ k) (h_ k) = K (n_ k) (h_ k) ∧
      p (n_ k) (h_ k) =
        B (m_ k) (n_ k) *
          (1 + eps (m_ k) (n_ k) * q (m_ k) + R (m_ k) (n_ k)) ∧
      D (m_ k) (n_ k) (h_ k) =
        K (n_ k) (h_ k) / B (m_ k) (n_ k) ∧
      D (m_ k) (n_ k) (h_ k) =
        1 + eps (m_ k) (n_ k) * q (m_ k) + R (m_ k) (n_ k) ∧
      (n_ k = 0 →
        p (n_ k) (h_ k) = 1 ∧ K (n_ k) (h_ k) = 1)) ∧
    (∃ K_time : ℕ, ∀ k : ℕ, K_time ≤ k →
      H (m_ k) ^ 2 ≤ N (n_ k) ∧
      1 ≤ n_ k ∧
      |R (m_ k) (n_ k)| ≤
        C_U * Real.exp
          (-Real.pi ^ 2 * N (n_ k) / H (m_ k) ^ 2) ∧
      |D (m_ k) (n_ k) (h_ k) - 1 -
          eps (m_ k) (n_ k) * q (m_ k)| ≤
        C_U * Real.exp
          (-Real.pi ^ 2 * N (n_ k) / H (m_ k) ^ 2) ∧
      |D (m_ k) (n_ k) (h_ k) - 1| ≤
        Real.pi ^ 2 / (4 * H (m_ k) ^ 2) +
          C_U * Real.exp
            (-Real.pi ^ 2 * N (n_ k) / H (m_ k) ^ 2)) ∧
    Tendsto
      (fun k : ℕ => Real.pi ^ 2 / (4 * H (m_ k) ^ 2))
      atTop (𝓝 (0 : ℝ)) ∧
    Tendsto
      (fun k : ℕ =>
        C_U * Real.exp (-Real.pi ^ 2 * N (n_ k) / H (m_ k) ^ 2))
      atTop (𝓝 (0 : ℝ)) ∧
    Tendsto (fun k : ℕ => D (m_ k) (n_ k) (h_ k))
      atTop (𝓝 (1 : ℝ)) ∧
    Tendsto
      (fun k : ℕ => K (n_ k) (h_ k) / B (m_ k) (n_ k))
      atTop (𝓝 (1 : ℝ)) ∧
    (∃ K_pos : ℕ, ∀ k : ℕ, K_pos ≤ k →
      0 < D (m_ k) (n_ k) (h_ k) ∧
      0 < p (n_ k) (h_ k) ∧
      0 < K (n_ k) (h_ k) ∧
      Real.log (p (n_ k) (h_ k)) - Real.log (a (m_ k)) -
          N (n_ k) * Real.log (rho (m_ k)) =
        Real.log (D (m_ k) (n_ k) (h_ k)) ∧
      Real.log (K (n_ k) (h_ k)) - Real.log (a (m_ k)) -
          N (n_ k) * Real.log (rho (m_ k)) =
        Real.log (D (m_ k) (n_ k) (h_ k))) ∧
    Tendsto
      (fun k : ℕ => Real.log (D (m_ k) (n_ k) (h_ k)))
      atTop (𝓝 (0 : ℝ)) ∧
    Tendsto
      (fun k : ℕ =>
        Real.log (p (n_ k) (h_ k)) - Real.log (a (m_ k)) -
          N (n_ k) * Real.log (rho (m_ k)))
      atTop (𝓝 (0 : ℝ)) ∧
    Tendsto
      (fun k : ℕ =>
        Real.log (K (n_ k) (h_ k)) - Real.log (a (m_ k)) -
          N (n_ k) * Real.log (rho (m_ k)))
      atTop (𝓝 (0 : ℝ)) := by
  have hAll :
      ∀ k : ℕ,
        0 < a (m_ k) ∧ 0 < rho (m_ k) ∧ rho (m_ k) < 1 ∧
        0 < B (m_ k) (n_ k) ∧
        p (n_ k) (h_ k) = K (n_ k) (h_ k) ∧
        p (n_ k) (h_ k) =
          B (m_ k) (n_ k) *
            (1 + eps (m_ k) (n_ k) * q (m_ k) + R (m_ k) (n_ k)) ∧
        D (m_ k) (n_ k) (h_ k) =
          K (n_ k) (h_ k) / B (m_ k) (n_ k) ∧
        D (m_ k) (n_ k) (h_ k) =
          1 + eps (m_ k) (n_ k) * q (m_ k) + R (m_ k) (n_ k) ∧
        (n_ k = 0 → p (n_ k) (h_ k) = 1 ∧ K (n_ k) (h_ k) = 1) := by
    intro k
    rcases F0 (m_ k) (hm k) (h_ k) (hmh k) (hhm k) (n_ k) with
      ⟨ha, hr, hr1, hB, hpK, hp, hDK, hD⟩
    refine ⟨ha, hr, hr1, hB, hpK, hp, hDK, hD, ?_⟩
    intro hn0
    rcases F0_zero_time (m_ k) (hm k) (h_ k) (hmh k) (hhm k) with
      ⟨hp0, hK0, hz⟩
    simpa only [hn0] using And.intro hp0 hK0
  have hInv : Tendsto (fun k : ℕ => (H (m_ k))⁻¹)
      atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hH
  have hA : Tendsto
      (fun k : ℕ => Real.pi ^ 2 / (4 * H (m_ k) ^ 2))
      atTop (𝓝 (0 : ℝ)) := by
    have heq :
        (fun k : ℕ => Real.pi ^ 2 / (4 * H (m_ k) ^ 2)) =
        (fun k : ℕ => (Real.pi ^ 2 / 4) * ((H (m_ k))⁻¹) ^ 2) := by
      funext k
      simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
      ring
    rw [heq]
    simpa using (hInv.pow 2).const_mul (Real.pi ^ 2 / 4)
  have hneg : -Real.pi ^ 2 < (0 : ℝ) :=
    neg_neg_of_pos (sq_pos_of_pos Real.pi_pos)
  have hnegTime := ht.const_mul_atTop_of_neg hneg
  have hE : Tendsto
      (fun k : ℕ => C_U * Real.exp
        (-Real.pi ^ 2 * N (n_ k) / H (m_ k) ^ 2))
      atTop (𝓝 (0 : ℝ)) := by
    have hh := (Real.tendsto_exp_atBot.comp hnegTime).const_mul C_U
    simpa only [Function.comp_def, t, ← mul_div_assoc, mul_zero] using hh
  obtain ⟨K_time, htime'⟩ :=
    eventually_atTop.mp (ht.eventually (eventually_ge_atTop (1 : ℝ)))
  have htime : ∀ k : ℕ, K_time ≤ k →
      H (m_ k) ^ 2 ≤ N (n_ k) ∧ 1 ≤ n_ k := by
    intro k hk
    have hHp : 0 < H (m_ k) := by unfold H; positivity
    have hsq : 0 < H (m_ k) ^ 2 := sq_pos_of_pos hHp
    have htn := (le_div_iff₀ hsq).mp (htime' k hk)
    simp only [one_mul] at htn
    have hnR : (0 : ℝ) < N (n_ k) := lt_of_lt_of_le hsq htn
    have hnN : 0 < n_ k := (Nat.cast_pos (α := ℝ)).mp (by simpa only [N] using hnR)
    exact ⟨htn, hnN⟩
  have hAbs : Tendsto
      (fun k : ℕ => |D (m_ k) (n_ k) (h_ k) - 1|)
      atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero' (Eventually.of_forall (fun k => abs_nonneg _))
    · filter_upwards [eventually_ge_atTop K_time] with k hk
      exact (F1.2 (m_ k) (hm k) (h_ k) (hmh k) (hhm k) (n_ k)
        (htime k hk).1).2.2
    · simpa only [zero_add] using hA.add hE
  have hD : Tendsto (fun k : ℕ => D (m_ k) (n_ k) (h_ k))
      atTop (𝓝 (1 : ℝ)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [Real.dist_eq] using hAbs
  have hK : Tendsto
      (fun k : ℕ => K (n_ k) (h_ k) / B (m_ k) (n_ k))
      atTop (𝓝 (1 : ℝ)) := by
    apply Filter.Tendsto.congr' _ hD
    exact Eventually.of_forall (fun k => (hAll k).2.2.2.2.2.2.1)
  obtain ⟨K_pos, hpos'⟩ :=
    eventually_atTop.mp (hD.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)))
  have hPos : ∀ k : ℕ, K_pos ≤ k →
      0 < D (m_ k) (n_ k) (h_ k) ∧
      0 < p (n_ k) (h_ k) ∧
      0 < K (n_ k) (h_ k) ∧
      Real.log (p (n_ k) (h_ k)) - Real.log (a (m_ k)) -
          N (n_ k) * Real.log (rho (m_ k)) =
        Real.log (D (m_ k) (n_ k) (h_ k)) ∧
      Real.log (K (n_ k) (h_ k)) - Real.log (a (m_ k)) -
          N (n_ k) * Real.log (rho (m_ k)) =
        Real.log (D (m_ k) (n_ k) (h_ k)) := by
    intro k hk
    rcases F0 (m_ k) (hm k) (h_ k) (hmh k) (hhm k) (n_ k) with
      ⟨ha, hr, hr1, hB, hpK, hp, hDK, hID⟩
    have hd : 0 < D (m_ k) (n_ k) (h_ k) := hpos' k hk
    have hpBD : p (n_ k) (h_ k) =
        B (m_ k) (n_ k) * D (m_ k) (n_ k) (h_ k) := by
      unfold D
      field_simp
    have hpp : 0 < p (n_ k) (h_ k) := by
      rw [hpBD]
      exact mul_pos hB hd
    have hkp : 0 < K (n_ k) (h_ k) := hpK ▸ hpp
    have hlogB : Real.log (B (m_ k) (n_ k)) =
        Real.log (a (m_ k)) + N (n_ k) * Real.log (rho (m_ k)) := by
      rw [B, Real.log_mul ha.ne' (pow_pos hr (n_ k)).ne', Real.log_pow]
      rfl
    have hlogD : Real.log (D (m_ k) (n_ k) (h_ k)) =
        Real.log (p (n_ k) (h_ k)) - Real.log (B (m_ k) (n_ k)) := by
      unfold D
      exact Real.log_div hpp.ne' hB.ne'
    have hlogP :
        Real.log (p (n_ k) (h_ k)) - Real.log (a (m_ k)) -
            N (n_ k) * Real.log (rho (m_ k)) =
          Real.log (D (m_ k) (n_ k) (h_ k)) := by
      rw [hlogB] at hlogD
      linarith
    refine ⟨hd, hpp, hkp, hlogP, ?_⟩
    rw [← hpK]
    exact hlogP
  have hLogD : Tendsto
      (fun k : ℕ => Real.log (D (m_ k) (n_ k) (h_ k)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hD
  have hLogP : Tendsto
      (fun k : ℕ =>
        Real.log (p (n_ k) (h_ k)) - Real.log (a (m_ k)) -
          N (n_ k) * Real.log (rho (m_ k)))
      atTop (𝓝 (0 : ℝ)) := by
    apply Filter.Tendsto.congr' _ hLogD
    filter_upwards [eventually_ge_atTop K_pos] with k hk
    exact (hPos k hk).2.2.2.1.symm
  have hLogK : Tendsto
      (fun k : ℕ =>
        Real.log (K (n_ k) (h_ k)) - Real.log (a (m_ k)) -
          N (n_ k) * Real.log (rho (m_ k)))
      atTop (𝓝 (0 : ℝ)) := by
    apply Filter.Tendsto.congr' _ hLogD
    filter_upwards [eventually_ge_atTop K_pos] with k hk
    exact (hPos k hk).2.2.2.2.symm
  refine ⟨hAll, ⟨K_time, ?_⟩, hA, hE, hD, hK,
    ⟨K_pos, hPos⟩, hLogD, hLogP, hLogK⟩
  intro k hk
  rcases htime k hk with ⟨hn, hnNat⟩
  rcases F1.2 (m_ k) (hm k) (h_ k) (hmh k) (hhm k) (n_ k) hn with
    ⟨hR, hcorrect, htotal⟩
  exact ⟨hn, hnNat, hR, hcorrect, htotal⟩

end Shao.OQ4.RademacherS2Assembly

end
