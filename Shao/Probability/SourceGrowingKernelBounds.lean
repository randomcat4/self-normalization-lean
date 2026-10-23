import Shao.Probability.SourceGrowingRegionIntegrals
import Shao.Probability.SourceGrowingTiltParameterPayment
import Shao.Probability.SourceLocalizedMicrotimeDerivatives
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

/- Signed Taylor displacement with its actual, possibly nonzero linear term. -/
private theorem sgk_positive_remainder (g : ℝ → ℝ) (M u : ℝ) (hu : 0 ≤ u)
    (hd : ∀ t ∈ Set.Icc 0 u, DifferentiableAt ℝ g t)
    (hdd : ∀ t ∈ Set.Icc 0 u, DifferentiableAt ℝ (deriv g) t)
    (hb : ∀ t ∈ Set.Icc 0 u, |deriv (deriv g) t| ≤ M) :
    |g u - g 0 - u * deriv g 0| ≤ M / 2 * u ^ 2 := by


  have h0 : (0 : ℝ) ∈ Set.Icc 0 u := ⟨le_rfl, hu⟩
  have huI : u ∈ Set.Icc 0 u := ⟨hu, le_rfl⟩
  have hp (t : ℝ) (ht : t ∈ Set.Icc 0 u) :
      |deriv g t - deriv g 0| ≤ M * t := by
    have hh := (convex_Icc (0 : ℝ) u).norm_image_sub_le_of_norm_deriv_le hdd
      (fun r hr => by simpa only [Real.norm_eq_abs] using hb r hr) h0 ht
    simpa only [sub_zero, Real.norm_eq_abs, abs_of_nonneg ht.1] using hh
  have hpD (t : ℝ) (ht : t ∈ Set.Icc 0 u) :
      HasDerivAt (fun r : ℝ => M / 2 * r ^ 2 - (g r - g 0 - r * deriv g 0))
        (M * t - (deriv g t - deriv g 0)) t := by
    convert (((hasDerivAt_id t).pow 2).const_mul (M / 2)).sub
      (((hd t ht).hasDerivAt.sub_const (g 0)).sub
        ((hasDerivAt_id t).mul_const (deriv g 0))) using 1
    · funext r; dsimp <;> ring1_nf (config := { zetaDelta := false })
    · dsimp; ring1_nf (config := { zetaDelta := false })
  have hmD (t : ℝ) (ht : t ∈ Set.Icc 0 u) :
      HasDerivAt (fun r : ℝ => M / 2 * r ^ 2 + (g r - g 0 - r * deriv g 0))
        (M * t + (deriv g t - deriv g 0)) t := by
    convert (((hasDerivAt_id t).pow 2).const_mul (M / 2)).add
      (((hd t ht).hasDerivAt.sub_const (g 0)).sub
        ((hasDerivAt_id t).mul_const (deriv g 0))) using 1
    · funext r; dsimp <;> ring1_nf (config := { zetaDelta := false })
    · dsimp; ring1_nf (config := { zetaDelta := false })
  have hplus : MonotoneOn
      (fun r : ℝ => M / 2 * r ^ 2 - (g r - g 0 - r * deriv g 0)) (Set.Icc 0 u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) u)
    · exact fun t ht => (hpD t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hpD t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hpD t (interior_subset ht)).deriv]
      exact sub_nonneg.mpr ((le_abs_self _).trans (hp t (interior_subset ht)))
  have hminus : MonotoneOn
      (fun r : ℝ => M / 2 * r ^ 2 + (g r - g 0 - r * deriv g 0)) (Set.Icc 0 u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) u)
    · exact fun t ht => (hmD t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hmD t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hmD t (interior_subset ht)).deriv]
      have hh := (abs_le.mp (hp t (interior_subset ht))).1
      linarith
  have hupper := hplus h0 huI hu
  have hlower := hminus h0 huI hu
  apply abs_le.mpr
  constructor <;> linarith

private theorem sgk_signed_remainder (g : ℝ → ℝ) (h M : ℝ) (hh : 0 ≤ h)
    (hd : ∀ t : ℝ, DifferentiableAt ℝ g t ∧ DifferentiableAt ℝ (deriv g) t)
    (hb : ∀ t : ℝ, |t| ≤ h → |deriv (deriv g) t| ≤ M) :
    ∀ w : ℝ, |w| ≤ h →
      |deriv g w - deriv g 0| ≤ M * |w| ∧
      |g w - g 0 - w * deriv g 0| ≤ M / 2 * w ^ 2 := by

  have hd1 : ∀ t ∈ Set.Icc (-h) h, DifferentiableAt ℝ (deriv g) t := fun t _ => (hd t).2

  have h0 : (0 : ℝ) ∈ Set.Icc (-h) h := ⟨by linarith, hh⟩
  intro w hw
  have hwI : w ∈ Set.Icc (-h) h := abs_le.mp hw
  have hdif := (convex_Icc (-h) h).norm_image_sub_le_of_norm_deriv_le hd1
    (fun t ht => by simpa only [Real.norm_eq_abs] using hb t (abs_le.mpr ht)) h0 hwI
  refine ⟨by simpa only [Real.norm_eq_abs, sub_zero] using hdif, ?_⟩
  by_cases hw0 : 0 ≤ w
  · exact sgk_positive_remainder g M w hw0
      (fun t _ => (hd t).1) (fun t _ => (hd t).2)
      (fun t ht => hb t (by rw [abs_of_nonneg ht.1]; exact ht.2.trans (by linarith [hwI.2])))
  · have hv : 0 ≤ -w := by linarith
    let k : ℝ → ℝ := fun t => g (-t)
    have hk (t : ℝ) : HasDerivAt k (-deriv g (-t)) t := by
      simpa only [k, Function.comp_def, mul_neg, mul_one] using
        ((hd (-t)).1.hasDerivAt.comp t ((hasDerivAt_id t).neg))
    have hkder : deriv k = fun t => -deriv g (-t) := funext fun t => (hk t).deriv
    have hkk (t : ℝ) : HasDerivAt (deriv k) (deriv (deriv g) (-t)) t := by
      rw [hkder]
      convert (((hd (-t)).2.hasDerivAt.comp t ((hasDerivAt_id t).neg)).neg) using 1
      · funext r; rfl
      · simp only [mul_neg, mul_one, neg_neg]
    have hr := sgk_positive_remainder k M (-w) hv
      (fun t _ => (hk t).differentiableAt) (fun t _ => (hkk t).differentiableAt)
      (fun t ht => by
        rw [(hkk t).deriv]
        apply hb (-t)
        rw [abs_neg, abs_of_nonneg ht.1]
        linarith [ht.2, hwI.1])
    simpa only [k, neg_neg, hkder, Pi.neg_apply, neg_zero, mul_neg, neg_mul, neg_sq] using hr

/- A positive-degree normalized Gamma monomial consumes only one Lambda. -/
private theorem sgk_monomial (a G z K : ℝ) (p r : ℕ)
    (ha : 1 ≤ a) (hG : 0 ≤ G) (hz : 0 ≤ z) (hz1 : z ≤ 1) (hK : 0 ≤ K)
    (hGK : a ^ 3 * G ≤ K * z) (hp : 1 ≤ p) (hr : r ≤ 3 * p) :
    a ^ r * G ^ p ≤ K ^ p * z := by

  have ha0 : 0 ≤ a := (by norm_num : (0 : ℝ) ≤ 1).trans ha
  calc
    a ^ r * G ^ p ≤ a ^ (3 * p) * G ^ p := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ha hr) (pow_nonneg hG _)
    _ = (a ^ 3 * G) ^ p := by rw [mul_pow, ← pow_mul]
    _ ≤ (K * z) ^ p := pow_le_pow_left₀ (by positivity) hGK _
    _ = K ^ p * z ^ p := mul_pow _ _ _
    _ ≤ K ^ p * z := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hK _)
      simpa only [pow_one] using pow_le_pow_of_le_one hz hz1 hp

private theorem sgk_J_bound (T t y D : ℝ) (hT : 0 < T) (ht : 0 < t)
    (htT : t ≤ T) (hy : 0 ≤ y) (hD : 0 ≤ D) (hs : Real.sqrt y * D ≤ 1)
    (k : ℕ) (hk : k ≤ 3) :
    0 ≤ T ^ (-((k : ℝ) + 1) / 2) +
      Real.sqrt y * D * T ^ (-(2 * (k : ℝ) + 3) / 4) ∧
    T ^ (-((k : ℝ) + 1) / 2) +
      Real.sqrt y * D * T ^ (-(2 * (k : ℝ) + 3) / 4) ≤ 2 * (1 + (t⁻¹) ^ 3) := by

  have hrpow (r : ℝ) (hr0 : -3 ≤ r) (hr1 : r ≤ 0) :
      T ^ r ≤ 1 + (t⁻¹) ^ 3 := by
    by_cases hT1 : 1 ≤ T
    · have hh := Real.rpow_le_one_of_one_le_of_nonpos hT1 hr1
      have hn : 0 ≤ (t⁻¹) ^ 3 := by positivity
      linarith
    · have he := Real.rpow_le_rpow_of_exponent_ge hT (le_of_not_ge hT1) hr0
      have heq : T ^ (-3 : ℝ) = (T⁻¹) ^ 3 := by
        rw [Real.rpow_neg hT.le, Real.rpow_ofNat, inv_pow]
      rw [heq] at he
      have hi : T⁻¹ ≤ t⁻¹ := inv_anti₀ ht htT
      have he2 := pow_le_pow_left₀ (inv_pos.mpr hT).le hi 3
      linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hk3 : (k : ℝ) ≤ 3 := by exact_mod_cast hk
  have hb0 := hrpow (-((k : ℝ) + 1) / 2) (by linarith) (by linarith)
  have hb1 := hrpow (-(2 * (k : ℝ) + 3) / 4) (by linarith) (by linarith)
  refine ⟨by positivity, ?_⟩
  have he := mul_le_mul_of_nonneg_right hs
    (Real.rpow_nonneg hT.le (-(2 * (k : ℝ) + 3) / 4))
  nlinarith only [hb0, hb1, he]

private theorem sgk_displacements (g : ℝ → ℝ) (h A M : ℝ) (hh : 0 ≤ h)
    (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hd : ∀ t : ℝ, DifferentiableAt ℝ g t ∧ DifferentiableAt ℝ (deriv g) t)
    (hfirst : |deriv g 0| ≤ A)
    (hsecond : ∀ t : ℝ, |t| ≤ h → |deriv (deriv g) t| ≤ M) :
    (∀ w : ℝ, |w| ≤ h →
      |deriv (deriv g) w| ≤ M ∧
      |deriv g w - deriv g 0| ≤ M * |w| ∧
      |deriv g w| ≤ A + M * |w| ∧
      |g w - g 0 - w * deriv g 0| ≤ M / 2 * w ^ 2 ∧
      |g w - g 0| ≤ A * |w| + M / 2 * w ^ 2) ∧
    (∀ u : ℝ, 0 ≤ u → u ≤ h →
      |g 0 - g (-u)| ≤ A * u + M / 2 * u ^ 2) := by

  have hb (w : ℝ) (hw : |w| ≤ h) :
      |deriv (deriv g) w| ≤ M ∧
      |deriv g w - deriv g 0| ≤ M * |w| ∧
      |deriv g w| ≤ A + M * |w| ∧
      |g w - g 0 - w * deriv g 0| ≤ M / 2 * w ^ 2 ∧
      |g w - g 0| ≤ A * |w| + M / 2 * w ^ 2 := by
    obtain ⟨hdif, hrem⟩ := sgk_signed_remainder g h M hh hd hsecond w hw
    refine ⟨hsecond w hw, hdif, ?_, hrem, ?_⟩
    · calc
        |deriv g w| = |(deriv g w - deriv g 0) + deriv g 0| := by ring_nf
        _ ≤ |deriv g w - deriv g 0| + |deriv g 0| := abs_add_le _ _
        _ ≤ A + M * |w| := by linarith
    · calc
        |g w - g 0| = |(g w - g 0 - w * deriv g 0) + w * deriv g 0| := by ring_nf
        _ ≤ |g w - g 0 - w * deriv g 0| + |w * deriv g 0| := abs_add_le _ _
        _ ≤ M / 2 * w ^ 2 + |w| * A := by
          rw [abs_mul]
          exact add_le_add hrem (mul_le_mul_of_nonneg_left hfirst (abs_nonneg _))
        _ = _ := by ring1_nf (config := { zetaDelta := false })
  refine ⟨hb, ?_⟩
  intro u hu huh
  have hr := (hb (-u) (by simpa only [abs_neg, abs_of_nonneg hu] using huh)).2.2.2.2
  simpa only [abs_sub_comm (g 0), abs_neg, abs_of_nonneg hu, neg_sq] using hr

/- Scalar payment of the complete four-region table, with its actual powers. -/
private theorem sgk_table_payment
    (a G z Λ T l D U V P R1 R2 H K d u v p g b : ℝ)
    (ha : 1 ≤ a) (hG : 0 ≤ G) (hz : 0 ≤ z) (hzΛ : z ≤ Λ)
    (hΛ : Λ ≤ 1) (hT : 0 ≤ T) (hT1 : T ≤ 4 / 3)
    (hl : 0 ≤ l) (hlK : l ≤ K * a) (hD : 0 ≤ D) (hDd : D ≤ d * a ^ 2)
    (hU : 0 ≤ U) (hUu : U ≤ u * a)
    (hV : 0 ≤ V) (hVv : V ≤ v * a ^ 3)
    (hP : 0 ≤ P) (hPp : P ≤ p * a ^ 16)
    (hR1 : 0 ≤ R1) (hR1G : R1 ≤ 2 * G ^ 14)
    (hR2 : 0 ≤ R2) (hR2G : R2 ≤ 2 * G ^ 13)
    (hH : 0 ≤ H) (hHb : H ≤ b * a ^ 31)
    (hK : 0 ≤ K) (hd : 0 ≤ d) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hp : 0 ≤ p) (hg : 0 ≤ g) (hb : 0 ≤ b)
    (hGg : a ^ 3 * G ≤ g * z) (nm nt : ℝ)
    (hnm : 0 ≤ nm) (hnt : 0 ≤ nt) (hzdef : z = a ^ 3 * nt)
    (hΛdef : Λ = a * nm + a ^ 3 * nt) :
    T * (nm * U + nt * V) + G * D + P * R1 + H * G ^ 30 ≤
      ((4 / 3 : ℝ) * (u + v) + g * d + 2 * p * g ^ 14 + b * g ^ 30) * Λ ∧
    U + (G ^ 2 * D ^ 2 + l * G * D) + P * (R2 + l * R1) +
        H * (G ^ 29 + l * G ^ 30) ≤
      (u + g ^ 2 * d ^ 2 + K * g * d +
        2 * p * (g ^ 13 + K * g ^ 14) +
        b * (g ^ 29 + K * g ^ 30)) * a := by

  have ha0 : 0 ≤ a := (by norm_num : (0 : ℝ) ≤ 1).trans ha
  have hΛ0 : 0 ≤ Λ := hz.trans hzΛ
  have hz1 : z ≤ 1 := hzΛ.trans hΛ

  have mono (r s : ℕ) (hs : 1 ≤ s) (hrs : r ≤ 3 * s) :
      a ^ r * G ^ s ≤ g ^ s * Λ :=
    (sgk_monomial a G z g s r ha hG hz hz1 hg hGg hs hrs).trans
      (mul_le_mul_of_nonneg_left hzΛ (pow_nonneg hg _))

  have mono1 (r s : ℕ) (hs : 1 ≤ s) (hrs : r ≤ 3 * s) :
      a ^ r * G ^ s ≤ g ^ s :=
    (mono r s hs hrs).trans (by simpa using mul_le_mul_of_nonneg_left hΛ (pow_nonneg hg s))

  have h0 : T * (nm * U + nt * V) ≤ (4 / 3 : ℝ) * (u + v) * Λ := by
    have hnmΛ : a * nm ≤ Λ := by
      rw [hΛdef]; exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg ha0 _) hnt)
    have hntΛ : a ^ 3 * nt ≤ Λ := hzdef ▸ hzΛ
    calc
      _ ≤ (4 / 3 : ℝ) * (nm * (u * a) + nt * (v * a ^ 3)) := by gcongr
      _ = (4 / 3 : ℝ) * (u * (a * nm) + v * (a ^ 3 * nt)) := by ring1_nf (config := { zetaDelta := false })
      _ ≤ (4 / 3 : ℝ) * (u * Λ + v * Λ) := by gcongr
      _ = _ := by ring1_nf (config := { zetaDelta := false })

  have h1 : G * D ≤ g * d * Λ := by
    calc
      _ ≤ G * (d * a ^ 2) := mul_le_mul_of_nonneg_left hDd hG
      _ = d * (a ^ 2 * G ^ 1) := by ring1_nf (config := { zetaDelta := false })
      _ ≤ d * (g ^ 1 * Λ) := mul_le_mul_of_nonneg_left (mono 2 1 (by norm_num) (by norm_num)) hd
      _ = _ := by ring1_nf (config := { zetaDelta := false })

  have h2 : P * R1 ≤ 2 * p * g ^ 14 * Λ := by
    calc
      _ ≤ p * a ^ 16 * (2 * G ^ 14) := by gcongr
      _ = (2 * p) * (a ^ 16 * G ^ 14) := by ring1_nf (config := { zetaDelta := false })
      _ ≤ (2 * p) * (g ^ 14 * Λ) := mul_le_mul_of_nonneg_left (mono 16 14 (by norm_num) (by norm_num)) (by positivity)
      _ = _ := by ring1_nf (config := { zetaDelta := false })

  have h3 : H * G ^ 30 ≤ b * g ^ 30 * Λ := by
    calc
      _ ≤ b * a ^ 31 * G ^ 30 := by gcongr
      _ = b * (a ^ 31 * G ^ 30) := by ring1_nf (config := { zetaDelta := false })
      _ ≤ b * (g ^ 30 * Λ) := mul_le_mul_of_nonneg_left (mono 31 30 (by norm_num) (by norm_num)) hb
      _ = _ := by ring1_nf (config := { zetaDelta := false })
  refine ⟨?_, ?_⟩
  · convert add_le_add (add_le_add (add_le_add h0 h1) h2) h3 using 1 <;> ring1_nf (config := { zetaDelta := false })

  have h10 : G ^ 2 * D ^ 2 ≤ g ^ 2 * d ^ 2 := by
    calc
      _ ≤ G ^ 2 * (d * a ^ 2) ^ 2 := by gcongr
      _ = d ^ 2 * (a ^ 4 * G ^ 2) := by ring1_nf (config := { zetaDelta := false })
      _ ≤ d ^ 2 * g ^ 2 := mul_le_mul_of_nonneg_left (mono1 4 2 (by norm_num) (by norm_num)) (sq_nonneg d)
      _ = _ := by ring1_nf (config := { zetaDelta := false })

  have h11 : l * G * D ≤ K * g * d := by
    calc
      _ ≤ (K * a) * G * (d * a ^ 2) := by gcongr
      _ = K * d * (a ^ 3 * G ^ 1) := by ring1_nf (config := { zetaDelta := false })
      _ ≤ K * d * g ^ 1 := mul_le_mul_of_nonneg_left (mono1 3 1 (by norm_num) (by norm_num)) (mul_nonneg hK hd)
      _ = _ := by ring1_nf (config := { zetaDelta := false })

  have h20 : P * R2 ≤ 2 * p * g ^ 13 := by
    calc
      _ ≤ (p * a ^ 16) * (2 * G ^ 13) := by gcongr
      _ = 2 * p * (a ^ 16 * G ^ 13) := by ring1_nf (config := { zetaDelta := false })
      _ ≤ 2 * p * g ^ 13 := mul_le_mul_of_nonneg_left (mono1 16 13 (by norm_num) (by norm_num)) (by positivity)

  have h21 : P * (l * R1) ≤ 2 * p * K * g ^ 14 := by
    calc
      _ ≤ (p * a ^ 16) * ((K * a) * (2 * G ^ 14)) := by gcongr
      _ = 2 * p * K * (a ^ 17 * G ^ 14) := by ring1_nf (config := { zetaDelta := false })
      _ ≤ 2 * p * K * g ^ 14 := mul_le_mul_of_nonneg_left (mono1 17 14 (by norm_num) (by norm_num)) (by positivity)

  have h30 : H * G ^ 29 ≤ b * g ^ 29 := by
    calc
      _ ≤ b * a ^ 31 * G ^ 29 := by gcongr
      _ = b * (a ^ 31 * G ^ 29) := by ring1_nf (config := { zetaDelta := false })
      _ ≤ b * g ^ 29 := mul_le_mul_of_nonneg_left (mono1 31 29 (by norm_num) (by norm_num)) hb

  have h31 : H * (l * G ^ 30) ≤ b * K * g ^ 30 := by
    calc
      _ ≤ b * a ^ 31 * (K * a * G ^ 30) := by gcongr
      _ = b * K * (a ^ 32 * G ^ 30) := by ring1_nf (config := { zetaDelta := false })
      _ ≤ b * K * g ^ 30 := mul_le_mul_of_nonneg_left (mono1 32 30 (by norm_num) (by norm_num)) (by positivity)

  have hc : 0 ≤ g ^ 2 * d ^ 2 + K * g * d +
      2 * p * (g ^ 13 + K * g ^ 14) + b * (g ^ 29 + K * g ^ 30) := by positivity
  have hca := mul_le_mul_of_nonneg_left ha hc
  have hsum := add_le_add (add_le_add (add_le_add hUu (add_le_add h10 h11))
    (add_le_add h20 h21)) (add_le_add h30 h31)
  calc
    _ ≤ u * a + (g ^ 2 * d ^ 2 + K * g * d) +
        (2 * p * g ^ 13 + 2 * p * K * g ^ 14) +
        (b * g ^ 29 + b * K * g ^ 30) := by convert hsum using 1 <;> ring1_nf (config := { zetaDelta := false })
    _ = u * a + (g ^ 2 * d ^ 2 + K * g * d +
        2 * p * (g ^ 13 + K * g ^ 14) + b * (g ^ 29 + K * g ^ 30)) := by ring1_nf (config := { zetaDelta := false })
    _ ≤ u * a + (g ^ 2 * d ^ 2 + K * g * d +
        2 * p * (g ^ 13 + K * g ^ 14) + b * (g ^ 29 + K * g ^ 30)) * a :=
      by simpa only [mul_one, add_comm] using add_le_add_left hca (u * a)
    _ = _ := by ring1_nf (config := { zetaDelta := false })

private theorem sgk_tail (G r D : ℝ) (hG : 0 < G) (hG1 : G ≤ 1)
    (hr : 0 ≤ r) (hD : 0 ≤ D) (hrD : r * D ≤ 1) (p : ℕ) (hp : 1 ≤ p) :
    0 ≤ G ^ p + r * D * G ^ p / Real.sqrt G ∧
      G ^ p + r * D * G ^ p / Real.sqrt G ≤ 2 * G ^ (p - 1) := by

  have hs : G / Real.sqrt G = Real.sqrt G := by
    apply (div_eq_iff (Real.sqrt_pos.mpr hG).ne').mpr
    nlinarith only [Real.sq_sqrt hG.le]
  have hs1 : Real.sqrt G ≤ 1 := Real.sqrt_le_iff.mpr ⟨by norm_num, by simpa using hG1⟩
  have hpow : G ^ p ≤ G ^ (p - 1) := by
    conv_lhs => rw [show p = (p - 1) + 1 by omega, pow_succ]
    exact mul_le_of_le_one_right (by positivity) hG1
  have hdiv : G ^ p / Real.sqrt G ≤ G ^ (p - 1) := by
    calc
      _ = G ^ (p - 1) * (G / Real.sqrt G) := by
        conv_lhs => rw [show p = (p - 1) + 1 by omega, pow_succ]
        ring1_nf (config := { zetaDelta := false })
      _ = G ^ (p - 1) * Real.sqrt G := by rw [hs]
      _ ≤ G ^ (p - 1) := mul_le_of_le_one_right (by positivity) hs1
  have hterm : r * D * G ^ p / Real.sqrt G ≤ G ^ (p - 1) := by
    rw [mul_div_assoc]
    exact (mul_le_mul hrD hdiv (by positivity) (by norm_num)).trans_eq (one_mul _)
  exact ⟨by positivity, by linarith⟩

private theorem sgk_macro_polynomials
    (t e y T l h N G : ℝ) (ht : 0 < t) (he : 0 < e)
    (hy : 2 ≤ y) (hT : t ≤ T) (hN : 0 < N) (hN7 : N ≤ 7)
    (hl : 0 ≤ l) (hlN : y / Real.sqrt N ≤ l)
    (hlK : l ≤ (3 / t) * (1 + y)) (hh : h = e / (1 + y))
    (hs : l * y / Real.sqrt N = y ^ 2 / T) (hG : 0 < G) (hG1 : G ≤ 1) :
    let a : ℝ := 1 + y
    let K : ℝ := 3 / t
    let d : ℝ := 1 + K
    let Dm : ℝ := 2 * (1 + (t⁻¹) ^ 3)
    let u : ℝ := Dm * (1 + K)
    let v : ℝ := Dm * (1 + K) ^ 3 + (t⁻¹ + d) * u + u
    let p : ℝ := (t⁻¹ + K ^ 2) ^ 8
    let b : ℝ := (e * d) ^ 31
    let D : ℝ := (1 + l * y)⁻¹
    let J : ℕ → ℝ := fun k => T ^ (-((k : ℝ) + 1) / 2) +
      Real.sqrt y * D * T ^ (-(2 * (k : ℝ) + 3) / 4)
    let U : ℝ := J 1 + l * J 0
    let V : ℝ := J 3 + 3 * l * J 2 + 3 * l ^ 2 * J 1 + l ^ 3 * J 0 +
      (l * y / Real.sqrt N + D⁻¹) * U + y * (J 2 + l * J 1)
    0 < D ∧ D⁻¹ ≤ d * a ^ 2 ∧ 0 ≤ U ∧ U ≤ u * a ∧
      0 ≤ V ∧ V ≤ v * a ^ 3 ∧
      (T⁻¹ + l ^ 2) ^ 8 ≤ p * a ^ 16 ∧
      (h * D⁻¹) ^ 31 ≤ b * a ^ 31 ∧
      (0 ≤ G ^ 15 + Real.sqrt y * D * G ^ 15 / Real.sqrt G ∧
        G ^ 15 + Real.sqrt y * D * G ^ 15 / Real.sqrt G ≤ 2 * G ^ 14) ∧
      (0 ≤ G ^ 14 + Real.sqrt y * D * G ^ 14 / Real.sqrt G ∧
        G ^ 14 + Real.sqrt y * D * G ^ 14 / Real.sqrt G ≤ 2 * G ^ 13) := by

  intro a K d Dm u v p b D J U V
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have ha0 : 0 < a := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hT0 : 0 < T := ht.trans_le hT
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hDm : 0 ≤ Dm := by dsimp [Dm]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hDi : D⁻¹ = 1 + l * y := by dsimp [D]; rw [inv_inv]
  have hy_a : y ≤ a := by dsimp [a]; linarith
  have hsn : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hsn3 : Real.sqrt N ≤ 3 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h3l : y ≤ 3 * l := by
    have hv := (div_le_iff₀ hsn).mp hlN
    have hm := mul_le_mul_of_nonneg_left hsn3 hl
    nlinarith only [hv, hm]
  have hys : Real.sqrt y ≤ y := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨hy0, by nlinarith only [hy]⟩
  have hcoeff : Real.sqrt y * D ≤ 1 := by
    dsimp [D]
    apply (mul_inv_le_iff₀ (show 0 < 1 + l * y by positivity)).mpr
    have hv := mul_le_mul_of_nonneg_right h3l hy0
    nlinarith only [hys, hv, sq_nonneg (y - 3 / 2)]
  have hDib : D⁻¹ ≤ d * a ^ 2 := by
    rw [hDi]
    have hla : l * y ≤ K * a * a := mul_le_mul hlK hy_a hy0 (by positivity)
    have ha2 : 1 ≤ a ^ 2 := one_le_pow₀ ha
    dsimp [d]
    nlinarith only [hla, ha2]
  have hJ (k : ℕ) (hk : k ≤ 3) : 0 ≤ J k ∧ J k ≤ Dm :=
    sgk_J_bound T t y D hT0 ht hT hy0 hD.le hcoeff k hk
  have hU0 : 0 ≤ U := by dsimp [U]; exact add_nonneg (hJ 1 (by norm_num)).1 (mul_nonneg hl (hJ 0 (by norm_num)).1)
  have hUb : U ≤ u * a := by
    calc
      _ ≤ Dm + K * a * Dm := by dsimp [U]; gcongr; exact (hJ 1 (by norm_num)).2; exact (hJ 0 (by norm_num)).2
      _ ≤ Dm * (1 + K) * a := by nlinarith only [mul_nonneg hDm (sub_nonneg.mpr ha)]
      _ = _ := rfl
  have hJsmall : J 2 + l * J 1 ≤ u * a := by
    calc
      _ ≤ Dm + K * a * Dm := by gcongr; exact (hJ 2 (by norm_num)).2; exact (hJ 1 (by norm_num)).2
      _ ≤ Dm * (1 + K) * a := by nlinarith only [mul_nonneg hDm (sub_nonneg.mpr ha)]
      _ = _ := rfl
  have hbase : J 3 + 3 * l * J 2 + 3 * l ^ 2 * J 1 + l ^ 3 * J 0 ≤
      Dm * (1 + K) ^ 3 * a ^ 3 := by
    calc
      _ ≤ Dm + 3 * (K * a) * Dm + 3 * (K * a) ^ 2 * Dm + (K * a) ^ 3 * Dm := by
        gcongr
        exact (hJ 3 (by norm_num)).2
        exact (hJ 2 (by norm_num)).2
        exact (hJ 1 (by norm_num)).2
        exact (hJ 0 (by norm_num)).2
      _ = Dm * (1 + K * a) ^ 3 := by ring1_nf (config := { zetaDelta := false })
      _ ≤ Dm * ((1 + K) * a) ^ 3 := by
        gcongr
        nlinarith only [ha]
      _ = _ := by ring1_nf (config := { zetaDelta := false })
  have hsi : l * y / Real.sqrt N ≤ t⁻¹ * a ^ 2 := by
    rw [hs, div_eq_mul_inv]
    have hi := inv_anti₀ ht hT
    calc
      y ^ 2 * T⁻¹ ≤ a ^ 2 * t⁻¹ :=
        mul_le_mul (pow_le_pow_left₀ hy0 hy_a 2) hi (inv_nonneg.mpr hT0.le) (sq_nonneg a)
      _ = _ := by ring1_nf (config := { zetaDelta := false })
  have hmid : (l * y / Real.sqrt N + D⁻¹) * U ≤ (t⁻¹ + d) * u * a ^ 3 := by
    calc
      _ ≤ (t⁻¹ * a ^ 2 + d * a ^ 2) * (u * a) := by gcongr
      _ = _ := by ring1_nf (config := { zetaDelta := false })
  have hlast : y * (J 2 + l * J 1) ≤ u * a ^ 3 := by
    have he : y * (J 2 + l * J 1) ≤ a * (u * a) := by gcongr
    have ha23 : a ^ 2 ≤ a ^ 3 := pow_le_pow_right₀ ha (by norm_num)
    calc
      _ ≤ u * a ^ 2 := by nlinarith only [he]
      _ ≤ u * a ^ 3 := mul_le_mul_of_nonneg_left ha23 hu
  have hV0 : 0 ≤ V := by dsimp [V]; positivity
  have hVb : V ≤ v * a ^ 3 := by dsimp only [V, v]; linarith only [hbase, hmid, hlast]
  have hP : (T⁻¹ + l ^ 2) ^ 8 ≤ p * a ^ 16 := by
    have hi : T⁻¹ ≤ t⁻¹ := inv_anti₀ ht hT
    have hia : t⁻¹ ≤ t⁻¹ * a ^ 2 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ ha)
    have hiT : T⁻¹ ≤ t⁻¹ * a ^ 2 := hi.trans hia
    calc
      _ ≤ (t⁻¹ * a ^ 2 + (K * a) ^ 2) ^ 8 := by gcongr
      _ = p * a ^ 16 := by
        rw [show t⁻¹ * a ^ 2 + (K * a) ^ 2 = (t⁻¹ + K ^ 2) * a ^ 2 by
          ring1_nf (config := { zetaDelta := false }), mul_pow, ← pow_mul]
  have hH : (h * D⁻¹) ^ 31 ≤ b * a ^ 31 := by
    have hh0 : 0 < h := by rw [hh]; positivity
    have heq : h * (d * a ^ 2) = e * d * a := by rw [hh]; dsimp [a]; field_simp <;> ring1_nf (config := { zetaDelta := false })
    calc
      _ ≤ (h * (d * a ^ 2)) ^ 31 := by gcongr
      _ = b * a ^ 31 := by rw [heq, mul_pow]
  exact ⟨hD, hDib, hU0, hUb, hV0, hVb, hP, hH,
    sgk_tail G (Real.sqrt y) D hG hG1 (Real.sqrt_nonneg _) hD.le hcoeff 15 (by norm_num),
    sgk_tail G (Real.sqrt y) D hG hG1 (Real.sqrt_nonneg _) hD.le hcoeff 14 (by norm_num)⟩

/- The short schedule retains the literal 512 envelope and Mills normalization. -/
private theorem sgk_short_normalization (e L y T l h E : ℝ)
    (he : 0 < e) (hL : 1600 ≤ L) (hy : 2 ≤ y) (hT : 0 < T)
    (hTe : T ≤ Real.exp (-1)) (hell : 1 ≤ Real.log (1 / T))
    (hh : h = e / (1 + y))
    (hl : l = ((1 / 1024 : ℝ) / h) * Real.log (1 / T))
    (hE0 : 0 ≤ E)
    (hE : E ≤ Real.exp (512 * l * h) *
      Real.exp (-L * y * (1 + y) * Real.log (1 / T))) :
    (1 + y + l + T⁻¹) ^ 128 * E ≤
      ((2 + (1 / 1024 : ℝ) / e) ^ 128 * Real.sqrt (2 * Real.pi)) *
        Shao.standardNormalTail y * T ^ 2 := by

  let a : ℝ := 1 + y
  let c : ℝ := (1 / 1024 : ℝ) / e
  let ell : ℝ := Real.log (1 / T)
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have ha0 : 0 < a := by linarith
  have hc : 0 < c := by dsimp [c]; positivity
  have hell0 : 0 ≤ ell := by dsimp [ell]; linarith
  have hlval : l = c * a * ell := by rw [hl, hh]; dsimp [c, a, ell]; field_simp <;> ring1_nf (config := { zetaDelta := false })
  have hlh : l * h = (1 / 1024 : ℝ) * ell := by rw [hl, hh]; dsimp [ell]; field_simp <;> ring1_nf (config := { zetaDelta := false })
  have hexp : T⁻¹ = Real.exp ell := by
    dsimp [ell]
    simpa only [one_div] using (Real.exp_log (by positivity : 0 < 1 / T)).symm
  have hellExp : ell ≤ Real.exp ell := by linarith [Real.add_one_le_exp ell]
  have honeExp : 1 ≤ Real.exp ell := Real.one_le_exp_iff.mpr hell0
  have hB0 : 0 ≤ 1 + y + l + T⁻¹ := by rw [hlval]; positivity
  have hB : 1 + y + l + T⁻¹ ≤ (2 + c) * a * Real.exp ell := by
    rw [hlval, hexp]

    have h0 := mul_le_mul_of_nonneg_left honeExp ha0.le

    have h1 := mul_le_mul_of_nonneg_left hellExp (show 0 ≤ c * a by positivity)

    have h2 := mul_le_mul_of_nonneg_right ha (Real.exp_pos ell).le
    dsimp [a] at h0 h1 h2 ⊢
    nlinarith only [h0, h1, h2]
  have hE' : E ≤ Real.exp ((1 / 2 : ℝ) * ell) *
      Real.exp (-L * y * a * ell) := by
    have heq : 512 * l * h = (1 / 2 : ℝ) * ell := by nlinarith only [hlh]
    change E ≤ Real.exp ((1 / 2 : ℝ) * ell) *
      Real.exp (-L * y * (1 + y) * Real.log (1 / T))
    rwa [heq] at hE
  have h128 : (Real.exp ell) ^ 128 = Real.exp ((128 : ℝ) * ell) :=
    (Real.exp_nat_mul ell 128).symm
  have hcoef : (128 : ℝ) * ell + (1 / 2 : ℝ) * ell ≤ 512 * ell := by linarith
  have hpay := (sourceGrowingTilt_log_polynomial_payment L y T hL hy hT hTe).2
  change a ^ 128 * Real.exp (512 * ell) * Real.exp (-L * y * a * ell) ≤ _ at hpay
  calc
    _ ≤ ((2 + c) * a * Real.exp ell) ^ 128 *
        (Real.exp ((1 / 2 : ℝ) * ell) * Real.exp (-L * y * a * ell)) :=
      mul_le_mul (pow_le_pow_left₀ hB0 hB _) hE' hE0 (by positivity)
    _ = (2 + c) ^ 128 * (a ^ 128 *
        Real.exp ((128 : ℝ) * ell + (1 / 2 : ℝ) * ell) *
        Real.exp (-L * y * a * ell)) := by
      rw [mul_pow, mul_pow, h128, Real.exp_add]
      ac_rfl
    _ ≤ (2 + c) ^ 128 * (a ^ 128 * Real.exp (512 * ell) *
        Real.exp (-L * y * a * ell)) := by gcongr
    _ ≤ (2 + c) ^ 128 * (Real.sqrt (2 * Real.pi) * Shao.standardNormalTail y * T ^ 2) :=
      mul_le_mul_of_nonneg_left hpay (by positivity)
    _ = _ := by dsimp only [c]; ac_rfl

private theorem sgk_macro_exponent
    (e t y T N l h mu m3 : ℝ) (n m : ℕ)
    (he : 0 < e) (ht : 0 < t) (hy : 2 ≤ y)
    (hl : 0 ≤ l) (hm : m ≤ n) (hm3 : 0 ≤ m3)
    (hΛ : (1 + y) * (n : ℝ) * |mu| + (1 + y) ^ 3 * (n : ℝ) * m3 ≤ 1)
    (hlK : l ≤ (3 / t) * (1 + y)) (hlh : l * h ≤ (3 / t) * e)
    (hlh0 : 0 ≤ l * h)
    (hid : -l * y * Real.sqrt N + T * l ^ 2 / 2 = -(y ^ 2 * N / (2 * T))) :
    Real.exp (-l * y * Real.sqrt N + T * l ^ 2 / 2 +
      (m : ℝ) * l * |mu| +
      24 * (m : ℝ) * l ^ 3 * m3 * Real.exp (l * h) + 200 * l * h) ≤
      Real.exp ((3 / t) +
        512 * (3 / t) ^ 3 * Real.exp (512 * (3 / t) * e) +
        512 * (3 / t) * e) * Real.exp (-(y ^ 2 * N / (2 * T))) := by

  let a : ℝ := 1 + y
  let K : ℝ := 3 / t
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hmn : (m : ℝ) ≤ n := by exact_mod_cast hm
  have hmean : a * (n : ℝ) * |mu| ≤ 1 := by
    have hn : 0 ≤ a ^ 3 * (n : ℝ) * m3 := by positivity
    dsimp [a] at hn ⊢
    linarith
  have hthird : a ^ 3 * (n : ℝ) * m3 ≤ 1 := by
    have hn : 0 ≤ a * (n : ℝ) * |mu| := by positivity
    dsimp [a] at hn ⊢
    linarith
  have hM : (m : ℝ) * l * |mu| ≤ K := by
    calc
      _ ≤ (n : ℝ) * (K * a) * |mu| := by gcongr
      _ = K * (a * (n : ℝ) * |mu|) := by ring1_nf (config := { zetaDelta := false })
      _ ≤ K := mul_le_of_le_one_right hK hmean
  have hE : Real.exp (l * h) ≤ Real.exp (512 * K * e) := by
    apply Real.exp_le_exp.mpr
    change l * h ≤ 512 * K * e
    have hKe : 0 ≤ K * e := by positivity
    dsimp [K] at *
    linarith

  have h3 : 24 * (m : ℝ) * l ^ 3 * m3 * Real.exp (l * h) ≤
      512 * K ^ 3 * Real.exp (512 * K * e) := by
    calc
      _ ≤ 512 * (n : ℝ) * (K * a) ^ 3 * m3 * Real.exp (512 * K * e) := by gcongr <;> norm_num
      _ = (512 * K ^ 3 * Real.exp (512 * K * e)) * (a ^ 3 * (n : ℝ) * m3) := by ring1_nf (config := { zetaDelta := false })
      _ ≤ _ := mul_le_of_le_one_right (by positivity) hthird
  have hlin : 200 * l * h ≤ 512 * K * e := by
    have hKe : 0 ≤ K * e := by positivity
    dsimp [K] at *
    nlinarith only [hlh, hlh0, hKe]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [hid]
  dsimp [K] at *
  linarith only [hM, h3, hlin]

private theorem sgk_macro_sums
    (e t y T l h N gamma mu m3 : ℝ) (n : ℕ)
    (he : 0 < e) (ht : 0 < t) (hy : 2 ≤ y) (hT : t ≤ T) (hThi : T ≤ 4 / 3)
    (hN : 0 < N) (hN7 : N ≤ 7) (hl : 0 ≤ l) (hlN : y / Real.sqrt N ≤ l)
    (hlK : l ≤ (3 / t) * (1 + y)) (hlh : l * h ≤ (3 / t) * e)
    (hh : h = e / (1 + y)) (hs : l * y / Real.sqrt N = y ^ 2 / T)
    (hg : 0 < gamma) (hm3 : 0 ≤ m3) (hgn : gamma ≤ 2 * (n : ℝ) * m3)
    (hΛ : (1 + y) * (n : ℝ) * |mu| + (1 + y) ^ 3 * (n : ℝ) * m3 ≤ 1)
    (hsmall : (y + l) * (8 * Real.exp (8 * l * h) * gamma) ≤ 1 / 2048) :
    let a : ℝ := 1 + y
    let K : ℝ := 3 / t
    let d : ℝ := 1 + K
    let Dm : ℝ := 2 * (1 + (t⁻¹) ^ 3)
    let u : ℝ := Dm * (1 + K)
    let v : ℝ := Dm * (1 + K) ^ 3 + (t⁻¹ + d) * u + u
    let p : ℝ := (t⁻¹ + K ^ 2) ^ 8
    let g : ℝ := 16 * Real.exp (8 * K * e)
    let b : ℝ := (e * d) ^ 31
    let QA : ℝ := (4 / 3 : ℝ) * (u + v) + g * d + 2 * p * g ^ 14 + b * g ^ 30
    let QB : ℝ := u + g ^ 2 * d ^ 2 + K * g * d +
      2 * p * (g ^ 13 + K * g ^ 14) + b * (g ^ 29 + K * g ^ 30)
    let G : ℝ := 8 * Real.exp (8 * l * h) * gamma
    let D : ℝ := (1 + l * y)⁻¹
    let J : ℕ → ℝ := fun k => T ^ (-((k : ℝ) + 1) / 2) +
      Real.sqrt y * D * T ^ (-(2 * (k : ℝ) + 3) / 4)
    let U : ℝ := J 1 + l * J 0
    let V : ℝ := J 3 + 3 * l * J 2 + 3 * l ^ 2 * J 1 + l ^ 3 * J 0 +
      (l * y / Real.sqrt N + D⁻¹) * U + y * (J 2 + l * J 1)
    let P : ℝ := (T⁻¹ + l ^ 2) ^ 8
    let R1 : ℝ := G ^ 15 + Real.sqrt y * D * G ^ 15 / Real.sqrt G
    let R2 : ℝ := G ^ 14 + Real.sqrt y * D * G ^ 14 / Real.sqrt G
    let Λ : ℝ := a * (n : ℝ) * |mu| + a ^ 3 * (n : ℝ) * m3
    T * ((n : ℝ) * |mu| * U + (n : ℝ) * m3 * V) + G * D⁻¹ + P * R1 +
        (h * D⁻¹) ^ 31 * G ^ 30 ≤ QA * Λ ∧
      U + (G ^ 2 * D⁻¹ ^ 2 + l * G * D⁻¹) + P * (R2 + l * R1) +
        (h * D⁻¹) ^ 31 * (G ^ 29 + l * G ^ 30) ≤ QB * a := by

  intro a K d Dm u v p g b QA QB G D J U V P R1 R2 Λ
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have ha0 : 0 ≤ a := (by norm_num : (0 : ℝ) ≤ 1).trans ha
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hDm : 0 ≤ Dm := by dsimp [Dm]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hgp : 0 ≤ g := by dsimp [g]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  have hG1 : G ≤ 1 := by
    have he1 := mul_le_mul_of_nonneg_right (show 2 ≤ y + l by linarith) hG.le
    change (y + l) * G ≤ 1 / 2048 at hsmall
    linarith
  obtain ⟨hD, hDi, hU, hUb, hV, hVb, hP, hH, hR1, hR2⟩ :=
    sgk_macro_polynomials t e y T l h N G ht he hy hT hN hN7 hl hlN hlK hh hs hG hG1
  change 0 < D at hD
  change D⁻¹ ≤ d * a ^ 2 at hDi
  change 0 ≤ U at hU
  change U ≤ u * a at hUb
  change 0 ≤ V at hV
  change V ≤ v * a ^ 3 at hVb
  change P ≤ p * a ^ 16 at hP
  change (h * D⁻¹) ^ 31 ≤ b * a ^ 31 at hH
  change 0 ≤ R1 ∧ R1 ≤ 2 * G ^ 14 at hR1
  change 0 ≤ R2 ∧ R2 ≤ 2 * G ^ 13 at hR2
  let z : ℝ := a ^ 3 * ((n : ℝ) * m3)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hzΛ : z ≤ Λ := by
    dsimp [z, Λ]
    nlinarith only [mul_nonneg (mul_nonneg ha0 (Nat.cast_nonneg n)) (abs_nonneg mu)]
  have hGg : a ^ 3 * G ≤ g * z := by
    have hexp : Real.exp (8 * l * h) ≤ Real.exp (8 * K * e) := by
      apply Real.exp_le_exp.mpr
      change l * h ≤ (3 / t) * e at hlh
      dsimp [K]
      linarith only [hlh]
    have hgb : G ≤ g * ((n : ℝ) * m3) := by
      calc
        G ≤ 8 * Real.exp (8 * K * e) * (2 * (n : ℝ) * m3) := by dsimp [G]; gcongr
        _ = g * ((n : ℝ) * m3) := by dsimp [g]; ring1_nf (config := { zetaDelta := false })
    calc
      _ ≤ a ^ 3 * (g * ((n : ℝ) * m3)) := mul_le_mul_of_nonneg_left hgb (pow_nonneg ha0 _)
      _ = g * z := by dsimp [z]; ring1_nf (config := { zetaDelta := false })
  have hh0 : 0 ≤ h := by rw [hh]; positivity
  exact sgk_table_payment a G z Λ T l D⁻¹ U V P R1 R2 ((h * D⁻¹) ^ 31)
    K d u v p g b ha hG.le hz hzΛ hΛ (ht.trans_le hT).le hThi hl hlK
    (inv_pos.mpr hD).le hDi hU hUb hV hVb (by dsimp [P]; positivity) hP
    hR1.1 hR1.2 hR2.1 hR2.2 (by positivity) hH hK hd hu hv hp hgp hb hGg
    ((n : ℝ) * |mu|) ((n : ℝ) * m3) (by positivity) (by positivity) rfl (by dsimp [Λ]; ring1_nf (config := { zetaDelta := false }))

private theorem sgk_local_package
    (g : ℝ → ℝ) (h C Λ b E : ℝ) (hh : 0 ≤ h)
    (hC : 0 ≤ C) (hΛ : 0 ≤ Λ) (hb : 0 ≤ b) (hE : 0 ≤ E)
    (hd : ∀ t : ℝ, DifferentiableAt ℝ g t ∧ DifferentiableAt ℝ (deriv g) t)
    (hfirst : |deriv g 0| ≤ C * Λ * E)
    (hsecond : ∀ w : ℝ, |w| ≤ h → |deriv (deriv g) w| ≤ C * b * E) :
    (∀ w : ℝ, |w| ≤ h →
      |deriv (deriv g) w| ≤ C * b * E ∧
      |deriv g w - deriv g 0| ≤ C * b * E * |w| ∧
      |deriv g w| ≤ C * E * (Λ + b * |w|) ∧
      |g w - g 0 - w * deriv g 0| ≤ C * b * E / 2 * w ^ 2 ∧
      |g w - g 0| ≤ C * E * (Λ * |w| + b * w ^ 2 / 2)) ∧
    (∀ u : ℝ, 0 ≤ u → u ≤ h →
      |g 0 - g (-u)| ≤ C * E * (Λ * u + b * u ^ 2 / 2)) := by

  obtain ⟨hr, hu⟩ := sgk_displacements g h (C * Λ * E) (C * b * E) hh
    (by positivity) (by positivity) hd hfirst hsecond
  constructor
  · intro w hw
    obtain ⟨h2, hdif, h1, hrem, hshift⟩ := hr w hw
    refine ⟨h2, hdif, ?_, hrem, ?_⟩
    · convert h1 using 1 <;> ring1_nf (config := { zetaDelta := false })
    · convert hshift using 1 <;> ring1_nf (config := { zetaDelta := false })
  · intro u hu0 huh
    convert hu u hu0 huh using 1 <;> ring1_nf (config := { zetaDelta := false })

set_option maxHeartbeats 8000000 in
theorem sourceTruncation_growing_kernel_derivative_local_shift_bounds :
    let L : ℝ := 1600
    let L2 : ℝ := 16384
    let alpha : ℝ := 1 / 1024
    let epsilon0 : ℝ := min (1 / (64 * Real.sqrt L2)) (alpha / (8 * L))
    let t0 : ℝ := Real.exp (-(48 * alpha / epsilon0))
    let eta0 : ℝ := min (1 / 16)
      (min (Real.sqrt t0 / (2 * Real.sqrt L2))
        (min ((epsilon0 / 20480) ^ 2)
          (1 / (16384 * (1 + 3 / t0) *
            Real.exp (24 * epsilon0 / t0)))))
    let epsilon : ℝ := min (epsilon0 / 2)
      (1 / (4 * (8 * (1 + L) + 1) * L))
    0 < epsilon0 ∧ 0 < epsilon ∧ epsilon ≤ epsilon0 / 2 ∧
      0 < t0 ∧ t0 < (3 / 8 : ℝ) ∧
      epsilon0 ≤ 1 / (192 * Real.sqrt (L2 + 1)) ∧
      (1 / 128 : ℝ) * Real.sqrt L2 = 1 ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ (nu0 : Measure ℝ), IsProbabilityMeasure nu0 →
          ∀ n : ℕ, Integrable (fun a : ℝ => a ^ 2) nu0 →
            (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂nu0) = 1 →
            (∫ a : ℝ, a ∂nu0) = 0 →
            ∀ x : ℝ, 0 ≤ x →
              Shao.truncationBudget nu0 n x ≤ epsilon ^ 3 / 8 →
              Shao.truncationBudget nu0 n x ≤ epsilon ^ 2 * eta0 / 40 →
              ∀ y : ℝ, 2 ≤ y →
                |y - x| ≤ 1 / (2 * (1 + x)) →
                let rho : Measure ℝ := ProbabilityTheory.cond nu0
                  {a : ℝ | |a| ≤ epsilon / (1 + x)}
                let h : ℝ := epsilon0 / (1 + y)
                let mu : ℝ := ∫ a : ℝ, a ∂rho
                let raw2 : ℝ := ∫ a : ℝ, a ^ 2 ∂rho
                let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂rho
                let V : ℝ := variance (id : ℝ → ℝ) rho
                let gamma : ℝ := m3 / V
                let Lambda : ℝ := (1 + y) * (n : ℝ) * |mu| +
                  (1 + y) ^ 3 * (n : ℝ) * m3
                let T : ℕ → ℝ := fun i => ((n - i : ℕ) : ℝ) * raw2
                let f : ℕ → ℝ → ℝ → ℝ := fun i q w =>
                  sourceFutureNoiseKernel rho (n - i) y (w, q)
                0 < gamma ∧ 0 < raw2 ∧ 0 ≤ Lambda ∧
                  ∀ i : ℕ, i ≤ n →
                    (T i = 0 ↔ n - i = 0) ∧
                    (∀ q w : ℝ,
                      DifferentiableAt ℝ (f i q) w ∧
                        DifferentiableAt ℝ (fun r : ℝ => deriv (f i q) r) w) ∧
                    (∀ q : ℝ, 5 < q → ∀ w : ℝ,
                      f i q w = 0 ∧ deriv (f i q) w = 0 ∧
                        deriv (fun r : ℝ => deriv (f i q) r) w = 0) ∧
                    (n - i = 0 →
                      (∀ q w : ℝ, |w| ≤ 2 * h → f i q w = f i q 0) ∧
                        (∀ q w : ℝ, |w| ≤ h →
                          deriv (f i q) w = 0 ∧
                            deriv (fun r : ℝ => deriv (f i q) r) w = 0)) ∧
                    (∀ q : ℝ, 0 ≤ q →
                      (i ≤ n / 2 ∨
                        (n / 2 < i ∧ t0 ≤ T i ∧ (1 / 16 : ℝ) ≤ q)) →
                      0 < T i ∧
                        |deriv (f i q) 0| ≤ C * Lambda *
                          Real.exp (-(y ^ 2 * (q + T i) / (2 * T i))) ∧
                        (∀ w : ℝ, |w| ≤ h →
                          |deriv (fun r : ℝ => deriv (f i q) r) w| ≤
                            C * (1 + y) *
                              Real.exp (-(y ^ 2 * (q + T i) / (2 * T i))) ∧
                          |deriv (f i q) w - deriv (f i q) 0| ≤
                            C * (1 + y) *
                              Real.exp (-(y ^ 2 * (q + T i) / (2 * T i))) * |w| ∧
                          |deriv (f i q) w| ≤
                            C * Real.exp (-(y ^ 2 * (q + T i) / (2 * T i))) *
                              (Lambda + (1 + y) * |w|) ∧
                          |f i q w - f i q 0 - w * deriv (f i q) 0| ≤
                            C * (1 + y) *
                              Real.exp (-(y ^ 2 * (q + T i) / (2 * T i))) / 2 * w ^ 2 ∧
                          |f i q w - f i q 0| ≤
                            C * Real.exp (-(y ^ 2 * (q + T i) / (2 * T i))) *
                              (Lambda * |w| + (1 + y) * w ^ 2 / 2)) ∧
                        (∀ u : ℝ, 0 ≤ u → u ≤ h →
                          |f i q 0 - f i q (-u)| ≤
                            C * Real.exp (-(y ^ 2 * (q + T i) / (2 * T i))) *
                              (Lambda * u + (1 + y) * u ^ 2 / 2))) ∧
                    (n / 2 < i → L2 * gamma ^ 2 ≤ T i → T i < t0 →
                      0 < T i ∧
                        ∀ q : ℝ, (1 / 16 : ℝ) ≤ q →
                          |deriv (f i q) 0| ≤
                            C * Lambda * Shao.standardNormalTail y * (T i) ^ 2 ∧
                          (∀ w : ℝ, |w| ≤ h →
                            |deriv (fun r : ℝ => deriv (f i q) r) w| ≤
                              C * Shao.standardNormalTail y * (T i) ^ 2 ∧
                            |deriv (f i q) w - deriv (f i q) 0| ≤
                              C * Shao.standardNormalTail y * (T i) ^ 2 * |w| ∧
                            |deriv (f i q) w| ≤
                              C * Shao.standardNormalTail y * (T i) ^ 2 *
                                (Lambda + |w|) ∧
                            |f i q w - f i q 0 - w * deriv (f i q) 0| ≤
                              C * Shao.standardNormalTail y * (T i) ^ 2 / 2 * w ^ 2 ∧
                            |f i q w - f i q 0| ≤
                              C * Shao.standardNormalTail y * (T i) ^ 2 *
                                (Lambda * |w| + w ^ 2 / 2)) ∧
                          (∀ u : ℝ, 0 ≤ u → u ≤ h →
                            |f i q 0 - f i q (-u)| ≤
                              C * Shao.standardNormalTail y * (T i) ^ 2 *
                                (Lambda * u + u ^ 2 / 2))) := by
  intro L L2 alpha epsilon0 t0 eta0 epsilon
  obtain ⟨he0, he064, heClock, heTilt, ht0, htThree, htExp, htLog,
    heta, heta16, hetaClock, hetaShort, hetaMacro⟩ :=
    sourceGrowingTilt_explicit_constant_payment L L2 (by norm_num [L]) (by norm_num [L2])
  change 0 < epsilon0 at he0
  change epsilon0 ≤ (1 / 64 : ℝ) at he064
  change epsilon0 ≤ 1 / (64 * Real.sqrt L2) at heClock
  change epsilon0 ≤ (1 / 1024 : ℝ) / (8 * L) at heTilt
  change 0 < t0 at ht0
  change t0 < (3 / 8 : ℝ) at htThree
  change t0 ≤ Real.exp (-1) at htExp
  change (3 * (1 / 1024 : ℝ) / epsilon0) * t0 * Real.log (1 / t0) ≤ (1 / 4 : ℝ) at htLog
  change 0 < eta0 at heta
  change eta0 ≤ (1 / 16 : ℝ) at heta16
  change eta0 ≤ Real.sqrt t0 / (2 * Real.sqrt L2) at hetaClock
  change eta0 ≤ (epsilon0 / 20480) ^ 2 at hetaShort
  change eta0 ≤ 1 / (16384 * (1 + 3 / t0) * Real.exp (24 * epsilon0 / t0)) at hetaMacro
  have heps : 0 < epsilon := by dsimp only [epsilon]; positivity
  have heps0 : epsilon ≤ epsilon0 / 2 := min_le_left _ _
  have hsL2 : Real.sqrt L2 = 128 := by
    dsimp only [L2]
    rw [show (16384 : ℝ) = 128 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 128)]
  have heval : epsilon0 = (1 / 13107200 : ℝ) := by
    dsimp only [epsilon0]
    rw [hsL2]
    norm_num [alpha, L]
  have hlarge : epsilon0 ≤ 1 / (192 * Real.sqrt (L2 + 1)) := by
    have hs : Real.sqrt (L2 + 1) ≤ 129 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num [L2]⟩
    have hsp : 0 < Real.sqrt (L2 + 1) := by positivity
    rw [heval]
    apply (le_div_iff₀ (show 0 < 192 * Real.sqrt (L2 + 1) by positivity)).mpr
    calc
      (1 / 13107200 : ℝ) * (192 * Real.sqrt (L2 + 1)) ≤ (1 / 13107200 : ℝ) * (192 * 129) := by gcongr
      _ ≤ 1 := by norm_num
  have hscale : (1 / 128 : ℝ) * Real.sqrt L2 = 1 := by rw [hsL2]; norm_num
  refine ⟨he0, heps, heps0, ht0, htThree, hlarge, hscale, ?_⟩
  obtain ⟨Creg, hCreg, hreg⟩ := sourceFutureNoiseKernel_growing_region_integrals
  let c : ℝ := alpha / epsilon0
  let Kshort : ℝ := (2 + c) ^ 128 * Real.sqrt (2 * Real.pi)
  let Klam : ℝ := 3 / t0
  let Dmoment : ℝ := 2 * (1 + (t0⁻¹) ^ 3)
  let Ddelta : ℝ := 1 + Klam
  let U0 : ℝ := Dmoment * (1 + Klam)
  let V0 : ℝ := Dmoment * (1 + Klam) ^ 3 + (t0⁻¹ + Ddelta) * U0 + U0
  let P0 : ℝ := (t0⁻¹ + Klam ^ 2) ^ 8
  let G0 : ℝ := 16 * Real.exp (8 * Klam * epsilon0)
  let H0 : ℝ := (epsilon0 * Ddelta) ^ 31
  let QA : ℝ := (4 / 3 : ℝ) * (U0 + V0) + G0 * Ddelta +
    2 * P0 * G0 ^ 14 + H0 * G0 ^ 30
  let QB : ℝ := U0 + G0 ^ 2 * Ddelta ^ 2 + Klam * G0 * Ddelta +
    2 * P0 * (G0 ^ 13 + Klam * G0 ^ 14) + H0 * (G0 ^ 29 + Klam * G0 ^ 30)
  let Dexp : ℝ := Klam + 512 * Klam ^ 3 * Real.exp (512 * Klam * epsilon0) +
    512 * Klam * epsilon0
  let C : ℝ := Creg * (Kshort + Real.exp Dexp * (QA + QB))
  have hKlam : 0 ≤ Klam := by dsimp only [Klam]; positivity
  have hDmoment : 0 ≤ Dmoment := by dsimp only [Dmoment]; positivity
  have hDdelta : 0 ≤ Ddelta := by dsimp only [Ddelta]; positivity
  have hU0 : 0 ≤ U0 := by dsimp only [U0]; positivity
  have hV0 : 0 ≤ V0 := by dsimp only [V0]; positivity
  have hP0 : 0 ≤ P0 := by dsimp only [P0]; positivity
  have hG0 : 0 ≤ G0 := by dsimp only [G0]; positivity
  have hH0 : 0 ≤ H0 := by dsimp only [H0]; positivity
  have hQA : 0 ≤ QA := by dsimp only [QA]; positivity
  have hQB : 0 ≤ QB := by dsimp only [QB]; positivity
  have hKshort : 0 < Kshort := by dsimp only [Kshort, c, alpha]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCS : Creg * Kshort ≤ C := by
    dsimp only [C]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) hCreg.le
  have hCA : Creg * Real.exp Dexp * QA ≤ C := by
    have he := mul_le_mul_of_nonneg_left (show QA ≤ QA + QB from le_add_of_nonneg_right hQB) (Real.exp_pos Dexp).le
    have hh : Real.exp Dexp * QA ≤ Kshort + Real.exp Dexp * (QA + QB) :=
      he.trans (le_add_of_nonneg_left hKshort.le)
    calc
      _ = Creg * (Real.exp Dexp * QA) := by ring1_nf (config := { zetaDelta := false })
      _ ≤ _ := mul_le_mul_of_nonneg_left hh hCreg.le
  have hCB : Creg * Real.exp Dexp * QB ≤ C := by
    have he := mul_le_mul_of_nonneg_left (show QB ≤ QA + QB from le_add_of_nonneg_left hQA) (Real.exp_pos Dexp).le
    have hh : Real.exp Dexp * QB ≤ Kshort + Real.exp Dexp * (QA + QB) :=
      he.trans (le_add_of_nonneg_left hKshort.le)
    calc
      _ = Creg * (Real.exp Dexp * QB) := by ring1_nf (config := { zetaDelta := false })
      _ ≤ _ := mul_le_mul_of_nonneg_left hh hCreg.le
  refine ⟨C, hC, ?_⟩
  intro nu0 hp n h2 hnorm hmean x hx hRc hRe y hy hwindow
  letI : IsProbabilityMeasure nu0 := hp
  intro rho h mu raw2 m3 V gamma Lambda T f
  obtain ⟨heps', hepsSmall, hprob, h1, h2rho, h3, hcut, hh, hcut_h, hsupportCut,
    hsupport, hyx, hwindow', hhy, hnm2lo, hnm2hi, hnV, hnmu, hV, hm3, hgamma,
    hm2V, hm2g, hgammaCut, hgammaN, hLambda0, hLambdaEta, hgammaEta, hclockEta,
    hcone, hmacro, hshort⟩ :=
    sourceTruncation_growingTilt_parameter_payment nu0 n h2 hnorm hmean
      L L2 epsilon0 t0 eta0 (by norm_num [L]) (by norm_num [L2])
      he0 heClock heTilt ht0 htThree htExp htLog heta heta16 hetaClock hetaShort hetaMacro
      x epsilon hx rfl hRc hRe y hy hwindow
  letI : IsProbabilityMeasure rho := hprob
  change 0 < h at hh
  change 0 < V at hV
  change 0 < m3 at hm3
  change 0 < gamma at hgamma
  change raw2 ≤ 2 * V at hm2V
  change gamma ≤ 2 * (n : ℝ) * m3 at hgammaN
  change 0 ≤ Lambda at hLambda0
  change Lambda ≤ eta0 / 2 at hLambdaEta
  change (3 / 4 : ℝ) ≤ (n : ℝ) * raw2 at hnm2lo
  change (n : ℝ) * raw2 ≤ (4 / 3 : ℝ) at hnm2hi
  change (1 / 2 : ℝ) ≤ (n : ℝ) * V at hnV
  change (n : ℝ) * |mu| ≤ (1 / 2 : ℝ) at hnmu
  change (∀ᵐ a : ℝ ∂rho, |a| ≤ h) at hsupport
  have hraw2 : 0 < raw2 := by
    by_contra hn
    have he := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (le_of_not_gt hn)
    linarith only [hnm2lo, he]
  have hLambda1 : Lambda ≤ 1 := by linarith only [hLambdaEta, heta16]
  have hy0 : 0 ≤ y := by linarith only [hy]
  have hyh : y * h ≤ (1 / 64 : ℝ) := by
    change (4 * h) * y ≤ (1 / 16 : ℝ) at hhy
    nlinarith only [hhy]
  have he192 : epsilon0 ≤ (1 / 192 : ℝ) := by rw [heval]; norm_num
  have hhsmall : h ≤ 1 / (192 * (1 + y)) := by
    change epsilon0 / (1 + y) ≤ _
    exact (div_le_div_of_nonneg_right he192 (by linarith only [hy])).trans_eq (by rw [div_div])
  have hgammah : gamma ≤ 2 * h := hgammaCut.trans (mul_le_mul_of_nonneg_left hcut_h (by norm_num))
  obtain ⟨_, _, hscalar⟩ := sourceFutureNoiseKernel_scalar_localized_bounds
  have hscalarData (i : ℕ) :=
    hscalar rho hprob h3 hV h hh hsupport hgammah (n - i) y hy hhsmall
  refine ⟨hgamma, hraw2, hLambda0, ?_⟩
  intro i hi
  obtain ⟨hd, hzero, hlocalized, hstep⟩ := hscalarData i
  change (∀ q w : ℝ, DifferentiableAt ℝ (f i q) w ∧
    DifferentiableAt ℝ (fun r : ℝ => deriv (f i q) r) w) at hd
  change (∀ q : ℝ, 5 < q → ∀ w : ℝ, f i q w = 0 ∧ deriv (f i q) w = 0 ∧
    deriv (fun r : ℝ => deriv (f i q) r) w = 0) at hzero
  have hclockzero : T i = 0 ↔ n - i = 0 := by
    dsimp only [T]
    rw [mul_eq_zero, or_iff_left hraw2.ne', Nat.cast_eq_zero]
  refine ⟨hclockzero, hd, hzero, hstep, ?_, ?_⟩
  · intro q hq hregime
    have hTlo : t0 ≤ T i := by
      rcases hregime with hearly | hlate
      · have hnrel : n ≤ 2 * (n - i) := by omega
        have hnr : (n : ℝ) ≤ 2 * ((n - i : ℕ) : ℝ) := by exact_mod_cast hnrel
        have he := mul_le_mul_of_nonneg_right hnr hraw2.le
        change t0 ≤ ((n - i : ℕ) : ℝ) * raw2
        nlinarith only [hnm2lo, he, htThree]
      · exact hlate.2.1
    have hT : 0 < T i := ht0.trans_le hTlo
    have hThi : T i ≤ (4 / 3 : ℝ) := by
      have hmn : ((n - i : ℕ) : ℝ) ≤ n := by exact_mod_cast (Nat.sub_le n i)
      exact (mul_le_mul_of_nonneg_right hmn hraw2.le).trans hnm2hi
    have hm : 0 < n - i := by
      by_contra hm
      have hz : n - i = 0 := Nat.eq_zero_of_not_pos hm
      have hzT := hclockzero.mpr hz
      linarith only [hzT, hT]
    let E : ℝ := Real.exp (-(y ^ 2 * (q + T i) / (2 * T i)))
    have hE : 0 ≤ E := (Real.exp_pos _).le
    have hder :
        |deriv (f i q) 0| ≤ C * Lambda * E ∧
        (∀ w : ℝ, |w| ≤ h →
          |deriv (fun r : ℝ => deriv (f i q) r) w| ≤ C * (1 + y) * E) := by
      by_cases hqbig : 5 < q
      · constructor
        · rw [(hzero q hqbig 0).2.1, abs_zero]
          positivity
        · intro w hw
          rw [(hzero q hqbig w).2.2, abs_zero]
          positivity
      · have hpay := (hmacro i q hi hq hregime).resolve_left hqbig
        let N : ℝ := q + T i
        let lam : ℝ := y * Real.sqrt N / T i
        let s : ℝ := lam * y / Real.sqrt N
        let Gamma : ℝ := 8 * Real.exp (8 * lam * h) * gamma
        obtain ⟨hTlo', hclock, hNlo, hNhi, hlamN, hlam, hs0, hs2, hsh,
          hsEq, hGamma, hlamBound, hlamh, hsmall, hsmall8, hconeG, hid⟩ := hpay
        change (1 / 16 : ℝ) ≤ N at hNlo
        change N ≤ 7 at hNhi
        change y / Real.sqrt N ≤ lam at hlamN
        change 0 ≤ lam at hlam
        change s = y ^ 2 / T i at hsEq
        change 0 < Gamma at hGamma
        change lam ≤ 3 * y / t0 at hlamBound
        change lam * h ≤ 3 * epsilon0 / t0 at hlamh
        change (y + lam) * Gamma ≤ (1 / 2048 : ℝ) at hsmall
        change -lam * y * Real.sqrt N + T i * lam ^ 2 / 2 =
          -(y ^ 2 * N / (2 * T i)) at hid
        have hN : 0 < N := by linarith only [hNlo]
        have hlamK : lam ≤ Klam * (1 + y) := by
          calc
            lam ≤ 3 * y / t0 := hlamBound
            _ = (3 / t0) * y := by ring1_nf (config := { zetaDelta := false })
            _ ≤ (3 / t0) * (1 + y) :=
              mul_le_mul_of_nonneg_left (by linarith only []) (by positivity)
        have hlamhK : lam * h ≤ Klam * epsilon0 := by
          calc
            lam * h ≤ 3 * epsilon0 / t0 := hlamh
            _ = _ := by dsimp only [Klam]; ring1_nf (config := { zetaDelta := false })
        have hclock20 : 20 * gamma ^ 2 ≤ T i := by
          change L2 * gamma ^ 2 ≤ T i at hclock
          norm_num only [L2] at hclock
          nlinarith only [hclock, sq_nonneg gamma]
        let Delta : ℝ := (1 + lam * y)⁻¹
        let J : ℕ → ℝ := fun k =>
          (T i) ^ (-((k : ℝ) + 1) / 2) +
            Real.sqrt y * Delta * (T i) ^ (-(2 * (k : ℝ) + 3) / 4)
        let U : ℝ := J 1 + lam * J 0
        let Vpoly : ℝ := J 3 + 3 * lam * J 2 + 3 * lam ^ 2 * J 1 + lam ^ 3 * J 0 +
          (s + Delta⁻¹) * U + y * (J 2 + lam * J 1)
        let PJ : ℝ := ((T i)⁻¹ + lam ^ 2) ^ 8
        let R1tail : ℝ := Gamma ^ 15 + Real.sqrt y * Delta * Gamma ^ 15 / Real.sqrt Gamma
        let R2tail : ℝ := Gamma ^ 14 + Real.sqrt y * Delta * Gamma ^ 14 / Real.sqrt Gamma
        let A : Fin 4 → ℝ := fun k =>
          if k = 0 then T i * ((n : ℝ) * |mu| * U + (n : ℝ) * m3 * Vpoly)
          else if k = 1 then Gamma * Delta⁻¹
          else if k = 2 then PJ * R1tail
          else (h * Delta⁻¹) ^ 31 * Gamma ^ 30
        let B : Fin 4 → ℝ := fun k =>
          if k = 0 then U
          else if k = 1 then Gamma ^ 2 * Delta⁻¹ ^ 2 + lam * Gamma * Delta⁻¹
          else if k = 2 then PJ * (R2tail + lam * R1tail)
          else (h * Delta⁻¹) ^ 31 * (Gamma ^ 29 + lam * Gamma ^ 30)
        let Ebase : ℝ := Real.exp
          (-lam * y * Real.sqrt N + T i * lam ^ 2 / 2 +
            ((n - i : ℕ) : ℝ) * lam * |mu| +
            24 * ((n - i : ℕ) : ℝ) * lam ^ 3 * m3 * Real.exp (lam * h) + 200 * lam * h)
        have hAsum : (∑ k : Fin 4, A k) ≤ QA * Lambda ∧
            (∑ k : Fin 4, B k) ≤ QB * (1 + y) := by
          have hp := sgk_macro_sums epsilon0 t0 y (T i) lam h N gamma mu m3 n
            he0 ht0 hy hTlo hThi hN hNhi hlam hlamN hlamK hlamhK rfl hsEq
            hgamma hm3.le hgammaN hLambda1 hsmall
          change
            T i * ((n : ℝ) * |mu| * U + (n : ℝ) * m3 * Vpoly) +
              Gamma * Delta⁻¹ + PJ * R1tail + (h * Delta⁻¹) ^ 31 * Gamma ^ 30 ≤ QA * Lambda ∧
            U + (Gamma ^ 2 * Delta⁻¹ ^ 2 + lam * Gamma * Delta⁻¹) +
              PJ * (R2tail + lam * R1tail) +
              (h * Delta⁻¹) ^ 31 * (Gamma ^ 29 + lam * Gamma ^ 30) ≤ QB * (1 + y) at hp
          have heA : (∑ k : Fin 4, A k) =
              T i * ((n : ℝ) * |mu| * U + (n : ℝ) * m3 * Vpoly) +
              Gamma * Delta⁻¹ + PJ * R1tail + (h * Delta⁻¹) ^ 31 * Gamma ^ 30 := by
            simp [A, Fin.sum_univ_succ]
            <;> ring1_nf (config := { zetaDelta := false })
          have heB : (∑ k : Fin 4, B k) =
              U + (Gamma ^ 2 * Delta⁻¹ ^ 2 + lam * Gamma * Delta⁻¹) +
              PJ * (R2tail + lam * R1tail) +
              (h * Delta⁻¹) ^ 31 * (Gamma ^ 29 + lam * Gamma ^ 30) := by
            simp [B, Fin.sum_univ_succ]
            <;> ring1_nf (config := { zetaDelta := false })
          rw [heA, heB]
          exact hp
        have hEb : Ebase ≤ Real.exp Dexp * E :=
          sgk_macro_exponent epsilon0 t0 y (T i) N lam h mu m3 n (n - i)
            he0 ht0 hy hlam (Nat.sub_le _ _) hm3.le hLambda1 hlamK hlamhK (by positivity) hid
        have hpair (w : ℝ) (hw : |w| ≤ h) :
            |deriv (f i q) 0| ≤ Creg * Ebase * (∑ k : Fin 4, A k) ∧
            |deriv (fun r : ℝ => deriv (f i q) r) w| ≤ Creg * Ebase * (∑ k : Fin 4, B k) := by
          have hr := hreg rho n (n - i) h y lam q w h3 hV hh hm hsupport
            hm2V hnm2lo hnm2hi hnV hnmu hy hq hyh hw
          obtain ⟨_, _, _, _, _, _, _, _, hfirst, hsecond, _, _⟩ :=
            hr hNlo hNhi hlamN hclock20 hsmall
          exact ⟨hfirst, hsecond⟩
        constructor
        · calc
            _ ≤ Creg * Ebase * (∑ k : Fin 4, A k) := (hpair 0 (by simpa using hh.le)).1
            _ ≤ Creg * (Real.exp Dexp * E) * (QA * Lambda) := by
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left hEb hCreg.le
              · exact hAsum.1
              · apply Finset.sum_nonneg
                intro k hk
                dsimp only [A]
                split_ifs <;> positivity
              · positivity
            _ = (Creg * Real.exp Dexp * QA) * Lambda * E := by ring1_nf (config := { zetaDelta := false })
            _ ≤ C * Lambda * E := by gcongr
        · intro w hw
          calc
            _ ≤ Creg * Ebase * (∑ k : Fin 4, B k) := (hpair w hw).2
            _ ≤ Creg * (Real.exp Dexp * E) * (QB * (1 + y)) := by
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left hEb hCreg.le
              · exact hAsum.2
              · apply Finset.sum_nonneg
                intro k hk
                dsimp only [B]
                split_ifs <;> positivity
              · positivity
            _ = (Creg * Real.exp Dexp * QB) * (1 + y) * E := by ring1_nf (config := { zetaDelta := false })
            _ ≤ C * (1 + y) * E := by gcongr
    refine ⟨hT, hder.1, ?_⟩
    exact sgk_local_package (f i q) h C Lambda (1 + y) E hh.le hC.le hLambda0
      (by linarith) hE (hd q) hder.1 hder.2
  · intro hlate hclock hTlt
    have hT : 0 < T i := by
      have hL2p : 0 < L2 := by norm_num [L2]
      exact (mul_pos hL2p (sq_pos_of_pos hgamma)).trans_le hclock
    refine ⟨hT, ?_⟩
    intro q hq
    have htail : 0 ≤ Shao.standardNormalTail y := ((Shao.standardNormalTail_basic.2.2.1 y).1).le
    let E : ℝ := Shao.standardNormalTail y * (T i) ^ 2
    have hE : 0 ≤ E := mul_nonneg htail (sq_nonneg _)
    have hder :
        |deriv (f i q) 0| ≤ C * Lambda * E ∧
        (∀ w : ℝ, |w| ≤ h → |deriv (fun r : ℝ => deriv (f i q) r) w| ≤ C * E) := by
      by_cases hqbig : 5 < q
      · constructor
        · rw [(hzero q hqbig 0).2.1, abs_zero]
          positivity
        · intro w hw
          rw [(hzero q hqbig w).2.2, abs_zero]
          positivity
      · have hpay := (hshort i q hi hlate hq hclock hTlt).resolve_left hqbig
        let ell : ℝ := Real.log (1 / T i)
        let lam : ℝ := (alpha / h) * ell
        let N : ℝ := q + T i
        let s : ℝ := lam * y / Real.sqrt N
        let Gamma : ℝ := 8 * Real.exp (8 * lam * h) * gamma
        let E512 : ℝ := Real.exp
          (-lam * y * Real.sqrt N + T i * lam ^ 2 / 2 +
            ((n - i : ℕ) : ℝ) * lam * |mu| +
            512 * ((n - i : ℕ) : ℝ) * lam ^ 3 * m3 * Real.exp (512 * lam * h) +
            512 * lam * h)
        let Bstar : ℝ := 1 + y + lam + (T i)⁻¹
        let Rn : ℝ := (n : ℝ) * |mu| + (n : ℝ) * m3
        obtain ⟨hT', hell, hNlo, hNhi, hlam4, hlamN, hs0, hs2, hsh, hlamh,
          hGamma, hsmallEta, hsmall, hsmall8, hconeG, hquad, hmeanPay, hthirdPay,
          hdamp, hEs⟩ := hpay
        change 1 ≤ ell at hell
        change (1 / 16 : ℝ) ≤ N at hNlo
        change N ≤ 7 at hNhi
        change 4 * y ≤ lam at hlam4
        change y / Real.sqrt N ≤ lam at hlamN
        change (y + lam) * Gamma ≤ (1 / 2048 : ℝ) at hsmall
        change E512 ≤ Real.exp (512 * lam * h) * Real.exp (-L * y * (1 + y) * ell) at hEs
        have hlam : 0 ≤ lam := by linarith only [hlam4, hy]
        have hm : 0 < n - i := by
          by_contra hm
          have hz : n - i = 0 := Nat.eq_zero_of_not_pos hm
          have hzT := hclockzero.mpr hz
          linarith only [hzT, hT]
        have hclock20 : 20 * gamma ^ 2 ≤ T i := by
          norm_num only [L2] at hclock
          nlinarith only [hclock, sq_nonneg gamma]
        have hnormShort0 := sgk_short_normalization epsilon0 L y (T i) lam h E512
          he0 (by norm_num [L]) hy hT (hTlt.le.trans htExp) hell rfl rfl
          (Real.exp_pos _).le hEs
        have hnormShort : Bstar ^ 128 * E512 ≤ Kshort * E := by
          simpa only [Bstar, Kshort, c, alpha, E, mul_assoc] using hnormShort0
        have hRn : Rn ≤ Lambda := by
          have ha : 1 ≤ 1 + y := by linarith only [hy]
          have ha3 : 1 ≤ (1 + y) ^ 3 := one_le_pow₀ ha
          have h0 := mul_le_mul_of_nonneg_right ha
            (show 0 ≤ (n : ℝ) * |mu| by positivity)
          have h1 := mul_le_mul_of_nonneg_right ha3
            (show 0 ≤ (n : ℝ) * m3 by positivity)
          change (n : ℝ) * |mu| + (n : ℝ) * m3 ≤
            (1 + y) * (n : ℝ) * |mu| + (1 + y) ^ 3 * (n : ℝ) * m3
          nlinarith only [h0, h1]
        have hpair (w : ℝ) (hw : |w| ≤ h) :
            |deriv (f i q) 0| ≤ Creg * Rn * Bstar ^ 128 * E512 ∧
            |deriv (fun r : ℝ => deriv (f i q) r) w| ≤ Creg * Bstar ^ 128 * E512 := by
          have hr := hreg rho n (n - i) h y lam q w h3 hV hh hm hsupport
            hm2V hnm2lo hnm2hi hnV hnmu hy (by linarith only [hq]) hyh hw
          obtain ⟨_, _, _, _, _, _, _, _, _, _, hfirst, hsecond⟩ :=
            hr hNlo hNhi hlamN hclock20 hsmall
          exact ⟨hfirst, hsecond⟩
        constructor
        · calc
            _ ≤ Creg * Rn * Bstar ^ 128 * E512 := (hpair 0 (by simpa using hh.le)).1
            _ = Creg * Rn * (Bstar ^ 128 * E512) := by ring1_nf (config := { zetaDelta := false })
            _ ≤ Creg * Lambda * (Kshort * E) := by
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left hRn hCreg.le
              · exact hnormShort
              · positivity
              · positivity
            _ = (Creg * Kshort) * Lambda * E := by ring1_nf (config := { zetaDelta := false })
            _ ≤ C * Lambda * E := by gcongr
        · intro w hw
          calc
            _ ≤ Creg * Bstar ^ 128 * E512 := (hpair w hw).2
            _ = Creg * (Bstar ^ 128 * E512) := by ring1_nf (config := { zetaDelta := false })
            _ ≤ Creg * (Kshort * E) := mul_le_mul_of_nonneg_left hnormShort hCreg.le
            _ = (Creg * Kshort) * E := by ring1_nf (config := { zetaDelta := false })
            _ ≤ C * E := mul_le_mul_of_nonneg_right hCS hE
    have hpkg := sgk_local_package (f i q) h C Lambda 1 E hh.le hC.le hLambda0
      (by norm_num) hE (hd q) hder.1 (by simpa only [mul_one] using hder.2)
    refine ⟨?_, ?_⟩
    · simpa only [E, mul_assoc] using hder.1
    · simpa only [E, mul_assoc, one_mul, mul_one] using hpkg


end Shao.Probability

