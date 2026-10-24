import Mathlib.Analysis.Complex.ExponentialBounds
import Shao.Probability.SourceNoiseCost
import Shao.Probability.SourceFourierScale
import Shao.Probability.TruncationRegularity
import Shao.Probability.MeasurablePath

set_option autoImplicit false
set_option Elab.async false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped Topology

theorem sourceReferenceG_local_lipschitz
    (x s t : ℝ) (hx : 0 ≤ x)
    (hs : |s - x| ≤ 1 / (1 + x))
    (ht : |t - x| ≤ 1 / (1 + x)) :
    let G : ℝ → ℝ := fun u =>
      if 0 < u then 1 - 2 * Shao.standardNormalTail u else 0
    |G t - G s| ≤
      (2 * Real.exp 2) * Shao.standardNormalDensity x * |t - s| := by
  dsimp only
  let H : ℝ → ℝ := fun u => 1 - 2 * Shao.standardNormalTail u
  let h : ℝ := 1 / (1 + x)
  have hx1 : 0 < 1 + x := by linarith
  have hh : 0 < h := one_div_pos.mpr hx1
  have hh1 : h ≤ 1 := (div_le_iff₀ hx1).mpr (by linarith)
  have hmul : h * (1 + x) = 1 := div_mul_cancel₀ 1 hx1.ne'
  have hφ0 : 0 < Shao.standardNormalDensity x :=
    ProbabilityTheory.gaussianPDFReal_pos 0 1 x (by norm_num)
  have hH (u : ℝ) : HasDerivAt H (2 * Shao.standardNormalDensity u) u := by
    convert ((Shao.standardNormal_derivatives u).2.const_mul 2).const_sub 1 using 1 <;> ring
  have hformula (u : ℝ) : Shao.standardNormalDensity u =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-u ^ 2 / 2) := by
    simp [Shao.standardNormalDensity, ProbabilityTheory.gaussianPDFReal]
  have hφ (u : ℝ) (hu : u ∈ Set.Icc (max 0 (x - h)) (x + h)) :
      Shao.standardNormalDensity u ≤ Real.exp 2 * Shao.standardNormalDensity x := by
    have hu0 : 0 ≤ u := (le_max_left _ _).trans hu.1
    have hlu : x - h ≤ u := (le_max_right _ _).trans hu.1
    have hux : x ^ 2 - u ^ 2 ≤ 4 := by
      have hprod := mul_nonneg (show 0 ≤ u - (x - h) by linarith) (show 0 ≤ x + u by linarith)
      have huupper := mul_le_mul_of_nonneg_left hu.2 hh.le
      nlinarith [sq_nonneg h]
    have hratio : Shao.standardNormalDensity u =
        Real.exp ((x ^ 2 - u ^ 2) / 2) * Shao.standardNormalDensity x := by
      rw [hformula u, hformula x]
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    rw [hratio]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hφ0.le
  have hclip (u : ℝ) (hu : |u - x| ≤ h) :
      max u 0 ∈ Set.Icc (max 0 (x - h)) (x + h) := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hu
    constructor
    · exact max_le (le_max_right _ _) (by linarith [le_max_left u 0])
    · exact max_le (by linarith) (by linarith)
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
    (C := 2 * Real.exp 2 * Shao.standardNormalDensity x)
    (fun u (_ : u ∈ Set.Icc (max 0 (x - h)) (x + h)) => (hH u).differentiableAt)
    (fun u (hu : u ∈ Set.Icc (max 0 (x - h)) (x + h)) => by
      rw [(hH u).deriv, Real.norm_eq_abs, abs_of_nonneg]
      · nlinarith only [hφ u hu]
      · exact mul_nonneg (by norm_num) (ProbabilityTheory.gaussianPDFReal_pos 0 1 u (by norm_num)).le)
    (convex_Icc (max 0 (x - h)) (x + h)) (hclip s hs) (hclip t ht)
  have hG (u : ℝ) : (if 0 < u then 1 - 2 * Shao.standardNormalTail u else 0) = H (max u 0) := by
    by_cases hu : 0 < u
    · simp [hu, max_eq_left hu.le, H]
    · simp [hu, max_eq_right (le_of_not_gt hu), H, Shao.standardNormalTail_basic.2.1]
  rw [hG t, hG s]
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
  exact hmv.trans (mul_le_mul_of_nonneg_left
    (by simpa only [sub_self, abs_zero, max_eq_left (abs_nonneg (t - s))] using
      (abs_max_sub_max_le_max t 0 s 0))
    (by positivity))

theorem sourceNoise_markov_at_mean_multiple
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (delta : Ω → ℝ) (hm : Measurable delta) (hi : Integrable delta P)
    (h0 : ∀ᵐ z ∂P, 0 ≤ delta z) (K : ℝ) (hK : 1 < K) :
    let d : ℝ := ∫ z, delta z ∂P
    let a : ℝ := K * d
    let theta : ℝ := P.real {z | a < delta z}
    0 ≤ d ∧ 0 ≤ a ∧ 0 ≤ theta ∧ theta ≤ 1 / K ∧
      (d = 0 → a = 0 ∧ (∀ᵐ z ∂P, delta z = 0) ∧ theta = 0) := by
  dsimp only
  have hd : 0 ≤ ∫ z, delta z ∂P := integral_nonneg_of_ae h0
  have hK0 : 0 < K := by linarith
  have ha : 0 ≤ K * ∫ z, delta z ∂P := mul_nonneg hK0.le hd
  have htheta : 0 ≤ P.real {z | K * (∫ z, delta z ∂P) < delta z} := measureReal_nonneg
  have hzero (hz : (∫ z, delta z ∂P) = 0) :
      K * (∫ z, delta z ∂P) = 0 ∧ (∀ᵐ z ∂P, delta z = 0) ∧
      P.real {z | K * (∫ z, delta z ∂P) < delta z} = 0 := by
    have heq := (integral_eq_zero_iff_of_nonneg_ae h0 hi).mp hz
    have hnull : P {z | K * (∫ z, delta z ∂P) < delta z} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [heq] with z hdz
      simp [hz, hdz]
    exact ⟨by simp [hz], heq, by simp [Measure.real, hnull]⟩
  refine ⟨hd, ha, htheta, ?_, hzero⟩
  by_cases hz : (∫ z, delta z ∂P) = 0
  · rw [(hzero hz).2.2]
    positivity
  · have hdpos : 0 < ∫ z, delta z ∂P := lt_of_le_of_ne hd (Ne.symm hz)
    let A : Set Ω := {z | K * (∫ z, delta z ∂P) < delta z}
    have hA : MeasurableSet A := measurableSet_lt measurable_const hm
    have hiA : Integrable (A.indicator (fun _ => K * (∫ z, delta z ∂P))) P :=
      (integrable_const _).indicator hA
    have hb : (∫ z, A.indicator (fun _ => K * (∫ z, delta z ∂P)) z ∂P) ≤
        ∫ z, delta z ∂P := by
      apply integral_mono_ae hiA hi
      filter_upwards [h0] with z hz
      by_cases hzA : z ∈ A
      · rw [Set.indicator_of_mem hzA]
        exact le_of_lt hzA
      · rw [Set.indicator_of_notMem hzA]
        exact hz
    rw [integral_indicator_const _ hA, smul_eq_mul] at hb
    apply (le_div_iff₀ hK0).mpr
    nlinarith only [hb, hdpos]

theorem sourceWeight_nearby_bound
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (x t L : ℝ) (hx : 0 ≤ x) (ht : 0 ≤ t)
    (hneigh : |t - x| ≤ 1 / (1 + x)) (hL : 1600 ≤ L) :
    let w : ℝ → ℝ := fun u =>
      Shao.truncationBudget nu n u * Shao.standardNormalTail u
    w t ≤ (8 * Real.exp 2) * w x ∧ w t ≤ L * w x := by
  dsimp only
  have hR := (Shao.truncationBudget_local_comparison nu n h2 x t hx ht (by simpa only [one_div] using hneigh)).2
  have hT := (Shao.standardNormalTail_local_comparison x t hx ht hneigh).2
  have hR0 := Shao.truncationBudget_nonneg nu n h2 x
  have htR0 := Shao.truncationBudget_nonneg nu n h2 t
  have hT0 := (Shao.standardNormalTail_basic.2.2.1 x).1.le
  have hfirst : Shao.truncationBudget nu n t * Shao.standardNormalTail t ≤
      (8 * Real.exp 2) * (Shao.truncationBudget nu n x * Shao.standardNormalTail x) := by
    calc
      _ ≤ (8 * Shao.truncationBudget nu n x) *
          (Real.exp 2 * Shao.standardNormalTail x) :=
        mul_le_mul hR hT (Shao.standardNormalTail_basic.2.2.1 t).1.le (by positivity)
      _ = _ := by ring
  have he : Real.exp 2 ≤ 9 := by
    calc
      Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ 3 ^ 2 := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le 2
      _ = 9 := by norm_num
  refine ⟨hfirst, hfirst.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg hR0 hT0)
  linarith

theorem sourceSignedCDF_convolution_lower
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (delta : Ω → ℝ) (hm : Measurable delta) (hi : Integrable delta P)
    (hdelta : ∀ᵐ z ∂P, 0 ≤ delta z)
    (F G E : ℝ → ℝ) (hmono : Monotone F)
    (hF : ∀ u : ℝ, 0 ≤ F u ∧ F u ≤ 1)
    (x radius a s p w B H g b J : ℝ)
    (hradius : 0 < radius) (ha : 0 ≤ a) (haLocal : a ≤ radius)
    (hs : s = 1 ∨ s = -1) (hsE : s * E x = |E x|)
    (hp : 0 < p) (hw : 0 < w) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hg : 0 ≤ g)
    (hsupport : ∀ᵐ z ∂P, a + delta z ≤ radius)
    (hG : ∀ u v : ℝ, |u - x| ≤ radius → |v - x| ≤ radius →
      |G u - G v| ≤ g * |u - v|)
    (hPB : ∀ u : ℝ, |u - x| ≤ radius →
      |F u - G u - E u / p| ≤ B * w)
    (hE : ∀ u : ℝ, |u - x| ≤ radius → |E u| ≤ H * w)
    (hsand :
      (∫ z, s * (F (x + s * a - s * delta z) - G (x + s * a)) ∂P) - b ≤
        s * (J - G (x + s * a))) :
    let theta : ℝ := P.real {z | a < delta z}
    ((1 - theta) * |E x| - theta * H * w) / p ≤
      s * (J - G (x + s * a)) + B * w + g * (a + ∫ z, delta z ∂P) + b := by
  classical
  dsimp only
  let y : ℝ := x + s * a
  let T : Ω → ℝ := fun z => x + s * a - s * delta z
  let A : Set Ω := {z | a < delta z}
  let q : ℝ := |E x| / p
  let r : ℝ := H * w / p
  have hsabs : |s| = 1 := by rcases hs with hs | hs <;> simp [hs]
  have hsign (v : ℝ) : -|v| ≤ s * v := by
    have hh := neg_abs_le (s * v)
    simpa only [abs_mul, hsabs, one_mul] using hh
  have hA : MeasurableSet A := measurableSet_lt measurable_const hm
  have hy : |y - x| = a := by
    dsimp [y]
    rw [add_sub_cancel_left, abs_mul, hsabs, one_mul, abs_of_nonneg ha]
  have hPBsigned (u : ℝ) (hu : |u - x| ≤ radius) :
      s * (F u - G u) ≥ s * E u / p - B * w := by
    have hh := (neg_le_neg (hPB u hu)).trans (hsign (F u - G u - E u / p))
    ring_nf at hh ⊢
    linarith only [hh]
  have hxPB := hPBsigned x (by simpa using hradius.le)
  rw [hsE] at hxPB
  have hGy : |G x - G y| ≤ g * a := by
    simpa only [abs_sub_comm x y, hy, sub_self, abs_zero] using
      hG x y (by simpa using hradius.le) (hy.le.trans haLocal)
  have hTmeas : Measurable T := measurable_const.sub (measurable_const.mul hm)
  have hiF : Integrable (fun z => F (T z)) P := by
    refine (integrable_const (1 : ℝ)).mono'
      (hmono.measurable.comp hTmeas).aestronglyMeasurable ?_
    exact ae_of_all P (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hF _).1]
      exact (hF _).2)
  have hii : Integrable (fun z => s * (F (T z) - G y)) P :=
    (hiF.sub (integrable_const _)).const_mul _
  have hilo : Integrable (fun z => q - B * w - g * a -
      A.indicator (fun _ => q + r) z - g * delta z) P :=
    ((integrable_const _).sub ((integrable_const _).indicator hA)).sub (hi.const_mul g)
  have hbound : (fun z => q - B * w - g * a -
      A.indicator (fun _ => q + r) z - g * delta z) ≤ᵐ[P]
      (fun z => s * (F (T z) - G y)) := by
    filter_upwards [hdelta, hsupport] with z hdz hsz
    have ht : |T z - x| ≤ radius := by
      calc
        |T z - x| = |s * (a - delta z)| := by congr 1 <;> dsimp [T] <;> ring
        _ = |a - delta z| := by rw [abs_mul, hsabs, one_mul]
        _ ≤ |a| + |delta z| := abs_sub _ _
        _ = a + delta z := by rw [abs_of_nonneg ha, abs_of_nonneg hdz]
        _ ≤ radius := hsz
    by_cases hzA : z ∈ A
    · rw [Set.indicator_of_mem hzA]
      have hpb := hPBsigned (T z) ht
      have hEt : s * E (T z) ≥ -(H * w) :=
        (neg_le_neg (hE (T z) ht)).trans (hsign _)
      have hEtdiv : -(H * w) / p ≤ s * E (T z) / p :=
        div_le_div_of_nonneg_right hEt hp.le
      simp only [neg_div] at hEtdiv
      have hGt : |G (T z) - G y| ≤ g * delta z := by
        have hh := hG (T z) y ht (hy.le.trans haLocal)
        have hty : |T z - y| = delta z := by
          have heq : T z - y = -s * delta z := by dsimp [T, y]; ring
          rw [heq, abs_mul, abs_neg, hsabs, one_mul, abs_of_nonneg hdz]
        simpa only [hty] using hh
      have hgsg := (neg_le_neg hGt).trans (hsign (G (T z) - G y))
      dsimp [q, r]
      nlinarith only [hpb, hEtdiv, hgsg, mul_nonneg hg ha]
    · rw [Set.indicator_of_notMem hzA]
      have hgood : delta z ≤ a := le_of_not_gt hzA
      have hFmono : 0 ≤ s * (F (T z) - F x) := by
        rcases hs with hs1 | hs1
        · have htx : x ≤ T z := by dsimp [T]; rw [hs1]; linarith
          have hh := hmono htx
          rw [hs1]
          linarith
        · have htx : T z ≤ x := by dsimp [T]; rw [hs1]; linarith
          have hh := hmono htx
          rw [hs1]
          linarith
      have hgsg := (neg_le_neg hGy).trans (hsign (G x - G y))
      dsimp [q]
      nlinarith only [hFmono, hxPB, hgsg, mul_nonneg hg hdz]
  have hintegral := integral_mono_ae hilo hii hbound
  have hiA : Integrable (fun z => A.indicator (fun _ => q + r) z) P := (integrable_const _).indicator hA
  have i1 := integral_sub ((integrable_const (q - B * w - g * a)).sub hiA) (hi.const_mul g)
  have i2 := integral_sub (integrable_const (q - B * w - g * a)) hiA
  simp only [Pi.sub_apply] at i1 i2
  rw [i1, i2,
      integral_const, probReal_univ, one_smul, integral_indicator_const _ hA,
      smul_eq_mul, integral_const_mul] at hintegral
  change ((1 - P.real A) * |E x| - P.real A * H * w) / p ≤ _
  have heq : ((1 - P.real A) * |E x| - P.real A * H * w) / p =
      q - P.real A * (q + r) := by dsimp [q, r]; ring
  rw [heq]
  change (∫ z, s * (F (T z) - G y) ∂P) - b ≤ s * (J - G y) at hsand
  linarith only [hintegral, hsand]

theorem sourceTruncation_weighted_desmoothing_from_interfaces
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (x epsilon eta0 L : ℝ) (hx : 0 < x)
    (hepsilon : 0 < epsilon) (heta0 : 0 < eta0) (hL : 1600 ≤ L)
    (hepsilonNoise : epsilon ≤ 1 / 800)
    (hepsilonGeometry : epsilon ≤ 1 / (4 * (8 * (1 + L) + 1) * L))
    (hRcube : Shao.truncationBudget nu n x ≤ epsilon ^ 3 / 8)
    (hReta : Shao.truncationBudget nu n x ≤ epsilon ^ 2 * eta0 / 40)
    (hxD3 : 4 * (8 * (1 + L)) * L * Shao.truncationBudget nu n 0 < x) :
    let K : ℝ := 8 * (1 + L)
    let h : ℝ := epsilon / (1 + x)
    let rho : Measure ℝ := ProbabilityTheory.cond nu {z : ℝ | |z| ≤ h}
    let P0 : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
    let N : Set (Shao.Path n) := {a | ∀ j : Fin n, |a j| ≤ h}
    let p : ℝ := P0.real N
    let noise : Measure (ℝ × ℝ) := quadraticFullNoiseLaw rho
    let delta : ℝ × ℝ → ℝ := fun z => 4 * (|z.1| + (1 + x) * |z.2|)
    let d : ℝ := ∫ z, delta z ∂noise
    let a : ℝ := K * d
    let theta : ℝ := noise.real {z | a < delta z}
    let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂rho) / variance (id : ℝ → ℝ) rho
    let w : ℝ := Shao.truncationBudget nu n x * Shao.standardNormalTail x
    let G : ℝ → ℝ := fun u =>
      if 0 < u then 1 - 2 * Shao.standardNormalTail u else 0
    let F0 : ℝ → ℝ := fun u => P0.real {v : Shao.Path n |
      0 < Shao.energy v ∧ Shao.maxWithZero v < u * Real.sqrt (Shao.energy v)}
    let E : ℝ → ℝ := fun u => F0 u - G u
    let F : ℝ → ℝ := fun u => P.real {v : Shao.Path n |
      0 < Shao.energy v ∧ Shao.maxWithZero v < u * Real.sqrt (Shao.energy v)}
    let Fend : ℝ → ℝ := fun u => P.real {v : Shao.Path n |
      0 < Shao.energy v ∧ |Shao.prefixSum v n| < u * Real.sqrt (Shao.energy v)}
    let Jmax : ℝ → ℝ := fun y => ∫ v : Shao.Path n,
      (∫ z : ℝ × ℝ, sourceFourierTest y
        (Shao.maxWithZero v + z.1, Shao.energy v + z.2) ∂noise) ∂P
    let Jend : ℝ → ℝ := fun y => ∫ v : Shao.Path n,
      (∫ z : ℝ × ℝ, sourceFourierTest y
        (Shao.prefixSum v n + z.1, Shao.energy v + z.2) ∂noise) ∂P
    let D : ℝ := 32768 * Real.sqrt (2 * Real.pi) +
      1 / Shao.standardNormalTail 2 + 1600
    let c : ℝ := 2 * Real.exp 2
    0 < w ∧ (7 / 8 : ℝ) ≤ p ∧ p ≤ 1 ∧
      IsProbabilityMeasure P ∧ IsProbabilityMeasure noise ∧
      Integrable delta noise ∧ 0 ≤ d ∧ theta ≤ 1 / K ∧
      a < x / 4 ∧ gamma < x / (4 * K) ∧
      (∀ᵐ z ∂noise, a + delta z ≤ 1 / (4 * (1 + x))) ∧
      (∀ B Ce Cs M : ℝ, 0 ≤ B → 0 ≤ Ce → 0 ≤ Cs → 0 ≤ M →
        (∀ u : ℝ, |u - x| ≤ 1 / (1 + x) →
          |F u - G u - E u / p| ≤ B * w) →
        (∀ u : ℝ, |u - x| ≤ 1 / (1 + x) →
          |Fend u - G u| ≤ Ce * w) →
        (∀ y : ℝ, gamma ≤ y → |y - x| ≤ 1 / (2 * (1 + x)) →
          |Jmax y - Jend y| ≤ Cs * w) →
        (∀ u : ℝ, |u - x| ≤ 1 / (1 + x) → |E u| ≤ L * M * w) →
        |E x| / w ≤
          K / (K - 1) * (B + Ce + Cs + c * (K + 2) * D) + L / (K - 1) * M ∧
        |E x| / w ≤
          K / (K - 1) * (B + Ce + Cs + c * (K + 2) * D) + M / 4) := by
  classical
  dsimp only
  let K : ℝ := 8 * (1 + L)
  let h : ℝ := epsilon / (1 + x)
  let rho : Measure ℝ := ProbabilityTheory.cond nu {z : ℝ | |z| ≤ h}
  let P0 : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
  let N : Set (Shao.Path n) := {v | ∀ j : Fin n, |v j| ≤ h}
  let p : ℝ := P0.real N
  let noise : Measure (ℝ × ℝ) := quadraticFullNoiseLaw rho
  let delta : ℝ × ℝ → ℝ := fun z => 4 * (|z.1| + (1 + x) * |z.2|)
  let d : ℝ := ∫ z, delta z ∂noise
  let a : ℝ := K * d
  let theta : ℝ := noise.real {z | a < delta z}
  let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂rho) / variance (id : ℝ → ℝ) rho
  let w : ℝ := Shao.truncationBudget nu n x * Shao.standardNormalTail x
  let G : ℝ → ℝ := fun u => if 0 < u then 1 - 2 * Shao.standardNormalTail u else 0
  let F0 : ℝ → ℝ := fun u => P0.real {v : Shao.Path n |
    0 < Shao.energy v ∧ Shao.maxWithZero v < u * Real.sqrt (Shao.energy v)}
  let E : ℝ → ℝ := fun u => F0 u - G u
  let F : ℝ → ℝ := fun u => P.real {v : Shao.Path n |
    0 < Shao.energy v ∧ Shao.maxWithZero v < u * Real.sqrt (Shao.energy v)}
  let Fend : ℝ → ℝ := fun u => P.real {v : Shao.Path n |
    0 < Shao.energy v ∧ |Shao.prefixSum v n| < u * Real.sqrt (Shao.energy v)}
  let Jmax : ℝ → ℝ := fun y => ∫ v : Shao.Path n,
    (∫ z : ℝ × ℝ, sourceFourierTest y
      (Shao.maxWithZero v + z.1, Shao.energy v + z.2) ∂noise) ∂P
  let Jend : ℝ → ℝ := fun y => ∫ v : Shao.Path n,
    (∫ z : ℝ × ℝ, sourceFourierTest y
      (Shao.prefixSum v n + z.1, Shao.energy v + z.2) ∂noise) ∂P
  let D : ℝ := 32768 * Real.sqrt (2 * Real.pi) + 1 / Shao.standardNormalTail 2 + 1600
  let c : ℝ := 2 * Real.exp 2
  let radius : ℝ := 1 / (1 + x)
  have hx1 : 0 < 1 + x := by linarith
  have hradius : 0 < radius := one_div_pos.mpr hx1
  have hK : 1 < K := by dsimp [K]; linarith
  have hK0 : 0 < K := by linarith
  have hehalf : epsilon ≤ 1 / 2 := by linarith
  have hn : 0 < n := by
    by_contra hh
    have hn0 : n = 0 := by omega
    simp [hn0] at hnorm
  have hsecond : 0 < ∫ z : ℝ, z ^ 2 ∂nu := by
    have hnon : 0 ≤ ∫ z : ℝ, z ^ 2 ∂nu := integral_nonneg (fun z : ℝ => sq_nonneg z)
    have hN : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    nlinarith only [hnorm, hnon, hN]
  have hw : 0 < w := mul_pos
    (Shao.truncationBudget_pos nu n h2 hn hsecond x hx.le)
    (Shao.standardNormalTail_basic.2.2.1 x).1
  letI : IsProbabilityMeasure rho :=
    (Shao.sourceTruncation_law_data nu n h2 hnorm x epsilon hx.le
      hepsilon hehalf hRcube).2.2.1
  letI : IsProbabilityMeasure P := inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => rho)))
  letI : IsProbabilityMeasure P0 := inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => nu)))
  let X : Fin n → (Shao.Path n) → ℝ := fun i v => v i
  have hX : ∀ i, Measurable (X i) := fun i => measurable_pi_apply i
  have hIndep : iIndepFun X P0 := iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable)
  have hLaw (i : Fin n) : IdentDistrib (X i) (id : ℝ → ℝ) P0 nu := by
    refine ⟨(hX i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa only [Measure.map_id] using (measurePreserving_eval (fun _ : Fin n => nu) i).map_eq
  have hsample := sourceTruncation_conditioned_sample hX hIndep hLaw h2 x epsilon
    hx.le hepsilon (by linarith) hRcube
  have hN : N = ⋂ i : Fin n, X i ⁻¹' {z : ℝ | |z| ≤ h} := by
    ext v
    simp only [N, X, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  have hp78 : (7 / 8 : ℝ) ≤ p := by simpa only [p, hN] using hsample.2.1
  have hp1 : p ≤ 1 := measureReal_le_one
  have hp : 0 < p := by linarith
  have hs := Shao.sourceTruncation_actual_noise_cdf_sandwich nu n h2 hnorm hmean
    x epsilon hx.le hepsilon hepsilonNoise hRcube
  letI : IsProbabilityMeasure noise := hs.2.1
  have hdi : Integrable delta noise := hs.2.2.1
  have hdAE : ∀ᵐ z ∂noise, delta z ∈ Set.Icc 0 (400 * h) := hs.2.2.2.1
  have hdgamma : d ≤ 400 * gamma := hs.2.2.2.2.1
  have hdm : Measurable delta := by dsimp [delta]; fun_prop
  have hd0 : ∀ᵐ z ∂noise, 0 ≤ delta z := hdAE.mono (fun _ hz => hz.1)
  have hmarkov := sourceNoise_markov_at_mean_multiple noise delta hdm hdi hd0 K hK
  have hd : 0 ≤ d := hmarkov.1
  have ha : 0 ≤ a := hmarkov.2.1
  have htheta0 : 0 ≤ theta := hmarkov.2.2.1
  have htheta : theta ≤ 1 / K := hmarkov.2.2.2.1
  have hgammadata := Shao.sourceTruncation_gamma_bounds nu n h2 hnorm hmean
    x epsilon hx.le hepsilon hehalf hRcube
  have hgamma : gamma ≤ 4 * Shao.truncationBudget nu n 0 := hgammadata.2.2.2.2.2.2.2.2
  have hr0 : 0 ≤ Shao.truncationBudget nu n 0 := Shao.truncationBudget_nonneg nu n h2 0
  have hdL : d ≤ L * Shao.truncationBudget nu n 0 := by
    have hh : d ≤ 1600 * Shao.truncationBudget nu n 0 := by linarith only [hdgamma, hgamma]
    exact hh.trans (mul_le_mul_of_nonneg_right hL hr0)
  have hax : a < x / 4 := by
    have hh := mul_le_mul_of_nonneg_left hdL hK0.le
    change K * d < x / 4
    change 4 * K * L * Shao.truncationBudget nu n 0 < x at hxD3
    nlinarith only [hh, hxD3]
  have hgammax : gamma < x / (4 * K) := by
    apply (lt_div_iff₀ (by positivity : 0 < 4 * K)).mpr
    have hh : gamma ≤ L * Shao.truncationBudget nu n 0 :=
      hgamma.trans (mul_le_mul_of_nonneg_right (by linarith : (4 : ℝ) ≤ L) hr0)
    have hmul := mul_le_mul_of_nonneg_left hh (show 0 ≤ 4 * K by positivity)
    change 4 * K * L * Shao.truncationBudget nu n 0 < x at hxD3
    nlinarith only [hmul, hxD3]
  have hdh : d ≤ 400 * h := by
    have hh := integral_mono_ae hdi (integrable_const (400 * h))
      (hdAE.mono (fun _ hz => hz.2))
    simpa only [integral_const, probReal_univ, one_smul] using hh
  have hgeometry : (K + 1) * 400 * h ≤ radius / 4 := by
    have hegeom : epsilon * (4 * (K + 1) * L) ≤ 1 :=
      (le_div_iff₀ (by positivity : 0 < 4 * (K + 1) * L)).1 hepsilonGeometry
    have he400 : epsilon * (4 * (K + 1) * 400) ≤ 1 := by
      have hh := mul_le_mul_of_nonneg_left (show (400 : ℝ) ≤ L by linarith)
        (show 0 ≤ epsilon * (4 * (K + 1)) by positivity)
      nlinarith only [hh, hegeom]
    have hsmall : (K + 1) * 400 * epsilon ≤ 1 / 4 := by nlinarith only [he400]
    dsimp only [h, radius]
    calc
      (K + 1) * 400 * (epsilon / (1 + x)) = ((K + 1) * 400 * epsilon) / (1 + x) := by ring
      _ ≤ (1 / 4) / (1 + x) := div_le_div_of_nonneg_right hsmall hx1.le
      _ = _ := by ring
  have hsupport : ∀ᵐ z ∂noise, a + delta z ≤ radius / 4 := by
    filter_upwards [hdAE] with z hz
    have hh := mul_le_mul_of_nonneg_left hdh hK0.le
    calc
      a + delta z ≤ K * (400 * h) + 400 * h := add_le_add hh hz.2
      _ = (K + 1) * 400 * h := by ring
      _ ≤ radius / 4 := hgeometry
  have halocal : a ≤ radius / 4 := by
    have hh := mul_le_mul_of_nonneg_left hdh hK0.le
    have hh0 : 0 ≤ 400 * h := by dsimp [h]; positivity
    nlinarith only [hh, hgeometry, hh0]
  refine ⟨hw, hp78, hp1, inferInstance, inferInstance, hdi, hd, htheta,
    hax, hgammax, ?_, ?_⟩
  · change ∀ᵐ z ∂noise, a + delta z ≤ 1 / (4 * (1 + x))
    have heq : radius / 4 = 1 / (4 * (1 + x)) := by dsimp only [radius]; field_simp
    simpa only [heq] using hsupport
  intro B Ce Cs M hB hCe hCs hM hPB hEND hSM hE
  let s : ℝ := if 0 ≤ E x then 1 else -1
  let y : ℝ := x + s * a
  let b : ℝ := P.real {v : Shao.Path n | Shao.energy v ∉ Set.Icc (1 / 4 : ℝ) 2}
  let g : ℝ := c * Shao.standardNormalDensity x
  let T0 : ℝ := B + Ce + Cs + c * (K + 2) * D
  have hsval : s = 1 ∨ s = -1 := by dsimp [s]; split <;> simp
  have hsabs : |s| = 1 := by rcases hsval with hs1 | hs1 <;> simp [hs1]
  have hsE : s * E x = |E x| := by
    dsimp [s]
    split
    · rename_i hh; simp [abs_of_nonneg hh]
    · rename_i hh; simp [abs_of_neg (lt_of_not_ge hh)]
  have hya : |y - x| = a := by
    dsimp [y]
    rw [add_sub_cancel_left, abs_mul, hsabs, one_mul, abs_of_nonneg ha]
  have hylo : 0 < y := by
    have hh := neg_abs_le (y - x)
    rw [hya] at hh
    linarith only [hh, hax, hx]
  have hyy : y ≤ 1 + x := by
    have hh := le_abs_self (y - x)
    rw [hya] at hh
    have hr1 : radius ≤ 1 := (div_le_iff₀ hx1).mpr (by linarith)
    linarith only [hh, halocal, hr1]
  have hygamma : gamma ≤ y := by
    have hgammax4 : gamma < x / 4 :=
      hgammax.trans_le (div_le_div_of_nonneg_left hx.le (by norm_num) (by nlinarith only [hK]))
    have hh := neg_abs_le (y - x)
    rw [hya] at hh
    linarith only [hgammax4, hh, hax, hx]
  have hylocal : |y - x| ≤ radius := by rw [hya]; linarith only [halocal, hradius]
  have hyhalf : |y - x| ≤ 1 / (2 * (1 + x)) := by
    rw [hya]
    have hh : radius / 4 ≤ 1 / (2 * (1 + x)) := by dsimp [radius]; field_simp; nlinarith
    exact halocal.trans hh
  have hφ : 0 < Shao.standardNormalDensity x := ProbabilityTheory.gaussianPDFReal_pos 0 1 x (by norm_num)
  have hc : 1 ≤ c := by
    have hh := Real.one_le_exp (show (0 : ℝ) ≤ 2 by norm_num)
    dsimp [c]; linarith
  have hg : 0 ≤ g := mul_nonneg (by linarith) hφ.le
  have hb : 0 ≤ b := measureReal_nonneg
  have htail2 := (Shao.standardNormalTail_basic.2.2.1 2).1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hT0 : 0 ≤ T0 := by dsimp [T0]; positivity
  have hcost : b + Shao.standardNormalDensity x * d ≤ D * w := by
    have hh := (Shao.sourceTruncation_noise_badClock_weighted_cost nu n h2 hnorm hmean
      x epsilon hx.le hepsilon hepsilonNoise hRcube).2
    simpa only [D, w, mul_assoc] using hh
  have hGlip (u v : ℝ) (hu : |u - x| ≤ radius) (hv : |v - x| ≤ radius) :
      |G u - G v| ≤ g * |u - v| := by
    have hh := sourceReferenceG_local_lipschitz x v u hx.le hv hu
    simpa only [G, g, c, mul_assoc] using hh
  have hend := hs.2.2.2.2.2 (fun v : Shao.Path n => Shao.prefixSum v n)
    (Shao.measurable_prefixSum n) y hylo hyy
  change Integrable (fun z => Fend (y - delta z)) noise ∧
    Integrable (fun z => Fend (y + delta z)) noise ∧
    Integrable (fun v => ∫ z, sourceFourierTest y (Shao.prefixSum v n + z.1, Shao.energy v + z.2) ∂noise) P ∧
    (∫ z, Fend (y - delta z) ∂noise) - b ≤ Jend y ∧
    Jend y ≤ (∫ z, Fend (y + delta z) ∂noise) + b at hend
  have hEndPoint : ∀ᵐ z ∂noise,
      |Fend (y - delta z) - G y| ≤ Ce * w + g * delta z ∧
      |Fend (y + delta z) - G y| ≤ Ce * w + g * delta z := by
    filter_upwards [hsupport, hd0] with z hsz hdz
    have hlocminus : |y - delta z - x| ≤ radius := by
      calc
        _ ≤ |y - x| + |delta z| := by convert abs_sub (y - x) (delta z) using 1 <;> ring
        _ = a + delta z := by rw [hya, abs_of_nonneg hdz]
        _ ≤ radius := by linarith only [hsz, hradius]
    have hlocplus : |y + delta z - x| ≤ radius := by
      calc
        _ ≤ |y - x| + |delta z| := by convert abs_add_le (y - x) (delta z) using 1 <;> ring
        _ = a + delta z := by rw [hya, abs_of_nonneg hdz]
        _ ≤ radius := by linarith only [hsz, hradius]
    constructor
    · calc
        _ ≤ |Fend (y - delta z) - G (y - delta z)| + |G (y - delta z) - G y| := abs_sub_le _ _ _
        _ ≤ Ce * w + g * |y - delta z - y| := add_le_add (hEND _ hlocminus) (hGlip _ _ hlocminus hylocal)
        _ = _ := by rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg hdz]
    · calc
        _ ≤ |Fend (y + delta z) - G (y + delta z)| + |G (y + delta z) - G y| := abs_sub_le _ _ _
        _ ≤ Ce * w + g * |y + delta z - y| := add_le_add (hEND _ hlocplus) (hGlip _ _ hlocplus hylocal)
        _ = _ := by rw [add_sub_cancel_left, abs_of_nonneg hdz]
  have hlo : G y - (Ce * w + g * d) ≤ ∫ z, Fend (y - delta z) ∂noise := by
    have hh := integral_mono_ae
      ((integrable_const (G y)).sub ((integrable_const (Ce * w)).add (hdi.const_mul g))) hend.1
      (hEndPoint.mono (fun z hz => by
        simp only [Pi.sub_apply, Pi.add_apply]
        linarith only [(abs_le.mp hz.1).1]))
    have i1 := integral_sub (integrable_const (G y))
      ((integrable_const (Ce * w)).add (hdi.const_mul g))
    have i2 := integral_add (integrable_const (Ce * w)) (hdi.const_mul g)
    simp only [Pi.sub_apply, Pi.add_apply] at hh i1 i2
    rw [i1, i2] at hh
    simp only [integral_const_mul, integral_const, probReal_univ, one_smul, smul_eq_mul, mul_one, one_mul] at hh
    exact hh
  have hhi : (∫ z, Fend (y + delta z) ∂noise) ≤ G y + (Ce * w + g * d) := by
    have hh := integral_mono_ae hend.2.1
      ((integrable_const (G y)).add ((integrable_const (Ce * w)).add (hdi.const_mul g)))
      (hEndPoint.mono (fun z hz => by
        simp only [Pi.add_apply]
        linarith only [(abs_le.mp hz.2).2]))
    have i1 := integral_add (integrable_const (G y))
      ((integrable_const (Ce * w)).add (hdi.const_mul g))
    have i2 := integral_add (integrable_const (Ce * w)) (hdi.const_mul g)
    simp only [Pi.add_apply] at hh i1 i2
    rw [i1, i2] at hh
    simp only [integral_const_mul, integral_const, probReal_univ, one_smul, smul_eq_mul, mul_one, one_mul] at hh
    exact hh
  have hJend : |Jend y - G y| ≤ Ce * w + g * d + b :=
    abs_le.mpr ⟨by linarith only [hlo, hend.2.2.2.1], by linarith only [hhi, hend.2.2.2.2]⟩
  have hJmax : |Jmax y - G y| ≤ (Ce + Cs) * w + g * d + b := by
    calc
      _ ≤ |Jmax y - Jend y| + |Jend y - G y| := abs_sub_le _ _ _
      _ ≤ Cs * w + (Ce * w + g * d + b) := add_le_add (hSM y hygamma hyhalf) hJend
      _ = _ := by ring
  have hmax := hs.2.2.2.2.2 (fun v : Shao.Path n => Shao.maxWithZero v)
    Shao.measurable_maxWithZero y hylo hyy
  have habsmax : (fun u => P.real {v : Shao.Path n | 0 < Shao.energy v ∧
      |Shao.maxWithZero v| < u * Real.sqrt (Shao.energy v)}) = F := by
    funext u
    simp only [F, abs_of_nonneg (Shao.maxWithZero_nonneg _)]
  rw [habsmax] at hmax
  change Integrable (fun z => F (y - delta z)) noise ∧
    Integrable (fun z => F (y + delta z)) noise ∧
    Integrable (fun v => ∫ z, sourceFourierTest y (Shao.maxWithZero v + z.1, Shao.energy v + z.2) ∂noise) P ∧
    (∫ z, F (y - delta z) ∂noise) - b ≤ Jmax y ∧
    Jmax y ≤ (∫ z, F (y + delta z) ∂noise) + b at hmax
  have hFmono : Monotone F := by
    intro u v huv
    exact measureReal_mono
      (fun z hz => ⟨hz.1, hz.2.trans_le (mul_le_mul_of_nonneg_right huv (Real.sqrt_nonneg _))⟩)
      (measure_ne_top _ _)
  have hFbound (u : ℝ) : 0 ≤ F u ∧ F u ≤ 1 := ⟨measureReal_nonneg, measureReal_le_one⟩
  have hsand : (∫ z, s * (F (x + s * a - s * delta z) - G y) ∂noise) - b ≤
      s * (Jmax y - G y) := by
    rcases hsval with hs1 | hs1
    · have harg (z : ℝ × ℝ) : x + s * a - s * delta z = y - delta z := by dsimp [y]; rw [hs1]; ring
      simp_rw [harg]
      rw [hs1]
      simp only [one_mul]
      rw [integral_sub hmax.1 (integrable_const _), integral_const, probReal_univ, one_smul]
      linarith only [hmax.2.2.2.1]
    · have harg (z : ℝ × ℝ) : x + s * a - s * delta z = y + delta z := by dsimp [y]; rw [hs1]; ring
      simp_rw [harg]
      rw [hs1]
      simp only [neg_one_mul]
      rw [integral_neg, integral_sub hmax.2.1 (integrable_const _), integral_const, probReal_univ, one_smul]
      linarith only [hmax.2.2.2.2]
  have hconv := sourceSignedCDF_convolution_lower noise delta hdm hdi hd0 F G E hFmono hFbound
    x radius a s p w B (L * M) g b (Jmax y) hradius ha (by linarith only [halocal, hradius])
    hsval hsE hp hw hB (mul_nonneg (by linarith) hM) hg
    (hsupport.mono fun _ hz => by linarith only [hz, hradius]) hGlip hPB hE hsand
  have hsigned : s * (Jmax y - G y) ≤ (Ce + Cs) * w + g * d + b := by
    have hh : s * (Jmax y - G y) ≤ |Jmax y - G y| := by
      have hl := le_abs_self (s * (Jmax y - G y))
      simpa only [abs_mul, hsabs, one_mul] using hl
    exact hh.trans hJmax
  have hpay : g * (a + 2 * d) + 2 * b ≤ c * (K + 2) * D * w := by
    have hcoef : 2 ≤ c * (K + 2) := by nlinarith only [hc, hK]
    have hh := mul_le_mul_of_nonneg_left hcost (show 0 ≤ c * (K + 2) by positivity)
    have hbextra := mul_nonneg (show 0 ≤ c * (K + 2) - 2 by linarith only [hcoef]) hb
    dsimp only [g, a]
    nlinarith only [hh, hbextra]
  have hquot : ((1 - theta) * |E x| - theta * (L * M) * w) / p ≤ T0 * w := by
    change ((1 - theta) * |E x| - theta * (L * M) * w) / p ≤
      s * (Jmax y - G y) + B * w + g * (a + d) + b at hconv
    dsimp only [T0]
    nlinarith only [hconv, hsigned, hpay]
  have hraw : (1 - theta) * |E x| - theta * L * M * w ≤ T0 * w := by
    have hh := (div_le_iff₀ hp).1 hquot
    have hT0w : 0 ≤ T0 * w := mul_nonneg hT0 hw.le
    have hmul := mul_le_mul_of_nonneg_left hp1 hT0w
    nlinarith only [hh, hmul]
  have hthetamul : theta * (|E x| + L * M * w) ≤ (|E x| + L * M * w) / K := by
    have hh := mul_le_mul_of_nonneg_right htheta
      (show 0 ≤ |E x| + L * M * w by positivity)
    simpa only [one_div_mul_eq_div] using hh
  have hfinalmul : (K - 1) * |E x| ≤ (K * T0 + L * M) * w := by
    have hh : |E x| ≤ T0 * w + (|E x| + L * M * w) / K := by
      nlinarith only [hraw, hthetamul]
    have hh2 := mul_le_mul_of_nonneg_left hh hK0.le
    rw [mul_add, mul_div_cancel₀ _ hK0.ne'] at hh2
    nlinarith only [hh2]
  have hfirst : |E x| / w ≤ K / (K - 1) * T0 + L / (K - 1) * M := by
    apply (div_le_iff₀ hw).mpr
    calc
      |E x| ≤ ((K * T0 + L * M) * w) / (K - 1) :=
        (le_div_iff₀ (by linarith only [hK] : 0 < K - 1)).mpr (by nlinarith only [hfinalmul])
      _ = (K / (K - 1) * T0 + L / (K - 1) * M) * w := by
        field_simp
        <;> ring
  have hLM : L / (K - 1) ≤ 1 / 4 := by
    apply (div_le_iff₀ (by linarith only [hK] : 0 < K - 1)).mpr
    dsimp [K]
    linarith
  refine ⟨hfirst, ?_⟩
  change |E x| / w ≤ K / (K - 1) * T0 + M / 4
  have hh : L / (K - 1) * M ≤ M / 4 := by
    simpa only [one_div_mul_eq_div] using mul_le_mul_of_nonneg_right hLM hM
  linarith only [hfirst, hh]

theorem sourceWeight_enlarged_domain_compact
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (H rhoStar : ℝ) (hH : 0 ≤ H) (hrho : 0 < rhoStar) :
    let I : Set ℝ := {t | 0 ≤ t ∧
      (t ≤ H ∨ Shao.truncationBudget nu n t ≤ rhoStar)}
    let w : ℝ → ℝ := fun t =>
      Shao.truncationBudget nu n t * Shao.standardNormalTail t
    IsCompact I ∧ 0 ∈ I ∧ ContinuousOn w I ∧
      (∀ t : ℝ, t ∈ I → 0 < w t) ∧
      ∃ m : ℝ, 0 < m ∧ ∀ t : ℝ, t ∈ I → m ≤ w t := by
  classical
  dsimp only
  let I : Set ℝ := {t | 0 ≤ t ∧ (t ≤ H ∨ Shao.truncationBudget nu n t ≤ rhoStar)}
  let w : ℝ → ℝ := fun t => Shao.truncationBudget nu n t * Shao.standardNormalTail t
  have hzero : (0 : ℝ) ∈ I := ⟨le_rfl, Or.inl hH⟩
  have hR := Shao.continuousOn_truncationBudget nu n h2
  have hclosed : IsClosed I := by
    have heq : I = Set.Icc 0 H ∪
        {t ∈ Set.Ici (0 : ℝ) | Shao.truncationBudget nu n t ≤ rhoStar} := by
      ext t
      simp only [I, Set.mem_setOf_eq, Set.mem_union, Set.mem_Icc, Set.mem_Ici]
      tauto
    rw [heq]
    exact isClosed_Icc.union (isClosed_Ici.isClosed_le hR continuousOn_const)
  have hlim := Shao.tendsto_truncationBudget_div_sq_of_normalized_second nu n h2 hnorm
  have hevent : ∀ᶠ t : ℝ in Filter.atTop,
      (1 / 2 : ℝ) < Shao.truncationBudget nu n t / (1 + t) ^ 2 :=
    (tendsto_order.1 hlim).1 _ (by norm_num)
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 hevent
  let U : ℝ := max H (max T (2 * rhoStar + 2))
  have hsub : I ⊆ Set.Icc 0 U := by
    intro t ht
    refine ⟨ht.1, ?_⟩
    rcases ht.2 with htH | htR
    · exact htH.trans (le_max_left _ _)
    · by_contra hnot
      have hUt : U < t := lt_of_not_ge hnot
      have htT : T ≤ t := (le_max_left T _).trans ((le_max_right H _).trans hUt.le)
      have htrho : 2 * rhoStar + 2 < t :=
        (le_max_right T _).trans_lt ((le_max_right H _).trans_lt hUt)
      have hden : 0 < (1 + t) ^ 2 := sq_pos_of_pos (by linarith [ht.1])
      have hh := (lt_div_iff₀ hden).1 (hT t htT)
      nlinarith [sq_nonneg t]
  have hcompact : IsCompact I := isCompact_Icc.of_isClosed_subset hclosed hsub
  have hn : 0 < n := by
    by_contra hh
    have hn0 : n = 0 := by omega
    simp [hn0] at hnorm
  have hsecond : 0 < ∫ z : ℝ, z ^ 2 ∂nu := by
    have hnon : 0 ≤ ∫ z : ℝ, z ^ 2 ∂nu := integral_nonneg (fun z : ℝ => sq_nonneg z)
    have hN : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    nlinarith only [hnorm, hnon, hN]
  have hwp (t : ℝ) (ht : t ∈ I) : 0 < w t :=
    mul_pos (Shao.truncationBudget_pos nu n h2 hn hsecond t ht.1)
      (Shao.standardNormalTail_basic.2.2.1 t).1
  have hwc : ContinuousOn w I :=
    (hR.mono fun (t : ℝ) (ht : t ∈ I) => ht.1).mul
      (continuous_iff_continuousAt.mpr (fun t =>
        (Shao.standardNormal_derivatives t).2.continuousAt)).continuousOn
  obtain ⟨t0, ht0, hmin⟩ := hcompact.exists_isMinOn ⟨0, hzero⟩ hwc
  exact ⟨hcompact, hzero, hwc, hwp, w t0, hwp t0 ht0, fun t ht => hmin ht⟩

theorem sourceWeight_compact_supremum_absorption
    (I : Set ℝ) (hI : IsCompact I) (E w : ℝ → ℝ)
    (hwc : ContinuousOn w I) (hwp : ∀ t : ℝ, t ∈ I → 0 < w t)
    (hEb : ∀ t : ℝ, t ∈ I → |E t| ≤ 1) :
    let ratios : Set ℝ := {v | ∃ t : ℝ, t ∈ I ∧ 0 < t ∧ v = |E t| / w t}
    let M : ℝ := sSup (Set.insert 0 ratios)
    BddAbove ratios ∧ BddAbove (Set.insert 0 ratios) ∧ 0 ≤ M ∧
      (∀ t : ℝ, t ∈ I → 0 < t → |E t| ≤ M * w t) ∧
      (ratios.Nonempty → M = sSup ratios) ∧
      (∀ C : ℝ, 0 ≤ C →
        (∀ t : ℝ, t ∈ I → 0 < t → |E t| / w t ≤ C + M / 4) →
        M ≤ 4 * C / 3) := by
  classical
  dsimp only
  let ratios : Set ℝ := {v | ∃ t : ℝ, t ∈ I ∧ 0 < t ∧ v = |E t| / w t}
  let M : ℝ := sSup (Set.insert 0 ratios)
  have hb : BddAbove ratios := by
    by_cases hne : I.Nonempty
    · obtain ⟨t0, ht0, hmin⟩ := hI.exists_isMinOn hne hwc
      refine ⟨1 / w t0, ?_⟩
      rintro v ⟨t, ht, htp, rfl⟩
      exact (div_le_div_of_nonneg_right (hEb t ht) (hwp t ht).le).trans
        (one_div_le_one_div_of_le (hwp t0 ht0) (hmin ht))
    · refine ⟨0, ?_⟩
      rintro v ⟨t, ht, htp, hv⟩
      exact False.elim (hne ⟨t, ht⟩)
  have hbi : BddAbove (Set.insert 0 ratios) := hb.insert 0
  have hM : 0 ≤ M := le_csSup hbi (Set.mem_insert _ _)
  have hpoint (t : ℝ) (ht : t ∈ I) (htp : 0 < t) : |E t| ≤ M * w t := by
    apply (div_le_iff₀ (hwp t ht)).mp
    exact le_csSup hbi (Set.mem_insert_of_mem _ ⟨t, ht, htp, rfl⟩)
  refine ⟨hb, hbi, hM, hpoint, ?_, ?_⟩
  · intro hne
    apply le_antisymm
    · apply csSup_le (Set.insert_nonempty _ _)
      intro v hv
      rcases hv with rfl | hv
      · obtain ⟨u, hu⟩ := hne
        rcases hu with ⟨t, ht, htp, rfl⟩
        exact (div_nonneg (abs_nonneg _) (hwp t ht).le).trans (le_csSup hb ⟨t, ht, htp, rfl⟩)
      · exact le_csSup hb hv
    · apply csSup_le hne
      intro v hv
      exact le_csSup hbi (Set.mem_insert_of_mem _ hv)
  · intro C hC hbound
    have h : M ≤ C + M / 4 := by
      apply csSup_le (Set.insert_nonempty _ _)
      intro v hv
      rcases hv with rfl | ⟨t, ht, htp, rfl⟩
      · linarith
      · exact hbound t ht htp
    linarith

theorem sourcePositiveCDF_weak_tail_error_identity
    {n : ℕ} (hn : 0 < n) (P : Measure (Shao.Path n)) [IsProbabilityMeasure P]
    (t : ℝ) (ht : 0 < t) :
    let G : ℝ := 1 - 2 * Shao.standardNormalTail t
    let F : ℝ := P.real {v : Shao.Path n |
      0 < Shao.energy v ∧ Shao.maxWithZero v < t * Real.sqrt (Shao.energy v)}
    F - G = 2 * Shao.standardNormalTail t - P.real (Shao.upperCrossing hn t) ∧
      |F - G| / Shao.standardNormalTail t =
        |P.real (Shao.upperCrossing hn t) / Shao.standardNormalTail t - 2| := by
  dsimp only
  have heq : {v : Shao.Path n | 0 < Shao.energy v ∧
      Shao.maxWithZero v < t * Real.sqrt (Shao.energy v)} =
      (Shao.upperCrossing hn t)ᶜ := by
    ext v
    rw [Set.mem_setOf_eq, Set.mem_compl_iff, Shao.upperCrossing, Set.mem_setOf_eq, not_le]
    constructor
    · rintro ⟨hQ, hmax⟩
      rw [Shao.maxWithZero_eq v hn] at hmax
      exact (le_max_right _ _).trans_lt hmax
    · intro hmax
      have hQ : 0 < Shao.energy v := by
        by_contra hh
        have hz : Shao.energy v = 0 := le_antisymm (le_of_not_gt hh) (Shao.energy_nonneg v)
        rw [Shao.upperMax_eq_zero_of_energy_eq_zero v hn hz, hz] at hmax
        simpa using hmax
      refine ⟨hQ, ?_⟩
      rw [Shao.maxWithZero_eq v hn, max_lt_iff]
      exact ⟨mul_pos ht (Real.sqrt_pos.2 hQ), hmax⟩
  have hprob : P.real {v : Shao.Path n | 0 < Shao.energy v ∧
      Shao.maxWithZero v < t * Real.sqrt (Shao.energy v)} =
      1 - P.real (Shao.upperCrossing hn t) := by
    rw [heq, measureReal_compl (Shao.measurableSet_upperCrossing hn t), probReal_univ]
  constructor
  · rw [hprob]
    ring
  · rw [hprob]
    have hT := (Shao.standardNormalTail_basic.2.2.1 t).1
    calc
      _ = |2 * Shao.standardNormalTail t - P.real (Shao.upperCrossing hn t)| /
          Shao.standardNormalTail t := by congr 2 <;> ring
      _ = |(2 * Shao.standardNormalTail t - P.real (Shao.upperCrossing hn t)) /
          Shao.standardNormalTail t| := by rw [abs_div, abs_of_pos hT]
      _ = |2 - P.real (Shao.upperCrossing hn t) / Shao.standardNormalTail t| := by
        congr 1
        field_simp
      _ = _ := abs_sub_comm _ _

end Shao.Probability
