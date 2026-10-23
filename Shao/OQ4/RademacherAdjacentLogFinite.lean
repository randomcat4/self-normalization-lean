import Shao.OQ4.RademacherS2Assembly
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Offline proof-body candidate for the exact frozen A1 subset.
NOT_ELABORATED / NOT_SERVER_CHECKED. No public theorem is included.
The finite probability/logarithm theorem and all other proposed units remain open.
-/

noncomputable section
open scoped BigOperators Topology

namespace Shao.OQ4.RademacherAdjacentLogFinite

private def gamma : ℝ := Real.pi ^ 2 / 16
private def qGeom : ℝ := Real.exp (-gamma)
private def sumConst : ℝ := 1 / (1 - qGeom) ^ 2
private def coeffA : ℝ := Real.pi ^ 2 / 2 + 2
private def coeffB : ℝ := Real.sqrt 2 * Real.pi ^ 2 / 4
private def derivConst : ℝ := (coeffA + 2 * coeffB) * sumConst
private def negConst : ℝ := (Real.pi ^ 2 / 4) * sumConst
private def ampConst : ℝ := 1 + Real.pi / Real.sqrt 2
private def finalConst : ℝ := ampConst + Real.pi ^ 2 / 2 + 2 * derivConst + 4 * negConst

private theorem constants_spec :
    0 < gamma ∧ 0 < qGeom ∧ qGeom < 1 ∧ 0 < sumConst ∧
    0 < coeffA ∧ 0 < coeffB ∧ 0 < derivConst ∧ 0 < negConst ∧
    0 < ampConst ∧ 0 < finalConst := by
  have hg : 0 < gamma := by
    dsimp only [gamma]
    positivity
  have hq0 : 0 < qGeom := Real.exp_pos _
  have hq1 : qGeom < 1 := by
    change Real.exp (-gamma) < 1
    simpa only [Real.exp_zero] using
      (Real.exp_lt_exp.mpr (show -gamma < 0 by linarith))
  have hgap : 0 < 1 - qGeom := sub_pos.mpr hq1
  have hS : 0 < sumConst := by
    dsimp only [sumConst]
    positivity
  have hA : 0 < coeffA := by
    dsimp only [coeffA]
    positivity
  have hB : 0 < coeffB := by
    dsimp only [coeffB]
    positivity
  have hD : 0 < derivConst := by
    dsimp only [derivConst]
    positivity
  have hE : 0 < negConst := by
    dsimp only [negConst]
    positivity
  have hL : 0 < ampConst := by
    dsimp only [ampConst]
    positivity
  have hC : 0 < finalConst := by
    dsimp only [finalConst]
    positivity
  exact ⟨hg, hq0, hq1, hS, hA, hB, hD, hE, hL, hC⟩

private theorem half_angle_bounds {y : ℝ} (hy0 : 0 ≤ y) (hy : y < Real.pi / 2) :
    Real.sin y ≤ y ∧ (2 / Real.pi) * y ≤ Real.sin y ∧ y ≤ Real.tan y := by
  exact ⟨Real.sin_le hy0, Real.mul_le_sin hy0 hy.le, Real.le_tan hy0 hy⟩

private theorem quarter_angle_bounds {y : ℝ} (hy0 : 0 < y) (hy : y ≤ Real.pi / 4) :
    1 / Real.sqrt 2 ≤ Real.cos y ∧ Real.tan y ≤ 2 * y ∧
    Real.cos y / Real.sin y ≤ 1 / y ∧
    1 / Real.sin y ^ 2 ≤ Real.pi ^ 2 / (4 * y ^ 2) ∧
    1 / Real.cos y ^ 2 ≤ 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hyhalf : y < Real.pi / 2 := by linarith
  have hsinpos : 0 < Real.sin y :=
    Real.sin_pos_of_pos_of_lt_pi hy0 (by linarith)
  have hsqrtpos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt_one : (1 : ℝ) ≤ Real.sqrt 2 := by
    simpa only [Real.sqrt_one] using
      (Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 2 by norm_num))
  have hcos : Real.sqrt 2 / 2 ≤ Real.cos y := by
    simpa only [Real.cos_pi_div_four] using
      (Real.cos_le_cos_of_nonneg_of_le_pi hy0.le
        (show Real.pi / 4 ≤ Real.pi by linarith) hy)
  have hcospos : 0 < Real.cos y := by linarith
  have hcoshalf : (1 / 2 : ℝ) ≤ Real.cos y := by linarith
  rcases half_angle_bounds hy0.le hyhalf with ⟨hsinle, hchord, htange⟩
  have hcosrecip : 1 / Real.sqrt 2 ≤ Real.cos y := by
    apply (div_le_iff₀ hsqrtpos).2
    have hmul := mul_le_mul_of_nonneg_right hcos hsqrtpos.le
    nlinarith
  have htanle : Real.tan y ≤ 2 * y := by
    rw [Real.tan_eq_sin_div_cos]
    apply (div_le_iff₀ hcospos).2
    nlinarith [mul_nonneg hy0.le (sub_nonneg.mpr hcoshalf)]
  have hcotle : Real.cos y / Real.sin y ≤ 1 / y := by
    apply (div_le_div_iff₀ hsinpos hy0).2
    have htanratio : y ≤ Real.sin y / Real.cos y := by
      simpa only [Real.tan_eq_sin_div_cos] using htange
    have hmul := (le_div_iff₀ hcospos).mp htanratio
    nlinarith
  have hchordmul : 2 * y ≤ Real.pi * Real.sin y := by
    calc
      2 * y = Real.pi * ((2 / Real.pi) * y) := by
        field_simp [ne_of_gt hpi] <;> ring
      _ ≤ Real.pi * Real.sin y := mul_le_mul_of_nonneg_left hchord hpi.le
  have hcsc : 1 / Real.sin y ^ 2 ≤ Real.pi ^ 2 / (4 * y ^ 2) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hsinpos)
      (mul_pos (show (0 : ℝ) < 4 by norm_num) (sq_pos_of_pos hy0))).2
    have hmul := mul_nonneg (sub_nonneg.mpr hchordmul)
      (show 0 ≤ Real.pi * Real.sin y + 2 * y by positivity)
    nlinarith
  have hsec : 1 / Real.cos y ^ 2 ≤ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hcospos)).2
    have hmul := mul_nonneg (sub_nonneg.mpr hcos)
      (show 0 ≤ Real.cos y + Real.sqrt 2 / 2 by positivity)
    nlinarith
  exact ⟨hcosrecip, htanle, hcotle, hcsc, hsec⟩

private theorem log_cos_drop {v y : ℝ} (hv : 0 < v) (hvy : v ≤ y)
    (hy : y < Real.pi / 2) :
    Real.log (Real.cos y) - Real.log (Real.cos v) ≤ -(y ^ 2 - v ^ 2) / 2 := by
  rcases lt_or_eq_of_le hvy with hlt | heq
  · let f : ℝ → ℝ := fun s => Real.log (Real.cos s) + s ^ 2 / 2
    have hdf : ∀ s ∈ Set.Icc v y, HasDerivAt f (-Real.tan s + s) s := by
      intro s hs
      have hc : 0 < Real.cos s := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hs.1, Real.pi_pos], lt_of_le_of_lt hs.2 hy⟩
      have hlog : HasDerivAt (fun t : ℝ => Real.log (Real.cos t)) (-Real.tan s) s := by
        simpa only [Real.tan_eq_sin_div_cos, neg_div] using
          (Real.hasDerivAt_cos s).log (ne_of_gt hc)
      have hsq : HasDerivAt (fun t : ℝ => t ^ 2 / 2) s s := by
        convert ((hasDerivAt_id s).pow 2).div_const (2 : ℝ) using 1 <;> norm_num <;> ring
      exact hlog.add hsq
    have hf : ContinuousOn f (Set.Icc v y) := by
      intro s hs
      exact (hdf s hs).continuousAt.continuousWithinAt
    obtain ⟨s, hs, hsecant⟩ :=
      exists_hasDerivAt_eq_slope f (fun s => -Real.tan s + s) hlt hf
        (fun s hs => hdf s ⟨hs.1.le, hs.2.le⟩)
    have htan : s ≤ Real.tan s := Real.le_tan (by linarith [hs.1]) (lt_trans hs.2 hy)
    have hslope : (f y - f v) / (y - v) ≤ 0 := by
      rw [← hsecant]
      linarith
    have hdiff : f y - f v ≤ 0 := by
      have hmul := (div_le_iff₀ (sub_pos.mpr hlt)).mp hslope
      simpa only [zero_mul] using hmul
    dsimp only [f] at hdiff
    linarith
  · subst y
    simp

private theorem finite_weighted_geom_identity (R : ℕ) {q : ℝ} (hq : q ≠ 1) :
    (∑ j ∈ Finset.range R, ((j : ℝ) + 1) * q ^ j) =
      (1 - ((R : ℝ) + 1) * q ^ R + (R : ℝ) * q ^ (R + 1)) / (1 - q) ^ 2 := by
  have hden : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  induction R with
  | zero => simp
  | succ R ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      simp only [pow_succ]
      field_simp [hden] <;> ring

private theorem finite_weighted_geom_le (I : Finset ℕ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hI : ∀ r ∈ I, 1 ≤ r) :
    (∑ r ∈ I, (r : ℝ) * q ^ (r - 1)) ≤ 1 / (1 - q) ^ 2 := by
  classical
  let R : ℕ := I.sup id
  have hsub : I ⊆ Finset.range (R + 1) := by
    intro r hr
    apply Finset.mem_range.mpr
    have hrle : r ≤ R := Finset.le_sup (f := id) hr
    exact Nat.lt_succ_of_le hrle
  have hembed :
      (∑ r ∈ I, (r : ℝ) * q ^ (r - 1)) ≤
        ∑ r ∈ Finset.range (R + 1), (r : ℝ) * q ^ (r - 1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro r hr hnot
    exact mul_nonneg (Nat.cast_nonneg r) (pow_nonneg hq0 _)
  have hshift :
      (∑ r ∈ Finset.range (R + 1), (r : ℝ) * q ^ (r - 1)) =
        ∑ j ∈ Finset.range R, ((j : ℝ) + 1) * q ^ j := by
    simpa using
      (Finset.sum_range_succ' (fun r : ℕ => (r : ℝ) * q ^ (r - 1)) R)
  have hden : 0 < (1 - q) ^ 2 := sq_pos_of_pos (sub_pos.mpr hq1)
  have hfactor : 0 ≤ q ^ R * (1 + (R : ℝ) * (1 - q)) := by
    have hgap : 0 ≤ 1 - q := sub_nonneg.mpr hq1.le
    positivity
  have hnum : 1 - ((R : ℝ) + 1) * q ^ R + (R : ℝ) * q ^ (R + 1) ≤ 1 := by
    rw [pow_succ]
    nlinarith
  calc
    (∑ r ∈ I, (r : ℝ) * q ^ (r - 1)) ≤
        ∑ j ∈ Finset.range R, ((j : ℝ) + 1) * q ^ j := by
      simpa only [hshift] using hembed
    _ = (1 - ((R : ℝ) + 1) * q ^ R + (R : ℝ) * q ^ (R + 1)) / (1 - q) ^ 2 :=
      finite_weighted_geom_identity R (ne_of_lt hq1)
    _ ≤ 1 / (1 - q) ^ 2 := by
      apply (div_le_div_iff₀ hden hden).2
      exact mul_le_mul_of_nonneg_right hnum hden.le

private theorem finite_gaussian_sum_le (I : Finset ℕ) (hI : ∀ r ∈ I, 1 ≤ r) :
    (∑ r ∈ I, (r : ℝ) * Real.exp (-gamma * ((r : ℝ) ^ 2 - 1))) ≤ sumConst := by
  rcases constants_spec with ⟨hg, hq0, hq1, hS, hA, hB, hD, hE, hL, hC⟩
  have hexp_pow : ∀ n : ℕ, Real.exp (-gamma * (n : ℝ)) = qGeom ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Nat.cast_succ, mul_add, mul_one, Real.exp_add, ih, pow_succ]
        rfl
  have hterm : ∀ r ∈ I,
      (r : ℝ) * Real.exp (-gamma * ((r : ℝ) ^ 2 - 1)) ≤
        (r : ℝ) * qGeom ^ (r - 1) := by
    intro r hr
    have hrnat : 1 ≤ r := hI r hr
    have hrreal : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrnat
    have hpoly : ((r - 1 : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 - 1 := by
      rw [Nat.cast_sub hrnat, Nat.cast_one]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ (r : ℝ) by positivity)
        (sub_nonneg.mpr hrreal)]
    apply mul_le_mul_of_nonneg_left _ (show (0 : ℝ) ≤ (r : ℝ) by positivity)
    calc
      Real.exp (-gamma * ((r : ℝ) ^ 2 - 1)) ≤
          Real.exp (-gamma * ((r - 1 : ℕ) : ℝ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hpoly hg.le]
      _ = qGeom ^ (r - 1) := hexp_pow (r - 1)
  calc
    (∑ r ∈ I, (r : ℝ) * Real.exp (-gamma * ((r : ℝ) ^ 2 - 1))) ≤
        ∑ r ∈ I, (r : ℝ) * qGeom ^ (r - 1) := Finset.sum_le_sum hterm
    _ ≤ sumConst := by
      simpa only [sumConst] using finite_weighted_geom_le I hq0.le hq1 hI

-- Cumulative offline A1 + B1 candidate; B1 definitions and proofs follow.
private def uReal (x : ℝ) : ℝ := Real.pi / (4 * x)
private def vReal (x : ℝ) : ℝ := Real.pi / (2 * x)
private def aReal (x : ℝ) : ℝ := (Real.cos (uReal x) / Real.sin (uReal x)) / x
private def rhoReal (x : ℝ) : ℝ := Real.cos (vReal x)
private def modeSign (r : ℕ) : ℝ := (-1 : ℝ) ^ ((r - 1) / 2)
private def oddIndices (H : ℕ) : Finset ℕ :=
  (Finset.range H).filter (fun r => 1 ≤ r ∧ Odd r)
private def cMode (r : ℕ) (x : ℝ) : ℝ :=
  Real.tan (uReal x) * (Real.cos ((r : ℝ) * uReal x) / Real.sin ((r : ℝ) * uReal x))
private def dMode (r : ℕ) (x : ℝ) : ℝ :=
  Real.tan (uReal x) * Real.tan ((r : ℝ) * uReal x)
private def bMode (N r : ℕ) (x : ℝ) : ℝ :=
  (Real.cos ((r : ℝ) * vReal x) / Real.cos (vReal x)) ^ N
private def positivePart (N H : ℕ) : ℝ :=
  ∑ r ∈ oddIndices H, modeSign r * cMode r (H : ℝ) * bMode N r (H : ℝ)
private def negativePart (N H : ℕ) : ℝ :=
  (-1 : ℝ) ^ (N + (H - 1)) *
    ∑ r ∈ oddIndices H, modeSign r * dMode r (H : ℝ) * bMode N r (H : ℝ)
private def normalizer (N : ℕ) (x : ℝ) : ℝ := aReal x * rhoReal x ^ N
private def normalizedActual (N H : ℕ) : ℝ :=
  Shao.OQ4.RademacherS2Assembly.p N ((H : ℝ) - 1) / normalizer N (H : ℝ)

private theorem oddIndices_spec (H r : ℕ) :
    r ∈ oddIndices H ↔ 1 ≤ r ∧ Odd r ∧ r < H := by
  simp only [oddIndices, Finset.mem_filter, Finset.mem_range]
  tauto

private theorem lowerModes_image {H : ℕ} (hH : 2 ≤ H) :
    (Shao.OQ4.RademacherSpectralPairing.lowerModes (H - 1)).image
      (fun ell => 2 * ell + 1) = oddIndices H := by
  classical
  ext r
  rw [Finset.mem_image, oddIndices_spec]
  constructor
  · rintro ⟨ell, hell, rfl⟩
    have hell' := (Shao.OQ4.RademacherSpectralPairing.mem_lowerModes (H - 1) ell).mp hell
    refine ⟨by omega, ⟨ell, by omega⟩, by omega⟩
  · rintro ⟨hr, ⟨ell, heq⟩, hrH⟩
    refine ⟨ell, ?_, by omega⟩
    rw [Shao.OQ4.RademacherSpectralPairing.mem_lowerModes]
    omega

private theorem scalar_bridge {H : ℕ} (hH : 2 ≤ H) :
    aReal (H : ℝ) = Shao.OQ4.RademacherSpectralPairing.amplitude (H - 1) ∧
    rhoReal (H : ℝ) = Shao.OQ4.RademacherSpectralPairing.rho (H - 1) := by
  have hcast : ((H - 1 : ℕ) : ℝ) + 1 = (H : ℝ) := by
    rw [Nat.cast_sub (show 1 ≤ H by omega), Nat.cast_one]
    ring
  constructor
  · dsimp only [aReal, uReal, Shao.OQ4.RademacherSpectralPairing.amplitude,
      Shao.OQ4.RademacherFiniteS1.cotangent]
    rw [hcast]
    ring
  · dsimp only [rhoReal, vReal, Shao.OQ4.RademacherSpectralPairing.rho]
    rw [hcast]

private theorem real_angle_domain {x : ℝ} {r : ℕ} (hx : 2 ≤ x)
    (hr : 1 ≤ r) (hrx : (r : ℝ) ≤ x) :
    0 < uReal x ∧ uReal x ≤ Real.pi / 8 ∧
    0 < vReal x ∧ vReal x ≤ Real.pi / 4 ∧
    0 < (r : ℝ) * uReal x ∧ (r : ℝ) * uReal x ≤ Real.pi / 4 ∧
    0 < (r : ℝ) * vReal x ∧ (r : ℝ) * vReal x ≤ Real.pi / 2 ∧
    0 < Real.sin ((r : ℝ) * uReal x) ∧ 0 < Real.cos (vReal x) := by
  have hxp : 0 < x := by linarith
  have hrp : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hu0 : 0 < uReal x := by dsimp only [uReal]; positivity
  have hv0 : 0 < vReal x := by dsimp only [vReal]; positivity
  have hu : uReal x ≤ Real.pi / 8 := by
    dsimp only [uReal]
    apply (div_le_iff₀ (show 0 < 4 * x by positivity)).2
    nlinarith [mul_nonneg hpi.le (sub_nonneg.mpr hx)]
  have hv : vReal x ≤ Real.pi / 4 := by
    dsimp only [vReal]
    apply (div_le_iff₀ (show 0 < 2 * x by positivity)).2
    nlinarith [mul_nonneg hpi.le (sub_nonneg.mpr hx)]
  have hru : (r : ℝ) * uReal x ≤ Real.pi / 4 := by
    dsimp only [uReal]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < 4 * x by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_right hrx hpi.le]
  have hrv : (r : ℝ) * vReal x ≤ Real.pi / 2 := by
    dsimp only [vReal]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < 2 * x by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_right hrx hpi.le]
  have hru0 : 0 < (r : ℝ) * uReal x := mul_pos hrp hu0
  have hrv0 : 0 < (r : ℝ) * vReal x := mul_pos hrp hv0
  have hsin : 0 < Real.sin ((r : ℝ) * uReal x) :=
    Real.sin_pos_of_pos_of_lt_pi hru0 (by linarith)
  have hcos : 0 < Real.cos (vReal x) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  exact ⟨hu0, hu, hv0, hv, hru0, hru, hrv0, hrv, hsin, hcos⟩

private theorem scalar_positive {x : ℝ} (hx : 2 ≤ x) (N : ℕ) :
    0 < aReal x ∧ 0 < rhoReal x ∧ 0 < normalizer N x := by
  rcases real_angle_domain (r := 1) hx (by norm_num) (by norm_num; linarith) with
    ⟨hu0, hu, hv0, hv, hru0, hru, hrv0, hrv, hsin, hcosv⟩
  have hsinu : 0 < Real.sin (uReal x) := by simpa only [Nat.cast_one, one_mul] using hsin
  have hcosu : 0 < Real.cos (uReal x) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hxp : 0 < x := by linarith
  have ha : 0 < aReal x := by
    dsimp only [aReal]
    exact div_pos (div_pos hcosu hsinu) hxp
  have hrho : 0 < rhoReal x := hcosv
  refine ⟨ha, hrho, ?_⟩
  dsimp only [normalizer]
  exact mul_pos ha (pow_pos hrho N)

private theorem mode_bounds {x : ℝ} {r : ℕ} (hx : 2 ≤ x)
    (hr : 1 ≤ r) (hrx : (r : ℝ) ≤ x) :
    0 < cMode r x ∧ cMode r x ≤ 2 / (r : ℝ) ∧
    0 < dMode r x ∧ dMode r x ≤ Real.pi ^ 2 * (r : ℝ) / (4 * x ^ 2) := by
  rcases real_angle_domain hx hr hrx with
    ⟨hu0, hu, hv0, hv, hru0, hru, hrv0, hrv, hsinru, hcosv⟩
  have hxp : 0 < x := by linarith
  have hrp : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have huq : uReal x ≤ Real.pi / 4 := by linarith [Real.pi_pos]
  have hsinu : 0 < Real.sin (uReal x) :=
    Real.sin_pos_of_pos_of_lt_pi hu0 (by linarith [Real.pi_pos])
  have hcosu : 0 < Real.cos (uReal x) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hcosru : 0 < Real.cos ((r : ℝ) * uReal x) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have htanu : 0 < Real.tan (uReal x) := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hsinu hcosu
  have htanru : 0 < Real.tan ((r : ℝ) * uReal x) := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hsinru hcosru
  rcases quarter_angle_bounds hu0 huq with ⟨hcu, htu, hcot, hcsc, hsec⟩
  rcases quarter_angle_bounds hru0 hru with ⟨hcru, htru, hcotru, hcscru, hsecru⟩
  have hcp : 0 < cMode r x := mul_pos htanu (div_pos hcosru hsinru)
  have hdp : 0 < dMode r x := mul_pos htanu htanru
  have hcub : cMode r x ≤ 2 / (r : ℝ) := by
    calc
      cMode r x ≤ (2 * uReal x) * (1 / ((r : ℝ) * uReal x)) :=
        mul_le_mul htu hcotru (div_pos hcosru hsinru).le (by positivity)
      _ = 2 / (r : ℝ) := by
        field_simp [ne_of_gt hu0, ne_of_gt hrp] <;> ring
  have hdub : dMode r x ≤ Real.pi ^ 2 * (r : ℝ) / (4 * x ^ 2) := by
    calc
      dMode r x ≤ (2 * uReal x) * (2 * ((r : ℝ) * uReal x)) :=
        mul_le_mul htu htru htanru.le (by positivity)
      _ = Real.pi ^ 2 * (r : ℝ) / (4 * x ^ 2) := by
        dsimp only [uReal]
        field_simp [ne_of_gt hxp] <;> ring
  exact ⟨hcp, hcub, hdp, hdub⟩

private theorem mode_decay {N r : ℕ} {x : ℝ} (hN : 1 ≤ N) (hx : 2 ≤ x)
    (hr : 1 ≤ r) (hrx : (r : ℝ) ≤ x) :
    0 ≤ bMode N r x ∧
    bMode N r x ≤ Real.exp (-2 * gamma * ((r : ℝ) ^ 2 - 1) * ((N : ℝ) / x ^ 2)) := by
  rcases real_angle_domain hx hr hrx with
    ⟨hu0, hu, hv0, hv, hru0, hru, hrv0, hrv, hsinru, hcosv⟩
  have hxp : 0 < x := by linarith
  have hrone : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hcosrv : 0 ≤ Real.cos ((r : ℝ) * vReal x) := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi hrv0.le
      (show Real.pi / 2 ≤ Real.pi by linarith [Real.pi_pos]) hrv
    simpa only [Real.cos_pi_div_two] using h
  have hb0 : 0 ≤ bMode N r x := pow_nonneg (div_nonneg hcosrv hcosv.le) N
  refine ⟨hb0, ?_⟩
  have hxv : x * vReal x = Real.pi / 2 := by
    dsimp only [vReal]
    field_simp [ne_of_gt hxp] <;> ring
  rcases lt_or_eq_of_le hrx with hrlt | hreq
  · have hrvlt : (r : ℝ) * vReal x < Real.pi / 2 := by
      have h := mul_lt_mul_of_pos_right hrlt hv0
      linarith
    have hcosrvp : 0 < Real.cos ((r : ℝ) * vReal x) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hrvlt⟩
    have hvle : vReal x ≤ (r : ℝ) * vReal x := by
      nlinarith [mul_le_mul_of_nonneg_right hrone hv0.le]
    have hlog := log_cos_drop hv0 hvle hrvlt
    have hbp : 0 < bMode N r x := pow_pos (div_pos hcosrvp hcosv) N
    apply (Real.log_le_iff_le_exp hbp).mp
    rw [bMode, Real.log_pow, Real.log_div (ne_of_gt hcosrvp) (ne_of_gt hcosv)]
    calc
      (N : ℝ) * (Real.log (Real.cos ((r : ℝ) * vReal x)) - Real.log (Real.cos (vReal x))) ≤
          (N : ℝ) * (-(((r : ℝ) * vReal x) ^ 2 - vReal x ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = -2 * gamma * ((r : ℝ) ^ 2 - 1) * ((N : ℝ) / x ^ 2) := by
        dsimp only [gamma, vReal]
        field_simp [ne_of_gt hxp] <;> ring
  · have hendpoint : (r : ℝ) * vReal x = Real.pi / 2 := by rw [hreq]; exact hxv
    have hbzero : bMode N r x = 0 := by
      simp only [bMode, hendpoint, Real.cos_pi_div_two, zero_div,
        zero_pow (show N ≠ 0 by omega)]
    rw [hbzero]
    exact (Real.exp_pos _).le

private theorem first_mode {x : ℝ} (hx : 2 ≤ x) (N : ℕ) :
    modeSign 1 = 1 ∧ cMode 1 x = 1 ∧ bMode N 1 x = 1 := by
  rcases real_angle_domain (r := 1) hx (by norm_num) (by norm_num; linarith) with
    ⟨hu0, hu, hv0, hv, hru0, hru, hrv0, hrv, hsin, hcosv⟩
  have hsinu : 0 < Real.sin (uReal x) := by simpa only [Nat.cast_one, one_mul] using hsin
  have hcosu : 0 < Real.cos (uReal x) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  refine ⟨by norm_num [modeSign], ?_, ?_⟩
  · dsimp only [cMode]
    simp only [Nat.cast_one, one_mul, Real.tan_eq_sin_div_cos]
    field_simp [ne_of_gt hsinu, ne_of_gt hcosu] <;> ring
  · simp only [bMode, Nat.cast_one, one_mul, div_self (ne_of_gt hcosv), one_pow]

private theorem modeSign_abs (r : ℕ) : |modeSign r| = 1 := by
  simp only [modeSign, abs_pow, abs_neg, abs_one, one_pow]

private theorem pairedTerm_normalized {H N ell : ℕ} (hH : 2 ≤ H)
    (hell : ell ∈ Shao.OQ4.RademacherSpectralPairing.lowerModes (H - 1)) :
    Shao.OQ4.RademacherSpectralPairing.pairedTerm (H - 1) N ell / (H : ℝ) =
      normalizer N (H : ℝ) * modeSign (2 * ell + 1) *
        (cMode (2 * ell + 1) (H : ℝ) +
          (-1 : ℝ) ^ (N + (H - 1)) * dMode (2 * ell + 1) (H : ℝ)) *
        bMode N (2 * ell + 1) (H : ℝ) := by
  have hHreal : (2 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hHp : (0 : ℝ) < (H : ℝ) := by linarith
  have hell' := (Shao.OQ4.RademacherSpectralPairing.mem_lowerModes (H - 1) ell).mp hell
  have hrH : 2 * ell + 1 < H := by omega
  have hrx : ((2 * ell + 1 : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast hrH.le
  rcases real_angle_domain hHreal (show 1 ≤ 2 * ell + 1 by omega) hrx with
    ⟨hu0, hu, hv0, hv, hru0, hru, hrv0, hrv, hsinru, hcosv⟩
  have hsinu : 0 < Real.sin (uReal (H : ℝ)) :=
    Real.sin_pos_of_pos_of_lt_pi hu0 (by linarith [Real.pi_pos])
  have hcosu : 0 < Real.cos (uReal (H : ℝ)) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hcosru : 0 < Real.cos (((2 * ell + 1 : ℕ) : ℝ) * uReal (H : ℝ)) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hcast : ((H - 1 : ℕ) : ℝ) + 1 = (H : ℝ) := by
    rw [Nat.cast_sub (show 1 ≤ H by omega), Nat.cast_one]
    ring
  have halpha : Shao.OQ4.RademacherSpectralPairing.alpha (H - 1) ell =
      ((2 * ell + 1 : ℕ) : ℝ) * uReal (H : ℝ) := by
    dsimp only [Shao.OQ4.RademacherSpectralPairing.alpha, uReal]
    rw [hcast]
    ring
  have hbeta : Shao.OQ4.RademacherSpectralPairing.beta (H - 1) ell =
      ((2 * ell + 1 : ℕ) : ℝ) * vReal (H : ℝ) := by
    dsimp only [Shao.OQ4.RademacherSpectralPairing.beta, vReal]
    rw [hcast]
    ring
  have hsign : modeSign (2 * ell + 1) = (-1 : ℝ) ^ ell := by
    dsimp only [modeSign]
    congr 1
    omega
  dsimp only [Shao.OQ4.RademacherSpectralPairing.pairedTerm]
  rw [halpha, hbeta, hsign]
  dsimp only [Shao.OQ4.RademacherSpectralPairing.epsilon, normalizer, aReal,
    rhoReal, cMode, dMode, bMode, Shao.OQ4.RademacherFiniteS1.cotangent]
  simp only [Real.tan_eq_sin_div_cos, div_pow]
  field_simp [ne_of_gt hHp, ne_of_gt hsinu, ne_of_gt hcosu,
    ne_of_gt hsinru, ne_of_gt hcosru, ne_of_gt hcosv,
    pow_ne_zero N (ne_of_gt hcosv)] <;> ring

private theorem actual_factorization {N H : ℕ} (hN : 1 ≤ N) (hH : 2 ≤ H) :
    Shao.OQ4.RademacherS2Assembly.p N ((H : ℝ) - 1) =
      normalizer N (H : ℝ) * (positivePart N H + negativePart N H) ∧
    normalizedActual N H = positivePart N H + negativePart N H := by
  classical
  have hHreal : (2 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hcast : ((H - 1 : ℕ) : ℝ) + 1 = (H : ℝ) := by
    rw [Nat.cast_sub (show 1 ≤ H by omega), Nat.cast_one]
    ring
  have hsub : ((H - 1 : ℕ) : ℝ) = (H : ℝ) - 1 := by linarith
  let f : ℕ → ℝ := fun r => modeSign r *
    (cMode r (H : ℝ) + (-1 : ℝ) ^ (N + (H - 1)) * dMode r (H : ℝ)) *
      bMode N r (H : ℝ)
  have hsum :
      (∑ ell ∈ Shao.OQ4.RademacherSpectralPairing.lowerModes (H - 1), f (2 * ell + 1)) =
        ∑ r ∈ oddIndices H, f r := by
    rw [← lowerModes_image hH]
    exact (Finset.sum_image (f := f) (by
      intro a ha b hb hab
      dsimp at hab
      omega)).symm
  have hsplit : (∑ r ∈ oddIndices H, f r) = positivePart N H + negativePart N H := by
    dsimp only [positivePart, negativePart]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    dsimp only [f]
    ring
  have hPair : Shao.OQ4.RademacherS2Assembly.p N ((H : ℝ) - 1) =
      (1 / (H : ℝ)) * ∑ ell ∈ Shao.OQ4.RademacherSpectralPairing.lowerModes (H - 1),
        Shao.OQ4.RademacherSpectralPairing.pairedTerm (H - 1) N ell := by
    simpa only [Shao.OQ4.RademacherS2Assembly.p, hcast,
      Shao.OQ4.RademacherSpectralPairing.zeroMode_positive_time (H - 1) hN, add_zero] using
      (Shao.OQ4.RademacherSpectralPairing.closedStrip_probability_paired
        (H - 1) (by omega) ((H : ℝ) - 1) (by rw [hsub])
        (by rw [hcast]; linarith) N)
  have hp : Shao.OQ4.RademacherS2Assembly.p N ((H : ℝ) - 1) =
      normalizer N (H : ℝ) * (positivePart N H + negativePart N H) := by
    calc
      Shao.OQ4.RademacherS2Assembly.p N ((H : ℝ) - 1) =
          (1 / (H : ℝ)) * ∑ ell ∈ Shao.OQ4.RademacherSpectralPairing.lowerModes (H - 1),
            Shao.OQ4.RademacherSpectralPairing.pairedTerm (H - 1) N ell := hPair
      _ = (∑ ell ∈ Shao.OQ4.RademacherSpectralPairing.lowerModes (H - 1),
          Shao.OQ4.RademacherSpectralPairing.pairedTerm (H - 1) N ell) / (H : ℝ) := by ring
      _ = ∑ ell ∈ Shao.OQ4.RademacherSpectralPairing.lowerModes (H - 1),
          Shao.OQ4.RademacherSpectralPairing.pairedTerm (H - 1) N ell / (H : ℝ) := by
        rw [Finset.sum_div]
      _ = ∑ ell ∈ Shao.OQ4.RademacherSpectralPairing.lowerModes (H - 1),
          normalizer N (H : ℝ) * f (2 * ell + 1) := by
        apply Finset.sum_congr rfl
        intro ell hell
        exact (pairedTerm_normalized hH hell).trans (by dsimp only [f]; ring)
      _ = normalizer N (H : ℝ) *
          ∑ ell ∈ Shao.OQ4.RademacherSpectralPairing.lowerModes (H - 1), f (2 * ell + 1) := by
        rw [Finset.mul_sum]
      _ = normalizer N (H : ℝ) * (positivePart N H + negativePart N H) := by
        rw [hsum, hsplit]
  refine ⟨hp, ?_⟩
  dsimp only [normalizedActual]
  rw [hp]
  have hn : 0 < normalizer N (H : ℝ) := (scalar_positive hHreal N).2.2
  field_simp [ne_of_gt hn] <;> ring

private theorem negativePart_bound {N H : ℕ} (hH : 2 ≤ H)
    (hNt : (H : ℝ) ^ 2 ≤ (N : ℝ)) :
    |negativePart N H| ≤ negConst / (H : ℝ) ^ 2 := by
  classical
  have hHreal : (2 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hHp : (0 : ℝ) < (H : ℝ) := by linarith
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by
    nlinarith [sq_nonneg ((H : ℝ) - 1)]
  have hN : 1 ≤ N := by exact_mod_cast hNreal
  let t : ℝ := (N : ℝ) / (H : ℝ) ^ 2
  have ht : 1 ≤ t := by
    dsimp only [t]
    apply (le_div_iff₀ (sq_pos_of_pos hHp)).2
    simpa only [one_mul] using hNt
  let A : ℝ := Real.pi ^ 2 / (4 * (H : ℝ) ^ 2)
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hg : 0 < gamma := constants_spec.1
  have hterm : ∀ r ∈ oddIndices H,
      |modeSign r * dMode r (H : ℝ) * bMode N r (H : ℝ)| ≤
        A * ((r : ℝ) * Real.exp (-gamma * ((r : ℝ) ^ 2 - 1))) := by
    intro r hr
    rcases (oddIndices_spec H r).mp hr with ⟨hr1, hodd, hrH⟩
    have hrreal : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    have hrx : (r : ℝ) ≤ (H : ℝ) := by exact_mod_cast hrH.le
    rcases mode_bounds hHreal hr1 hrx with ⟨hcp, hcb, hdp, hdb⟩
    rcases mode_decay hN hHreal hr1 hrx with ⟨hb0, hbb⟩
    let P : ℝ := (r : ℝ) ^ 2 - 1
    have hP0 : 0 ≤ P := by
      dsimp only [P]
      nlinarith [mul_nonneg (sub_nonneg.mpr hrreal)
        (show 0 ≤ (r : ℝ) + 1 by positivity)]
    have hscale : 0 ≤ gamma * P := mul_nonneg hg.le hP0
    have hExp : Real.exp (-2 * gamma * P * t) ≤ Real.exp (-gamma * P) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hscale (show 0 ≤ 2 * t - 1 by linarith)]
    have hbb' : bMode N r (H : ℝ) ≤ Real.exp (-2 * gamma * P * t) := hbb
    calc
      |modeSign r * dMode r (H : ℝ) * bMode N r (H : ℝ)| =
          dMode r (H : ℝ) * bMode N r (H : ℝ) := by
        simp only [abs_mul, modeSign_abs, one_mul, abs_of_pos hdp, abs_of_nonneg hb0]
      _ ≤ (Real.pi ^ 2 * (r : ℝ) / (4 * (H : ℝ) ^ 2)) * Real.exp (-gamma * P) :=
        mul_le_mul hdb (hbb'.trans hExp) hb0 (by positivity)
      _ = A * ((r : ℝ) * Real.exp (-gamma * ((r : ℝ) ^ 2 - 1))) := by
        dsimp only [A, P]
        ring
  calc
    |negativePart N H| =
        |∑ r ∈ oddIndices H, modeSign r * dMode r (H : ℝ) * bMode N r (H : ℝ)| := by
      simp only [negativePart, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    _ ≤ ∑ r ∈ oddIndices H, |modeSign r * dMode r (H : ℝ) * bMode N r (H : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ oddIndices H,
        A * ((r : ℝ) * Real.exp (-gamma * ((r : ℝ) ^ 2 - 1))) := Finset.sum_le_sum hterm
    _ = A * ∑ r ∈ oddIndices H,
        (r : ℝ) * Real.exp (-gamma * ((r : ℝ) ^ 2 - 1)) := by rw [Finset.mul_sum]
    _ ≤ A * sumConst := mul_le_mul_of_nonneg_left
      (finite_gaussian_sum_le (oddIndices H) (fun r hr => ((oddIndices_spec H r).mp hr).1)) hA0
    _ = negConst / (H : ℝ) ^ 2 := by dsimp only [A, negConst]; ring

private theorem positivePart_tail_bound {N H : ℕ} (hH : 2 ≤ H)
    (hNt : (H : ℝ) ^ 2 ≤ (N : ℝ)) :
    |positivePart N H - 1| ≤
      2 * sumConst * Real.exp (-8 * gamma * ((N : ℝ) / (H : ℝ) ^ 2)) := by
  classical
  have hHreal : (2 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hHp : (0 : ℝ) < (H : ℝ) := by linarith
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by
    nlinarith [sq_nonneg ((H : ℝ) - 1)]
  have hN : 1 ≤ N := by exact_mod_cast hNreal
  let t : ℝ := (N : ℝ) / (H : ℝ) ^ 2
  have ht : 1 ≤ t := by
    dsimp only [t]
    apply (le_div_iff₀ (sq_pos_of_pos hHp)).2
    simpa only [one_mul] using hNt
  let J : Finset ℕ := (oddIndices H).erase 1
  let B : ℝ := 2 * Real.exp (-8 * gamma * t)
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hg : 0 < gamma := constants_spec.1
  have h1mem : 1 ∈ oddIndices H := by
    apply (oddIndices_spec H 1).2
    exact ⟨by omega, ⟨0, by norm_num⟩, by omega⟩
  have hfirst : modeSign 1 * cMode 1 (H : ℝ) * bMode N 1 (H : ℝ) = 1 := by
    rcases first_mode hHreal N with ⟨hs, hc, hb⟩
    rw [hs, hc, hb]
    norm_num
  have hsplit : positivePart N H - 1 =
      ∑ r ∈ J, modeSign r * cMode r (H : ℝ) * bMode N r (H : ℝ) := by
    have hsum := Finset.sum_erase_add (oddIndices H)
      (fun r : ℕ => modeSign r * cMode r (H : ℝ) * bMode N r (H : ℝ)) h1mem
    rw [hfirst] at hsum
    change (∑ r ∈ J, modeSign r * cMode r (H : ℝ) * bMode N r (H : ℝ)) + 1 =
      positivePart N H at hsum
    linarith
  have hJpos : ∀ r ∈ J, 1 ≤ r := by
    intro r hr
    exact ((oddIndices_spec H r).mp (Finset.mem_erase.mp hr).2).1
  have hterm : ∀ r ∈ J,
      |modeSign r * cMode r (H : ℝ) * bMode N r (H : ℝ)| ≤
        B * ((r : ℝ) * Real.exp (-gamma * ((r : ℝ) ^ 2 - 1))) := by
    intro r hr
    have hrne : r ≠ 1 := (Finset.mem_erase.mp hr).1
    have hrmem : r ∈ oddIndices H := (Finset.mem_erase.mp hr).2
    rcases (oddIndices_spec H r).mp hrmem with ⟨hr1, hodd, hrH⟩
    have hr3 : 3 ≤ r := by
      rcases hodd with ⟨ell, heq⟩
      omega
    have hr3real : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr3
    have hrp : (0 : ℝ) < (r : ℝ) := by linarith
    have hrx : (r : ℝ) ≤ (H : ℝ) := by exact_mod_cast hrH.le
    rcases mode_bounds hHreal hr1 hrx with ⟨hcp, hcb, hdp, hdb⟩
    rcases mode_decay hN hHreal hr1 hrx with ⟨hb0, hbb⟩
    let P : ℝ := (r : ℝ) ^ 2 - 1
    have hP8 : 8 ≤ P := by
      dsimp only [P]
      nlinarith [mul_nonneg (sub_nonneg.mpr hr3real)
        (show 0 ≤ (r : ℝ) + 3 by positivity)]
    have hbase : 8 * t + P ≤ 2 * P * t := by
      nlinarith [mul_nonneg (show 0 ≤ P by linarith) (sub_nonneg.mpr ht),
        mul_nonneg (show 0 ≤ P - 8 by linarith) (show 0 ≤ t by linarith)]
    have hExp : Real.exp (-2 * gamma * P * t) ≤
        Real.exp (-8 * gamma * t) * Real.exp (-gamma * P) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hbase hg.le]
    have hbb' : bMode N r (H : ℝ) ≤ Real.exp (-2 * gamma * P * t) := hbb
    have hinv : 1 / (r : ℝ) ≤ (r : ℝ) := by
      apply (div_le_iff₀ hrp).2
      nlinarith [mul_nonneg (show 0 ≤ (r : ℝ) - 1 by linarith)
        (show 0 ≤ (r : ℝ) + 1 by positivity)]
    have htwo : 2 / (r : ℝ) ≤ 2 * (r : ℝ) := by
      calc
        2 / (r : ℝ) = 2 * (1 / (r : ℝ)) := by ring
        _ ≤ 2 * (r : ℝ) := mul_le_mul_of_nonneg_left hinv (by norm_num)
    calc
      |modeSign r * cMode r (H : ℝ) * bMode N r (H : ℝ)| =
          cMode r (H : ℝ) * bMode N r (H : ℝ) := by
        simp only [abs_mul, modeSign_abs, one_mul, abs_of_pos hcp, abs_of_nonneg hb0]
      _ ≤ (2 / (r : ℝ)) * (Real.exp (-8 * gamma * t) * Real.exp (-gamma * P)) :=
        mul_le_mul hcb (hbb'.trans hExp) hb0 (by positivity)
      _ ≤ (2 * (r : ℝ)) * (Real.exp (-8 * gamma * t) * Real.exp (-gamma * P)) :=
        mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = B * ((r : ℝ) * Real.exp (-gamma * ((r : ℝ) ^ 2 - 1))) := by
        dsimp only [B, P]
        ring
  calc
    |positivePart N H - 1| =
        |∑ r ∈ J, modeSign r * cMode r (H : ℝ) * bMode N r (H : ℝ)| := by rw [hsplit]
    _ ≤ ∑ r ∈ J, |modeSign r * cMode r (H : ℝ) * bMode N r (H : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ J, B * ((r : ℝ) * Real.exp (-gamma * ((r : ℝ) ^ 2 - 1))) :=
      Finset.sum_le_sum hterm
    _ = B * ∑ r ∈ J, (r : ℝ) * Real.exp (-gamma * ((r : ℝ) ^ 2 - 1)) := by
      rw [Finset.mul_sum]
    _ ≤ B * sumConst := mul_le_mul_of_nonneg_left (finite_gaussian_sum_le J hJpos) hB0
    _ = 2 * sumConst * Real.exp (-8 * gamma * ((N : ℝ) / (H : ℝ) ^ 2)) := by
      dsimp only [B, t]
      ring

-- Cumulative offline A1 + B1 + C1 candidate; C1 definitions and proofs follow.
private def interpolation (N k : ℕ) (x : ℝ) : ℝ :=
  ∑ r ∈ oddIndices (k + 1), modeSign r * cMode r x * bMode N r x
private def cDerivative (r : ℕ) (x : ℝ) : ℝ :=
  (uReal x / x) *
    ((r : ℝ) * Real.tan (uReal x) / Real.sin ((r : ℝ) * uReal x) ^ 2 -
      (Real.cos ((r : ℝ) * uReal x) / Real.sin ((r : ℝ) * uReal x)) /
        Real.cos (uReal x) ^ 2)

-- D27: sine/power formula is finite at the cutoff; it never evaluates tan(r*v).
private def bDerivative (N r : ℕ) (x : ℝ) : ℝ :=
  ((N : ℝ) * vReal x / x) *
    ((r : ℝ) * Real.sin ((r : ℝ) * vReal x) *
        Real.cos ((r : ℝ) * vReal x) ^ (N - 1) / Real.cos (vReal x) ^ N -
      Real.sin (vReal x) * Real.cos ((r : ℝ) * vReal x) ^ N /
        Real.cos (vReal x) ^ (N + 1))
private def termDerivative (N r : ℕ) (x : ℝ) : ℝ :=
  cDerivative r x * bMode N r x + cMode r x * bDerivative N r x
private def interpolationDerivative (N k : ℕ) (x : ℝ) : ℝ :=
  ∑ r ∈ oddIndices (k + 1), modeSign r * termDerivative N r x

private theorem cMode_hasDerivAt {r : ℕ} {x : ℝ} (hx : 2 ≤ x)
    (hr : 1 ≤ r) (hrx : (r : ℝ) < x) :
    HasDerivAt (cMode r) (cDerivative r x) x := by
  rcases real_angle_domain hx hr hrx.le with
    ⟨hu0, hu, hv0, hv, hru0, hru, hrv0, hrv, hsinru, hcosv⟩
  have hxp : 0 < x := by linarith
  have hcosu : 0 < Real.cos (uReal x) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hcosru : 0 < Real.cos ((r : ℝ) * uReal x) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have htanu : 0 < Real.tan ((r : ℝ) * uReal x) := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hsinru hcosru
  have hdu : HasDerivAt uReal (-uReal x / x) x := by
    have hfun : uReal = fun y : ℝ => (Real.pi / 4) * y⁻¹ := by
      funext y
      simp only [uReal, div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hfun]
    convert ((hasDerivAt_id x).inv (ne_of_gt hxp)).const_mul (Real.pi / 4) using 1 <;>
      (try simp only [Pi.inv_apply, id_eq]) <;> field_simp [ne_of_gt hxp] <;> ring
  have hru' : HasDerivAt (fun y : ℝ => (r : ℝ) * uReal y)
      ((r : ℝ) * (-uReal x / x)) x := hdu.const_mul (r : ℝ)
  have htanu' := (Real.hasDerivAt_tan (ne_of_gt hcosu)).comp x hdu
  have htanru' := (Real.hasDerivAt_tan (ne_of_gt hcosru)).comp x hru'
  have hcot : HasDerivAt
      (fun y : ℝ => Real.cos ((r : ℝ) * uReal y) / Real.sin ((r : ℝ) * uReal y))
      ((r : ℝ) * uReal x / (x * Real.sin ((r : ℝ) * uReal x) ^ 2)) x := by
    have hfun : (fun y : ℝ => Real.cos ((r : ℝ) * uReal y) /
        Real.sin ((r : ℝ) * uReal y)) =
        (fun y : ℝ => (Real.tan ((r : ℝ) * uReal y))⁻¹) := by
      funext y
      simp only [Real.tan_eq_sin_div_cos, inv_div]
    have hinv := htanru'.inv (ne_of_gt htanu)
    change HasDerivAt (fun y : ℝ => (Real.tan ((r : ℝ) * uReal y))⁻¹) _ x at hinv
    rw [← hfun] at hinv
    convert hinv using 1 <;>
      simp only [Function.comp_apply, Pi.inv_apply, Real.tan_eq_sin_div_cos] <;>
      field_simp [ne_of_gt hxp, ne_of_gt hsinru, ne_of_gt hcosru] <;> ring
  change HasDerivAt
    (fun y : ℝ => Real.tan (uReal y) *
      (Real.cos ((r : ℝ) * uReal y) / Real.sin ((r : ℝ) * uReal y)))
    (cDerivative r x) x
  have hmul := htanu'.mul hcot
  change HasDerivAt
    (fun y : ℝ => Real.tan (uReal y) *
      (Real.cos ((r : ℝ) * uReal y) / Real.sin ((r : ℝ) * uReal y))) _ x at hmul
  convert hmul using 1 <;>
    simp only [cDerivative, Function.comp_apply, Pi.mul_apply, Real.tan_eq_sin_div_cos] <;>
    field_simp [ne_of_gt hxp, ne_of_gt hsinru, ne_of_gt hcosu] <;> ring

private theorem cDerivative_bound {r : ℕ} {x : ℝ} (hx : 2 ≤ x)
    (hr : 1 ≤ r) (hrx : (r : ℝ) < x) :
    |cDerivative r x| ≤ coeffA / ((r : ℝ) * x) := by
  rcases real_angle_domain hx hr hrx.le with
    ⟨hu0, hu, hv0, hv, hru0, hru, hrv0, hrv, hsinru, hcosv⟩
  have hxp : 0 < x := by linarith
  have hrp : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have huq : uReal x ≤ Real.pi / 4 := by linarith [Real.pi_pos]
  have hsinu : 0 < Real.sin (uReal x) :=
    Real.sin_pos_of_pos_of_lt_pi hu0 (by linarith [Real.pi_pos])
  have hcosu : 0 < Real.cos (uReal x) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hcosru : 0 < Real.cos ((r : ℝ) * uReal x) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have htanu : 0 < Real.tan (uReal x) := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hsinu hcosu
  rcases quarter_angle_bounds hu0 huq with ⟨hcu, htu, hcotu, hcscu, hsecu⟩
  rcases quarter_angle_bounds hru0 hru with ⟨hcru, htru, hcotru, hcscru, hsecru⟩
  let A : ℝ := (r : ℝ) * Real.tan (uReal x) / Real.sin ((r : ℝ) * uReal x) ^ 2
  let B : ℝ := (Real.cos ((r : ℝ) * uReal x) / Real.sin ((r : ℝ) * uReal x)) /
    Real.cos (uReal x) ^ 2
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hAub : A ≤ ((r : ℝ) * (2 * uReal x)) *
      (Real.pi ^ 2 / (4 * ((r : ℝ) * uReal x) ^ 2)) := by
    calc
      A = ((r : ℝ) * Real.tan (uReal x)) *
          (1 / Real.sin ((r : ℝ) * uReal x) ^ 2) := by dsimp only [A]; ring
      _ ≤ ((r : ℝ) * (2 * uReal x)) *
          (Real.pi ^ 2 / (4 * ((r : ℝ) * uReal x) ^ 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left htu hrp.le) hcscru
          (by positivity) (by positivity)
  have hBub : B ≤ (1 / ((r : ℝ) * uReal x)) * 2 := by
    calc
      B = (Real.cos ((r : ℝ) * uReal x) / Real.sin ((r : ℝ) * uReal x)) *
          (1 / Real.cos (uReal x) ^ 2) := by dsimp only [B]; ring
      _ ≤ (1 / ((r : ℝ) * uReal x)) * 2 :=
        mul_le_mul hcotru hsecu (by positivity) (by positivity)
  have hformula : cDerivative r x = (uReal x / x) * (A - B) := by
    rfl
  calc
    |cDerivative r x| = (uReal x / x) * |A - B| := by
      rw [hformula, abs_mul, abs_of_pos (div_pos hu0 hxp)]
    _ ≤ (uReal x / x) * (A + B) :=
      mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩) (div_pos hu0 hxp).le
    _ ≤ (uReal x / x) *
        (((r : ℝ) * (2 * uReal x)) * (Real.pi ^ 2 / (4 * ((r : ℝ) * uReal x) ^ 2)) +
          (1 / ((r : ℝ) * uReal x)) * 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hAub hBub) (div_pos hu0 hxp).le
    _ = coeffA / ((r : ℝ) * x) := by
      dsimp only [coeffA]
      field_simp [ne_of_gt hrp, ne_of_gt hu0, ne_of_gt hxp] <;> ring

private theorem bMode_hasDerivAt {N r : ℕ} {x : ℝ} (hN : 1 ≤ N)
    (hx : 2 ≤ x) (hr : 1 ≤ r) (hrx : (r : ℝ) < x) :
    HasDerivAt (bMode N r) (bDerivative N r x) x := by
  rcases real_angle_domain hx hr hrx.le with
    ⟨hu0, hu, hv0, hv, hru0, hru, hrv0, hrv, hsinru, hcosv⟩
  have hxp : 0 < x := by linarith
  have hdv : HasDerivAt vReal (-vReal x / x) x := by
    have hfun : vReal = fun y : ℝ => (Real.pi / 2) * y⁻¹ := by
      funext y
      simp only [vReal, div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hfun]
    convert ((hasDerivAt_id x).inv (ne_of_gt hxp)).const_mul (Real.pi / 2) using 1 <;>
      (try simp only [Pi.inv_apply, id_eq]) <;> field_simp [ne_of_gt hxp] <;> ring
  have hcr : HasDerivAt (fun y : ℝ => Real.cos ((r : ℝ) * vReal y))
      (((r : ℝ) * vReal x / x) * Real.sin ((r : ℝ) * vReal x)) x := by
    convert (hdv.const_mul (r : ℝ)).cos using 1 <;> ring
  have hcv : HasDerivAt (fun y : ℝ => Real.cos (vReal y))
      ((vReal x / x) * Real.sin (vReal x)) x := by
    convert hdv.cos using 1 <;> ring
  have hq := hcr.div hcv (ne_of_gt hcosv)
  have hrpow : Real.cos ((r : ℝ) * vReal x) ^ (N - 1) * Real.cos ((r : ℝ) * vReal x) =
      Real.cos ((r : ℝ) * vReal x) ^ N := by
    rw [← pow_succ, Nat.sub_add_cancel hN]
  have hvpow : Real.cos (vReal x) ^ (N - 1) * Real.cos (vReal x) =
      Real.cos (vReal x) ^ N := by
    rw [← pow_succ, Nat.sub_add_cancel hN]
  change HasDerivAt
    (fun y : ℝ => (Real.cos ((r : ℝ) * vReal y) / Real.cos (vReal y)) ^ N)
    (bDerivative N r x) x
  have hp := hq.pow N
  change HasDerivAt
    (fun y : ℝ => (Real.cos ((r : ℝ) * vReal y) / Real.cos (vReal y)) ^ N) _ x at hp
  convert hp using 1 <;>
    simp only [bDerivative, Function.comp_apply, Pi.div_apply, Pi.pow_apply,
      div_pow, pow_succ, ← hrpow, ← hvpow] <;>
    field_simp [ne_of_gt hxp, ne_of_gt hcosv,
      pow_ne_zero (N - 1) (ne_of_gt hcosv)] <;> ring

private theorem bDerivative_bound {N r : ℕ} {x : ℝ} (hN : 2 ≤ N)
    (hx : 2 ≤ x) (hr : 1 ≤ r) (hrx : (r : ℝ) < x) :
    0 ≤ bDerivative N r x ∧ bDerivative N r x ≤
      coeffB * ((N : ℝ) * (r : ℝ) ^ 2 / x ^ 3) *
        Real.exp (-gamma * ((r : ℝ) ^ 2 - 1) * ((N : ℝ) / x ^ 2)) := by
  set_option maxHeartbeats 800000 in
    rcases real_angle_domain hx hr hrx.le with
      ⟨hu0, hu, hv0, hv, hru0, hru, hrv0, hrv, hsinru, hcosv⟩
    have hxp : 0 < x := by linarith
    have hrreal : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hrp : (0 : ℝ) < (r : ℝ) := by linarith
    have hN1 : 1 ≤ N := by omega
    have hxv : x * vReal x = Real.pi / 2 := by
      dsimp only [vReal]
      field_simp [ne_of_gt hxp] <;> ring
    have hrvlt : (r : ℝ) * vReal x < Real.pi / 2 := by
      have hm := mul_lt_mul_of_pos_right hrx hv0
      linarith
    have hcosrv : 0 < Real.cos ((r : ℝ) * vReal x) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hrvlt⟩
    have hcosvr : 0 < Real.cos (vReal x * (r : ℝ)) := by
      simpa only [mul_comm] using hcosrv
    have hvlt : vReal x < Real.pi / 2 := by linarith [Real.pi_pos]
    have hsinv : 0 < Real.sin (vReal x) :=
      Real.sin_pos_of_pos_of_lt_pi hv0 (by linarith [Real.pi_pos])
    have hvle : vReal x ≤ (r : ℝ) * vReal x := by
      nlinarith [mul_le_mul_of_nonneg_right hrreal hv0.le]
    have htanmono : Real.tan (vReal x) ≤ Real.tan ((r : ℝ) * vReal x) :=
      Real.strictMonoOn_tan.monotoneOn
        ⟨by linarith [Real.pi_pos], hvlt⟩
        ⟨by linarith [Real.pi_pos], hrvlt⟩ hvle
    have htanrv0 : 0 ≤ Real.tan ((r : ℝ) * vReal x) := by
      have ht := Real.le_tan hrv0.le hrvlt
      linarith
    have hbracket : 0 ≤ (r : ℝ) * Real.tan ((r : ℝ) * vReal x) - Real.tan (vReal x) := by
      nlinarith [mul_le_mul_of_nonneg_right hrreal htanrv0]
    have hrpow : Real.cos ((r : ℝ) * vReal x) ^ (N - 1) * Real.cos ((r : ℝ) * vReal x) =
        Real.cos ((r : ℝ) * vReal x) ^ N := by
      rw [← pow_succ, Nat.sub_add_cancel hN1]
    have hvpow : Real.cos (vReal x) ^ (N - 1) * Real.cos (vReal x) =
        Real.cos (vReal x) ^ N := by
      rw [← pow_succ, Nat.sub_add_cancel hN1]
    let pref : ℝ := (N : ℝ) * vReal x / x
    have hpref0 : 0 ≤ pref := by dsimp only [pref]; positivity
    have hb0 : 0 ≤ bMode N r x := (mode_decay hN1 hx hr hrx.le).1
    have hlogForm : bDerivative N r x = pref * bMode N r x *
        ((r : ℝ) * Real.tan ((r : ℝ) * vReal x) - Real.tan (vReal x)) := by
      dsimp only [bDerivative, bMode, pref]
      simp only [Real.tan_eq_sin_div_cos, div_pow, pow_succ, ← hrpow, ← hvpow]
      field_simp [ne_of_gt hxp, ne_of_gt hcosrv, ne_of_gt hcosvr, ne_of_gt hcosv,
        pow_ne_zero (N - 1) (ne_of_gt hcosv)] <;> ring
    have hderiv0 : 0 ≤ bDerivative N r x := by
      rw [hlogForm]
      exact mul_nonneg (mul_nonneg hpref0 hb0) hbracket
    have hsecond0 : 0 ≤ Real.sin (vReal x) * Real.cos ((r : ℝ) * vReal x) ^ N /
        Real.cos (vReal x) ^ (N + 1) := by positivity
    have hdrop : bDerivative N r x ≤ pref *
        ((r : ℝ) * Real.sin ((r : ℝ) * vReal x) *
          Real.cos ((r : ℝ) * vReal x) ^ (N - 1) / Real.cos (vReal x) ^ N) := by
      have hm := mul_nonneg hpref0 hsecond0
      dsimp only [bDerivative, pref] at *
      nlinarith only [hm]
    have hsinNumer :
        (r : ℝ) * Real.sin ((r : ℝ) * vReal x) * Real.cos ((r : ℝ) * vReal x) ^ (N - 1) ≤
          (r : ℝ) * ((r : ℝ) * vReal x) * Real.cos ((r : ℝ) * vReal x) ^ (N - 1) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.sin_le hrv0.le) hrp.le) (by positivity)
    have hsinQuot :
        (r : ℝ) * Real.sin ((r : ℝ) * vReal x) *
            Real.cos ((r : ℝ) * vReal x) ^ (N - 1) / Real.cos (vReal x) ^ N ≤
          (r : ℝ) * ((r : ℝ) * vReal x) *
            Real.cos ((r : ℝ) * vReal x) ^ (N - 1) / Real.cos (vReal x) ^ N := by
      apply (div_le_div_iff₀ (pow_pos hcosv N) (pow_pos hcosv N)).2
      exact mul_le_mul_of_nonneg_right hsinNumer (by positivity)
    rcases quarter_angle_bounds hv0 hv with ⟨hcoslower, htanv, hcotv, hcscv, hsecv⟩
    have hsqrtp : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
    have hinvcos : 1 / Real.cos (vReal x) ≤ Real.sqrt 2 := by
      apply (div_le_iff₀ hcosv).2
      have hm := (div_le_iff₀ hsqrtp).mp hcoslower
      nlinarith
    let P : ℝ := (r : ℝ) ^ 2 - 1
    let t : ℝ := (N : ℝ) / x ^ 2
    let predT : ℝ := ((N - 1 : ℕ) : ℝ) / x ^ 2
    have hP0 : 0 ≤ P := by
      dsimp only [P]
      nlinarith [mul_nonneg (sub_nonneg.mpr hrreal)
        (show 0 ≤ (r : ℝ) + 1 by positivity)]
    have hgP0 : 0 ≤ gamma * P := mul_nonneg constants_spec.1.le hP0
    have hNum : (N : ℝ) ≤ 2 * ((N - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show N ≤ 2 * (N - 1) by omega)
    have hscale : t ≤ 2 * predT := by
      calc
        t ≤ (2 * ((N - 1 : ℕ) : ℝ)) / x ^ 2 := by
          dsimp only [t]
          apply (div_le_div_iff₀ (sq_pos_of_pos hxp) (sq_pos_of_pos hxp)).2
          exact mul_le_mul_of_nonneg_right hNum (sq_nonneg x)
        _ = 2 * predT := by dsimp only [predT]; ring
    rcases mode_decay (N := N - 1) (show 1 ≤ N - 1 by omega) hx hr hrx.le with ⟨hbp0, hbp⟩
    have hbp' : bMode (N - 1) r x ≤ Real.exp (-2 * gamma * P * predT) := hbp
    have hExp : Real.exp (-2 * gamma * P * predT) ≤ Real.exp (-gamma * P * t) := by
      apply Real.exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_left hscale hgP0
      linarith only [hm]
    have hquot : Real.cos ((r : ℝ) * vReal x) ^ (N - 1) / Real.cos (vReal x) ^ N =
        (1 / Real.cos (vReal x)) * bMode (N - 1) r x := by
      dsimp only [bMode]
      rw [div_pow, ← hvpow]
      field_simp [ne_of_gt hcosv, pow_ne_zero (N - 1) (ne_of_gt hcosv)] <;> ring
    have hquotBound : Real.cos ((r : ℝ) * vReal x) ^ (N - 1) / Real.cos (vReal x) ^ N ≤
        Real.sqrt 2 * Real.exp (-gamma * P * t) := by
      rw [hquot]
      exact mul_le_mul hinvcos (hbp'.trans hExp) hbp0 (Real.sqrt_nonneg 2)
    let A : ℝ := (N : ℝ) * (r : ℝ) ^ 2 * vReal x ^ 2 / x
    have hA0 : 0 ≤ A := by dsimp only [A]; positivity
    refine ⟨hderiv0, ?_⟩
    calc
      bDerivative N r x ≤ pref *
          ((r : ℝ) * Real.sin ((r : ℝ) * vReal x) *
            Real.cos ((r : ℝ) * vReal x) ^ (N - 1) / Real.cos (vReal x) ^ N) := hdrop
      _ ≤ pref * ((r : ℝ) * ((r : ℝ) * vReal x) *
          Real.cos ((r : ℝ) * vReal x) ^ (N - 1) / Real.cos (vReal x) ^ N) :=
        mul_le_mul_of_nonneg_left hsinQuot hpref0
      _ = A * (Real.cos ((r : ℝ) * vReal x) ^ (N - 1) / Real.cos (vReal x) ^ N) := by
        dsimp only [A, pref]
        ring
      _ ≤ A * (Real.sqrt 2 * Real.exp (-gamma * P * t)) := mul_le_mul_of_nonneg_left hquotBound hA0
      _ = coeffB * ((N : ℝ) * (r : ℝ) ^ 2 / x ^ 3) *
          Real.exp (-gamma * ((r : ℝ) ^ 2 - 1) * ((N : ℝ) / x ^ 2)) := by
        dsimp only [A, P, t, coeffB, vReal]
        field_simp [ne_of_gt hxp] <;> ring

private theorem modeProduct_hasDerivAt {N r : ℕ} {x : ℝ} (hN : 2 ≤ N)
    (hx : 2 ≤ x) (hr : 1 ≤ r) (hrx : (r : ℝ) < x) :
    HasDerivAt (fun y : ℝ => cMode r y * bMode N r y) (termDerivative N r x) x := by
  exact (cMode_hasDerivAt hx hr hrx).mul (bMode_hasDerivAt (by omega) hx hr hrx)

private theorem termDerivative_bound {N r : ℕ} {x : ℝ} (hN : 2 ≤ N)
    (hx : 2 ≤ x) (hr : 1 ≤ r) (hrx : (r : ℝ) < x) (hNt : x ^ 2 ≤ (N : ℝ)) :
    |termDerivative N r x| ≤
      (coeffA + 2 * coeffB) * ((N : ℝ) / x ^ 3) *
        ((r : ℝ) * Real.exp (-gamma * ((r : ℝ) ^ 2 - 1))) := by
  rcases constants_spec with ⟨hg, hq0, hq1, hS, hA, hB, hD, hE, hL, hC⟩
  have hxp : 0 < x := by linarith
  have hrreal : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrp : (0 : ℝ) < (r : ℝ) := by linarith
  let t : ℝ := (N : ℝ) / x ^ 2
  let P : ℝ := (r : ℝ) ^ 2 - 1
  let e : ℝ := Real.exp (-gamma * P * t)
  let e0 : ℝ := Real.exp (-gamma * P)
  have ht : 1 ≤ t := by
    dsimp only [t]
    apply (le_div_iff₀ (sq_pos_of_pos hxp)).2
    simpa only [one_mul] using hNt
  have hP0 : 0 ≤ P := by
    dsimp only [P]
    nlinarith [mul_nonneg (sub_nonneg.mpr hrreal)
      (show 0 ≤ (r : ℝ) + 1 by positivity)]
  have hgP0 : 0 ≤ gamma * P := mul_nonneg hg.le hP0
  have he0 : 0 ≤ e := by dsimp only [e]; positivity
  have he_le : e ≤ e0 := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hgP0 (sub_nonneg.mpr ht)]
  have htwoExp : Real.exp (-2 * gamma * P * t) ≤ e := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hgP0 (show 0 ≤ t by linarith)]
  rcases mode_bounds hx hr hrx.le with ⟨hcp, hcb, hdp, hdb⟩
  rcases mode_decay (show 1 ≤ N by omega) hx hr hrx.le with ⟨hb0, hbb⟩
  have hbb' : bMode N r x ≤ e := hbb.trans htwoExp
  have hcderiv := cDerivative_bound hx hr hrx
  rcases bDerivative_bound hN hx hr hrx with ⟨hbderiv0, hbderiv⟩
  have hbderiv' : bDerivative N r x ≤ coeffB * ((N : ℝ) * (r : ℝ) ^ 2 / x ^ 3) * e := hbderiv
  have hinv : 1 / (r : ℝ) ≤ (r : ℝ) := by
    apply (div_le_iff₀ hrp).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hrreal)
      (show 0 ≤ (r : ℝ) + 1 by positivity)]
  have hfrac : 1 / x ≤ (N : ℝ) / x ^ 3 := by
    apply (div_le_div_iff₀ hxp (pow_pos hxp 3)).2
    have hm := mul_le_mul_of_nonneg_right hNt hxp.le
    nlinarith only [hm]
  have hCoefA : coeffA / ((r : ℝ) * x) ≤ coeffA * ((N : ℝ) / x ^ 3) * (r : ℝ) := by
    calc
      coeffA / ((r : ℝ) * x) = (coeffA * (1 / (r : ℝ))) * (1 / x) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ (coeffA * (r : ℝ)) * ((N : ℝ) / x ^ 3) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hinv hA.le) hfrac (by positivity) (by positivity)
      _ = coeffA * ((N : ℝ) / x ^ 3) * (r : ℝ) := by ring
  have hCoefB : (2 / (r : ℝ)) * (coeffB * ((N : ℝ) * (r : ℝ) ^ 2 / x ^ 3)) =
      2 * coeffB * ((N : ℝ) / x ^ 3) * (r : ℝ) := by
    field_simp [ne_of_gt hrp, ne_of_gt hxp] <;> ring
  have hCoef : coeffA / ((r : ℝ) * x) +
      (2 / (r : ℝ)) * (coeffB * ((N : ℝ) * (r : ℝ) ^ 2 / x ^ 3)) ≤
        (coeffA + 2 * coeffB) * ((N : ℝ) / x ^ 3) * (r : ℝ) := by
    rw [hCoefB]
    nlinarith only [hCoefA]
  calc
    |termDerivative N r x| =
        |cDerivative r x * bMode N r x + cMode r x * bDerivative N r x| := rfl
    _ ≤ |cDerivative r x * bMode N r x| + |cMode r x * bDerivative N r x| := abs_add_le _ _
    _ = |cDerivative r x| * bMode N r x + cMode r x * bDerivative N r x := by
      simp only [abs_mul, abs_of_nonneg hb0, abs_of_pos hcp, abs_of_nonneg hbderiv0]
    _ ≤ (coeffA / ((r : ℝ) * x)) * e +
        (2 / (r : ℝ)) * (coeffB * ((N : ℝ) * (r : ℝ) ^ 2 / x ^ 3) * e) :=
      add_le_add (mul_le_mul hcderiv hbb' hb0 (by positivity))
        (mul_le_mul hcb hbderiv' hbderiv0 (by positivity))
    _ = (coeffA / ((r : ℝ) * x) +
        (2 / (r : ℝ)) * (coeffB * ((N : ℝ) * (r : ℝ) ^ 2 / x ^ 3))) * e := by ring
    _ ≤ ((coeffA + 2 * coeffB) * ((N : ℝ) / x ^ 3) * (r : ℝ)) * e :=
      mul_le_mul_of_nonneg_right hCoef he0
    _ ≤ ((coeffA + 2 * coeffB) * ((N : ℝ) / x ^ 3) * (r : ℝ)) * e0 :=
      mul_le_mul_of_nonneg_left he_le (by positivity)
    _ = (coeffA + 2 * coeffB) * ((N : ℝ) / x ^ 3) *
        ((r : ℝ) * Real.exp (-gamma * ((r : ℝ) ^ 2 - 1))) := by
      dsimp only [e0, P]
      ring

private theorem interpolation_continuous {N k : ℕ} (hN : 1 ≤ N) (hk : 2 ≤ k) :
    ContinuousOn (interpolation N k) (Set.Icc (k : ℝ) ((k : ℝ) + 1)) := by
  classical
  intro x hx
  have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hx2 : 2 ≤ x := le_trans hkreal hx.1
  have hxp : 0 < x := by linarith
  let T : ℕ → ℝ → ℝ := fun r y => modeSign r * cMode r y * bMode N r y
  have hterm : ∀ r ∈ oddIndices (k + 1), ContinuousAt (T r) x := by
    intro r hr
    rcases (oddIndices_spec (k + 1) r).mp hr with ⟨hr1, hodd, hrk⟩
    have hrkle : r ≤ k := by omega
    have hrreal : (r : ℝ) ≤ (k : ℝ) := by exact_mod_cast hrkle
    have hrx : (r : ℝ) ≤ x := le_trans hrreal hx.1
    rcases real_angle_domain hx2 hr1 hrx with
      ⟨hu0, hu, hv0, hv, hru0, hru, hrv0, hrv, hsinru, hcosv⟩
    have hcosu : 0 < Real.cos (uReal x) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hcu : ContinuousAt uReal x := by
      change ContinuousAt (fun y : ℝ => Real.pi / (4 * y)) x
      exact continuousAt_const.div (continuousAt_const.mul continuousAt_id) (by positivity)
    have hcv : ContinuousAt vReal x := by
      change ContinuousAt (fun y : ℝ => Real.pi / (2 * y)) x
      exact continuousAt_const.div (continuousAt_const.mul continuousAt_id) (by positivity)
    have hcru : ContinuousAt (fun y : ℝ => (r : ℝ) * uReal y) x := continuousAt_const.mul hcu
    have hcrv : ContinuousAt (fun y : ℝ => (r : ℝ) * vReal y) x := continuousAt_const.mul hcv
    have htan : ContinuousAt (fun y : ℝ => Real.tan (uReal y)) x := by
      simp_rw [Real.tan_eq_sin_div_cos]
      exact (Real.continuous_sin.continuousAt.comp hcu).div
        (Real.continuous_cos.continuousAt.comp hcu) (ne_of_gt hcosu)
    have hcot : ContinuousAt
        (fun y : ℝ => Real.cos ((r : ℝ) * uReal y) / Real.sin ((r : ℝ) * uReal y)) x :=
      (Real.continuous_cos.continuousAt.comp hcru).div
        (Real.continuous_sin.continuousAt.comp hcru) (ne_of_gt hsinru)
    have hb : ContinuousAt (bMode N r) x := by
      change ContinuousAt
        (fun y : ℝ => (Real.cos ((r : ℝ) * vReal y) / Real.cos (vReal y)) ^ N) x
      exact ((Real.continuous_cos.continuousAt.comp hcrv).div
        (Real.continuous_cos.continuousAt.comp hcv) (ne_of_gt hcosv)).pow N
    change ContinuousAt (fun y : ℝ => modeSign r * cMode r y * bMode N r y) x
    exact (continuousAt_const.mul (htan.mul hcot)).mul hb
  have hsumCont (s : Finset ℕ) :
      (∀ r ∈ s, ContinuousAt (T r) x) → ContinuousAt (fun y : ℝ => ∑ r ∈ s, T r y) x := by
    induction s using Finset.induction_on with
    | empty =>
        intro hs
        simpa only [Finset.sum_empty] using
          (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) x)
    | @insert a s ha ih =>
        intro hs
        have hca : ContinuousAt (T a) x := hs a (by simp)
        have hcs := ih (fun r hr => hs r (by simp only [Finset.mem_insert]; exact Or.inr hr))
        have hadd := hca.add hcs
        change ContinuousAt (fun y : ℝ => T a y + ∑ r ∈ s, T r y) x at hadd
        simpa only [Finset.sum_insert ha] using hadd
  exact (hsumCont (oddIndices (k + 1)) hterm).continuousWithinAt

private theorem cutoff_mode_zero {N k : ℕ} (hN : 1 ≤ N) (hk : 2 ≤ k) :
    bMode N k (k : ℝ) = 0 := by
  have hkp : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hangle : (k : ℝ) * vReal (k : ℝ) = Real.pi / 2 := by
    dsimp only [vReal]
    field_simp [ne_of_gt hkp] <;> ring
  simp only [bMode, hangle, Real.cos_pi_div_two, zero_div, zero_pow (show N ≠ 0 by omega)]

private theorem interpolation_endpoints {N k : ℕ} (hN : 1 ≤ N) (hk : 2 ≤ k) :
    interpolation N k (k : ℝ) = positivePart N k ∧
    interpolation N k ((k : ℝ) + 1) = positivePart N (k + 1) := by
  classical
  have hsub : oddIndices k ⊆ oddIndices (k + 1) := by
    intro r hr
    rcases (oddIndices_spec k r).mp hr with ⟨hr1, hodd, hrk⟩
    exact (oddIndices_spec (k + 1) r).2 ⟨hr1, hodd, by omega⟩
  constructor
  · change (∑ r ∈ oddIndices (k + 1), modeSign r * cMode r (k : ℝ) * bMode N r (k : ℝ)) =
        ∑ r ∈ oddIndices k, modeSign r * cMode r (k : ℝ) * bMode N r (k : ℝ)
    apply Eq.symm
    apply Finset.sum_subset hsub
    intro r hr hnot
    rcases (oddIndices_spec (k + 1) r).mp hr with ⟨hr1, hodd, hrk⟩
    have hrge : k ≤ r := by
      by_contra hh
      exact hnot ((oddIndices_spec k r).2 ⟨hr1, hodd, by omega⟩)
    have heq : r = k := by omega
    subst r
    rw [cutoff_mode_zero hN hk]
    ring
  · simp only [interpolation, positivePart, Nat.cast_add, Nat.cast_one]

private theorem interpolation_hasDerivAt {N k : ℕ} {x : ℝ}
    (hN : 2 ≤ N) (hk : 2 ≤ k) (hx : x ∈ Set.Ioo (k : ℝ) ((k : ℝ) + 1)) :
    HasDerivAt (interpolation N k) (interpolationDerivative N k x) x := by
  classical
  have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hx2 : 2 ≤ x := by linarith [hx.1]
  have hterm : ∀ r ∈ oddIndices (k + 1),
      HasDerivAt (fun y : ℝ => modeSign r * cMode r y * bMode N r y)
        (modeSign r * termDerivative N r x) x := by
    intro r hr
    rcases (oddIndices_spec (k + 1) r).mp hr with ⟨hr1, hodd, hrk⟩
    have hrkle : r ≤ k := by omega
    have hrreal : (r : ℝ) ≤ (k : ℝ) := by exact_mod_cast hrkle
    have hrx : (r : ℝ) < x := lt_of_le_of_lt hrreal hx.1
    have hfun : (fun y : ℝ => modeSign r * cMode r y * bMode N r y) =
        (fun y : ℝ => modeSign r * (cMode r y * bMode N r y)) := by
      funext y
      ring
    rw [hfun]
    exact (modeProduct_hasDerivAt hN hx2 hr1 hrx).const_mul (modeSign r)
  change HasDerivAt
    (fun y : ℝ => ∑ r ∈ oddIndices (k + 1), modeSign r * cMode r y * bMode N r y)
    (∑ r ∈ oddIndices (k + 1), modeSign r * termDerivative N r x) x
  convert! HasDerivAt.fun_sum hterm using 1 <;> rfl

private theorem interpolationDerivative_bound {N k : ℕ} {x : ℝ}
    (hN : 2 ≤ N) (hk : 2 ≤ k) (hNt : ((k : ℝ) + 1) ^ 2 ≤ (N : ℝ))
    (hx : x ∈ Set.Ioo (k : ℝ) ((k : ℝ) + 1)) :
    |interpolationDerivative N k x| ≤ derivConst * ((N : ℝ) / (k : ℝ) ^ 3) := by
  classical
  rcases constants_spec with ⟨hg, hq0, hq1, hS, hA, hB, hD, hE, hL, hC⟩
  have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkp : (0 : ℝ) < (k : ℝ) := by linarith
  have hx2 : 2 ≤ x := by linarith [hx.1]
  have hxp : 0 < x := by linarith
  have hNtx : x ^ 2 ≤ (N : ℝ) := by
    nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) + 1 - x by linarith [hx.2])
      (show 0 ≤ (k : ℝ) + 1 + x by positivity)]
  have hCube : (k : ℝ) ^ 3 ≤ x ^ 3 := by
    gcongr <;> linarith [hx.1]
  have hfrac : (N : ℝ) / x ^ 3 ≤ (N : ℝ) / (k : ℝ) ^ 3 := by
    apply (div_le_div_iff₀ (pow_pos hxp 3) (pow_pos hkp 3)).2
    exact mul_le_mul_of_nonneg_left hCube (by positivity)
  let M : ℝ := (coeffA + 2 * coeffB) * ((N : ℝ) / (k : ℝ) ^ 3)
  have hM0 : 0 ≤ M := by dsimp only [M]; positivity
  have hterm : ∀ r ∈ oddIndices (k + 1),
      |modeSign r * termDerivative N r x| ≤
        M * ((r : ℝ) * Real.exp (-gamma * ((r : ℝ) ^ 2 - 1))) := by
    intro r hr
    rcases (oddIndices_spec (k + 1) r).mp hr with ⟨hr1, hodd, hrk⟩
    have hrkle : r ≤ k := by omega
    have hrreal : (r : ℝ) ≤ (k : ℝ) := by exact_mod_cast hrkle
    have hrx : (r : ℝ) < x := lt_of_le_of_lt hrreal hx.1
    rw [abs_mul, modeSign_abs, one_mul]
    calc
      |termDerivative N r x| ≤ (coeffA + 2 * coeffB) * ((N : ℝ) / x ^ 3) *
          ((r : ℝ) * Real.exp (-gamma * ((r : ℝ) ^ 2 - 1))) :=
        termDerivative_bound hN hx2 hr1 hrx hNtx
      _ ≤ M * ((r : ℝ) * Real.exp (-gamma * ((r : ℝ) ^ 2 - 1))) := by
        dsimp only [M]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hfrac (by positivity)
  calc
    |interpolationDerivative N k x| =
        |∑ r ∈ oddIndices (k + 1), modeSign r * termDerivative N r x| := rfl
    _ ≤ ∑ r ∈ oddIndices (k + 1), |modeSign r * termDerivative N r x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ oddIndices (k + 1),
        M * ((r : ℝ) * Real.exp (-gamma * ((r : ℝ) ^ 2 - 1))) := Finset.sum_le_sum hterm
    _ = M * ∑ r ∈ oddIndices (k + 1),
        (r : ℝ) * Real.exp (-gamma * ((r : ℝ) ^ 2 - 1)) := by rw [Finset.mul_sum]
    _ ≤ M * sumConst := mul_le_mul_of_nonneg_left
      (finite_gaussian_sum_le (oddIndices (k + 1))
        (fun r hr => ((oddIndices_spec (k + 1) r).mp hr).1)) hM0
    _ = derivConst * ((N : ℝ) / (k : ℝ) ^ 3) := by
      dsimp only [M, derivConst]
      ring

private theorem abs_sub_le_of_hasDerivAt_bound {f f' : ℝ → ℝ} {a b M : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    (hdf : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hM : ∀ x ∈ Set.Ioo a b, |f' x| ≤ M) :
    |f b - f a| ≤ M * (b - a) := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f f' hlt hf hdf
    have heq' : f b - f a = f' c * (b - a) := by
      exact ((eq_div_iff (ne_of_gt (sub_pos.mpr hlt))).mp hslope).symm
    calc
      |f b - f a| = |f' c| * (b - a) := by
        rw [heq', abs_mul, abs_of_pos (sub_pos.mpr hlt)]
      _ ≤ M * (b - a) := mul_le_mul_of_nonneg_right (hM c hc) (sub_nonneg.mpr hab)
  · subst b
    simp

private theorem positivePart_adjacent_bound {N k : ℕ} (hN : 2 ≤ N) (hk : 2 ≤ k)
    (hNt : ((k : ℝ) + 1) ^ 2 ≤ (N : ℝ)) :
    |positivePart N (k + 1) - positivePart N k| ≤
      derivConst * ((N : ℝ) / (k : ℝ) ^ 3) := by
  have hends := interpolation_endpoints (N := N) (k := k) (show 1 ≤ N by omega) hk
  have hmain := abs_sub_le_of_hasDerivAt_bound
    (f := interpolation N k) (f' := interpolationDerivative N k)
    (a := (k : ℝ)) (b := (k : ℝ) + 1)
    (M := derivConst * ((N : ℝ) / (k : ℝ) ^ 3))
    (by linarith) (interpolation_continuous (by omega) hk)
    (fun x hx => interpolation_hasDerivAt hN hk hx)
    (fun x hx => interpolationDerivative_bound hN hk hNt hx)
  have hlen : ((k : ℝ) + 1) - (k : ℝ) = 1 := by ring
  simpa only [hends.2, hends.1, hlen, mul_one] using hmain


/-
Offline D1 fragment; no elaboration or kernel result is claimed.
Splice inside the existing noncomputable section and namespace
Shao.OQ4.RademacherAdjacentLogFinite, after C1's
positivePart_adjacent_bound and before E1. The two transparent definitions
may instead occupy their D10/D11 inventory positions after finalConst.
All A1/B1/C1 definitions and frozen private theorem heads remain in scope.
No imports, namespace wrapper, or public theorem are supplied here.
-/

private def timeCutoff : ℝ := max 1 (Real.log (8 * sumConst) / (8 * gamma))
private def heightCutoff : ℕ := Nat.ceil (4 * negConst) + 2

private theorem cutoffs_spec :
    2 ≤ heightCutoff ∧ 1 ≤ timeCutoff ∧
    2 * sumConst * Real.exp (-8 * gamma * timeCutoff) ≤ (1 / 4 : ℝ) ∧
    negConst / (heightCutoff : ℝ) ^ 2 ≤ (1 / 4 : ℝ) := by
  rcases constants_spec with ⟨hγ, hq0, hq1, hS, hA, hB, hD, hE, hL, hC⟩
  have hK : 2 ≤ heightCutoff := by
    dsimp only [heightCutoff]
    omega
  have hT : 1 ≤ timeCutoff := by
    exact le_max_left _ _
  have hTlog : Real.log (8 * sumConst) / (8 * gamma) ≤ timeCutoff := by
    exact le_max_right _ _
  have h8γ : (0 : ℝ) < 8 * gamma := by positivity
  have h8S : (0 : ℝ) < 8 * sumConst := by positivity
  have hlog : Real.log (8 * sumConst) ≤ (8 * gamma) * timeCutoff := by
    simpa only [mul_comm] using (div_le_iff₀ h8γ).1 hTlog
  have harg : -8 * gamma * timeCutoff ≤ -Real.log (8 * sumConst) := by
    nlinarith
  have hexp :
      2 * sumConst * Real.exp (-8 * gamma * timeCutoff) ≤ (1 / 4 : ℝ) := by
    calc
      2 * sumConst * Real.exp (-8 * gamma * timeCutoff) ≤
          2 * sumConst * Real.exp (-Real.log (8 * sumConst)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by positivity)
      _ = (1 / 4 : ℝ) := by
        rw [Real.exp_neg, Real.exp_log h8S]
        field_simp [ne_of_gt hS] <;> ring
  have hKreal : (2 : ℝ) ≤ (heightCutoff : ℝ) := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < (heightCutoff : ℝ) := by linarith
  have hceil : 4 * negConst ≤ (Nat.ceil (4 * negConst) : ℝ) := Nat.le_ceil _
  have hK4 : 4 * negConst ≤ (heightCutoff : ℝ) := by
    dsimp only [heightCutoff]
    push_cast
    linarith
  have hKsq : 4 * negConst ≤ (heightCutoff : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((heightCutoff : ℝ) - 1)]
  have hheight : negConst / (heightCutoff : ℝ) ^ 2 ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos hKpos)).2
    nlinarith
  exact ⟨hK, hT, hexp, hheight⟩

private theorem long_time_domain {N k : ℕ} (hk : heightCutoff ≤ k)
    (hNt : timeCutoff * ((k : ℝ) + 1) ^ 2 ≤ (N : ℝ)) :
    2 ≤ k ∧ 2 ≤ N ∧ ((k : ℝ) + 1) ^ 2 ≤ (N : ℝ) ∧
    timeCutoff ≤ (N : ℝ) / ((k : ℝ) + 1) ^ 2 ∧
    timeCutoff ≤ (N : ℝ) / (k : ℝ) ^ 2 ∧
    (k : ℝ) ≤ (N : ℝ) ∧ (k : ℝ) ^ 2 ≤ (N : ℝ) := by
  rcases cutoffs_spec with ⟨hK, hT, hexp, hheight⟩
  have hk2 : 2 ≤ k := hK.trans hk
  have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hnextpos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have hT0 : 0 ≤ timeCutoff := by linarith
  have hlarge : ((k : ℝ) + 1) ^ 2 ≤ (N : ℝ) := by
    calc
      ((k : ℝ) + 1) ^ 2 = 1 * ((k : ℝ) + 1) ^ 2 := by ring
      _ ≤ timeCutoff * ((k : ℝ) + 1) ^ 2 :=
        mul_le_mul_of_nonneg_right hT (sq_nonneg _)
      _ ≤ (N : ℝ) := hNt
  have hNreal : (2 : ℝ) ≤ (N : ℝ) := by
    nlinarith [sq_nonneg (k : ℝ)]
  have hN2 : 2 ≤ N := by exact_mod_cast hNreal
  have hsquares : (k : ℝ) ^ 2 ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
  have hcurrent : timeCutoff * (k : ℝ) ^ 2 ≤ (N : ℝ) :=
    (mul_le_mul_of_nonneg_left hsquares hT0).trans hNt
  have htnext : timeCutoff ≤ (N : ℝ) / ((k : ℝ) + 1) ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hnextpos)).2 hNt
  have htcurrent : timeCutoff ≤ (N : ℝ) / (k : ℝ) ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hkpos)).2 hcurrent
  have hksq : (k : ℝ) ^ 2 ≤ (N : ℝ) := hsquares.trans hlarge
  have hkN : (k : ℝ) ≤ (N : ℝ) := by
    nlinarith [sq_nonneg ((k : ℝ) - 1)]
  exact ⟨hk2, hN2, hlarge, htnext, htcurrent, hkN, hksq⟩

private theorem normalizedActual_close {N H : ℕ} (hH : heightCutoff ≤ H)
    (hNt : timeCutoff * (H : ℝ) ^ 2 ≤ (N : ℝ)) :
    |normalizedActual N H - 1| ≤ (1 / 2 : ℝ) ∧
    (1 / 2 : ℝ) ≤ normalizedActual N H ∧
    0 < Shao.OQ4.RademacherS2Assembly.p N ((H : ℝ) - 1) := by
  rcases cutoffs_spec with ⟨hK, hT, hexp, hheight⟩
  rcases constants_spec with ⟨hγ, hq0, hq1, hS, hA, hB, hD, hE, hL, hC⟩
  have hH2 : 2 ≤ H := hK.trans hH
  have hHreal : (2 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH2
  have hHpos : (0 : ℝ) < (H : ℝ) := by linarith
  have hHsq : (H : ℝ) ^ 2 ≤ (N : ℝ) := by
    calc
      (H : ℝ) ^ 2 = 1 * (H : ℝ) ^ 2 := by ring
      _ ≤ timeCutoff * (H : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hT (sq_nonneg _)
      _ ≤ (N : ℝ) := hNt
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by
    nlinarith [sq_nonneg ((H : ℝ) - 1)]
  have hN : 1 ≤ N := by exact_mod_cast hNreal
  have htime : timeCutoff ≤ (N : ℝ) / (H : ℝ) ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hHpos)).2 hNt
  have harg : -8 * gamma * ((N : ℝ) / (H : ℝ) ^ 2) ≤
      -8 * gamma * timeCutoff := by
    have hm := mul_le_mul_of_nonneg_left htime (show 0 ≤ 8 * gamma by positivity)
    nlinarith
  have htail : |positivePart N H - 1| ≤ (1 / 4 : ℝ) := by
    calc
      |positivePart N H - 1| ≤
          2 * sumConst * Real.exp (-8 * gamma * ((N : ℝ) / (H : ℝ) ^ 2)) :=
        positivePart_tail_bound hH2 hHsq
      _ ≤ 2 * sumConst * Real.exp (-8 * gamma * timeCutoff) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by positivity)
      _ ≤ (1 / 4 : ℝ) := hexp
  have hKreal : (2 : ℝ) ≤ (heightCutoff : ℝ) := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < (heightCutoff : ℝ) := by linarith
  have hKH : (heightCutoff : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hsquares : (heightCutoff : ℝ) ^ 2 ≤ (H : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hKH)
      (show 0 ≤ (H : ℝ) + (heightCutoff : ℝ) by linarith)]
  have hquot : negConst / (H : ℝ) ^ 2 ≤ negConst / (heightCutoff : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (le_of_lt hE) (sq_pos_of_pos hKpos) hsquares
  have hneg : |negativePart N H| ≤ (1 / 4 : ℝ) :=
    (negativePart_bound hH2 hHsq).trans (hquot.trans hheight)
  have hfac := actual_factorization hN hH2
  have htriangle (a b : ℝ) : |a + b| ≤ |a| + |b| := by
    have ha := abs_le.mp (le_rfl : |a| ≤ |a|)
    have hb := abs_le.mp (le_rfl : |b| ≤ |b|)
    exact abs_le.mpr ⟨by linarith only [ha.1, hb.1], by linarith only [ha.2, hb.2]⟩
  have hclose : |normalizedActual N H - 1| ≤ (1 / 2 : ℝ) := by
    calc
      |normalizedActual N H - 1| = |(positivePart N H - 1) + negativePart N H| := by
        rw [hfac.2]
        congr 1 <;> ring
      _ ≤ |positivePart N H - 1| + |negativePart N H| := htriangle _ _
      _ ≤ (1 / 4 : ℝ) + 1 / 4 := add_le_add htail hneg
      _ = (1 / 2 : ℝ) := by norm_num
  have hlower : (1 / 2 : ℝ) ≤ normalizedActual N H := by
    linarith [(abs_le.mp hclose).1]
  have hp : 0 < Shao.OQ4.RademacherS2Assembly.p N ((H : ℝ) - 1) := by
    rw [hfac.1, ← hfac.2]
    exact mul_pos (scalar_positive hHreal N).2.2 (by linarith)
  exact ⟨hclose, hlower, hp⟩

private theorem normalizedActual_adjacent_bound {N k : ℕ} (hk : heightCutoff ≤ k)
    (hNt : timeCutoff * ((k : ℝ) + 1) ^ 2 ≤ (N : ℝ)) :
    |normalizedActual N (k + 1) - normalizedActual N k| ≤
      (derivConst + 2 * negConst) * ((N : ℝ) / (k : ℝ) ^ 3) := by
  rcases long_time_domain hk hNt with ⟨hk2, hN2, hlarge, htnext, htcurrent, hkN, hksq⟩
  rcases constants_spec with ⟨hγ, hq0, hq1, hS, hA, hB, hD, hE, hL, hC⟩
  have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hnextpos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have hkplus : 2 ≤ k + 1 := by omega
  have hN1 : 1 ≤ N := by omega
  have hnextsq : ((k + 1 : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hlarge
  have hfacnext := (actual_factorization hN1 hkplus).2
  have hfaccurrent := (actual_factorization hN1 hk2).2
  have hpositive := positivePart_adjacent_bound hN2 hk2 hlarge
  have hnegativeNext : |negativePart N (k + 1)| ≤ negConst / ((k : ℝ) + 1) ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using negativePart_bound hkplus hnextsq
  have hnegativeCurrent : |negativePart N k| ≤ negConst / (k : ℝ) ^ 2 :=
    negativePart_bound hk2 hksq
  have hsquares : (k : ℝ) ^ 2 ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
  have hnegativeNext' : |negativePart N (k + 1)| ≤ negConst / (k : ℝ) ^ 2 :=
    hnegativeNext.trans
      (div_le_div_of_nonneg_left (le_of_lt hE) (sq_pos_of_pos hkpos) hsquares)
  have hbase : 1 / (k : ℝ) ^ 2 ≤ (N : ℝ) / (k : ℝ) ^ 3 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hkpos) (pow_pos hkpos 3)).2
    have hm := mul_le_mul_of_nonneg_right hkN (sq_nonneg (k : ℝ))
    nlinarith
  have habsorb : negConst / (k : ℝ) ^ 2 ≤
      negConst * ((N : ℝ) / (k : ℝ) ^ 3) := by
    calc
      negConst / (k : ℝ) ^ 2 = negConst * (1 / (k : ℝ) ^ 2) := by ring
      _ ≤ negConst * ((N : ℝ) / (k : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hbase (le_of_lt hE)
  have htriangle (a b : ℝ) : |a + b| ≤ |a| + |b| := by
    have ha := abs_le.mp (le_rfl : |a| ≤ |a|)
    have hb := abs_le.mp (le_rfl : |b| ≤ |b|)
    exact abs_le.mpr ⟨by linarith only [ha.1, hb.1], by linarith only [ha.2, hb.2]⟩
  have hnegativeDifference : |negativePart N (k + 1) - negativePart N k| ≤
      |negativePart N (k + 1)| + |negativePart N k| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      htriangle (negativePart N (k + 1)) (-negativePart N k)
  calc
    |normalizedActual N (k + 1) - normalizedActual N k| =
        |(positivePart N (k + 1) - positivePart N k) +
          (negativePart N (k + 1) - negativePart N k)| := by
      rw [hfacnext, hfaccurrent]
      congr 1 <;> ring
    _ ≤ |positivePart N (k + 1) - positivePart N k| +
        |negativePart N (k + 1) - negativePart N k| := htriangle _ _
    _ ≤ |positivePart N (k + 1) - positivePart N k| +
        (|negativePart N (k + 1)| + |negativePart N k|) :=
      by linarith only [hnegativeDifference]
    _ ≤ derivConst * ((N : ℝ) / (k : ℝ) ^ 3) +
        (negConst / (k : ℝ) ^ 2 + negConst / (k : ℝ) ^ 2) :=
      add_le_add hpositive (add_le_add hnegativeNext' hnegativeCurrent)
    _ ≤ derivConst * ((N : ℝ) / (k : ℝ) ^ 3) +
        (negConst * ((N : ℝ) / (k : ℝ) ^ 3) +
          negConst * ((N : ℝ) / (k : ℝ) ^ 3)) :=
      by linarith only [habsorb]
    _ = (derivConst + 2 * negConst) * ((N : ℝ) / (k : ℝ) ^ 3) := by ring

private theorem log_lipschitz_half {z w : ℝ} (hz : (1 / 2 : ℝ) ≤ z)
    (hw : (1 / 2 : ℝ) ≤ w) :
    |Real.log z - Real.log w| ≤ 2 * |z - w| := by
  have hordered : ∀ {a b : ℝ}, (1 / 2 : ℝ) ≤ a → a ≤ b →
      |Real.log b - Real.log a| ≤ 2 * (b - a) := by
    intro a b ha hab
    apply abs_sub_le_of_hasDerivAt_bound
      (f := Real.log) (f' := fun x : ℝ => x⁻¹) (M := 2) hab
    · intro x hx
      have hxpos : 0 < x := by linarith [hx.1]
      exact (Real.continuousAt_log (ne_of_gt hxpos)).continuousWithinAt
    · intro x hx
      have hxpos : 0 < x := by linarith [hx.1]
      exact Real.hasDerivAt_log (ne_of_gt hxpos)
    · intro x hx
      have hxpos : 0 < x := by linarith [hx.1]
      rw [abs_of_pos (inv_pos.mpr hxpos)]
      simpa only [one_div] using
        (div_le_iff₀ hxpos).2 (show (1 : ℝ) ≤ 2 * x by linarith [hx.1])
  by_cases hwz : w ≤ z
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hwz)] using hordered hw hwz
  · have hzw : z ≤ w := le_of_lt (lt_of_not_ge hwz)
    calc
      |Real.log z - Real.log w| = |Real.log w - Real.log z| := abs_sub_comm _ _
      _ ≤ 2 * (w - z) := hordered hz hzw
      _ = 2 * |z - w| := by
        rw [abs_sub_comm z w, abs_of_nonneg (sub_nonneg.mpr hzw)]

private theorem normalizedActual_log_adjacent_bound {N k : ℕ}
    (hk : heightCutoff ≤ k)
    (hNt : timeCutoff * ((k : ℝ) + 1) ^ 2 ≤ (N : ℝ)) :
    |Real.log (normalizedActual N (k + 1)) - Real.log (normalizedActual N k)| ≤
      2 * (derivConst + 2 * negConst) * ((N : ℝ) / (k : ℝ) ^ 3) := by
  rcases long_time_domain hk hNt with ⟨hk2, hN2, hlarge, htnext, htcurrent, hkN, hksq⟩
  have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hcurrent : timeCutoff * (k : ℝ) ^ 2 ≤ (N : ℝ) :=
    (le_div_iff₀ (sq_pos_of_pos hkpos)).1 htcurrent
  have hnext : timeCutoff * ((k + 1 : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hNt
  have hknext : heightCutoff ≤ k + 1 := by omega
  have hlowerCurrent : (1 / 2 : ℝ) ≤ normalizedActual N k :=
    (normalizedActual_close hk hcurrent).2.1
  have hlowerNext : (1 / 2 : ℝ) ≤ normalizedActual N (k + 1) :=
    (normalizedActual_close hknext hnext).2.1
  calc
    |Real.log (normalizedActual N (k + 1)) - Real.log (normalizedActual N k)| ≤
        2 * |normalizedActual N (k + 1) - normalizedActual N k| :=
      log_lipschitz_half hlowerNext hlowerCurrent
    _ ≤ 2 * ((derivConst + 2 * negConst) * ((N : ℝ) / (k : ℝ) ^ 3)) :=
      mul_le_mul_of_nonneg_left (normalizedActual_adjacent_bound hk hNt) (by norm_num)
    _ = 2 * (derivConst + 2 * negConst) * ((N : ℝ) / (k : ℝ) ^ 3) := by ring


/-!
Offline E1 tail fragment. Append inside namespace
Shao.OQ4.RademacherAdjacentLogFinite after the frozen A1/B1/C1 implementation.
NOT_ELABORATED / NOT_SERVER_CHECKED. Exactly two frozen private definitions
and four frozen private theorem bodies; no public declaration or E2 assembly.
-/

private def logADerivative (x : ℝ) : ℝ :=
  (1 / x) * (uReal x / (Real.sin (uReal x) * Real.cos (uReal x)) - 1)
private def logRhoDerivative (x : ℝ) : ℝ := (vReal x / x) * Real.tan (vReal x)

private theorem logA_hasDerivAt {x : ℝ} (hx : 2 ≤ x) :
    HasDerivAt (fun y : ℝ => Real.log (aReal y)) (logADerivative x) x := by
  rcases real_angle_domain (r := 1) hx (by norm_num) (by norm_num; linarith) with
    ⟨hu0, hu, hv0, hv, hru0, hru, hrv0, hrv, hsin, hcosv⟩
  have hxp : 0 < x := by linarith
  have hsinu : 0 < Real.sin (uReal x) := by simpa only [Nat.cast_one, one_mul] using hsin
  have hcosu : 0 < Real.cos (uReal x) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have htanu : 0 < Real.tan (uReal x) := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hsinu hcosu
  have hdu : HasDerivAt uReal (-uReal x / x) x := by
    have hfun : uReal = fun y : ℝ => (Real.pi / 4) * y⁻¹ := by
      funext y
      simp only [uReal, div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hfun]
    convert ((hasDerivAt_id x).inv (ne_of_gt hxp)).const_mul (Real.pi / 4) using 1 <;>
      (try simp only [Pi.inv_apply, id_eq]) <;> field_simp [ne_of_gt hxp] <;> ring
  have htan := (Real.hasDerivAt_tan (ne_of_gt hcosu)).comp x hdu
  have hcot : HasDerivAt
      (fun y : ℝ => Real.cos (uReal y) / Real.sin (uReal y))
      (uReal x / (x * Real.sin (uReal x) ^ 2)) x := by
    have hfun : (fun y : ℝ => Real.cos (uReal y) / Real.sin (uReal y)) =
        (fun y : ℝ => (Real.tan (uReal y))⁻¹) := by
      funext y
      simp only [Real.tan_eq_sin_div_cos, inv_div]
    have hinv := htan.inv (ne_of_gt htanu)
    change HasDerivAt (fun y : ℝ => (Real.tan (uReal y))⁻¹) _ x at hinv
    rw [← hfun] at hinv
    convert hinv using 1 <;>
      simp only [Function.comp_apply, Pi.inv_apply, Real.tan_eq_sin_div_cos] <;>
      field_simp [ne_of_gt hxp, ne_of_gt hsinu, ne_of_gt hcosu] <;> ring
  have ha := hcot.div (hasDerivAt_id x) (ne_of_gt hxp)
  have hap : 0 < aReal x := (scalar_positive hx 0).1
  change HasDerivAt
    (fun y : ℝ => Real.log ((Real.cos (uReal y) / Real.sin (uReal y)) / y))
    (logADerivative x) x
  have hlog := ha.log (ne_of_gt hap)
  change HasDerivAt
    (fun y : ℝ => Real.log ((Real.cos (uReal y) / Real.sin (uReal y)) / y)) _ x at hlog
  convert hlog using 1 <;>
    simp only [logADerivative, Function.comp_apply, Pi.div_apply, id_eq] <;>
    field_simp [ne_of_gt hxp, ne_of_gt hsinu, ne_of_gt hcosu] <;> ring

private theorem logRho_hasDerivAt {x : ℝ} (hx : 2 ≤ x) :
    HasDerivAt (fun y : ℝ => Real.log (rhoReal y)) (logRhoDerivative x) x := by
  have hxp : 0 < x := by linarith
  have hdv : HasDerivAt vReal (-vReal x / x) x := by
    have hfun : vReal = fun y : ℝ => (Real.pi / 2) * y⁻¹ := by
      funext y
      simp only [vReal, div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hfun]
    convert ((hasDerivAt_id x).inv (ne_of_gt hxp)).const_mul (Real.pi / 2) using 1 <;>
      (try simp only [Pi.inv_apply, id_eq]) <;> field_simp [ne_of_gt hxp] <;> ring
  have hrhop : 0 < rhoReal x := (scalar_positive hx 0).2.1
  change HasDerivAt (fun y : ℝ => Real.log (Real.cos (vReal y))) (logRhoDerivative x) x
  have hlog := hdv.cos.log (ne_of_gt hrhop)
  change HasDerivAt (fun y : ℝ => Real.log (Real.cos (vReal y))) _ x at hlog
  convert hlog using 1 <;>
    simp only [logRhoDerivative, Function.comp_apply, Real.tan_eq_sin_div_cos] <;> ring

private theorem scalar_log_derivative_bounds {x : ℝ} (hx : 2 ≤ x) :
    |logADerivative x| ≤ ampConst / x ∧
    0 ≤ logRhoDerivative x ∧ logRhoDerivative x ≤ Real.pi ^ 2 / (2 * x ^ 3) := by
  rcases real_angle_domain (r := 1) hx (by norm_num) (by norm_num; linarith) with
    ⟨hu0, hu, hv0, hv, hru0, hru, hrv0, hrv, hsin, hcosv⟩
  have hxp : 0 < x := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have huq : uReal x ≤ Real.pi / 4 := by linarith
  have huhalf : uReal x < Real.pi / 2 := by linarith
  have hvhalf : vReal x < Real.pi / 2 := by linarith
  have hsinu : 0 < Real.sin (uReal x) := by simpa only [Nat.cast_one, one_mul] using hsin
  have hcosu : 0 < Real.cos (uReal x) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  rcases half_angle_bounds hu0.le huhalf with ⟨hsinu_le, hchord, htanu_le⟩
  rcases quarter_angle_bounds hu0 huq with ⟨hcoslower, htanub, hcotub, hcscu, hsecu⟩
  rcases quarter_angle_bounds hv0 hv with ⟨hcosvlower, htanvb, hcotvb, hcscv, hsecv⟩
  have hsqrtp : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have husin : uReal x / Real.sin (uReal x) ≤ Real.pi / 2 := by
    apply (div_le_iff₀ hsinu).2
    calc
      uReal x = (Real.pi / 2) * ((2 / Real.pi) * uReal x) := by
        field_simp [ne_of_gt hpi] <;> ring
      _ ≤ (Real.pi / 2) * Real.sin (uReal x) :=
        mul_le_mul_of_nonneg_left hchord (by positivity)
  have hinvcos : 1 / Real.cos (uReal x) ≤ Real.sqrt 2 := by
    apply (div_le_iff₀ hcosu).2
    have hm := (div_le_iff₀ hsqrtp).mp hcoslower
    nlinarith
  let R : ℝ := uReal x / (Real.sin (uReal x) * Real.cos (uReal x))
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hRbound : R ≤ Real.pi / Real.sqrt 2 := by
    calc
      R = (uReal x / Real.sin (uReal x)) * (1 / Real.cos (uReal x)) := by
        simp only [R, div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ (Real.pi / 2) * Real.sqrt 2 := mul_le_mul husin hinvcos (by positivity) (by positivity)
      _ = Real.pi / Real.sqrt 2 := by
        field_simp [ne_of_gt hsqrtp]
        nlinarith [congrArg (fun z : ℝ => Real.pi * z) hsqrt_sq]
  have hAbound : |logADerivative x| ≤ ampConst / x := by
    calc
      |logADerivative x| = (1 / x) * |R - 1| := by
        dsimp only [logADerivative, R]
        rw [abs_mul, abs_of_pos (one_div_pos.mpr hxp)]
      _ ≤ (1 / x) * (R + 1) :=
        mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩) (by positivity)
      _ ≤ (1 / x) * (Real.pi / Real.sqrt 2 + 1) :=
        mul_le_mul_of_nonneg_left (show R + 1 ≤ Real.pi / Real.sqrt 2 + 1 by linarith only [hRbound]) (by positivity)
      _ = ampConst / x := by dsimp only [ampConst]; ring
  have htanv0 : 0 ≤ Real.tan (vReal x) := by
    have ht := Real.le_tan hv0.le hvhalf
    linarith
  have hRho0 : 0 ≤ logRhoDerivative x := by
    dsimp only [logRhoDerivative]
    exact mul_nonneg (div_pos hv0 hxp).le htanv0
  have hRhoBound : logRhoDerivative x ≤ Real.pi ^ 2 / (2 * x ^ 3) := by
    calc
      logRhoDerivative x ≤ (vReal x / x) * (2 * vReal x) :=
        mul_le_mul_of_nonneg_left htanvb (div_pos hv0 hxp).le
      _ = Real.pi ^ 2 / (2 * x ^ 3) := by
        dsimp only [vReal]
        field_simp [ne_of_gt hxp] <;> ring
  exact ⟨hAbound, hRho0, hRhoBound⟩

private theorem scalar_log_adjacent_bounds {k : ℕ} (hk : 2 ≤ k) :
    |Real.log (aReal ((k : ℝ) + 1)) - Real.log (aReal (k : ℝ))| ≤
      ampConst / (k : ℝ) ∧
    |Real.log (rhoReal ((k : ℝ) + 1)) - Real.log (rhoReal (k : ℝ))| ≤
      Real.pi ^ 2 / (2 * (k : ℝ) ^ 3) := by
  have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkp : (0 : ℝ) < (k : ℝ) := by linarith
  have hL : 0 < ampConst := constants_spec.2.2.2.2.2.2.2.2.1
  have hAdf : ∀ x ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1),
      HasDerivAt (fun y : ℝ => Real.log (aReal y)) (logADerivative x) x := by
    intro x hx
    exact logA_hasDerivAt (le_trans hkreal hx.1)
  have hRdf : ∀ x ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1),
      HasDerivAt (fun y : ℝ => Real.log (rhoReal y)) (logRhoDerivative x) x := by
    intro x hx
    exact logRho_hasDerivAt (le_trans hkreal hx.1)
  have hAc : ContinuousOn (fun y : ℝ => Real.log (aReal y))
      (Set.Icc (k : ℝ) ((k : ℝ) + 1)) := by
    intro x hx
    exact (hAdf x hx).continuousAt.continuousWithinAt
  have hRc : ContinuousOn (fun y : ℝ => Real.log (rhoReal y))
      (Set.Icc (k : ℝ) ((k : ℝ) + 1)) := by
    intro x hx
    exact (hRdf x hx).continuousAt.continuousWithinAt
  have hAb : ∀ x ∈ Set.Ioo (k : ℝ) ((k : ℝ) + 1), |logADerivative x| ≤ ampConst / (k : ℝ) := by
    intro x hx
    have hx2 : 2 ≤ x := by linarith [hx.1]
    have hxp : 0 < x := by linarith
    have hb := (scalar_log_derivative_bounds hx2).1
    refine hb.trans ?_
    apply (div_le_div_iff₀ hxp hkp).2
    exact mul_le_mul_of_nonneg_left hx.1.le hL.le
  have hRb : ∀ x ∈ Set.Ioo (k : ℝ) ((k : ℝ) + 1),
      |logRhoDerivative x| ≤ Real.pi ^ 2 / (2 * (k : ℝ) ^ 3) := by
    intro x hx
    have hx2 : 2 ≤ x := by linarith [hx.1]
    have hxp : 0 < x := by linarith
    rcases (scalar_log_derivative_bounds hx2).2 with ⟨h0, hb⟩
    rw [abs_of_nonneg h0]
    refine hb.trans ?_
    have hCube : (k : ℝ) ^ 3 ≤ x ^ 3 := by gcongr <;> linarith [hx.1]
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * x ^ 3)
      (by positivity : 0 < 2 * (k : ℝ) ^ 3)).2
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hCube (by norm_num)) (sq_nonneg Real.pi)
  have hA := abs_sub_le_of_hasDerivAt_bound
    (f := fun y : ℝ => Real.log (aReal y)) (f' := logADerivative)
    (a := (k : ℝ)) (b := (k : ℝ) + 1) (M := ampConst / (k : ℝ))
    (by linarith) hAc (fun x hx => hAdf x ⟨hx.1.le, hx.2.le⟩) hAb
  have hR := abs_sub_le_of_hasDerivAt_bound
    (f := fun y : ℝ => Real.log (rhoReal y)) (f' := logRhoDerivative)
    (a := (k : ℝ)) (b := (k : ℝ) + 1) (M := Real.pi ^ 2 / (2 * (k : ℝ) ^ 3))
    (by linarith) hRc (fun x hx => hRdf x ⟨hx.1.le, hx.2.le⟩) hRb
  have hlen : ((k : ℝ) + 1) - (k : ℝ) = 1 := by ring
  exact ⟨by simpa only [hlen, mul_one] using hA,
    by simpa only [hlen, mul_one] using hR⟩


/-
OFFLINE TAIL CANDIDATE / NOT ELABORATED.
Insert in the existing noncomputable section and namespace
Shao.OQ4.RademacherAdjacentLogFinite after the frozen E1 scalar lemmas.
No import, namespace change, additional definition, or extra global helper.
The preceding frozen A/B/C/D/E1 declarations must have complete proofs.
-/

private theorem actual_probability_mono (N : ℕ) {h h' : ℝ} (hh : h ≤ h') :
    Shao.OQ4.RademacherS2Assembly.p N h ≤ Shao.OQ4.RademacherS2Assembly.p N h' := by
  unfold Shao.OQ4.RademacherS2Assembly.p
  letI : MeasureTheory.IsProbabilityMeasure Shao.OQ4.RademacherCosine.law :=
    Shao.OQ4.RademacherCosine.law_isProbabilityMeasure
  haveI : MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.Measure.pi (fun _ : Fin N => Shao.OQ4.RademacherCosine.law)) := inferInstance
  refine MeasureTheory.measureReal_mono ?_ (MeasureTheory.measure_ne_top _ _)
  intro a ha
  intro j hj
  exact (ha j hj).trans hh

private theorem adjacent_log_decomposition {N k : ℕ} (hk : heightCutoff ≤ k)
    (hNt : timeCutoff * ((k : ℝ) + 1) ^ 2 ≤ (N : ℝ)) :
    Real.log (Shao.OQ4.RademacherS2Assembly.p N (k : ℝ)) -
        Real.log (Shao.OQ4.RademacherS2Assembly.p N ((k : ℝ) - 1)) =
      (Real.log (aReal ((k : ℝ) + 1)) - Real.log (aReal (k : ℝ))) +
      (N : ℝ) * (Real.log (rhoReal ((k : ℝ) + 1)) - Real.log (rhoReal (k : ℝ))) +
      (Real.log (normalizedActual N (k + 1)) - Real.log (normalizedActual N k)) := by
  have hdom := long_time_domain hk hNt
  have hk2 : 2 ≤ k := hdom.1
  have hkr : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hknonneg : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hT : 0 ≤ timeCutoff := le_trans (by norm_num) cutoffs_spec.2.1
  have hNk : timeCutoff * (k : ℝ) ^ 2 ≤ (N : ℝ) := by
    calc
      timeCutoff * (k : ℝ) ^ 2 ≤ timeCutoff * ((k : ℝ) + 1) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hT
        nlinarith
      _ ≤ (N : ℝ) := hNt
  have hkplus : heightCutoff ≤ k + 1 := le_trans hk (Nat.le_succ k)
  have hNplus : timeCutoff * ((k + 1 : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hNt
  have hpk := (normalizedActual_close hk hNk).2.2
  have hpplus := (normalizedActual_close hkplus hNplus).2.2
  have hlog_formula (H : ℕ) (hH : (2 : ℝ) ≤ (H : ℝ))
      (hp : 0 < Shao.OQ4.RademacherS2Assembly.p N ((H : ℝ) - 1)) :
      Real.log (Shao.OQ4.RademacherS2Assembly.p N ((H : ℝ) - 1)) =
        Real.log (aReal (H : ℝ)) + (N : ℝ) * Real.log (rhoReal (H : ℝ)) +
          Real.log (normalizedActual N H) := by
    rcases scalar_positive hH N with ⟨ha, hrho, hnormalizer⟩
    have heq : Real.log (normalizedActual N H) =
        Real.log (Shao.OQ4.RademacherS2Assembly.p N ((H : ℝ) - 1)) -
          (Real.log (aReal (H : ℝ)) + (N : ℝ) * Real.log (rhoReal (H : ℝ))) := by
      rw [normalizedActual, Real.log_div (ne_of_gt hp) (ne_of_gt hnormalizer)]
      rw [normalizer, Real.log_mul (ne_of_gt ha) (ne_of_gt (pow_pos hrho N)),
        Real.log_pow]
    linarith
  have hlo := hlog_formula k hkr hpk
  have hhi := hlog_formula (k + 1) (by
    simp only [Nat.cast_add, Nat.cast_one]
    linarith) hpplus
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hhi
  linarith

private theorem adjacent_log_upper {N k : ℕ} (hk : heightCutoff ≤ k)
    (hNt : timeCutoff * ((k : ℝ) + 1) ^ 2 ≤ (N : ℝ)) :
    Real.log (Shao.OQ4.RademacherS2Assembly.p N (k : ℝ)) -
        Real.log (Shao.OQ4.RademacherS2Assembly.p N ((k : ℝ) - 1)) ≤
      finalConst * ((N : ℝ) / (k : ℝ) ^ 3) := by
  have hdom := long_time_domain hk hNt
  have hk2 : 2 ≤ k := hdom.1
  have hkr : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hNk2 : (k : ℝ) ^ 2 ≤ (N : ℝ) := hdom.2.2.2.2.2.2
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  rcases constants_spec with ⟨hgamma, hq, hq1, hsum, hcoeffA, hcoeffB,
    hderiv, hneg, hamp, hfinal⟩
  rcases scalar_log_adjacent_bounds hk2 with ⟨hA, hR⟩
  have hZ := normalizedActual_log_adjacent_bound hk hNt
  have hscale : 1 / (k : ℝ) ≤ (N : ℝ) / (k : ℝ) ^ 3 := by
    apply (div_le_div_iff₀ hkpos (pow_pos hkpos 3)).2
    nlinarith [mul_nonneg (le_of_lt hkpos) (sub_nonneg.mpr hNk2)]
  have hA' : |Real.log (aReal ((k : ℝ) + 1)) - Real.log (aReal (k : ℝ))| ≤
      ampConst * ((N : ℝ) / (k : ℝ) ^ 3) := by
    apply le_trans hA
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hscale (le_of_lt hamp)
  have hR' : (N : ℝ) *
      (Real.log (rhoReal ((k : ℝ) + 1)) - Real.log (rhoReal (k : ℝ))) ≤
      (Real.pi ^ 2 / 2) * ((N : ℝ) / (k : ℝ) ^ 3) := by
    calc
      _ ≤ (N : ℝ) * |Real.log (rhoReal ((k : ℝ) + 1)) -
          Real.log (rhoReal (k : ℝ))| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hN0
      _ ≤ (N : ℝ) * (Real.pi ^ 2 / (2 * (k : ℝ) ^ 3)) :=
        mul_le_mul_of_nonneg_left hR hN0
      _ = (Real.pi ^ 2 / 2) * ((N : ℝ) / (k : ℝ) ^ 3) := by ring
  rw [adjacent_log_decomposition hk hNt]
  have hAa := le_trans (le_abs_self _) hA'
  have hZa := le_trans (le_abs_self _) hZ
  unfold finalConst
  nlinarith

theorem finite_adjacent_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, 2 ≤ K ∧ ∃ T : ℝ, 1 ≤ T ∧
      ∀ N k : ℕ, K ≤ k →
        T * ((k : ℝ) + 1) ^ 2 ≤ (N : ℝ) →
        0 < Shao.OQ4.RademacherS2Assembly.p N (k : ℝ) ∧
        0 < Shao.OQ4.RademacherS2Assembly.p N ((k : ℝ) - 1) ∧
        0 ≤ Real.log (Shao.OQ4.RademacherS2Assembly.p N (k : ℝ)) -
          Real.log (Shao.OQ4.RademacherS2Assembly.p N ((k : ℝ) - 1)) ∧
        Real.log (Shao.OQ4.RademacherS2Assembly.p N (k : ℝ)) -
          Real.log (Shao.OQ4.RademacherS2Assembly.p N ((k : ℝ) - 1)) ≤
          C * ((N : ℝ) / (k : ℝ) ^ 3) := by
  rcases constants_spec with ⟨hgamma, hq, hq1, hsum, hcoeffA, hcoeffB,
    hderiv, hneg, hamp, hfinal⟩
  refine ⟨finalConst, hfinal, heightCutoff, cutoffs_spec.1,
    timeCutoff, cutoffs_spec.2.1, ?_⟩
  intro N k hk hNt
  have hdom := long_time_domain hk hNt
  have hk2 : 2 ≤ k := hdom.1
  have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hT : 0 ≤ timeCutoff := le_trans (by norm_num) cutoffs_spec.2.1
  have hNk : timeCutoff * (k : ℝ) ^ 2 ≤ (N : ℝ) := by
    calc
      timeCutoff * (k : ℝ) ^ 2 ≤ timeCutoff * ((k : ℝ) + 1) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hT
        nlinarith
      _ ≤ (N : ℝ) := hNt
  have hpLow := (normalizedActual_close hk hNk).2.2
  have hpHigh : 0 < Shao.OQ4.RademacherS2Assembly.p N (k : ℝ) := by
    have hkplus : heightCutoff ≤ k + 1 := le_trans hk (Nat.le_succ k)
    have hNplus : timeCutoff * ((k + 1 : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hNt
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using
      (normalizedActual_close hkplus hNplus).2.2
  refine ⟨hpHigh, hpLow, ?_, adjacent_log_upper hk hNt⟩
  apply sub_nonneg.mpr
  apply Real.log_le_log hpLow
  exact actual_probability_mono N (by linarith)

end Shao.OQ4.RademacherAdjacentLogFinite

end
