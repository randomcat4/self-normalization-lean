/- Declaration preparation only: no production proof bodies and no Lean/AX grant.
   Actual late-omitted real-suffix probability bill, with the same tau/nu/sigma. -/
import Shao.Probability.SourcePermutationReveal
import Shao.Probability.SourceSuffixMomentBudgets
import Shao.Probability.SourceIIDGaussianProfileBudget
import Shao.C2.AdaptiveRevealCutoff
import Shao.C2.AuxiliaryRealMarkedFiniteCutoffBudget
import Shao.C2.AuxiliaryThirdMomentTruncation
import Shao.C2.AuxiliaryLowEnergyGaussian
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.Ring.GeomSum

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
noncomputable section
namespace Shao.Probability.SourceLateOmittedSuffixBudget
open MeasureTheory ProbabilityTheory
open SourcePermutationReveal
open scoped BigOperators Classical NNReal

local instance labelPermMeasurableSpace (n : ℕ) : MeasurableSpace (LabelPerm n) := ⊤

private theorem los_finite_geometric_grid_integrals
    (c b H : ℝ) (hc : 0 < c) (hb : 1 ≤ b) (hbH : b ≤ H)
    (N m : ℕ) (hm : 1 ≤ m) (hmH : (m : ℝ) ≤ 2 * H) :
    let I : Set ℝ := Set.Ioo 0 (1 / b)
    let shifted : ℝ → ℝ := fun s =>
      Real.rpow s (-(1 / 2 : ℝ)) *
        ∑ k ∈ Finset.range N, Real.exp (-c * (s + 1 / H) * (k : ℝ))
    let ordinary : ℝ → ℝ := fun s =>
      Real.rpow s (-(1 / 2 : ℝ)) *
        ∑ k ∈ Finset.range (min N m), Real.exp (-c * s * (k : ℝ))
    IntegrableOn shifted I ∧ IntegrableOn ordinary I ∧
      (∫ s : ℝ in I, shifted s) ≤ (2 + 4 / c) * Real.sqrt H ∧
      (∫ s : ℝ in I, ordinary s) ≤ 8 * (1 + 1 / c) * Real.sqrt H := by
  classical
  intro I shifted ordinary
  have hb0 : 0 < b := by linarith
  have hH : 0 < H := lt_of_lt_of_le hb0 hbH
  have hH1 : 1 ≤ H := hb.trans hbH
  have hB : 0 < 1 / b := one_div_pos.2 hb0
  let p : ℝ → ℝ := fun s => Real.rpow s (-(1 / 2 : ℝ))
  have hpnn (s : ℝ) (hs : 0 ≤ s) : 0 ≤ p s := Real.rpow_nonneg hs _
  have hpower (B : ℝ) (hB : 0 < B) :
      IntegrableOn p (Set.Ioc 0 B) ∧ (∫ s : ℝ in Set.Ioc 0 B, p s) = 2 * Real.sqrt B := by
    have hi : IntervalIntegrable p volume 0 B :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hB.le).mp hi, ?_⟩
    rw [← intervalIntegral.integral_of_le hB.le]
    dsimp [p]
    rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
    norm_num [Real.sqrt_eq_rpow]
    ring
  have hmin (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
      IntegrableOn (fun s : ℝ => p s * min A (1 / s)) (Set.Ioo 0 B) ∧
        (∫ s : ℝ in Set.Ioo 0 B, p s * min A (1 / s)) ≤ 4 * Real.sqrt A := by
    let q : ℝ := 1 / A
    let S : Set ℝ := Set.Ioc 0 q
    let V : Set ℝ := Set.Ioi q
    let L : ℝ → ℝ := fun s => Real.rpow s (-3 / 2 : ℝ)
    let G : ℝ → ℝ := fun s => A * S.indicator p s + V.indicator L s
    let F : ℝ → ℝ := (Set.Ioo 0 B).indicator (fun s => p s * min A (1 / s))
    have hq : 0 < q := one_div_pos.2 hA
    have hpi : Integrable (S.indicator p) volume :=
      (integrable_indicator_iff measurableSet_Ioc).2 (hpower q hq).1
    have hli : IntegrableOn L V := integrableOn_Ioi_rpow_of_lt (by norm_num) hq
    have hLi : Integrable (V.indicator L) volume :=
      (integrable_indicator_iff measurableSet_Ioi).2 hli
    have hGi : Integrable G volume := (hpi.const_mul A).add hLi
    have hSnn (s : ℝ) : 0 ≤ S.indicator p s := by
      by_cases hs : s ∈ S
      · rw [Set.indicator_of_mem hs]; exact hpnn s hs.1.le
      · rw [Set.indicator_of_notMem hs]
    have hVnn (s : ℝ) : 0 ≤ V.indicator L s := by
      by_cases hs : s ∈ V
      · rw [Set.indicator_of_mem hs]
        exact Real.rpow_nonneg (hq.le.trans hs.le) _
      · rw [Set.indicator_of_notMem hs]
    have hGnn (s : ℝ) : 0 ≤ G s := add_nonneg (mul_nonneg hA.le (hSnn s)) (hVnn s)
    have hFnn (s : ℝ) : 0 ≤ F s := by
      by_cases hs : s ∈ Set.Ioo 0 B
      · dsimp only [F]
        rw [Set.indicator_of_mem hs]
        exact mul_nonneg (hpnn s hs.1.le) (le_min hA.le (one_div_nonneg.2 hs.1.le))
      · dsimp only [F]
        rw [Set.indicator_of_notMem hs]
    have hpoint (s : ℝ) : F s ≤ G s := by
      by_cases hs : s ∈ Set.Ioo 0 B
      · dsimp only [F]
        rw [Set.indicator_of_mem hs]
        by_cases hsq : s ≤ q
        · have hmS : s ∈ S := ⟨hs.1, hsq⟩
          have hmV : s ∉ V := not_lt_of_ge hsq
          dsimp [G]
          rw [Set.indicator_of_mem hmS, Set.indicator_of_notMem hmV, add_zero]
          nlinarith only [mul_le_mul_of_nonneg_left (min_le_left A (1 / s)) (hpnn s hs.1.le)]
        · have hmV : s ∈ V := lt_of_not_ge hsq
          have hmS : s ∉ S := fun hh => hsq hh.2
          dsimp [G]
          rw [Set.indicator_of_notMem hmS, Set.indicator_of_mem hmV, mul_zero, zero_add]
          have hp : p s * (1 / s) = L s := by
            dsimp [p, L]
            calc
              _ = s ^ (-(1 / 2 : ℝ)) * s ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]; simp only [one_div]
              _ = s ^ (-(1 / 2 : ℝ) + (-1 : ℝ)) := by rw [Real.rpow_add hs.1]
              _ = _ := by congr 1 <;> norm_num
          exact (mul_le_mul_of_nonneg_left (min_le_right A (1 / s)) (hpnn s hs.1.le)).trans_eq hp
      · dsimp only [F]
        rw [Set.indicator_of_notMem hs]
        exact hGnn s
    have hFm : Measurable F := by
      exact (by dsimp [p]; fun_prop : Measurable (fun s : ℝ => p s * min A (1 / s))).indicator measurableSet_Ioo
    have hFi : Integrable F volume := hGi.mono' hFm.aestronglyMeasurable
      (ae_of_all _ fun s => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hFnn s)] using hpoint s)
    have hFint := integral_mono hFi hGi hpoint
    have htail : (∫ s : ℝ in V, L s) = 2 * Real.sqrt A := by
      have hh := integral_Ioi_rpow_of_lt (a := (-3 / 2 : ℝ)) (by norm_num) hq
      convert hh using 1
      dsimp [q]
      norm_num
      rw [Real.rpow_neg (inv_nonneg.mpr hA.le), ← Real.sqrt_eq_rpow, Real.sqrt_inv, inv_inv]
      ring
    have hGval : (∫ s : ℝ, G s) = 4 * Real.sqrt A := by
      dsimp [G]
      rw [integral_add (hpi.const_mul A) hLi, integral_const_mul,
        integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioi,
        (hpower q hq).2, htail]
      dsimp [q]
      rw [one_div, Real.sqrt_inv]
      have hsp : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
      field_simp
      nlinarith [Real.sq_sqrt hA.le]
    refine ⟨(integrable_indicator_iff measurableSet_Ioo).1 hFi, ?_⟩
    dsimp [F] at hFint
    rw [integral_indicator measurableSet_Ioo, hGval] at hFint
    exact hFint
  have hgeo (v : ℝ) (hv : 0 < v) (L : ℕ) :
      (∑ k ∈ Finset.range L, Real.exp (-v * (k : ℝ))) ≤ (L : ℝ) ∧
        (∑ k ∈ Finset.range L, Real.exp (-v * (k : ℝ))) ≤ 1 + 1 / v := by
    let q : ℝ := Real.exp (-v)
    have hq0 : 0 ≤ q := (Real.exp_pos _).le
    have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by linarith)
    have he (k : ℕ) : Real.exp (-v * (k : ℝ)) = q ^ k := by
      dsimp [q]
      rw [← Real.exp_nat_mul]
      congr 1 <;> ring
    simp_rw [he]
    constructor
    · exact (Finset.sum_le_sum fun k _ => pow_le_one₀ hq0 hq1.le).trans_eq (by simp)
    · have hden : 0 < 1 - q := sub_pos.2 hq1
      have hg : (∑ k ∈ Finset.range L, q ^ k) ≤ 1 / (1 - q) := by
        apply (le_div_iff₀ hden).2
        have hh := geom_sum_mul q L
        nlinarith only [hh, pow_nonneg hq0 L]
      apply hg.trans
      apply (div_le_iff₀ hden).2
      have hgap : (v + 1) * q ≤ 1 := by
        have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp v) hq0
        have heq : Real.exp v * q = 1 := by
          dsimp [q]
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        rwa [heq] at hh
      have heq : (1 + 1 / v) * (1 - q) = ((v + 1) * (1 - q)) / v := by
        field_simp <;> ring
      rw [heq]
      apply (le_div_iff₀ hv).2
      nlinarith only [hgap]
  have hpi : IntegrableOn p I := (hpower (1 / b) hB).1.mono_set Set.Ioo_subset_Ioc_self
  have hpval : (∫ s : ℝ in I, p s) = 2 * Real.sqrt (1 / b) := by
    have hh := (hpower (1 / b) hB).2
    rwa [integral_Ioc_eq_integral_Ioo] at hh
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hMinH := hmin H (1 / b) hH hB
  have hMinM := hmin (m : ℝ) (1 / b) hm0 hB
  have hsm : Measurable shifted := by dsimp [shifted]; fun_prop
  have hom : Measurable ordinary := by dsimp [ordinary]; fun_prop
  have hsnn (s : ℝ) (hs : s ∈ I) : 0 ≤ shifted s := by
    exact mul_nonneg (hpnn s hs.1.le) (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)
  have hon (s : ℝ) (hs : s ∈ I) : 0 ≤ ordinary s := by
    exact mul_nonneg (hpnn s hs.1.le) (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)
  have hsBound (s : ℝ) (hs : s ∈ I) : shifted s ≤ (N : ℝ) * p s := by
    have hp := (hgeo (c * (s + 1 / H)) (mul_pos hc (add_pos hs.1 (one_div_pos.2 hH))) N).1
    have he : (∑ k ∈ Finset.range N, Real.exp (-(c * (s + 1 / H)) * (k : ℝ))) =
        ∑ k ∈ Finset.range N, Real.exp (-c * (s + 1 / H) * (k : ℝ)) := by congr 1 <;> simp [neg_mul]
    rw [he] at hp
    change p s * _ ≤ _
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp (hpnn s hs.1.le)
  have hoBound (s : ℝ) (hs : s ∈ I) : ordinary s ≤ (min N m : ℕ) * p s := by
    have hp : (∑ k ∈ Finset.range (min N m), Real.exp (-c * s * (k : ℝ))) ≤ (min N m : ℕ) := by
      simpa only [neg_mul] using (hgeo (c * s) (mul_pos hc hs.1) (min N m)).1
    change p s * _ ≤ _
    exact (mul_le_mul_of_nonneg_left hp (hpnn s hs.1.le)).trans_eq (mul_comm _ _)
  have hsi : IntegrableOn shifted I := (hpi.const_mul (N : ℝ)).mono' hsm.aestronglyMeasurable
    (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hsnn s hs)] using hsBound s hs)
  have hoi : IntegrableOn ordinary I := (hpi.const_mul (min N m : ℕ)).mono' hom.aestronglyMeasurable
    (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hon s hs)] using hoBound s hs)
  refine ⟨hsi, hoi, ?_, ?_⟩
  · have hpoint (s : ℝ) (hs : s ∈ I) : shifted s ≤
        p s + (1 / c) * (p s * min H (1 / s)) := by
      have hs0 : 0 < s := hs.1
      have hq : 0 < 1 / H := one_div_pos.2 hH
      have hsum : (∑ k ∈ Finset.range N, Real.exp (-c * (s + 1 / H) * (k : ℝ))) ≤ 1 + 1 / (c * (s + 1 / H)) := by
        simpa only [neg_mul] using (hgeo (c * (s + 1 / H)) (mul_pos hc (add_pos hs0 hq)) N).2
      have hminv : 1 / (s + 1 / H) ≤ min H (1 / s) := by
        apply le_min
        · apply (div_le_iff₀ (add_pos hs0 hq)).2
          have hHQ : H * (1 / H) = 1 := by field_simp
          nlinarith only [hHQ, mul_nonneg hH.le hs0.le]
        · exact div_le_div_of_nonneg_left zero_le_one hs0 (le_add_of_nonneg_right hq.le)
      have hi : 1 / (c * (s + 1 / H)) = (1 / c) * (1 / (s + 1 / H)) := by field_simp <;> ring
      rw [hi] at hsum
      have hh := hsum.trans (add_le_add_right (mul_le_mul_of_nonneg_left hminv (one_div_nonneg.2 hc.le)) 1)
      change p s * _ ≤ _
      calc
        _ ≤ p s * (1 + 1 / c * min H (1 / s)) := mul_le_mul_of_nonneg_left hh (hpnn s hs.1.le)
        _ = _ := by ring
    have hu := setIntegral_mono_on hsi (hpi.add (hMinH.1.const_mul (1 / c))) measurableSet_Ioo hpoint
    change (∫ s : ℝ in I, shifted s) ≤ (∫ s : ℝ in I, p s + (1 / c) * (p s * min H (1 / s))) at hu
    rw [integral_add hpi (hMinH.1.const_mul (1 / c)), integral_const_mul, hpval] at hu
    have hBH : 1 / b ≤ H := (div_le_one hb0).2 hb |>.trans hH1
    have hsB := Real.sqrt_le_sqrt hBH
    have hh := mul_le_mul_of_nonneg_left hMinH.2 (one_div_nonneg.2 hc.le)
    dsimp only [I] at hu ⊢
    simp only [div_eq_mul_inv, one_mul] at hu hh hsB ⊢
    nlinarith only [hu, hh, hsB]
  · let A : ℝ := 1 + 1 / c
    have hA : 1 ≤ A := by
      have hh : 0 ≤ 1 / c := one_div_nonneg.2 hc.le
      dsimp [A]; linarith
    have hA0 : 0 ≤ A := zero_le_one.trans hA
    have hpoint (s : ℝ) (hs : s ∈ I) : ordinary s ≤ A * (p s * min (m : ℝ) (1 / s)) := by
      have hs0 : 0 < s := hs.1
      have hs1 : s ≤ 1 := hs.2.le.trans ((div_le_one hb0).2 hb)
      have hg :
          (∑ k ∈ Finset.range (min N m), Real.exp (-c * s * (k : ℝ))) ≤ (min N m : ℕ) ∧
          (∑ k ∈ Finset.range (min N m), Real.exp (-c * s * (k : ℝ))) ≤ 1 + 1 / (c * s) := by
        simpa only [neg_mul] using hgeo (c * s) (mul_pos hc hs0) (min N m)
      have hcount : (min N m : ℕ) ≤ (m : ℝ) := by exact_mod_cast Nat.min_le_right N m
      have hfirst : (∑ k ∈ Finset.range (min N m), Real.exp (-c * s * (k : ℝ))) ≤ A * (m : ℝ) :=
        hg.1.trans (hcount.trans (le_mul_of_one_le_left hm0.le hA))
      have hlast : 1 + 1 / (c * s) ≤ A / s := by
        apply (le_div_iff₀ hs0).2
        have hh : (1 / (c * s)) * s = 1 / c := by field_simp <;> ring
        dsimp [A]
        nlinarith only [hh, hs1]
      have hsecond := hg.2.trans hlast
      have hsum := le_min hfirst hsecond
      rw [div_eq_mul_inv, ← one_div, ← mul_min_of_nonneg _ _ hA0] at hsum
      change p s * _ ≤ _
      calc
        _ ≤ p s * (A * min (m : ℝ) (1 / s)) := mul_le_mul_of_nonneg_left hsum (hpnn s hs.1.le)
        _ = _ := by ring
    have hu := setIntegral_mono_on hoi (hMinM.1.const_mul A) measurableSet_Ioo hpoint
    rw [integral_const_mul] at hu
    have hh := mul_le_mul_of_nonneg_left hMinM.2 hA0
    have hsM : Real.sqrt (m : ℝ) ≤ 2 * Real.sqrt H := by
      apply (Real.sqrt_le_iff).2
      constructor
      · positivity
      · nlinarith only [hmH, Real.sq_sqrt hH.le]
    have hh2 := mul_le_mul_of_nonneg_left hsM (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hA0)
    dsimp [A] at hu hh hh2
    nlinarith only [hu, hh, hh2]

private theorem los_iid_omitted_suffix_grids :
    ∃ Cgrid : ℝ, 0 < Cgrid ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho],
        Integrable (fun z : ℝ => z ^ 2) rho →
        Integrable (fun z : ℝ => |z| ^ 3) rho →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        let h0 : ℝ := 4 * beta ^ 2
        ∀ H : ℝ, h0 ≤ H → ∀ N : ℕ,
          let m : ℕ := ⌈H⌉₊
          let Pt : (k : ℕ) → Measure (Shao.Path (k + 1)) :=
            fun k => Measure.pi (fun _ : Fin (k + 1) => rho)
          let low : (k : ℕ) → Shao.Path (k + 1) → ℝ := fun k v =>
            if 0 < Shao.energy v ∧ h0 ≤ Shao.energy v ∧ Shao.energy v < H then
              |v 0| ^ 3 / Real.sqrt (Shao.energy v) *
                (1 + |Shao.prefixSum v (k + 1)| / Real.sqrt (Shao.energy v)) ^ 5
            else 0
          let ordinary : (k : ℕ) → Shao.Path (k + 1) → ℝ := fun k v =>
            if 0 < Shao.energy v ∧ h0 ≤ Shao.energy v then
              |v 0| ^ 3 / Real.sqrt (Shao.energy v) *
                (1 + |Shao.prefixSum v (k + 1)| / Real.sqrt (Shao.energy v)) ^ 5
            else 0
          (∀ k : ℕ, Measurable (low k) ∧ Integrable (low k) (Pt k) ∧
            Measurable (ordinary k) ∧ Integrable (ordinary k) (Pt k)) ∧
            ((∑ k ∈ Finset.range N, ∫ v, low k v ∂Pt k) +
              ∑ k ∈ Finset.range (min N m), ∫ v, ordinary k v ∂Pt k) ≤
              Cgrid * beta * Real.sqrt H
 := by
  classical
  let c : ℝ := (1 - Real.exp (-2)) / 8
  have hc : 0 < c := by
    have he : Real.exp (-2) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
    dsimp [c]; positivity
  obtain ⟨CF, hCF, hF⟩ :=
    Shao.C2.AuxiliaryRealMarkedFiniteCutoffBudget.auxiliary_actual_real_marked_finite_cutoff_budget
      (5 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
  obtain ⟨CS, hCS, hS⟩ := iid_marked_cutoff_inverse_moments 5 1 (Or.inl rfl)
  refine ⟨CF * (2 + 4 / c) + 8 * CS * (1 + 1 / c), by positivity, ?_⟩
  intro rho hrho h2 h3 hmean hnorm beta h0 H hH0 N m Pt low ordinary
  letI : IsProbabilityMeasure rho := hrho
  have hbeta : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one rho h2 h3 hnorm
  have hbeta0 : 0 ≤ beta := zero_le_one.trans hbeta
  have hh01 : 1 ≤ h0 := by dsimp [h0]; nlinarith
  have hh0 : 0 < h0 := lt_of_lt_of_le zero_lt_one hh01
  have hH : 0 < H := lt_of_lt_of_le hh0 hH0
  have hret : (1 / 2 : ℝ) ≤ ∫ z : ℝ, if z ^ 2 ≤ h0 then z ^ 2 else 0 ∂rho :=
    (Shao.C2.AuxiliaryThirdMomentTruncation.auxiliary_actual_third_moment_retains_half rho h2 h3 hnorm).2
  have hm : 1 ≤ m := by dsimp [m]; exact Nat.one_le_ceil_iff.2 hH
  have hmH : (m : ℝ) ≤ 2 * H := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ H from hH.le)
    dsimp only [m]
    have : 1 ≤ H := hh01.trans hH0
    linarith
  let I : Set ℝ := Set.Ioo 0 (1 / h0)
  let a3 : ℝ → ℝ := fun s => ∫ z : ℝ, |z| ^ 3 * Real.exp (-s * z ^ 2) ∂rho
  let KL : ℕ → ℝ → ℝ := fun k s =>
    Real.rpow s (-(1 / 2 : ℝ)) * a3 (s / 2) * Real.exp (-c * (s + 1 / H) * (k : ℝ))
  let KO : ℕ → ℝ → ℝ := fun k s =>
    Real.rpow s (-(1 / 2 : ℝ)) * a3 (s / 2) * Real.exp (-c * s * (k : ℝ))
  have hpow (T : ℝ) (hT : 0 ≤ T) : Real.rpow T (-(1 / 2 : ℝ)) = 1 / Real.sqrt T := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_neg hT, ← Real.sqrt_eq_rpow, one_div]
  have hlow (k : ℕ) : Integrable (low k) (Pt k) ∧ IntegrableOn (KL k) I ∧
      (∫ v, low k v ∂Pt k) ≤ CF * ∫ s : ℝ in I, KL k s := by
    have hh := hF rho h2 hmean hnorm k h0 H hh0 hH0
    let F : Shao.Path (k + 1) → ℝ := fun v =>
      if 0 < Shao.energy v ∧ h0 ≤ Shao.energy v ∧ Shao.energy v < H then
        |v 0| ^ 3 * Real.rpow (Shao.energy v) (-(1 / 2 : ℝ)) *
          Real.rpow (1 + |Shao.prefixSum v (k + 1)| / Real.sqrt (Shao.energy v)) (5 : ℝ)
      else 0
    have heq : F = low k := by
      funext v
      dsimp only [F, low]
      split_ifs with hv
      · rw [hpow _ hv.1.le]
        norm_num [Real.rpow_natCast, div_eq_mul_inv]
      · rfl
    dsimp only at hh
    simp only [if_pos hret] at hh
    norm_num only at hh
    change Integrable F (Pt k) ∧ IntegrableOn (KL k) I ∧
      (∫ v, F v ∂Pt k) ≤ CF * ∫ s : ℝ in I, KL k s at hh
    rwa [heq] at hh
  have hord (k : ℕ) : Integrable (ordinary k) (Pt k) ∧ IntegrableOn (KO k) I ∧
      (∫ v, ordinary k v ∂Pt k) ≤ CS * ∫ s : ℝ in I, KO k s := by
    have hh := hS rho h2 hmean hnorm k h0 hh0
    dsimp only at hh
    simp only [if_pos hret, pow_one] at hh
    norm_num only at hh
    exact hh
  have hmeas (k : ℕ) : Measurable (low k) ∧ Measurable (ordinary k) := by
    have hT : Measurable (Shao.energy : Shao.Path (k + 1) → ℝ) := Shao.measurable_energy
    have hd : Measurable (fun v : Shao.Path (k + 1) => Shao.prefixSum v (k + 1)) :=
      Shao.measurable_prefixSum (k + 1)
    have hM : Measurable (fun v : Shao.Path (k + 1) => |v 0| ^ 3) := by fun_prop
    constructor
    · apply Measurable.ite
      · exact (measurableSet_lt measurable_const hT).inter ((measurableSet_le measurable_const hT).inter
          (measurableSet_lt hT measurable_const))
      · fun_prop
      · fun_prop
    · apply Measurable.ite
      · exact (measurableSet_lt measurable_const hT).inter (measurableSet_le measurable_const hT)
      · fun_prop
      · fun_prop
  refine ⟨fun k => ⟨(hmeas k).1, (hlow k).1, (hmeas k).2, (hord k).1⟩, ?_⟩
  have ha3 (s : ℝ) (hs : 0 ≤ s) : 0 ≤ a3 s ∧ a3 s ≤ beta := by
    have hmi : Measurable (fun z : ℝ => |z| ^ 3 * Real.exp (-s * z ^ 2)) := by fun_prop
    have hnn (z : ℝ) : 0 ≤ |z| ^ 3 * Real.exp (-s * z ^ 2) := by positivity
    have hle (z : ℝ) : |z| ^ 3 * Real.exp (-s * z ^ 2) ≤ |z| ^ 3 := by
      exact mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg z]))
    have hi : Integrable (fun z : ℝ => |z| ^ 3 * Real.exp (-s * z ^ 2)) rho :=
      h3.mono' hmi.aestronglyMeasurable (ae_of_all _ fun z => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hnn z)] using hle z)
    exact ⟨integral_nonneg hnn, integral_mono hi h3 hle⟩
  let FL : ℝ → ℝ := fun s => ∑ k ∈ Finset.range N, KL k s
  let FO : ℝ → ℝ := fun s => ∑ k ∈ Finset.range (min N m), KO k s
  let gL : ℝ → ℝ := fun s => Real.rpow s (-(1 / 2 : ℝ)) *
    ∑ k ∈ Finset.range N, Real.exp (-c * (s + 1 / H) * (k : ℝ))
  let gO : ℝ → ℝ := fun s => Real.rpow s (-(1 / 2 : ℝ)) *
    ∑ k ∈ Finset.range (min N m), Real.exp (-c * s * (k : ℝ))
  have hiL : IntegrableOn FL I := integrable_finsetSum _ fun k _ => (hlow k).2.1
  have hiO : IntegrableOn FO I := integrable_finsetSum _ fun k _ => (hord k).2.1
  have hgrid := los_finite_geometric_grid_integrals c h0 H hc hh01 hH0 N m hm hmH
  change IntegrableOn gL I ∧ IntegrableOn gO I ∧
    (∫ s : ℝ in I, gL s) ≤ (2 + 4 / c) * Real.sqrt H ∧
    (∫ s : ℝ in I, gO s) ≤ 8 * (1 + 1 / c) * Real.sqrt H at hgrid
  have hFL (s : ℝ) (hs : s ∈ I) : FL s ≤ beta * gL s := by
    have ha := (ha3 (s / 2) (by linarith [hs.1])).2
    dsimp only [FL, gL, KL]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    calc
      _ ≤ (Real.rpow s (-(1 / 2 : ℝ)) * beta) * Real.exp (-c * (s + 1 / H) * (k : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left ha (Real.rpow_nonneg hs.1.le (-(1 / 2 : ℝ)))) (Real.exp_pos _).le
      _ = _ := by ring
  have hFO (s : ℝ) (hs : s ∈ I) : FO s ≤ beta * gO s := by
    have ha := (ha3 (s / 2) (by linarith [hs.1])).2
    dsimp only [FO, gO, KO]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    calc
      _ ≤ (Real.rpow s (-(1 / 2 : ℝ)) * beta) * Real.exp (-c * s * (k : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left ha (Real.rpow_nonneg hs.1.le (-(1 / 2 : ℝ)))) (Real.exp_pos _).le
      _ = _ := by ring
  have hL : (∫ s : ℝ in I, FL s) ≤ beta * ((2 + 4 / c) * Real.sqrt H) := by
    have hh := setIntegral_mono_on hiL (hgrid.1.const_mul beta) measurableSet_Ioo hFL
    rw [integral_const_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hgrid.2.2.1 hbeta0)
  have hO : (∫ s : ℝ in I, FO s) ≤ beta * (8 * (1 + 1 / c) * Real.sqrt H) := by
    have hh := setIntegral_mono_on hiO (hgrid.2.1.const_mul beta) measurableSet_Ioo hFO
    rw [integral_const_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hgrid.2.2.2 hbeta0)
  have hsumL : (∑ k ∈ Finset.range N, ∫ v, low k v ∂Pt k) ≤ CF * ∫ s : ℝ in I, FL s := by
    calc
      _ ≤ ∑ k ∈ Finset.range N, CF * ∫ s : ℝ in I, KL k s :=
        Finset.sum_le_sum fun k _ => (hlow k).2.2
      _ = _ := by rw [← Finset.mul_sum, ← integral_finsetSum _ fun k _ => (hlow k).2.1]
  have hsumO : (∑ k ∈ Finset.range (min N m), ∫ v, ordinary k v ∂Pt k) ≤ CS * ∫ s : ℝ in I, FO s := by
    calc
      _ ≤ ∑ k ∈ Finset.range (min N m), CS * ∫ s : ℝ in I, KO k s :=
        Finset.sum_le_sum fun k _ => (hord k).2.2
      _ = _ := by rw [← Finset.mul_sum, ← integral_finsetSum _ fun k _ => (hord k).2.1]
  have hhL := hsumL.trans (mul_le_mul_of_nonneg_left hL hCF.le)
  have hhO := hsumO.trans (mul_le_mul_of_nonneg_left hO hCS.le)
  nlinarith only [hhL, hhO]

theorem iid_actual_late_omitted_suffix_budget :
    let K : ℝ := (2 : ℝ) ^ 64
    ∃ C : ℝ, 0 < C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho],
        Integrable (fun z : ℝ => z ^ 2) rho →
        Integrable (fun z : ℝ => |z| ^ 3) rho →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        ∀ (n : ℕ), 0 < n → ∀ (x : ℝ), 16 ≤ x →
          let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
          let delta : ℝ := beta / Real.sqrt (n : ℝ)
          let u : ℝ := delta * (1 + x) ^ 3
          u ≤ Real.exp (-3 * x ^ 2) →
          let h0 : ℝ := 4 * beta ^ 2
          let H : ℝ := K * beta ^ 2 * (1 + x) ^ 6
          let m : ℕ := ⌈H⌉₊
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
          let nu : Shao.Path n → LabelPerm n → ℕ :=
            fun a sigma => energyCutoff a h0 sigma
          let tau : Shao.Path n → LabelPerm n → ℕ := fun a sigma =>
            min (energyCutoff a H sigma) (n - m)
          let W : (Shao.Path n × LabelPerm n) → Fin n → ℝ := fun p r =>
            |p.1 (p.2 r)| ^ 3 / Real.sqrt (remainingEnergy p.1 r.val p.2) *
              (1 + |remainingSum p.1 r.val p.2| /
                Real.sqrt (remainingEnergy p.1 r.val p.2)) ^ 5
          let lateOmitted : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
            (1 / (n : ℝ)) * ∑ r : Fin n,
              if n / 2 < r.val ∧ tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2
              then W p r else 0
          Measurable lateOmitted ∧ Integrable lateOmitted (revealLaw P) ∧
            (∫ p, lateOmitted p ∂revealLaw P) ≤
              C * beta * Real.sqrt H / (n : ℝ) ∧
            (∫ p, lateOmitted p ∂revealLaw P) ≤
              C * delta * Shao.standardNormalTail x
 := by
  classical
  intro K
  obtain ⟨Cg, hCg, hGrids⟩ := los_iid_omitted_suffix_grids
  let C : ℝ := Cg * (1 + (8 / 3 : ℝ) * Real.sqrt K)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro rho hrho h2 h3 hmean hnorm n hn x hx beta delta u hu h0 H m P nu tau W lateOmitted
  letI : IsProbabilityMeasure rho := hrho
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  have hbeta : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one rho h2 h3 hnorm
  have hbeta0 : 0 < beta := lt_of_lt_of_le zero_lt_one hbeta
  have hh0 : 0 < h0 := by dsimp [h0]; positivity
  have hK : 4 ≤ K := by norm_num [K]
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ 1 + x := by linarith
  have hx6 : 1 ≤ (1 + x) ^ 6 := one_le_pow₀ hx1
  have hH0 : h0 ≤ H := by
    dsimp [h0, H]
    have hh := mul_le_mul_of_nonneg_right hK (sq_nonneg beta)
    have hh2 := mul_le_mul_of_nonneg_left hx6 (mul_nonneg (by positivity : 0 ≤ K) (sq_nonneg beta))
    nlinarith only [hh, hh2]
  have hH : 0 < H := lt_of_lt_of_le hh0 hH0
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  let Pt : (t : ℕ) → Measure (Shao.Path t) := fun t => Measure.pi (fun _ : Fin t => rho)
  let L : (t : ℕ) → Shao.Path t → ℝ := fun t v =>
    if 0 < Shao.energy v ∧ h0 ≤ Shao.energy v ∧ Shao.energy v < H then
      |SourceIIDGaussianProfileBudget.firstValue v| ^ 3 / Real.sqrt (Shao.energy v) *
        (1 + |Shao.prefixSum v t| / Real.sqrt (Shao.energy v)) ^ 5 else 0
  let A : (t : ℕ) → Shao.Path t → ℝ := fun t v =>
    if 0 < Shao.energy v ∧ h0 ≤ Shao.energy v then
      |SourceIIDGaussianProfileBudget.firstValue v| ^ 3 / Real.sqrt (Shao.energy v) *
        (1 + |Shao.prefixSum v t| / Real.sqrt (Shao.energy v)) ^ 5 else 0
  have hgrid :
      (∀ k : ℕ, Measurable (L (k + 1)) ∧ Integrable (L (k + 1)) (Pt (k + 1)) ∧
        Measurable (A (k + 1)) ∧ Integrable (A (k + 1)) (Pt (k + 1))) ∧
      ((∑ k ∈ Finset.range (n / 2), ∫ v, L (k + 1) v ∂Pt (k + 1)) +
        ∑ k ∈ Finset.range (min (n / 2) m), ∫ v, A (k + 1) v ∂Pt (k + 1)) ≤
        Cg * beta * Real.sqrt H := by
    simpa [L, A, SourceIIDGaussianProfileBudget.firstValue, h0, beta, Pt, m]
      using hGrids rho h2 h3 hmean hnorm H hH0 (n / 2)
  have hLA (t : ℕ) (ht : 0 < t) : Measurable (L t) ∧ Integrable (L t) (Pt t) ∧
      Measurable (A t) ∧ Integrable (A t) (Pt t) := by
    have he : t - 1 + 1 = t := by omega
    rw [← he]
    exact hgrid.1 (t - 1)
  have hLnn (t : ℕ) (v : Shao.Path t) : 0 ≤ L t v := by dsimp [L]; split_ifs <;> positivity
  have hAnn (t : ℕ) (v : Shao.Path t) : 0 ≤ A t v := by dsimp [A]; split_ifs <;> positivity
  have hPt (t : ℕ) : IsProbabilityMeasure (Pt t) := by dsimp [Pt]; infer_instance
  let split : (r : Fin n) → Shao.Path n → Shao.Path r.val × Shao.Path (n - r.val) := fun r a =>
    (Spitzer.head a r.val r.is_lt.le, Spitzer.tail a r.val r.is_lt.le)
  have hSplit (r : Fin n) : MeasurePreserving (split r) P ((Pt r.val).prod (Pt (n - r.val))) := by
    let e : Fin r.val ⊕ Fin (n - r.val) ≃ Fin n :=
      finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le r.is_lt.le))
    have h1 := (measurePreserving_piCongrLeft (fun _ : Fin n => rho) e).symm
    have h2 := measurePreserving_sumPiEquivProdPi (fun _ : Fin r.val ⊕ Fin (n - r.val) => rho)
    convert h2.comp h1 using 1
    ext a i <;> change a _ = a _ <;> congr 1
  have hTail (r : Fin n) : MeasurePreserving (fun a : Shao.Path n => (split r a).2) P (Pt (n - r.val)) := by
    letI := hPt r.val
    exact (measurePreserving_snd (μ := Pt r.val) (ν := Pt (n - r.val))).comp (hSplit r)
  have hTailId (r : Fin n) : IdentDistrib (fun a : Shao.Path n => (split r a).2)
      (id : Shao.Path (n - r.val) → Shao.Path (n - r.val)) P (Pt (n - r.val)) := by
    refine ⟨(hTail r).measurable.aemeasurable, measurable_id.aemeasurable, ?_⟩
    rw [Measure.map_id]; exact (hTail r).map_eq
  let R : (Shao.Path n × LabelPerm n) → Shao.Path n := fun p => Spitzer.reorder p.1 p.2
  have hRm : Measurable R := by
    apply measurable_from_prod_countable_left
    intro sigma
    exact Measurable.of_eval fun i => measurable_pi_apply (sigma i)
  let X : Fin n → Shao.Path n → ℝ := fun i a => a i
  have hX (i : Fin n) : Measurable (X i) := measurable_pi_apply i
  have hLaw (i : Fin n) : IdentDistrib (X i) (id : ℝ → ℝ) P rho := by
    refine ⟨(hX i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa only [Measure.map_id] using (measurePreserving_eval (μ := fun _ : Fin n => rho) i).map_eq
  have hIndep : iIndepFun X P :=
    iIndepFun_pi (X := fun _ : Fin n => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable)
  have hMap : Measure.map R (revealLaw P) = P := iid_randomPermutation_map_eq_pi P rho X hX hIndep hLaw
  have hPath : IdentDistrib R (id : Shao.Path n → Shao.Path n) (revealLaw P) P := by
    refine ⟨hRm.aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa only [Measure.map_id] using hMap
  let S : (r : Fin n) → (Shao.Path n × LabelPerm n) → Shao.Path (n - r.val) :=
    fun r p => (split r (R p)).2
  have hSm (r : Fin n) : Measurable (S r) := (hTail r).measurable.comp hRm
  have hSeed (r : Fin n) : IdentDistrib (S r)
      (id : Shao.Path (n - r.val) → Shao.Path (n - r.val)) (revealLaw P) (Pt (n - r.val)) :=
    (hPath.comp (hTail r).measurable).trans (hTailId r)
  have hState (r : Fin n) (p : Shao.Path n × LabelPerm n) :
      Shao.energy (S r p) = remainingEnergy p.1 r.val p.2 ∧
      Shao.prefixSum (S r p) (n - r.val) = remainingSum p.1 r.val p.2 ∧
      SourceIIDGaussianProfileBudget.firstValue (S r p) = p.1 (p.2 r) := by
    have hh := SourceIIDGaussianProfileBudget.gaussian_weight_source_state (R p) r h0 x ∅ false
    have hEnergy : Shao.energy (R p) = Shao.energy p.1 := by
      simpa only [R, Shao.energy, Spitzer.reorder] using Equiv.sum_comp p.2 (fun i => (p.1 i) ^ 2)
    have hSum : Shao.prefixSum (R p) n = Shao.prefixSum p.1 n := by
      simpa only [R, Shao.prefixSum_length, Spitzer.reorder] using Equiv.sum_comp p.2 p.1
    exact ⟨by simpa only [remainingEnergy, hEnergy] using hh.1,
      by simpa only [remainingSum, hSum] using hh.2.1, hh.2.2.2.1⟩
  let low : Fin n → (Shao.Path n × LabelPerm n) → ℝ := fun r p => L (n - r.val) (S r p)
  let ordinary : Fin n → (Shao.Path n × LabelPerm n) → ℝ := fun r p => A (n - r.val) (S r p)
  have hLowM (r : Fin n) : Measurable (low r) := (hLA _ (Nat.sub_pos_of_lt r.is_lt)).1.comp (hSm r)
  have hOrdM (r : Fin n) : Measurable (ordinary r) := (hLA _ (Nat.sub_pos_of_lt r.is_lt)).2.2.1.comp (hSm r)
  have hLowId (r : Fin n) : IdentDistrib (low r) (L (n - r.val)) (revealLaw P) (Pt (n - r.val)) :=
    (hSeed r).comp (hLA _ (Nat.sub_pos_of_lt r.is_lt)).1
  have hOrdId (r : Fin n) : IdentDistrib (ordinary r) (A (n - r.val)) (revealLaw P) (Pt (n - r.val)) :=
    (hSeed r).comp (hLA _ (Nat.sub_pos_of_lt r.is_lt)).2.2.1
  have hLowI (r : Fin n) : Integrable (low r) (revealLaw P) :=
    (hLowId r).integrable_iff.2 (hLA _ (Nat.sub_pos_of_lt r.is_lt)).2.1
  have hOrdI (r : Fin n) : Integrable (ordinary r) (revealLaw P) :=
    (hOrdId r).integrable_iff.2 (hLA _ (Nat.sub_pos_of_lt r.is_lt)).2.2.2
  have hLowVal (r : Fin n) (p : Shao.Path n × LabelPerm n) : low r p =
      if 0 < remainingEnergy p.1 r.val p.2 ∧ h0 ≤ remainingEnergy p.1 r.val p.2 ∧
        remainingEnergy p.1 r.val p.2 < H then W p r else 0 := by
    dsimp only [low, L]
    rw [(hState r p).1, (hState r p).2.1, (hState r p).2.2]
  have hOrdVal (r : Fin n) (p : Shao.Path n × LabelPerm n) : ordinary r p =
      if 0 < remainingEnergy p.1 r.val p.2 ∧ h0 ≤ remainingEnergy p.1 r.val p.2 then W p r else 0 := by
    dsimp only [ordinary, A]
    rw [(hState r p).1, (hState r p).2.1, (hState r p).2.2]
  have hWnn (p : Shao.Path n × LabelPerm n) (r : Fin n) : 0 ≤ W p r := by dsimp [W]; positivity
  have hCut (r : Fin n) (p : Shao.Path n × LabelPerm n) :
      (tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2) ↔
        h0 ≤ remainingEnergy p.1 r.val p.2 ∧
          (remainingEnergy p.1 r.val p.2 < H ∨ n - r.val ≤ m) :=
    Shao.C2.AdaptiveRevealCutoff.omitted_adaptive_cutoff_iff p.1 h0 H hh0 hH m r.val r.is_lt.le p.2
  have hT (r : Fin n) : Measurable (fun p : Shao.Path n × LabelPerm n => remainingEnergy p.1 r.val p.2) :=
    (Shao.measurable_energy.comp measurable_fst).sub ((Shao.measurable_prefixSquares r.val).comp hRm)
  have hd (r : Fin n) : Measurable (fun p : Shao.Path n × LabelPerm n => remainingSum p.1 r.val p.2) :=
    ((Shao.measurable_prefixSum n).comp measurable_fst).sub ((Shao.measurable_prefixSum r.val).comp hRm)
  have hb (r : Fin n) : Measurable (fun p : Shao.Path n × LabelPerm n => p.1 (p.2 r)) := by
    apply measurable_from_prod_countable_left
    intro sigma
    exact measurable_pi_apply (sigma r)
  have hWm (r : Fin n) : Measurable (fun p => W p r) := by dsimp [W]; fun_prop
  have hGuard (r : Fin n) : MeasurableSet {p : Shao.Path n × LabelPerm n |
      n / 2 < r.val ∧ tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2} := by
    have he : {p : Shao.Path n × LabelPerm n | n / 2 < r.val ∧ tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2} =
        {p | n / 2 < r.val ∧ h0 ≤ remainingEnergy p.1 r.val p.2 ∧
          (remainingEnergy p.1 r.val p.2 < H ∨ n - r.val ≤ m)} := by
      ext p; exact and_congr_right fun _ => hCut r p
    rw [he]
    by_cases hr : n / 2 < r.val
    · by_cases ht : n - r.val ≤ m
      · simpa only [hr, ht, or_true, and_true, true_and] using measurableSet_le measurable_const (hT r)
      · simpa only [hr, ht, or_false, true_and, Set.setOf_and] using
          (measurableSet_le measurable_const (hT r)).inter (measurableSet_lt (hT r) measurable_const)
    · simp only [hr, false_and, Set.setOf_false]; exact MeasurableSet.empty
  let selected : Fin n → (Shao.Path n × LabelPerm n) → ℝ := fun r p =>
    if n / 2 < r.val ∧ tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 then W p r else 0
  let majorant : Fin n → (Shao.Path n × LabelPerm n) → ℝ := fun r p =>
    if n / 2 < r.val then low r p + (if n - r.val ≤ m then ordinary r p else 0) else 0
  have hSelectedM (r : Fin n) : Measurable (selected r) := (hWm r).ite (hGuard r) measurable_const
  have hMajorantI (r : Fin n) : Integrable (majorant r) (revealLaw P) := by
    by_cases hr : n / 2 < r.val
    · by_cases ht : n - r.val ≤ m
      · convert (hLowI r).add (hOrdI r) using 1
        funext p
        simp only [majorant, if_pos hr, if_pos ht, Pi.add_apply]
      · simpa only [majorant, if_pos hr, if_neg ht, add_zero] using hLowI r
    · convert (integrable_zero _ _ _ : Integrable (fun _ : Shao.Path n × LabelPerm n => (0 : ℝ)) (revealLaw P)) using 1
      funext p
      simp only [majorant, if_neg hr, Pi.zero_apply]
  have hPoint (r : Fin n) (p : Shao.Path n × LabelPerm n) :
      0 ≤ selected r p ∧ selected r p ≤ majorant r p := by
    have hnn := hWnn p r
    dsimp only [selected, majorant]
    rw [hLowVal, hOrdVal]
    by_cases hr : n / 2 < r.val
    · simp only [hr, true_and, if_true]
      by_cases hs : tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2
      · have ht := (hCut r p).1 hs
        have hpos : 0 < remainingEnergy p.1 r.val p.2 := lt_of_lt_of_le hh0 ht.1
        simp only [if_pos hs]
        rcases ht.2 with he | he
        · simp only [hpos, ht.1, he, and_self, if_true]
          split_ifs <;> constructor <;> linarith
        · simp only [hpos, ht.1, he, and_self, if_true]
          split_ifs <;> constructor <;> linarith
      · simp only [if_neg hs]
        constructor
        · exact le_rfl
        · split_ifs <;> positivity
    · simp only [hr, false_and, if_false]; exact ⟨le_rfl, le_rfl⟩
  have hSelectedI (r : Fin n) : Integrable (selected r) (revealLaw P) :=
    (hMajorantI r).mono' (hSelectedM r).aestronglyMeasurable (ae_of_all _ fun p => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hPoint r p).1] using (hPoint r p).2)
  have hLm : Measurable lateOmitted := by
    exact (Finset.measurable_sum _ fun r _ => hSelectedM r).const_mul (1 / (n : ℝ))
  have hLi : Integrable lateOmitted (revealLaw P) :=
    (integrable_finsetSum _ fun r _ => hSelectedI r).const_mul (1 / (n : ℝ))
  have hgridBudget : (∫ p, lateOmitted p ∂revealLaw P) ≤ Cg * beta * Real.sqrt H / (n : ℝ) := by
    let fL : ℕ → ℝ := fun t => ∫ v, L t v ∂Pt t
    let fA : ℕ → ℝ := fun t => ∫ v, A t v ∂Pt t
    have hfL (t : ℕ) : 0 ≤ fL t := integral_nonneg (hLnn t)
    have hfA (t : ℕ) : 0 ≤ fA t := integral_nonneg (hAnn t)
    let er : Finset (Fin n) := Finset.univ.filter (fun r => n / 2 < r.val)
    let sr : Finset (Fin n) := er.filter (fun r => n - r.val ≤ m)
    have hIL : (∑ r ∈ er, fL (n - r.val)) ≤ ∑ k ∈ Finset.range (n / 2), fL (k + 1) := by
      apply Finset.sum_le_sum_of_injOn (fun r : Fin n => n - r.val - 1)
      · intro r hr s hs he
        apply Fin.ext
        have hri := r.is_lt; have hsi := s.is_lt
        dsimp only at he
        omega
      · intro k hk
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hk
        have hh := (Finset.mem_filter.1 hr).2
        have hri := r.is_lt
        exact Finset.mem_range.2 (by omega)
      · intro r hr
        have he : n - r.val - 1 + 1 = n - r.val := by have hri := r.is_lt; omega
        rw [he]
      · intro k hk hnot; exact hfL (k + 1)
    have hIA : (∑ r ∈ sr, fA (n - r.val)) ≤ ∑ k ∈ Finset.range (min (n / 2) m), fA (k + 1) := by
      apply Finset.sum_le_sum_of_injOn (fun r : Fin n => n - r.val - 1)
      · intro r hr s hs he
        apply Fin.ext
        have hri := r.is_lt; have hsi := s.is_lt
        dsimp only at he
        omega
      · intro k hk
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hk
        have hh := Finset.mem_filter.1 hr
        have hh2 := (Finset.mem_filter.1 hh.1).2
        have hri := r.is_lt
        exact Finset.mem_range.2 (by omega)
      · intro r hr
        have he : n - r.val - 1 + 1 = n - r.val := by have hri := r.is_lt; omega
        rw [he]
      · intro k hk hnot; exact hfA (k + 1)
    have hMajInt : (∑ r : Fin n, ∫ p, majorant r p ∂revealLaw P) =
        (∑ r ∈ er, fL (n - r.val)) + ∑ r ∈ sr, fA (n - r.val) := by
      simp only [er, sr, Finset.sum_filter]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases he : n / 2 < r.val
      · by_cases hs : n - r.val ≤ m
        · simp only [majorant, if_pos he, if_pos hs, integral_add (hLowI r) (hOrdI r)]
          rw [(hLowId r).integral_eq, (hOrdId r).integral_eq]
        · simp only [majorant, if_pos he, if_neg hs, add_zero]
          rw [(hLowId r).integral_eq]
      · simp [majorant, he]
    calc
      _ = (1 / (n : ℝ)) * ∑ r : Fin n, ∫ p, selected r p ∂revealLaw P := by
        rw [show lateOmitted = fun p => (1 / (n : ℝ)) * ∑ r : Fin n, selected r p from rfl,
          integral_const_mul, integral_finsetSum _ fun r _ => hSelectedI r]
      _ ≤ (1 / (n : ℝ)) * ∑ r : Fin n, ∫ p, majorant r p ∂revealLaw P :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r _ => integral_mono (hSelectedI r) (hMajorantI r) (fun p => (hPoint r p).2)) (one_div_nonneg.2 hn0.le)
      _ = (1 / (n : ℝ)) * ((∑ r ∈ er, fL (n - r.val)) + ∑ r ∈ sr, fA (n - r.val)) := by rw [hMajInt]
      _ ≤ (1 / (n : ℝ)) * Cg * beta * Real.sqrt H := by
        have hh := (add_le_add hIL hIA).trans hgrid.2
        nlinarith only [mul_le_mul_of_nonneg_left hh (one_div_nonneg.2 hn0.le)]
      _ = _ := by ring
  refine ⟨hLm, hLi, ?_, ?_⟩
  · have hC : Cg ≤ C := by
      dsimp [C]
      have hh : 0 ≤ (8 / 3 : ℝ) * Real.sqrt K := by positivity
      nlinarith
    exact hgridBudget.trans (by gcongr)
  · have hscale : beta * Real.sqrt H / (n : ℝ) = Real.sqrt K * delta * u := by
      have hnS : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
      have hHval : Real.sqrt H = Real.sqrt K * beta * (1 + x) ^ 3 := by
        apply (Real.sqrt_eq_iff_eq_sq hH.le (by positivity)).2
        dsimp [H]
        rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ K)]
        ring
      rw [hHval]
      dsimp [delta, u]
      field_simp
      nlinarith only [hnS]
    have htail := Shao.C2.AuxiliaryLowEnergyGaussian.auxiliary_exponential_le_gaussian_tail
      x (3 * x ^ 2) hx0 (by nlinarith)
    have hdelta : 0 ≤ delta := by dsimp [delta]; positivity
    calc
      _ ≤ Cg * (beta * Real.sqrt H / (n : ℝ)) := by convert hgridBudget using 1 <;> ring
      _ = Cg * Real.sqrt K * delta * u := by rw [hscale]; ring
      _ ≤ Cg * Real.sqrt K * delta * ((8 / 3 : ℝ) * Shao.standardNormalTail x) := by
        gcongr
        exact hu.trans (by simpa only [neg_mul] using htail)
      _ ≤ C * delta * Shao.standardNormalTail x := by
        have htailnn : 0 ≤ Shao.standardNormalTail x := by
          have hh := htail; nlinarith [Real.exp_pos (-(3 * x ^ 2))]
        dsimp [C]
        nlinarith [mul_nonneg hCg.le (mul_nonneg hdelta htailnn)]

end Shao.Probability.SourceLateOmittedSuffixBudget
