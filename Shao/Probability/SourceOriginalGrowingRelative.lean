/- Mathematical candidate only. No production source, Lean or AX execution.
   One public head; no new global definitions or instances.
   rhoStar is the original fixed host constant, not a replacement domain. -/
import Shao.Probability.SourceFullYReflection
import Shao.Probability.SourceDesmoothing
import Shao.Probability.SourceMomentDomain
import Shao.Probability.EndpointRelativeError
import Shao.Probability.OriginalCDFPullback
import Shao.Probability.OriginalGaussianTail
import Shao.Probability.SourceSmallBoundary

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace Shao.Probability.SourceOriginalGrowingRelative
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem original_iid_signed_halfline_growing_relative_comparison :
    ∃ C : ℝ, 0 < C ∧
      ∀ rhoStar : ℝ, 0 < rhoStar → rhoStar ≤ 1 / 16 →
        ∀ p : ℝ, 2 < p → p ≤ 3 →
          ∀ {Ω : Type*} [MeasurableSpace Ω]
            (mu : Measure Ω) (rho : Measure ℝ)
            [IsProbabilityMeasure mu] [IsProbabilityMeasure rho]
            (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ),
            (∀ i, AEMeasurable (X i) mu) →
            iIndepFun X mu →
            (∀ i, IdentDistrib (X i) (id : ℝ → ℝ) mu rho) →
            Integrable (fun z : ℝ => z ^ 2) rho →
            (∫ z : ℝ, z ∂rho) = 0 →
            (0 < ∫ z : ℝ, z ^ 2 ∂rho) →
            Integrable (fun z : ℝ => Real.rpow |z| p) rho →
            let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂rho
            let sigma : ℝ := Real.sqrt sigmaSq
            let scale : ℝ := sigma * Real.sqrt (n : ℝ)
            let nu : Measure ℝ := Measure.map (fun z : ℝ => z / scale) rho
            let Ln : ℝ := (∫ z : ℝ, Real.rpow |z| p ∂rho) /
              (Real.rpow sigma p * Real.rpow (n : ℝ) ((p - 2) / 2))
            let Rn : ℝ → ℝ := fun t => Shao.truncationBudget nu n t
            let I : Set ℝ := {t | 0 ≤ t ∧
              (t ≤ Real.rpow Ln (-1 / p) ∨ Rn t ≤ rhoStar)}
            let population : Ω → Shao.Path n := Shao.Probability.samplePath X
            let rawEnergy : Ω → ℝ := fun omega => ∑ i : Fin n, (X i omega) ^ 2
            ∀ (s x : ℝ), (s = 1 ∨ s = -1) → 1 ≤ x → x ∈ I →
              let signedMax : Ω → ℝ := fun omega =>
                Shao.upperMax (s • population omega) hn
              let crossing : Set Ω :=
                {omega | x * Real.sqrt (rawEnergy omega) ≤ signedMax omega}
              let survival : Set Ω :=
                {omega | signedMax omega < x * Real.sqrt (rawEnergy omega)}
              Integrable (crossing.indicator (fun _ : Ω => (1 : ℝ))) mu ∧
              Integrable (survival.indicator (fun _ : Ω => (1 : ℝ))) mu ∧
              mu.real {omega : Ω | rawEnergy omega = 0} ≤
                C * Rn x * Shao.standardNormalTail x ∧
              |mu.real crossing - 2 * Shao.standardNormalTail x| ≤
                C * Rn x * Shao.standardNormalTail x ∧
              |mu.real survival - (1 - 2 * Shao.standardNormalTail x)| ≤
                C * Rn x * Shao.standardNormalTail x ∧
              |mu.real crossing / Shao.standardNormalTail x - 2| ≤ C * Rn x := by
  let L : ℝ := 1600
  let L2 : ℝ := 16384
  let alpha : ℝ := 1 / 1024
  let epsilon0 : ℝ := min (1 / (64 * Real.sqrt L2)) (alpha / (8 * L))
  let t0 : ℝ := Real.exp (-(48 * alpha / epsilon0))
  let eta0 : ℝ := min (1 / 16)
    (min (Real.sqrt t0 / (2 * Real.sqrt L2))
      (min ((epsilon0 / 20480) ^ 2)
        (1 / (16384 * (1 + 3 / t0) * Real.exp (24 * epsilon0 / t0)))))
  let epsilon : ℝ := min (epsilon0 / 2)
    (1 / (4 * (8 * (1 + L) + 1) * L))
  have hcompat : epsilon0 = (1 / 13107200 : ℝ) ∧
      epsilon = (1 / 81977600 : ℝ) ∧ 0 < epsilon ∧
      epsilon ≤ (1 / 16384 : ℝ) ∧ epsilon ≤ (1 / 800 : ℝ) :=
    sourceGrowingCutoff_exact_and_bounded_compatible
  have he : 0 < epsilon := hcompat.2.2.1
  have he800 : epsilon ≤ 1 / 800 := hcompat.2.2.2.2
  have heHalf : epsilon ≤ 1 / 2 := by linarith
  have he0 : 0 < epsilon0 := by rw [hcompat.1]; norm_num
  have ht0 : 0 < t0 := Real.exp_pos _
  have heta0 : 0 < eta0 := by dsimp [eta0, L2]; positivity
  have heGeom : epsilon ≤ 1 / (4 * (8 * (1 + L) + 1) * L) := min_le_right _ _
  let K : ℝ := 8 * (1 + L)
  let A0 : ℝ := 4 * K * L
  have hK : 1 < K := by norm_num [K, L]
  have hA0 : 0 < A0 := by norm_num [A0, K, L]
  let eta : ℝ := min (epsilon ^ 3 / 8)
    (min (epsilon ^ 2 * eta0 / 40) (min ((1 / 16 : ℝ) / 32) (1 / (4 * A0))))
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hetaCube : eta ≤ epsilon ^ 3 / 8 := min_le_left _ _
  have hetaEta : eta ≤ epsilon ^ 2 * eta0 / 40 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hetaRho : eta ≤ (1 / 16 : ℝ) / 32 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hetaA : eta ≤ 1 / (4 * A0) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Cc, hCc, hCoarse⟩ := original_coarse_gaussian_upper
  obtain ⟨Cp, hCp, hPullback⟩ := sourceTruncation_original_max_cdf_pullback
  obtain ⟨Cs, hCs, hSmoothed⟩ := sourceTruncation_full_y_smoothed_probability_comparison
  obtain ⟨Ce, hCe, hEndpoint⟩ := sourceTruncation_endpoint_relative_error epsilon he he800
  obtain ⟨Cn, hCn, hNearZero⟩ := original_maximum_near_zero_cdf
  let Bpull : ℝ := (4 / 3 : ℝ) * Cp / epsilon ^ 3
  let D : ℝ := 32768 * Real.sqrt (2 * Real.pi) +
    1 / Shao.standardNormalTail 2 + 1600
  let c : ℝ := 2 * Real.exp 2
  let Cd : ℝ := K / (K - 1) * (Bpull + Ce + Cs + c * (K + 2) * D)
  let C1 : ℝ := (Cc + 2) / eta
  let C2 : ℝ := Cn * (A0 + 1) / Shao.standardNormalTail (1 / 2)
  let B0 : ℝ := 1 + C1 + C2 + Cd
  let Ccan : ℝ := 4 * B0 / 3
  let Cq : ℝ := Cc / eta + Real.sqrt (2 * Real.pi)
  have hTail (u : ℝ) : 0 < Shao.standardNormalTail u :=
    (Shao.standardNormalTail_basic.2.2.1 u).1
  have hTail2 := hTail 2
  have hTailHalf := hTail (1 / 2)
  have hKm : 0 < K - 1 := by linarith
  have hBpull : 0 ≤ Bpull := by dsimp [Bpull]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hCd : 0 ≤ Cd := by dsimp [Cd]; positivity
  have hC1 : 0 ≤ C1 := by dsimp [C1]; positivity
  have hC2 : 0 ≤ C2 := by dsimp [C2]; positivity
  have hB0 : 0 < B0 := by dsimp [B0]; positivity
  have hCcan : 0 < Ccan := by dsimp [Ccan]; positivity
  have hCq : 0 < Cq := by dsimp [Cq]; positivity
  have hCanonical (p : ℝ) (hp2 : 2 < p) (hp3 : p ≤ 3)
      (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 0 < n)
      (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
      (hmean : (∫ z : ℝ, z ∂nu) = 0)
      (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
      (hp : Integrable (fun z : ℝ => Real.rpow |z| p) nu) :
      let beta : ℝ := (n : ℝ) * ∫ z : ℝ, Real.rpow |z| p ∂nu
      let H : ℝ := Real.rpow beta (-1 / p)
      let R : ℝ → ℝ := fun u => Shao.truncationBudget nu n u
      let P0 : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
      ∀ x : ℝ, 0 < x → (x ≤ H ∨ R x ≤ 1 / 16) →
        P0.real {a : Shao.Path n | Shao.energy a = 0} ≤
          Cq * R x * Shao.standardNormalTail x ∧
        |P0.real (Shao.upperCrossing hn x) - 2 * Shao.standardNormalTail x| ≤
          Ccan * R x * Shao.standardNormalTail x := by
    intro beta H R P0
    letI : IsProbabilityMeasure P0 := by dsimp [P0]; infer_instance
    let Ibar : Set ℝ := {u | 0 ≤ u ∧ (u ≤ H ∨ R u ≤ 1 / 16)}
    let w : ℝ → ℝ := fun u => R u * Shao.standardNormalTail u
    let G : ℝ → ℝ := fun u => if 0 < u then 1 - 2 * Shao.standardNormalTail u else 0
    let F0 : ℝ → ℝ := fun u => P0.real {a : Shao.Path n |
      0 < Shao.energy a ∧ Shao.maxWithZero a < u * Real.sqrt (Shao.energy a)}
    let E : ℝ → ℝ := fun u => F0 u - G u
    have hR (u : ℝ) : 0 ≤ R u := Shao.truncationBudget_nonneg nu n h2 u
    have hguard := original_moment_domain_coarse_guards p hp2 hp3 nu n hn h2 hnorm hp
    have hH : 0 < H := hguard.2.2.1
    have hcompact := sourceWeight_enlarged_domain_compact nu n h2 hnorm H
      (1 / 16) hH.le (by norm_num)
    have hI : IsCompact Ibar := hcompact.1
    have hwc : ContinuousOn w Ibar := hcompact.2.2.1
    have hwp : ∀ u : ℝ, u ∈ Ibar → 0 < w u := hcompact.2.2.2.1
    have hEb (u : ℝ) (_hu : u ∈ Ibar) : |E u| ≤ 1 := by
      have hF0 : 0 ≤ F0 u := measureReal_nonneg
      have hF1 : F0 u ≤ 1 := by
        calc
          _ ≤ P0.real Set.univ := measureReal_mono (Set.subset_univ _)
          _ = 1 := probReal_univ
      have hG : 0 ≤ G u ∧ G u ≤ 1 := by
        by_cases hu : 0 < u
        · have ht := Shao.standardNormalTail_basic.1 hu.le
          rw [Shao.standardNormalTail_basic.2.1] at ht
          simp only [G, if_pos hu]
          constructor <;> linarith [(hTail u).le]
        · simp [G, hu]
      exact abs_le.mpr ⟨by dsimp [E]; linarith, by dsimp [E]; linarith⟩
    let ratios : Set ℝ := {v | ∃ u : ℝ, u ∈ Ibar ∧ 0 < u ∧ v = |E u| / w u}
    let M : ℝ := sSup (Set.insert 0 ratios)
    have hsup := sourceWeight_compact_supremum_absorption Ibar hI E w hwc hwp hEb
    have hM : 0 ≤ M := hsup.2.2.1
    have hMu (u : ℝ) (hu : u ∈ Ibar) (hu0 : 0 < u) : |E u| ≤ M * w u :=
      hsup.2.2.2.1 u hu hu0
    have hCoarseI (u : ℝ) (hu : 0 < u) (hue : u ∈ Ibar) :
        P0.real (Shao.upperCrossing hn u) ≤ Cc * Shao.standardNormalTail u := by
      have hinputs : u ^ 6 ≤ (n : ℝ) ∧
          (n : ℝ) * (∫ z : ℝ, Shao.truncationF (u * z) ∂nu) ≤ 1 := by
        rcases hue.2 with hm | hr
        · exact hguard.2.2.2.2 u hu.le hm
        · have hs := Shao.truncationBudget_sample_size_lower nu n h2 hnorm u
            (1 / 16) hu.le hr (by norm_num)
          refine ⟨(pow_le_pow_left₀ hu.le (by linarith : u ≤ 1 + u) 6).trans
            (hs.1.trans hs.2), ?_⟩
          apply le_trans _ (hr.trans (by norm_num : (1 / 16 : ℝ) ≤ 1))
          exact mul_le_mul_of_nonneg_left
            (integral_mono (Shao.integrable_truncationF_mul nu h2 u)
              (Shao.integrable_truncationF_mul nu h2 (1 + u))
              (fun z => Shao.truncationF_mono_scale u (1 + u) z hu.le (by linarith)))
            (Nat.cast_nonneg n)
      exact hCoarse nu inferInstance n hn h2 hmean hnorm u hu hinputs.1 hinputs.2
    have hEidentity (u : ℝ) (hu : 0 < u) :
        E u = 2 * Shao.standardNormalTail u - P0.real (Shao.upperCrossing hn u) :=
      by simpa only [E, F0, G, if_pos hu] using
        (sourcePositiveCDF_weak_tail_error_identity hn P0 u hu).1
    have hRatio (x : ℝ) (hxI : x ∈ Ibar) (hx : 0 < x) :
        |E x| / w x ≤ B0 + M / 4 := by
      have hw : 0 < w x := hwp x hxI
      by_cases hbig : eta ≤ R x
      · have he : |E x| ≤ (Cc + 2) * Shao.standardNormalTail x := by
          rw [hEidentity x hx]
          calc
            _ ≤ |2 * Shao.standardNormalTail x| + |P0.real (Shao.upperCrossing hn x)| :=
              abs_sub _ _
            _ ≤ (Cc + 2) * Shao.standardNormalTail x := by
              rw [abs_of_nonneg (mul_nonneg (by norm_num) (hTail x).le),
                abs_of_nonneg measureReal_nonneg]
              nlinarith only [hCoarseI x hx hxI]
        have hpaid : |E x| ≤ C1 * w x := by
          calc
            _ ≤ (Cc + 2) * Shao.standardNormalTail x := he
            _ = C1 * (eta * Shao.standardNormalTail x) := by
              dsimp [C1]; field_simp <;> ring
            _ ≤ C1 * (R x * Shao.standardNormalTail x) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hbig (hTail x).le) hC1
            _ = _ := rfl
        have hr : |E x| / w x ≤ C1 := (div_le_iff₀ hw).mpr hpaid
        dsimp only [B0]
        linarith
      · have hsmall : R x < eta := lt_of_not_ge hbig
        by_cases hnear : x ≤ A0 * R 0
        · have hr0 : R 0 ≤ R x := Shao.truncationBudget_mono nu n h2 0 x (by norm_num) hx.le
          have hax : A0 * R 0 < 1 / 4 := by
            have heA : A0 * eta ≤ 1 / 4 := by
              have hh := mul_le_mul_of_nonneg_left hetaA hA0.le
              have hc : A0 * (1 / (4 * A0)) = 1 / 4 := by field_simp <;> ring
              rw [hc] at hh
              exact hh
            exact (mul_lt_mul_of_pos_left (hr0.trans_lt hsmall) hA0).trans_le heA
          have hxh : x ≤ 1 / 2 := by linarith
          have heN := (hNearZero nu n hn h2 hmean hnorm).2 x hx.le hxh
          change |E x| ≤ Cn * (x + R 0) at heN
          have htail := Shao.standardNormalTail_basic.1 hxh
          have hlow : R 0 * Shao.standardNormalTail (1 / 2) ≤ w x :=
            mul_le_mul hr0 htail (hTail (1 / 2)).le (hR x)
          have hpaid : |E x| ≤ C2 * w x := by
            calc
              _ ≤ Cn * (x + R 0) := heN
              _ ≤ Cn * (A0 + 1) * R 0 := by nlinarith only [hnear, hCn]
              _ = C2 * (R 0 * Shao.standardNormalTail (1 / 2)) := by
                dsimp [C2]; field_simp [ne_of_gt hTailHalf] <;> ring
              _ ≤ C2 * w x := mul_le_mul_of_nonneg_left hlow hC2
          have hr : |E x| / w x ≤ C2 := (div_le_iff₀ hw).mpr hpaid
          dsimp only [B0]
          linarith
        · have hD3 : 4 * (8 * (1 + L)) * L * R 0 < x := lt_of_not_ge hnear
          have hcube : R x ≤ epsilon ^ 3 / 8 := hsmall.le.trans hetaCube
          have heta' : R x ≤ epsilon ^ 2 * eta0 / 40 := hsmall.le.trans hetaEta
          have hpull := hPullback nu n hn h2 hmean hnorm x epsilon hx.le he he800 hcube
          rcases hpull with ⟨hpN, hpN1, hpbad, hprob, hprobP, hcond, hmix, hcost⟩
          have hlocal (u : ℝ) (hu : |u - x| ≤ 1 / (1 + x)) : |E u| ≤ L * M * w x := by
            by_cases hu0 : 0 < u
            · have hRu := (Shao.truncationBudget_local_comparison nu n h2 x u
                hx.le hu0.le (by simpa only [one_div] using hu)).2
              have huI : u ∈ Ibar := ⟨hu0.le, Or.inr (by
                have hh : R u ≤ 8 * R x := hRu
                have he' : 8 * eta ≤ (1 / 16 : ℝ) := by linarith only [hetaRho]
                linarith only [hh, hsmall, he'])⟩
              have hwu := (sourceWeight_nearby_bound nu n h2 x u L hx.le hu0.le hu
                (by norm_num [L])).2
              calc
                _ ≤ M * w u := hMu u huI hu0
                _ ≤ M * (L * w x) := mul_le_mul_of_nonneg_left hwu hM
                _ = _ := by ring
            · have huN : u ≤ 0 := le_of_not_gt hu0
              have hempty : {a : Shao.Path n | 0 < Shao.energy a ∧
                  Shao.maxWithZero a < u * Real.sqrt (Shao.energy a)} = ∅ := by
                apply Set.eq_empty_iff_forall_notMem.mpr
                intro a ha
                have ht : u * Real.sqrt (Shao.energy a) ≤ 0 :=
                  mul_nonpos_of_nonpos_of_nonneg huN (Real.sqrt_nonneg _)
                exact (not_lt_of_ge (ht.trans (Shao.maxWithZero_nonneg a))) ha.2
              have hEu : E u = 0 := by simp only [E, F0, hempty, measureReal_empty, G, if_neg hu0, sub_zero]
              rw [hEu, abs_zero]
              exact mul_nonneg (mul_nonneg (by norm_num [L]) hM) hw.le
          have hd := sourceTruncation_weighted_desmoothing_from_interfaces nu n h2 hnorm hmean
            x epsilon eta0 L hx he heta0 (by norm_num [L]) he800 heGeom hcube heta' hD3
          rcases hd with ⟨_, _, _, _, _, _, _, _, _, _, _, happly⟩
          have hb := happly Bpull Ce Cs M hBpull hCe hCs.le hM
            (fun u hu => (hcost u hu).2.2.2.2.1)
            (fun u hu => by
              simpa only [mul_assoc] using hEndpoint nu n h2 hnorm hmean x hx hcube u hu)
            (fun y hy hxy => by
              rcases (hSmoothed nu inferInstance n h2 hnorm hmean x hx.le hcube heta').2.2.2
                  y hy hxy with ⟨_, _, _, _, _, _, hbound⟩
              exact hbound)
            hlocal
          have hr : |E x| / w x ≤ Cd + M / 4 := hb.2
          dsimp only [B0]
          linarith
    have hMcap : M ≤ Ccan := hsup.2.2.2.2.2 B0 hB0.le hRatio
    intro x hx hxI
    have hxi : x ∈ Ibar := ⟨hx.le, hxI⟩
    have hwx : 0 < w x := hwp x hxi
    have hbound : |P0.real (Shao.upperCrossing hn x) - 2 * Shao.standardNormalTail x| ≤
        Ccan * R x * Shao.standardNormalTail x := by
      calc
        _ = |2 * Shao.standardNormalTail x - P0.real (Shao.upperCrossing hn x)| := abs_sub_comm _ _
        _ = |E x| := congrArg abs (hEidentity x hx).symm
        _ ≤ M * w x := hMu x hxi hx
        _ ≤ Ccan * w x := mul_le_mul_of_nonneg_right hMcap hwx.le
        _ = _ := by dsimp [w]; ring
    refine ⟨?_, hbound⟩
    by_cases hbig : eta ≤ R x
    · have hsub : {a : Shao.Path n | Shao.energy a = 0} ⊆ Shao.upperCrossing hn x :=
        fun a ha => Shao.mem_upperCrossing_of_energy_eq_zero a hn x ha
      calc
        _ ≤ P0.real (Shao.upperCrossing hn x) := measureReal_mono hsub
        _ ≤ Cc * Shao.standardNormalTail x := hCoarseI x hx hxi
        _ = (Cc / eta) * (eta * Shao.standardNormalTail x) := by field_simp <;> ring
        _ ≤ (Cc / eta) * (R x * Shao.standardNormalTail x) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbig (hTail x).le)
            (div_nonneg hCc.le heta.le)
        _ ≤ Cq * (R x * Shao.standardNormalTail x) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg (hR x) (hTail x).le)
          exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
        _ = _ := by ring
    · have hsmall : R x < eta := lt_of_not_ge hbig
      have hcube : R x ≤ epsilon ^ 3 / 8 := hsmall.le.trans hetaCube
      let rho : Measure ℝ := ProbabilityTheory.cond nu {z : ℝ | |z| ≤ epsilon / (1 + x)}
      let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
      let N : Set (Shao.Path n) := {a | ∀ j : Fin n, |a j| ≤ epsilon / (1 + x)}
      let pN : ℝ := P0.real N
      rcases hPullback nu n hn h2 hmean hnorm x epsilon hx.le he he800 hcube with
        ⟨hpN, hpN1, _, hprob, hprobP, hcond, _, _⟩
      letI : IsProbabilityMeasure rho := hprob
      letI : IsProbabilityMeasure P := hprobP
      have hNm : MeasurableSet N := by
        simp only [N, Set.setOf_forall]
        exact MeasurableSet.iInter (fun j : Fin n =>
          measurableSet_le (by fun_prop : Measurable (fun a : Shao.Path n => |a j|)) measurable_const)
      have hzero : {a : Shao.Path n | Shao.energy a = 0} ⊆ N := by
        intro a ha j
        rw [(Shao.energy_eq_zero_iff a).mp ha j]
        simp only [abs_zero]
        exact (div_pos he (by linarith : 0 < 1 + x)).le
      have hinter : N ∩ {a : Shao.Path n | Shao.energy a = 0} =
          {a : Shao.Path n | Shao.energy a = 0} := Set.inter_eq_right.mpr hzero
      have hid : P.real {a : Shao.Path n | Shao.energy a = 0} * pN =
          P0.real {a : Shao.Path n | Shao.energy a = 0} := by
        have hcond' : ProbabilityTheory.cond P0 N = P := hcond
        have hm := congrArg ENNReal.toReal
          (cond_mul_eq_inter hNm {a : Shao.Path n | Shao.energy a = 0} P0)
        rw [ENNReal.toReal_mul] at hm
        change (ProbabilityTheory.cond P0 N).real {a : Shao.Path n | Shao.energy a = 0} * pN =
          P0.real (N ∩ {a : Shao.Path n | Shao.energy a = 0}) at hm
        rw [hcond', hinter] at hm
        exact hm
      have hz := (sourceTruncation_endpoint_zero_energy_gaussian_cost nu n h2 hnorm hmean
        x epsilon hx.le he he800 hcube).2.2.2.2
      calc
        _ = P.real {a : Shao.Path n | Shao.energy a = 0} * pN := hid.symm
        _ ≤ P.real {a : Shao.Path n | Shao.energy a = 0} :=
          mul_le_of_le_one_right measureReal_nonneg hpN1
        _ ≤ Real.sqrt (2 * Real.pi) * R x * Shao.standardNormalTail x := hz
        _ ≤ Cq * R x * Shao.standardNormalTail x := by
          apply mul_le_mul_of_nonneg_right _ (hTail x).le
          apply mul_le_mul_of_nonneg_right _ (hR x)
          dsimp [Cq]
          exact le_add_of_nonneg_left (div_nonneg hCc.le heta.le)
  refine ⟨1 + Ccan + Cq, by positivity, ?_⟩
  intro rhoStar hrhoStar hrhoStar16 p hp2 hp3 Ω _ mu rho _ _ n hn X hX hIndep hLaw
    h2 hmean hsecond hp sigmaSq sigma scale nu Ln Rn I population rawEnergy
  have hraw := original_raw_normalization_data p hp2 hp3 rho n hn h2 hmean hsecond hp
  rcases hraw with ⟨hsigma, hprobNu, h2nu, hmeanNu, hnormNu, hpnu, hpvalue,
    hLn, hLnEq, hnormalizeMap, hnormalizeCross⟩
  letI : IsProbabilityMeasure nu := hprobNu
  let Praw : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
  let Pnorm : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  letI : IsProbabilityMeasure Praw := by dsimp [Praw]; infer_instance
  letI : IsProbabilityMeasure Pnorm := by dsimp [Pnorm]; infer_instance
  have hscale : 0 < scale := mul_pos hsigma (Real.sqrt_pos.mpr (by exact_mod_cast hn))
  have hPopulation : AEMeasurable population mu := AEMeasurable.of_eval hX
  have hPopulationMap : Measure.map population mu = Praw := by
    change Measure.map (fun omega i => X i omega) mu = _
    rw [hIndep.map_fun_eq_pi_map hX]
    congr 1
    funext i
    simpa only [Measure.map_id] using (hLaw i).map_eq
  have hPopulationLaw : HasLaw population Praw mu := ⟨hPopulation, hPopulationMap⟩
  let normalize : Shao.Path n → Shao.Path n := fun a i => a i / scale
  have hNormalizeM : Measurable normalize := by
    change Measurable (fun a : Shao.Path n => fun i : Fin n => a i / scale)
    exact Measurable.of_eval fun i =>
      (measurable_pi_apply (X := fun _ : Fin n => ℝ) i).div_const scale
  have hNormalizeLaw : HasLaw normalize Pnorm Praw := ⟨hNormalizeM.aemeasurable, hnormalizeMap⟩
  let Z : Set (Shao.Path n) := {a | Shao.energy a = 0}
  have hZm : MeasurableSet Z := measurableSet_eq_fun Shao.measurable_energy measurable_const
  have hNormalizeZero (a : Shao.Path n) : Shao.energy (normalize a) = 0 ↔ Shao.energy a = 0 := by
    have heq : Shao.energy (normalize a) = Shao.energy a / scale ^ 2 := by
      simp only [Shao.energy, normalize, div_pow, Finset.sum_div]
    rw [heq, div_eq_zero_iff]
    simp only [ne_of_gt (pow_pos hscale 2), or_false]
  have hNormalizePre : normalize ⁻¹' Z = Z := by
    ext a
    exact hNormalizeZero a
  have hNormalizeZeroLaw : Pnorm.real Z = Praw.real Z := by
    have hh := hNormalizeLaw.measureReal_eq hZm
    change Praw.real (normalize ⁻¹' Z) = Pnorm.real Z at hh
    rw [hNormalizePre] at hh
    exact hh.symm
  have hOriginalZero : mu.real {omega : Ω | rawEnergy omega = 0} = Praw.real Z :=
    hPopulationLaw.measureReal_eq hZm
  intro s x hs hx1 hxI signedMax crossing survival
  have hx : 0 < x := by linarith
  have hsabs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hsq : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hsignM : Measurable (fun z : ℝ => s * z) := by fun_prop
  let nus : Measure ℝ := Measure.map (fun z : ℝ => s * z) nu
  letI : IsProbabilityMeasure nus := by dsimp [nus]; exact (Measure.isProbabilityMeasure_map_iff hsignM.aemeasurable).mpr inferInstance
  let Ps : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nus)
  letI : IsProbabilityMeasure Ps := by dsimp [Ps]; infer_instance
  have h2s : Integrable (fun z : ℝ => z ^ 2) nus := by
    apply (integrable_map_measure (by fun_prop) hsignM.aemeasurable).2
    simpa only [Function.comp_def, mul_pow, hsq, one_mul] using h2nu
  have hsecondS : (∫ z : ℝ, z ^ 2 ∂nus) = ∫ z : ℝ, z ^ 2 ∂nu := by
    change (∫ z : ℝ, z ^ 2 ∂Measure.map (fun z => s * z) nu) = _
    rw [integral_map hsignM.aemeasurable (by fun_prop)]
    simp only [mul_pow, hsq, one_mul]
  have hmeanS : (∫ z : ℝ, z ∂nus) = 0 := by
    change (∫ z : ℝ, z ∂Measure.map (fun z => s * z) nu) = 0
    rw [integral_map hsignM.aemeasurable (f := fun z : ℝ => z) (by fun_prop),
      integral_const_mul, hmeanNu, mul_zero]
  have hnormS : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nus) = 1 := by
    rw [hsecondS]
    exact hnormNu
  have hpm : Measurable (fun z : ℝ => Real.rpow |z| p) := by
    change Measurable (fun z : ℝ => |z| ^ (p : ℝ))
    fun_prop
  have hps : Integrable (fun z : ℝ => Real.rpow |z| p) nus := by
    apply (integrable_map_measure hpm.aestronglyMeasurable hsignM.aemeasurable).2
    simpa only [Function.comp_def, abs_mul, hsabs, one_mul] using hpnu
  have hmomentS : (∫ z : ℝ, Real.rpow |z| p ∂nus) = ∫ z : ℝ, Real.rpow |z| p ∂nu := by
    change (∫ z : ℝ, Real.rpow |z| p ∂Measure.map (fun z => s * z) nu) = _
    rw [integral_map hsignM.aemeasurable hpm.aestronglyMeasurable]
    simp only [abs_mul, hsabs, one_mul]
  have hbetaS : (n : ℝ) * (∫ z : ℝ, Real.rpow |z| p ∂nus) = Ln := by
    rw [hmomentS]
    exact hLnEq.symm
  have hbudgetS (u : ℝ) : Shao.truncationBudget nus n u = Rn u := by
    change (n : ℝ) * (∫ z : ℝ, Shao.truncationF ((1 + u) * z) ∂Measure.map (fun z => s * z) nu) = _
    have hm : Measurable (fun z : ℝ => Shao.truncationF ((1 + u) * z)) :=
      Shao.continuous_truncationF.measurable.comp (measurable_const.mul measurable_id)
    rw [integral_map hsignM.aemeasurable
      (f := fun z : ℝ => Shao.truncationF ((1 + u) * z)) hm.aestronglyMeasurable]
    have heq (z : ℝ) : Shao.truncationF ((1 + u) * (s * z)) = Shao.truncationF ((1 + u) * z) := by
      rcases hs with rfl | rfl <;> simp [Shao.truncationF_neg]
    simp only [heq]
    rfl
  have hdomainS : x ≤ Real.rpow ((n : ℝ) * ∫ z : ℝ, Real.rpow |z| p ∂nus) (-1 / p) ∨
      Shao.truncationBudget nus n x ≤ 1 / 16 := by
    rcases hxI.2 with hm | hr
    · exact Or.inl (by simpa only [hbetaS] using hm)
    · exact Or.inr (by rw [hbudgetS]; exact hr.trans hrhoStar16)
  have hcomparison := hCanonical p hp2 hp3 nus n hn h2s hmeanS hnormS hps x hx hdomainS
  let signPath : Shao.Path n → Shao.Path n := fun a => s • a
  have hSignPathM : Measurable signPath := Measurable.of_eval fun i =>
    measurable_const.mul (measurable_pi_apply i)
  have hSignPathMap : Measure.map signPath Pnorm = Ps :=
    Measure.pi_map_pi (fun _ : Fin n => hsignM.aemeasurable)
  have hSignPathLaw : HasLaw signPath Ps Pnorm := ⟨hSignPathM.aemeasurable, hSignPathMap⟩
  have hSignEnergy (a : Shao.Path n) : Shao.energy (signPath a) = Shao.energy a := by
    simp only [Shao.energy, signPath, Pi.smul_apply, smul_eq_mul, mul_pow, hsq, one_mul]
  have hSignPreZero : signPath ⁻¹' Z = Z := by
    ext a
    simp only [Set.mem_preimage, Z, Set.mem_setOf_eq, hSignEnergy]
  have hSignZeroLaw : Ps.real Z = Pnorm.real Z := by
    have hh := hSignPathLaw.measureReal_eq hZm
    change Pnorm.real (signPath ⁻¹' Z) = Ps.real Z at hh
    rw [hSignPreZero] at hh
    exact hh.symm
  have hZeroIdentity : mu.real {omega : Ω | rawEnergy omega = 0} = Ps.real Z :=
    hOriginalZero.trans (hNormalizeZeroLaw.symm.trans hSignZeroLaw.symm)
  let AC : Set (Shao.Path n) := {a | x * Real.sqrt (Shao.energy a) ≤ Shao.upperMax (s • a) hn}
  have hACm : MeasurableSet AC := measurableSet_le (Shao.measurable_energyWall x)
    ((Shao.measurable_upperMax hn).comp hSignPathM)
  have hOriginalCross : mu.real crossing = Praw.real AC := hPopulationLaw.measureReal_eq hACm
  have hNormalizeCross : Pnorm.real AC = Praw.real AC := hnormalizeCross x s hs
  have hSignPreCross : signPath ⁻¹' Shao.upperCrossing hn x = AC := by
    ext a
    simp only [Set.mem_preimage, Shao.upperCrossing, Set.mem_setOf_eq, AC, hSignEnergy, signPath]
  have hSignCross : Ps.real (Shao.upperCrossing hn x) = Pnorm.real AC := by
    rw [← hSignPreCross]
    exact (hSignPathLaw.measureReal_eq (Shao.measurableSet_upperCrossing hn x)).symm
  have hCrossIdentity : mu.real crossing = Ps.real (Shao.upperCrossing hn x) :=
    hOriginalCross.trans (hNormalizeCross.symm.trans hSignCross.symm)
  have hCrossAE : AEMeasurable (crossing.indicator (fun _ : Ω => (1 : ℝ))) mu :=
    (measurable_const.indicator hACm).comp_aemeasurable hPopulation
  have hCrossInt : Integrable (crossing.indicator (fun _ : Ω => (1 : ℝ))) mu :=
    Integrable.of_bound hCrossAE.aestronglyMeasurable 1 (ae_of_all _ fun omega => by
      by_cases h : omega ∈ crossing <;> simp [Set.indicator, h])
  have hCrossNull : NullMeasurableSet crossing mu := hPopulation.nullMeasurable hACm
  have hComplement : survival = crossingᶜ := by
    ext omega
    simp only [survival, crossing, Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
  have hSurvivalAE : AEMeasurable (survival.indicator (fun _ : Ω => (1 : ℝ))) mu := by
    rw [hComplement]
    exact (measurable_const.indicator hACm.compl).comp_aemeasurable hPopulation
  have hSurvivalInt : Integrable (survival.indicator (fun _ : Ω => (1 : ℝ))) mu :=
    Integrable.of_bound hSurvivalAE.aestronglyMeasurable 1 (ae_of_all _ fun omega => by
      by_cases h : omega ∈ survival <;> simp [Set.indicator, h])
  have hRn : 0 ≤ Rn x := Shao.truncationBudget_nonneg nu n h2nu x
  have hCcanFull : Ccan ≤ 1 + Ccan + Cq := by linarith
  have hCqFull : Cq ≤ 1 + Ccan + Cq := by linarith
  have hWeak : |mu.real crossing - 2 * Shao.standardNormalTail x| ≤
      (1 + Ccan + Cq) * Rn x * Shao.standardNormalTail x := by
    rw [hCrossIdentity]
    have hb := hcomparison.2
    change |Ps.real (Shao.upperCrossing hn x) - 2 * Shao.standardNormalTail x| ≤
      Ccan * Shao.truncationBudget nus n x * Shao.standardNormalTail x at hb
    rw [hbudgetS] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCcanFull hRn) (hTail x).le)
  have hZero : mu.real {omega : Ω | rawEnergy omega = 0} ≤
      (1 + Ccan + Cq) * Rn x * Shao.standardNormalTail x := by
    rw [hZeroIdentity]
    have hb := hcomparison.1
    change Ps.real Z ≤ Cq * Shao.truncationBudget nus n x * Shao.standardNormalTail x at hb
    rw [hbudgetS] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCqFull hRn) (hTail x).le)
  have hSurvivalProbability : mu.real survival = 1 - mu.real crossing := by
    rw [hComplement, measureReal_compl₀ hCrossNull, probReal_univ]
  have hStrict : |mu.real survival - (1 - 2 * Shao.standardNormalTail x)| ≤
      (1 + Ccan + Cq) * Rn x * Shao.standardNormalTail x := by
    rw [hSurvivalProbability]
    have heq : 1 - mu.real crossing - (1 - 2 * Shao.standardNormalTail x) =
        -(mu.real crossing - 2 * Shao.standardNormalTail x) := by ring
    rw [heq, abs_neg]
    exact hWeak
  refine ⟨hCrossInt, hSurvivalInt, hZero, hWeak, hStrict, ?_⟩
  have heq : mu.real crossing / Shao.standardNormalTail x - 2 =
      (mu.real crossing - 2 * Shao.standardNormalTail x) / Shao.standardNormalTail x := by
    field_simp [ne_of_gt (hTail x)] <;> ring
  rw [heq, abs_div, abs_of_pos (hTail x)]
  exact (div_le_iff₀ (hTail x)).mpr hWeak


end Shao.Probability.SourceOriginalGrowingRelative
