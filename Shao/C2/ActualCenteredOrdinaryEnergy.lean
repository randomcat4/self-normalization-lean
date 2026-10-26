import Shao.C2.ActualUniformAbsoluteFixedThreshold
import Shao.Probability.SourceActualBoundedRelativeConsumer
import Shao.C2.TwoSided

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
noncomputable section
namespace Shao.C2.ActualCenteredOrdinaryEnergy
open MeasureTheory ProbabilityTheory Set Filter
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.Probability.SourcePermutationReveal
open Shao.C2.ActualSignedDoubleTelescope
open scoped BigOperators NNReal Topology Classical

theorem iid_actual_centered_ordinary_energy_relative_comparison :
    ∃ etaG epsilonG C : ℝ, 0 < etaG ∧ 0 < epsilonG ∧ 0 < C ∧
      ∀ {ΩB : Type*} [MeasurableSpace ΩB]
        (Bm : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
        IsBrownianReal Bm PB →
        ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
          (n : ℕ) (hn : 0 < n) (x : ℝ), 1 / 2 ≤ x →
          (∀ᵐ z : ℝ ∂rho, |z| ≤ etaG * Real.sqrt (n : ℝ) / x) →
          (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
          let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
          let delta : ℝ := beta / Real.sqrt (n : ℝ)
          delta * x ^ 3 ≤ epsilonG →
          |(Measure.pi (fun _ : Fin n => rho)).real (Shao.C2.doubleCrossing hn x) -
              PB.real {omega |
                (∃ t : BridgeTime, x ≤ Bm ⟨(t : ℝ), t.property.1⟩ omega) ∧
                ∃ t : BridgeTime, Bm ⟨(t : ℝ), t.property.1⟩ omega ≤ -x}| ≤
            C * delta * (1 + x) ^ 3 * Shao.standardNormalTail x := by
  classical
  obtain ⟨epsilonF, CA, KD, hepsilonF, _hepsilonUpper, _hCA, _hKD, hLowM⟩ :=
    Shao.C2.ActualUniformAbsoluteFixedThreshold.iid_actual_bounded_centered_uniform_absolute_fixed_threshold_comparison
  obtain ⟨CF, hCF, hLow⟩ := hLowM 16 (by norm_num)
  obtain ⟨CH, _hCH, hHigh⟩ :=
    Shao.Probability.SourceActualBoundedRelativeConsumer.iid_actual_bounded_centered_high_threshold_relative_comparison
  refine ⟨1 / 200, min epsilonF (1 / (27 * 20000)), max CF CH,
    by norm_num, lt_min hepsilonF (by norm_num),
    lt_of_lt_of_le hCF (le_max_left CF CH), ?_⟩
  intro ΩB _ Bm PB _ hBm rho _ n hn x hx hbound hmean hsecond
  dsimp only
  intro hsmall
  let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
  let delta : ℝ := beta / Real.sqrt (n : ℝ)
  change delta * x ^ 3 ≤ min epsilonF (1 / (27 * 20000)) at hsmall
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
  let DB : Set ΩB := {omega |
    (∃ t : BridgeTime, x ≤ Bm ⟨(t : ℝ), t.property.1⟩ omega) ∧
    ∃ t : BridgeTime, Bm ⟨(t : ℝ), t.property.1⟩ omega ≤ -x}
  change |P.real (Shao.C2.doubleCrossing hn x) - PB.real DB| ≤
    max CF CH * delta * (1 + x) ^ 3 * Shao.standardNormalTail x
  have hxpos : 0 < x := by linarith only [hx]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  let Bcap : ℝ := Real.sqrt (n : ℝ) / (200 * x)
  have hBpos : 0 < Bcap := div_pos hsn (mul_pos (by norm_num) hxpos)
  have hcapEq : (1 / 200 : ℝ) * Real.sqrt (n : ℝ) / x = Bcap := by
    dsimp only [Bcap]
    field_simp [ne_of_gt hxpos] <;> ring
  have hsupport : ∀ᵐ z : ℝ ∂rho, |z| ≤ Bcap := by
    filter_upwards [hbound] with z hz
    simpa only [hcapEq] using hz
  have hB100 : Bcap ≤ Real.sqrt (n : ℝ) / (100 * x) := by
    dsimp only [Bcap]
    exact div_le_div_of_nonneg_left hsn.le (mul_pos (by norm_num) hxpos)
      (by nlinarith only [hxpos])
  have hbeta : 0 ≤ beta := integral_nonneg (fun z => pow_nonneg (abs_nonneg z) 3)
  have hdelta : 0 ≤ delta := div_nonneg hbeta hsn.le
  have hPsi : 0 ≤ Shao.standardNormalTail x := ((Shao.standardNormalTail_basic.2.2.1 x).1).le
  have hWeight : 0 ≤ delta * (1 + x) ^ 3 * Shao.standardNormalTail x :=
    mul_nonneg (mul_nonneg hdelta (pow_nonneg (by linarith only [hx]) 3)) hPsi
  have hsmallLow : delta * x ^ 3 ≤ epsilonF := hsmall.trans (min_le_left _ _)
  have hOnePlus : 1 + x ≤ 3 * x := by linarith only [hx]
  have hu : delta * (1 + x) ^ 3 ≤ 1 / 20000 := by
    calc
      delta * (1 + x) ^ 3 ≤ delta * (3 * x) ^ 3 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by linarith only [hx]) hOnePlus 3) hdelta
      _ = 27 * (delta * x ^ 3) := by ring
      _ ≤ 27 * (1 / (27 * 20000) : ℝ) :=
        mul_le_mul_of_nonneg_left (hsmall.trans (min_le_right _ _)) (by norm_num)
      _ = 1 / 20000 := by norm_num
  have hHit (s : ℝ) (hsign : s = 1 ∨ s = -1) (a : Shao.Path n) :
      (∃ r : ℕ, r ≤ n ∧ actualWall a x ≤ s * Shao.prefixSum a r) ↔
        actualWall a x ≤ Shao.upperMax (s • a) hn := by
    constructor
    · rintro ⟨rank, hr, hc⟩
      by_cases hr0 : rank = 0
      · have hw0 : actualWall a x ≤ 0 := by
          simpa only [hr0, Shao.prefixSum_zero, mul_zero] using hc
        have hE0 : Shao.energy a = 0 := by
          by_contra hne
          have hp : 0 < Shao.energy a :=
            lt_of_le_of_ne (Shao.energy_nonneg a) (Ne.symm hne)
          exact (not_lt_of_ge hw0) (mul_pos hxpos (Real.sqrt_pos.mpr hp))
        have hSigned0 : Shao.energy (s • a) = 0 := by
          rcases hsign with rfl | rfl <;> simpa using hE0
        rw [Shao.upperMax_eq_zero_of_energy_eq_zero _ hn hSigned0]
        exact hw0
      · have hp := Shao.le_upperMax (s • a) hn rank (Nat.one_le_iff_ne_zero.mpr hr0) hr
        rw [Shao.prefixSum_smul] at hp
        exact hc.trans hp
    · intro hc
      obtain ⟨rank, _hr, hrn, hEq⟩ := Shao.upperMax_attained (s • a) hn
      refine ⟨rank, hrn, ?_⟩
      rw [hEq, Shao.prefixSum_smul] at hc
      exact hc
  have hEvent : doubleCrossingEvent x = Shao.C2.doubleCrossing hn x := by
    ext a
    change ((∃ rank : ℕ, rank ≤ n ∧ actualWall a x ≤ Shao.prefixSum a rank) ∧
      (∃ rank : ℕ, rank ≤ n ∧ Shao.prefixSum a rank ≤ -actualWall a x)) ↔
      (actualWall a x ≤ Shao.upperMax a hn ∧ actualWall a x ≤ Shao.upperMax (-a) hn)
    constructor
    · rintro ⟨⟨rank, hr, hc⟩, ⟨t, ht, hd⟩⟩
      constructor
      · simpa only [one_smul] using
          (hHit 1 (Or.inl rfl) a).mp ⟨rank, hr, by simpa only [one_mul] using hc⟩
      · simpa only [neg_one_smul] using
          (hHit (-1) (Or.inr rfl) a).mp
            ⟨t, ht, by simp only [neg_one_mul]; linarith only [hd]⟩
    · rintro ⟨hu, hl⟩
      obtain ⟨rank, hr, hc⟩ :=
        (hHit 1 (Or.inl rfl) a).mpr (by simpa only [one_smul] using hu)
      obtain ⟨t, ht, hd⟩ :=
        (hHit (-1) (Or.inr rfl) a).mpr (by simpa only [neg_one_smul] using hl)
      refine ⟨⟨rank, hr, by simpa only [one_mul] using hc⟩, ⟨t, ht, ?_⟩⟩
      simp only [neg_one_mul] at hd
      linarith only [hd]
  by_cases hlow : x ≤ 16
  · rcases hLow rho Bcap hBpos hsupport hmean hsecond n hn x hx hB100 hsmallLow
        Bm PB hBm with ⟨_hR0, _hRx, _hAbsolute, hRelative, _hMaximum⟩
    have hrel := hRelative hlow
    rw [hEvent] at hrel
    change |P.real (Shao.C2.doubleCrossing hn x) - PB.real DB| ≤
      CF * delta * (1 + x) ^ 3 * Shao.standardNormalTail x at hrel
    calc
      |P.real (Shao.C2.doubleCrossing hn x) - PB.real DB| ≤
          CF * delta * (1 + x) ^ 3 * Shao.standardNormalTail x := hrel
      _ ≤ max CF CH * delta * (1 + x) ^ 3 * Shao.standardNormalTail x := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right (le_max_left CF CH) hWeight
  · have hxHigh : 16 ≤ x := le_of_lt (lt_of_not_ge hlow)
    rcases hHigh Bm PB hBm rho Bcap hBpos hsupport hmean hsecond n hn x hxHigh
        (le_rfl : Bcap ≤ Real.sqrt (n : ℝ) / (200 * x)) hu with
      ⟨_hSecondI, _hThirdI, _hDeltaPos, hR, _hDMeasurable, _hDI,
        _hDBMeasurable, _hZMeasurable, _hZI, _hResidual, hBrownian⟩
    rw [hR] at hBrownian
    have hrel : |P.real (Shao.C2.doubleCrossing hn x) - PB.real DB| ≤
        CH * delta * (1 + x) ^ 3 * Shao.standardNormalTail x := by
      simpa only [mul_assoc] using hBrownian
    calc
      |P.real (Shao.C2.doubleCrossing hn x) - PB.real DB| ≤
          CH * delta * (1 + x) ^ 3 * Shao.standardNormalTail x := hrel
      _ ≤ max CF CH * delta * (1 + x) ^ 3 * Shao.standardNormalTail x := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right (le_max_right CF CH) hWeight

end Shao.C2.ActualCenteredOrdinaryEnergy
