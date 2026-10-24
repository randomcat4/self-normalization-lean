import Shao.OQ4.StrictIIDWindow
import Shao.OQ4.CriticalWindowNecessity
import Shao.OQ4.RademacherOriginalStrictS4
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal Topology
universe uX uB

namespace Shao.OQ4.StrictWindowNecessity
variable {ΩB : Type uB} [MeasurableSpace ΩB]

-- B01: half-integer strict wall; delta_strict is EXACTLY 1/2.
def criticalHeight (c : ℝ) (n : ℕ) : ℝ :=
  CriticalWindowNecessity.criticalHeight c n + 1 / 2

-- B02: total real division at n=0; limits explicitly use the n>0 tail.
def criticalPoint (c : ℝ) (n : ℕ) : ℝ :=
  criticalHeight c n / Real.sqrt (n : ℝ)

-- B03: half of the weak integer displacement in the logarithmic correction.
def criticalGap (c : ℝ) : ℝ := Real.exp (Real.pi ^ 2 / (8 * c ^ 3)) - 1

-- B04: actual one-law quotient, positive tail, scale, and nonzero error limit.
theorem rademacher_half_integer_ratio_tendsto
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (c : ℝ) (hc : 0 < c)
    (nSeq : ℕ → ℕ) (hn : Tendsto nSeq atTop atTop) :
    0 < criticalGap c ∧
    (∀ᶠ j : ℕ in atTop,
      1 ≤ nSeq j ∧
      RademacherGeneralStrictS4.delta (criticalHeight c (nSeq j)) = 1 / 2 ∧
      0 < criticalPoint c (nSeq j) ∧
      0 < (CriticalWindowNecessity.rademacherIIDLaw.{uX}).real
        (RademacherOriginalStrictBoundary.sourceStrictEvent (nSeq j)
          (CriticalWindowNecessity.rademacherIIDCoordinate.{uX})
          (criticalPoint c (nSeq j))) ∧
      0 < Shao.Probability.BrownianSup.probability B P hB
        (criticalPoint c (nSeq j))) ∧
    Tendsto (fun j => criticalPoint c (nSeq j)) atTop (𝓝 (0 : ℝ)) ∧
    Tendsto (fun j => criticalPoint c (nSeq j) *
      (nSeq j : ℝ) ^ ((1 : ℝ) / 6)) atTop (𝓝 c) ∧
    Tendsto (fun j =>
      (CriticalWindowNecessity.rademacherIIDLaw.{uX}).real
        (RademacherOriginalStrictBoundary.sourceStrictEvent (nSeq j)
          (CriticalWindowNecessity.rademacherIIDCoordinate.{uX})
          (criticalPoint c (nSeq j))) /
        Shao.Probability.BrownianSup.probability B P hB
          (criticalPoint c (nSeq j)))
      atTop (𝓝 (Real.exp (Real.pi ^ 2 / (8 * c ^ 3)))) ∧
    Tendsto (fun j =>
      |(CriticalWindowNecessity.rademacherIIDLaw.{uX}).real
        (RademacherOriginalStrictBoundary.sourceStrictEvent (nSeq j)
          (CriticalWindowNecessity.rademacherIIDCoordinate.{uX})
          (criticalPoint c (nSeq j))) /
        Shao.Probability.BrownianSup.probability B P hB
          (criticalPoint c (nSeq j)) - 1|)
      atTop (𝓝 (criticalGap c)) := by
  classical
  rcases CriticalWindowNecessity.rademacherIID_facts.{uX} with
    ⟨hμ, hX, hind, _, hmap, _, _, _⟩
  letI : IsProbabilityMeasure (CriticalWindowNecessity.rademacherIIDLaw.{uX}) := hμ
  have hLaw (i : ℕ) :
      IdentDistrib (CriticalWindowNecessity.rademacherIIDCoordinate.{uX} (i + 1))
        (id : ℝ → ℝ) (CriticalWindowNecessity.rademacherIIDLaw.{uX})
        RademacherCosine.law :=
    ⟨(hX i).aemeasurable, measurable_id.aemeasurable,
      by simpa only [Measure.map_id] using hmap i⟩
  have hdelta (n : ℕ) :
      RademacherGeneralStrictS4.delta (criticalHeight c n) = 1 / 2 := by
    let m : ℕ := CriticalWindowNecessity.criticalCell c n
    have hceil : Nat.ceil ((m : ℝ) + 1 / 2) = m + 1 := by
      apply (Nat.ceil_eq_iff (by omega : m + 1 ≠ 0)).2
      simp only [Nat.add_sub_cancel_right, Nat.cast_add, Nat.cast_one]
      constructor <;> linarith
    change (Nat.ceil ((m : ℝ) + 1 / 2) : ℝ) - ((m : ℝ) + 1 / 2) = 1 / 2
    rw [hceil, Nat.cast_add, Nat.cast_one]
    ring
  have hround (n : ℕ) :
      0 ≤ criticalHeight c n - c * (n : ℝ) ^ ((1 : ℝ) / 3) ∧
      criticalHeight c n - c * (n : ℝ) ^ ((1 : ℝ) / 3) ≤ 2 := by
    have hnonneg : 0 ≤ c * (n : ℝ) ^ ((1 : ℝ) / 3) :=
      mul_nonneg hc.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hlo := Nat.le_ceil (c * (n : ℝ) ^ ((1 : ℝ) / 3))
    have hup := Nat.ceil_lt_add_one hnonneg
    change 0 ≤ (Nat.ceil (c * (n : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) + 1 / 2 -
        c * (n : ℝ) ^ ((1 : ℝ) / 3) ∧
      (Nat.ceil (c * (n : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) + 1 / 2 -
        c * (n : ℝ) ^ ((1 : ℝ) / 3) ≤ 2
    constructor <;> linarith
  let r : ℕ → ℝ := fun j => (nSeq j : ℝ) ^ ((1 : ℝ) / 3)
  let q : ℕ → ℝ := fun j => (nSeq j : ℝ) ^ ((1 : ℝ) / 6)
  have hN : Tendsto (fun j => (nSeq j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hr : Tendsto r atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 3)).comp hN
  have hq : Tendsto q atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 6)).comp hN
  have hr0 (j : ℕ) : 0 ≤ r j := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hnt : ∀ᶠ j in atTop, 0 < nSeq j := by
    filter_upwards [hn.eventually_ge_atTop 1] with j hj
    omega
  have hrpos : ∀ᶠ j in atTop, 0 < r j := by
    filter_upwards [hnt] with j hj
    exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hj) _
  have hhpos : ∀ᶠ j in atTop, 0 < criticalHeight c (nSeq j) := by
    filter_upwards [hrpos] with j hj
    have hlo := (Nat.le_ceil (c * (nSeq j : ℝ) ^ ((1 : ℝ) / 3)))
    change 0 < CriticalWindowNecessity.criticalHeight c (nSeq j) + 1 / 2
    have hbase : 0 < CriticalWindowNecessity.criticalHeight c (nSeq j) :=
      (mul_pos hc hj).trans_le hlo
    linarith
  have hid : ∀ᶠ j in atTop,
      ((nSeq j : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (nSeq j : ℝ) ∧
      Real.sqrt (nSeq j : ℝ) = r j * q j ∧
      criticalPoint c (nSeq j) * q j = criticalHeight c (nSeq j) / r j ∧
      (nSeq j : ℝ) / criticalHeight c (nSeq j) ^ 2 =
        r j / (criticalHeight c (nSeq j) / r j) ^ 2 ∧
      (nSeq j : ℝ) / criticalHeight c (nSeq j) ^ 3 =
        1 / (criticalHeight c (nSeq j) / r j) ^ 3 := by
    filter_upwards [hnt, hhpos] with j hnj hhj
    have hNj : 0 < (nSeq j : ℝ) := Nat.cast_pos.mpr hnj
    have hrj : 0 < r j := Real.rpow_pos_of_pos hNj _
    have hqj : 0 < q j := Real.rpow_pos_of_pos hNj _
    have hr3 : r j ^ 3 = (nSeq j : ℝ) := by
      dsimp [r]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNj.le]
      norm_num
    have hs : Real.sqrt (nSeq j : ℝ) = r j * q j := by
      dsimp [r, q]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hNj]
      norm_num
    refine ⟨hr3, hs, ?_, ?_, ?_⟩
    · unfold criticalPoint
      rw [hs]
      field_simp [hrj.ne', hqj.ne'] <;> ring
    · calc
        (nSeq j : ℝ) / criticalHeight c (nSeq j) ^ 2 =
            r j ^ 3 / criticalHeight c (nSeq j) ^ 2 :=
          congrArg (fun z : ℝ => z / criticalHeight c (nSeq j) ^ 2) hr3.symm
        _ = _ := by field_simp [hrj.ne', hhj.ne'] <;> ring
    · calc
        (nSeq j : ℝ) / criticalHeight c (nSeq j) ^ 3 =
            r j ^ 3 / criticalHeight c (nSeq j) ^ 3 :=
          congrArg (fun z : ℝ => z / criticalHeight c (nSeq j) ^ 3) hr3.symm
        _ = _ := by field_simp [hrj.ne', hhj.ne'] <;> ring
  have hinv : Tendsto (fun j => 2 / r j) atTop (𝓝 (0 : ℝ)) := by
    have ht : Tendsto (fun j => (2 : ℝ) * (r j)⁻¹)
        atTop (𝓝 ((2 : ℝ) * 0)) :=
      tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hr)
    simpa only [mul_zero, div_eq_mul_inv, Function.comp_def] using
      ht
  have herr : Tendsto
      (fun j => (criticalHeight c (nSeq j) - c * r j) / r j)
      atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero'
      (Eventually.of_forall fun j => div_nonneg (hround (nSeq j)).1 (hr0 j))
      (Eventually.of_forall fun j =>
        div_le_div_of_nonneg_right (hround (nSeq j)).2 (hr0 j)) hinv
  have hratio : Tendsto (fun j => criticalHeight c (nSeq j) / r j)
      atTop (𝓝 c) := by
    have hsum : Tendsto
        (fun j => c + (criticalHeight c (nSeq j) - c * r j) / r j)
        atTop (𝓝 c) := by
      simpa only [add_zero] using tendsto_const_nhds.add herr
    apply hsum.congr'
    filter_upwards [hrpos] with j hj
    field_simp [hj.ne'] <;> ring
  have hh : Tendsto (fun j => criticalHeight c (nSeq j)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hr.eventually_ge_atTop (b / c)] with j hj
    have hb : b ≤ c * r j := by
      have hbc := (div_le_iff₀ hc).mp hj
      simpa only [mul_comm] using hbc
    exact hb.trans (by linarith [(hround (nSeq j)).1])
  let bound : ℝ := (c + 1) ^ 2
  have hbound : 0 < bound := by dsimp [bound]; positivity
  have hratioBound : ∀ᶠ j in atTop,
      (criticalHeight c (nSeq j) / r j) ^ 2 ≤ bound := by
    have hlt : c ^ 2 < bound := by dsimp [bound]; nlinarith
    exact ((hratio.pow 2).eventually (eventually_lt_nhds hlt)).mono fun _ h => h.le
  have hscale2 : Tendsto
      (fun j => (nSeq j : ℝ) / criticalHeight c (nSeq j) ^ 2)
      atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hid, hratioBound, hr.eventually_ge_atTop (b * bound),
      hrpos, hhpos] with j hj hz hbj hrj hhj
    rw [hj.2.2.2.1]
    have hzpos : 0 < (criticalHeight c (nSeq j) / r j) ^ 2 :=
      sq_pos_of_pos (div_pos hhj hrj)
    apply (le_div_iff₀ hzpos).mpr
    by_cases hb : 0 ≤ b
    · exact (mul_le_mul_of_nonneg_left hz hb).trans hbj
    · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hb) hzpos.le).trans hrj.le
  have hscale3 : Tendsto
      (fun j => (nSeq j : ℝ) / criticalHeight c (nSeq j) ^ 3)
      atTop (𝓝 (1 / c ^ 3)) := by
    have hi : Tendsto
        (fun j => 1 / (criticalHeight c (nSeq j) / r j) ^ 3)
        atTop (𝓝 (1 / c ^ 3)) :=
      tendsto_const_nhds.div (hratio.pow 3) (pow_ne_zero 3 hc.ne')
    exact hi.congr' (hid.mono fun _ hj => hj.2.2.2.2.symm)
  have hxscale : Tendsto (fun j => criticalPoint c (nSeq j) * q j)
      atTop (𝓝 c) :=
    hratio.congr' (hid.mono fun _ hj => hj.2.2.1.symm)
  have hx : Tendsto (fun j => criticalPoint c (nSeq j)) atTop (𝓝 (0 : ℝ)) := by
    have hx0 : Tendsto
        (fun j => (criticalHeight c (nSeq j) / r j) * (q j)⁻¹)
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero, Pi.inv_apply] using hratio.mul hq.inv_tendsto_atTop
    apply hx0.congr'
    filter_upwards [hid, hnt] with j hj hnj
    have hqj : 0 < q j := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hnj) _
    calc
      (criticalHeight c (nSeq j) / r j) * (q j)⁻¹ =
          (criticalPoint c (nSeq j) * q j) * (q j)⁻¹ := by rw [hj.2.2.1]
      _ = criticalPoint c (nSeq j) := by field_simp [hqj.ne']
  have hbounded : ∃ M : ℝ, 0 < M ∧ ∃ K : ℕ, ∀ j : ℕ, K ≤ j →
      (nSeq j : ℝ) / criticalHeight c (nSeq j) ^ 3 ≤ M := by
    have hM : 0 < 1 / c ^ 3 + 1 := by positivity
    have he : ∀ᶠ j in atTop,
        (nSeq j : ℝ) / criticalHeight c (nSeq j) ^ 3 < 1 / c ^ 3 + 1 :=
      hscale3.eventually (eventually_lt_nhds (by linarith))
    obtain ⟨K, hK⟩ := eventually_atTop.mp he
    exact ⟨1 / c ^ 3 + 1, hM, K, fun j hj => (hK j hj).le⟩
  have hS4 := RademacherOriginalStrictS4.original_strict_S4 B P hB
    (CriticalWindowNecessity.rademacherIIDLaw.{uX})
    (CriticalWindowNecessity.rademacherIIDCoordinate.{uX}) hind hLaw
    nSeq (fun j => criticalHeight c (nSeq j)) hh hscale2 hbounded
  have hcorrection : Tendsto (fun j =>
      RademacherGeneralStrictS4.correction (nSeq j) (criticalHeight c (nSeq j)))
      atTop (𝓝 (Real.pi ^ 2 / (8 * c ^ 3))) := by
    have heq : (Real.pi ^ 2 / 4) * (1 / c ^ 3) * (1 / 2) =
        Real.pi ^ 2 / (8 * c ^ 3) := by ring
    rw [← heq]
    have ht := ((tendsto_const_nhds :
      Tendsto (fun _ : ℕ => Real.pi ^ 2 / 4) atTop (𝓝 (Real.pi ^ 2 / 4))).mul hscale3).mul
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ) / 2) atTop (𝓝 (1 / 2)))
    simpa only [RademacherGeneralStrictS4.correction, hdelta] using ht
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hcorrection
  have hquot : Tendsto (fun j =>
      RademacherOriginalStrictS4.sourceQ B P hB
        (CriticalWindowNecessity.rademacherIIDLaw.{uX})
        (CriticalWindowNecessity.rademacherIIDCoordinate.{uX})
        (nSeq j) (criticalHeight c (nSeq j)))
      atTop (𝓝 (Real.exp (Real.pi ^ 2 / (8 * c ^ 3)))) := by
    have ht := hS4.2.2.2.1.mul hexp
    simp only [one_mul] at ht
    apply ht.congr'
    exact Eventually.of_forall fun j =>
      div_mul_cancel₀ _ (Real.exp_ne_zero _)
  have hgap : 0 < criticalGap c := by
    unfold criticalGap
    have hp : 0 < Real.pi ^ 2 / (8 * c ^ 3) := by positivity
    have he := Real.exp_lt_exp.mpr hp
    rw [Real.exp_zero] at he
    linarith
  have herror : Tendsto (fun j =>
      |RademacherOriginalStrictS4.sourceQ B P hB
        (CriticalWindowNecessity.rademacherIIDLaw.{uX})
        (CriticalWindowNecessity.rademacherIIDCoordinate.{uX})
        (nSeq j) (criticalHeight c (nSeq j)) - 1|)
      atTop (𝓝 (criticalGap c)) := by
    have ht := (hquot.sub (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))).abs
    change Tendsto _ atTop (𝓝 |criticalGap c|) at ht
    rw [abs_of_pos hgap] at ht
    exact ht
  refine ⟨hgap, ?_, hx, hxscale, hquot, herror⟩
  filter_upwards [hnt, hhpos, hS4.2.1] with j hnj hhj hj
  have hs : 0 < Real.sqrt (nSeq j : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr hnj)
  exact ⟨by omega, hdelta _, div_pos hhj hs, hj.1, hj.2.2.1⟩

-- B05: proper strict sSup even if a_n<=0, using accepted weak bounds + 1.
theorem rademacher_strict_windowError_spec
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a : ℕ → ℝ) (n : ℕ)
    (hn : 0 < n) (ha : a n < 1) :
    ((fun x : ℝ =>
      |(CriticalWindowNecessity.rademacherIIDLaw.{uX}).real
        (RademacherOriginalStrictBoundary.sourceStrictEvent n
          (CriticalWindowNecessity.rademacherIIDCoordinate.{uX}) x) /
        Shao.Probability.BrownianSup.probability B P hB x - 1|) ''
      Ioo (a n) 1).Nonempty ∧
    BddAbove ((fun x : ℝ =>
      |(CriticalWindowNecessity.rademacherIIDLaw.{uX}).real
        (RademacherOriginalStrictBoundary.sourceStrictEvent n
          (CriticalWindowNecessity.rademacherIIDCoordinate.{uX}) x) /
        Shao.Probability.BrownianSup.probability B P hB x - 1|) ''
      Ioo (a n) 1) ∧
    IsLUB ((fun x : ℝ =>
      |(CriticalWindowNecessity.rademacherIIDLaw.{uX}).real
        (RademacherOriginalStrictBoundary.sourceStrictEvent n
          (CriticalWindowNecessity.rademacherIIDCoordinate.{uX}) x) /
        Shao.Probability.BrownianSup.probability B P hB x - 1|) ''
      Ioo (a n) 1)
      (StrictIIDWindow.sourceStrictWindowError B P hB
        (CriticalWindowNecessity.rademacherIIDLaw.{uX})
        (CriticalWindowNecessity.rademacherIIDCoordinate.{uX}) a n) ∧
    0 ≤ StrictIIDWindow.sourceStrictWindowError B P hB
      (CriticalWindowNecessity.rademacherIIDLaw.{uX})
      (CriticalWindowNecessity.rademacherIIDCoordinate.{uX}) a n ∧
    (∀ x ∈ Ioo (a n) 1,
      |(CriticalWindowNecessity.rademacherIIDLaw.{uX}).real
        (RademacherOriginalStrictBoundary.sourceStrictEvent n
          (CriticalWindowNecessity.rademacherIIDCoordinate.{uX}) x) /
        Shao.Probability.BrownianSup.probability B P hB x - 1| ≤
        StrictIIDWindow.sourceStrictWindowError B P hB
          (CriticalWindowNecessity.rademacherIIDLaw.{uX})
          (CriticalWindowNecessity.rademacherIIDCoordinate.{uX}) a n) := by
  classical
  let μ := CriticalWindowNecessity.rademacherIIDLaw.{uX}
  let X := CriticalWindowNecessity.rademacherIIDCoordinate.{uX}
  letI : IsProbabilityMeasure μ := CriticalWindowNecessity.rademacherIID_facts.{uX}.1
  let F : ℝ → ℝ := Shao.Probability.BrownianSup.probability B P hB
  let e : ℝ → ℝ := fun x =>
    |μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent n X x) / F x - 1|
  have hs := CriticalWindowNecessity.rademacher_windowError_spec B P hB a n hn ha
  have hbound (x : ℝ) (hx : x ∈ Ioo (a n) 1) :
      e x ≤ OriginalWindowProduct.windowError B P hB RademacherCosine.law a n + 1 := by
    have hsubset : RademacherOriginalStrictBoundary.sourceStrictEvent n X x ⊆
        OriginalIIDWindow.sourceEvent n X x := by
      intro ω hω
      exact (OriginalIIDWindow.sourceMaximum_le_iff n hn X ω _).2
        (fun k hk hkn => (hω k hk hkn).le)
    have hprob : μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent n X x) ≤
        OriginalWindowProduct.productProbability RademacherCosine.law n x := by
      rw [← CriticalWindowNecessity.rademacher_original_probability_eq_product.{uX} n x]
      exact measureReal_mono hsubset
    have hF : 0 ≤ F x := ENNReal.toReal_nonneg
    have hquot : μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent n X x) / F x ≤
        OriginalWindowProduct.productProbability RademacherCosine.law n x / F x :=
      div_le_div_of_nonneg_right hprob hF
    have hquot0 : 0 ≤
        μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent n X x) / F x :=
      div_nonneg ENNReal.toReal_nonneg hF
    have hw := hs.2.2.2.2.2 x hx
    change |OriginalWindowProduct.productProbability RademacherCosine.law n x / F x - 1| ≤
      OriginalWindowProduct.windowError B P hB RademacherCosine.law a n at hw
    dsimp only [e]
    apply abs_le.mpr
    constructor
    · linarith [hs.2.2.2.1]
    · linarith [le_abs_self
        (OriginalWindowProduct.productProbability RademacherCosine.law n x / F x - 1)]
  have hmid : (a n + 1) / 2 ∈ Ioo (a n) 1 := ⟨by linarith, by linarith⟩
  have hmem : e ((a n + 1) / 2) ∈ e '' Ioo (a n) 1 :=
    ⟨(a n + 1) / 2, hmid, rfl⟩
  have hne : (e '' Ioo (a n) 1).Nonempty := ⟨_, hmem⟩
  have hb : BddAbove (e '' Ioo (a n) 1) := by
    refine ⟨OriginalWindowProduct.windowError B P hB RademacherCosine.law a n + 1, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact hbound x hx
  have hlub : IsLUB (e '' Ioo (a n) 1)
      (StrictIIDWindow.sourceStrictWindowError B P hB μ X a n) :=
    isLUB_csSup hne hb
  refine ⟨hne, hb, hlub, (abs_nonneg _).trans (hlub.1 hmem), ?_⟩
  intro x hx
  exact hlub.1 ⟨x, hx, rfl⟩

-- B06: stronger necessity witness; no antitonicity or a_n->0 premise.
theorem rademacher_strict_window_obstruction
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a : ℕ → ℝ)
    (hbad : ¬ Tendsto
      (fun n => a n * (n : ℝ) ^ ((1 : ℝ) / 6)) atTop atTop) :
    ∃ c : ℝ, 0 < c ∧ 0 < criticalGap c ∧ ∃ nSeq : ℕ → ℕ,
      StrictMono nSeq ∧
      (∀ᶠ j : ℕ in atTop,
        1 ≤ nSeq j ∧ criticalPoint c (nSeq j) ∈ Ioo (a (nSeq j)) 1) ∧
      Tendsto (fun j =>
        |(CriticalWindowNecessity.rademacherIIDLaw.{uX}).real
          (RademacherOriginalStrictBoundary.sourceStrictEvent (nSeq j)
            (CriticalWindowNecessity.rademacherIIDCoordinate.{uX})
            (criticalPoint c (nSeq j))) /
          Shao.Probability.BrownianSup.probability B P hB
            (criticalPoint c (nSeq j)) - 1|)
        atTop (𝓝 (criticalGap c)) ∧
      (∀ᶠ j : ℕ in atTop,
        criticalGap c / 2 ≤ StrictIIDWindow.sourceStrictWindowError B P hB
          (CriticalWindowNecessity.rademacherIIDLaw.{uX})
          (CriticalWindowNecessity.rademacherIIDCoordinate.{uX}) a (nSeq j)) := by
  obtain ⟨c, hc, _, nSeq, hmono, hwindow, _, _⟩ :=
    CriticalWindowNecessity.rademacher_window_obstruction B P hB a hbad
  have hcrit := rademacher_half_integer_ratio_tendsto.{uX} B P hB c hc
    nSeq hmono.tendsto_atTop
  have hnewwindow : ∀ᶠ j in atTop,
      1 ≤ nSeq j ∧ criticalPoint c (nSeq j) ∈ Ioo (a (nSeq j)) 1 := by
    have hupper : ∀ᶠ j in atTop, criticalPoint c (nSeq j) < 1 :=
      hcrit.2.2.1.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hwindow, hupper] with j hj hju
    have hs : 0 < Real.sqrt (nSeq j : ℝ) :=
      Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega : 0 < nSeq j))
    have hraise : CriticalWindowNecessity.criticalPoint c (nSeq j) <
        criticalPoint c (nSeq j) := by
      unfold CriticalWindowNecessity.criticalPoint criticalPoint criticalHeight
      apply (div_lt_div_iff_of_pos_right hs).mpr
      linarith
    exact ⟨hj.1, hj.2.1.trans hraise, hju⟩
  have herror := hcrit.2.2.2.2.2
  refine ⟨c, hc, hcrit.1, nSeq, hmono, hnewwindow, herror, ?_⟩
  have herrorLower := herror.eventually
    (eventually_gt_nhds (show criticalGap c / 2 < criticalGap c by linarith [hcrit.1]))
  filter_upwards [hnewwindow, herrorLower] with j hj he
  have hs := rademacher_strict_windowError_spec.{uX} B P hB a (nSeq j)
    (by omega) (hj.2.1.trans hj.2.2)
  exact he.le.trans (hs.2.2.2.2 (criticalPoint c (nSeq j)) hj.2)

-- B07: one fixed Rademacher law; not a necessity claim for each law.
theorem rademacher_strict_window_necessity
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a : ℕ → ℝ)
    (hwin : Tendsto (StrictIIDWindow.sourceStrictWindowError B P hB
      (CriticalWindowNecessity.rademacherIIDLaw.{uX})
      (CriticalWindowNecessity.rademacherIIDCoordinate.{uX}) a)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n => a n * (n : ℝ) ^ ((1 : ℝ) / 6)) atTop atTop := by
  by_contra hbad
  obtain ⟨c, hc, hgap, nSeq, hmono, _, _, hlower⟩ :=
    rademacher_strict_window_obstruction.{uX} B P hB a hbad
  have hsub := hwin.comp hmono.tendsto_atTop
  have hupper := hsub.eventually
    (eventually_lt_nhds (show (0 : ℝ) < criticalGap c / 2 by linarith))
  obtain ⟨j, hjlo, hjup⟩ := (hlower.and hupper).exists
  exact (not_lt_of_ge hjlo) hjup

-- B08: universal fixed-family criterion at any prescribed sample universe.
theorem universal_fixed_iid_strict_window_iff
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a : ℕ → ℝ) (haAnti : Antitone a)
    (ha : Tendsto a atTop (𝓝 (0 : ℝ))) :
    (∀ (ΩX : Type uX) [MeasurableSpace ΩX]
      (μ : Measure ΩX) [IsProbabilityMeasure μ]
      (X : ℕ → ΩX → ℝ)
      (hX : ∀ i : ℕ, AEMeasurable (X (i + 1)) μ)
      (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
      (hIdent : ∀ i : ℕ, IdentDistrib (X (i + 1)) (X 1) μ μ)
      (h3 : Integrable (fun ω => |X 1 ω| ^ 3) μ)
      (hmean : (∫ ω, X 1 ω ∂μ) = 0)
      (hsecond : 0 < ∫ ω, (X 1 ω) ^ 2 ∂μ),
      Tendsto (fun n : ℕ => sSup ((fun x : ℝ =>
        |μ.real {ω | OriginalIIDWindow.sourceMaximum n X ω <
          x * Real.sqrt (OriginalIIDWindow.sourceEnergy n X ω)} /
          Shao.Probability.BrownianSup.probability B P hB x - 1|) '' Ioo (a n) 1))
        atTop (𝓝 (0 : ℝ))) ↔
      Tendsto (fun n => a n * (n : ℝ) ^ ((1 : ℝ) / 6)) atTop atTop := by
  constructor
  · intro hall
    rcases CriticalWindowNecessity.rademacherIID_facts.{uX} with
      ⟨hμ, hX, hind, hident, _, h3, hmean, hsecond⟩
    letI : IsProbabilityMeasure (CriticalWindowNecessity.rademacherIIDLaw.{uX}) := hμ
    have hsecondpos : 0 < ∫ ω,
        (CriticalWindowNecessity.rademacherIIDCoordinate.{uX} 1 ω) ^ 2
        ∂(CriticalWindowNecessity.rademacherIIDLaw.{uX}) := by
      rw [hsecond]
      norm_num
    have hgiven := hall (ULift.{uX} (ℕ → ℝ))
      (CriticalWindowNecessity.rademacherIIDLaw.{uX})
      (CriticalWindowNecessity.rademacherIIDCoordinate.{uX})
      (fun i => (hX i).aemeasurable) hind hident h3 hmean hsecondpos
    apply rademacher_strict_window_necessity.{uX} B P hB a
    apply hgiven.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    simp only [StrictIIDWindow.sourceStrictWindowError,
      StrictIIDWindow.source_strict_event_eq_max n (by omega : 0 < n)]
  · intro hslow ΩX _ μ _ X hX hind hident h3 hmean hsecond
    exact StrictIIDWindow.original_iid_strict_sSup_tendsto B P hB μ X hX
      hind hident h3 hmean hsecond a haAnti ha hslow

end Shao.OQ4.StrictWindowNecessity
end
