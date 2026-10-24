/-
Complete LOCAL implementation of the parent-frozen 25-declaration proposal.
Freeze SHA256 ae51f9b011c62b2404c4b37eb0dacc4ecb2aedc0adc7c0637658302764c417c8.
No Lean/parser/server/test run by author187; pending input qualification remains pending.
All original root groups remain OPEN.
-/
import Shao.OQ4.OriginalIIDWindow
import Shao.OQ4.BrownianPositiveCDF
import Shao.OQ4.RademacherS5Assembly
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

noncomputable section
universe u v
namespace Shao.OQ4.CriticalWindowNecessity
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal BigOperators Topology
set_option autoImplicit false
variable {ΩB : Type v} [MeasurableSpace ΩB]

-- D01 PUBLIC full value. The law is never rounded; only the real boundary is.
def criticalCell (c : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil (c * (n : ℝ) ^ ((1 : ℝ) / 3))

-- D02 PUBLIC full value. Integer weak wall, with absorbing site m+1.
def criticalHeight (c : ℝ) (n : ℕ) : ℝ := (criticalCell c n : ℝ)

-- D03 PUBLIC full value. Literal x=h/sqrt(n), with existing total division at0.
def criticalPoint (c : ℝ) (n : ℕ) : ℝ :=
  criticalHeight c n / Real.sqrt (n : ℝ)

-- D04 PUBLIC full value. Positive for c>0, derived rather than postulated.
def criticalGap (c : ℝ) : ℝ := Real.exp (Real.pi ^ 2 / (4 * c ^ 3)) - 1

-- T05 PRIVATE head. Exact identities on the positive-time branch.
private theorem critical_power_identities (c : ℝ) (hc : 0 < c)
    (n : ℕ) (hn : 0 < n) :
    ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (n : ℝ) ∧
    Real.sqrt (n : ℝ) =
      (n : ℝ) ^ ((1 : ℝ) / 3) * (n : ℝ) ^ ((1 : ℝ) / 6) ∧
    criticalPoint c n * (n : ℝ) ^ ((1 : ℝ) / 6) =
      criticalHeight c n / (n : ℝ) ^ ((1 : ℝ) / 3) ∧
    (n : ℝ) / criticalHeight c n ^ 2 =
      (n : ℝ) ^ ((1 : ℝ) / 3) /
        (criticalHeight c n / (n : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 ∧
    (n : ℝ) / criticalHeight c n ^ 3 =
      1 / (criticalHeight c n / (n : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := by
  have hN : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hr : 0 < (n : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hN _
  have hq : 0 < (n : ℝ) ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hN _
  have hh : 0 < criticalHeight c n :=
    (mul_pos hc hr).trans_le (Nat.le_ceil _)
  have hr3 : ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (n : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    norm_num
  have hs : Real.sqrt (n : ℝ) =
      (n : ℝ) ^ ((1 : ℝ) / 3) * (n : ℝ) ^ ((1 : ℝ) / 6) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN]
    norm_num
  refine ⟨hr3, hs, ?_, ?_, ?_⟩
  · unfold criticalPoint
    rw [hs]
    field_simp [hr.ne', hq.ne'] <;> ring
  · calc
      (n : ℝ) / criticalHeight c n ^ 2 =
          ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 / criticalHeight c n ^ 2 :=
        congrArg (fun z : ℝ => z / criticalHeight c n ^ 2) hr3.symm
      _ = _ := by field_simp [hr.ne', hh.ne'] <;> ring
  · calc
      (n : ℝ) / criticalHeight c n ^ 3 =
          ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 / criticalHeight c n ^ 3 :=
        congrArg (fun z : ℝ => z / criticalHeight c n ^ 3) hr3.symm
      _ = _ := by field_simp [hr.ne', hh.ne'] <;> ring


-- T06 PRIVATE head. Every analytic input to the old S4 is a conclusion here.
private theorem rounded_scales (c : ℝ) (hc : 0 < c)
    (nSeq : ℕ → ℕ) (hn : Tendsto nSeq atTop atTop) :
    (∀ n : ℕ, 0 ≤ criticalHeight c n - c * (n : ℝ) ^ ((1 : ℝ) / 3) ∧
      criticalHeight c n - c * (n : ℝ) ^ ((1 : ℝ) / 3) < 1) ∧
    Tendsto (fun j => criticalHeight c (nSeq j) /
      (nSeq j : ℝ) ^ ((1 : ℝ) / 3)) atTop (𝓝 c) ∧
    Tendsto (fun j => criticalHeight c (nSeq j)) atTop atTop ∧
    Tendsto (fun j => (nSeq j : ℝ) / criticalHeight c (nSeq j) ^ 2)
      atTop atTop ∧
    Tendsto (fun j => (nSeq j : ℝ) / criticalHeight c (nSeq j) ^ 3)
      atTop (𝓝 (1 / c ^ 3)) ∧
    Tendsto (fun j => criticalPoint c (nSeq j)) atTop (𝓝 (0 : ℝ)) ∧
    Tendsto (fun j => criticalPoint c (nSeq j) *
      (nSeq j : ℝ) ^ ((1 : ℝ) / 6)) atTop (𝓝 c) ∧
    (∀ᶠ j in atTop,
      1 ≤ nSeq j ∧ 1 ≤ criticalCell c (nSeq j) ∧
      0 < criticalHeight c (nSeq j) ∧ 0 < criticalPoint c (nSeq j) ∧
      criticalPoint c (nSeq j) * Real.sqrt (nSeq j : ℝ) =
        criticalHeight c (nSeq j) ∧
      RademacherS4Assembly.delta (criticalCell c (nSeq j))
        (criticalHeight c (nSeq j)) = 1) := by
  have hround : ∀ n : ℕ,
      0 ≤ criticalHeight c n - c * (n : ℝ) ^ ((1 : ℝ) / 3) ∧
      criticalHeight c n - c * (n : ℝ) ^ ((1 : ℝ) / 3) < 1 := by
    intro n
    have hnonneg : 0 ≤ c * (n : ℝ) ^ ((1 : ℝ) / 3) :=
      mul_nonneg hc.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hlo := Nat.le_ceil (c * (n : ℝ) ^ ((1 : ℝ) / 3))
    have hup := Nat.ceil_lt_add_one hnonneg
    change 0 ≤ (Nat.ceil (c * (n : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) -
        c * (n : ℝ) ^ ((1 : ℝ) / 3) ∧
      (Nat.ceil (c * (n : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) -
        c * (n : ℝ) ^ ((1 : ℝ) / 3) < 1
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
    exact (mul_pos hc hj).trans_le (Nat.le_ceil _)
  have hid : ∀ᶠ j in atTop,
      ((nSeq j : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (nSeq j : ℝ) ∧
      Real.sqrt (nSeq j : ℝ) = r j * q j ∧
      criticalPoint c (nSeq j) * q j = criticalHeight c (nSeq j) / r j ∧
      (nSeq j : ℝ) / criticalHeight c (nSeq j) ^ 2 =
        r j / (criticalHeight c (nSeq j) / r j) ^ 2 ∧
      (nSeq j : ℝ) / criticalHeight c (nSeq j) ^ 3 =
        1 / (criticalHeight c (nSeq j) / r j) ^ 3 := by
    filter_upwards [hnt] with j hj
    exact critical_power_identities c hc (nSeq j) hj
  have hinv : Tendsto (fun j => 1 / r j) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hr
  have herr : Tendsto
      (fun j => (criticalHeight c (nSeq j) - c * r j) / r j)
      atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero'
      (Eventually.of_forall fun j => div_nonneg (hround (nSeq j)).1 (hr0 j))
      (Eventually.of_forall fun j =>
        div_le_div_of_nonneg_right (hround (nSeq j)).2.le (hr0 j)) hinv
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
    exact hb.trans (Nat.le_ceil _)
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
  refine ⟨hround, hratio, hh, hscale2, hscale3, hx, hxscale, ?_⟩
  filter_upwards [hnt, hhpos] with j hnj hhj
  have hnjR : 0 < (nSeq j : ℝ) := Nat.cast_pos.mpr hnj
  have hs : 0 < Real.sqrt (nSeq j : ℝ) := Real.sqrt_pos.mpr hnjR
  have hm : 1 ≤ criticalCell c (nSeq j) := by
    have hmpos : 0 < criticalCell c (nSeq j) := Nat.cast_pos.mp hhj
    omega
  refine ⟨by omega, hm, hhj, div_pos hhj hs, ?_, ?_⟩
  · exact div_mul_cancel₀ _ hs.ne'
  · exact RademacherLatticeShift.delta_at_left (criticalCell c (nSeq j))


-- T07 PUBLIC head. Derived from the actual two half-weighted atoms.
theorem rademacher_moments :
    Integrable (fun z : ℝ => |z| ^ 3) RademacherCosine.law ∧
    (∫ z : ℝ, z ∂RademacherCosine.law) = 0 ∧
    (∫ z : ℝ, z ^ 2 ∂RademacherCosine.law) = 1 ∧
    (∫ z : ℝ, |z| ^ 3 ∂RademacherCosine.law) = 1 := by
  have hhalf : RademacherCosine.halfENNReal ≠ ⊤ := by
    norm_num [RademacherCosine.halfENNReal]
  have hreal : RademacherCosine.halfENNReal.toReal = (1 / 2 : ℝ) := by
    norm_num [RademacherCosine.halfENNReal, ENNReal.toReal_div]
  have hp (f : ℝ → ℝ) :
      Integrable f (RademacherCosine.halfENNReal • Measure.dirac (1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure hhalf
  have hn (f : ℝ → ℝ) :
      Integrable f (RademacherCosine.halfENNReal • Measure.dirac (-1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure hhalf
  have hi (f : ℝ → ℝ) : Integrable f RademacherCosine.law := by
    rw [RademacherCosine.law]
    exact (hp f).add_measure (hn f)
  have hformula (f : ℝ → ℝ) :
      (∫ z : ℝ, f z ∂RademacherCosine.law) =
        (1 / 2 : ℝ) * f 1 + (1 / 2 : ℝ) * f (-1) := by
    rw [RademacherCosine.law, integral_add_measure (hp f) (hn f),
      integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac, hreal]
    rfl
  refine ⟨hi _, ?_, ?_, ?_⟩ <;> norm_num [hformula]


-- T08 PRIVATE head. Does not consume OriginalWindowProduct's private helper.
private theorem rademacher_probability_bounds (n : ℕ) (x : ℝ) :
    0 ≤ OriginalWindowProduct.productProbability RademacherCosine.law n x ∧
    OriginalWindowProduct.productProbability RademacherCosine.law n x ≤ 1 := by
  refine ⟨measureReal_nonneg, ?_⟩
  have h := measureReal_mono
    (μ := Measure.pi (fun _ : Fin n => RademacherCosine.law))
    (Set.subset_univ (RandomDenominatorFarTail.randomDenominatorEvent n
      (x * Real.sqrt (n : ℝ))))
  simpa only [OriginalWindowProduct.productProbability, Measure.real,
    measure_univ, ENNReal.toReal_one] using h


-- T09 PRIVATE head. All x, including nonpositive x; n=0 is not asserted here.
private theorem rademacher_event_bridge (n : ℕ) (hn : 0 < n) (x : ℝ) :
    (∀ᵐ w ∂(Measure.pi (fun _ : Fin n => RademacherCosine.law)),
      (w ∈ RandomDenominatorFarTail.randomDenominatorEvent n
        (x * Real.sqrt (n : ℝ)) ↔
      w ∈ @Shao.closedStrip n (x * Real.sqrt (n : ℝ)))) ∧
    OriginalWindowProduct.productProbability RademacherCosine.law n x =
      RademacherS2Assembly.p n (x * Real.sqrt (n : ℝ)) := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hcancel : (x * Real.sqrt (n : ℝ)) / Real.sqrt (n : ℝ) = x := by
    field_simp [hs.ne']
  have hae : ∀ᵐ w ∂(Measure.pi (fun _ : Fin n => RademacherCosine.law)),
      (w ∈ RandomDenominatorFarTail.randomDenominatorEvent n
        (x * Real.sqrt (n : ℝ)) ↔
      w ∈ @Shao.closedStrip n (x * Real.sqrt (n : ℝ))) := by
    filter_upwards [(RademacherS5Assembly.actual_path_energy n).2] with w hw
    have henergy : Shao.energy w = (n : ℝ) := hw.2.1
    change (w ∈ @Shao.closedStrip n
      ((x * Real.sqrt (n : ℝ)) / Real.sqrt (n : ℝ) * Real.sqrt (Shao.energy w))) ↔ _
    rw [hcancel, henergy]
  refine ⟨hae, ?_⟩
  have hsets : RandomDenominatorFarTail.randomDenominatorEvent n
      (x * Real.sqrt (n : ℝ)) =ᵐ[Measure.pi (fun _ : Fin n => RademacherCosine.law)]
      @Shao.closedStrip n (x * Real.sqrt (n : ℝ)) :=
    hae.mono fun _ hw => propext hw
  change ((Measure.pi (fun _ : Fin n => RademacherCosine.law))
      (RandomDenominatorFarTail.randomDenominatorEvent n (x * Real.sqrt (n : ℝ)))).toReal =
    ((Measure.pi (fun _ : Fin n => RademacherCosine.law))
      (@Shao.closedStrip n (x * Real.sqrt (n : ℝ)))).toReal
  exact congrArg ENNReal.toReal (measure_congr hsets)


-- T10 PUBLIC head. First-step obstruction also pays x<=0 without a CDF premise.
theorem rademacher_zero_below_first_step
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (n : ℕ) (hn : 0 < n)
    (x : ℝ) (hx : x < 1 / Real.sqrt (n : ℝ)) :
    OriginalWindowProduct.productProbability RademacherCosine.law n x = 0 ∧
    OriginalWindowProduct.relativeError B P hB RademacherCosine.law n x = 1 := by
  classical
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hwall : x * Real.sqrt (n : ℝ) < 1 := (lt_div_iff₀ hs).mp hx
  have hfirst (w : Shao.Path n) : Shao.prefixSum w 1 = w ⟨0, hn⟩ := by
    have hset : (Finset.univ.filter (fun i : Fin n => i.val < 1)) = {⟨0, hn⟩} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hi
        apply Fin.ext
        change i.val = 0
        omega
      · rintro rfl
        norm_num
    simp only [Shao.prefixSum, hset, Finset.sum_singleton]
  have hnull : (Measure.pi (fun _ : Fin n => RademacherCosine.law))
      (@Shao.closedStrip n (x * Real.sqrt (n : ℝ))) = 0 := by
    have hae : ∀ᵐ w ∂(Measure.pi (fun _ : Fin n => RademacherCosine.law)),
        w ∉ @Shao.closedStrip n (x * Real.sqrt (n : ℝ)) := by
      filter_upwards [(RademacherS5Assembly.actual_path_energy n).2] with w hw
      have habs : |Shao.prefixSum w 1| = 1 := by
        rw [hfirst w]
        rcases hw.1 ⟨0, hn⟩ with h | h <;> simp [h]
      intro hmem
      have hle := hmem 1 (show 1 ≤ n by omega)
      rw [habs] at hle
      exact (not_lt_of_ge hle) hwall
    simpa only [ae_iff, not_not, Set.setOf_mem_eq] using hae
  have hp : OriginalWindowProduct.productProbability RademacherCosine.law n x = 0 := by
    rw [(rademacher_event_bridge n hn x).2]
    change ((Measure.pi (fun _ : Fin n => RademacherCosine.law))
      (@Shao.closedStrip n (x * Real.sqrt (n : ℝ)))).toReal = 0
    rw [hnull, ENNReal.toReal_zero]
  refine ⟨hp, ?_⟩
  simp only [OriginalWindowProduct.relativeError, hp, zero_div, zero_sub, abs_neg,
    abs_one]


-- T11 PRIVATE head. A finite bound for every real x, independent of a_n's sign.
private theorem rademacher_error_bound
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (n : ℕ) (hn : 0 < n) (x : ℝ) :
    OriginalWindowProduct.relativeError B P hB RademacherCosine.law n x ≤
      1 + 1 / Shao.Probability.BrownianSup.probability B P hB
        (1 / Real.sqrt (n : ℝ)) := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hd : 0 < 1 / Real.sqrt (n : ℝ) := one_div_pos.mpr hs
  have hFd := BrownianPositiveCDF.probability_pos B P hB
    (1 / Real.sqrt (n : ℝ)) hd
  by_cases hx : x < 1 / Real.sqrt (n : ℝ)
  · rw [(rademacher_zero_below_first_step B P hB n hn x hx).2]
    have hi : 0 ≤ 1 / Shao.Probability.BrownianSup.probability B P hB
        (1 / Real.sqrt (n : ℝ)) := one_div_nonneg.mpr hFd.le
    linarith
  · have hdx : 1 / Real.sqrt (n : ℝ) ≤ x := le_of_not_gt hx
    have hmono := BrownianPositiveCDF.probability_mono B P hB hdx
    have hFx : 0 < Shao.Probability.BrownianSup.probability B P hB x :=
      hFd.trans_le hmono
    have hp := rademacher_probability_bounds n x
    have hr : 0 ≤ OriginalWindowProduct.productProbability RademacherCosine.law n x /
        Shao.Probability.BrownianSup.probability B P hB x := div_nonneg hp.1 hFx.le
    have hrb : OriginalWindowProduct.productProbability RademacherCosine.law n x /
        Shao.Probability.BrownianSup.probability B P hB x ≤
        1 / Shao.Probability.BrownianSup.probability B P hB
          (1 / Real.sqrt (n : ℝ)) :=
      (div_le_div_of_nonneg_right hp.2 hFx.le).trans
        (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hFd hmono)
    unfold OriginalWindowProduct.relativeError
    calc
      _ ≤ |OriginalWindowProduct.productProbability RademacherCosine.law n x /
          Shao.Probability.BrownianSup.probability B P hB x| + |(1 : ℝ)| :=
        by simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (OriginalWindowProduct.productProbability RademacherCosine.law n x /
            Shao.Probability.BrownianSup.probability B P hB x) (0 : ℝ) 1)
      _ = OriginalWindowProduct.productProbability RademacherCosine.law n x /
          Shao.Probability.BrownianSup.probability B P hB x + 1 := by
        rw [abs_of_nonneg hr, abs_one]
      _ ≤ _ := by linarith


-- T12 PUBLIC head. Genuine finite real sSup for ANY lower endpoint below1.
theorem rademacher_windowError_spec
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a : ℕ → ℝ) (n : ℕ)
    (hn : 0 < n) (ha : a n < 1) :
    (OriginalWindowProduct.windowValues B P hB RademacherCosine.law a n).Nonempty ∧
    BddAbove (OriginalWindowProduct.windowValues B P hB RademacherCosine.law a n) ∧
    IsLUB (OriginalWindowProduct.windowValues B P hB RademacherCosine.law a n)
      (OriginalWindowProduct.windowError B P hB RademacherCosine.law a n) ∧
    0 ≤ OriginalWindowProduct.windowError B P hB RademacherCosine.law a n ∧
    OriginalWindowProduct.windowError B P hB RademacherCosine.law a n ≤
      1 + 1 / Shao.Probability.BrownianSup.probability B P hB
        (1 / Real.sqrt (n : ℝ)) ∧
    (∀ x ∈ Ioo (a n) 1,
      OriginalWindowProduct.relativeError B P hB RademacherCosine.law n x ≤
        OriginalWindowProduct.windowError B P hB RademacherCosine.law a n) := by
  have hmid : (a n + 1) / 2 ∈ Ioo (a n) 1 := ⟨by linarith, by linarith⟩
  have hmem : OriginalWindowProduct.relativeError B P hB RademacherCosine.law n
      ((a n + 1) / 2) ∈
      OriginalWindowProduct.windowValues B P hB RademacherCosine.law a n :=
    ⟨(a n + 1) / 2, hmid, rfl⟩
  have hne : (OriginalWindowProduct.windowValues B P hB RademacherCosine.law a n).Nonempty :=
    ⟨_, hmem⟩
  have hbound : ∀ y ∈ OriginalWindowProduct.windowValues B P hB RademacherCosine.law a n,
      y ≤ 1 + 1 / Shao.Probability.BrownianSup.probability B P hB
        (1 / Real.sqrt (n : ℝ)) := by
    rintro y ⟨x, hx, rfl⟩
    exact rademacher_error_bound B P hB n hn x
  have hb : BddAbove (OriginalWindowProduct.windowValues B P hB RademacherCosine.law a n) :=
    ⟨_, hbound⟩
  have hlub : IsLUB (OriginalWindowProduct.windowValues B P hB RademacherCosine.law a n)
      (OriginalWindowProduct.windowError B P hB RademacherCosine.law a n) :=
    isLUB_csSup hne hb
  refine ⟨hne, hb, hlub, (abs_nonneg _).trans (hlub.1 hmem), csSup_le hne hbound, ?_⟩
  intro x hx
  exact hlub.1 ⟨x, hx, rfl⟩


-- T13 PUBLIC head. Actual probability quotient, not a log quotient or rate.
theorem critical_ratio_tendsto
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (c : ℝ) (hc : 0 < c)
    (nSeq : ℕ → ℕ) (hn : Tendsto nSeq atTop atTop) :
    0 < criticalGap c ∧
    Tendsto (fun j =>
      OriginalWindowProduct.productProbability RademacherCosine.law (nSeq j)
        (criticalPoint c (nSeq j)) /
      Shao.Probability.BrownianSup.probability B P hB (criticalPoint c (nSeq j)))
      atTop (𝓝 (Real.exp (Real.pi ^ 2 / (4 * c ^ 3)))) ∧
    Tendsto (fun j => OriginalWindowProduct.relativeError B P hB
      RademacherCosine.law (nSeq j) (criticalPoint c (nSeq j)))
      atTop (𝓝 (criticalGap c)) := by
  rcases rounded_scales c hc nSeq hn with
    ⟨_, _, hh, hscale2, hscale3, _, _, hlegal⟩
  have hcell : ∃ K_cell : ℕ, ∀ j : ℕ, K_cell ≤ j →
      1 ≤ criticalCell c (nSeq j) ∧
      (criticalCell c (nSeq j) : ℝ) ≤ criticalHeight c (nSeq j) ∧
      criticalHeight c (nSeq j) < (criticalCell c (nSeq j) : ℝ) + 1 := by
    apply eventually_atTop.mp
    filter_upwards [hlegal] with j hj
    exact ⟨hj.2.1, le_rfl, lt_add_one _⟩
  have hbounded : ∃ M : ℝ, 0 < M ∧
      ∃ K_M : ℕ, ∀ j : ℕ, K_M ≤ j →
        RademacherS4Assembly.scale3 (nSeq j) (criticalHeight c (nSeq j)) ≤ M := by
    refine ⟨1 / c ^ 3 + 1, by positivity, ?_⟩
    have he := hscale3.eventually
      (eventually_lt_nhds (lt_add_one (1 / c ^ 3)))
    obtain ⟨K, hK⟩ := eventually_atTop.mp he
    exact ⟨K, fun j hj => (hK j hj).le⟩
  have hs4 := RademacherS4Assembly.S4_EVENTUAL B P hB
    (fun j => criticalCell c (nSeq j)) nSeq
    (fun j => criticalHeight c (nSeq j)) hcell hh hscale2 hbounded
  rcases hs4 with
    ⟨_, _, _, _, _, _, _, hlogerr, _, K_time, K_pos, _, _, hpositive, _⟩
  have hQpos : ∀ᶠ j in atTop,
      0 < RademacherS4Assembly.Q B P hB (nSeq j) (criticalHeight c (nSeq j)) := by
    filter_upwards [eventually_ge_atTop K_pos] with j hj
    rcases (hpositive j hj).1 with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hpos, _⟩
    exact hpos
  have hw0 : Tendsto
      (fun j => (Real.pi ^ 2 / 4) * ((nSeq j : ℝ) / criticalHeight c (nSeq j) ^ 3))
      atTop (𝓝 ((Real.pi ^ 2 / 4) * (1 / c ^ 3))) :=
    hscale3.const_mul (Real.pi ^ 2 / 4)
  have hw : Tendsto
      (fun j => RademacherS4Assembly.w (criticalCell c (nSeq j))
        (nSeq j) (criticalHeight c (nSeq j)))
      atTop (𝓝 (Real.pi ^ 2 / (4 * c ^ 3))) := by
    have halg : (Real.pi ^ 2 / 4) * (1 / c ^ 3) =
        Real.pi ^ 2 / (4 * c ^ 3) := by ring
    rw [← halg]
    apply hw0.congr'
    filter_upwards [hlegal] with j hj
    change (Real.pi ^ 2 / 4) * ((nSeq j : ℝ) / criticalHeight c (nSeq j) ^ 3) =
      (Real.pi ^ 2 / 4) * ((nSeq j : ℝ) / criticalHeight c (nSeq j) ^ 3) *
        RademacherS4Assembly.delta (criticalCell c (nSeq j)) (criticalHeight c (nSeq j))
    rw [hj.2.2.2.2.2, mul_one]
  have hlog : Tendsto
      (fun j => Real.log (RademacherS4Assembly.Q B P hB (nSeq j)
        (criticalHeight c (nSeq j))))
      atTop (𝓝 (Real.pi ^ 2 / (4 * c ^ 3))) := by
    simpa only [sub_add_cancel, zero_add] using hlogerr.add hw
  have hexp : Tendsto
      (fun j => Real.exp (Real.log (RademacherS4Assembly.Q B P hB (nSeq j)
        (criticalHeight c (nSeq j)))))
      atTop (𝓝 (Real.exp (Real.pi ^ 2 / (4 * c ^ 3)))) :=
    Real.continuous_exp.continuousAt.tendsto.comp hlog
  have hQ : Tendsto
      (fun j => RademacherS4Assembly.Q B P hB (nSeq j) (criticalHeight c (nSeq j)))
      atTop (𝓝 (Real.exp (Real.pi ^ 2 / (4 * c ^ 3)))) :=
    hexp.congr' (hQpos.mono fun _ hj => Real.exp_log hj)
  have hprodEq : ∀ᶠ j in atTop,
      RademacherS4Assembly.Q B P hB (nSeq j) (criticalHeight c (nSeq j)) =
        OriginalWindowProduct.productProbability RademacherCosine.law (nSeq j)
          (criticalPoint c (nSeq j)) /
        Shao.Probability.BrownianSup.probability B P hB (criticalPoint c (nSeq j)) := by
    filter_upwards [hlegal] with j hj
    have hp := (rademacher_event_bridge (nSeq j) (by have := hj.1; omega : 0 < nSeq j)
      (criticalPoint c (nSeq j))).2
    rw [hj.2.2.2.2.1] at hp
    change RademacherS2Assembly.p (nSeq j) (criticalHeight c (nSeq j)) /
        Shao.Probability.BrownianSup.probability B P hB (criticalPoint c (nSeq j)) = _
    rw [hp]
  have hprod := hQ.congr' hprodEq
  have hk : 0 < Real.pi ^ 2 / (4 * c ^ 3) := by positivity
  have hexpgt : 1 < Real.exp (Real.pi ^ 2 / (4 * c ^ 3)) := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hk
  have hgap : 0 < criticalGap c := sub_pos.mpr hexpgt
  refine ⟨hgap, hprod, ?_⟩
  have hsub : Tendsto
      (fun j => OriginalWindowProduct.productProbability RademacherCosine.law (nSeq j)
        (criticalPoint c (nSeq j)) /
        Shao.Probability.BrownianSup.probability B P hB (criticalPoint c (nSeq j)) - 1)
      atTop (𝓝 (Real.exp (Real.pi ^ 2 / (4 * c ^ 3)) - 1)) :=
    hprod.sub tendsto_const_nhds
  have he := hsub.abs
  simpa only [OriginalWindowProduct.relativeError, criticalGap,
    abs_of_pos (sub_pos.mpr hexpgt)] using he


-- T14 PRIVATE head. Strictly increasing positive indices; no positivity of a.
private theorem bad_scale_subsequence (a : ℕ → ℝ)
    (hbad : ¬ Tendsto (fun n => a n * (n : ℝ) ^ ((1 : ℝ) / 6)) atTop atTop) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ nSeq : ℕ → ℕ,
      StrictMono nSeq ∧ (∀ j, 1 ≤ nSeq j) ∧
      (∀ j, a (nSeq j) * (nSeq j : ℝ) ^ ((1 : ℝ) / 6) ≤ C) := by
  classical
  have hfre : ∃ D : ℝ,
      ∃ᶠ n in atTop, a n * (n : ℝ) ^ ((1 : ℝ) / 6) ≤ D := by
    by_contra hnone
    apply hbad
    apply tendsto_atTop.mpr
    intro b
    have hnot : ¬ ∃ᶠ n in atTop,
        a n * (n : ℝ) ^ ((1 : ℝ) / 6) ≤ b :=
      fun hb => hnone ⟨b, hb⟩
    have he : ∀ᶠ n in atTop, ¬ a n * (n : ℝ) ^ ((1 : ℝ) / 6) ≤ b := by
      simpa only [Filter.Frequently, not_not] using hnot
    exact he.mono fun _ h => (lt_of_not_ge h).le
  obtain ⟨D, hD⟩ := hfre
  have hb : ∃ᶠ n in atTop,
      a n * (n : ℝ) ^ ((1 : ℝ) / 6) ≤ max D 0 ∧ 1 ≤ n :=
    (hD.mono fun _ h => h.trans (le_max_left D 0)).and_eventually
      (eventually_ge_atTop 1)
  have htail : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      (a n * (n : ℝ) ^ ((1 : ℝ) / 6) ≤ max D 0 ∧ 1 ≤ n) :=
    frequently_atTop.mp hb
  choose pick hpick using htail
  let nSeq : ℕ → ℕ := Nat.rec (pick 1) (fun _ prev => pick (prev + 1))
  have hstep (j : ℕ) : nSeq j < nSeq (j + 1) := by
    have hge := (hpick (nSeq j + 1)).1
    change nSeq j < pick (nSeq j + 1)
    omega
  have hmono : StrictMono nSeq := strictMono_nat_of_lt_succ hstep
  have hseq : ∀ j, 1 ≤ nSeq j ∧
      a (nSeq j) * (Nat.cast (nSeq j) : ℝ) ^ ((1 : ℝ) / 6) ≤ max D 0 := by
    intro j
    cases j with
    | zero => exact ⟨(hpick 1).2.2, (hpick 1).2.1⟩
    | succ j => exact ⟨(hpick (nSeq j + 1)).2.2, (hpick (nSeq j + 1)).2.1⟩
  exact ⟨max D 0, le_max_right D 0, nSeq, hmono,
    fun j => (hseq j).1, fun j => (hseq j).2⟩


-- T15 PRIVATE head. Exact original open interval; no rounded x substitution.
private theorem critical_inside_window (a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (nSeq : ℕ → ℕ) (hn : Tendsto nSeq atTop atTop)
    (hbound : ∀ j, a (nSeq j) * (nSeq j : ℝ) ^ ((1 : ℝ) / 6) ≤ C) :
    ∀ᶠ j in atTop, criticalPoint (C + 1) (nSeq j) ∈ Ioo (a (nSeq j)) 1 := by
  have hc : 0 < C + 1 := by linarith
  rcases rounded_scales (C + 1) hc nSeq hn with
    ⟨_, _, _, _, _, hx, hxscale, _⟩
  have hlarge := hxscale.eventually
    (eventually_gt_nhds (show C < C + 1 by linarith))
  have hsmall := hx.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hlarge, hsmall, hn.eventually_ge_atTop 1] with j hj hj1 hnj
  refine ⟨?_, hj1⟩
  have hq : 0 ≤ (nSeq j : ℝ) ^ ((1 : ℝ) / 6) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  by_contra hnot
  have hxa : criticalPoint (C + 1) (nSeq j) ≤ a (nSeq j) := le_of_not_gt hnot
  have hm := mul_le_mul_of_nonneg_right hxa hq
  exact (not_lt_of_ge (hm.trans (hbound j))) hj


-- T16 PUBLIC head. One fixed law; includes the actual proper-sSup lower bound.
-- This stronger necessity statement does not require Antitone a or a->0.
theorem rademacher_window_obstruction
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a : ℕ → ℝ)
    (hbad : ¬ Tendsto (fun n => a n * (n : ℝ) ^ ((1 : ℝ) / 6)) atTop atTop) :
    ∃ c : ℝ, 0 < c ∧ 0 < criticalGap c ∧ ∃ nSeq : ℕ → ℕ,
      StrictMono nSeq ∧
      (∀ᶠ j in atTop,
        1 ≤ nSeq j ∧ criticalPoint c (nSeq j) ∈ Ioo (a (nSeq j)) 1) ∧
      Tendsto (fun j => OriginalWindowProduct.relativeError B P hB
        RademacherCosine.law (nSeq j) (criticalPoint c (nSeq j)))
        atTop (𝓝 (criticalGap c)) ∧
      (∀ᶠ j in atTop, criticalGap c / 2 ≤
        OriginalWindowProduct.windowError B P hB RademacherCosine.law a (nSeq j)) := by
  obtain ⟨C, hC, nSeq, hmono, hnpos, hbound⟩ := bad_scale_subsequence a hbad
  have hc : 0 < C + 1 := by linarith
  have hcrit := critical_ratio_tendsto B P hB (C + 1) hc nSeq hmono.tendsto_atTop
  have hwindow := critical_inside_window a C hC nSeq hmono.tendsto_atTop hbound
  refine ⟨C + 1, hc, hcrit.1, nSeq, hmono, ?_, hcrit.2.2, ?_⟩
  · exact hwindow.mono fun j hj => ⟨hnpos j, hj⟩
  · have herror := hcrit.2.2.eventually
      (eventually_gt_nhds (show criticalGap (C + 1) / 2 < criticalGap (C + 1)
        by linarith [hcrit.1]))
    filter_upwards [hwindow, herror] with j hj he
    have hs := rademacher_windowError_spec B P hB a (nSeq j)
      (by have := hnpos j; omega) (hj.1.trans hj.2)
    exact he.le.trans (hs.2.2.2.2.2 (criticalPoint (C + 1) (nSeq j)) hj)


-- T17 PUBLIC head. Necessity for the same fixed law at every n.
theorem rademacher_window_necessity
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a : ℕ → ℝ)
    (hwin : Tendsto (OriginalWindowProduct.windowError B P hB
      RademacherCosine.law a) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n => a n * (n : ℝ) ^ ((1 : ℝ) / 6)) atTop atTop := by
  by_contra hbad
  obtain ⟨c, hc, hgap, nSeq, hmono, _, _, hlower⟩ :=
    rademacher_window_obstruction B P hB a hbad
  have hsub := hwin.comp hmono.tendsto_atTop
  have hupper := hsub.eventually
    (eventually_lt_nhds (show (0 : ℝ) < criticalGap c / 2 by linarith))
  obtain ⟨j, hjlo, hjup⟩ := (hlower.and hupper).exists
  exact (not_lt_of_ge hjlo) hjup


-- D18 PUBLIC full value. Each law is fixed outside the n-limit; no sup over laws.
def universalFixedLawWindow
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a : ℕ → ℝ) : Prop :=
  ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
    Integrable (fun z : ℝ => |z| ^ 3) ν →
    (∫ z : ℝ, z ∂ν) = 0 → (∫ z : ℝ, z ^ 2 ∂ν) = 1 →
    Tendsto (OriginalWindowProduct.windowError B P hB ν a) atTop (𝓝 (0 : ℝ))

-- T19 PUBLIC SHARP CLASSIFICATION head. Original hypotheses, fixed laws.
theorem universal_fixed_law_window_iff
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a : ℕ → ℝ) (haAnti : Antitone a)
    (ha : Tendsto a atTop (𝓝 (0 : ℝ))) :
    universalFixedLawWindow B P hB a ↔
      Tendsto (fun n => a n * (n : ℝ) ^ ((1 : ℝ) / 6)) atTop atTop := by
  constructor
  · intro hall
    exact rademacher_window_necessity B P hB a
      (hall RademacherCosine.law inferInstance rademacher_moments.1
        rademacher_moments.2.1 rademacher_moments.2.2.1)
  · intro hslow ν hν h3 hmean hsecond
    letI : IsProbabilityMeasure ν := hν
    exact OriginalWindowProduct.product_window_tendsto B P hB ν h3 hmean hsecond
      a haAnti ha hslow


-- D20 PUBLIC full value. One actual infinite product, with a measurable universe lift.
def rademacherIIDLaw : Measure (ULift.{u} (ℕ → ℝ)) :=
  (Measure.infinitePi (fun _ : ℕ => RademacherCosine.law)).map ULift.up

-- D21 PUBLIC full value. The OriginalIIDWindow interface uses X_(i+1).
def rademacherIIDCoordinate (i : ℕ) (ω : ULift.{u} (ℕ → ℝ)) : ℝ :=
  ω.down i

-- T22 PUBLIC head. Proves every original moment/iid premise for that one space.
theorem rademacherIID_facts :
    IsProbabilityMeasure (rademacherIIDLaw.{u}) ∧
    (∀ i : ℕ, Measurable (rademacherIIDCoordinate.{u} (i + 1))) ∧
    iIndepFun (fun i : ℕ => rademacherIIDCoordinate.{u} (i + 1))
      (rademacherIIDLaw.{u}) ∧
    (∀ i : ℕ, IdentDistrib (rademacherIIDCoordinate.{u} (i + 1))
      (rademacherIIDCoordinate.{u} 1) (rademacherIIDLaw.{u}) (rademacherIIDLaw.{u})) ∧
    (∀ i : ℕ, (rademacherIIDLaw.{u}).map (rademacherIIDCoordinate.{u} (i + 1)) =
      RademacherCosine.law) ∧
    Integrable (fun ω => |rademacherIIDCoordinate.{u} 1 ω| ^ 3)
      (rademacherIIDLaw.{u}) ∧
    (∫ ω, rademacherIIDCoordinate.{u} 1 ω ∂(rademacherIIDLaw.{u})) = 0 ∧
    (∫ ω, (rademacherIIDCoordinate.{u} 1 ω) ^ 2 ∂(rademacherIIDLaw.{u})) = 1 := by
  let μ0 : Measure (ℕ → ℝ) :=
    Measure.infinitePi (fun _ : ℕ => RademacherCosine.law)
  haveI : IsProbabilityMeasure μ0 := by dsimp [μ0]; infer_instance
  have hμ : IsProbabilityMeasure (rademacherIIDLaw.{u}) := ⟨by
    change (μ0.map (ULift.up : (ℕ → ℝ) → ULift.{u} (ℕ → ℝ))) univ = 1
    rw [Measure.map_apply measurable_up MeasurableSet.univ]
    simp⟩
  letI : IsProbabilityMeasure (rademacherIIDLaw.{u}) := hμ
  have hX (i : ℕ) : Measurable (rademacherIIDCoordinate.{u} i) :=
    (measurable_pi_apply i).comp measurable_down
  have hmap (i : ℕ) :
      (rademacherIIDLaw.{u}).map (rademacherIIDCoordinate.{u} i) = RademacherCosine.law := by
    change (μ0.map (ULift.up : (ℕ → ℝ) → ULift.{u} (ℕ → ℝ))).map
      (rademacherIIDCoordinate.{u} i) = RademacherCosine.law
    rw [Measure.map_map (hX i) measurable_up]
    change μ0.map (fun ω : ℕ → ℝ => ω i) = RademacherCosine.law
    exact Measure.infinitePi_map_eval (fun _ : ℕ => RademacherCosine.law) i
  have hdown : (rademacherIIDLaw.{u}).map
      (fun ω i => rademacherIIDCoordinate.{u} i ω) = μ0 := by
    change (μ0.map (ULift.up : (ℕ → ℝ) → ULift.{u} (ℕ → ℝ))).map
      (ULift.down : ULift.{u} (ℕ → ℝ) → (ℕ → ℝ)) = μ0
    rw [Measure.map_map measurable_down measurable_up]
    exact Measure.map_id (μ := μ0)
  have hind : iIndepFun (rademacherIIDCoordinate.{u}) (rademacherIIDLaw.{u}) := by
    apply (iIndepFun_iff_map_fun_eq_infinitePi_map hX).mpr
    rw [hdown]
    simp only [hmap]
    rfl
  have hLaw (i : ℕ) : IdentDistrib (rademacherIIDCoordinate.{u} i) (id : ℝ → ℝ)
      (rademacherIIDLaw.{u}) RademacherCosine.law :=
    ⟨(hX i).aemeasurable, measurable_id.aemeasurable,
      by simpa only [Measure.map_id] using hmap i⟩
  have hLaw3 := (hLaw 1).comp (show Measurable (fun z : ℝ => |z| ^ 3) by fun_prop)
  have hLaw2 := (hLaw 1).comp (show Measurable (fun z : ℝ => z ^ 2) by fun_prop)
  refine ⟨hμ, fun i => hX (i + 1),
    hind.precomp (g := fun i : ℕ => i + 1)
      (by intro i j hij; change i + 1 = j + 1 at hij; omega),
    fun i => (hLaw (i + 1)).trans (hLaw 1).symm,
    fun i => hmap (i + 1), hLaw3.integrable_iff.mpr rademacher_moments.1,
    (hLaw 1).integral_eq.trans rademacher_moments.2.1,
    hLaw2.integral_eq.trans rademacher_moments.2.2.1⟩


-- T23 PUBLIC head. Literal one-based original event, every n and every x.
theorem rademacher_original_probability_eq_product (n : ℕ) (x : ℝ) :
    (rademacherIIDLaw.{u}).real
      (OriginalIIDWindow.sourceEvent n (rademacherIIDCoordinate.{u}) x) =
      OriginalWindowProduct.productProbability RademacherCosine.law n x := by
  rcases rademacherIID_facts.{u} with ⟨hμ, hX, hind, hident, hmap, _, _, _⟩
  letI : IsProbabilityMeasure (rademacherIIDLaw.{u}) := hμ
  have heq : (rademacherIIDLaw.{u}).map
      (fun ω => rademacherIIDCoordinate.{u} 1 ω / 1) = RademacherCosine.law := by
    simpa only [div_one, zero_add] using hmap 0
  have hp := OriginalIIDWindow.source_probability_eq_product
    (rademacherIIDLaw.{u}) (rademacherIIDCoordinate.{u}) hX hind hident
    1 (by norm_num) n x
  rw [heq] at hp
  exact hp


-- T24 PUBLIC head. Exact equality of real suprema, with all early conventions.
theorem rademacher_original_window_eq_product
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a : ℕ → ℝ) (n : ℕ) :
    OriginalIIDWindow.sourceWindowError B P hB (rademacherIIDLaw.{u})
      (rademacherIIDCoordinate.{u}) a n =
    OriginalWindowProduct.windowError B P hB RademacherCosine.law a n := by
  simp only [OriginalIIDWindow.sourceWindowError, OriginalWindowProduct.windowError,
    OriginalWindowProduct.windowValues, OriginalWindowProduct.relativeError,
    rademacher_original_probability_eq_product]


-- T25 PUBLIC ORIGINAL SHARP CLASSIFICATION head. All fixed iid spaces at ANY u.
-- No standardized-variance restriction, no ordinary-measurability restriction.
-- ULift above supplies a concrete Rademacher test space in that very universe.
theorem universal_fixed_iid_window_iff
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a : ℕ → ℝ) (haAnti : Antitone a)
    (ha : Tendsto a atTop (𝓝 (0 : ℝ))) :
    (∀ (ΩX : Type u) [MeasurableSpace ΩX]
      (μ : Measure ΩX) [IsProbabilityMeasure μ]
      (X : ℕ → ΩX → ℝ) (hX : ∀ i : ℕ, AEMeasurable (X (i + 1)) μ)
      (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
      (hIdent : ∀ i : ℕ, IdentDistrib (X (i + 1)) (X 1) μ μ)
      (h3 : Integrable (fun ω => |X 1 ω| ^ 3) μ)
      (hmean : (∫ ω, X 1 ω ∂μ) = 0)
      (hsecond : 0 < ∫ ω, (X 1 ω) ^ 2 ∂μ),
      Tendsto (fun n : ℕ => sSup ((fun x : ℝ =>
        |μ.real {ω | OriginalIIDWindow.sourceMaximum n X ω ≤
          x * Real.sqrt (OriginalIIDWindow.sourceEnergy n X ω)} /
          Shao.Probability.BrownianSup.probability B P hB x - 1|) '' Ioo (a n) 1))
        atTop (𝓝 (0 : ℝ))) ↔
      Tendsto (fun n => a n * (n : ℝ) ^ ((1 : ℝ) / 6)) atTop atTop := by
  constructor
  · intro hall
    rcases rademacherIID_facts.{u} with
      ⟨hμ, hX, hind, hident, _, h3, hmean, hsecond⟩
    letI : IsProbabilityMeasure (rademacherIIDLaw.{u}) := hμ
    have hsecondpos : 0 < ∫ ω, (rademacherIIDCoordinate.{u} 1 ω) ^ 2
        ∂(rademacherIIDLaw.{u}) := by rw [hsecond]; norm_num
    have hgiven := hall (ULift.{u} (ℕ → ℝ)) (rademacherIIDLaw.{u})
      (rademacherIIDCoordinate.{u}) (fun i => (hX i).aemeasurable)
      hind hident h3 hmean hsecondpos
    have hsource : Tendsto
        (OriginalIIDWindow.sourceWindowError B P hB (rademacherIIDLaw.{u})
          (rademacherIIDCoordinate.{u}) a) atTop (𝓝 (0 : ℝ)) := by
      exact hgiven.congr' (Eventually.of_forall fun n => by rfl)
    have hproduct : Tendsto
        (OriginalWindowProduct.windowError B P hB RademacherCosine.law a)
        atTop (𝓝 (0 : ℝ)) :=
      hsource.congr' (Eventually.of_forall fun n =>
        rademacher_original_window_eq_product B P hB a n)
    exact rademacher_window_necessity B P hB a hproduct
  · intro hslow ΩX mX μ hμ X hX hind hident h3 hmean hsecond
    exact OriginalIIDWindow.original_iid_sSup_tendsto B P hB μ X hX hind hident
      h3 hmean hsecond a haAnti ha hslow


end Shao.OQ4.CriticalWindowNecessity
end
