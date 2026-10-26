import Shao.OQ6.OriginalGhostGoodEvent
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.OrderClosed

set_option autoImplicit false

namespace Shao.OQ6.OriginalLowEnergyTail

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology

theorem original_low_energy_exponential
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgsecond : (∫ o : Ω, (g o) ^ (2 : ℕ) ∂μ) = 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      (Shao.OQ6.CanonicalDoubleGhostRowMoments.sampleLaw n μ).real
        {x : Fin n → Ω |
          Shao.OQ6.OriginalGhostGoodEvent.sampleEnergy n g x < (n : ℝ) / (2 : ℝ)} ≤
        Real.exp (-c * (n : ℝ)) := by
  classical
  let X : Ω → ℝ := fun o : Ω => (g o) ^ (2 : ℕ)
  let Z : ℕ → Ω → ℝ := fun k : ℕ => fun o : Ω => min (X o) (k : ℝ)
  let KExistsProp : Prop :=
    ∃ k : ℕ, 1 ≤ k ∧ (7 / 8 : ℝ) ≤ ∫ o : Ω, Z k o ∂μ
  have hXMeas : Measurable X := hg.pow_const (2 : ℕ)
  have hXInt : Integrable X μ := hg2.integrable_sq
  have hXNonneg : ∀ o : Ω, 0 ≤ X o := fun o => sq_nonneg (g o)
  have hZMeas : ∀ k : ℕ, Measurable (Z k) := by
    intro k
    exact hXMeas.min measurable_const
  have hZBounds : ∀ (k : ℕ) (o : Ω),
      0 ≤ Z k o ∧ Z k o ≤ X o ∧ Z k o ≤ (k : ℝ) := by
    intro k o
    exact ⟨le_min (hXNonneg o) (Nat.cast_nonneg k),
      min_le_left _ _, min_le_right _ _⟩
  have hZInt : ∀ k : ℕ, Integrable (Z k) μ := by
    intro k
    apply hXInt.mono' (hZMeas k).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun o => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hZBounds k o).1]
      exact (hZBounds k o).2.1)
  have hCastLimit :
      Filter.Tendsto (fun k : ℕ => (k : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hZPointLimit : ∀ o : Ω,
      Filter.Tendsto (fun k : ℕ => Z k o) Filter.atTop (𝓝 (X o)) := by
    intro o
    apply tendsto_order.2
    constructor
    · intro a ha
      filter_upwards [hCastLimit.eventually (eventually_ge_atTop (X o))] with k hk
      dsimp only [Z]
      rw [min_eq_left hk]
      exact ha
    · intro b hb
      exact Filter.Eventually.of_forall
        (fun k => ((hZBounds k o).2.1).trans_lt hb)
  have hZIntegralLimit :
      Filter.Tendsto (fun k : ℕ => ∫ o : Ω, Z k o ∂μ)
        Filter.atTop (𝓝 (1 : ℝ)) := by
    simpa only [X, hgsecond] using
      (tendsto_integral_of_dominated_convergence (μ := μ) (F := Z) (f := X) X
        (fun k : ℕ => (hZMeas k).aestronglyMeasurable) hXInt
        (fun k : ℕ => Filter.Eventually.of_forall (fun o : Ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hZBounds k o).1]
          exact (hZBounds k o).2.1))
        (Filter.Eventually.of_forall hZPointLimit))
  have hIntegralEventually :
      ∀ᶠ k : ℕ in Filter.atTop, (7 / 8 : ℝ) ≤ ∫ o : Ω, Z k o ∂μ :=
    hZIntegralLimit.eventually
      (eventually_ge_nhds (by norm_num : (7 / 8 : ℝ) < 1))
  have hKExists : KExistsProp := by
    change ∃ k : ℕ, 1 ≤ k ∧ (7 / 8 : ℝ) ≤ ∫ o : Ω, Z k o ∂μ
    exact ((eventually_ge_atTop (1 : ℕ)).and hIntegralEventually).exists
  rcases hKExists with ⟨k, hkOne, hkMoment⟩
  let K : ℝ := (k : ℝ)
  let Y : Ω → ℝ := fun o : Ω => min (X o) K
  let s : ℝ := 1 / (8 * K)
  let c : ℝ := s / 4
  let f : Ω → ℝ := fun o : Ω => Real.exp (-s * X o)
  let L : ℝ := ∫ o : Ω, f o ∂μ
  let U : Ω → ℝ :=
    fun o : Ω => 1 - (s * Y o - s ^ (2 : ℕ) * (Y o) ^ (2 : ℕ))
  have hKOne : (1 : ℝ) ≤ K := by
    dsimp only [K]
    exact_mod_cast hkOne
  have hKPos : 0 < K := lt_of_lt_of_le zero_lt_one hKOne
  have hYMeas : Measurable Y := hXMeas.min measurable_const
  have hYBounds : ∀ o : Ω, 0 ≤ Y o ∧ Y o ≤ X o ∧ Y o ≤ K := by
    intro o
    exact ⟨le_min (hXNonneg o) hKPos.le, min_le_left _ _, min_le_right _ _⟩
  have hYInt : Integrable Y μ := by
    apply hXInt.mono' hYMeas.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun o => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hYBounds o).1]
      exact (hYBounds o).2.1)
  have hYsqMeas : Measurable (fun o : Ω => (Y o) ^ (2 : ℕ)) :=
    hYMeas.pow_const (2 : ℕ)
  have hYsqPoint : ∀ o : Ω, (Y o) ^ (2 : ℕ) ≤ K * Y o := by
    intro o
    simpa only [pow_two] using
      mul_le_mul_of_nonneg_right (hYBounds o).2.2 (hYBounds o).1
  have hYsqInt : Integrable (fun o : Ω => (Y o) ^ (2 : ℕ)) μ := by
    apply (hYInt.const_mul K).mono' hYsqMeas.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun o => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Y o))]
      exact hYsqPoint o)
  have hEYBounds :
      (7 / 8 : ℝ) ≤ (∫ o : Ω, Y o ∂μ) ∧ (∫ o : Ω, Y o ∂μ) ≤ 1 := by
    refine ⟨hkMoment, ?_⟩
    calc
      (∫ o : Ω, Y o ∂μ) ≤ ∫ o : Ω, X o ∂μ :=
        integral_mono hYInt hXInt (fun o => (hYBounds o).2.1)
      _ = 1 := hgsecond
  have hEYsqBound : (∫ o : Ω, (Y o) ^ (2 : ℕ) ∂μ) ≤ K := by
    calc
      (∫ o : Ω, (Y o) ^ (2 : ℕ) ∂μ) ≤ ∫ o : Ω, K * Y o ∂μ :=
        integral_mono hYsqInt (hYInt.const_mul K) hYsqPoint
      _ = K * (∫ o : Ω, Y o ∂μ) := integral_const_mul K Y
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left hEYBounds.2 hKPos.le
      _ = K := by ring
  have hSPos : 0 < s :=
    div_pos zero_lt_one (mul_pos (by norm_num : (0 : ℝ) < 8) hKPos)
  have hCPos : 0 < c := div_pos hSPos (by norm_num : (0 : ℝ) < 4)
  have hSK : s * K = (1 / 8 : ℝ) := by
    dsimp only [s]
    field_simp [hKPos.ne'] <;> ring
  have hSsqK : s ^ (2 : ℕ) * K = s / 8 := by
    calc
      s ^ (2 : ℕ) * K = s * (s * K) := by ring
      _ = s / 8 := by rw [hSK]; ring
  have hExpOrder : ∀ (a b : ℝ), a ≤ b → Real.exp a ≤ Real.exp b := by
    intro a b hab
    have hGapOne : 1 ≤ Real.exp (b - a) := by
      linarith only [Real.add_one_le_exp (b - a), hab]
    calc
      Real.exp a ≤ Real.exp a * Real.exp (b - a) := by
        nlinarith only
          [mul_nonneg (Real.exp_pos a).le (sub_nonneg.mpr hGapOne)]
      _ = Real.exp b := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hScalar : ∀ u : ℝ, 0 ≤ u → Real.exp (-u) ≤ 1 - u + u ^ (2 : ℕ) := by
    intro u hu
    have hDen : 0 < 1 + u := by linarith only [hu]
    have hReciprocal : Real.exp (-u) ≤ 1 / (1 + u) := by
      apply (le_div_iff₀ hDen).2
      calc
        Real.exp (-u) * (1 + u) ≤ Real.exp (-u) * Real.exp u :=
          mul_le_mul_of_nonneg_left
            (by simpa only [add_comm] using Real.add_one_le_exp u)
            (Real.exp_pos (-u)).le
        _ = 1 := by
          rw [Real.exp_neg]
          field_simp [Real.exp_ne_zero u]
    have hCubicNonneg : 0 ≤ u ^ (2 : ℕ) * u :=
      mul_nonneg (sq_nonneg u) hu
    have hPolynomial : 1 / (1 + u) ≤ 1 - u + u ^ (2 : ℕ) := by
      apply (div_le_iff₀ hDen).2
      nlinarith only [hCubicNonneg]
    exact hReciprocal.trans hPolynomial
  have hfm : Measurable f := (hXMeas.const_mul (-s)).exp
  have hfBounds : ∀ o : Ω, 0 < f o ∧ f o ≤ 1 := by
    intro o
    refine ⟨Real.exp_pos _, ?_⟩
    simpa only [f, Real.exp_zero] using
      hExpOrder (-s * X o) 0
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hSPos.le) (hXNonneg o))
  have hfInt : Integrable f μ := by
    apply (integrable_const (1 : ℝ)).mono' hfm.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun o => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hfBounds o).1.le]
      exact (hfBounds o).2)
  have hLNonneg : 0 ≤ L := integral_nonneg (fun o => (hfBounds o).1.le)
  have hUInt : Integrable U μ :=
    (integrable_const (1 : ℝ)).sub
      ((hYInt.const_mul s).sub (hYsqInt.const_mul (s ^ (2 : ℕ))))
  have hPointwise : ∀ o : Ω, f o ≤ U o := by
    intro o
    calc
      f o = Real.exp (-s * X o) := rfl
      _ ≤ Real.exp (-s * Y o) := hExpOrder _ _ (by
        nlinarith only [mul_le_mul_of_nonneg_left (hYBounds o).2.1 hSPos.le])
      _ = Real.exp (-(s * Y o)) := by congr 1; ring
      _ ≤ 1 - s * Y o + (s * Y o) ^ (2 : ℕ) :=
        hScalar (s * Y o) (mul_nonneg hSPos.le (hYBounds o).1)
      _ = U o := by dsimp only [U]; ring
  have hLLinear : L ≤ 1 - 3 * s / 4 := by
    calc
      L ≤ ∫ o : Ω, U o ∂μ := integral_mono hfInt hUInt hPointwise
      _ = 1 - (s * (∫ o : Ω, Y o ∂μ) -
          s ^ (2 : ℕ) * (∫ o : Ω, (Y o) ^ (2 : ℕ) ∂μ)) := by
        dsimp only [U]
        calc
          (∫ o : Ω, 1 - (s * Y o - s ^ (2 : ℕ) * (Y o) ^ (2 : ℕ)) ∂μ) =
              (∫ _ : Ω, (1 : ℝ) ∂μ) -
                (∫ o : Ω, s * Y o - s ^ (2 : ℕ) * (Y o) ^ (2 : ℕ) ∂μ) := by
            exact integral_sub (integrable_const (1 : ℝ))
              ((hYInt.const_mul s).sub (hYsqInt.const_mul (s ^ (2 : ℕ))))
          _ = (∫ _ : Ω, (1 : ℝ) ∂μ) -
              ((∫ o : Ω, s * Y o ∂μ) -
                (∫ o : Ω, s ^ (2 : ℕ) * (Y o) ^ (2 : ℕ) ∂μ)) := by
            congr 1
            exact integral_sub (hYInt.const_mul s)
              (hYsqInt.const_mul (s ^ (2 : ℕ)))
          _ = 1 - (s * (∫ o : Ω, Y o ∂μ) -
              s ^ (2 : ℕ) * (∫ o : Ω, (Y o) ^ (2 : ℕ) ∂μ)) := by
            rw [integral_const_mul, integral_const_mul, integral_const]
            simp only [probReal_univ, smul_eq_mul, one_mul]
      _ ≤ 1 - (s * (7 / 8 : ℝ) - s ^ (2 : ℕ) * K) := by
        nlinarith only
          [mul_le_mul_of_nonneg_left hEYBounds.1 hSPos.le,
            mul_le_mul_of_nonneg_left hEYsqBound (sq_nonneg s)]
      _ = 1 - 3 * s / 4 := by rw [hSsqK]; ring
  have hLDecay : L ≤ Real.exp (-3 * s / 4) := by
    apply hLLinear.trans
    linarith only [Real.add_one_le_exp (-3 * s / 4)]
  have hNaturalPowerOrder :
      ∀ (a b : ℝ), 0 ≤ a → a ≤ b → ∀ k : ℕ, a ^ k ≤ b ^ k := by
    intro a b ha hab k
    induction k with
    | zero => simp only [pow_zero, le_refl]
    | succ k ih =>
      simpa only [pow_succ] using
        mul_le_mul ih hab ha (pow_nonneg (ha.trans hab) k)
  refine ⟨c, hCPos, ?_⟩
  intro n
  let P : Measure (Fin n → Ω) :=
    Shao.OQ6.CanonicalDoubleGhostRowMoments.sampleLaw n μ
  let S : (Fin n → Ω) → ℝ := Shao.OQ6.OriginalGhostGoodEvent.sampleEnergy n g
  let F : (Fin n → Ω) → ℝ := fun x : Fin n → Ω => Real.exp (-s * S x)
  let ε : ℝ := Real.exp (-s * (n : ℝ) / (2 : ℝ))
  let E : Set (Fin n → Ω) := {x : Fin n → Ω | S x < (n : ℝ) / (2 : ℝ)}
  haveI hPprob : IsProbabilityMeasure P := by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin n => μ))
    infer_instance
  have hSm : Measurable S := by
    change Measurable (fun x : Fin n → Ω => ∑ i : Fin n, (g (x i)) ^ (2 : ℕ))
    exact Finset.measurable_fun_sum (Finset.univ : Finset (Fin n))
      (fun i _ => (hg.comp (measurable_pi_apply i)).pow_const (2 : ℕ))
  have hEm : MeasurableSet E := measurableSet_lt hSm measurable_const
  have hFmm : Measurable F := (hSm.const_mul (-s)).exp
  have hFactor : F = (fun x : Fin n → Ω => ∏ i : Fin n, f (x i)) := by
    funext x
    calc
      F x = Real.exp (∑ i : Fin n, -s * (g (x i)) ^ (2 : ℕ)) := by
        dsimp only [F, S, Shao.OQ6.OriginalGhostGoodEvent.sampleEnergy]
        congr 1
        rw [Finset.mul_sum]
      _ = ∏ i : Fin n, f (x i) := by
        simpa only [f, X] using
          Real.exp_sum (Finset.univ : Finset (Fin n))
            (fun i : Fin n => -s * (g (x i)) ^ (2 : ℕ))
  have hFInt : Integrable F P := by
    rw [hFactor]
    change Integrable (fun x : Fin n → Ω => ∏ i : Fin n, f (x i))
      (Measure.pi (fun _ : Fin n => μ))
    exact Integrable.fin_nat_prod (μ := fun _ : Fin n => μ)
      (f := fun _ : Fin n => f) (fun _ : Fin n => hfInt)
  have hIntegral : (∫ x : Fin n → Ω, F x ∂P) = L ^ n := by
    rw [hFactor]
    change (∫ x : Fin n → Ω, ∏ i : Fin n, f (x i)
      ∂(Measure.pi (fun _ : Fin n => μ))) = L ^ n
    simpa only [Fintype.card_fin] using
      (integral_fintype_prod_eq_pow (ι := Fin n) (μ := μ) f)
  have hIntegralBound :
      (∫ x : Fin n → Ω, F x ∂P) ≤ Real.exp (-3 * s * (n : ℝ) / 4) := by
    calc
      (∫ x : Fin n → Ω, F x ∂P) = L ^ n := hIntegral
      _ ≤ (Real.exp (-3 * s / 4)) ^ n :=
        hNaturalPowerOrder L (Real.exp (-3 * s / 4)) hLNonneg hLDecay n
      _ = Real.exp (-3 * s * (n : ℝ) / 4) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hεPos : 0 < ε := Real.exp_pos _
  have hESubset : E ⊆ {x : Fin n → Ω | ε ≤ F x} := by
    intro x hx
    change S x < (n : ℝ) / (2 : ℝ) at hx
    change Real.exp (-s * (n : ℝ) / 2) ≤ Real.exp (-s * S x)
    apply hExpOrder
    nlinarith only [mul_le_mul_of_nonneg_left hx.le hSPos.le]
  have hMeasure : P.real E ≤ P.real {x : Fin n → Ω | ε ≤ F x} :=
    measureReal_mono hESubset
  have hMarkov :
      ε * P.real {x : Fin n → Ω | ε ≤ F x} ≤ ∫ x : Fin n → Ω, F x ∂P :=
    mul_meas_ge_le_integral_of_nonneg (μ := P) (f := F)
      (Filter.Eventually.of_forall
        (fun x : Fin n → Ω => (Real.exp_pos (-s * S x)).le)) hFInt ε
  have hPaid : ε * P.real E ≤ Real.exp (-3 * s * (n : ℝ) / 4) :=
    (mul_le_mul_of_nonneg_left hMeasure hεPos.le).trans
      (hMarkov.trans hIntegralBound)
  have hBound : P.real E ≤ Real.exp (-c * (n : ℝ)) := by
    calc
      P.real E ≤ Real.exp (-3 * s * (n : ℝ) / 4) / ε := by
        apply (le_div_iff₀ hεPos).2
        simpa only [mul_comm ε (P.real E)] using hPaid
      _ = Real.exp (-c * (n : ℝ)) := by
        dsimp only [ε, c]
        rw [← Real.exp_sub]
        congr 1
        ring
  exact hBound

end

end Shao.OQ6.OriginalLowEnergyTail
