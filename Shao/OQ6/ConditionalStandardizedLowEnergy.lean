import Shao.OQ6.ConditionalStandardizedPMoment
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.Complex.Exponential

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Shao.OQ6.ConditionalStandardizedLowEnergy

noncomputable section

open MeasureTheory ProbabilityTheory

theorem actual_conditional_standardized_low_energy
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun z : Ω × Ω => h z.1 z.2))
    (hh2 : MemLp (fun z : Ω × Ω => h z.1 z.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ z : Ω × Ω, h z.1 z.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (w : Ω → ℝ)
    (hw : Measurable w)
    (hwone : ∀ᵐ o ∂μ, 1 ≤ w o)
    (α τ : ℝ) (hα : 0 < α) (hτ : 0 < τ)
    (hwexp : Integrable (fun o => Real.exp (τ * Real.rpow (w o) α)) μ)
    (henvelope : ∀ᵐ z : Ω × Ω ∂(μ.prod μ),
      |h z.1 z.2 - (∫ y, h z.1 y ∂μ) - (∫ y, h z.2 y ∂μ)| ≤
        w z.1 * w z.2)
    (p : ℝ) (hp : 2 < p ∧ p ≤ 3)
    (hgp : Integrable
      (fun o => Real.rpow |∫ y, h o y ∂μ| p) μ) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let β : ℝ := ∫ o, Real.rpow |g o| p ∂μ
    let q : ℝ := p / 2
    let t0 : ℝ := Real.rpow (1 / (8 * β)) (2 / (p - 2))
    let c0 : ℝ := t0 / 4
    1 ≤ β ∧ 1 < q ∧ q ≤ (3 / 2 : ℝ) ∧
      0 < t0 ∧ t0 ≤ 1 ∧ 0 < c0 ∧
      2 * β * Real.rpow t0 (q - 1) = (1 / 4 : ℝ) ∧
      ∃ N0 : ℕ, 1 ≤ N0 ∧
      ∀ R : ℝ, (N0 : ℝ) ≤ R →
      let C : Set Ω := {o : Ω | w o ≤ R}
      let d : ℝ := μ.real C
      let ν : Measure Ω := (μ C)⁻¹ • μ.restrict C
      MeasurableSet C ∧ (1 / 2 : ℝ) ≤ d ∧
        IsProbabilityMeasure ν ∧ ν ≪ μ ∧ ν C = 1 ∧
        ∀ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 →
        let H : Ω → Ω → ℝ := fun o y => g o + g y + lam * r o y
        let κ : ℝ := ∫ z : Ω × Ω, H z.1 z.2 ∂(ν.prod ν)
        let G : Ω → ℝ := fun o => (∫ y, H o y ∂ν) - κ
        let σ2 : ℝ := ∫ o, G o ^ 2 ∂ν
        let σ : ℝ := Real.sqrt σ2
        let X : Ω → ℝ := fun o => G o / σ
        Measurable G ∧ MemLp G 2 ν ∧
          Integrable (fun o => G o ^ 2) ν ∧
          (∫ o, G o ∂ν) = 0 ∧
          (1 / 2 : ℝ) ≤ σ2 ∧ σ2 ≤ (3 / 2 : ℝ) ∧
          0 < σ ∧ σ ^ 2 = σ2 ∧
          Measurable X ∧ MemLp X (ENNReal.ofReal p) ν ∧
          MemLp X 2 ν ∧ Integrable (fun o => X o ^ 2) ν ∧
          (∫ o, X o ^ 2 ∂ν) = 1 ∧
          Integrable (fun o => Real.rpow |X o| p) ν ∧
          (∫ o, Real.rpow |X o| p ∂ν) ≤ 2 * β ∧
          (let f : Ω → ℝ := fun o => Real.exp (-t0 * X o ^ 2)
           let L : ℝ := ∫ o, f o ∂ν
           Measurable f ∧ Integrable f ν ∧ 0 ≤ L ∧
             L ≤ 1 - 3 * t0 / 4 ∧
             L ≤ Real.exp (-3 * t0 / 4) ∧
             ∀ m : ℕ,
             let Pm : Measure (Fin m → Ω) := Measure.pi (fun _ : Fin m => ν)
             let S : (Fin m → Ω) → ℝ := fun o => ∑ i : Fin m, X (o i) ^ 2
             let Fm : (Fin m → Ω) → ℝ := fun o => Real.exp (-t0 * S o)
             let εm : ℝ := Real.exp (-t0 * (m : ℝ) / 2)
             let E : Set (Fin m → Ω) := {o : Fin m → Ω | S o ≤ (m : ℝ) / 2}
             IsProbabilityMeasure Pm ∧ Measurable S ∧ MeasurableSet E ∧
               Measurable Fm ∧ Integrable Fm Pm ∧ 0 < εm ∧
               (∫ o, Fm o ∂Pm) = L ^ m ∧
               (∫ o, Fm o ∂Pm) ≤ Real.exp (-3 * t0 * (m : ℝ) / 4) ∧
               Pm.real E ≤ Real.exp (-c0 * (m : ℝ))) := by
  classical
  dsimp only
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
  let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
  let β : ℝ := ∫ o, Real.rpow |g o| p ∂μ
  let q : ℝ := p / 2
  let t0 : ℝ := Real.rpow (1 / (8 * β)) (2 / (p - 2))
  let c0 : ℝ := t0 / 4
  have h178 :=
    Shao.OQ6.ConditionalStandardizedPMoment.actual_conditional_standardized_pmoment
      μ h hh hh2 hhsymm hcenter hprojectionsecond w hw hwone
      α τ hα hτ hwexp henvelope p hp hgp
  dsimp only at h178
  rcases h178 with
    ⟨hAexp, hExpDom, hwpInt, hwpLp, hgpLp, hBeta, h178Tail⟩
  change 1 ≤ β at hBeta
  have hBetaPos : 0 < β := lt_of_lt_of_le zero_lt_one hBeta
  have hpminus : 0 < p - 2 := by linarith only [hp.1]
  have hqLower : 1 < q := by dsimp only [q]; linarith only [hp.1]
  have hqUpper : q ≤ (3 / 2 : ℝ) := by dsimp only [q]; linarith only [hp.2]
  have hqTwo : q ≤ 2 := by linarith only [hqUpper]
  have hbasePos : 0 < 1 / (8 * β) :=
    div_pos zero_lt_one (mul_pos (by norm_num) hBetaPos)
  have hbaseOne : 1 / (8 * β) ≤ 1 := by
    apply (div_le_one (mul_pos (by norm_num : (0 : ℝ) < 8) hBetaPos)).2
    linarith only [hBeta]
  have hExponentPos : 0 < 2 / (p - 2) := div_pos (by norm_num) hpminus
  have ht0Pos : 0 < t0 := Real.rpow_pos_of_pos hbasePos _
  have ht0One : t0 ≤ 1 := Real.rpow_le_one hbasePos.le hbaseOne hExponentPos.le
  have hc0Pos : 0 < c0 := div_pos ht0Pos (by norm_num)
  have hTpower : Real.rpow t0 (q - 1) = 1 / (8 * β) := by
    dsimp only [t0]
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul hbasePos.le]
    have hExponent : (2 / (p - 2)) * (q - 1) = 1 := by
      dsimp only [q]
      field_simp [hpminus.ne'] <;> ring
    rw [hExponent, Real.rpow_one]
  have hQuarter : 2 * β * Real.rpow t0 (q - 1) = (1 / 4 : ℝ) := by
    rw [hTpower]
    field_simp [hBetaPos.ne'] <;> ring
  have hTq : Real.rpow t0 q = Real.rpow t0 (q - 1) * t0 := by
    have hExponent : q = (q - 1) + 1 := by ring
    calc
      Real.rpow t0 q = Real.rpow t0 ((q - 1) + 1) := by rw [← hExponent]
      _ = Real.rpow t0 (q - 1) * t0 := by
        simpa only [Real.rpow_eq_pow, Real.rpow_one] using
          Real.rpow_add ht0Pos (q - 1) 1
  have hTqQuarter : 2 * β * Real.rpow t0 q = t0 / 4 := by
    calc
      2 * β * Real.rpow t0 q =
          (2 * β * Real.rpow t0 (q - 1)) * t0 := by rw [hTq]; ring
      _ = (1 / 4 : ℝ) * t0 := by rw [hQuarter]
      _ = t0 / 4 := by ring
  have hExpOrder : ∀ x y : ℝ, x ≤ y → Real.exp x ≤ Real.exp y := by
    intro x y hxy
    have hOne : 1 ≤ Real.exp (y - x) := by
      linarith only [Real.add_one_le_exp (y - x), hxy]
    calc
      Real.exp x ≤ Real.exp x * Real.exp (y - x) := by
        nlinarith only [mul_nonneg (Real.exp_pos x).le (sub_nonneg.mpr hOne)]
      _ = Real.exp y := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hScalar : ∀ «qʹ» z : ℝ, 1 ≤ «qʹ» → «qʹ» ≤ 2 → 0 ≤ z →
      Real.exp (-z) ≤ 1 - z + Real.rpow z «qʹ» := by
    intro «qʹ» z hqLower hqUpper hz
    by_cases hzZero : z = 0
    · subst z
      have hqNonzero : «qʹ» ≠ 0 := by linarith only [hqLower]
      simp only [neg_zero, Real.exp_zero, sub_zero, Real.rpow_eq_pow, Real.zero_rpow hqNonzero, add_zero, le_refl]
    have hzPos : 0 < z := by
      rcases eq_or_lt_of_le hz with hZero | hPos
      · exact False.elim (hzZero hZero.symm)
      · exact hPos
    have hDen : 0 < 1 + z := by linarith only [hz]
    have hReciprocal : Real.exp (-z) ≤ 1 / (1 + z) := by
      apply (le_div_iff₀ hDen).2
      calc
        Real.exp (-z) * (1 + z) ≤ Real.exp (-z) * Real.exp z :=
          mul_le_mul_of_nonneg_left
            (by simpa only [add_comm] using Real.add_one_le_exp z)
            (Real.exp_pos (-z)).le
        _ = 1 := by
          rw [Real.exp_neg]
          field_simp [Real.exp_ne_zero z]
    by_cases hzOne : z ≤ 1
    · have hPower : z ^ 2 ≤ Real.rpow z «qʹ» := by
        simpa only [Real.rpow_eq_pow, Real.rpow_ofNat] using
          (Real.rpow_le_rpow_of_exponent_ge
            (x := z) (y := (2 : ℝ)) (z := «qʹ») hzPos hzOne hqUpper)
      have hFraction : z ^ 2 / (1 + z) ≤ z ^ 2 := by
        apply (div_le_iff₀ hDen).2
        nlinarith only [mul_nonneg (sq_nonneg z) hz]
      have hIdentity : 1 / (1 + z) = 1 - z + z ^ 2 / (1 + z) := by
        field_simp [hDen.ne'] <;> ring
      calc
        Real.exp (-z) ≤ 1 / (1 + z) := hReciprocal
        _ = 1 - z + z ^ 2 / (1 + z) := hIdentity
        _ ≤ 1 - z + z ^ 2 := by simpa only [add_comm] using (add_le_add_left hFraction (1 - z))
        _ ≤ 1 - z + Real.rpow z «qʹ» := by simpa only [add_comm] using (add_le_add_left hPower (1 - z))
    · have hzGeOne : 1 ≤ z := le_of_lt (lt_of_not_ge hzOne)
      have hPower : z ≤ Real.rpow z «qʹ» := by
        simpa only [Real.rpow_eq_pow, Real.rpow_one] using
          (Real.rpow_le_rpow_of_exponent_le
            (x := z) (y := (1 : ℝ)) (z := «qʹ») hzGeOne hqLower)
      have hExpOne : Real.exp (-z) ≤ 1 := by
        simpa only [Real.exp_zero] using hExpOrder (-z) 0 (neg_nonpos.mpr hz)
      linarith only [hPower, hExpOne]
  have hNaturalPowerOrder : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      ∀ k : ℕ, a ^ k ≤ b ^ k := by
    intro a b ha hab k
    induction k with
    | zero => simp only [pow_zero, le_refl]
    | succ k ih =>
      simpa only [pow_succ] using
        mul_le_mul ih hab ha (pow_nonneg (ha.trans hab) k)
  have h178AtBeta := h178Tail β hBetaPos
  let N0 : ℕ := Classical.choose h178AtBeta
  have hN0 := Classical.choose_spec h178AtBeta
  refine ⟨hBeta, hqLower, hqUpper, ht0Pos, ht0One, hc0Pos, hQuarter,
    N0, hN0.1, ?_⟩
  intro R hR
  let C : Set Ω := {o : Ω | w o ≤ R}
  let d : ℝ := μ.real C
  let ν : Measure Ω := (μ C)⁻¹ • μ.restrict C
  have hAtR := hN0.2 R hR
  rcases hAtR with
    ⟨hdHalf, hdPi, hνprob, hνac, hνC, hwνp, hgνp, haνp,
      hgνInt, hMp, hTpNonneg, hTpSmall, hMpSmall, hAtLam⟩
  change (1 / 2 : ℝ) ≤ d at hdHalf
  change IsProbabilityMeasure ν at hνprob
  change ν ≪ μ at hνac
  change ν C = 1 at hνC
  haveI : IsProbabilityMeasure ν := hνprob
  have hC : MeasurableSet C := measurableSet_le hw measurable_const
  refine ⟨hC, hdHalf, hνprob, hνac, hνC, ?_⟩
  intro lam hLam
  let H : Ω → Ω → ℝ := fun o y => g o + g y + lam * r o y
  let κ : ℝ := ∫ z : Ω × Ω, H z.1 z.2 ∂(ν.prod ν)
  let G : Ω → ℝ := fun o => (∫ y, H o y ∂ν) - κ
  let σ2 : ℝ := ∫ o, G o ^ 2 ∂ν
  let σ : ℝ := Real.sqrt σ2
  let X : Ω → ℝ := fun o => G o / σ
  have hAtGLam := hAtLam lam hLam
  rcases hAtGLam with
    ⟨hGm, hGp, hDiffInt, hDeltaFinite, hDeltaSmall, hσLower, hσUpper,
      hσError, hσPos, hXp, hXInt, hMomentError, hMomentBound⟩
  change Measurable G at hGm
  change MemLp G (ENNReal.ofReal p) ν at hGp
  change (1 / 2 : ℝ) ≤ σ2 at hσLower
  change σ2 ≤ (3 / 2 : ℝ) at hσUpper
  change 0 < σ at hσPos
  change MemLp X (ENNReal.ofReal p) ν at hXp
  change Integrable (fun o => Real.rpow |X o| p) ν at hXInt
  change (∫ o, Real.rpow |X o| p ∂ν) ≤ 2 * β at hMomentBound
  have h176 :=
    Shao.OQ6.ConditionalVarianceMean.actual_conditional_variance_mean
      μ h hh hh2 hhsymm hcenter hprojectionsecond w hw hwone
      α τ hα hτ hwexp henvelope p hp hgp
  dsimp only at h176
  rcases h176 with ⟨h176β, h176B, h176W, h176Var, h176Mean, h176⟩
  specialize h176 R hdHalf lam hLam
  rcases h176 with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, hGmean, _⟩
  change (∫ o, G o ∂ν) = 0 at hGmean
  have hpENN : (2 : ENNReal) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hp.1.le
  have hG2 : MemLp G 2 ν := hGp.mono_exponent hpENN
  have hX2 : MemLp X 2 ν := hXp.mono_exponent hpENN
  have hGsq : Integrable (fun o => G o ^ 2) ν := hG2.integrable_sq
  have hXsq : Integrable (fun o => X o ^ 2) ν := hX2.integrable_sq
  have hσ2Pos : 0 < σ2 := by linarith only [hσLower]
  have hσSquare : σ ^ 2 = σ2 := Real.sq_sqrt hσ2Pos.le
  have hXm : Measurable X := hGm.div_const σ
  have hNormalization : (∫ o, X o ^ 2 ∂ν) = 1 := by
    calc
      (∫ o, X o ^ 2 ∂ν) = ∫ o, G o ^ 2 / σ ^ 2 ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun o => by
          dsimp only [X]
          rw [div_pow])
      _ = (∫ o, G o ^ 2 ∂ν) / σ ^ 2 := integral_div _ _
      _ = 1 := by
        change σ2 / σ ^ 2 = 1
        rw [hσSquare]
        exact div_self hσ2Pos.ne'
  refine ⟨hGm, hG2, hGsq, hGmean, hσLower, hσUpper, hσPos, hσSquare,
    hXm, hXp, hX2, hXsq, hNormalization, hXInt, hMomentBound, ?_⟩
  let f : Ω → ℝ := fun o => Real.exp (-t0 * X o ^ 2)
  let L : ℝ := ∫ o, f o ∂ν
  have hfm : Measurable f := ((hXm.pow_const (2 : ℕ)).const_mul (-t0)).exp
  have hfNonneg : ∀ o, 0 ≤ f o := fun o => (Real.exp_pos _).le
  have hfOne : ∀ o, f o ≤ 1 := by
    intro o
    have hExp := hExpOrder (-t0 * X o ^ 2) 0
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht0Pos.le) (sq_nonneg (X o)))
    simpa only [f, Real.exp_zero] using hExp
  have hfInt : Integrable f ν := by
    apply (integrable_const (1 : ℝ)).mono' hfm.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun o => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hfNonneg o)]
      exact hfOne o)
  have hLNonneg : 0 ≤ L := integral_nonneg hfNonneg
  have hPointwise : ∀ o, f o ≤
      1 - (t0 * X o ^ 2 - Real.rpow t0 q * Real.rpow |X o| p) := by
    intro o
    have hProduct : Real.rpow (t0 * X o ^ 2) q =
        Real.rpow t0 q * Real.rpow (X o ^ 2) q := by
      simpa only [Real.rpow_eq_pow] using
        (Real.mul_rpow ht0Pos.le (sq_nonneg (X o)) (z := q))
    have hSquarePower : Real.rpow (X o ^ 2) q = Real.rpow |X o| p := by
      simp only [Real.rpow_eq_pow]
      rw [← sq_abs, ← Real.rpow_ofNat |X o| 2,
        ← Real.rpow_mul (abs_nonneg (X o))]
      have hTwoq : (2 : ℝ) * q = p := by dsimp only [q]; ring
      rw [hTwoq]
    calc
      f o = Real.exp (-(t0 * X o ^ 2)) := by dsimp only [f]; congr 1; ring
      _ ≤ 1 - t0 * X o ^ 2 + Real.rpow (t0 * X o ^ 2) q :=
        hScalar q (t0 * X o ^ 2) hqLower.le hqTwo
          (mul_nonneg ht0Pos.le (sq_nonneg (X o)))
      _ = 1 - (t0 * X o ^ 2 - Real.rpow t0 q * Real.rpow |X o| p) := by
        rw [hProduct, hSquarePower]
        ring
  have hUpperInt : Integrable
      (fun o => 1 - (t0 * X o ^ 2 - Real.rpow t0 q * Real.rpow |X o| p)) ν := by
    exact (integrable_const (1 : ℝ)).sub
      ((hXsq.const_mul t0).sub (hXInt.const_mul (Real.rpow t0 q)))
  have hLLinear : L ≤ 1 - 3 * t0 / 4 := by
    calc
      L ≤ ∫ o, 1 - (t0 * X o ^ 2 - Real.rpow t0 q * Real.rpow |X o| p) ∂ν :=
        integral_mono_ae hfInt hUpperInt (Filter.Eventually.of_forall hPointwise)
      _ = 1 - (t0 * (∫ o, X o ^ 2 ∂ν) -
          Real.rpow t0 q * (∫ o, Real.rpow |X o| p ∂ν)) := by
        calc
          (∫ o, 1 - (t0 * X o ^ 2 -
              Real.rpow t0 q * Real.rpow |X o| p) ∂ν) =
              (∫ _ : Ω, (1 : ℝ) ∂ν) -
                (∫ o, t0 * X o ^ 2 -
                  Real.rpow t0 q * Real.rpow |X o| p ∂ν) :=
            integral_sub (integrable_const (1 : ℝ))
              ((hXsq.const_mul t0).sub (hXInt.const_mul (Real.rpow t0 q)))
          _ = (∫ _ : Ω, (1 : ℝ) ∂ν) -
              ((∫ o, t0 * X o ^ 2 ∂ν) -
                (∫ o, Real.rpow t0 q * Real.rpow |X o| p ∂ν)) := by
            congr 1
            exact integral_sub (hXsq.const_mul t0)
              (hXInt.const_mul (Real.rpow t0 q))
          _ = 1 - (t0 * (∫ o, X o ^ 2 ∂ν) -
              Real.rpow t0 q * (∫ o, Real.rpow |X o| p ∂ν)) := by
            rw [integral_const_mul, integral_const_mul, integral_const]
            simp only [probReal_univ, smul_eq_mul, one_mul]
      _ ≤ 1 - (t0 - Real.rpow t0 q * (2 * β)) := by
        rw [hNormalization]
        have hBound := mul_le_mul_of_nonneg_left hMomentBound
          (Real.rpow_nonneg ht0Pos.le q)
        change Real.rpow t0 q * (∫ o, Real.rpow |X o| p ∂ν) ≤
          Real.rpow t0 q * (2 * β) at hBound
        linarith only [hBound]
      _ = 1 - 3 * t0 / 4 := by
        rw [mul_comm (Real.rpow t0 q) (2 * β), hTqQuarter]
        ring
  have hLDecay : L ≤ Real.exp (-3 * t0 / 4) := by
    apply hLLinear.trans
    have hLower := Real.add_one_le_exp (-3 * t0 / 4)
    linarith only [hLower]
  refine ⟨hfm, hfInt, hLNonneg, hLLinear, hLDecay, ?_⟩
  intro m
  let Pm : Measure (Fin m → Ω) := Measure.pi (fun _ : Fin m => ν)
  let S : (Fin m → Ω) → ℝ := fun o => ∑ i : Fin m, X (o i) ^ 2
  let Fm : (Fin m → Ω) → ℝ := fun o => Real.exp (-t0 * S o)
  let εm : ℝ := Real.exp (-t0 * (m : ℝ) / 2)
  let E : Set (Fin m → Ω) := {o : Fin m → Ω | S o ≤ (m : ℝ) / 2}
  haveI : IsProbabilityMeasure Pm :=
    MeasureTheory.Measure.pi.instIsProbabilityMeasure (fun _ : Fin m => ν)
  have hSm : Measurable S := by
    exact Finset.measurable_fun_sum (Finset.univ : Finset (Fin m))
      (fun i _ => (hXm.comp (measurable_pi_apply i)).pow_const (2 : ℕ))
  have hEm : MeasurableSet E := measurableSet_le hSm measurable_const
  have hFmm : Measurable Fm := (hSm.const_mul (-t0)).exp
  have hFactor : Fm = (fun o => ∏ i : Fin m, f (o i)) := by
    funext o
    calc
      Fm o = Real.exp (∑ i : Fin m, -t0 * X (o i) ^ 2) := by
        dsimp only [Fm, S]
        congr 1
        rw [Finset.mul_sum]
      _ = ∏ i : Fin m, f (o i) := by
        simpa only [f] using
          Real.exp_sum (Finset.univ : Finset (Fin m))
            (fun i : Fin m => -t0 * X (o i) ^ 2)
  have hFmInt : Integrable Fm Pm := by
    rw [hFactor]
    change Integrable (fun o : Fin m → Ω => ∏ i : Fin m, f (o i))
      (Measure.pi (fun _ : Fin m => ν))
    exact Integrable.fin_nat_prod (μ := fun _ : Fin m => ν)
      (f := fun _ : Fin m => f) (fun _ => hfInt)
  have hIntegral : (∫ o, Fm o ∂Pm) = L ^ m := by
    rw [hFactor]
    change (∫ o : Fin m → Ω, ∏ i : Fin m, f (o i)
      ∂(Measure.pi (fun _ : Fin m => ν))) = L ^ m
    simpa only [Fintype.card_fin] using
      (integral_fintype_prod_eq_pow (ι := Fin m) (μ := ν) f)
  have hIntegralBound : (∫ o, Fm o ∂Pm) ≤
      Real.exp (-3 * t0 * (m : ℝ) / 4) := by
    calc
      (∫ o, Fm o ∂Pm) = L ^ m := hIntegral
      _ ≤ (Real.exp (-3 * t0 / 4)) ^ m :=
        hNaturalPowerOrder L (Real.exp (-3 * t0 / 4)) hLNonneg hLDecay m
      _ = Real.exp (-3 * t0 * (m : ℝ) / 4) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hεPos : 0 < εm := Real.exp_pos _
  have hClosedInMarkov : E ⊆ {o : Fin m → Ω | εm ≤ Fm o} := by
    intro o ho
    have hSo : S o ≤ (m : ℝ) / 2 := ho
    change Real.exp (-t0 * (m : ℝ) / 2) ≤ Real.exp (-t0 * S o)
    apply hExpOrder
    have hMul := mul_le_mul_of_nonneg_left hSo ht0Pos.le
    linarith only [hMul]
  have hStrictEnergySubset :
      {o : Fin m → Ω | S o < (m : ℝ) / 2} ⊆ E := by
    intro o ho
    have hSo : S o < (m : ℝ) / 2 := ho
    exact hSo.le
  have hStrictSourceSubset : 0 < m →
      {o : Fin m → Ω | S o / (m : ℝ) < (1 / 2 : ℝ)} ⊆ E := by
    intro hm o ho
    have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
    apply hStrictEnergySubset
    have hSo := (div_lt_iff₀ hmReal).1 ho
    change S o < (m : ℝ) / 2
    linarith only [hSo]
  have hMeasure : Pm.real E ≤ Pm.real {o : Fin m → Ω | εm ≤ Fm o} :=
    measureReal_mono hClosedInMarkov
  have hMarkov := mul_meas_ge_le_integral_of_nonneg (μ := Pm) (f := Fm)
    (Filter.Eventually.of_forall (fun o => (Real.exp_pos (-t0 * S o)).le)) hFmInt εm
  have hProductBound : εm * Pm.real E ≤ Real.exp (-3 * t0 * (m : ℝ) / 4) :=
    (mul_le_mul_of_nonneg_left hMeasure hεPos.le).trans
      (hMarkov.trans hIntegralBound)
  have hClosedBound : Pm.real E ≤ Real.exp (-c0 * (m : ℝ)) := by
    calc
      Pm.real E ≤ Real.exp (-3 * t0 * (m : ℝ) / 4) / εm := by
        apply (le_div_iff₀ hεPos).2
        simpa only [mul_comm εm (Pm.real E)] using hProductBound
      _ = Real.exp (-c0 * (m : ℝ)) := by
        dsimp only [εm, c0]
        rw [← Real.exp_sub]
        congr 1
        ring
  exact ⟨inferInstance, hSm, hEm, hFmm, hFmInt, hεPos,
    hIntegral, hIntegralBound, hClosedBound⟩

end

end Shao.OQ6.ConditionalStandardizedLowEnergy
