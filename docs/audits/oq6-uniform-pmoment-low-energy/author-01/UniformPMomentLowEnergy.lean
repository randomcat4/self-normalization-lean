import Shao.OQ6.ConditionalStandardizedLowEnergy
import Shao.OQ6.OriginalLowEnergyTail
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
universe u
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology MeasureTheory

namespace Shao.OQ6.UniformPMomentLowEnergy
noncomputable section
theorem actual_uniform_pmoment_low_energy
    (p : ℝ) (hp2 : 2 < p) (hp3 : p ≤ 3)
    (B : ℝ) (hB : 1 ≤ B) :
    let q : ℝ := p / 2
    let tB : ℝ := Real.rpow (1 / (4 * B)) (2 / (p - 2))
    let cg : ℝ := tB / 4
    1 < q ∧ q ≤ (3 / 2 : ℝ) ∧
      0 < tB ∧ tB ≤ 1 ∧ 0 < cg ∧
      B * Real.rpow tB (q - 1) = (1 / 4 : ℝ) ∧
      ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
        (hgsecond : (∫ o : Ω, g o ^ (2 : ℕ) ∂μ) = 1)
        (hgp : Integrable (fun o : Ω => Real.rpow |g o| p) μ)
        (hβBound : (∫ o : Ω, Real.rpow |g o| p ∂μ) ≤ B),
        let f : Ω → ℝ := fun o => Real.exp (-tB * g o ^ (2 : ℕ))
        let L : ℝ := ∫ o : Ω, f o ∂μ
        Measurable f ∧ Integrable f μ ∧ 0 ≤ L ∧
          L ≤ 1 - 3 * tB / 4 ∧ L ≤ Real.exp (-3 * tB / 4) ∧
          ∀ n : ℕ,
            let mN : MeasurableSpace (Fin n → Ω) :=
              @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => mΩ)
            let P : @Measure (Fin n → Ω) mN :=
              @Measure.pi (Fin n) (fun _ : Fin n => Ω) (Fin.fintype n)
                (fun _ : Fin n => mΩ) (fun _ : Fin n => μ)
            let S : (Fin n → Ω) → ℝ := fun ζ => ∑ i : Fin n, g (ζ i) ^ (2 : ℕ)
            let F : (Fin n → Ω) → ℝ := fun ζ => Real.exp (-tB * S ζ)
            IsProbabilityMeasure P ∧ Measurable S ∧
              MeasurableSet {ζ : Fin n → Ω | S ζ ≤ (n : ℝ) / 2} ∧
              Measurable F ∧ Integrable F P ∧
              (∫ ζ : Fin n → Ω, F ζ ∂P) = L ^ n ∧
              (∫ ζ : Fin n → Ω, F ζ ∂P) ≤ Real.exp (-3 * tB * (n : ℝ) / 4) ∧
              P.real {ζ : Fin n → Ω | S ζ ≤ (n : ℝ) / 2} ≤
                Real.exp (-cg * (n : ℝ))
:= by
  set_option maxHeartbeats 800000 in
    classical
    intro q tB cg
    have hBPos : 0 < B := lt_of_lt_of_le zero_lt_one hB
    have hpminus : 0 < p - 2 := by linarith only [hp2]
    have hqLower : 1 < q := by dsimp only [q]; linarith only [hp2]
    have hqUpper : q ≤ (3 / 2 : ℝ) := by dsimp only [q]; linarith only [hp3]
    have hqTwo : q ≤ 2 := by linarith only [hqUpper]
    have hbasePos : 0 < 1 / (4 * B) :=
      div_pos zero_lt_one (mul_pos (by norm_num) hBPos)
    have hbaseOne : 1 / (4 * B) ≤ 1 := by
      apply (div_le_one (mul_pos (by norm_num : (0 : ℝ) < 4) hBPos)).2
      linarith only [hB]
    have hExponentPos : 0 < 2 / (p - 2) := div_pos (by norm_num) hpminus
    have htBPos : 0 < tB := Real.rpow_pos_of_pos hbasePos _
    have htBOne : tB ≤ 1 :=
      Real.rpow_le_one hbasePos.le hbaseOne hExponentPos.le
    have hcgPos : 0 < cg := div_pos htBPos (by norm_num)
    have hTpower : Real.rpow tB (q - 1) = 1 / (4 * B) := by
      dsimp only [tB]
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_mul hbasePos.le]
      have hExponent : (2 / (p - 2)) * (q - 1) = 1 := by
        dsimp only [q]
        field_simp [hpminus.ne'] <;> ring
      rw [hExponent, Real.rpow_one]
    have hQuarter : B * Real.rpow tB (q - 1) = (1 / 4 : ℝ) := by
      rw [hTpower]
      field_simp [hBPos.ne'] <;> ring
    have hTq : Real.rpow tB q = Real.rpow tB (q - 1) * tB := by
      have hExponent : q = (q - 1) + 1 := by ring
      calc
        Real.rpow tB q = Real.rpow tB ((q - 1) + 1) := by rw [← hExponent]
        _ = Real.rpow tB (q - 1) * tB := by
          simpa only [Real.rpow_eq_pow, Real.rpow_one] using
            Real.rpow_add htBPos (q - 1) 1
    have hTqQuarter : B * Real.rpow tB q = tB / 4 := by
      calc
        B * Real.rpow tB q =
            (B * Real.rpow tB (q - 1)) * tB := by rw [hTq]; ring
        _ = (1 / 4 : ℝ) * tB := by rw [hQuarter]
        _ = tB / 4 := by ring
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
    have hScalar : ∀ q' z : ℝ, 1 ≤ q' → q' ≤ 2 → 0 ≤ z →
        Real.exp (-z) ≤ 1 - z + Real.rpow z q' := by
      intro q' z hqLower' hqUpper' hz
      by_cases hzZero : z = 0
      · subst z
        have hqNonzero : q' ≠ 0 := by linarith only [hqLower']
        simp only [neg_zero, Real.exp_zero, sub_zero, Real.rpow_eq_pow,
          Real.zero_rpow hqNonzero, add_zero, le_refl]
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
      · have hPower : z ^ 2 ≤ Real.rpow z q' := by
          simpa only [Real.rpow_eq_pow, Real.rpow_ofNat] using
            (Real.rpow_le_rpow_of_exponent_ge
              (x := z) (y := (2 : ℝ)) (z := q') hzPos hzOne hqUpper')
        have hFraction : z ^ 2 / (1 + z) ≤ z ^ 2 := by
          apply (div_le_iff₀ hDen).2
          nlinarith only [mul_nonneg (sq_nonneg z) hz]
        have hIdentity : 1 / (1 + z) = 1 - z + z ^ 2 / (1 + z) := by
          field_simp [hDen.ne'] <;> ring
        calc
          Real.exp (-z) ≤ 1 / (1 + z) := hReciprocal
          _ = 1 - z + z ^ 2 / (1 + z) := hIdentity
          _ ≤ 1 - z + z ^ 2 := by
            simpa only [add_comm] using (add_le_add_left hFraction (1 - z))
          _ ≤ 1 - z + Real.rpow z q' := by
            simpa only [add_comm] using (add_le_add_left hPower (1 - z))
      · have hzGeOne : 1 ≤ z := le_of_lt (lt_of_not_ge hzOne)
        have hPower : z ≤ Real.rpow z q' := by
          simpa only [Real.rpow_eq_pow, Real.rpow_one] using
            (Real.rpow_le_rpow_of_exponent_le
              (x := z) (y := (1 : ℝ)) (z := q') hzGeOne hqLower')
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
    refine ⟨hqLower, hqUpper, htBPos, htBOne, hcgPos, hQuarter, ?_⟩
    intro Ω mΩ μ hμ g hg hg2 hgsecond hgp hβBound f L
    have hgsq : Integrable (fun o : Ω => g o ^ (2 : ℕ)) μ := hg2.integrable_sq
    have hfm : Measurable f := ((hg.pow_const (2 : ℕ)).const_mul (-tB)).exp
    have hfNonneg : ∀ o : Ω, 0 ≤ f o := fun o => (Real.exp_pos _).le
    have hfOne : ∀ o : Ω, f o ≤ 1 := by
      intro o
      have hExp := hExpOrder (-tB * g o ^ 2) 0
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr htBPos.le) (sq_nonneg (g o)))
      simpa only [f, Real.exp_zero] using hExp
    have hfInt : Integrable f μ := by
      apply (integrable_const (1 : ℝ)).mono' hfm.aestronglyMeasurable
      exact Filter.Eventually.of_forall (fun o => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hfNonneg o)]
        exact hfOne o)
    have hLNonneg : 0 ≤ L := integral_nonneg hfNonneg
    have hPointwise : ∀ o : Ω, f o ≤
        1 - (tB * g o ^ 2 - Real.rpow tB q * Real.rpow |g o| p) := by
      intro o
      have hProduct : Real.rpow (tB * g o ^ 2) q =
          Real.rpow tB q * Real.rpow (g o ^ 2) q := by
        simpa only [Real.rpow_eq_pow] using
          (Real.mul_rpow htBPos.le (sq_nonneg (g o)) (z := q))
      have hSquarePower : Real.rpow (g o ^ 2) q = Real.rpow |g o| p := by
        simp only [Real.rpow_eq_pow]
        rw [← sq_abs, ← Real.rpow_ofNat |g o| 2,
          ← Real.rpow_mul (abs_nonneg (g o))]
        have hTwoq : (2 : ℝ) * q = p := by dsimp only [q]; ring
        rw [hTwoq]
      calc
        f o = Real.exp (-(tB * g o ^ 2)) := by
          dsimp only [f]
          congr 1
          ring
        _ ≤ 1 - tB * g o ^ 2 + Real.rpow (tB * g o ^ 2) q :=
          hScalar q (tB * g o ^ 2) hqLower.le hqTwo
            (mul_nonneg htBPos.le (sq_nonneg (g o)))
        _ = 1 - (tB * g o ^ 2 - Real.rpow tB q * Real.rpow |g o| p) := by
          rw [hProduct, hSquarePower]
          ring
    have hUpperInt : Integrable
        (fun o : Ω => 1 - (tB * g o ^ 2 - Real.rpow tB q * Real.rpow |g o| p)) μ := by
      exact (integrable_const (1 : ℝ)).sub
        ((hgsq.const_mul tB).sub (hgp.const_mul (Real.rpow tB q)))
    have hLLinear : L ≤ 1 - 3 * tB / 4 := by
      calc
        L ≤ ∫ o : Ω, 1 - (tB * g o ^ 2 - Real.rpow tB q * Real.rpow |g o| p) ∂μ :=
          integral_mono_ae hfInt hUpperInt (Filter.Eventually.of_forall hPointwise)
        _ = 1 - (tB * (∫ o : Ω, g o ^ 2 ∂μ) -
            Real.rpow tB q * (∫ o : Ω, Real.rpow |g o| p ∂μ)) := by
          calc
            (∫ o : Ω, 1 - (tB * g o ^ 2 -
                Real.rpow tB q * Real.rpow |g o| p) ∂μ) =
                (∫ _ : Ω, (1 : ℝ) ∂μ) -
                  (∫ o : Ω, tB * g o ^ 2 -
                    Real.rpow tB q * Real.rpow |g o| p ∂μ) :=
              integral_sub (integrable_const (1 : ℝ))
                ((hgsq.const_mul tB).sub (hgp.const_mul (Real.rpow tB q)))
            _ = (∫ _ : Ω, (1 : ℝ) ∂μ) -
                ((∫ o : Ω, tB * g o ^ 2 ∂μ) -
                  (∫ o : Ω, Real.rpow tB q * Real.rpow |g o| p ∂μ)) := by
              congr 1
              exact integral_sub (hgsq.const_mul tB)
                (hgp.const_mul (Real.rpow tB q))
            _ = 1 - (tB * (∫ o : Ω, g o ^ 2 ∂μ) -
                Real.rpow tB q * (∫ o : Ω, Real.rpow |g o| p ∂μ)) := by
              rw [integral_const_mul, integral_const_mul, integral_const]
              simp only [probReal_univ, smul_eq_mul, one_mul]
        _ ≤ 1 - (tB - Real.rpow tB q * B) := by
          rw [hgsecond]
          have hBound := mul_le_mul_of_nonneg_left hβBound
            (Real.rpow_nonneg htBPos.le q)
          linarith only [hBound]
        _ = 1 - 3 * tB / 4 := by
          rw [mul_comm (Real.rpow tB q) B, hTqQuarter]
          ring
    have hLDecay : L ≤ Real.exp (-3 * tB / 4) := by
      apply hLLinear.trans
      linarith only [Real.add_one_le_exp (-3 * tB / 4)]
    refine ⟨hfm, hfInt, hLNonneg, hLLinear, hLDecay, ?_⟩
    intro n mN P S F
    let ε : ℝ := Real.exp (-tB * (n : ℝ) / 2)
    let E : Set (Fin n → Ω) := {ζ : Fin n → Ω | S ζ ≤ (n : ℝ) / 2}
    haveI : IsProbabilityMeasure P := by
      dsimp only [P, mN]
      infer_instance
    have hSm : Measurable S := by
      exact Finset.measurable_fun_sum (Finset.univ : Finset (Fin n))
        (fun i _ => (hg.comp (measurable_pi_apply i)).pow_const (2 : ℕ))
    have hEm : MeasurableSet E := measurableSet_le hSm measurable_const
    have hFmm : Measurable F := (hSm.const_mul (-tB)).exp
    have hFactor : F = (fun ζ => ∏ i : Fin n, f (ζ i)) := by
      funext ζ
      calc
        F ζ = Real.exp (∑ i : Fin n, -tB * g (ζ i) ^ 2) := by
          dsimp only [F, S]
          congr 1
          rw [Finset.mul_sum]
        _ = ∏ i : Fin n, f (ζ i) := by
          simpa only [f] using
            Real.exp_sum (Finset.univ : Finset (Fin n))
              (fun i : Fin n => -tB * g (ζ i) ^ 2)
    have hFInt : Integrable F P := by
      rw [hFactor]
      change Integrable (fun ζ : Fin n → Ω => ∏ i : Fin n, f (ζ i))
        (Measure.pi (fun _ : Fin n => μ))
      exact Integrable.fin_nat_prod (μ := fun _ : Fin n => μ)
        (f := fun _ : Fin n => f) (fun _ => hfInt)
    have hIntegral : (∫ ζ : Fin n → Ω, F ζ ∂P) = L ^ n := by
      rw [hFactor]
      change (∫ ζ : Fin n → Ω, ∏ i : Fin n, f (ζ i)
        ∂(Measure.pi (fun _ : Fin n => μ))) = L ^ n
      simpa only [Fintype.card_fin] using
        (integral_fintype_prod_eq_pow (ι := Fin n) (μ := μ) f)
    have hIntegralBound : (∫ ζ : Fin n → Ω, F ζ ∂P) ≤
        Real.exp (-3 * tB * (n : ℝ) / 4) := by
      calc
        (∫ ζ : Fin n → Ω, F ζ ∂P) = L ^ n := hIntegral
        _ ≤ (Real.exp (-3 * tB / 4)) ^ n :=
          hNaturalPowerOrder L (Real.exp (-3 * tB / 4)) hLNonneg hLDecay n
        _ = Real.exp (-3 * tB * (n : ℝ) / 4) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
    have hεPos : 0 < ε := Real.exp_pos _
    have hClosedInMarkov : E ⊆ {ζ : Fin n → Ω | ε ≤ F ζ} := by
      intro ζ hζ
      have hSζ : S ζ ≤ (n : ℝ) / 2 := hζ
      change Real.exp (-tB * (n : ℝ) / 2) ≤ Real.exp (-tB * S ζ)
      apply hExpOrder
      have hMul := mul_le_mul_of_nonneg_left hSζ htBPos.le
      linarith only [hMul]
    have hMeasure : P.real E ≤ P.real {ζ : Fin n → Ω | ε ≤ F ζ} :=
      measureReal_mono hClosedInMarkov
    have hMarkov := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := F)
      (Filter.Eventually.of_forall (fun ζ => (Real.exp_pos (-tB * S ζ)).le)) hFInt ε
    have hProductBound : ε * P.real E ≤ Real.exp (-3 * tB * (n : ℝ) / 4) :=
      (mul_le_mul_of_nonneg_left hMeasure hεPos.le).trans
        (hMarkov.trans hIntegralBound)
    have hClosedBound : P.real E ≤ Real.exp (-cg * (n : ℝ)) := by
      calc
        P.real E ≤ Real.exp (-3 * tB * (n : ℝ) / 4) / ε := by
          apply (le_div_iff₀ hεPos).2
          simpa only [mul_comm ε (P.real E)] using hProductBound
        _ = Real.exp (-cg * (n : ℝ)) := by
          dsimp only [ε, cg]
          rw [← Real.exp_sub]
          congr 1
          ring
    exact ⟨inferInstance, hSm, hEm, hFmm, hFInt, hIntegral, hIntegralBound,
      hClosedBound⟩
end
end Shao.OQ6.UniformPMomentLowEnergy
