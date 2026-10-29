import Shao.OQ6.UniformPMomentLowEnergy
import Shao.OQ5.P51.ClippedStudentizer
import Shao.OQ6.OriginalGoodEventBridge
import Mathlib.MeasureTheory.Measure.Real

set_option autoImplicit false
universe u
open Filter MeasureTheory
open scoped BigOperators ENNReal
open Shao.OQ5.P51
open Shao.OQ6.BoundedProductEnvelopeTails (tailScale)
open Shao.OQ6.CanonicalDoubleGhostRowMoments (sampleLaw originalRows)
open Shao.OQ6.CanonicalDoubleGhostScalarMoments (originalUpper)

namespace Shao.OQ6.UniformPMomentActualGoodsetFrontier
noncomputable section
theorem uniform_pmoment_original_boundedPolylog_goodset_frontier
    (p : ℝ) (hp2 : 2 < p) (hp3 : p ≤ 3)
    (B : ℝ) (hB : 1 ≤ B) :
    let tB : ℝ := Real.rpow (1 / (4 * B)) (2 / (p - 2))
    let cg : ℝ := tB / 4
    0 < cg ∧
      ∀ (C a t0 M : ℝ)
        (hC : 0 ≤ C) (ha : 0 ≤ a) (ht0 : 0 < t0) (hM : 0 ≤ M),
        ∃ N : ℕ, 4 ≤ N ∧
          ∀ (n : ℕ), N ≤ n →
            ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω]
              (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]
              (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
              (hgmean : (∫ o : Ω, g o ∂μ) = 0)
              (hgsecond : (∫ o : Ω, (g o) ^ (2 : ℕ) ∂μ) = 1)
              (hgp : Integrable (fun o : Ω => Real.rpow |g o| p) μ)
              (hβBound : (∫ o : Ω, Real.rpow |g o| p ∂μ) ≤ B)
              (r : Ω → Ω → ℝ) (w : Ω → ℝ)
              (hr : Measurable (Function.uncurry r))
              (hr1 : Integrable (Function.uncurry r) (μ.prod μ))
              (hcR : ∀ᵐ o : Ω ∂μ, (∫ o' : Ω, r o o' ∂μ) = 0)
              (hcL : ∀ᵐ o' : Ω ∂μ, (∫ o : Ω, r o o' ∂μ) = 0)
              (hW : ∀ᵐ o : Ω ∂μ, 0 ≤ w o)
              (hWR : ∀ᵐ o : Ω ∂μ, w o ≤ boundedPolylogHeight C a n)
              (hSq : Integrable (fun o : Ω => (w o) ^ (2 : ℕ)) μ)
              (hSqBound : (∫ o : Ω, (w o) ^ (2 : ℕ) ∂μ) ≤ M)
              (hEnv : ∀ᵐ o : Ω × Ω ∂μ.prod μ,
                |r o.1 o.2| ≤ w o.1 * w o.2)
              (hsym : ∀ o o' : Ω, r o o' = r o' o)
              (C0 rho z : ℝ) (hC0 : 0 ≤ C0) (hrho : 0 ≤ rho)
              (hz : (1 : ℝ) ≤ z)
              (hzWindow : z ≤ remainderWindowScale (tailScale M) t0 *
                Real.rpow (n : ℝ) (1 / 6 : ℝ)),
              let q : ℝ := boundedPolylogMomentOrder t0 n
              let K : ℝ := tailScale M
              let G : Set (Fin n → Ω) := projectionGood n g z
              let C2 : Set (Fin n → Ω) :=
                {x : Fin n → Ω |
                  |originalUpper n r x| ≤ K * (n : ℝ) * q ∧
                  ‖originalRows n r x‖ ^ (2 : ℕ) ≤
                    K * (n : ℝ) ^ (2 : ℕ) * q}
              let H : Set (Fin n → Ω) := G ∩ C2
              let e1 : (Fin n → Ω) → ℝ :=
                fun x : Fin n → Ω => clippedCenteredDelta n g r C0 rho 1 x
              MeasurableSet H ∧
                (∀ x : Fin n → Ω, x ∈ H →
                  0 < projectionV n g x ∧
                  (1 / 2 : ℝ) ≤ projectionEnergy n g x ∧
                  z * |residualStatisticD n r x| ≤ projectionV n g x / 8 ∧
                  z * |residualStatisticD n r x| < projectionV n g x / 4 ∧
                  z ^ (2 : ℕ) * |centeredDelta n g r x| ≤ (1 / 32 : ℝ) ∧
                  |centeredDelta n g r x| ≤ (1 / 32 : ℝ) ∧
                  -(1 / 8 : ℝ) < centeredDelta n g r x ∧
                  |e1 x| ≤ |centeredDelta n g r x| ∧
                  z ^ (2 : ℕ) * |e1 x| ≤ (1 / 32 : ℝ) ∧
                  z ^ (2 : ℕ) * |e1 x| < (1 / 8 : ℝ) ∧
                  |e1 x| ≤ (1 / 32 : ℝ) ∧
                  0 < projectionV n g x * Real.sqrt (1 + e1 x) ∧
                  0 < Real.sqrt (centeredSq n g r x) ∧
                  Real.sqrt (centeredSq n g r x) =
                    projectionV n g x *
                      Real.sqrt (1 + centeredDelta n g r x)) ∧
                (({x : Fin n → Ω | projectionV n g x = 0} ∪
                    {x : Fin n → Ω | Real.sqrt (centeredSq n g r x) = 0}) ⊆ Hᶜ) ∧
                (sampleLaw n μ).real Hᶜ ≤
                  (3 : ℝ) * Real.exp (-q) + Real.exp (-cg * (n : ℝ)) +
                    (4 : ℝ) * Real.exp (-(z * Real.sqrt (n : ℝ)) / (2 : ℝ))
:= by
  set_option maxHeartbeats 800000 in
    classical
    intro tB cg
    rcases Shao.OQ6.UniformPMomentLowEnergy.actual_uniform_pmoment_low_energy.{u}
      p hp2 hp3 B hB with ⟨_, _, _, _, hcg, _, hLowAll⟩
    refine ⟨hcg, ?_⟩
    intro C a t0 M hC ha ht0 hM
    have hConcEventually :=
      eventually_boundedPolylog_product_joint_failure.{u} C a t0 M hC ha ht0 hM
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hConcEventually
    refine ⟨max 4 N0, le_max_left 4 N0, ?_⟩
    intro n hn Ω mΩ μ hμ g hg hg2 hgmean hgsecond hgp hβBound
      r w hr hr1 hcR hcL hW hWR hSq hSqBound hEnv hsym
      C0 rho z hC0 hrho hz hzWindow
    have hn4 : 4 ≤ n := (le_max_left 4 N0).trans hn
    have hConc := hN0 n ((le_max_right 4 N0).trans hn)
    let q : ℝ := boundedPolylogMomentOrder t0 n
    let K : ℝ := tailScale M
    let G : Set (Fin n → Ω) := projectionGood n g z
    let C2 : Set (Fin n → Ω) :=
      {x : Fin n → Ω |
        |originalUpper n r x| ≤ K * (n : ℝ) * q ∧
        ‖originalRows n r x‖ ^ (2 : ℕ) ≤ K * (n : ℝ) ^ (2 : ℕ) * q}
    let H : Set (Fin n → Ω) := G ∩ C2
    let e1 : (Fin n → Ω) → ℝ :=
      fun x : Fin n → Ω => clippedCenteredDelta n g r C0 rho 1 x
    let Pn : Measure (Fin n → Ω) := sampleLaw n μ
    letI instSample : IsProbabilityMeasure (sampleLaw n μ) :=
      inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => μ)))
    have hnpos : 0 < n := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 4) hn4
    have hKpos : 0 < K :=
      (Shao.OQ6.BoundedProductEnvelopeTails.bounded_scales_pos M hM).2.2.2.2.2
    -- The low-energy witness was selected before all model data.
    have hLowClosed :
        Pn.real {x : Fin n → Ω |
          Shao.OQ6.OriginalGhostGoodEvent.sampleEnergy n g x ≤ (n : ℝ) / 2} ≤
          Real.exp (-cg * (n : ℝ)) := by
      rcases hLowAll μ g hg hg2 hgsecond hgp hβBound with
        ⟨_, _, _, _, _, hProductAll⟩
      rcases hProductAll n with ⟨_, _, _, _, _, _, _, hClosed⟩
      simpa only [Pn, sampleLaw,
        Shao.OQ6.OriginalGhostGoodEvent.sampleEnergy] using hClosed
    -- Keep the explicit common cg instead of the old model-selected witness.
    have hNormalized :
        Pn.real (Shao.OQ6.OriginalGoodEventProbability.normalizedGoodEvent n g z)ᶜ ≤
          Real.exp (-cg * (n : ℝ)) +
            (4 : ℝ) * Real.exp (-(z * Real.sqrt (n : ℝ)) / (2 : ℝ)) := by
      let E : (Fin n → Ω) → ℝ :=
        fun x : Fin n → Ω => Shao.OQ6.OriginalGhostGoodEvent.sampleEnergy n g x
      let S : (Fin n → Ω) → ℝ :=
        fun x : Fin n → Ω => Shao.OQ6.OriginalGhostGoodEvent.sampleSum n g x
      let T : (Fin n → Ω) → ℝ :=
        fun x : Fin n → Ω => Real.sqrt z * Real.rpow (n : ℝ) ((1 : ℝ) / 4) *
          ((4 : ℝ) + Real.sqrt (E x / (n : ℝ)))
      let A : Set (Fin n → Ω) := {x : Fin n → Ω | E x < (n : ℝ) / 2}
      let U : Set (Fin n → Ω) :=
        {x : Fin n → Ω | T x < |S x / Real.sqrt (n : ℝ)|}
      have hNpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos
      have hLowPoint : ∀ x : Fin n → Ω,
          E x / (n : ℝ) < (1 / 2 : ℝ) ↔ E x < (n : ℝ) / 2 := by
        intro x
        rw [div_lt_iff₀ hNpos]
        rw [show (1 / 2 : ℝ) * (n : ℝ) = (n : ℝ) / 2 by ring]
      have hComplementEq :
          (Shao.OQ6.OriginalGoodEventProbability.normalizedGoodEvent n g z)ᶜ =
            A ∪ U := by
        ext x
        change ¬ ((1 / 2 : ℝ) ≤ E x / (n : ℝ) ∧
          |S x / Real.sqrt (n : ℝ)| ≤ T x) ↔
            E x < (n : ℝ) / 2 ∨ T x < |S x / Real.sqrt (n : ℝ)|
        rw [not_and_or, not_le, not_le, hLowPoint x]
      have hLowSubset : A ⊆ {x : Fin n → Ω |
          Shao.OQ6.OriginalGhostGoodEvent.sampleEnergy n g x ≤ (n : ℝ) / 2} := by
        intro x hx
        exact le_of_lt hx
      have hLow : Pn.real A ≤ Real.exp (-cg * (n : ℝ)) :=
        (MeasureTheory.measureReal_mono (μ := Pn) hLowSubset).trans hLowClosed
      have hUpper : Pn.real U ≤
          (4 : ℝ) * Real.exp (-(z * Real.sqrt (n : ℝ)) / (2 : ℝ)) := by
        exact Shao.OQ6.OriginalNormalizedUpperTail.original_normalized_upper_tail
          n hnpos μ g hg hg2 hgmean hgsecond z hz
      calc
        Pn.real (Shao.OQ6.OriginalGoodEventProbability.normalizedGoodEvent n g z)ᶜ =
            Pn.real (A ∪ U) :=
          congrArg (fun V : Set (Fin n → Ω) => Pn.real V) hComplementEq
        _ ≤ Pn.real A + Pn.real U :=
          MeasureTheory.measureReal_union_le (μ := Pn) A U
        _ ≤ Real.exp (-cg * (n : ℝ)) +
            (4 : ℝ) * Real.exp (-(z * Real.sqrt (n : ℝ)) / (2 : ℝ)) :=
          add_le_add hLow hUpper
    -- H consists of the original finite measurable observables.
    let gi : Fin n → (Fin n → Ω) → ℝ :=
      fun (i : Fin n) (x : Fin n → Ω) => g (x i)
    let rij : Fin n → Fin n → (Fin n → Ω) → ℝ :=
      fun (i j : Fin n) (x : Fin n → Ω) => r (x i) (x j)
    let rowSum : Fin n → (Fin n → Ω) → ℝ :=
      fun (i : Fin n) (x : Fin n → Ω) =>
        ∑ j : Fin n, if i = j then 0 else r (x i) (x j)
    let rowEnergy : (Fin n → Ω) → ℝ :=
      fun x : Fin n → Ω => ∑ i : Fin n, (rowSum i x) ^ (2 : ℕ)
    let F : (Fin n → Ω) → ℝ := fun x : Fin n → Ω => originalUpper n r x
    let E : (Fin n → Ω) → ℝ := fun x : Fin n → Ω => projectionEnergy n g x
    let W : (Fin n → Ω) → ℝ := fun x : Fin n → Ω => projectionW n g x
    let V : (Fin n → Ω) → ℝ := fun x : Fin n → Ω => projectionV n g x
    have hGi : ∀ i : Fin n, Measurable (gi i) := by
      intro i
      exact hg.comp (measurable_pi_apply i)
    have hRij : ∀ i j : Fin n, Measurable (rij i j) := by
      intro i j
      change Measurable ((Function.uncurry r) ∘
        (fun x : Fin n → Ω => (x i, x j)))
      exact hr.comp
        (show Measurable (fun x : Fin n → Ω => (x i, x j)) from
          (measurable_pi_apply i).prodMk (measurable_pi_apply j))
    have hRowSum : ∀ i : Fin n, Measurable (rowSum i) := by
      intro i
      change Measurable (fun x : Fin n → Ω =>
        ∑ j : Fin n, if i = j then (0 : ℝ) else r (x i) (x j))
      refine Finset.measurable_fun_sum (Finset.univ : Finset (Fin n))
        (fun j _ => ?_)
      by_cases hij : i = j
      · simpa only [if_pos hij] using
          (measurable_const : Measurable (fun _ : Fin n → Ω => (0 : ℝ)))
      · simpa only [if_neg hij] using hRij i j
    have hRowEnergy : Measurable rowEnergy := by
      change Measurable (fun x : Fin n → Ω =>
        ∑ i : Fin n, (rowSum i x) ^ (2 : ℕ))
      exact Finset.measurable_fun_sum (Finset.univ : Finset (Fin n))
        (fun i _ => (hRowSum i).pow_const (2 : ℕ))
    have hRowIdentity : ∀ x : Fin n → Ω,
        ‖originalRows n r x‖ ^ (2 : ℕ) = rowEnergy x := by
      intro x
      rw [EuclideanSpace.real_norm_sq_eq]
      rfl
    have hRowsMeas : Measurable
        (fun x : Fin n → Ω => ‖originalRows n r x‖ ^ (2 : ℕ)) := by
      have hEq : (fun x : Fin n → Ω =>
          ‖originalRows n r x‖ ^ (2 : ℕ)) = rowEnergy := funext hRowIdentity
      rw [hEq]
      exact hRowEnergy
    have hFMeas : Measurable F := by
      change Measurable (fun x : Fin n → Ω =>
        ∑ i : Fin n, ∑ j : Fin n, if i < j then r (x i) (x j) else (0 : ℝ))
      refine Finset.measurable_fun_sum (Finset.univ : Finset (Fin n))
        (fun i _ => ?_)
      refine Finset.measurable_fun_sum (Finset.univ : Finset (Fin n))
        (fun j _ => ?_)
      by_cases hij : i < j
      · simpa only [if_pos hij] using hRij i j
      · simpa only [if_neg hij] using
          (measurable_const : Measurable (fun _ : Fin n → Ω => (0 : ℝ)))
    have hEMeas : Measurable E := by
      change Measurable (fun x : Fin n → Ω =>
        (∑ i : Fin n, (g (x i)) ^ (2 : ℕ)) / (n : ℝ))
      exact (Finset.measurable_fun_sum (Finset.univ : Finset (Fin n))
        (fun i _ => (hGi i).pow_const (2 : ℕ))).div_const (n : ℝ)
    have hWMeas : Measurable W := by
      change Measurable (fun x : Fin n → Ω =>
        (∑ i : Fin n, g (x i)) / Real.sqrt (n : ℝ))
      exact (Finset.measurable_fun_sum (Finset.univ : Finset (Fin n))
        (fun i _ => hGi i)).div_const (Real.sqrt (n : ℝ))
    have hVMeas : Measurable V := Real.continuous_sqrt.measurable.comp hEMeas
    have hGMeas : MeasurableSet G := by
      change MeasurableSet {x : Fin n → Ω |
        (1 / 2 : ℝ) ≤ E x ∧
        |W x| ≤ Real.sqrt z * Real.sqrt (Real.sqrt (n : ℝ)) * (4 + V x)}
      exact (measurableSet_le measurable_const hEMeas).inter
        (measurableSet_le (continuous_abs.measurable.comp hWMeas)
          (((measurable_const : Measurable
            (fun _ : Fin n → Ω => (4 : ℝ))).add hVMeas).const_mul
              (Real.sqrt z * Real.sqrt (Real.sqrt (n : ℝ)))))
    have hC2Meas : MeasurableSet C2 := by
      change MeasurableSet {x : Fin n → Ω |
        |F x| ≤ K * (n : ℝ) * q ∧
        ‖originalRows n r x‖ ^ (2 : ℕ) ≤ K * (n : ℝ) ^ (2 : ℕ) * q}
      exact (measurableSet_le (continuous_abs.measurable.comp hFMeas)
        measurable_const).inter (measurableSet_le hRowsMeas measurable_const)
    have hHMeas : MeasurableSet H := hGMeas.inter hC2Meas
    have hSmall (x : Fin n → Ω) (hx : x ∈ H) :
        0 < projectionV n g x ∧
        z * |residualStatisticD n r x| / projectionV n g x ≤ (1 / 8 : ℝ) ∧
        z ^ (2 : ℕ) * |centeredDelta n g r x| ≤ (1 / 32 : ℝ) ∧
        |centeredDelta n g r x| ≤ (1 / 32 : ℝ) := by
      exact bounded_remainder_small_window n g r x K t0 z hsym hn4
        (le_of_lt hKpos) ht0 hz hzWindow hx.2.1 hx.2.2 hx.1
    have hActualFactor (x : Fin n → Ω) (hx : x ∈ H) :
        0 < Real.sqrt (centeredSq n g r x) ∧
        Real.sqrt (centeredSq n g r x) =
          projectionV n g x * Real.sqrt (1 + centeredDelta n g r x) := by
      have hVpos : 0 < projectionV n g x := (hSmall x hx).1
      have hAbs : |centeredDelta n g r x| ≤ (1 / 32 : ℝ) :=
        (hSmall x hx).2.2.2
      have hNeg : -|centeredDelta n g r x| ≤ centeredDelta n g r x := neg_abs_le _
      have hLower : -(1 / 2 : ℝ) ≤ centeredDelta n g r x := by
        linarith only [hAbs, hNeg]
      exact centered_studentizer_factorization n g r x hVpos hLower
    -- The squareSum(w) failure is a payer and is not an extra test in H.
    let Bad : Set (Fin n → Ω) := boundedProductFailure n r w M q
    have hC2cSubset : C2ᶜ ⊆ Bad := by
      intro x hx
      by_contra hNot
      have hBounds := (not_mem_boundedProductFailure_iff n r w M q x).1 hNot
      exact hx ⟨hBounds.2.1, hBounds.2.2⟩
    have hHcSubset : Hᶜ ⊆ Gᶜ ∪ Bad := by
      intro x hx
      by_cases hG : x ∈ G
      · apply Or.inr
        apply hC2cSubset
        intro hC2
        exact hx ⟨hG, hC2⟩
      · exact Or.inl hG
    have hFailure : Pn.real Bad ≤ (3 : ℝ) * Real.exp (-q) :=
      hConc μ r w hr hr1 hcR hcL hW hWR hSq hSqBound hEnv hsym
    have hGPayment : Pn.real Gᶜ ≤ Real.exp (-cg * (n : ℝ)) +
        (4 : ℝ) * Real.exp (-(z * Real.sqrt (n : ℝ)) / (2 : ℝ)) := by
      have hOriginal := hNormalized
      rw [Shao.OQ6.OriginalGoodEventBridge.normalizedGoodEvent_eq_projectionGood
        n g z] at hOriginal
      exact hOriginal
    have hUnionPayment : Pn.real Hᶜ ≤ Pn.real Gᶜ + Pn.real Bad :=
      (MeasureTheory.measureReal_mono (μ := Pn) hHcSubset).trans
        (MeasureTheory.measureReal_union_le (μ := Pn) Gᶜ Bad)
    refine ⟨hHMeas, ?_, ?_, ?_⟩
    · intro x hx
      rcases hSmall x hx with ⟨hVpos, hRatio, hScaled, hAbs⟩
      have hEnergy : (1 / 2 : ℝ) ≤ projectionEnergy n g x := hx.1.1
      have hNumRaw : z * |residualStatisticD n r x| ≤
          (1 / 8 : ℝ) * projectionV n g x := (div_le_iff₀ hVpos).1 hRatio
      have hNum : z * |residualStatisticD n r x| ≤ projectionV n g x / 8 := by
        nlinarith only [hNumRaw]
      have hNumStrict : z * |residualStatisticD n r x| < projectionV n g x / 4 := by
        nlinarith only [hNum, hVpos]
      have hNeg : -|centeredDelta n g r x| ≤ centeredDelta n g r x := neg_abs_le _
      have hLowerStrong : -(1 / 8 : ℝ) < centeredDelta n g r x := by
        linarith only [hAbs, hNeg]
      have hClip := clippedCenteredDelta_bounds n g r C0 rho 1 x
        hC0 hrho (by norm_num : (0 : ℝ) ≤ 1)
      have hContract : |e1 x| ≤ |centeredDelta n g r x| := hClip.2.2.1
      have hClipScaled : z ^ (2 : ℕ) * |e1 x| ≤ (1 / 32 : ℝ) :=
        (mul_le_mul_of_nonneg_left hContract (sq_nonneg z)).trans hScaled
      have hClipStrict : z ^ (2 : ℕ) * |e1 x| < (1 / 8 : ℝ) := by
        linarith only [hClipScaled]
      have hClipAbs : |e1 x| ≤ (1 / 32 : ℝ) := hContract.trans hAbs
      have hClipPos : 0 < projectionV n g x * Real.sqrt (1 + e1 x) :=
        hClip.2.2.2 hVpos
      have hFactor := hActualFactor x hx
      exact ⟨hVpos, hEnergy, hNum, hNumStrict, hScaled, hAbs, hLowerStrong,
        hContract, hClipScaled, hClipStrict, hClipAbs, hClipPos, hFactor.1, hFactor.2⟩
    · intro x hxZero hxH
      rcases hxZero with hZero | hZero
      · exact (ne_of_gt (hSmall x hxH).1) hZero
      · exact (ne_of_gt (hActualFactor x hxH).1) hZero
    · change Pn.real Hᶜ ≤
        (3 : ℝ) * Real.exp (-q) + Real.exp (-cg * (n : ℝ)) +
          (4 : ℝ) * Real.exp (-(z * Real.sqrt (n : ℝ)) / (2 : ℝ))
      calc
        Pn.real Hᶜ ≤ Pn.real Gᶜ + Pn.real Bad := hUnionPayment
        _ ≤ (Real.exp (-cg * (n : ℝ)) +
            (4 : ℝ) * Real.exp (-(z * Real.sqrt (n : ℝ)) / (2 : ℝ))) +
              (3 : ℝ) * Real.exp (-q) := add_le_add hGPayment hFailure
        _ = (3 : ℝ) * Real.exp (-q) + Real.exp (-cg * (n : ℝ)) +
            (4 : ℝ) * Real.exp (-(z * Real.sqrt (n : ℝ)) / (2 : ℝ)) := by ring
end
end Shao.OQ6.UniformPMomentActualGoodsetFrontier
