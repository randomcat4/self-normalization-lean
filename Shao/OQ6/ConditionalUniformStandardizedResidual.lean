import Shao.OQ6.ConditionalStandardizedLowEnergy
import Shao.OQ6.ConditionalTrueProjectionCarrier

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Shao.OQ6.ConditionalUniformStandardizedResidual

noncomputable section

open MeasureTheory ProbabilityTheory

theorem actual_conditional_uniform_standardized_residual
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
    let M : ℝ := ∫ o, w o ^ 2 ∂μ
    let W2 : ℝ := Real.sqrt M
    let Cenv : ℝ := 2 * (1 + 2 * W2) ^ 2
    let RhoBound : ℝ := 4 * Cenv ^ 2 * M ^ 2
    MemLp w 2 μ ∧ Integrable (fun o => w o ^ 2) μ ∧
      1 ≤ M ∧ 1 ≤ W2 ∧ W2 ^ 2 = M ∧ 0 < Cenv ∧ 0 < RhoBound ∧
      ∃ N0 : ℕ, 1 ≤ N0 ∧
      ∀ R : ℝ, (N0 : ℝ) ≤ R →
      let C : Set Ω := {o : Ω | w o ≤ R}
      let d : ℝ := μ.real C
      let ν : Measure Ω := (μ C)⁻¹ • μ.restrict C
      let b : ℝ := ∫ o in Cᶜ, w o ∂μ
      let c : ℝ := b / d
      let Mν : ℝ := ∫ o, w o ^ 2 ∂ν
      MeasurableSet C ∧ (1 / 2 : ℝ) ≤ d ∧
        IsProbabilityMeasure ν ∧ ν ≪ μ ∧ (ν.prod ν) ≪ (μ.prod μ) ∧
        ν C = 1 ∧ (∀ᵐ o ∂ν, 1 ≤ w o ∧ w o ≤ R) ∧
        MemLp w 2 ν ∧ Integrable (fun o => w o ^ 2) ν ∧
        0 ≤ Mν ∧ Mν ≤ 2 * M ∧
        0 ≤ b ∧ b ≤ W2 ∧ 0 ≤ c ∧ c ≤ 2 * W2 ∧
        MemLp (fun z : Ω × Ω => w z.1 * w z.2) 2 (ν.prod ν) ∧
        Integrable (fun z : Ω × Ω => (w z.1 * w z.2) ^ 2) (ν.prod ν) ∧
        (∫ z : Ω × Ω, (w z.1 * w z.2) ^ 2 ∂(ν.prod ν)) = Mν ^ 2 ∧
        ∀ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 →
        let H : Ω → Ω → ℝ := fun o y => g o + g y + lam * r o y
        let κ : ℝ := ∫ z : Ω × Ω, H z.1 z.2 ∂(ν.prod ν)
        let G : Ω → ℝ := fun o => (∫ y, H o y ∂ν) - κ
        let σ2 : ℝ := ∫ o, G o ^ 2 ∂ν
        let σ : ℝ := Real.sqrt σ2
        let K : Ω → Ω → ℝ := fun o y => H o y - κ - G o - G y
        let Kstd : Ω → Ω → ℝ := fun o y => K o y / σ
        let ρ2 : ℝ := ∫ z : Ω × Ω, Kstd z.1 z.2 ^ 2 ∂(ν.prod ν)
        Measurable (fun z : Ω × Ω => H z.1 z.2) ∧
          MemLp (fun z : Ω × Ω => H z.1 z.2) 2 (ν.prod ν) ∧
          Measurable G ∧ MemLp G 2 ν ∧
          Integrable (fun o => G o ^ 2) ν ∧ (∫ o, G o ∂ν) = 0 ∧
          (1 / 2 : ℝ) ≤ σ2 ∧ σ2 ≤ (3 / 2 : ℝ) ∧
          (1 / 2 : ℝ) ≤ σ ∧ 0 < σ ∧ σ ^ 2 = σ2 ∧
          Measurable (fun z : Ω × Ω => K z.1 z.2) ∧
          MemLp (fun z : Ω × Ω => K z.1 z.2) 2 (ν.prod ν) ∧
          (∀ o y, K o y = K y o) ∧
          Measurable (fun z : Ω × Ω => Kstd z.1 z.2) ∧
          MemLp (fun z : Ω × Ω => Kstd z.1 z.2) 2 (ν.prod ν) ∧
          Integrable (fun z : Ω × Ω => Kstd z.1 z.2 ^ 2) (ν.prod ν) ∧
          (∀ o y, Kstd o y = Kstd y o) ∧
          (∀ᵐ o ∂ν, Integrable (Kstd o) ν ∧ (∫ y, Kstd o y ∂ν) = 0) ∧
          (∫ z : Ω × Ω, Kstd z.1 z.2 ∂(ν.prod ν)) = 0 ∧
          (∀ᵐ z : Ω × Ω ∂(ν.prod ν),
            |Kstd z.1 z.2| ≤ Cenv * w z.1 * w z.2) ∧
          (∀ᵐ z : Ω × Ω ∂(ν.prod ν), |Kstd z.1 z.2| ≤ Cenv * R ^ 2) ∧
          0 ≤ ρ2 ∧ ρ2 ≤ RhoBound := by
  classical
  dsimp only
  -- frozen ITEM023
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
  -- frozen ITEM024
  let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
  -- frozen ITEM025
  let M : ℝ := ∫ o, w o ^ 2 ∂μ
  -- frozen ITEM026
  let W2 : ℝ := Real.sqrt M
  -- frozen ITEM027
  let Cenv : ℝ := 2 * (1 + 2 * W2) ^ 2
  -- frozen ITEM028
  let RhoBound : ℝ := 4 * Cenv ^ 2 * M ^ 2
  -- frozen ITEM029
  have hThreshold : ∃ n : ℕ, 1 ≤ n ∧
    ∀ R : ℝ, (n : ℝ) ≤ R →
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
      Measurable G ∧ MemLp G 2 ν ∧
        Integrable (fun o => G o ^ 2) ν ∧ (∫ o, G o ∂ν) = 0 ∧
        (1 / 2 : ℝ) ≤ σ2 ∧ σ2 ≤ (3 / 2 : ℝ) ∧
        0 < σ ∧ σ ^ 2 = σ2 := by
    obtain ⟨n, hnOne, hn⟩ := (Shao.OQ6.ConditionalStandardizedLowEnergy.actual_conditional_standardized_low_energy
      μ h hh hh2 hhsymm hcenter hprojectionsecond w hw hwone
      α τ hα hτ hwexp henvelope p hp hgp).2.2.2.2.2.2.2
    refine ⟨n, hnOne, ?_⟩
    intro R hR
    refine ⟨(hn R hR).1, (hn R hR).2.1, (hn R hR).2.2.1,
      (hn R hR).2.2.2.1, (hn R hR).2.2.2.2.1, ?_⟩
    intro lam hLam
    exact ⟨((hn R hR).2.2.2.2.2 lam hLam).1,
      ((hn R hR).2.2.2.2.2 lam hLam).2.1,
      ((hn R hR).2.2.2.2.2 lam hLam).2.2.1,
      ((hn R hR).2.2.2.2.2 lam hLam).2.2.2.1,
      ((hn R hR).2.2.2.2.2 lam hLam).2.2.2.2.1,
      ((hn R hR).2.2.2.2.2 lam hLam).2.2.2.2.2.1,
      ((hn R hR).2.2.2.2.2 lam hLam).2.2.2.2.2.2.1,
      ((hn R hR).2.2.2.2.2 lam hLam).2.2.2.2.2.2.2.1⟩
  -- frozen ITEM030
  let N0 : ℕ := Classical.choose hThreshold
  -- frozen ITEM031
  have hN0Spec : 1 ≤ N0 ∧
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
      Measurable G ∧ MemLp G 2 ν ∧
        Integrable (fun o => G o ^ 2) ν ∧ (∫ o, G o ∂ν) = 0 ∧
        (1 / 2 : ℝ) ≤ σ2 ∧ σ2 ≤ (3 / 2 : ℝ) ∧
        0 < σ ∧ σ ^ 2 = σ2 := by
    exact Classical.choose_spec hThreshold
  -- frozen ITEM032
  have hN0one : 1 ≤ N0 := by
    exact hN0Spec.1
  -- frozen ITEM033
  have hAnchorCutoff : 0 < μ.real {o : Ω | w o ≤ (N0 : ℝ)} := by
    have hdAnchor : (1 / 2 : ℝ) ≤ μ.real {o : Ω | w o ≤ (N0 : ℝ)} :=
      (hN0Spec.2 (N0 : ℝ) le_rfl).2.1
    linarith only [hdAnchor]
  -- frozen ITEM034
  have hw2 : MemLp w 2 μ := by
    have hLamZero : 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 1 := by norm_num
    exact (Shao.OQ6.ConditionalTrueProjectionCarrier.actual_conditional_true_projection_carrier
      μ h hh hh2 hhsymm hcenter hprojectionsecond w hw hwone
      α τ hα hτ hwexp henvelope (N0 : ℝ) hAnchorCutoff 0 hLamZero).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- frozen ITEM035
  have hwSq : Integrable (fun o : Ω => w o ^ 2) μ := by
    exact hw2.integrable_sq
  -- frozen ITEM036
  have hw1 : Integrable w μ := by
    exact hw2.integrable (by norm_num)
  -- frozen ITEM037
  have hwNonneg : ∀ᵐ o : Ω ∂μ, 0 ≤ w o := by
    exact hwone.mono (fun o ho => by linarith only [ho])
  -- frozen ITEM038
  have hMone : 1 ≤ M := by
    calc
      (1 : ℝ) = ∫ _o : Ω, (1 : ℝ) ∂μ := by simp
      _ ≤ ∫ o : Ω, w o ^ 2 ∂μ := by
        apply integral_mono_ae (integrable_const (1 : ℝ)) hwSq
        filter_upwards [hwone] with o ho
        nlinarith only [ho, sq_nonneg (w o - 1)]
  -- frozen ITEM039
  have hW2Nonneg : 0 ≤ W2 := by
    exact Real.sqrt_nonneg M
  -- frozen ITEM040
  have hW2Square : W2 ^ 2 = M := by
    exact Real.sq_sqrt (by linarith only [hMone])
  -- frozen ITEM041
  have hW2one : 1 ≤ W2 := by
    by_contra hNot
    have hBelow : W2 < 1 := lt_of_not_ge hNot
    have hProduct : 0 < (1 - W2) * (1 + W2) :=
      mul_pos (by linarith only [hBelow]) (by linarith only [hW2Nonneg])
    nlinarith only [hMone, hW2Square, hProduct]
  -- frozen ITEM042
  let W1 : ℝ := ∫ o, w o ∂μ
  -- frozen ITEM043
  have hW1Nonneg : 0 ≤ W1 := by
    exact integral_nonneg_of_ae hwNonneg
  -- frozen ITEM044
  have hWVarInt : Integrable (fun o : Ω => (w o - W1) ^ 2) μ := by
    exact (hw2.sub (memLp_const W1)).integrable_sq
  -- frozen ITEM045
  have hWVarId : (∫ o : Ω, (w o - W1) ^ 2 ∂μ) = M - W1 ^ 2 := by
    calc
      (∫ o : Ω, (w o - W1) ^ 2 ∂μ) =
          ∫ o : Ω, w o ^ 2 - 2 * W1 * w o + W1 ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards with o
        ring
      _ = ((∫ o : Ω, w o ^ 2 ∂μ) - 2 * W1 * (∫ o : Ω, w o ∂μ)) + W1 ^ 2 := by
        rw [integral_add
          (f := fun o : Ω => w o ^ 2 - 2 * W1 * w o)
          (g := fun _o : Ω => W1 ^ 2)
          (hwSq.sub (hw1.const_mul (2 * W1)))
          (integrable_const (W1 ^ 2)),
          integral_sub hwSq (hw1.const_mul (2 * W1)), integral_const_mul]
        simp only [integral_const, probReal_univ, one_smul]
      _ = M - W1 ^ 2 := by change (M - 2 * W1 * W1) + W1 ^ 2 = M - W1 ^ 2; ring
  -- frozen ITEM046
  have hW1Square : W1 ^ 2 ≤ M := by
    have hVarNonneg : 0 ≤ ∫ o : Ω, (w o - W1) ^ 2 ∂μ :=
      integral_nonneg (fun o => sq_nonneg (w o - W1))
    rw [hWVarId] at hVarNonneg
    linarith only [hVarNonneg]
  -- frozen ITEM047
  have hW1Bound : W1 ≤ W2 := by
    by_contra hNot
    have hAbove : W2 < W1 := lt_of_not_ge hNot
    have hProduct : 0 < (W1 - W2) * (W1 + W2) :=
      mul_pos (sub_pos.mpr hAbove) (by linarith only [hAbove, hW2Nonneg])
    nlinarith only [hW1Square, hW2Square, hProduct]
  -- frozen ITEM048
  have hCenvPos : 0 < Cenv := by
    change 0 < 2 * (1 + 2 * W2) ^ 2
    have hBasePos : 0 < 1 + 2 * W2 := by linarith only [hW2Nonneg]
    positivity
  -- frozen ITEM049
  have hRhoBoundPos : 0 < RhoBound := by
    change 0 < 4 * Cenv ^ 2 * M ^ 2
    have hMpos : 0 < M := by linarith only [hMone]
    positivity
  refine ⟨hw2, hwSq, hMone, hW2one, hW2Square, hCenvPos,
    hRhoBoundPos, N0, hN0one, ?_⟩
  intro R hR
  -- frozen ITEM052
  let C : Set Ω := {o : Ω | w o ≤ R}
  -- frozen ITEM053
  let d : ℝ := μ.real C
  -- frozen ITEM054
  let ν : Measure Ω := (μ C)⁻¹ • μ.restrict C
  -- frozen ITEM055
  let b : ℝ := ∫ o in Cᶜ, w o ∂μ
  -- frozen ITEM056
  let c : ℝ := b / d
  -- frozen ITEM057
  let Mν : ℝ := ∫ o, w o ^ 2 ∂ν
  -- frozen ITEM058
  have hCmeas : MeasurableSet C := by
    exact (hN0Spec.2 R hR).1
  -- frozen ITEM059
  have hdHalf : (1 / 2 : ℝ) ≤ d := by
    exact (hN0Spec.2 R hR).2.1
  -- frozen ITEM060
  have hdPos : 0 < d := by
    linarith only [hdHalf]
  -- frozen ITEM061
  have hνprob : IsProbabilityMeasure ν := by
    exact (hN0Spec.2 R hR).2.2.1
  -- frozen ITEM062
  letI : IsProbabilityMeasure ν := hνprob
  -- frozen ITEM063
  have hνac : ν ≪ μ := by
    exact (hN0Spec.2 R hR).2.2.2.1
  -- frozen ITEM064
  have hνC : ν C = 1 := by
    exact (hN0Spec.2 R hR).2.2.2.2.1
  -- frozen ITEM065
  have hνprodac : (ν.prod ν) ≪ (μ.prod μ) := by
    have hLamZero : 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 1 := by norm_num
    exact (Shao.OQ6.ConditionalTrueProjectionCarrier.actual_conditional_true_projection_carrier
      μ h hh hh2 hhsymm hcenter hprojectionsecond w hw hwone
      α τ hα hτ hwexp henvelope R hdPos 0 hLamZero).2.2.2.2.2.2.2.2.2.1
  -- frozen ITEM066
  have hwCutν : ∀ᵐ o : Ω ∂ν, 1 ≤ w o ∧ w o ≤ R := by
    filter_upwards [hνac.ae_le hwone,
      (MeasureTheory.mem_ae_iff_prob_eq_one (μ := ν) hCmeas).2 hνC] with o ho hmem
    exact ⟨ho, hmem⟩
  -- frozen ITEM067
  have hw2ν : MemLp w 2 ν := by
    have hLamZero : 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 1 := by norm_num
    exact (Shao.OQ6.ConditionalTrueProjectionCarrier.actual_conditional_true_projection_carrier
      μ h hh hh2 hhsymm hcenter hprojectionsecond w hw hwone
      α τ hα hτ hwexp henvelope R hdPos 0 hLamZero).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- frozen ITEM068
  have hwSqν : Integrable (fun o : Ω => w o ^ 2) ν := by
    exact hw2ν.integrable_sq
  -- frozen ITEM069
  have hw1ν : Integrable w ν := by
    exact hw2ν.integrable (by norm_num)
  -- frozen ITEM070
  have hMν0 : 0 ≤ Mν := by
    exact integral_nonneg (fun o => sq_nonneg (w o))
  -- frozen ITEM071
  have hMνBound : Mν ≤ 2 * M := by
    have hLamZero : 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 1 := by norm_num
    have hConditionalSecond : Mν ≤ M / d := by
      exact (Shao.OQ6.ConditionalTrueProjectionCarrier.actual_conditional_true_projection_carrier
      μ h hh hh2 hhsymm hcenter hprojectionsecond w hw hwone
      α τ hα hτ hwexp henvelope R hdPos 0 hLamZero).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hPaidSecond : Mν * d ≤ M := (le_div_iff₀ hdPos).1 hConditionalSecond
    have hHalfProduct : Mν * (1 / 2 : ℝ) ≤ Mν * d :=
      mul_le_mul_of_nonneg_left hdHalf hMν0
    linarith only [hPaidSecond, hHalfProduct]
  -- frozen ITEM072
  have hb0 : 0 ≤ b := by
    exact integral_nonneg_of_ae (ae_restrict_of_ae hwNonneg)
  -- frozen ITEM073
  have hbUpper : b ≤ W2 := by
    have hRetainedNonneg : 0 ≤ ∫ o in C, w o ∂μ :=
      integral_nonneg_of_ae (ae_restrict_of_ae hwNonneg)
    have hWeightSplit : (∫ o in C, w o ∂μ) + b = W1 := integral_add_compl hCmeas hw1
    linarith only [hRetainedNonneg, hWeightSplit, hW1Bound]
  -- frozen ITEM074
  have hc0 : 0 ≤ c := by
    exact div_nonneg hb0 hdPos.le
  -- frozen ITEM075
  have hcBound : c ≤ 2 * W2 := by
    apply (div_le_iff₀ hdPos).2
    nlinarith only [hbUpper, mul_nonneg hW2Nonneg (sub_nonneg.mpr hdHalf)]
  -- frozen ITEM076
  have hPairSqInt : Integrable (fun z : Ω × Ω => (w z.1 * w z.2) ^ 2) (ν.prod ν) := by
    simpa only [mul_pow] using hwSqν.mul_prod hwSqν
  -- frozen ITEM077
  have hPairSquare : (∫ z : Ω × Ω, (w z.1 * w z.2) ^ 2 ∂(ν.prod ν)) = Mν ^ 2 := by
    calc
      (∫ z : Ω × Ω, (w z.1 * w z.2) ^ 2 ∂(ν.prod ν)) =
          ∫ z : Ω × Ω, w z.1 ^ 2 * w z.2 ^ 2 ∂(ν.prod ν) := by
        simp only [mul_pow]
      _ = Mν * Mν := integral_prod_mul (fun o : Ω => w o ^ 2) (fun o : Ω => w o ^ 2)
      _ = Mν ^ 2 := by ring
  -- frozen ITEM078
  have hPair2 : MemLp (fun z : Ω × Ω => w z.1 * w z.2) 2 (ν.prod ν) := by
    exact (memLp_two_iff_integrable_sq
      (((hw.comp measurable_fst).mul (hw.comp measurable_snd)).aestronglyMeasurable)).2 hPairSqInt
  -- frozen ITEM079
  have hRone : 1 ≤ R := by
    have hNatCastOne : (1 : ℝ) ≤ (N0 : ℝ) := by exact_mod_cast hN0one
    exact hNatCastOne.trans hR
  refine ⟨hCmeas, hdHalf, hνprob, hνac, hνprodac, hνC, hwCutν,
    hw2ν, hwSqν, hMν0, hMνBound, hb0, hbUpper, hc0, hcBound,
    hPair2, hPairSqInt, hPairSquare, ?_⟩
  intro lam hLam
  -- frozen ITEM082
  let H : Ω → Ω → ℝ := fun o y => g o + g y + lam * r o y
  -- frozen ITEM083
  let κ : ℝ := ∫ z : Ω × Ω, H z.1 z.2 ∂(ν.prod ν)
  -- frozen ITEM084
  let G : Ω → ℝ := fun o => (∫ y, H o y ∂ν) - κ
  -- frozen ITEM085
  let σ2 : ℝ := ∫ o, G o ^ 2 ∂ν
  -- frozen ITEM086
  let σ : ℝ := Real.sqrt σ2
  -- frozen ITEM087
  let K : Ω → Ω → ℝ := fun o y => H o y - κ - G o - G y
  -- frozen ITEM088
  let Kstd : Ω → Ω → ℝ := fun o y => K o y / σ
  -- frozen ITEM089
  let ρ2 : ℝ := ∫ z : Ω × Ω, Kstd z.1 z.2 ^ 2 ∂(ν.prod ν)
  -- frozen ITEM090
  let a : Ω → ℝ := fun o => ∫ y, r o y ∂ν
  -- frozen ITEM091
  let θ : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ∂(ν.prod ν)
  -- frozen ITEM092
  let rC : Ω → Ω → ℝ := fun o y => r o y - a o - a y + θ
  -- frozen ITEM093
  have hHm : Measurable (fun z : Ω × Ω => H z.1 z.2) := by
    exact (Shao.OQ6.ConditionalTrueProjectionCarrier.actual_conditional_true_projection_carrier
      μ h hh hh2 hhsymm hcenter hprojectionsecond w hw hwone
      α τ hα hτ hwexp henvelope R hdPos lam hLam).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- frozen ITEM094
  have hH2 : MemLp (fun z : Ω × Ω => H z.1 z.2) 2 (ν.prod ν) := by
    exact (Shao.OQ6.ConditionalTrueProjectionCarrier.actual_conditional_true_projection_carrier
      μ h hh hh2 hhsymm hcenter hprojectionsecond w hw hwone
      α τ hα hτ hwexp henvelope R hdPos lam hLam).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- frozen ITEM095
  have hGm : Measurable G := by
    exact (((hN0Spec.2 R hR).2.2.2.2.2 lam hLam)).1
  -- frozen ITEM096
  have hG2 : MemLp G 2 ν := by
    exact (((hN0Spec.2 R hR).2.2.2.2.2 lam hLam)).2.1
  -- frozen ITEM097
  have hGsq : Integrable (fun o : Ω => G o ^ 2) ν := by
    exact (((hN0Spec.2 R hR).2.2.2.2.2 lam hLam)).2.2.1
  -- frozen ITEM098
  have hGmean : (∫ o : Ω, G o ∂ν) = 0 := by
    exact (((hN0Spec.2 R hR).2.2.2.2.2 lam hLam)).2.2.2.1
  -- frozen ITEM099
  have hσ2Half : (1 / 2 : ℝ) ≤ σ2 := by
    exact (((hN0Spec.2 R hR).2.2.2.2.2 lam hLam)).2.2.2.2.1
  -- frozen ITEM100
  have hσ2Upper : σ2 ≤ (3 / 2 : ℝ) := by
    exact (((hN0Spec.2 R hR).2.2.2.2.2 lam hLam)).2.2.2.2.2.1
  -- frozen ITEM101
  have hσPos : 0 < σ := by
    exact (((hN0Spec.2 R hR).2.2.2.2.2 lam hLam)).2.2.2.2.2.2.1
  -- frozen ITEM102
  have hσSquare : σ ^ 2 = σ2 := by
    exact (((hN0Spec.2 R hR).2.2.2.2.2 lam hLam)).2.2.2.2.2.2.2
  -- frozen ITEM103
  have hσHalf : (1 / 2 : ℝ) ≤ σ := by
    by_contra hNot
    have hBelow : σ < (1 / 2 : ℝ) := lt_of_not_ge hNot
    have hProduct : 0 < ((1 / 2 : ℝ) - σ) * ((1 / 2 : ℝ) + σ) :=
      mul_pos (sub_pos.mpr hBelow) (by linarith only [hσPos])
    nlinarith only [hσSquare, hσ2Half, hProduct]
  -- frozen ITEM104
  have hσInv : 1 / σ ≤ 2 := by
    apply (div_le_iff₀ hσPos).2
    linarith only [hσHalf]
  -- frozen ITEM105
  have hKm : Measurable (fun z : Ω × Ω => K z.1 z.2) := by
    exact ((hHm.sub measurable_const).sub (hGm.comp measurable_fst)).sub
      (hGm.comp measurable_snd)
  -- frozen ITEM106
  have hK2 : MemLp (fun z : Ω × Ω => K z.1 z.2) 2 (ν.prod ν) := by
    exact (Shao.OQ6.ConditionalTrueProjectionCarrier.actual_conditional_true_projection_carrier
      μ h hh hh2 hhsymm hcenter hprojectionsecond w hw hwone
      α τ hα hτ hwexp henvelope R hdPos lam hLam).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- frozen ITEM107
  have hKsym : ∀ o y : Ω, K o y = K y o := by
    intro o y
    dsimp only [K, H, r]
    rw [hhsymm o y]
    ring
  -- frozen ITEM108
  have hKagree : ∀ᵐ z : Ω × Ω ∂(ν.prod ν), K z.1 z.2 = lam * rC z.1 z.2 := by
    exact (Shao.OQ6.ConditionalTrueProjectionCarrier.actual_conditional_true_projection_carrier
      μ h hh hh2 hhsymm hcenter hprojectionsecond w hw hwone
      α τ hα hτ hwexp henvelope R hdPos lam hLam).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- frozen ITEM109
  have hKcan : ∀ᵐ o : Ω ∂ν, (∫ y : Ω, K o y ∂ν) = 0 := by
    exact (Shao.OQ6.ConditionalTrueProjectionCarrier.actual_conditional_true_projection_carrier
      μ h hh hh2 hhsymm hcenter hprojectionsecond w hw hwone
      α τ hα hτ hwexp henvelope R hdPos lam hLam).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- frozen ITEM110
  have hMuEnvelope : ∀ᵐ z : Ω × Ω ∂(μ.prod μ), |lam * rC z.1 z.2| ≤ (1 + c) ^ 2 * w z.1 * w z.2 := by
    filter_upwards [(Shao.OQ6.ConditionalTrueProjectionCarrier.actual_conditional_true_projection_carrier
      μ h hh hh2 hhsymm hcenter hprojectionsecond w hw hwone
      α τ hα hτ hwexp henvelope R hdPos lam hLam).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] with z hz
    exact hz.2
  -- frozen ITEM111
  have hNuEnvelope : ∀ᵐ z : Ω × Ω ∂(ν.prod ν), |K z.1 z.2| ≤ (1 + c) ^ 2 * w z.1 * w z.2 := by
    filter_upwards [hKagree, hνprodac.ae_le hMuEnvelope] with z hz henv
    rw [hz]
    exact henv
  -- frozen ITEM112
  have hKstdm : Measurable (fun z : Ω × Ω => Kstd z.1 z.2) := by
    exact hKm.div_const σ
  -- frozen ITEM113
  have hKstd2 : MemLp (fun z : Ω × Ω => Kstd z.1 z.2) 2 (ν.prod ν) := by
    simpa only [Kstd, div_eq_mul_inv, mul_comm] using hK2.const_mul σ⁻¹
  -- frozen ITEM114
  have hKstdSq : Integrable (fun z : Ω × Ω => Kstd z.1 z.2 ^ 2) (ν.prod ν) := by
    exact hKstd2.integrable_sq
  -- frozen ITEM115
  have hKstd1 : Integrable (fun z : Ω × Ω => Kstd z.1 z.2) (ν.prod ν) := by
    exact hKstd2.integrable (by norm_num)
  -- frozen ITEM116
  have hKstdSym : ∀ o y : Ω, Kstd o y = Kstd y o := by
    intro o y
    change K o y / σ = K y o / σ
    rw [hKsym o y]
  -- frozen ITEM117
  have hKstdRows : ∀ᵐ o : Ω ∂ν, Integrable (Kstd o) ν ∧ (∫ y : Ω, Kstd o y ∂ν) = 0 := by
    filter_upwards [hKstd1.prod_right_ae, hKcan] with o hrow hcenterRow
    refine ⟨hrow, ?_⟩
    change (∫ y : Ω, K o y / σ ∂ν) = 0
    rw [integral_div, hcenterRow, zero_div]
  -- frozen ITEM118
  have hKstdMean : (∫ z : Ω × Ω, Kstd z.1 z.2 ∂(ν.prod ν)) = 0 := by
    calc
      (∫ z : Ω × Ω, Kstd z.1 z.2 ∂(ν.prod ν)) =
          ∫ o : Ω, ∫ y : Ω, Kstd o y ∂ν ∂ν := integral_prod _ hKstd1
      _ = ∫ _o : Ω, (0 : ℝ) ∂ν := by
        apply integral_congr_ae
        filter_upwards [hKstdRows] with o ho
        exact ho.2
      _ = 0 := by simp
  -- frozen ITEM119
  have hKstdEnv : ∀ᵐ z : Ω × Ω ∂(ν.prod ν), |Kstd z.1 z.2| ≤ Cenv * w z.1 * w z.2 := by
    have hCoeff : (1 + c) ^ 2 ≤ (1 + 2 * W2) ^ 2 := by
      have hSumNonneg : 0 ≤ 2 + 2 * W2 + c := by linarith only [hW2Nonneg, hc0]
      nlinarith only [mul_nonneg (sub_nonneg.mpr hcBound) hSumNonneg]
    filter_upwards [hNuEnvelope,
      measurePreserving_fst.quasiMeasurePreserving.ae hwCutν,
      measurePreserving_snd.quasiMeasurePreserving.ae hwCutν] with z henv hwz1 hwz2
    have hwz10 : 0 ≤ w z.1 := by linarith only [hwz1.1]
    have hwz20 : 0 ≤ w z.2 := by linarith only [hwz2.1]
    have hPairNonneg : 0 ≤ w z.1 * w z.2 := mul_nonneg hwz10 hwz20
    have hOldEnvNonneg : 0 ≤ (1 + c) ^ 2 * w z.1 * w z.2 :=
      mul_nonneg (mul_nonneg (sq_nonneg (1 + c)) hwz10) hwz20
    calc
      |Kstd z.1 z.2| = |K z.1 z.2| / σ := by
        simp only [Kstd, abs_div, abs_of_pos hσPos]
      _ ≤ ((1 + c) ^ 2 * w z.1 * w z.2) / σ :=
        div_le_div_of_nonneg_right henv hσPos.le
      _ = (1 / σ) * ((1 + c) ^ 2 * w z.1 * w z.2) := by ring
      _ ≤ 2 * ((1 + c) ^ 2 * w z.1 * w z.2) :=
        mul_le_mul_of_nonneg_right hσInv hOldEnvNonneg
      _ = (2 * (1 + c) ^ 2) * (w z.1 * w z.2) := by ring
      _ ≤ (2 * (1 + 2 * W2) ^ 2) * (w z.1 * w z.2) :=
        mul_le_mul_of_nonneg_right (by linarith only [hCoeff]) hPairNonneg
      _ = Cenv * w z.1 * w z.2 := by dsimp only [Cenv]; ring
  -- frozen ITEM120
  have hKstdBounded : ∀ᵐ z : Ω × Ω ∂(ν.prod ν), |Kstd z.1 z.2| ≤ Cenv * R ^ 2 := by
    filter_upwards [hKstdEnv,
      measurePreserving_fst.quasiMeasurePreserving.ae hwCutν,
      measurePreserving_snd.quasiMeasurePreserving.ae hwCutν] with z henv hwz1 hwz2
    have hwz20 : 0 ≤ w z.2 := by linarith only [hwz2.1]
    have hR0 : 0 ≤ R := by linarith only [hRone]
    have hPairBound : w z.1 * w z.2 ≤ R ^ 2 := by
      simpa only [pow_two] using mul_le_mul hwz1.2 hwz2.2 hwz20 hR0
    calc
      |Kstd z.1 z.2| ≤ Cenv * w z.1 * w z.2 := henv
      _ = Cenv * (w z.1 * w z.2) := by ring
      _ ≤ Cenv * R ^ 2 := mul_le_mul_of_nonneg_left hPairBound hCenvPos.le
  -- frozen ITEM121
  have hRhoNonneg : 0 ≤ ρ2 := by
    exact integral_nonneg (fun z => sq_nonneg (Kstd z.1 z.2))
  -- frozen ITEM122
  have hRhoByMν : ρ2 ≤ Cenv ^ 2 * Mν ^ 2 := by
    have hEnvSquare : ∀ᵐ z : Ω × Ω ∂(ν.prod ν),
        Kstd z.1 z.2 ^ 2 ≤ Cenv ^ 2 * (w z.1 * w z.2) ^ 2 := by
      filter_upwards [hKstdEnv] with z hz
      have hPoint : |Kstd z.1 z.2| ≤ Cenv * (w z.1 * w z.2) := by
        simpa only [mul_assoc] using hz
      have hRightNonneg : 0 ≤ Cenv * (w z.1 * w z.2) :=
        (abs_nonneg (Kstd z.1 z.2)).trans hPoint
      have hDifferenceProduct : 0 ≤
          (Cenv * (w z.1 * w z.2) - |Kstd z.1 z.2|) *
            (Cenv * (w z.1 * w z.2) + |Kstd z.1 z.2|) :=
        mul_nonneg (sub_nonneg.mpr hPoint)
          (add_nonneg hRightNonneg (abs_nonneg (Kstd z.1 z.2)))
      nlinarith only [hDifferenceProduct, sq_abs (Kstd z.1 z.2)]
    calc
      ρ2 = ∫ z : Ω × Ω, Kstd z.1 z.2 ^ 2 ∂(ν.prod ν) := rfl
      _ ≤ ∫ z : Ω × Ω, Cenv ^ 2 * (w z.1 * w z.2) ^ 2 ∂(ν.prod ν) :=
        integral_mono_ae hKstdSq (hPairSqInt.const_mul (Cenv ^ 2)) hEnvSquare
      _ = Cenv ^ 2 * Mν ^ 2 := by rw [integral_const_mul, hPairSquare]
  -- frozen ITEM123
  have hRhoBound : ρ2 ≤ RhoBound := by
    have hM0 : 0 ≤ M := by linarith only [hMone]
    have hConditionalSumNonneg : 0 ≤ 2 * M + Mν := by linarith only [hM0, hMν0]
    have hConditionalSquare : Mν ^ 2 ≤ 4 * M ^ 2 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hMνBound) hConditionalSumNonneg]
    calc
      ρ2 ≤ Cenv ^ 2 * Mν ^ 2 := hRhoByMν
      _ ≤ Cenv ^ 2 * (4 * M ^ 2) :=
        mul_le_mul_of_nonneg_left hConditionalSquare (sq_nonneg Cenv)
      _ = RhoBound := by dsimp only [RhoBound]; ring
  exact ⟨hHm, hH2, hGm, hG2, hGsq, hGmean, hσ2Half, hσ2Upper,
    hσHalf, hσPos, hσSquare, hKm, hK2, hKsym, hKstdm, hKstd2,
    hKstdSq, hKstdSym, hKstdRows, hKstdMean, hKstdEnv, hKstdBounded,
    hRhoNonneg, hRhoBound⟩
end

end Shao.OQ6.ConditionalUniformStandardizedResidual
