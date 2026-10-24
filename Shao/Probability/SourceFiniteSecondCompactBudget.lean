/- Original finite-second centered truncation and compact one-wall budget. -/
import Shao.Probability.SourceOneSidedRelativeError
import Shao.C1.Normalization
import Shao.Probability.SourceOriginalZeroEnergyBudget
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000

noncomputable section
namespace Shao.Probability
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem centered_bounded_truncation_budget_limit
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (n : ℕ) (hn : 0 < n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) mu)
    (hmean : (∫ z : ℝ, z ∂mu) = 0)
    (hpos : 0 < ∫ z : ℝ, z ^ 2 ∂mu) :
    let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂mu
    let sigma : ℝ := Real.sqrt sigmaSq
    let cut : ℕ → ℝ → ℝ := fun K z =>
      if |z| ≤ (K : ℝ) + 1 then z else 0
    let center : ℕ → ℝ := fun K => ∫ z : ℝ, cut K z ∂mu
    let centered : ℕ → ℝ → ℝ := fun K z => cut K z - center K
    let variance : ℕ → ℝ := fun K => ∫ z : ℝ, (centered K z) ^ 2 ∂mu
    let truncatedLaw : ℕ → Measure ℝ := fun K => Measure.map (centered K) mu
    let normalizedLaw : Measure ℝ := Measure.map
      (fun z : ℝ => z / (sigma * Real.sqrt (n : ℝ))) mu
    let normalizedTruncatedLaw : ℕ → Measure ℝ := fun K => Measure.map
      (fun z : ℝ => z / (Real.sqrt (variance K) * Real.sqrt (n : ℝ)))
      (truncatedLaw K)
    (∀ K : ℕ,
      Measurable (centered K) ∧
        (∀ z : ℝ, |centered K z| ≤ 2 * ((K : ℝ) + 1)) ∧
        Integrable (fun z : ℝ => (centered K z) ^ 2) mu ∧
        Integrable (fun z : ℝ => Real.rpow |centered K z| 3) mu ∧
        (∫ z : ℝ, centered K z ∂mu) = 0 ∧
        IsProbabilityMeasure (truncatedLaw K) ∧
        IsProbabilityMeasure (normalizedTruncatedLaw K)) ∧
      Tendsto center atTop (𝓝 0) ∧
      (∀ z : ℝ, Tendsto (fun K : ℕ => centered K z) atTop (𝓝 z)) ∧
      Tendsto (fun K : ℕ => ∫ z : ℝ, (centered K z - z) ^ 2 ∂mu)
        atTop (𝓝 0) ∧
      Tendsto variance atTop (𝓝 sigmaSq) ∧
      (∀ᶠ K : ℕ in atTop, sigmaSq / 2 ≤ variance K) ∧
      (∀ u : ℝ, Tendsto
        (fun K : ℕ => Shao.truncationBudget (normalizedTruncatedLaw K) n u)
        atTop (𝓝 (Shao.truncationBudget normalizedLaw n u))) := by
  classical
  dsimp only
  let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂mu
  let sigma : ℝ := Real.sqrt sigmaSq
  let cut : ℕ → ℝ → ℝ := fun K z => if |z| ≤ (K : ℝ) + 1 then z else 0
  let center : ℕ → ℝ := fun K => ∫ z : ℝ, cut K z ∂mu
  let centered : ℕ → ℝ → ℝ := fun K z => cut K z - center K
  let variance : ℕ → ℝ := fun K => ∫ z : ℝ, (centered K z) ^ 2 ∂mu
  let truncatedLaw : ℕ → Measure ℝ := fun K => Measure.map (centered K) mu
  let normalizedLaw : Measure ℝ := Measure.map
    (fun z : ℝ => z / (sigma * Real.sqrt (n : ℝ))) mu
  let normalizedTruncatedLaw : ℕ → Measure ℝ := fun K => Measure.map
    (fun z : ℝ => z / (Real.sqrt (variance K) * Real.sqrt (n : ℝ))) (truncatedLaw K)
  have hid : Integrable (fun z : ℝ => z) mu := by
    apply (h2.add (integrable_const 1)).mono' measurable_id.aestronglyMeasurable
    exact ae_of_all _ fun z => by
      change |z| ≤ z ^ 2 + 1
      nlinarith [sq_nonneg (|z| - 1), sq_abs z]
  let L : ℝ := ∫ z : ℝ, |z| ∂mu
  have hL : 0 ≤ L := integral_nonneg fun z => abs_nonneg z
  have hcm (K : ℕ) : Measurable (cut K) :=
    Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
      measurable_id measurable_const
  have hca (K : ℕ) (z : ℝ) : |cut K z| ≤ |z| := by
    dsimp [cut]
    split_ifs <;> simp
  have hcb (K : ℕ) (z : ℝ) : |cut K z| ≤ (K : ℝ) + 1 := by
    dsimp [cut]
    split_ifs with h
    · exact h
    · simp; positivity
  have hci (K : ℕ) : Integrable (cut K) mu := by
    apply hid.abs.mono' (hcm K).aestronglyMeasurable
    exact ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hca K z
  have hmb (K : ℕ) : |center K| ≤ (K : ℝ) + 1 := by
    calc
      |center K| ≤ ∫ z : ℝ, |cut K z| ∂mu := by
        simpa only [center, Real.norm_eq_abs] using norm_integral_le_integral_norm (cut K)
      _ ≤ ∫ _z : ℝ, (K : ℝ) + 1 ∂mu :=
        integral_mono (hci K).abs (integrable_const _) (hcb K)
      _ = _ := by simp
  have hmL (K : ℕ) : |center K| ≤ L := by
    calc
      |center K| ≤ ∫ z : ℝ, |cut K z| ∂mu := by
        simpa only [center, Real.norm_eq_abs] using norm_integral_le_integral_norm (cut K)
      _ ≤ ∫ z : ℝ, |z| ∂mu := integral_mono (hci K).abs hid.abs (hca K)
      _ = L := rfl
  have hym (K : ℕ) : Measurable (centered K) := (hcm K).sub_const _
  have hyb (K : ℕ) (z : ℝ) : |centered K z| ≤ 2 * ((K : ℝ) + 1) := by
    calc
      |centered K z| ≤ |cut K z| + |center K| := abs_sub _ _
      _ ≤ ((K : ℝ) + 1) + ((K : ℝ) + 1) := add_le_add (hcb K z) (hmb K)
      _ = _ := by ring
  have hyi (K : ℕ) : Integrable (centered K) mu := (hci K).sub (integrable_const _)
  have hy2 (K : ℕ) : Integrable (fun z : ℝ => (centered K z) ^ 2) mu := by
    apply (integrable_const ((2 * ((K : ℝ) + 1)) ^ 2)).mono'
      ((hym K).pow_const 2).aestronglyMeasurable
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hyb K z) 2
  have hy3 (K : ℕ) : Integrable (fun z : ℝ => Real.rpow |centered K z| 3) mu := by
    have he : (fun z : ℝ => Real.rpow |centered K z| 3) =
        fun z => |centered K z| ^ 3 := by
      funext z
      exact Real.rpow_natCast _ 3
    rw [he]
    apply (integrable_const ((2 * ((K : ℝ) + 1)) ^ 3)).mono'
      ((continuous_abs.measurable.comp (hym K)).pow_const 3).aestronglyMeasurable
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hyb K z) 3
  have hy0 (K : ℕ) : (∫ z : ℝ, centered K z ∂mu) = 0 := by
    change (∫ z : ℝ, cut K z - center K ∂mu) = 0
    rw [integral_sub (hci K) (integrable_const _)]
    simp [center]
  have hpK (K : ℕ) : IsProbabilityMeasure (truncatedLaw K) :=
    (Measure.isProbabilityMeasure_map_iff (hym K).aemeasurable).mpr inferInstance
  have hpNK (K : ℕ) : IsProbabilityMeasure (normalizedTruncatedLaw K) := by
    letI := hpK K
    exact (Measure.isProbabilityMeasure_map_iff
      (measurable_id.div_const _).aemeasurable).mpr inferInstance
  have hcutlim (z : ℝ) : Tendsto (fun K : ℕ => cut K z) atTop (𝓝 z) := by
    obtain ⟨N, hN⟩ := exists_nat_gt |z|
    have he : (fun K : ℕ => cut K z) =ᶠ[atTop] fun _ => z := by
      filter_upwards [eventually_ge_atTop N] with K hK
      have hNK : (N : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
      exact if_pos (by linarith)
    exact Filter.Tendsto.congr' he.symm tendsto_const_nhds
  have hmlim : Tendsto center atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun z : ℝ => |z|)
      (fun K => (hcm K).aestronglyMeasurable) hid.abs
      (fun K => ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hca K z)
      (ae_of_all _ hcutlim)
    simpa only [center, hmean] using h
  have hylim (z : ℝ) : Tendsto (fun K : ℕ => centered K z) atTop (𝓝 z) := by
    simpa only [centered, sub_zero] using (hcutlim z).sub hmlim
  have hydom (K : ℕ) (z : ℝ) : (centered K z) ^ 2 ≤ 2 * z ^ 2 + 2 * L ^ 2 := by
    have h : |centered K z| ≤ |z| + L := (abs_sub _ _).trans (add_le_add (hca K z) (hmL K))
    nlinarith [sq_nonneg (|z| - L), sq_abs z, sq_abs (centered K z), abs_nonneg (centered K z)]
  have hdiffdom (K : ℕ) (z : ℝ) :
      (centered K z - z) ^ 2 ≤ 2 * z ^ 2 + 2 * L ^ 2 := by
    have hcd : |cut K z - z| ≤ |z| := by dsimp [cut]; split_ifs <;> simp
    have h : |centered K z - z| ≤ |z| + L := by
      calc
        |centered K z - z| = |(cut K z - z) - center K| := by congr 1; dsimp [centered]; ring
        _ ≤ |cut K z - z| + |center K| := abs_sub _ _
        _ ≤ |z| + L := add_le_add hcd (hmL K)
    nlinarith [sq_nonneg (|z| - L), sq_abs z, sq_abs (centered K z - z), abs_nonneg (centered K z - z)]
  have hdomi : Integrable (fun z : ℝ => 2 * z ^ 2 + 2 * L ^ 2) mu :=
    (h2.const_mul 2).add (integrable_const _)
  have hdiff : Tendsto (fun K : ℕ => ∫ z : ℝ, (centered K z - z) ^ 2 ∂mu)
      atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence
      (fun z : ℝ => 2 * z ^ 2 + 2 * L ^ 2)
      (fun K => (((hym K).sub measurable_id).pow_const 2).aestronglyMeasurable) hdomi
      (fun K => ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hdiffdom K z)
      (ae_of_all _ fun z => by simpa using ((hylim z).sub tendsto_const_nhds).pow 2)
    simpa using h
  have hvlim : Tendsto variance atTop (𝓝 sigmaSq) := by
    exact tendsto_integral_of_dominated_convergence
      (fun z : ℝ => 2 * z ^ 2 + 2 * L ^ 2)
      (fun K => ((hym K).pow_const 2).aestronglyMeasurable) hdomi
      (fun K => ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hydom K z)
      (ae_of_all _ fun z => (hylim z).pow 2)
  have hvlo : ∀ᶠ K : ℕ in atTop, sigmaSq / 2 ≤ variance K := by
    have hsq : 0 < sigmaSq := hpos
    filter_upwards [(tendsto_order.1 hvlim).1 (sigmaSq / 2) (by linarith)] with K hK
    exact hK.le
  refine ⟨fun K => ⟨hym K, hyb K, hy2 K, hy3 K, hy0 K, hpK K, hpNK K⟩,
    hmlim, hylim, hdiff, hvlim, hvlo, ?_⟩
  intro u
  let scale : ℝ := sigma * Real.sqrt (n : ℝ)
  let scales : ℕ → ℝ := fun K => Real.sqrt (variance K) * Real.sqrt (n : ℝ)
  have hsn : 0 < (n : ℝ) := by exact_mod_cast hn
  have hss : 0 < sigmaSq := hpos
  have hns : 0 < (n : ℝ) * sigmaSq := mul_pos hsn hss
  have hscale : 0 < scale := mul_pos (Real.sqrt_pos.mpr hss) (Real.sqrt_pos.mpr hsn)
  have hscaleslim : Tendsto scales atTop (𝓝 scale) :=
    (Real.continuous_sqrt.continuousAt.tendsto.comp hvlim).mul tendsto_const_nhds
  have hscales2 (K : ℕ) : (scales K) ^ 2 = (n : ℝ) * variance K := by
    dsimp [scales]
    rw [mul_pow, Real.sq_sqrt (integral_nonneg fun z => sq_nonneg (centered K z)),
      Real.sq_sqrt (Nat.cast_nonneg n)]
    ring
  let D : ℝ := 4 * (1 + u) ^ 2 / ((n : ℝ) * sigmaSq)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hbndi : Integrable (fun z : ℝ => D * (z ^ 2 + L ^ 2)) mu :=
    (h2.add (integrable_const _)).const_mul D
  have hbnd : ∀ᶠ K : ℕ in atTop, ∀ᵐ z : ℝ ∂mu,
      ‖Shao.truncationF ((1 + u) * (centered K z / scales K))‖ ≤ D * (z ^ 2 + L ^ 2) := by
    filter_upwards [hvlo] with K hK
    have hvp : 0 < variance K := lt_of_lt_of_le (by linarith : 0 < sigmaSq / 2) hK
    have hsp : 0 < scales K := mul_pos (Real.sqrt_pos.mpr hvp) (Real.sqrt_pos.mpr hsn)
    have hinv : 1 / (scales K) ^ 2 ≤ 2 / ((n : ℝ) * sigmaSq) := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hsp) hns).mpr
      rw [hscales2]
      nlinarith [mul_le_mul_of_nonneg_left hK hsn.le]
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Shao.truncationF_nonneg _)]
      calc
        _ ≤ ((1 + u) * (centered K z / scales K)) ^ 2 := Shao.truncationF_le_sq _
        _ = ((1 + u) ^ 2 * (centered K z) ^ 2) * (1 / (scales K) ^ 2) := by
          simp only [mul_pow, div_pow, div_eq_mul_inv, one_mul]
          ring
        _ ≤ ((1 + u) ^ 2 * (2 * z ^ 2 + 2 * L ^ 2)) * (2 / ((n : ℝ) * sigmaSq)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hydom K z) (sq_nonneg _)) hinv
            (by positivity) (by positivity)
        _ = D * (z ^ 2 + L ^ 2) := by dsimp [D]; ring
  have hpoint : ∀ᵐ z : ℝ ∂mu, Tendsto
      (fun K : ℕ => Shao.truncationF ((1 + u) * (centered K z / scales K))) atTop
      (𝓝 (Shao.truncationF ((1 + u) * (z / scale)))) := by
    exact ae_of_all _ fun z =>
      Shao.continuous_truncationF.continuousAt.tendsto.comp
        (tendsto_const_nhds.mul ((hylim z).div hscaleslim hscale.ne'))
  have hI := tendsto_integral_filter_of_dominated_convergence
    (fun z : ℝ => D * (z ^ 2 + L ^ 2))
    (Eventually.of_forall fun K =>
      (Shao.continuous_truncationF.measurable.comp
        (measurable_const.mul ((hym K).div_const _))).aestronglyMeasurable)
    hbnd hbndi hpoint
  have heqK (K : ℕ) : Shao.truncationBudget (normalizedTruncatedLaw K) n u =
      (n : ℝ) * ∫ z : ℝ, Shao.truncationF ((1 + u) * (centered K z / scales K)) ∂mu := by
    have hm : Measurable (fun z : ℝ => z / (Real.sqrt (variance K) * Real.sqrt (n : ℝ))) :=
      measurable_id.div_const _
    dsimp only [Shao.truncationBudget, normalizedTruncatedLaw, truncatedLaw]
    rw [integral_map (f := fun z : ℝ => Shao.truncationF ((1 + u) * z)) hm.aemeasurable
      (Shao.continuous_truncationF.comp (continuous_const.mul continuous_id)).aestronglyMeasurable,
      integral_map (f := fun z : ℝ => Shao.truncationF ((1 + u) * (z / (Real.sqrt (variance K) * Real.sqrt (n : ℝ))))) (hym K).aemeasurable
        (Shao.continuous_truncationF.comp
          (continuous_const.mul (continuous_id.div_const _))).aestronglyMeasurable]
  have heq : Shao.truncationBudget normalizedLaw n u =
      (n : ℝ) * ∫ z : ℝ, Shao.truncationF ((1 + u) * (z / scale)) ∂mu := by
    have hm : Measurable (fun z : ℝ => z / (sigma * Real.sqrt (n : ℝ))) :=
      measurable_id.div_const _
    dsimp only [Shao.truncationBudget, normalizedLaw]
    rw [integral_map (f := fun z : ℝ => Shao.truncationF ((1 + u) * z)) hm.aemeasurable
      (Shao.continuous_truncationF.comp (continuous_const.mul continuous_id)).aestronglyMeasurable]
  change Tendsto (fun K : ℕ => Shao.truncationBudget (normalizedTruncatedLaw K) n u)
    atTop (𝓝 (Shao.truncationBudget normalizedLaw n u))
  simp_rw [heqK]
  rw [heq]
  exact tendsto_const_nhds.mul hI

/- Frozen full private head before its first proof-body write. -/
private theorem fsc_vanishing_event_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℕ → Set Ω) (hA : ∀ K : ℕ, MeasurableSet (A K))
    (hzero : ∀ omega : Ω, ∀ᶠ K : ℕ in atTop, omega ∉ A K) :
    Tendsto (fun K : ℕ => P.real (A K)) atTop (𝓝 0) := by
  classical
  let f : ℕ → Ω → ℝ := fun K omega => if omega ∈ A K then 1 else 0
  have hm (K : ℕ) : Measurable (f K) :=
    Measurable.ite (hA K) measurable_const measurable_const
  have hpoint (omega : Ω) : Tendsto (fun K : ℕ => f K omega) atTop (𝓝 0) := by
    have he : (fun K : ℕ => f K omega) =ᶠ[atTop] fun _ => (0 : ℝ) := by
      filter_upwards [hzero omega] with K hK
      exact ite_eq_right hK
    exact Filter.Tendsto.congr' he.symm tendsto_const_nhds
  have h := tendsto_integral_of_dominated_convergence (μ := P) (fun _ : Ω => (1 : ℝ))
    (fun K => (hm K).aestronglyMeasurable) (integrable_const _)
    (fun K => ae_of_all _ fun omega => by dsimp [f]; split_ifs <;> norm_num)
    (ae_of_all _ hpoint)
  have he (K : ℕ) : (∫ omega : Ω, f K omega ∂P) = P.real (A K) := by
    have hf : f K = (A K).indicator (fun _ : Ω => (1 : ℝ)) := by
      funext omega
      simp only [f, Set.indicator_apply]
    rw [hf, integral_indicator_const _ (hA K)]
    simp
  simpa only [he, integral_zero] using h


/- Frozen full private head before its first proof-body write.
   This only adapts the accepted p=3 raw relative-error theorem. -/
private theorem fsc_third_moment_compact_input :
    ∃ rho C : ℝ, 0 < rho ∧ rho ≤ 1 / 16 ∧ 0 < C ∧
      ∀ (mu : Measure ℝ) [IsProbabilityMeasure mu]
        (n : ℕ) (hn : 0 < n),
        Integrable (fun z : ℝ => z ^ 2) mu →
        (∫ z : ℝ, z ∂mu) = 0 →
        (0 < ∫ z : ℝ, z ^ 2 ∂mu) →
        Integrable (fun z : ℝ => Real.rpow |z| 3) mu →
        let sigma : ℝ := Real.sqrt (∫ z : ℝ, z ^ 2 ∂mu)
        let nu : Measure ℝ := Measure.map
          (fun z : ℝ => z / (sigma * Real.sqrt (n : ℝ))) mu
        let R : ℝ := Shao.truncationBudget nu n 0
        R < rho / 27 →
          ∀ y : ℝ, 0 < y → y ≤ 2 →
            ∀ s : ℝ, (s = 1 ∨ s = -1) →
              |(Measure.pi (fun _ : Fin n => mu)).real
                  {a : Shao.Path n |
                    y * Real.sqrt (Shao.energy a) ≤ Shao.maxWithZero (s • a)} -
                2 * Shao.standardNormalTail y| ≤ 27 * C * R := by
  classical
  obtain ⟨rho, C, hrho, hrho16, hC, hraw⟩ := original_one_sided_relative_error_raw
  refine ⟨rho, C, hrho, hrho16, hC, ?_⟩
  intro mu _ n hn h2 hmean hpos h3 sigma nu R hsmall y hy hy2 s hs
  have hm : Measurable (fun z : ℝ => z / (sigma * Real.sqrt (n : ℝ))) :=
    measurable_id.div_const _
  have hnu2 : Integrable (fun z : ℝ => z ^ 2) nu := by
    apply (integrable_map_measure (by fun_prop) hm.aemeasurable).2
    simpa only [Function.comp_def, div_pow] using h2.div_const ((sigma * Real.sqrt (n : ℝ)) ^ 2)
  have hR : 0 ≤ R := Shao.truncationBudget_nonneg nu n hnu2 0
  have hRy : Shao.truncationBudget nu n y ≤ 27 * R := by
    have hscale := (Shao.truncationBudget_scale_one_le nu n hnu2 0 (1 + y) (by linarith)).2
    have hscale' : Shao.truncationBudget nu n y ≤ (1 + y) ^ 3 * R := by
      simpa only [zero_add, add_zero, mul_one, add_sub_cancel_left] using hscale
    have hcube : (1 + y) ^ 3 ≤ 27 := by
      have h := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + y) (by linarith : 1 + y ≤ 3) 3
      norm_num at h
      exact h
    exact hscale'.trans (mul_le_mul_of_nonneg_right hcube hR)
  have hdomain : Shao.truncationBudget nu n y ≤ rho := by
    have h : 27 * R < rho := by linarith
    exact hRy.trans h.le
  have he := hraw 3 (by norm_num) (by norm_num) mu n hn h2 hmean hpos h3
    y hy.le (Or.inr hdomain) s hs
  have hevent : {a : Shao.Path n | y * Real.sqrt (Shao.energy a) ≤ Shao.upperMax (s • a) hn} =
      {a : Shao.Path n | y * Real.sqrt (Shao.energy a) ≤ Shao.maxWithZero (s • a)} := by
    ext a
    change y * Real.sqrt (Shao.energy a) ≤ Shao.upperMax (s • a) hn ↔
      y * Real.sqrt (Shao.energy a) ≤ Shao.maxWithZero (s • a)
    rw [Shao.maxWithZero_eq _ hn]
    by_cases hQ : Shao.energy a = 0
    · have hQs : Shao.energy (s • a) = 0 := by rw [Shao.energy_smul, hQ, mul_zero]
      rw [Shao.upperMax_eq_zero_of_energy_eq_zero _ hn hQs]
      simp [hQ]
    · have hQp : 0 < Shao.energy a := lt_of_le_of_ne (Shao.energy_nonneg a) (Ne.symm hQ)
      have hp : 0 < y * Real.sqrt (Shao.energy a) := mul_pos hy (Real.sqrt_pos.mpr hQp)
      constructor
      · exact fun h => h.trans (le_max_right _ _)
      · intro h
        rcases (le_max_iff).mp h with h | h
        · exact False.elim ((not_le_of_gt hp) h)
        · exact h
  rw [hevent] at he
  have hPsi : 0 < Shao.standardNormalTail y := (Shao.standardNormalTail_basic.2.2.1 y).1
  have hPsile : Shao.standardNormalTail y ≤ 1 := (Shao.standardNormalTail_basic.2.2.1 y).2.le
  have hBy : 0 ≤ Shao.truncationBudget nu n y := Shao.truncationBudget_nonneg nu n hnu2 y
  let p : ℝ := (Measure.pi (fun _ : Fin n => mu)).real
    {a : Shao.Path n | y * Real.sqrt (Shao.energy a) ≤ Shao.maxWithZero (s • a)}
  change |p - 2 * Shao.standardNormalTail y| ≤ 27 * C * R
  change |p / Shao.standardNormalTail y - 2| ≤ C * Shao.truncationBudget nu n y at he
  calc
    |p - 2 * Shao.standardNormalTail y| =
        |(p / Shao.standardNormalTail y - 2) * Shao.standardNormalTail y| := by
      congr 1
      field_simp
    _ = |p / Shao.standardNormalTail y - 2| * Shao.standardNormalTail y := by
      rw [abs_mul, abs_of_pos hPsi]
    _ ≤ (C * Shao.truncationBudget nu n y) * Shao.standardNormalTail y :=
      mul_le_mul_of_nonneg_right he hPsi.le
    _ ≤ C * Shao.truncationBudget nu n y :=
      mul_le_of_le_one_right (mul_nonneg hC.le hBy) hPsile
    _ ≤ 27 * C * R := by nlinarith [mul_le_mul_of_nonneg_left hRy hC.le]


/- Frozen full private head before body: only specializes the qualified
   original zero-energy producer to its actual product-coordinate family. -/
private theorem fsc_original_zero_mass
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (n : ℕ) (hn : 0 < n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) mu)
    (hpos : 0 < ∫ z : ℝ, z ^ 2 ∂mu) :
    let sigma : ℝ := Real.sqrt (∫ z : ℝ, z ^ 2 ∂mu)
    let nu : Measure ℝ := Measure.map
      (fun z : ℝ => z / (sigma * Real.sqrt (n : ℝ))) mu
    (Measure.pi (fun _ : Fin n => mu)).real {a : Shao.Path n | Shao.energy a = 0} ≤
      16 * Shao.truncationBudget nu n 0 := by
  classical
  intro sigma nu
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
  have hI : iIndepFun (fun i : Fin n => Function.eval i) P :=
    iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable)
  have hLaw (i : Fin n) : IdentDistrib (Function.eval i) (id : ℝ → ℝ) P mu := by
    refine ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    exact (measurePreserving_eval (fun _ : Fin n => mu) i).map_eq.trans Measure.map_id.symm
  have h := SourceOriginalZeroEnergyBudget.original_iid_zero_energy_budget P mu n hn
    (fun i : Fin n => Function.eval i) (fun i => (measurable_pi_apply i).aemeasurable)
    hI hLaw h2 hpos
  have hscale : Real.sqrt ((n : ℝ) * ∫ z : ℝ, z ^ 2 ∂mu) =
      sigma * Real.sqrt (n : ℝ) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg n)]
    exact mul_comm _ _
  simpa only [hscale, Shao.energy, Function.eval] using h


theorem finite_second_one_sided_compact_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ (mu : Measure ℝ) [IsProbabilityMeasure mu]
        (n : ℕ) (hn : 0 < n),
        Integrable (fun z : ℝ => z ^ 2) mu →
        (∫ z : ℝ, z ∂mu) = 0 →
        (0 < ∫ z : ℝ, z ^ 2 ∂mu) →
        let sigma : ℝ := Real.sqrt (∫ z : ℝ, z ^ 2 ∂mu)
        let normalizedLaw : Measure ℝ := Measure.map
          (fun z : ℝ => z / (sigma * Real.sqrt (n : ℝ))) mu
        let R : ℝ := Shao.truncationBudget normalizedLaw n 0
        let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
        ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
          ∀ s : ℝ, (s = 1 ∨ s = -1) →
            |P.real {a : Shao.Path n |
                x * Real.sqrt (Shao.energy a) ≤ Shao.maxWithZero (s • a)} -
              2 * Shao.standardNormalTail x| ≤ C * R := by
  classical
  obtain ⟨rho, C0, hrho, hrho16, hC0, hthird⟩ := fsc_third_moment_compact_input
  let C : ℝ := 27 * C0 + 16 + 108 / rho
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro mu _ n hn h2 hmean hpos sigma normalizedLaw R P x hx hx1 s hs
  have hnormm : Measurable (fun z : ℝ => z / (sigma * Real.sqrt (n : ℝ))) :=
    measurable_id.div_const _
  have hnorm2 : Integrable (fun z : ℝ => z ^ 2) normalizedLaw := by
    apply (integrable_map_measure (by fun_prop) hnormm.aemeasurable).2
    simpa only [Function.comp_def, div_pow] using h2.div_const ((sigma * Real.sqrt (n : ℝ)) ^ 2)
  have hR : 0 ≤ R := Shao.truncationBudget_nonneg normalizedLaw n hnorm2 0
  have htail (t : ℝ) (ht : 0 ≤ t) :
      0 ≤ 2 * Shao.standardNormalTail t ∧ 2 * Shao.standardNormalTail t ≤ 1 := by
    have hp := (Shao.standardNormalTail_basic.2.2.1 t).1
    have hu := Shao.standardNormalTail_basic.1 ht
    rw [Shao.standardNormalTail_basic.2.1] at hu
    constructor <;> linarith
  by_cases hlarge : rho / 108 ≤ R
  · have he : |P.real {a : Shao.Path n |
        x * Real.sqrt (Shao.energy a) ≤ Shao.maxWithZero (s • a)} -
        2 * Shao.standardNormalTail x| ≤ 1 := by
      have hp0 : 0 ≤ P.real {a : Shao.Path n |
          x * Real.sqrt (Shao.energy a) ≤ Shao.maxWithZero (s • a)} := measureReal_nonneg
      have hp1 : P.real {a : Shao.Path n |
          x * Real.sqrt (Shao.energy a) ≤ Shao.maxWithZero (s • a)} ≤ 1 := measureReal_le_one
      exact abs_le.mpr ⟨by linarith [(htail x hx).2], by linarith [(htail x hx).1]⟩
    apply he.trans
    have hsmallmul : 1 ≤ (108 / rho) * R := by
      have h := mul_le_mul_of_nonneg_left hlarge (show 0 ≤ 108 / rho by positivity)
      have heq : (108 / rho) * (rho / 108) = (1 : ℝ) := by field_simp
      simpa only [heq] using h
    dsimp [C]
    nlinarith [mul_nonneg (show 0 ≤ 27 * C0 + 16 by positivity) hR]
  by_cases hx0 : x = 0
  · subst x
    have hevent : {a : Shao.Path n | (0 : ℝ) * Real.sqrt (Shao.energy a) ≤
        Shao.maxWithZero (s • a)} = Set.univ := by
      ext a
      simp only [zero_mul, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact Shao.maxWithZero_nonneg _
    rw [hevent, probReal_univ, Shao.standardNormalTail_basic.2.1]
    norm_num
    exact mul_nonneg (by dsimp [C]; positivity) hR
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hsmall : R < rho / 108 := lt_of_not_ge hlarge
  let cut : ℕ → ℝ → ℝ := fun K z => if |z| ≤ (K : ℝ) + 1 then z else 0
  let center : ℕ → ℝ := fun K => ∫ z : ℝ, cut K z ∂mu
  let Y : ℕ → ℝ → ℝ := fun K z => cut K z - center K
  let v : ℕ → ℝ := fun K => ∫ z : ℝ, (Y K z) ^ 2 ∂mu
  let muK : ℕ → Measure ℝ := fun K => Measure.map (Y K) mu
  let nuK : ℕ → Measure ℝ := fun K => Measure.map
    (fun z : ℝ => z / (Real.sqrt (v K) * Real.sqrt (n : ℝ))) (muK K)
  let RK : ℕ → ℝ := fun K => Shao.truncationBudget (nuK K) n 0
  obtain ⟨hKs, hcenterlim, hYlim, hL2lim, hvlim, hvlo, hbudgetlim⟩ :=
    centered_bounded_truncation_budget_limit mu n hn h2 hmean hpos
  have hYm (K : ℕ) : Measurable (Y K) := (hKs K).1
  have hY2 (K : ℕ) : Integrable (fun z : ℝ => (Y K z) ^ 2) mu := (hKs K).2.2.1
  have hY3 (K : ℕ) : Integrable (fun z : ℝ => Real.rpow |Y K z| 3) mu := (hKs K).2.2.2.1
  have hY0 (K : ℕ) : (∫ z : ℝ, Y K z ∂mu) = 0 := (hKs K).2.2.2.2.1
  have hpK (K : ℕ) : IsProbabilityMeasure (muK K) := (hKs K).2.2.2.2.2.1
  have hRKlim : Tendsto RK atTop (𝓝 R) := hbudgetlim 0
  have hRKe : ∀ᶠ K : ℕ in atTop, RK K < rho / 27 :=
    (tendsto_order.1 hRKlim).2 (rho / 27) (by linarith)
  let A : ℕ → Shao.Path n → Shao.Path n := fun K a i => Y K (a i)
  have hAm (K : ℕ) : Measurable (A K) :=
    Measurable.of_eval fun i => (hYm K).comp (measurable_pi_apply i)
  have hAlim (a : Shao.Path n) : Tendsto (fun K : ℕ => A K a) atTop (𝓝 a) :=
    tendsto_pi_nhds.mpr fun i => hYlim (a i)
  have hmap (K : ℕ) : Measure.map (A K) P = Measure.pi (fun _ : Fin n => muK K) := by
    letI := hpK K
    exact Measure.pi_map_pi (fun _ : Fin n => (hYm K).aemeasurable)
  let M : Shao.Path n → ℝ := fun a => Shao.maxWithZero (s • a)
  let QK : ℕ → Shao.Path n → ℝ := fun K a => Shao.energy (A K a)
  let MK : ℕ → Shao.Path n → ℝ := fun K a => M (A K a)
  have hsm : Measurable (fun a : Shao.Path n => s • a) :=
    Measurable.of_eval fun i => measurable_const.mul (measurable_pi_apply i)
  have hMm : Measurable M := Shao.measurable_maxWithZero.comp hsm
  have hQm (K : ℕ) : Measurable (QK K) := Shao.measurable_energy.comp (hAm K)
  have hMKm (K : ℕ) : Measurable (MK K) := hMm.comp (hAm K)
  let E : Set (Shao.Path n) := {a | x * Real.sqrt (Shao.energy a) ≤ M a}
  let E0 : Set (Shao.Path n) := {a | Shao.energy a = 0}
  let EK : ℕ → ℝ → Set (Shao.Path n) := fun K y =>
    {a | y * Real.sqrt (QK K a) ≤ MK K a}
  let p : ℝ := P.real E
  let p0 : ℝ := P.real E0
  let q : ℕ → ℝ → ℝ := fun K y => P.real (EK K y)
  have hp0 : p0 ≤ 16 * R := fsc_original_zero_mass mu n hn h2 hpos
  have hq (y : ℝ) (hy : 0 < y) (hy2 : y ≤ 2) :
      ∀ᶠ K : ℕ in atTop, |q K y - 2 * Shao.standardNormalTail y| ≤ 27 * C0 * RK K := by
    filter_upwards [hvlo, hRKe] with K hvK hRK
    letI := hpK K
    have h2K : Integrable (fun z : ℝ => z ^ 2) (muK K) := by
      exact (integrable_map_measure (by fun_prop) (hYm K).aemeasurable).2 (hY2 K)
    have h3m : AEStronglyMeasurable (fun z : ℝ => Real.rpow |z| 3) (muK K) := by
      have he : (fun z : ℝ => Real.rpow |z| 3) = fun z => |z| ^ 3 := by
        funext z
        exact Real.rpow_natCast _ 3
      rw [he]
      exact (continuous_abs.pow 3).aestronglyMeasurable
    have h3K : Integrable (fun z : ℝ => Real.rpow |z| 3) (muK K) :=
      (integrable_map_measure h3m (hYm K).aemeasurable).2 (hY3 K)
    have hmeanK : (∫ z : ℝ, z ∂muK K) = 0 := by
      rw [show muK K = Measure.map (Y K) mu from rfl,
        integral_map (μ := mu) (f := fun z : ℝ => z) (hYm K).aemeasurable continuous_id.aestronglyMeasurable]
      exact hY0 K
    have hsecondK : (∫ z : ℝ, z ^ 2 ∂muK K) = v K := by
      rw [show muK K = Measure.map (Y K) mu from rfl,
        integral_map (μ := mu) (f := fun z : ℝ => z ^ 2) (hYm K).aemeasurable (continuous_id.pow 2).aestronglyMeasurable]
    have hposK : 0 < ∫ z : ℝ, z ^ 2 ∂muK K := by rw [hsecondK]; change 0 < v K; linarith
    have hbound := hthird (muK K) n hn h2K hmeanK hposK h3K
    dsimp only at hbound
    rw [hsecondK] at hbound
    have hb := hbound hRK y hy hy2 s hs
    have hset : MeasurableSet {a : Shao.Path n |
        y * Real.sqrt (Shao.energy a) ≤ M a} :=
      measurableSet_le (Shao.measurable_energyWall y) hMm
    have hprob : q K y = (Measure.pi (fun _ : Fin n => muK K)).real
        {a : Shao.Path n | y * Real.sqrt (Shao.energy a) ≤ M a} := by
      rw [← hmap K, Measure.real_def, Measure.map_apply (hAm K) hset]
      rfl
    rw [hprob]
    exact hb
  let f : Shao.Path n → ℝ := fun a => M a / Real.sqrt (Shao.energy a)
  let fK : ℕ → Shao.Path n → ℝ := fun K a => MK K a / Real.sqrt (QK K a)
  have hfm : Measurable f := hMm.div (Real.continuous_sqrt.measurable.comp Shao.measurable_energy)
  have hfKm (K : ℕ) : Measurable (fK K) :=
    (hMKm K).div (Real.continuous_sqrt.measurable.comp (hQm K))
  have hQlim (a : Shao.Path n) : Tendsto (fun K : ℕ => QK K a) atTop (𝓝 (Shao.energy a)) :=
    Shao.continuous_energy.continuousAt.tendsto.comp (hAlim a)
  have hMlim (a : Shao.Path n) : Tendsto (fun K : ℕ => MK K a) atTop (𝓝 (M a)) :=
    Shao.continuous_maxWithZero.continuousAt.tendsto.comp (tendsto_const_nhds.smul (hAlim a))
  have hflim (a : Shao.Path n) (ha : 0 < Shao.energy a) :
      Tendsto (fun K : ℕ => fK K a) atTop (𝓝 (f a)) :=
    (hMlim a).div (Real.continuous_sqrt.continuousAt.tendsto.comp (hQlim a))
      (Real.sqrt_pos.mpr ha).ne'
  have hclaim (eps : ℝ) (heps : 0 < eps) (hepsx : eps < x) (heps1 : eps ≤ 1) :
      p ≤ 2 * Shao.standardNormalTail (x - eps) + 27 * C0 * R + p0 ∧
      2 * Shao.standardNormalTail (x + eps) - 27 * C0 * R - p0 ≤ p := by
    let Bad : ℕ → Set (Shao.Path n) := fun K =>
      {a | 0 < Shao.energy a ∧ (QK K a = 0 ∨ eps ≤ |fK K a - f a|)}
    have hBadm (K : ℕ) : MeasurableSet (Bad K) :=
      (measurableSet_lt measurable_const Shao.measurable_energy).inter
        ((measurableSet_eq_fun (hQm K) measurable_const).union
          (measurableSet_le measurable_const (continuous_abs.measurable.comp ((hfKm K).sub hfm))))
    have hBadzero (a : Shao.Path n) : ∀ᶠ K : ℕ in atTop, a ∉ Bad K := by
      by_cases ha : 0 < Shao.energy a
      · have hposQ := (tendsto_order.1 (hQlim a)).1 0 ha
        have hl : Tendsto (fun K : ℕ => |fK K a - f a|) atTop (𝓝 0) := by
          simpa only [sub_self, abs_zero] using ((hflim a ha).sub_const (f a)).abs
        have herr := (tendsto_order.1 hl).2 eps heps
        filter_upwards [hposQ, herr] with K hK hE
        simp only [Bad, Set.mem_setOf_eq, ha, true_and, not_or, not_le]
        exact ⟨hK.ne', hE⟩
      · exact Eventually.of_forall fun K => by simp [Bad, ha]
    have hBadlim := fsc_vanishing_event_probability P Bad hBadm hBadzero
    have hsublo (K : ℕ) : E ⊆ (EK K (x - eps) ∪ E0) ∪ Bad K := by
      intro a ha
      by_cases h0 : a ∈ E0
      · exact Or.inl (Or.inr h0)
      by_cases hB : a ∈ Bad K
      · exact Or.inr hB
      have hQa : 0 < Shao.energy a := lt_of_le_of_ne (Shao.energy_nonneg a) (Ne.symm h0)
      have hb : QK K a ≠ 0 ∧ |fK K a - f a| < eps := by
        simpa only [Bad, Set.mem_setOf_eq, hQa, true_and, not_or, not_le] using hB
      have hQKa : 0 < QK K a := lt_of_le_of_ne (Shao.energy_nonneg _) (Ne.symm hb.1)
      have hfa : x ≤ f a := (le_div_iff₀ (Real.sqrt_pos.mpr hQa)).mpr ha
      have hfk : x - eps ≤ fK K a := by linarith [(abs_lt.mp hb.2).1]
      exact Or.inl (Or.inl ((le_div_iff₀ (Real.sqrt_pos.mpr hQKa)).mp hfk))
    have hsubhi (K : ℕ) : EK K (x + eps) ⊆ (E ∪ E0) ∪ Bad K := by
      intro a ha
      by_cases h0 : a ∈ E0
      · exact Or.inl (Or.inr h0)
      by_cases hB : a ∈ Bad K
      · exact Or.inr hB
      have hQa : 0 < Shao.energy a := lt_of_le_of_ne (Shao.energy_nonneg a) (Ne.symm h0)
      have hb : QK K a ≠ 0 ∧ |fK K a - f a| < eps := by
        simpa only [Bad, Set.mem_setOf_eq, hQa, true_and, not_or, not_le] using hB
      have hQKa : 0 < QK K a := lt_of_le_of_ne (Shao.energy_nonneg _) (Ne.symm hb.1)
      have hfk : x + eps ≤ fK K a := (le_div_iff₀ (Real.sqrt_pos.mpr hQKa)).mpr ha
      have hfa : x ≤ f a := by linarith [(abs_lt.mp hb.2).2]
      exact Or.inl (Or.inl ((le_div_iff₀ (Real.sqrt_pos.mpr hQa)).mp hfa))
    have hplo (K : ℕ) : p ≤ q K (x - eps) + p0 + P.real (Bad K) :=
      (measureReal_mono (hsublo K)).trans ((measureReal_union_le _ _).trans
        (add_le_add (measureReal_union_le _ _) le_rfl))
    have hphi (K : ℕ) : q K (x + eps) ≤ p + p0 + P.real (Bad K) :=
      (measureReal_mono (hsubhi K)).trans ((measureReal_union_le _ _).trans
        (add_le_add (measureReal_union_le _ _) le_rfl))
    have helo := hq (x - eps) (by linarith) (by linarith)
    have hehi := hq (x + eps) (by linarith) (by linarith)
    have hulim : Tendsto
        (fun K : ℕ => 2 * Shao.standardNormalTail (x - eps) + 27 * C0 * RK K + p0 + P.real (Bad K))
        atTop (𝓝 (2 * Shao.standardNormalTail (x - eps) + 27 * C0 * R + p0)) := by
      simpa only [add_zero] using
        ((tendsto_const_nhds.add (tendsto_const_nhds.mul hRKlim)).add tendsto_const_nhds).add hBadlim
    have hllim : Tendsto
        (fun K : ℕ => 2 * Shao.standardNormalTail (x + eps) - 27 * C0 * RK K - p0 - P.real (Bad K))
        atTop (𝓝 (2 * Shao.standardNormalTail (x + eps) - 27 * C0 * R - p0)) := by
      simpa only [sub_zero] using
        ((tendsto_const_nhds.sub (tendsto_const_nhds.mul hRKlim)).sub tendsto_const_nhds).sub hBadlim
    constructor
    · apply le_of_tendsto_of_tendsto tendsto_const_nhds hulim
      filter_upwards [helo] with K hK
      linarith [(abs_le.mp hK).2, hplo K]
    · apply le_of_tendsto_of_tendsto hllim tendsto_const_nhds
      filter_upwards [hehi] with K hK
      linarith [(abs_le.mp hK).1, hphi K]
  let eps : ℕ → ℝ := fun j => (x / 2) * (1 / ((j : ℝ) + 1))
  have hepslim : Tendsto eps atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (x / 2)
  have heps (j : ℕ) : 0 < eps j ∧ eps j < x ∧ eps j ≤ 1 := by
    have hi : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 := by
      apply (div_le_one (by positivity : (0 : ℝ) < (j : ℝ) + 1)).mpr
      linarith [show (0 : ℝ) ≤ (j : ℝ) from Nat.cast_nonneg j]
    have hip : 0 < (1 : ℝ) / ((j : ℝ) + 1) := by positivity
    dsimp [eps]
    have hup := mul_le_mul_of_nonneg_left hi (by linarith : 0 ≤ x / 2)
    constructor
    · positivity
    · constructor <;> nlinarith
  have htcont : Continuous Shao.standardNormalTail :=
    continuous_iff_continuousAt.mpr fun t => (Shao.standardNormal_derivatives t).2.continuousAt
  have hulim : Tendsto
      (fun j : ℕ => 2 * Shao.standardNormalTail (x - eps j) + 27 * C0 * R + p0)
      atTop (𝓝 (2 * Shao.standardNormalTail x + 27 * C0 * R + p0)) := by
    simpa only [sub_zero, Function.comp_def] using
      ((tendsto_const_nhds.mul (htcont.continuousAt.tendsto.comp
        (tendsto_const_nhds.sub hepslim))).add_const (27 * C0 * R)).add_const p0
  have hllim : Tendsto
      (fun j : ℕ => 2 * Shao.standardNormalTail (x + eps j) - 27 * C0 * R - p0)
      atTop (𝓝 (2 * Shao.standardNormalTail x - 27 * C0 * R - p0)) := by
    simpa only [add_zero, Function.comp_def] using
      ((tendsto_const_nhds.mul (htcont.continuousAt.tendsto.comp
        (tendsto_const_nhds.add hepslim))).sub_const (27 * C0 * R)).sub_const p0
  have hu : p ≤ 2 * Shao.standardNormalTail x + 27 * C0 * R + p0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hulim (Eventually.of_forall fun j =>
      (hclaim (eps j) (heps j).1 (heps j).2.1 (heps j).2.2).1)
  have hl : 2 * Shao.standardNormalTail x - 27 * C0 * R - p0 ≤ p :=
    le_of_tendsto_of_tendsto hllim tendsto_const_nhds (Eventually.of_forall fun j =>
      (hclaim (eps j) (heps j).1 (heps j).2.1 (heps j).2.2).2)
  change |p - 2 * Shao.standardNormalTail x| ≤ C * R
  have hab : |p - 2 * Shao.standardNormalTail x| ≤ (27 * C0 + 16) * R :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  apply hab.trans
  dsimp [C]
  nlinarith [mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 108) hrho.le) hR]

end Shao.Probability
