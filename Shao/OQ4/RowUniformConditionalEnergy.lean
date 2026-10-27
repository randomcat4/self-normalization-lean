import Shao.OQ4.UniformConditionalEnergy
import Shao.OQ4.RowEnergyLaplace

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace Shao.OQ4.RowUniformConditionalEnergy

open MeasureTheory Filter Set
open RademacherScalarBounds (lambda)
open UniformConditionalEnergy (energyCoshExcessIntegral)
open scoped Topology

-- PRIVATE 1: purely scalar; admissibility is required only eventually.
private theorem selected_radius_scales
    (h : ℕ → ℝ) (n : ℕ → ℕ) (b : ℕ → ℝ)
    (C : ℝ) (hC : 1 ≤ C)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun j => (n j : ℝ) / h j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (n j : ℝ) / h j ^ 3)
      atTop (𝓝 (0 : ℝ)))
    (hb : ∀ᶠ j in atTop, h j / 2 ≤ b j ∧ b j ≤ C * h j) :
    Tendsto b atTop atTop ∧
      Tendsto (fun j => (n j : ℝ) / b j ^ 2) atTop atTop ∧
      Tendsto (fun j => (n j : ℝ) / b j ^ 3) atTop (𝓝 (0 : ℝ)) := by
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hpos : ∀ᶠ j in atTop, 0 < h j := hinfty.eventually_gt_atTop 0
  have hhalf : Tendsto (fun j => h j / 2) atTop atTop :=
    (tendsto_div_const_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).mpr hinfty
  have hbInf : Tendsto b atTop atTop :=
    tendsto_atTop_mono' atTop (hb.mono fun _ hj => hj.1) hhalf
  have hlongLower : Tendsto (fun j => ((n j : ℝ) / h j ^ 2) / C ^ 2) atTop atTop :=
    (tendsto_div_const_atTop_of_pos (sq_pos_of_pos hCpos)).mpr hlong
  have hlongBound : ∀ᶠ j in atTop,
      ((n j : ℝ) / h j ^ 2) / C ^ 2 ≤ (n j : ℝ) / b j ^ 2 := by
    filter_upwards [hb, hpos] with j hj hh
    have hbj : 0 < b j := lt_of_lt_of_le (half_pos hh) hj.1
    have hden : b j ^ 2 ≤ C ^ 2 * h j ^ 2 := by
      simpa only [mul_pow] using pow_le_pow_left₀ hbj.le hj.2 2
    calc
      _ = (n j : ℝ) / (C ^ 2 * h j ^ 2) := by
        rw [div_div]
        congr 1
        ring
      _ ≤ (n j : ℝ) / b j ^ 2 := by
        apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hCpos) (sq_pos_of_pos hh))
          (sq_pos_of_pos hbj)).mpr
        exact mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg _)
  have hbLong : Tendsto (fun j => (n j : ℝ) / b j ^ 2) atTop atTop :=
    tendsto_atTop_mono' atTop hlongBound hlongLower
  have hnonneg : ∀ᶠ j in atTop, 0 ≤ (n j : ℝ) / b j ^ 3 := by
    filter_upwards [hb, hpos] with j hj hh
    have hbj : 0 < b j := lt_of_lt_of_le (half_pos hh) hj.1
    exact div_nonneg (Nat.cast_nonneg _) (pow_pos hbj 3).le
  have hupper : ∀ᶠ j in atTop,
      (n j : ℝ) / b j ^ 3 ≤ 8 * ((n j : ℝ) / h j ^ 3) := by
    filter_upwards [hb, hpos] with j hj hh
    have hbj : 0 < b j := lt_of_lt_of_le (half_pos hh) hj.1
    have hcube : h j ^ 3 ≤ 8 * b j ^ 3 := by
      have hp := pow_le_pow_left₀ (half_pos hh).le hj.1 3
      nlinarith
    calc
      _ ≤ (8 * (n j : ℝ)) / h j ^ 3 := by
        apply (div_le_div_iff₀ (pow_pos hbj 3) (pow_pos hh 3)).mpr
        have hm := mul_le_mul_of_nonneg_left hcube (Nat.cast_nonneg (n j) : (0 : ℝ) ≤ n j)
        nlinarith
      _ = 8 * ((n j : ℝ) / h j ^ 3) := by ring
  have hzero : Tendsto (fun j => 8 * ((n j : ℝ) / h j ^ 3)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (8 : ℝ)) atTop (𝓝 8)).mul hshort
  exact ⟨hbInf, hbLong, squeeze_zero' hnonneg hupper hzero⟩

-- PRIVATE 2: selected actual radii; row law/moment hypotheses are explicit.
-- Its bounded parameters are internally patched, never additional public inputs.
-- The finite integrability and integral identity are derived body-locally.
private theorem selected_radius_energy_ratio_tendsto
    (νSeq : ℕ → Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ)
    (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun j => (n j : ℝ) / h j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (n j : ℝ) / h j ^ 3)
      atTop (𝓝 (0 : ℝ)))
    (b : ℕ → ℝ) (C : ℝ) (hC : 1 ≤ C)
    (hb : ∀ᶠ j in atTop, h j / 2 ≤ b j ∧ b j ≤ C * h j)
    (s : ℝ) (hs : 0 < s) :
    Tendsto (fun j =>
      energyCoshExcessIntegral (νSeq j) (n j) (b j) (h j) s /
        (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
          (@Shao.closedStrip (n j) (b j)))
      atTop (𝓝 (0 : ℝ)) := by
  classical
  obtain ⟨hbInf, hbLong, hbShort⟩ := selected_radius_scales h n b C hC hinfty hlong hshort hb
  let H : ℕ → Prop := fun j => 0 < h j ∧ h j / 2 ≤ b j ∧ b j ≤ C * h j
  let u : ℕ → ℝ := fun j => if H j then s * (b j / h j) ^ 2 else 0
  let T : ℝ := s * C ^ 2
  have hT : 0 ≤ T := mul_nonneg hs.le (sq_nonneg _)
  have hu (j : ℕ) : |u j| ≤ T := by
    by_cases hj : H j
    · have hbpos : 0 < b j := lt_of_lt_of_le (half_pos hj.1) hj.2.1
      have hr0 : 0 ≤ b j / h j := div_nonneg hbpos.le hj.1.le
      have hrC : b j / h j ≤ C := (div_le_iff₀ hj.1).mpr hj.2.2
      have hr2 : (b j / h j) ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ hr0 hrC 2
      simp only [u, if_pos hj, abs_of_nonneg (mul_nonneg hs.le (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_left hr2 hs.le
    · simpa only [u, if_neg hj, abs_zero] using hT
  have hum (j : ℕ) : |-(u j)| ≤ T := by simpa only [abs_neg] using hu j
  have hH : ∀ᶠ j in atTop, H j := by
    filter_upwards [hb, hinfty.eventually_gt_atTop 0] with j hj hh
    exact ⟨hh, hj⟩
  let G : ℕ → ℝ := fun j =>
    (Measure.pi (fun _ : Fin (n j) => νSeq j)).real (@Shao.closedStrip (n j) (b j))
  let U : ℕ → ℝ := fun j =>
    (energyJointIntegral (νSeq j) (n j) (b j) (u j) / G j +
      energyJointIntegral (νSeq j) (n j) (b j) (-(u j)) / G j) / 2 - 1
  have hp := RowEnergyLaplace.varying_row_energy_laplace_ratio_tendsto
    νSeq hprob h3 hmean hsecond M hM b n hbInf hbLong hbShort T hT u hu
  have hm := RowEnergyLaplace.varying_row_energy_laplace_ratio_tendsto
    νSeq hprob h3 hmean hsecond M hM b n hbInf hbLong hbShort T hT (fun j => -(u j)) hum
  have hU : Tendsto U atTop (𝓝 (0 : ℝ)) := by
    simpa only [U, G, show ((1 : ℝ) + 1) / 2 - 1 = 0 by norm_num] using
      ((hp.add hm).div_const 2).sub_const 1
  have hGpos : ∀ᶠ j in atTop, 0 < G j :=
    RowEnergyLaplace.varying_row_closedStrip_probability_eventually_pos
      νSeq hprob h3 hmean hsecond M hM b n hbInf hbLong hbShort
  have identity (ν : Measure ℝ) [IsProbabilityMeasure ν]
      (n : ℕ) (b h s T : ℝ) (hT : 0 ≤ T) (hb1 : 1 ≤ b) (hh : 0 < h)
      (hu : |s * (b / h) ^ 2| ≤ T) :
      Integrable (fun a : Shao.Path n =>
        if a ∈ (@Shao.closedStrip n b) then
          (Real.exp (s * (Shao.energy a - (n : ℝ)) / h ^ 2) +
            Real.exp (-(s * (Shao.energy a - (n : ℝ)) / h ^ 2))) / 2 - 1
        else 0) (Measure.pi (fun _ : Fin n => ν)) ∧
        energyCoshExcessIntegral ν n b h s =
          (energyJointIntegral ν n b (s * (b / h) ^ 2) +
            energyJointIntegral ν n b (-(s * (b / h) ^ 2))) / 2 -
            (Measure.pi (fun _ : Fin n => ν)).real (@Shao.closedStrip n b) := by
    classical
    have hb : 0 < b := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hb1
    let μ : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ν)
    let A : Set (Shao.Path n) := Shao.closedStrip b
    let IA : Shao.Path n → ℝ := A.indicator (fun _ => 1)
    let u : ℝ := s * (b / h) ^ 2
    let f : Shao.Path n → ℝ := fun a =>
      if a ∈ A then
        (Real.exp (s * (Shao.energy a - (n : ℝ)) / h ^ 2) +
          Real.exp (-(s * (Shao.energy a - (n : ℝ)) / h ^ 2))) / 2 - 1
      else 0
    have hA : MeasurableSet A := by
      dsimp only [A]
      rw [← shiftedClosedSurvival_eq_closedStrip n b hb.le]
      exact measurableSet_shiftedClosedSurvival n b 0
    have hiA : Integrable IA μ := (integrable_const (1 : ℝ)).indicator hA
    have hiP : Integrable (energyPathIntegrand (n := n) b u) μ :=
      energyPathIntegrand_integrable ν n T b u hT hb1 hu
    have hiM : Integrable (energyPathIntegrand (n := n) b (-u)) μ :=
      energyPathIntegrand_integrable ν n T b (-u) hT hb1 (by simpa only [abs_neg] using hu)
    have hscale (q : ℝ) : u * q / b ^ 2 = s * q / h ^ 2 := by
      dsimp only [u]
      field_simp [hb.ne', hh.ne']
      <;> ring
    have hscaleNeg (q : ℝ) : (-u) * q / b ^ 2 = -(s * q / h ^ 2) := by
      rw [neg_mul, neg_div, hscale]
    have hpoint (a : Shao.Path n) :
        f a = (energyPathIntegrand b u a + energyPathIntegrand b (-u) a) / 2 - IA a := by
      by_cases ha : a ∈ A
      · have ha' : a ∈ Shao.closedStrip b := ha
        simp only [f, if_pos ha, energyPathIntegrand, if_pos ha',
          hscale, hscaleNeg, IA, Set.indicator_of_mem ha]
      · have ha' : a ∉ Shao.closedStrip b := ha
        simp [f, ha, energyPathIntegrand, ha', IA]
    have hif : Integrable f μ :=
      (((hiP.add hiM).div_const 2).sub hiA).congr
        (Eventually.of_forall fun a => (hpoint a).symm)
    have hIA : (∫ a, IA a ∂μ) = μ.real A := by
      simpa only [IA, measureReal_def, show (1 : Shao.Path n → ℝ) = (fun _ => 1) from rfl] using
        (integral_indicator_one (μ := μ) hA)
    refine ⟨hif, ?_⟩
    have hJ : energyCoshExcessIntegral ν n b h s =
        ∫ a, (energyPathIntegrand b u a + energyPathIntegrand b (-u) a) / 2 - IA a ∂μ := by
      change (∫ a, f a ∂μ) = _
      exact integral_congr_ae (Eventually.of_forall hpoint)
    have hiSum : Integrable (fun a => energyPathIntegrand b u a +
        energyPathIntegrand b (-u) a) μ := hiP.add hiM
    have hiDiv : Integrable (fun a => (energyPathIntegrand b u a +
        energyPathIntegrand b (-u) a) / 2) μ := hiSum.div_const 2
    have hdiv : (fun a : Shao.Path n =>
        (energyPathIntegrand b u a + energyPathIntegrand b (-u) a) / 2) =
        (fun a => (2 : ℝ)⁻¹ * (energyPathIntegrand b u a + energyPathIntegrand b (-u) a)) := by
      funext a
      ring
    rw [hJ, integral_sub hiDiv hiA, hdiv, integral_const_mul, integral_add hiP hiM, hIA]
    dsimp only [u, energyJointIntegral, μ, A]
    ring
  apply hU.congr'
  filter_upwards [hH, hbInf.eventually_ge_atTop 1, hGpos] with j hj hb1 hGj
  have he : u j = s * (b j / h j) ^ 2 := if_pos hj
  letI := hprob j
  have hi := (identity (νSeq j) (n j) (b j) (h j) s T hT hb1 hj.1
    (by simpa only [he] using hu j)).2
  rw [← he] at hi
  dsimp only [U]
  rw [hi]
  change _ = _ / G j
  field_simp [hGj.ne']
  <;> ring

-- PUBLIC 1: one tail, all actual radii in [h_j/2, C*h_j], literal G and J.
theorem varying_row_uniform_closedStrip_energy_controls
    (νSeq : ℕ → Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ)
    (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun j => (n j : ℝ) / h j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (n j : ℝ) / h j ^ 3)
      atTop (𝓝 (0 : ℝ)))
    (C : ℝ) (hC : 1 ≤ C) (s : ℝ) (hs : 0 < s)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ j in atTop, ∀ b : ℝ, h j / 2 ≤ b → b ≤ C * h j →
      0 < (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
        (@Shao.closedStrip (n j) b) ∧
      |(Measure.pi (fun _ : Fin (n j) => νSeq j)).real
          (@Shao.closedStrip (n j) b) /
            ((4 / Real.pi) * Real.exp (-lambda * (n j : ℝ) / b ^ 2)) - 1| < δ ∧
      0 ≤ energyCoshExcessIntegral (νSeq j) (n j) b (h j) s /
        (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
          (@Shao.closedStrip (n j) b) ∧
      energyCoshExcessIntegral (νSeq j) (n j) b (h j) s /
        (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
          (@Shao.closedStrip (n j) b) < δ := by
  classical
  let P : ℕ → ℝ → Prop := fun j b =>
    0 < (Measure.pi (fun _ : Fin (n j) => νSeq j)).real (@Shao.closedStrip (n j) b) ∧
    |(Measure.pi (fun _ : Fin (n j) => νSeq j)).real (@Shao.closedStrip (n j) b) /
      ((4 / Real.pi) * Real.exp (-lambda * (n j : ℝ) / b ^ 2)) - 1| < δ ∧
    0 ≤ energyCoshExcessIntegral (νSeq j) (n j) b (h j) s /
      (Measure.pi (fun _ : Fin (n j) => νSeq j)).real (@Shao.closedStrip (n j) b) ∧
    energyCoshExcessIntegral (νSeq j) (n j) b (h j) s /
      (Measure.pi (fun _ : Fin (n j) => νSeq j)).real (@Shao.closedStrip (n j) b) < δ
  have hselected (b : ℕ → ℝ)
      (hb : ∀ᶠ j in atTop, h j / 2 ≤ b j ∧ b j ≤ C * h j) :
      ∀ᶠ j in atTop, P j (b j) := by
    obtain ⟨hbInf, hbLong, hbShort⟩ := selected_radius_scales h n b C hC hinfty hlong hshort hb
    let bp : ℕ → ℝ := fun j => max (b j) 1
    have heq : bp =ᶠ[atTop] b := by
      filter_upwards [hbInf.eventually_ge_atTop 1] with j hj
      exact max_eq_left hj
    have hpInf : Tendsto bp atTop atTop := hbInf.congr' heq.symm
    have hpLong : Tendsto (fun j => (n j : ℝ) / bp j ^ 2) atTop atTop := by
      apply hbLong.congr'
      exact heq.symm.mono fun j hj => by dsimp only; rw [hj]
    have hpShort : Tendsto (fun j => (n j : ℝ) / bp j ^ 3) atTop (𝓝 (0 : ℝ)) := by
      apply hbShort.congr'
      exact heq.symm.mono fun j hj => by dsimp only; rw [hj]
    have hKp := UnconditionalKernelAsymptotic.varying_row_closedStrip_relative_asymptotic
      νSeq hprob h3 hmean hsecond M hM bp n
      (fun j => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _))
      hpInf hpLong hpShort
    have hK : Tendsto (fun j =>
        (Measure.pi (fun _ : Fin (n j) => νSeq j)).real (@Shao.closedStrip (n j) (b j)) /
          ((4 / Real.pi) * Real.exp (-lambda * (n j : ℝ) / b j ^ 2)))
        atTop (𝓝 (1 : ℝ)) := by
      apply hKp.congr'
      filter_upwards [heq] with j hj
      rw [hj]
    have hKzero : Tendsto (fun j =>
        |(Measure.pi (fun _ : Fin (n j) => νSeq j)).real
          (@Shao.closedStrip (n j) (b j)) /
            ((4 / Real.pi) * Real.exp (-lambda * (n j : ℝ) / b j ^ 2)) - 1|)
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [sub_self, abs_zero] using (hK.sub_const 1).abs
    have hGpos := RowEnergyLaplace.varying_row_closedStrip_probability_eventually_pos
      νSeq hprob h3 hmean hsecond M hM b n hbInf hbLong hbShort
    have hJ := selected_radius_energy_ratio_tendsto
      νSeq hprob h3 hmean hsecond M hM h n hinfty hlong hshort b C hC hb s hs
    filter_upwards [hGpos, hKzero.eventually (gt_mem_nhds hδ),
      hJ.eventually (gt_mem_nhds hδ)] with j hj hk hsmall
    exact ⟨hj, hk, div_nonneg
      (UniformConditionalEnergy.energyCoshExcessIntegral_nonneg (νSeq j) (n j) (b j) (h j) s) hj.le, hsmall⟩
  let Bad : ℕ → Prop := fun j => ∃ b : ℝ, h j / 2 ≤ b ∧ b ≤ C * h j ∧ ¬P j b
  let β : ℕ → ℝ := fun j => if hj : Bad j then Classical.choose hj else h j
  have hβ : ∀ᶠ j in atTop, h j / 2 ≤ β j ∧ β j ≤ C * h j := by
    filter_upwards [hinfty.eventually_gt_atTop 0] with j hj
    by_cases hbad : Bad j
    · have hc := Classical.choose_spec hbad
      simpa only [β, dif_pos hbad] using And.intro hc.1 hc.2.1
    · simp only [β, dif_neg hbad]
      constructor
      · linarith
      · simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hj.le
  have hP : ∀ᶠ j in atTop, P j (β j) := hselected β hβ
  filter_upwards [hP] with j hj b hb0 hb1
  change P j b
  by_contra hnot
  have hbad : Bad j := ⟨b, hb0, hb1, hnot⟩
  have hβbad : ¬P j (β j) := by
    simpa only [β, dif_pos hbad] using (Classical.choose_spec hbad).2.2
  exact hβbad hj

-- PUBLIC 2: simultaneous boundary-ratio bound; includes both strict positivities.
theorem varying_row_uniform_closedStrip_boundary_ratio_bound
    (νSeq : ℕ → Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ)
    (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun j => (n j : ℝ) / h j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (n j : ℝ) / h j ^ 3)
      atTop (𝓝 (0 : ℝ)))
    (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ j in atTop,
      0 < (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
        (@Shao.closedStrip (n j) (h j)) ∧
      ∀ b : ℝ, h j / 2 ≤ b → b ≤ C * h j →
        0 < (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
          (@Shao.closedStrip (n j) b) ∧
        (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
            (@Shao.closedStrip (n j) b) /
          (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
            (@Shao.closedStrip (n j) (h j)) ≤
          4 * Real.exp
            (lambda * ((n j : ℝ) / h j ^ 2 - (n j : ℝ) / b ^ 2)) := by
  have hcontrols := varying_row_uniform_closedStrip_energy_controls νSeq hprob h3 hmean hsecond M hM h n
    hinfty hlong hshort C hC 1 (by norm_num) (1 / 2) (by norm_num)
  filter_upwards [hcontrols, hinfty.eventually_gt_atTop 0] with j hj hh
  have hhlo : h j / 2 ≤ h j := by linarith
  have hhhi : h j ≤ C * h j := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hh.le
  have hself := hj (h j) hhlo hhhi
  refine ⟨hself.1, ?_⟩
  intro b hb0 hb1
  have hB := hj b hb0 hb1
  refine ⟨hB.1, ?_⟩
  let Gb : ℝ := (Measure.pi (fun _ : Fin (n j) => νSeq j)).real (@Shao.closedStrip (n j) b)
  let Gh : ℝ := (Measure.pi (fun _ : Fin (n j) => νSeq j)).real (@Shao.closedStrip (n j) (h j))
  let mb : ℝ := (4 / Real.pi) * Real.exp (-lambda * (n j : ℝ) / b ^ 2)
  let mh : ℝ := (4 / Real.pi) * Real.exp (-lambda * (n j : ℝ) / h j ^ 2)
  let E : ℝ := Real.exp (lambda * ((n j : ℝ) / h j ^ 2 - (n j : ℝ) / b ^ 2))
  have hmb : 0 < mb := mul_pos (div_pos (by norm_num) Real.pi_pos) (Real.exp_pos _)
  have hmh : 0 < mh := mul_pos (div_pos (by norm_num) Real.pi_pos) (Real.exp_pos _)
  have hGh : 0 < Gh := hself.1
  have hqb : Gb / mb ≤ 2 := by
    have hu := (abs_lt.mp hB.2.1).2
    change Gb / mb - 1 < (1 / 2 : ℝ) at hu
    linarith
  have hqh : (1 / 2 : ℝ) ≤ Gh / mh := by
    have hl := (abs_lt.mp hself.2.1).1
    change -(1 / 2 : ℝ) < Gh / mh - 1 at hl
    linarith
  have hGb : Gb ≤ 2 * mb := (div_le_iff₀ hmb).mp hqb
  have hGhMain : mh ≤ 2 * Gh := by
    have hm := (le_div_iff₀ hmh).mp hqh
    linarith
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hexp : Real.exp (-lambda * (n j : ℝ) / b ^ 2) =
      E * Real.exp (-lambda * (n j : ℝ) / h j ^ 2) := by
    dsimp only [E]
    rw [← Real.exp_add]
    congr 1
    ring
  have hmain : mb = E * mh := by
    dsimp only [mb, mh]
    rw [hexp]
    ring
  change Gb / Gh ≤ 4 * E
  apply (div_le_iff₀ hGh).mpr
  calc
    Gb ≤ 2 * mb := hGb
    _ ≤ 4 * E * Gh := by
      rw [hmain]
      have hm := mul_le_mul_of_nonneg_left hGhMain (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hE)
      nlinarith

-- PUBLIC 3: actual joint-energy concentration at the original h_j² scale.
theorem varying_row_uniform_energy_concentration
    (νSeq : ℕ → Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ)
    (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun j => (n j : ℝ) / h j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (n j : ℝ) / h j ^ 3)
      atTop (𝓝 (0 : ℝ)))
    (C : ℝ) (hC : 1 ≤ C)
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ j in atTop, ∀ b : ℝ, h j / 2 ≤ b → b ≤ C * h j →
      0 < (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
        (@Shao.closedStrip (n j) b) ∧
      0 ≤ (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
          ((@Shao.closedStrip (n j) b) ∩
            {a : Shao.Path (n j) |
              ε * h j ^ 2 < |Shao.energy a - (n j : ℝ)|}) /
        (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
          (@Shao.closedStrip (n j) b) ∧
      (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
          ((@Shao.closedStrip (n j) b) ∩
            {a : Shao.Path (n j) |
              ε * h j ^ 2 < |Shao.energy a - (n j : ℝ)|}) /
        (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
          (@Shao.closedStrip (n j) b) < δ := by
  let D : ℝ := (Real.exp ε + Real.exp (-ε)) / 2 - 1
  have hD : 0 < D := by
    have hp := Real.add_one_lt_exp (ne_of_gt hε)
    dsimp only [D]
    nlinarith [Real.add_one_le_exp (-ε)]
  have hcontrols := varying_row_uniform_closedStrip_energy_controls νSeq hprob h3 hmean hsecond M hM h n
    hinfty hlong hshort C hC 1 (by norm_num) (δ * D) (mul_pos hδ hD)
  filter_upwards [hcontrols, hinfty.eventually_gt_atTop 0] with j hj hh b hb0 hb1
  have hB := hj b hb0 hb1
  have hbpos : 0 < b := lt_of_lt_of_le (half_pos hh) hb0
  letI := hprob j
  have hfinite := (UniformConditionalEnergy.energy_deviation_finite_bound (νSeq j) (n j) b (h j) 1 ε
    hbpos hh (by norm_num) hε).2
  let G : ℝ := (Measure.pi (fun _ : Fin (n j) => νSeq j)).real (@Shao.closedStrip (n j) b)
  let R : ℝ := (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
    ((@Shao.closedStrip (n j) b) ∩
      {a : Shao.Path (n j) | ε * h j ^ 2 < |Shao.energy a - (n j : ℝ)|})
  have hG : 0 < G := hB.1
  have hf : D * R ≤ energyCoshExcessIntegral (νSeq j) (n j) b (h j) 1 := by
    simpa only [one_mul, D, R] using hfinite
  have hR : 0 ≤ R / G := div_nonneg ENNReal.toReal_nonneg hG.le
  refine ⟨hB.1, hR, ?_⟩
  change R / G < δ
  have hprod : (R / G) * D < δ * D := by
    calc
      _ = (D * R) / G := by ring
      _ ≤ energyCoshExcessIntegral (νSeq j) (n j) b (h j) 1 / G :=
        div_le_div_of_nonneg_right hf hG.le
      _ < δ * D := hB.2.2.2
  nlinarith [hprod]

end Shao.OQ4.RowUniformConditionalEnergy
end
