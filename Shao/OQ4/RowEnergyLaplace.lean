import Shao.OQ4.EnergyJointTransport
import Shao.OQ4.UnconditionalKernelAsymptotic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace Shao.OQ4.RowEnergyLaplace

open MeasureTheory Filter Set
open RademacherScalarBounds (lambda)
open scoped Topology

theorem varying_row_closedStrip_probability_eventually_pos
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
      atTop (𝓝 (0 : ℝ))) :
    ∀ᶠ j in atTop,
      0 < (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
        (@Shao.closedStrip (n j) (h j)) := by
  classical
  let hp : ℕ → ℝ := fun j => max (h j) 1
  have heq : hp =ᶠ[atTop] h := by
    filter_upwards [hinfty.eventually_ge_atTop 1] with j hj
    exact max_eq_left hj
  have hpinf : Tendsto hp atTop atTop := hinfty.congr' heq.symm
  have hplong : Tendsto (fun j => (n j : ℝ) / hp j ^ 2) atTop atTop := by
    apply hlong.congr'
    exact heq.symm.mono fun j hj => by dsimp only; rw [hj]
  have hpshort : Tendsto (fun j => (n j : ℝ) / hp j ^ 3) atTop (𝓝 (0 : ℝ)) := by
    apply hshort.congr'
    exact heq.symm.mono fun j hj => by dsimp only; rw [hj]
  have hk := UnconditionalKernelAsymptotic.varying_row_closedStrip_relative_asymptotic
    νSeq hprob h3 hmean hsecond M hM hp n
    (fun j => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _))
    hpinf hplong hpshort
  have hkpos := hk.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hkpos, heq] with j hj he
  rw [he] at hj
  have ha : 0 < (4 / Real.pi) * Real.exp (-lambda * (n j : ℝ) / h j ^ 2) :=
    mul_pos (div_pos (by norm_num) Real.pi_pos) (Real.exp_pos _)
  have hz := mul_pos hj ha
  have he : ((Measure.pi (fun _ : Fin (n j) => νSeq j)).real
      (@Shao.closedStrip (n j) (h j)) /
      ((4 / Real.pi) * Real.exp (-lambda * (n j : ℝ) / h j ^ 2))) *
      ((4 / Real.pi) * Real.exp (-lambda * (n j : ℝ) / h j ^ 2)) =
      (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
        (@Shao.closedStrip (n j) (h j)) := by field_simp [ha.ne']
  rwa [he] at hz

theorem varying_row_energy_laplace_ratio_tendsto
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
    (T : ℝ) (hT : 0 ≤ T) (s : ℕ → ℝ) (hs : ∀ j, |s j| ≤ T) :
    Tendsto (fun j => energyJointIntegral (νSeq j) (n j) (h j) (s j) /
      (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
        (@Shao.closedStrip (n j) (h j)))
      atTop (𝓝 (1 : ℝ)) := by
  classical
  have hM0 : 0 ≤ M := (integral_nonneg fun x : ℝ => pow_nonneg (abs_nonneg x) 3).trans (hM 0)
  have hSq (j : ℕ) : Integrable (fun x : ℝ => x ^ 2) (νSeq j) := by
    letI := hprob j
    have hd : Integrable (fun x : ℝ => 1 + |x| ^ 3) (νSeq j) :=
      (integrable_const (1 : ℝ)).add (h3 j)
    apply hd.mono' (by fun_prop : Measurable (fun x : ℝ => x ^ 2)).aestronglyMeasurable
    filter_upwards [] with x
    simp only [Real.norm_eq_abs, abs_pow]
    by_cases hx : |x| ≤ 1
    · nlinarith [abs_nonneg x, pow_nonneg (abs_nonneg x) 3,
        mul_nonneg (abs_nonneg x) (sub_nonneg.mpr hx)]
    · have hx1 : 1 ≤ |x| := (lt_of_not_ge hx).le
      nlinarith [sq_nonneg |x|, mul_nonneg (sq_nonneg |x|) (sub_nonneg.mpr hx1)]
  let C : ℝ := energyE2Constant M T
  have hC : 0 ≤ C := le_trans (by norm_num) (energyE2Constant_dominates M T hM0 hT).1
  let H : ℝ := max (energyE2Threshold M T) (max 1 (2 * C))
  have hH1 : 1 ≤ H := le_trans (le_max_left _ _) (le_max_right _ _)
  have hH2 : 2 * C ≤ H := le_trans (le_max_right _ _) (le_max_right _ _)
  have hHt : energyE2Threshold M T ≤ H := le_max_left _ _
  have htail : ∀ᶠ j in atTop, H ≤ h j := hinfty.eventually_ge_atTop H
  have hex (j : ℕ) : ∃ θ : ℝ, H ≤ h j →
      energyE2Conclusion (νSeq j) M T (h j) (s j) θ := by
    by_cases hj : H ≤ h j
    · letI := hprob j
      obtain ⟨θ, hθ⟩ := energyE2_common_bounds (νSeq j) M T (h j) (s j)
        hM0 hT (hHt.trans hj) (hs j) (hSq j) (h3 j) (hsecond j) (hmean j) (hM j)
      exact ⟨θ, fun _ => hθ⟩
    · exact ⟨0, fun hj' => (hj hj').elim⟩
  choose θ hθ using hex
  let μ : ℕ → Measure ℝ := fun j => energyLinearTiltLaw (νSeq j) (h j) (s j) (θ j)
  let v : ℕ → ℝ := fun j => ∫ x : ℝ, x ^ 2 ∂(μ j)
  let ρ : ℕ → Measure ℝ := fun j => if H ≤ h j then μ j else νSeq 0
  let w : ℕ → ℝ := fun j => if H ≤ h j then v j else 1
  let hp : ℕ → ℝ := fun j => if H ≤ h j then h j else 1
  have hvar (j : ℕ) (hj : H ≤ h j) : (1 / 2 : ℝ) ≤ v j ∧ v j ≤ 2 := by
    have he := (hθ j hj).2.2.2.2.2.2.2.2.2.1
    have hhp : 0 < h j := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hH1.trans hj)
    have hd : C / h j ≤ (1 / 2 : ℝ) := (div_le_iff₀ hhp).2 (by linarith [hH2.trans hj])
    change |v j - 1| ≤ C / h j at he
    have hv := abs_le.mp he
    constructor <;> linarith
  have hρprob (j : ℕ) : IsProbabilityMeasure (ρ j) := by
    by_cases hj : H ≤ h j
    · simpa only [ρ, if_pos hj] using (hθ j hj).2.1
    · simpa only [ρ, if_neg hj] using hprob 0
  have hρ3 (j : ℕ) : Integrable (fun x : ℝ => |x| ^ 3) (ρ j) := by
    by_cases hj : H ≤ h j
    · simpa only [ρ, if_pos hj] using (hθ j hj).2.2.2.2.2.1
    · simpa only [ρ, if_neg hj] using h3 0
  have hρmean (j : ℕ) : (∫ x : ℝ, x ∂(ρ j)) = 0 := by
    by_cases hj : H ≤ h j
    · simpa only [ρ, if_pos hj] using (hθ j hj).2.2.2.2.2.2.1
    · simpa only [ρ, if_neg hj] using hmean 0
  have hρsecond (j : ℕ) : (∫ x : ℝ, x ^ 2 ∂(ρ j)) = w j := by
    by_cases hj : H ≤ h j
    · simp only [ρ, w, if_pos hj, v]
    · simpa only [ρ, w, if_neg hj] using hsecond 0
  have hwlo (j : ℕ) : (1 / 2 : ℝ) ≤ w j := by
    by_cases hj : H ≤ h j
    · simpa only [w, if_pos hj] using (hvar j hj).1
    · simp only [w, if_neg hj]; norm_num
  have hwup (j : ℕ) : w j ≤ 2 := by
    by_cases hj : H ≤ h j
    · simpa only [w, if_pos hj] using (hvar j hj).2
    · simp only [w, if_neg hj]; norm_num
  have hρM (j : ℕ) : (∫ x : ℝ, |x| ^ 3 ∂(ρ j)) ≤ max M C := by
    by_cases hj : H ≤ h j
    · simpa only [ρ, if_pos hj] using ((hθ j hj).2.2.2.2.2.2.2.2.2.2.trans (le_max_right M C))
    · simpa only [ρ, if_neg hj] using (hM 0).trans (le_max_left M C)
  have hppos (j : ℕ) : 0 < hp j := by
    by_cases hj : H ≤ h j
    · simpa only [hp, if_pos hj] using lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hH1.trans hj)
    · simp only [hp, if_neg hj]; norm_num
  have hpeq : hp =ᶠ[atTop] h := htail.mono fun j hj => if_pos hj
  have hpinf : Tendsto hp atTop atTop := hinfty.congr' hpeq.symm
  have hplong : Tendsto (fun j => (n j : ℝ) / hp j ^ 2) atTop atTop := by
    apply hlong.congr'
    exact hpeq.symm.mono fun j hj => by dsimp only; rw [hj]
  have hpshort : Tendsto (fun j => (n j : ℝ) / hp j ^ 3) atTop (𝓝 (0 : ℝ)) := by
    apply hshort.congr'
    exact hpeq.symm.mono fun j hj => by dsimp only; rw [hj]
  let p : ℕ → ℝ := fun j => (Measure.pi (fun _ : Fin (n j) => νSeq j)).real (@Shao.closedStrip (n j) (h j))
  let c : ℕ → ℝ := fun j => energyJointCenteredProbability (νSeq j) (n j) (h j) (s j) (θ j)
  let a : ℕ → ℝ := fun j => (4 / Real.pi) * Real.exp (-lambda * (n j : ℝ) / h j ^ 2)
  let b : ℕ → ℝ := fun j => (4 / Real.pi) * Real.exp (-lambda * v j * (n j : ℝ) / h j ^ 2)
  have ha (j : ℕ) : 0 < a j := mul_pos (div_pos (by norm_num) Real.pi_pos) (Real.exp_pos _)
  have hb (j : ℕ) : 0 < b j := mul_pos (div_pos (by norm_num) Real.pi_pos) (Real.exp_pos _)
  have hpa : Tendsto (fun j => p j / a j) atTop (𝓝 (1 : ℝ)) := by
    have hk := UnconditionalKernelAsymptotic.varying_row_closedStrip_relative_asymptotic
      νSeq hprob h3 hmean hsecond M hM hp n hppos hpinf hplong hpshort
    apply hk.congr'
    filter_upwards [hpeq] with j hj
    simp only [hj, p, a]
  have hcb : Tendsto (fun j => c j / b j) atTop (𝓝 (1 : ℝ)) := by
    have hk := UnconditionalKernelAsymptotic.varying_row_variance_closedStrip_relative_asymptotic
      ρ hρprob w hρ3 hρmean hρsecond hwlo hwup (max M C) hρM hp n hppos hpinf hplong hpshort
    apply hk.congr'
    filter_upwards [htail] with j hj
    simp only [ρ, w, hp, if_pos hj, c, b, energyJointCenteredProbability, μ]
  have hexp : Tendsto (fun j => -lambda * (v j - 1) * (n j : ℝ) / h j ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).2
    apply squeeze_zero' (Eventually.of_forall fun j => abs_nonneg _) _
      (by simpa using hshort.const_mul (|lambda| * C))
    filter_upwards [htail] with j hj
    have hhp : 0 < h j := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hH1.trans hj)
    have he : |v j - 1| ≤ C / h j := (hθ j hj).2.2.2.2.2.2.2.2.2.1
    calc
      _ = |lambda| * |v j - 1| * ((n j : ℝ) / h j ^ 2) := by
        simp only [abs_div, abs_mul, abs_neg,
          abs_of_nonneg (Nat.cast_nonneg (n j) : (0 : ℝ) ≤ (n j : ℝ)), abs_pow, abs_of_pos hhp]
        ring
      _ ≤ |lambda| * (C / h j) * ((n j : ℝ) / h j ^ 2) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (abs_nonneg _))
          (div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
      _ = |lambda| * C * ((n j : ℝ) / h j ^ 3) := by field_simp
  have hba : Tendsto (fun j => b j / a j) atTop (𝓝 (1 : ℝ)) := by
    have hl : Tendsto (fun j => Real.exp (-lambda * (v j - 1) * (n j : ℝ) / h j ^ 2))
        atTop (𝓝 (1 : ℝ)) := by
      simpa only [Function.comp_def, Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp hexp
    apply hl.congr'
    filter_upwards [] with j
    dsimp only [a, b]
    rw [mul_div_mul_left _ _ (ne_of_gt (div_pos (by norm_num : (0 : ℝ) < 4) Real.pi_pos)), ← Real.exp_sub]
    congr 1
    ring
  have hp0 : ∀ᶠ j in atTop, 0 < p j :=
    varying_row_closedStrip_probability_eventually_pos νSeq hprob h3 hmean hsecond M hM h n hinfty hlong hshort
  have hcp : Tendsto (fun j => c j / p j) atTop (𝓝 (1 : ℝ)) := by
    have hl := (hcb.mul hba).div hpa (by norm_num : (1 : ℝ) ≠ 0)
    simp only [one_mul, div_one] at hl
    apply hl.congr'
    filter_upwards [hp0] with j hj
    change (c j / b j * (b j / a j)) / (p j / a j) = c j / p j
    field_simp [ne_of_gt (ha j), ne_of_gt (hb j), ne_of_gt hj]
  let δ : ℕ → ℝ := fun j => Real.exp (energyRelativePathError M T (n j) (h j)) - 1
  have hδ : Tendsto δ atTop (𝓝 (0 : ℝ)) :=
    (energyJointTransport_error_limits M T h n hinfty hshort).2.2.2.1
  have hdiff : Tendsto (fun j => energyJointIntegral (νSeq j) (n j) (h j) (s j) / p j - c j / p j)
      atTop (𝓝 (0 : ℝ)) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).2
    apply squeeze_zero' (Eventually.of_forall fun j => abs_nonneg _) _
      (by simpa only [zero_mul] using hδ.mul hcp)
    filter_upwards [htail, hp0] with j hj hpj
    letI := hprob j
    have hf := energyJointTransport_finite_of_e2 (νSeq j) M T (h j) (s j) (θ j) (n j)
      hM0 hT (hHt.trans hj) (hs j) (hSq j) (h3 j) (hsecond j) (hmean j) (hM j) (hθ j hj)
    have he : |energyJointIntegral (νSeq j) (n j) (h j) (s j) - c j| ≤ δ j * c j :=
      hf.2.2.2.2.2.2.2.2
    rw [← sub_div, abs_div, abs_of_pos hpj]
    exact (div_le_div_of_nonneg_right he hpj.le).trans_eq (by ring)
  have hl := hdiff.add hcp
  simpa only [zero_add, sub_add_cancel] using hl

end Shao.OQ4.RowEnergyLaplace
end
