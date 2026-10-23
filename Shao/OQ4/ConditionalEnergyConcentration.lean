-- LOCAL implementation of the exact parent-frozen eight theorem heads.
-- Freeze dbd29354fd1f856bbdf5682779cb04b8cf99944d4fda363a1c176f8c072d36e4.
-- UNCHECKED: future K/Kv qualifications and this source's server gates are pending.
-- No original OQ4 or random-denominator far-layer closure is claimed.

import Shao.OQ4.EnergyJointTransport
import Shao.OQ4.UnconditionalKernelAsymptotic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
noncomputable section
namespace Shao.OQ4.ConditionalEnergyConcentration

open MeasureTheory Filter Set
open RademacherScalarBounds (lambda)
open scoped Topology

private theorem lower_moments_integrable
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν) :
    Integrable (fun x : ℝ => x) ν ∧
      Integrable (fun x : ℝ => x ^ 2) ν := by
  have hdom : Integrable (fun x : ℝ => 1 + |x| ^ 3) ν :=
    (integrable_const (1 : ℝ)).add h3
  have hsmall (r : ℝ) (hr : 0 ≤ r) : r ≤ 1 + r ^ 3 ∧ r ^ 2 ≤ 1 + r ^ 3 := by
    by_cases hr1 : r ≤ 1
    · have hp := mul_nonneg hr (sub_nonneg.mpr hr1)
      have hr3 : 0 ≤ r ^ 3 := pow_nonneg hr 3
      constructor <;> nlinarith
    · have hlarge : 1 ≤ r := (lt_of_not_ge hr1).le
      have hp := mul_nonneg hr (sub_nonneg.mpr hlarge)
      have hq := mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hlarge)
      constructor <;> nlinarith
  constructor
  · apply hdom.mono' (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x) ν)
    exact Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, id_eq] using (hsmall |x| (abs_nonneg x)).1
  · apply hdom.mono' (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ 2) ν)
    exact Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_pow, id_eq] using (hsmall |x| (abs_nonneg x)).2

private theorem tail_variance_closedStrip_relative_asymptotic
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (ρ : ℕ → Measure ℝ) (v : ℕ → ℝ) (M : ℝ)
    (hrows : ∀ᶠ j in atTop,
      IsProbabilityMeasure (ρ j) ∧
        Integrable (fun x : ℝ => |x| ^ 3) (ρ j) ∧
        (∫ x : ℝ, x ∂(ρ j)) = 0 ∧
        (∫ x : ℝ, x ^ 2 ∂(ρ j)) = v j ∧
        (1 / 2 : ℝ) ≤ v j ∧ v j ≤ 2 ∧
        (∫ x : ℝ, |x| ^ 3 ∂(ρ j)) ≤ M)
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun j => (n j : ℝ) / h j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (n j : ℝ) / h j ^ 3) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun j =>
      (Measure.pi (fun _ : Fin (n j) => ρ j)).real
        (@Shao.closedStrip (n j) (h j)) /
          ((4 / Real.pi) *
            Real.exp (-lambda * v j * (n j : ℝ) / h j ^ 2)))
      atTop (𝓝 (1 : ℝ)) := by
  classical
  let β : ℝ := ∫ x : ℝ, |x| ^ 3 ∂ν
  let B : ℝ := max β M
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hrows.and (hinfty.eventually_ge_atTop 1))
  let ρ' : ℕ → Measure ℝ := fun j => if N ≤ j then ρ j else ν
  let v' : ℕ → ℝ := fun j => if N ≤ j then v j else 1
  let h' : ℕ → ℝ := fun j => if N ≤ j then h j else 1
  have hpay (j : ℕ) :
      IsProbabilityMeasure (ρ' j) ∧
        Integrable (fun x : ℝ => |x| ^ 3) (ρ' j) ∧
        (∫ x : ℝ, x ∂(ρ' j)) = 0 ∧
        (∫ x : ℝ, x ^ 2 ∂(ρ' j)) = v' j ∧
        (1 / 2 : ℝ) ≤ v' j ∧ v' j ≤ 2 ∧
        (∫ x : ℝ, |x| ^ 3 ∂(ρ' j)) ≤ B ∧ 0 < h' j := by
    by_cases hj : N ≤ j
    · obtain ⟨hp, hc, hm, hs, hvlo, hvhi, hM⟩ := (hN j hj).1
      have hB : (∫ x : ℝ, |x| ^ 3 ∂(ρ j)) ≤ B :=
        hM.trans (le_max_right β M)
      have hh : 0 < h j := lt_of_lt_of_le (by norm_num) (hN j hj).2
      simpa only [ρ', v', h', if_pos hj] using
        And.intro hp (And.intro hc (And.intro hm (And.intro hs
          (And.intro hvlo (And.intro hvhi (And.intro hB hh))))))
    · have hB : (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ B := le_max_left β M
      have hp : IsProbabilityMeasure ν := inferInstance
      simpa only [ρ', v', h', if_neg hj] using
        And.intro hp (And.intro h3 (And.intro hmean (And.intro hsecond
          (And.intro (by norm_num : (1 / 2 : ℝ) ≤ 1)
            (And.intro (by norm_num : (1 : ℝ) ≤ 2)
              (And.intro hB (by norm_num : (0 : ℝ) < 1)))))))
  have htail : ∀ᶠ j in atTop, N ≤ j := eventually_ge_atTop N
  have hh' : Tendsto h' atTop atTop := by
    apply hinfty.congr'
    filter_upwards [htail] with j hj
    simp only [h', if_pos hj]
  have hl' : Tendsto (fun j => (n j : ℝ) / h' j ^ 2) atTop atTop := by
    apply hlong.congr'
    filter_upwards [htail] with j hj
    simp only [h', if_pos hj]
  have hs' : Tendsto (fun j => (n j : ℝ) / h' j ^ 3) atTop (𝓝 (0 : ℝ)) := by
    apply hshort.congr'
    filter_upwards [htail] with j hj
    simp only [h', if_pos hj]
  have hk :=
    UnconditionalKernelAsymptotic.varying_row_variance_closedStrip_relative_asymptotic
      ρ' (fun j => (hpay j).1) v'
      (fun j => (hpay j).2.1)
      (fun j => (hpay j).2.2.1)
      (fun j => (hpay j).2.2.2.1)
      (fun j => (hpay j).2.2.2.2.1)
      (fun j => (hpay j).2.2.2.2.2.1)
      B (fun j => (hpay j).2.2.2.2.2.2.1)
      h' n (fun j => (hpay j).2.2.2.2.2.2.2) hh' hl' hs'
  apply hk.congr'
  filter_upwards [htail] with j hj
  simp only [ρ', v', h', if_pos hj]

theorem closedStrip_probability_eventually_pos
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun j => (n j : ℝ) / h j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (n j : ℝ) / h j ^ 3) atTop (𝓝 (0 : ℝ))) :
    ∀ᶠ j in atTop,
      0 < (Measure.pi (fun _ : Fin (n j) => ν)).real
        (@Shao.closedStrip (n j) (h j)) := by
  let G : ℕ → ℝ := fun j =>
    (Measure.pi (fun _ : Fin (n j) => ν)).real (@Shao.closedStrip (n j) (h j))
  let a : ℕ → ℝ := fun j =>
    (4 / Real.pi) * Real.exp (-lambda * (n j : ℝ) / h j ^ 2)
  have hrows : ∀ᶠ j in (atTop : Filter ℕ),
      IsProbabilityMeasure ν ∧ Integrable (fun x : ℝ => |x| ^ 3) ν ∧
        (∫ x : ℝ, x ∂ν) = 0 ∧ (∫ x : ℝ, x ^ 2 ∂ν) = (1 : ℝ) ∧
        (1 / 2 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 2 ∧
        (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ (∫ x : ℝ, |x| ^ 3 ∂ν) :=
    Eventually.of_forall fun _ =>
      ⟨inferInstance, h3, hmean, hsecond, by norm_num, by norm_num, le_rfl⟩
  have hk : Tendsto (fun j => G j / a j) atTop (𝓝 (1 : ℝ)) := by
    simpa only [G, a, mul_one] using
      tail_variance_closedStrip_relative_asymptotic ν h3 hmean hsecond
        (fun _ => ν) (fun _ => 1) (∫ x : ℝ, |x| ^ 3 ∂ν)
        hrows h n hinfty hlong hshort
  have hhalf : ∀ᶠ j in atTop, (1 / 2 : ℝ) < G j / a j :=
    hk.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [hhalf] with j hj
  have ha : 0 < a j :=
    mul_pos (div_pos (by norm_num) Real.pi_pos) (Real.exp_pos _)
  have hratio : 0 < G j / a j := lt_trans (by norm_num) hj
  have hp : 0 < (G j / a j) * a j := mul_pos hratio ha
  have heq : (G j / a j) * a j = G j := by field_simp [ha.ne']
  simpa only [heq, G] using hp

private theorem e2_centered_survival_ratio
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun j => (n j : ℝ) / h j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (n j : ℝ) / h j ^ 3) atTop (𝓝 (0 : ℝ)))
    (s : ℝ) (θ : ℕ → ℝ)
    (he2 : ∀ᶠ j in atTop,
      energyE2Conclusion ν (∫ x : ℝ, |x| ^ 3 ∂ν) |s| (h j) s (θ j)) :
    Tendsto (fun j =>
      energyJointCenteredProbability ν (n j) (h j) s (θ j) /
        (Measure.pi (fun _ : Fin (n j) => ν)).real
          (@Shao.closedStrip (n j) (h j)))
      atTop (𝓝 (1 : ℝ)) := by
  let β : ℝ := ∫ x : ℝ, |x| ^ 3 ∂ν
  let C : ℝ := energyE2Constant β |s|
  let ρ : ℕ → Measure ℝ := fun j => energyLinearTiltLaw ν (h j) s (θ j)
  let v : ℕ → ℝ := fun j => ∫ x : ℝ, x ^ 2 ∂(ρ j)
  let G : ℕ → ℝ := fun j =>
    (Measure.pi (fun _ : Fin (n j) => ν)).real (@Shao.closedStrip (n j) (h j))
  let H : ℕ → ℝ := fun j => energyJointCenteredProbability ν (n j) (h j) s (θ j)
  let a : ℕ → ℝ := fun j =>
    (4 / Real.pi) * Real.exp (-lambda * (n j : ℝ) / h j ^ 2)
  let b : ℕ → ℝ := fun j =>
    (4 / Real.pi) * Real.exp (-lambda * v j * (n j : ℝ) / h j ^ 2)
  have hβ : 0 ≤ β := integral_nonneg fun x => pow_nonneg (abs_nonneg x) 3
  have hC : 1 ≤ C := (energyE2Constant_dominates β |s| hβ (abs_nonneg s)).1
  have hrows : ∀ᶠ j in atTop,
      IsProbabilityMeasure (ρ j) ∧
        Integrable (fun x : ℝ => |x| ^ 3) (ρ j) ∧
        (∫ x : ℝ, x ∂(ρ j)) = 0 ∧
        (∫ x : ℝ, x ^ 2 ∂(ρ j)) = v j ∧
        (1 / 2 : ℝ) ≤ v j ∧ v j ≤ 2 ∧
        (∫ x : ℝ, |x| ^ 3 ∂(ρ j)) ≤ C := by
    filter_upwards [he2, hinfty.eventually_ge_atTop (max 1 (2 * C))] with j hej hj
    obtain ⟨_, hp, _, _, _, hc, hm, _, _, hv, hthird⟩ := hej
    have hh1 : 1 ≤ h j := (le_max_left 1 (2 * C)).trans hj
    have hhpos : 0 < h j := lt_of_lt_of_le (by norm_num) hh1
    have hhC : 2 * C ≤ h j := (le_max_right 1 (2 * C)).trans hj
    have hhalf : C / h j ≤ (1 / 2 : ℝ) :=
      (div_le_iff₀ hhpos).2 (by linarith)
    have hv' : |v j - 1| ≤ C / h j := hv
    obtain ⟨hvlo, hvhi⟩ := abs_le.mp hv'
    exact ⟨hp, hc, hm, rfl, by linarith, by linarith, hthird⟩
  have hH : Tendsto (fun j => H j / b j) atTop (𝓝 (1 : ℝ)) := by
    simpa only [H, b, energyJointCenteredProbability, ρ] using
      tail_variance_closedStrip_relative_asymptotic ν h3 hmean hsecond
        ρ v C hrows h n hinfty hlong hshort
  have hG : Tendsto (fun j => G j / a j) atTop (𝓝 (1 : ℝ)) := by
    have hrowsν : ∀ᶠ j in (atTop : Filter ℕ),
        IsProbabilityMeasure ν ∧ Integrable (fun x : ℝ => |x| ^ 3) ν ∧
          (∫ x : ℝ, x ∂ν) = 0 ∧ (∫ x : ℝ, x ^ 2 ∂ν) = (1 : ℝ) ∧
          (1 / 2 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 2 ∧
          (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ β :=
      Eventually.of_forall fun _ =>
        ⟨inferInstance, h3, hmean, hsecond, by norm_num, by norm_num, le_rfl⟩
    simpa only [G, a, mul_one] using
      tail_variance_closedStrip_relative_asymptotic ν h3 hmean hsecond
        (fun _ => ν) (fun _ => 1) β hrowsν h n hinfty hlong hshort
  have hsmall : Tendsto
      (fun j => -lambda * (v j - 1) * (n j : ℝ) / h j ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    have hmajor : Tendsto (fun j => (|lambda| * C) * ((n j : ℝ) / h j ^ 3))
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using hshort.const_mul (|lambda| * C)
    have hbnd : ∀ᶠ j in atTop,
        |-lambda * (v j - 1) * (n j : ℝ) / h j ^ 2| ≤
          (|lambda| * C) * ((n j : ℝ) / h j ^ 3) := by
      filter_upwards [he2, hinfty.eventually_ge_atTop 1] with j hej hj
      obtain ⟨_, _, _, _, _, _, _, _, _, hv, _⟩ := hej
      have hh : 0 < h j := lt_of_lt_of_le (by norm_num) hj
      have hv' : |v j - 1| ≤ C / h j := hv
      have hn : 0 ≤ (n j : ℝ) / h j ^ 2 :=
        div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
      calc
        |-lambda * (v j - 1) * (n j : ℝ) / h j ^ 2| =
            |lambda| * |v j - 1| * ((n j : ℝ) / h j ^ 2) := by
          rw [abs_div, abs_mul, abs_mul, abs_neg,
            abs_of_nonneg (a := (n j : ℝ)) (Nat.cast_nonneg (n j)),
            abs_of_nonneg (a := h j ^ 2) (sq_nonneg (h j))]
          ring
        _ ≤ |lambda| * (C / h j) * ((n j : ℝ) / h j ^ 2) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hv' (abs_nonneg lambda)) hn
        _ = (|lambda| * C) * ((n j : ℝ) / h j ^ 3) := by
          field_simp [hh.ne']
          <;> ring
    apply (tendsto_zero_iff_abs_tendsto_zero _).2
    exact squeeze_zero' (Eventually.of_forall fun j => abs_nonneg _) hbnd hmajor
  have ha (j : ℕ) : 0 < a j :=
    mul_pos (div_pos (by norm_num) Real.pi_pos) (Real.exp_pos _)
  have hb (j : ℕ) : 0 < b j :=
    mul_pos (div_pos (by norm_num) Real.pi_pos) (Real.exp_pos _)
  have hba : Tendsto (fun j => b j / a j) atTop (𝓝 (1 : ℝ)) := by
    have hexp : Tendsto
        (fun j => Real.exp (-lambda * (v j - 1) * (n j : ℝ) / h j ^ 2))
        atTop (𝓝 (1 : ℝ)) := by
      simpa only [Function.comp_def, Real.exp_zero] using
        (Real.continuous_exp.tendsto 0).comp hsmall
    apply hexp.congr'
    exact Eventually.of_forall fun j => by
      have he : Real.exp (-lambda * v j * (n j : ℝ) / h j ^ 2) =
          Real.exp (-lambda * (v j - 1) * (n j : ℝ) / h j ^ 2) *
            Real.exp (-lambda * (n j : ℝ) / h j ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have heq : b j =
          Real.exp (-lambda * (v j - 1) * (n j : ℝ) / h j ^ 2) * a j := by
        dsimp only [b, a]
        rw [he]
        ring
      change Real.exp (-lambda * (v j - 1) * (n j : ℝ) / h j ^ 2) = b j / a j
      rw [heq]
      field_simp [(ha j).ne']
  have hGpos : ∀ᶠ j in atTop, 0 < G j :=
    closedStrip_probability_eventually_pos ν h3 hmean hsecond h n hinfty hlong hshort
  have hquot : Tendsto (fun j => ((H j / b j) * (b j / a j)) / (G j / a j))
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [Pi.mul_def, Pi.div_def, one_mul, div_one] using (hH.mul hba).div hG (by norm_num : (1 : ℝ) ≠ 0)
  apply hquot.congr'
  filter_upwards [hGpos] with j hj
  change ((H j / b j) * (b j / a j)) / (G j / a j) = H j / G j
  field_simp [(ha j).ne', (hb j).ne', hj.ne']
  <;> ring

theorem energy_laplace_ratio_tendsto
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun j => (n j : ℝ) / h j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (n j : ℝ) / h j ^ 3) atTop (𝓝 (0 : ℝ)))
    (s : ℝ) :
    Tendsto (fun j => energyJointIntegral ν (n j) (h j) s /
      (Measure.pi (fun _ : Fin (n j) => ν)).real
        (@Shao.closedStrip (n j) (h j)))
      atTop (𝓝 (1 : ℝ)) := by
  let β : ℝ := ∫ x : ℝ, |x| ^ 3 ∂ν
  have hβ : 0 ≤ β := integral_nonneg fun x => pow_nonneg (abs_nonneg x) 3
  have hSq := (lower_moments_integrable ν h3).2
  obtain ⟨θ, _, he2, _, hseq⟩ := energyJointTransport_common_bounds.{0,0,0}
    ν β |s| h (fun _ => s) hβ (abs_nonneg s) hinfty
    (fun _ => le_rfl) hSq h3 hsecond hmean le_rfl
  have he2' : ∀ᶠ j in atTop,
      energyE2Conclusion ν (∫ x : ℝ, |x| ^ 3 ∂ν) |s| (h j) s (θ j) :=
    he2.mono fun _ hj => hj.1
  have hratio := e2_centered_survival_ratio ν h3 hmean hsecond
    h n hinfty hlong hshort s θ he2'
  obtain ⟨herr, _, hfinite, _⟩ := hseq n hshort
  let G : ℕ → ℝ := fun j =>
    (Measure.pi (fun _ : Fin (n j) => ν)).real (@Shao.closedStrip (n j) (h j))
  let H : ℕ → ℝ := fun j => energyJointCenteredProbability ν (n j) (h j) s (θ j)
  let δ : ℕ → ℝ := fun j => Real.exp (energyRelativePathError β |s| (n j) (h j)) - 1
  have hδ : Tendsto δ atTop (𝓝 (0 : ℝ)) := herr.2.2.2.1
  have hGpos : ∀ᶠ j in atTop, 0 < G j :=
    closedStrip_probability_eventually_pos ν h3 hmean hsecond h n hinfty hlong hshort
  have hbound : ∀ᶠ j in atTop,
      |energyJointIntegral ν (n j) (h j) s / G j - H j / G j| ≤
        δ j * (H j / G j) := by
    filter_upwards [hfinite, hGpos] with j hj hp
    obtain ⟨_, _, _, _, _, _, _, _, habs⟩ := hj
    calc
      |energyJointIntegral ν (n j) (h j) s / G j - H j / G j| =
          |energyJointIntegral ν (n j) (h j) s - H j| / G j := by
        rw [← sub_div, abs_div, abs_of_pos hp]
      _ ≤ (δ j * H j) / G j := div_le_div_of_nonneg_right habs hp.le
      _ = δ j * (H j / G j) := by ring
  have hmajor : Tendsto (fun j => δ j * (H j / G j)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_mul] using hδ.mul hratio
  have hdiff : Tendsto
      (fun j => energyJointIntegral ν (n j) (h j) s / G j - H j / G j)
      atTop (𝓝 (0 : ℝ)) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).2
    exact squeeze_zero' (Eventually.of_forall fun j => abs_nonneg _) hbound hmajor
  simpa only [zero_add, sub_add_cancel, G, H] using hdiff.add hratio

private theorem exp_pair_deviation_bound (ε y : ℝ) (hε : 0 < ε) :
    0 < Real.exp ε + Real.exp (-ε) - 2 ∧
      (if ε < |y| then Real.exp ε + Real.exp (-ε) - 2 else 0) ≤
        Real.exp y + Real.exp (-y) - 2 := by
  have hformula (t : ℝ) :
      Real.exp t + Real.exp (-t) - 2 = (Real.exp t - 1) ^ 2 / Real.exp t := by
    rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero t]
    <;> ring
  have hnonneg (t : ℝ) : 0 ≤ Real.exp t + Real.exp (-t) - 2 := by
    rw [hformula]
    exact div_nonneg (sq_nonneg _) (Real.exp_nonneg _)
  have hεexp : 1 < Real.exp ε := by
    simpa only [Real.exp_zero] using (Real.exp_lt_exp.mpr hε)
  have hD : 0 < Real.exp ε + Real.exp (-ε) - 2 := by
    rw [hformula]
    exact div_pos (pow_pos (sub_pos.mpr hεexp) 2) (Real.exp_pos _)
  refine ⟨hD, ?_⟩
  by_cases hy : ε < |y|
  · rw [if_pos hy]
    have heven : Real.exp y + Real.exp (-y) - 2 =
        Real.exp |y| + Real.exp (-|y|) - 2 := by
      rcases le_total 0 y with hpos | hneg
      · rw [abs_of_nonneg hpos]
      · rw [abs_of_nonpos hneg, neg_neg]
        ring
    let u : ℝ := Real.exp |y|
    let v : ℝ := Real.exp ε
    have hu : 0 < u := Real.exp_pos _
    have hv : 0 < v := Real.exp_pos _
    have hv1 : 1 < v := hεexp
    have hvu : v < u := Real.exp_lt_exp.mpr hy
    have huv1 : 1 ≤ u * v := by
      have hprod := mul_nonneg (show 0 ≤ u - 1 by linarith)
        (show 0 ≤ v - 1 by linarith)
      nlinarith
    have hdiff :
        (Real.exp y + Real.exp (-y) - 2) -
          (Real.exp ε + Real.exp (-ε) - 2) =
            (u - v) * (u * v - 1) / (u * v) := by
      rw [heven]
      simp only [Real.exp_neg]
      change (u + u⁻¹ - 2) - (v + v⁻¹ - 2) = _
      field_simp [hu.ne', hv.ne']
      <;> ring
    have hnn : 0 ≤ (u - v) * (u * v - 1) / (u * v) :=
      div_nonneg (mul_nonneg (sub_nonneg.mpr hvu.le) (sub_nonneg.mpr huv1))
        (mul_nonneg hu.le hv.le)
    linarith
  · rw [if_neg hy]
    exact hnonneg y

private theorem energy_deviation_finite_bound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (h ε : ℝ) (hh : 1 ≤ h) (hε : 0 < ε) :
    (Real.exp ε + Real.exp (-ε) - 2) *
      (Measure.pi (fun _ : Fin n => ν)).real
        ((@Shao.closedStrip n h) ∩
          {a : Shao.Path n | ε < |(Shao.energy a - (n : ℝ)) / h ^ 2|}) ≤
      energyJointIntegral ν n h 1 + energyJointIntegral ν n h (-1) -
        2 * (Measure.pi (fun _ : Fin n => ν)).real (@Shao.closedStrip n h) := by
  classical
  let μ : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ν)
  let A : Set (Shao.Path n) := Shao.closedStrip h
  let Y : Shao.Path n → ℝ := fun a => (Shao.energy a - (n : ℝ)) / h ^ 2
  let B : Set (Shao.Path n) := A ∩ {a | ε < |Y a|}
  let IA : Shao.Path n → ℝ := A.indicator (fun _ => 1)
  let IB : Shao.Path n → ℝ := B.indicator (fun _ => 1)
  let D : ℝ := Real.exp ε + Real.exp (-ε) - 2
  have hA : MeasurableSet A := by
    dsimp only [A]
    rw [← shiftedClosedSurvival_eq_closedStrip n h (by linarith : 0 ≤ h)]
    exact measurableSet_shiftedClosedSurvival n h 0
  have hQ : Measurable (fun a : Shao.Path n => Shao.energy a) := by
    unfold Shao.energy
    fun_prop
  have hY : Measurable Y := by
    dsimp only [Y]
    fun_prop
  have hYabs : Measurable (fun a : Shao.Path n => |Y a|) := by fun_prop
  have hB : MeasurableSet B :=
    hA.inter (measurableSet_lt measurable_const hYabs)
  have hiA : Integrable IA μ := (integrable_const (1 : ℝ)).indicator hA
  have hiB : Integrable IB μ := (integrable_const (1 : ℝ)).indicator hB
  have hIA : (∫ a, IA a ∂μ) = μ.real A := by
    simpa only [IA, measureReal_def, show (1 : Shao.Path n → ℝ) = (fun _ => 1) from rfl] using
      (integral_indicator_one (μ := μ) hA)
  have hIB : (∫ a, IB a ∂μ) = μ.real B := by
    simpa only [IB, measureReal_def, show (1 : Shao.Path n → ℝ) = (fun _ => 1) from rfl] using
      (integral_indicator_one (μ := μ) hB)
  have hiP : Integrable (energyPathIntegrand (n := n) h 1) μ :=
    energyPathIntegrand_integrable ν n 1 h 1 (by norm_num) hh (by norm_num)
  have hiM : Integrable (energyPathIntegrand (n := n) h (-1)) μ :=
    energyPathIntegrand_integrable ν n 1 h (-1) (by norm_num) hh (by norm_num)
  have hpoint (a : Shao.Path n) :
      D * IB a ≤ energyPathIntegrand h 1 a + energyPathIntegrand h (-1) a -
        2 * IA a := by
    by_cases ha : a ∈ A
    · have ha' : a ∈ Shao.closedStrip h := ha
      have hp := (exp_pair_deviation_bound ε (Y a) hε).2
      have hleft : D * IB a = if ε < |Y a| then D else 0 := by
        by_cases hb : ε < |Y a| <;> simp [IB, B, ha, hb]
      have hplus : energyPathIntegrand h 1 a = Real.exp (Y a) := by
        simp only [energyPathIntegrand, if_pos ha', one_mul, Y]
      have hminus : energyPathIntegrand h (-1) a = Real.exp (-Y a) := by
        simp only [energyPathIntegrand, if_pos ha', neg_one_mul, neg_div, Y]
      have hIAa : IA a = 1 := by simp only [IA, Set.indicator_of_mem ha]
      rw [hleft, hplus, hminus, hIAa, mul_one]
      exact hp
    · have ha' : a ∉ Shao.closedStrip h := ha
      simp [IA, IB, B, ha, energyPathIntegrand, ha']
  have hiSum : Integrable (fun a => energyPathIntegrand h 1 a +
      energyPathIntegrand h (-1) a) μ := hiP.add hiM
  have hiTwo : Integrable (fun a => 2 * IA a) μ := hiA.const_mul 2
  have hm : (∫ a, D * IB a ∂μ) ≤
      ∫ a, energyPathIntegrand h 1 a + energyPathIntegrand h (-1) a - 2 * IA a ∂μ :=
    integral_mono (hiB.const_mul D) (hiSum.sub hiTwo) hpoint
  rw [integral_const_mul, integral_sub hiSum hiTwo,
    integral_add hiP hiM, integral_const_mul, hIA, hIB] at hm
  simpa only [D, B, A, Y, μ, energyJointIntegral] using hm

theorem energy_concentration_ratio_tendsto
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun j => (n j : ℝ) / h j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (n j : ℝ) / h j ^ 3) atTop (𝓝 (0 : ℝ)))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun j =>
      (Measure.pi (fun _ : Fin (n j) => ν)).real
        ((@Shao.closedStrip (n j) (h j)) ∩
          {a : Shao.Path (n j) |
            ε < |(Shao.energy a - (n j : ℝ)) / h j ^ 2|}) /
      (Measure.pi (fun _ : Fin (n j) => ν)).real
        (@Shao.closedStrip (n j) (h j)))
      atTop (𝓝 (0 : ℝ)) := by
  let G : ℕ → ℝ := fun j =>
    (Measure.pi (fun _ : Fin (n j) => ν)).real (@Shao.closedStrip (n j) (h j))
  let R : ℕ → ℝ := fun j =>
    (Measure.pi (fun _ : Fin (n j) => ν)).real
      ((@Shao.closedStrip (n j) (h j)) ∩
        {a : Shao.Path (n j) | ε < |(Shao.energy a - (n j : ℝ)) / h j ^ 2|})
  let D : ℝ := Real.exp ε + Real.exp (-ε) - 2
  let U : ℕ → ℝ := fun j =>
    (energyJointIntegral ν (n j) (h j) 1 / G j +
      energyJointIntegral ν (n j) (h j) (-1) / G j - 2) / D
  have hD : 0 < D := (exp_pair_deviation_bound ε 0 hε).1
  have hp := energy_laplace_ratio_tendsto ν h3 hmean hsecond h n hinfty hlong hshort 1
  have hm := energy_laplace_ratio_tendsto ν h3 hmean hsecond h n hinfty hlong hshort (-1)
  have hU : Tendsto U atTop (𝓝 (0 : ℝ)) := by
    simpa only [U, sub_self, zero_div, show (1 : ℝ) + 1 = 2 by norm_num] using
      ((hp.add hm).sub_const 2).div_const D
  have hGpos : ∀ᶠ j in atTop, 0 < G j :=
    closedStrip_probability_eventually_pos ν h3 hmean hsecond h n hinfty hlong hshort
  have hlower : ∀ᶠ j in atTop, 0 ≤ R j / G j := by
    filter_upwards [hGpos] with j hj
    exact div_nonneg ENNReal.toReal_nonneg hj.le
  have hupper : ∀ᶠ j in atTop, R j / G j ≤ U j := by
    filter_upwards [hGpos, hinfty.eventually_ge_atTop 1] with j hj hh
    have hfinite := energy_deviation_finite_bound ν (n j) (h j) ε hh hε
    change R j / G j ≤
      (energyJointIntegral ν (n j) (h j) 1 / G j +
        energyJointIntegral ν (n j) (h j) (-1) / G j - 2) / D
    apply (le_div_iff₀ hD).2
    calc
      (R j / G j) * D = (D * R j) / G j := by ring
      _ ≤ (energyJointIntegral ν (n j) (h j) 1 +
          energyJointIntegral ν (n j) (h j) (-1) - 2 * G j) / G j :=
        div_le_div_of_nonneg_right hfinite hj.le
      _ = energyJointIntegral ν (n j) (h j) 1 / G j +
          energyJointIntegral ν (n j) (h j) (-1) / G j - 2 := by
        field_simp [hj.ne']
        <;> ring
  simpa only [R, G] using squeeze_zero' hlower hupper hU

end Shao.OQ4.ConditionalEnergyConcentration
end
