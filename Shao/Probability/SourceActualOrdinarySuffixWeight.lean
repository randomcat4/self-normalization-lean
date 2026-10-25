import Shao.C2.AuxiliaryUnmarkedDampedMoments
import Shao.C2.AuxiliaryThirdMomentTruncation
import Shao.Probability.SourceSuffixScalarInterfaces

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
noncomputable section
namespace Shao.Probability
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem iid_actual_ordinary_suffix_weight_first_moment_and_sum :
    ∃ C : ℝ, 0 < C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho],
        Integrable (fun z : ℝ => |z| ^ 3) rho →
        (∫ z : ℝ, z ∂rho) = 0 →
        (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        let P : (t : ℕ) → Measure (Shao.Path t) :=
          fun t => Measure.pi (fun _ : Fin t => rho)
        let W : (t : ℕ) → Shao.Path t → ℝ := fun t u =>
          if 0 < Shao.energy u ∧ 2 * beta ^ 2 ≤ Shao.energy u then
            1 / Real.sqrt (Shao.energy u) *
              (1 + |Shao.prefixSum u t| / Real.sqrt (Shao.energy u)) ^ 2
          else 0
        (∀ t : ℕ,
          Measurable (W t) ∧
          Integrable (W t) (P t) ∧
          (∀ u : Shao.Path t, 0 ≤ W t u) ∧
          (∫ u : Shao.Path t, W t u ∂P t) ≤
            C / Real.sqrt ((t : ℝ) + beta ^ 2)) ∧
        (∀ u : Shao.Path 0, W 0 u = 0) ∧
        (∀ n : ℕ,
          (∑ t ∈ Finset.Icc 0 n, ∫ u : Shao.Path t, W t u ∂P t) ≤
            C * Real.sqrt (n : ℝ)) := by
  classical
  let c : ℝ := (1 - Real.exp (-2)) / 8
  have hc : 0 < c := raw_gaussian_damped_coordinate_factors.2.1
  let K0 : ℝ := Classical.choose
    (Shao.C2.AuxiliaryUnmarkedDampedMoments.auxiliary_actual_unmarked_gaussian_damped_moments 0)
  let K2 : ℝ := Classical.choose
    (Shao.C2.AuxiliaryUnmarkedDampedMoments.auxiliary_actual_unmarked_gaussian_damped_moments 2)
  have hs0 := Classical.choose_spec
    (Shao.C2.AuxiliaryUnmarkedDampedMoments.auxiliary_actual_unmarked_gaussian_damped_moments 0)
  have hs2 := Classical.choose_spec
    (Shao.C2.AuxiliaryUnmarkedDampedMoments.auxiliary_actual_unmarked_gaussian_damped_moments 2)
  have hK0 : 0 < K0 := hs0.1
  have hK2 : 0 < K2 := hs2.1
  let A0 : ℝ := Real.rpow 2 (1 / 2 : ℝ) * Real.exp 1 * (1 / 2 : ℝ)
  let A2 : ℝ := Real.rpow 2 (3 / 2 : ℝ) * Real.exp 1 * (3 / 2 : ℝ)
  let D : ℝ := 2 * (A0 * K0 + A2 * K2)
  let G : ℝ := Real.Gamma (1 / 2 : ℝ) / Real.sqrt c
  let H : ℝ := Real.sqrt 2 * (1 + G)
  let C : ℝ := 2 * D * H
  have hA0 : 0 < A0 := by dsimp [A0]; positivity
  have hA2 : 0 < A2 := by dsimp [A2]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hG : 0 < G := div_pos (Real.Gamma_pos_of_pos (by norm_num)) (Real.sqrt_pos.2 hc)
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro rho hProb h3 hmean hnorm beta P W
  letI : IsProbabilityMeasure rho := hProb
  have h2 : Integrable (fun z : ℝ => z ^ 2) rho := by
    apply (h3.add (integrable_const 1)).mono' (by fun_prop)
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z)]
      change z ^ 2 ≤ |z| ^ 3 + 1
      by_cases hz : |z| ≤ 1
      · have hh := pow_le_pow_left₀ (abs_nonneg z) hz 2
        rw [sq_abs] at hh
        nlinarith [pow_nonneg (abs_nonneg z) 3]
      · have hz' : 1 ≤ |z| := le_of_not_ge hz
        have hh := mul_nonneg (sq_nonneg (|z|)) (sub_nonneg.mpr hz')
        nlinarith [sq_abs z]
  have hBeta : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one rho h2 h3 hnorm
  have hBeta0 : 0 < beta := by linarith
  have hBetaSq : 0 < beta ^ 2 := sq_pos_of_pos hBeta0
  let b : ℝ := 4 * beta ^ 2
  let L : ℝ := 1 / b
  let S : Set ℝ := Set.Ioo 0 L
  have hb : 0 < b := by dsimp [b]; positivity
  have hL : 0 < L := one_div_pos.2 hb
  have hret : (1 / 2 : ℝ) ≤
      ∫ z : ℝ, if z ^ 2 ≤ b then z ^ 2 else 0 ∂rho :=
    (Shao.C2.AuxiliaryThirdMomentTruncation.auxiliary_actual_third_moment_retains_half
      rho h2 h3 hnorm).2
  have hsmall (a : ℝ) (ha : 0 < a) :
      IntegrableOn (fun s : ℝ => Real.rpow s (a - 1)) S ∧
        (∫ s : ℝ in S, Real.rpow s (a - 1)) = Real.rpow L a / a := by
    have hi := intervalIntegral.intervalIntegrable_rpow'
      (a := (0 : ℝ)) (b := L) (by linarith : -1 < a - 1)
    have he := integral_rpow (a := (0 : ℝ)) (b := L) (r := a - 1)
      (Or.inl (by linarith))
    refine ⟨hi.1.mono_set Set.Ioo_subset_Ioc_self, ?_⟩
    rw [intervalIntegral.integral_of_le hL.le, integral_Ioc_eq_integral_Ioo] at he
    simpa only [S, sub_add_cancel, Real.zero_rpow ha.ne', sub_zero,
      Real.rpow_eq_pow] using he
  have hhalf : IntegrableOn (fun s : ℝ => Real.rpow s (-1 / 2 : ℝ)) S ∧
      (∫ s : ℝ in S, Real.rpow s (-1 / 2 : ℝ)) = 1 / beta := by
    have hh := hsmall (1 / 2) (by norm_num)
    rw [show (1 / 2 : ℝ) - 1 = -1 / 2 by ring] at hh
    refine ⟨hh.1, ?_⟩
    rw [hh.2, Real.rpow_eq_pow, ← Real.sqrt_eq_rpow]
    dsimp [L, b]
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_sq_eq_abs,
      abs_of_pos hBeta0]
    rw [show Real.sqrt (4 : ℝ) = 2 by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
      norm_num]
    norm_num <;> field_simp <;> ring
  let kernel : ℕ → ℝ → ℝ := fun t s =>
    Real.rpow s (-1 / 2 : ℝ) * Real.exp (-c * s * (t : ℝ))
  let I : ℕ → ℝ := fun t => ∫ s : ℝ in S, kernel t s
  have hknn (t : ℕ) (s : ℝ) (hs : 0 ≤ s) : 0 ≤ kernel t s :=
    mul_nonneg (Real.rpow_nonneg hs _) (Real.exp_pos _).le
  have hki (t : ℕ) : IntegrableOn (kernel t) S := by
    have hkm : Measurable (kernel t) := by dsimp [kernel]; fun_prop
    apply hhalf.1.mono' hkm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (hknn t s hs.1.le)]
    calc
      kernel t s ≤ Real.rpow s (-1 / 2 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.2 (by
            have hh := mul_nonneg (mul_nonneg hc.le hs.1.le) (Nat.cast_nonneg t)
            nlinarith only [hh])) (Real.rpow_nonneg hs.1.le _)
      _ = _ := mul_one _
  have hInn (t : ℕ) : 0 ≤ I t := integral_nonneg_of_ae (by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact hknn t s hs.1.le)
  have hIsmall (t : ℕ) : I t ≤ 1 / beta := by
    rw [← hhalf.2]
    apply integral_mono_ae (hki t) hhalf.1
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    calc
      kernel t s ≤ Real.rpow s (-1 / 2 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.2 (by
            have hh := mul_nonneg (mul_nonneg hc.le hs.1.le) (Nat.cast_nonneg t)
            nlinarith only [hh])) (Real.rpow_nonneg hs.1.le _)
      _ = _ := mul_one _
  have hIlarge (t : ℕ) (ht : 0 < t) : I t ≤ G / Real.sqrt (t : ℝ) := by
    have htp : 0 < (t : ℝ) := by exact_mod_cast ht
    have hg := SourceSuffixScalarInterfaces.gamma_kernel (1 / 2) (c * (t : ℝ))
      (by norm_num) (mul_pos hc htp)
    have he (s : ℝ) : Real.rpow s ((1 / 2 : ℝ) - 1) *
        Real.exp (-(c * (t : ℝ)) * s) = kernel t s := by
      dsimp only [kernel]
      rw [show (1 / 2 : ℝ) - 1 = -1 / 2 by ring,
        show -(c * (t : ℝ)) * s = -c * s * (t : ℝ) by ring]
    have hg' : IntegrableOn (kernel t) (Set.Ioi 0) := by
      simpa only [he] using hg.1
    calc
      I t ≤ ∫ s : ℝ in Set.Ioi 0, kernel t s := by
        apply setIntegral_mono_set hg' _ (ae_of_all _ fun s (hs : s ∈ S) => hs.1)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        exact hknn t s hs.le
      _ = Real.rpow (1 / (c * (t : ℝ))) (1 / 2 : ℝ) * Real.Gamma (1 / 2 : ℝ) := by
        simpa only [he] using hg.2
      _ = G / Real.sqrt (t : ℝ) := by
        rw [Real.rpow_eq_pow, ← Real.sqrt_eq_rpow,
          Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one,
          Real.sqrt_mul hc.le]
        dsimp [G]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  have hIbound (t : ℕ) : I t ≤ H / Real.sqrt ((t : ℝ) + beta ^ 2) := by
    have hs : 0 < Real.sqrt ((t : ℝ) + beta ^ 2) := Real.sqrt_pos.2 (by positivity)
    apply (le_div_iff₀ hs).2
    by_cases ht : (t : ℝ) ≤ beta ^ 2
    · have hr : Real.sqrt ((t : ℝ) + beta ^ 2) ≤ Real.sqrt 2 * beta := by
        have hh := Real.sqrt_le_sqrt (show (t : ℝ) + beta ^ 2 ≤ 2 * beta ^ 2 by linarith)
        rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
          Real.sqrt_sq_eq_abs, abs_of_pos hBeta0] at hh
      calc
        I t * Real.sqrt ((t : ℝ) + beta ^ 2) ≤ I t * (Real.sqrt 2 * beta) :=
          mul_le_mul_of_nonneg_left hr (hInn t)
        _ = Real.sqrt 2 * (I t * beta) := by ring
        _ ≤ Real.sqrt 2 * 1 := mul_le_mul_of_nonneg_left
          ((le_div_iff₀ hBeta0).1 (hIsmall t)) (Real.sqrt_nonneg _)
        _ ≤ H := by dsimp [H]; nlinarith [Real.sqrt_nonneg (2 : ℝ)]
    · have ht' : 0 < t := by
        have htp : 0 < (t : ℝ) := hBetaSq.trans (lt_of_not_ge ht)
        exact_mod_cast htp
      have htp : 0 < (t : ℝ) := by exact_mod_cast ht'
      have hr : Real.sqrt ((t : ℝ) + beta ^ 2) ≤ Real.sqrt 2 * Real.sqrt (t : ℝ) := by
        have hh := Real.sqrt_le_sqrt
          (show (t : ℝ) + beta ^ 2 ≤ 2 * (t : ℝ) by linarith [lt_of_not_ge ht])
        rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at hh
      calc
        I t * Real.sqrt ((t : ℝ) + beta ^ 2) ≤ I t * (Real.sqrt 2 * Real.sqrt (t : ℝ)) :=
          mul_le_mul_of_nonneg_left hr (hInn t)
        _ = Real.sqrt 2 * (I t * Real.sqrt (t : ℝ)) := by ring
        _ ≤ Real.sqrt 2 * G := mul_le_mul_of_nonneg_left
          ((le_div_iff₀ (Real.sqrt_pos.2 htp)).1 (hIlarge t ht')) (Real.sqrt_nonneg _)
        _ ≤ H := by dsimp [H]; nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hsb (s : ℝ) (hs : s ∈ S) : s ≤ 2 / b := by
    calc
      s ≤ 1 / b := hs.2.le
      _ ≤ 1 / b + 1 / b := le_add_of_nonneg_right (one_div_pos.2 hb).le
      _ = _ := by ring
  have hm0 (t : ℕ) (s : ℝ) (hs : s ∈ S) :
      Integrable (fun u : Shao.Path t => |Shao.prefixSum u t| ^ 0 *
        Real.exp (-s * Shao.energy u)) (P t) ∧
      (∫ u : Shao.Path t, |Shao.prefixSum u t| ^ 0 * Real.exp (-s * Shao.energy u) ∂P t) ≤
        K0 * Real.rpow s (-(0 : ℝ) / 2) * Real.exp (-c * s * (t : ℝ)) := by
    simpa only [if_pos hret, Nat.cast_zero, P, K0, c] using
      hs0.2 rho h2 hmean hnorm t b s hb hs.1 (hsb s hs)
  have hm2 (t : ℕ) (s : ℝ) (hs : s ∈ S) :
      Integrable (fun u : Shao.Path t => |Shao.prefixSum u t| ^ 2 *
        Real.exp (-s * Shao.energy u)) (P t) ∧
      (∫ u : Shao.Path t, |Shao.prefixSum u t| ^ 2 * Real.exp (-s * Shao.energy u) ∂P t) ≤
        K2 * Real.rpow s (-(2 : ℝ) / 2) * Real.exp (-c * s * (t : ℝ)) := by
    simpa only [if_pos hret, Nat.cast_ofNat, P, K2, c] using
      hs2.2 rho h2 hmean hnorm t b s hb hs.1 (hsb s hs)
  have hpower (p : ℕ) (Kp : ℝ) (hKp : 0 < Kp) (t : ℕ)
      (hmoment : ∀ s : ℝ, s ∈ S →
        Integrable (fun u : Shao.Path t => |Shao.prefixSum u t| ^ p *
          Real.exp (-s * Shao.energy u)) (P t) ∧
        (∫ u : Shao.Path t, |Shao.prefixSum u t| ^ p * Real.exp (-s * Shao.energy u) ∂P t) ≤
          Kp * Real.rpow s (-(p : ℝ) / 2) * Real.exp (-c * s * (t : ℝ))) :
      let a : ℝ := ((p : ℝ) + 1) / 2
      let F : Shao.Path t → ℝ := fun u =>
        if 0 < Shao.energy u ∧ 2 * beta ^ 2 ≤ Shao.energy u then
          |Shao.prefixSum u t| ^ p * Real.rpow (Shao.energy u) (-a) else 0
      Measurable F ∧ Integrable F (P t) ∧ (∀ u, 0 ≤ F u) ∧
        (∫ u, F u ∂P t) ≤ (Real.rpow 2 a * Real.exp 1 * a) * Kp * I t := by
    intro a F
    have ha : 0 < a := by dsimp [a]; positivity
    let A : ℝ := Real.rpow 2 a * Real.exp 1 * a
    have hA : 0 < A := by dsimp [A]; positivity
    let K : ℝ × Shao.Path t → ℝ := fun x =>
      Real.rpow x.1 (a - 1) *
        (|Shao.prefixSum x.2 t| ^ p * Real.exp (-x.1 * Shao.energy x.2))
    have hTm : Measurable (Shao.energy : Shao.Path t → ℝ) := Shao.measurable_energy
    have hdm : Measurable (fun u : Shao.Path t => Shao.prefixSum u t) := Shao.measurable_prefixSum t
    have hKm : Measurable K := by dsimp [K]; fun_prop
    have hKnn (s : ℝ) (hs : 0 ≤ s) (u : Shao.Path t) : 0 ≤ K (s, u) :=
      mul_nonneg (Real.rpow_nonneg hs _)
        (mul_nonneg (pow_nonneg (abs_nonneg _) _) (Real.exp_pos _).le)
    have hsexp (s : ℝ) (hs : 0 < s) :
        Real.rpow s (a - 1) * Real.rpow s (-(p : ℝ) / 2) = Real.rpow s (-1 / 2 : ℝ) := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_add hs]
      congr 1
      dsimp [a]
      ring
    have hsections : ∀ᵐ s ∂volume.restrict S, Integrable (fun u => K (s, u)) (P t) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact ((hmoment s hs).1).const_mul (Real.rpow s (a - 1))
    have hupper (s : ℝ) (hs : s ∈ S) : (∫ u, K (s, u) ∂P t) ≤ Kp * kernel t s := by
      change (∫ u, Real.rpow s (a - 1) *
        (|Shao.prefixSum u t| ^ p * Real.exp (-s * Shao.energy u)) ∂P t) ≤ _
      rw [integral_const_mul]
      calc
        _ ≤ Real.rpow s (a - 1) *
            (Kp * Real.rpow s (-(p : ℝ) / 2) * Real.exp (-c * s * (t : ℝ))) :=
          mul_le_mul_of_nonneg_left (hmoment s hs).2 (Real.rpow_nonneg hs.1.le _)
        _ = Kp * (Real.rpow s (a - 1) * Real.rpow s (-(p : ℝ) / 2)) *
            Real.exp (-c * s * (t : ℝ)) := by ring
        _ = _ := by rw [hsexp s hs.1]; dsimp [kernel]; ring
    have hnormi : Integrable (fun s => ∫ u, ‖K (s, u)‖ ∂P t) (volume.restrict S) := by
      apply ((hki t).const_mul Kp).mono' hKm.aestronglyMeasurable.norm.integral_prod_right'
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      have he : (∫ u, ‖K (s, u)‖ ∂P t) = ∫ u, K (s, u) ∂P t := by
        apply integral_congr_ae
        exact ae_of_all _ fun u => Real.norm_of_nonneg (hKnn s hs.1.le u)
      rw [he]
      exact hupper s hs
    have hKi : Integrable K ((volume.restrict S).prod (P t)) :=
      (integrable_prod_iff hKm.aestronglyMeasurable).2 ⟨hsections, hnormi⟩
    have hFm : Measurable F := by
      apply Measurable.ite
        ((measurableSet_lt measurable_const hTm).inter (measurableSet_le measurable_const hTm))
      · exact ((continuous_abs.measurable.comp hdm).pow_const p).mul
          (by simpa only [Real.rpow_eq_pow] using hTm.pow_const (-a))
      · exact measurable_const
    have hFnn (u : Shao.Path t) : 0 ≤ F u := by
      dsimp [F]
      split_ifs with hu
      · exact mul_nonneg (pow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg hu.1.le _)
      · exact le_rfl
    have hpoint (u : Shao.Path t) : F u ≤ A * ∫ s : ℝ, K (s, u) ∂volume.restrict S := by
      by_cases hu : 0 < Shao.energy u ∧ 2 * beta ^ 2 ≤ Shao.energy u
      · rw [show F u = |Shao.prefixSum u t| ^ p * Real.rpow (Shao.energy u) (-a) from if_pos hu]
        have hi := SourceSuffixScalarInterfaces.inverse_laplace a (2 * Shao.energy u) b ha hb
          (show b ≤ 2 * Shao.energy u by dsimp [b]; linarith [hu.2])
        have hg1 := (SourceSuffixScalarInterfaces.gamma_kernel a (Shao.energy u) ha hu.1).1
        have hg2 := (SourceSuffixScalarInterfaces.gamma_kernel a (2 * Shao.energy u) ha
          (mul_pos (by norm_num : (0 : ℝ) < 2) hu.1)).1
        have hgi1 : IntegrableOn (fun s : ℝ => Real.rpow s (a - 1) *
            Real.exp (-s * Shao.energy u)) S := by
          have hh : IntegrableOn (fun s : ℝ => Real.rpow s (a - 1) *
              Real.exp (-s * Shao.energy u)) (Set.Ioi 0) := by
            simpa only [neg_mul, mul_neg, mul_comm] using hg1
          exact hh.mono_set Set.Ioo_subset_Ioi_self
        have hgi2 : IntegrableOn (fun s : ℝ => Real.rpow s (a - 1) *
            Real.exp (-s * (2 * Shao.energy u))) S := by
          have hh : IntegrableOn (fun s : ℝ => Real.rpow s (a - 1) *
              Real.exp (-s * (2 * Shao.energy u))) (Set.Ioi 0) := by
            simpa only [neg_mul, mul_neg, mul_comm] using hg2
          exact hh.mono_set Set.Ioo_subset_Ioi_self
        have hiexp : (∫ s : ℝ in S, Real.rpow s (a - 1) * Real.exp (-s * (2 * Shao.energy u))) ≤
            ∫ s : ℝ in S, Real.rpow s (a - 1) * Real.exp (-s * Shao.energy u) := by
          apply integral_mono_ae hgi2 hgi1
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hs.1.le _)
          apply Real.exp_le_exp.2
          nlinarith [mul_pos hs.1 hu.1]
        have hscale : Real.rpow (Shao.energy u) (-a) =
            Real.rpow 2 a * Real.rpow (2 * Shao.energy u) (-a) := by
          simp only [Real.rpow_eq_pow]
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hu.1.le,
            ← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          simp
        have hinv : Real.rpow (Shao.energy u) (-a) ≤
            A * (∫ s : ℝ in S, Real.rpow s (a - 1) * Real.exp (-s * Shao.energy u)) := by
          calc
            _ = Real.rpow 2 a * Real.rpow (2 * Shao.energy u) (-a) := hscale
            _ ≤ Real.rpow 2 a * (Real.exp 1 * a *
                (∫ s : ℝ in S, Real.rpow s (a - 1) * Real.exp (-s * (2 * Shao.energy u)))) :=
              mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg (by norm_num) _)
            _ ≤ Real.rpow 2 a * (Real.exp 1 * a *
                (∫ s : ℝ in S, Real.rpow s (a - 1) * Real.exp (-s * Shao.energy u))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hiexp
                (mul_pos (Real.exp_pos _) ha).le) (Real.rpow_nonneg (by norm_num) _)
            _ = _ := by dsimp [A]; ring
        calc
          _ ≤ |Shao.prefixSum u t| ^ p * (A *
              (∫ s : ℝ in S, Real.rpow s (a - 1) * Real.exp (-s * Shao.energy u))) :=
            mul_le_mul_of_nonneg_left hinv (pow_nonneg (abs_nonneg _) _)
          _ = A * (|Shao.prefixSum u t| ^ p *
              (∫ s : ℝ in S, Real.rpow s (a - 1) * Real.exp (-s * Shao.energy u))) := by ring
          _ = _ := by
            rw [← integral_const_mul]
            congr 1
            apply integral_congr_ae
            exact ae_of_all _ fun s => by dsimp [K]; ring
      · rw [show F u = 0 from if_neg hu]
        exact mul_nonneg hA.le (integral_nonneg_of_ae (by
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
          exact hKnn s hs.1.le u))
    have hFi : Integrable F (P t) := by
      apply (hKi.integral_prod_right.const_mul A).mono' hFm.aestronglyMeasurable
      exact ae_of_all _ fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hFnn u)]
        exact hpoint u
    refine ⟨hFm, hFi, hFnn, ?_⟩
    calc
      _ ≤ ∫ u, A * (∫ s : ℝ, K (s, u) ∂volume.restrict S) ∂P t :=
        integral_mono hFi (hKi.integral_prod_right.const_mul A) hpoint
      _ = A * ∫ s : ℝ, ∫ u, K (s, u) ∂P t ∂volume.restrict S := by
        rw [integral_const_mul, ← integral_integral_swap hKi]
      _ ≤ A * ∫ s : ℝ, Kp * kernel t s ∂volume.restrict S := by
        apply mul_le_mul_of_nonneg_left _ hA.le
        apply integral_mono_ae hKi.integral_prod_left ((hki t).const_mul Kp)
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        exact hupper s hs
      _ = _ := by rw [integral_const_mul]; dsimp [I, A]; ring
  have hhalfPow (z : ℝ) (hz : 0 < z) :
      Real.rpow z (-1 / 2 : ℝ) = 1 / Real.sqrt z := by
    simp only [Real.rpow_eq_pow]
    rw [show (-1 / 2 : ℝ) = -((1 / 2 : ℝ)) by ring,
      Real.rpow_neg hz.le, ← Real.sqrt_eq_rpow, one_div]
  have hthreePow (z : ℝ) (hz : 0 < z) :
      Real.rpow z (-3 / 2 : ℝ) = (1 / Real.sqrt z) * (1 / z) := by
    calc
      Real.rpow z (-3 / 2 : ℝ) =
          Real.rpow z (-1 / 2 : ℝ) * Real.rpow z (-1 : ℝ) := by
        simp only [Real.rpow_eq_pow]
        rw [← Real.rpow_add hz]
        congr 1
        ring
      _ = _ := by
        rw [hhalfPow z hz]
        simp only [Real.rpow_eq_pow, Real.rpow_neg_one, one_div]
  have hWdata (t : ℕ) : Measurable (W t) ∧ Integrable (W t) (P t) ∧
      (∀ u : Shao.Path t, 0 ≤ W t u) ∧
      (∫ u : Shao.Path t, W t u ∂P t) ≤ D * I t := by
    let F0 : Shao.Path t → ℝ := fun u =>
      if 0 < Shao.energy u ∧ 2 * beta ^ 2 ≤ Shao.energy u then
        Real.rpow (Shao.energy u) (-1 / 2 : ℝ) else 0
    let F2 : Shao.Path t → ℝ := fun u =>
      if 0 < Shao.energy u ∧ 2 * beta ^ 2 ≤ Shao.energy u then
        |Shao.prefixSum u t| ^ 2 * Real.rpow (Shao.energy u) (-3 / 2 : ℝ) else 0
    have h0 : Measurable F0 ∧ Integrable F0 (P t) ∧ (∀ u, 0 ≤ F0 u) ∧
        (∫ u, F0 u ∂P t) ≤ A0 * K0 * I t := by
      convert hpower 0 K0 hK0 t (by simpa only [Nat.cast_zero] using hm0 t) using 1 <;>
        norm_num [F0, A0]
    have h2' : Measurable F2 ∧ Integrable F2 (P t) ∧ (∀ u, 0 ≤ F2 u) ∧
        (∫ u, F2 u ∂P t) ≤ A2 * K2 * I t := by
      convert hpower 2 K2 hK2 t (hm2 t) using 1 <;> norm_num [F2, A2]
    have hsum : Integrable (fun u => 2 * (F0 u + F2 u)) (P t) :=
      (h0.2.1.add h2'.2.1).const_mul 2
    have hWm : Measurable (W t) := by
      have hTm : Measurable (Shao.energy : Shao.Path t → ℝ) := Shao.measurable_energy
      apply Measurable.ite
        ((measurableSet_lt measurable_const hTm).inter (measurableSet_le measurable_const hTm))
      · exact (measurable_const.div hTm.sqrt).mul
          ((measurable_const.add
            ((continuous_abs.measurable.comp (Shao.measurable_prefixSum t)).div hTm.sqrt)).pow_const 2)
      · exact measurable_const
    have hWnn (u : Shao.Path t) : 0 ≤ W t u := by
      dsimp [W]
      split_ifs <;> positivity
    have hpoint (u : Shao.Path t) : W t u ≤ 2 * (F0 u + F2 u) := by
      by_cases hu : 0 < Shao.energy u ∧ 2 * beta ^ 2 ≤ Shao.energy u
      · rw [show W t u = 1 / Real.sqrt (Shao.energy u) *
            (1 + |Shao.prefixSum u t| / Real.sqrt (Shao.energy u)) ^ 2 from if_pos hu]
        have hquad : (1 + |Shao.prefixSum u t| / Real.sqrt (Shao.energy u)) ^ 2 ≤
            2 * (1 + (|Shao.prefixSum u t| / Real.sqrt (Shao.energy u)) ^ 2) := by
          nlinarith [sq_nonneg (|Shao.prefixSum u t| / Real.sqrt (Shao.energy u) - 1)]
        calc
          _ ≤ (1 / Real.sqrt (Shao.energy u)) *
              (2 * (1 + (|Shao.prefixSum u t| / Real.sqrt (Shao.energy u)) ^ 2)) :=
            mul_le_mul_of_nonneg_left hquad (by positivity)
          _ = _ := by
            dsimp only [F0, F2]
            rw [if_pos hu, if_pos hu, hhalfPow _ hu.1, hthreePow _ hu.1,
              div_pow, Real.sq_sqrt hu.1.le]
            ring
      · simp only [W, F0, F2, if_neg hu, add_zero, mul_zero, le_refl]
    have hWi : Integrable (W t) (P t) := by
      apply hsum.mono' hWm.aestronglyMeasurable
      exact ae_of_all _ fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hWnn u)]
        exact hpoint u
    refine ⟨hWm, hWi, hWnn, ?_⟩
    calc
      _ ≤ ∫ u, 2 * (F0 u + F2 u) ∂P t := integral_mono hWi hsum hpoint
      _ = 2 * ((∫ u, F0 u ∂P t) + ∫ u, F2 u ∂P t) := by
        rw [integral_const_mul, integral_add h0.2.1 h2'.2.1]
      _ ≤ 2 * (A0 * K0 * I t + A2 * K2 * I t) :=
        mul_le_mul_of_nonneg_left (add_le_add h0.2.2.2 h2'.2.2.2) (by norm_num)
      _ = _ := by dsimp [D]; ring
  have hEW (t : ℕ) : (∫ u : Shao.Path t, W t u ∂P t) ≤
      D * H / Real.sqrt ((t : ℝ) + beta ^ 2) := by
    calc
      _ ≤ D * I t := (hWdata t).2.2.2
      _ ≤ D * (H / Real.sqrt ((t : ℝ) + beta ^ 2)) :=
        mul_le_mul_of_nonneg_left (hIbound t) hD.le
      _ = _ := by ring
  have hWzero (u : Shao.Path 0) : W 0 u = 0 := by
    simp [W, Shao.energy]
  have hEzero : (∫ u : Shao.Path 0, W 0 u ∂P 0) = 0 := by
    apply integral_eq_zero_of_ae
    exact ae_of_all _ hWzero
  have hsum (n : ℕ) :
      (∑ t ∈ Finset.Icc 0 n, ∫ u : Shao.Path t, W t u ∂P t) ≤
        2 * D * H * Real.sqrt (n : ℝ) := by
    induction n with
    | zero => simp [hEzero]
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hroot : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := by positivity
      have hterm : (∫ u : Shao.Path (n + 1), W (n + 1) u ∂P (n + 1)) ≤
          D * H / Real.sqrt ((n + 1 : ℕ) : ℝ) := by
        apply (hEW (n + 1)).trans
        apply div_le_div_of_nonneg_left (mul_pos hD hH).le hroot
        exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg beta))
      have hs0 := Real.sq_sqrt (Nat.cast_nonneg n)
      have hs1 := Real.sq_sqrt (Nat.cast_nonneg (n + 1))
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
        simp only [Nat.cast_add, Nat.cast_one]
      have hstep : 1 / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤
          2 * Real.sqrt ((n + 1 : ℕ) : ℝ) - 2 * Real.sqrt (n : ℝ) := by
        apply (div_le_iff₀ hroot).2
        nlinarith only [hs0, hs1, hcast,
          sq_nonneg (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ))]
      have hpaid := mul_le_mul_of_nonneg_left hstep (mul_pos hD hH).le
      calc
        _ ≤ 2 * D * H * Real.sqrt (n : ℝ) +
            D * H / Real.sqrt ((n + 1 : ℕ) : ℝ) := add_le_add ih hterm
        _ = 2 * D * H * Real.sqrt (n : ℝ) +
            D * H * (1 / Real.sqrt ((n + 1 : ℕ) : ℝ)) := by ring
        _ ≤ 2 * D * H * Real.sqrt (n : ℝ) +
            D * H * (2 * Real.sqrt ((n + 1 : ℕ) : ℝ) - 2 * Real.sqrt (n : ℝ)) :=
          add_le_add (le_refl _) hpaid
        _ = _ := by ring
  refine ⟨?_, hWzero, ?_⟩
  · intro t
    refine ⟨(hWdata t).1, (hWdata t).2.1, (hWdata t).2.2.1, ?_⟩
    apply (hEW t).trans
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    dsimp [C]
    nlinarith [mul_pos hD hH]
  · intro n
    simpa only [C, mul_assoc] using hsum n

end Shao.Probability
