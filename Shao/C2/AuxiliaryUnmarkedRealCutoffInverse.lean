import Shao.C2.AuxiliaryRealDampedMoments
import Shao.Probability.SourceSuffixScalarInterfaces
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace Shao.C2.AuxiliaryUnmarkedRealCutoffInverse
open MeasureTheory ProbabilityTheory

private theorem cutoff_exponential_kernel_integrable
    (q r b : ℝ) (hq : 0 < q) (hb : 0 < b) :
    IntegrableOn (fun s : ℝ => Real.rpow s (q / 2 - 1) * Real.exp (r * s))
      (Set.Ioo 0 (1 / b)) := by
  have hbase := (Shao.Probability.SourceSuffixScalarInterfaces.gamma_kernel
    (q / 2) 1 (by linarith) (by norm_num)).1
  have hbase' : IntegrableOn (fun s : ℝ => Real.rpow s (q / 2 - 1) * Real.exp (-s))
      (Set.Ioo 0 (1 / b)) := by
    have hbase0 : IntegrableOn (fun s : ℝ => Real.rpow s (q / 2 - 1) * Real.exp (-s)) (Set.Ioi 0) := by
      simpa only [neg_mul, one_mul] using hbase
    exact hbase0.mono_set Set.Ioo_subset_Ioi_self
  let C : ℝ := Real.exp ((|r| + 1) / b)
  have hm : Measurable (fun s : ℝ => Real.rpow s (q / 2 - 1) * Real.exp (r * s)) := by
    simp only [Real.rpow_eq_pow]
    fun_prop
  apply (hbase'.const_mul C).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have hn : 0 ≤ Real.rpow s (q / 2 - 1) * Real.exp (r * s) :=
    mul_nonneg (Real.rpow_nonneg hs.1.le _) (Real.exp_pos _).le
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  have he : r * s ≤ (|r| + 1) / b - s := by
    have h1 := mul_le_mul_of_nonneg_right (add_le_add_right (le_abs_self r) 1) hs.1.le
    have h2 := mul_le_mul_of_nonneg_left hs.2.le (by positivity : 0 ≤ |r| + 1)
    have h2' : (|r| + 1) * s ≤ (|r| + 1) / b := by
      simpa only [div_eq_mul_inv, one_mul] using h2
    nlinarith [h2']
  have hexp : Real.exp (r * s) ≤ C * Real.exp (-s) := by
    calc
      _ ≤ Real.exp ((|r| + 1) / b - s) := Real.exp_le_exp.mpr he
      _ = _ := by dsimp [C]; rw [sub_eq_add_neg, Real.exp_add]
  calc
    _ ≤ Real.rpow s (q / 2 - 1) * (C * Real.exp (-s)) :=
      mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hs.1.le _)
    _ = _ := by ring

private theorem unmarked_real_power_cutoff_inverse :
    let c : ℝ := (1 - Real.exp (-2)) / 8
    ∀ a q : ℝ, 0 ≤ a → 0 < q → ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu],
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 → (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        ∀ (n : ℕ) (b : ℝ), 0 < b →
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
          let T : Shao.Path n → ℝ := Shao.energy
          let d : Shao.Path n → ℝ := fun v => Shao.prefixSum v n
          let retained : ℝ := ∫ z : ℝ, if z ^ 2 ≤ b then z ^ 2 else 0 ∂nu
          let gamma : ℝ := if (1 / 2 : ℝ) ≤ retained then -c else 1
          let selected : Shao.Path n → ℝ := fun v =>
            if 0 < T v ∧ b ≤ T v then
              Real.rpow |d v| a * Real.rpow (T v) (-(q + a) / 2) else 0
          let kernel : ℝ → ℝ := fun s =>
            Real.rpow s (q / 2 - 1) * Real.exp (gamma * s * (n : ℝ))
          Integrable selected P ∧ IntegrableOn kernel (Set.Ioo 0 (1 / b)) ∧
            (∫ v, selected v ∂P) ≤ C * ∫ s : ℝ in Set.Ioo 0 (1 / b), kernel s := by
  intro c a q ha hq
  obtain ⟨Ca, hCa, hmoment⟩ :=
    Shao.C2.AuxiliaryRealDampedMoments.auxiliary_actual_unmarked_real_gaussian_damped_moments a ha
  let alpha : ℝ := (q + a) / 2
  have halpha : 0 < alpha := by dsimp [alpha]; linarith
  let A : ℝ := Real.exp 1 * alpha
  have hA : 0 < A := mul_pos (Real.exp_pos _) halpha
  refine ⟨A * Ca, mul_pos hA hCa, ?_⟩
  intro nu hnu h2 hmean hnorm n b hb P T d retained gamma selected kernel
  letI : IsProbabilityMeasure nu := hnu
  let S : Set ℝ := Set.Ioo 0 (1 / b)
  let K : ℝ × Shao.Path n → ℝ := fun x =>
    Real.rpow x.1 (alpha - 1) *
      (Real.rpow |d x.2| a * Real.exp (-x.1 * T x.2))
  have hTm : Measurable T := Shao.measurable_energy
  have hdm : Measurable d := Shao.measurable_prefixSum n
  have hKm : Measurable K := by
    dsimp [K]
    fun_prop
  have hknn (s : ℝ) (hs : 0 ≤ s) (v : Shao.Path n) : 0 ≤ K (s, v) :=
    mul_nonneg (Real.rpow_nonneg hs _)
      (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (Real.exp_pos _).le)
  have hki : IntegrableOn kernel S := by
    have h := cutoff_exponential_kernel_integrable q (gamma * (n : ℝ)) b hq hb
    simpa only [kernel, S, mul_assoc, mul_left_comm, mul_comm] using h
  have hsexp (s : ℝ) (hs : 0 < s) :
      Real.rpow s (alpha - 1) * Real.rpow s (-a / 2) = Real.rpow s (q / 2 - 1) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hs]
    congr 1
    dsimp [alpha]
    ring
  have hsb (s : ℝ) (hs : s ∈ S) : s ≤ 2 / b := by
    calc
      s ≤ 1 / b := hs.2.le
      _ ≤ 1 / b + 1 / b := le_add_of_nonneg_right (one_div_pos.2 hb).le
      _ = _ := by ring
  have hsections : ∀ᵐ s ∂volume.restrict S, Integrable (fun v => K (s, v)) P := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact ((hmoment nu h2 hmean hnorm n b s hb hs.1 (hsb s hs)).1).const_mul
      (Real.rpow s (alpha - 1))
  have hupper (s : ℝ) (hs : s ∈ S) : (∫ v, K (s, v) ∂P) ≤ Ca * kernel s := by
    change (∫ v, Real.rpow s (alpha - 1) *
      (Real.rpow |d v| a * Real.exp (-s * T v)) ∂P) ≤ _
    rw [integral_const_mul]
    calc
      _ ≤ Real.rpow s (alpha - 1) *
          (Ca * Real.rpow s (-a / 2) * Real.exp (gamma * s * (n : ℝ))) :=
        mul_le_mul_of_nonneg_left (hmoment nu h2 hmean hnorm n b s hb hs.1 (hsb s hs)).2
          (Real.rpow_nonneg hs.1.le _)
      _ = Ca * (Real.rpow s (alpha - 1) * Real.rpow s (-a / 2)) *
          Real.exp (gamma * s * (n : ℝ)) := by ring
      _ = _ := by rw [hsexp s hs.1]; dsimp [kernel]; ring
  have hnormi : Integrable (fun s => ∫ v, ‖K (s, v)‖ ∂P) (volume.restrict S) := by
    apply (hki.const_mul Ca).mono' hKm.aestronglyMeasurable.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have he : (∫ v, ‖K (s, v)‖ ∂P) = ∫ v, K (s, v) ∂P := by
      apply integral_congr_ae
      exact ae_of_all _ fun v => Real.norm_of_nonneg (hknn s hs.1.le v)
    rw [he]
    exact hupper s hs
  have hKi : Integrable K ((volume.restrict S).prod P) :=
    (integrable_prod_iff hKm.aestronglyMeasurable).2 ⟨hsections, hnormi⟩
  have hselm : Measurable selected := by
    apply Measurable.ite
      ((measurableSet_lt measurable_const hTm).inter (measurableSet_le measurable_const hTm))
    · simp only [Real.rpow_eq_pow]
      exact ((continuous_abs.measurable.comp hdm).pow_const a).mul (hTm.pow_const _)
    · exact measurable_const
  have hselnn (v : Shao.Path n) : 0 ≤ selected v := by
    dsimp [selected]
    split_ifs with hv
    · exact mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
        (Real.rpow_nonneg hv.1.le _)
    · exact le_rfl
  have hpoint (v : Shao.Path n) : selected v ≤ A * ∫ s : ℝ, K (s, v) ∂volume.restrict S := by
    by_cases hv : 0 < T v ∧ b ≤ T v
    · rw [show selected v = Real.rpow |d v| a * Real.rpow (T v) (-(q + a) / 2) from if_pos hv]
      have hi := Shao.Probability.SourceSuffixScalarInterfaces.inverse_laplace alpha (T v) b halpha hb hv.2
      have hexp : -(q + a) / 2 = -alpha := by dsimp [alpha]; ring
      rw [hexp]
      calc
        _ ≤ Real.rpow |d v| a * (A * ∫ s : ℝ in Set.Ioo 0 (1 / b),
            Real.rpow s (alpha - 1) * Real.exp (-s * T v)) :=
          mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg (abs_nonneg _) _)
        _ = A * (Real.rpow |d v| a * (∫ s : ℝ in Set.Ioo 0 (1 / b),
            Real.rpow s (alpha - 1) * Real.exp (-s * T v))) := by ring
        _ = _ := by
          rw [← integral_const_mul]
          congr 1
          apply integral_congr_ae
          exact ae_of_all _ fun s => by dsimp [K]; ring
    · rw [show selected v = 0 from if_neg hv]
      exact mul_nonneg hA.le (integral_nonneg_of_ae (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        exact hknn s hs.1.le v))
  have hseli : Integrable selected P := by
    apply (hKi.integral_prod_right.const_mul A).mono' hselm.aestronglyMeasurable
    exact ae_of_all _ fun v => by rw [Real.norm_eq_abs, abs_of_nonneg (hselnn v)]; exact hpoint v
  refine ⟨hseli, hki, ?_⟩
  calc
    _ ≤ ∫ v, A * (∫ s : ℝ, K (s, v) ∂volume.restrict S) ∂P :=
      integral_mono hseli (hKi.integral_prod_right.const_mul A) hpoint
    _ = A * ∫ s : ℝ, ∫ v, K (s, v) ∂P ∂volume.restrict S := by
      rw [integral_const_mul, ← integral_integral_swap hKi]
    _ ≤ A * ∫ s : ℝ, Ca * kernel s ∂volume.restrict S := by
      apply mul_le_mul_of_nonneg_left _ hA.le
      apply integral_mono_ae hKi.integral_prod_left (hki.const_mul Ca)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact hupper s hs
    _ = _ := by rw [integral_const_mul]; ring

theorem auxiliary_actual_unmarked_real_cutoff_inverse_moments :
    let c : ℝ := (1 - Real.exp (-2)) / 8
    ∀ a q : ℝ, 0 ≤ a → 0 < q → ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu],
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 → (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        ∀ (n : ℕ) (b : ℝ), 0 < b →
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
          let T : Shao.Path n → ℝ := Shao.energy
          let d : Shao.Path n → ℝ := fun v => Shao.prefixSum v n
          let retained : ℝ := ∫ z : ℝ, if z ^ 2 ≤ b then z ^ 2 else 0 ∂nu
          let gamma : ℝ := if (1 / 2 : ℝ) ≤ retained then -c else 1
          let selected : Shao.Path n → ℝ := fun v =>
            if 0 < T v ∧ b ≤ T v then
              Real.rpow (T v) (-q / 2) *
                Real.rpow (1 + |d v| / Real.sqrt (T v)) a else 0
          let kernel : ℝ → ℝ := fun s =>
            Real.rpow s (q / 2 - 1) * Real.exp (gamma * s * (n : ℝ))
          Integrable selected P ∧ IntegrableOn kernel (Set.Ioo 0 (1 / b)) ∧
            (∫ v, selected v ∂P) ≤ C * ∫ s : ℝ in Set.Ioo 0 (1 / b), kernel s := by
  intro c a q ha hq
  obtain ⟨C0, hC0, hmoment0⟩ := unmarked_real_power_cutoff_inverse 0 q (by norm_num) hq
  obtain ⟨Ca, hCa, hmomenta⟩ := unmarked_real_power_cutoff_inverse a q ha hq
  let D : ℝ := Real.rpow 2 a
  have hD : 0 < D := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨D * (C0 + Ca), mul_pos hD (add_pos hC0 hCa), ?_⟩
  intro nu hnu h2 hmean hnorm n b hb P T d retained gamma selected kernel
  letI : IsProbabilityMeasure nu := hnu
  let F0 : Shao.Path n → ℝ := fun v =>
    if 0 < T v ∧ b ≤ T v then Real.rpow (T v) (-q / 2) else 0
  let Fa : Shao.Path n → ℝ := fun v =>
    if 0 < T v ∧ b ≤ T v then Real.rpow |d v| a * Real.rpow (T v) (-(q + a) / 2) else 0
  have h0 : Integrable F0 P ∧ IntegrableOn kernel (Set.Ioo 0 (1 / b)) ∧
      (∫ v, F0 v ∂P) ≤ C0 * ∫ s : ℝ in Set.Ioo 0 (1 / b), kernel s := by
    simpa only [F0, P, T, kernel, gamma, retained, c, Real.rpow_eq_pow, Real.rpow_zero, one_mul, add_zero] using hmoment0 nu h2 hmean hnorm n b hb
  have hFa := hmomenta nu h2 hmean hnorm n b hb
  have hsum : Integrable (fun v => D * (F0 v + Fa v)) P :=
    (h0.1.add hFa.1).const_mul D
  have hpower (u : ℝ) (hu : 0 ≤ u) : Real.rpow (1 + u) a ≤ D * (1 + Real.rpow u a) := by
    have hnn : 0 ≤ Real.rpow u a := Real.rpow_nonneg hu _
    by_cases hle : u ≤ 1
    · calc
        _ ≤ Real.rpow 2 a := Real.rpow_le_rpow (by linarith) (by linarith) ha
        _ = D * 1 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hD.le
    · have hge : 1 ≤ u := (lt_of_not_ge hle).le
      calc
        _ ≤ Real.rpow (2 * u) a := Real.rpow_le_rpow (by linarith) (by linarith) ha
        _ = D * Real.rpow u a := Real.mul_rpow (by norm_num) hu
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hD.le
  have hpoint (v : Shao.Path n) : selected v ≤ D * (F0 v + Fa v) := by
    by_cases hv : 0 < T v ∧ b ≤ T v
    · dsimp only [selected, F0, Fa]
      rw [if_pos hv, if_pos hv, if_pos hv]
      have hratio : Real.rpow (|d v| / Real.sqrt (T v)) a =
          Real.rpow |d v| a * Real.rpow (T v) (-a / 2) := by
        simp only [Real.rpow_eq_pow]
        rw [Real.div_rpow (abs_nonneg _) (Real.sqrt_nonneg _) a,
          ← Real.rpow_div_two_eq_sqrt a hv.1.le, div_eq_mul_inv,
          ← Real.rpow_neg hv.1.le]
        congr 2
        ring
      have hcombine : Real.rpow (T v) (-q / 2) * Real.rpow (T v) (-a / 2) =
          Real.rpow (T v) (-(q + a) / 2) := by
        simp only [Real.rpow_eq_pow]
        rw [← Real.rpow_add hv.1]
        congr 1
        ring
      calc
        _ ≤ Real.rpow (T v) (-q / 2) * (D * (1 + Real.rpow (|d v| / Real.sqrt (T v)) a)) :=
          mul_le_mul_of_nonneg_left (hpower _ (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)))
            (Real.rpow_nonneg hv.1.le _)
        _ = D * (Real.rpow (T v) (-q / 2) + Real.rpow |d v| a *
            (Real.rpow (T v) (-q / 2) * Real.rpow (T v) (-a / 2))) := by rw [hratio]; ring
        _ = _ := by rw [hcombine]
    · dsimp only [selected, F0, Fa]
      rw [if_neg hv, if_neg hv, if_neg hv]
      simp
  have hTm : Measurable T := Shao.measurable_energy
  have hdm : Measurable d := Shao.measurable_prefixSum n
  have hselm : Measurable selected := by
    apply Measurable.ite
      ((measurableSet_lt measurable_const hTm).inter (measurableSet_le measurable_const hTm))
    · simp only [Real.rpow_eq_pow]
      exact (hTm.pow_const _).mul
        ((measurable_const.add ((continuous_abs.measurable.comp hdm).div hTm.sqrt)).pow_const a)
    · exact measurable_const
  have hselnn (v : Shao.Path n) : 0 ≤ selected v := by
    dsimp [selected]
    split_ifs with hv
    · exact mul_nonneg (Real.rpow_nonneg hv.1.le _)
        (Real.rpow_nonneg (by positivity) _)
    · exact le_rfl
  have hseli : Integrable selected P := by
    apply hsum.mono' hselm.aestronglyMeasurable
    exact ae_of_all _ fun v => by rw [Real.norm_eq_abs, abs_of_nonneg (hselnn v)]; exact hpoint v
  refine ⟨hseli, h0.2.1, ?_⟩
  calc
    _ ≤ ∫ v, D * (F0 v + Fa v) ∂P := integral_mono hseli hsum hpoint
    _ = D * ((∫ v, F0 v ∂P) + ∫ v, Fa v ∂P) := by
      rw [integral_const_mul, integral_add h0.1 hFa.1]
    _ ≤ D * (C0 * (∫ s : ℝ in Set.Ioo 0 (1 / b), kernel s) +
        Ca * ∫ s : ℝ in Set.Ioo 0 (1 / b), kernel s) :=
      mul_le_mul_of_nonneg_left (add_le_add h0.2.2 hFa.2.2) hD.le
    _ = _ := by ring

end Shao.C2.AuxiliaryUnmarkedRealCutoffInverse
