import Shao.C2.AuxiliaryRealMarkedFiniteCutoffExtendedBudget
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace Shao.C2.AuxiliaryRealMarkedCutoffExtendedBudget
open MeasureTheory ProbabilityTheory

theorem auxiliary_actual_real_marked_cutoff_extended_budget :
    let c : ℝ := (1 - Real.exp (-2)) / 8
    ∀ a q : ℝ, 0 ≤ a → 0 < q → ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu],
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 → (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        ∀ (m : ℕ) (b : ℝ), 0 < b →
          let P : Measure (Shao.Path (m + 1)) := Measure.pi (fun _ : Fin (m + 1) => nu)
          let T : Shao.Path (m + 1) → ℝ := Shao.energy
          let d : Shao.Path (m + 1) → ℝ := fun v => Shao.prefixSum v (m + 1)
          let M : Shao.Path (m + 1) → ℝ := fun v => |v 0| ^ 3
          let a3 : ℝ → ℝ := fun u => ∫ z : ℝ, |z| ^ 3 * Real.exp (-u * z ^ 2) ∂nu
          let retained : ℝ := ∫ z : ℝ, if z ^ 2 ≤ b then z ^ 2 else 0 ∂nu
          let gamma : ℝ := if (1 / 2 : ℝ) ≤ retained then -c else 1
          let selected : Shao.Path (m + 1) → ℝ := fun v =>
            if 0 < T v ∧ b ≤ T v then
              M v * Real.rpow (T v) (-q / 2) *
                Real.rpow (1 + |d v| / Real.sqrt (T v)) a else 0
          let kernel : ℝ → ℝ := fun s =>
            Real.rpow s (q / 2 - 1) * a3 (s / 2) *
              Real.exp (gamma * s * (m : ℝ))
          (∫⁻ v, ENNReal.ofReal (selected v) ∂P) ≤
            ENNReal.ofReal C *
              ∫⁻ s : ℝ in Set.Ioo 0 (1 / b), ENNReal.ofReal (kernel s) := by
  intro c a q ha hq
  obtain ⟨C0, hC0, hFinite⟩ :=
    Shao.C2.AuxiliaryRealMarkedFiniteCutoffExtendedBudget.auxiliary_actual_real_marked_finite_cutoff_extended_budget
      a q ha hq
  refine ⟨C0 * Real.exp 1, mul_pos hC0 (Real.exp_pos _), ?_⟩
  intro nu hnu h2 hmean hnorm m b hb P T d M a3 retained gamma selected kernel
  letI : IsProbabilityMeasure nu := hnu
  let S : Set ℝ := Set.Ioo 0 (1 / b)
  let H : ℕ → ℝ := fun n => b + (m : ℝ) + (n : ℝ) + 1
  let F : ℕ → Shao.Path (m + 1) → ℝ := fun n v =>
    if 0 < T v ∧ b ≤ T v ∧ T v < H n then
      M v * Real.rpow (T v) (-q / 2) *
        Real.rpow (1 + |d v| / Real.sqrt (T v)) a else 0
  let G : ℕ → Shao.Path (m + 1) → ENNReal := fun n v => ENNReal.ofReal (F n v)
  let kernelH : ℕ → ℝ → ℝ := fun n s =>
    Real.rpow s (q / 2 - 1) * a3 (s / 2) *
      Real.exp (gamma * (s + 1 / H n) * (m : ℝ))
  have hmnn : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hHb (n : ℕ) : b ≤ H n := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    dsimp [H]
    linarith
  have hHpos (n : ℕ) : 0 < H n := lt_of_lt_of_le hb (hHb n)
  have hHm (n : ℕ) : (m : ℝ) ≤ H n := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    dsimp [H]
    linarith
  have hHmono : Monotone H := by
    intro i j hij
    have hcij : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    dsimp [H]
    linarith
  have hc : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num))) (by norm_num)
  have hgamma : gamma ≤ 1 := by
    dsimp only [gamma]
    split_ifs <;> linarith
  have hAnn (u : ℝ) : 0 ≤ a3 u :=
    integral_nonneg fun z => mul_nonneg (pow_nonneg (abs_nonneg _) 3) (Real.exp_pos _).le
  have hKernelBound (n : ℕ) :
      kernelH n ≤ᵐ[volume.restrict S] fun s => Real.exp 1 * kernel s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hratio0 : 0 ≤ (m : ℝ) / H n := div_nonneg hmnn (hHpos n).le
    have hratio1 : (m : ℝ) / H n ≤ 1 := (div_le_one (hHpos n)).2 (hHm n)
    have hgamratio : gamma * ((m : ℝ) / H n) ≤ 1 := by
      calc
        _ ≤ 1 * ((m : ℝ) / H n) := mul_le_mul_of_nonneg_right hgamma hratio0
        _ ≤ 1 := by simpa using hratio1
    have harg : gamma * (s + 1 / H n) * (m : ℝ) ≤ 1 + gamma * s * (m : ℝ) := by
      calc
        _ = gamma * s * (m : ℝ) + gamma * ((m : ℝ) / H n) := by ring
        _ ≤ gamma * s * (m : ℝ) + 1 := add_le_add le_rfl hgamratio
        _ = _ := by ring
    dsimp only [kernelH, kernel]
    calc
      _ ≤ (Real.rpow s (q / 2 - 1) * a3 (s / 2)) *
          Real.exp (1 + gamma * s * (m : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg)
          (mul_nonneg (Real.rpow_nonneg hs.1.le _) (hAnn _))
      _ = _ := by rw [Real.exp_add]; ring
  have hKernelL (n : ℕ) :
      (∫⁻ s : ℝ in S, ENNReal.ofReal (kernelH n s)) ≤
        ENNReal.ofReal (Real.exp 1) * ∫⁻ s : ℝ in S, ENNReal.ofReal (kernel s) := by
    calc
      _ ≤ ∫⁻ s : ℝ in S, ENNReal.ofReal (Real.exp 1 * kernel s) :=
        lintegral_mono_ae ((hKernelBound n).mono fun _ h => ENNReal.ofReal_le_ofReal h)
      _ = _ := by
        simp_rw [ENNReal.ofReal_mul (Real.exp_pos 1).le]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hbound (n : ℕ) : (∫⁻ v, G n v ∂P) ≤
      ENNReal.ofReal (C0 * Real.exp 1) *
        ∫⁻ s : ℝ in S, ENNReal.ofReal (kernel s) := by
    have hcut := hFinite nu h2 hmean hnorm m b (H n) hb (hHb n)
    calc
      _ ≤ ENNReal.ofReal C0 * ∫⁻ s : ℝ in S, ENNReal.ofReal (kernelH n s) := hcut.2
      _ ≤ ENNReal.ofReal C0 *
          (ENNReal.ofReal (Real.exp 1) * ∫⁻ s : ℝ in S, ENNReal.ofReal (kernel s)) :=
        mul_le_mul_of_nonneg_left (hKernelL n) (by positivity)
      _ = _ := by rw [ENNReal.ofReal_mul hC0.le, mul_assoc]
  have hTm : Measurable T := Shao.measurable_energy
  have hdm : Measurable d := Shao.measurable_prefixSum (m + 1)
  have hCoord : Continuous (fun v : Shao.Path (m + 1) => v 0) := continuous_apply 0
  have hMm : Measurable M := (hCoord.abs.pow 3).measurable
  have hFm (n : ℕ) : Measurable (F n) := by
    apply Measurable.ite
      ((measurableSet_lt measurable_const hTm).inter
        ((measurableSet_le measurable_const hTm).inter
          (measurableSet_lt hTm measurable_const)))
    · simp only [Real.rpow_eq_pow]
      exact (hMm.mul (hTm.pow_const _)).mul
        ((measurable_const.add ((continuous_abs.measurable.comp hdm).div hTm.sqrt)).pow_const a)
    · exact measurable_const
  have hGm (n : ℕ) : Measurable (G n) := (hFm n).ennreal_ofReal
  have hGmono : Monotone G := by
    intro i j hij v
    by_cases hi : 0 < T v ∧ b ≤ T v ∧ T v < H i
    · have hj : 0 < T v ∧ b ≤ T v ∧ T v < H j :=
        ⟨hi.1, hi.2.1, lt_of_lt_of_le hi.2.2 (hHmono hij)⟩
      dsimp only [G, F]
      rw [if_pos hi, if_pos hj]
    · dsimp only [G, F]
      rw [if_neg hi, ENNReal.ofReal_zero]
      exact zero_le
  have hSup (v : Shao.Path (m + 1)) : (⨆ n, G n v) = ENNReal.ofReal (selected v) := by
    apply le_antisymm
    · apply iSup_le
      intro n
      by_cases hn : 0 < T v ∧ b ≤ T v ∧ T v < H n
      · have hv : 0 < T v ∧ b ≤ T v := ⟨hn.1, hn.2.1⟩
        dsimp only [G, F, selected]
        rw [if_pos hn, if_pos hv]
      · dsimp only [G, F]
        rw [if_neg hn, ENNReal.ofReal_zero]
        exact zero_le
    · by_cases hv : 0 < T v ∧ b ≤ T v
      · obtain ⟨n, hn⟩ := exists_nat_gt (T v)
        have hTH : T v < H n := by
          dsimp [H]
          linarith
        have heq : G n v = ENNReal.ofReal (selected v) := by
          dsimp only [G, F, selected]
          rw [if_pos ⟨hv.1, hv.2, hTH⟩, if_pos hv]
        rw [← heq]
        exact le_iSup (fun n => G n v) n
      · dsimp only [selected]
        rw [if_neg hv, ENNReal.ofReal_zero]
        exact zero_le
  calc
    (∫⁻ v, ENNReal.ofReal (selected v) ∂P) = ∫⁻ v, ⨆ n, G n v ∂P :=
      lintegral_congr_ae (ae_of_all _ fun v => (hSup v).symm)
    _ = ⨆ n, ∫⁻ v, G n v ∂P := lintegral_iSup hGm hGmono
    _ ≤ _ := iSup_le hbound

end Shao.C2.AuxiliaryRealMarkedCutoffExtendedBudget
