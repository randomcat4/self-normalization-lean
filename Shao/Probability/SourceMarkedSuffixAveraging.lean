/- Genuine marked-coordinate averaging for actual iid suffixes. -/
import Shao.Probability.FiniteIID
import Shao.Probability.SpitzerFinite
import Shao.Probability.TruncationIntegrals
import Shao.C1.PermutationEnergyEnvelope
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

noncomputable section

namespace Shao.Probability.SourceMarkedSuffixAveraging

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical ENNReal

/-- 求和按标签位置进行，重复数值不合并。 -/
def cubicMass {t : ℕ} (a : Shao.Path t) : ℝ :=
  ∑ i : Fin t, |a i| ^ 3

/-- 在零能量分支先置零；没有使用全局三阶矩。 -/
def normalizedCubicMark {t : ℕ} (a : Shao.Path t) (j : Fin t) : ℝ :=
  if 0 < Shao.energy a then
    |a j| ^ 3 / (Shao.energy a * Real.sqrt (Shao.energy a))
  else 0

def suffixBeta {t : ℕ} (a : Shao.Path t) : ℝ :=
  if 0 < Shao.energy a then
    cubicMass a / (Shao.energy a * Real.sqrt (Shao.energy a))
  else 0

/-- D 在选中正能量上逐字等于 1+|d|/sqrt T；零能量总化为 1。 -/
def suffixD {t : ℕ} (a : Shao.Path t) : ℝ :=
  if 0 < Shao.energy a then
    1 + |Shao.prefixSum a t| / Real.sqrt (Shao.energy a)
  else 1

def lateMarkedWeight {t : ℕ} (H V R : ℝ) (a : Shao.Path t) (j : Fin t) : ℝ :=
  if H ≤ Shao.energy a then
    normalizedCubicMark a j * suffixD a ^ 5 * (Shao.energy a / V + R ^ 2)
  else 0

def lateAveragedWeight {t : ℕ} (H V R : ℝ) (a : Shao.Path t) : ℝ :=
  if H ≤ Shao.energy a then
    (suffixBeta a / (t : ℝ)) * suffixD a ^ 5 * (Shao.energy a / V + R ^ 2)
  else 0

/-- 非负一般机制所消费的实际对称因子，正能量守卫先于除法。 -/
def lateSymmetricFactor {t : ℕ} (H V R : ℝ) (a : Shao.Path t) : ℝ≥0∞ :=
  if 0 < Shao.energy a ∧ H ≤ Shao.energy a then
    ENNReal.ofReal
      (suffixD a ^ 5 * (Shao.energy a / V + R ^ 2) /
        (Shao.energy a * Real.sqrt (Shao.energy a)))
  else 0

/-- 任意实际交换不变测度；允许无穷积分，未要求目标可积。 -/
theorem exchangeable_marked_lintegral_eq_average
    {t : ℕ} (ht : 0 < t) (P : Measure (Shao.Path t))
    (hPerm : ∀ σ : Equiv.Perm (Fin t),
      Measure.map (fun a : Shao.Path t => Spitzer.reorder a σ) P = P)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g)
    (W : Shao.Path t → ℝ≥0∞) (hW : Measurable W)
    (hSymm : ∀ (a : Shao.Path t) (σ : Equiv.Perm (Fin t)),
      W (Spitzer.reorder a σ) = W a)
    (j : Fin t) :
    (∫⁻ a : Shao.Path t, g (a j) * W a ∂P) =
      ∫⁻ a : Shao.Path t,
        ((∑ i : Fin t, g (a i)) / (t : ℝ≥0∞)) * W a ∂P := by
  classical
  have hm (i : Fin t) : Measurable (fun a : Shao.Path t => g (a i) * W a) :=
    (hg.comp (measurable_pi_apply i)).mul hW
  have hi (i : Fin t) :
      (∫⁻ a : Shao.Path t, g (a j) * W a ∂P) =
        ∫⁻ a : Shao.Path t, g (a i) * W a ∂P := by
    let σ : Equiv.Perm (Fin t) := Equiv.swap j i
    have hσ : Measurable (fun a : Shao.Path t => Spitzer.reorder a σ) :=
      Measurable.of_eval (fun k => measurable_pi_apply (σ k))
    calc
      _ = ∫⁻ a : Shao.Path t, g (a j) * W a
          ∂Measure.map (fun a : Shao.Path t => Spitzer.reorder a σ) P := by rw [hPerm σ]
      _ = ∫⁻ a : Shao.Path t,
          g ((Spitzer.reorder a σ) j) * W (Spitzer.reorder a σ) ∂P :=
        lintegral_map (hm j) hσ
      _ = _ := by simp only [hSymm, Spitzer.reorder, σ, Equiv.swap_apply_left]
  have hfun : (fun a : Shao.Path t =>
      ((∑ i : Fin t, g (a i)) / (t : ℝ≥0∞)) * W a) =
      (fun a : Shao.Path t => (t : ℝ≥0∞)⁻¹ * ∑ i : Fin t, g (a i) * W a) := by
    funext a
    simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ac_rfl
  rw [hfun, lintegral_const_mul _ (Finset.measurable_sum _ (fun i _ => hm i)),
    lintegral_finsetSum _ (fun i _ => hm i)]
  simp_rw [← hi]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (t : ℝ≥0∞) ≠ 0 := by exact_mod_cast ht.ne'
  rw [← mul_assoc, ENNReal.inv_mul_cancel hn (by simp), one_mul]

theorem iid_product_reorder_map
    {t : ℕ} (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (σ : Equiv.Perm (Fin t)) :
    Measure.map (fun a : Shao.Path t => Spitzer.reorder a σ)
      (Measure.pi (fun _ : Fin t => nu)) =
      Measure.pi (fun _ : Fin t => nu) := by
  convert (measurePreserving_piCongrLeft (fun _ : Fin t => nu) σ.symm).map_eq using 1
  congr 1
  funext a i
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply, Spitzer.reorder]

theorem iid_marked_lintegral_eq_average
    {t : ℕ} (ht : 0 < t) {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (nu : Measure ℝ)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (X : Fin t → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X mu)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) mu nu)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g)
    (W : Shao.Path t → ℝ≥0∞) (hW : Measurable W)
    (hSymm : ∀ (a : Shao.Path t) (σ : Equiv.Perm (Fin t)),
      W (Spitzer.reorder a σ) = W a)
    (j : Fin t) :
    (∫⁻ ω : Ω, g (X j ω) * W (samplePath X ω) ∂mu) =
      ∫⁻ ω : Ω,
        ((∑ i : Fin t, g (X i ω)) / (t : ℝ≥0∞)) * W (samplePath X ω) ∂mu := by
  have hpath := iid_samplePath_identDistrib hX hIndep hLaw
  have hleft : Measurable (fun a : Shao.Path t => g (a j) * W a) :=
    (hg.comp (measurable_pi_apply j)).mul hW
  have hright : Measurable (fun a : Shao.Path t =>
      ((∑ i : Fin t, g (a i)) / (t : ℝ≥0∞)) * W a) := by
    exact ((Finset.measurable_sum _ (fun i _ => hg.comp (measurable_pi_apply i))).div_const _).mul hW
  calc
    _ = ∫⁻ a : Shao.Path t, g (a j) * W a ∂Measure.pi (fun _ : Fin t => nu) :=
      (hpath.comp hleft).lintegral_eq
    _ = ∫⁻ a : Shao.Path t, ((∑ i : Fin t, g (a i)) / (t : ℝ≥0∞)) * W a
        ∂Measure.pi (fun _ : Fin t => nu) :=
      exchangeable_marked_lintegral_eq_average ht _ (iid_product_reorder_map nu) g hg W hW hSymm j
    _ = _ := (hpath.comp hright).lintegral_eq.symm

theorem suffix_normalized_geometry {t : ℕ} (a : Shao.Path t) :
    (∀ i : Fin t, (a i) ^ 2 ≤ Shao.energy a) ∧
    (Shao.prefixSum a t) ^ 2 ≤ (t : ℝ) * Shao.energy a ∧
    cubicMass a ≤ Shao.energy a * Real.sqrt (Shao.energy a) ∧
    (∀ i : Fin t, 0 ≤ normalizedCubicMark a i ∧ normalizedCubicMark a i ≤ 1) ∧
    (0 ≤ suffixBeta a ∧ suffixBeta a ≤ 1) ∧
    (1 ≤ suffixD a ∧ suffixD a ≤ 1 + Real.sqrt (t : ℝ)) ∧
    (Shao.energy a = 0 →
      (∀ i : Fin t, a i = 0) ∧ suffixBeta a = 0 ∧ suffixD a = 1) := by
  classical
  have hT0 : 0 ≤ Shao.energy a := Shao.energy_nonneg a
  have hsingle (i : Fin t) : (a i) ^ 2 ≤ Shao.energy a :=
    Finset.single_le_sum (fun k _ => sq_nonneg (a k)) (Finset.mem_univ i)
  have hsum : (Shao.prefixSum a t) ^ 2 ≤ (t : ℝ) * Shao.energy a := by
    by_cases ht : 0 < t
    · have hh := Shao.C1.PermutationEnergyEnvelope.remaining_energy_bounds a
        (Equiv.refl (Fin t)) (⟨0, ht⟩ : Fin t)
      simpa [Shao.C1.PermutationEnergyEnvelope.revealRemainingSum,
        Shao.C1.PermutationEnergyEnvelope.revealRemainingEnergy, Shao.prefixSum_length,
        Shao.energy] using hh.2
    · have ht' : t = 0 := Nat.eq_zero_of_not_pos ht
      subst t
      simp [Shao.prefixSum, Shao.energy]
  have habs (i : Fin t) : |a i| ≤ Real.sqrt (Shao.energy a) := by
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).1
    simpa only [sq_abs, Real.sq_sqrt hT0] using hsingle i
  have hcub : cubicMass a ≤ Shao.energy a * Real.sqrt (Shao.energy a) := by
    calc
      _ ≤ ∑ i : Fin t, (a i) ^ 2 * Real.sqrt (Shao.energy a) := by
        apply Finset.sum_le_sum
        intro i _
        calc
          |a i| ^ 3 = (a i) ^ 2 * |a i| := by rw [← sq_abs (a i)]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (habs i) (sq_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; rfl
  have hmass : 0 ≤ cubicMass a := Finset.sum_nonneg (fun i _ => pow_nonneg (abs_nonneg _) _)
  have hmark (i : Fin t) : 0 ≤ normalizedCubicMark a i ∧ normalizedCubicMark a i ≤ 1 := by
    by_cases hT : 0 < Shao.energy a
    · have hden : 0 < Shao.energy a * Real.sqrt (Shao.energy a) :=
        mul_pos hT (Real.sqrt_pos.2 hT)
      rw [normalizedCubicMark, if_pos hT]
      refine ⟨div_nonneg (pow_nonneg (abs_nonneg _) _) hden.le, (div_le_one hden).2 ?_⟩
      exact (Finset.single_le_sum (fun i _ => pow_nonneg (abs_nonneg (a i)) 3)
        (Finset.mem_univ i)).trans hcub
    · simp [normalizedCubicMark, hT]
  have hbeta : 0 ≤ suffixBeta a ∧ suffixBeta a ≤ 1 := by
    by_cases hT : 0 < Shao.energy a
    · have hden : 0 < Shao.energy a * Real.sqrt (Shao.energy a) :=
        mul_pos hT (Real.sqrt_pos.2 hT)
      rw [suffixBeta, if_pos hT]
      exact ⟨div_nonneg hmass hden.le, (div_le_one hden).2 hcub⟩
    · simp [suffixBeta, hT]
  have hD : 1 ≤ suffixD a ∧ suffixD a ≤ 1 + Real.sqrt (t : ℝ) := by
    by_cases hT : 0 < Shao.energy a
    · have hs : 0 < Real.sqrt (Shao.energy a) := Real.sqrt_pos.2 hT
      have hn : 0 ≤ |Shao.prefixSum a t| / Real.sqrt (Shao.energy a) :=
        div_nonneg (abs_nonneg _) hs.le
      have hh : (|Shao.prefixSum a t| / Real.sqrt (Shao.energy a)) ^ 2 ≤ (t : ℝ) := by
        rw [div_pow, sq_abs, Real.sq_sqrt hT.le]
        exact (div_le_iff₀ hT).2 hsum
      have hh' : |Shao.prefixSum a t| / Real.sqrt (Shao.energy a) ≤ Real.sqrt (t : ℝ) := by
        apply (sq_le_sq₀ hn (Real.sqrt_nonneg _)).1
        simpa only [Real.sq_sqrt (Nat.cast_nonneg t)] using hh
      rw [suffixD, if_pos hT]
      exact ⟨by linarith only [hn], add_le_add le_rfl hh'⟩
    · simp only [suffixD, if_neg hT, le_refl, true_and]
      linarith [Real.sqrt_nonneg (t : ℝ)]
  refine ⟨hsingle, hsum, hcub, hmark, hbeta, hD, ?_⟩
  intro hzero
  exact ⟨(Shao.energy_eq_zero_iff a).1 hzero, by simp [suffixBeta, hzero], by simp [suffixD, hzero]⟩

theorem suffixBeta_eq_sum_marks {t : ℕ} (a : Shao.Path t) :
    suffixBeta a = ∑ i : Fin t, normalizedCubicMark a i := by
  classical
  by_cases hT : 0 < Shao.energy a
  · simp only [suffixBeta, normalizedCubicMark, if_pos hT, cubicMass, Finset.sum_div]
  · simp only [suffixBeta, normalizedCubicMark, if_neg hT, Finset.sum_const_zero]

theorem empty_suffix_conventions (a : Shao.Path 0) (H V R : ℝ) :
    Shao.energy a = 0 ∧ Shao.prefixSum a 0 = 0 ∧ cubicMass a = 0 ∧
    suffixBeta a = 0 ∧ suffixD a = 1 ∧
    lateAveragedWeight H V R a = 0 ∧ lateSymmetricFactor H V R a = 0 := by
  simp [Shao.energy, Shao.prefixSum, cubicMass, suffixBeta, suffixD,
    lateAveragedWeight, lateSymmetricFactor]

theorem late_weights_measurable_and_covariant
    {t : ℕ} (H V R : ℝ) :
    (∀ j : Fin t, Measurable (fun a : Shao.Path t => lateMarkedWeight H V R a j)) ∧
    Measurable (lateAveragedWeight H V R : Shao.Path t → ℝ) ∧
    Measurable (lateSymmetricFactor H V R : Shao.Path t → ℝ≥0∞) ∧
    ∀ (a : Shao.Path t) (σ : Equiv.Perm (Fin t)),
      (∀ j : Fin t,
        lateMarkedWeight H V R (Spitzer.reorder a σ) j =
          lateMarkedWeight H V R a (σ j)) ∧
      lateAveragedWeight H V R (Spitzer.reorder a σ) = lateAveragedWeight H V R a ∧
      lateSymmetricFactor H V R (Spitzer.reorder a σ) = lateSymmetricFactor H V R a := by
  classical
  have he : Measurable (Shao.energy : Shao.Path t → ℝ) := Shao.measurable_energy
  have hd : Measurable (fun a : Shao.Path t => Shao.prefixSum a t) := Shao.measurable_prefixSum t
  have hden : Measurable (fun a : Shao.Path t => Shao.energy a * Real.sqrt (Shao.energy a)) := he.mul he.sqrt
  have hpos : MeasurableSet {a : Shao.Path t | 0 < Shao.energy a} := measurableSet_lt measurable_const he
  have hsel : MeasurableSet {a : Shao.Path t | H ≤ Shao.energy a} := measurableSet_le measurable_const he
  have hc : Measurable (cubicMass : Shao.Path t → ℝ) := by
    unfold cubicMass
    fun_prop
  have hm (j : Fin t) : Measurable (fun a : Shao.Path t => normalizedCubicMark a j) := by
    unfold normalizedCubicMark
    apply Measurable.ite hpos
    · exact ((continuous_abs.measurable.comp
        (measurable_pi_apply j : Measurable (fun a : Shao.Path t => a j))).pow_const 3).div hden
    · exact measurable_const
  have hb : Measurable (suffixBeta : Shao.Path t → ℝ) :=
    Measurable.ite hpos (hc.div hden) measurable_const
  have hD : Measurable (suffixD : Shao.Path t → ℝ) :=
    Measurable.ite hpos (measurable_const.add ((continuous_abs.measurable.comp hd).div he.sqrt)) measurable_const
  have hbr : Measurable (fun a : Shao.Path t => Shao.energy a / V + R ^ 2) :=
    (he.div_const V).add measurable_const
  refine ⟨(fun j => Measurable.ite hsel ((hm j |>.mul (hD.pow_const 5)).mul hbr) measurable_const),
    Measurable.ite hsel (((hb.div_const _).mul (hD.pow_const 5)).mul hbr) measurable_const,
    Measurable.ite (hpos.inter hsel) (((hD.pow_const 5).mul hbr).div hden).ennreal_ofReal measurable_const, ?_⟩
  intro a σ
  have heq : Shao.energy (Spitzer.reorder a σ) = Shao.energy a :=
    Equiv.sum_comp σ (fun i => (a i) ^ 2)
  have hdeq : Shao.prefixSum (Spitzer.reorder a σ) t = Shao.prefixSum a t := by
    simpa only [Shao.prefixSum_length, Spitzer.reorder] using Equiv.sum_comp σ a
  have hceq : cubicMass (Spitzer.reorder a σ) = cubicMass a :=
    Equiv.sum_comp σ (fun i => |a i| ^ 3)
  simp only [lateMarkedWeight, lateAveragedWeight, lateSymmetricFactor, normalizedCubicMark,
    suffixBeta, suffixD, heq, hdeq, hceq, Spitzer.reorder]
  simp

theorem late_weights_source_forms
    {t : ℕ} (H V R : ℝ) (hH : 0 < H) (a : Shao.Path t) (j : Fin t) :
    let T : ℝ := Shao.energy a
    let d : ℝ := Shao.prefixSum a t
    let D : ℝ := 1 + |d| / Real.sqrt T
    let beta : ℝ := if 0 < T then cubicMass a / Real.rpow T (3 / 2 : ℝ) else 0
    lateMarkedWeight H V R a j =
      (if H ≤ T then |a j| ^ 3 / Real.rpow T (3 / 2 : ℝ) * D ^ 5 *
        (T / V + R ^ 2) else 0) ∧
    lateAveragedWeight H V R a =
      (if H ≤ T then (beta / (t : ℝ)) * D ^ 5 * (T / V + R ^ 2) else 0) := by
  dsimp only
  by_cases hsel : H ≤ Shao.energy a
  · have hT : 0 < Shao.energy a := hH.trans_le hsel
    have hp : Real.rpow (Shao.energy a) (3 / 2 : ℝ) =
        Shao.energy a * Real.sqrt (Shao.energy a) := by
      rw [Real.rpow_eq_pow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hT,
        Real.rpow_one, ← Real.sqrt_eq_rpow]
    simp only [lateMarkedWeight, lateAveragedWeight, normalizedCubicMark, suffixBeta,
      suffixD, if_pos hsel, if_pos hT, hp, and_self]
  · simp only [lateMarkedWeight, lateAveragedWeight, if_neg hsel, and_self]

theorem late_weights_pointwise_bound
    {t : ℕ} (H V R : ℝ) (hV : 0 < V) (a : Shao.Path t) :
    (∀ j : Fin t,
      0 ≤ lateMarkedWeight H V R a j ∧
      |lateMarkedWeight H V R a j| ≤
        (1 + Real.sqrt (t : ℝ)) ^ 5 * (Shao.energy a / V + R ^ 2)) ∧
    (0 ≤ lateAveragedWeight H V R a ∧
      |lateAveragedWeight H V R a| ≤
        (1 + Real.sqrt (t : ℝ)) ^ 5 * (Shao.energy a / V + R ^ 2)) := by
  rcases suffix_normalized_geometry a with ⟨_, _, _, hm, hb, hD, _⟩
  have hD0 : 0 ≤ suffixD a := le_trans (by norm_num) hD.1
  have hp : suffixD a ^ 5 ≤ (1 + Real.sqrt (t : ℝ)) ^ 5 :=
    pow_le_pow_left₀ hD0 hD.2 5
  have hbr : 0 ≤ Shao.energy a / V + R ^ 2 :=
    add_nonneg (div_nonneg (Shao.energy_nonneg a) hV.le) (sq_nonneg R)
  have hratio : 0 ≤ suffixBeta a / (t : ℝ) ∧ suffixBeta a / (t : ℝ) ≤ 1 := by
    refine ⟨div_nonneg hb.1 (Nat.cast_nonneg t), ?_⟩
    by_cases ht : t = 0
    · simp only [ht, Nat.cast_zero, div_zero, zero_le_one]
    · have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 ht
      exact (div_le_one (by linarith : (0 : ℝ) < t)).2 (hb.2.trans ht1)
  constructor
  · intro j
    unfold lateMarkedWeight
    split_ifs
    · have hn : 0 ≤ normalizedCubicMark a j * suffixD a ^ 5 * (Shao.energy a / V + R ^ 2) :=
        mul_nonneg (mul_nonneg (hm j).1 (pow_nonneg hD0 5)) hbr
      refine ⟨hn, ?_⟩
      rw [abs_of_nonneg hn]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (mul_le_mul (hm j).2 hp (pow_nonneg hD0 5) (by norm_num)) hbr
    · exact ⟨le_rfl, by simp only [abs_zero]; positivity⟩
  · unfold lateAveragedWeight
    split_ifs
    · have hn : 0 ≤ (suffixBeta a / (t : ℝ)) * suffixD a ^ 5 * (Shao.energy a / V + R ^ 2) :=
        mul_nonneg (mul_nonneg hratio.1 (pow_nonneg hD0 5)) hbr
      refine ⟨hn, ?_⟩
      rw [abs_of_nonneg hn]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (mul_le_mul hratio.2 hp (pow_nonneg hD0 5) (by norm_num)) hbr
    · exact ⟨le_rfl, by simp only [abs_zero]; positivity⟩

theorem identDistrib_energy_integrable_and_integral
    {t : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (nu : Measure ℝ)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (X : Fin t → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) mu nu)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu) :
    Integrable (fun ω : Ω => Shao.energy (samplePath X ω)) mu ∧
    (∫ ω : Ω, Shao.energy (samplePath X ω) ∂mu) =
      (t : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) := by
  have hi (i : Fin t) : Integrable (fun ω : Ω => X i ω ^ 2) mu :=
    ((hLaw i).comp (measurable_id.pow_const 2)).symm.integrable_snd h2
  have he (i : Fin t) : (∫ ω : Ω, X i ω ^ 2 ∂mu) = ∫ z : ℝ, z ^ 2 ∂nu :=
    ((hLaw i).comp (measurable_id.pow_const 2)).integral_eq
  constructor
  · exact integrable_finsetSum Finset.univ (fun i _ => hi i)
  · change (∫ ω : Ω, ∑ i : Fin t, X i ω ^ 2 ∂mu) = _
    rw [integral_finsetSum _ (fun i _ => hi i)]
    simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem identDistrib_late_weights_integrable
    {t : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (nu : Measure ℝ)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (X : Fin t → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) mu nu)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (H V R : ℝ) (hV : 0 < V) :
    (∀ j : Fin t,
      Integrable (fun ω : Ω => lateMarkedWeight H V R (samplePath X ω) j) mu) ∧
    Integrable (fun ω : Ω => lateAveragedWeight H V R (samplePath X ω)) mu := by
  have hE := (identDistrib_energy_integrable_and_integral mu nu X hX hLaw h2).1
  have henv : Integrable (fun ω : Ω =>
      (1 + Real.sqrt (t : ℝ)) ^ 5 * (Shao.energy (samplePath X ω) / V + R ^ 2)) mu :=
    ((hE.div_const V).add (integrable_const (R ^ 2))).const_mul _
  have hm := late_weights_measurable_and_covariant (t := t) H V R
  refine ⟨(fun j => henv.mono' (((hm.1 j).comp (measurable_samplePath hX)).aestronglyMeasurable) ?_),
    henv.mono' ((hm.2.1.comp (measurable_samplePath hX)).aestronglyMeasurable) ?_⟩
  · exact ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs] using
      (late_weights_pointwise_bound H V R hV (samplePath X ω)).1 j |>.2)
  · exact ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs] using
      (late_weights_pointwise_bound H V R hV (samplePath X ω)).2.2)

theorem iid_late_marked_integral_eq_average
    {t : ℕ} (ht : 0 < t) {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (nu : Measure ℝ)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (X : Fin t → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X mu)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) mu nu)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (H V R : ℝ) (hH : 0 < H) (hV : 0 < V) (j : Fin t) :
    (∫ ω : Ω, lateMarkedWeight H V R (samplePath X ω) j ∂mu) =
      ∫ ω : Ω, lateAveragedWeight H V R (samplePath X ω) ∂mu := by
  classical
  have hi := identDistrib_late_weights_integrable mu nu X hX hLaw h2 H V R hV
  have hm := late_weights_measurable_and_covariant (t := t) H V R
  have he (i : Fin t) :
      (∫ ω : Ω, lateMarkedWeight H V R (samplePath X ω) j ∂mu) =
        ∫ ω : Ω, lateMarkedWeight H V R (samplePath X ω) i ∂mu := by
    have hh := (iid_observable_identDistrib_perm hX hIndep hLaw (Equiv.swap j i) (hm.1 j)).integral_eq
    calc
      _ = ∫ ω : Ω, lateMarkedWeight H V R
          (samplePath (fun k => X (Equiv.swap j i k)) ω) j ∂mu := hh
      _ = _ := by
        apply integral_congr_ae
        exact ae_of_all _ fun ω => by
          have hc := (hm.2.2.2 (samplePath X ω) (Equiv.swap j i)).1 j
          change lateMarkedWeight H V R (Spitzer.reorder (samplePath X ω) (Equiv.swap j i)) j = _
          simpa only [Equiv.swap_apply_left] using hc
  have hpoint (a : Shao.Path t) :
      lateAveragedWeight H V R a = (∑ i : Fin t, lateMarkedWeight H V R a i) / (t : ℝ) := by
    unfold lateAveragedWeight lateMarkedWeight
    by_cases hs : H ≤ Shao.energy a
    · simp only [if_pos hs, suffixBeta_eq_sum_marks, div_eq_mul_inv, Finset.sum_mul,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    · simp [hs]
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  calc
    _ = ((t : ℝ) * (∫ ω : Ω, lateMarkedWeight H V R (samplePath X ω) j ∂mu)) / (t : ℝ) := by
      field_simp
    _ = (∑ i : Fin t, ∫ ω : Ω, lateMarkedWeight H V R (samplePath X ω) i ∂mu) / (t : ℝ) := by
      simp_rw [← he]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (∫ ω : Ω, ∑ i : Fin t, lateMarkedWeight H V R (samplePath X ω) i ∂mu) / (t : ℝ) := by
      rw [integral_finsetSum _ (fun i _ => hi.1 i)]
    _ = _ := by
      rw [← integral_div]
      exact integral_congr_ae (ae_of_all _ fun ω => (hpoint (samplePath X ω)).symm)

theorem iid_product_late_marked_integral_eq_average
    {t : ℕ} (ht : 0 < t) (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (H V R : ℝ) (hH : 0 < H) (hV : 0 < V) (j : Fin t) :
    Integrable (fun a : Shao.Path t => lateMarkedWeight H V R a j)
      (Measure.pi (fun _ : Fin t => nu)) ∧
    Integrable (lateAveragedWeight H V R : Shao.Path t → ℝ)
      (Measure.pi (fun _ : Fin t => nu)) ∧
    (∫ a : Shao.Path t, lateMarkedWeight H V R a j
      ∂Measure.pi (fun _ : Fin t => nu)) =
      ∫ a : Shao.Path t, lateAveragedWeight H V R a
        ∂Measure.pi (fun _ : Fin t => nu) := by
  let P : Measure (Shao.Path t) := Measure.pi (fun _ : Fin t => nu)
  let X : Fin t → Shao.Path t → ℝ := fun i a => a i
  have hX (i : Fin t) : Measurable (X i) := measurable_pi_apply i
  have hLaw (i : Fin t) : IdentDistrib (X i) (id : ℝ → ℝ) P nu := by
    refine ⟨(hX i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa only [Measure.map_id] using (measurePreserving_eval (μ := fun _ : Fin t => nu) i).map_eq
  have hIndep : iIndepFun X P := by
    exact iIndepFun_pi (X := fun _ : Fin t => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable)
  have hi := identDistrib_late_weights_integrable P nu X hX hLaw h2 H V R hV
  exact ⟨hi.1 j, hi.2, iid_late_marked_integral_eq_average ht P nu X hX hIndep hLaw h2 H V R hH hV j⟩

theorem raw_prefix_budget_data
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (r : ℕ) (hr : 0 < r)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hsecond : 0 < ∫ z : ℝ, z ^ 2 ∂nu) :
    let sigma : ℝ := Real.sqrt (∫ z : ℝ, z ^ 2 ∂nu)
    let V : ℝ := (r : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu)
    let scale : ℝ := Real.sqrt V
    let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / scale) nu
    let R : ℝ := Shao.truncationBudget normalizedLaw r 0
    0 < sigma ∧ 0 < V ∧ V = (r : ℝ) * sigma ^ 2 ∧
    scale = sigma * Real.sqrt (r : ℝ) ∧
    Integrable (fun z : ℝ => Shao.truncationF (z / (sigma * Real.sqrt (r : ℝ)))) nu ∧
    0 ≤ R ∧ R ≤ 1 ∧
    R = (r : ℝ) *
      (∫ z : ℝ, Shao.truncationF (z / (sigma * Real.sqrt (r : ℝ))) ∂nu) := by
  intro sigma V scale normalizedLaw R
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hsig : 0 < sigma := Real.sqrt_pos.2 hsecond
  have hV : 0 < V := mul_pos hr0 hsecond
  have hs : 0 < scale := Real.sqrt_pos.2 hV
  have hs2 : scale ^ 2 = V := Real.sq_sqrt hV.le
  have hVeq : V = (r : ℝ) * sigma ^ 2 := by rw [Real.sq_sqrt hsecond.le]
  have hscale : scale = sigma * Real.sqrt (r : ℝ) := by
    dsimp only [scale, V, sigma]
    rw [Real.sqrt_mul (Nat.cast_nonneg r), mul_comm]
  have hFi : Integrable (fun z : ℝ => Shao.truncationF (z / scale)) nu := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using
      Shao.integrable_truncationF_mul nu h2 (1 / scale)
  have hReq : R = (r : ℝ) * (∫ z : ℝ, Shao.truncationF (z / scale) ∂nu) := by
    dsimp only [R, Shao.truncationBudget, normalizedLaw]
    simp only [add_zero, one_mul]
    rw [integral_map (μ := nu) (φ := fun z : ℝ => z / scale) (f := Shao.truncationF)
      (measurable_id.div_const scale).aemeasurable Shao.continuous_truncationF.aestronglyMeasurable]
  have hR0 : 0 ≤ R := by
    rw [hReq]
    exact mul_nonneg hr0.le (integral_nonneg fun z => Shao.truncationF_nonneg _)
  have hsq : Integrable (fun z : ℝ => (z / scale) ^ 2) nu := by
    simpa only [div_pow] using h2.div_const (scale ^ 2)
  have hR1 : R ≤ 1 := by
    calc
      R = (r : ℝ) * (∫ z : ℝ, Shao.truncationF (z / scale) ∂nu) := hReq
      _ ≤ (r : ℝ) * (∫ z : ℝ, (z / scale) ^ 2 ∂nu) :=
        mul_le_mul_of_nonneg_left (integral_mono hFi hsq (fun z => Shao.truncationF_le_sq _)) hr0.le
      _ = (r : ℝ) * ((∫ z : ℝ, z ^ 2 ∂nu) / scale ^ 2) := by simp_rw [div_pow]; rw [integral_div]
      _ = 1 := by rw [hs2]; dsimp only [V]; field_simp
  refine ⟨hsig, hV, hVeq, hscale, ?_, hR0, hR1, ?_⟩
  · simpa only [hscale] using hFi
  · simpa only [hscale] using hReq

theorem iid_actual_suffix_marked_averaging
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (nu : Measure ℝ)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X mu)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) mu nu)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hsecond : 0 < ∫ z : ℝ, z ^ 2 ∂nu)
    (r : ℕ) (hr : 0 < r) (hrn : r < n) (H : ℝ) (hH : 0 < H) :
    let V : ℝ := (r : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu)
    let scale : ℝ := Real.sqrt V
    let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / scale) nu
    let R : ℝ := Shao.truncationBudget normalizedLaw r 0
    let suffix : Ω → Shao.Path (n - r) := fun ω =>
      Spitzer.tail (samplePath X ω) r (Nat.le_of_lt hrn)
    let j : Fin (n - r) := ⟨0, Nat.sub_pos_of_lt hrn⟩
    Integrable (fun ω : Ω => lateMarkedWeight H V R (suffix ω) j) mu ∧
    Integrable (fun ω : Ω => lateAveragedWeight H V R (suffix ω)) mu ∧
    (∫ ω : Ω, lateMarkedWeight H V R (suffix ω) j ∂mu) =
      ∫ ω : Ω, lateAveragedWeight H V R (suffix ω) ∂mu := by
  intro V scale normalizedLaw R suffix j
  let f : Fin (n - r) → Fin n := fun i => ⟨r + i.val, by omega⟩
  have hf : Function.Injective f := by
    intro i k hik
    apply Fin.ext
    have hh := congrArg Fin.val hik
    dsimp only [f] at hh
    omega
  let Y : Fin (n - r) → Ω → ℝ := fun i => X (f i)
  have hY (i : Fin (n - r)) : Measurable (Y i) := hX (f i)
  have hYi : iIndepFun Y mu := hIndep.precomp hf
  have hYlaw (i : Fin (n - r)) : IdentDistrib (Y i) (id : ℝ → ℝ) mu nu := hLaw (f i)
  have hV : 0 < V := mul_pos (by exact_mod_cast hr) hsecond
  have hi := identDistrib_late_weights_integrable mu nu Y hY hYlaw h2 H V R hV
  exact ⟨hi.1 j, hi.2,
    iid_late_marked_integral_eq_average (Nat.sub_pos_of_lt hrn) mu nu Y hY hYi hYlaw h2 H V R hH hV j⟩

end Shao.Probability.SourceMarkedSuffixAveraging
