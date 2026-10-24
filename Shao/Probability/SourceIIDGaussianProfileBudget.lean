/- Actual iid Gaussian wall-profile payment: complete frozen Gaussian-envelope consumers. -/
import Shao.Probability.SourceTrueWallProfile
import Shao.Probability.SourceMarkedSuffixAveraging
import Shao.Probability.SourceSuffixMomentBudgets
import Shao.Probability.FiniteIID
import Shao.Probability.SpitzerFinite
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.Probability.SourceIIDGaussianProfileBudget
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

/-- 只有空后缀才取零；非空时是第一个实际 Fin 标签，重复数值不合并。 -/
def firstValue {t : ℕ} (u : Shao.Path t) : ℝ :=
  if ht : 0 < t then u ⟨0, ht⟩ else 0

/-- 同一个 final-energy wall；closed=false 正是 cn:paid 的严格生存。 -/
def prefixSurvival {r t : ℕ} (x : ℝ) (signs : Finset ℝ) (closed : Bool)
    (v : Shao.Path r) (u : Shao.Path t) : Prop :=
  ∀ s ∈ signs,
    if closed = true then
      Shao.maxWithZero (s • v) ≤ x * Real.sqrt (Shao.energy u + Shao.energy v)
    else
      Shao.maxWithZero (s • v) < x * Real.sqrt (Shao.energy u + Shao.energy v)

/-- 原文 M_s=|b|+(s*d)_+；零能量分支先置零再除法。 -/
def gaussianProfiles {r t : ℕ} (x : ℝ) (signs : Finset ℝ)
    (v : Shao.Path r) (u : Shao.Path t) : ℝ :=
  if 0 < Shao.energy u then
    ∑ s ∈ signs, Real.exp
      (-((max (x * Real.sqrt (Shao.energy u + Shao.energy v) -
        s * Shao.prefixSum v r -
        (|firstValue u| + max (s * Shao.prefixSum u t) 0)) 0) ^ 2) / Shao.energy u)
  else 0

def fixedGaussianWeight {r t : ℕ} (H x : ℝ) (signs : Finset ℝ) (closed : Bool)
    (v : Shao.Path r) (u : Shao.Path t) : ℝ :=
  if 0 < Shao.energy u ∧ H ≤ Shao.energy u ∧ prefixSurvival x signs closed v u then
    |firstValue u| ^ 3 / (Shao.energy u * Real.sqrt (Shao.energy u)) *
      SourceMarkedSuffixAveraging.suffixD u ^ 3 * gaussianProfiles x signs v u
  else 0

/-- 真实原样本的 head/tail，未排列、重抽或更换条件律。 -/
def rankGaussianWeight {n : ℕ} (H x : ℝ) (signs : Finset ℝ) (closed : Bool)
    (a : Shao.Path n) (r : Fin n) : ℝ :=
  fixedGaussianWeight H x signs closed
    (Spitzer.head a r.val (Nat.le_of_lt r.is_lt))
    (Spitzer.tail a r.val (Nat.le_of_lt r.is_lt))

/-- 所有原文状态/墙/mark/Pi 逐字识别；不对任何 remainder 作假设。 -/
theorem gaussian_weight_source_state
    {n : ℕ} (a : Shao.Path n) (r : Fin n) (H x : ℝ)
    (signs : Finset ℝ) (closed : Bool) :
    let v : Shao.Path r.val := Spitzer.head a r.val (Nat.le_of_lt r.is_lt)
    let u : Shao.Path (n - r.val) := Spitzer.tail a r.val (Nat.le_of_lt r.is_lt)
    let T : ℝ := Shao.energy a - Shao.prefixSquares a r.val
    let d : ℝ := Shao.prefixSum a n - Shao.prefixSum a r.val
    let wall : ℝ := x * Real.sqrt (Shao.energy a)
    let D : ℝ := 1 + |d| / Real.sqrt T
    let q : ℝ := |a r| / Real.sqrt T
    let A : Prop := ∀ s ∈ signs,
      if closed = true then Shao.maxWithZero (s • v) ≤ wall
      else Shao.maxWithZero (s • v) < wall
    let Pi : ℝ := if 0 < T then ∑ s ∈ signs, Real.exp
      (-((max (wall - s * Shao.prefixSum a r.val - (|a r| + max (s * d) 0)) 0) ^ 2) / T)
      else 0
    Shao.energy u = T ∧ Shao.prefixSum u (n - r.val) = d ∧
    Shao.energy u + Shao.energy v = Shao.energy a ∧ firstValue u = a r ∧
    rankGaussianWeight H x signs closed a r =
      (if 0 < T ∧ H ≤ T ∧ A then q ^ 3 * D ^ 3 * Pi else 0) := by
  classical
  intro v u T d wall D q A Pi
  have hsplit (g : ℝ → ℝ) :
      (∑ i : Fin n, g (a i)) =
        (∑ i : Fin r.val, g (v i)) + (∑ i : Fin (n - r.val), g (u i)) := by
    let e : Fin r.val ⊕ Fin (n - r.val) ≃ Fin n :=
      finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le (Nat.le_of_lt r.is_lt)))
    have hh := e.sum_comp (fun i : Fin n => g (a i))
    rw [Fintype.sum_sum_type] at hh
    exact hh.symm
  have hvsum : Shao.prefixSum v r.val = Shao.prefixSum a r.val :=
    Spitzer.head_prefixSum a r.val (Nat.le_of_lt r.is_lt) r.val le_rfl
  have hvenergy : Shao.energy v = Shao.prefixSquares a r.val := by
    have hh := Spitzer.head_prefixSum (fun i : Fin n => (a i) ^ 2)
      r.val (Nat.le_of_lt r.is_lt) r.val le_rfl
    rw [Shao.prefixSum_length] at hh
    simpa only [Shao.energy, v, Spitzer.head, Shao.prefixSum, Shao.prefixSquares] using hh
  have hwhole : Shao.energy a = Shao.energy v + Shao.energy u := hsplit (fun z => z ^ 2)
  have hT : Shao.energy u = T := by dsimp only [T]; linarith only [hwhole, hvenergy]
  have hd : Shao.prefixSum u (n - r.val) = d := by
    have hh := hsplit (fun z => z)
    rw [← Shao.prefixSum_length a, ← Shao.prefixSum_length v, ← Shao.prefixSum_length u] at hh
    dsimp only [d]
    linarith only [hh, hvsum]
  have hwhole' : Shao.energy u + Shao.energy v = Shao.energy a := by linarith only [hwhole]
  have ht : 0 < n - r.val := Nat.sub_pos_of_lt r.is_lt
  have hb : firstValue u = a r := by
    simp only [firstValue, dif_pos ht, u, Spitzer.tail]
    congr 1
  have hA : prefixSurvival x signs closed v u ↔ A := by
    dsimp only [prefixSurvival, A, wall]
    rw [hwhole']
  have hPi : gaussianProfiles x signs v u = Pi := by
    dsimp only [gaussianProfiles, Pi, wall]
    rw [hwhole', hT, hd, hb, hvsum]
  refine ⟨hT, hd, hwhole', hb, ?_⟩
  change fixedGaussianWeight H x signs closed v u = _
  unfold fixedGaussianWeight
  rw [hT, hb, hPi, hA]
  by_cases hpos : 0 < T
  · have hDu : SourceMarkedSuffixAveraging.suffixD u = D := by
      unfold SourceMarkedSuffixAveraging.suffixD
      rw [hT, if_pos hpos, hd]
    have hden : (Real.sqrt T) ^ 3 = T * Real.sqrt T := by
      calc
        _ = (Real.sqrt T) ^ 2 * Real.sqrt T := by ring
        _ = _ := by rw [Real.sq_sqrt hpos.le]
    have hq : |a r| ^ 3 / (T * Real.sqrt T) = q ^ 3 := by
      dsimp only [q]
      rw [div_pow, hden]
    rw [hDu, hq]
    split_ifs <;> rfl
  · simp only [hpos, false_and, ite_false]

theorem fixed_gaussian_weight_measurable_bound
    (r t : ℕ) (H x : ℝ) (signs : Finset ℝ) (closed : Bool) :
    Measurable (fun p : Shao.Path r × Shao.Path t =>
      fixedGaussianWeight H x signs closed p.1 p.2) ∧
    (∀ (v : Shao.Path r) (u : Shao.Path t),
      0 ≤ fixedGaussianWeight H x signs closed v u ∧
      |fixedGaussianWeight H x signs closed v u| ≤
        (signs.card : ℝ) * (1 + Real.sqrt (t : ℝ)) ^ 3) ∧
    (∀ (v : Shao.Path r) (u : Shao.Path t), Shao.energy u = 0 →
      gaussianProfiles x signs v u = 0 ∧ fixedGaussianWeight H x signs closed v u = 0) := by
  classical
  have he : Measurable (fun p : Shao.Path r × Shao.Path t => Shao.energy p.2) :=
    Shao.measurable_energy.comp measurable_snd
  have hev : Measurable (fun p : Shao.Path r × Shao.Path t => Shao.energy p.1) :=
    Shao.measurable_energy.comp measurable_fst
  have hd : Measurable (fun p : Shao.Path r × Shao.Path t => Shao.prefixSum p.2 t) :=
    (Shao.measurable_prefixSum t).comp measurable_snd
  have hdv : Measurable (fun p : Shao.Path r × Shao.Path t => Shao.prefixSum p.1 r) :=
    (Shao.measurable_prefixSum r).comp measurable_fst
  have hb : Measurable (fun p : Shao.Path r × Shao.Path t => firstValue p.2) := by
    by_cases ht : 0 < t
    · simpa only [firstValue, dif_pos ht, Function.comp_def] using
        ((show Measurable (fun u : Shao.Path t => u ⟨0, ht⟩) from
          measurable_pi_apply _).comp measurable_snd)
    · simp only [firstValue, dif_neg ht]
      exact measurable_const
  have hw : Measurable (fun p : Shao.Path r × Shao.Path t =>
      x * Real.sqrt (Shao.energy p.2 + Shao.energy p.1)) :=
    measurable_const.mul (he.add hev).sqrt
  have hpos : MeasurableSet {p : Shao.Path r × Shao.Path t | 0 < Shao.energy p.2} :=
    measurableSet_lt measurable_const he
  have hcut : MeasurableSet {p : Shao.Path r × Shao.Path t | H ≤ Shao.energy p.2} :=
    measurableSet_le measurable_const he
  have hA : MeasurableSet {p : Shao.Path r × Shao.Path t |
      prefixSurvival x signs closed p.1 p.2} := by
    induction signs using Finset.induction_on with
    | empty => simp [prefixSurvival]
    | @insert s signs hs ih =>
      have hmax : Measurable (fun p : Shao.Path r × Shao.Path t =>
          Shao.maxWithZero (s • p.1)) :=
        Shao.measurable_maxWithZero.comp (Measurable.of_eval fun i =>
          measurable_const.mul ((measurable_pi_apply i).comp measurable_fst))
      have hm : MeasurableSet {p : Shao.Path r × Shao.Path t |
          if closed = true then Shao.maxWithZero (s • p.1) ≤
            x * Real.sqrt (Shao.energy p.2 + Shao.energy p.1)
          else Shao.maxWithZero (s • p.1) <
            x * Real.sqrt (Shao.energy p.2 + Shao.energy p.1)} := by
        split_ifs
        · exact measurableSet_le hmax hw
        · exact measurableSet_lt hmax hw
      simpa only [prefixSurvival, Finset.forall_mem_insert, Set.setOf_and] using hm.inter ih
  have hD : Measurable (fun p : Shao.Path r × Shao.Path t =>
      SourceMarkedSuffixAveraging.suffixD p.2) :=
    Measurable.ite hpos
      (measurable_const.add ((continuous_abs.measurable.comp hd).div he.sqrt)) measurable_const
  have hPi : Measurable (fun p : Shao.Path r × Shao.Path t =>
      gaussianProfiles x signs p.1 p.2) := by
    unfold gaussianProfiles
    apply Measurable.ite hpos
    · apply Finset.measurable_sum
      intro s hs
      fun_prop
    · exact measurable_const
  have hmeas : Measurable (fun p : Shao.Path r × Shao.Path t =>
      fixedGaussianWeight H x signs closed p.1 p.2) := by
    unfold fixedGaussianWeight
    apply Measurable.ite (hpos.inter (hcut.inter hA))
    · exact ((((continuous_abs.measurable.comp hb).pow_const 3).div (he.mul he.sqrt)).mul
        (hD.pow_const 3)).mul hPi
    · exact measurable_const
  have hPiBound (v : Shao.Path r) (u : Shao.Path t) :
      0 ≤ gaussianProfiles x signs v u ∧ gaussianProfiles x signs v u ≤ (signs.card : ℝ) := by
    unfold gaussianProfiles
    split_ifs with hT
    · refine ⟨Finset.sum_nonneg (fun s _ => (Real.exp_pos _).le), ?_⟩
      calc
        _ ≤ ∑ s ∈ signs, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro s hs
          exact Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) hT.le)
        _ = _ := by simp
    · simp
  refine ⟨hmeas, ?_, ?_⟩
  · intro v u
    rcases SourceMarkedSuffixAveraging.suffix_normalized_geometry u with ⟨_, _, _, hm, _, hDu, _⟩
    have hD0 : 0 ≤ SourceMarkedSuffixAveraging.suffixD u := (by norm_num : (0 : ℝ) ≤ 1).trans hDu.1
    have hDp : SourceMarkedSuffixAveraging.suffixD u ^ 3 ≤ (1 + Real.sqrt (t : ℝ)) ^ 3 :=
      pow_le_pow_left₀ hD0 hDu.2 3
    have hPiB := hPiBound v u
    unfold fixedGaussianWeight
    split_ifs with hs
    · have hT : 0 < Shao.energy u := hs.1
      have ht : 0 < t := by
        by_contra hh
        have ht0 : t = 0 := Nat.eq_zero_of_not_pos hh
        subst t
        simpa [Shao.energy] using hT
      have hnorm : 0 ≤ |firstValue u| ^ 3 / (Shao.energy u * Real.sqrt (Shao.energy u)) ∧
          |firstValue u| ^ 3 / (Shao.energy u * Real.sqrt (Shao.energy u)) ≤ 1 := by
        simpa only [firstValue, dif_pos ht, SourceMarkedSuffixAveraging.normalizedCubicMark, if_pos hT]
          using hm (⟨0, ht⟩ : Fin t)
      have hn : 0 ≤ |firstValue u| ^ 3 / (Shao.energy u * Real.sqrt (Shao.energy u)) *
          SourceMarkedSuffixAveraging.suffixD u ^ 3 * gaussianProfiles x signs v u :=
        mul_nonneg (mul_nonneg hnorm.1 (pow_nonneg hD0 3)) hPiB.1
      refine ⟨hn, ?_⟩
      rw [abs_of_nonneg hn]
      have hp := mul_le_mul hnorm.2 hDp (pow_nonneg hD0 3) (by norm_num : (0 : ℝ) ≤ 1)
      have hbnd := mul_le_mul (by simpa only [one_mul] using hp) hPiB.2 hPiB.1
        (pow_nonneg (by positivity : (0 : ℝ) ≤ 1 + Real.sqrt (t : ℝ)) 3)
      simpa only [mul_comm] using hbnd
    · exact ⟨le_rfl, by simp only [abs_zero]; positivity⟩
  · intro v u hzero
    simp [gaussianProfiles, fixedGaussianWeight, hzero]

theorem gaussian_weight_early_domination
    {r t : ℕ} (H x : ℝ) (signs : Finset ℝ)
    (hsigns : ∀ s ∈ signs, s = 1 ∨ s = -1) (closed : Bool)
    (v : Shao.Path r) (u : Shao.Path t) :
    let T : ℝ := Shao.energy u
    let d : ℝ := Shao.prefixSum u t
    fixedGaussianWeight H x signs closed v u ≤
      8 * (if 0 < T ∧ H ≤ T then
        |firstValue u| ^ 3 / (T * Real.sqrt T) *
          (1 + |d| ^ 3 / (T * Real.sqrt T)) else 0) := by
  classical
  dsimp only
  by_cases hcut : 0 < Shao.energy u ∧ H ≤ Shao.energy u
  · rw [if_pos hcut]
    have hT := hcut.1
    have hm : 0 ≤ |firstValue u| ^ 3 / (Shao.energy u * Real.sqrt (Shao.energy u)) := by positivity
    have hc : 0 ≤ |Shao.prefixSum u t| ^ 3 / (Shao.energy u * Real.sqrt (Shao.energy u)) := by positivity
    have hden : Real.sqrt (Shao.energy u) ^ 3 =
        Shao.energy u * Real.sqrt (Shao.energy u) := by
      calc
        _ = Real.sqrt (Shao.energy u) ^ 2 * Real.sqrt (Shao.energy u) := by ring
        _ = _ := by rw [Real.sq_sqrt hcut.1.le]
    let z : ℝ := |Shao.prefixSum u t| / Real.sqrt (Shao.energy u)
    have hz : 0 ≤ z := by positivity
    have hz3 : z ^ 3 =
        |Shao.prefixSum u t| ^ 3 / (Shao.energy u * Real.sqrt (Shao.energy u)) := by
      dsimp only [z]
      rw [div_pow, hden]
    have hcube : (1 + z) ^ 3 ≤ 4 * (1 + z ^ 3) := by
      nlinarith [mul_nonneg (sq_nonneg (z - 1)) (show 0 ≤ z + 1 by positivity)]
    have hD : SourceMarkedSuffixAveraging.suffixD u ^ 3 ≤
        4 * (1 + |Shao.prefixSum u t| ^ 3 /
          (Shao.energy u * Real.sqrt (Shao.energy u))) := by
      simpa only [SourceMarkedSuffixAveraging.suffixD, if_pos hcut.1, ← hz3] using hcube
    have hcards : (signs.card : ℝ) ≤ 2 := by
      have hsub : signs ⊆ ({1, -1} : Finset ℝ) := by
        intro s hs
        rcases hsigns s hs with h | h <;> simp [h]
      have hh := Finset.card_le_card hsub
      norm_num at hh
      exact_mod_cast hh
    have hPi : 0 ≤ gaussianProfiles x signs v u ∧ gaussianProfiles x signs v u ≤ 2 := by
      unfold gaussianProfiles
      rw [if_pos hcut.1]
      refine ⟨Finset.sum_nonneg (fun s _ => (Real.exp_pos _).le), ?_⟩
      calc
        _ ≤ ∑ s ∈ signs, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro s hs
          exact Real.exp_le_one_iff.2
            (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) hcut.1.le)
        _ = (signs.card : ℝ) := by simp
        _ ≤ 2 := hcards
    unfold fixedGaussianWeight
    by_cases hA : prefixSurvival x signs closed v u
    · rw [if_pos ⟨hcut.1, hcut.2, hA⟩]
      calc
        _ ≤ (|firstValue u| ^ 3 / (Shao.energy u * Real.sqrt (Shao.energy u)) *
            (4 * (1 + |Shao.prefixSum u t| ^ 3 /
              (Shao.energy u * Real.sqrt (Shao.energy u))))) * 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hD hm) hPi.2 hPi.1 (by positivity)
        _ = _ := by ring
    · rw [if_neg (by tauto)]
      positivity
  · rw [if_neg hcut]
    unfold fixedGaussianWeight
    rw [if_neg (by tauto)]
    norm_num

theorem fixed_suffix_weighted_gaussian_integral :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu] (r : ℕ) (hr : 0 < r),
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 → 0 < (∫ z : ℝ, z ^ 2 ∂nu) →
        let V : ℝ := (r : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu)
        let scale : ℝ := Real.sqrt V
        let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / scale) nu
        let Rprefix : ℝ := Shao.truncationBudget normalizedLaw r 0
        ∀ (t : ℕ) (u : Shao.Path (t + 1)) (H x : ℝ), 0 < H → 0 < x → x ≤ 1 →
          ∀ (signs : Finset ℝ), (∀ s ∈ signs, s = 1 ∨ s = -1) →
            ∀ (closed : Bool),
              Integrable (fun v : Shao.Path r => fixedGaussianWeight H x signs closed v u)
                (Measure.pi (fun _ : Fin r => nu)) ∧
              (∫ v : Shao.Path r, fixedGaussianWeight H x signs closed v u
                ∂Measure.pi (fun _ : Fin r => nu)) ≤
                C * SourceMarkedSuffixAveraging.lateMarkedWeight H V Rprefix u 0 := by
  classical
  obtain ⟨C, hC, hprofile⟩ := Shao.Probability.iid_fixed_suffix_gaussian_wall_profiles
  refine ⟨C, hC, ?_⟩
  intro nu hnu r hr h2 hmean hsecond V scale normalizedLaw Rprefix t u H x hH hx hx1 signs hsigns closed
  letI : IsProbabilityMeasure nu := hnu
  let P : Measure (Shao.Path r) := Measure.pi (fun _ : Fin r => nu)
  have hdata := fixed_gaussian_weight_measurable_bound r (t + 1) H x signs closed
  have hm : Measurable (fun v : Shao.Path r => fixedGaussianWeight H x signs closed v u) :=
    hdata.1.comp (measurable_id.prodMk measurable_const)
  have hi : Integrable (fun v : Shao.Path r => fixedGaussianWeight H x signs closed v u) P :=
    (integrable_const ((signs.card : ℝ) * (1 + Real.sqrt ((t + 1 : ℕ) : ℝ)) ^ 3)).mono'
      hm.aestronglyMeasurable (ae_of_all _ fun v => by
        simpa only [Real.norm_eq_abs] using (hdata.2.1 v u).2)
  refine ⟨hi, ?_⟩
  by_cases hcut : 0 < Shao.energy u ∧ H ≤ Shao.energy u
  · let q : ℝ := |u 0| ^ 3 / (Shao.energy u * Real.sqrt (Shao.energy u))
    let D : ℝ := 1 + |Shao.prefixSum u (t + 1)| / Real.sqrt (Shao.energy u)
    let A : Set (Shao.Path r) := {v | prefixSurvival x signs closed v u}
    let profiles : Shao.Path r → ℝ := fun v =>
      ∑ s ∈ signs, Real.exp
        (-((max (x * Real.sqrt (Shao.energy u + Shao.energy v) -
          s * Shao.prefixSum v r -
          (|u 0| + max (s * Shao.prefixSum u (t + 1)) 0)) 0) ^ 2) / Shao.energy u)
    have he (v : Shao.Path r) : fixedGaussianWeight H x signs closed v u =
        (q * D ^ 3) * A.indicator profiles v := by
      by_cases hv : v ∈ A
      · have hsurv : prefixSurvival x signs closed v u := hv
        have hcond : 0 < Shao.energy u ∧ H ≤ Shao.energy u ∧
            prefixSurvival x signs closed v u := ⟨hcut.1, hcut.2, hsurv⟩
        rw [fixedGaussianWeight, if_pos hcond, Set.indicator_of_mem hv]
        simp only [gaussianProfiles, SourceMarkedSuffixAveraging.suffixD,
          if_pos hcut.1, firstValue, dif_pos (Nat.succ_pos t)]
        rfl
      · have hsurv : ¬prefixSurvival x signs closed v u := hv
        rw [fixedGaussianWeight, if_neg (by tauto), Set.indicator_of_notMem hv, mul_zero]
    have hp := hprofile nu r hr h2 hmean hsecond t u hcut.1 x hx hx1 signs hsigns closed
    change (∫ v, A.indicator profiles v ∂P) ≤
      C * D ^ 2 * (Shao.energy u / V + Rprefix ^ 2) at hp
    calc
      _ = (q * D ^ 3) * (∫ v, A.indicator profiles v ∂P) := by
        simp_rw [he]
        exact integral_const_mul _ _
      _ ≤ (q * D ^ 3) * (C * D ^ 2 * (Shao.energy u / V + Rprefix ^ 2)) := by
        apply mul_le_mul_of_nonneg_left hp
        have hT := hcut.1
        dsimp only [q, D]
        positivity
      _ = _ := by
        unfold SourceMarkedSuffixAveraging.lateMarkedWeight
          SourceMarkedSuffixAveraging.normalizedCubicMark SourceMarkedSuffixAveraging.suffixD
        simp only [if_pos hcut.2, if_pos hcut.1]
        dsimp only [q, D]
        ring
  · have hfzero (v : Shao.Path r) : fixedGaussianWeight H x signs closed v u = 0 := by
      unfold fixedGaussianWeight
      exact if_neg (by tauto)
    have hnot : ¬H ≤ Shao.energy u := by
      intro hh
      exact hcut ⟨hH.trans_le hh, hh⟩
    simp only [hfzero, integral_zero, SourceMarkedSuffixAveraging.lateMarkedWeight,
      if_neg hnot, mul_zero, le_refl]

theorem iid_rank_gaussian_weight_fubini
    {n : ℕ} (nu : Measure ℝ) [IsProbabilityMeasure nu] (r : Fin n)
    (H x : ℝ) (signs : Finset ℝ) (closed : Bool) :
    Integrable (fun a : Shao.Path n => rankGaussianWeight H x signs closed a r)
      (Measure.pi (fun _ : Fin n => nu)) ∧
    Integrable (fun u : Shao.Path (n - r.val) =>
      ∫ v : Shao.Path r.val, fixedGaussianWeight H x signs closed v u
        ∂Measure.pi (fun _ : Fin r.val => nu))
      (Measure.pi (fun _ : Fin (n - r.val) => nu)) ∧
    (∫ a : Shao.Path n, rankGaussianWeight H x signs closed a r
      ∂Measure.pi (fun _ : Fin n => nu)) =
      ∫ u : Shao.Path (n - r.val),
        (∫ v : Shao.Path r.val, fixedGaussianWeight H x signs closed v u
          ∂Measure.pi (fun _ : Fin r.val => nu))
        ∂Measure.pi (fun _ : Fin (n - r.val) => nu) := by
  classical
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let Pr : Measure (Shao.Path r.val) := Measure.pi (fun _ : Fin r.val => nu)
  let Pt : Measure (Shao.Path (n - r.val)) := Measure.pi (fun _ : Fin (n - r.val) => nu)
  let split : Shao.Path n → Shao.Path r.val × Shao.Path (n - r.val) := fun a =>
    (Spitzer.head a r.val (Nat.le_of_lt r.is_lt), Spitzer.tail a r.val (Nat.le_of_lt r.is_lt))
  have hsplit : MeasurePreserving split P (Pr.prod Pt) := by
    let e : Fin r.val ⊕ Fin (n - r.val) ≃ Fin n :=
      finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le (Nat.le_of_lt r.is_lt)))
    have h1 := (measurePreserving_piCongrLeft (fun _ : Fin n => nu) e).symm
    have h2 := measurePreserving_sumPiEquivProdPi (fun _ : Fin r.val ⊕ Fin (n - r.val) => nu)
    convert h2.comp h1 using 1
    ext a i <;> change a _ = a _ <;> congr 1
  let F : Shao.Path r.val × Shao.Path (n - r.val) → ℝ := fun p =>
    fixedGaussianWeight H x signs closed p.1 p.2
  have hdata := fixed_gaussian_weight_measurable_bound r.val (n - r.val) H x signs closed
  have hFi : Integrable F (Pr.prod Pt) :=
    (integrable_const ((signs.card : ℝ) * (1 + Real.sqrt ((n - r.val : ℕ) : ℝ)) ^ 3)).mono'
      hdata.1.aestronglyMeasurable (ae_of_all _ fun p => by
        simpa only [Real.norm_eq_abs] using (hdata.2.1 p.1 p.2).2)
  refine ⟨hsplit.integrable_comp_of_integrable hFi, hFi.integral_prod_right, ?_⟩
  have he := integral_map (μ := P) (φ := split) (f := F)
    hsplit.measurable.aemeasurable hdata.1.aestronglyMeasurable
  rw [hsplit.map_eq] at he
  exact he.symm.trans (integral_prod_symm _ hFi)

theorem iid_late_rank_gaussian_integral_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (r : Fin n),
        0 < r.val → Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 → 0 < (∫ z : ℝ, z ^ 2 ∂nu) →
        let V : ℝ := (r.val : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu)
        let scale : ℝ := Real.sqrt V
        let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / scale) nu
        let Rprefix : ℝ := Shao.truncationBudget normalizedLaw r.val 0
        ∀ (H x : ℝ), 0 < H → 0 < x → x ≤ 1 →
          ∀ (signs : Finset ℝ), (∀ s ∈ signs, s = 1 ∨ s = -1) →
            ∀ (closed : Bool),
              (∫ a : Shao.Path n, rankGaussianWeight H x signs closed a r
                ∂Measure.pi (fun _ : Fin n => nu)) ≤
                C * ∫ a : Shao.Path n,
                  SourceMarkedSuffixAveraging.lateAveragedWeight H V Rprefix
                    (Spitzer.tail a r.val (Nat.le_of_lt r.is_lt))
                  ∂Measure.pi (fun _ : Fin n => nu) := by
  classical
  obtain ⟨C, hC, hfixed⟩ := fixed_suffix_weighted_gaussian_integral
  refine ⟨C, hC, ?_⟩
  intro nu hnu n r hr h2 hmean hsecond V scale normalizedLaw Rprefix H x hH hx hx1 signs hsigns closed
  letI : IsProbabilityMeasure nu := hnu
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let Pr : Measure (Shao.Path r.val) := Measure.pi (fun _ : Fin r.val => nu)
  let Pt : Measure (Shao.Path (n - r.val)) := Measure.pi (fun _ : Fin (n - r.val) => nu)
  have ht : 0 < n - r.val := Nat.sub_pos_of_lt r.is_lt
  let j : Fin (n - r.val) := ⟨0, ht⟩
  have hV : 0 < V := mul_pos (by exact_mod_cast hr) hsecond
  have hp (t : ℕ) (ht : 0 < t) (u : Shao.Path t) :
      (∫ v : Shao.Path r.val, fixedGaussianWeight H x signs closed v u ∂Pr) ≤
        C * SourceMarkedSuffixAveraging.lateMarkedWeight H V Rprefix u ⟨0, ht⟩ := by
    cases t with
    | zero => omega
    | succ t => exact (hfixed nu r.val hr h2 hmean hsecond t u H x hH hx hx1 signs hsigns closed).2
  have hf := iid_rank_gaussian_weight_fubini nu r H x signs closed
  have hm := SourceMarkedSuffixAveraging.iid_product_late_marked_integral_eq_average
    ht nu h2 H V Rprefix hH hV j
  let f : Fin (n - r.val) → Fin n := fun i => ⟨r.val + i.val, by omega⟩
  have hinj : Function.Injective f := by
    intro i k hik
    apply Fin.ext
    have hh := congrArg Fin.val hik
    dsimp only [f] at hh
    omega
  let Y : Fin (n - r.val) → Shao.Path n → ℝ := fun i a => a (f i)
  have hY (i : Fin (n - r.val)) : Measurable (Y i) := measurable_pi_apply (f i)
  have hYindep : iIndepFun Y P :=
    (iIndepFun_pi (X := fun _ : Fin n => (id : ℝ → ℝ))
      (fun _ => measurable_id.aemeasurable)).precomp hinj
  have hYlaw (i : Fin (n - r.val)) : IdentDistrib (Y i) (id : ℝ → ℝ) P nu := by
    refine ⟨(hY i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa only [Measure.map_id] using
      (measurePreserving_eval (μ := fun _ : Fin n => nu) (f i)).map_eq
  have hTail : IdentDistrib
      (fun a : Shao.Path n => Spitzer.tail a r.val (Nat.le_of_lt r.is_lt))
      (id : Shao.Path (n - r.val) → Shao.Path (n - r.val)) P Pt :=
    iid_samplePath_identDistrib hY hYindep hYlaw
  have hAvg : Measurable (SourceMarkedSuffixAveraging.lateAveragedWeight H V Rprefix :
      Shao.Path (n - r.val) → ℝ) :=
    (SourceMarkedSuffixAveraging.late_weights_measurable_and_covariant H V Rprefix).2.1
  have he := (hTail.comp hAvg).integral_eq
  calc
    _ = ∫ u : Shao.Path (n - r.val),
        (∫ v : Shao.Path r.val, fixedGaussianWeight H x signs closed v u ∂Pr) ∂Pt := hf.2.2
    _ ≤ ∫ u : Shao.Path (n - r.val),
        C * SourceMarkedSuffixAveraging.lateMarkedWeight H V Rprefix u j ∂Pt :=
      integral_mono hf.2.1 (hm.1.const_mul C) (fun u => hp (n - r.val) ht u)
    _ = C * (∫ u : Shao.Path (n - r.val),
        SourceMarkedSuffixAveraging.lateMarkedWeight H V Rprefix u j ∂Pt) :=
      integral_const_mul _ _
    _ = C * (∫ u : Shao.Path (n - r.val),
        SourceMarkedSuffixAveraging.lateAveragedWeight H V Rprefix u ∂Pt) := by rw [hm.2.2]
    _ = _ := by
      simpa only [Function.comp_def, id_eq] using congrArg (fun z : ℝ => C * z) he.symm

theorem iid_gaussian_profile_early_late_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 0 < n),
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 → 0 < (∫ z : ℝ, z ^ 2 ∂nu) →
        let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂nu
        let scale : ℝ := Real.sqrt ((n : ℝ) * sigmaSq)
        let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / scale) nu
        let R : ℝ := Shao.truncationBudget normalizedLaw n 0
        let h : ℝ := 4 * (n : ℝ) * sigmaSq * R ^ 2
        let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
        ∀ (x : ℝ), 0 < x → x ≤ 1 →
          ∀ (signs : Finset ℝ), (∀ s ∈ signs, s = 1 ∨ s = -1) →
            ∀ (closed : Bool),
              let earlyRanks : Finset (Fin n) := Finset.univ.filter (fun r => 2 * r.val < n)
              let lateRanks : Finset (Fin n) := Finset.univ.filter (fun r => n ≤ 2 * r.val)
              let early : Shao.Path n → ℝ := fun a =>
                ∑ r ∈ earlyRanks, rankGaussianWeight h x signs closed a r
              let late : Shao.Path n → ℝ := fun a =>
                ∑ r ∈ lateRanks, rankGaussianWeight h x signs closed a r
              let total : Shao.Path n → ℝ := fun a =>
                ∑ r : Fin n, rankGaussianWeight h x signs closed a r
              (∀ r : Fin n, Integrable (fun a => rankGaussianWeight h x signs closed a r) P) ∧
              Integrable early P ∧ Integrable late P ∧ Integrable total P ∧
              (∫ a, early a ∂P) ≤ C * R ∧ (∫ a, late a ∂P) ≤ C * R ∧
              (∫ a, total a ∂P) ≤ C * R := by
  classical
  obtain ⟨CE, hCE, hEarly⟩ := Shao.Probability.iid_early_cubic_suffix_budget
  obtain ⟨CL, hCL, hLate⟩ := Shao.Probability.iid_late_fifth_and_cubic_suffix_budgets
  obtain ⟨CP, hCP, hPrefix⟩ := iid_late_rank_gaussian_integral_bound
  refine ⟨8 * CE + CP * CL, by positivity, ?_⟩
  intro nu hnu n hn h2 hmean hsecond sigmaSq scale normalizedLaw R h P x hx hx1 signs hsigns closed
    earlyRanks lateRanks early late total
  letI : IsProbabilityMeasure nu := hnu
  have hgeometry := Shao.Probability.raw_truncation_budget_suffix_geometry nu n hn h2 hsecond
  have hR : 0 ≤ R := hgeometry.1.le
  have hh : 0 < h := hgeometry.2.2.2.1
  let Ptail : (t : ℕ) → Measure (Shao.Path t) := fun t => Measure.pi (fun _ : Fin t => nu)
  let firstCube : (t : ℕ) → Shao.Path t → ℝ := fun t u =>
    if ht : 0 < t then |u ⟨0, ht⟩| ^ 3 else 0
  let EW : (t : ℕ) → Shao.Path t → ℝ := fun t u =>
    if 0 < Shao.energy u ∧ h ≤ Shao.energy u then
      firstCube t u / (Shao.energy u * Real.sqrt (Shao.energy u)) *
        (1 + |Shao.prefixSum u t| ^ 3 / (Shao.energy u * Real.sqrt (Shao.energy u)))
    else 0
  let suffix : (t : ℕ) → Shao.Path n → Shao.Path (n - (n - t)) := fun t a =>
    Spitzer.tail a (n - t) (Nat.sub_le n t)
  let T : ℕ → Shao.Path n → ℝ := fun t a => Shao.energy (suffix t a)
  let d : ℕ → Shao.Path n → ℝ := fun t a => Shao.prefixSum (suffix t a) (n - (n - t))
  let beta : ℕ → Shao.Path n → ℝ := fun t a =>
    if 0 < T t a then (∑ i : Fin (n - (n - t)), |suffix t a i| ^ 3) /
      (T t a * Real.sqrt (T t a)) else 0
  let D : ℕ → Shao.Path n → ℝ := fun t a =>
    if 0 < T t a then 1 + |d t a| / Real.sqrt (T t a) else 1
  let Rp : ℕ → ℝ := fun t => Shao.truncationBudget
    (Measure.map (fun z : ℝ => z / Real.sqrt (((n - t : ℕ) : ℝ) * sigmaSq)) nu) (n - t) 0
  let LW : ℕ → ℕ → Shao.Path n → ℝ := fun p t a =>
    if 0 < T t a ∧ h ≤ T t a then (beta t a / (t : ℝ)) * D t a ^ p *
      (T t a / (((n - t : ℕ) : ℝ) * sigmaSq) + Rp t ^ 2) else 0
  have hEB : (∀ t ∈ Finset.Icc ((n + 1) / 2) n, Integrable (EW t) (Ptail t)) ∧
      (∑ t ∈ Finset.Icc ((n + 1) / 2) n, ∫ u, EW t u ∂Ptail t) ≤ CE * R :=
    hEarly nu n hn h2 hmean hsecond
  have hLB : (∀ t ∈ Finset.Icc 1 (n / 2), Integrable (LW 5 t) P) ∧
      (∑ t ∈ Finset.Icc 1 (n / 2), ∫ a, LW 5 t a ∂P) ≤ CL * R :=
    hLate nu n hn h2 hmean hsecond 5 (Or.inr rfl)
  have hEWnonneg (t : ℕ) (u : Shao.Path t) : 0 ≤ EW t u := by
    dsimp only [EW, firstCube]
    split_ifs with hsel ht
    · have hT := hsel.1
      positivity
    · simp
    · exact le_rfl
  have hLWnonneg (t : ℕ) (a : Shao.Path n) : 0 ≤ LW 5 t a := by
    dsimp only [LW]
    split_ifs with hsel
    · have hT := hsel.1
      have hb : 0 ≤ beta t a := by
        dsimp only [beta]
        rw [if_pos hT]
        positivity
      have hD : 0 ≤ D t a := by
        dsimp only [D]
        rw [if_pos hT]
        positivity
      have hs : 0 ≤ sigmaSq := hsecond.le
      exact mul_nonneg
        (mul_nonneg (div_nonneg hb (Nat.cast_nonneg t)) (pow_nonneg hD 5))
        (add_nonneg (div_nonneg hT.le (mul_nonneg (Nat.cast_nonneg _) hs)) (sq_nonneg _))
    · exact le_rfl
  have hEWmeas (t : ℕ) : Measurable (EW t) := by
    have he : Measurable (Shao.energy : Shao.Path t → ℝ) := Shao.measurable_energy
    have hf : Measurable (firstCube t) := by
      by_cases ht : 0 < t
      · simp only [firstCube, dif_pos ht]
        fun_prop
      · simp only [firstCube, dif_neg ht]
        exact measurable_const
    apply Measurable.ite ((measurableSet_lt measurable_const he).inter
      (measurableSet_le measurable_const he))
    · exact (hf.div (he.mul he.sqrt)).mul (measurable_const.add
        (((continuous_abs.measurable.comp (Shao.measurable_prefixSum t)).pow_const 3).div (he.mul he.sqrt)))
    · exact measurable_const
  have hTail (r : Fin n) : IdentDistrib
      (fun a : Shao.Path n => Spitzer.tail a r.val (Nat.le_of_lt r.is_lt))
      (id : Shao.Path (n - r.val) → Shao.Path (n - r.val)) P (Ptail (n - r.val)) := by
    let f : Fin (n - r.val) → Fin n := fun i => ⟨r.val + i.val, by omega⟩
    have hinj : Function.Injective f := by
      intro i k hik
      apply Fin.ext
      have he := congrArg Fin.val hik
      dsimp only [f] at he
      omega
    let Y : Fin (n - r.val) → Shao.Path n → ℝ := fun i a => a (f i)
    have hY (i : Fin (n - r.val)) : Measurable (Y i) := measurable_pi_apply (f i)
    have hYi : iIndepFun Y P :=
      (iIndepFun_pi (X := fun _ : Fin n => (id : ℝ → ℝ))
        (fun _ => measurable_id.aemeasurable)).precomp hinj
    have hYlaw (i : Fin (n - r.val)) : IdentDistrib (Y i) (id : ℝ → ℝ) P nu := by
      refine ⟨(hY i).aemeasurable, measurable_id.aemeasurable, ?_⟩
      simpa only [Measure.map_id] using
        (measurePreserving_eval (μ := fun _ : Fin n => nu) (f i)).map_eq
    exact iid_samplePath_identDistrib hY hYi hYlaw
  have hRank (r : Fin n) : Integrable (fun a => rankGaussianWeight h x signs closed a r) P :=
    (iid_rank_gaussian_weight_fubini nu r h x signs closed).1
  have hErank (r : Fin n) (hr : r ∈ earlyRanks) :
      (∫ a, rankGaussianWeight h x signs closed a r ∂P) ≤
        8 * (∫ u, EW (n - r.val) u ∂Ptail (n - r.val)) := by
    have hrE : 2 * r.val < n := (Finset.mem_filter.1 hr).2
    have hmem : n - r.val ∈ Finset.Icc ((n + 1) / 2) n := by
      simp only [Finset.mem_Icc]
      have hrn := r.is_lt
      omega
    have hid := (hTail r).comp (hEWmeas (n - r.val))
    have hi : Integrable (fun a : Shao.Path n => EW (n - r.val)
        (Spitzer.tail a r.val (Nat.le_of_lt r.is_lt))) P :=
      hid.integrable_iff.mpr (hEB.1 _ hmem)
    have hp (a : Shao.Path n) : rankGaussianWeight h x signs closed a r ≤
        8 * EW (n - r.val) (Spitzer.tail a r.val (Nat.le_of_lt r.is_lt)) := by
      have hb := gaussian_weight_early_domination h x signs hsigns closed
        (Spitzer.head a r.val (Nat.le_of_lt r.is_lt))
        (Spitzer.tail a r.val (Nat.le_of_lt r.is_lt))
      have hfirst (u : Shao.Path (n - r.val)) :
          |firstValue u| ^ 3 = firstCube (n - r.val) u := by
        simp only [firstValue, firstCube, dif_pos (Nat.sub_pos_of_lt r.is_lt)]
      simpa only [rankGaussianWeight, hfirst, EW] using hb
    calc
      _ ≤ ∫ a : Shao.Path n, 8 * EW (n - r.val)
          (Spitzer.tail a r.val (Nat.le_of_lt r.is_lt)) ∂P :=
        integral_mono (hRank r) (hi.const_mul 8) hp
      _ = 8 * (∫ a : Shao.Path n, EW (n - r.val)
          (Spitzer.tail a r.val (Nat.le_of_lt r.is_lt)) ∂P) := integral_const_mul _ _
      _ = _ := by
        simpa only [Function.comp_def, id_eq] using congrArg (fun z : ℝ => 8 * z) hid.integral_eq
  have hLrank (r : Fin n) (hr : r ∈ lateRanks) :
      (∫ a, rankGaussianWeight h x signs closed a r ∂P) ≤
        CP * (∫ a, LW 5 (n - r.val) a ∂P) := by
    have hrL : n ≤ 2 * r.val := (Finset.mem_filter.1 hr).2
    have hr0 : 0 < r.val := by omega
    have hrr : n - (n - r.val) = r.val := Nat.sub_sub_self r.is_lt.le
    have he (a : Shao.Path n) : LW 5 (n - r.val) a =
        SourceMarkedSuffixAveraging.lateAveragedWeight h
          ((r.val : ℝ) * sigmaSq)
          (Shao.truncationBudget
            (Measure.map (fun z : ℝ => z / Real.sqrt ((r.val : ℝ) * sigmaSq)) nu) r.val 0)
          (Spitzer.tail a r.val (Nat.le_of_lt r.is_lt)) := by
      let W (k : ℕ) (hk : k ≤ n) : ℝ :=
        SourceMarkedSuffixAveraging.lateAveragedWeight h ((k : ℝ) * sigmaSq)
          (Shao.truncationBudget
            (Measure.map (fun z : ℝ => z / Real.sqrt ((k : ℝ) * sigmaSq)) nu) k 0)
          (Spitzer.tail a k hk)
      have hW : W (n - (n - r.val)) (Nat.sub_le n _) =
          W r.val (Nat.le_of_lt r.is_lt) := by
        have heq : (⟨n - (n - r.val), Nat.sub_le n (n - r.val)⟩ : {k : ℕ // k ≤ n}) =
            ⟨r.val, Nat.le_of_lt r.is_lt⟩ := Subtype.ext hrr
        exact congrArg (fun k : {k : ℕ // k ≤ n} => W k.1 k.2)
          heq
      change LW 5 (n - r.val) a = W r.val (Nat.le_of_lt r.is_lt)
      rw [← hW]
      dsimp only [LW, T, beta, D, d, Rp, suffix]
      dsimp only [W]
      unfold SourceMarkedSuffixAveraging.lateAveragedWeight
        SourceMarkedSuffixAveraging.suffixBeta SourceMarkedSuffixAveraging.suffixD
        SourceMarkedSuffixAveraging.cubicMass
      have hlen : n - (n - (n - r.val)) = n - r.val :=
        Nat.sub_sub_self (Nat.sub_le n r.val)
      simp only [hlen]
      by_cases hcut : h ≤ Shao.energy (Spitzer.tail a (n - (n - r.val)) (Nat.sub_le n _))
      · have hpos := hh.trans_le hcut
        simp only [hpos, hcut, and_self, ite_true]
      · simp only [hcut, and_false, ite_false]
    have hb := hPrefix nu n r hr0 h2 hmean hsecond h x hh hx hx1 signs hsigns closed
    simpa only [he] using hb
  have hsumE : (∑ r ∈ earlyRanks, ∫ a, rankGaussianWeight h x signs closed a r ∂P) ≤
      8 * CE * R := by
    calc
      _ ≤ ∑ t ∈ Finset.Icc ((n + 1) / 2) n, 8 * (∫ u, EW t u ∂Ptail t) := by
        apply Finset.sum_le_sum_of_injOn (fun r : Fin n => n - r.val)
        · intro r hr s hs he
          apply Fin.ext
          change n - r.val = n - s.val at he
          have hrn := r.is_lt
          have hsn := s.is_lt
          omega
        · intro t ht
          obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 ht
          have hrE : 2 * r.val < n := (Finset.mem_filter.1 hr).2
          simp only [Finset.mem_Icc]
          have hrn := r.is_lt
          omega
        · exact hErank
        · intro t ht _
          exact mul_nonneg (by norm_num) (integral_nonneg (hEWnonneg t))
      _ = 8 * (∑ t ∈ Finset.Icc ((n + 1) / 2) n, ∫ u, EW t u ∂Ptail t) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ 8 * (CE * R) := mul_le_mul_of_nonneg_left hEB.2 (by norm_num)
      _ = _ := by ring
  have hsumL : (∑ r ∈ lateRanks, ∫ a, rankGaussianWeight h x signs closed a r ∂P) ≤
      CP * CL * R := by
    calc
      _ ≤ ∑ t ∈ Finset.Icc 1 (n / 2), CP * (∫ a, LW 5 t a ∂P) := by
        apply Finset.sum_le_sum_of_injOn (fun r : Fin n => n - r.val)
        · intro r hr s hs he
          apply Fin.ext
          change n - r.val = n - s.val at he
          have hrn := r.is_lt
          have hsn := s.is_lt
          omega
        · intro t ht
          obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 ht
          have hrL : n ≤ 2 * r.val := (Finset.mem_filter.1 hr).2
          simp only [Finset.mem_Icc]
          have hrn := r.is_lt
          omega
        · exact hLrank
        · intro t ht _
          exact mul_nonneg hCP.le (integral_nonneg (hLWnonneg t))
      _ = CP * (∑ t ∈ Finset.Icc 1 (n / 2), ∫ a, LW 5 t a ∂P) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ CP * (CL * R) := mul_le_mul_of_nonneg_left hLB.2 hCP.le
      _ = _ := by ring
  have hEi : Integrable early P := integrable_finsetSum earlyRanks (fun r _ => hRank r)
  have hLi : Integrable late P := integrable_finsetSum lateRanks (fun r _ => hRank r)
  have hTi : Integrable total P := integrable_finsetSum Finset.univ (fun r _ => hRank r)
  have hE : (∫ a, early a ∂P) ≤ 8 * CE * R := by
    dsimp only [early]
    rw [integral_finsetSum _ (fun r _ => hRank r)]
    exact hsumE
  have hL : (∫ a, late a ∂P) ≤ CP * CL * R := by
    dsimp only [late]
    rw [integral_finsetSum _ (fun r _ => hRank r)]
    exact hsumL
  have hdisj : Disjoint earlyRanks lateRanks := by
    apply Finset.disjoint_left.2
    intro r hr hs
    have he := (Finset.mem_filter.1 hr).2
    have hl := (Finset.mem_filter.1 hs).2
    change 2 * r.val < n at he
    change n ≤ 2 * r.val at hl
    omega
  have hunion : earlyRanks ∪ lateRanks = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro r
    apply Finset.mem_union.2
    by_cases he : 2 * r.val < n
    · exact Or.inl (Finset.mem_filter.2 ⟨Finset.mem_univ r, he⟩)
    · exact Or.inr (Finset.mem_filter.2 ⟨Finset.mem_univ r, Nat.le_of_not_gt he⟩)
  have htotal : total = fun a => early a + late a := by
    funext a
    dsimp only [total, early, late]
    rw [← Finset.sum_union hdisj, hunion]
  refine ⟨hRank, hEi, hLi, hTi, ?_, ?_, ?_⟩
  · exact hE.trans (mul_le_mul_of_nonneg_right (by nlinarith [mul_pos hCP hCL]) hR)
  · exact hL.trans (mul_le_mul_of_nonneg_right (by nlinarith) hR)
  · rw [htotal, integral_add hEi hLi]
    calc
      _ ≤ 8 * CE * R + CP * CL * R := add_le_add hE hL
      _ = _ := by ring

theorem iid_family_gaussian_profile_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) (nu : Measure ℝ)
        [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
        (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ),
        (∀ i, Measurable (X i)) → iIndepFun X mu →
        (∀ i, IdentDistrib (X i) (id : ℝ → ℝ) mu nu) →
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 → 0 < (∫ z : ℝ, z ^ 2 ∂nu) →
        let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂nu
        let scale : ℝ := Real.sqrt ((n : ℝ) * sigmaSq)
        let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / scale) nu
        let R : ℝ := Shao.truncationBudget normalizedLaw n 0
        let h : ℝ := 4 * (n : ℝ) * sigmaSq * R ^ 2
        ∀ (x : ℝ), 0 < x → x ≤ 1 →
          ∀ (signs : Finset ℝ), (∀ s ∈ signs, s = 1 ∨ s = -1) →
            ∀ (closed : Bool),
              let earlyRanks : Finset (Fin n) := Finset.univ.filter (fun r => 2 * r.val < n)
              let lateRanks : Finset (Fin n) := Finset.univ.filter (fun r => n ≤ 2 * r.val)
              let early : Ω → ℝ := fun omega =>
                ∑ r ∈ earlyRanks, rankGaussianWeight h x signs closed (samplePath X omega) r
              let late : Ω → ℝ := fun omega =>
                ∑ r ∈ lateRanks, rankGaussianWeight h x signs closed (samplePath X omega) r
              let total : Ω → ℝ := fun omega =>
                ∑ r : Fin n, rankGaussianWeight h x signs closed (samplePath X omega) r
              Integrable early mu ∧ Integrable late mu ∧ Integrable total mu ∧
              (∫ omega, early omega ∂mu) ≤ C * R ∧
              (∫ omega, late omega ∂mu) ≤ C * R ∧
              (∫ omega, total omega ∂mu) ≤ C * R := by
  classical
  obtain ⟨C, hC, hCanonical⟩ := iid_gaussian_profile_early_late_budget
  refine ⟨C, hC, ?_⟩
  intro Ω hΩ mu nu hmu hnu n hn X hX hIndep hLaw h2 hmean hsecond
    sigmaSq scale normalizedLaw R h x hx hx1 signs hsigns closed earlyRanks lateRanks early late total
  letI : IsProbabilityMeasure mu := hmu
  letI : IsProbabilityMeasure nu := hnu
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let E : Shao.Path n → ℝ := fun a =>
    ∑ r ∈ earlyRanks, rankGaussianWeight h x signs closed a r
  let L : Shao.Path n → ℝ := fun a =>
    ∑ r ∈ lateRanks, rankGaussianWeight h x signs closed a r
  let G : Shao.Path n → ℝ := fun a =>
    ∑ r : Fin n, rankGaussianWeight h x signs closed a r
  have hRankMeas (r : Fin n) : Measurable (fun a : Shao.Path n =>
      rankGaussianWeight h x signs closed a r) := by
    have hs : Measurable (fun a : Shao.Path n =>
        (Spitzer.head a r.val (Nat.le_of_lt r.is_lt),
          Spitzer.tail a r.val (Nat.le_of_lt r.is_lt))) :=
      (Measurable.of_eval fun i => measurable_pi_apply _).prodMk
        (Measurable.of_eval fun i => measurable_pi_apply _)
    exact (fixed_gaussian_weight_measurable_bound r.val (n - r.val) h x signs closed).1.comp hs
  have hEmeas : Measurable E := Finset.measurable_sum _ (fun r _ => hRankMeas r)
  have hLmeas : Measurable L := Finset.measurable_sum _ (fun r _ => hRankMeas r)
  have hGmeas : Measurable G := Finset.measurable_sum _ (fun r _ => hRankMeas r)
  have hpath := iid_samplePath_identDistrib hX hIndep hLaw
  have hE := hpath.comp hEmeas
  have hL := hpath.comp hLmeas
  have hG := hpath.comp hGmeas
  have hb := hCanonical nu n hn h2 hmean hsecond x hx hx1 signs hsigns closed
  refine ⟨hE.integrable_iff.mpr hb.2.1, hL.integrable_iff.mpr hb.2.2.1,
    hG.integrable_iff.mpr hb.2.2.2.1, ?_, ?_, ?_⟩
  · exact hE.integral_eq.le.trans hb.2.2.2.2.1
  · exact hL.integral_eq.le.trans hb.2.2.2.2.2.1
  · exact hG.integral_eq.le.trans hb.2.2.2.2.2.2

end Shao.Probability.SourceIIDGaussianProfileBudget
