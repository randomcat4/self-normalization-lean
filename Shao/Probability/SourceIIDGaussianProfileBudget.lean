/- Actual iid Gaussian wall-profile payment: independent partial target. -/
import Shao.Probability.SourceTrueWallProfile
import Shao.Probability.SourceMarkedSuffixAveraging
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

end Shao.Probability.SourceIIDGaussianProfileBudget
