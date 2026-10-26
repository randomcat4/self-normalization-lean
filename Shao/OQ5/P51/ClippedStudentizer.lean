import Shao.OQ5.P51.BoundedRemainderPayments

set_option autoImplicit false

universe u

noncomputable section
open scoped Classical

namespace Shao.OQ5.P51

def studentizerClip (B d : ℝ) : ℝ :=
  max (-(min B (1 / 2 : ℝ))) (min d B)

def studentizerClipBudget (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (C0 rho y : ℝ) (x : Fin n → Ω) : ℝ :=
  C0 * (((1 + rho) * y) / Real.sqrt (n : ℝ) +
    residualEnergyJ n r x / ((1 + rho) * y * Real.sqrt (n : ℝ)))

def clippedCenteredDelta (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (C0 rho y : ℝ)
    (x : Fin n → Ω) : ℝ :=
  if projectionV n g x = 0 then 0 else
    studentizerClip (studentizerClipBudget n r C0 rho y x)
      (centeredDelta n g r x)

def clippedCenteredStatistic (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (C0 rho y : ℝ)
    (x : Fin n → Ω) : ℝ :=
  if projectionV n g x = 0 then 0 else
    (projectionW n g x + residualStatisticD n r x) /
      (projectionV n g x *
        Real.sqrt (1 + clippedCenteredDelta n g r C0 rho y x))

theorem studentizerClip_contract (B d : ℝ) (hB : 0 ≤ B) :
    (1 / 2 : ℝ) ≤ 1 + studentizerClip B d ∧
    |studentizerClip B d| ≤ B ∧
    |studentizerClip B d| ≤ |d| ∧
    (-(1 / 2 : ℝ) ≤ d → |d| ≤ B → studentizerClip B d = d) := by
  have hmin0 : 0 ≤ min B (1 / 2 : ℝ) := le_min hB (by norm_num)
  have hminB : min B (1 / 2 : ℝ) ≤ B := min_le_left _ _
  have hminhalf : min B (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) := min_le_right _ _
  have hClipLower : -(1 / 2 : ℝ) ≤ studentizerClip B d := by
    exact le_trans (neg_le_neg hminhalf) (le_max_left _ _)
  have hClipLowerB : -B ≤ studentizerClip B d := by
    exact le_trans (neg_le_neg hminB) (le_max_left _ _)
  have hClipUpperB : studentizerClip B d ≤ B := by
    exact max_le (le_trans (neg_nonpos.mpr hmin0) hB) (min_le_right _ _)
  have hAbsB : |studentizerClip B d| ≤ B :=
    abs_le.mpr ⟨hClipLowerB, hClipUpperB⟩
  have hAbsD : |studentizerClip B d| ≤ |d| := by
    by_cases hd : 0 ≤ d
    · have hminD0 : 0 ≤ min d B := le_min hd hB
      have hClipEq : studentizerClip B d = min d B :=
        max_eq_right (le_trans (neg_nonpos.mpr hmin0) hminD0)
      rw [hClipEq, abs_of_nonneg hminD0, abs_of_nonneg hd]
      exact min_le_left _ _
    · have hd0 : d ≤ 0 := le_of_lt (lt_of_not_ge hd)
      have hminDEq : min d B = d := min_eq_left (le_trans hd0 hB)
      have hClip0 : studentizerClip B d ≤ 0 := by
        apply max_le (neg_nonpos.mpr hmin0)
        rw [hminDEq]
        exact hd0
      have hdClip : d ≤ studentizerClip B d := by
        unfold studentizerClip
        rw [hminDEq]
        exact le_max_right _ _
      rw [abs_of_nonpos hClip0, abs_of_nonpos hd0]
      exact neg_le_neg hdClip
  refine ⟨?_, hAbsB, hAbsD, ?_⟩
  · linarith only [hClipLower]
  · intro hLower hDom
    have hdB : d ≤ B := (abs_le.mp hDom).2
    have hBd : -B ≤ d := (abs_le.mp hDom).1
    have hLowerMin : -(min B (1 / 2 : ℝ)) ≤ d := by
      by_cases hBhalf : B ≤ (1 / 2 : ℝ)
      · rw [min_eq_left hBhalf]
        exact hBd
      · rw [min_eq_right (le_of_lt (lt_of_not_ge hBhalf))]
        exact hLower
    unfold studentizerClip
    rw [min_eq_left hdB, max_eq_right hLowerMin]

theorem studentizerClipBudget_nonneg (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (C0 rho y : ℝ) (x : Fin n → Ω)
    (hC0 : 0 ≤ C0) (hrho : 0 ≤ rho) (hy : 0 ≤ y) :
    0 ≤ studentizerClipBudget n r C0 rho y x := by
  have hsigma : 0 ≤ 1 + rho := by linarith only [hrho]
  have hJ : 0 ≤ residualEnergyJ n r x := by
    unfold residualEnergyJ
    exact Finset.sum_nonneg (fun i _ => sq_nonneg (residualU n r x i))
  unfold studentizerClipBudget
  exact mul_nonneg hC0
    (add_nonneg
      (div_nonneg (mul_nonneg hsigma hy) (Real.sqrt_nonneg (n : ℝ)))
      (div_nonneg hJ
        (mul_nonneg (mul_nonneg hsigma hy) (Real.sqrt_nonneg (n : ℝ)))))

theorem clippedCentered_zero (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (C0 rho y : ℝ)
    (x : Fin n → Ω) (hV : projectionV n g x = 0) :
    centeredDelta n g r x = 0 ∧
    clippedCenteredDelta n g r C0 rho y x = 0 ∧
    clippedCenteredStatistic n g r C0 rho y x = 0 := by
  refine ⟨centeredDelta_eq_zero_of_projectionV_eq_zero n g r x hV, ?_, ?_⟩
  · simp only [clippedCenteredDelta, if_pos hV]
  · simp only [clippedCenteredStatistic, if_pos hV]

theorem clippedCenteredDelta_bounds (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (C0 rho y : ℝ)
    (x : Fin n → Ω) (hC0 : 0 ≤ C0) (hrho : 0 ≤ rho) (hy : 0 ≤ y) :
    (1 / 2 : ℝ) ≤ 1 + clippedCenteredDelta n g r C0 rho y x ∧
    |clippedCenteredDelta n g r C0 rho y x| ≤
      studentizerClipBudget n r C0 rho y x ∧
    |clippedCenteredDelta n g r C0 rho y x| ≤ |centeredDelta n g r x| ∧
    (0 < projectionV n g x →
      0 < projectionV n g x *
        Real.sqrt (1 + clippedCenteredDelta n g r C0 rho y x)) := by
  have hB : 0 ≤ studentizerClipBudget n r C0 rho y x :=
    studentizerClipBudget_nonneg n r C0 rho y x hC0 hrho hy
  by_cases hV : projectionV n g x = 0
  · have hZero := clippedCentered_zero n g r C0 rho y x hV
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hZero.2.1]
      norm_num
    · rw [hZero.2.1, abs_zero]
      exact hB
    · rw [hZero.2.1, abs_zero]
      exact abs_nonneg _
    · intro hPos
      exact False.elim ((ne_of_gt hPos) hV)
  · have hScalar := studentizerClip_contract
      (studentizerClipBudget n r C0 rho y x) (centeredDelta n g r x) hB
    have hDelta : clippedCenteredDelta n g r C0 rho y x =
        studentizerClip (studentizerClipBudget n r C0 rho y x)
          (centeredDelta n g r x) := by
      simp only [clippedCenteredDelta, if_neg hV]
    have hHalf : (1 / 2 : ℝ) ≤ 1 + clippedCenteredDelta n g r C0 rho y x := by
      rw [hDelta]
      exact hScalar.1
    refine ⟨hHalf, ?_, ?_, ?_⟩
    · rw [hDelta]
      exact hScalar.2.1
    · rw [hDelta]
      exact hScalar.2.2.1
    · intro hPos
      exact mul_pos hPos (Real.sqrt_pos.mpr (by linarith only [hHalf]))

theorem centered_studentizer_factorization (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (x : Fin n → Ω)
    (hV : 0 < projectionV n g x)
    (hLower : -(1 / 2 : ℝ) ≤ centeredDelta n g r x) :
    0 < Real.sqrt (centeredSq n g r x) ∧
    Real.sqrt (centeredSq n g r x) =
      projectionV n g x * Real.sqrt (1 + centeredDelta n g r x) := by
  have hVne : projectionV n g x ≠ 0 := ne_of_gt hV
  have hVsqne : (projectionV n g x) ^ 2 ≠ 0 := pow_ne_zero 2 hVne
  have hRatio : centeredDelta n g r x =
      centeredSq n g r x / (projectionV n g x) ^ 2 - 1 := by
    simp only [centeredDelta, if_neg hVne]
  have hSquare : centeredSq n g r x =
      (projectionV n g x) ^ 2 * (1 + centeredDelta n g r x) := by
    calc
      centeredSq n g r x =
          (centeredDelta n g r x + 1) * (projectionV n g x) ^ 2 :=
        (div_eq_iff hVsqne).mp (by linarith only [hRatio])
      _ = (projectionV n g x) ^ 2 * (1 + centeredDelta n g r x) := by ring
  have hRad : 0 < 1 + centeredDelta n g r x := by linarith only [hLower]
  have hFactor : Real.sqrt (centeredSq n g r x) =
      projectionV n g x * Real.sqrt (1 + centeredDelta n g r x) := by
    calc
      Real.sqrt (centeredSq n g r x) =
          Real.sqrt ((projectionV n g x) ^ 2 * (1 + centeredDelta n g r x)) :=
        congrArg Real.sqrt hSquare
      _ = Real.sqrt ((projectionV n g x) ^ 2) *
          Real.sqrt (1 + centeredDelta n g r x) :=
        Real.sqrt_mul (sq_nonneg (projectionV n g x)) _
      _ = projectionV n g x * Real.sqrt (1 + centeredDelta n g r x) := by
        rw [Real.sqrt_sq hV.le]
  refine ⟨?_, hFactor⟩
  rw [hFactor]
  exact mul_pos hV (Real.sqrt_pos.mpr hRad)

theorem clippedCentered_comparison_on_projectionGood (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (C0 rho y : ℝ)
    (x : Fin n → Ω) (hn : 4 ≤ n) (hy : (1 : ℝ) ≤ y)
    (hGood : x ∈ projectionGood n g y)
    (hDom : |centeredDelta n g r x| ≤ studentizerClipBudget n r C0 rho y x)
    (hLower : -(1 / 2 : ℝ) ≤ centeredDelta n g r x) :
    clippedCenteredDelta n g r C0 rho y x = centeredDelta n g r x ∧
    0 < projectionV n g x *
      Real.sqrt (1 + clippedCenteredDelta n g r C0 rho y x) ∧
    0 < Real.sqrt (centeredSq n g r x) ∧
    projectionV n g x * Real.sqrt (1 + clippedCenteredDelta n g r C0 rho y x) =
      Real.sqrt (centeredSq n g r x) ∧
    clippedCenteredStatistic n g r C0 rho y x =
      (if Real.sqrt (centeredSq n g r x) = 0 then 0 else
        (projectionW n g x + residualStatisticD n r x) /
          Real.sqrt (centeredSq n g r x)) := by
  have hV : 0 < projectionV n g x :=
    (projectionGood_bounds n g x y hn hy hGood).1
  have hVne : projectionV n g x ≠ 0 := ne_of_gt hV
  have hB : 0 ≤ studentizerClipBudget n r C0 rho y x :=
    le_trans (abs_nonneg (centeredDelta n g r x)) hDom
  have hFixed : studentizerClip (studentizerClipBudget n r C0 rho y x)
      (centeredDelta n g r x) = centeredDelta n g r x :=
    (studentizerClip_contract (studentizerClipBudget n r C0 rho y x)
      (centeredDelta n g r x) hB).2.2.2 hLower hDom
  have hDelta : clippedCenteredDelta n g r C0 rho y x = centeredDelta n g r x := by
    simp only [clippedCenteredDelta, if_neg hVne]
    exact hFixed
  obtain ⟨hSourcePos, hFactor⟩ := centered_studentizer_factorization n g r x hV hLower
  have hDenom : projectionV n g x *
      Real.sqrt (1 + clippedCenteredDelta n g r C0 rho y x) =
        Real.sqrt (centeredSq n g r x) := by
    rw [hDelta]
    exact hFactor.symm
  have hClipPos : 0 < projectionV n g x *
      Real.sqrt (1 + clippedCenteredDelta n g r C0 rho y x) := by
    rw [hDenom]
    exact hSourcePos
  refine ⟨hDelta, hClipPos, hSourcePos, hDenom, ?_⟩
  unfold clippedCenteredStatistic
  rw [if_neg hVne, if_neg (ne_of_gt hSourcePos), hDenom]

theorem clippedCentered_denominator_bad_subset (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (C0 rho y : ℝ)
    (hC0 : 0 ≤ C0) (hrho : 0 ≤ rho) (hy : 0 ≤ y) :
    {x : Fin n → Ω |
      (1 / 4 : ℝ) < y ^ 2 * |clippedCenteredDelta n g r C0 rho y x| ∧
        x ∈ projectionGood n g y} ⊆
      denominatorRemainderBad n g r y := by
  intro x hx
  change (1 / 4 : ℝ) < y ^ 2 * |centeredDelta n g r x| ∧
    x ∈ projectionGood n g y
  have hBound : |clippedCenteredDelta n g r C0 rho y x| ≤ |centeredDelta n g r x| :=
    (clippedCenteredDelta_bounds n g r C0 rho y x hC0 hrho hy).2.2.1
  exact ⟨lt_of_lt_of_le hx.1 (mul_le_mul_of_nonneg_left hBound (sq_nonneg y)), hx.2⟩

theorem clippedCentered_comparison_exception_subset (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (C0 rho y : ℝ)
    (hn : 4 ≤ n) (hy : (1 : ℝ) ≤ y)
    (hDom : ∀ x : Fin n → Ω, x ∈ projectionGood n g y →
      |centeredDelta n g r x| ≤ studentizerClipBudget n r C0 rho y x) :
    {x : Fin n → Ω |
      clippedCenteredStatistic n g r C0 rho y x ≠
        (if Real.sqrt (centeredSq n g r x) = 0 then 0 else
          (projectionW n g x + residualStatisticD n r x) /
            Real.sqrt (centeredSq n g r x))} ⊆
      (projectionGood n g y)ᶜ ∪ lowerStudentizerBad n g r y := by
  intro x hDisagree
  by_cases hGood : x ∈ projectionGood n g y
  · by_cases hBad : centeredDelta n g r x < -(1 / 2 : ℝ)
    · exact Or.inr ⟨hBad, hGood⟩
    · have hLower : -(1 / 2 : ℝ) ≤ centeredDelta n g r x := le_of_not_gt hBad
      have hEq :=
        (clippedCentered_comparison_on_projectionGood n g r C0 rho y x hn hy
          hGood (hDom x hGood) hLower).2.2.2.2
      exact False.elim (hDisagree hEq)
  · exact Or.inl hGood

end Shao.OQ5.P51

end
