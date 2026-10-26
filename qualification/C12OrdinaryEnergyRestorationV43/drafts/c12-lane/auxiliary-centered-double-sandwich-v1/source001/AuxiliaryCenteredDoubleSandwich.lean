import Shao.C2.AuxiliaryCenteredEvent
import Shao.C2.TwoSided

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
noncomputable section
namespace Shao.C2.AuxiliaryCenteredDoubleSandwich
open MeasureTheory Set
open scoped BigOperators Classical

private theorem centered_prefix_abs_le
    {n : ℕ} (v : Shao.Path n) (mu : ℝ) (k : ℕ) :
    |Shao.prefixSum (fun i => v i - mu) k - Shao.prefixSum v k| ≤
      (n : ℝ) * |mu| := by
  classical
  let I : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => i.val < k)
  have hCardNat : I.card ≤ n := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_le_card (Finset.subset_univ I))
  have hCard : (I.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hCardNat
  have hSum : Shao.prefixSum (fun i => v i - mu) k =
      Shao.prefixSum v k - (I.card : ℝ) * mu := by
    change (∑ i ∈ I, v i - mu) = (∑ i ∈ I, v i) - (I.card : ℝ) * mu
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have hDiff : Shao.prefixSum (fun i => v i - mu) k - Shao.prefixSum v k =
      -((I.card : ℝ) * mu) := by rw [hSum]; ring
  rw [hDiff, abs_neg, abs_mul, abs_of_nonneg (Nat.cast_nonneg I.card)]
  exact mul_le_mul_of_nonneg_right hCard (abs_nonneg mu)

private theorem upper_max_difference_le
    {n : ℕ} (hn : 0 < n) (v w : Shao.Path n) (d : ℝ)
    (hPrefix : ∀ k : ℕ, |Shao.prefixSum v k - Shao.prefixSum w k| ≤ d) :
    |Shao.upperMax v hn - Shao.upperMax w hn| ≤ d := by
  have hv : Shao.upperMax v hn ≤ Shao.upperMax w hn + d := by
    apply (Shao.upperMax_le_iff v hn _).mpr
    intro k hk hkn
    have hp := (abs_le.mp (hPrefix k)).2
    have hw := Shao.le_upperMax w hn k hk hkn
    linarith only [hp, hw]
  have hw : Shao.upperMax w hn ≤ Shao.upperMax v hn + d := by
    apply (Shao.upperMax_le_iff w hn _).mpr
    intro k hk hkn
    have hp := (abs_le.mp (hPrefix k)).1
    have hvk := Shao.le_upperMax v hn k hk hkn
    linarith only [hp, hvk]
  exact abs_le.mpr ⟨by linarith only [hw], by linarith only [hv]⟩

theorem auxiliary_centered_double_crossing_transport
    {n : ℕ} (hn : 0 < n) (v : Shao.Path n) (mu x h : ℝ) (hx : 0 ≤ x)
    (hShift : (n : ℝ) * |mu| + x * (Real.sqrt (n : ℝ) * |mu|) ≤
      h * Real.sqrt (Shao.energy (fun i => v i - mu))) :
    ((fun i => v i - mu) ∈ Shao.C2.doubleCrossing hn (x + h) →
      v ∈ Shao.C2.doubleCrossing hn x) ∧
    (v ∈ Shao.C2.doubleCrossing hn x →
      (fun i => v i - mu) ∈ Shao.C2.doubleCrossing hn (x - h)) := by
  classical
  let c : Shao.Path n := fun i => v i - mu
  let d : ℝ := (n : ℝ) * |mu|
  let e : ℝ := Real.sqrt (n : ℝ) * |mu|
  have hPrefix (k : ℕ) : |Shao.prefixSum c k - Shao.prefixSum v k| ≤ d :=
    centered_prefix_abs_le v mu k
  have hUpper : |Shao.upperMax c hn - Shao.upperMax v hn| ≤ d :=
    upper_max_difference_le hn c v d hPrefix
  have hNegPrefix (k : ℕ) :
      |Shao.prefixSum (-c) k - Shao.prefixSum (-v) k| ≤ d := by
    rw [Shao.prefixSum_neg, Shao.prefixSum_neg]
    rw [show -Shao.prefixSum c k - -Shao.prefixSum v k =
      -(Shao.prefixSum c k - Shao.prefixSum v k) by ring, abs_neg]
    exact hPrefix k
  have hLower : |Shao.lowerMax c hn - Shao.lowerMax v hn| ≤ d :=
    upper_max_difference_le hn (-c) (-v) d hNegPrefix
  have hCenteredEnergy : Real.sqrt (Shao.energy c) ≤
      Real.sqrt (Shao.energy v) + e :=
    (Shao.C2.AuxiliaryCenteredEvent.auxiliary_centered_path_energy_and_sum v mu).2
  have hBack : (fun i => c i - -mu) = v := by
    funext i
    dsimp only [c]
    ring
  have hOriginalEnergy : Real.sqrt (Shao.energy v) ≤
      Real.sqrt (Shao.energy c) + e := by
    have hb :=
      (Shao.C2.AuxiliaryCenteredEvent.auxiliary_centered_path_energy_and_sum c (-mu)).2
    rw [hBack, abs_neg] at hb
    exact hb
  have hShift' : d + x * e ≤ h * Real.sqrt (Shao.energy c) := hShift
  have hCenteredWeighted := mul_le_mul_of_nonneg_left hCenteredEnergy hx
  have hOriginalWeighted := mul_le_mul_of_nonneg_left hOriginalEnergy hx
  have huLeft := (abs_le.mp hUpper).1
  have huRight := (abs_le.mp hUpper).2
  have hlLeft := (abs_le.mp hLower).1
  have hlRight := (abs_le.mp hLower).2
  constructor
  · intro hc
    change (x + h) * Real.sqrt (Shao.energy c) ≤ Shao.upperMax c hn ∧
      (x + h) * Real.sqrt (Shao.energy c) ≤ Shao.lowerMax c hn at hc
    change x * Real.sqrt (Shao.energy v) ≤ Shao.upperMax v hn ∧
      x * Real.sqrt (Shao.energy v) ≤ Shao.lowerMax v hn
    constructor
    · nlinarith only [hc.1, huRight, hShift', hOriginalWeighted]
    · nlinarith only [hc.2, hlRight, hShift', hOriginalWeighted]
  · intro hv
    change x * Real.sqrt (Shao.energy v) ≤ Shao.upperMax v hn ∧
      x * Real.sqrt (Shao.energy v) ≤ Shao.lowerMax v hn at hv
    change (x - h) * Real.sqrt (Shao.energy c) ≤ Shao.upperMax c hn ∧
      (x - h) * Real.sqrt (Shao.energy c) ≤ Shao.lowerMax c hn
    constructor
    · nlinarith only [hv.1, huLeft, hShift', hCenteredWeighted]
    · nlinarith only [hv.2, hlLeft, hShift', hCenteredWeighted]

theorem auxiliary_centered_double_crossing_sandwich
    {n : ℕ} (hn : 0 < n) (v : Shao.Path n) (mu x : ℝ) (hx : 0 ≤ x)
    (hxScale : x / Real.sqrt (n : ℝ) ≤ 1 / 2)
    (hEnergy : 1 / 4 ≤ Shao.energy (fun i => v i - mu)) :
    ((fun i => v i - mu) ∈
        Shao.C2.doubleCrossing hn (x + 3 * ((n : ℝ) * |mu|)) →
      v ∈ Shao.C2.doubleCrossing hn x) ∧
    (v ∈ Shao.C2.doubleCrossing hn x →
      (fun i => v i - mu) ∈
        Shao.C2.doubleCrossing hn (x - 3 * ((n : ℝ) * |mu|))) := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hSqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnReal
  have hxBound : x ≤ (1 / 2 : ℝ) * Real.sqrt (n : ℝ) :=
    (div_le_iff₀ hSqrt).mp hxScale
  have hRootEnergy : (1 / 2 : ℝ) ≤
      Real.sqrt (Shao.energy (fun i => v i - mu)) := by
    have hs := Real.sq_sqrt (Shao.energy_nonneg (fun i => v i - mu))
    have hz := Real.sqrt_nonneg (Shao.energy (fun i => v i - mu))
    nlinarith only [hEnergy, hs, hz]
  have hd : 0 ≤ (n : ℝ) * |mu| := mul_nonneg (Nat.cast_nonneg n) (abs_nonneg mu)
  have hxError : x * (Real.sqrt (n : ℝ) * |mu|) ≤
      (n : ℝ) * |mu| / 2 := by
    calc
      x * (Real.sqrt (n : ℝ) * |mu|) ≤
          ((1 / 2 : ℝ) * Real.sqrt (n : ℝ)) * (Real.sqrt (n : ℝ) * |mu|) :=
        mul_le_mul_of_nonneg_right hxBound (mul_nonneg hSqrt.le (abs_nonneg mu))
      _ = (Real.sqrt (n : ℝ)) ^ 2 * |mu| / 2 := by ring
      _ = (n : ℝ) * |mu| / 2 := by rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  have hThree : 0 ≤ 3 * ((n : ℝ) * |mu|) := by positivity
  have hRootWeighted := mul_le_mul_of_nonneg_left hRootEnergy hThree
  apply auxiliary_centered_double_crossing_transport hn v mu x
    (3 * ((n : ℝ) * |mu|)) hx
  nlinarith only [hxError, hRootWeighted]

theorem auxiliary_centered_double_probability_sandwich
    {n : ℕ} (hn : 0 < n) (P : Measure (Shao.Path n)) [IsFiniteMeasure P]
    (mu x : ℝ) (hx : 0 ≤ x) (hxScale : x / Real.sqrt (n : ℝ) ≤ 1 / 2) :
    P.real {v : Shao.Path n | (fun i => v i - mu) ∈
        Shao.C2.doubleCrossing hn (x + 3 * ((n : ℝ) * |mu|))} -
        P.real {v : Shao.Path n | Shao.energy (fun i => v i - mu) < 1 / 4} ≤
      P.real (Shao.C2.doubleCrossing hn x) ∧
    P.real (Shao.C2.doubleCrossing hn x) ≤
      P.real {v : Shao.Path n | (fun i => v i - mu) ∈
          Shao.C2.doubleCrossing hn (x - 3 * ((n : ℝ) * |mu|))} +
        P.real {v : Shao.Path n | Shao.energy (fun i => v i - mu) < 1 / 4} := by
  classical
  let bad : Set (Shao.Path n) :=
    {v | Shao.energy (fun i => v i - mu) < 1 / 4}
  let plus : Set (Shao.Path n) :=
    {v | (fun i => v i - mu) ∈
      Shao.C2.doubleCrossing hn (x + 3 * ((n : ℝ) * |mu|))}
  let minus : Set (Shao.Path n) :=
    {v | (fun i => v i - mu) ∈
      Shao.C2.doubleCrossing hn (x - 3 * ((n : ℝ) * |mu|))}
  have hPlus : plus ⊆ Shao.C2.doubleCrossing hn x ∪ bad := by
    intro v hv
    by_cases hEnergy : 1 / 4 ≤ Shao.energy (fun i => v i - mu)
    · exact Or.inl
        ((auxiliary_centered_double_crossing_sandwich hn v mu x hx hxScale hEnergy).1 hv)
    · exact Or.inr (lt_of_not_ge hEnergy)
  have hMinus : Shao.C2.doubleCrossing hn x ⊆ minus ∪ bad := by
    intro v hv
    by_cases hEnergy : 1 / 4 ≤ Shao.energy (fun i => v i - mu)
    · exact Or.inl
        ((auxiliary_centered_double_crossing_sandwich hn v mu x hx hxScale hEnergy).2 hv)
    · exact Or.inr (lt_of_not_ge hEnergy)
  have hp : P.real plus ≤ P.real (Shao.C2.doubleCrossing hn x) + P.real bad := by
    calc
      P.real plus ≤ P.real (Shao.C2.doubleCrossing hn x ∪ bad) := measureReal_mono hPlus
      _ ≤ P.real (Shao.C2.doubleCrossing hn x) + P.real bad :=
        measureReal_union_le _ _
  have hm : P.real (Shao.C2.doubleCrossing hn x) ≤ P.real minus + P.real bad := by
    calc
      P.real (Shao.C2.doubleCrossing hn x) ≤ P.real (minus ∪ bad) :=
        measureReal_mono hMinus
      _ ≤ P.real minus + P.real bad := measureReal_union_le _ _
  change P.real plus - P.real bad ≤ P.real (Shao.C2.doubleCrossing hn x) ∧
    P.real (Shao.C2.doubleCrossing hn x) ≤ P.real minus + P.real bad
  exact ⟨by linarith only [hp], hm⟩

end Shao.C2.AuxiliaryCenteredDoubleSandwich
