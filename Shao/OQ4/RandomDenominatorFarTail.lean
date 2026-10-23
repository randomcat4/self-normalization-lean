import Shao.OQ4.EnergyTiltedLaw
import Shao.Probability.MeasurablePath
import Shao.Basic.ClosedSurvival
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
The actual random-denominator FAR energy tail, from denom01.md lines79–112.
The cutoff exponential difference pays the entire countable dyadic union.
This auxiliary argument needs no centering, K, Brownian or conditional-MGF input.
All walls are closed and the dyadic energy intervals are closed/open.
The original root, center/middle layers and source attribution are unchanged.
-/

namespace Shao.OQ4.RandomDenominatorFarTail

open MeasureTheory Filter
open scoped BigOperators Topology

noncomputable def cutoffBox (n : ℕ) (H : ℝ) : Set (Shao.Path n) :=
  {a | ∀ i, |a i| ≤ 2 * H}

noncomputable def cutoffExcess {n : ℕ} (H s : ℝ) (a : Shao.Path n) : ℝ :=
  by
    classical
    exact if a ∈ cutoffBox n H then Real.exp (s * Shao.energy a / H ^ 2) - 1 else 0

noncomputable def randomDenominatorEvent (n : ℕ) (h : ℝ) : Set (Shao.Path n) :=
  {a | a ∈ Shao.closedStrip (h / Real.sqrt (n : ℝ) * Real.sqrt (Shao.energy a))}

noncomputable def farLayer (n : ℕ) (h : ℝ) (j : ℕ) : Set (Shao.Path n) :=
  randomDenominatorEvent n h ∩
    {a | (2 : ℝ) ^ j * (n : ℝ) ≤ Shao.energy a ∧
      Shao.energy a < (2 : ℝ) ^ (j + 1) * (n : ℝ)}

noncomputable def farHeight (h : ℝ) (j : ℕ) : ℝ :=
  Real.sqrt ((2 : ℝ) ^ (j + 1)) * h

noncomputable def farDifferenceConstant (s : ℝ) : ℝ :=
  Real.exp (4 * s) * s

noncomputable def farScalarBound (s β : ℝ) (n : ℕ) (h : ℝ) : ℝ :=
  farDifferenceConstant s * ((n : ℝ) / h ^ 2) *
    Real.exp (-s * ((n : ℝ) / h ^ 2) / 4 +
      energyNormalizerErrorConstant s * β * ((n : ℝ) / h ^ 3) / 8)

noncomputable def farMainTerm (n : ℕ) (h : ℝ) : ℝ :=
  (4 / Real.pi) * Real.exp (-(Real.pi ^ 2 / 8) * ((n : ℝ) / h ^ 2))

private theorem measurableSet_cutoffBox (n : ℕ) (H : ℝ) :
    MeasurableSet (cutoffBox n H) := by
  simp only [cutoffBox, Set.setOf_forall]
  exact MeasurableSet.iInter fun i =>
    measurableSet_le ((continuous_apply i : Continuous (fun a : Shao.Path n => a i)).abs.measurable) measurable_const

private theorem measurable_cutoffExcess (n : ℕ) (H s : ℝ) :
    Measurable (cutoffExcess (n := n) H s) := by
  classical
  exact Measurable.ite (measurableSet_cutoffBox n H)
    ((((Shao.measurable_energy.const_mul s).div_const (H ^ 2)).exp).sub_const 1)
    measurable_const

theorem cutoffExcess_nonneg (n : ℕ) (H s : ℝ) (hs : 0 ≤ s) (a : Shao.Path n) :
    0 ≤ cutoffExcess H s a := by
  classical
  unfold cutoffExcess
  split_ifs
  · exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr
      (div_nonneg (mul_nonneg hs (Shao.energy_nonneg a)) (sq_nonneg H)))
  · exact le_rfl

theorem cutoffExcess_eq_products (n : ℕ) (H s : ℝ) (a : Shao.Path n) :
    cutoffExcess H s a =
      (∏ i, energyWeight H s (a i)) - (∏ i, energyWeight H 0 (a i)) := by
  classical
  by_cases ha : a ∈ cutoffBox n H
  · have hp : (∏ i, energyWeight H s (a i)) =
        Real.exp (s * Shao.energy a / H ^ 2) := by
      calc
        _ = ∏ i : Fin n, Real.exp (s * (a i) ^ 2 / H ^ 2) := by
          apply Finset.prod_congr rfl
          intro i _
          simp only [energyWeight, ha i, ite_true]
        _ = _ := by
          rw [← Real.exp_sum]
          congr 1
          change (∑ i : Fin n, s * (a i) ^ 2 / H ^ 2) =
            s * (∑ i : Fin n, (a i) ^ 2) / H ^ 2
          rw [← Finset.sum_div, ← Finset.mul_sum]
    have hp0 : (∏ i, energyWeight H 0 (a i)) = 1 := by
      have hw (i : Fin n) : energyWeight H 0 (a i) = 1 := by
        simp [energyWeight, ha i]
      simp only [hw, Finset.prod_const_one]
    simp only [cutoffExcess, ha, ite_true, hp, hp0]
  · have hnall : ¬ ∀ i, |a i| ≤ 2 * H := ha
    obtain ⟨i, hi⟩ := not_forall.mp hnall
    have hp : (∏ i, energyWeight H s (a i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [energyWeight, hi])
    have hp0 : (∏ i, energyWeight H 0 (a i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [energyWeight, hi])
    simp only [cutoffExcess, ha, ite_false, hp, hp0, sub_self]

theorem cutoffExcess_integral (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (H s : ℝ) (hH : 0 < H) (hs : 0 ≤ s) :
    Integrable (cutoffExcess (n := n) H s) (Measure.pi (fun _ : Fin n => ν)) ∧
      (∫ a, cutoffExcess H s a ∂Measure.pi (fun _ : Fin n => ν)) =
        energyNormalizer ν H s ^ n - energyNormalizer ν H 0 ^ n := by
  have hw := energyWeight_integrable ν s H s hs hH (le_of_eq (abs_of_nonneg hs))
  have hw0 := energyWeight_integrable ν 0 H 0 (by norm_num) hH (by norm_num)
  have hpi : Integrable (fun a : Shao.Path n => ∏ i, energyWeight H s (a i))
      (Measure.pi (fun _ : Fin n => ν)) :=
    Integrable.fintype_prod (fun _ : Fin n => hw)
  have hpi0 : Integrable (fun a : Shao.Path n => ∏ i, energyWeight H 0 (a i))
      (Measure.pi (fun _ : Fin n => ν)) :=
    Integrable.fintype_prod (fun _ : Fin n => hw0)
  have heq : cutoffExcess (n := n) H s =
      fun a => (∏ i, energyWeight H s (a i)) - (∏ i, energyWeight H 0 (a i)) :=
    funext (cutoffExcess_eq_products n H s)
  constructor
  · rw [heq]
    exact hpi.sub hpi0
  · rw [heq, integral_sub hpi hpi0]
    simp only [integral_fintype_prod_eq_pow, Fintype.card_fin, energyNormalizer]

theorem cutoff_normalizer_difference_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (H s : ℝ) (hH : 0 < H) (hs : 0 ≤ s)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    0 ≤ energyNormalizer ν H s - energyNormalizer ν H 0 ∧
      energyNormalizer ν H s - energyNormalizer ν H 0 ≤
        farDifferenceConstant s / H ^ 2 := by
  have hw := energyWeight_integrable ν s H s hs hH (le_of_eq (abs_of_nonneg hs))
  have hw0 := energyWeight_integrable ν 0 H 0 (by norm_num) hH (by norm_num)
  have hp0 (x : ℝ) : 0 ≤ energyWeight H s x - energyWeight H 0 x := by
    by_cases hx : |x| ≤ 2 * H
    · simp only [energyWeight, hx, ite_true, zero_mul, zero_div, Real.exp_zero]
      exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr
        (div_nonneg (mul_nonneg hs (sq_nonneg x)) (sq_nonneg H)))
    · simp [energyWeight, hx]
  have hp (x : ℝ) : energyWeight H s x - energyWeight H 0 x ≤
      (farDifferenceConstant s / H ^ 2) * x ^ 2 := by
    by_cases hx : |x| ≤ 2 * H
    · have hb := energyTilt_weight_difference_inside s H s x hs hH
        (le_of_eq (abs_of_nonneg hs)) hx
      have hz : energyWeight H 0 x = 1 := by simp [energyWeight, hx]
      rw [hz]
      exact (le_abs_self _).trans (by simpa only [farDifferenceConstant] using hb)
    · simp only [energyWeight, hx, ite_false, sub_self]
      unfold farDifferenceConstant
      positivity
  constructor
  · change 0 ≤ (∫ x, energyWeight H s x ∂ν) - ∫ x, energyWeight H 0 x ∂ν
    rw [← integral_sub hw hw0]
    exact integral_nonneg hp0
  · have hb := integral_mono (hw.sub hw0)
        (hSq.const_mul (farDifferenceConstant s / H ^ 2)) hp
    change (∫ x, energyWeight H s x - energyWeight H 0 x ∂ν) ≤ _ at hb
    rw [integral_sub hw hw0, integral_const_mul, hsecond, mul_one] at hb
    exact hb

theorem cutoff_normalizer_first_order_upper (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (H s : ℝ) (hH : 1 ≤ H) (hs : 0 ≤ s)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    energyNormalizer ν H s ≤ 1 + s / H ^ 2 +
      energyNormalizerErrorConstant s * (∫ x : ℝ, |x| ^ 3 ∂ν) / H ^ 3 := by
  have he := (abs_le.mp (energyNormalizer_expansion ν s H s hs hH
    (le_of_eq (abs_of_nonneg hs)) hSq hCube hsecond)).2
  linarith

private theorem power_difference_bound (a b u : ℝ) (n : ℕ)
    (hn : 0 < n) (hb : 0 ≤ b) (hba : b ≤ a) (hu : 0 ≤ u) (ha : a ≤ 1 + u) :
    a ^ n - b ^ n ≤ (n : ℝ) * (a - b) * Real.exp ((n : ℝ) * u) := by
  have ha0 : 0 ≤ a := hb.trans hba
  have hd0 : 0 ≤ a - b := sub_nonneg.mpr hba
  have hae : a ≤ Real.exp u := ha.trans (by linarith [Real.add_one_le_exp u])
  have hbe : b ≤ Real.exp u := hba.trans hae
  have hpow (m : ℕ) : b ^ m ≤ Real.exp ((m : ℝ) * u) := by
    calc
      _ ≤ Real.exp u ^ m := pow_le_pow_left₀ hb hbe m
      _ = _ := (Real.exp_nat_mul u m).symm
  have hall (m : ℕ) : a ^ m - b ^ m ≤
      (m : ℝ) * (a - b) * Real.exp ((m : ℝ) * u) := by
    induction m with
    | zero => simp
    | succ m ih =>
      have hstep : (m : ℝ) * u ≤ ((m + 1 : ℕ) : ℝ) * u := by
        push_cast
        linarith
      have hemon := Real.exp_le_exp.mpr hstep
      calc
        _ = (a ^ m - b ^ m) * a + b ^ m * (a - b) := by
          simp only [pow_succ]
          ring
        _ ≤ ((m : ℝ) * (a - b) * Real.exp ((m : ℝ) * u)) * a +
            b ^ m * (a - b) :=
          add_le_add (mul_le_mul_of_nonneg_right ih ha0) le_rfl
        _ ≤ ((m : ℝ) * (a - b) * Real.exp ((m : ℝ) * u)) * Real.exp u +
            Real.exp ((m : ℝ) * u) * (a - b) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hae (by positivity))
            (mul_le_mul_of_nonneg_right (hpow m) hd0)
        _ = (m : ℝ) * (a - b) * Real.exp ((((m + 1 : ℕ) : ℝ)) * u) +
            (a - b) * Real.exp ((m : ℝ) * u) := by
          rw [show (((m + 1 : ℕ) : ℝ)) * u = (m : ℝ) * u + u by push_cast; ring,
            Real.exp_add]
          ring
        _ ≤ (m : ℝ) * (a - b) * Real.exp ((((m + 1 : ℕ) : ℝ)) * u) +
            (a - b) * Real.exp ((((m + 1 : ℕ) : ℝ)) * u) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hemon hd0)
        _ = _ := by push_cast; ring
  exact hall n

theorem cutoff_energy_markov_difference (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (H s q : ℝ) (hH : 0 < H) (hs : 0 < s) (hq : 0 < q)
    (A : Set (Shao.Path n)) (hA : MeasurableSet A)
    (hsub : A ⊆ cutoffBox n H ∩ {a | q ≤ Shao.energy a}) :
    (Measure.pi (fun _ : Fin n => ν)).real A ≤
      (energyNormalizer ν H s ^ n - energyNormalizer ν H 0 ^ n) /
        (Real.exp (s * q / H ^ 2) - 1) := by
  classical
  let d : ℝ := Real.exp (s * q / H ^ 2) - 1
  have hd : 0 < d := by
    dsimp [d]
    exact sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
  obtain ⟨hGi, hGe⟩ := cutoffExcess_integral ν n H s hH hs.le
  have hi : Integrable (A.indicator (fun _ : Shao.Path n => d))
      (Measure.pi (fun _ : Fin n => ν)) := (integrable_const d).indicator hA
  have hp (a : Shao.Path n) : A.indicator (fun _ => d) a ≤ cutoffExcess H s a := by
    by_cases ha : a ∈ A
    · obtain ⟨hbox, hqQ⟩ := hsub ha
      have harg : s * q / H ^ 2 ≤ s * Shao.energy a / H ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hqQ hs.le) (sq_nonneg H)
      simpa only [Set.indicator_of_mem ha, cutoffExcess, hbox, ite_true, d] using
        sub_le_sub_right (Real.exp_le_exp.mpr harg) 1
    · simpa only [Set.indicator_of_notMem ha] using cutoffExcess_nonneg n H s hs.le a
  have hb := integral_mono hi hGi hp
  have hInd : (∫ a, A.indicator (fun _ : Shao.Path n => d) a
        ∂Measure.pi (fun _ : Fin n => ν)) =
      (Measure.pi (fun _ : Fin n => ν)).real A * d := by
    simpa only [smul_eq_mul] using
      (integral_indicator_const (μ := Measure.pi (fun _ : Fin n => ν)) d hA)
  rw [hInd, hGe] at hb
  exact (le_div_iff₀ hd).2 hb

theorem measurableSet_randomDenominatorEvent (n : ℕ) (h : ℝ) :
    MeasurableSet (randomDenominatorEvent n h) := by
  change MeasurableSet {a : Shao.Path n | ∀ k : ℕ, k ≤ n →
    |Shao.prefixSum a k| ≤ h / Real.sqrt (n : ℝ) * Real.sqrt (Shao.energy a)}
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_le (Shao.continuous_prefixSum k).abs.measurable
    (continuous_const.mul (Real.continuous_sqrt.comp Shao.continuous_energy)).measurable

theorem randomDenominatorEvent_eq_absMax (n : ℕ) (hn : 0 < n) (h : ℝ) (hh : 0 ≤ h) :
    randomDenominatorEvent n h =
      {a | Shao.absMax a hn ≤ h / Real.sqrt (n : ℝ) * Real.sqrt (Shao.energy a)} := by
  ext a
  exact Shao.mem_closedStrip_iff_absMax_le a hn _ (by positivity)

theorem zero_energy_mem_randomDenominatorEvent (n : ℕ) (h : ℝ) (a : Shao.Path n)
    (hQ : Shao.energy a = 0) : a ∈ randomDenominatorEvent n h := by
  intro k _
  simp only [Shao.prefixSum_eq_zero_of_energy_eq_zero a hQ k, abs_zero,
    hQ, Real.sqrt_zero, mul_zero, le_refl]

private theorem measurableSet_farLayer (n : ℕ) (h : ℝ) (j : ℕ) :
    MeasurableSet (farLayer n h j) := by
  exact (measurableSet_randomDenominatorEvent n h).inter
    ((measurableSet_le measurable_const Shao.measurable_energy).inter
      (measurableSet_lt Shao.measurable_energy measurable_const))

theorem farHeight_identities (n : ℕ) (h : ℝ) (hh : 0 < h) (j : ℕ) (hj : 1 ≤ j) :
    0 < farHeight h j ∧
    farHeight h j ^ 2 = (2 : ℝ) ^ (j + 1) * h ^ 2 ∧
    2 * h ≤ farHeight h j ∧
    (2 : ℝ) ^ j * (n : ℝ) / farHeight h j ^ 2 = ((n : ℝ) / h ^ 2) / 2 ∧
    (n : ℝ) / farHeight h j ^ 2 = ((n : ℝ) / h ^ 2) / (2 : ℝ) ^ (j + 1) ∧
    (n : ℝ) / farHeight h j ^ 3 ≤ ((n : ℝ) / h ^ 3) / 8 := by
  have hp : 0 < (2 : ℝ) ^ (j + 1) := by positivity
  have hp4 : (4 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
    have hp := (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (by omega : 2 ≤ j + 1))
    norm_num at hp
    exact hp
  have hroot : 2 ≤ Real.sqrt ((2 : ℝ) ^ (j + 1)) := by
    apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
    simpa only [Real.sq_sqrt hp.le, show (2 : ℝ) ^ 2 = 4 by norm_num] using hp4
  have hH : 0 < farHeight h j :=
    mul_pos (Real.sqrt_pos.2 hp) hh
  have hsq : farHeight h j ^ 2 = (2 : ℝ) ^ (j + 1) * h ^ 2 := by
    unfold farHeight
    rw [mul_pow, Real.sq_sqrt hp.le]
  have htwo : 2 * h ≤ farHeight h j := mul_le_mul_of_nonneg_right hroot hh.le
  have hcube : 8 * h ^ 3 ≤ farHeight h j ^ 3 := by
    have hc := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * h) htwo 3
    nlinarith
  refine ⟨hH, hsq, htwo, ?_, ?_, ?_⟩
  · rw [hsq, pow_succ]
    field_simp [ne_of_gt hh, ne_of_gt (pow_pos (by norm_num : (0 : ℝ) < 2) j)]
    <;> ring
  · rw [hsq]
    field_simp [ne_of_gt hh, ne_of_gt hp]
    <;> ring
  · rw [div_div]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg n) (by positivity : 0 < h ^ 3 * 8)
      (by nlinarith [hcube])

theorem farLayer_subset_cutoff (n : ℕ) (hn : 0 < n) (h : ℝ) (hh : 0 < h)
    (j : ℕ) (hj : 1 ≤ j) :
    farLayer n h j ⊆ cutoffBox n (farHeight h j) ∩
      {a | (2 : ℝ) ^ j * (n : ℝ) ≤ Shao.energy a} := by
  intro a ha
  obtain ⟨hH, hHsq, _, _, _, _⟩ := farHeight_identities n h hh j hj
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnS : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hR0 : 0 ≤ h / Real.sqrt (n : ℝ) * Real.sqrt (Shao.energy a) := by positivity
  have hRsq : (h / Real.sqrt (n : ℝ) * Real.sqrt (Shao.energy a)) ^ 2 =
      h ^ 2 * Shao.energy a / (n : ℝ) := by
    rw [mul_pow, div_pow, Real.sq_sqrt hnR.le, Real.sq_sqrt (Shao.energy_nonneg a)]
    ring
  have hsq : (h / Real.sqrt (n : ℝ) * Real.sqrt (Shao.energy a)) ^ 2 ≤
      farHeight h j ^ 2 := by
    rw [hRsq, hHsq]
    apply (div_le_iff₀ hnR).2
    have hm := mul_le_mul_of_nonneg_left ha.2.2.le (sq_nonneg h)
    nlinarith
  have hR : h / Real.sqrt (n : ℝ) * Real.sqrt (Shao.energy a) ≤ farHeight h j :=
    (sq_le_sq₀ hR0 hH.le).mp hsq
  have hstrip : a ∈ Shao.closedStrip (farHeight h j) := by
    intro k hk
    exact (ha.1 k hk).trans hR
  exact ⟨fun i => Shao.abs_coordinate_le_two_mul_of_mem_closedStrip a _ hstrip i, ha.2.1⟩

theorem farLayer_markov_difference (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 0 < n) (h s : ℝ) (hh : 0 < h) (hs : 0 < s)
    (j : ℕ) (hj : 1 ≤ j) :
    (Measure.pi (fun _ : Fin n => ν)).real (farLayer n h j) ≤
      (energyNormalizer ν (farHeight h j) s ^ n -
        energyNormalizer ν (farHeight h j) 0 ^ n) /
      (Real.exp (s * ((2 : ℝ) ^ j * (n : ℝ)) / farHeight h j ^ 2) - 1) := by
  exact cutoff_energy_markov_difference ν n (farHeight h j) s
    ((2 : ℝ) ^ j * (n : ℝ)) (farHeight_identities n h hh j hj).1 hs
    (mul_pos (by positivity) (Nat.cast_pos.mpr hn)) (farLayer n h j)
    (measurableSet_farLayer n h j) (farLayer_subset_cutoff n hn h hh j hj)

theorem farLayer_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 0 < n) (h s : ℝ) (hh : 1 ≤ h) (hs : 0 < s)
    (ht : Real.log 2 ≤ s * ((n : ℝ) / h ^ 2) / 2)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) (j : ℕ) (hj : 1 ≤ j) :
    (Measure.pi (fun _ : Fin n => ν)).real (farLayer n h j) ≤
      2 * farScalarBound s (∫ x : ℝ, |x| ^ 3 ∂ν) n h / (2 : ℝ) ^ (j + 1) := by
  let H := farHeight h j
  let β := ∫ x : ℝ, |x| ^ 3 ∂ν
  let D := energyNormalizerErrorConstant s * β
  let t := (n : ℝ) / h ^ 2
  let r := (n : ℝ) / h ^ 3
  let C := farDifferenceConstant s
  let a := energyNormalizer ν H s
  let b := energyNormalizer ν H 0
  let u := s / H ^ 2 + D / H ^ 3
  let y := s * t / 2
  have hh0 : 0 < h := by linarith
  obtain ⟨hH0, hHsq, hH2, hq, hratio, hcuberatio⟩ := farHeight_identities n h hh0 j hj
  have hH1 : 1 ≤ H := by dsimp [H]; linarith
  have hβ0 : 0 ≤ β := integral_nonneg fun x => pow_nonneg (abs_nonneg x) 3
  have hD0 : 0 ≤ D := mul_nonneg (energyNormalizerErrorConstant_nonneg s hs.le) hβ0
  have hC0 : 0 ≤ C := by dsimp [C, farDifferenceConstant]; positivity
  have ht0 : 0 < t := div_pos (Nat.cast_pos.mpr hn) (sq_pos_of_pos hh0)
  have hr0 : 0 ≤ r := div_nonneg (Nat.cast_nonneg n) (by positivity)
  have hδ := cutoff_normalizer_difference_bound ν H s hH0 hs.le hSq hsecond
  have hb0 : 0 ≤ b := integral_nonneg (energyWeight_nonneg H 0)
  have hba : b ≤ a := sub_nonneg.mp hδ.1
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have ha : a ≤ 1 + u := by
    have hu := cutoff_normalizer_first_order_upper ν H s hH1 hs.le hSq hCube hsecond
    dsimp [a, u, D, β]
    linarith
  have hnu : (n : ℝ) * u = s * ((n : ℝ) / H ^ 2) + D * ((n : ℝ) / H ^ 3) := by
    dsimp [u]
    ring
  have hnumbound : a ^ n - b ^ n ≤
      C * ((n : ℝ) / H ^ 2) *
        Real.exp (s * ((n : ℝ) / H ^ 2) + D * ((n : ℝ) / H ^ 3)) := by
    calc
      _ ≤ (n : ℝ) * (a - b) * Real.exp ((n : ℝ) * u) :=
        power_difference_bound a b u n hn hb0 hba hu0 ha
      _ ≤ (n : ℝ) * (C / H ^ 2) * Real.exp ((n : ℝ) * u) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hδ.2 (Nat.cast_nonneg n)) (Real.exp_nonneg _)
      _ = _ := by rw [hnu]; ring
  have he2 : 2 ≤ Real.exp y := by
    calc
      _ = Real.exp (Real.log 2) := (Real.exp_log (by norm_num : (0 : ℝ) < 2)).symm
      _ ≤ _ := Real.exp_le_exp.mpr ht
  have hden0 : 0 < Real.exp y - 1 := by linarith
  have hdenhalf : Real.exp y / 2 ≤ Real.exp y - 1 := by linarith
  have hinv : 1 / (Real.exp y - 1) ≤ 2 * Real.exp (-y) := by
    calc
      _ ≤ 1 / (Real.exp y / 2) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hdenhalf
      _ = _ := by rw [Real.exp_neg]; field_simp <;> ring
  have hp4 : (4 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
    have hp := (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (by omega : 2 ≤ j + 1))
    norm_num at hp
    exact hp
  have hfirst : s * ((n : ℝ) / H ^ 2) ≤ s * t / 4 := by
    rw [hratio]
    change s * (t / (2 : ℝ) ^ (j + 1)) ≤ s * t / 4
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_left (mul_nonneg hs.le ht0.le) (by norm_num) hp4
  have hthird : D * ((n : ℝ) / H ^ 3) ≤ D * r / 8 := by
    have he := mul_le_mul_of_nonneg_left hcuberatio hD0
    simpa only [r, mul_div_assoc] using he
  have hexp : s * ((n : ℝ) / H ^ 2) + D * ((n : ℝ) / H ^ 3) - y ≤
      -s * t / 4 + D * r / 8 := by
    dsimp [y]
    linarith
  have harg : s * ((2 : ℝ) ^ j * (n : ℝ)) / H ^ 2 = y := by
    calc
      _ = s * ((2 : ℝ) ^ j * (n : ℝ) / H ^ 2) := by ring
      _ = _ := by rw [hq]; dsimp [y, t]; ring
  have hpre : 0 ≤ 2 * C * t / (2 : ℝ) ^ (j + 1) := by positivity
  have hbound := farLayer_markov_difference ν n hn h s hh0 hs j hj
  change (Measure.pi (fun _ : Fin n => ν)).real (farLayer n h j) ≤
    (a ^ n - b ^ n) / (Real.exp (s * ((2 : ℝ) ^ j * (n : ℝ)) / H ^ 2) - 1) at hbound
  rw [harg] at hbound
  calc
    _ ≤ (a ^ n - b ^ n) / (Real.exp y - 1) := hbound
    _ = (a ^ n - b ^ n) * (1 / (Real.exp y - 1)) := by ring
    _ ≤ (C * ((n : ℝ) / H ^ 2) *
        Real.exp (s * ((n : ℝ) / H ^ 2) + D * ((n : ℝ) / H ^ 3))) *
        (2 * Real.exp (-y)) :=
      mul_le_mul hnumbound hinv (by positivity) (by positivity)
    _ = (2 * C * t / (2 : ℝ) ^ (j + 1)) *
        Real.exp (s * ((n : ℝ) / H ^ 2) + D * ((n : ℝ) / H ^ 3) - y) := by
      rw [Real.exp_sub, hratio]
      rw [Real.exp_neg]
      change (C * (t / (2 : ℝ) ^ (j + 1)) *
        Real.exp (s * (t / (2 : ℝ) ^ (j + 1)) + D * ((n : ℝ) / H ^ 3))) *
          (2 * (Real.exp y)⁻¹) = _
      ring
    _ ≤ (2 * C * t / (2 : ℝ) ^ (j + 1)) * Real.exp (-s * t / 4 + D * r / 8) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hpre
    _ = _ := by dsimp [farScalarBound, C, t, r, D, β]; ring

theorem dyadic_energy_cover (n : ℕ) (hn : 0 < n) (h : ℝ) :
    randomDenominatorEvent n h ∩ {a | 2 * (n : ℝ) ≤ Shao.energy a} =
      ⋃ k : ℕ, farLayer n h (k + 1) := by
  classical
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hgrow (k : ℕ) : (k : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [pow_succ]
      push_cast
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k, (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
  ext a
  constructor
  · intro ha
    obtain ⟨N, hN⟩ := exists_nat_gt (Shao.energy a / (n : ℝ))
    have hpowN : (N : ℝ) ≤ (2 : ℝ) ^ (N + 1) := by
      have hg := hgrow (N + 1)
      push_cast at hg
      linarith
    have hex : ∃ j : ℕ, Shao.energy a < (2 : ℝ) ^ (j + 1) * (n : ℝ) := by
      refine ⟨N, ?_⟩
      exact ((div_lt_iff₀ hnR).1 hN).trans_le
        (mul_le_mul_of_nonneg_right hpowN hnR.le)
    let j := Nat.find hex
    have hupper : Shao.energy a < (2 : ℝ) ^ (j + 1) * (n : ℝ) := Nat.find_spec hex
    have hj0 : j ≠ 0 := by
      intro hz
      rw [hz] at hupper
      norm_num at hupper
      have hlower : 2 * (n : ℝ) ≤ Shao.energy a := ha.2
      exact (not_lt_of_ge hlower) hupper
    have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
    have hpred : j - 1 + 1 = j := Nat.sub_add_cancel hj1
    have hmin : ¬ Shao.energy a < (2 : ℝ) ^ (j - 1 + 1) * (n : ℝ) :=
      Nat.find_min hex (Nat.sub_lt (Nat.zero_lt_of_ne_zero hj0) (by decide : 0 < 1))
    have hlower : (2 : ℝ) ^ j * (n : ℝ) ≤ Shao.energy a := by
      exact le_of_not_gt (by simpa only [hpred] using hmin)
    apply Set.mem_iUnion.mpr
    refine ⟨j - 1, ?_⟩
    change a ∈ farLayer n h (j - 1 + 1)
    rw [hpred]
    exact ⟨ha.1, hlower, hupper⟩
  · intro ha
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp ha
    have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
      simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by omega : 1 ≤ k + 1)
    exact ⟨hk.1, (mul_le_mul_of_nonneg_right htwo hnR.le).trans hk.2.1⟩

private theorem shifted_geometric_summable :
    Summable (fun k : ℕ => (1 : ℝ) / (2 : ℝ) ^ (k + 2)) := by
  have heq (k : ℕ) : (1 : ℝ) / (2 : ℝ) ^ (k + 2) =
      (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ k := by
    simp only [pow_add, div_eq_mul_inv, mul_inv_rev, inv_pow, one_mul]
    norm_num <;> ring
  simp_rw [heq]
  exact (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left _

private theorem shifted_geometric_tsum :
    (∑' k : ℕ, (1 : ℝ) / (2 : ℝ) ^ (k + 2)) = 1 / 2 := by
  have heq (k : ℕ) : (1 : ℝ) / (2 : ℝ) ^ (k + 2) =
      (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ k := by
    simp only [pow_add, div_eq_mul_inv, mul_inv_rev, inv_pow, one_mul]
    norm_num <;> ring
  simp_rw [heq]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
  norm_num

private theorem farLayer_real_summable (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 0 < n) (h s : ℝ) (hh : 1 ≤ h) (hs : 0 < s)
    (ht : Real.log 2 ≤ s * ((n : ℝ) / h ^ 2) / 2)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    Summable (fun k : ℕ =>
      (Measure.pi (fun _ : Fin n => ν)).real (farLayer n h (k + 1))) := by
  have hmajor : Summable (fun k : ℕ =>
      2 * farScalarBound s (∫ x : ℝ, |x| ^ 3 ∂ν) n h / (2 : ℝ) ^ (k + 2)) := by
    convert shifted_geometric_summable.mul_left
      (2 * farScalarBound s (∫ x : ℝ, |x| ^ 3 ∂ν) n h) using 1
    funext k
    ring
  exact Summable.of_nonneg_of_le (fun _ => measureReal_nonneg)
    (fun k => by simpa only [Nat.add_assoc] using
      farLayer_bound ν n hn h s hh hs ht hSq hCube hsecond (k + 1) (by omega)) hmajor

theorem far_tail_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 0 < n) (h s : ℝ) (hh : 1 ≤ h) (hs : 0 < s)
    (ht : Real.log 2 ≤ s * ((n : ℝ) / h ^ 2) / 2)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    (Measure.pi (fun _ : Fin n => ν)).real
        (randomDenominatorEvent n h ∩ {a | 2 * (n : ℝ) ≤ Shao.energy a}) ≤
      farScalarBound s (∫ x : ℝ, |x| ^ 3 ∂ν) n h := by
  let B := farScalarBound s (∫ x : ℝ, |x| ^ 3 ∂ν) n h
  let b : ℕ → ℝ := fun k => 2 * B / (2 : ℝ) ^ (k + 2)
  have hB : 0 ≤ B := by dsimp [B, farScalarBound, farDifferenceConstant]; positivity
  have hb0 (k : ℕ) : 0 ≤ b k := by dsimp [b]; positivity
  have hbs : Summable b := by
    convert shifted_geometric_summable.mul_left (2 * B) using 1
    funext k
    dsimp [b]
    ring
  have hsum : (∑' k, b k) = B := by
    have heq (k : ℕ) : b k = (2 * B) * ((1 : ℝ) / (2 : ℝ) ^ (k + 2)) := by
      dsimp [b]
      ring
    simp_rw [heq]
    rw [tsum_mul_left, shifted_geometric_tsum]
    ring
  have hmass : (Measure.pi (fun _ : Fin n => ν))
      (randomDenominatorEvent n h ∩ {a | 2 * (n : ℝ) ≤ Shao.energy a}) ≤ ENNReal.ofReal B := by
    calc
      _ ≤ ∑' k : ℕ, (Measure.pi (fun _ : Fin n => ν)) (farLayer n h (k + 1)) := by
        rw [dyadic_energy_cover n hn h]
        exact measure_iUnion_le _
      _ ≤ ∑' k : ℕ, ENNReal.ofReal (b k) := ENNReal.tsum_le_tsum (fun k => by
        have hb := ENNReal.ofReal_le_ofReal
          (farLayer_bound ν n hn h s hh hs ht hSq hCube hsecond (k + 1) (by omega))
        simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _),
          b, B, Nat.add_assoc, Nat.reduceAdd] using hb)
      _ = ENNReal.ofReal (∑' k : ℕ, b k) :=
        (ENNReal.ofReal_tsum_of_nonneg hb0 hbs).symm
      _ = _ := by rw [hsum]
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  simpa only [measureReal_def, ENNReal.toReal_ofReal hB] using hb

theorem farMainTerm_pos (n : ℕ) (h : ℝ) : 0 < farMainTerm n h := by
  unfold farMainTerm
  positivity

private theorem time_mul_exp_neg_tendsto (t : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (ht : Tendsto t atTop atTop) :
    Tendsto (fun k => t k * Real.exp (-δ * t k)) atTop (𝓝 0) := by
  have hu : Tendsto (fun k => (4 / δ ^ 2) * (t k)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using (tendsto_inv_atTop_zero.comp ht).const_mul (4 / δ ^ 2)
  apply squeeze_zero' ?_ ?_ hu
  · filter_upwards [ht.eventually_ge_atTop 0] with k hk
    exact mul_nonneg hk (Real.exp_nonneg _)
  · filter_upwards [ht.eventually_ge_atTop 1] with k hk
    have htk : 0 < t k := by linarith
    have he : δ * t k / 2 ≤ Real.exp (δ * t k / 2) := by
      linarith [Real.add_one_le_exp (δ * t k / 2)]
    have hsq : δ ^ 2 * t k ^ 2 / 4 ≤ Real.exp (δ * t k) := by
      calc
        _ = (δ * t k / 2) ^ 2 := by ring
        _ ≤ Real.exp (δ * t k / 2) ^ 2 :=
          pow_le_pow_left₀ (by positivity) he 2
        _ = _ := by rw [← Real.exp_nat_mul]; congr 1 <;> norm_num <;> ring
    calc
      _ = t k / Real.exp (δ * t k) := by
        rw [show -δ * t k = -(δ * t k) by ring, Real.exp_neg]
        ring
      _ ≤ t k / (δ ^ 2 * t k ^ 2 / 4) :=
        div_le_div_of_nonneg_left htk.le (by positivity) hsq
      _ = _ := by field_simp [ne_of_gt hδ, ne_of_gt htk] <;> ring

private theorem eventual_finite_conditions (n : ℕ → ℕ) (h : ℕ → ℝ) (s : ℝ)
    (hs : 0 < s) (hh : Tendsto h atTop atTop)
    (ht : Tendsto (fun k => (n k : ℝ) / h k ^ 2) atTop atTop) :
    ∀ᶠ k in atTop, 0 < n k ∧ 1 ≤ h k ∧
      Real.log 2 ≤ s * ((n k : ℝ) / h k ^ 2) / 2 := by
  filter_upwards [hh.eventually_ge_atTop 1,
    ht.eventually_ge_atTop (max 1 (2 * Real.log 2 / s))] with k hk htk
  have ht1 : 1 ≤ (n k : ℝ) / h k ^ 2 := (le_max_left _ _).trans htk
  have hn : 0 < n k := by
    by_contra hn
    have hz : n k = 0 := Nat.eq_zero_of_not_pos hn
    simp only [hz, Nat.cast_zero, zero_div] at ht1
    linarith
  refine ⟨hn, hk, ?_⟩
  have hq : 2 * Real.log 2 / s ≤ (n k : ℝ) / h k ^ 2 := (le_max_right _ _).trans htk
  have hm := (div_le_iff₀ hs).1 hq
  nlinarith

theorem far_tail_relative_tendsto_zero (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (n : ℕ → ℕ) (h : ℕ → ℝ) (s : ℝ) (hs : Real.pi ^ 2 / 2 < s)
    (hh : Tendsto h atTop atTop)
    (ht : Tendsto (fun k => (n k : ℝ) / h k ^ 2) atTop atTop)
    (hr : Tendsto (fun k => (n k : ℝ) / h k ^ 3) atTop (𝓝 0)) :
    Tendsto (fun k =>
      (Measure.pi (fun _ : Fin (n k) => ν)).real
          (randomDenominatorEvent (n k) (h k) ∩
            {a | 2 * (n k : ℝ) ≤ Shao.energy a}) /
        farMainTerm (n k) (h k)) atTop (𝓝 0) := by
  let δ := s / 4 - Real.pi ^ 2 / 8
  let D := energyNormalizerErrorConstant s * (∫ x : ℝ, |x| ^ 3 ∂ν)
  let C := farDifferenceConstant s
  let t : ℕ → ℝ := fun k => (n k : ℝ) / h k ^ 2
  let r : ℕ → ℝ := fun k => (n k : ℝ) / h k ^ 3
  have hs0 : 0 < s := by nlinarith [sq_nonneg Real.pi]
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have htime := time_mul_exp_neg_tendsto t δ hδ ht
  have hc0 : Tendsto (fun k => (D / 8) * r k) atTop (𝓝 0) := by
    simpa only [mul_zero] using hr.const_mul (D / 8)
  have hce : Tendsto (fun k => Real.exp ((D / 8) * r k)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp hc0
  have hmajor : Tendsto
      (fun k => (C * Real.pi / 4) * (t k * Real.exp (-δ * t k)) *
        Real.exp ((D / 8) * r k)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (htime.const_mul (C * Real.pi / 4)).mul hce
  have hratio (k : ℕ) : farScalarBound s (∫ x : ℝ, |x| ^ 3 ∂ν) (n k) (h k) /
        farMainTerm (n k) (h k) =
      (C * Real.pi / 4) * (t k * Real.exp (-δ * t k)) *
        Real.exp ((D / 8) * r k) := by
    have he : Real.exp (-s * t k / 4 + D * r k / 8) =
        Real.exp (-(Real.pi ^ 2 / 8) * t k) * Real.exp (-δ * t k) *
          Real.exp ((D / 8) * r k) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [δ]
      ring
    change (C * t k * Real.exp (-s * t k / 4 + D * r k / 8)) /
      ((4 / Real.pi) * Real.exp (-(Real.pi ^ 2 / 8) * t k)) = _
    rw [he]
    field_simp [ne_of_gt Real.pi_pos,
      ne_of_gt (Real.exp_pos (-(Real.pi ^ 2 / 8) * t k))]
    <;> ring
  apply squeeze_zero' (Eventually.of_forall fun k =>
    div_nonneg measureReal_nonneg (farMainTerm_pos (n k) (h k)).le) ?_ hmajor
  filter_upwards [eventual_finite_conditions n h s hs0 hh ht] with k hk
  have hb := div_le_div_of_nonneg_right
    (far_tail_bound ν (n k) hk.1 (h k) s hk.2.1 hs0 hk.2.2 hSq hCube hsecond)
    (farMainTerm_pos (n k) (h k)).le
  rwa [hratio k] at hb

end Shao.OQ4.RandomDenominatorFarTail
