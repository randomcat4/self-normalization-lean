import Shao.OQ5.P53.SparseLabelLaw

/-!
# Moments of the fixed sparse coefficients under the actual label law

The complete alpha/x/N data are fixed before every real moment order and
exponential parameter. Genuine summability supplies actual L1 before either
integral conclusion. Positive levels and the residual zero atom stay separate.
-/

set_option autoImplicit false

open Filter MeasureTheory
open scoped BigOperators Topology

namespace Shao.OQ5.P53

noncomputable section

private theorem moments_dyadic_nonneg (j : ℕ) : 0 ≤ sparseDyadic j := by
  exact inv_nonneg.mpr (pow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) j)

private theorem moments_amplitude_nonneg (α : ℝ) (x : ℕ → ℝ)
    (N : ℕ → ℕ) (j : ℕ) : 0 ≤ sparseLevelAmplitude α x N j := by
  unfold sparseLevelAmplitude
  split_ifs
  · exact le_rfl
  · unfold sparseAmplitude
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.sqrt_nonneg _)

private theorem moments_global_rpow_exp_bound (α q : ℝ)
    (hα : 0 < α) (hq : 0 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      t ^ q * Real.exp (-(t ^ α)) ≤ C := by
  have hlim : Tendsto (fun u : ℝ => u ^ (q / α) * Real.exp (-u))
      atTop (nhds 0) := by
    simpa only [neg_mul, one_mul] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (q / α) 1 (by norm_num))
  have hevent : ∀ᶠ u : ℝ in atTop, u ^ (q / α) * Real.exp (-u) < 1 :=
    hlim.eventually_lt
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1))
      (by norm_num)
  rcases Filter.eventually_atTop.mp hevent with ⟨A, hA⟩
  let D : ℝ := max A 1
  let C : ℝ := max 1 (D ^ (q / α))
  have hD : 0 ≤ D := le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right A 1)
  refine ⟨C, le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _), ?_⟩
  intro t ht
  let u : ℝ := t ^ α
  have hu : 0 ≤ u := Real.rpow_nonneg ht α
  have hpower : u ^ (q / α) = t ^ q := by
    change (t ^ α) ^ (q / α) = t ^ q
    rw [← Real.rpow_mul ht]
    congr 1
    calc
      α * (q / α) = (α / α) * q := by ring
      _ = q := by rw [div_self (ne_of_gt hα), one_mul]
  change t ^ q * Real.exp (-u) ≤ C
  rw [← hpower]
  by_cases huD : u ≤ D
  · calc
      u ^ (q / α) * Real.exp (-u) ≤ D ^ (q / α) * 1 :=
        mul_le_mul (Real.rpow_le_rpow hu huD (div_pos hq hα).le)
          (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu))
          (Real.exp_pos _).le (Real.rpow_nonneg hD _)
      _ = D ^ (q / α) := mul_one _
      _ ≤ C := le_max_right _ _
  · have hAu : A ≤ u := le_trans (le_max_left A 1) (lt_of_not_ge huD).le
    exact le_trans (hA u hAu).le (le_max_left _ _)

private theorem moments_dyadic_hasSum (j : ℕ) :
    HasSum (fun k : ℕ => sparseDyadic (k + j + 1)) (sparseDyadic j) := by
  have hfun : (fun k : ℕ => sparseDyadic (k + j + 1)) =
      (fun k : ℕ => sparseDyadic j / 2 / (2 : ℝ) ^ k) := by
    funext k
    simp only [sparseDyadic, pow_add, pow_one, mul_inv_rev, div_eq_mul_inv]
    ring
  rw [hfun]
  exact hasSum_geometric_two' (sparseDyadic j)

private theorem moments_positive_geometric_hasSum :
    HasSum (fun k : ℕ => sparseDyadic (k + 3)) (1 / 4 : ℝ) := by
  have hvalue : sparseDyadic 2 = (1 / 4 : ℝ) := by norm_num [sparseDyadic]
  simpa only [Nat.add_assoc, hvalue] using moments_dyadic_hasSum 2

private theorem moments_shift_bounds (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (hN : SparseSelectionCore α x N) (j : ℕ) :
    0 ≤ sparseLevelShift α x N j ∧
      sparseLevelShift α x N j ≤ 2 * sparseLevelAmplitude α x N j := by
  cases j with
  | zero => simp only [sparseLevelShift, sparseLevelAmplitude, ite_true, mul_zero, le_refl, and_self]
  | succ m =>
    rcases hN.2.2 m with ⟨_hnext, hn4, _hx, _hslow, ht, hd, _hlower,
      htupper, _hdupper, _hcurrent, _hprevious⟩
    have hn4r : (4 : ℝ) ≤ (N (m + 1) : ℝ) := by exact_mod_cast hn4
    have hden : 0 < (N (m + 1) : ℝ) - 2 := by linarith
    have hfactor : (N (m + 1) : ℝ) ≤ 2 * ((N (m + 1) : ℝ) - 2) := by linarith
    have hsq := mul_le_mul_of_nonneg_left htupper ht.le
    have hupper := mul_le_mul_of_nonneg_left hfactor ht.le
    have hform : sparseLevelShift α x N (m + 1) =
        sparseLevelAmplitude α x N (m + 1) ^ 2 / ((N (m + 1) : ℝ) - 2) := by
      simp only [sparseLevelShift, sparseLevelAmplitude, Nat.add_one_ne_zero, ite_false, sparseShift]
    refine ⟨hd.le, ?_⟩
    rw [hform]
    apply (div_le_iff₀ hden).mpr
    nlinarith [hsq, hupper]

private theorem moments_positive_exp_bound (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (τ : ℝ) (hτ : τ ≤ 1) (j : ℕ) (hj : 1 ≤ j) :
    sparseLabelMass α x N j *
      Real.exp (τ * |sparseLevelAmplitude α x N j| ^ α) ≤ sparseDyadic (j + 2) := by
  have hj0 : j ≠ 0 := by omega
  have ht := moments_amplitude_nonneg α x N j
  have hu := Real.rpow_nonneg ht α
  have he : -(sparseLevelAmplitude α x N j ^ α) +
      τ * sparseLevelAmplitude α x N j ^ α =
      (τ - 1) * sparseLevelAmplitude α x N j ^ α := by ring
  rw [sparseLabelMass_eq_positiveMass α x N j hj, sparsePositiveMass,
    ite_eq_right hj0, abs_of_nonneg ht]
  calc
    sparseDyadic (j + 2) * Real.exp (-(sparseLevelAmplitude α x N j ^ α)) *
        Real.exp (τ * sparseLevelAmplitude α x N j ^ α) =
        sparseDyadic (j + 2) * Real.exp (-(sparseLevelAmplitude α x N j ^ α) +
          τ * sparseLevelAmplitude α x N j ^ α) := by rw [Real.exp_add, mul_assoc]
    _ = sparseDyadic (j + 2) * Real.exp ((τ - 1) * sparseLevelAmplitude α x N j ^ α) := by rw [he]
    _ ≤ sparseDyadic (j + 2) * 1 :=
      mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hτ) hu))
        (moments_dyadic_nonneg _)
    _ = sparseDyadic (j + 2) := mul_one _

private theorem moments_integrable_of_nonneg (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j)
    (hs : Summable (fun j : ℕ => sparseLabelMass α x N j * f j)) :
    Integrable f (sparseLabelMeasure α x N) := by
  apply (integrable_sparseLabelMeasure_iff α x N f).mpr
  have hfun : (fun j : ℕ => sparseLabelMass α x N j * ‖f j‖) =
      (fun j : ℕ => sparseLabelMass α x N j * f j) := by
    funext j
    rw [Real.norm_eq_abs, abs_of_nonneg (hf j)]
  rw [hfun]
  exact hs

theorem summable_sparseLabelMass_amplitude_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α →
  ∀ q : ℝ, 0 < q →
  Summable (fun j : ℕ => sparseLabelMass α x N j * |sparseLevelAmplitude α x N j| ^ q) := by
  intro α x N hα q hq
  rcases moments_global_rpow_exp_bound α q hα hq with ⟨C, hC, hbound⟩
  have hgeom : Summable (fun j : ℕ => sparseDyadic (j + 2)) := by
    simpa only [Nat.add_assoc] using (moments_dyadic_hasSum 1).summable
  have hmajor := hgeom.mul_left C
  refine Summable.of_nonneg_of_le
    (fun j => mul_nonneg (sparseLabelMass_nonneg α x N j)
      (Real.rpow_nonneg (abs_nonneg _) q)) ?_ hmajor
  intro j
  by_cases hj : j = 0
  · subst j
    simp only [sparseLevelAmplitude, ite_true, abs_zero,
      Real.zero_rpow (ne_of_gt hq), mul_zero]
    exact mul_nonneg hC (moments_dyadic_nonneg _)
  · have hj1 : 1 ≤ j := by omega
    have ht := moments_amplitude_nonneg α x N j
    rw [sparseLabelMass_eq_positiveMass α x N j hj1, sparsePositiveMass,
      ite_eq_right hj, abs_of_nonneg ht]
    calc
      sparseDyadic (j + 2) * Real.exp (-(sparseLevelAmplitude α x N j ^ α)) *
          sparseLevelAmplitude α x N j ^ q =
          sparseDyadic (j + 2) * (sparseLevelAmplitude α x N j ^ q *
            Real.exp (-(sparseLevelAmplitude α x N j ^ α))) := by ring
      _ ≤ sparseDyadic (j + 2) * C :=
        mul_le_mul_of_nonneg_left (hbound _ ht) (moments_dyadic_nonneg _)
      _ = C * sparseDyadic (j + 2) := mul_comm _ _

theorem summable_sparseLabelMass_shift_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → SparseSelectionCore α x N →
  ∀ q : ℝ, 0 < q →
  Summable (fun j : ℕ => sparseLabelMass α x N j * |sparseLevelShift α x N j| ^ q) := by
  intro α x N hα hN q hq
  have hmajor := (summable_sparseLabelMass_amplitude_rpow α x N hα q hq).mul_left
    ((2 : ℝ) ^ q)
  refine Summable.of_nonneg_of_le
    (fun j => mul_nonneg (sparseLabelMass_nonneg α x N j)
      (Real.rpow_nonneg (abs_nonneg _) q)) ?_ hmajor
  intro j
  rcases moments_shift_bounds α x N hN j with ⟨hd, hdt⟩
  have ht := moments_amplitude_nonneg α x N j
  have hp : |sparseLevelShift α x N j| ^ q ≤
      (2 : ℝ) ^ q * |sparseLevelAmplitude α x N j| ^ q := by
    rw [abs_of_nonneg hd, abs_of_nonneg ht]
    calc
      sparseLevelShift α x N j ^ q ≤ (2 * sparseLevelAmplitude α x N j) ^ q :=
        Real.rpow_le_rpow hd hdt hq.le
      _ = (2 : ℝ) ^ q * sparseLevelAmplitude α x N j ^ q :=
        Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) ht
  calc
    sparseLabelMass α x N j * |sparseLevelShift α x N j| ^ q ≤
        sparseLabelMass α x N j * ((2 : ℝ) ^ q * |sparseLevelAmplitude α x N j| ^ q) :=
      mul_le_mul_of_nonneg_left hp (sparseLabelMass_nonneg α x N j)
    _ = (2 : ℝ) ^ q * (sparseLabelMass α x N j * |sparseLevelAmplitude α x N j| ^ q) := by ring

theorem summable_sparseLabelMass_amplitude_exp :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α →
  ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
  Summable (fun j : ℕ => sparseLabelMass α x N j *
    Real.exp (τ * |sparseLevelAmplitude α x N j| ^ α)) := by
  intro α x N _hα τ _hτ0 hτ1
  have hshift : Summable (fun k : ℕ => sparseLabelMass α x N (k + 1) *
      Real.exp (τ * |sparseLevelAmplitude α x N (k + 1)| ^ α)) := by
    refine Summable.of_nonneg_of_le
      (fun k => mul_nonneg (sparseLabelMass_nonneg α x N (k + 1)) (Real.exp_pos _).le)
      ?_ moments_positive_geometric_hasSum.summable
    intro k
    simpa only [Nat.add_assoc] using
      moments_positive_exp_bound α x N τ hτ1 (k + 1) (by omega)
  exact (summable_nat_add_iff 1).mp hshift

theorem sparseLabelMass_amplitude_exp_tsum_le :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α →
  ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
  (∑' j : ℕ, sparseLabelMass α x N j *
    Real.exp (τ * |sparseLevelAmplitude α x N j| ^ α)) ≤ (5 / 4 : ℝ) := by
  intro α x N hα τ hτ0 hτ1
  have hs := summable_sparseLabelMass_amplitude_exp α x N hα τ hτ0 hτ1
  have hshift := (summable_nat_add_iff 1).mpr hs
  have htail : (∑' k : ℕ, sparseLabelMass α x N (k + 1) *
      Real.exp (τ * |sparseLevelAmplitude α x N (k + 1)| ^ α)) ≤ (1 / 4 : ℝ) := by
    calc
      (∑' k : ℕ, sparseLabelMass α x N (k + 1) *
          Real.exp (τ * |sparseLevelAmplitude α x N (k + 1)| ^ α)) ≤
          ∑' k : ℕ, sparseDyadic (k + 3) :=
        hshift.tsum_le_tsum (fun k => by
          simpa only [Nat.add_assoc] using
            moments_positive_exp_bound α x N τ hτ1 (k + 1) (by omega))
          moments_positive_geometric_hasSum.summable
      _ = 1 / 4 := moments_positive_geometric_hasSum.tsum_eq
  have htzero : |sparseLevelAmplitude α x N 0| ^ α = 0 := by
    simpa only [sparseLevelAmplitude, ite_true, abs_zero] using
      (Real.zero_rpow (ne_of_gt hα))
  have hfzero : sparseLabelMass α x N 0 *
      Real.exp (τ * |sparseLevelAmplitude α x N 0| ^ α) = sparseLabelMass α x N 0 := by
    rw [htzero, mul_zero, Real.exp_zero, mul_one]
  have hpref : (∑ i ∈ Finset.range 1, sparseLabelMass α x N i *
      Real.exp (τ * |sparseLevelAmplitude α x N i| ^ α)) = sparseLabelMass α x N 0 := by
    simpa only [Finset.sum_range_one] using hfzero
  have hsplit := hs.sum_add_tsum_nat_add 1
  rw [hpref] at hsplit
  have hmzero : sparseLabelMass α x N 0 ≤ 1 := by
    change 1 - (∑' k : ℕ, sparsePositiveMass α x N k) ≤ 1
    linarith [(sparsePositiveMass_tsum_bounds α x N).1]
  calc
    (∑' j : ℕ, sparseLabelMass α x N j *
        Real.exp (τ * |sparseLevelAmplitude α x N j| ^ α)) =
        sparseLabelMass α x N 0 + ∑' k : ℕ, sparseLabelMass α x N (k + 1) *
          Real.exp (τ * |sparseLevelAmplitude α x N (k + 1)| ^ α) := hsplit.symm
    _ ≤ sparseLabelMass α x N 0 + 1 / 4 := by linarith only [htail]
    _ ≤ 5 / 4 := by linarith

theorem sparseLabelMass_amplitude_sq_tsum_pos :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → SparseSelectionCore α x N →
  0 < ∑' j : ℕ, sparseLabelMass α x N j * (sparseLevelAmplitude α x N j) ^ 2 := by
  intro α x N hα hN
  have hs := summable_sparseLabelMass_amplitude_rpow α x N hα 2 (by norm_num)
  have hfun : (fun j : ℕ => sparseLabelMass α x N j *
      |sparseLevelAmplitude α x N j| ^ (2 : ℝ)) =
      (fun j : ℕ => sparseLabelMass α x N j * sparseLevelAmplitude α x N j ^ 2) := by
    funext j
    rw [abs_of_nonneg (moments_amplitude_nonneg α x N j), Real.rpow_two]
  rw [hfun] at hs
  rcases hN.2.2 0 with ⟨_hnext, _hfour, _hx, _hslow, ht1, _hd, _hlower,
    _htupper, _hdupper, _hcurrent, _hprevious⟩
  have hm1 : 0 < sparseLabelMass α x N 1 := by
    rw [sparseLabelMass_eq_positiveMass α x N 1 (by decide)]
    exact sparsePositiveMass_pos α x N 1 (by decide)
  exact hs.tsum_pos
    (fun j => mul_nonneg (sparseLabelMass_nonneg α x N j) (sq_nonneg _)) 1
    (mul_pos hm1 (pow_pos ht1 2))

theorem integrable_sparseLabelMeasure_amplitude_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α →
  ∀ q : ℝ, 0 < q →
  Integrable (fun j : ℕ => |sparseLevelAmplitude α x N j| ^ q)
    (sparseLabelMeasure α x N) := by
  intro α x N hα q hq
  exact moments_integrable_of_nonneg α x N
    (fun j : ℕ => |sparseLevelAmplitude α x N j| ^ q)
    (fun j => Real.rpow_nonneg (abs_nonneg _) q)
    (summable_sparseLabelMass_amplitude_rpow α x N hα q hq)

theorem integrable_sparseLabelMeasure_shift_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → SparseSelectionCore α x N →
  ∀ q : ℝ, 0 < q →
  Integrable (fun j : ℕ => |sparseLevelShift α x N j| ^ q)
    (sparseLabelMeasure α x N) := by
  intro α x N hα hN q hq
  exact moments_integrable_of_nonneg α x N
    (fun j : ℕ => |sparseLevelShift α x N j| ^ q)
    (fun j => Real.rpow_nonneg (abs_nonneg _) q)
    (summable_sparseLabelMass_shift_rpow α x N hα hN q hq)

theorem integrable_sparseLabelMeasure_amplitude_exp :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α →
  ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
  Integrable (fun j : ℕ => Real.exp (τ * |sparseLevelAmplitude α x N j| ^ α))
    (sparseLabelMeasure α x N) := by
  intro α x N hα τ hτ0 hτ1
  exact moments_integrable_of_nonneg α x N
    (fun j : ℕ => Real.exp (τ * |sparseLevelAmplitude α x N j| ^ α))
    (fun j => (Real.exp_pos _).le)
    (summable_sparseLabelMass_amplitude_exp α x N hα τ hτ0 hτ1)

theorem integral_sparseLabelMeasure_amplitude_exp_le :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α →
  ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
  (∫ j, Real.exp (τ * |sparseLevelAmplitude α x N j| ^ α)
    ∂(sparseLabelMeasure α x N)) ≤ (5 / 4 : ℝ) := by
  intro α x N hα τ hτ0 hτ1
  have hf := integrable_sparseLabelMeasure_amplitude_exp α x N hα τ hτ0 hτ1
  rw [integral_sparseLabelMeasure α x N _ hf]
  exact sparseLabelMass_amplitude_exp_tsum_le α x N hα τ hτ0 hτ1

theorem integral_sparseLabelMeasure_amplitude_sq_pos :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → SparseSelectionCore α x N →
  0 < ∫ j, (sparseLevelAmplitude α x N j) ^ 2 ∂(sparseLabelMeasure α x N) := by
  intro α x N hα hN
  have hf := integrable_sparseLabelMeasure_amplitude_rpow α x N hα 2 (by norm_num)
  have hfun : (fun j : ℕ => |sparseLevelAmplitude α x N j| ^ (2 : ℝ)) =
      (fun j : ℕ => sparseLevelAmplitude α x N j ^ 2) := by
    funext j
    rw [abs_of_nonneg (moments_amplitude_nonneg α x N j), Real.rpow_two]
  rw [hfun] at hf
  rw [integral_sparseLabelMeasure α x N _ hf]
  exact sparseLabelMass_amplitude_sq_tsum_pos α x N hα hN

end

end Shao.OQ5.P53
