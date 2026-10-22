import Shao.OQ3.FiniteNormalSpan
import Shao.Probability.FiniteIID

/-!
# Actual sample boundary geometry and likelihood weight bounds

Source: current/oq3/proofs/r1/report.md, lines 400-408 and 495-510.
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U9a scope: cd6883e78387d9fbeb50d42bddcab9fc0a81955458d7228c53f98eb23e4c35c9.
-/

namespace Shao.OQ3

open MeasureTheory
open scoped BigOperators

noncomputable section

def normalDeviation (q : ℝ) {n : ℕ} (z : Shao.Path n) : ℝ :=
  (∑ i, normalValue (z i)) - (n : ℝ) * q

def tangentDeviation (q : ℝ) {n : ℕ} (z : Shao.Path n) : ℝ :=
  (∑ i, z i) - (n : ℝ) * q / 4

def sourceTail (q : ℝ) (n : ℕ) : Set (Shao.Path n) :=
  {z | 0 < Shao.energy z ∧
    Real.sqrt q / 4 * Real.sqrt ((n : ℝ) * Shao.energy z) ≤ ∑ i, z i}

theorem normalDeviation_eq_sum_energy (q : ℝ) (n : ℕ) (z : Shao.Path n) :
  normalDeviation q z = 8 * (∑ i, z i) - Shao.energy z - (n : ℝ) * q := by
  simp only [normalDeviation, normalValue, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Shao.energy]

theorem curved_sample_identity (q : ℝ) (n : ℕ) (z : Shao.Path n) :
  (∑ i, z i) ^ 2 - (n : ℝ) * (q / 16) * Shao.energy z =
    (n : ℝ) * q / 16 * normalDeviation q z + tangentDeviation q z ^ 2 := by
  rw [normalDeviation_eq_sum_energy]
  unfold tangentDeviation
  ring

theorem sourceTail_measurable (q : ℝ) (n : ℕ) :
  MeasurableSet (sourceTail q n) := by
  have he : Continuous (fun z : Shao.Path n => Shao.energy z) := by
    unfold Shao.energy
    fun_prop
  have hs : Continuous (fun z : Shao.Path n => ∑ i, z i) := by fun_prop
  have ht : Continuous (fun z : Shao.Path n =>
      Real.sqrt q / 4 * Real.sqrt ((n : ℝ) * Shao.energy z)) :=
    continuous_const.mul ((continuous_const.mul he).sqrt)
  exact (measurableSet_lt measurable_const he.measurable).inter
    (measurableSet_le ht.measurable hs.measurable)

theorem sourceTail_iff_curved (q : ℝ) (hq : 0 < q) (n : ℕ) (hn : 0 < n)
    (z : Shao.Path n) :
  z ∈ sourceTail q n ↔ 0 < Shao.energy z ∧ 0 < (∑ i, z i) ∧
    0 ≤ (n : ℝ) * q / 16 * normalDeviation q z + tangentDeviation q z ^ 2 := by
  let T : ℝ := Real.sqrt q / 4 * Real.sqrt ((n : ℝ) * Shao.energy z)
  change (0 < Shao.energy z ∧ T ≤ ∑ i, z i) ↔ _
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hE := Shao.energy_nonneg z
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hTsq : T ^ 2 = (n : ℝ) * (q / 16) * Shao.energy z := by
    dsimp [T]
    rw [mul_pow, div_pow, Real.sq_sqrt hq.le, Real.sq_sqrt (mul_nonneg hnR.le hE)]
    ring
  have hid := curved_sample_identity q n z
  constructor
  · rintro ⟨he, ht⟩
    have hTpos : 0 < T := by
      exact mul_pos (div_pos (Real.sqrt_pos_of_pos hq) (by norm_num))
        (Real.sqrt_pos_of_pos (mul_pos hnR he))
    have hS := hTpos.trans_le ht
    have hsq := (sq_le_sq₀ hT hS.le).mpr ht
    refine ⟨he, hS, ?_⟩
    nlinarith only [hsq, hTsq, hid]
  · rintro ⟨he, hS, hc⟩
    refine ⟨he, ?_⟩
    apply (sq_le_sq₀ hT hS.le).mp
    nlinarith only [hTsq, hid, hc]

theorem sourceTail_on_normal_layer (q : ℝ) (hq : 0 < q) (n : ℕ) (hn : 0 < n)
    (z : Shao.Path n) (d : ℝ) (hd : normalDeviation q z = d) :
  z ∈ sourceTail q n ↔ 0 < Shao.energy z ∧ 0 < (∑ i, z i) ∧
    -((n : ℝ) * q / 16 * d) ≤ tangentDeviation q z ^ 2 := by
  rw [sourceTail_iff_curved q hq n hn z, hd]
  constructor <;> rintro ⟨he, hS, hc⟩ <;> refine ⟨he, hS, ?_⟩ <;> linarith

theorem stage_sample_normal_layer (q : ℝ) (n J : ℕ) (z : Shao.Path n)
    (hz : ∀ i, z i ∈ Set.range (fun j : Fin 4 ⊕ Fin J =>
      stageAtom (fun k : Fin J => addedAtom k.val) j)) :
  ∃ k : ℤ, normalDeviation q z = dyadicMesh J * (k : ℝ) - (n : ℝ) * q := by
  classical
  have hi (i : Fin n) : ∃ k : ℤ, normalValue (z i) = dyadicMesh J * (k : ℝ) := by
    obtain ⟨j, hj⟩ := hz i
    rw [← hj]
    exact stageAtom_normalValue_lattice J j
  choose k hk using hi
  refine ⟨∑ i, k i, ?_⟩
  unfold normalDeviation
  congr 1
  rw [Int.cast_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => hk i)

theorem fixedAtom_normalValue_lower (i : AtomicIndex) :
  -9 ≤ normalValue (fixedAtom i) := by
  cases i with
  | inl i =>
    change -9 ≤ normalValue (baseAtom i)
    rw [congrFun normalValue_baseAtom i]
    fin_cases i <;> norm_num
  | inr j =>
    change -9 ≤ normalValue (addedAtom j)
    rw [addedAtom_normalValue]
    have hmesh : 0 < dyadicMesh (j + 1) := by unfold dyadicMesh; positivity
    linarith

theorem atomicMeasure_ae_normalValue_lower (w : AtomicIndex → ℝ) :
  ∀ᵐ x ∂atomicMeasure w, -9 ≤ normalValue x := by
  filter_upwards [atomicMeasure_ae_range w] with x hx
  obtain ⟨i, rfl⟩ := hx
  exact fixedAtom_normalValue_lower i

theorem originalMeasure_ae_normalValue_lower (ell : ℝ) (w : AtomicIndex → ℝ) :
  ∀ᵐ x ∂originalMeasure ell w, -9 ≤ normalValue x := by
  exact (tilted_absolutelyContinuous (atomicMeasure w)
    (fun x => -ell * normalValue x)).ae_le (atomicMeasure_ae_normalValue_lower w)

theorem normal_likelihood_weight_bound (ell q : ℝ) (hell : 0 ≤ ell) (hq : q ≤ 2)
    (n : ℕ) (z : Shao.Path n) (hY : ∀ i, -9 ≤ normalValue (z i)) :
  Real.exp (-ell * normalDeviation q z) ≤ Real.exp (11 * ell * (n : ℝ)) := by
  have hsum : -(9 : ℝ) * (n : ℝ) ≤ ∑ i, normalValue (z i) := by
    calc
      _ = ∑ _ : Fin n, (-9 : ℝ) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hY i)
  have hnq : (n : ℝ) * q ≤ (n : ℝ) * 2 :=
    mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg n)
  have hd : -11 * (n : ℝ) ≤ normalDeviation q z := by
    unfold normalDeviation
    linarith
  have hm := mul_le_mul_of_nonneg_left hd hell
  apply Real.exp_le_exp.mpr
  nlinarith only [hm]

theorem iid_normal_likelihood_ae_bound (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (ell q : ℝ) (hell : 0 ≤ ell) (hq : q ≤ 2)
    (hY : ∀ᵐ x ∂mu, -9 ≤ normalValue x) (n : ℕ) :
  ∀ᵐ z ∂Measure.pi (fun _ : Fin n => mu),
    Real.exp (-ell * normalDeviation q z) ≤ Real.exp (11 * ell * (n : ℝ)) := by
  have hcoords (i : Fin n) : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => mu),
      -9 ≤ normalValue (z i) :=
    (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => mu) (i := i)).eventually hY
  have hall : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => mu),
      ∀ i, -9 ≤ normalValue (z i) := ae_all_iff.mpr hcoords
  filter_upwards [hall] with z hz
  exact normal_likelihood_weight_bound ell q hell hq n z hz

theorem source_atomic_iid_likelihood_ae_bound (q : ℝ) (hq : q < 103 / 100)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (n : ℕ) :
  ∀ᵐ z ∂Measure.pi (fun _ : Fin n => atomicMeasure w),
    Real.exp (-sourceEll * normalDeviation q z) ≤
      Real.exp (11 * sourceEll * (n : ℝ)) := by
  let := atomicMeasure_isProbabilityMeasure w hw hs
  exact iid_normal_likelihood_ae_bound (atomicMeasure w) sourceEll q
    sourceEll_pos.le (by linarith) (atomicMeasure_ae_normalValue_lower w) n

end
end Shao.OQ3
