import Shao.OQ3.NegativeLayerGeometricTail
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace Shao.OQ3

open MeasureTheory Filter
open scoped BigOperators

noncomputable section

def sourcePositiveNormalLayerTerm (mu : Measure ℝ) (q ell h theta : ℝ)
    (n k : ℕ) : ℝ :=
  Real.sqrt (n : ℝ) * Real.exp (-ell * (h * ((k : ℝ) + 1 - theta))) *
    (Measure.pi (fun _ : Fin n => mu)).real
      {z : Shao.Path n | normalDeviation q z = h * ((k : ℝ) + 1 - theta) ∧
        z ∈ sourceTail q n}

theorem stage_source_layer_decomposition (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q ell : ℝ)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i)) :
    ∀ n : ℕ,
      let theta : ℝ := Int.fract ((n : ℝ) * q / dyadicMesh J)
      Summable (fun k : ℕ =>
        sourcePositiveNormalLayerTerm mu q ell (dyadicMesh J) theta n k) ∧
      Summable (fun k : ℕ =>
        negativeNormalLayerTerm mu q ell (dyadicMesh J) theta n k) ∧
      Real.sqrt (n : ℝ) *
          (∫ z : Shao.Path n in sourceTail q n, Real.exp (-ell * normalDeviation q z)
            ∂Measure.pi (fun _ : Fin n => mu)) =
        (∑' k : ℕ, sourcePositiveNormalLayerTerm mu q ell (dyadicMesh J) theta n k) +
          ∑' k : ℕ, negativeNormalLayerTerm mu q ell (dyadicMesh J) theta n k := by
  classical
  intro n
  let nu : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
  let h : ℝ := dyadicMesh J
  let theta : ℝ := Int.fract ((n : ℝ) * q / h)
  let f : Shao.Path n → ℝ := fun z => Real.sqrt (n : ℝ) *
    Real.exp (-ell * normalDeviation q z)
  let P : ℕ → Set (Shao.Path n) := fun k =>
    {z | normalDeviation q z = h * ((k : ℝ) + 1 - theta) ∧ z ∈ sourceTail q n}
  let N : ℕ → Set (Shao.Path n) := fun k =>
    {z | normalDeviation q z = -(h * ((k : ℝ) + theta)) ∧ z ∈ sourceTail q n}
  have hh : 0 < h := by dsimp [h, dyadicMesh]; positivity
  have ht0 : 0 ≤ theta := Int.fract_nonneg _
  have ht1 : theta < 1 := Int.fract_lt_one _
  have hcoords : ∀ᵐ z ∂nu, ∀ i : Fin n,
      z i ∈ Set.range (fun j : Fin 4 ⊕ Fin J =>
        stageAtom (fun k : Fin J => addedAtom k.val) j) := by
    rw [ae_all_iff]
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => mu) (i := i)).eventually hrange
  have hY (x : ℝ) (hx : x ∈ Set.range (fun j : Fin 4 ⊕ Fin J =>
      stageAtom (fun k : Fin J => addedAtom k.val) j)) : |normalValue x| ≤ 16 := by
    obtain ⟨i, rfl⟩ := hx
    have hlo : -9 ≤ normalValue (stageAtom (fun k : Fin J => addedAtom k.val) i) := by
      cases i with
      | inl i => exact fixedAtom_normalValue_lower (Sum.inl i)
      | inr i => exact fixedAtom_normalValue_lower (Sum.inr i.val)
    have hhi : normalValue (stageAtom (fun k : Fin J => addedAtom k.val) i) ≤ 16 := by
      unfold normalValue
      nlinarith [sq_nonneg (stageAtom (fun k : Fin J => addedAtom k.val) i - 4)]
    exact abs_le.mpr ⟨by linarith, hhi⟩
  have hMb : ∀ᵐ z ∂nu, |normalDeviation q z| ≤ (16 + |q|) * (n : ℝ) := by
    filter_upwards [hcoords] with z hz
    have hs : |∑ i : Fin n, normalValue (z i)| ≤ 16 * (n : ℝ) := by
      calc
        _ ≤ ∑ i : Fin n, |normalValue (z i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, (16 : ℝ) := Finset.sum_le_sum (fun i _ => hY (z i) (hz i))
        _ = _ := by simp; ring
    calc
      |normalDeviation q z| ≤ |∑ i : Fin n, normalValue (z i)| + |(n : ℝ) * q| :=
        by simpa only [normalDeviation, sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (∑ i : Fin n, normalValue (z i)) 0 ((n : ℝ) * q))
      _ ≤ 16 * (n : ℝ) + (n : ℝ) * |q| := by
        rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
        linarith only [hs]
      _ = _ := by ring
  have hMc : Continuous (fun z : Shao.Path n => normalDeviation q z) := by
    unfold normalDeviation normalValue
    fun_prop
  have hg : Integrable (fun z : Shao.Path n => Real.exp (-ell * normalDeviation q z)) nu := by
    apply Integrable.of_bound
      (Real.continuous_exp.comp (continuous_const.mul hMc)).aestronglyMeasurable
      (Real.exp (|ell| * ((16 + |q|) * (n : ℝ))))
    filter_upwards [hMb] with z hz
    change |Real.exp (-ell * normalDeviation q z)| ≤ _
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      -ell * normalDeviation q z ≤ |-ell * normalDeviation q z| := le_abs_self _
      _ = |ell| * |normalDeviation q z| := by rw [abs_mul, abs_neg]
      _ ≤ _ := mul_le_mul_of_nonneg_left hz (abs_nonneg ell)
  have hf : Integrable f nu := hg.const_mul _
  have hphase : h * (⌊(n : ℝ) * q / h⌋ : ℝ) + h * theta = (n : ℝ) * q := by
    calc
      _ = h * ((⌊(n : ℝ) * q / h⌋ : ℝ) + theta) := by ring
      _ = h * ((n : ℝ) * q / h) := by rw [Int.floor_add_fract]
      _ = _ := mul_div_cancel₀ _ hh.ne'
  have hgrid : ∀ᵐ z ∂nu, ∃ m : ℤ, normalDeviation q z = h * ((m : ℝ) - theta) := by
    filter_upwards [hcoords] with z hz
    obtain ⟨K, hK⟩ := stage_sample_normal_layer q n J z hz
    refine ⟨K - ⌊(n : ℝ) * q / h⌋, ?_⟩
    rw [Int.cast_sub, hK]
    change h * (K : ℝ) - (n : ℝ) * q = _
    nlinarith only [hphase]
  have hPm (k : ℕ) : MeasurableSet (P k) :=
    (isClosed_eq hMc continuous_const).measurableSet.inter (sourceTail_measurable q n)
  have hNm (k : ℕ) : MeasurableSet (N k) :=
    (isClosed_eq hMc continuous_const).measurableSet.inter (sourceTail_measurable q n)
  have hPd : Pairwise (fun k l => Disjoint (P k) (P l)) := by
    intro k l hkl
    apply Set.disjoint_left.mpr
    intro z hz hz'
    have heq := mul_left_cancel₀ hh.ne' (hz.1.symm.trans hz'.1)
    apply hkl
    exact_mod_cast (show (k : ℝ) = (l : ℝ) by linarith)
  have hNd : Pairwise (fun k l => Disjoint (N k) (N l)) := by
    intro k l hkl
    apply Set.disjoint_left.mpr
    intro z hz hz'
    have heq := mul_left_cancel₀ hh.ne' (neg_injective (hz.1.symm.trans hz'.1))
    apply hkl
    exact_mod_cast (show (k : ℝ) = (l : ℝ) by linarith)
  have hPN (k l : ℕ) : Disjoint (P k) (N l) := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    have hp : 0 < normalDeviation q z := by
      rw [hz.1]
      exact mul_pos hh (by have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k; linarith)
    have hn : normalDeviation q z ≤ 0 := by
      rw [hz'.1]
      exact neg_nonpos.mpr (mul_nonneg hh.le (add_nonneg (Nat.cast_nonneg l) ht0))
    exact not_lt_of_ge hn hp
  have hUd : Disjoint (⋃ k, P k) (⋃ k, N k) := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hz'
    exact Set.disjoint_left.mp (hPN k l) hk hl
  have hcover : sourceTail q n =ᵐ[nu] (⋃ k, P k) ∪ ⋃ k, N k := by
    filter_upwards [hgrid] with z hz
    apply propext
    change z ∈ sourceTail q n ↔ z ∈ (⋃ k, P k) ∪ ⋃ k, N k
    constructor
    · intro hzE
      obtain ⟨m, hm⟩ := hz
      cases m with
      | ofNat t =>
        cases t with
        | zero =>
          apply Or.inr
          refine Set.mem_iUnion.mpr ⟨0, ?_, hzE⟩
          simpa [mul_neg] using hm
        | succ k =>
          apply Or.inl
          refine Set.mem_iUnion.mpr ⟨k, ?_, hzE⟩
          change normalDeviation q z = h * ((k : ℝ) + 1 - theta)
          simpa only [Int.ofNat_eq_natCast, Int.cast_natCast, Nat.cast_add,
            Nat.cast_one, Int.cast_add, Int.cast_one] using hm
      | negSucc k =>
        apply Or.inr
        refine Set.mem_iUnion.mpr ⟨k + 1, ?_, hzE⟩
        change normalDeviation q z = -(h * (((k + 1 : ℕ) : ℝ) + theta))
        convert hm using 1 <;> push_cast <;> ring
    · intro hzE
      rcases hzE with hzP | hzN
      · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hzP
        exact hk.2
      · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hzN
        exact hk.2
  have hPi (k : ℕ) : (∫ z in P k, f z ∂nu) =
      sourcePositiveNormalLayerTerm mu q ell h theta n k := by
    calc
      _ = ∫ _z in P k, Real.sqrt (n : ℝ) *
          Real.exp (-ell * (h * ((k : ℝ) + 1 - theta))) ∂nu := by
        apply setIntegral_congr_fun (hPm k)
        intro z hz
        dsimp [f]
        rw [hz.1]
      _ = _ := by
        rw [setIntegral_const]
        change nu.real (P k) * (Real.sqrt (n : ℝ) *
          Real.exp (-ell * (h * ((k : ℝ) + 1 - theta)))) =
            Real.sqrt (n : ℝ) * Real.exp (-ell * (h * ((k : ℝ) + 1 - theta))) *
              nu.real (P k)
        ring
  have hNi (k : ℕ) : (∫ z in N k, f z ∂nu) =
      negativeNormalLayerTerm mu q ell h theta n k := by
    calc
      _ = ∫ _z in N k, Real.sqrt (n : ℝ) *
          Real.exp (ell * (h * ((k : ℝ) + theta))) ∂nu := by
        apply setIntegral_congr_fun (hNm k)
        intro z hz
        dsimp [f]
        rw [hz.1]
        congr 2
        ring
      _ = _ := by
        rw [setIntegral_const]
        change nu.real (N k) * (Real.sqrt (n : ℝ) *
          Real.exp (ell * (h * ((k : ℝ) + theta)))) =
            Real.sqrt (n : ℝ) * Real.exp (ell * (h * ((k : ℝ) + theta))) *
              nu.real (N k)
        ring
  have hsP : HasSum (fun k => sourcePositiveNormalLayerTerm mu q ell h theta n k)
      (∫ z in ⋃ k, P k, f z ∂nu) := by
    simpa only [hPi] using
      (hasSum_integral_iUnion hPm hPd hf.integrableOn)
  have hsN : HasSum (fun k => negativeNormalLayerTerm mu q ell h theta n k)
      (∫ z in ⋃ k, N k, f z ∂nu) := by
    simpa only [hNi] using
      (hasSum_integral_iUnion hNm hNd hf.integrableOn)
  refine ⟨hsP.summable, hsN.summable, ?_⟩
  calc
    _ = ∫ z in sourceTail q n, f z ∂nu := by
      rw [integral_const_mul]
    _ = ∫ z in (⋃ k, P k) ∪ ⋃ k, N k, f z ∂nu := setIntegral_congr_set hcover
    _ = (∫ z in ⋃ k, P k, f z ∂nu) + ∫ z in ⋃ k, N k, f z ∂nu :=
      setIntegral_union hUd (MeasurableSet.iUnion hNm) hf.integrableOn hf.integrableOn
    _ = _ := by rw [hsP.tsum_eq, hsN.tsum_eq]

end
end Shao.OQ3
