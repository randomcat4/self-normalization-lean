import Shao.OQ3.StageCurvedLayerLimit
import Shao.OQ3.StageSourceNegativeTail
import Shao.OQ3.PositiveLayerTail
import Shao.OQ3.SampleChangeOfMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace Shao.OQ3

open MeasureTheory Filter
open scoped Topology BigOperators

noncomputable section

def sourceGaussianLayerWeight (mu : Measure ℝ) (q ell d : ℝ) : ℝ :=
  Real.exp (-ell * d) *
    (ProbabilityTheory.gaussianReal 0 (Real.toNNReal (transverseVariance mu))).real
      {x : ℝ | -((q / 16) * d) ≤ x ^ 2}

private theorem term_le_shifted_tsum (f : ℕ → ℝ) (hs : Summable f)
    (h0 : ∀ k, 0 ≤ f k) (K : ℕ) : f K ≤ ∑' k : ℕ, f (K + k) := by
  have hshift : Summable (fun k : ℕ => f (K + k)) :=
    hs.comp_injective (fun _ _ h => Nat.add_left_cancel h)
  simpa only [Finset.sum_singleton, Nat.add_zero] using
    hshift.sum_le_tsum ({0} : Finset ℕ) (fun k _ => h0 (K + k))

private theorem nonnegative_tsum_tendsto
    (F : ℕ → ℕ → ℝ) (L b : ℕ → ℝ)
    (hF0 : ∀ j k, 0 ≤ F j k) (hFs : ∀ j, Summable (F j))
    (hb0 : ∀ k, 0 ≤ b k) (hbs : Summable b)
    (hbound : ∀ᶠ j : ℕ in atTop, ∀ k, F j k ≤ b k)
    (hlim : ∀ k, Tendsto (fun j : ℕ => F j k) atTop (nhds (L k))) :
    Summable L ∧
      Tendsto (fun j : ℕ => ∑' k : ℕ, F j k) atTop (nhds (∑' k : ℕ, L k)) := by
  have hL0 (k : ℕ) : 0 ≤ L k :=
    le_of_tendsto_of_tendsto tendsto_const_nhds (hlim k)
      (Eventually.of_forall (fun j => hF0 j k))
  have hLb (k : ℕ) : L k ≤ b k :=
    le_of_tendsto (hlim k) (hbound.mono (fun _ hj => hj k))
  have hLs : Summable L := Summable.of_nonneg_of_le hL0 hLb hbs
  have hFi (j : ℕ) : Integrable (F j) (Measure.count : Measure ℕ) := by
    apply integrable_count_iff.mpr
    have heq : (fun k => ‖F j k‖) = F j := by
      funext k
      rw [Real.norm_eq_abs, abs_of_nonneg (hF0 j k)]
    rw [heq]
    exact hFs j
  have hLi : Integrable L (Measure.count : Measure ℕ) := by
    apply integrable_count_iff.mpr
    have heq : (fun k => ‖L k‖) = L := by
      funext k
      rw [Real.norm_eq_abs, abs_of_nonneg (hL0 k)]
    rwa [heq]
  have hbi : Integrable b (Measure.count : Measure ℕ) := by
    apply integrable_count_iff.mpr
    have heq : (fun k => ‖b k‖) = b := by
      funext k
      rw [Real.norm_eq_abs, abs_of_nonneg (hb0 k)]
    rwa [heq]
  have hD := tendsto_integral_filter_of_dominated_convergence
    (μ := (Measure.count : Measure ℕ)) b
    (Eventually.of_forall (fun j => (hFi j).aestronglyMeasurable))
    (hbound.mono (fun j hj => ae_of_all _ (fun k => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hF0 j k)]
      exact hj k))) hbi (ae_of_all _ hlim)
  have hInt (j : ℕ) : (∫ k : ℕ, F j k ∂Measure.count) = ∑' k : ℕ, F j k := by
    simpa only [count_real_singleton, one_smul] using integral_countable (hFi j)
  have hIntL : (∫ k : ℕ, L k ∂Measure.count) = ∑' k : ℕ, L k := by
    simpa only [count_real_singleton, one_smul] using integral_countable hLi
  refine ⟨hLs, ?_⟩
  simpa only [hInt, hIntL] using hD

theorem normalizedTailCoefficient_stage_subsequence_tendsto
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1)
    (J : ℕ) (q : ℝ) (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (hmeanY : (∫ x : ℝ, normalValue x ∂atomicMeasure w) = q)
    (hmeanX : (∫ x : ℝ, x ∂atomicMeasure w) = q / 4)
    (hrange : ∀ᵐ x ∂atomicMeasure w, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < (atomicMeasure w).real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (hphase : Tendsto (fun j : ℕ => Int.fract ((m j : ℝ) * q / dyadicMesh J))
      atTop (nhds 0))
    (hcont : ∀ d : ℕ → ℝ,
      (∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M) →
      (∀ᶠ n : ℕ in atTop, ∃ k : ℤ,
        d n + (n : ℝ) * q = dyadicMesh J * (k : ℝ)) →
      ∀ A : Set ℝ,
        (ProbabilityTheory.gaussianReal 0
          (Real.toNNReal (transverseVariance (atomicMeasure w)))) (frontier A) = 0 →
        Tendsto (fun n : ℕ =>
          (normalLayerConditionalLaw (atomicMeasure w) q (q / 4) (d n) n).real A)
          atTop (nhds ((ProbabilityTheory.gaussianReal 0
            (Real.toNNReal (transverseVariance (atomicMeasure w)))).real A))) :
    Summable (fun k : ℤ => sourceGaussianLayerWeight (atomicMeasure w) q sourceEll
        (dyadicMesh J * (k : ℝ))) ∧
      Tendsto (fun j : ℕ => normalizedTailCoefficient sourceEll q w (m j))
        atTop (nhds ((dyadicMesh J / Real.sqrt (normalVariance (atomicMeasure w))) *
          ∑' k : ℤ, sourceGaussianLayerWeight (atomicMeasure w) q sourceEll
            (dyadicMesh J * (k : ℝ)))) := by
  let mu : Measure ℝ := atomicMeasure w
  let : IsProbabilityMeasure mu := atomicMeasure_isProbabilityMeasure w hw hs
  let h : ℝ := dyadicMesh J
  have hh : 0 < h := by dsimp [h, dyadicMesh]; positivity
  have hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10 := by
    filter_upwards [hrange] with x hx
    obtain ⟨i, rfl⟩ := hx
    cases i with
    | inl i => exact (fixedAtom_bounds (Sum.inl i)).2
    | inr j => exact (fixedAtom_bounds (Sum.inr j.val)).2
  have hbase : ∀ i : Fin 4, 0 < mu.real {baseAtom i} := fun i => hpos (Sum.inl i)
  have hS := normalVariance_pos mu hb hbase
  have hD := parabolaCovariance_det_pos mu hb hbase
  let C : ℝ := (h / (2 * Real.pi)) * Real.sqrt (2 * Real.pi / normalVariance mu)
  have hC : 0 < C := by
    dsimp only [C]
    exact mul_pos (div_pos hh (by positivity))
      (Real.sqrt_pos.mpr (div_pos (by positivity) hS))
  let W : ℝ → ℝ := sourceGaussianLayerWeight mu q sourceEll
  let theta : ℕ → ℝ := fun n => Int.fract ((n : ℝ) * q / h)
  have ht (n : ℕ) : theta n ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hfloor (n : ℕ) :
      h * ((⌊(n : ℝ) * q / h⌋ : ℤ) : ℝ) + h * theta n = (n : ℝ) * q := by
    rw [← mul_add]
    dsimp only [theta]
    rw [Int.floor_add_fract, mul_div_cancel₀ _ hh.ne']
  let P : ℕ → ℕ → ℝ := fun n k =>
    sourcePositiveNormalLayerTerm mu q sourceEll h (theta n) n k
  let N : ℕ → ℕ → ℝ := fun n k =>
    negativeNormalLayerTerm mu q sourceEll h (theta n) n k
  have hPs (n : ℕ) : Summable (P n) :=
    (stage_source_layer_decomposition mu J q sourceEll hrange n).1
  have hNs (n : ℕ) : Summable (N n) :=
    (stage_source_layer_decomposition mu J q sourceEll hrange n).2.1
  have hP0 (n k : ℕ) : 0 ≤ P n k := by
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)
      ENNReal.toReal_nonneg
  have hN0 (n k : ℕ) : 0 ≤ N n k := by
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)
      ENNReal.toReal_nonneg
  have hPraw (n k : ℕ) :
      P n k ≤ positiveNormalLayerTerm mu q sourceEll h (theta n) n k := by
    apply mul_le_mul_of_nonneg_left _
      (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)
    exact measureReal_mono (fun _ hz => hz.1) (measure_ne_top _ _)
  obtain ⟨Cp, hCp, hptail⟩ := exists_stage_positive_layer_tail_bound
    mu J q (q / 4) sourceEll sourceEll_pos hb hmeanY hmeanX hS hD hrange hpos
  obtain ⟨gamma, Cn, hgamma, hCn, hntail⟩ :=
    exists_stage_source_negative_layer_geometric_tail mu J q hq0 hq1
      hmeanY hmeanX hrange hpos
  let rp : ℝ := Real.exp (-sourceEll * h)
  let rn : ℝ := Real.exp (-gamma * h)
  have hrp : 0 < rp := Real.exp_pos _
  have hrn : 0 < rn := Real.exp_pos _
  have hrp1 : rp < 1 := Real.exp_lt_one_iff.mpr (by
    nlinarith only [mul_pos sourceEll_pos hh])
  have hrn1 : rn < 1 := Real.exp_lt_one_iff.mpr (by
    nlinarith only [mul_pos hgamma hh])
  let bp : ℕ → ℝ := fun k => (Cp / (1 - rp)) * rp ^ k
  let bn : ℕ → ℝ := fun k => (Cn / (1 - rn)) * rn ^ k
  have hbp0 (k : ℕ) : 0 ≤ bp k :=
    mul_nonneg (div_nonneg hCp.le (sub_pos.mpr hrp1).le) (pow_nonneg hrp.le k)
  have hbn0 (k : ℕ) : 0 ≤ bn k :=
    mul_nonneg (div_nonneg hCn.le (sub_pos.mpr hrn1).le) (pow_nonneg hrn.le k)
  have hbps : Summable bp :=
    (summable_geometric_of_abs_lt_one (by rwa [abs_of_pos hrp])).mul_left _
  have hbns : Summable bn :=
    (summable_geometric_of_abs_lt_one (by rwa [abs_of_pos hrn])).mul_left _
  have hPb : ∀ᶠ j : ℕ in atTop, ∀ k : ℕ, P (m j) k ≤ bp k := by
    filter_upwards [hm.eventually hptail] with j hj
    intro k
    have htj := hj (theta (m j)) (ht (m j))
    have hraw0 (i : ℕ) :
        0 ≤ positiveNormalLayerTerm mu q sourceEll h (theta (m j)) (m j) i :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)
        ENNReal.toReal_nonneg
    exact (hPraw (m j) k).trans
      ((term_le_shifted_tsum _ htj.1 hraw0 k).trans
        ((htj.2 k).trans_eq (by dsimp only [bp, rp, h]; ring)))
  have hNb : ∀ᶠ j : ℕ in atTop, ∀ k : ℕ, N (m j) k ≤ bn k := by
    filter_upwards [hm.eventually hntail] with j hj
    intro k
    have htj := hj (theta (m j)) (ht (m j))
    exact (term_le_shifted_tsum _ htj.1 (hN0 (m j)) k).trans
      ((htj.2 k).trans_eq (by dsimp only [bn, rn, h]; ring))
  have hPlim (k : ℕ) : Tendsto (fun j : ℕ => P (m j) k) atTop
      (nhds (C * W (h * ((k : ℝ) + 1)))) := by
    let d : ℕ → ℝ := fun n => h * ((k : ℝ) + 1 - theta n)
    have hd : ∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M := by
      refine ⟨h * ((k : ℝ) + 1), ?_⟩
      intro n
      have hd0 : 0 ≤ d n := by
        dsimp only [d]
        exact mul_nonneg hh.le (by have hk := Nat.cast_nonneg (α := ℝ) k; linarith [(ht n).2])
      rw [abs_of_nonneg hd0]
      dsimp only [d]
      nlinarith only [mul_nonneg hh.le (ht n).1]
    have hgrid : ∀ᶠ n : ℕ in atTop, ∃ i : ℤ,
        d n + (n : ℝ) * q = dyadicMesh J * (i : ℝ) := by
      apply Eventually.of_forall
      intro n
      refine ⟨⌊(n : ℝ) * q / h⌋ + (k : ℤ) + 1, ?_⟩
      simp only [Int.cast_add, Int.cast_natCast, Int.cast_one]
      dsimp only [d]
      change h * ((k : ℝ) + 1 - theta n) + (n : ℝ) * q =
        h * (((⌊(n : ℝ) * q / h⌋ : ℤ) : ℝ) + (k : ℝ) + 1)
      nlinarith only [hfloor n]
    have hdlim : Tendsto (fun j : ℕ => d (m j)) atTop
        (nhds (h * ((k : ℝ) + 1))) := by
      have H := ((tendsto_const_nhds : Tendsto
        (fun _ : ℕ => (k : ℝ) + 1) atTop (nhds ((k : ℝ) + 1))).sub hphase).const_mul h
      simpa only [sub_zero] using H
    have H := stage_source_weighted_layer_subsequence_tendsto mu J q sourceEll
      (lt_trans zero_lt_one hq0) hmeanY hmeanX hrange hpos d hd hgrid m hm
      (h * ((k : ℝ) + 1)) hdlim (hcont d hd hgrid)
    convert H using 1
    · rfl
    · dsimp only [C, W, sourceGaussianLayerWeight, h]
      congr 1
      ring
  have hNlim (k : ℕ) : Tendsto (fun j : ℕ => N (m j) k) atTop
      (nhds (C * W (-(h * (k : ℝ))))) := by
    let d : ℕ → ℝ := fun n => -(h * ((k : ℝ) + theta n))
    have hd : ∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M := by
      refine ⟨h * ((k : ℝ) + 1), ?_⟩
      intro n
      have hd0 : 0 ≤ h * ((k : ℝ) + theta n) :=
        mul_nonneg hh.le (add_nonneg (Nat.cast_nonneg k) (ht n).1)
      rw [show |d n| = h * ((k : ℝ) + theta n) by
        dsimp only [d]; rw [abs_neg, abs_of_nonneg hd0]]
      nlinarith only [mul_nonneg hh.le (sub_nonneg.mpr (ht n).2)]
    have hgrid : ∀ᶠ n : ℕ in atTop, ∃ i : ℤ,
        d n + (n : ℝ) * q = dyadicMesh J * (i : ℝ) := by
      apply Eventually.of_forall
      intro n
      refine ⟨⌊(n : ℝ) * q / h⌋ - (k : ℤ), ?_⟩
      simp only [Int.cast_sub, Int.cast_natCast]
      dsimp only [d]
      change -(h * ((k : ℝ) + theta n)) + (n : ℝ) * q =
        h * (((⌊(n : ℝ) * q / h⌋ : ℤ) : ℝ) - (k : ℝ))
      nlinarith only [hfloor n]
    have hdlim : Tendsto (fun j : ℕ => d (m j)) atTop
        (nhds (-(h * (k : ℝ)))) := by
      have H := (((tendsto_const_nhds : Tendsto
        (fun _ : ℕ => (k : ℝ)) atTop (nhds (k : ℝ))).add hphase).const_mul h).neg
      simpa only [add_zero] using H
    have H := stage_source_weighted_layer_subsequence_tendsto mu J q sourceEll
      (lt_trans zero_lt_one hq0) hmeanY hmeanX hrange hpos d hd hgrid m hm
      (-(h * (k : ℝ))) hdlim (hcont d hd hgrid)
    convert H using 1
    · funext j
      simp only [N, negativeNormalLayerTerm, d, mul_neg, neg_mul, neg_neg]
    · dsimp only [C, W, sourceGaussianLayerWeight, h]
      congr 1
      ring
  obtain ⟨hPLs, hPT⟩ := nonnegative_tsum_tendsto
    (fun j => P (m j)) (fun k => C * W (h * ((k : ℝ) + 1))) bp
    (fun j => hP0 (m j)) (fun j => hPs (m j)) hbp0 hbps hPb hPlim
  obtain ⟨hNLs, hNT⟩ := nonnegative_tsum_tendsto
    (fun j => N (m j)) (fun k => C * W (-(h * (k : ℝ)))) bn
    (fun j => hN0 (m j)) (fun j => hNs (m j)) hbn0 hbns hNb hNlim
  have hWp : Summable (fun k : ℕ => W (h * ((k : ℝ) + 1))) := by
    simpa only [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul] using hPLs.mul_left C⁻¹
  have hWn : Summable (fun k : ℕ => W (-(h * (k : ℝ)))) := by
    simpa only [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul] using hNLs.mul_left C⁻¹
  let f : ℤ → ℝ := fun k => W (h * (k : ℝ))
  have hfp : Summable (fun k : ℕ => f ((k : ℤ) + 1)) := by
    simpa only [f, Int.cast_add, Int.cast_natCast, Int.cast_one] using hWp
  have hfn : Summable (fun k : ℕ => f (-(k : ℤ))) := by
    simpa only [f, Int.cast_neg, Int.cast_natCast, mul_neg] using hWn
  have hfns : Summable (fun k : ℕ => f (-((k : ℤ) + 1))) := by
    have H : Summable (fun k : ℕ => f (-((k + 1 : ℕ) : ℤ))) :=
      hfn.comp_injective (fun _ _ h => Nat.add_right_cancel h)
    simpa only [Nat.cast_add, Nat.cast_one] using H
  have hfs : Summable f := hfp.of_add_one_of_neg_add_one hfns
  have hsumf := tsum_of_add_one_of_neg_add_one hfp hfns
  have hfnzero : (∑' k : ℕ, f (-(k : ℤ))) =
      f 0 + ∑' k : ℕ, f (-((k : ℤ) + 1)) := by
    simpa only [Nat.cast_zero, neg_zero, Nat.cast_add, Nat.cast_one] using hfn.tsum_eq_zero_add
  have hreindex : (∑' k : ℕ, W (h * ((k : ℝ) + 1))) +
      (∑' k : ℕ, W (-(h * (k : ℝ)))) = ∑' k : ℤ, f k := by
    calc
      _ = (∑' k : ℕ, f ((k : ℤ) + 1)) + ∑' k : ℕ, f (-(k : ℤ)) := by
        congr 1 <;> apply tsum_congr <;> intro k <;>
          simp only [f, Int.cast_add, Int.cast_natCast, Int.cast_one, Int.cast_neg, mul_neg]
      _ = (∑' k : ℕ, f ((k : ℤ) + 1)) + (f 0 + ∑' k : ℕ, f (-((k : ℤ) + 1))) := by
        rw [hfnzero]
      _ = ∑' k : ℤ, f k := by rw [hsumf]; ring
  have htotal : Tendsto (fun j : ℕ => (∑' k : ℕ, P (m j) k) + ∑' k : ℕ, N (m j) k)
      atTop (nhds (C * ((∑' k : ℕ, W (h * ((k : ℝ) + 1))) +
        ∑' k : ℕ, W (-(h * (k : ℝ)))))) := by
    convert hPT.add hNT using 1
    rw [hWp.tsum_mul_left C, hWn.tsum_mul_left C]
    congr 1
    ring
  have hcoef (n : ℕ) : normalizedTailCoefficient sourceEll q w n =
      Real.sqrt (2 * Real.pi) * ((∑' k : ℕ, P n k) + ∑' k : ℕ, N n k) := by
    rw [normalizedTailCoefficient_eq_tilted sourceEll q w hw hs n]
    change Real.sqrt (2 * Real.pi * (n : ℝ)) *
        (∫ z : Shao.Path n, (sourceTail q n).indicator
          (fun z => Real.exp (-sourceEll * normalDeviation q z)) z
          ∂Measure.pi (fun _ : Fin n => mu)) = _
    rw [integral_indicator (sourceTail_measurable q n)]
    calc
      _ = Real.sqrt (2 * Real.pi) * (Real.sqrt (n : ℝ) *
          ∫ z : Shao.Path n in sourceTail q n, Real.exp (-sourceEll * normalDeviation q z)
            ∂Measure.pi (fun _ : Fin n => mu)) := by
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
        ring
      _ = _ := by rw [(stage_source_layer_decomposition mu J q sourceEll hrange n).2.2]
  have hnorm : Real.sqrt (2 * Real.pi) * C = h / Real.sqrt (normalVariance mu) := by
    dsimp only [C]
    rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    calc
      _ = (h / Real.sqrt (normalVariance mu)) *
          (Real.sqrt (2 * Real.pi) ^ 2 / (2 * Real.pi)) := by ring
      _ = _ := by rw [Real.sq_sqrt (by positivity), div_self (by positivity)]; ring
  refine ⟨hfs, ?_⟩
  have H := (htotal.const_mul (Real.sqrt (2 * Real.pi))).congr'
    (Eventually.of_forall (fun j => (hcoef (m j)).symm))
  rw [← mul_assoc, hnorm, hreindex] at H
  exact H

end
end Shao.OQ3
