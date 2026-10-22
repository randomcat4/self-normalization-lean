import Shao.OQ3.FinitePrefixLaw
import Shao.OQ3.StageSourceWitness
import Shao.OQ3.SourceTransferBudgets
import Shao.OQ3.StageSourceAsymptotic

/-!
# One final source law with unbounded scaled remainder

Source: current/oq3/proofs/r1/report.md, equations (26)–(31), lines 486–550.
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U18c scope67. Every analytic input is produced for the actual finite model.
-/

namespace Shao.OQ3
open MeasureTheory Filter
open scoped Matrix Topology BigOperators
noncomputable section

private theorem exists_finite_stage_witness
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1)
    (J : ℕ) (q : ℝ) (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (hmeanY : (∫ x : ℝ, normalValue x ∂atomicMeasure w) = q)
    (hmeanX : (∫ x : ℝ, x ∂atomicMeasure w) = q / 4)
    (hrange : ∀ᵐ x ∂atomicMeasure w, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < (atomicMeasure w).real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 0 < n ∧
      correctedInverseScale sourceEll q (atomicMeasure w) +
        (3 * dyadicMesh J * Real.sqrt (dyadicMesh J)) / (16384 * Real.pi) ≤
          normalizedTailCoefficient sourceEll q w n ∧
      (J : ℝ) ≤ Real.sqrt (n : ℝ) * dyadicMesh J * Real.sqrt (dyadicMesh J) := by
  let : IsProbabilityMeasure (atomicMeasure w) := atomicMeasure_isProbabilityMeasure w hw hs
  let h : ℝ := dyadicMesh J
  let C : ℝ := correctedInverseScale sourceEll q (atomicMeasure w)
  let L : ℝ := (h / Real.sqrt (normalVariance (atomicMeasure w))) *
    ∑' k : ℤ, sourceGaussianLayerWeight (atomicMeasure w) q sourceEll (h * (k : ℝ))
  have hh : 0 < h := by dsimp [h, dyadicMesh]; positivity
  have ha : 0 < h * Real.sqrt h := mul_pos hh (Real.sqrt_pos.mpr hh)
  obtain ⟨m, hm, hphase⟩ := exists_stage_phase_return_subsequence J q
  have hmTop : Tendsto m atTop atTop := hm.tendsto_atTop
  obtain ⟨_, hlim⟩ := normalizedTailCoefficient_stage_subsequence_tendsto_of_stage
    w hw hs J q hq0 hq1 hmeanY hmeanX hrange hpos m hmTop hphase
  have hlimL : Tendsto (fun j : ℕ => normalizedTailCoefficient sourceEll q w (m j))
      atTop (nhds L) := by simpa only [L, h] using hlim
  obtain ⟨_, hgap⟩ := stage_sourceGaussianLayerWeight_lattice_gap
    (atomicMeasure w) J q hq0 hq1 hmeanY hmeanX hrange hpos
  have hgapL : C + (h * Real.sqrt h) / (4096 * Real.pi) ≤ L := by
    simpa only [C, L, h, mul_comm] using hgap
  let delta : ℝ := h * Real.sqrt h / (16384 * Real.pi)
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hsplit : h * Real.sqrt h / (4096 * Real.pi) =
      (3 * h * Real.sqrt h) / (16384 * Real.pi) + delta := by
    dsimp only [delta]
    field_simp
    <;> ring
  have hmargin : C + (3 * h * Real.sqrt h) / (16384 * Real.pi) < L := by
    rw [hsplit] at hgapL
    linarith only [hgapL, hdelta]
  have hcoef : ∀ᶠ j : ℕ in atTop,
      C + (3 * h * Real.sqrt h) / (16384 * Real.pi) <
        normalizedTailCoefficient sourceEll q w (m j) :=
    (tendsto_order.mp hlimL).1 _ hmargin
  obtain ⟨B, hB⟩ := exists_nat_gt (((J : ℝ) / (h * Real.sqrt h)) ^ 2)
  have hNtime : ∀ᶠ j : ℕ in atTop, N ≤ m j := hmTop.eventually (eventually_ge_atTop N)
  have hBtime : ∀ᶠ j : ℕ in atTop, B ≤ m j := hmTop.eventually (eventually_ge_atTop B)
  have hptime : ∀ᶠ j : ℕ in atTop, 1 ≤ m j := hmTop.eventually (eventually_ge_atTop 1)
  obtain ⟨j, hNj, hBj, hpj, hcj⟩ := (hNtime.and (hBtime.and (hptime.and hcoef))).exists
  refine ⟨m j, hNj, by omega, ?_, ?_⟩
  · simpa only [C, h] using hcj.le
  · have hBcast : (B : ℝ) ≤ (m j : ℝ) := by exact_mod_cast hBj
    have hsqrt : (J : ℝ) / (h * Real.sqrt h) ≤ Real.sqrt (m j : ℝ) :=
      Real.le_sqrt_of_sq_le (hB.le.trans hBcast)
    have H := (div_le_iff₀ ha).mp hsqrt
    simpa only [h, mul_assoc] using H


private theorem scaled_remainder_unbounded
    (w : AtomicIndex → ℝ) (q : ℝ) (nseq : ℕ → ℕ)
    (hn : ∀ J : ℕ, 0 < nseq J)
    (hgap : ∀ J : ℕ,
      correctedInverseScale sourceEll q (atomicMeasure w) +
        (dyadicMesh J * Real.sqrt (dyadicMesh J)) / (8192 * Real.pi) ≤
          normalizedTailCoefficient sourceEll q w (nseq J))
    (hgrowth : ∀ J : ℕ, (J : ℝ) ≤ Real.sqrt (nseq J : ℝ) *
      dyadicMesh J * Real.sqrt (dyadicMesh J)) :
    ∀ (K : ℝ) (N : ℕ), ∃ n : ℕ, N ≤ n ∧ 0 < n ∧
      K < Real.sqrt (n : ℝ) *
        (normalizedTailCoefficient sourceEll q w n -
          correctedInverseScale sourceEll q (atomicMeasure w)) := by
  intro K N
  obtain ⟨J, hJ⟩ := exists_nat_gt (max (N : ℝ) (K * (8192 * Real.pi)))
  have hNJ : N < J := by
    exact_mod_cast ((le_max_left (N : ℝ) (K * (8192 * Real.pi))).trans_lt hJ)
  have hh : 0 < dyadicMesh J := by dsimp [dyadicMesh]; positivity
  have hh1 : dyadicMesh J ≤ 1 := by
    unfold dyadicMesh
    exact (inv_le_one₀ (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hroot1 : Real.sqrt (dyadicMesh J) ≤ 1 := Real.sqrt_le_one.mpr hh1
  have ha1 : dyadicMesh J * Real.sqrt (dyadicMesh J) ≤ 1 := by
    simpa only [one_mul] using
      mul_le_mul hh1 hroot1 (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hJroot : (J : ℝ) ≤ Real.sqrt (nseq J : ℝ) := by
    calc
      (J : ℝ) ≤ Real.sqrt (nseq J : ℝ) * dyadicMesh J *
          Real.sqrt (dyadicMesh J) := hgrowth J
      _ = Real.sqrt (nseq J : ℝ) * (dyadicMesh J * Real.sqrt (dyadicMesh J)) :=
        mul_assoc _ _ _
      _ ≤ Real.sqrt (nseq J : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left ha1 (Real.sqrt_nonneg _)
      _ = Real.sqrt (nseq J : ℝ) := mul_one _
  have hJ2 : (J : ℝ) ^ 2 ≤ (nseq J : ℝ) :=
    (Real.le_sqrt (Nat.cast_nonneg J) (Nat.cast_nonneg (nseq J))).mp hJroot
  have hJone : (1 : ℝ) ≤ (J : ℝ) := by
    exact_mod_cast (show 1 ≤ J by omega)
  have hJle : (J : ℝ) ≤ (J : ℝ) ^ 2 := by
    nlinarith only [hJone, sq_nonneg ((J : ℝ) - 1)]
  have hNn : N ≤ nseq J := by
    have hcast : (N : ℝ) ≤ (nseq J : ℝ) :=
      (show (N : ℝ) ≤ (J : ℝ) by exact_mod_cast hNJ.le).trans (hJle.trans hJ2)
    exact_mod_cast hcast
  refine ⟨nseq J, hNn, hn J, ?_⟩
  have hD : 0 < (8192 : ℝ) * Real.pi := by positivity
  have hK : K < (J : ℝ) / (8192 * Real.pi) :=
    (lt_div_iff₀ hD).mpr ((le_max_right (N : ℝ) (K * (8192 * Real.pi))).trans_lt hJ)
  have hgapJ : (dyadicMesh J * Real.sqrt (dyadicMesh J)) / (8192 * Real.pi) ≤
      normalizedTailCoefficient sourceEll q w (nseq J) -
        correctedInverseScale sourceEll q (atomicMeasure w) := by
    linarith only [hgap J]
  calc
    K < (J : ℝ) / (8192 * Real.pi) := hK
    _ ≤ (Real.sqrt (nseq J : ℝ) * dyadicMesh J * Real.sqrt (dyadicMesh J)) /
        (8192 * Real.pi) := (div_le_div_iff_of_pos_right hD).mpr (hgrowth J)
    _ = Real.sqrt (nseq J : ℝ) *
        ((dyadicMesh J * Real.sqrt (dyadicMesh J)) / (8192 * Real.pi)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hgapJ (Real.sqrt_nonneg _)

theorem exists_source_fixed_law_unbounded_scaled_remainder :
  ∃ (p : Fin 4 → ℝ) (q eps : ℝ),
    (∀ i, 0 < p i) ∧ 1 < q ∧ q < 103 / 100 ∧ 0 < eps ∧
    (constraintMatrix sourceEll) *ᵥ p = constraintTarget q ∧
    ∃ r : ℕ → ℝ, (∀ j, 0 < r j) ∧ Summable r ∧ (∑' j, r j) < eps ∧
      (∀ i : AtomicIndex, 0 < limitingMass sourceEll p r i) ∧
      (∀ k : Fin 4,
        HasSum (fun i => limitingMass sourceEll p r i * constraintFeature sourceEll (fixedAtom i) k)
          (constraintTarget q k)) ∧
      IsProbabilityMeasure (originalMeasure sourceEll (limitingMass sourceEll p r)) ∧
      (Integrable (fun x : ℝ => x) (originalMeasure sourceEll (limitingMass sourceEll p r)) ∧
        (∫ x : ℝ, x ∂originalMeasure sourceEll (limitingMass sourceEll p r)) = 0) ∧
      ∀ (K : ℝ) (N : ℕ), ∃ n : ℕ, N ≤ n ∧ 0 < n ∧
        K < Real.sqrt (n : ℝ) *
          (normalizedTailCoefficient sourceEll q (limitingMass sourceEll p r) n -
            correctedInverseScale sourceEll q (atomicMeasure (limitingMass sourceEll p r))) := by
  classical
  obtain ⟨p, q, epsT, hp, hq0, hq1, hepsT, hc, hfamily, hcaps⟩ :=
    exists_source_transfer_caps
  obtain ⟨epsP, hepsP, hprefix⟩ := exists_source_prefix_radius p q hp hc
  let eps : ℝ := min epsT epsP
  have heps : 0 < eps := lt_min hepsT hepsP
  refine ⟨p, q, eps, hp, hq0, hq1, heps, hc, ?_⟩
  let eta : ℕ → ℝ := fun J =>
    (dyadicMesh J * Real.sqrt (dyadicMesh J)) / (32768 * Real.pi)
  have heta (J : ℕ) : 0 < eta J := by
    dsimp [eta, dyadicMesh]
    positivity
  let W : (J : ℕ) → (Fin J → ℝ) → ℕ → Prop := fun J u n =>
    0 < n ∧
      correctedInverseScale sourceEll q (atomicMeasure (prefixMass sourceEll p J u)) +
        (3 * dyadicMesh J * Real.sqrt (dyadicMesh J)) / (16384 * Real.pi) ≤
          normalizedTailCoefficient sourceEll q (prefixMass sourceEll p J u) n ∧
      (J : ℝ) ≤ Real.sqrt (n : ℝ) * dyadicMesh J * Real.sqrt (dyadicMesh J)
  have hW (J : ℕ) (u : Fin J → ℝ) (hu : ∀ i, 0 < u i)
      (hsu : (∑ i, u i) < eps) : ∃ n : ℕ, W J u n := by
    obtain ⟨hw, hs, hmeanY, hmeanX, hrange, hpos⟩ :=
      hprefix J u hu (hsu.trans_le (min_le_right epsT epsP))
    obtain ⟨n, _, hn, hgap, hgrowth⟩ := exists_finite_stage_witness
      (prefixMass sourceEll p J u) hw hs J q hq0 hq1 hmeanY hmeanX hrange hpos
      1
    exact ⟨n, hn, hgap, hgrowth⟩
  obtain ⟨cap, hcap, herror⟩ := hcaps eta heta
  obtain ⟨chooseN, hn, r, hr, hs, ht, htail⟩ :=
    exists_witness_first_positive_mass_with_tail_caps eps heps W hW cap
      (fun J u hu hsu n _ => hcap J u hu (hsu.trans_le (min_le_left epsT epsP)) n)
  obtain ⟨hpl, _⟩ := hfamily r hr hs (ht.trans_le (min_le_left epsT epsP))
  have hpositive : ∀ i : AtomicIndex, 0 < limitingMass sourceEll p r i := by
    intro i
    cases i with
    | inl i => exact hpl i
    | inr j => exact hr j
  have hnonneg := fun i => (hpositive i).le
  have hm := limitingMoment_hasSum sourceEll q sourceEll_pos.le p r
    source_constraintMatrix_nonsingular hc (fun j => (hr j).le) hs
  have hmass : HasSum (limitingMass sourceEll p r) 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  let nseq : ℕ → ℕ := fun J => chooseN J (fun i : Fin J => r i.val)
  have hfinal : ∀ J : ℕ,
      0 < nseq J ∧
      correctedInverseScale sourceEll q (atomicMeasure (limitingMass sourceEll p r)) +
        (dyadicMesh J * Real.sqrt (dyadicMesh J)) / (8192 * Real.pi) ≤
          normalizedTailCoefficient sourceEll q (limitingMass sourceEll p r) (nseq J) ∧
      (J : ℝ) ≤ Real.sqrt (nseq J : ℝ) * dyadicMesh J * Real.sqrt (dyadicMesh J) := by
    intro J
    let u : Fin J → ℝ := fun i => r i.val
    have hpos : ∀ i, 0 < u i := fun i => hr i.val
    have hsum : (∑ i, u i) < eps := by
      dsimp only [u]
      rw [Fin.sum_univ_eq_sum_range]
      exact (hs.sum_le_tsum (Finset.range J) (fun j _ => (hr j).le)).trans_lt ht
    have hstage := hn J u hpos hsum
    dsimp only [W] at hstage
    have herr := herror J u hpos (hsum.trans_le (min_le_left epsT epsP))
      (chooseN J u) r hr hs (ht.trans_le (min_le_left epsT epsP))
      (fun _ => rfl) (htail J)
    have heq := finiteMass_eq_prefixMass sourceEll p J u r (fun _ => rfl)
    rw [heq] at herr
    refine ⟨hstage.1, ?_, hstage.2.2⟩
    have hsplit : (3 * dyadicMesh J * Real.sqrt (dyadicMesh J)) / (16384 * Real.pi) =
        (dyadicMesh J * Real.sqrt (dyadicMesh J)) / (8192 * Real.pi) + 2 * eta J := by
      dsimp only [eta]
      field_simp
      <;> ring
    have hgap := hstage.2.1
    rw [hsplit] at hgap
    have hcoef := (abs_lt.mp herr.1).1
    have hscale := (abs_lt.mp herr.2).2
    linarith only [hgap, hcoef, hscale]
  refine ⟨r, hr, hs, ht, hpositive, hm,
    originalMeasure_isProbabilityMeasure _ _ hnonneg hmass,
    originalMeasure_centered sourceEll q _ hnonneg hm, ?_⟩
  exact scaled_remainder_unbounded (limitingMass sourceEll p r) q nseq
    (fun J => (hfinal J).1) (fun J => (hfinal J).2.1) (fun J => (hfinal J).2.2)

end
end Shao.OQ3
