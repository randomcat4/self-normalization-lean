import Shao.OQ3.FinitePrefixLaw
import Shao.OQ3.StageSourceWitness
import Shao.OQ3.SourceTransferBudgets

/-!
# A single final source law after prefix-first sample selection

Source: current/oq3/proofs/r1/report.md, lines 486–550, equations (26)–(31).
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U17q scope64-v2. The actual all-prefix continuity family remains explicit.
-/

namespace Shao.OQ3
open MeasureTheory Filter
open scoped Matrix Topology BigOperators
noncomputable section

theorem exists_source_fixed_law_coefficient_diagonal :
  ∃ (p : Fin 4 → ℝ) (q eps : ℝ),
    (∀ i, 0 < p i) ∧ 1 < q ∧ q < 103 / 100 ∧ 0 < eps ∧
    (constraintMatrix sourceEll) *ᵥ p = constraintTarget q ∧
    ∀ (hcont : ∀ (J : ℕ) (u : Fin J → ℝ),
      (∀ i, 0 < u i) → (∑ i, u i) < eps →
      ∀ d : ℕ → ℝ,
        (∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M) →
        (∀ᶠ n : ℕ in atTop, ∃ k : ℤ,
          d n + (n : ℝ) * q = dyadicMesh J * (k : ℝ)) →
        ∀ A : Set ℝ,
          (ProbabilityTheory.gaussianReal 0
            (Real.toNNReal (transverseVariance
              (atomicMeasure (prefixMass sourceEll p J u))))) (frontier A) = 0 →
          Tendsto (fun n : ℕ =>
            (normalLayerConditionalLaw (atomicMeasure (prefixMass sourceEll p J u))
              q (q / 4) (d n) n).real A)
            atTop (nhds ((ProbabilityTheory.gaussianReal 0
              (Real.toNNReal (transverseVariance
                (atomicMeasure (prefixMass sourceEll p J u))))).real A))),
    ∃ chooseN : (J : ℕ) → (Fin J → ℝ) → ℕ,
      (∀ (J : ℕ) (u : Fin J → ℝ),
        (∀ i, 0 < u i) → (∑ i, u i) < eps →
        0 < chooseN J u ∧
        correctedInverseScale sourceEll q (atomicMeasure (prefixMass sourceEll p J u)) +
          (3 * dyadicMesh J * Real.sqrt (dyadicMesh J)) / (16384 * Real.pi) ≤
            normalizedTailCoefficient sourceEll q (prefixMass sourceEll p J u) (chooseN J u) ∧
        (J : ℝ) ≤ Real.sqrt (chooseN J u : ℝ) * dyadicMesh J * Real.sqrt (dyadicMesh J)) ∧
      ∃ r : ℕ → ℝ, (∀ j, 0 < r j) ∧ Summable r ∧ (∑' j, r j) < eps ∧
        (∀ i : AtomicIndex, 0 < limitingMass sourceEll p r i) ∧
        (∀ k : Fin 4,
          HasSum (fun i => limitingMass sourceEll p r i * constraintFeature sourceEll (fixedAtom i) k)
            (constraintTarget q k)) ∧
        IsProbabilityMeasure (originalMeasure sourceEll (limitingMass sourceEll p r)) ∧
        (Integrable (fun x : ℝ => x) (originalMeasure sourceEll (limitingMass sourceEll p r)) ∧
          (∫ x : ℝ, x ∂originalMeasure sourceEll (limitingMass sourceEll p r)) = 0) ∧
        ∀ J : ℕ,
          0 < chooseN J (fun i : Fin J => r i.val) ∧
          correctedInverseScale sourceEll q (atomicMeasure (limitingMass sourceEll p r)) +
            (dyadicMesh J * Real.sqrt (dyadicMesh J)) / (8192 * Real.pi) ≤
              normalizedTailCoefficient sourceEll q (limitingMass sourceEll p r)
                (chooseN J (fun i : Fin J => r i.val)) ∧
          (J : ℝ) ≤ Real.sqrt (chooseN J (fun i : Fin J => r i.val) : ℝ) *
            dyadicMesh J * Real.sqrt (dyadicMesh J) := by
  classical
  obtain ⟨p, q, epsT, hp, hq0, hq1, hepsT, hc, hfamily, hcaps⟩ :=
    exists_source_transfer_caps
  obtain ⟨epsP, hepsP, hprefix⟩ := exists_source_prefix_radius p q hp hc
  let eps : ℝ := min epsT epsP
  have heps : 0 < eps := lt_min hepsT hepsP
  refine ⟨p, q, eps, hp, hq0, hq1, heps, hc, ?_⟩
  intro hcont
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
    obtain ⟨n, _, hn, hgap, hgrowth⟩ := exists_stage_source_witness
      (prefixMass sourceEll p J u) hw hs J q hq0 hq1 hmeanY hmeanX hrange hpos
      (hcont J u hu hsu) 1
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
  refine ⟨chooseN, hn, r, hr, hs, ht, hpositive, hm,
    originalMeasure_isProbabilityMeasure _ _ hnonneg hmass,
    originalMeasure_centered sourceEll q _ hnonneg hm, ?_⟩
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

end
end Shao.OQ3
