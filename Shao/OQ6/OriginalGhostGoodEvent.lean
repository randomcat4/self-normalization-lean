-- STAGE1 DECLARATION PROPOSAL ONLY. NO THEOREM PROOF BODIES.
-- Parent must substantively freeze this complete context and the exact heads/RHS.
import Shao.OQ6.CanonicalDoubleGhostRowMoments
import Shao.OQ6.CompactGoodEvent
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real

set_option autoImplicit false

namespace Shao.OQ6.OriginalGhostGoodEvent

noncomputable section

open MeasureTheory
open scoped BigOperators

def sampleSum (n : ℕ) {Ω : Type*} (g : Ω → ℝ)
    (x : Fin n → Ω) : ℝ :=
  ∑ i : Fin n, g (x i)

def sampleEnergy (n : ℕ) {Ω : Type*} (g : Ω → ℝ)
    (x : Fin n → Ω) : ℝ :=
  ∑ i : Fin n, (g (x i)) ^ (2 : ℕ)

def goodEvent (n : ℕ) {Ω : Type*} (g : Ω → ℝ) :
    Set (Fin n → Ω) :=
  {x : Fin n → Ω |
    |sampleSum n g x| ≤ (2 : ℝ) * Real.sqrt (n : ℝ) ∧
      sampleEnergy n g x ≤ (4 : ℝ) * (n : ℝ)}

theorem original_sample_second_moments
    (n : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgmean : (∫ o : Ω, g o ∂μ) = 0)
    (hgsecond : (∫ o : Ω, (g o) ^ (2 : ℕ) ∂μ) = 1) :
    let M : Measure (Fin n → Ω) :=
      Shao.OQ6.CanonicalDoubleGhostRowMoments.sampleLaw n μ
    Measurable (sampleSum n g) ∧
      Measurable (sampleEnergy n g) ∧
      Integrable (fun x : Fin n → Ω => (sampleSum n g x) ^ (2 : ℕ)) M ∧
      Integrable (sampleEnergy n g) M ∧
      (∫ x : Fin n → Ω, (sampleSum n g x) ^ (2 : ℕ) ∂M) = (n : ℝ) ∧
      (∫ x : Fin n → Ω, sampleEnergy n g x ∂M) = (n : ℝ) := by
  let M : Measure (Fin n → Ω) :=
    Shao.OQ6.CanonicalDoubleGhostRowMoments.sampleLaw n μ
  letI hProbM : IsProbabilityMeasure M :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => μ)))
  let N : ℝ := (n : ℝ)
  let S : (Fin n → Ω) → ℝ := sampleSum n g
  let Q : (Fin n → Ω) → ℝ := sampleEnergy n g
  change Measurable S ∧ Measurable Q ∧
    Integrable (fun x : Fin n → Ω => (S x) ^ (2 : ℕ)) M ∧
    Integrable Q M ∧
    (∫ x : Fin n → Ω, (S x) ^ (2 : ℕ) ∂M) = N ∧
    (∫ x : Fin n → Ω, Q x ∂M) = N
  have hSMeas : Measurable S := by
    change Measurable (fun x : Fin n → Ω => ∑ i : Fin n, g (x i))
    exact Finset.measurable_sum Finset.univ
      (fun (i : Fin n) (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
        hg.comp (measurable_pi_apply i))
  have hQMeas : Measurable Q := by
    change Measurable (fun x : Fin n → Ω =>
      ∑ i : Fin n, (g (x i)) ^ (2 : ℕ))
    exact Finset.measurable_sum Finset.univ
      (fun (i : Fin n) (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
        (hg.comp (measurable_pi_apply i)).pow_const (2 : ℕ))
  have mp_i (i : Fin n) :
      MeasurePreserving (fun x : Fin n → Ω => x i) M μ := by
    change MeasurePreserving (fun x : Fin n → Ω => x i)
      (Measure.pi (fun _ : Fin n => μ)) μ
    exact measurePreserving_eval (fun _ : Fin n => μ) i
  have hgSqInt : Integrable (fun o : Ω => (g o) ^ (2 : ℕ)) μ :=
    hg2.integrable_sq
  have hcoordInt (i : Fin n) :
      Integrable (fun x : Fin n → Ω => (g (x i)) ^ (2 : ℕ)) M := by
    have hgSqMapMeas : AEStronglyMeasurable
        (fun o : Ω => (g o) ^ (2 : ℕ))
        (M.map (fun x : Fin n → Ω => x i)) :=
      (hg.pow_const (2 : ℕ)).aestronglyMeasurable
    have hMapped : Integrable (fun o : Ω => (g o) ^ (2 : ℕ))
        (M.map (fun x : Fin n → Ω => x i)) := by
      rw [(mp_i i).map_eq]
      exact hgSqInt
    exact (integrable_map_measure hgSqMapMeas
      (mp_i i).measurable.aemeasurable).1 hMapped
  have hcoordMean (i : Fin n) :
      (∫ x : Fin n → Ω, (g (x i)) ^ (2 : ℕ) ∂M) = (1 : ℝ) := by
    calc
      (∫ x : Fin n → Ω, (g (x i)) ^ (2 : ℕ) ∂M) =
          ∫ o : Ω, (g o) ^ (2 : ℕ)
            ∂M.map (fun x : Fin n → Ω => x i) :=
        (integral_map (mp_i i).measurable.aemeasurable
          (hg.pow_const (2 : ℕ)).aestronglyMeasurable).symm
      _ = 1 := by
        rw [(mp_i i).map_eq]
        exact hgsecond
  have hQInt : Integrable Q M := by
    change Integrable (fun x : Fin n → Ω =>
      ∑ i : Fin n, (g (x i)) ^ (2 : ℕ)) M
    exact integrable_finsetSum Finset.univ
      (fun (i : Fin n) (_ : i ∈ (Finset.univ : Finset (Fin n))) => hcoordInt i)
  have hQMean : (∫ x : Fin n → Ω, Q x ∂M) = N := by
    change (∫ x : Fin n → Ω, ∑ i : Fin n, (g (x i)) ^ (2 : ℕ) ∂M) = (n : ℝ)
    rw [integral_finsetSum Finset.univ
      (fun (i : Fin n) (_ : i ∈ (Finset.univ : Finset (Fin n))) => hcoordInt i)]
    simp only [hcoordMean, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  by_cases hn0 : n = 0
  · subst n
    refine ⟨hSMeas, hQMeas, ?_, hQInt, ?_, hQMean⟩
    · simpa [S, sampleSum] using
        (integrable_const (0 : ℝ) :
          Integrable (fun _ : Fin 0 → Ω => (0 : ℝ)) M)
    · simp [S, sampleSum, N]
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hN : (0 : ℝ) < N := by
      dsimp [N]
      exact_mod_cast hn
    obtain ⟨c, hc, hCompact⟩ :=
      Shao.OQ6.CompactGoodEvent.original_projection_compact_good_event
        μ g hg hg2 hgmean hgsecond
    let WOld : (Fin n → Ω) → ℝ := fun x : Fin n → Ω =>
      (∑ i : Fin n, g (x i)) / Real.sqrt (n : ℝ)
    let q : ℝ := Real.sqrt N
    have hq : (0 : ℝ) < q := Real.sqrt_pos.2 hN
    have hqsq : q ^ (2 : ℕ) = N := Real.sq_sqrt hN.le
    have hW2Int : Integrable
        (fun x : Fin n → Ω => (WOld x) ^ (2 : ℕ)) M :=
      (hCompact n hn).2.1
    have hW2Mean :
        (∫ x : Fin n → Ω, (WOld x) ^ (2 : ℕ) ∂M) = (1 : ℝ) :=
      (hCompact n hn).2.2.1
    have hS2Scale : ∀ x : Fin n → Ω,
        (S x) ^ (2 : ℕ) = N * (WOld x) ^ (2 : ℕ) := by
      intro x
      change (∑ i : Fin n, g (x i)) ^ (2 : ℕ) =
        N * ((∑ i : Fin n, g (x i)) / q) ^ (2 : ℕ)
      rw [div_pow, hqsq]
      field_simp [hN.ne'] <;> ring
    have hS2Int : Integrable
        (fun x : Fin n → Ω => (S x) ^ (2 : ℕ)) M := by
      apply (hW2Int.const_mul N).congr
      exact ae_of_all M (fun x : Fin n → Ω => (hS2Scale x).symm)
    have hS2Mean :
        (∫ x : Fin n → Ω, (S x) ^ (2 : ℕ) ∂M) = N := by
      calc
        (∫ x : Fin n → Ω, (S x) ^ (2 : ℕ) ∂M) =
            ∫ x : Fin n → Ω, N * (WOld x) ^ (2 : ℕ) ∂M :=
          integral_congr_ae (ae_of_all M hS2Scale)
        _ = N * (∫ x : Fin n → Ω, (WOld x) ^ (2 : ℕ) ∂M) :=
          integral_const_mul N (fun x : Fin n → Ω => (WOld x) ^ (2 : ℕ))
        _ = N := by rw [hW2Mean, mul_one]
    exact ⟨hSMeas, hQMeas, hS2Int, hQInt, hS2Mean, hQMean⟩

theorem original_ghost_strict_bad_bounds
    (n : ℕ) (hn : 0 < n) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgmean : (∫ o : Ω, g o ∂μ) = 0)
    (hgsecond : (∫ o : Ω, (g o) ^ (2 : ℕ) ∂μ) = 1) :
    let M : Measure (Fin n → Ω) :=
      Shao.OQ6.CanonicalDoubleGhostRowMoments.sampleLaw n μ
    M.real {x : Fin n → Ω |
      (2 : ℝ) * Real.sqrt (n : ℝ) < |sampleSum n g x|} ≤ (1 / 4 : ℝ) ∧
      M.real {x : Fin n → Ω |
        (4 : ℝ) * (n : ℝ) < sampleEnergy n g x} ≤ (1 / 4 : ℝ) := by
  let M : Measure (Fin n → Ω) :=
    Shao.OQ6.CanonicalDoubleGhostRowMoments.sampleLaw n μ
  letI hProbM : IsProbabilityMeasure M :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => μ)))
  let N : ℝ := (n : ℝ)
  let S : (Fin n → Ω) → ℝ := sampleSum n g
  let Q : (Fin n → Ω) → ℝ := sampleEnergy n g
  let H : ℝ := (4 : ℝ) * N
  let K : ℝ := (2 : ℝ) * Real.sqrt N
  let A : Set (Fin n → Ω) :=
    {x : Fin n → Ω | H < (S x) ^ (2 : ℕ)}
  let D : Set (Fin n → Ω) := {x : Fin n → Ω | K < |S x|}
  let C : Set (Fin n → Ω) := {x : Fin n → Ω | H < Q x}
  let I_A : (Fin n → Ω) → ℝ :=
    A.indicator (fun _ : Fin n → Ω => H)
  let I_C : (Fin n → Ω) → ℝ :=
    C.indicator (fun _ : Fin n → Ω => H)
  change M.real D ≤ (1 / 4 : ℝ) ∧ M.real C ≤ (1 / 4 : ℝ)
  have hStats : Measurable S ∧ Measurable Q ∧
      Integrable (fun x : Fin n → Ω => (S x) ^ (2 : ℕ)) M ∧
      Integrable Q M ∧
      (∫ x : Fin n → Ω, (S x) ^ (2 : ℕ) ∂M) = N ∧
      (∫ x : Fin n → Ω, Q x ∂M) = N :=
    original_sample_second_moments n μ g hg hg2 hgmean hgsecond
  have hSMeas : Measurable S := hStats.1
  have hQMeas : Measurable Q := hStats.2.1
  have hS2Int : Integrable
      (fun x : Fin n → Ω => (S x) ^ (2 : ℕ)) M := hStats.2.2.1
  have hQInt : Integrable Q M := hStats.2.2.2.1
  have hS2Mean :
      (∫ x : Fin n → Ω, (S x) ^ (2 : ℕ) ∂M) = N := hStats.2.2.2.2.1
  have hQMean : (∫ x : Fin n → Ω, Q x ∂M) = N := hStats.2.2.2.2.2
  have hN : (0 : ℝ) < N := by
    dsimp [N]
    exact_mod_cast hn
  have hH : (0 : ℝ) < H := by
    dsimp [H]
    positivity
  have hKnonneg : (0 : ℝ) ≤ K := by
    dsimp [K]
    positivity
  have hKsq : K ^ (2 : ℕ) = H := by
    dsimp [K, H]
    nlinarith only [Real.sq_sqrt hN.le]
  have hQnonneg : ∀ x : Fin n → Ω, (0 : ℝ) ≤ Q x := by
    intro x
    dsimp [Q, sampleEnergy]
    exact Finset.sum_nonneg
      (fun (i : Fin n) (_ : i ∈ (Finset.univ : Finset (Fin n))) => sq_nonneg (g (x i)))
  have hAm : MeasurableSet A :=
    measurableSet_lt measurable_const (hSMeas.pow_const (2 : ℕ))
  have hCm : MeasurableSet C :=
    measurableSet_lt measurable_const hQMeas
  have hDA : D = A := by
    ext x
    change K < |S x| ↔ H < (S x) ^ (2 : ℕ)
    constructor
    · intro hlt
      have hprod : (0 : ℝ) < (|S x| - K) * (|S x| + K) :=
        mul_pos (sub_pos.mpr hlt) (by
          linarith only [hlt, hKnonneg, abs_nonneg (S x)])
      nlinarith only [hprod, sq_abs (S x), hKsq]
    · intro hsq
      have hnle : ¬ |S x| ≤ K := by
        intro hle
        have hprod : (0 : ℝ) ≤ (K - |S x|) * (K + |S x|) :=
          mul_nonneg (sub_nonneg.mpr hle)
            (add_nonneg hKnonneg (abs_nonneg (S x)))
        nlinarith only [hprod, sq_abs (S x), hKsq, hsq]
      exact lt_of_not_ge hnle
  have hI_AInt : Integrable I_A M :=
    (integrable_const H).indicator hAm
  have hI_CInt : Integrable I_C M :=
    (integrable_const H).indicator hCm
  have hI_AMono : ∀ x : Fin n → Ω, I_A x ≤ (S x) ^ (2 : ℕ) := by
    intro x
    change A.indicator (fun _ : Fin n → Ω => H) x ≤ (S x) ^ (2 : ℕ)
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      exact le_of_lt hx
    · rw [Set.indicator_of_notMem hx]
      exact sq_nonneg (S x)
  have hI_CMono : ∀ x : Fin n → Ω, I_C x ≤ Q x := by
    intro x
    change C.indicator (fun _ : Fin n → Ω => H) x ≤ Q x
    by_cases hx : x ∈ C
    · rw [Set.indicator_of_mem hx]
      exact le_of_lt hx
    · rw [Set.indicator_of_notMem hx]
      exact hQnonneg x
  have hMarkA : H * M.real A ≤ N := by
    calc
      H * M.real A = ∫ x : Fin n → Ω, I_A x ∂M := by
        change H * M.real A =
          ∫ x : Fin n → Ω, A.indicator (fun _ : Fin n → Ω => H) x ∂M
        rw [integral_indicator_const H hAm, smul_eq_mul, mul_comm]
      _ ≤ ∫ x : Fin n → Ω, (S x) ^ (2 : ℕ) ∂M :=
        integral_mono hI_AInt hS2Int hI_AMono
      _ = N := hS2Mean
  have hMarkC : H * M.real C ≤ N := by
    calc
      H * M.real C = ∫ x : Fin n → Ω, I_C x ∂M := by
        change H * M.real C =
          ∫ x : Fin n → Ω, C.indicator (fun _ : Fin n → Ω => H) x ∂M
        rw [integral_indicator_const H hCm, smul_eq_mul, mul_comm]
      _ ≤ ∫ x : Fin n → Ω, Q x ∂M :=
        integral_mono hI_CInt hQInt hI_CMono
      _ = N := hQMean
  have hQuarter : H * (1 / 4 : ℝ) = N := by
    dsimp [H]
    ring
  have hAprob : M.real A ≤ (1 / 4 : ℝ) := by
    by_contra hnot
    have hprod : (0 : ℝ) < H * (M.real A - (1 / 4 : ℝ)) :=
      mul_pos hH (sub_pos.mpr (lt_of_not_ge hnot))
    nlinarith only [hprod, hMarkA, hQuarter]
  have hCprob : M.real C ≤ (1 / 4 : ℝ) := by
    by_contra hnot
    have hprod : (0 : ℝ) < H * (M.real C - (1 / 4 : ℝ)) :=
      mul_pos hH (sub_pos.mpr (lt_of_not_ge hnot))
    nlinarith only [hprod, hMarkC, hQuarter]
  have hDprob : M.real D ≤ (1 / 4 : ℝ) := by
    rw [hDA]
    exact hAprob
  exact ⟨hDprob, hCprob⟩

theorem original_ghost_good_event
    (n : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgmean : (∫ o : Ω, g o ∂μ) = 0)
    (hgsecond : (∫ o : Ω, (g o) ^ (2 : ℕ) ∂μ) = 1) :
    MeasurableSet (goodEvent n g) ∧
      (1 / 2 : ℝ) ≤
        (Shao.OQ6.CanonicalDoubleGhostRowMoments.sampleLaw n μ).real (goodEvent n g) := by
  let M : Measure (Fin n → Ω) :=
    Shao.OQ6.CanonicalDoubleGhostRowMoments.sampleLaw n μ
  letI hProbM : IsProbabilityMeasure M :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => μ)))
  let N : ℝ := (n : ℝ)
  let S : (Fin n → Ω) → ℝ := sampleSum n g
  let Q : (Fin n → Ω) → ℝ := sampleEnergy n g
  let B : Set (Fin n → Ω) := goodEvent n g
  change MeasurableSet B ∧ (1 / 2 : ℝ) ≤ M.real B
  have hSMeas : Measurable S :=
    (original_sample_second_moments n μ g hg hg2 hgmean hgsecond).1
  have hQMeas : Measurable Q :=
    (original_sample_second_moments n μ g hg hg2 hgmean hgsecond).2.1
  have hBMeas : MeasurableSet B := by
    change MeasurableSet {x : Fin n → Ω |
      |S x| ≤ (2 : ℝ) * Real.sqrt N ∧ Q x ≤ (4 : ℝ) * N}
    exact (measurableSet_le
      (continuous_abs.measurable.comp hSMeas) measurable_const).inter
      (measurableSet_le hQMeas measurable_const)
  have hMassOne : M.real Set.univ = (1 : ℝ) := by
    change (M Set.univ).toReal = (1 : ℝ)
    rw [measure_univ, ENNReal.toReal_one]
  by_cases hn0 : n = 0
  · subst n
    have hBzero : goodEvent 0 g = Set.univ := by
      ext x
      simp [goodEvent, sampleSum, sampleEnergy]
    refine ⟨hBMeas, ?_⟩
    change (1 / 2 : ℝ) ≤ M.real (goodEvent 0 g)
    rw [hBzero, hMassOne]
    norm_num
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    let H : ℝ := (4 : ℝ) * N
    let K : ℝ := (2 : ℝ) * Real.sqrt N
    let D : Set (Fin n → Ω) := {x : Fin n → Ω | K < |S x|}
    let C : Set (Fin n → Ω) := {x : Fin n → Ω | H < Q x}
    have hBad : M.real D ≤ (1 / 4 : ℝ) ∧ M.real C ≤ (1 / 4 : ℝ) :=
      original_ghost_strict_bad_bounds n hn μ g hg hg2 hgmean hgsecond
    have hBcompl : Bᶜ = D ∪ C := by
      ext x
      change ¬ (|S x| ≤ K ∧ Q x ≤ H) ↔ K < |S x| ∨ H < Q x
      constructor
      · intro hx
        by_cases hs : |S x| ≤ K
        · exact Or.inr (lt_of_not_ge
            (fun hq : Q x ≤ H => hx ⟨hs, hq⟩))
        · exact Or.inl (lt_of_not_ge hs)
      · intro hx hgood
        rcases hx with hs | hq
        · exact (not_lt_of_ge hgood.1) hs
        · exact (not_lt_of_ge hgood.2) hq
    have hComplBound : M.real Bᶜ ≤ (1 / 2 : ℝ) := by
      rw [hBcompl]
      calc
        M.real (D ∪ C) ≤ M.real D + M.real C := measureReal_union_le D C
        _ ≤ (1 / 4 : ℝ) + (1 / 4 : ℝ) := add_le_add hBad.1 hBad.2
        _ = (1 / 2 : ℝ) := by norm_num
    have hBMass : M.real B + M.real Bᶜ = (1 : ℝ) := by
      calc
        M.real B + M.real Bᶜ = M.real Set.univ :=
          measureReal_add_measureReal_compl hBMeas
        _ = 1 := hMassOne
    refine ⟨hBMeas, ?_⟩
    linarith only [hBMass, hComplBound]

end

end Shao.OQ6.OriginalGhostGoodEvent
