import Shao.OQ6.NormalizedRemainderEnvelope
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Shao.OQ6.WeightedCostClipping

noncomputable section

open MeasureTheory
open scoped BigOperators Classical Topology

theorem natural_clipping_envelope_contract
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (D1 D2 A B : Ω → ℝ)
    (Adelete Bdelete : Fin n → Ω → ℝ)
    (hD1 : Measurable D1) (hD2 : Measurable D2)
    (hA : Measurable A) (hB : Measurable B)
    (hAdelete : ∀ i : Fin n, Measurable (Adelete i))
    (hBdelete : ∀ i : Fin n, Measurable (Bdelete i))
    (hAnonneg : ∀ ω : Ω, 0 ≤ A ω)
    (hBnonneg : ∀ ω : Ω, 0 ≤ B ω)
    (hAdeletenonneg : ∀ (i : Fin n) (ω : Ω), 0 ≤ Adelete i ω)
    (hBdeletenonneg : ∀ (i : Fin n) (ω : Ω), 0 ≤ Bdelete i ω)
    (hD1A : ∀ᵐ ω ∂ν, |D1 ω| ≤ A ω)
    (hD2B : ∀ᵐ ω ∂ν, |D2 ω| ≤ B ω)
    (hD2pos : ∀ᵐ ω ∂ν, 0 < 1 + D2 ω) :
    let D1M : ℕ → Ω → ℝ := fun M ω => max (-(M : ℝ)) (min (D1 ω) (M : ℝ))
    let D2M : ℕ → Ω → ℝ := fun M ω => min (D2 ω) (M : ℝ)
    let AM : ℕ → Ω → ℝ := fun M ω => min (A ω) (M : ℝ)
    let BM : ℕ → Ω → ℝ := fun M ω => min (B ω) (M : ℝ)
    let AdeleteM : ℕ → Fin n → Ω → ℝ := fun M i ω => min (Adelete i ω) (M : ℝ)
    let BdeleteM : ℕ → Fin n → Ω → ℝ := fun M i ω => min (Bdelete i ω) (M : ℝ)
    let G : Set Ω := {ω : Ω | 0 < 1 + D2 ω ∧ |D1 ω| ≤ A ω ∧ |D2 ω| ≤ B ω}
    let D1goodM : ℕ → Ω → ℝ := fun M ω => if ω ∈ G then D1M M ω else 0
    let D2goodM : ℕ → Ω → ℝ := fun M ω => if ω ∈ G then D2M M ω else 0
    MeasurableSet G ∧ ν G = 1 ∧
    (∀ M : ℕ, Measurable (D1M M) ∧ Measurable (D2M M) ∧
      Measurable (AM M) ∧ Measurable (BM M) ∧
      Measurable (D1goodM M) ∧ Measurable (D2goodM M)) ∧
    (∀ (M : ℕ) (i : Fin n), Measurable (AdeleteM M i) ∧ Measurable (BdeleteM M i)) ∧
    (∀ (M : ℕ) (ω : Ω), 0 ≤ AM M ω ∧ AM M ω ≤ A ω ∧ AM M ω ≤ (M : ℝ) ∧
      0 ≤ BM M ω ∧ BM M ω ≤ B ω ∧ BM M ω ≤ (M : ℝ)) ∧
    (∀ (M : ℕ) (i : Fin n) (ω : Ω),
      0 ≤ AdeleteM M i ω ∧ AdeleteM M i ω ≤ Adelete i ω ∧ AdeleteM M i ω ≤ (M : ℝ) ∧
      0 ≤ BdeleteM M i ω ∧ BdeleteM M i ω ≤ Bdelete i ω ∧ BdeleteM M i ω ≤ (M : ℝ)) ∧
    (∀ (M : ℕ) (i : Fin n) (ω : Ω),
      |AM M ω - AdeleteM M i ω| ≤ |A ω - Adelete i ω| ∧
      |BM M ω - BdeleteM M i ω| ≤ |B ω - Bdelete i ω|) ∧
    (∀ M : ℕ, Integrable (AM M) ν ∧ Integrable (BM M) ν ∧
      ∀ i : Fin n, Integrable (AdeleteM M i) ν ∧ Integrable (BdeleteM M i) ν) ∧
    (∀ M : ℕ, 1 ≤ M → Integrable (D1M M) ν ∧ Integrable (D2M M) ν ∧
      Integrable (D1goodM M) ν ∧ Integrable (D2goodM M) ν) ∧
    (∀ M : ℕ, 1 ≤ M → ∀ᵐ ω ∂ν,
      0 < 1 + D2M M ω ∧ |D1M M ω| ≤ AM M ω ∧ |D2M M ω| ≤ BM M ω) ∧
    (∀ (M : ℕ), 1 ≤ M → ∀ ω : Ω,
      0 < 1 + D2goodM M ω ∧ |D1goodM M ω| ≤ AM M ω ∧ |D2goodM M ω| ≤ BM M ω) ∧
    (∀ M : ℕ, D1goodM M =ᵐ[ν] D1M M ∧ D2goodM M =ᵐ[ν] D2M M) ∧
    (∀ ω : Ω, ∀ᶠ M : ℕ in Filter.atTop,
      D1M M ω = D1 ω ∧ D2M M ω = D2 ω ∧ AM M ω = A ω ∧ BM M ω = B ω ∧
      ∀ i : Fin n, AdeleteM M i ω = Adelete i ω ∧ BdeleteM M i ω = Bdelete i ω) := by
  classical
  dsimp only
  let D1M : ℕ → Ω → ℝ := fun M ω => max (-(M : ℝ)) (min (D1 ω) (M : ℝ))
  let D2M : ℕ → Ω → ℝ := fun M ω => min (D2 ω) (M : ℝ)
  let AM : ℕ → Ω → ℝ := fun M ω => min (A ω) (M : ℝ)
  let BM : ℕ → Ω → ℝ := fun M ω => min (B ω) (M : ℝ)
  let AdeleteM : ℕ → Fin n → Ω → ℝ := fun M i ω => min (Adelete i ω) (M : ℝ)
  let BdeleteM : ℕ → Fin n → Ω → ℝ := fun M i ω => min (Bdelete i ω) (M : ℝ)
  let G : Set Ω := {ω : Ω | 0 < 1 + D2 ω ∧ |D1 ω| ≤ A ω ∧ |D2 ω| ≤ B ω}
  let D1goodM : ℕ → Ω → ℝ := fun M ω => if ω ∈ G then D1M M ω else 0
  let D2goodM : ℕ → Ω → ℝ := fun M ω => if ω ∈ G then D2M M ω else 0
  have hminlip (a b c : ℝ) : |min a c - min b c| ≤ |a - b| := by
    by_cases ha : a ≤ c <;> by_cases hb : b ≤ c
    · simp only [min_eq_left ha, min_eq_left hb, le_refl]
    · rw [min_eq_left ha, min_eq_right (le_of_not_ge hb),
        abs_of_nonpos (sub_nonpos.mpr ha), abs_of_nonpos (by linarith : a - b ≤ 0)]
      linarith
    · rw [min_eq_right (le_of_not_ge ha), min_eq_left hb,
        abs_of_nonneg (sub_nonneg.mpr hb), abs_of_nonneg (by linarith : 0 ≤ a - b)]
      linarith
    · simp only [min_eq_right (le_of_not_ge ha), min_eq_right (le_of_not_ge hb),
        sub_self, abs_zero, abs_nonneg]
  have hclip (d a m : ℝ) (hm : 0 ≤ m) (ha : 0 ≤ a) (hd : |d| ≤ a) :
      |max (-m) (min d m)| ≤ min a m := by
    rcases abs_le.mp hd with ⟨hlo, hhi⟩
    apply abs_le.mpr
    constructor
    · by_cases ham : a ≤ m
      · rw [min_eq_left ham]
        exact (le_min hlo (by linarith)).trans (le_max_right _ _)
      · rw [min_eq_right (le_of_not_ge ham)]
        exact le_max_left _ _
    · exact le_min
        (max_le (by linarith) ((min_le_left d m).trans hhi))
        (max_le (by linarith) (min_le_right d m))
  have hden (d b m : ℝ) (hm : 1 ≤ m) (hp : 0 < 1 + d) (hb : |d| ≤ b) :
      0 < 1 + min d m ∧ |min d m| ≤ min b m := by
    constructor
    · by_cases hdm : d ≤ m
      · simpa only [min_eq_left hdm] using hp
      · rw [min_eq_right (le_of_not_ge hdm)]
        linarith
    · by_cases hd : 0 ≤ d
      · rw [abs_of_nonneg (le_min hd (by linarith))]
        exact min_le_min (by simpa only [abs_of_nonneg hd] using hb) le_rfl
      · have hdm : d ≤ m := by linarith
        rw [min_eq_left hdm]
        exact le_min hb (by rw [abs_of_neg (lt_of_not_ge hd)]; linarith)
  have hminEvent (a : ℝ) : ∀ᶠ M : ℕ in Filter.atTop, min a (M : ℝ) = a := by
    obtain ⟨N, hN⟩ := exists_nat_gt a
    filter_upwards [Filter.eventually_ge_atTop N] with M hM
    exact min_eq_left (hN.le.trans (by exact_mod_cast hM))
  have hclipEvent (a : ℝ) : ∀ᶠ M : ℕ in Filter.atTop,
      max (-(M : ℝ)) (min a (M : ℝ)) = a := by
    obtain ⟨N, hN⟩ := exists_nat_gt |a|
    filter_upwards [Filter.eventually_ge_atTop N] with M hM
    have hbound : |a| ≤ (M : ℝ) := hN.le.trans (by exact_mod_cast hM)
    rw [min_eq_left ((le_abs_self a).trans hbound), max_eq_right (by linarith [neg_abs_le a])]
  have hG : MeasurableSet G :=
    (measurableSet_lt measurable_const (measurable_const.add hD2)).inter
      ((measurableSet_le (continuous_abs.measurable.comp hD1) hA).inter
        (measurableSet_le (continuous_abs.measurable.comp hD2) hB))
  have hGae : ∀ᵐ ω ∂ν, ω ∈ G := by
    filter_upwards [hD2pos, hD1A, hD2B] with ω hp ha hb
    exact ⟨hp, ha, hb⟩
  have hGmass : ν G = 1 := by
    have heq : G =ᵐ[ν] Set.univ := hGae.mono fun ω h => propext ⟨fun _ => Set.mem_univ _, fun _ => h⟩
    simpa only [measure_univ] using (measure_congr heq)
  have hm (M : ℕ) : Measurable (D1M M) ∧ Measurable (D2M M) ∧
      Measurable (AM M) ∧ Measurable (BM M) ∧
      Measurable (D1goodM M) ∧ Measurable (D2goodM M) := by
    have h1 : Measurable (D1M M) := measurable_const.max (hD1.min measurable_const)
    have h2 : Measurable (D2M M) := hD2.min measurable_const
    exact ⟨h1, h2, hA.min measurable_const, hB.min measurable_const,
      Measurable.ite hG h1 measurable_const, Measurable.ite hG h2 measurable_const⟩
  have hdm (M : ℕ) (i : Fin n) : Measurable (AdeleteM M i) ∧ Measurable (BdeleteM M i) :=
    ⟨(hAdelete i).min measurable_const, (hBdelete i).min measurable_const⟩
  have hb (M : ℕ) (ω : Ω) : 0 ≤ AM M ω ∧ AM M ω ≤ A ω ∧ AM M ω ≤ (M : ℝ) ∧
      0 ≤ BM M ω ∧ BM M ω ≤ B ω ∧ BM M ω ≤ (M : ℝ) :=
    ⟨le_min (hAnonneg ω) (Nat.cast_nonneg M), min_le_left _ _, min_le_right _ _,
      le_min (hBnonneg ω) (Nat.cast_nonneg M), min_le_left _ _, min_le_right _ _⟩
  have hdb (M : ℕ) (i : Fin n) (ω : Ω) :
      0 ≤ AdeleteM M i ω ∧ AdeleteM M i ω ≤ Adelete i ω ∧ AdeleteM M i ω ≤ (M : ℝ) ∧
      0 ≤ BdeleteM M i ω ∧ BdeleteM M i ω ≤ Bdelete i ω ∧ BdeleteM M i ω ≤ (M : ℝ) :=
    ⟨le_min (hAdeletenonneg i ω) (Nat.cast_nonneg M), min_le_left _ _, min_le_right _ _,
      le_min (hBdeletenonneg i ω) (Nat.cast_nonneg M), min_le_left _ _, min_le_right _ _⟩
  have hboundedInt (f : Ω → ℝ) (hf : Measurable f) (M : ℕ)
      (hbound : ∀ᵐ ω ∂ν, |f ω| ≤ (M : ℝ)) : Integrable f ν := by
    exact (integrable_const (M : ℝ)).mono' hf.aestronglyMeasurable
      (hbound.mono fun _ h => by simpa only [Real.norm_eq_abs] using h)
  have henvInt (M : ℕ) : Integrable (AM M) ν ∧ Integrable (BM M) ν ∧
      ∀ i : Fin n, Integrable (AdeleteM M i) ν ∧ Integrable (BdeleteM M i) ν := by
    refine ⟨hboundedInt _ (hm M).2.2.1 M ?_, hboundedInt _ (hm M).2.2.2.1 M ?_, ?_⟩
    · exact Filter.Eventually.of_forall fun ω => by rw [abs_of_nonneg (hb M ω).1]; exact (hb M ω).2.2.1
    · exact Filter.Eventually.of_forall fun ω => by rw [abs_of_nonneg (hb M ω).2.2.2.1]; exact (hb M ω).2.2.2.2.2
    · intro i
      refine ⟨hboundedInt _ (hdm M i).1 M ?_, hboundedInt _ (hdm M i).2 M ?_⟩
      · exact Filter.Eventually.of_forall fun ω => by rw [abs_of_nonneg (hdb M i ω).1]; exact (hdb M i ω).2.2.1
      · exact Filter.Eventually.of_forall fun ω => by rw [abs_of_nonneg (hdb M i ω).2.2.2.1]; exact (hdb M i ω).2.2.2.2.2
  have hvalid (M : ℕ) (hM : 1 ≤ M) : ∀ᵐ ω ∂ν,
      0 < 1 + D2M M ω ∧ |D1M M ω| ≤ AM M ω ∧ |D2M M ω| ≤ BM M ω := by
    filter_upwards [hGae] with ω hg
    have hd := hden (D2 ω) (B ω) (M : ℝ) (by exact_mod_cast hM) hg.1 hg.2.2
    exact ⟨hd.1, hclip _ _ _ (Nat.cast_nonneg M) (hAnonneg ω) hg.2.1, hd.2⟩
  have hgood (M : ℕ) (hM : 1 ≤ M) (ω : Ω) :
      0 < 1 + D2goodM M ω ∧ |D1goodM M ω| ≤ AM M ω ∧ |D2goodM M ω| ≤ BM M ω := by
    by_cases hg : ω ∈ G
    · have hd := hden (D2 ω) (B ω) (M : ℝ) (by exact_mod_cast hM) hg.1 hg.2.2
      simpa only [D1goodM, D2goodM, if_pos hg] using
        And.intro hd.1 (And.intro (hclip _ _ _ (Nat.cast_nonneg M) (hAnonneg ω) hg.2.1) hd.2)
    · simpa only [D1goodM, D2goodM, if_neg hg, abs_zero, add_zero] using
        And.intro (by norm_num : (0 : ℝ) < 1) (And.intro (hb M ω).1 (hb M ω).2.2.2.1)
  have hDint (M : ℕ) (hM : 1 ≤ M) : Integrable (D1M M) ν ∧ Integrable (D2M M) ν ∧
      Integrable (D1goodM M) ν ∧ Integrable (D2goodM M) ν := by
    refine ⟨hboundedInt _ (hm M).1 M ?_, hboundedInt _ (hm M).2.1 M ?_,
      hboundedInt _ (hm M).2.2.2.2.1 M ?_, hboundedInt _ (hm M).2.2.2.2.2 M ?_⟩
    · exact (hvalid M hM).mono fun ω h => h.2.1.trans (hb M ω).2.2.1
    · exact (hvalid M hM).mono fun ω h => h.2.2.trans (hb M ω).2.2.2.2.2
    · exact Filter.Eventually.of_forall fun ω => (hgood M hM ω).2.1.trans (hb M ω).2.2.1
    · exact Filter.Eventually.of_forall fun ω => (hgood M hM ω).2.2.trans (hb M ω).2.2.2.2.2
  have hgoodEq (M : ℕ) : D1goodM M =ᵐ[ν] D1M M ∧ D2goodM M =ᵐ[ν] D2M M := by
    constructor <;> filter_upwards [hGae] with ω hg <;> simp only [D1goodM, D2goodM, if_pos hg]
  have hevent (ω : Ω) : ∀ᶠ M : ℕ in Filter.atTop,
      D1M M ω = D1 ω ∧ D2M M ω = D2 ω ∧ AM M ω = A ω ∧ BM M ω = B ω ∧
      ∀ i : Fin n, AdeleteM M i ω = Adelete i ω ∧ BdeleteM M i ω = Bdelete i ω := by
    have hd : ∀ᶠ M : ℕ in Filter.atTop, ∀ i : Fin n,
        AdeleteM M i ω = Adelete i ω ∧ BdeleteM M i ω = Bdelete i ω := by
      rw [Filter.eventually_all]
      intro i
      exact (hminEvent (Adelete i ω)).and (hminEvent (Bdelete i ω))
    filter_upwards [hclipEvent (D1 ω), hminEvent (D2 ω), hminEvent (A ω), hminEvent (B ω), hd]
      with M h1 h2 ha hb hd
    exact ⟨h1, h2, ha, hb, hd⟩
  exact ⟨hG, hGmass, hm, hdm, hb, hdb,
    (fun M i ω => ⟨hminlip _ _ _, hminlip _ _ _⟩), henvInt, hDint, hvalid, hgood, hgoodEq, hevent⟩

theorem natural_clipping_preserves_scalar_factorizations
    {Ω : Type*} (n : ℕ)
    (C : Ω → (Fin n → ℝ))
    (D1 D2 A B : Ω → ℝ) (Adelete Bdelete : Fin n → Ω → ℝ)
    (F1 F2 FA FB : (Fin n → ℝ) → ℝ)
    (FAdelete FBdelete : ∀ i : Fin n, ({j : Fin n // j ≠ i} → ℝ) → ℝ)
    (hF1 : Measurable[borel (Fin n → ℝ), borel ℝ] F1)
    (hF2 : Measurable[borel (Fin n → ℝ), borel ℝ] F2)
    (hFA : Measurable[borel (Fin n → ℝ), borel ℝ] FA)
    (hFB : Measurable[borel (Fin n → ℝ), borel ℝ] FB)
    (hFAdelete : ∀ i : Fin n, Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] (FAdelete i))
    (hFBdelete : ∀ i : Fin n, Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] (FBdelete i))
    (hfull : ∀ ω : Ω, D1 ω = F1 (C ω) ∧ D2 ω = F2 (C ω) ∧ A ω = FA (C ω) ∧ B ω = FB (C ω))
    (hdeleted : ∀ (i : Fin n) (ω : Ω),
      Adelete i ω = FAdelete i (fun j => C ω j.1) ∧ Bdelete i ω = FBdelete i (fun j => C ω j.1)) :
    let F1M : ℕ → (Fin n → ℝ) → ℝ := fun M v => max (-(M : ℝ)) (min (F1 v) (M : ℝ))
    let F2M : ℕ → (Fin n → ℝ) → ℝ := fun M v => min (F2 v) (M : ℝ)
    let FAM : ℕ → (Fin n → ℝ) → ℝ := fun M v => min (FA v) (M : ℝ)
    let FBM : ℕ → (Fin n → ℝ) → ℝ := fun M v => min (FB v) (M : ℝ)
    let FAdeleteM : ℕ → ∀ i : Fin n, ({j : Fin n // j ≠ i} → ℝ) → ℝ := fun M i v => min (FAdelete i v) (M : ℝ)
    let FBdeleteM : ℕ → ∀ i : Fin n, ({j : Fin n // j ≠ i} → ℝ) → ℝ := fun M i v => min (FBdelete i v) (M : ℝ)
    let F1goodM : ℕ → (Fin n → ℝ) → ℝ := fun M v => if 0 < 1 + F2 v ∧ |F1 v| ≤ FA v ∧ |F2 v| ≤ FB v then F1M M v else 0
    let F2goodM : ℕ → (Fin n → ℝ) → ℝ := fun M v => if 0 < 1 + F2 v ∧ |F1 v| ≤ FA v ∧ |F2 v| ≤ FB v then F2M M v else 0
    (∀ M : ℕ,
      Measurable[borel (Fin n → ℝ), borel ℝ] (F1M M) ∧
      Measurable[borel (Fin n → ℝ), borel ℝ] (F2M M) ∧
      Measurable[borel (Fin n → ℝ), borel ℝ] (FAM M) ∧
      Measurable[borel (Fin n → ℝ), borel ℝ] (FBM M) ∧
      Measurable[borel (Fin n → ℝ), borel ℝ] (F1goodM M) ∧
      Measurable[borel (Fin n → ℝ), borel ℝ] (F2goodM M)) ∧
    (∀ (M : ℕ) (i : Fin n),
      Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] (FAdeleteM M i) ∧
      Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] (FBdeleteM M i) ∧
      Measurable[borel (Fin n → ℝ), borel ℝ] (fun v : Fin n → ℝ => FAdeleteM M i (fun j => v j.1)) ∧
      Measurable[borel (Fin n → ℝ), borel ℝ] (fun v : Fin n → ℝ => FBdeleteM M i (fun j => v j.1))) ∧
    (∀ (M : ℕ) (ω : Ω),
      max (-(M : ℝ)) (min (D1 ω) (M : ℝ)) = F1M M (C ω) ∧
      min (D2 ω) (M : ℝ) = F2M M (C ω) ∧
      min (A ω) (M : ℝ) = FAM M (C ω) ∧
      min (B ω) (M : ℝ) = FBM M (C ω) ∧
      (if 0 < 1 + D2 ω ∧ |D1 ω| ≤ A ω ∧ |D2 ω| ≤ B ω then max (-(M : ℝ)) (min (D1 ω) (M : ℝ)) else 0) = F1goodM M (C ω) ∧
      (if 0 < 1 + D2 ω ∧ |D1 ω| ≤ A ω ∧ |D2 ω| ≤ B ω then min (D2 ω) (M : ℝ) else 0) = F2goodM M (C ω)) ∧
    (∀ (M : ℕ) (i : Fin n) (ω : Ω),
      min (Adelete i ω) (M : ℝ) = FAdeleteM M i (fun j => C ω j.1) ∧
      min (Bdelete i ω) (M : ℝ) = FBdeleteM M i (fun j => C ω j.1)) := by
  classical
  dsimp only
  let F1M : ℕ → (Fin n → ℝ) → ℝ := fun M v => max (-(M : ℝ)) (min (F1 v) (M : ℝ))
  let F2M : ℕ → (Fin n → ℝ) → ℝ := fun M v => min (F2 v) (M : ℝ)
  let FAM : ℕ → (Fin n → ℝ) → ℝ := fun M v => min (FA v) (M : ℝ)
  let FBM : ℕ → (Fin n → ℝ) → ℝ := fun M v => min (FB v) (M : ℝ)
  let FAdeleteM : ℕ → ∀ i : Fin n, ({j : Fin n // j ≠ i} → ℝ) → ℝ := fun M i v => min (FAdelete i v) (M : ℝ)
  let FBdeleteM : ℕ → ∀ i : Fin n, ({j : Fin n // j ≠ i} → ℝ) → ℝ := fun M i v => min (FBdelete i v) (M : ℝ)
  let F1goodM : ℕ → (Fin n → ℝ) → ℝ := fun M v => if 0 < 1 + F2 v ∧ |F1 v| ≤ FA v ∧ |F2 v| ≤ FB v then F1M M v else 0
  let F2goodM : ℕ → (Fin n → ℝ) → ℝ := fun M v => if 0 < 1 + F2 v ∧ |F1 v| ≤ FA v ∧ |F2 v| ≤ FB v then F2M M v else 0
  have hG : @MeasurableSet (Fin n → ℝ) (borel (Fin n → ℝ))
      {v : Fin n → ℝ | 0 < 1 + F2 v ∧ |F1 v| ≤ FA v ∧ |F2 v| ≤ FB v} :=
    (measurableSet_lt measurable_const (measurable_const.add hF2)).inter
      ((measurableSet_le (continuous_abs.measurable.comp hF1) hFA).inter
        (measurableSet_le (continuous_abs.measurable.comp hF2) hFB))
  have hm (M : ℕ) :
      Measurable[borel (Fin n → ℝ), borel ℝ] (F1M M) ∧
      Measurable[borel (Fin n → ℝ), borel ℝ] (F2M M) ∧
      Measurable[borel (Fin n → ℝ), borel ℝ] (FAM M) ∧
      Measurable[borel (Fin n → ℝ), borel ℝ] (FBM M) ∧
      Measurable[borel (Fin n → ℝ), borel ℝ] (F1goodM M) ∧
      Measurable[borel (Fin n → ℝ), borel ℝ] (F2goodM M) := by
    have h1 : Measurable[borel (Fin n → ℝ), borel ℝ] (F1M M) :=
      measurable_const.max (hF1.min measurable_const)
    have h2 : Measurable[borel (Fin n → ℝ), borel ℝ] (F2M M) := hF2.min measurable_const
    exact ⟨h1, h2, hFA.min measurable_const, hFB.min measurable_const,
      Measurable.ite hG h1 measurable_const, Measurable.ite hG h2 measurable_const⟩
  have hdel (M : ℕ) (i : Fin n) :
      Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] (FAdeleteM M i) ∧
      Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] (FBdeleteM M i) ∧
      Measurable[borel (Fin n → ℝ), borel ℝ] (fun v : Fin n → ℝ => FAdeleteM M i (fun j => v j.1)) ∧
      Measurable[borel (Fin n → ℝ), borel ℝ] (fun v : Fin n → ℝ => FBdeleteM M i (fun j => v j.1)) := by
    have hrestrict : Measurable[borel (Fin n → ℝ), borel ({j : Fin n // j ≠ i} → ℝ)]
        (fun v : Fin n → ℝ => fun j : {j : Fin n // j ≠ i} => v j.1) :=
      (continuous_pi fun j => continuous_apply j.1).borel_measurable
    have ha : Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] (FAdeleteM M i) :=
      (hFAdelete i).min measurable_const
    have hb : Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] (FBdeleteM M i) :=
      (hFBdelete i).min measurable_const
    exact ⟨ha, hb, ha.comp hrestrict, hb.comp hrestrict⟩
  refine ⟨hm, hdel, ?_, ?_⟩
  · intro M ω
    rcases hfull ω with ⟨h1, h2, ha, hb⟩
    simp only [F1M, F2M, FAM, FBM, F1goodM, F2goodM, h1, h2, ha, hb, and_self]
  · intro M i ω
    rcases hdeleted i ω with ⟨ha, hb⟩
    simp only [FAdeleteM, FBdeleteM, ha, hb, and_self]

theorem actual_weighted_source_cost_clipping_limits
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 1 ≤ n) (ξ : Fin n → Ω → ℝ)
    (hξ : ∀ i : Fin n, Measurable (ξ i))
    (A B : Ω → ℝ) (Adelete Bdelete : Fin n → Ω → ℝ)
    (hA : Measurable A) (hB : Measurable B)
    (hAdelete : ∀ i : Fin n, Measurable (Adelete i))
    (hBdelete : ∀ i : Fin n, Measurable (Bdelete i))
    (hAnonneg : ∀ ω : Ω, 0 ≤ A ω)
    (hBnonneg : ∀ ω : Ω, 0 ≤ B ω)
    (hAdeletenonneg : ∀ (i : Fin n) (ω : Ω), 0 ≤ Adelete i ω)
    (hBdeletenonneg : ∀ (i : Fin n) (ω : Ω), 0 ≤ Bdelete i ω)
    (x : ℝ) (hx : 0 < x)
    (hFull : Integrable (fun ω => (x * A ω + x ^ 2 * B ω) *
      Real.exp (∑ i : Fin n, (x * ξ i ω - (x * ξ i ω) ^ 2 / 2))) ν)
    (hDeleted : ∀ i : Fin n, Integrable (fun ω =>
      (min |x * ξ i ω| 1 * (|A ω - Adelete i ω| + x * |B ω - Bdelete i ω|)) *
      Real.exp (∑ j ∈ Finset.univ.erase i, (x * ξ j ω - (x * ξ j ω) ^ 2 / 2))) ν) :
    let ℓ : Fin n → Ω → ℝ := fun i ω => x * ξ i ω - (x * ξ i ω) ^ 2 / 2
    let S : Ω → ℝ := fun ω => ∑ i : Fin n, ℓ i ω
    let Sminus : Fin n → Ω → ℝ := fun i ω => ∑ j ∈ Finset.univ.erase i, ℓ j ω
    let I : ℝ := ∫ ω, Real.exp (S ω) ∂ν
    let J : Fin n → ℝ := fun i => ∫ ω, Real.exp (Sminus i ω) ∂ν
    let AM : ℕ → Ω → ℝ := fun M ω => min (A ω) (M : ℝ)
    let BM : ℕ → Ω → ℝ := fun M ω => min (B ω) (M : ℝ)
    let AdeleteM : ℕ → Fin n → Ω → ℝ := fun M i ω => min (Adelete i ω) (M : ℝ)
    let BdeleteM : ℕ → Fin n → Ω → ℝ := fun M i ω => min (Bdelete i ω) (M : ℝ)
    let cap : Fin n → Ω → ℝ := fun i ω => min |x * ξ i ω| 1
    let full : Ω → ℝ := fun ω => (x * A ω + x ^ 2 * B ω) * Real.exp (S ω)
    let fullM : ℕ → Ω → ℝ := fun M ω => (x * AM M ω + x ^ 2 * BM M ω) * Real.exp (S ω)
    let deleted : Fin n → Ω → ℝ := fun i ω => (cap i ω * (|A ω - Adelete i ω| + x * |B ω - Bdelete i ω|)) * Real.exp (Sminus i ω)
    let deletedM : ℕ → Fin n → Ω → ℝ := fun M i ω => (cap i ω * (|AM M ω - AdeleteM M i ω| + x * |BM M ω - BdeleteM M i ω|)) * Real.exp (Sminus i ω)
    let sourceCost : ℝ := ((∫ ω, full ω ∂ν) + ∑ i : Fin n, ∫ ω, deleted i ω ∂ν) / I
    let sourceCostM : ℕ → ℝ := fun M => ((∫ ω, fullM M ω ∂ν) + ∑ i : Fin n, ∫ ω, deletedM M i ω ∂ν) / I
    Integrable (fun ω => Real.exp (S ω)) ν ∧ 0 < I ∧
    (∀ i : Fin n, Integrable (fun ω => Real.exp (Sminus i ω)) ν ∧ 0 < J i) ∧
    Integrable (fun ω => Real.exp (S ω) / I) ν ∧ (∫ ω, Real.exp (S ω) / I ∂ν) = 1 ∧
    (∀ i : Fin n, Integrable (fun ω => Real.exp (Sminus i ω) / I) ν ∧
      (∫ ω, Real.exp (Sminus i ω) / I ∂ν) = J i / I ∧
      Integrable (fun ω => Real.exp (Sminus i ω) / J i) ν ∧
      (∫ ω, Real.exp (Sminus i ω) / J i ∂ν) = 1) ∧
    (∀ M : ℕ, Measurable (fullM M) ∧ Integrable (fullM M) ν ∧
      ∀ ω : Ω, 0 ≤ fullM M ω ∧ fullM M ω ≤ full ω) ∧
    (∀ (M : ℕ) (i : Fin n), Measurable (deletedM M i) ∧ Integrable (deletedM M i) ν ∧
      Integrable (fun ω => deletedM M i ω / I) ν ∧
      Integrable (fun ω => deletedM M i ω / J i) ν ∧
      ∀ ω : Ω, 0 ≤ deletedM M i ω ∧ deletedM M i ω ≤ deleted i ω) ∧
    (∀ ω : Ω, ∀ᶠ M : ℕ in Filter.atTop,
      fullM M ω = full ω ∧ ∀ i : Fin n, deletedM M i ω = deleted i ω) ∧
    Filter.Tendsto (fun M : ℕ => ∫ ω, |fullM M ω - full ω| ∂ν)
      Filter.atTop (nhds (0 : ℝ)) ∧
    (∀ i : Fin n, Filter.Tendsto (fun M : ℕ => ∫ ω, |deletedM M i ω - deleted i ω| ∂ν)
      Filter.atTop (nhds (0 : ℝ))) ∧
    Filter.Tendsto (fun M : ℕ => ∫ ω, fullM M ω ∂ν)
      Filter.atTop (nhds (∫ ω, full ω ∂ν)) ∧
    (∀ i : Fin n, Filter.Tendsto (fun M : ℕ => ∫ ω, deletedM M i ω ∂ν)
      Filter.atTop (nhds (∫ ω, deleted i ω ∂ν))) ∧
    Filter.Tendsto (fun M : ℕ => (∫ ω, fullM M ω ∂ν) / I)
      Filter.atTop (nhds ((∫ ω, full ω ∂ν) / I)) ∧
    (∀ i : Fin n,
      Filter.Tendsto (fun M : ℕ => (∫ ω, deletedM M i ω ∂ν) / I)
        Filter.atTop (nhds ((∫ ω, deleted i ω ∂ν) / I)) ∧
      Filter.Tendsto (fun M : ℕ => (∫ ω, deletedM M i ω ∂ν) / J i)
        Filter.atTop (nhds ((∫ ω, deleted i ω ∂ν) / J i)) ∧
      ((∫ ω, deleted i ω ∂ν) / I) = (J i / I) * ((∫ ω, deleted i ω ∂ν) / J i) ∧
      ∀ M : ℕ, ((∫ ω, deletedM M i ω ∂ν) / I) =
        (J i / I) * ((∫ ω, deletedM M i ω ∂ν) / J i)) ∧
    (∀ M : ℕ, 0 ≤ sourceCostM M ∧ sourceCostM M ≤ sourceCost) ∧
    Filter.Tendsto sourceCostM Filter.atTop (nhds sourceCost) := by
  classical
  dsimp only
  let ℓ : Fin n → Ω → ℝ := fun i ω => x * ξ i ω - (x * ξ i ω) ^ 2 / 2
  let S : Ω → ℝ := fun ω => ∑ i : Fin n, ℓ i ω
  let Sminus : Fin n → Ω → ℝ := fun i ω => ∑ j ∈ Finset.univ.erase i, ℓ j ω
  let I : ℝ := ∫ ω, Real.exp (S ω) ∂ν
  let J : Fin n → ℝ := fun i => ∫ ω, Real.exp (Sminus i ω) ∂ν
  let AM : ℕ → Ω → ℝ := fun M ω => min (A ω) (M : ℝ)
  let BM : ℕ → Ω → ℝ := fun M ω => min (B ω) (M : ℝ)
  let AdeleteM : ℕ → Fin n → Ω → ℝ := fun M i ω => min (Adelete i ω) (M : ℝ)
  let BdeleteM : ℕ → Fin n → Ω → ℝ := fun M i ω => min (Bdelete i ω) (M : ℝ)
  let cap : Fin n → Ω → ℝ := fun i ω => min |x * ξ i ω| 1
  let full : Ω → ℝ := fun ω => (x * A ω + x ^ 2 * B ω) * Real.exp (S ω)
  let fullM : ℕ → Ω → ℝ := fun M ω => (x * AM M ω + x ^ 2 * BM M ω) * Real.exp (S ω)
  let deleted : Fin n → Ω → ℝ := fun i ω => (cap i ω * (|A ω - Adelete i ω| + x * |B ω - Bdelete i ω|)) * Real.exp (Sminus i ω)
  let deletedM : ℕ → Fin n → Ω → ℝ := fun M i ω => (cap i ω * (|AM M ω - AdeleteM M i ω| + x * |BM M ω - BdeleteM M i ω|)) * Real.exp (Sminus i ω)
  let sourceCost : ℝ := ((∫ ω, full ω ∂ν) + ∑ i : Fin n, ∫ ω, deleted i ω ∂ν) / I
  let sourceCostM : ℕ → ℝ := fun M => ((∫ ω, fullM M ω ∂ν) + ∑ i : Fin n, ∫ ω, deletedM M i ω ∂ν) / I
  have hclips := natural_clipping_envelope_contract ν n (fun _ : Ω => 0) (fun _ : Ω => 0)
    A B Adelete Bdelete measurable_const measurable_const hA hB hAdelete hBdelete
    hAnonneg hBnonneg hAdeletenonneg hBdeletenonneg
    (Filter.Eventually.of_forall fun ω => by simpa only [abs_zero] using hAnonneg ω)
    (Filter.Eventually.of_forall fun ω => by simpa only [abs_zero] using hBnonneg ω)
    (Filter.Eventually.of_forall fun _ => by norm_num)
  rcases hclips with ⟨_, _, _, _, hb, _, hlip, _, _, _, _, _, hevent⟩
  have hℓm (i : Fin n) : Measurable (ℓ i) :=
    (measurable_const.mul (hξ i)).sub (((measurable_const.mul (hξ i)).pow_const 2).div_const 2)
  have hSm : Measurable S := Finset.measurable_sum Finset.univ (fun i _ => hℓm i)
  have hSmm (i : Fin n) : Measurable (Sminus i) :=
    Finset.measurable_sum (Finset.univ.erase i) (fun j _ => hℓm j)
  have hTilt (t : Finset (Fin n)) : Integrable (fun ω => Real.exp (∑ i ∈ t, ℓ i ω)) ν := by
    apply (integrable_const (Real.exp ((t.card : ℝ) / 2))).mono'
      (Finset.measurable_sum t (fun i _ => hℓm i)).exp.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      calc
        (∑ i ∈ t, ℓ i ω) ≤ ∑ _i ∈ t, (1 / 2 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          dsimp only [ℓ]
          nlinarith [sq_nonneg (x * ξ i ω - 1)]
        _ = (t.card : ℝ) / 2 := by simp [div_eq_mul_inv]
  have hSI : Integrable (fun ω => Real.exp (S ω)) ν := hTilt Finset.univ
  have hIpos : 0 < I := integral_exp_pos hSI
  have hJI (i : Fin n) : Integrable (fun ω => Real.exp (Sminus i ω)) ν ∧ 0 < J i := by
    have hi : Integrable (fun ω => Real.exp (Sminus i ω)) ν := hTilt (Finset.univ.erase i)
    exact ⟨hi, integral_exp_pos hi⟩
  have hquot (f : Ω → ℝ) (hf : Integrable f ν) (a : ℝ) :
      Integrable (fun ω => f ω / a) ν ∧ (∫ ω, f ω / a ∂ν) = (∫ ω, f ω ∂ν) / a := by
    refine ⟨hf.div_const a, ?_⟩
    simp only [div_eq_mul_inv, integral_mul_const]
  have hq : Integrable (fun ω => Real.exp (S ω) / I) ν ∧
      (∫ ω, Real.exp (S ω) / I ∂ν) = 1 :=
    ⟨(hquot _ hSI I).1, (hquot _ hSI I).2.trans (div_self hIpos.ne')⟩
  have hqdel (i : Fin n) : Integrable (fun ω => Real.exp (Sminus i ω) / I) ν ∧
      (∫ ω, Real.exp (Sminus i ω) / I ∂ν) = J i / I ∧
      Integrable (fun ω => Real.exp (Sminus i ω) / J i) ν ∧
      (∫ ω, Real.exp (Sminus i ω) / J i ∂ν) = 1 :=
    ⟨(hquot _ (hJI i).1 I).1, (hquot _ (hJI i).1 I).2,
      (hquot _ (hJI i).1 (J i)).1,
      (hquot _ (hJI i).1 (J i)).2.trans (div_self (hJI i).2.ne')⟩
  have hAMm (M : ℕ) : Measurable (AM M) := hA.min measurable_const
  have hBMm (M : ℕ) : Measurable (BM M) := hB.min measurable_const
  have hADm (M : ℕ) (i : Fin n) : Measurable (AdeleteM M i) := (hAdelete i).min measurable_const
  have hBDm (M : ℕ) (i : Fin n) : Measurable (BdeleteM M i) := (hBdelete i).min measurable_const
  have hcapm (i : Fin n) : Measurable (cap i) :=
    (continuous_abs.measurable.comp (measurable_const.mul (hξ i))).min measurable_const
  have hcap0 (i : Fin n) (ω : Ω) : 0 ≤ cap i ω := le_min (abs_nonneg _) (by norm_num)
  have hfm : Measurable full :=
    ((measurable_const.mul hA).add (measurable_const.mul hB)).mul hSm.exp
  have hfMm (M : ℕ) : Measurable (fullM M) :=
    ((measurable_const.mul (hAMm M)).add (measurable_const.mul (hBMm M))).mul hSm.exp
  have hdm (i : Fin n) : Measurable (deleted i) :=
    ((hcapm i).mul ((continuous_abs.measurable.comp (hA.sub (hAdelete i))).add
      (measurable_const.mul (continuous_abs.measurable.comp (hB.sub (hBdelete i)))))).mul (hSmm i).exp
  have hdMm (M : ℕ) (i : Fin n) : Measurable (deletedM M i) :=
    ((hcapm i).mul ((continuous_abs.measurable.comp ((hAMm M).sub (hADm M i))).add
      (measurable_const.mul (continuous_abs.measurable.comp ((hBMm M).sub (hBDm M i)))))).mul (hSmm i).exp
  have hfb (M : ℕ) (ω : Ω) : 0 ≤ fullM M ω ∧ fullM M ω ≤ full ω := by
    refine ⟨mul_nonneg (add_nonneg (mul_nonneg hx.le (hb M ω).1)
      (mul_nonneg (sq_nonneg x) (hb M ω).2.2.2.1)) (Real.exp_pos _).le, ?_⟩
    exact mul_le_mul_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_left (hb M ω).2.1 hx.le)
        (mul_le_mul_of_nonneg_left (hb M ω).2.2.2.2.1 (sq_nonneg x))) (Real.exp_pos _).le
  have hdb (M : ℕ) (i : Fin n) (ω : Ω) : 0 ≤ deletedM M i ω ∧ deletedM M i ω ≤ deleted i ω := by
    refine ⟨mul_nonneg (mul_nonneg (hcap0 i ω)
      (add_nonneg (abs_nonneg _) (mul_nonneg hx.le (abs_nonneg _)))) (Real.exp_pos _).le, ?_⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (add_le_add (hlip M i ω).1 (mul_le_mul_of_nonneg_left (hlip M i ω).2 hx.le))
      (hcap0 i ω)) (Real.exp_pos _).le
  have heq (ω : Ω) : ∀ᶠ M : ℕ in Filter.atTop,
      fullM M ω = full ω ∧ ∀ i : Fin n, deletedM M i ω = deleted i ω := by
    filter_upwards [hevent ω] with M h
    rcases h with ⟨_, _, ha, hb, hd⟩
    refine ⟨?_, ?_⟩
    · simp only [fullM, full, AM, BM, ha, hb]
    · intro i
      simp only [deletedM, deleted, AM, BM, AdeleteM, BdeleteM, ha, hb, (hd i).1, (hd i).2]
  have hdct (f : Ω → ℝ) (F : ℕ → Ω → ℝ) (hfm : Measurable f)
      (hf : Integrable f ν) (hFm : ∀ M : ℕ, Measurable (F M))
      (hb : ∀ (M : ℕ) (ω : Ω), 0 ≤ F M ω ∧ F M ω ≤ f ω)
      (he : ∀ ω : Ω, ∀ᶠ M : ℕ in Filter.atTop, F M ω = f ω) :
      (∀ M : ℕ, Integrable (F M) ν) ∧
      Filter.Tendsto (fun M : ℕ => ∫ ω, |F M ω - f ω| ∂ν) Filter.atTop (nhds (0 : ℝ)) ∧
      Filter.Tendsto (fun M : ℕ => ∫ ω, F M ω ∂ν) Filter.atTop (nhds (∫ ω, f ω ∂ν)) := by
    have hFI (M : ℕ) : Integrable (F M) ν := by
      apply hf.mono' (hFm M).aestronglyMeasurable
      exact Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hb M ω).1]
        exact (hb M ω).2
    have hp (ω : Ω) : Filter.Tendsto (fun M : ℕ => F M ω) Filter.atTop (nhds (f ω)) :=
      tendsto_const_nhds.congr' (Filter.EventuallyEq.symm (he ω))
    have hraw := tendsto_integral_of_dominated_convergence (μ := ν) (F := F) (f := f) f
      (fun M => (hFm M).aestronglyMeasurable) hf
      (fun M => Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hb M ω).1]; exact (hb M ω).2)
      (Filter.Eventually.of_forall hp)
    have herr := tendsto_integral_of_dominated_convergence (μ := ν)
      (F := fun M ω => |F M ω - f ω|) (f := fun _ : Ω => (0 : ℝ)) f
      (fun M => (continuous_abs.measurable.comp ((hFm M).sub hfm)).aestronglyMeasurable) hf
      (fun M => Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_abs, abs_of_nonpos (sub_nonpos.mpr (hb M ω).2)]
        linarith [(hb M ω).1])
      (Filter.Eventually.of_forall fun ω => by
        have he0 : ∀ᶠ M : ℕ in Filter.atTop, |F M ω - f ω| = 0 :=
          (he ω).mono fun _ h => by rw [h, sub_self, abs_zero]
        exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he0))
    exact ⟨hFI, by simpa only [integral_zero] using herr, hraw⟩
  have hfres := hdct full fullM hfm hFull hfMm hfb (fun ω => (heq ω).mono fun _ h => h.1)
  have hdres (i : Fin n) := hdct (deleted i) (fun M => deletedM M i) (hdm i) (hDeleted i)
    (fun M => hdMm M i) (fun M ω => hdb M i ω) (fun ω => (heq ω).mono fun _ h => h.2 i)
  have hfullSpec (M : ℕ) : Measurable (fullM M) ∧ Integrable (fullM M) ν ∧
      ∀ ω : Ω, 0 ≤ fullM M ω ∧ fullM M ω ≤ full ω := ⟨hfMm M, hfres.1 M, hfb M⟩
  have hdelSpec (M : ℕ) (i : Fin n) : Measurable (deletedM M i) ∧ Integrable (deletedM M i) ν ∧
      Integrable (fun ω => deletedM M i ω / I) ν ∧
      Integrable (fun ω => deletedM M i ω / J i) ν ∧
      ∀ ω : Ω, 0 ≤ deletedM M i ω ∧ deletedM M i ω ≤ deleted i ω :=
    ⟨hdMm M i, (hdres i).1 M, ((hdres i).1 M).div_const I,
      ((hdres i).1 M).div_const (J i), hdb M i⟩
  have hnormed (i : Fin n) :
      Filter.Tendsto (fun M : ℕ => (∫ ω, deletedM M i ω ∂ν) / I)
        Filter.atTop (nhds ((∫ ω, deleted i ω ∂ν) / I)) ∧
      Filter.Tendsto (fun M : ℕ => (∫ ω, deletedM M i ω ∂ν) / J i)
        Filter.atTop (nhds ((∫ ω, deleted i ω ∂ν) / J i)) ∧
      ((∫ ω, deleted i ω ∂ν) / I) = (J i / I) * ((∫ ω, deleted i ω ∂ν) / J i) ∧
      ∀ M : ℕ, ((∫ ω, deletedM M i ω ∂ν) / I) =
        (J i / I) * ((∫ ω, deletedM M i ω ∂ν) / J i) := by
    refine ⟨(hdres i).2.2.div tendsto_const_nhds hIpos.ne',
      (hdres i).2.2.div tendsto_const_nhds (hJI i).2.ne', ?_, ?_⟩
    · field_simp [hIpos.ne', (hJI i).2.ne']
    · intro M
      field_simp [hIpos.ne', (hJI i).2.ne']
  have hcostBound (M : ℕ) : 0 ≤ sourceCostM M ∧ sourceCostM M ≤ sourceCost := by
    constructor
    · apply div_nonneg _ hIpos.le
      exact add_nonneg (integral_nonneg fun ω => (hfb M ω).1)
        (Finset.sum_nonneg fun i _ => integral_nonneg fun ω => (hdb M i ω).1)
    · apply div_le_div_of_nonneg_right _ hIpos.le
      exact add_le_add (integral_mono (hfres.1 M) hFull (fun ω => (hfb M ω).2))
        (Finset.sum_le_sum fun i _ => integral_mono ((hdres i).1 M) (hDeleted i) (fun ω => (hdb M i ω).2))
  have hcostLim : Filter.Tendsto sourceCostM Filter.atTop (nhds sourceCost) :=
    (hfres.2.2.add (tendsto_finsetSum Finset.univ (fun i _ => (hdres i).2.2))).div
      tendsto_const_nhds hIpos.ne'
  exact ⟨hSI, hIpos, hJI, hq.1, hq.2, hqdel, hfullSpec, hdelSpec, heq,
    hfres.2.1, (fun i => (hdres i).2.1), hfres.2.2, (fun i => (hdres i).2.2),
    hfres.2.2.div tendsto_const_nhds hIpos.ne', hnormed, hcostBound, hcostLim⟩

theorem actual_continuous_compact_cost_clipping_limits
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (ξ : Fin n → Ω → ℝ)
    (hξ : ∀ i : Fin n, Measurable (ξ i))
    (hξ2 : ∀ i : Fin n, MemLp (ξ i) 2 ν)
    (A B : Ω → ℝ) (Adelete Bdelete : Fin n → Ω → ℝ)
    (hA : Measurable A) (hB : Measurable B)
    (hAdelete : ∀ i : Fin n, Measurable (Adelete i))
    (hBdelete : ∀ i : Fin n, Measurable (Bdelete i))
    (hAnonneg : ∀ ω : Ω, 0 ≤ A ω)
    (hBnonneg : ∀ ω : Ω, 0 ≤ B ω)
    (hAdeletenonneg : ∀ (i : Fin n) (ω : Ω), 0 ≤ Adelete i ω)
    (hBdeletenonneg : ∀ (i : Fin n) (ω : Ω), 0 ≤ Bdelete i ω)
    (x : ℝ) (hx : 0 ≤ x)
    (hFull : Integrable (fun ω => A ω + x * B ω) ν)
    (hDeleted : ∀ i : Fin n, Integrable (fun ω =>
      min |ξ i ω| (1 + x)⁻¹ * (|A ω - Adelete i ω| + x * |B ω - Bdelete i ω|)) ν) :
    let AM : ℕ → Ω → ℝ := fun M ω => min (A ω) (M : ℝ)
    let BM : ℕ → Ω → ℝ := fun M ω => min (B ω) (M : ℝ)
    let AdeleteM : ℕ → Fin n → Ω → ℝ := fun M i ω => min (Adelete i ω) (M : ℝ)
    let BdeleteM : ℕ → Fin n → Ω → ℝ := fun M i ω => min (Bdelete i ω) (M : ℝ)
    let cap : Fin n → Ω → ℝ := fun i ω => min |ξ i ω| (1 + x)⁻¹
    let full : Ω → ℝ := fun ω => A ω + x * B ω
    let fullM : ℕ → Ω → ℝ := fun M ω => AM M ω + x * BM M ω
    let deleted : Fin n → Ω → ℝ := fun i ω => cap i ω * (|A ω - Adelete i ω| + x * |B ω - Bdelete i ω|)
    let deletedM : ℕ → Fin n → Ω → ℝ := fun M i ω => cap i ω * (|AM M ω - AdeleteM M i ω| + x * |BM M ω - BdeleteM M i ω|)
    let δcompact : Fin n → ℝ := fun i => ∫ ω, ((1 + x) * ξ i ω) ^ 2 * min |(1 + x) * ξ i ω| 1 ∂ν
    let Lcompact : ℝ := ∑ i : Fin n, δcompact i
    let compactCost : ℝ := Lcompact + (∫ ω, full ω ∂ν) + ∑ i : Fin n, ∫ ω, deleted i ω ∂ν
    let compactCostM : ℕ → ℝ := fun M => Lcompact + (∫ ω, fullM M ω ∂ν) + ∑ i : Fin n, ∫ ω, deletedM M i ω ∂ν
    Integrable A ν ∧ (x ≠ 0 → Integrable B ν) ∧
    (∀ i : Fin n, Integrable (fun ω => ((1 + x) * ξ i ω) ^ 2 * min |(1 + x) * ξ i ω| 1) ν) ∧
    (∀ M : ℕ, Measurable (fullM M) ∧ Integrable (fullM M) ν ∧
      ∀ ω : Ω, 0 ≤ fullM M ω ∧ fullM M ω ≤ full ω) ∧
    (∀ (M : ℕ) (i : Fin n), Measurable (deletedM M i) ∧ Integrable (deletedM M i) ν ∧
      ∀ ω : Ω, 0 ≤ deletedM M i ω ∧ deletedM M i ω ≤ deleted i ω) ∧
    (∀ ω : Ω, ∀ᶠ M : ℕ in Filter.atTop,
      fullM M ω = full ω ∧ ∀ i : Fin n, deletedM M i ω = deleted i ω) ∧
    Filter.Tendsto (fun M : ℕ => ∫ ω, |fullM M ω - full ω| ∂ν)
      Filter.atTop (nhds (0 : ℝ)) ∧
    (∀ i : Fin n, Filter.Tendsto (fun M : ℕ => ∫ ω, |deletedM M i ω - deleted i ω| ∂ν)
      Filter.atTop (nhds (0 : ℝ))) ∧
    Filter.Tendsto (fun M : ℕ => ∫ ω, fullM M ω ∂ν)
      Filter.atTop (nhds (∫ ω, full ω ∂ν)) ∧
    (∀ i : Fin n, Filter.Tendsto (fun M : ℕ => ∫ ω, deletedM M i ω ∂ν)
      Filter.atTop (nhds (∫ ω, deleted i ω ∂ν))) ∧
    compactCost = Lcompact + (∫ ω, A ω ∂ν) +
      (if x = 0 then 0 else x * (∫ ω, B ω ∂ν)) + (∑ i : Fin n, ∫ ω, deleted i ω ∂ν) ∧
    (∀ M : ℕ, compactCostM M = Lcompact + (∫ ω, AM M ω ∂ν) +
      (if x = 0 then 0 else x * (∫ ω, BM M ω ∂ν)) + (∑ i : Fin n, ∫ ω, deletedM M i ω ∂ν)) ∧
    (x = 0 → compactCost = Lcompact + (∫ ω, A ω ∂ν) +
      (∑ i : Fin n, ∫ ω, min |ξ i ω| 1 * |A ω - Adelete i ω| ∂ν)) ∧
    (∀ M : ℕ, 0 ≤ compactCostM M ∧ compactCostM M ≤ compactCost) ∧
    Filter.Tendsto compactCostM Filter.atTop (nhds compactCost) := by
  classical
  dsimp only
  let AM : ℕ → Ω → ℝ := fun M ω => min (A ω) (M : ℝ)
  let BM : ℕ → Ω → ℝ := fun M ω => min (B ω) (M : ℝ)
  let AdeleteM : ℕ → Fin n → Ω → ℝ := fun M i ω => min (Adelete i ω) (M : ℝ)
  let BdeleteM : ℕ → Fin n → Ω → ℝ := fun M i ω => min (Bdelete i ω) (M : ℝ)
  let cap : Fin n → Ω → ℝ := fun i ω => min |ξ i ω| (1 + x)⁻¹
  let full : Ω → ℝ := fun ω => A ω + x * B ω
  let fullM : ℕ → Ω → ℝ := fun M ω => AM M ω + x * BM M ω
  let deleted : Fin n → Ω → ℝ := fun i ω => cap i ω * (|A ω - Adelete i ω| + x * |B ω - Bdelete i ω|)
  let deletedM : ℕ → Fin n → Ω → ℝ := fun M i ω => cap i ω * (|AM M ω - AdeleteM M i ω| + x * |BM M ω - BdeleteM M i ω|)
  let δcompact : Fin n → ℝ := fun i => ∫ ω, ((1 + x) * ξ i ω) ^ 2 * min |(1 + x) * ξ i ω| 1 ∂ν
  let Lcompact : ℝ := ∑ i : Fin n, δcompact i
  let compactCost : ℝ := Lcompact + (∫ ω, full ω ∂ν) + ∑ i : Fin n, ∫ ω, deleted i ω ∂ν
  let compactCostM : ℕ → ℝ := fun M => Lcompact + (∫ ω, fullM M ω ∂ν) + ∑ i : Fin n, ∫ ω, deletedM M i ω ∂ν
  have hclips := natural_clipping_envelope_contract ν n (fun _ : Ω => 0) (fun _ : Ω => 0)
    A B Adelete Bdelete measurable_const measurable_const hA hB hAdelete hBdelete
    hAnonneg hBnonneg hAdeletenonneg hBdeletenonneg
    (Filter.Eventually.of_forall fun ω => by simpa only [abs_zero] using hAnonneg ω)
    (Filter.Eventually.of_forall fun ω => by simpa only [abs_zero] using hBnonneg ω)
    (Filter.Eventually.of_forall fun _ => by norm_num)
  rcases hclips with ⟨_, _, _, _, hb, _, hlip, henvInt, _, _, _, _, hevent⟩
  have hAI : Integrable A ν := by
    apply hFull.mono' hA.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hAnonneg ω)]
      exact le_add_of_nonneg_right (mul_nonneg hx (hBnonneg ω))
  have hBI (hne : x ≠ 0) : Integrable B ν := by
    have hxpos : 0 < x := lt_of_le_of_ne hx hne.symm
    apply (hFull.div_const x).mono' hB.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hBnonneg ω)]
      apply (le_div_iff₀ hxpos).mpr
      nlinarith [hAnonneg ω]
  have hδI (i : Fin n) : Integrable (fun ω => ((1 + x) * ξ i ω) ^ 2 * min |(1 + x) * ξ i ω| 1) ν := by
    have hu : Measurable (fun ω : Ω => (1 + x) * ξ i ω) := measurable_const.mul (hξ i)
    have hm : Measurable (fun ω : Ω => ((1 + x) * ξ i ω) ^ 2 * min |(1 + x) * ξ i ω| 1) :=
      (hu.pow_const 2).mul ((continuous_abs.measurable.comp hu).min measurable_const)
    apply ((hξ2 i).integrable_sq.const_mul ((1 + x) ^ 2)).mono' hm.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      have hn : 0 ≤ ((1 + x) * ξ i ω) ^ 2 * min |(1 + x) * ξ i ω| 1 :=
        mul_nonneg (sq_nonneg _) (le_min (abs_nonneg _) (by norm_num))
      rw [Real.norm_eq_abs, abs_of_nonneg hn]
      calc
        ((1 + x) * ξ i ω) ^ 2 * min |(1 + x) * ξ i ω| 1 ≤ ((1 + x) * ξ i ω) ^ 2 := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left
            (min_le_right |(1 + x) * ξ i ω| 1) (sq_nonneg ((1 + x) * ξ i ω))
        _ = (1 + x) ^ 2 * (ξ i ω) ^ 2 := mul_pow _ _ _
  have hL0 : 0 ≤ Lcompact := by
    apply Finset.sum_nonneg
    intro i _
    exact integral_nonneg fun ω => mul_nonneg (sq_nonneg _) (le_min (abs_nonneg _) (by norm_num))
  have hAMm (M : ℕ) : Measurable (AM M) := hA.min measurable_const
  have hBMm (M : ℕ) : Measurable (BM M) := hB.min measurable_const
  have hADm (M : ℕ) (i : Fin n) : Measurable (AdeleteM M i) := (hAdelete i).min measurable_const
  have hBDm (M : ℕ) (i : Fin n) : Measurable (BdeleteM M i) := (hBdelete i).min measurable_const
  have hcapm (i : Fin n) : Measurable (cap i) :=
    (continuous_abs.measurable.comp (hξ i)).min measurable_const
  have hcap0 (i : Fin n) (ω : Ω) : 0 ≤ cap i ω :=
    le_min (abs_nonneg _) (inv_nonneg.mpr (by linarith))
  have hfm : Measurable full := hA.add (measurable_const.mul hB)
  have hfMm (M : ℕ) : Measurable (fullM M) := (hAMm M).add (measurable_const.mul (hBMm M))
  have hdm (i : Fin n) : Measurable (deleted i) :=
    (hcapm i).mul ((continuous_abs.measurable.comp (hA.sub (hAdelete i))).add
      (measurable_const.mul (continuous_abs.measurable.comp (hB.sub (hBdelete i)))))
  have hdMm (M : ℕ) (i : Fin n) : Measurable (deletedM M i) :=
    (hcapm i).mul ((continuous_abs.measurable.comp ((hAMm M).sub (hADm M i))).add
      (measurable_const.mul (continuous_abs.measurable.comp ((hBMm M).sub (hBDm M i)))))
  have hfb (M : ℕ) (ω : Ω) : 0 ≤ fullM M ω ∧ fullM M ω ≤ full ω :=
    ⟨add_nonneg (hb M ω).1 (mul_nonneg hx (hb M ω).2.2.2.1),
      add_le_add (hb M ω).2.1 (mul_le_mul_of_nonneg_left (hb M ω).2.2.2.2.1 hx)⟩
  have hdb (M : ℕ) (i : Fin n) (ω : Ω) : 0 ≤ deletedM M i ω ∧ deletedM M i ω ≤ deleted i ω :=
    ⟨mul_nonneg (hcap0 i ω) (add_nonneg (abs_nonneg _) (mul_nonneg hx (abs_nonneg _))),
      mul_le_mul_of_nonneg_left
        (add_le_add (hlip M i ω).1 (mul_le_mul_of_nonneg_left (hlip M i ω).2 hx)) (hcap0 i ω)⟩
  have heq (ω : Ω) : ∀ᶠ M : ℕ in Filter.atTop,
      fullM M ω = full ω ∧ ∀ i : Fin n, deletedM M i ω = deleted i ω := by
    filter_upwards [hevent ω] with M h
    rcases h with ⟨_, _, ha, hb, hd⟩
    refine ⟨?_, ?_⟩
    · simp only [fullM, full, AM, BM, ha, hb]
    · intro i
      simp only [deletedM, deleted, AM, BM, AdeleteM, BdeleteM, ha, hb, (hd i).1, (hd i).2]
  have hdct (f : Ω → ℝ) (F : ℕ → Ω → ℝ) (hfm : Measurable f)
      (hf : Integrable f ν) (hFm : ∀ M : ℕ, Measurable (F M))
      (hb : ∀ (M : ℕ) (ω : Ω), 0 ≤ F M ω ∧ F M ω ≤ f ω)
      (he : ∀ ω : Ω, ∀ᶠ M : ℕ in Filter.atTop, F M ω = f ω) :
      (∀ M : ℕ, Integrable (F M) ν) ∧
      Filter.Tendsto (fun M : ℕ => ∫ ω, |F M ω - f ω| ∂ν) Filter.atTop (nhds (0 : ℝ)) ∧
      Filter.Tendsto (fun M : ℕ => ∫ ω, F M ω ∂ν) Filter.atTop (nhds (∫ ω, f ω ∂ν)) := by
    have hFI (M : ℕ) : Integrable (F M) ν := by
      apply hf.mono' (hFm M).aestronglyMeasurable
      exact Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hb M ω).1]
        exact (hb M ω).2
    have hp (ω : Ω) : Filter.Tendsto (fun M : ℕ => F M ω) Filter.atTop (nhds (f ω)) :=
      tendsto_const_nhds.congr' (Filter.EventuallyEq.symm (he ω))
    have hraw := tendsto_integral_of_dominated_convergence (μ := ν) (F := F) (f := f) f
      (fun M => (hFm M).aestronglyMeasurable) hf
      (fun M => Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hb M ω).1]; exact (hb M ω).2)
      (Filter.Eventually.of_forall hp)
    have herr := tendsto_integral_of_dominated_convergence (μ := ν)
      (F := fun M ω => |F M ω - f ω|) (f := fun _ : Ω => (0 : ℝ)) f
      (fun M => (continuous_abs.measurable.comp ((hFm M).sub hfm)).aestronglyMeasurable) hf
      (fun M => Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_abs, abs_of_nonpos (sub_nonpos.mpr (hb M ω).2)]
        linarith [(hb M ω).1])
      (Filter.Eventually.of_forall fun ω => by
        have he0 : ∀ᶠ M : ℕ in Filter.atTop, |F M ω - f ω| = 0 :=
          (he ω).mono fun _ h => by rw [h, sub_self, abs_zero]
        exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he0))
    exact ⟨hFI, by simpa only [integral_zero] using herr, hraw⟩
  have hfres := hdct full fullM hfm hFull hfMm hfb (fun ω => (heq ω).mono fun _ h => h.1)
  have hdres (i : Fin n) := hdct (deleted i) (fun M => deletedM M i) (hdm i) (hDeleted i)
    (fun M => hdMm M i) (fun M ω => hdb M i ω) (fun ω => (heq ω).mono fun _ h => h.2 i)
  have hfullSpec (M : ℕ) : Measurable (fullM M) ∧ Integrable (fullM M) ν ∧
      ∀ ω : Ω, 0 ≤ fullM M ω ∧ fullM M ω ≤ full ω := ⟨hfMm M, hfres.1 M, hfb M⟩
  have hdelSpec (M : ℕ) (i : Fin n) : Measurable (deletedM M i) ∧ Integrable (deletedM M i) ν ∧
      ∀ ω : Ω, 0 ≤ deletedM M i ω ∧ deletedM M i ω ≤ deleted i ω :=
    ⟨hdMm M i, (hdres i).1 M, hdb M i⟩
  have hfullDecomp : (∫ ω, full ω ∂ν) = (∫ ω, A ω ∂ν) +
      (if x = 0 then 0 else x * (∫ ω, B ω ∂ν)) := by
    by_cases hx0 : x = 0
    · simp [full, hx0]
    · rw [if_neg hx0]
      exact (integral_add hAI ((hBI hx0).const_mul x)).trans (by rw [integral_const_mul])
  have hfullMDecomp (M : ℕ) : (∫ ω, fullM M ω ∂ν) = (∫ ω, AM M ω ∂ν) +
      (if x = 0 then 0 else x * (∫ ω, BM M ω ∂ν)) := by
    by_cases hx0 : x = 0
    · simp [fullM, hx0]
    · rw [if_neg hx0]
      exact (integral_add (henvInt M).1 ((henvInt M).2.1.const_mul x)).trans
        (by rw [integral_const_mul])
  have hdecomp : compactCost = Lcompact + (∫ ω, A ω ∂ν) +
      (if x = 0 then 0 else x * (∫ ω, B ω ∂ν)) + (∑ i : Fin n, ∫ ω, deleted i ω ∂ν) := by
    dsimp only [compactCost]
    rw [hfullDecomp]
    ring
  have hdecompM (M : ℕ) : compactCostM M = Lcompact + (∫ ω, AM M ω ∂ν) +
      (if x = 0 then 0 else x * (∫ ω, BM M ω ∂ν)) + (∑ i : Fin n, ∫ ω, deletedM M i ω ∂ν) := by
    dsimp only [compactCostM]
    rw [hfullMDecomp]
    ring
  have hzero : x = 0 → compactCost = Lcompact + (∫ ω, A ω ∂ν) +
      (∑ i : Fin n, ∫ ω, min |ξ i ω| 1 * |A ω - Adelete i ω| ∂ν) := by
    intro hx0
    simp only [compactCost, full, deleted, cap, hx0, zero_mul, add_zero, inv_one]
  have hbound (M : ℕ) : 0 ≤ compactCostM M ∧ compactCostM M ≤ compactCost := by
    constructor
    · exact add_nonneg (add_nonneg hL0 (integral_nonneg fun ω => (hfb M ω).1))
        (Finset.sum_nonneg fun i _ => integral_nonneg fun ω => (hdb M i ω).1)
    · exact add_le_add (add_le_add (le_refl Lcompact)
        (integral_mono (hfres.1 M) hFull (fun ω => (hfb M ω).2)))
        (Finset.sum_le_sum fun i _ => integral_mono ((hdres i).1 M) (hDeleted i) (fun ω => (hdb M i ω).2))
  have hlim : Filter.Tendsto compactCostM Filter.atTop (nhds compactCost) :=
    (tendsto_const_nhds.add hfres.2.2).add
      (tendsto_finsetSum Finset.univ (fun i _ => (hdres i).2.2))
  exact ⟨hAI, hBI, hδI, hfullSpec, hdelSpec, heq, hfres.2.1,
    (fun i => (hdres i).2.1), hfres.2.2, (fun i => (hdres i).2.2),
    hdecomp, hdecompM, hzero, hbound, hlim⟩

theorem actual_clipped_event_probabilities
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (ξ : Fin n → Ω → ℝ)
    (hξ : ∀ i : Fin n, Measurable (ξ i))
    (D1 D2 κ : Ω → ℝ)
    (hD1 : Measurable D1) (hD2 : Measurable D2) (hκ : Measurable κ)
    (hD2pos : ∀ᵐ ω ∂ν, 0 < 1 + D2 ω)
    (x : ℝ) (hx : 0 ≤ x) :
    let W : Ω → ℝ := fun ω => ∑ i : Fin n, ξ i ω
    let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
    let D1M : ℕ → Ω → ℝ := fun M ω => max (-(M : ℝ)) (min (D1 ω) (M : ℝ))
    let D2M : ℕ → Ω → ℝ := fun M ω => min (D2 ω) (M : ℝ)
    let T : Ω → ℝ := fun ω => if V ω = 0 then κ ω else (W ω + D1 ω) / (V ω * Real.sqrt (1 + D2 ω))
    let TM : ℕ → Ω → ℝ := fun M ω => if V ω = 0 then κ ω else (W ω + D1M M ω) / (V ω * Real.sqrt (1 + D2M M ω))
    let Z : Set Ω := {ω : Ω | V ω = 0}
    let p0 : ℝ := ν.real Z
    let comparisons : Set (ℝ → ℝ → Prop) := {R | R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨ R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨ R = (fun a b : ℝ => a = b)}
    let F : (ℝ → ℝ → Prop) → Set Ω := fun R => {ω : Ω | R (W ω + D1 ω) (x * V ω * Real.sqrt (1 + D2 ω))}
    let FM : ℕ → (ℝ → ℝ → Prop) → Set Ω := fun M R => {ω : Ω | R (W ω + D1M M ω) (x * V ω * Real.sqrt (1 + D2M M ω))}
    let Q : (ℝ → ℝ → Prop) → Set Ω := fun R => {ω : Ω | R (T ω) x}
    let QM : ℕ → (ℝ → ℝ → Prop) → Set Ω := fun M R => {ω : Ω | R (TM M ω) x}
    let numeratorBad : Set Ω := {ω : Ω | x * |D1 ω| > V ω / 8}
    let numeratorBadM : ℕ → Set Ω := fun M => {ω : Ω | x * |D1M M ω| > V ω / 8}
    let denominatorBad : Set Ω := {ω : Ω | x ^ 2 * |D2 ω| > (1 / 4 : ℝ)}
    let denominatorBadM : ℕ → Set Ω := fun M => {ω : Ω | x ^ 2 * |D2M M ω| > (1 / 4 : ℝ)}
    let eventLimit : Set Ω → (ℕ → Set Ω) → Prop := fun E EM =>
      MeasurableSet E ∧ (∀ M : ℕ, MeasurableSet (EM M)) ∧
      (∀ ω : Ω, ∀ᶠ M : ℕ in Filter.atTop, (ω ∈ EM M ↔ ω ∈ E)) ∧
      (∀ M : ℕ, Measurable (((EM M \ E) ∪ (E \ EM M)).indicator (fun _ : Ω => (1 : ℝ))) ∧
        Integrable (((EM M \ E) ∪ (E \ EM M)).indicator (fun _ : Ω => (1 : ℝ))) ν) ∧
      Filter.Tendsto (fun M : ℕ => ∫ ω, ((EM M \ E) ∪ (E \ EM M)).indicator (fun _ : Ω => (1 : ℝ)) ω ∂ν)
        Filter.atTop (nhds (0 : ℝ)) ∧
      Filter.Tendsto (fun M : ℕ => ν.real ((EM M \ E) ∪ (E \ EM M)))
        Filter.atTop (nhds (0 : ℝ)) ∧
      Filter.Tendsto (fun M : ℕ => ν.real (EM M)) Filter.atTop (nhds (ν.real E))
    Measurable W ∧ Measurable V ∧ Measurable T ∧ (∀ M : ℕ, Measurable (TM M)) ∧
    MeasurableSet Z ∧ (∀ M : ℕ, ν.real {ω : Ω | V ω = 0} = p0) ∧
    (∀ ω : Ω, ∀ᶠ M : ℕ in Filter.atTop, D1M M ω = D1 ω ∧ D2M M ω = D2 ω ∧ TM M ω = T ω) ∧
    (∀ᵐ ω ∂ν, 0 < V ω →
      (∀ R : ℝ → ℝ → Prop, R ∈ comparisons → (ω ∈ Q R ↔ ω ∈ F R)) ∧
      ∀ M : ℕ, 1 ≤ M → 0 < 1 + D2M M ω ∧
        ∀ R : ℝ → ℝ → Prop, R ∈ comparisons → (ω ∈ QM M R ↔ ω ∈ FM M R)) ∧
    (∀ R : ℝ → ℝ → Prop, R ∈ comparisons →
      eventLimit (F R) (fun M => FM M R) ∧ eventLimit (Q R) (fun M => QM M R)) ∧
    eventLimit numeratorBad numeratorBadM ∧ eventLimit denominatorBad denominatorBadM := by
  classical
  dsimp only
  let W : Ω → ℝ := fun ω => ∑ i : Fin n, ξ i ω
  let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
  let D1M : ℕ → Ω → ℝ := fun M ω => max (-(M : ℝ)) (min (D1 ω) (M : ℝ))
  let D2M : ℕ → Ω → ℝ := fun M ω => min (D2 ω) (M : ℝ)
  let T : Ω → ℝ := fun ω => if V ω = 0 then κ ω else (W ω + D1 ω) / (V ω * Real.sqrt (1 + D2 ω))
  let TM : ℕ → Ω → ℝ := fun M ω => if V ω = 0 then κ ω else (W ω + D1M M ω) / (V ω * Real.sqrt (1 + D2M M ω))
  let Z : Set Ω := {ω : Ω | V ω = 0}
  let p0 : ℝ := ν.real Z
  let comparisons : Set (ℝ → ℝ → Prop) := {R | R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨ R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨ R = (fun a b : ℝ => a = b)}
  let F : (ℝ → ℝ → Prop) → Set Ω := fun R => {ω : Ω | R (W ω + D1 ω) (x * V ω * Real.sqrt (1 + D2 ω))}
  let FM : ℕ → (ℝ → ℝ → Prop) → Set Ω := fun M R => {ω : Ω | R (W ω + D1M M ω) (x * V ω * Real.sqrt (1 + D2M M ω))}
  let Q : (ℝ → ℝ → Prop) → Set Ω := fun R => {ω : Ω | R (T ω) x}
  let QM : ℕ → (ℝ → ℝ → Prop) → Set Ω := fun M R => {ω : Ω | R (TM M ω) x}
  let numeratorBad : Set Ω := {ω : Ω | x * |D1 ω| > V ω / 8}
  let numeratorBadM : ℕ → Set Ω := fun M => {ω : Ω | x * |D1M M ω| > V ω / 8}
  let denominatorBad : Set Ω := {ω : Ω | x ^ 2 * |D2 ω| > (1 / 4 : ℝ)}
  let denominatorBadM : ℕ → Set Ω := fun M => {ω : Ω | x ^ 2 * |D2M M ω| > (1 / 4 : ℝ)}
  let eventLimit : Set Ω → (ℕ → Set Ω) → Prop := fun E EM =>
    MeasurableSet E ∧ (∀ M : ℕ, MeasurableSet (EM M)) ∧
    (∀ ω : Ω, ∀ᶠ M : ℕ in Filter.atTop, (ω ∈ EM M ↔ ω ∈ E)) ∧
    (∀ M : ℕ, Measurable (((EM M \ E) ∪ (E \ EM M)).indicator (fun _ : Ω => (1 : ℝ))) ∧
      Integrable (((EM M \ E) ∪ (E \ EM M)).indicator (fun _ : Ω => (1 : ℝ))) ν) ∧
    Filter.Tendsto (fun M : ℕ => ∫ ω, ((EM M \ E) ∪ (E \ EM M)).indicator (fun _ : Ω => (1 : ℝ)) ω ∂ν)
      Filter.atTop (nhds (0 : ℝ)) ∧
    Filter.Tendsto (fun M : ℕ => ν.real ((EM M \ E) ∪ (E \ EM M)))
      Filter.atTop (nhds (0 : ℝ)) ∧
    Filter.Tendsto (fun M : ℕ => ν.real (EM M)) Filter.atTop (nhds (ν.real E))
  have hAbs1 : Measurable (fun ω => |D1 ω|) := continuous_abs.measurable.comp hD1
  have hAbs2 : Measurable (fun ω => |D2 ω|) := continuous_abs.measurable.comp hD2
  have hclips := natural_clipping_envelope_contract ν n D1 D2 (fun ω => |D1 ω|) (fun ω => |D2 ω|)
    (fun _ _ => 0) (fun _ _ => 0) hD1 hD2 hAbs1 hAbs2
    (fun _ => measurable_const) (fun _ => measurable_const)
    (fun _ => abs_nonneg _) (fun _ => abs_nonneg _) (fun _ _ => le_refl 0) (fun _ _ => le_refl 0)
    (Filter.Eventually.of_forall fun _ => le_refl _) (Filter.Eventually.of_forall fun _ => le_refl _) hD2pos
  rcases hclips with ⟨_, _, hclipMeas, _, _, _, _, _, _, _, _, _, hclipEvent⟩
  have hWm : Measurable W := Finset.measurable_sum Finset.univ (fun i _ => hξ i)
  have hVm : Measurable V :=
    (Finset.measurable_sum Finset.univ (fun i _ => (hξ i).pow_const 2)).sqrt
  have hZm : MeasurableSet Z := measurableSet_eq_fun hVm measurable_const
  have hTm : Measurable T := Measurable.ite hZm hκ
    ((hWm.add hD1).div (hVm.mul (measurable_const.add hD2).sqrt))
  have hTMm (M : ℕ) : Measurable (TM M) := Measurable.ite hZm hκ
    ((hWm.add (hclipMeas M).1).div (hVm.mul (measurable_const.add (hclipMeas M).2.1).sqrt))
  have hevent (ω : Ω) : ∀ᶠ M : ℕ in Filter.atTop,
      D1M M ω = D1 ω ∧ D2M M ω = D2 ω ∧ TM M ω = T ω := by
    filter_upwards [hclipEvent ω] with M h
    refine ⟨h.1, h.2.1, ?_⟩
    dsimp only [TM, T, D1M, D2M]
    rw [h.1, h.2.1]
  have hrel (f t : Ω → ℝ) (hf : Measurable f) (ht : Measurable t)
      (R : ℝ → ℝ → Prop) (hR : R ∈ comparisons) : MeasurableSet {ω : Ω | R (f ω) (t ω)} := by
    change R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨
      R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨
      R = (fun a b : ℝ => a = b) at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl
    · exact measurableSet_le hf ht
    · exact measurableSet_lt hf ht
    · exact measurableSet_le ht hf
    · exact measurableSet_lt ht hf
    · exact measurableSet_eq_fun hf ht
  have hdivCompare (u v z : ℝ) (hv : 0 < v) (R : ℝ → ℝ → Prop) (hR : R ∈ comparisons) :
      (R (u / v) z ↔ R u (z * v)) := by
    change R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨
      R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨
      R = (fun a b : ℝ => a = b) at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl
    · exact div_le_iff₀ hv
    · exact div_lt_iff₀ hv
    · exact le_div_iff₀ hv
    · exact lt_div_iff₀ hv
    · constructor
      · intro h
        exact le_antisymm ((div_le_iff₀ hv).mp h.le) ((le_div_iff₀ hv).mp h.ge)
      · intro h
        exact le_antisymm ((div_le_iff₀ hv).mpr h.le) ((le_div_iff₀ hv).mpr h.ge)
  have hpositiveCompare : ∀ᵐ ω ∂ν, 0 < V ω →
      (∀ R : ℝ → ℝ → Prop, R ∈ comparisons → (ω ∈ Q R ↔ ω ∈ F R)) ∧
      ∀ M : ℕ, 1 ≤ M → 0 < 1 + D2M M ω ∧
        ∀ R : ℝ → ℝ → Prop, R ∈ comparisons → (ω ∈ QM M R ↔ ω ∈ FM M R) := by
    filter_upwards [hD2pos] with ω hd
    intro hv
    constructor
    · intro R hR
      simpa only [Q, F, Set.mem_setOf_eq, T, if_neg (ne_of_gt hv), mul_assoc] using
        hdivCompare (W ω + D1 ω) (V ω * Real.sqrt (1 + D2 ω)) x
          (mul_pos hv (Real.sqrt_pos.mpr hd)) R hR
    · intro M hM
      have hm : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      have hdM : 0 < 1 + D2M M ω := by
        by_cases hdm : D2 ω ≤ (M : ℝ)
        · simpa only [D2M, min_eq_left hdm] using hd
        · dsimp only [D2M]
          rw [min_eq_right (le_of_not_ge hdm)]
          linarith
      refine ⟨hdM, ?_⟩
      intro R hR
      simpa only [QM, FM, Set.mem_setOf_eq, TM, if_neg (ne_of_gt hv), mul_assoc] using
        hdivCompare (W ω + D1M M ω) (V ω * Real.sqrt (1 + D2M M ω)) x
          (mul_pos hv (Real.sqrt_pos.mpr hdM)) R hR
  have hindicator (E : Set Ω) (EM : ℕ → Set Ω) (hE : MeasurableSet E)
      (hEM : ∀ M : ℕ, MeasurableSet (EM M))
      (he : ∀ ω : Ω, ∀ᶠ M : ℕ in Filter.atTop, (ω ∈ EM M ↔ ω ∈ E)) :
      Filter.Tendsto (fun M : ℕ => ν.real (EM M)) Filter.atTop (nhds (ν.real E)) := by
    have hp (ω : Ω) : Filter.Tendsto
        (fun M : ℕ => (EM M).indicator (fun _ : Ω => (1 : ℝ)) ω) Filter.atTop
        (nhds (E.indicator (fun _ : Ω => (1 : ℝ)) ω)) := by
      have hEq : ∀ᶠ M : ℕ in Filter.atTop,
          (EM M).indicator (fun _ : Ω => (1 : ℝ)) ω = E.indicator (fun _ : Ω => (1 : ℝ)) ω := by
        filter_upwards [he ω] with M h
        by_cases hω : ω ∈ E
        · simp only [Set.indicator_of_mem hω, Set.indicator_of_mem (h.mpr hω)]
        · have hn : ω ∉ EM M := fun hm => hω (h.mp hm)
          simp [Set.indicator, hω, hn]
      exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hEq)
    have hi := tendsto_integral_of_dominated_convergence (μ := ν)
      (F := fun M ω => (EM M).indicator (fun _ : Ω => (1 : ℝ)) ω)
      (f := E.indicator (fun _ : Ω => (1 : ℝ))) (fun _ : Ω => (1 : ℝ))
      (fun M => (measurable_const.indicator (hEM M)).aestronglyMeasurable)
      (integrable_const _)
      (fun M => Filter.Eventually.of_forall fun ω => by
        by_cases hω : ω ∈ EM M <;> simp [Set.indicator, hω])
      (Filter.Eventually.of_forall hp)
    have heqM (M : ℕ) : (∫ ω, (EM M).indicator (fun _ : Ω => (1 : ℝ)) ω ∂ν) = ν.real (EM M) := by
      simpa only [smul_eq_mul, mul_one] using integral_indicator_const (μ := ν) (1 : ℝ) (hEM M)
    have heqE : (∫ ω, E.indicator (fun _ : Ω => (1 : ℝ)) ω ∂ν) = ν.real E := by
      simpa only [smul_eq_mul, mul_one] using integral_indicator_const (μ := ν) (1 : ℝ) hE
    simpa only [heqM, heqE] using hi
  have hEventResult (E : Set Ω) (EM : ℕ → Set Ω) (hE : MeasurableSet E)
      (hEM : ∀ M : ℕ, MeasurableSet (EM M))
      (he : ∀ ω : Ω, ∀ᶠ M : ℕ in Filter.atTop, (ω ∈ EM M ↔ ω ∈ E)) : eventLimit E EM := by
    let H : ℕ → Set Ω := fun M => (EM M \ E) ∪ (E \ EM M)
    have hHm (M : ℕ) : MeasurableSet (H M) := ((hEM M).diff hE).union (hE.diff (hEM M))
    have hpoint (ω : Ω) : ∀ᶠ M : ℕ in Filter.atTop,
        (H M).indicator (fun _ : Ω => (1 : ℝ)) ω = 0 := by
      filter_upwards [he ω] with M h
      have hn : ω ∉ H M := by
        intro hh
        rcases hh with ⟨hm, hn⟩ | ⟨hm, hn⟩
        · exact hn (h.mp hm)
        · exact hn (h.mpr hm)
      simp [Set.indicator, hn]
    have hlim := tendsto_integral_of_dominated_convergence (μ := ν)
      (F := fun M ω => (H M).indicator (fun _ : Ω => (1 : ℝ)) ω)
      (f := fun _ : Ω => (0 : ℝ)) (fun _ : Ω => (1 : ℝ))
      (fun M => (measurable_const.indicator (hHm M)).aestronglyMeasurable)
      (integrable_const _)
      (fun M => Filter.Eventually.of_forall fun ω => by
        by_cases hω : ω ∈ H M <;> simp [Set.indicator, hω])
      (Filter.Eventually.of_forall fun ω => tendsto_const_nhds.congr' (Filter.EventuallyEq.symm (hpoint ω)))
    have hlim0 : Filter.Tendsto
        (fun M : ℕ => ∫ ω, (H M).indicator (fun _ : Ω => (1 : ℝ)) ω ∂ν)
        Filter.atTop (nhds (0 : ℝ)) := by simpa only [integral_zero] using hlim
    have hmass (M : ℕ) : (∫ ω, (H M).indicator (fun _ : Ω => (1 : ℝ)) ω ∂ν) = ν.real (H M) := by
      simpa only [smul_eq_mul, mul_one] using integral_indicator_const (μ := ν) (1 : ℝ) (hHm M)
    have hmasslim : Filter.Tendsto (fun M : ℕ => ν.real (H M)) Filter.atTop (nhds (0 : ℝ)) := by
      simpa only [hmass] using hlim0
    exact ⟨hE, hEM, he, (fun M => ⟨measurable_const.indicator (hHm M),
      (integrable_const (1 : ℝ)).indicator (hHm M)⟩), hlim0, hmasslim, hindicator E EM hE hEM he⟩
  have hcomparisons (R : ℝ → ℝ → Prop) (hR : R ∈ comparisons) :
      eventLimit (F R) (fun M => FM M R) ∧ eventLimit (Q R) (fun M => QM M R) := by
    constructor
    · apply hEventResult (F R) (fun M => FM M R)
      · exact hrel (fun ω => W ω + D1 ω) (fun ω => x * V ω * Real.sqrt (1 + D2 ω))
          (hWm.add hD1) ((measurable_const.mul hVm).mul (measurable_const.add hD2).sqrt) R hR
      · intro M
        exact hrel (fun ω => W ω + D1M M ω) (fun ω => x * V ω * Real.sqrt (1 + D2M M ω))
          (hWm.add (hclipMeas M).1)
          ((measurable_const.mul hVm).mul (measurable_const.add (hclipMeas M).2.1).sqrt) R hR
      · intro ω
        filter_upwards [hevent ω] with M h
        change R (W ω + D1M M ω) (x * V ω * Real.sqrt (1 + D2M M ω)) ↔
          R (W ω + D1 ω) (x * V ω * Real.sqrt (1 + D2 ω))
        rw [h.1, h.2.1]
    · apply hEventResult (Q R) (fun M => QM M R)
      · exact hrel T (fun _ => x) hTm measurable_const R hR
      · intro M
        exact hrel (TM M) (fun _ => x) (hTMm M) measurable_const R hR
      · intro ω
        filter_upwards [hevent ω] with M h
        change R (TM M ω) x ↔ R (T ω) x
        rw [h.2.2]
  have hnum : eventLimit numeratorBad numeratorBadM := by
    apply hEventResult numeratorBad numeratorBadM
    · exact measurableSet_lt (hVm.div_const 8) (measurable_const.mul hAbs1)
    · intro M
      exact measurableSet_lt (hVm.div_const 8)
        (measurable_const.mul (continuous_abs.measurable.comp (hclipMeas M).1))
    · intro ω
      filter_upwards [hevent ω] with M h
      change x * |D1M M ω| > V ω / 8 ↔ x * |D1 ω| > V ω / 8
      rw [h.1]
  have hden : eventLimit denominatorBad denominatorBadM := by
    apply hEventResult denominatorBad denominatorBadM
    · exact measurableSet_lt measurable_const (measurable_const.mul hAbs2)
    · intro M
      exact measurableSet_lt measurable_const
        (measurable_const.mul (continuous_abs.measurable.comp (hclipMeas M).2.1))
    · intro ω
      filter_upwards [hevent ω] with M h
      change x ^ 2 * |D2M M ω| > (1 / 4 : ℝ) ↔ x ^ 2 * |D2 ω| > (1 / 4 : ℝ)
      rw [h.2.1]
  exact ⟨hWm, hVm, hTm, hTMm, hZm, (fun _ => rfl), hevent,
    hpositiveCompare, hcomparisons, hnum, hden⟩

end

end Shao.OQ6.WeightedCostClipping
