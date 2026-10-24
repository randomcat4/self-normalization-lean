/- Actual stopped terminal envelope. Public declarations are root-frozen.
   Complete seven-head proof source; acceptance requires separate exact-source review. -/
import Shao.Probability.SourceTrueEnergyStrip
import Shao.Probability.SourceTrueWallProfile
import Shao.Probability.SourceBackwardStoppedEnergy
import Shao.Probability.SourcePermutationReveal
import Shao.Probability.SourceSuffixMomentBudgets
import Shao.C2.BrownianBridgeLaw
import Shao.OQ4.BoundaryOccupation
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Data.Nat.Find

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.Probability
open MeasureTheory ProbabilityTheory
open Shao.Probability.SourcePermutationReveal
open Shao.C2.BridgeDomination
open Shao.C2.BrownianBridgeLaw
open scoped BigOperators Classical NNReal Topology

private theorem te_capped_hit_order
    (L : ℕ) (H : ℝ) (Q : ℕ → ℝ) (hQ : Monotone Q) :
    let NH : ℕ := @dite ℕ (∃ k : ℕ, k ≤ L ∧ H ≤ Q k)
      (Classical.propDecidable _)
      (fun he => @Nat.find (fun k : ℕ => k ≤ L ∧ H ≤ Q k)
        (fun k => Classical.propDecidable _) he)
      (fun _ => L)
    NH ≤ L ∧ ∀ k : ℕ, k < NH ↔ k < L ∧ Q k < H := by
  classical
  intro NH
  letI : DecidablePred (fun k : ℕ => k ≤ L ∧ H ≤ Q k) :=
    fun k => Classical.propDecidable _
  by_cases he : ∃ k : ℕ, k ≤ L ∧ H ≤ Q k
  · simp only [NH, dif_pos he]
    have hs := Nat.find_spec he
    refine ⟨hs.1, fun k => ?_⟩
    constructor
    · intro hk
      refine ⟨hk.trans_le hs.1, ?_⟩
      by_contra hh
      exact Nat.find_min he hk ⟨by omega, le_of_not_gt hh⟩
    · rintro ⟨hk, hq⟩
      by_contra hh
      exact (not_le_of_gt hq) (hs.2.trans (hQ (le_of_not_gt hh)))
  · simp only [NH, dif_neg he]
    refine ⟨le_rfl, fun k => ?_⟩
    constructor
    · intro hk
      refine ⟨hk, ?_⟩
      by_contra hh
      exact he ⟨k, hk.le, le_of_not_gt hh⟩
    · exact And.left

private theorem te_capped_hit_selector
    (L : ℕ) (hL : 0 < L) (H : ℝ) (Q : ℕ → ℝ)
    (hQ : Monotone Q) (hQ0 : Q 0 < H)
    (m t : ℕ) (hm : m ≤ L) (ht : t ≤ L) :
    let NH : ℕ := @dite ℕ (∃ k : ℕ, k ≤ L ∧ H ≤ Q k)
      (Classical.propDecidable _)
      (fun he => @Nat.find (fun k : ℕ => k ≤ L ∧ H ≤ Q k)
        (fun k => Classical.propDecidable _) he)
      (fun _ => L)
    max m NH = t ↔
      if t < m then False
      else if t = m then (if t = L then True else H ≤ Q t)
      else if t < L then Q (t - 1) < H ∧ H ≤ Q t
      else Q (t - 1) < H := by
  intro NH
  have hd := te_capped_hit_order L H Q hQ
  change NH ≤ L ∧ ∀ k, k < NH ↔ k < L ∧ Q k < H at hd
  have hpos : 0 < NH := (hd.2 0).mpr ⟨hL, hQ0⟩
  have hle : NH ≤ t ↔ t = L ∨ H ≤ Q t := by
    constructor
    · intro hh
      by_cases he : t = L
      · exact Or.inl he
      · right
        apply le_of_not_gt
        intro hqt
        exact (not_lt_of_ge hh) ((hd.2 t).mpr ⟨by omega, hqt⟩)
    · rintro (he | he)
      · exact he ▸ hd.1
      · by_contra hh
        exact (not_lt_of_ge he) ((hd.2 t).mp (lt_of_not_ge hh)).2
  have hprev (htp : 0 < t) : t ≤ NH ↔ Q (t - 1) < H := by
    constructor
    · intro hh
      exact ((hd.2 (t - 1)).mp (by omega)).2
    · intro hh
      have hlt := (hd.2 (t - 1)).mpr ⟨by omega, hh⟩
      omega
  by_cases htm : t < m
  · simp only [htm, ↓reduceIte]
    apply iff_false_intro
    intro hh
    exact (not_le_of_gt htm) (hh ▸ le_max_left m NH)
  · simp only [htm, ↓reduceIte]
    by_cases hte : t = m
    · rw [if_pos hte]
      have hmax : max m NH = t ↔ NH ≤ t := by rw [← hte, max_eq_left_iff]
      rw [hmax, hle]
      by_cases htl : t = L
      · simp only [htl, ↓reduceIte, true_or]
      · simp only [htl, ↓reduceIte, false_or]
    · rw [if_neg hte]
      have htp : 0 < t := by omega
      have hh := hprev htp
      have hmax : max m NH = t ↔ NH = t := by
        constructor
        · intro he
          rcases le_total m NH with hmn | hnm
          · simpa only [max_eq_right hmn] using he
          · rw [max_eq_left hnm] at he
            omega
        · intro he
          rw [he, max_eq_right (by omega)]
      rw [hmax, le_antisymm_iff]
      by_cases htl : t < L
      · rw [if_pos htl, hh, hle]
        have hne : t ≠ L := by omega
        simp only [hne, false_or, and_comm]
      · rw [if_neg htl, hh]
        exact and_iff_right (hd.1.trans (by omega))

private theorem te_split_measure_preserving
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (r t : ℕ) :
    MeasurePreserving
      (fun a : Shao.Path (r + t) =>
        ((fun i : Fin r => a (Fin.castAdd t i)),
         (fun i : Fin t => a (Fin.natAdd r i))))
      (Measure.pi (fun _ : Fin (r + t) => nu))
      ((Measure.pi (fun _ : Fin r => nu)).prod
        (Measure.pi (fun _ : Fin t => nu))) := by
  have h₁ := (measurePreserving_piCongrLeft
    (fun _ : Fin (r + t) => nu) (finSumFinEquiv : Fin r ⊕ Fin t ≃ Fin (r + t))).symm
  have h₂ := measurePreserving_sumPiEquivProdPi (fun _ : Fin r ⊕ Fin t => nu)
  convert h₂.comp h₁ using 1
  ext a i <;> rfl

private theorem te_reverse_suffix_squares
    (n t : ℕ) (ht : t ≤ n) (a : Shao.Path n) (k : ℕ) (hk : k ≤ t) :
    let b : Shao.Path t := fun i =>
      a ⟨n - t + i.val, by omega⟩
    Shao.prefixSquares (fun i : Fin n => a (Fin.rev i)) k =
      Shao.prefixSquares (fun i : Fin t => b (Fin.rev i)) k := by
  classical
  intro b
  unfold Shao.prefixSquares
  apply Finset.sum_bij
    (fun i hi => (⟨i.val, by
      have hh := (Finset.mem_filter.mp hi).2
      omega⟩ : Fin t))
  · intro i hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      (Finset.mem_filter.mp hi).2
  · intro i hi j hj hij
    exact Fin.ext (congrArg (fun z : Fin t => z.val) hij)
  · intro j hj
    refine ⟨⟨j.val, j.is_lt.trans_le ht⟩, ?_, rfl⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      (Finset.mem_filter.mp hj).2
  · intro i hi
    have he : Fin.rev i =
        (⟨n - t + (Fin.rev (⟨i.val, by
          have hh := (Finset.mem_filter.mp hi).2
          omega⟩ : Fin t)).val, by
            have hi' : (Fin.rev (⟨i.val, by
              have hh := (Finset.mem_filter.mp hi).2
              omega⟩ : Fin t)).val < t := (Fin.rev _).is_lt
            omega⟩ : Fin n) := by
      apply Fin.ext
      simp only [Fin.val_rev]
      have hi' := i.is_lt
      have hh := (Finset.mem_filter.mp hi).2
      omega
    dsimp [b]
    rw [he]
    simp only [Fin.val_rev]

private theorem te_prefix_squares_monotone
    {n : ℕ} (a : Shao.Path n) :
    Monotone (Shao.prefixSquares a) := by
  intro k l hkl
  unfold Shao.prefixSquares
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.trans_le hkl
  · intro i _ _
    exact sq_nonneg _

private theorem te_bounded_selected_fubini
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (r t : ℕ)
    (S : Set (Shao.Path t)) (hS : MeasurableSet S)
    (Phi : Shao.Path r × Shao.Path t → ℝ)
    (hPhi : Measurable Phi) (hb : ∀ p, |Phi p| ≤ 1) :
    let selected : Shao.Path (r + t) → ℝ := fun a =>
      if (fun i : Fin t => a (Fin.natAdd r i)) ∈ S then
        Phi ((fun i : Fin r => a (Fin.castAdd t i)),
          (fun i : Fin t => a (Fin.natAdd r i)))
      else 0
    let suffixIntegral : Shao.Path t → ℝ := fun b =>
      if b ∈ S then
        ∫ v : Shao.Path r, Phi (v, b) ∂Measure.pi (fun _ : Fin r => nu)
      else 0
    Integrable selected (Measure.pi (fun _ : Fin (r + t) => nu)) ∧
      Integrable suffixIntegral (Measure.pi (fun _ : Fin t => nu)) ∧
      (∫ a, selected a ∂Measure.pi (fun _ : Fin (r + t) => nu)) =
        ∫ b, suffixIntegral b ∂Measure.pi (fun _ : Fin t => nu) := by
  classical
  intro selected suffixIntegral
  let G : Shao.Path r × Shao.Path t → ℝ :=
    fun p => if p.2 ∈ S then Phi p else 0
  have hGm : Measurable G :=
    Measurable.ite (hS.preimage measurable_snd) hPhi measurable_const
  have hG : Integrable G
      ((Measure.pi (fun _ : Fin r => nu)).prod (Measure.pi (fun _ : Fin t => nu))) := by
    apply Integrable.of_bound hGm.aestronglyMeasurable 1
    filter_upwards [] with p
    dsimp [G]
    split_ifs
    · simpa only [Real.norm_eq_abs] using hb p
    · norm_num
  have hs := te_split_measure_preserving nu r t
  have hselected : Integrable selected (Measure.pi (fun _ : Fin (r + t) => nu)) :=
    hs.integrable_comp_of_integrable hG
  have hinter (b : Shao.Path t) :
      (∫ v : Shao.Path r, G (v, b) ∂Measure.pi (fun _ : Fin r => nu)) =
        suffixIntegral b := by
    dsimp [G, suffixIntegral]
    split_ifs <;> simp only [integral_zero]
  have hsuffix : Integrable suffixIntegral (Measure.pi (fun _ : Fin t => nu)) := by
    simpa only [hinter] using hG.integral_prod_right
  refine ⟨hselected, hsuffix, ?_⟩
  calc
    (∫ a, selected a ∂Measure.pi (fun _ : Fin (r + t) => nu)) =
        ∫ p, G p ∂((Measure.pi (fun _ : Fin r => nu)).prod
          (Measure.pi (fun _ : Fin t => nu))) := by
      rw [← hs.map_eq]
      exact (integral_map hs.measurable.aemeasurable hGm.aestronglyMeasurable).symm
    _ = ∫ b, suffixIntegral b ∂Measure.pi (fun _ : Fin t => nu) := by
      rw [integral_prod_symm G hG]
      simp only [hinter]

private theorem te_split_at_measure_preserving
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n t : ℕ) (ht : t ≤ n) :
    MeasurePreserving
      (fun a : Shao.Path n =>
        ((fun i : Fin (n - t) =>
            a ⟨i.val, lt_of_lt_of_le i.is_lt (Nat.sub_le n t)⟩),
          (fun i : Fin t => a ⟨n - t + i.val, by omega⟩)))
      (Measure.pi (fun _ : Fin n => nu))
      ((Measure.pi (fun _ : Fin (n - t) => nu)).prod
        (Measure.pi (fun _ : Fin t => nu))) := by
  let e : Fin (n - t) ⊕ Fin t ≃ Fin n :=
    finSumFinEquiv.trans (finCongr (Nat.sub_add_cancel ht))
  have h₁ := (measurePreserving_piCongrLeft (fun _ : Fin n => nu) e).symm
  have h₂ := measurePreserving_sumPiEquivProdPi (fun _ : Fin (n - t) ⊕ Fin t => nu)
  convert h₂.comp h₁ using 1
  ext a i <;> rfl

private theorem te_bounded_selected_fubini_at
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (n t : ℕ) (ht : t ≤ n)
    (S : Set (Shao.Path t)) (hS : MeasurableSet S) :
    ∀ (Phi : Shao.Path (n - t) × Shao.Path t → ℝ),
      Measurable Phi → (∀ p, |Phi p| ≤ 1) →
      let prefixPart : Shao.Path n → Shao.Path (n - t) := fun a i =>
        a ⟨i.val, lt_of_lt_of_le i.is_lt (Nat.sub_le n t)⟩
      let suffixPart : Shao.Path n → Shao.Path t := fun a i =>
        a ⟨n - t + i.val, by omega⟩
      let selected : Shao.Path n → ℝ := fun a =>
        if suffixPart a ∈ S then Phi (prefixPart a, suffixPart a) else 0
      let suffixIntegral : Shao.Path t → ℝ := fun b =>
        if b ∈ S then
          ∫ v : Shao.Path (n - t), Phi (v, b)
            ∂Measure.pi (fun _ : Fin (n - t) => nu)
        else 0
      Integrable selected (Measure.pi (fun _ : Fin n => nu)) ∧
        Integrable suffixIntegral (Measure.pi (fun _ : Fin t => nu)) ∧
        (∫ a, selected a ∂Measure.pi (fun _ : Fin n => nu)) =
          ∫ b, suffixIntegral b ∂Measure.pi (fun _ : Fin t => nu) := by
  intro Phi hPhi hb
  intro prefixPart suffixPart selected suffixIntegral
  let G : Shao.Path (n - t) × Shao.Path t → ℝ :=
    fun p => if p.2 ∈ S then Phi p else 0
  have hGm : Measurable G :=
    Measurable.ite (hS.preimage measurable_snd) hPhi measurable_const
  have hG : Integrable G
      ((Measure.pi (fun _ : Fin (n - t) => nu)).prod
        (Measure.pi (fun _ : Fin t => nu))) := by
    apply Integrable.of_bound hGm.aestronglyMeasurable 1
    filter_upwards [] with p
    dsimp [G]
    split_ifs
    · simpa only [Real.norm_eq_abs] using hb p
    · norm_num
  have hs := te_split_at_measure_preserving nu n t ht
  have hselected : Integrable selected (Measure.pi (fun _ : Fin n => nu)) :=
    hs.integrable_comp_of_integrable hG
  have hinter (b : Shao.Path t) :
      (∫ v : Shao.Path (n - t), G (v, b)
        ∂Measure.pi (fun _ : Fin (n - t) => nu)) = suffixIntegral b := by
    dsimp [G, suffixIntegral]
    split_ifs <;> simp only [integral_zero]
  have hsuffix : Integrable suffixIntegral (Measure.pi (fun _ : Fin t => nu)) := by
    simpa only [hinter] using hG.integral_prod_right
  refine ⟨hselected, hsuffix, ?_⟩
  calc
    (∫ a, selected a ∂Measure.pi (fun _ : Fin n => nu)) =
        ∫ p, G p ∂((Measure.pi (fun _ : Fin (n - t) => nu)).prod
          (Measure.pi (fun _ : Fin t => nu))) := by
      rw [← hs.map_eq]
      exact (integral_map hs.measurable.aemeasurable hGm.aestronglyMeasurable).symm
    _ = ∫ b, suffixIntegral b ∂Measure.pi (fun _ : Fin t => nu) := by
      rw [integral_prod_symm G hG]
      simp only [hinter]

theorem actual_backward_stopped_suffix_integral
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 4 ≤ n)
    (H : ℝ) (hH : 0 < H) (m : ℕ) (hm : m ≤ n / 2) :
    let L : ℕ := n / 2
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    let rev : Shao.Path n → Shao.Path n := fun a i => a (Fin.rev i)
    let Qrev : Shao.Path n → ℕ → ℝ := fun a k => Shao.prefixSquares (rev a) k
    let NH : Shao.Path n → ℕ := fun a =>
      @dite ℕ (∃ k : ℕ, k ≤ L ∧ H ≤ Qrev a k) (Classical.propDecidable _)
        (fun he => @Nat.find (fun k : ℕ => k ≤ L ∧ H ≤ Qrev a k)
          (fun k => Classical.propDecidable _) he)
        (fun _ => L)
    let N : Shao.Path n → ℕ := fun a => max m (NH a)
    ∀ (t : ℕ) (ht : t ≤ L),
      let «prefix» : Shao.Path n → Shao.Path (n - t) := fun a i =>
        a ⟨i.val, lt_of_lt_of_le i.is_lt (Nat.sub_le n t)⟩
      let suffix : Shao.Path n → Shao.Path t := fun a i =>
        a ⟨n - t + i.val, by have htn : t ≤ n := ht.trans (Nat.div_le_self n 2); omega⟩
      let previousEnergy : Shao.Path t → ℝ := fun b =>
        Shao.prefixSquares (fun i : Fin t => b (Fin.rev i)) (t - 1)
      let selectedSuffix : Set (Shao.Path t) := {b |
        if t < m then False
        else if t = m then (if t = L then True else H ≤ Shao.energy b)
        else if t < L then previousEnergy b < H ∧ H ≤ Shao.energy b
        else previousEnergy b < H}
      ∀ Phi : Shao.Path (n - t) × Shao.Path t → ℝ,
        Measurable Phi → (∀ p, |Phi p| ≤ 1) →
        let selected : Shao.Path n → ℝ := fun a =>
          if N a = t then Phi («prefix» a, suffix a) else 0
        let suffixIntegral : Shao.Path t → ℝ := fun b =>
          if b ∈ selectedSuffix then
            ∫ v : Shao.Path (n - t), Phi (v, b)
              ∂Measure.pi (fun _ : Fin (n - t) => nu)
          else 0
        (∀ a, N a = t ↔ suffix a ∈ selectedSuffix) ∧
          Integrable selected P ∧
          Integrable suffixIntegral (Measure.pi (fun _ : Fin t => nu)) ∧
          (∫ a, selected a ∂P) =
            ∫ b : Shao.Path t, suffixIntegral b ∂Measure.pi (fun _ : Fin t => nu) := by
  classical
  intro L P rev Qrev NH N t ht «prefix» suffix previousEnergy selectedSuffix
    Phi hPhi hb selected suffixIntegral
  have htn : t ≤ n := ht.trans (Nat.div_le_self n 2)
  have hLt : 0 < L := by dsimp [L]; omega
  have hQ (a : Shao.Path n) : Monotone (Qrev a) :=
    te_prefix_squares_monotone (rev a)
  have hq0 (a : Shao.Path n) : Qrev a 0 < H := by
    simpa only [Qrev, Shao.prefixSquares_zero] using hH
  have hsq (a : Shao.Path n) (k : ℕ) (hk : k ≤ t) :
      Qrev a k = Shao.prefixSquares (fun i : Fin t => suffix a (Fin.rev i)) k :=
    te_reverse_suffix_squares n t htn a k hk
  have henergy (a : Shao.Path n) : Qrev a t = Shao.energy (suffix a) := by
    rw [hsq a t le_rfl, Shao.prefixSquares_length]
    unfold Shao.energy
    exact Equiv.sum_comp Fin.revPerm (fun i : Fin t => (suffix a i) ^ 2)
  have hprevious (a : Shao.Path n) : Qrev a (t - 1) = previousEnergy (suffix a) :=
    hsq a (t - 1) (Nat.sub_le _ _)
  have hsel (a : Shao.Path n) : N a = t ↔ suffix a ∈ selectedSuffix := by
    have hh := te_capped_hit_selector L hLt H (Qrev a) (hQ a) (hq0 a) m t hm ht
    change max m (NH a) = t ↔ _ at hh
    simpa only [N, selectedSuffix, Set.mem_setOf_eq, henergy a, hprevious a] using hh
  have hprev : Measurable previousEnergy :=
    (Shao.measurable_prefixSquares (t - 1)).comp
      (Measurable.of_eval (fun i : Fin t => measurable_pi_apply (Fin.rev i)))
  have hS : MeasurableSet selectedSuffix := by
    dsimp [selectedSuffix]
    split_ifs
    · exact MeasurableSet.empty
    · exact MeasurableSet.univ
    · exact measurableSet_le measurable_const Shao.measurable_energy
    · exact (measurableSet_lt hprev measurable_const).inter
        (measurableSet_le measurable_const Shao.measurable_energy)
    · exact measurableSet_lt hprev measurable_const
  have hgeneric :
      Integrable
        (fun a : Shao.Path n =>
          if suffix a ∈ selectedSuffix then Phi («prefix» a, suffix a) else 0) P ∧
      Integrable suffixIntegral (Measure.pi (fun _ : Fin t => nu)) ∧
      (∫ a : Shao.Path n,
          (if suffix a ∈ selectedSuffix then Phi («prefix» a, suffix a) else 0) ∂P) =
        ∫ b, suffixIntegral b ∂Measure.pi (fun _ : Fin t => nu) := by
    have hg := te_bounded_selected_fubini_at nu n t htn selectedSuffix hS Phi hPhi hb
    have heq :
        (fun b : Shao.Path t =>
          @ite ℝ (b ∈ selectedSuffix) (Classical.propDecidable _)
            (∫ v : Shao.Path (n - t), Phi (v, b)
              ∂Measure.pi (fun _ : Fin (n - t) => nu)) 0) =
          suffixIntegral := by
      funext b
      dsimp [suffixIntegral]
      by_cases hb : b ∈ selectedSuffix <;> simp only [hb, ↓reduceIte]
    dsimp only at hg
    have heq' :
        (fun a : Shao.Path n =>
          @ite ℝ (suffix a ∈ selectedSuffix) (Classical.propDecidable _)
            (Phi («prefix» a, suffix a)) 0) =
          (fun a : Shao.Path n =>
            if suffix a ∈ selectedSuffix then Phi («prefix» a, suffix a) else 0) := by
      funext a
      by_cases ha : suffix a ∈ selectedSuffix <;> simp only [ha, ↓reduceIte]
    rw [heq, heq'] at hg
    exact hg
  refine ⟨hsel, ?_⟩
  simpa only [selected, hsel] using hgeneric

private theorem te_brownian_exp_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (PB : Measure Ω) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B PB)
    (t : ℝ≥0) (lambda : ℝ) :
    Integrable (fun omega => Real.exp (lambda * B t omega)) PB ∧
      (∫ omega, Real.exp (lambda * B t omega) ∂PB) =
        Real.exp ((t : ℝ) * lambda ^ 2 / 2) := by
  refine ⟨(hB.hasLaw_eval t).integrable_comp (integrable_exp_mul_gaussianReal lambda), ?_⟩
  simpa only [mgf, zero_mul, zero_add] using mgf_gaussianReal (hB.hasLaw_eval t) lambda

private theorem te_brownian_future_exponential_factor
    {Ω : Type*} [MeasurableSpace Ω]
    (PB : Measure Ω) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B PB)
    (s : ℝ≥0) (hs : s ≤ 1) (m : ℕ)
    (times : Fin m → ℝ≥0) (htimes : ∀ i, times i ≤ s)
    (F : (Fin m → ℝ) → ℝ) (hF : Measurable F)
    (hFbounds : ∀ z, 0 ≤ F z ∧ F z ≤ 1) (lambda : ℝ) :
    let past : Ω → (Fin m → ℝ) := fun omega i => B (times i) omega
    Integrable (fun omega => F (past omega) * Real.exp (lambda * B 1 omega)) PB ∧
      Integrable (fun omega => F (past omega) * Real.exp (lambda * B s omega)) PB ∧
      (∫ omega, F (past omega) * Real.exp (lambda * B 1 omega) ∂PB) =
        Real.exp ((nndist (1 : ℝ) (s : ℝ) : ℝ≥0) * lambda ^ 2 / 2) *
          (∫ omega, F (past omega) * Real.exp (lambda * B s omega) ∂PB) := by
  intro past
  have hpast : AEMeasurable past PB :=
    AEMeasurable.of_eval (fun i => hB.aemeasurable (times i))
  have hFp : AEMeasurable (fun omega => F (past omega)) PB :=
    hF.comp_aemeasurable hpast
  have hexp (t : ℝ≥0) := te_brownian_exp_moment PB B hB t lambda
  have hint (t : ℝ≥0) :
      Integrable (fun omega => F (past omega) * Real.exp (lambda * B t omega)) PB := by
    apply (hexp t).1.mono'
      (hFp.mul ((hB.aemeasurable t).const_mul lambda).exp).aestronglyMeasurable
    filter_upwards [] with omega
    change |F (past omega) * Real.exp (lambda * B t omega)| ≤
      Real.exp (lambda * B t omega)
    rw [abs_of_nonneg
      (mul_nonneg (hFbounds _).1 (Real.exp_pos _).le)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (hFbounds _).2
  refine ⟨hint 1, hint s, ?_⟩
  let future : Ω → ℝ := fun omega => Real.exp (lambda * (B 1 omega - B s omega))
  let weightedPast : Ω → ℝ :=
    fun omega => F (past omega) * Real.exp (lambda * B s omega)
  have hadd : s + (1 - s) = (1 : ℝ≥0) := add_tsub_cancel_of_le hs
  have hi : IndepFun future weightedPast PB := by
    have hh := (hB.indepFun_shift s).comp
      (φ := fun f : ℝ≥0 → ℝ => Real.exp (lambda * f (1 - s)))
      (ψ := fun f : Set.Iic s → ℝ =>
        F (fun i : Fin m => f ⟨times i, htimes i⟩) *
          Real.exp (lambda * f ⟨s, by simp⟩))
      (by fun_prop)
      ((hF.comp (Measurable.of_eval (fun i =>
        measurable_pi_apply (⟨times i, htimes i⟩ : Set.Iic s)))).mul
        (Real.measurable_exp.comp (measurable_const.mul
          (measurable_pi_apply (⟨s, by simp⟩ : Set.Iic s)))))
    simpa only [future, weightedPast, past, Function.comp_def, hadd] using hh
  have hf : AEMeasurable future PB :=
    (((hB.aemeasurable 1).sub (hB.aemeasurable s)).const_mul lambda).exp
  have hw : AEMeasurable weightedPast PB :=
    hFp.mul ((hB.aemeasurable s).const_mul lambda).exp
  have hfact := hi.integral_mul_eq_mul_integral hf.aestronglyMeasurable hw.aestronglyMeasurable
  have hpoint (omega : Ω) :
      future omega * weightedPast omega =
        F (past omega) * Real.exp (lambda * B 1 omega) := by
    dsimp [future, weightedPast]
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  have hmgf : (∫ omega, future omega ∂PB) =
      Real.exp ((nndist (1 : ℝ) (s : ℝ) : ℝ≥0) * lambda ^ 2 / 2) := by
    simpa [future, mgf] using
      mgf_gaussianReal (hB.hasLaw_sub 1 s) lambda
  simpa only [Pi.mul_apply, hpoint, hmgf, weightedPast] using hfact

private theorem te_first_hit_partition
    (m : ℕ) (z : Fin m → ℝ) (v : ℝ) :
    (∑ i : Fin m,
      if v ≤ z i ∧ ∀ j : Fin m, j < i → z j < v then (1 : ℝ) else 0) =
      if ∃ i : Fin m, v ≤ z i then 1 else 0 := by
  classical
  by_cases he : ∃ i : Fin m, v ≤ z i
  · let S := Finset.univ.filter (fun i : Fin m => v ≤ z i)
    have hS : S.Nonempty := by
      rcases he with ⟨i, hi⟩
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    let i : Fin m := S.min' hS
    have himem : i ∈ S := Finset.min'_mem S hS
    have hi : v ≤ z i := (Finset.mem_filter.mp himem).2
    have hprevious : ∀ j : Fin m, j < i → z j < v := by
      intro j hj
      by_contra hh
      have hjmem : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt hh⟩
      have hmin : i ≤ j := Finset.min'_le S j hjmem
      exact (not_le_of_gt hj) hmin
    rw [if_pos he, Finset.sum_eq_single i]
    · exact if_pos ⟨hi, hprevious⟩
    · intro j _ hji
      apply if_neg
      rintro ⟨hj, hp⟩
      rcases lt_or_gt_of_ne hji with hlt | hgt
      · exact (not_lt_of_ge hj) (hprevious j hlt)
      · exact (not_lt_of_ge hi) (hp i hgt)
    · intro hh
      exact False.elim (hh (Finset.mem_univ i))
  · rw [if_neg he]
    apply Finset.sum_eq_zero
    intro i _
    apply if_neg
    intro hi
    exact he ⟨i, hi.1⟩

private theorem te_brownian_finite_grid_upper
    {Ω : Type*} [MeasurableSpace Ω]
    (PB : Measure Ω) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B PB)
    (m : ℕ) (times : Fin m → ℝ≥0)
    (hmono : Monotone times) (htimes : ∀ i, times i ≤ 1)
    (v : ℝ) (hv : 0 ≤ v) :
    PB.real {omega | ∃ i : Fin m, v ≤ B (times i) omega} ≤
      Real.exp (-(v ^ 2) / 2) := by
  classical
  let past : Ω → Fin m → ℝ := fun omega i => B (times i) omega
  let F : Fin m → (Fin m → ℝ) → ℝ := fun i z =>
    if v ≤ z i ∧ ∀ j : Fin m, j < i → z j < v then 1 else 0
  let E : Set Ω := {omega | ∃ i : Fin m, v ≤ B (times i) omega}
  have hpast : AEMeasurable past PB :=
    AEMeasurable.of_eval (fun i => hB.aemeasurable (times i))
  have hF (i : Fin m) : Measurable (F i) := by
    apply Measurable.ite _ measurable_const measurable_const
    change MeasurableSet ({z : Fin m → ℝ | v ≤ z i} ∩
      {z : Fin m → ℝ | ∀ j : Fin m, j < i → z j < v})
    refine (measurableSet_le measurable_const (measurable_pi_apply i)).inter ?_
    rw [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro j
    by_cases hj : j < i
    · simpa only [hj, true_implies] using
        (measurableSet_lt (measurable_pi_apply j) measurable_const : MeasurableSet {z : Fin m → ℝ | z j < v})
    · simp only [hj, false_implies, Set.setOf_true, MeasurableSet.univ]
  have hFb (i : Fin m) (z : Fin m → ℝ) : 0 ≤ F i z ∧ F i z ≤ 1 := by
    dsimp [F]
    split_ifs <;> norm_num
  have hFi (i : Fin m) : Integrable (fun omega => F i (past omega)) PB := by
    apply Integrable.of_bound ((hF i).comp_aemeasurable hpast).aestronglyMeasurable 1
    filter_upwards [] with omega
    change |F i (past omega)| ≤ 1
    rw [abs_of_nonneg (hFb i _).1]
    exact (hFb i _).2
  have hclip (i : Fin m) (omega : Ω) :
      F i (fun j => B (min (times j) (times i)) omega) = F i (past omega) := by
    have hc :
        (v ≤ B (min (times i) (times i)) omega ∧
          ∀ j : Fin m, j < i → B (min (times j) (times i)) omega < v) ↔
        (v ≤ B (times i) omega ∧ ∀ j : Fin m, j < i → B (times j) omega < v) := by
      simp only [min_self]
      constructor
      · rintro ⟨hi, hj⟩
        refine ⟨hi, fun j hji => ?_⟩
        simpa only [min_eq_left (hmono hji.le)] using hj j hji
      · rintro ⟨hi, hj⟩
        refine ⟨hi, fun j hji => ?_⟩
        simpa only [min_eq_left (hmono hji.le)] using hj j hji
    dsimp [F, past]
    simp only [hc]
  have hfactor (i : Fin m) :=
    te_brownian_future_exponential_factor PB B hB (times i) (htimes i) m
      (fun j => min (times j) (times i)) (fun j => min_le_right _ _) (F i) (hF i) (hFb i) v
  have hfactor' (i : Fin m) :
      Integrable (fun omega => F i (past omega) * Real.exp (v * B 1 omega)) PB ∧
      Integrable (fun omega => F i (past omega) * Real.exp (v * B (times i) omega)) PB ∧
      (∫ omega, F i (past omega) * Real.exp (v * B 1 omega) ∂PB) =
        Real.exp ((nndist (1 : ℝ) (times i : ℝ) : ℝ≥0) * v ^ 2 / 2) *
          (∫ omega, F i (past omega) * Real.exp (v * B (times i) omega) ∂PB) := by
    simpa only [hclip] using hfactor i
  have hterm (i : Fin m) :
      Real.exp (v ^ 2) * (∫ omega, F i (past omega) ∂PB) ≤
        ∫ omega, F i (past omega) * Real.exp (v * B 1 omega) ∂PB := by
    have hlocal :
        Real.exp (v ^ 2) * (∫ omega, F i (past omega) ∂PB) ≤
          ∫ omega, F i (past omega) * Real.exp (v * B (times i) omega) ∂PB := by
      have hh := integral_mono ((hFi i).const_mul (Real.exp (v ^ 2))) (hfactor' i).2.1
        (fun omega => show Real.exp (v ^ 2) * F i (past omega) ≤
          F i (past omega) * Real.exp (v * B (times i) omega) from by
          dsimp [F, past]
          split_ifs with hh
          · simp only [mul_one, one_mul]
            apply Real.exp_le_exp.mpr
            nlinarith only [mul_le_mul_of_nonneg_left hh.1 hv]
          · simp only [mul_zero, zero_mul, le_refl])
      simpa only [integral_const_mul] using hh
    have hnon : 0 ≤ ∫ omega, F i (past omega) * Real.exp (v * B (times i) omega) ∂PB :=
      integral_nonneg (fun omega => mul_nonneg (hFb i _).1 (Real.exp_pos _).le)
    have hcoeff : 1 ≤ Real.exp ((nndist (1 : ℝ) (times i : ℝ) : ℝ≥0) * v ^ 2 / 2) :=
      Real.one_le_exp_iff.mpr (by positivity)
    exact hlocal.trans ((le_mul_of_one_le_left hnon hcoeff).trans_eq (hfactor' i).2.2.symm)
  have hpartition (omega : Ω) :
      (∑ i : Fin m, F i (past omega)) = if omega ∈ E then 1 else 0 :=
    te_first_hit_partition m (past omega) v
  have hE : NullMeasurableSet E PB := by
    change NullMeasurableSet (past ⁻¹' {z : Fin m → ℝ | ∃ i : Fin m, v ≤ z i}) PB
    apply hpast.nullMeasurableSet_preimage
    rw [Set.setOf_exists]
    exact MeasurableSet.iUnion (fun i => measurableSet_le measurable_const (measurable_pi_apply i))
  have hsumprob : (∑ i : Fin m, ∫ omega, F i (past omega) ∂PB) = PB.real E := by
    rw [← integral_finsetSum _ (fun i _ => hFi i)]
    simp only [hpartition]
    have heq : (fun omega : Ω => if omega ∈ E then (1 : ℝ) else 0) = E.indicator (fun _ => 1) := by
      funext omega
      by_cases hh : omega ∈ E <;> simp only [hh, ↓reduceIte, Set.indicator_apply]
    rw [heq, integral_indicator₀ hE]
    simp only [integral_const, smul_eq_mul, mul_one]
    simp [Measure.real]
  have hsum :
      (∑ i : Fin m, ∫ omega, F i (past omega) * Real.exp (v * B 1 omega) ∂PB) ≤
        Real.exp (v ^ 2 / 2) := by
    rw [← integral_finsetSum _ (fun i _ => (hfactor' i).1)]
    have hpoint (omega : Ω) :
        (∑ i : Fin m, F i (past omega) * Real.exp (v * B 1 omega)) ≤ Real.exp (v * B 1 omega) := by
      rw [← Finset.sum_mul, hpartition]
      split_ifs <;> simp only [one_mul, zero_mul, le_refl, (Real.exp_pos _).le]
    have hh := integral_mono
      (integrable_finsetSum _ (fun i _ => (hfactor' i).1))
      (te_brownian_exp_moment PB B hB 1 v).1 hpoint
    simpa only [(te_brownian_exp_moment PB B hB 1 v).2, NNReal.coe_one, one_mul] using hh
  have hmain :
      Real.exp (v ^ 2) * PB.real E ≤ Real.exp (v ^ 2 / 2) := by
    rw [← hsumprob, Finset.mul_sum]
    exact (Finset.sum_le_sum (fun i _ => hterm i)).trans hsum
  have hdiv := (le_div_iff₀ (Real.exp_pos (v ^ 2))).mpr
    (show PB.real E * Real.exp (v ^ 2) ≤ Real.exp (v ^ 2 / 2) by
      simpa only [mul_comm] using hmain)
  convert hdiv using 1
  rw [← Real.exp_sub]
  congr 1
  ring

private theorem te_brownian_finite_set_upper
    {Ω : Type*} [MeasurableSpace Ω]
    (PB : Measure Ω) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B PB)
    (S : Finset ℝ≥0) (hS : ∀ t ∈ S, t ≤ 1)
    (v : ℝ) (hv : 0 ≤ v) :
    PB.real {omega | ∃ t ∈ S, v ≤ B t omega} ≤ Real.exp (-(v ^ 2) / 2) := by
  classical
  have hh := te_brownian_finite_grid_upper PB B hB S.card (S.orderEmbOfFin rfl)
    (S.orderEmbOfFin rfl).monotone (fun i => hS _ (S.orderEmbOfFin_mem rfl i)) v hv
  have heq : {omega | ∃ t ∈ S, v ≤ B t omega} =
      {omega | ∃ i : Fin S.card, v ≤ B (S.orderEmbOfFin rfl i) omega} := by
    ext omega
    constructor
    · rintro ⟨t, ht, hvt⟩
      have hr : t ∈ Set.range (S.orderEmbOfFin rfl) := by
        rw [S.range_orderEmbOfFin rfl]
        exact ht
      rcases hr with ⟨i, rfl⟩
      exact ⟨i, hvt⟩
    · rintro ⟨i, hi⟩
      exact ⟨_, S.orderEmbOfFin_mem rfl i, hi⟩
  rwa [heq]

private theorem te_brownian_sequence_upper
    {Ω : Type*} [MeasurableSpace Ω]
    (PB : Measure Ω) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B PB)
    (times : ℕ → ℝ≥0) (htimes : ∀ k, times k ≤ 1)
    (v : ℝ) (hv : 0 ≤ v) :
    PB.real {omega | ∃ k : ℕ, v ≤ B (times k) omega} ≤ Real.exp (-(v ^ 2) / 2) := by
  classical
  let A : ℕ → Set Ω := fun m => {omega | ∃ k < m, v ≤ B (times k) omega}
  have hA (m : ℕ) : PB.real (A m) ≤ Real.exp (-(v ^ 2) / 2) := by
    have hh := te_brownian_finite_set_upper PB B hB ((Finset.range m).image times)
      (by
        intro t ht
        rcases Finset.mem_image.mp ht with ⟨k, _, rfl⟩
        exact htimes k) v hv
    simpa only [Finset.mem_image, Finset.mem_range, exists_exists_and_eq_and, A] using hh
  have hmono : Monotone A := by
    intro i j hij omega h
    rcases h with ⟨k, hk, hvk⟩
    exact ⟨k, hk.trans_le hij, hvk⟩
  have heq : (⋃ m : ℕ, A m) = {omega | ∃ k : ℕ, v ≤ B (times k) omega} := by
    ext omega
    simp only [Set.mem_iUnion, A, Set.mem_setOf_eq]
    constructor
    · rintro ⟨m, k, _, hk⟩
      exact ⟨k, hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨k + 1, k, Nat.lt_succ_self _, hk⟩
  have hmeasure : PB (⋃ m : ℕ, A m) ≤ ENNReal.ofReal (Real.exp (-(v ^ 2) / 2)) := by
    rw [hmono.directed_le.measure_iUnion]
    apply iSup_le
    intro m
    have hh := ENNReal.ofReal_le_ofReal (hA m)
    simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top PB (A m))] using hh
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  rw [heq] at hh
  simpa only [Measure.real, ENNReal.toReal_ofReal (Real.exp_pos _).le] using hh

private theorem te_brownian_sequence_absolute
    {Ω : Type*} [MeasurableSpace Ω]
    (PB : Measure Ω) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B PB)
    (times : ℕ → ℝ≥0) (htimes : ∀ k, times k ≤ 1)
    (v : ℝ) (hv : 0 ≤ v) :
    PB.real {omega | ∃ k : ℕ, v ≤ |B (times k) omega|} ≤
      2 * Real.exp (-(v ^ 2) / 2) := by
  have hu := te_brownian_sequence_upper PB B hB times htimes v hv
  have hl := te_brownian_sequence_upper PB (-B) hB.neg times htimes v hv
  have hs :
      {omega | ∃ k : ℕ, v ≤ |B (times k) omega|} ⊆
        {omega | ∃ k : ℕ, v ≤ B (times k) omega} ∪
          {omega | ∃ k : ℕ, v ≤ -B (times k) omega} := by
    rintro omega ⟨k, hk⟩
    rcases le_abs.mp hk with h | h
    · exact Or.inl ⟨k, h⟩
    · exact Or.inr ⟨k, by linarith⟩
  have hh := (measureReal_mono (μ := PB) hs).trans (measureReal_union_le _ _)
  change PB.real {omega | ∃ k : ℕ, v ≤ -B (times k) omega} ≤ _ at hl
  linarith

private theorem te_bridge_dense_domination
    {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (omega : Ω)
    (hcont : Continuous (fun t : ℝ≥0 => B t omega))
    (g : BridgeNoise)
    (heq : ∀ t : BridgeTime, g.val t =
      B ⟨(t : ℝ), t.property.1⟩ omega - (t : ℝ) * B 1 omega)
    (v : ℝ) (hv : 0 ≤ v)
    (hdense : ∀ k : ℕ,
      |B ⟨(TopologicalSpace.denseSeq BridgeTime k : ℝ),
        (TopologicalSpace.denseSeq BridgeTime k).property.1⟩ omega| ≤ v) :
    ‖g.val‖ ≤ 2 * v := by
  have hc : Continuous (fun t : BridgeTime =>
      B ⟨(t : ℝ), t.property.1⟩ omega) :=
    hcont.comp (continuous_subtype_val.subtype_mk _)
  have hb (t : BridgeTime) :
      |B ⟨(t : ℝ), t.property.1⟩ omega| ≤ v :=
    (TopologicalSpace.denseRange_denseSeq BridgeTime).induction_on t
      (isClosed_le hc.abs continuous_const) hdense
  have htime : (⟨((1 : BridgeTime) : ℝ), (1 : BridgeTime).property.1⟩ : ℝ≥0) = 1 := by
    apply Subtype.ext
    norm_num
  have hb1 : |B 1 omega| ≤ v := by
    convert hb (1 : BridgeTime) using 2 <;>
      congr 2 <;> apply Subtype.ext <;> norm_num
  apply (ContinuousMap.norm_le _ (by positivity : 0 ≤ 2 * v)).mpr
  intro t
  rw [Real.norm_eq_abs, heq]
  calc
    |B ⟨(t : ℝ), t.property.1⟩ omega - (t : ℝ) * B 1 omega| ≤
        |B ⟨(t : ℝ), t.property.1⟩ omega| + |(t : ℝ) * B 1 omega| := abs_sub _ _
    _ ≤ v + v := by
      apply add_le_add (hb t)
      rw [abs_mul, abs_of_nonneg t.property.1]
      exact (mul_le_of_le_one_left (abs_nonneg _) t.property.2).trans hb1
    _ = 2 * v := by ring

theorem actual_brownian_bridge_noise_maximal_tail
    {Ω : Type*} [MeasurableSpace Ω]
    (PB : Measure Ω) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B PB) :
    let bridge : Measure BridgeNoise := bridgeLaw B PB
    ∀ u : ℝ, 0 ≤ u →
      bridge.real {g : BridgeNoise | u ≤ ‖g.val‖} ≤
        2 * Real.exp (-(u ^ 2) / 8) := by
  intro bridge u hu
  letI : IsProbabilityMeasure bridge := isProbabilityMeasure_bridgeLaw B PB hB
  by_cases hu0 : u = 0
  · have hh : bridge.real {g : BridgeNoise | u ≤ ‖g.val‖} ≤ 1 := measureReal_le_one
    simpa only [hu0, zero_pow (by decide : 2 ≠ 0), neg_zero, zero_div, Real.exp_zero, mul_one] using hh.trans (by norm_num : (1 : ℝ) ≤ 2)
  have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
  let c : ℝ := u / 2
  have hcp : 0 < c := by dsimp [c]; positivity
  let times : ℕ → ℝ≥0 := fun k =>
    ⟨(TopologicalSpace.denseSeq BridgeTime k : ℝ),
      (TopologicalSpace.denseSeq BridgeTime k).property.1⟩
  have ht : ∀ k, times k ≤ 1 := fun k => (TopologicalSpace.denseSeq BridgeTime k).property.2
  have htail (v : ℝ) (hv : 0 ≤ v) (hvc : v < c) :
      bridge.real {g : BridgeNoise | u ≤ ‖g.val‖} ≤ 2 * Real.exp (-(v ^ 2) / 2) := by
    have hm : MeasurableSet {g : BridgeNoise | u ≤ ‖g.val‖} :=
      measurableSet_le measurable_const continuous_subtype_val.norm.measurable
    have hmap : bridge.real {g : BridgeNoise | u ≤ ‖g.val‖} =
        PB.real {omega | u ≤ ‖(bridgeNoise B omega).val‖} := by
      unfold Measure.real
      change ((PB.map (bridgeNoise B)) _).toReal = _
      rw [Measure.map_apply_of_aemeasurable (aemeasurable_bridgeNoise B PB hB) hm]
      rfl
    rw [hmap]
    have hsub :
        {omega | u ≤ ‖(bridgeNoise B omega).val‖} ≤ᵐ[PB]
          {omega | ∃ k : ℕ, v ≤ |B (times k) omega|} := by
      filter_upwards [ae_bridgeNoise_eq B PB hB, hB.cont] with omega heq hc hmem
      by_contra hnot
      have hd : ∀ k, |B (times k) omega| ≤ v := by
        intro k
        exact (lt_of_not_ge (fun hh => hnot ⟨k, hh⟩)).le
      have hh := te_bridge_dense_domination B omega hc (bridgeNoise B omega) heq v hv hd
      change u ≤ ‖(bridgeNoise B omega).val‖ at hmem
      dsimp [c] at hvc
      linarith
    have hh := ENNReal.toReal_mono (measure_ne_top PB _) (measure_mono_ae hsub)
    exact hh.trans (te_brownian_sequence_absolute PB B hB.toIsPreBrownianReal times ht v hv)
  let approximant : ℕ → ℝ := fun k => max 0 (c - 1 / ((k : ℝ) + 1))
  have happroximant : Filter.Tendsto approximant Filter.atTop (𝓝 c) := by
    have hh : Filter.Tendsto
        (fun k : ℕ => max (0 : ℝ) (c - 1 / ((k : ℝ) + 1)))
        Filter.atTop (𝓝 (max (0 : ℝ) (c - 0))) :=
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (𝓝 0)).max
      ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => c) Filter.atTop (𝓝 c)).sub
        (tendsto_one_div_add_atTop_nhds_zero_nat : Filter.Tendsto
        (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) Filter.atTop (𝓝 0)))
    simpa only [sub_zero, max_eq_right hcp.le] using hh
  have hbound (k : ℕ) :
      bridge.real {g : BridgeNoise | u ≤ ‖g.val‖} ≤
        2 * Real.exp (-(approximant k ^ 2) / 2) := by
    apply htail _ (le_max_left _ _)
    apply max_lt hcp
    have hp : 0 < (1 : ℝ) / ((k : ℝ) + 1) := by positivity
    linarith
  have hlim : Filter.Tendsto (fun k => 2 * Real.exp (-(approximant k ^ 2) / 2))
      Filter.atTop (𝓝 (2 * Real.exp (-(c ^ 2) / 2))) :=
    tendsto_const_nhds.mul (Real.continuous_exp.continuousAt.tendsto.comp
      ((happroximant.pow 2).neg.div_const 2))
  have hh := ge_of_tendsto hlim (Filter.Eventually.of_forall hbound)
  convert hh using 1
  congr 2
  dsimp [c]
  ring

private theorem te_alive_mono
    {n : ℕ} (I : MonitoredDomain) (a : Shao.Path n) (x : ℝ)
    (i j : ℕ) (hij : i ≤ j) (sigma : LabelPerm n) :
    sourceAlive I a x j sigma → sourceAlive I a x i sigma := by
  rintro ⟨hQ, hz, hs⟩
  exact ⟨hQ, hz, fun k hk => hs k (hk.trans hij)⟩

private theorem te_alive_wall_pos
    {n : ℕ} (I : MonitoredDomain) (a : Shao.Path n) (x : ℝ)
    (r : ℕ) (sigma : LabelPerm n) :
    sourceAlive I a x r sigma → 0 < actualWall a x := by
  intro ha
  have hh := ha.2.2 0 (Nat.zero_le r)
  simp only [Shao.prefixSum_zero] at hh
  cases I <;> dsimp [Interior] at hh
  · exact hh
  · linarith
  · exact hh.2

private theorem te_actual_source_bounds
    {n : ℕ} (I : MonitoredDomain)
    (P : Measure BridgeNoise) [IsProbabilityMeasure P]
    (a : Shao.Path n) (x : ℝ) (r : ℕ) (sigma : LabelPerm n) :
    0 ≤ sourceValue I (eventCompletionKernel I P) a x r sigma ∧
      sourceValue I (eventCompletionKernel I P) a x r sigma ≤ 1 := by
  have hf := (eventCompletionKernel_data I P).2.1
  unfold sourceValue completionExt
  split_ifs <;> first | exact hf _ | norm_num

private theorem te_remaining_antitone
    {n : ℕ} (a : Shao.Path n) (sigma : LabelPerm n) :
    Antitone (fun r : ℕ => remainingEnergy a r sigma) := by
  intro i j hij
  have hh := te_prefix_squares_monotone (Spitzer.reorder a sigma) hij
  dsimp [remainingEnergy]
  linarith

private theorem te_actual_terminal_value
    {n : ℕ} (I : MonitoredDomain)
    (P : Measure BridgeNoise) [IsProbabilityMeasure P]
    (a : Shao.Path n) (x : ℝ) :
    sourceValue I (eventCompletionKernel I P) a x n (Equiv.refl (Fin n)) =
      if sourceAlive I a x n (Equiv.refl (Fin n)) then 1 else 0 := by
  classical
  have hreorder : Spitzer.reorder a (Equiv.refl (Fin n)) = a := rfl
  by_cases ha : sourceAlive I a x n (Equiv.refl (Fin n))
  · have hw := te_alive_wall_pos I a x n (Equiv.refl (Fin n)) ha
    have hz : Interior I (actualWall a x) (∑ i : Fin n, a i) := by
      simpa only [Shao.prefixSum_length] using ha.2.1
    simp [sourceValue, completionExt, ha, hw, hreorder, remainingEnergy, hz]
  · simp only [sourceValue, if_neg ha]

private theorem te_zero_remaining_source
    {n : ℕ} (I : MonitoredDomain)
    (P : Measure BridgeNoise) [IsProbabilityMeasure P]
    (a : Shao.Path n) (x : ℝ) (r : ℕ) (hr : r ≤ n)
    (hzero : remainingEnergy a r (Equiv.refl (Fin n)) = 0) :
    ∀ j : ℕ, r ≤ j → j ≤ n →
      sourceValue I (eventCompletionKernel I P) a x j (Equiv.refl (Fin n)) =
        if sourceAlive I a x n (Equiv.refl (Fin n)) then 1 else 0 := by
  classical
  have hreorder : Spitzer.reorder a (Equiv.refl (Fin n)) = a := rfl
  have ht (j : ℕ) (hrj : r ≤ j) (hjn : j ≤ n) :
      remainingEnergy a j (Equiv.refl (Fin n)) = 0 := by
    have hnon := (remaining_population_geometry a j hjn (Equiv.refl (Fin n))).1
    have hle := te_remaining_antitone a (Equiv.refl (Fin n)) hrj
    dsimp only at hle
    rw [hzero] at hle
    exact le_antisymm hle hnon
  have hy (j : ℕ) (hrj : r ≤ j) (hjn : j ≤ n) :
      Shao.prefixSum a j = Shao.prefixSum a n := by
    have hh := ((remaining_population_geometry a j hjn (Equiv.refl (Fin n))).2.2.2
      (ht j hrj hjn)).1
    change Shao.prefixSum a n - Shao.prefixSum a j = 0 at hh
    linarith
  intro j hrj hjn
  by_cases ha : sourceAlive I a x r (Equiv.refl (Fin n))
  · have han : sourceAlive I a x n (Equiv.refl (Fin n)) := by
      refine ⟨ha.1, ha.2.1, ?_⟩
      intro k hk
      by_cases hkr : k ≤ r
      · exact ha.2.2 k hkr
      · rw [hreorder, hy k (by omega) hk]
        exact ha.2.1
    have haj := te_alive_mono I a x j n hjn (Equiv.refl (Fin n)) han
    have hw := te_alive_wall_pos I a x r (Equiv.refl (Fin n)) ha
    have hz : Interior I (actualWall a x) (∑ i : Fin n, a i) := by
      simpa only [Shao.prefixSum_length] using ha.2.1
    simp [sourceValue, completionExt, haj, han, hw, ht j hrj hjn,
      hreorder, hy j hrj hjn, hz]
  · have haj : ¬sourceAlive I a x j (Equiv.refl (Fin n)) :=
      fun hj => ha (te_alive_mono I a x r j hrj (Equiv.refl (Fin n)) hj)
    have han : ¬sourceAlive I a x n (Equiv.refl (Fin n)) :=
      fun hn => ha (te_alive_mono I a x r n hr (Equiv.refl (Fin n)) hn)
    simp only [sourceValue, if_neg haj, if_neg han]

private theorem te_zero_wall_dead
    {n : ℕ} (I : MonitoredDomain) (a : Shao.Path n)
    (r : ℕ) (sigma : LabelPerm n) :
    ¬sourceAlive I a 0 r sigma := by
  intro ha
  have hh := te_alive_wall_pos I a 0 r sigma ha
  simpa only [actualWall, zero_mul, lt_self_iff_false] using hh

private theorem te_terminal_discrepancy_boundaries
    {n : ℕ} (I : MonitoredDomain)
    (P : Measure BridgeNoise) [IsProbabilityMeasure P]
    (a : Shao.Path n) (r : ℕ) (hr : r ≤ n) (x : ℝ) :
    let terminal : ℝ := if sourceAlive I a x n (Equiv.refl (Fin n)) then 1 else 0
    let discrepancy : ℝ := (Finset.Icc r n).sup'
      (by exact ⟨r, Finset.mem_Icc.mpr ⟨le_rfl, hr⟩⟩)
      (fun j => |sourceValue I (eventCompletionKernel I P) a x j
        (Equiv.refl (Fin n)) - terminal|)
    0 ≤ discrepancy ∧ discrepancy ≤ 1 ∧
      (remainingEnergy a r (Equiv.refl (Fin n)) = 0 → discrepancy = 0) ∧
      (x = 0 → discrepancy = 0) ∧
      (¬sourceAlive I a x r (Equiv.refl (Fin n)) → discrepancy = 0) := by
  classical
  intro terminal discrepancy
  have hnon : 0 ≤ discrepancy := by
    have hh :
        |sourceValue I (eventCompletionKernel I P) a x r (Equiv.refl (Fin n)) - terminal| ≤
          discrepancy :=
      Finset.le_sup'
        (fun j : ℕ => |sourceValue I (eventCompletionKernel I P) a x j
          (Equiv.refl (Fin n)) - terminal|)
        (Finset.mem_Icc.mpr ⟨le_rfl, hr⟩)
    exact (abs_nonneg _).trans hh
  have hone : discrepancy ≤ 1 := by
    apply Finset.sup'_le
    intro j hj
    have hh := te_actual_source_bounds I P a x j (Equiv.refl (Fin n))
    rw [abs_sub_le_iff]
    dsimp [terminal]
    split_ifs <;> constructor <;> linarith
  have hzero
      (h : ∀ j ∈ Finset.Icc r n,
        sourceValue I (eventCompletionKernel I P) a x j (Equiv.refl (Fin n)) = terminal) :
      discrepancy = 0 := by
    apply le_antisymm _ hnon
    apply Finset.sup'_le
    intro j hj
    rw [h j hj, sub_self, abs_zero]
  have hdead (ha : ¬sourceAlive I a x r (Equiv.refl (Fin n))) : discrepancy = 0 := by
    apply hzero
    intro j hj
    have haj : ¬sourceAlive I a x j (Equiv.refl (Fin n)) :=
      fun hh => ha (te_alive_mono I a x r j (Finset.mem_Icc.mp hj).1
        (Equiv.refl (Fin n)) hh)
    have han : ¬sourceAlive I a x n (Equiv.refl (Fin n)) :=
      fun hh => ha (te_alive_mono I a x r n hr (Equiv.refl (Fin n)) hh)
    simp only [sourceValue, if_neg haj, terminal, if_neg han]
  refine ⟨hnon, hone, ?_, ?_, hdead⟩
  · intro hz
    apply hzero
    intro j hj
    exact te_zero_remaining_source I P a x r hr hz j
      (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
  · intro hx
    subst x
    exact hdead (te_zero_wall_dead I a r (Equiv.refl (Fin n)))

private theorem te_bridge_failure_budget
    {Ω : Type*} [MeasurableSpace Ω]
    (PB : Measure Ω) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B PB)
    (S : Set BridgeNoise) (hS : MeasurableSet S)
    (U d : ℝ) (hU : 0 < U) (hd : 0 < d)
    (hfailure : ∀ g : BridgeNoise, g ∉ S → d ≤ Real.sqrt U * ‖g.val‖) :
    1 - (bridgeLaw B PB).real S ≤ 2 * Real.exp (-(d ^ 2) / (8 * U)) := by
  letI : IsProbabilityMeasure (bridgeLaw B PB) := isProbabilityMeasure_bridgeLaw B PB hB
  have heq : 1 - (bridgeLaw B PB).real S = (bridgeLaw B PB).real Sᶜ := by
    rw [measureReal_compl hS, probReal_univ]
  rw [heq]
  have hsub : Sᶜ ⊆ {g : BridgeNoise | d / Real.sqrt U ≤ ‖g.val‖} := by
    intro g hg
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hU)).mpr
    simpa only [mul_comm] using hfailure g hg
  have hh := (measureReal_mono (μ := bridgeLaw B PB) hsub).trans
    (actual_brownian_bridge_noise_maximal_tail PB B hB (d / Real.sqrt U)
      (div_nonneg hd.le (Real.sqrt_nonneg U)))
  convert hh using 1
  congr 2
  rw [div_pow, Real.sq_sqrt hU.le]
  field_simp <;> ring

private theorem te_upper_completion_tail
    {Ω : Type*} [MeasurableSpace Ω]
    (PB : Measure Ω) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B PB)
    (a y T z U d : ℝ) (hU : 0 < U) (hT : 0 ≤ T) (hTU : T ≤ U)
    (hd : 0 < d) (hy : y ≤ a - d) (hz : z ≤ a - d) :
    1 - upperCompletion (bridgeLaw B PB) a y T z ≤
      2 * Real.exp (-(d ^ 2) / (8 * U)) := by
  apply te_bridge_failure_budget PB B hB (strictUpper a y T z)
    (measurableSet_strictUpper a y T z) U d hU hd
  intro g hg
  change ¬∀ t : BridgeTime, bridgePath y T z g t < a at hg
  rcases not_forall.mp hg with ⟨t, ht⟩
  have hpath : a ≤ (1 - (t : ℝ)) * y + (t : ℝ) * z + Real.sqrt T * g.val t :=
    le_of_not_gt ht
  have hmean : (1 - (t : ℝ)) * y + (t : ℝ) * z ≤ a - d := by
    have h₁ := mul_le_mul_of_nonneg_left hy (sub_nonneg.mpr t.property.2)
    have h₂ := mul_le_mul_of_nonneg_left hz t.property.1
    nlinarith only [h₁, h₂]
  have hnoise : Real.sqrt T * g.val t ≤ Real.sqrt U * ‖g.val‖ :=
    (mul_le_mul_of_nonneg_left (g.val.apply_le_norm t) (Real.sqrt_nonneg T)).trans
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hTU) (norm_nonneg g.val))
  linarith

private theorem te_lower_completion_tail
    {Ω : Type*} [MeasurableSpace Ω]
    (PB : Measure Ω) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B PB)
    (a y T z U d : ℝ) (hU : 0 < U) (hT : 0 ≤ T) (hTU : T ≤ U)
    (hd : 0 < d) (hy : -a + d ≤ y) (hz : -a + d ≤ z) :
    1 - lowerCompletion (bridgeLaw B PB) a y T z ≤
      2 * Real.exp (-(d ^ 2) / (8 * U)) := by
  apply te_bridge_failure_budget PB B hB (strictLower a y T z)
    (measurableSet_strictLower a y T z) U d hU hd
  intro g hg
  change ¬∀ t : BridgeTime, -a < bridgePath y T z g t at hg
  rcases not_forall.mp hg with ⟨t, ht⟩
  have hpath : (1 - (t : ℝ)) * y + (t : ℝ) * z + Real.sqrt T * g.val t ≤ -a :=
    le_of_not_gt ht
  have hmean : -a + d ≤ (1 - (t : ℝ)) * y + (t : ℝ) * z := by
    have h₁ := mul_le_mul_of_nonneg_left hy (sub_nonneg.mpr t.property.2)
    have h₂ := mul_le_mul_of_nonneg_left hz t.property.1
    nlinarith only [h₁, h₂]
  have hneg : -g.val t ≤ ‖g.val‖ := by
    linarith only [g.val.neg_norm_le_apply t]
  have hnoise : Real.sqrt T * (-g.val t) ≤ Real.sqrt U * ‖g.val‖ :=
    (mul_le_mul_of_nonneg_left hneg (Real.sqrt_nonneg T)).trans
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hTU) (norm_nonneg g.val))
  nlinarith only [hpath, hmean, hnoise]

private theorem te_interior_signs
    (I : MonitoredDomain) (wall y : ℝ) :
    let signs : Finset ℝ := match I with
      | .upper => {1}
      | .lower => {-1}
      | .interval => {1, -1}
    Interior I wall y ↔ ∀ eta ∈ signs, eta * y < wall := by
  cases I with
  | upper => simp [Interior]
  | lower =>
    simp only [Interior, Finset.mem_singleton, forall_eq, neg_one_mul]
    constructor <;> intro h <;> linarith
  | interval =>
    simp only [Interior, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq,
      one_mul, neg_one_mul]
    constructor
    · rintro ⟨hl, hu⟩
      exact ⟨hu, by linarith⟩
    · rintro ⟨hu, hl⟩
      exact ⟨by linarith, hu⟩

private theorem te_sign_absolute
    (I : MonitoredDomain) :
    let signs : Finset ℝ := match I with
      | .upper => {1}
      | .lower => {-1}
      | .interval => {1, -1}
    ∀ eta ∈ signs, |eta| = 1 := by
  cases I <;> norm_num

private theorem te_suffix_displacement_bound
    {n : ℕ} (a : Shao.Path n) (r : ℕ) (hr : r ≤ n) :
    let J : ℝ := (Finset.Icc 0 (n - r)).sup'
      (by exact ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩)
      (fun l => |Shao.prefixSum a (r + l) - Shao.prefixSum a r|)
    0 ≤ J ∧ ∀ j : ℕ, r ≤ j → j ≤ n →
      |Shao.prefixSum a j - Shao.prefixSum a r| ≤ J := by
  intro J
  have hb (j : ℕ) (hrj : r ≤ j) (hjn : j ≤ n) :
      |Shao.prefixSum a j - Shao.prefixSum a r| ≤ J := by
    have hh := Finset.le_sup'
      (fun l => |Shao.prefixSum a (r + l) - Shao.prefixSum a r|)
      (Finset.mem_Icc.mpr ⟨Nat.zero_le (j - r), Nat.sub_le_sub_right hjn r⟩)
    have he : r + (j - r) = j := by omega
    simpa only [he] using hh
  refine ⟨?_, hb⟩
  simpa only [sub_self, abs_zero] using hb r le_rfl hr

private theorem te_far_corridor_data
    {n : ℕ} (I : MonitoredDomain)
    (a : Shao.Path n) (r : ℕ) (hr : r ≤ n) (x : ℝ) :
    let signs : Finset ℝ := match I with
      | .upper => {1}
      | .lower => {-1}
      | .interval => {1, -1}
    let wall : ℝ := actualWall a x
    let J : ℝ := (Finset.Icc 0 (n - r)).sup'
      (by exact ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩)
      (fun l => |Shao.prefixSum a (r + l) - Shao.prefixSum a r|)
    let w : ℝ → ℝ := fun eta => wall - eta * Shao.prefixSum a r
    sourceAlive I a x r (Equiv.refl (Fin n)) →
      (∀ eta ∈ signs, 2 * J < w eta) →
      (∀ j : ℕ, r ≤ j → j ≤ n →
        sourceAlive I a x j (Equiv.refl (Fin n))) ∧
      (∀ eta ∈ signs, 0 < w eta ∧
        ∀ j : ℕ, r ≤ j → j ≤ n →
          eta * Shao.prefixSum a j ≤ wall - w eta / 2) := by
  intro signs wall J w ha hfar
  have hJ := te_suffix_displacement_bound a r hr
  change 0 ≤ J ∧ ∀ j, r ≤ j → j ≤ n →
    |Shao.prefixSum a j - Shao.prefixSum a r| ≤ J at hJ
  have hbound (eta : ℝ) (he : eta ∈ signs) (j : ℕ) (hrj : r ≤ j) (hjn : j ≤ n) :
      eta * Shao.prefixSum a j ≤ wall - w eta / 2 := by
    have hsign : |eta| = 1 := te_sign_absolute I eta he
    have hh : eta * (Shao.prefixSum a j - Shao.prefixSum a r) ≤ J := by
      apply (le_abs_self _).trans
      rw [abs_mul, hsign, one_mul]
      exact hJ.2 j hrj hjn
    have hf := hfar eta he
    dsimp [w] at hf ⊢
    nlinarith
  have hpos (eta : ℝ) (he : eta ∈ signs) : 0 < w eta := by
    have hh := hfar eta he
    linarith only [hh, hJ.1]
  have han : sourceAlive I a x n (Equiv.refl (Fin n)) := by
    refine ⟨ha.1, ha.2.1, ?_⟩
    intro k hk
    by_cases hkr : k ≤ r
    · exact ha.2.2 k hkr
    · change Interior I wall (Shao.prefixSum a k)
      apply (te_interior_signs I wall (Shao.prefixSum a k)).mpr
      intro eta he
      have hh := hbound eta he k (by omega) hk
      have hp := hpos eta he
      linarith
  exact ⟨fun j _ hj => te_alive_mono I a x j n hj (Equiv.refl (Fin n)) han,
    fun eta he => ⟨hpos eta he, hbound eta he⟩⟩

private theorem te_interval_deficit_le
    (P : Measure BridgeNoise) [IsProbabilityMeasure P] (wall y T z : ℝ) :
    1 - intervalCompletion P wall y T z ≤
      (1 - upperCompletion P wall y T z) + (1 - lowerCompletion P wall y T z) := by
  have hh := measureReal_union_le (μ := P)
    (strictUpper wall y T z)ᶜ (strictLower wall y T z)ᶜ
  rw [← Set.compl_inter,
    measureReal_compl ((measurableSet_strictUpper wall y T z).inter
      (measurableSet_strictLower wall y T z)),
    measureReal_compl (measurableSet_strictUpper wall y T z),
    measureReal_compl (measurableSet_strictLower wall y T z),
    probReal_univ] at hh
  exact hh

private theorem te_actual_completion_far_deficit
    {Ω : Type*} [MeasurableSpace Ω]
    (PB : Measure Ω) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B PB)
    (I : MonitoredDomain) (wall y T z U y0 : ℝ)
    (hU : 0 < U) (hT : 0 ≤ T) (hTU : T ≤ U) :
    let signs : Finset ℝ := match I with
      | .upper => {1}
      | .lower => {-1}
      | .interval => {1, -1}
    let w : ℝ → ℝ := fun eta => wall - eta * y0
    (∀ eta ∈ signs, 0 < w eta ∧
      eta * y ≤ wall - w eta / 2 ∧ eta * z ≤ wall - w eta / 2) →
      1 - eventCompletionKernel I (bridgeLaw B PB) (wall, y, T, z) ≤
        ∑ eta ∈ signs, 2 * Real.exp (-(w eta ^ 2) / (32 * U)) := by
  intro signs w hm
  letI : IsProbabilityMeasure (bridgeLaw B PB) := isProbabilityMeasure_bridgeLaw B PB hB
  have hu (d : ℝ) (hd : 0 < d) (hy : y ≤ wall - d / 2) (hz : z ≤ wall - d / 2) :
      1 - upperCompletion (bridgeLaw B PB) wall y T z ≤
        2 * Real.exp (-(d ^ 2) / (32 * U)) := by
    have hh := te_upper_completion_tail PB B hB wall y T z U (d / 2)
      hU hT hTU (by positivity) hy hz
    convert hh using 1
    congr 2
    field_simp <;> ring
  have hl (d : ℝ) (hd : 0 < d) (hy : -wall + d / 2 ≤ y) (hz : -wall + d / 2 ≤ z) :
      1 - lowerCompletion (bridgeLaw B PB) wall y T z ≤
        2 * Real.exp (-(d ^ 2) / (32 * U)) := by
    have hh := te_lower_completion_tail PB B hB wall y T z U (d / 2)
      hU hT hTU (by positivity) hy hz
    convert hh using 1
    congr 2
    field_simp <;> ring
  cases I with
  | upper =>
    have hm1 := hm 1 (by simp [signs])
    have hh := hu (w 1) hm1.1 (by simpa only [one_mul] using hm1.2.1)
      (by simpa only [one_mul] using hm1.2.2)
    simpa only [signs, eventCompletionKernel, Finset.sum_singleton] using hh
  | lower =>
    have hm1 := hm (-1) (by simp [signs])
    have hh := hl (w (-1)) hm1.1
      (by have hh := hm1.2.1; simp only [neg_one_mul] at hh; linarith)
      (by have hh := hm1.2.2; simp only [neg_one_mul] at hh; linarith)
    simpa only [signs, eventCompletionKernel, Finset.sum_singleton] using hh
  | interval =>
    have hm1 := hm 1 (by simp [signs])
    have hm2 := hm (-1) (by simp [signs])
    have hupper := hu (w 1) hm1.1 (by simpa only [one_mul] using hm1.2.1)
      (by simpa only [one_mul] using hm1.2.2)
    have hlower := hl (w (-1)) hm2.1
      (by have hh := hm2.2.1; simp only [neg_one_mul] at hh; linarith)
      (by have hh := hm2.2.2; simp only [neg_one_mul] at hh; linarith)
    change 1 - intervalCompletion (bridgeLaw B PB) wall y T z ≤
      ∑ eta ∈ ({1, -1} : Finset ℝ), 2 * Real.exp (-(w eta ^ 2) / (32 * U))
    rw [Finset.sum_insert (by norm_num : (1 : ℝ) ∉ ({(-1 : ℝ)} : Finset ℝ)),
      Finset.sum_singleton]
    exact (te_interval_deficit_le (bridgeLaw B PB) wall y T z).trans (add_le_add hupper hlower)

theorem actual_source_terminal_corridor_envelope
    {Ω : Type*} [MeasurableSpace Ω]
    (PB : Measure Ω) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B PB)
    (n : ℕ) (a : Shao.Path n) (r : ℕ) (hr : r ≤ n)
    (x : ℝ) (hx : 0 ≤ x) (I : MonitoredDomain) :
    let F : BridgeKernel := eventCompletionKernel I (bridgeLaw B PB)
    let signs : Finset ℝ := match I with
      | .upper => {1}
      | .lower => {-1}
      | .interval => {1, -1}
    let wall : ℝ := actualWall a x
    let U : ℝ := remainingEnergy a r (Equiv.refl (Fin n))
    let J : ℝ := (Finset.Icc 0 (n - r)).sup'
      (by exact ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩)
      (fun l => |Shao.prefixSum a (r + l) - Shao.prefixSum a r|)
    let w : ℝ → ℝ := fun eta => wall - eta * Shao.prefixSum a r
    let terminal : ℝ := if sourceAlive I a x n (Equiv.refl (Fin n)) then 1 else 0
    let discrepancy : ℝ := (Finset.Icc r n).sup'
      (by exact ⟨r, Finset.mem_Icc.mpr ⟨le_rfl, hr⟩⟩)
      (fun j => |sourceValue I F a x j (Equiv.refl (Fin n)) - terminal|)
    0 ≤ discrepancy ∧ discrepancy ≤ 1 ∧
      (U = 0 → discrepancy = 0) ∧
      (x = 0 → discrepancy = 0) ∧
      discrepancy ≤
        if 0 < U ∧ sourceAlive I a x r (Equiv.refl (Fin n)) then
          ∑ eta ∈ signs,
            ((if 0 < w eta ∧ w eta ≤ 2 * J then 1 else 0) +
            (if 2 * J < w eta then 2 * Real.exp (-(w eta ^ 2) / (32 * U)) else 0))
        else 0 := by
  classical
  intro F signs wall U J w terminal discrepancy
  letI : IsProbabilityMeasure (bridgeLaw B PB) := isProbabilityMeasure_bridgeLaw B PB hB
  have hb := te_terminal_discrepancy_boundaries I (bridgeLaw B PB) a r hr x
  change 0 ≤ discrepancy ∧ discrepancy ≤ 1 ∧ (U = 0 → discrepancy = 0) ∧
    (x = 0 → discrepancy = 0) ∧
    (¬sourceAlive I a x r (Equiv.refl (Fin n)) → discrepancy = 0) at hb
  refine ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, ?_⟩
  have hU0 : 0 ≤ U := (remaining_population_geometry a r hr (Equiv.refl (Fin n))).1
  by_cases hcase : 0 < U ∧ sourceAlive I a x r (Equiv.refl (Fin n))
  · rw [if_pos hcase]
    have hpay0 (eta : ℝ) :
        0 ≤ (if 0 < w eta ∧ w eta ≤ 2 * J then (1 : ℝ) else 0) +
          (if 2 * J < w eta then 2 * Real.exp (-(w eta ^ 2) / (32 * U)) else 0) := by
      split_ifs <;> positivity
    by_cases hnear : ∃ eta ∈ signs, w eta ≤ 2 * J
    · rcases hnear with ⟨eta, he, hne⟩
      have hi : Interior I wall (Shao.prefixSum a r) := hcase.2.2.2 r le_rfl
      have hsi := (te_interior_signs I wall (Shao.prefixSum a r)).mp hi eta he
      have hwp : 0 < w eta := by dsimp [w]; linarith
      have hterm :
          1 ≤ (if 0 < w eta ∧ w eta ≤ 2 * J then (1 : ℝ) else 0) +
            (if 2 * J < w eta then 2 * Real.exp (-(w eta ^ 2) / (32 * U)) else 0) := by
        rw [if_pos ⟨hwp, hne⟩]
        apply le_add_of_nonneg_right
        split_ifs <;> positivity
      exact hb.2.1.trans (hterm.trans (Finset.single_le_sum (fun eta _ => hpay0 eta) he))
    · have hfar : ∀ eta ∈ signs, 2 * J < w eta := by
        intro eta he
        exact lt_of_not_ge (fun hh => hnear ⟨eta, he, hh⟩)
      have hd := te_far_corridor_data I a r hr x hcase.2 hfar
      have han := hd.1 n hr le_rfl
      have hterminal : terminal = 1 := if_pos han
      have hsum :
          (∑ eta ∈ signs,
            ((if 0 < w eta ∧ w eta ≤ 2 * J then (1 : ℝ) else 0) +
            (if 2 * J < w eta then 2 * Real.exp (-(w eta ^ 2) / (32 * U)) else 0))) =
          ∑ eta ∈ signs, 2 * Real.exp (-(w eta ^ 2) / (32 * U)) := by
        apply Finset.sum_congr rfl
        intro eta he
        rw [if_neg (fun hh => (not_le_of_gt (hfar eta he)) hh.2), if_pos (hfar eta he), zero_add]
      rw [hsum]
      apply Finset.sup'_le
      intro j hj
      have hrj := (Finset.mem_Icc.mp hj).1
      have hjn := (Finset.mem_Icc.mp hj).2
      have haj := hd.1 j hrj hjn
      have hbound := te_actual_source_bounds I (bridgeLaw B PB) a x j (Equiv.refl (Fin n))
      have hT := (remaining_population_geometry a j hjn (Equiv.refl (Fin n))).1
      have hTU := te_remaining_antitone a (Equiv.refl (Fin n)) hrj
      dsimp only at hTU
      have hy0 : remainingEnergy a j (Equiv.refl (Fin n)) = 0 →
          Shao.prefixSum a j = Shao.prefixSum a n := by
        intro hz
        have hh := ((remaining_population_geometry a j hjn (Equiv.refl (Fin n))).2.2.2 hz).1
        change Shao.prefixSum a n - Shao.prefixSum a j = 0 at hh
        linarith
      have hvalue :
          sourceValue I F a x j (Equiv.refl (Fin n)) =
            F (wall, Shao.prefixSum a j, remainingEnergy a j (Equiv.refl (Fin n)), Shao.prefixSum a n) := by
        unfold sourceValue
        rw [if_pos haj]
        exact (eventCompletionKernel_data I (bridgeLaw B PB)).2.2
          wall (Shao.prefixSum a j) (remainingEnergy a j (Equiv.refl (Fin n)))
          (Shao.prefixSum a n) (te_alive_wall_pos I a x r (Equiv.refl (Fin n)) hcase.2) hT hy0
      have hneg : sourceValue I F a x j (Equiv.refl (Fin n)) - 1 ≤ 0 := by
        linarith only [hbound.2]
      rw [hterminal, abs_of_nonpos hneg, neg_sub, hvalue]
      apply te_actual_completion_far_deficit PB B hB I wall (Shao.prefixSum a j)
        (remainingEnergy a j (Equiv.refl (Fin n))) (Shao.prefixSum a n) U
        (Shao.prefixSum a r) hcase.1 hT hTU
      intro eta he
      exact ⟨(hd.2 eta he).1, (hd.2 eta he).2 j hrj hjn, (hd.2 eta he).2 n hr le_rfl⟩
  · rw [if_neg hcase]
    by_cases hp : 0 < U
    · exact le_of_eq (hb.2.2.2.2 (fun ha => hcase ⟨hp, ha⟩))
    · exact le_of_eq (hb.2.2.1 (le_antisymm (le_of_not_gt hp) hU0))

private theorem te_raw_normalization
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (n : ℕ) (hn : 0 < n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hsecond : 0 < ∫ z : ℝ, z ^ 2 ∂nu) :
    let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂nu
    let scale : ℝ := Real.sqrt ((n : ℝ) * sigmaSq)
    let eta : Measure ℝ := Measure.map (fun z : ℝ => z / scale) nu
    0 < scale ∧ scale ^ 2 = (n : ℝ) * sigmaSq ∧
      IsProbabilityMeasure eta ∧
      Integrable (fun z : ℝ => z ^ 2) eta ∧
      (∫ z : ℝ, z ∂eta) = 0 ∧
      (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta) = 1 ∧
      ∀ t : ℕ, Measure.map (fun a : Shao.Path t => fun i => a i / scale)
        (Measure.pi (fun _ : Fin t => nu)) = Measure.pi (fun _ : Fin t => eta) := by
  intro sigmaSq scale eta
  have hN : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hs : 0 < scale := Real.sqrt_pos.mpr (mul_pos hN hsecond)
  have hs2 : scale ^ 2 = (n : ℝ) * sigmaSq := Real.sq_sqrt (by positivity)
  have hm : Measurable (fun z : ℝ => z / scale) := measurable_id.div_const _
  have hp : IsProbabilityMeasure eta := by dsimp [eta]; infer_instance
  have hi2 : Integrable (fun z : ℝ => z ^ 2) eta := by
    apply (integrable_map_measure (by fun_prop) hm.aemeasurable).2
    simpa only [Function.comp_def, div_pow] using h2.div_const (scale ^ 2)
  have hme : (∫ z : ℝ, z ∂eta) = 0 := by
    rw [show eta = Measure.map (fun z : ℝ => z / scale) nu from rfl,
      integral_map hm.aemeasurable (f := fun z : ℝ => z) (by fun_prop),
      integral_div, hmean, zero_div]
  have hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta) = 1 := by
    rw [show eta = Measure.map (fun z : ℝ => z / scale) nu from rfl,
      integral_map hm.aemeasurable (by fun_prop)]
    simp_rw [div_pow]
    rw [integral_div, hs2]
    rw [← mul_div_assoc]
    exact div_self (mul_pos hN hsecond).ne'
  exact ⟨hs, hs2, hp, hi2, hme, hnorm,
    fun t => Measure.pi_map_pi (fun _ : Fin t => hm.aemeasurable)⟩

private theorem te_actual_cutoff_measurable
    (n : ℕ) (H : ℝ) (hH : 0 < H) :
    Measurable (fun a : Shao.Path n => energyCutoff a H (Equiv.refl (Fin n))) := by
  apply measurable_of_Ioi
  intro k
  by_cases hk : k ≤ n
  · have heq :
        (fun a : Shao.Path n => energyCutoff a H (Equiv.refl (Fin n))) ⁻¹' Set.Ioi k =
          {a : Shao.Path n | H ≤ remainingEnergy a k (Equiv.refl (Fin n))} := by
      ext a
      change k < energyCutoff a H (Equiv.refl (Fin n)) ↔
        H ≤ remainingEnergy a k (Equiv.refl (Fin n))
      rw [← not_le, (energy_cutoff_data a H hH).2.1 (Equiv.refl (Fin n)) k hk]
      exact not_lt
    rw [heq]
    exact measurableSet_le measurable_const
      (Shao.measurable_energy.sub (Shao.measurable_prefixSquares k))
  · have heq :
        (fun a : Shao.Path n => energyCutoff a H (Equiv.refl (Fin n))) ⁻¹' Set.Ioi k = ∅ := by
      ext a
      have hh := (energy_cutoff_data a H hH).1.1 (Equiv.refl (Fin n))
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false]
      omega
    rw [heq]
    exact MeasurableSet.empty

private theorem te_reverse_energy
    {n : ℕ} (a : Shao.Path n) (k : ℕ) (hk : k ≤ n) :
    Shao.prefixSquares (fun i : Fin n => a (Fin.rev i)) k =
      remainingEnergy a (n - k) (Equiv.refl (Fin n)) := by
  classical
  have hreindex :
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), (a (Fin.rev i)) ^ 2) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => n - k ≤ i.val), (a i) ^ 2 := by
    apply Finset.sum_equiv Fin.revPerm
    · intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change i.val < k ↔ n - k ≤ (Fin.rev i).val
      rw [Fin.val_rev]
      have hi := i.is_lt
      omega
    · intro i _
      rfl
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i : Fin n => i.val < n - k) (fun i => (a i) ^ 2)
  simp only [not_lt] at hsplit
  change (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), (a (Fin.rev i)) ^ 2) =
    (∑ i : Fin n, (a i) ^ 2) -
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < n - k), (a i) ^ 2
  rw [hreindex]
  linarith only [hsplit]

private theorem te_scaled_path_data
    {n : ℕ} (a : Shao.Path n) (c : ℝ) :
    let b : Shao.Path n := fun i => a i / c
    (∀ k : ℕ, Shao.prefixSum b k = Shao.prefixSum a k / c ∧
      Shao.prefixSquares b k = Shao.prefixSquares a k / c ^ 2) ∧
      Shao.energy b = Shao.energy a / c ^ 2 := by
  intro b
  constructor
  · intro k
    constructor
    · simp only [Shao.prefixSum, b, Finset.sum_div]
    · simp only [Shao.prefixSquares, b, div_pow, Finset.sum_div]
  · simp only [Shao.energy, b, div_pow, Finset.sum_div]

private theorem te_capped_hit_scale
    (L : ℕ) (H : ℝ) (Q : ℕ → ℝ) (hQ : Monotone Q)
    (c : ℝ) (hc : 0 < c) :
    let NH : ℕ := @dite ℕ (∃ k : ℕ, k ≤ L ∧ H ≤ Q k)
      (Classical.propDecidable _)
      (fun he => @Nat.find (fun k : ℕ => k ≤ L ∧ H ≤ Q k)
        (fun k => Classical.propDecidable _) he)
      (fun _ => L)
    let NHscaled : ℕ := @dite ℕ (∃ k : ℕ, k ≤ L ∧ H / c ^ 2 ≤ Q k / c ^ 2)
      (Classical.propDecidable _)
      (fun he => @Nat.find (fun k : ℕ => k ≤ L ∧ H / c ^ 2 ≤ Q k / c ^ 2)
        (fun k => Classical.propDecidable _) he)
      (fun _ => L)
    NHscaled = NH := by
  intro NH NHscaled
  have hQscaled : Monotone (fun k => Q k / c ^ 2) :=
    fun i j hij => div_le_div_of_nonneg_right (hQ hij) (sq_nonneg c)
  have hraw := te_capped_hit_order L H Q hQ
  have hscaled := te_capped_hit_order L (H / c ^ 2) (fun k => Q k / c ^ 2) hQscaled
  change NH ≤ L ∧ ∀ k, k < NH ↔ k < L ∧ Q k < H at hraw
  change NHscaled ≤ L ∧ ∀ k, k < NHscaled ↔ k < L ∧ Q k / c ^ 2 < H / c ^ 2 at hscaled
  have heq (k : ℕ) : k < NHscaled ↔ k < NH := by
    rw [hscaled.2 k, hraw.2 k, div_lt_div_iff_of_pos_right (pow_pos hc 2)]
  apply le_antisymm
  · by_contra h
    have hh : NH < NHscaled := by omega
    have hh' := (heq NH).mp hh
    omega
  · by_contra h
    have hh : NHscaled < NH := by omega
    have hh' := (heq NHscaled).mpr hh
    omega

private theorem te_scaled_suffix_max
    {n : ℕ} (a : Shao.Path n) (N : ℕ) (c : ℝ) (hc : 0 < c) :
    let b : Shao.Path n := fun i => a i / c
    (Finset.Icc 0 N).sup'
      (by exact ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩)
      (fun l => |Shao.prefixSum b (n - N + l) - Shao.prefixSum b (n - N)|) =
      ((Finset.Icc 0 N).sup'
        (by exact ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩)
        (fun l => |Shao.prefixSum a (n - N + l) - Shao.prefixSum a (n - N)|)) / c := by
  intro b
  have hdata := te_scaled_path_data a c
  have hpoint (l : ℕ) :
      |Shao.prefixSum b (n - N + l) - Shao.prefixSum b (n - N)| =
        |Shao.prefixSum a (n - N + l) - Shao.prefixSum a (n - N)| / c := by
    rw [(hdata.1 _).1, (hdata.1 _).1, ← sub_div, abs_div, abs_of_pos hc]
  apply le_antisymm
  · apply Finset.sup'_le
    intro l hl
    rw [hpoint]
    exact div_le_div_of_nonneg_right
      (Finset.le_sup'
        (fun k => |Shao.prefixSum a (n - N + k) - Shao.prefixSum a (n - N)|) hl) hc.le
  · apply (div_le_iff₀ hc).mpr
    apply Finset.sup'_le
    intro l hl
    have hh := Finset.le_sup'
      (fun k => |Shao.prefixSum b (n - N + k) - Shao.prefixSum b (n - N)|) hl
    rw [hpoint] at hh
    exact (div_le_iff₀ hc).mp hh

private theorem te_reverse_cutoff_identity
    {n : ℕ} (a : Shao.Path n) (hn : 4 ≤ n)
    (H : ℝ) (hH : 0 < H) :
    let L : ℕ := n / 2
    let rev : Shao.Path n := fun i => a (Fin.rev i)
    let Qrev : ℕ → ℝ := fun k => Shao.prefixSquares rev k
    let NH : ℕ := @dite ℕ (∃ k : ℕ, k ≤ L ∧ H ≤ Qrev k)
      (Classical.propDecidable _)
      (fun he => @Nat.find (fun k : ℕ => k ≤ L ∧ H ≤ Qrev k)
        (fun k => Classical.propDecidable _) he)
      (fun _ => L)
    H ≤ Qrev L →
      energyCutoff a H (Equiv.refl (Fin n)) = n - NH + 1 := by
  classical
  intro L rev Qrev NH hcross
  letI : DecidablePred (fun k : ℕ => k ≤ L ∧ H ≤ Qrev k) :=
    fun k => Classical.propDecidable _
  have hL : 0 < L := by dsimp [L]; omega
  have hLn : L ≤ n := Nat.div_le_self n 2
  have hQ : Monotone Qrev := te_prefix_squares_monotone rev
  have hd := te_capped_hit_order L H Qrev hQ
  change NH ≤ L ∧ ∀ k, k < NH ↔ k < L ∧ Qrev k < H at hd
  have hp : 0 < NH := (hd.2 0).mpr ⟨hL, by simpa only [Qrev, Shao.prefixSquares_zero] using hH⟩
  have he : ∃ k, k ≤ L ∧ H ≤ Qrev k := ⟨L, le_rfl, hcross⟩
  have hfind : NH = Nat.find he := by simp only [NH, dif_pos he]
  have hstop : H ≤ Qrev NH := by
    rw [hfind]
    exact (Nat.find_spec he).2
  have hbefore : Qrev (NH - 1) < H := ((hd.2 (NH - 1)).mp (by omega)).2
  have hlow : remainingEnergy a (n - NH + 1) (Equiv.refl (Fin n)) < H := by
    have hh := te_reverse_energy a (NH - 1) (by omega)
    have hindex : n - (NH - 1) = n - NH + 1 := by omega
    rw [hindex] at hh
    rw [← hh]
    exact hbefore
  have hhigh : H ≤ remainingEnergy a (n - NH) (Equiv.refl (Fin n)) := by
    rw [← te_reverse_energy a NH (hd.1.trans hLn)]
    exact hstop
  have hcut := (energy_cutoff_data a H hH).2.1
  have hle : energyCutoff a H (Equiv.refl (Fin n)) ≤ n - NH + 1 :=
    (hcut (Equiv.refl (Fin n)) (n - NH + 1) (by omega)).mpr hlow
  have hnot : ¬energyCutoff a H (Equiv.refl (Fin n)) ≤ n - NH :=
    fun hh => (not_lt_of_ge hhigh) ((hcut (Equiv.refl (Fin n)) (n - NH) (by omega)).mp hh)
  omega

private theorem te_raw_backward_core
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 4 ≤ n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hsecond : 0 < ∫ z : ℝ, z ^ 2 ∂nu) :
    let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂nu
    let normalizedLaw : Measure ℝ :=
      Measure.map (fun z : ℝ => z / Real.sqrt ((n : ℝ) * sigmaSq)) nu
    let R : ℝ := Shao.truncationBudget normalizedLaw n 0
    let h : ℝ := 4 * (n : ℝ) * sigmaSq * R ^ 2
    R ≤ 1 / 2 → ∀ H : ℝ, h ≤ H →
      let L : ℕ := n / 2
      let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
      let rev : Shao.Path n → Shao.Path n := fun a i => a (Fin.rev i)
      let Qrev : Shao.Path n → ℕ → ℝ := fun a k => Shao.prefixSquares (rev a) k
      let NH : Shao.Path n → ℕ := fun a =>
        @dite ℕ (∃ k : ℕ, k ≤ L ∧ H ≤ Qrev a k) (Classical.propDecidable _)
          (fun he => @Nat.find (fun k : ℕ => k ≤ L ∧ H ≤ Qrev a k)
            (fun k => Classical.propDecidable _) he)
          (fun _ => L)
      ∀ m : ℕ, m ≤ L → (m : ℝ) ≤ 3 * H / sigmaSq →
        let N : Shao.Path n → ℕ := fun a => max m (NH a)
        let r : Shao.Path n → ℕ := fun a => n - N a
        let U : Shao.Path n → ℝ := fun a => Shao.energy a - Shao.prefixSquares a (r a)
        let J : Shao.Path n → ℝ := fun a =>
          (Finset.Icc 0 (N a)).sup'
            (by exact ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩)
            (fun l => |Shao.prefixSum a (r a + l) - Shao.prefixSum a (r a)|)
        let exceptional : Set (Shao.Path n) := {a | Qrev a L < H}
        0 < H ∧
          Integrable (fun z : ℝ => min (z ^ 2) H) nu ∧
          sigmaSq / 2 ≤ (∫ z : ℝ, min (z ^ 2) H ∂nu) ∧
          Measurable NH ∧ Measurable N ∧ Measurable U ∧ Measurable J ∧
          (∀ a, 1 ≤ NH a ∧ NH a ≤ N a ∧ N a ≤ L ∧ U a = Qrev a (N a)) ∧
          Integrable (fun a => (NH a : ℝ)) P ∧
          Integrable (fun a => (N a : ℝ)) P ∧ Integrable U P ∧
          Integrable (fun a => J a ^ 2) P ∧
          (∫ a, (NH a : ℝ) ∂P) ≤ 4 * H / sigmaSq ∧
          (∫ a, (N a : ℝ) ∂P) ≤ 7 * H / sigmaSq ∧
          P.real exceptional ≤ 12 * H / ((n : ℝ) * sigmaSq) ∧
          (∫ a, U a ∂P) = sigmaSq * (∫ a, (N a : ℝ) ∂P) ∧
          (∫ a, J a ^ 2 ∂P) ≤ 16 * sigmaSq * (∫ a, (N a : ℝ) ∂P) := by
  classical
  intro sigmaSq normalizedLaw R h hR H hH L P rev Qrev NH m hmL hmH N r U J exceptional
  have hn0 : 0 < n := by omega
  have hNpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn0
  have hSigma : 0 < sigmaSq := hsecond
  have hg := raw_truncation_budget_suffix_geometry nu n hn0 h2 hsecond
  have hHp : 0 < H := hg.2.2.2.1.trans_le hH
  have hclip : Integrable (fun z : ℝ => min (z ^ 2) H) nu := by
    apply h2.mono' (by fun_prop)
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (sq_nonneg z) hHp.le)]
    exact min_le_left _ _
  have hret : Integrable (fun z : ℝ => if z ^ 2 ≤ h then z ^ 2 else 0) nu := by
    apply h2.mono' ((Measurable.ite
      (measurableSet_le (measurable_id.pow_const 2) measurable_const)
      (measurable_id.pow_const 2) measurable_const).aestronglyMeasurable)
    filter_upwards [] with z
    split_ifs
    · simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z)] using le_rfl (a := z ^ 2)
    · simpa only [id_eq, Real.norm_eq_abs, abs_zero] using sq_nonneg z
  have hclipMean : sigmaSq / 2 ≤ ∫ z : ℝ, min (z ^ 2) H ∂nu :=
    (hg.2.2.2.2.2.2 hR).trans (integral_mono hret hclip (fun z => by
      split_ifs with hz
      · exact le_min le_rfl (hz.trans hH)
      · exact le_min (sq_nonneg z) hHp.le))
  let c : ℝ := Real.sqrt ((n : ℝ) * sigmaSq)
  have hd := te_raw_normalization nu n hn0 h2 hmean hsecond
  have hc : 0 < c := hd.1
  have hc2 : c ^ 2 = (n : ℝ) * sigmaSq := hd.2.1
  letI : IsProbabilityMeasure normalizedLaw := hd.2.2.1
  let Pn : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => normalizedLaw)
  let S : Shao.Path n → Shao.Path n := fun a i => a i / c
  have hSm : Measurable S := by
    apply Measurable.of_eval
    intro i
    change Measurable (fun a : Shao.Path n => a i / c)
    exact (measurable_pi_apply i : Measurable (fun a : Shao.Path n => a i)).div_const c
  have hmap : Measure.map S P = Pn := hd.2.2.2.2.2.2 n
  have hs : MeasurePreserving S P Pn := ⟨hSm, hmap⟩
  let Hn : ℝ := H / c ^ 2
  have hHn : 4 * R ^ 2 ≤ Hn := by
    apply (le_div_iff₀ (pow_pos hc 2)).mpr
    rw [hc2]
    dsimp [h] at hH
    nlinarith only [hH]
  have hmHn : (m : ℝ) ≤ 3 * (n : ℝ) * Hn := by
    have he : 3 * (n : ℝ) * Hn = 3 * H / sigmaSq := by
      dsimp [Hn]
      rw [hc2]
      field_simp
      <;> ring
    rwa [he]
  let Qn : Shao.Path n → ℕ → ℝ :=
    fun b k => Shao.prefixSquares (fun i : Fin n => b (Fin.rev i)) k
  let NHn : Shao.Path n → ℕ := fun b =>
    @dite ℕ (∃ k : ℕ, k ≤ L ∧ Hn ≤ Qn b k) (Classical.propDecidable _)
      (fun he => @Nat.find (fun k : ℕ => k ≤ L ∧ Hn ≤ Qn b k)
        (fun k => Classical.propDecidable _) he) (fun _ => L)
  let Nn : Shao.Path n → ℕ := fun b => max m (NHn b)
  let Un : Shao.Path n → ℝ := fun b => Shao.energy b - Shao.prefixSquares b (n - Nn b)
  let Jn : Shao.Path n → ℝ := fun b =>
    (Finset.Icc 0 (Nn b)).sup'
      (by exact ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩)
      (fun l => |Shao.prefixSum b (n - Nn b + l) - Shao.prefixSum b (n - Nn b)|)
  rcases sourceBackward_capped_stopping_energy_budget normalizedLaw n hn
      hd.2.2.2.1 hd.2.2.2.2.2.1 Hn hR hHn m hmL hmHn with
    ⟨hmNHn, hmNn, hmUn, hdata, hiNHn, hiNn, hiUn, hENHn, hENn, hEn, hEUn⟩
  rcases sourceBackward_stopped_second_and_maximal normalizedLaw n hn
      hd.2.2.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2.1 Hn hR hHn m hmL hmHn with
    ⟨_, _, hmJn, _, _, hiJn, _, _, _, hEJn⟩
  change Measurable NHn at hmNHn
  change Measurable Nn at hmNn
  change Measurable Un at hmUn
  change Measurable Jn at hmJn
  change Integrable (fun b => (NHn b : ℝ)) Pn at hiNHn
  change Integrable (fun b => (Nn b : ℝ)) Pn at hiNn
  change Integrable Un Pn at hiUn
  change Integrable (fun b => Jn b ^ 2) Pn at hiJn
  change (∀ b, 1 ≤ NHn b ∧ NHn b ≤ Nn b ∧ Nn b ≤ L ∧ Un b = Qn b (Nn b)) at hdata
  change (∫ b, (NHn b : ℝ) ∂Pn) ≤ 4 * (n : ℝ) * Hn at hENHn
  change (∫ b, (Nn b : ℝ) ∂Pn) ≤ 7 * (n : ℝ) * Hn at hENn
  change (∫ b, Un b ∂Pn) = (1 / (n : ℝ)) * (∫ b, (Nn b : ℝ) ∂Pn) at hEUn
  change (∫ b, Jn b ^ 2 ∂Pn) ≤ 16 * (1 / (n : ℝ)) * (∫ b, (Nn b : ℝ) ∂Pn) at hEJn
  have hQscale (a : Shao.Path n) (k : ℕ) : Qn (S a) k = Qrev a k / c ^ 2 :=
    (te_scaled_path_data (rev a) c).1 k |>.2
  have hNHscale (a : Shao.Path n) : NHn (S a) = NH a := by
    have hr := te_capped_hit_order L H (Qrev a) (te_prefix_squares_monotone (rev a))
    have hn := te_capped_hit_order L Hn (Qn (S a))
      (te_prefix_squares_monotone (fun i : Fin n => S a (Fin.rev i)))
    change NH a ≤ L ∧ ∀ k, k < NH a ↔ k < L ∧ Qrev a k < H at hr
    change NHn (S a) ≤ L ∧ ∀ k, k < NHn (S a) ↔ k < L ∧ Qn (S a) k < Hn at hn
    have heq (k : ℕ) : k < NHn (S a) ↔ k < NH a := by
      rw [hn.2 k, hr.2 k, hQscale]
      change k < L ∧ Qrev a k / c ^ 2 < H / c ^ 2 ↔ k < L ∧ Qrev a k < H
      rw [div_lt_div_iff_of_pos_right (pow_pos hc 2)]
    apply le_antisymm
    · by_contra hh
      have hh' := (heq (NH a)).mp (lt_of_not_ge hh)
      omega
    · by_contra hh
      have hh' := (heq (NHn (S a))).mpr (lt_of_not_ge hh)
      omega
  have hNscale (a : Shao.Path n) : Nn (S a) = N a := by
    simp only [Nn, N, hNHscale]
  have hUscale (a : Shao.Path n) : Un (S a) = U a / c ^ 2 := by
    dsimp only [Un]
    rw [hNscale, (te_scaled_path_data a c).2, (te_scaled_path_data a c).1 _ |>.2]
    exact (sub_div _ _ _).symm
  have hJscale (a : Shao.Path n) : Jn (S a) = J a / c := by
    dsimp only [Jn]
    rw [hNscale]
    exact te_scaled_suffix_max a (N a) c hc
  have hNHfun : (fun a => NHn (S a)) = NH := funext hNHscale
  have hNfun : (fun a => Nn (S a)) = N := funext hNscale
  have hUfun : U = (fun a => c ^ 2 * Un (S a)) := by
    funext a
    rw [hUscale]
    field_simp
  have hJfun : J = (fun a => c * Jn (S a)) := by
    funext a
    rw [hJscale]
    field_simp
  have hmNH : Measurable NH := hNHfun ▸ hmNHn.comp hSm
  have hmN : Measurable N := hNfun ▸ hmNn.comp hSm
  have hmU : Measurable U := by rw [hUfun]; exact (hmUn.comp hSm).const_mul _
  have hmJ : Measurable J := by rw [hJfun]; exact (hmJn.comp hSm).const_mul _
  have hiNH : Integrable (fun a => (NH a : ℝ)) P := by
    convert hs.integrable_comp_of_integrable hiNHn using 1
    funext a
    dsimp only [Function.comp_def]
    rw [hNHscale]
  have hiN : Integrable (fun a => (N a : ℝ)) P := by
    convert hs.integrable_comp_of_integrable hiNn using 1
    funext a
    dsimp only [Function.comp_def]
    rw [hNscale]
  have hiU : Integrable U P := by
    rw [hUfun]
    exact (hs.integrable_comp_of_integrable hiUn).const_mul _
  have hiJ : Integrable (fun a => J a ^ 2) P := by
    convert (hs.integrable_comp_of_integrable hiJn).const_mul (c ^ 2) using 1
    funext a
    dsimp only [Function.comp_def]
    rw [hJscale, div_pow]
    field_simp
  have hintegral (f : Shao.Path n → ℝ) (hf : Measurable f) :
      (∫ b, f b ∂Pn) = ∫ a, f (S a) ∂P := by
    rw [← hmap]
    exact integral_map hSm.aemeasurable hf.aestronglyMeasurable
  have hcast : Measurable (fun k : ℕ => (k : ℝ)) := measurable_of_countable _
  have eNH : (∫ b, (NHn b : ℝ) ∂Pn) = ∫ a, (NH a : ℝ) ∂P := by
    rw [hintegral (fun b => (NHn b : ℝ)) (hcast.comp hmNHn)]
    simp only [hNHscale]
  have eN : (∫ b, (Nn b : ℝ) ∂Pn) = ∫ a, (N a : ℝ) ∂P := by
    rw [hintegral (fun b => (Nn b : ℝ)) (hcast.comp hmNn)]
    simp only [hNscale]
  have eU : (∫ b, Un b ∂Pn) = (∫ a, U a ∂P) / c ^ 2 := by
    rw [hintegral Un hmUn]
    simp_rw [hUscale]
    exact integral_div _ _
  have eJ : (∫ b, Jn b ^ 2 ∂Pn) = (∫ a, J a ^ 2 ∂P) / c ^ 2 := by
    rw [hintegral _ (hmJn.pow_const 2)]
    simp_rw [hJscale, div_pow]
    exact integral_div _ _
  have hstat (a : Shao.Path n) :
      1 ≤ NH a ∧ NH a ≤ N a ∧ N a ≤ L ∧ U a = Qrev a (N a) := by
    have hh := hdata (S a)
    rw [hNHscale, hNscale, hUscale, hQscale] at hh
    refine ⟨hh.1, hh.2.1, hh.2.2.1, ?_⟩
    have he := congrArg (fun z : ℝ => z * c ^ 2) hh.2.2.2
    field_simp at he
    exact he
  have eException :
      Pn.real {b : Shao.Path n | Shao.energy b - Shao.prefixSquares b (n - L) < Hn} =
        P.real exceptional := by
    unfold Measure.real
    have hEm : MeasurableSet {b : Shao.Path n |
        Shao.energy b - Shao.prefixSquares b (n - L) < Hn} :=
      measurableSet_lt
        (Shao.measurable_energy.sub (Shao.measurable_prefixSquares (n - L))) measurable_const
    rw [← hmap, Measure.map_apply (f := S) (μ := P)
      (s := {b : Shao.Path n | Shao.energy b - Shao.prefixSquares b (n - L) < Hn}) hSm hEm]
    congr 2
    ext a
    change Shao.energy (S a) - Shao.prefixSquares (S a) (n - L) < Hn ↔ Qrev a L < H
    rw [(te_scaled_path_data a c).2, (te_scaled_path_data a c).1 _ |>.2, ← sub_div]
    change (Shao.energy a - Shao.prefixSquares a (n - L)) / c ^ 2 < H / c ^ 2 ↔ _
    rw [div_lt_div_iff_of_pos_right (pow_pos hc 2)]
    dsimp only [Qrev, rev]
    rw [te_reverse_energy a L (Nat.div_le_self n 2)]
    rfl
  rw [eNH] at hENHn
  rw [eN] at hENn
  rw [eException] at hEn
  rw [eU, eN] at hEUn
  rw [eJ, eN] at hEJn
  have hpay (q : ℝ) : q * (n : ℝ) * Hn = q * H / sigmaSq := by
    dsimp [Hn]
    rw [hc2]
    field_simp <;> ring
  have hEpay : 12 * Hn = 12 * H / ((n : ℝ) * sigmaSq) := by
    dsimp only [Hn]
    rw [hc2]
    ring
  refine ⟨hHp, hclip, hclipMean, hmNH, hmN, hmU, hmJ, hstat, hiNH, hiN, hiU, hiJ,
    by simpa only [hpay] using hENHn, by simpa only [hpay] using hENn,
    by simpa only [hEpay] using hEn, ?_, ?_⟩
  · calc
      (∫ a, U a ∂P) = c ^ 2 * ((∫ a, U a ∂P) / c ^ 2) := by field_simp
      _ = c ^ 2 * ((1 / (n : ℝ)) * (∫ a, (N a : ℝ) ∂P)) := by rw [hEUn]
      _ = sigmaSq * (∫ a, (N a : ℝ) ∂P) := by rw [hc2]; field_simp
  · calc
      (∫ a, J a ^ 2 ∂P) = c ^ 2 * ((∫ a, J a ^ 2 ∂P) / c ^ 2) := by field_simp
      _ ≤ c ^ 2 * (16 * (1 / (n : ℝ)) * (∫ a, (N a : ℝ) ∂P)) :=
        mul_le_mul_of_nonneg_left hEJn (sq_nonneg c)
      _ = 16 * sigmaSq * (∫ a, (N a : ℝ) ∂P) := by rw [hc2]; field_simp <;> ring

theorem actual_backward_terminal_raw_data
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 4 ≤ n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hsecond : 0 < ∫ z : ℝ, z ^ 2 ∂nu) :
    let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂nu
    let normalizedLaw : Measure ℝ :=
      Measure.map (fun z : ℝ => z / Real.sqrt ((n : ℝ) * sigmaSq)) nu
    let R : ℝ := Shao.truncationBudget normalizedLaw n 0
    let h : ℝ := 4 * (n : ℝ) * sigmaSq * R ^ 2
    R ≤ 1 / 2 → ∀ H : ℝ, h ≤ H →
      let L : ℕ := n / 2
      let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
      let rev : Shao.Path n → Shao.Path n := fun a i => a (Fin.rev i)
      let Qrev : Shao.Path n → ℕ → ℝ := fun a k => Shao.prefixSquares (rev a) k
      let NH : Shao.Path n → ℕ := fun a =>
        @dite ℕ (∃ k : ℕ, k ≤ L ∧ H ≤ Qrev a k) (Classical.propDecidable _)
          (fun he => @Nat.find (fun k : ℕ => k ≤ L ∧ H ≤ Qrev a k)
            (fun k => Classical.propDecidable _) he)
          (fun _ => L)
      ∀ m : ℕ, m ≤ L → (m : ℝ) ≤ 3 * H / sigmaSq →
        let N : Shao.Path n → ℕ := fun a => max m (NH a)
        let r : Shao.Path n → ℕ := fun a => n - N a
        let U : Shao.Path n → ℝ := fun a => Shao.energy a - Shao.prefixSquares a (r a)
        let J : Shao.Path n → ℝ := fun a =>
          (Finset.Icc 0 (N a)).sup'
            (by exact ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩)
            (fun l => |Shao.prefixSum a (r a + l) - Shao.prefixSum a (r a)|)
        let exceptional : Set (Shao.Path n) := {a | Qrev a L < H}
        let kappa : Shao.Path n → ℕ := fun a => energyCutoff a H (Equiv.refl (Fin n))
        let tau : Shao.Path n → ℕ := fun a => min (kappa a) (n - m)
        0 < H ∧
          Integrable (fun z : ℝ => min (z ^ 2) H) nu ∧
          sigmaSq / 2 ≤ (∫ z : ℝ, min (z ^ 2) H ∂nu) ∧
          Measurable NH ∧ Measurable N ∧ Measurable U ∧ Measurable J ∧ Measurable tau ∧
          (∀ a, 1 ≤ NH a ∧ NH a ≤ N a ∧ N a ≤ L ∧
            U a = Qrev a (N a) ∧
            (a ∉ exceptional → tau a = if NH a ≤ m then r a else r a + 1)) ∧
          Integrable (fun a => (NH a : ℝ)) P ∧
          Integrable (fun a => (N a : ℝ)) P ∧ Integrable U P ∧
          Integrable (fun a => J a ^ 2) P ∧
          (∫ a, (NH a : ℝ) ∂P) ≤ 4 * H / sigmaSq ∧
          (∫ a, (N a : ℝ) ∂P) ≤ 7 * H / sigmaSq ∧
          P.real exceptional ≤ 12 * H / ((n : ℝ) * sigmaSq) ∧
          (∫ a, U a ∂P) = sigmaSq * (∫ a, (N a : ℝ) ∂P) ∧
          (∫ a, J a ^ 2 ∂P) ≤ 16 * sigmaSq * (∫ a, (N a : ℝ) ∂P) := by
  classical
  intro sigmaSq normalizedLaw R h hR H hH L P rev Qrev NH m hmL hmH N r U J
    exceptional kappa tau
  rcases te_raw_backward_core nu n hn h2 hmean hsecond hR H hH m hmL hmH with
    ⟨hHp, hclip, hclipMean, hmNH, hmN, hmU, hmJ, hdata, hiNH, hiN, hiU, hiJ,
      hENH, hEN, hE, hEU, hEJ⟩
  have hmTau : Measurable tau :=
    (te_actual_cutoff_measurable n H hHp).min measurable_const
  refine ⟨hHp, hclip, hclipMean, hmNH, hmN, hmU, hmJ, hmTau, ?_,
    hiNH, hiN, hiU, hiJ, hENH, hEN, hE, hEU, hEJ⟩
  intro a
  have hd := hdata a
  refine ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2, ?_⟩
  intro hgood
  have hcross : H ≤ Qrev a L := le_of_not_gt hgood
  have hk : kappa a = n - NH a + 1 := te_reverse_cutoff_identity a hn H hHp hcross
  have hNHn : NH a ≤ n := (hd.2.1.trans hd.2.2.1).trans (Nat.div_le_self n 2)
  dsimp only [tau, r, N]
  rw [hk]
  split_ifs with hh
  · rw [max_eq_left hh, min_eq_right (by omega)]
  · rw [max_eq_right (by omega), min_eq_left (by omega)]

private theorem te_corridor_payment_profile
    (U J w : ℝ) (hU : 0 < U) (hJ : 0 ≤ J) :
    let T : ℝ := 32 * (U + J ^ 2)
    (if 0 < w ∧ w ≤ 2 * J then (1 : ℝ) else 0) +
      (if 2 * J < w then 2 * Real.exp (-(w ^ 2) / (32 * U)) else 0) ≤
        (Real.exp 1 + 2) * Real.exp (-((max w 0) ^ 2) / T) := by
  intro T
  have hT : 0 < T := by dsimp [T]; positivity
  by_cases hn : 0 < w ∧ w ≤ 2 * J
  · rw [if_pos hn, if_neg (not_lt_of_ge hn.2), add_zero, max_eq_left hn.1.le]
    have hw : w ^ 2 ≤ T := by
      have hh : 0 ≤ (2 * J - w) * (2 * J + w) := mul_nonneg (by linarith) (by linarith)
      dsimp [T]
      nlinarith only [hh, hU, sq_nonneg J]
    have he : Real.exp (-1) ≤ Real.exp (-(w ^ 2) / T) := by
      apply Real.exp_le_exp.mpr
      apply (le_div_iff₀ hT).mpr
      nlinarith only [hw]
    calc
      (1 : ℝ) = Real.exp 1 * Real.exp (-1) := by rw [← Real.exp_add]; norm_num
      _ ≤ Real.exp 1 * Real.exp (-(w ^ 2) / T) :=
        mul_le_mul_of_nonneg_left he (Real.exp_pos 1).le
      _ ≤ (Real.exp 1 + 2) * Real.exp (-(w ^ 2) / T) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  · rw [if_neg hn]
    by_cases hf : 2 * J < w
    · rw [if_pos hf, zero_add, max_eq_left (by linarith : 0 ≤ w)]
      have he : Real.exp (-(w ^ 2) / (32 * U)) ≤ Real.exp (-(w ^ 2) / T) := by
        apply Real.exp_le_exp.mpr
        apply (div_le_div_iff₀ (by positivity : 0 < 32 * U) hT).mpr
        have hh := mul_nonneg (sq_nonneg w) (sq_nonneg J)
        dsimp [T]
        nlinarith only [hh]
      exact (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 2)).trans
        (mul_le_mul_of_nonneg_right (by linarith [Real.exp_pos (1 : ℝ)]) (Real.exp_pos _).le)
    · rw [if_neg hf, zero_add]
      positivity

private theorem te_actual_alive_measurable
    (n : ℕ) (I : MonitoredDomain) (x : ℝ) (r : ℕ) :
    MeasurableSet {a : Shao.Path n | sourceAlive I a x r (Equiv.refl (Fin n))} := by
  have hw : Measurable (fun a : Shao.Path n => actualWall a x) :=
    measurable_const.mul (Real.continuous_sqrt.measurable.comp Shao.measurable_energy)
  have hinterior (f : Shao.Path n → ℝ) (hf : Measurable f) :
      MeasurableSet {a | Interior I (actualWall a x) (f a)} := by
    cases I with
    | upper => exact measurableSet_lt hf hw
    | lower => exact measurableSet_lt hw.neg hf
    | interval => exact (measurableSet_lt hw.neg hf).inter (measurableSet_lt hf hw)
  have hp : MeasurableSet {a : Shao.Path n | ∀ k : ℕ, k ≤ r →
      Interior I (actualWall a x) (Shao.prefixSum a k)} := by
    rw [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro k
    by_cases hk : k ≤ r
    · simpa only [hk, true_implies] using hinterior _ (Shao.measurable_prefixSum k)
    · simp only [hk, false_implies, Set.setOf_true, MeasurableSet.univ]
  change MeasurableSet ({a : Shao.Path n | 0 < Shao.energy a} ∩
    ({a | Interior I (actualWall a x) (Shao.prefixSum a n)} ∩
      {a | ∀ k : ℕ, k ≤ r → Interior I (actualWall a x) (Shao.prefixSum a k)}))
  exact (measurableSet_lt measurable_const Shao.measurable_energy).inter
    ((hinterior _ (Shao.measurable_prefixSum n)).inter hp)

private theorem te_actual_source_measurable
    (n : ℕ) (I : MonitoredDomain)
    (P : Measure BridgeNoise) [IsProbabilityMeasure P]
    (x : ℝ) (r : ℕ) (hr : r ≤ n) :
    Measurable (fun a : Shao.Path n =>
      sourceValue I (eventCompletionKernel I P) a x r (Equiv.refl (Fin n))) := by
  classical
  have hF := (eventCompletionKernel_data I P).1
  have hw : Measurable (fun a : Shao.Path n => actualWall a x) :=
    measurable_const.mul (Real.continuous_sqrt.measurable.comp Shao.measurable_energy)
  have hy := Shao.measurable_prefixSum (n := n) r
  have hT : Measurable (fun a : Shao.Path n => remainingEnergy a r (Equiv.refl (Fin n))) :=
    Shao.measurable_energy.sub (Shao.measurable_prefixSquares r)
  have hz := Shao.measurable_prefixSum (n := n) n
  have heq :
      (fun a : Shao.Path n => sourceValue I (eventCompletionKernel I P) a x r
        (Equiv.refl (Fin n))) =
      (fun a => if sourceAlive I a x r (Equiv.refl (Fin n)) then
        eventCompletionKernel I P (actualWall a x, Shao.prefixSum a r,
          remainingEnergy a r (Equiv.refl (Fin n)), Shao.prefixSum a n) else 0) := by
    funext a
    simp only [sourceValue]
    split_ifs with ha
    · apply (eventCompletionKernel_data I P).2.2
      · exact te_alive_wall_pos I a x r (Equiv.refl (Fin n)) ha
      · exact (remaining_population_geometry a r hr (Equiv.refl (Fin n))).1
      · intro hzero
        have hh := ((remaining_population_geometry a r hr (Equiv.refl (Fin n))).2.2.2 hzero).1
        change Shao.prefixSum a n - Shao.prefixSum a r = 0 at hh
        change Shao.prefixSum a r = Shao.prefixSum a n
        linarith
    · rfl
  rw [heq]
  exact Measurable.ite (te_actual_alive_measurable n I x r)
    (hF.comp (hw.prodMk (hy.prodMk (hT.prodMk hz)))) measurable_const

private theorem te_actual_discrepancy_measurable
    (n : ℕ) (I : MonitoredDomain)
    (P : Measure BridgeNoise) [IsProbabilityMeasure P]
    (x : ℝ) (r : ℕ) (hr : r ≤ n) :
    let terminal : Shao.Path n → ℝ := fun a =>
      if sourceAlive I a x n (Equiv.refl (Fin n)) then 1 else 0
    Measurable (fun a : Shao.Path n =>
      (Finset.Icc r n).sup'
        (by exact ⟨r, Finset.mem_Icc.mpr ⟨le_rfl, hr⟩⟩)
        (fun j => |sourceValue I (eventCompletionKernel I P) a x j
          (Equiv.refl (Fin n)) - terminal a|)) := by
  classical
  intro terminal
  have ht : Measurable terminal :=
    Measurable.ite (te_actual_alive_measurable n I x n) measurable_const measurable_const
  have hf (j : ℕ) (hj : j ∈ Finset.Icc r n) :
      Measurable (fun a : Shao.Path n =>
        |sourceValue I (eventCompletionKernel I P) a x j (Equiv.refl (Fin n)) - terminal a|) :=
    continuous_abs.measurable.comp
      ((te_actual_source_measurable n I P x j (Finset.mem_Icc.mp hj).2).sub ht)
  convert Finset.measurable_sup' (s := Finset.Icc r n)
    (by exact ⟨r, Finset.mem_Icc.mpr ⟨le_rfl, hr⟩⟩) hf using 1
  ext a
  exact (Finset.sup'_apply
    (by exact ⟨r, Finset.mem_Icc.mpr ⟨le_rfl, hr⟩⟩)
    (fun (j : ℕ) (a : Shao.Path n) =>
      |sourceValue I (eventCompletionKernel I P) a x j (Equiv.refl (Fin n)) - terminal a|) a).symm

private theorem te_closed_wall_survival_measurable
    (r : ℕ) (q x : ℝ) (signs : Finset ℝ) :
    MeasurableSet {v : Shao.Path r | ∀ eta ∈ signs,
      Shao.maxWithZero (eta • v) ≤ x * Real.sqrt (q + Shao.energy v)} := by
  have hwall : Measurable (fun v : Shao.Path r => x * Real.sqrt (q + Shao.energy v)) :=
    measurable_const.mul ((measurable_const.add Shao.measurable_energy).sqrt)
  have hs : MeasurableSet {v : Shao.Path r | ∀ eta : signs,
      Shao.maxWithZero (eta.val • v) ≤ x * Real.sqrt (q + Shao.energy v)} := by
    rw [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro eta
    apply measurableSet_le _ hwall
    apply Shao.measurable_maxWithZero.comp
    apply Measurable.of_eval
    intro i
    exact (measurable_pi_apply i : Measurable (fun v : Shao.Path r => v i)).const_mul eta.val
  convert hs using 1
  ext v
  simp only [Set.mem_setOf_eq, Subtype.forall]

private theorem te_append_suffix_data
    (r t : ℕ) (b : Shao.Path t) :
    Measurable (fun v : Shao.Path r => Fin.append v b) ∧
      ∀ v : Shao.Path r,
        Shao.energy (Fin.append v b) = Shao.energy v + Shao.energy b ∧
        Shao.prefixSquares (Fin.append v b) r = Shao.energy v ∧
        (∀ k : ℕ, k ≤ r → Shao.prefixSum (Fin.append v b) k = Shao.prefixSum v k) ∧
        ∀ l : ℕ, Shao.prefixSum (Fin.append v b) (r + l) -
          Shao.prefixSum (Fin.append v b) r = Shao.prefixSum b l := by
  classical
  have hm : Measurable (fun v : Shao.Path r => Fin.append v b) := by
    apply Measurable.of_eval
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [Fin.append_left] using
        (measurable_pi_apply j : Measurable (fun v : Shao.Path r => v j))
    · intro j
      simpa only [Fin.append_right] using
        (measurable_const : Measurable (fun _ : Shao.Path r => b j))
  refine ⟨hm, ?_⟩
  intro v
  have henergy : Shao.energy (Fin.append v b) = Shao.energy v + Shao.energy b := by
    unfold Shao.energy
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  have hsquares : Shao.prefixSquares (Fin.append v b) r = Shao.energy v := by
    rw [Shao.prefixSquares, Finset.sum_filter, Fin.sum_univ_add]
    have hl (i : Fin r) : i.val < r := i.is_lt
    have hr (i : Fin t) : ¬r + i.val < r := by omega
    simp [hl, hr, Shao.energy]
  have hhead : Spitzer.head (Fin.append v b) r (Nat.le_add_right r t) = v := by
    ext i
    change Fin.append v b (Fin.castAdd t i) = v i
    exact Fin.append_left _ _ _
  have hpref (k : ℕ) (hk : k ≤ r) :
      Shao.prefixSum (Fin.append v b) k = Shao.prefixSum v k := by
    have hh := Spitzer.head_prefixSum (Fin.append v b) r (Nat.le_add_right r t) k hk
    rw [hhead] at hh
    exact hh.symm
  refine ⟨henergy, hsquares, hpref, ?_⟩
  intro l
  rw [Shao.OQ4.prefixSum_append, hpref r le_rfl]
  ring

private theorem te_sign_values
    (I : MonitoredDomain) :
    let signs : Finset ℝ := match I with
      | .upper => {1}
      | .lower => {-1}
      | .interval => {1, -1}
    signs.card ≤ 2 ∧ ∀ eta ∈ signs, eta = 1 ∨ eta = -1 := by
  classical
  cases I <;> norm_num

private theorem te_fixed_suffix_profile_domination
    {Ω : Type*} [MeasurableSpace Ω]
    (PB : Measure Ω) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B PB)
    (r t : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (I : MonitoredDomain) (b : Shao.Path t) :
    let n : ℕ := r + t
    let U : ℝ := Shao.energy b
    let J : ℝ := (Finset.Icc 0 t).sup'
      (by exact ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩)
      (fun l => |Shao.prefixSum b l|)
    let T : ℝ := 32 * (U + J ^ 2)
    let F : BridgeKernel := eventCompletionKernel I (bridgeLaw B PB)
    let a : Shao.Path r → Shao.Path n := fun v => Fin.append v b
    let terminal : Shao.Path r → ℝ := fun v =>
      if sourceAlive I (a v) x n (Equiv.refl (Fin n)) then 1 else 0
    let discrepancy : Shao.Path r → ℝ := fun v =>
      (Finset.Icc r n).sup'
        (by exact ⟨r, Finset.mem_Icc.mpr ⟨le_rfl, Nat.le_add_right r t⟩⟩)
        (fun j => |sourceValue I F (a v) x j (Equiv.refl (Fin n)) - terminal v|)
    let signs : Finset ℝ := match I with
      | .upper => {1}
      | .lower => {-1}
      | .interval => {1, -1}
    let wall : Shao.Path r → ℝ := fun v => x * Real.sqrt (U + Shao.energy v)
    let A : Set (Shao.Path r) := {v | ∀ eta ∈ signs, Shao.maxWithZero (eta • v) ≤ wall v}
    let w : ℝ → Shao.Path r → ℝ := fun eta v => wall v - eta * Shao.prefixSum v r
    let profiles : Shao.Path r → ℝ := fun v =>
      ∑ eta ∈ signs, Real.exp (-((max (w eta v) 0) ^ 2) / T)
    0 ≤ U ∧ 0 ≤ J ∧
      (U = 0 → ∀ v, discrepancy v = 0) ∧
      (0 < U → ∀ v, discrepancy v ≤ (Real.exp 1 + 2) * A.indicator profiles v) := by
  classical
  intro n U J T F a terminal discrepancy signs wall A w profiles
  have ha := te_append_suffix_data r t b
  have hrn : r ≤ n := Nat.le_add_right r t
  have hU (v : Shao.Path r) :
      remainingEnergy (a v) r (Equiv.refl (Fin n)) = U := by
    change Shao.energy (Fin.append v b) - Shao.prefixSquares (Fin.append v b) r = Shao.energy b
    rw [(ha.2 v).1, (ha.2 v).2.1]
    ring
  have hJ (v : Shao.Path r) :
      (Finset.Icc 0 (n - r)).sup'
        (by exact ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩)
        (fun l => |Shao.prefixSum (a v) (r + l) - Shao.prefixSum (a v) r|) = J := by
    have hlen : n - r = t := by dsimp [n]; omega
    rw [hlen]
    congr 1
    funext l
    rw [(ha.2 v).2.2.2]
  have hwall (v : Shao.Path r) : actualWall (a v) x = wall v := by
    dsimp only [actualWall, a, wall, U]
    rw [(ha.2 v).1, add_comm (Shao.energy v) (Shao.energy b)]
  have hpref (v : Shao.Path r) (k : ℕ) (hk : k ≤ r) :
      Shao.prefixSum (a v) k = Shao.prefixSum v k := (ha.2 v).2.2.1 k hk
  have hJ0 : 0 ≤ J := by
    have hh : |Shao.prefixSum b 0| ≤ J :=
      Finset.le_sup' (fun l => |Shao.prefixSum b l|)
        (Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le t⟩)
    simpa only [Shao.prefixSum_zero, abs_zero] using hh
  refine ⟨Shao.energy_nonneg b, hJ0, ?_, ?_⟩
  · intro hzero v
    exact (actual_source_terminal_corridor_envelope PB B hB n (a v) r hrn x hx I).2.2.1
      (by rw [hU v, hzero])
  · intro hUp v
    have hc := actual_source_terminal_corridor_envelope PB B hB n (a v) r hrn x hx I
    by_cases halive : sourceAlive I (a v) x r (Equiv.refl (Fin n))
    · have hA : v ∈ A := by
        intro eta he
        apply (Shao.maxWithZero_le_iff (eta • v) (wall v)).mpr
        intro k hk
        rw [Shao.prefixSum_smul]
        have hi : Interior I (actualWall (a v) x) (Shao.prefixSum (a v) k) :=
          halive.2.2 k hk
        have hh := ((te_interior_signs I _ _).mp hi eta he).le
        simpa only [hwall v, hpref v k hk] using hh
      have he := hc.2.2.2.2
      change discrepancy v ≤ if 0 < remainingEnergy (a v) r (Equiv.refl (Fin n)) ∧
        sourceAlive I (a v) x r (Equiv.refl (Fin n)) then _ else 0 at he
      have hcond : 0 < remainingEnergy (a v) r (Equiv.refl (Fin n)) ∧
          sourceAlive I (a v) x r (Equiv.refl (Fin n)) :=
        ⟨by rw [hU v]; exact hUp, halive⟩
      rw [if_pos hcond, hJ v] at he
      simp only [hU v, hwall v, hpref v r le_rfl] at he
      change discrepancy v ≤ ∑ eta ∈ signs,
        ((if 0 < w eta v ∧ w eta v ≤ 2 * J then (1 : ℝ) else 0) +
          (if 2 * J < w eta v then 2 * Real.exp (-(w eta v ^ 2) / (32 * U)) else 0)) at he
      rw [Set.indicator_of_mem hA]
      dsimp only [profiles]
      rw [Finset.mul_sum]
      apply he.trans
      apply Finset.sum_le_sum
      intro eta _
      exact te_corridor_payment_profile U J (w eta v) hUp hJ0
    · have he := hc.2.2.2.2
      change discrepancy v ≤ if 0 < remainingEnergy (a v) r (Equiv.refl (Fin n)) ∧
        sourceAlive I (a v) x r (Equiv.refl (Fin n)) then _ else 0 at he
      have hcond : ¬(0 < remainingEnergy (a v) r (Equiv.refl (Fin n)) ∧
          sourceAlive I (a v) x r (Equiv.refl (Fin n))) := fun h => halive h.2
      rw [if_neg hcond] at he
      apply he.trans
      by_cases hv : v ∈ A
      · rw [Set.indicator_of_mem hv]
        apply mul_nonneg (by positivity)
        exact Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
      · rw [Set.indicator_of_notMem hv, mul_zero]

theorem actual_fixed_suffix_terminal_corridor_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω]
        (PB : Measure Ω) [IsProbabilityMeasure PB]
        (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B PB →
        ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu] (r t : ℕ), 0 < r → t ≤ r →
          Integrable (fun z : ℝ => z ^ 2) nu → (∫ z : ℝ, z ∂nu) = 0 →
          0 < (∫ z : ℝ, z ^ 2 ∂nu) →
          let n : ℕ := r + t
          let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂nu
          let R : ℝ := Shao.truncationBudget
            (Measure.map (fun z : ℝ => z / Real.sqrt ((n : ℝ) * sigmaSq)) nu) n 0
          let h : ℝ := 4 * (n : ℝ) * sigmaSq * R ^ 2
          ∀ H : ℝ, h ≤ H → ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
            ∀ (I : MonitoredDomain) (b : Shao.Path t),
              let F : BridgeKernel := eventCompletionKernel I (bridgeLaw B PB)
              let U : ℝ := Shao.energy b
              let J : ℝ := (Finset.Icc 0 t).sup'
                (by exact ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩)
                (fun l => |Shao.prefixSum b l|)
              let a : Shao.Path r → Shao.Path n := fun v => Fin.append v b
              let terminal : Shao.Path r → ℝ := fun v =>
                if sourceAlive I (a v) x n (Equiv.refl (Fin n)) then 1 else 0
              let discrepancy : Shao.Path r → ℝ := fun v =>
                (Finset.Icc r n).sup'
                  (by exact ⟨r, Finset.mem_Icc.mpr ⟨le_rfl, Nat.le_add_right r t⟩⟩)
                  (fun j => |sourceValue I F (a v) x j (Equiv.refl (Fin n)) - terminal v|)
              Integrable discrepancy (Measure.pi (fun _ : Fin r => nu)) ∧
                (∫ v, discrepancy v ∂Measure.pi (fun _ : Fin r => nu)) ≤
                  C * (J ^ 2 + U + H) / ((r : ℝ) * sigmaSq) := by
  classical
  obtain ⟨Cp, hCp, hprofile⟩ := iid_true_wall_gaussian_profile
  refine ⟨64 * (Real.exp 1 + 2) * Cp, by positivity, ?_⟩
  intro Ω _ PB _ B hB nu hnu r t hr htr h2 hmean hsecond n sigmaSq R h H hH x hx hx1
    I b F U J a terminal discrepancy
  letI : IsProbabilityMeasure nu := hnu
  letI : IsProbabilityMeasure (bridgeLaw B PB) := isProbabilityMeasure_bridgeLaw B PB hB
  let P : Measure (Shao.Path r) := Measure.pi (fun _ : Fin r => nu)
  let V : ℝ := (r : ℝ) * sigmaSq
  have hV : 0 < V := mul_pos (by exact_mod_cast hr) hsecond
  have hn : 0 < n := by dsimp [n]; omega
  have hg := raw_truncation_budget_suffix_geometry nu n hn h2 hsecond
  change 0 < R ∧ R ≤ 1 ∧ _ ∧ 0 < h ∧ _ ∧ _ ∧ _ at hg
  have hHp : 0 < H := hg.2.2.2.1.trans_le hH
  have hd (v : Shao.Path r) :=
    actual_source_terminal_corridor_envelope PB B hB n (a v) r
      (Nat.le_add_right r t) x hx I
  have hDm : Measurable discrepancy :=
    (te_actual_discrepancy_measurable n I (bridgeLaw B PB) x r
      (Nat.le_add_right r t)).comp (te_append_suffix_data r t b).1
  have hDi : Integrable discrepancy P := by
    apply Integrable.of_bound hDm.aestronglyMeasurable 1
    exact ae_of_all _ fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hd v).1]
      exact (hd v).2.1
  refine ⟨hDi, ?_⟩
  have hdom := te_fixed_suffix_profile_domination PB B hB r t x hx I b
  have hU : 0 ≤ U := hdom.1
  have hJ : 0 ≤ J := hdom.2.1
  have hright : 0 ≤ 64 * (Real.exp 1 + 2) * Cp * (J ^ 2 + U + H) / V := by
    positivity
  by_cases hUz : U = 0
  · have he : discrepancy = 0 := funext (hdom.2.2.1 hUz)
    simp only [he, Pi.zero_apply, integral_zero]
    exact hright
  by_cases hxz : x = 0
  · have he : discrepancy = 0 := funext fun v => (hd v).2.2.2.1 hxz
    simp only [he, Pi.zero_apply, integral_zero]
    exact hright
  have hUp : 0 < U := lt_of_le_of_ne hU (Ne.symm hUz)
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hxz)
  let T : ℝ := 32 * (U + J ^ 2)
  have hT : 0 < T := by dsimp [T]; positivity
  let signs : Finset ℝ := match I with
    | .upper => {1}
    | .lower => {-1}
    | .interval => {1, -1}
  let wall : Shao.Path r → ℝ := fun v => x * Real.sqrt (U + Shao.energy v)
  let A : Set (Shao.Path r) := {v | ∀ eta ∈ signs,
    Shao.maxWithZero (eta • v) ≤ wall v}
  let w : ℝ → Shao.Path r → ℝ := fun eta v => wall v - eta * Shao.prefixSum v r
  let f : ℝ → Shao.Path r → ℝ := fun eta v =>
    Real.exp (-((max (w eta v) 0) ^ 2) / T)
  let profiles : Shao.Path r → ℝ := fun v => ∑ eta ∈ signs, f eta v
  have hsigns : signs.card ≤ 2 ∧ ∀ eta ∈ signs, eta = 1 ∨ eta = -1 := by
    cases I <;> norm_num [signs]
  let Rp : ℝ := Shao.truncationBudget
    (Measure.map (fun z : ℝ => z / Real.sqrt V) nu) r 0
  have hA : MeasurableSet A := te_closed_wall_survival_measurable r U x signs
  have hwm : Measurable wall :=
    measurable_const.mul ((measurable_const.add Shao.measurable_energy).sqrt)
  have hfi (eta : ℝ) : Integrable (A.indicator (f eta)) P := by
    simpa only [sub_zero] using
      (gaussian_wall_profile_layer_cake P A hA (w eta)
        (hwm.sub (measurable_const.mul (Shao.measurable_prefixSum r)))
        T 0 hT le_rfl).1
  have hfbound (eta : ℝ) (he : eta ∈ signs) :
      (∫ v, A.indicator (f eta) v ∂P) ≤ Cp * (T / V + Rp ^ 2) := by
    have hp := hprofile nu r hr h2 hmean hsecond U T 0 0 x hU hT
      (by simpa using hT.le) hxp hx1 signs hsigns.2 true eta he
    simpa only [Bool.true_eq, if_true, abs_zero, zero_add, zero_div, add_zero,
      one_pow, mul_one, sub_zero] using hp
  have heq : A.indicator profiles = fun v => ∑ eta ∈ signs, A.indicator (f eta) v := by
    funext v
    by_cases hv : v ∈ A
    · simp only [Set.indicator_of_mem hv]; rfl
    · simp only [Set.indicator_of_notMem hv, Finset.sum_const_zero]
  have hpi : Integrable (A.indicator profiles) P := by
    rw [heq]
    exact integrable_finsetSum _ (fun eta _ => hfi eta)
  have hsum : (∫ v, A.indicator profiles v ∂P) ≤ 2 * Cp * (T / V + Rp ^ 2) := by
    calc
      _ = ∑ eta ∈ signs, ∫ v, A.indicator (f eta) v ∂P := by
        rw [heq]
        exact integral_finsetSum _ (fun eta _ => hfi eta)
      _ ≤ ∑ eta ∈ signs, Cp * (T / V + Rp ^ 2) := Finset.sum_le_sum hfbound
      _ = (signs.card : ℝ) * (Cp * (T / V + Rp ^ 2)) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * (Cp * (T / V + Rp ^ 2)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hsigns.1)
          (by positivity)
      _ = _ := by ring
  have hRp : 0 < Rp :=
    (raw_truncation_budget_suffix_geometry nu r hr h2 hsecond).1
  have hcomp : Rp ≤ Real.sqrt ((n : ℝ) / (r : ℝ)) * R :=
    hg.2.2.2.2.2.1 r hr (Nat.le_add_right r t)
  have hsq : Rp ^ 2 ≤ ((n : ℝ) / (r : ℝ)) * R ^ 2 := by
    have hh := (sq_le_sq₀ hRp.le
      (mul_nonneg (Real.sqrt_nonneg _) hg.1.le)).2 hcomp
    simpa only [mul_pow, Real.sq_sqrt (div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg r))]
      using hh
  have hpay : V * Rp ^ 2 ≤ H / 4 := by
    have he : V * (((n : ℝ) / (r : ℝ)) * R ^ 2) =
        (n : ℝ) * sigmaSq * R ^ 2 := by
      dsimp [V]
      have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
      field_simp
      <;> ring
    have hh := mul_le_mul_of_nonneg_left hsq hV.le
    rw [he] at hh
    change 4 * (n : ℝ) * sigmaSq * R ^ 2 ≤ H at hH
    nlinarith only [hh, hH]
  have hfirst : (∫ v, discrepancy v ∂P) ≤
      (Real.exp 1 + 2) * (2 * Cp * (T / V + Rp ^ 2)) := by
    have hdprofile : ∀ v, discrepancy v ≤ (Real.exp 1 + 2) * A.indicator profiles v := by
      cases I <;>
        simpa only [n, F, U, J, a, terminal, discrepancy, signs, wall, A, w, f, profiles, T]
          using hdom.2.2.2 hUp
    calc
      _ ≤ ∫ v, (Real.exp 1 + 2) * A.indicator profiles v ∂P :=
        integral_mono_ae hDi (hpi.const_mul _) (ae_of_all _ hdprofile)
      _ = (Real.exp 1 + 2) * (∫ v, A.indicator profiles v ∂P) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
  apply hfirst.trans
  have htot : 2 * Cp * (T / V + Rp ^ 2) ≤
      64 * Cp * (J ^ 2 + U + H) / V := by
    apply (le_div_iff₀ hV).mpr
    have he : (2 * Cp * (T / V + Rp ^ 2)) * V =
        2 * Cp * (T + V * Rp ^ 2) := by field_simp <;> ring
    rw [he]
    dsimp only [T]
    nlinarith only [mul_le_mul_of_nonneg_left hpay hCp.le,
      mul_nonneg hCp.le hHp.le]
  calc
    _ ≤ (Real.exp 1 + 2) * (64 * Cp * (J ^ 2 + U + H) / V) :=
      mul_le_mul_of_nonneg_left htot (by positivity)
    _ = _ := by ring
/- Frozen before implementation: measurable bounded actual discrepancy at a measurable finite rank. -/
private theorem te_random_discrepancy_data
    (n : ℕ) (I : MonitoredDomain)
    (P : Measure BridgeNoise) [IsProbabilityMeasure P]
    (x : ℝ) (K : Shao.Path n → ℕ) (hK : Measurable K)
    (hKn : ∀ a, K a ≤ n) :
    let terminal : Shao.Path n → ℝ := fun a =>
      if sourceAlive I a x n (Equiv.refl (Fin n)) then 1 else 0
    let D : Shao.Path n → ℝ := fun a =>
      (Finset.Icc (K a) n).sup'
        (by exact ⟨n, Finset.mem_Icc.mpr ⟨hKn a, le_rfl⟩⟩)
        (fun j => |sourceValue I (eventCompletionKernel I P) a x j
          (Equiv.refl (Fin n)) - terminal a|)
    Measurable D ∧ ∀ a, 0 ≤ D a ∧ D a ≤ 1 := by
  classical
  intro terminal D
  let Q : Shao.Path n × ℕ → ℝ := fun p =>
    if hk : p.2 ≤ n then
      (Finset.Icc p.2 n).sup'
        (by exact ⟨n, Finset.mem_Icc.mpr ⟨hk, le_rfl⟩⟩)
        (fun j => |sourceValue I (eventCompletionKernel I P) p.1 x j
          (Equiv.refl (Fin n)) - terminal p.1|)
    else 0
  have hQ : Measurable Q := by
    apply measurable_from_prod_countable_left
    intro k
    by_cases hk : k ≤ n
    · simpa only [Q, hk, dite_true] using
        te_actual_discrepancy_measurable n I P x k hk
    · simp only [Q, hk, dite_false]
      exact measurable_const
  have heq : D = fun a => Q (a, K a) := by
    funext a
    simp only [Q, hKn a, dite_true]
    rfl
  refine ⟨heq ▸ (hQ.comp (measurable_id.prodMk hK)), ?_⟩
  intro a
  exact ⟨(te_terminal_discrepancy_boundaries I P a (K a) (hKn a) x).1,
    (te_terminal_discrepancy_boundaries I P a (K a) (hKn a) x).2.1⟩
/- Frozen before implementation: exact finite prefix/suffix recomposition and actual square/sum data. -/
private theorem te_merge_at_data
    (n r t : ℕ) (hlen : n = r + t) :
    let merge : Shao.Path r × Shao.Path t → Shao.Path n := fun p i =>
      Fin.append p.1 p.2 (finCongr hlen i)
    let prefixPart : Shao.Path n → Shao.Path r := fun a i =>
      a ⟨i.val, by have hi := i.is_lt; omega⟩
    let suffixPart : Shao.Path n → Shao.Path t := fun a i =>
      a ⟨r + i.val, by have hi := i.is_lt; omega⟩
    Measurable merge ∧
      (∀ a, merge (prefixPart a, suffixPart a) = a) ∧
      ∀ p, Shao.energy (merge p) = Shao.energy p.1 + Shao.energy p.2 ∧
        Shao.prefixSquares (merge p) r = Shao.energy p.1 ∧
        ∀ l, Shao.prefixSum (merge p) (r + l) -
          Shao.prefixSum (merge p) r = Shao.prefixSum p.2 l := by
  classical
  subst n
  intro merge prefixPart suffixPart
  have hm : Measurable merge := by
    apply Measurable.of_eval
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [merge, finCongr_refl, Equiv.refl_apply, Fin.append_left, Function.comp_def] using
        (measurable_pi_apply j : Measurable (fun a : Shao.Path r => a j)).comp
          (measurable_fst : Measurable (fun p : Shao.Path r × Shao.Path t => p.1))
    · intro j
      simpa only [merge, finCongr_refl, Equiv.refl_apply, Fin.append_right, Function.comp_def] using
        (measurable_pi_apply j : Measurable (fun a : Shao.Path t => a j)).comp
          (measurable_snd : Measurable (fun p : Shao.Path r × Shao.Path t => p.2))
  refine ⟨hm, ?_, ?_⟩
  · intro a
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [merge, finCongr_refl, Equiv.refl_apply, Fin.append_left, prefixPart]
      rfl
    · intro j
      simp only [merge, finCongr_refl, Equiv.refl_apply, Fin.append_right, suffixPart]
      rfl
  · intro p
    have hd := (te_append_suffix_data r t p.2).2 p.1
    exact ⟨hd.1, hd.2.1, hd.2.2.2⟩
/- Frozen before implementation: transport of the actual proved fixed suffix budget across an exact length equality. -/
private theorem te_fixed_suffix_budget_at :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω]
        (PB : Measure Ω) [IsProbabilityMeasure PB]
        (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B PB →
        ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu] (n r t : ℕ), ∀ hlen : n = r + t, 0 < r → t ≤ r →
          Integrable (fun z : ℝ => z ^ 2) nu → (∫ z : ℝ, z ∂nu) = 0 →
          0 < (∫ z : ℝ, z ^ 2 ∂nu) →
          let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂nu
          let R : ℝ := Shao.truncationBudget
            (Measure.map (fun z : ℝ => z / Real.sqrt ((n : ℝ) * sigmaSq)) nu) n 0
          let h : ℝ := 4 * (n : ℝ) * sigmaSq * R ^ 2
          ∀ H : ℝ, h ≤ H → ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
            ∀ (I : MonitoredDomain) (b : Shao.Path t),
              let F : BridgeKernel := eventCompletionKernel I (bridgeLaw B PB)
              let U : ℝ := Shao.energy b
              let J : ℝ := (Finset.Icc 0 t).sup'
                (by exact ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩)
                (fun l => |Shao.prefixSum b l|)
              let a : Shao.Path r → Shao.Path n := fun v i =>
                Fin.append v b (finCongr hlen i)
              let terminal : Shao.Path r → ℝ := fun v =>
                if sourceAlive I (a v) x n (Equiv.refl (Fin n)) then 1 else 0
              let discrepancy : Shao.Path r → ℝ := fun v =>
                (Finset.Icc r n).sup'
                  (by exact ⟨r, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩)
                  (fun j => |sourceValue I F (a v) x j (Equiv.refl (Fin n)) - terminal v|)
              Integrable discrepancy (Measure.pi (fun _ : Fin r => nu)) ∧
                (∫ v, discrepancy v ∂Measure.pi (fun _ : Fin r => nu)) ≤
                  C * (J ^ 2 + U + H) / ((r : ℝ) * sigmaSq) := by
  classical
  obtain ⟨C, hC, hfix⟩ := actual_fixed_suffix_terminal_corridor_budget
  refine ⟨C, hC, ?_⟩
  intro Ω _ PB _ B hB nu hnu n r t hlen
  subst n
  exact hfix PB B hB nu r t
/- Named finite-rank assumptions are in scope for the literal cast proofs; proposal25 is retained. Frozen before implementation: bounded centered actual suffix sections.
   The subtraction uses min(cost,1), so the already proved bounded stopped Fubini
   applies without an unbounded-integral premise or a new disintegration producer. -/
private theorem te_fixed_suffix_centered_sections :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω]
        (PB : Measure Ω) [IsProbabilityMeasure PB]
        (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B PB →
        ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu] (n t : ℕ),
          ∀ hn : 0 < n, ∀ ht : t ≤ n / 2,
          Integrable (fun z : ℝ => z ^ 2) nu → (∫ z : ℝ, z ∂nu) = 0 →
          0 < (∫ z : ℝ, z ^ 2 ∂nu) →
          let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂nu
          let R : ℝ := Shao.truncationBudget
            (Measure.map (fun z : ℝ => z / Real.sqrt ((n : ℝ) * sigmaSq)) nu) n 0
          let h : ℝ := 4 * (n : ℝ) * sigmaSq * R ^ 2
          ∀ H : ℝ, h ≤ H → ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
            ∀ I : MonitoredDomain,
              let r : ℕ := n - t
              let F : BridgeKernel := eventCompletionKernel I (bridgeLaw B PB)
              let merge : Shao.Path r × Shao.Path t → Shao.Path n := fun p i =>
                Fin.append p.1 p.2 (finCongr (by omega : n = r + t) i)
              let prefixPart : Shao.Path n → Shao.Path r := fun a i =>
                a ⟨i.val, lt_of_lt_of_le i.is_lt (Nat.sub_le n t)⟩
              let suffixPart : Shao.Path n → Shao.Path t := fun a i =>
                a ⟨r + i.val, by have hi := i.is_lt; dsimp [r]; omega⟩
              let terminal : Shao.Path n → ℝ := fun a =>
                if sourceAlive I a x n (Equiv.refl (Fin n)) then 1 else 0
              let discrepancy : Shao.Path n → ℝ := fun a =>
                (Finset.Icc r n).sup'
                  (by exact ⟨n, Finset.mem_Icc.mpr ⟨Nat.sub_le n t, le_rfl⟩⟩)
                  (fun j => |sourceValue I F a x j (Equiv.refl (Fin n)) - terminal a|)
              let suffixJ : Shao.Path t → ℝ := fun b =>
                (Finset.Icc 0 t).sup'
                  (by exact ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩)
                  (fun l => |Shao.prefixSum b l|)
              let cost : Shao.Path t → ℝ := fun b =>
                2 * C * (suffixJ b ^ 2 + Shao.energy b + H) / ((n : ℝ) * sigmaSq)
              let Phi : Shao.Path r × Shao.Path t → ℝ := fun p =>
                discrepancy (merge p) - min (cost p.2) 1
              let actualJ : Shao.Path n → ℝ := fun a =>
                (Finset.Icc 0 t).sup'
                  (by exact ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩)
                  (fun l => |Shao.prefixSum a (r + l) - Shao.prefixSum a r|)
              Measurable Phi ∧ (∀ p, |Phi p| ≤ 1) ∧
                (∀ b, (∫ v : Shao.Path r, Phi (v, b)
                  ∂Measure.pi (fun _ : Fin r => nu)) ≤ 0) ∧
                ∀ a, Phi (prefixPart a, suffixPart a) =
                  discrepancy a - min
                    (2 * C * (actualJ a ^ 2 +
                      remainingEnergy a r (Equiv.refl (Fin n)) + H) /
                        ((n : ℝ) * sigmaSq)) 1 := by
  classical
  obtain ⟨C, hC, hfix⟩ := te_fixed_suffix_budget_at
  refine ⟨C, hC, ?_⟩
  intro Ω _ PB _ B hB nu hnu n t hn ht h2 hmean hsecond sigmaSq R h H hH x hx hx1
    I r F merge prefixPart suffixPart terminal discrepancy suffixJ cost Phi actualJ
  letI : IsProbabilityMeasure nu := hnu
  letI : IsProbabilityMeasure (bridgeLaw B PB) := isProbabilityMeasure_bridgeLaw B PB hB
  have htn : t ≤ n := ht.trans (Nat.div_le_self n 2)
  have hrn : r ≤ n := Nat.sub_le n t
  have hr : 0 < r := by dsimp [r]; omega
  have htr : t ≤ r := by dsimp [r]; omega
  have hlen : n = r + t := by dsimp [r]; omega
  have hV : 0 < (n : ℝ) * sigmaSq := mul_pos (by exact_mod_cast hn) hsecond
  have hrV : 0 < (r : ℝ) * sigmaSq := mul_pos (by exact_mod_cast hr) hsecond
  have hg := raw_truncation_budget_suffix_geometry nu n hn h2 hsecond
  have hHp : 0 < H := hg.2.2.2.1.trans_le hH
  have hm := te_merge_at_data n r t hlen
  have hDm : Measurable discrepancy :=
    te_actual_discrepancy_measurable n I (bridgeLaw B PB) x r hrn
  have hDb (a : Shao.Path n) : 0 ≤ discrepancy a ∧ discrepancy a ≤ 1 :=
    ⟨(te_terminal_discrepancy_boundaries I (bridgeLaw B PB) a r hrn x).1,
      (te_terminal_discrepancy_boundaries I (bridgeLaw B PB) a r hrn x).2.1⟩
  have hJm : Measurable suffixJ := by
    have hf (l : ℕ) (_ : l ∈ Finset.Icc 0 t) :
        Measurable (fun b : Shao.Path t => |Shao.prefixSum b l|) :=
      continuous_abs.measurable.comp (Shao.measurable_prefixSum l)
    convert Finset.measurable_sup' (s := Finset.Icc 0 t)
      (by exact ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩) hf using 1
    ext b
    exact (Finset.sup'_apply
      (by exact ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩)
      (fun (l : ℕ) (b : Shao.Path t) => |Shao.prefixSum b l|) b).symm
  have hcm : Measurable cost :=
    (((hJm.pow_const 2).add Shao.measurable_energy).add_const H).const_mul (2 * C)
      |>.div_const _
  have hc0 (b : Shao.Path t) : 0 ≤ cost b := by
    dsimp [cost]
    exact div_nonneg (mul_nonneg (by positivity)
      (by have he := Shao.energy_nonneg b; positivity)) hV.le
  have hPhi : Measurable Phi :=
    (hDm.comp hm.1).sub ((hcm.comp measurable_snd).min measurable_const)
  refine ⟨hPhi, ?_, ?_, ?_⟩
  · intro p
    change |discrepancy (merge p) - min (cost p.2) 1| ≤ 1
    rw [abs_sub_le_iff]
    have hmin0 : 0 ≤ min (cost p.2) 1 := le_min (hc0 _) (by norm_num)
    have hmin1 : min (cost p.2) 1 ≤ 1 := min_le_right _ _
    constructor <;> linarith [(hDb (merge p)).1, (hDb (merge p)).2]
  · intro b
    let Q : Measure (Shao.Path r) := Measure.pi (fun _ : Fin r => nu)
    letI : IsProbabilityMeasure Q := by dsimp [Q]; infer_instance
    have hs := hfix PB B hB nu n r t hlen hr htr h2 hmean hsecond H hH x hx hx1 I b
    change Integrable (fun v : Shao.Path r => discrepancy (merge (v, b))) Q ∧
      (∫ v, discrepancy (merge (v, b)) ∂Q) ≤
        C * (suffixJ b ^ 2 + Shao.energy b + H) / ((r : ℝ) * sigmaSq) at hs
    have hone : (∫ v, discrepancy (merge (v, b)) ∂Q) ≤ 1 := by
      calc
        _ ≤ ∫ _ : Shao.Path r, (1 : ℝ) ∂Q :=
          integral_mono_ae hs.1 (integrable_const 1) (ae_of_all _ fun v => (hDb _).2)
        _ = 1 := by simp
    have hcost : C * (suffixJ b ^ 2 + Shao.energy b + H) / ((r : ℝ) * sigmaSq) ≤ cost b := by
      dsimp [cost]
      apply (div_le_div_iff₀ hrV hV).mpr
      have hnr : (n : ℝ) ≤ 2 * (r : ℝ) := by exact_mod_cast (show n ≤ 2 * r by omega)
      have hw : 0 ≤ C * (suffixJ b ^ 2 + Shao.energy b + H) := by
        have he := Shao.energy_nonneg b
        positivity
      have hh := mul_le_mul_of_nonneg_left hnr (mul_nonneg hw hsecond.le)
      nlinarith only [hh]
    have hmin : (∫ v, discrepancy (merge (v, b)) ∂Q) ≤ min (cost b) 1 :=
      le_min (hs.2.trans hcost) hone
    change (∫ v, discrepancy (merge (v, b)) - min (cost b) 1 ∂Q) ≤ 0
    rw [integral_sub hs.1 (integrable_const _)]
    have hQreal : Q.real Set.univ = 1 := by simp [Measure.real]
    rw [integral_const, hQreal, one_smul]
    exact sub_nonpos.mpr hmin
  · intro a
    have ha : merge (prefixPart a, suffixPart a) = a := hm.2.1 a
    have hd := hm.2.2 (prefixPart a, suffixPart a)
    change Shao.energy (merge (prefixPart a, suffixPart a)) =
        Shao.energy (prefixPart a) + Shao.energy (suffixPart a) ∧
      Shao.prefixSquares (merge (prefixPart a, suffixPart a)) r = Shao.energy (prefixPart a) ∧
      ∀ l, Shao.prefixSum (merge (prefixPart a, suffixPart a)) (r + l) -
        Shao.prefixSum (merge (prefixPart a, suffixPart a)) r =
          Shao.prefixSum (suffixPart a) l at hd
    have hd' : Shao.energy a = Shao.energy (prefixPart a) + Shao.energy (suffixPart a) ∧
        Shao.prefixSquares a r = Shao.energy (prefixPart a) ∧
        ∀ l, Shao.prefixSum a (r + l) - Shao.prefixSum a r =
          Shao.prefixSum (suffixPart a) l := by
      simpa only [ha] using hd
    have hU : Shao.energy (suffixPart a) = remainingEnergy a r (Equiv.refl (Fin n)) := by
      change Shao.energy (suffixPart a) = Shao.energy a - Shao.prefixSquares a r
      rw [hd'.1, hd'.2.1]
      ring
    have hJ : suffixJ (suffixPart a) = actualJ a := by
      dsimp only [suffixJ, actualJ]
      congr 1
      funext l
      rw [hd'.2.2 l]
    change discrepancy (merge (prefixPart a, suffixPart a)) - min (cost (suffixPart a)) 1 = _
    rw [ha]
    dsimp only [cost]
    rw [hU, hJ]
theorem actual_stopped_terminal_envelope_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω]
        (PB : Measure Ω) [IsProbabilityMeasure PB]
        (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B PB →
        ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ), 0 < n →
          Integrable (fun z : ℝ => z ^ 2) nu → (∫ z : ℝ, z ∂nu) = 0 →
          0 < (∫ z : ℝ, z ^ 2 ∂nu) →
          let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂nu
          let R : ℝ := Shao.truncationBudget
            (Measure.map (fun z : ℝ => z / Real.sqrt ((n : ℝ) * sigmaSq)) nu) n 0
          let h : ℝ := 4 * (n : ℝ) * sigmaSq * R ^ 2
          ∀ H : ℝ, h ≤ H → ∀ m : ℕ, m ≤ n / 2 → (m : ℝ) ≤ 3 * H / sigmaSq →
            ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∀ I : MonitoredDomain,
              let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
              let F : BridgeKernel := eventCompletionKernel I (bridgeLaw B PB)
              let kappa : Shao.Path n → ℕ := fun a => energyCutoff a H (Equiv.refl (Fin n))
              let tau : Shao.Path n → ℕ := fun a => min (kappa a) (n - m)
              let terminal : Shao.Path n → ℝ := fun a =>
                if sourceAlive I a x n (Equiv.refl (Fin n)) then 1 else 0
              let discrepancy : Shao.Path n → ℝ := fun a =>
                (Finset.Icc (tau a) n).sup'
                  (by exact ⟨n, Finset.mem_Icc.mpr
                    ⟨(Nat.min_le_right _ _).trans (Nat.sub_le n m), le_rfl⟩⟩)
                  (fun j => |sourceValue I F a x j (Equiv.refl (Fin n)) - terminal a|)
              Integrable discrepancy P ∧
                (∫ a, discrepancy a ∂P) ≤ C * H / ((n : ℝ) * sigmaSq) := by
  classical
  obtain ⟨C, hC, hsections⟩ := te_fixed_suffix_centered_sections
  refine ⟨240 * C + 18, by positivity, ?_⟩
  intro Ω _ PB _ B hB nu hnu n hn h2 hmean hsecond sigmaSq R h H hH m hm hmH x hx hx1
    I P F kappa tau terminal discrepancy
  letI : IsProbabilityMeasure nu := hnu
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  letI : IsProbabilityMeasure (bridgeLaw B PB) := isProbabilityMeasure_bridgeLaw B PB hB
  let V : ℝ := (n : ℝ) * sigmaSq
  have hV : 0 < V := mul_pos (by exact_mod_cast hn) hsecond
  have hg := raw_truncation_budget_suffix_geometry nu n hn h2 hsecond
  have hHp : 0 < H := hg.2.2.2.1.trans_le hH
  have htaun : ∀ a, tau a ≤ n := fun a =>
    (Nat.min_le_right _ _).trans (Nat.sub_le n m)
  have hmTau : Measurable tau :=
    (te_actual_cutoff_measurable n H hHp).min measurable_const
  have hd := te_random_discrepancy_data n I (bridgeLaw B PB) x tau hmTau htaun
  have hiD : Integrable discrepancy P := by
    apply Integrable.of_bound hd.1.aestronglyMeasurable 1
    exact ae_of_all _ fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hd.2 a).1]
      exact (hd.2 a).2
  have hEone : (∫ a, discrepancy a ∂P) ≤ 1 := by
    calc
      _ ≤ ∫ _ : Shao.Path n, (1 : ℝ) ∂P :=
        integral_mono_ae hiD (integrable_const 1) (ae_of_all _ fun a => (hd.2 a).2)
      _ = 1 := by simp
  refine ⟨hiD, ?_⟩
  by_cases hn4 : 4 ≤ n
  swap
  · apply hEone.trans
    apply (le_div_iff₀ hV).mpr
    have hn3 : (n : ℝ) ≤ 3 := by exact_mod_cast (show n ≤ 3 by omega)
    have hh : sigmaSq / 2 ≤ H := hg.2.2.2.2.1.trans hH
    have hnv : V ≤ 6 * H := by
      dsimp [V]
      nlinarith only [mul_le_mul_of_nonneg_right hn3 hsecond.le, hh]
    nlinarith only [hnv, mul_pos hC hHp, hHp]
  by_cases hR : R ≤ 1 / 2
  swap
  · apply hEone.trans
    apply (le_div_iff₀ hV).mpr
    have hRp : 1 / 2 < R := lt_of_not_ge hR
    have hsq : 1 < 4 * R ^ 2 := by nlinarith only [sq_nonneg (R - 1 / 2), hRp]
    have hh : V * (4 * R ^ 2) ≤ H := by
      change 4 * (n : ℝ) * sigmaSq * R ^ 2 ≤ H at hH
      dsimp [V]
      nlinarith only [hH]
    have hnv : V ≤ H := by
      have hm' := mul_le_mul_of_nonneg_left hsq.le hV.le
      linarith only [hm', hh]
    nlinarith only [hnv, mul_pos hC hHp, hHp]
  let L : ℕ := n / 2
  let rev : Shao.Path n → Shao.Path n := fun a i => a (Fin.rev i)
  let Qrev : Shao.Path n → ℕ → ℝ := fun a k => Shao.prefixSquares (rev a) k
  let NH : Shao.Path n → ℕ := fun a =>
    @dite ℕ (∃ k : ℕ, k ≤ L ∧ H ≤ Qrev a k) (Classical.propDecidable _)
      (fun he => @Nat.find (fun k : ℕ => k ≤ L ∧ H ≤ Qrev a k)
        (fun k => Classical.propDecidable _) he)
      (fun _ => L)
  let N : Shao.Path n → ℕ := fun a => max m (NH a)
  let r : Shao.Path n → ℕ := fun a => n - N a
  let U : Shao.Path n → ℝ := fun a => Shao.energy a - Shao.prefixSquares a (r a)
  let J : Shao.Path n → ℝ := fun a =>
    (Finset.Icc 0 (N a)).sup'
      (by exact ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩)
      (fun l => |Shao.prefixSum a (r a + l) - Shao.prefixSum a (r a)|)
  let exceptional : Set (Shao.Path n) := {a | Qrev a L < H}
  rcases actual_backward_terminal_raw_data nu n hn4 h2 hmean hsecond hR H hH m hm hmH with
    ⟨_, _, _, hmNH, hmN, hmU, hmJ, _, hstat, hiNH, hiN, hiU, hiJ,
      hENH, hEN, hE, hEU, hEJ⟩
  change Measurable N at hmN
  change Measurable U at hmU
  change Measurable J at hmJ
  change ∀ a, 1 ≤ NH a ∧ NH a ≤ N a ∧ N a ≤ L ∧
    U a = Qrev a (N a) ∧
    (a ∉ exceptional → tau a = if NH a ≤ m then r a else r a + 1) at hstat
  change Integrable U P at hiU
  change Integrable (fun a => J a ^ 2) P at hiJ
  change (∫ a, (N a : ℝ) ∂P) ≤ 7 * H / sigmaSq at hEN
  change P.real exceptional ≤ 12 * H / V at hE
  change (∫ a, U a ∂P) = sigmaSq * (∫ a, (N a : ℝ) ∂P) at hEU
  change (∫ a, J a ^ 2 ∂P) ≤ 16 * sigmaSq * (∫ a, (N a : ℝ) ∂P) at hEJ
  have hrn : ∀ a, r a ≤ n := fun a => Nat.sub_le n (N a)
  have hmr : Measurable r :=
    (measurable_of_countable (fun k : ℕ => n - k)).comp hmN
  let Dr : Shao.Path n → ℝ := fun a =>
    (Finset.Icc (r a) n).sup'
      (by exact ⟨n, Finset.mem_Icc.mpr ⟨hrn a, le_rfl⟩⟩)
      (fun j => |sourceValue I F a x j (Equiv.refl (Fin n)) - terminal a|)
  have hDr := te_random_discrepancy_data n I (bridgeLaw B PB) x r hmr hrn
  have hiDr : Integrable Dr P := by
    apply Integrable.of_bound hDr.1.aestronglyMeasurable 1
    exact ae_of_all _ fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hDr.2 a).1]
      exact (hDr.2 a).2
  let W : Shao.Path n → ℝ := fun a => J a ^ 2 + U a + H
  have hiW : Integrable W P := (hiJ.add hiU).add (integrable_const H)
  have hWm : Measurable W := ((hmJ.pow_const 2).add hmU).add_const H
  have hW0 (a : Shao.Path n) : 0 ≤ W a := by
    have hu : 0 ≤ U a :=
      (remaining_population_geometry a (r a) (hrn a) (Equiv.refl (Fin n))).1
    dsimp [W]
    positivity
  let g : Shao.Path n → ℝ := fun a => 2 * C * W a / V
  let c : Shao.Path n → ℝ := fun a => min (g a) 1
  have hgm : Measurable g := (hWm.const_mul (2 * C)).div_const V
  have hcm : Measurable c := hgm.min measurable_const
  have hig : Integrable g P := (hiW.const_mul (2 * C)).div_const V
  have hic : Integrable c P := by
    apply Integrable.of_bound hcm.aestronglyMeasurable 1
    exact ae_of_all _ fun a => by
      have hga : 0 ≤ g a := div_nonneg (mul_nonneg (by positivity) (hW0 a)) hV.le
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min hga (by norm_num))]
      exact min_le_right _ _
  have hiDiff : Integrable (fun a => Dr a - c a) P := hiDr.sub hic
  have hslice (t : ℕ) : Integrable
      (fun a => if N a = t then Dr a - c a else 0) P := by
    have hS : MeasurableSet {a : Shao.Path n | N a = t} :=
      (measurableSet_singleton t).preimage hmN
    convert hiDiff.indicator hS using 1
    funext a
    by_cases hat : N a = t
    · rw [if_pos hat, Set.indicator_of_mem hat]
    · rw [if_neg hat, Set.indicator_of_notMem hat]
  have hpiece (t : ℕ) (ht : t ≤ L) :
      (∫ a, (if N a = t then Dr a - c a else 0) ∂P) ≤ 0 := by
    have hs := hsections PB B hB nu n t hn ht h2 hmean hsecond H hH x hx hx1 I
    dsimp only at hs
    let rt : ℕ := n - t
    let merge : Shao.Path rt × Shao.Path t → Shao.Path n := fun p i =>
      Fin.append p.1 p.2 (finCongr (by dsimp [rt]; omega : n = rt + t) i)
    let prefixPart : Shao.Path n → Shao.Path rt := fun a i =>
      a ⟨i.val, lt_of_lt_of_le i.is_lt (Nat.sub_le n t)⟩
    let suffixPart : Shao.Path n → Shao.Path t := fun a i =>
      a ⟨rt + i.val, by have hi := i.is_lt; dsimp [rt]; dsimp [L] at ht; omega⟩
    let Dt : Shao.Path n → ℝ := fun a =>
      (Finset.Icc rt n).sup'
        (by exact ⟨n, Finset.mem_Icc.mpr ⟨Nat.sub_le n t, le_rfl⟩⟩)
        (fun j => |sourceValue I F a x j (Equiv.refl (Fin n)) - terminal a|)
    let Jt : Shao.Path t → ℝ := fun b =>
      (Finset.Icc 0 t).sup'
        (by exact ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩)
        (fun l => |Shao.prefixSum b l|)
    let cost : Shao.Path t → ℝ := fun b =>
      2 * C * (Jt b ^ 2 + Shao.energy b + H) / V
    let Phi : Shao.Path rt × Shao.Path t → ℝ := fun p =>
      Dt (merge p) - min (cost p.2) 1
    change Measurable Phi ∧ (∀ p, |Phi p| ≤ 1) ∧
      (∀ b, (∫ v : Shao.Path rt, Phi (v, b) ∂Measure.pi (fun _ : Fin rt => nu)) ≤ 0) ∧
      ∀ a, Phi (prefixPart a, suffixPart a) =
        Dt a - min (2 * C *
          (((Finset.Icc 0 t).sup'
            (by exact ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩)
            (fun l => |Shao.prefixSum a (rt + l) - Shao.prefixSum a rt|)) ^ 2 +
            remainingEnergy a rt (Equiv.refl (Fin n)) + H) / V) 1 at hs
    have heq (a : Shao.Path n) (hat : N a = t) :
        Phi (prefixPart a, suffixPart a) = Dr a - c a := by
      rw [hs.2.2.2 a]
      dsimp only [Dr, c, g, W, r, U, J]
      simp only [hat]
      rfl
    have hf := actual_backward_stopped_suffix_integral nu n hn4 H hHp m hm t ht
      Phi hs.1 hs.2.1
    rcases hf with ⟨_, his, hio, he⟩
    have heqf :
        (fun a : Shao.Path n => if N a = t then Dr a - c a else 0) =
          (fun a => if N a = t then Phi (prefixPart a, suffixPart a) else 0) := by
      funext a
      by_cases hat : N a = t
      · simp only [hat, ite_true, heq a hat]
      · simp only [hat, ite_false]
    rw [heqf, he]
    apply integral_nonpos
    intro b
    dsimp only [Pi.zero_apply]
    split_ifs <;> first | exact hs.2.2.1 b | norm_num
  have hpartition (a : Shao.Path n) :
      (∑ t ∈ Finset.range (L + 1), if N a = t then Dr a - c a else 0) = Dr a - c a := by
    rw [Finset.sum_eq_single (N a)]
    · simp
    · intro t _ ht
      exact if_neg (Ne.symm ht)
    · intro hh
      have hnL := (hstat a).2.2.1
      exact False.elim (hh (Finset.mem_range.mpr (by omega)))
  have hDiff : (∫ a, Dr a - c a ∂P) ≤ 0 := by
    calc
      _ = ∫ a, ∑ t ∈ Finset.range (L + 1),
          (if N a = t then Dr a - c a else 0) ∂P := by
        apply integral_congr_ae
        exact ae_of_all _ fun a => (hpartition a).symm
      _ = ∑ t ∈ Finset.range (L + 1),
          ∫ a, (if N a = t then Dr a - c a else 0) ∂P :=
        integral_finsetSum _ (fun t _ => hslice t)
      _ ≤ 0 := Finset.sum_nonpos fun t ht =>
        hpiece t (by have hh := Finset.mem_range.mp ht; omega)
  have hDrg : (∫ a, Dr a ∂P) ≤ ∫ a, g a ∂P := by
    have hDrc : (∫ a, Dr a ∂P) ≤ ∫ a, c a ∂P := by
      rw [integral_sub hiDr hic] at hDiff
      linarith only [hDiff]
    exact hDrc.trans (integral_mono_ae hic hig (ae_of_all _ fun a => min_le_left _ _))
  have hEW : (∫ a, W a ∂P) ≤ 120 * H := by
    have he : (∫ a, W a ∂P) = (∫ a, J a ^ 2 ∂P) + (∫ a, U a ∂P) + H := by
      calc
        _ = (∫ a, J a ^ 2 + U a ∂P) + (∫ _ : Shao.Path n, H ∂P) :=
          integral_add (hiJ.add hiU) (integrable_const H)
        _ = _ := by rw [integral_add hiJ hiU]; simp
    rw [he, hEU]
    have hENp := (le_div_iff₀ hsecond).mp hEN
    nlinarith only [hEJ, hENp]
  have hDrpay : (∫ a, Dr a ∂P) ≤ 240 * C * H / V := by
    apply hDrg.trans
    calc
      (∫ a, g a ∂P) = 2 * C * (∫ a, W a ∂P) / V := by
        calc
          _ = (∫ a, 2 * C * W a ∂P) / V := integral_div V (fun a => 2 * C * W a)
          _ = _ := congrArg (fun q : ℝ => q / V) (integral_const_mul (μ := P) (2 * C) W)
      _ ≤ 2 * C * (120 * H) / V := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hEW (by positivity)) hV.le
      _ = _ := by ring
  have hEm : MeasurableSet exceptional := by
    apply measurableSet_lt _ measurable_const
    exact (Shao.measurable_prefixSquares L).comp
      (Measurable.of_eval (fun i : Fin n => measurable_pi_apply (Fin.rev i)))
  have hiE : Integrable (exceptional.indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const 1).indicator hEm
  have hdom (a : Shao.Path n) :
      discrepancy a ≤ exceptional.indicator (fun _ => (1 : ℝ)) a + Dr a := by
    by_cases he : a ∈ exceptional
    · rw [Set.indicator_of_mem he]
      exact (hd.2 a).2.trans (by linarith [(hDr.2 a).1])
    · rw [Set.indicator_of_notMem he, zero_add]
      have hrt : r a ≤ tau a := by
        have hh := (hstat a).2.2.2.2 he
        change tau a = if NH a ≤ m then r a else r a + 1 at hh
        rw [hh]
        split_ifs <;> omega
      apply Finset.sup'_le
      intro j hj
      exact Finset.le_sup'
        (fun j => |sourceValue I F a x j (Equiv.refl (Fin n)) - terminal a|)
        (Finset.mem_Icc.mpr ⟨hrt.trans (Finset.mem_Icc.mp hj).1,
          (Finset.mem_Icc.mp hj).2⟩)
  have hterminal : (∫ a, discrepancy a ∂P) ≤
      12 * H / V + 240 * C * H / V := by
    calc
      _ ≤ ∫ a, exceptional.indicator (fun _ => (1 : ℝ)) a + Dr a ∂P :=
        integral_mono_ae hiD (hiE.add hiDr) (ae_of_all _ hdom)
      _ = P.real exceptional + (∫ a, Dr a ∂P) := by
        rw [integral_add hiE hiDr, integral_indicator_const 1 hEm]
        simp only [smul_eq_mul, mul_one]
      _ ≤ _ := add_le_add hE hDrpay
  apply hterminal.trans
  change 12 * H / V + 240 * C * H / V ≤ (240 * C + 18) * H / V
  calc
    _ = (240 * C + 12) * H / V := by ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) hHp.le) hV.le
theorem actual_terminal_at_energy_cutoff :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω]
        (PB : Measure Ω) [IsProbabilityMeasure PB]
        (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B PB →
        ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ), 0 < n →
          Integrable (fun z : ℝ => z ^ 2) nu → (∫ z : ℝ, z ∂nu) = 0 →
          0 < (∫ z : ℝ, z ^ 2 ∂nu) →
          let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂nu
          let R : ℝ := Shao.truncationBudget
            (Measure.map (fun z : ℝ => z / Real.sqrt ((n : ℝ) * sigmaSq)) nu) n 0
          let h : ℝ := 4 * (n : ℝ) * sigmaSq * R ^ 2
          ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∀ I : MonitoredDomain,
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
            let F : BridgeKernel := eventCompletionKernel I (bridgeLaw B PB)
            let kappa : Shao.Path n → ℕ := fun a => energyCutoff a h (Equiv.refl (Fin n))
            let terminal : Shao.Path n → ℝ := fun a =>
              if sourceAlive I a x n (Equiv.refl (Fin n)) then 1 else 0
            let discrepancy : Shao.Path n → ℝ := fun a =>
              |sourceValue I F a x (kappa a) (Equiv.refl (Fin n)) - terminal a|
            Integrable discrepancy P ∧ (∫ a, discrepancy a ∂P) ≤ C * R ^ 2 := by
  classical
  obtain ⟨C, hC, hbound⟩ := actual_stopped_terminal_envelope_budget
  refine ⟨4 * C, by positivity, ?_⟩
  intro Ω _ PB _ B hB nu hnu n hn h2 hmean hsecond sigmaSq R h x hx hx1
    I P F kappa terminal discrepancy
  letI : IsProbabilityMeasure nu := hnu
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  letI : IsProbabilityMeasure (bridgeLaw B PB) := isProbabilityMeasure_bridgeLaw B PB hB
  have hg := raw_truncation_budget_suffix_geometry nu n hn h2 hsecond
  have hhp : 0 < h := hg.2.2.2.1
  have hk : ∀ a : Shao.Path n, kappa a ≤ n :=
    fun a => (energy_cutoff_data a h hhp).1.1 (Equiv.refl (Fin n))
  have hkm : Measurable kappa := te_actual_cutoff_measurable n h hhp
  have htm : Measurable terminal :=
    Measurable.ite (te_actual_alive_measurable n I x n) measurable_const measurable_const
  let f : Shao.Path n × ℕ → ℝ := fun p =>
    if hj : p.2 ≤ n then
      |sourceValue I F p.1 x p.2 (Equiv.refl (Fin n)) - terminal p.1|
    else 0
  have hfm : Measurable f := by
    apply measurable_from_prod_countable_left
    intro j
    by_cases hj : j ≤ n
    · simpa only [f, hj, dite_true, F, Function.comp_def, Pi.sub_apply] using
        continuous_abs.measurable.comp
          ((te_actual_source_measurable n I (bridgeLaw B PB) x j hj).sub htm)
    · simp only [f, hj, dite_false]
      exact measurable_const
  have hDm : Measurable discrepancy := by
    convert hfm.comp (measurable_id.prodMk hkm) using 1
    funext a
    simp only [Function.comp_def, f, hk a, dite_true]
    rfl
  have hD1 (a : Shao.Path n) : discrepancy a ≤ 1 := by
    have hb := te_actual_source_bounds I (bridgeLaw B PB) a x (kappa a) (Equiv.refl (Fin n))
    change |sourceValue I F a x (kappa a) (Equiv.refl (Fin n)) - terminal a| ≤ 1
    rw [abs_sub_le_iff]
    dsimp only [terminal]
    split_ifs <;> constructor <;> linarith only [hb.1, hb.2]
  have hiD : Integrable discrepancy P := by
    apply Integrable.of_bound hDm.aestronglyMeasurable 1
    exact ae_of_all _ fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
      exact hD1 a
  refine ⟨hiD, ?_⟩
  have hmH : (0 : ℝ) ≤ 3 * h / sigmaSq := by positivity
  have hs := hbound PB B hB nu n hn h2 hmean hsecond h le_rfl 0
    (Nat.zero_le _) (by simpa only [Nat.cast_zero] using hmH) x hx hx1 I
  let tau : Shao.Path n → ℕ := fun a => min (kappa a) n
  let D : Shao.Path n → ℝ := fun a =>
    (Finset.Icc (tau a) n).sup'
      (by exact ⟨n, Finset.mem_Icc.mpr ⟨Nat.min_le_right _ _, le_rfl⟩⟩)
      (fun j => |sourceValue I F a x j (Equiv.refl (Fin n)) - terminal a|)
  change Integrable D P ∧
    (∫ a, D a ∂P) ≤ C * h / ((n : ℝ) * sigmaSq) at hs
  have hle (a : Shao.Path n) : discrepancy a ≤ D a :=
    Finset.le_sup'
      (fun j => |sourceValue I F a x j (Equiv.refl (Fin n)) - terminal a|)
      (Finset.mem_Icc.mpr ⟨Nat.min_le_left _ _, hk a⟩)
  calc
    _ ≤ ∫ a, D a ∂P := integral_mono_ae hiD hs.1 (ae_of_all _ hle)
    _ ≤ C * h / ((n : ℝ) * sigmaSq) := hs.2
    _ = _ := by
      have hV : (n : ℝ) * sigmaSq ≠ 0 :=
        ne_of_gt (mul_pos (by exact_mod_cast hn) hsecond)
      dsimp only [h]
      have hs0 : sigmaSq ≠ 0 := ne_of_gt hsecond
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
      field_simp [hs0, hn0]
      <;> ring
end Shao.Probability
