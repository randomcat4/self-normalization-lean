import Shao.OQ6.WeightedAECDFBounds
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Shao.OQ6.CompactTailBounds

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology

universe u v

theorem ambient_weighted_ae_compact_tail_bounds
    (C : ℝ)
    (hSZ : Shao.OQ6.NormalizedIntegrableCDFAssembly.ScalarShaoZhouFiniteCostCDFInput.{v} C)
    {Ω0 : Type u} [MeasurableSpace Ω0]
    (P : Measure Ω0) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n) {X : Fin n → Type v}
    [mX : ∀ i : Fin n, MeasurableSpace (X i)]
    [∀ i : Fin n, MeasurableSpace.CountablyGenerated (X i)]
    (O : ∀ i : Fin n, Ω0 → X i)
    (hO : ∀ i : Fin n, Measurable (O i))
    (hOindep : iIndepFun O P)
    (g : ∀ i : Fin n, X i → ℝ)
    (hg : ∀ i : Fin n, Measurable (g i))
    (hg2 : ∀ i : Fin n, MemLp (fun ω : Ω0 => g i (O i ω)) 2 P)
    (hgmean : ∀ i : Fin n, (∫ ω, g i (O i ω) ∂P) = 0)
    (hgenergy : (∑ i : Fin n, ∫ ω, (g i (O i ω)) ^ 2 ∂P) = 1)
    (D1 D2 Aenv Benv : (∀ i : Fin n, X i) → ℝ)
    (Adeleted Bdeleted : ∀ i : Fin n, (∀ j : {j : Fin n // j ≠ i}, X j.1) → ℝ)
    (hD1 : Measurable D1) (hD2 : Measurable D2)
    (hAenv : Measurable Aenv) (hBenv : Measurable Benv)
    (hAdeleted : ∀ i : Fin n, Measurable (Adeleted i))
    (hBdeleted : ∀ i : Fin n, Measurable (Bdeleted i))
    (hAnonneg : ∀ᵐ ω ∂P, 0 ≤ Aenv (fun i => O i ω))
    (hBnonneg : ∀ᵐ ω ∂P, 0 ≤ Benv (fun i => O i ω))
    (hAdeletenonneg : ∀ i : Fin n, ∀ᵐ ω ∂P,
      0 ≤ Adeleted i (fun j => O j.1 ω))
    (hBdeletenonneg : ∀ i : Fin n, ∀ᵐ ω ∂P,
      0 ≤ Bdeleted i (fun j => O j.1 ω))
    (hD1A : ∀ᵐ ω ∂P, |D1 (fun i => O i ω)| ≤ Aenv (fun i => O i ω))
    (hD2B : ∀ᵐ ω ∂P, |D2 (fun i => O i ω)| ≤ Benv (fun i => O i ω))
    (hD2pos : ∀ᵐ ω ∂P, 0 < 1 + D2 (fun i => O i ω))
    (κ : Ω0 → ℝ) (hκ : Measurable κ)
    (x : ℝ) (hz : 0 ≤ x)
    (hFull : Integrable (fun ω : Ω0 =>
      Aenv (fun i => O i ω) + x * Benv (fun i => O i ω)) P)
    (hDeleted : ∀ i : Fin n, Integrable (fun ω : Ω0 =>
      min |g i (O i ω)| (1 + x)⁻¹ *
        (|Aenv (fun j => O j ω) - Adeleted i (fun j => O j.1 ω)| +
          x * |Benv (fun j => O j ω) - Bdeleted i (fun j => O j.1 ω)|)) P) :
    let Q : Ω0 → (∀ i : Fin n, X i) := fun ω i => O i ω
    let ξ0 : Fin n → Ω0 → ℝ := fun i ω => g i (O i ω)
    let W0 : Ω0 → ℝ := fun ω => ∑ i : Fin n, ξ0 i ω
    let V0 : Ω0 → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ0 i ω) ^ 2)
    let b0 : Ω0 → ℝ := fun ω => Real.sqrt (1 + D2 (Q ω))
    let T0 : Ω0 → ℝ := fun ω => if V0 ω = 0 then κ ω else (W0 ω + D1 (Q ω)) / (V0 ω * b0 ω)
    let F0 : Set Ω0 := {ω : Ω0 | W0 ω + D1 (Q ω) ≤ x * V0 ω * b0 ω}
    let Z0 : Set Ω0 := {ω : Ω0 | V0 ω = 0}
    let p0 : ℝ := P.real Z0
    let δ0 : Fin n → ℝ := fun i =>
      ∫ ω, ((1 + x) * ξ0 i ω) ^ 2 * min |(1 + x) * ξ0 i ω| 1 ∂P
    let L0 : ℝ := ∑ i : Fin n, δ0 i
    let compactDeleted0 : Fin n → Ω0 → ℝ := fun i ω =>
      min |ξ0 i ω| (1 + x)⁻¹ *
        (|Aenv (Q ω) - Adeleted i (fun j => O j.1 ω)| +
          x * |Benv (Q ω) - Bdeleted i (fun j => O j.1 ω)|)
    let compactCost0 : ℝ := L0 + (∫ ω, Aenv (Q ω) + x * Benv (Q ω) ∂P) +
      ∑ i : Fin n, ∫ ω, compactDeleted0 i ω ∂P
    |P.real {ω : Ω0 | x * V0 ω * b0 ω < W0 ω + D1 (Q ω)} -
      (1 - Shao.OQ4.standardNormalCDF x)| ≤ C * compactCost0 ∧
    |P.real {ω : Ω0 | x * V0 ω * b0 ω ≤ W0 ω + D1 (Q ω)} -
      (1 - Shao.OQ4.standardNormalCDF x)| ≤ C * compactCost0 ∧
    |P.real {ω : Ω0 | x < T0 ω} - (1 - Shao.OQ4.standardNormalCDF x)| ≤
      C * compactCost0 + p0 ∧
    |P.real {ω : Ω0 | x ≤ T0 ω} - (1 - Shao.OQ4.standardNormalCDF x)| ≤
      C * compactCost0 + p0 := by
  classical
  let Q : Ω0 → (∀ i : Fin n, X i) := fun ω i => O i ω
  let ξ0 : Fin n → Ω0 → ℝ := fun i ω => g i (O i ω)
  let W0 : Ω0 → ℝ := fun ω => ∑ i : Fin n, ξ0 i ω
  let V0 : Ω0 → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ0 i ω) ^ 2)
  let b0 : Ω0 → ℝ := fun ω => Real.sqrt (1 + D2 (Q ω))
  let T0 : Ω0 → ℝ := fun ω => if V0 ω = 0 then κ ω else (W0 ω + D1 (Q ω)) / (V0 ω * b0 ω)
  let F0 : Set Ω0 := {ω : Ω0 | W0 ω + D1 (Q ω) ≤ x * V0 ω * b0 ω}
  let Z0 : Set Ω0 := {ω : Ω0 | V0 ω = 0}
  let p0 : ℝ := P.real Z0
  let δ0 : Fin n → ℝ := fun i =>
      ∫ ω, ((1 + x) * ξ0 i ω) ^ 2 * min |(1 + x) * ξ0 i ω| 1 ∂P
  let L0 : ℝ := ∑ i : Fin n, δ0 i
  let compactDeleted0 : Fin n → Ω0 → ℝ := fun i ω =>
      min |ξ0 i ω| (1 + x)⁻¹ *
        (|Aenv (Q ω) - Adeleted i (fun j => O j.1 ω)| +
          x * |Benv (Q ω) - Bdeleted i (fun j => O j.1 ω)|)
  let compactCost0 : ℝ := L0 + (∫ ω, Aenv (Q ω) + x * Benv (Q ω) ∂P) +
      ∑ i : Fin n, ∫ ω, compactDeleted0 i ω ∂P
  change
    |P.real {ω : Ω0 | x * V0 ω * b0 ω < W0 ω + D1 (Q ω)} -
      (1 - Shao.OQ4.standardNormalCDF x)| ≤ C * compactCost0 ∧
    |P.real {ω : Ω0 | x * V0 ω * b0 ω ≤ W0 ω + D1 (Q ω)} -
      (1 - Shao.OQ4.standardNormalCDF x)| ≤ C * compactCost0 ∧
    |P.real {ω : Ω0 | x < T0 ω} - (1 - Shao.OQ4.standardNormalCDF x)| ≤
      C * compactCost0 + p0 ∧
    |P.real {ω : Ω0 | x ≤ T0 ω} - (1 - Shao.OQ4.standardNormalCDF x)| ≤
      C * compactCost0 + p0
  have hQ : Measurable Q := Measurable.of_eval hO
  have hξ (i : Fin n) : Measurable (ξ0 i) := (hg i).comp (hO i)
  have hW : Measurable W0 :=
    Finset.measurable_sum Finset.univ (fun i _ => hξ i)
  have hV : Measurable V0 := by
    apply Measurable.sqrt
    exact Finset.measurable_sum Finset.univ (fun i _ =>
      (hξ i).pow (measurable_const : Measurable (fun _ : Ω0 => (2 : ℕ))))
  have hb : Measurable b0 := (measurable_const.add (hD2.comp hQ)).sqrt
  have hN : Measurable (fun ω : Ω0 => W0 ω + D1 (Q ω)) :=
    hW.add (hD1.comp hQ)
  have hxd : Measurable (fun ω : Ω0 => x * V0 ω * b0 ω) :=
    (measurable_const.mul hV).mul hb
  have hZ : MeasurableSet Z0 := measurableSet_eq_fun hV measurable_const
  have hT : Measurable T0 :=
    Measurable.ite hZ hκ (hN.div (hV.mul hb))
  have hF0 : MeasurableSet F0 := measurableSet_le hN hxd
  have hTc : MeasurableSet {ω : Ω0 | T0 ω ≤ x} :=
    measurableSet_le hT measurable_const
  have hFl : MeasurableSet {ω : Ω0 | W0 ω + D1 (Q ω) < x * V0 ω * b0 ω} :=
    measurableSet_lt hN hxd
  have hTl : MeasurableSet {ω : Ω0 | T0 ω < x} :=
    measurableSet_lt hT measurable_const
  have hClosed :
      |P.real F0 - Shao.OQ4.standardNormalCDF x| ≤ C * compactCost0 ∧
      |P.real {ω : Ω0 | T0 ω ≤ x} - Shao.OQ4.standardNormalCDF x| ≤
        C * compactCost0 + p0 := by
    exact Shao.OQ6.WeightedAECDFBounds.ambient_weighted_ae_cdf_bounds
      C hSZ P n hn O hO hOindep g hg hg2 hgmean hgenergy
      D1 D2 Aenv Benv Adeleted Bdeleted hD1 hD2 hAenv hBenv hAdeleted hBdeleted
      hAnonneg hBnonneg hAdeletenonneg hBdeletenonneg hD1A hD2B hD2pos
      κ hκ x hz hFull hDeleted
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  let D1Seq : ℕ → (∀ i : Fin n, X i) → ℝ := fun k o => D1 o + ε k
  let AenvSeq : ℕ → (∀ i : Fin n, X i) → ℝ := fun k o => Aenv o + ε k
  let AdeletedSeq : ℕ → ∀ i : Fin n, (∀ j : {j : Fin n // j ≠ i}, X j.1) → ℝ := fun k i t => Adeleted i t + ε k
  let κSeq : ℕ → Ω0 → ℝ := fun k ω => κ ω + ε k
  let fullSeq : ℕ → Ω0 → ℝ := fun k ω => AenvSeq k (Q ω) + x * Benv (Q ω)
  let deletedSeq : ℕ → Fin n → Ω0 → ℝ := fun k i ω => min |ξ0 i ω| (1 + x)⁻¹ * (|AenvSeq k (Q ω) - AdeletedSeq k i (fun j => O j.1 ω)| + x * |Benv (Q ω) - Bdeleted i (fun j => O j.1 ω)|)
  let compactCostSeq : ℕ → ℝ := fun k => L0 + (∫ ω, fullSeq k ω ∂P) + ∑ i : Fin n, ∫ ω, deletedSeq k i ω ∂P
  let FSeq : ℕ → Set Ω0 := fun k => {ω : Ω0 | W0 ω + D1Seq k (Q ω) ≤ x * V0 ω * b0 ω}
  let TSeq : ℕ → Ω0 → ℝ := fun k ω => if V0 ω = 0 then κSeq k ω else (W0 ω + D1Seq k (Q ω)) / (V0 ω * b0 ω)
  let HSeq : ℕ → Set Ω0 := fun k => {ω : Ω0 | TSeq k ω ≤ x}
  have hεpos (k : ℕ) : 0 < ε k := by
    dsimp only [ε]
    positivity
  have hεanti : Antitone ε := by
    intro i j hij
    change 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1)
    exact one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (i : ℝ) + 1)
      (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hden : Filter.Tendsto (fun k : ℕ => (k : ℝ) + 1)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun k : ℕ => by linarith) tendsto_natCast_atTop_atTop
  have hεlim : Filter.Tendsto ε Filter.atTop (nhds (0 : ℝ)) := by
    change Filter.Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1))
      Filter.atTop (nhds (0 : ℝ))
    exact tendsto_const_nhds.div_atTop hden
  have hεcut (a b : ℝ) : (∃ k : ℕ, a + ε k ≤ b) ↔ a < b := by
    constructor
    · rintro ⟨k, hk⟩
      linarith [hεpos k]
    · intro hab
      have he : ∀ᶠ k : ℕ in Filter.atTop, ε k < b - a :=
        hεlim.eventually (eventually_lt_nhds (sub_pos.mpr hab))
      obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 he
      refine ⟨k, ?_⟩
      have hh := hk k le_rfl
      linarith
  have hD1Seq (k : ℕ) : Measurable (D1Seq k) := hD1.add measurable_const
  have hASeq (k : ℕ) : Measurable (AenvSeq k) := hAenv.add measurable_const
  have hAdSeq (k : ℕ) (i : Fin n) : Measurable (AdeletedSeq k i) :=
    (hAdeleted i).add measurable_const
  have hκSeq (k : ℕ) : Measurable (κSeq k) := hκ.add measurable_const
  have hASeq0 (k : ℕ) : ∀ᵐ ω ∂P, 0 ≤ AenvSeq k (Q ω) := by
    filter_upwards [hAnonneg] with ω hω
    exact add_nonneg hω (hεpos k).le
  have hAdSeq0 (k : ℕ) (i : Fin n) :
      ∀ᵐ ω ∂P, 0 ≤ AdeletedSeq k i (fun j => O j.1 ω) := by
    filter_upwards [hAdeletenonneg i] with ω hω
    exact add_nonneg hω (hεpos k).le
  have hD1SeqA (k : ℕ) :
      ∀ᵐ ω ∂P, |D1Seq k (Q ω)| ≤ AenvSeq k (Q ω) := by
    filter_upwards [hD1A] with ω hω
    change |D1 (Q ω) + ε k| ≤ Aenv (Q ω) + ε k
    calc
      |D1 (Q ω) + ε k| ≤ |D1 (Q ω)| + |ε k| := abs_add_le _ _
      _ ≤ Aenv (Q ω) + ε k := by
        rw [abs_of_pos (hεpos k)]
        exact add_le_add hω le_rfl
  have hFullSeqEq (k : ℕ) : fullSeq k =
      (fun ω : Ω0 => (Aenv (Q ω) + x * Benv (Q ω)) + ε k) := by
    funext ω
    dsimp only [fullSeq, AenvSeq]
    ring
  have hFullSeqI (k : ℕ) : Integrable (fullSeq k) P := by
    rw [hFullSeqEq k]
    exact hFull.add (integrable_const (ε k))
  have hFullSeqIntegral (k : ℕ) :
      (∫ ω, fullSeq k ω ∂P) = (∫ ω, Aenv (Q ω) + x * Benv (Q ω) ∂P) + ε k := by
    rw [hFullSeqEq k, integral_add hFull (integrable_const (ε k))]
    simp only [integral_const, probReal_univ, one_smul, Q]
  have hADiff (k : ℕ) (i : Fin n) (ω : Ω0) :
      AenvSeq k (Q ω) - AdeletedSeq k i (fun j => O j.1 ω) =
        Aenv (Q ω) - Adeleted i (fun j => O j.1 ω) := by
    dsimp only [AenvSeq, AdeletedSeq]
    ring
  have hDeletedSeqEq (k : ℕ) (i : Fin n) : deletedSeq k i = compactDeleted0 i := by
    funext ω
    dsimp only [deletedSeq, compactDeleted0]
    rw [hADiff k i ω]
  have hDeletedSeqI (k : ℕ) (i : Fin n) : Integrable (deletedSeq k i) P := by
    rw [hDeletedSeqEq k i]
    exact hDeleted i
  have hCostSeq (k : ℕ) : compactCostSeq k = compactCost0 + ε k := by
    dsimp only [compactCostSeq, compactCost0]
    rw [hFullSeqIntegral k]
    have hs : (∑ i : Fin n, ∫ ω, deletedSeq k i ω ∂P) =
        ∑ i : Fin n, ∫ ω, compactDeleted0 i ω ∂P := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hDeletedSeqEq k i]
    rw [hs]
    ring
  have hFixed (k : ℕ) :
      |P.real (FSeq k) - Shao.OQ4.standardNormalCDF x| ≤ C * compactCostSeq k ∧
      |P.real (HSeq k) - Shao.OQ4.standardNormalCDF x| ≤ C * compactCostSeq k + p0 := by
    exact Shao.OQ6.WeightedAECDFBounds.ambient_weighted_ae_cdf_bounds
      C hSZ P n hn O hO hOindep g hg hg2 hgmean hgenergy
      (D1Seq k) D2 (AenvSeq k) Benv (AdeletedSeq k) Bdeleted
      (hD1Seq k) hD2 (hASeq k) hBenv (hAdSeq k) hBdeleted
      (hASeq0 k) hBnonneg (hAdSeq0 k) hBdeletenonneg (hD1SeqA k) hD2B hD2pos
      (κSeq k) (hκSeq k) x hz (hFullSeqI k) (hDeletedSeqI k)
  have hFSeqMeas (k : ℕ) : MeasurableSet (FSeq k) :=
    measurableSet_le (hW.add ((hD1Seq k).comp hQ)) hxd
  have hTSeqMeas (k : ℕ) : Measurable (TSeq k) :=
    Measurable.ite hZ (hκSeq k)
      ((hW.add ((hD1Seq k).comp hQ)).div (hV.mul hb))
  have hHSeqMeas (k : ℕ) : MeasurableSet (HSeq k) :=
    measurableSet_le (hTSeqMeas k) measurable_const
  have hFmono : Monotone FSeq := by
    intro i j hij ω hω
    change W0 ω + (D1 (Q ω) + ε i) ≤ x * V0 ω * b0 ω at hω
    change W0 ω + (D1 (Q ω) + ε j) ≤ x * V0 ω * b0 ω
    linarith [hεanti hij]
  have hHmono : Monotone HSeq := by
    intro i j hij ω hω
    change TSeq j ω ≤ x
    have ht : TSeq j ω ≤ TSeq i ω := by
      by_cases hV0 : V0 ω = 0
      · simp only [TSeq, if_pos hV0, κSeq]
        exact add_le_add le_rfl (hεanti hij)
      · simp only [TSeq, if_neg hV0, D1Seq]
        apply div_le_div_of_nonneg_right _
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        linarith [hεanti hij]
    exact ht.trans hω
  have hFUnion : (⋃ k : ℕ, FSeq k) =
      {ω : Ω0 | W0 ω + D1 (Q ω) < x * V0 ω * b0 ω} := by
    ext ω
    simp only [FSeq, D1Seq, Set.mem_iUnion, Set.mem_setOf_eq]
    simpa only [add_assoc] using
      hεcut (W0 ω + D1 (Q ω)) (x * V0 ω * b0 ω)
  have hHUnion : (⋃ k : ℕ, HSeq k) =ᵐ[P] {ω : Ω0 | T0 ω < x} := by
    filter_upwards [hD2pos] with ω hω
    apply propext
    by_cases hV0 : V0 ω = 0
    · simpa only [HSeq, TSeq, T0, if_pos hV0, κSeq, Set.mem_iUnion,
        Set.mem_setOf_eq] using hεcut (κ ω) x
    · have hv : 0 < V0 ω := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hV0)
      have hbpos : 0 < b0 ω := Real.sqrt_pos.mpr hω
      have hdpos : 0 < V0 ω * b0 ω := mul_pos hv hbpos
      simp only [HSeq, TSeq, T0, if_neg hV0, D1Seq, Set.mem_iUnion,
        Set.mem_setOf_eq, div_le_iff₀ hdpos, div_lt_iff₀ hdpos]
      simpa only [add_assoc] using
        hεcut (W0 ω + D1 (Q ω)) (x * (V0 ω * b0 ω))
  have hRealUnion (E : ℕ → Set Ω0) (hEmono : Monotone E) :
      Filter.Tendsto (fun k : ℕ => P.real (E k)) Filter.atTop
        (nhds (P.real (⋃ k : ℕ, E k))) := by
    have hh := tendsto_measure_iUnion_atTop (μ := P) hEmono
    have ht := (ENNReal.continuousAt_toReal (measure_ne_top P (⋃ k : ℕ, E k))).tendsto.comp hh
    simpa only [Function.comp_def, ← measureReal_def] using ht
  have hFProbLim : Filter.Tendsto (fun k : ℕ => P.real (FSeq k)) Filter.atTop
      (nhds (P.real {ω : Ω0 | W0 ω + D1 (Q ω) < x * V0 ω * b0 ω})) := by
    have hh := hRealUnion FSeq hFmono
    rw [hFUnion] at hh
    exact hh
  have hHProbLim : Filter.Tendsto (fun k : ℕ => P.real (HSeq k)) Filter.atTop
      (nhds (P.real {ω : Ω0 | T0 ω < x})) := by
    have he : P.real (⋃ k : ℕ, HSeq k) = P.real {ω : Ω0 | T0 ω < x} :=
      measureReal_congr hHUnion
    simpa only [he] using hRealUnion HSeq hHmono
  have hCostLim : Filter.Tendsto compactCostSeq Filter.atTop (nhds compactCost0) := by
    have he : compactCostSeq = (fun k : ℕ => compactCost0 + ε k) := funext hCostSeq
    rw [he]
    simpa only [add_zero] using tendsto_const_nhds.add hεlim
  have hFAbsLim : Filter.Tendsto
      (fun k : ℕ => |P.real (FSeq k) - Shao.OQ4.standardNormalCDF x|) Filter.atTop
      (nhds |P.real {ω : Ω0 | W0 ω + D1 (Q ω) < x * V0 ω * b0 ω} -
        Shao.OQ4.standardNormalCDF x|) :=
    (continuous_abs : Continuous (fun t : ℝ => |t|)).continuousAt.tendsto.comp
      (hFProbLim.sub tendsto_const_nhds)
  have hHAbsLim : Filter.Tendsto
      (fun k : ℕ => |P.real (HSeq k) - Shao.OQ4.standardNormalCDF x|) Filter.atTop
      (nhds |P.real {ω : Ω0 | T0 ω < x} - Shao.OQ4.standardNormalCDF x|) :=
    (continuous_abs : Continuous (fun t : ℝ => |t|)).continuousAt.tendsto.comp
      (hHProbLim.sub tendsto_const_nhds)
  have hRHSLim : Filter.Tendsto (fun k : ℕ => C * compactCostSeq k) Filter.atTop
      (nhds (C * compactCost0)) := tendsto_const_nhds.mul hCostLim
  have hTRHSLim : Filter.Tendsto (fun k : ℕ => C * compactCostSeq k + p0) Filter.atTop
      (nhds (C * compactCost0 + p0)) := hRHSLim.add tendsto_const_nhds
  have hOpenF :
      |P.real {ω : Ω0 | W0 ω + D1 (Q ω) < x * V0 ω * b0 ω} -
        Shao.OQ4.standardNormalCDF x| ≤ C * compactCost0 :=
    le_of_tendsto_of_tendsto hFAbsLim hRHSLim
      (Filter.Eventually.of_forall fun k => (hFixed k).1)
  have hOpenT :
      |P.real {ω : Ω0 | T0 ω < x} - Shao.OQ4.standardNormalCDF x| ≤
        C * compactCost0 + p0 :=
    le_of_tendsto_of_tendsto hHAbsLim hTRHSLim
      (Filter.Eventually.of_forall fun k => (hFixed k).2)
  have hComplementError (E : Set Ω0) (hE : MeasurableSet E) (a : ℝ) :
      |P.real Eᶜ - (1 - a)| = |P.real E - a| := by
    have he : P.real Eᶜ = 1 - P.real E := by
      simpa only [probReal_univ] using measureReal_compl (μ := P) hE
    rw [he, show (1 - P.real E) - (1 - a) = -(P.real E - a) by ring, abs_neg]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have he : {ω : Ω0 | x * V0 ω * b0 ω < W0 ω + D1 (Q ω)} = F0ᶜ := by
      ext ω
      simp only [F0, Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    rw [he, hComplementError F0 hF0 (Shao.OQ4.standardNormalCDF x)]
    exact hClosed.1
  · have he : {ω : Ω0 | x * V0 ω * b0 ω ≤ W0 ω + D1 (Q ω)} =
        {ω : Ω0 | W0 ω + D1 (Q ω) < x * V0 ω * b0 ω}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
    rw [he, hComplementError _ hFl (Shao.OQ4.standardNormalCDF x)]
    exact hOpenF
  · have he : {ω : Ω0 | x < T0 ω} = {ω : Ω0 | T0 ω ≤ x}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    rw [he, hComplementError _ hTc (Shao.OQ4.standardNormalCDF x)]
    exact hClosed.2
  · have he : {ω : Ω0 | x ≤ T0 ω} = {ω : Ω0 | T0 ω < x}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
    rw [he, hComplementError _ hTl (Shao.OQ4.standardNormalCDF x)]
    exact hOpenT

end

end Shao.OQ6.CompactTailBounds
