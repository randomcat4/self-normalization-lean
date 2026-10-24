import Shao.OQ6.PhysicalCompact
import Shao.OQ6.ActualUncenteredCompactCDF
import Shao.Probability.TruncationIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace Shao.OQ6.ActualPhysicalCompactCDF

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

universe u

theorem normalized_observation_truncation_budget_le_rpow_moment
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (p : ℝ) (hp2 : 2 ≤ p) (hp3 : p ≤ 3)
    (hgp : Integrable (fun o => Real.rpow |g o| p) μ)
    (n : ℕ) (hn : 1 ≤ n) (y : ℝ) (hy : 0 ≤ y) :
    let N : ℝ := (n : ℝ)
    let q : ℝ := Real.sqrt N
    let β : ℝ := ∫ o, Real.rpow |g o| p ∂μ
    let L : ℝ := N * (∫ o, Shao.truncationF ((1 + y) * (g o / q)) ∂μ)
    Integrable (fun o => Shao.truncationF ((1 + y) * (g o / q))) μ ∧
      L ≤ β * Real.rpow (1 + y) p * N / Real.rpow q p ∧
      L ≤ β * Real.rpow (1 + y) p /
        Real.rpow N ((p - 2) / 2) := by
  classical
  let N : ℝ := (n : ℝ)
  let q : ℝ := Real.sqrt N
  let β : ℝ := ∫ o, Real.rpow |g o| p ∂μ
  let L : ℝ := N * (∫ o, Shao.truncationF ((1 + y) * (g o / q)) ∂μ)
  change Integrable (fun o => Shao.truncationF ((1 + y) * (g o / q))) μ ∧
    L ≤ β * Real.rpow (1 + y) p * N / Real.rpow q p ∧
    L ≤ β * Real.rpow (1 + y) p / Real.rpow N ((p - 2) / 2)
  let f : Ω → ℝ := fun o => g o / q
  let ν : Measure ℝ := μ.map f
  have hN1 : 1 ≤ N := by
    dsimp only [N]
    exact_mod_cast hn
  have hN : 0 < N := by linarith
  have hq : 0 < q := Real.sqrt_pos.mpr hN
  have hf : Measurable f := hg.div_const q
  have hf2 : Integrable (fun o => f o ^ 2) μ := by
    apply (hg2.integrable_sq.div_const (q ^ 2)).congr
    exact ae_of_all μ (fun o => by
      dsimp only [f]
      rw [div_pow])
  have hfpoint (o : Ω) :
      Real.rpow |f o| p = Real.rpow |g o| p / Real.rpow q p := by
    dsimp only [f]
    rw [abs_div, abs_of_pos hq]
    exact Real.div_rpow (abs_nonneg (g o)) hq.le p
  have hfp : Integrable (fun o => Real.rpow |f o| p) μ :=
    (hgp.div_const (Real.rpow q p)).congr
      (ae_of_all μ (fun o => (hfpoint o).symm))
  have hν2 : Integrable (fun z : ℝ => z ^ 2) ν := by
    change Integrable (fun z : ℝ => z ^ 2) (μ.map f)
    exact (integrable_map_measure (by fun_prop) hf.aemeasurable).2 hf2
  have hνp : Integrable (fun z : ℝ => Real.rpow |z| p) ν := by
    change Integrable (fun z : ℝ => Real.rpow |z| p) (μ.map f)
    exact (integrable_map_measure
      (by
        have hcont : Continuous (fun z : ℝ => Real.rpow |z| p) := by
          simpa only [Real.rpow_eq_pow, Function.comp_def] using
            (Real.continuous_rpow_const
              (show 0 ≤ p by linarith only [hp2])).comp continuous_abs
        exact hcont.aestronglyMeasurable)
      hf.aemeasurable).2 hfp
  have hνmoment :
      (∫ z : ℝ, Real.rpow |z| p ∂ν) = β / Real.rpow q p := by
    change (∫ z : ℝ, Real.rpow |z| p ∂(μ.map f)) = _
    rw [integral_map hf.aemeasurable hνp.aestronglyMeasurable]
    calc
      (∫ o, Real.rpow |f o| p ∂μ) =
          ∫ o, (Real.rpow q p)⁻¹ * Real.rpow |g o| p ∂μ := by
        apply integral_congr_ae
        exact ae_of_all μ (fun o => by
          change Real.rpow |f o| p = (Real.rpow q p)⁻¹ * Real.rpow |g o| p
          rw [hfpoint o]
          ring)
      _ = (Real.rpow q p)⁻¹ * β := integral_const_mul _ _
      _ = β / Real.rpow q p := by ring
  have hFν : Integrable (fun z : ℝ => Shao.truncationF ((1 + y) * z)) ν :=
    Shao.integrable_truncationF_mul ν hν2 (1 + y)
  have hF : Integrable (fun o => Shao.truncationF ((1 + y) * (g o / q))) μ := by
    change Integrable (fun o => Shao.truncationF ((1 + y) * f o)) μ
    exact (integrable_map_measure hFν.aestronglyMeasurable hf.aemeasurable).1 hFν
  have hbudget : Shao.truncationBudget ν n y = L := by
    unfold Shao.truncationBudget
    change (n : ℝ) * (∫ z : ℝ, Shao.truncationF ((1 + y) * z) ∂(μ.map f)) = _
    rw [integral_map hf.aemeasurable hFν.aestronglyMeasurable]
  have hbound : L ≤
      Real.rpow (1 + y) p * (N * (β / Real.rpow q p)) := by
    have h := Shao.truncationBudget_le_rpow_moment
      ν n hν2 y p hy hp2 hp3 hνp
    rw [hbudget, hνmoment] at h
    exact h
  have hfirst : L ≤ β * Real.rpow (1 + y) p * N / Real.rpow q p := by
    calc
      L ≤ Real.rpow (1 + y) p * (N * (β / Real.rpow q p)) := hbound
      _ = β * Real.rpow (1 + y) p * N / Real.rpow q p := by ring
  have hqpower : Real.rpow q p = Real.rpow N (p / 2) := by
    calc
      Real.rpow q p = Real.rpow (Real.rpow N (1 / (2 : ℝ))) p := by
        dsimp only [q]
        simp only [Real.rpow_eq_pow, Real.sqrt_eq_rpow]
      _ = Real.rpow N ((1 / (2 : ℝ)) * p) :=
        (Real.rpow_mul hN.le (1 / (2 : ℝ)) p).symm
      _ = Real.rpow N (p / 2) := by congr 1; ring
  have hden :
      Real.rpow N ((p - 2) / 2) = Real.rpow q p / N := by
    calc
      Real.rpow N ((p - 2) / 2) = Real.rpow N (p / 2 - 1) := by
        congr 1
        ring
      _ = Real.rpow N (p / 2) / Real.rpow N 1 :=
        Real.rpow_sub hN (p / 2) 1
      _ = Real.rpow q p / N := by
        rw [hqpower]
        simp only [Real.rpow_eq_pow, Real.rpow_one]
  have hnormalize :
      β * Real.rpow (1 + y) p * N / Real.rpow q p =
        β * Real.rpow (1 + y) p / Real.rpow N ((p - 2) / 2) := by
    rw [hden]
    field_simp [hN.ne', (Real.rpow_pos_of_pos hq p).ne'] <;> ring
  refine ⟨hF, hfirst, ?_⟩
  calc
    L ≤ β * Real.rpow (1 + y) p * N / Real.rpow q p := hfirst
    _ = β * Real.rpow (1 + y) p / Real.rpow N ((p - 2) / 2) := hnormalize

theorem actual_physical_compact_cdf_tail_bounds_nonnegative
    (C : ℝ)
    (hSZ : Shao.OQ6.NormalizedIntegrableCDFAssembly.ScalarShaoZhouFiniteCostCDFInput.{u} C)
    {Ω : Type u} [MeasurableSpace Ω]
    [MeasurableSpace.CountablyGenerated Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
    (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
    let s : ℝ := 1 + Real.sqrt v
    ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ), 3 ≤ n →
        let N : ℝ := (n : ℝ)
        let q : ℝ := Real.sqrt N
        let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
        let U : (Fin n → Ω) → ℝ := fun ξ =>
          Shao.OQ6.FiniteRows.uStatistic (fun i j => h (ξ i) (ξ j))
        let R2 : (Fin n → Ω) → ℝ := fun ξ =>
          Shao.OQ6.FiniteRows.jackknifeSq (fun i j => h (ξ i) (ξ j))
        let c_n : ℝ := 4 * (N - 1) / (N - 2) ^ 2
        let τ : ℝ → ℝ := fun x => x / Real.sqrt (1 + c_n * x ^ 2)
        let T : (Fin n → Ω) → ℝ := fun ξ =>
          if 0 < R2 ξ then q * U ξ / Real.sqrt (R2 ξ) else 0
        Measurable T ∧
          ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
            let y : ℝ := τ x
            let Lcompact : ℝ := N *
              (∫ o, Shao.truncationF ((1 + y) * (g o / q)) ∂μ)
            let error : ℝ :=
              C * (Lcompact + 16 * (1 + 4096) * (1 + y) * s / q) +
                2 * Real.exp (-c * N) +
                ((1 / 8 : ℝ) + 33104 * s) / q + 12 / N
            |P₀.real {ξ | T ξ ≤ x} - Shao.OQ4.standardNormalCDF x| ≤ error ∧
            |P₀.real {ξ | T ξ < x} - Shao.OQ4.standardNormalCDF x| ≤ error ∧
            |P₀.real {ξ | x < T ξ} -
              (1 - Shao.OQ4.standardNormalCDF x)| ≤ error ∧
            |P₀.real {ξ | x ≤ T ξ} -
              (1 - Shao.OQ4.standardNormalCDF x)| ≤ error := by
  classical
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
  let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
  let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
  let s : ℝ := 1 + Real.sqrt v
  obtain ⟨c169, hc169, h169⟩ :=
    Shao.OQ6.ActualUncenteredCompactCDF.actual_uncentered_compact_cdf_tail_bounds_nonnegative
      C hSZ μ h hh hh2 hhsymm hcenter hprojectionsecond
  obtain ⟨c147, hc147, h147⟩ :=
    Shao.OQ6.PhysicalCompact.actual_physical_zero_probability_and_compact_transport
      μ h hh hh2 hhsymm hcenter hprojectionsecond
  let c : ℝ := min c169 c147
  have hc : 0 < c := by
    dsimp only [c]
    exact lt_min hc169 hc147
  refine ⟨c, hc, ?_⟩
  intro n hn
  let N : ℝ := (n : ℝ)
  let q : ℝ := Real.sqrt N
  let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  let U : (Fin n → Ω) → ℝ := fun ξ =>
    Shao.OQ6.FiniteRows.uStatistic (fun i j => h (ξ i) (ξ j))
  let R2 : (Fin n → Ω) → ℝ := fun ξ =>
    Shao.OQ6.FiniteRows.jackknifeSq (fun i j => h (ξ i) (ξ j))
  let c_n : ℝ := 4 * (N - 1) / (N - 2) ^ 2
  let τ : ℝ → ℝ := fun x => x / Real.sqrt (1 + c_n * x ^ 2)
  let T : (Fin n → Ω) → ℝ := fun ξ =>
    if 0 < R2 ξ then q * U ξ / Real.sqrt (R2 ξ) else 0
  let J : (Fin n → Ω) → ℝ := fun ξ =>
    Shao.OQ6.FiniteRows.uncenteredSq (fun i j => h (ξ i) (ξ j))
  let Tstar : (Fin n → Ω) → ℝ := fun ξ =>
    if 0 < J ξ then q * U ξ / (2 * Real.sqrt (J ξ)) else 0
  let H0 : Fin n → Fin n → ℝ := fun _ _ => 0
  have hN : 0 ≤ N := Nat.cast_nonneg n
  have h147n := h147 n hn
  dsimp only at h147n
  rcases h147n with
    ⟨_, _, _, hT, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hclosed147, hopen147⟩
  change Measurable T at hT
  change (∀ x : ℝ, |x| ≤ 1 →
    |P₀.real {ξ | T ξ ≤ x} - Shao.OQ4.standardNormalCDF x| ≤
      |P₀.real {ξ | Tstar ξ ≤ τ x} - Shao.OQ4.standardNormalCDF (τ x)| +
        Real.exp (-c147 * N) + ((1 / 16 : ℝ) + 16720 * s) / q + 12 / N)
    at hclosed147
  change (∀ x : ℝ, |x| ≤ 1 →
    |P₀.real {ξ | T ξ < x} - Shao.OQ4.standardNormalCDF x| ≤
      |P₀.real {ξ | Tstar ξ < τ x} - Shao.OQ4.standardNormalCDF (τ x)| +
        Real.exp (-c147 * N) + ((1 / 16 : ℝ) + 16720 * s) / q + 12 / N)
    at hopen147
  have h169n := h169 n hn
  dsimp only at h169n
  rcases h169n with ⟨_, h169bound⟩
  have hfinite :=
    Shao.OQ6.PhysicalCompact.finite_physical_studentizer_conversion
      H0 (by intro i j; rfl) hn
  dsimp only at hfinite
  rcases hfinite with ⟨_, _, _, _, _, _, hτrange, _⟩
  change (∀ x : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ τ x ∧ τ x ≤ 1) at hτrange
  have hexp169 : Real.exp (-c169 * N) ≤ Real.exp (-c * N) := by
    apply Real.exp_le_exp.mpr
    have hprod := mul_le_mul_of_nonneg_right
      (show c ≤ c169 from min_le_left c169 c147) hN
    nlinarith only [hprod]
  have hexp147 : Real.exp (-c147 * N) ≤ Real.exp (-c * N) := by
    apply Real.exp_le_exp.mpr
    have hprod := mul_le_mul_of_nonneg_right
      (show c ≤ c147 from min_le_right c169 c147) hN
    nlinarith only [hprod]
  refine ⟨hT, ?_⟩
  intro x hx hx1
  let y : ℝ := τ x
  let Lcompact : ℝ := N *
    (∫ o, Shao.truncationF ((1 + y) * (g o / q)) ∂μ)
  let error : ℝ :=
    C * (Lcompact + 16 * (1 + 4096) * (1 + y) * s / q) +
      2 * Real.exp (-c * N) +
      ((1 / 8 : ℝ) + 33104 * s) / q + 12 / N
  change
    |P₀.real {ξ | T ξ ≤ x} - Shao.OQ4.standardNormalCDF x| ≤ error ∧
    |P₀.real {ξ | T ξ < x} - Shao.OQ4.standardNormalCDF x| ≤ error ∧
    |P₀.real {ξ | x < T ξ} - (1 - Shao.OQ4.standardNormalCDF x)| ≤ error ∧
    |P₀.real {ξ | x ≤ T ξ} - (1 - Shao.OQ4.standardNormalCDF x)| ≤ error
  have hy : 0 ≤ y := (hτrange x hx hx1).1
  have hxabs : |x| ≤ 1 := by simpa only [abs_of_nonneg hx] using hx1
  have h169y := h169bound y hy
  rcases h169y with ⟨hclosed169, hopen169, _, _⟩
  change |P₀.real {ξ | Tstar ξ ≤ y} - Shao.OQ4.standardNormalCDF y| ≤
    C * (Lcompact + 16 * (1 + 4096) * (1 + y) * s / q) +
      Real.exp (-c169 * N) + ((1 / 16 : ℝ) + 16384 * s) / q
    at hclosed169
  change |P₀.real {ξ | Tstar ξ < y} - Shao.OQ4.standardNormalCDF y| ≤
    C * (Lcompact + 16 * (1 + 4096) * (1 + y) * s / q) +
      Real.exp (-c169 * N) + ((1 / 16 : ℝ) + 16384 * s) / q
    at hopen169
  have hpay :
      (C * (Lcompact + 16 * (1 + 4096) * (1 + y) * s / q) +
        Real.exp (-c169 * N) + ((1 / 16 : ℝ) + 16384 * s) / q) +
        Real.exp (-c147 * N) + ((1 / 16 : ℝ) + 16720 * s) / q + 12 / N ≤
      error := by
    dsimp only [error]
    have hfractions :
        ((1 / 16 : ℝ) + 16384 * s) / q + ((1 / 16 : ℝ) + 16720 * s) / q =
          ((1 / 8 : ℝ) + 33104 * s) / q := by ring
    have hexps :
        Real.exp (-c169 * N) + Real.exp (-c147 * N) ≤ 2 * Real.exp (-c * N) := by
      linarith only [hexp169, hexp147]
    calc
      (C * (Lcompact + 16 * (1 + 4096) * (1 + y) * s / q) +
        Real.exp (-c169 * N) + ((1 / 16 : ℝ) + 16384 * s) / q) +
        Real.exp (-c147 * N) + ((1 / 16 : ℝ) + 16720 * s) / q + 12 / N =
          C * (Lcompact + 16 * (1 + 4096) * (1 + y) * s / q) +
            (Real.exp (-c169 * N) + Real.exp (-c147 * N)) +
            (((1 / 16 : ℝ) + 16384 * s) / q +
              ((1 / 16 : ℝ) + 16720 * s) / q) + 12 / N := by ring
      _ = C * (Lcompact + 16 * (1 + 4096) * (1 + y) * s / q) +
          (Real.exp (-c169 * N) + Real.exp (-c147 * N)) +
          ((1 / 8 : ℝ) + 33104 * s) / q + 12 / N := by rw [hfractions]
      _ ≤ C * (Lcompact + 16 * (1 + 4096) * (1 + y) * s / q) +
          2 * Real.exp (-c * N) + ((1 / 8 : ℝ) + 33104 * s) / q + 12 / N := by
        linarith only [hexps]
  have hclosed :
      |P₀.real {ξ | T ξ ≤ x} - Shao.OQ4.standardNormalCDF x| ≤ error := by
    have htransport := hclosed147 x hxabs
    change |P₀.real {ξ | T ξ ≤ x} - Shao.OQ4.standardNormalCDF x| ≤
      |P₀.real {ξ | Tstar ξ ≤ y} - Shao.OQ4.standardNormalCDF y| +
        Real.exp (-c147 * N) + ((1 / 16 : ℝ) + 16720 * s) / q + 12 / N
      at htransport
    linarith only [htransport, hclosed169, hpay]
  have hopen :
      |P₀.real {ξ | T ξ < x} - Shao.OQ4.standardNormalCDF x| ≤ error := by
    have htransport := hopen147 x hxabs
    change |P₀.real {ξ | T ξ < x} - Shao.OQ4.standardNormalCDF x| ≤
      |P₀.real {ξ | Tstar ξ < y} - Shao.OQ4.standardNormalCDF y| +
        Real.exp (-c147 * N) + ((1 / 16 : ℝ) + 16720 * s) / q + 12 / N
      at htransport
    linarith only [htransport, hopen169, hpay]
  have hComplementError (E : Set (Fin n → Ω)) (hE : MeasurableSet E) (a : ℝ) :
      |P₀.real Eᶜ - (1 - a)| = |P₀.real E - a| := by
    have he : P₀.real Eᶜ = 1 - P₀.real E := by
      simpa only [probReal_univ] using measureReal_compl (μ := P₀) hE
    rw [he, show (1 - P₀.real E) - (1 - a) = -(P₀.real E - a) by ring, abs_neg]
  refine ⟨hclosed, hopen, ?_, ?_⟩
  · have he : {ξ | x < T ξ} = {ξ | T ξ ≤ x}ᶜ := by
      ext ξ
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    rw [he, hComplementError _ (measurableSet_le hT measurable_const)
      (Shao.OQ4.standardNormalCDF x)]
    exact hclosed
  · have he : {ξ | x ≤ T ξ} = {ξ | T ξ < x}ᶜ := by
      ext ξ
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
    rw [he, hComplementError _ (measurableSet_lt hT measurable_const)
      (Shao.OQ4.standardNormalCDF x)]
    exact hopen

theorem actual_physical_compact_cdf_tail_rpow_rate
    (C : ℝ)
    (hSZ : Shao.OQ6.NormalizedIntegrableCDFAssembly.ScalarShaoZhouFiniteCostCDFInput.{u} C)
    {Ω : Type u} [MeasurableSpace Ω]
    [MeasurableSpace.CountablyGenerated Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
    (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (p : ℝ) (hp2 : 2 < p) (hp3 : p ≤ 3)
    (hgp : Integrable (fun o => Real.rpow |∫ y, h o y ∂μ| p) μ) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
    let s : ℝ := 1 + Real.sqrt v
    let β : ℝ := ∫ o, Real.rpow |g o| p ∂μ
    ∃ K : ℝ, 0 < K ∧
      ∀ (n : ℕ), 3 ≤ n →
        let N : ℝ := (n : ℝ)
        let q : ℝ := Real.sqrt N
        let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
        let U : (Fin n → Ω) → ℝ := fun ξ =>
          Shao.OQ6.FiniteRows.uStatistic (fun i j => h (ξ i) (ξ j))
        let R2 : (Fin n → Ω) → ℝ := fun ξ =>
          Shao.OQ6.FiniteRows.jackknifeSq (fun i j => h (ξ i) (ξ j))
        let T : (Fin n → Ω) → ℝ := fun ξ =>
          if 0 < R2 ξ then q * U ξ / Real.sqrt (R2 ξ) else 0
        Measurable T ∧
          ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
            let error : ℝ := K *
              (β / Real.rpow N ((p - 2) / 2) + s / q)
            |P₀.real {ξ | T ξ ≤ x} - Shao.OQ4.standardNormalCDF x| ≤ error ∧
            |P₀.real {ξ | T ξ < x} - Shao.OQ4.standardNormalCDF x| ≤ error ∧
            |P₀.real {ξ | x < T ξ} -
              (1 - Shao.OQ4.standardNormalCDF x)| ≤ error ∧
            |P₀.real {ξ | x ≤ T ξ} -
              (1 - Shao.OQ4.standardNormalCDF x)| ≤ error := by
  classical
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
  let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
  let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
  let s : ℝ := 1 + Real.sqrt v
  let β : ℝ := ∫ o, Real.rpow |g o| p ∂μ
  obtain ⟨c, hc, hphysical⟩ :=
    actual_physical_compact_cdf_tail_bounds_nonnegative
      C hSZ μ h hh hh2 hhsymm hcenter hprojectionsecond
  have hdata := Shao.OQ6.ActualQuadraticTiltMoments.actual_quadratic_source_moments
    μ h hh hh2 hhsymm hcenter hprojectionsecond 3 (by norm_num) 0
      (by norm_num) (by positivity)
  dsimp only at hdata
  rcases hdata with ⟨hg, hg2, _, _, _, _, _, _, _, hs, _⟩
  change Measurable g at hg
  change MemLp g 2 μ at hg2
  change 1 ≤ s at hs
  change Integrable (fun o => Real.rpow |g o| p) μ at hgp
  have hC : 0 < C := lt_trans (by norm_num : (0 : ℝ) < 1) hSZ.1
  have hdivc : 0 ≤ 2 / c := div_nonneg (by norm_num) hc.le
  let K : ℝ := 131112 * C + 33117 + 2 / c
  have hK : 0 < K := by
    dsimp only [K]
    nlinarith only [hC, hdivc]
  have hKA : 8 * C ≤ K := by
    dsimp only [K]
    nlinarith only [hC, hdivc]
  have hKB : 131104 * C + 33117 + 2 / c ≤ K := by
    dsimp only [K]
    nlinarith only [hC]
  have hβ : 0 ≤ β := by
    apply integral_nonneg
    intro o
    change (0 : ℝ) ≤ Real.rpow |g o| p
    simpa only [Real.rpow_eq_pow] using Real.rpow_nonneg (abs_nonneg (g o)) p
  refine ⟨K, hK, ?_⟩
  intro n hn
  let N : ℝ := (n : ℝ)
  let q : ℝ := Real.sqrt N
  let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  let U : (Fin n → Ω) → ℝ := fun ξ =>
    Shao.OQ6.FiniteRows.uStatistic (fun i j => h (ξ i) (ξ j))
  let R2 : (Fin n → Ω) → ℝ := fun ξ =>
    Shao.OQ6.FiniteRows.jackknifeSq (fun i j => h (ξ i) (ξ j))
  let T : (Fin n → Ω) → ℝ := fun ξ =>
    if 0 < R2 ξ then q * U ξ / Real.sqrt (R2 ξ) else 0
  let c_n : ℝ := 4 * (N - 1) / (N - 2) ^ 2
  let τ : ℝ → ℝ := fun x => x / Real.sqrt (1 + c_n * x ^ 2)
  let H0 : Fin n → Fin n → ℝ := fun _ _ => 0
  have hN3 : (3 : ℝ) ≤ N := by
    dsimp only [N]
    exact_mod_cast hn
  have hN : 0 < N := by linarith only [hN3]
  have hq : 0 < q := Real.sqrt_pos.mpr hN
  have hqsq : q ^ 2 = N := Real.sq_sqrt hN.le
  have hq1 : 1 ≤ q := by
    by_contra hnot
    have hlt : q < 1 := lt_of_not_ge hnot
    have hprod := mul_pos (sub_pos.mpr hlt) (by linarith only [hq] : 0 < 1 + q)
    nlinarith only [hprod, hqsq, hN3]
  have hqN : q ≤ N := by
    have hprod := mul_nonneg hq.le (sub_nonneg.mpr hq1)
    nlinarith only [hprod, hqsq]
  have hden : 0 < Real.rpow N ((p - 2) / 2) := Real.rpow_pos_of_pos hN _
  have hβden : 0 ≤ β / Real.rpow N ((p - 2) / 2) :=
    div_nonneg hβ hden.le
  have hs0 : 0 ≤ s := by linarith only [hs]
  have hsq : 0 ≤ s / q := div_nonneg hs0 hq.le
  have hunit : 1 / q ≤ s / q := div_le_div_of_nonneg_right hs hq.le
  have hNrecip : 1 / N ≤ 1 / q :=
    (div_le_div_iff₀ hN hq).2 (by simpa only [one_mul] using hqN)
  have hexpden : c * q ≤ Real.exp (c * N) := by
    have hprod := mul_le_mul_of_nonneg_left hqN hc.le
    have hexp := Real.add_one_le_exp (c * N)
    linarith only [hprod, hexp]
  have hexpbase : Real.exp (-c * N) ≤ 1 / (c * q) := by
    calc
      Real.exp (-c * N) = 1 / Real.exp (c * N) := by
        rw [show -c * N = -(c * N) by ring, Real.exp_neg, one_div]
      _ ≤ 1 / (c * q) :=
        (div_le_div_iff₀ (Real.exp_pos _) (mul_pos hc hq)).2
          (by simpa only [one_mul] using hexpden)
  have hexpunit : 1 / (c * q) ≤ (1 / c) * (s / q) := by
    have hmul := mul_le_mul_of_nonneg_left hunit
      (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hc.le)
    convert hmul using 1 <;> field_simp [hc.ne', hq.ne'] <;> ring
  have hexp : 2 * Real.exp (-c * N) ≤ (2 / c) * (s / q) := by
    calc
      2 * Real.exp (-c * N) ≤ 2 * ((1 / c) * (s / q)) :=
        mul_le_mul_of_nonneg_left (hexpbase.trans hexpunit) (by norm_num)
      _ = (2 / c) * (s / q) := by ring
  have h12 : 12 / N ≤ 12 * (s / q) := by
    calc
      12 / N = 12 * (1 / N) := by ring
      _ ≤ 12 * (s / q) :=
        mul_le_mul_of_nonneg_left (hNrecip.trans hunit) (by norm_num)
  have h18 : (1 / 8 : ℝ) / q ≤ (1 / 8 : ℝ) * (s / q) := by
    have hmul := mul_le_mul_of_nonneg_left hunit
      (by norm_num : (0 : ℝ) ≤ 1 / 8)
    convert hmul using 1 <;> ring
  have hpoly : ((1 / 8 : ℝ) + 33104 * s) / q + 12 / N ≤
      33117 * (s / q) := by
    calc
      ((1 / 8 : ℝ) + 33104 * s) / q + 12 / N =
          (1 / 8 : ℝ) / q + 33104 * (s / q) + 12 / N := by ring
      _ ≤ (1 / 8 : ℝ) * (s / q) + 33104 * (s / q) + 12 * (s / q) := by
        linarith only [h12, h18]
      _ ≤ 33117 * (s / q) := by linarith only [hsq]
  have hfinite :=
    Shao.OQ6.PhysicalCompact.finite_physical_studentizer_conversion
      H0 (by intro i j; rfl) hn
  dsimp only at hfinite
  rcases hfinite with ⟨_, _, _, _, _, _, hτrange, _⟩
  change (∀ x : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ τ x ∧ τ x ≤ 1) at hτrange
  have hphysicaln := hphysical n hn
  dsimp only at hphysicaln
  rcases hphysicaln with ⟨hT, hphysicalbound⟩
  change Measurable T at hT
  refine ⟨hT, ?_⟩
  intro x hx hx1
  let error : ℝ := K * (β / Real.rpow N ((p - 2) / 2) + s / q)
  let y : ℝ := τ x
  let Lcompact : ℝ := N *
    (∫ o, Shao.truncationF ((1 + y) * (g o / q)) ∂μ)
  change
    |P₀.real {ξ | T ξ ≤ x} - Shao.OQ4.standardNormalCDF x| ≤ error ∧
    |P₀.real {ξ | T ξ < x} - Shao.OQ4.standardNormalCDF x| ≤ error ∧
    |P₀.real {ξ | x < T ξ} - (1 - Shao.OQ4.standardNormalCDF x)| ≤ error ∧
    |P₀.real {ξ | x ≤ T ξ} - (1 - Shao.OQ4.standardNormalCDF x)| ≤ error
  have hy : 0 ≤ y := (hτrange x hx hx1).1
  have hy1 : y ≤ 1 := (hτrange x hx hx1).2
  have hmoment := normalized_observation_truncation_budget_le_rpow_moment
    μ g hg hg2 p hp2.le hp3 hgp n (le_trans (by norm_num : 1 ≤ 3) hn) y hy
  dsimp only at hmoment
  have hL := hmoment.2.2
  change Lcompact ≤ β * Real.rpow (1 + y) p /
    Real.rpow N ((p - 2) / 2) at hL
  have hscale : Real.rpow (1 + y) p ≤ 8 := by
    calc
      Real.rpow (1 + y) p ≤ Real.rpow (2 : ℝ) p :=
        Real.rpow_le_rpow (by linarith only [hy])
          (by linarith only [hy1]) (by linarith only [hp2])
      _ ≤ Real.rpow (2 : ℝ) (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hp3
      _ = (2 : ℝ) ^ 3 := Real.rpow_natCast 2 3
      _ = 8 := by norm_num
  have hL8 : Lcompact ≤ 8 * (β / Real.rpow N ((p - 2) / 2)) := by
    calc
      Lcompact ≤ β * Real.rpow (1 + y) p /
          Real.rpow N ((p - 2) / 2) := hL
      _ ≤ β * 8 / Real.rpow N ((p - 2) / 2) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hscale hβ) hden.le
      _ = 8 * (β / Real.rpow N ((p - 2) / 2)) := by ring
  have hrescoef : 16 * (1 + 4096) * (1 + y) ≤ (131104 : ℝ) := by
    linarith only [hy1]
  have hres := mul_le_mul_of_nonneg_right hrescoef hsq
  have hinside :
      Lcompact + 16 * (1 + 4096) * (1 + y) * s / q ≤
        8 * (β / Real.rpow N ((p - 2) / 2)) + 131104 * (s / q) := by
    calc
      Lcompact + 16 * (1 + 4096) * (1 + y) * s / q =
          Lcompact + (16 * (1 + 4096) * (1 + y)) * (s / q) := by ring
      _ ≤ 8 * (β / Real.rpow N ((p - 2) / 2)) + 131104 * (s / q) :=
        add_le_add hL8 hres
  have hanalytic :
      C * (Lcompact + 16 * (1 + 4096) * (1 + y) * s / q) ≤
        8 * C * (β / Real.rpow N ((p - 2) / 2)) + 131104 * C * (s / q) := by
    calc
      _ ≤ C * (8 * (β / Real.rpow N ((p - 2) / 2)) + 131104 * (s / q)) :=
        mul_le_mul_of_nonneg_left hinside hC.le
      _ = _ := by ring
  have hfee :
      C * (Lcompact + 16 * (1 + 4096) * (1 + y) * s / q) +
        2 * Real.exp (-c * N) + ((1 / 8 : ℝ) + 33104 * s) / q + 12 / N ≤
      error := by
    have hA := mul_le_mul_of_nonneg_right hKA hβden
    have hB := mul_le_mul_of_nonneg_right hKB hsq
    dsimp only [error]
    nlinarith only [hanalytic, hexp, hpoly, hA, hB]
  have hphysicalx := hphysicalbound x hx hx1
  rcases hphysicalx with ⟨h1, h2, h3, h4⟩
  exact ⟨h1.trans hfee, h2.trans hfee, h3.trans hfee, h4.trans hfee⟩

end

end Shao.OQ6.ActualPhysicalCompactCDF
