import Shao.OQ6.ActualPhysicalCompactCDF

set_option autoImplicit false

namespace Shao.OQ6.ActualPhysicalCompactRelative

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

universe u

private theorem standard_normal_tail_at_one_pos :
    0 < 1 - Shao.OQ4.standardNormalCDF 1 := by
  let f : ℝ → ℝ := gaussianPDFReal 0 1
  have hfpos : ∀ x : ℝ, 0 < f x := by
    intro x
    exact gaussianPDFReal_pos 0 1 x (by norm_num)
  have hfnonneg : 0 ≤ f := fun x => (hfpos x).le
  have hfi : Integrable f (volume.restrict (Set.Ioc (1 : ℝ) 2)) :=
    (integrable_gaussianPDFReal 0 1).restrict
  have hsupport : Function.support f = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hfpos x).ne'
  have hsupportmass :
      0 < (volume.restrict (Set.Ioc (1 : ℝ) 2)) (Function.support f) := by
    rw [hsupport, Measure.restrict_apply_univ, Real.volume_Ioc]
    norm_num
  have hI : 0 < ∫ x in Set.Ioc (1 : ℝ) 2, f x :=
    (integral_pos_iff_support_of_nonneg hfnonneg hfi).2 hsupportmass
  have hmass : 0 < (gaussianReal 0 1).real (Set.Ioc (1 : ℝ) 2) := by
    rw [measureReal_def,
      gaussianReal_apply_eq_integral 0 (by norm_num : (1 : NNReal) ≠ 0),
      ENNReal.toReal_ofReal (integral_nonneg (gaussianPDFReal_nonneg 0 1))]
    exact hI
  have hsub : Set.Ioc (1 : ℝ) 2 ⊆ Set.Ioi 1 := by
    intro x hx
    exact hx.1
  have htail : 0 < (gaussianReal 0 1).real (Set.Ioi (1 : ℝ)) :=
    hmass.trans_le (measureReal_mono (μ := gaussianReal 0 1) hsub)
  have hcomp : (gaussianReal 0 1).real (Set.Ioi (1 : ℝ)) =
      1 - Shao.OQ4.standardNormalCDF 1 := by
    have he : Set.Ioi (1 : ℝ) = (Set.Iic (1 : ℝ))ᶜ := by
      ext x
      simp only [Set.mem_Ioi, Set.mem_compl_iff, Set.mem_Iic, not_le]
    rw [he, measureReal_compl (μ := gaussianReal 0 1) measurableSet_Iic, probReal_univ,
      ← Shao.OQ4.standardNormalCDF_eq_real]
  rw [hcomp] at htail
  exact htail

theorem actual_physical_compact_relative_tail_rpow_rate
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
    ∃ Krel : ℝ, 0 < Krel ∧
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
            let error : ℝ := Krel *
              (β / Real.rpow N ((p - 2) / 2) + s / q)
            |P₀.real {ξ | x < T ξ} /
              (1 - Shao.OQ4.standardNormalCDF x) - 1| ≤ error ∧
            |P₀.real {ξ | x ≤ T ξ} /
              (1 - Shao.OQ4.standardNormalCDF x) - 1| ≤ error := by
  classical
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
  let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
  let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
  let s : ℝ := 1 + Real.sqrt v
  let β : ℝ := ∫ o, Real.rpow |g o| p ∂μ
  obtain ⟨Kabs, hKabs, habsolute⟩ :=
    Shao.OQ6.ActualPhysicalCompactCDF.actual_physical_compact_cdf_tail_rpow_rate
      C hSZ μ h hh hh2 hhsymm hcenter hprojectionsecond p hp2 hp3 hgp
  let a : ℝ := 1 - Shao.OQ4.standardNormalCDF 1
  have ha : 0 < a := standard_normal_tail_at_one_pos
  let Krel : ℝ := Kabs / a
  have hKrel : 0 < Krel := div_pos hKabs ha
  refine ⟨Krel, hKrel, ?_⟩
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
  have habsoluten := habsolute n hn
  dsimp only at habsoluten
  rcases habsoluten with ⟨hT, hbound⟩
  change Measurable T at hT
  refine ⟨hT, ?_⟩
  intro x hx hx1
  let Ψ : ℝ := 1 - Shao.OQ4.standardNormalCDF x
  let E : ℝ := β / Real.rpow N ((p - 2) / 2) + s / q
  change |P₀.real {ξ | x < T ξ} / Ψ - 1| ≤ Krel * E ∧
    |P₀.real {ξ | x ≤ T ξ} / Ψ - 1| ≤ Krel * E
  have hCDF : Shao.OQ4.standardNormalCDF x ≤ Shao.OQ4.standardNormalCDF 1 := by
    exact monotone_cdf (gaussianReal 0 1) hx1
  have haΨ : a ≤ Ψ := by
    dsimp only [a, Ψ]
    exact sub_le_sub_left hCDF 1
  have hΨ : 0 < Ψ := ha.trans_le haΨ
  have habsolutex := hbound x hx hx1
  rcases habsolutex with ⟨_, _, hstrict, hweak⟩
  change |P₀.real {ξ | x < T ξ} - Ψ| ≤ Kabs * E at hstrict
  change |P₀.real {ξ | x ≤ T ξ} - Ψ| ≤ Kabs * E at hweak
  have hnonneg : 0 ≤ Kabs * E := (abs_nonneg _).trans hstrict
  have hrelative (P : ℝ) (hP : |P - Ψ| ≤ Kabs * E) :
    |P / Ψ - 1| ≤ Krel * E := by
    have heq : P / Ψ - 1 = (P - Ψ) / Ψ := by
      field_simp [hΨ.ne'] <;> ring
    calc
      |P / Ψ - 1| = |P - Ψ| / Ψ := by
        rw [heq, abs_div, abs_of_pos hΨ]
      _ ≤ (Kabs * E) / Ψ := div_le_div_of_nonneg_right hP hΨ.le
      _ ≤ (Kabs * E) / a :=
        (div_le_div_iff₀ hΨ ha).2 (mul_le_mul_of_nonneg_left haΨ hnonneg)
      _ = Krel * E := by
        dsimp only [Krel]
        ring
  exact ⟨hrelative _ hstrict, hrelative _ hweak⟩

end

end Shao.OQ6.ActualPhysicalCompactRelative
