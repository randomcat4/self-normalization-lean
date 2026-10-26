import Shao.OQ6.WeightedDeletionMoments
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

namespace Shao.OQ6.RhoWeightedDeletionMoments

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

private theorem scaled_centered_kernel_model
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgmean : (∫ o, g o ∂μ) = 0)
    (hgsecond : (∫ o, g o ^ 2 ∂μ) = 1)
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun z : Ω × Ω => r z.1 z.2))
    (hr2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (μ.prod μ))
    (hrsymm : ∀ o y, r o y = r y o)
    (hrcan : ∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    let k : Ω → Ω → ℝ := fun o y => g o + g y + t * r o y
    let gk : Ω → ℝ := fun o => ∫ y, k o y ∂μ
    let rk : Ω → Ω → ℝ := fun o y => k o y - gk o - gk y
    let v : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)
    let vk : ℝ := ∫ z : Ω × Ω, rk z.1 z.2 ^ 2 ∂(μ.prod μ)
    Measurable (fun z : Ω × Ω => k z.1 z.2) ∧
      MemLp (fun z : Ω × Ω => k z.1 z.2) 2 (μ.prod μ) ∧
      (∀ o y, k o y = k y o) ∧
      (∫ z : Ω × Ω, k z.1 z.2 ∂(μ.prod μ)) = 0 ∧
      (∫ o, (∫ y, k o y ∂μ) ^ 2 ∂μ) = 1 ∧
      gk =ᵐ[μ] g ∧
      (∀ o y, gk o = g o → gk y = g y → rk o y = t * r o y) ∧
      (fun z : Ω × Ω => rk z.1 z.2) =ᵐ[μ.prod μ]
        (fun z : Ω × Ω => t * r z.1 z.2) ∧
      vk = t ^ 2 * v ∧
      Real.sqrt vk = t * Real.sqrt v := by
  classical
  dsimp only
  let k : Ω → Ω → ℝ := fun o y => g o + g y + t * r o y
  let gk : Ω → ℝ := fun o => ∫ y, k o y ∂μ
  let rk : Ω → Ω → ℝ := fun o y => k o y - gk o - gk y
  let v : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)
  let vk : ℝ := ∫ z : Ω × Ω, rk z.1 z.2 ^ 2 ∂(μ.prod μ)
  have hg1 : Integrable g μ := hg2.integrable (by norm_num)
  have hr1 : Integrable (fun z : Ω × Ω => r z.1 z.2) (μ.prod μ) :=
    hr2.integrable (by norm_num)
  have hkM : Measurable (fun z : Ω × Ω => k z.1 z.2) :=
    ((hg.comp measurable_fst).add (hg.comp measurable_snd)).add (hr.const_mul t)
  have hk2 : MemLp (fun z : Ω × Ω => k z.1 z.2) 2 (μ.prod μ) :=
    ((hg2.comp_fst μ).add (hg2.comp_snd μ)).add (hr2.const_mul t)
  have hk1 : Integrable (fun z : Ω × Ω => k z.1 z.2) (μ.prod μ) :=
    hk2.integrable (by norm_num)
  have hkSymm : ∀ o y, k o y = k y o := by
    intro o y
    dsimp only [k]
    rw [hrsymm o y]
    ring
  have hProjectionAE : gk =ᵐ[μ] g := by
    filter_upwards [hr1.prod_right_ae, hrcan] with o ho hcan
    change (∫ y, g o + g y + t * r o y ∂μ) = g o
    have hsum : Integrable (fun y : Ω => g o + g y) μ :=
      (integrable_const (g o)).add hg1
    rw [integral_add hsum (ho.const_mul t),
      integral_add (integrable_const (g o)) hg1, integral_const_mul,
      integral_const, probReal_univ, one_smul, hgmean, hcan]
    ring
  have hkMean : (∫ z : Ω × Ω, k z.1 z.2 ∂(μ.prod μ)) = 0 := by
    calc
      _ = ∫ o, gk o ∂μ := integral_prod _ hk1
      _ = ∫ o, g o ∂μ := integral_congr_ae hProjectionAE
      _ = 0 := hgmean
  have hkSecond : (∫ o, (∫ y, k o y ∂μ) ^ 2 ∂μ) = 1 := by
    calc
      _ = ∫ o, g o ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [hProjectionAE] with o ho
        change gk o ^ 2 = g o ^ 2
        rw [ho]
      _ = 1 := hgsecond
  have hrPoint : ∀ o y, gk o = g o → gk y = g y →
      rk o y = t * r o y := by
    intro o y ho hy
    dsimp only [rk, k]
    rw [ho, hy]
    ring
  have hrAE : (fun z : Ω × Ω => rk z.1 z.2) =ᵐ[μ.prod μ]
      (fun z : Ω × Ω => t * r z.1 z.2) := by
    filter_upwards [
      (measurePreserving_fst (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hProjectionAE,
      (measurePreserving_snd (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hProjectionAE]
      with z hz1 hz2
    exact hrPoint z.1 z.2 hz1 hz2
  have hEnergy : vk = t ^ 2 * v := by
    calc
      _ = ∫ z : Ω × Ω, t ^ 2 * r z.1 z.2 ^ 2 ∂(μ.prod μ) := by
        apply integral_congr_ae
        filter_upwards [hrAE] with z hz
        rw [hz]
        ring
      _ = t ^ 2 * v := integral_const_mul _ _
  have hRootEnergy : Real.sqrt vk = t * Real.sqrt v := by
    rw [hEnergy, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]
  exact ⟨hkM, hk2, hkSymm, hkMean, hkSecond, hProjectionAE,
    hrPoint, hrAE, hEnergy, hRootEnergy⟩

private theorem remove_positive_scale_offset
    (A B ρr : ℝ) (p : ℕ)
    (hscaled : ∀ t : ℝ, 0 < t →
      t ^ p * A ≤ B * (1 + t * ρr) ^ p) :
    A ≤ B * ρr ^ p := by
  have hpoint (k : ℕ) : A ≤ B * (ρr + 1 / ((k : ℝ) + 1)) ^ p := by
    have ht : 0 < (k : ℝ) + 1 := by positivity
    have hpower : (1 + ((k : ℝ) + 1) * ρr) ^ p =
        ((k : ℝ) + 1) ^ p * (ρr + 1 / ((k : ℝ) + 1)) ^ p := by
      rw [← mul_pow]
      congr 1
      field_simp [ht.ne']
      <;> ring
    apply (mul_le_mul_iff_right₀ (pow_pos ht p)).mp
    calc
      ((k : ℝ) + 1) ^ p * A ≤ B * (1 + ((k : ℝ) + 1) * ρr) ^ p :=
        hscaled ((k : ℝ) + 1) ht
      _ = ((k : ℝ) + 1) ^ p * (B * (ρr + 1 / ((k : ℝ) + 1)) ^ p) := by
        rw [hpower]
        ring
  have hlim : Tendsto (fun k : ℕ => B * (ρr + 1 / ((k : ℝ) + 1)) ^ p)
      atTop (nhds (B * ρr ^ p)) := by
    simpa only [add_zero] using
      ((((tendsto_const_nhds (x := ρr)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).pow p).const_mul B)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (Filter.Eventually.of_forall hpoint)

theorem actual_quadratic_rho_weighted_deletion_bounds
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun z : Ω × Ω => h z.1 z.2))
    (hh2 : MemLp (fun z : Ω × Ω => h z.1 z.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ z : Ω × Ω, h z.1 z.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (n : ℕ) (hn : 4 ≤ n)
    (x : ℝ) (hx : 0 ≤ x)
    (hwindow : x ≤ Real.sqrt (n : ℝ) /
      (2 * Real.exp (1 / 2 : ℝ))) :
    let C : ℝ := Real.exp (1 / 2 : ℝ)
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)
    let ρr : ℝ := Real.sqrt v
    let a : ℝ := x / Real.sqrt (n : ℝ)
    let φ : Ω → ℝ := fun o => a * g o - (a * g o) ^ 2 / 2
    let w : Ω → ℝ := fun o => Real.exp (φ o)
    let m : ℝ := ∫ o, w o ∂μ
    let L : Ω → ℝ := fun o => w o / m
    let ρ : Measure Ω :=
      μ.withDensity (fun o => ENNReal.ofReal (L o))
    let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
    let I : ℝ := m ^ n
    let R : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Real.exp (∑ j ∈ Finset.univ.erase i, φ (ξ j)) / I
    let cap : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      min |a * g (ξ i)| 1
    let e : (Fin n → Ω) → Fin n → Fin n → ℝ :=
      fun ξ j k => r (ξ j) (ξ k)
    let F : (Fin n → Ω) → ℝ := fun ξ =>
      Shao.OQ5.P35.unorderedPairSum (e ξ)
    let Fdel : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Shao.OQ5.P35.unorderedPairSum
        (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i)
    let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ j =>
      Shao.OQ6.ResidualDeletion.rowSum (e ξ) j
    let ψdel : (Fin n → Ω) → Fin n → Fin n → ℝ := fun ξ i j =>
      Shao.OQ6.ResidualDeletion.rowSum
        (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i) j
    let Λsq : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ j : Fin n, ψ ξ j ^ 2
    let Λdelsq : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      ∑ j : Fin n, ψdel ξ i j ^ 2
    let u : (Fin n → Ω) → Fin n → ℝ := fun ξ j =>
      ψ ξ j / ((n : ℝ) - 2)
    let udel : (Fin n → Ω) → Fin n → Fin n → ℝ := fun ξ i j =>
      ψdel ξ i j / ((n : ℝ) - 2)
    let J : (Fin n → Ω) → ℝ := fun ξ => ∑ j : Fin n, u ξ j ^ 2
    let Jdel : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      ∑ j : Fin n, udel ξ i j ^ 2
    let D₁ : (Fin n → Ω) → ℝ := fun ξ =>
      F ξ / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
    let D₁del : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Fdel ξ i / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
    let cross : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      ∑ j ∈ Finset.univ.erase i,
        2 * r (ξ i) (ξ j) * (ψ ξ j - r (ξ i) (ξ j))
    (∀ ξ i, Λsq ξ - Λdelsq ξ i = ψ ξ i ^ 2 + cross ξ i +
      ∑ j ∈ Finset.univ.erase i, r (ξ i) (ξ j) ^ 2) ∧
      (∀ i : Fin n, Integrable
        (fun ξ => R ξ i * cap ξ i * |D₁ ξ - D₁del ξ i|) P₀) ∧
      (∑ i : Fin n,
        ∫ ξ, R ξ i * cap ξ i * |D₁ ξ - D₁del ξ i| ∂P₀) ≤
          4 * Real.sqrt 2 * C * ρr * (1 + x) ^ 2 /
            Real.sqrt (n : ℝ) ∧
      (∀ i : Fin n, Integrable
        (fun ξ => R ξ i * cap ξ i * |cross ξ i|) P₀) ∧
      (∑ i : Fin n,
        ∫ ξ, R ξ i * cap ξ i * |cross ξ i| ∂P₀) ≤
          16 * C ^ 2 * ρr ^ 2 * (n : ℝ) ^ 2 * x * (1 + x) ∧
      (∀ i : Fin n, Integrable
        (fun ξ => R ξ i * cap ξ i * |Λsq ξ - Λdelsq ξ i|) P₀) ∧
      (∑ i : Fin n,
        ∫ ξ, R ξ i * cap ξ i * |Λsq ξ - Λdelsq ξ i| ∂P₀) ≤
          24 * C ^ 2 * ρr ^ 2 * (n : ℝ) ^ 2 * (1 + x) ^ 2 ∧
      (∀ i : Fin n, Integrable
        (fun ξ => R ξ i * cap ξ i * abs (abs (D₁ ξ) - abs (D₁del ξ i))) P₀) ∧
      (∑ i : Fin n,
        ∫ ξ, R ξ i * cap ξ i * abs (abs (D₁ ξ) - abs (D₁del ξ i)) ∂P₀) ≤
          4 * Real.sqrt 2 * C * ρr * (1 + x) ^ 2 /
            Real.sqrt (n : ℝ) ∧
      (∀ i : Fin n, Integrable
        (fun ξ => R ξ i * cap ξ i * |J ξ - Jdel ξ i|) P₀) ∧
      (∑ i : Fin n,
        ∫ ξ, R ξ i * cap ξ i * |J ξ - Jdel ξ i| ∂P₀) ≤
          96 * C ^ 2 * ρr ^ 2 * (1 + x) ^ 2 := by
  classical
  dsimp only
  let C : ℝ := Real.exp (1 / 2 : ℝ)
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
  let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
  let v : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)
  let ρr : ℝ := Real.sqrt v
  let a : ℝ := x / Real.sqrt (n : ℝ)
  let φ : Ω → ℝ := fun o => a * g o - (a * g o) ^ 2 / 2
  let w : Ω → ℝ := fun o => Real.exp (φ o)
  let m : ℝ := ∫ o, w o ∂μ
  let L : Ω → ℝ := fun o => w o / m
  let ρ : Measure Ω := μ.withDensity (fun o => ENNReal.ofReal (L o))
  let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  let I : ℝ := m ^ n
  let R : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    Real.exp (∑ j ∈ Finset.univ.erase i, φ (ξ j)) / I
  let cap : (Fin n → Ω) → Fin n → ℝ := fun ξ i => min |a * g (ξ i)| 1
  let e : (Fin n → Ω) → Fin n → Fin n → ℝ := fun ξ j k => r (ξ j) (ξ k)
  let F : (Fin n → Ω) → ℝ := fun ξ => Shao.OQ5.P35.unorderedPairSum (e ξ)
  let Fdel : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    Shao.OQ5.P35.unorderedPairSum
      (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i)
  let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ j =>
    Shao.OQ6.ResidualDeletion.rowSum (e ξ) j
  let ψdel : (Fin n → Ω) → Fin n → Fin n → ℝ := fun ξ i j =>
    Shao.OQ6.ResidualDeletion.rowSum
      (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i) j
  let Λsq : (Fin n → Ω) → ℝ := fun ξ => ∑ j : Fin n, ψ ξ j ^ 2
  let Λdelsq : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    ∑ j : Fin n, ψdel ξ i j ^ 2
  let u : (Fin n → Ω) → Fin n → ℝ := fun ξ j => ψ ξ j / ((n : ℝ) - 2)
  let udel : (Fin n → Ω) → Fin n → Fin n → ℝ := fun ξ i j =>
    ψdel ξ i j / ((n : ℝ) - 2)
  let J : (Fin n → Ω) → ℝ := fun ξ => ∑ j : Fin n, u ξ j ^ 2
  let Jdel : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    ∑ j : Fin n, udel ξ i j ^ 2
  let D₁ : (Fin n → Ω) → ℝ := fun ξ =>
    F ξ / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
  let D₁del : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    Fdel ξ i / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
  let cross : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    ∑ j ∈ Finset.univ.erase i,
      2 * r (ξ i) (ξ j) * (ψ ξ j - r (ξ i) (ξ j))
  have hn3 : 3 ≤ n := le_trans (by norm_num : 3 ≤ 4) hn
  have source := Shao.OQ6.ActualQuadraticTiltMoments.actual_quadratic_source_moments
    μ h hh hh2 hhsymm hcenter hprojectionsecond n hn3 x hx hwindow
  rcases source with
    ⟨hg, hg2, hgmean, hgsecond, hr, hr2, hrsymm, hrcan,
      hv, hs1, hvs, hw, hmlo, hrest⟩
  change Measurable g at hg
  change MemLp g 2 μ at hg2
  change (∫ o, g o ∂μ) = 0 at hgmean
  change (∫ o, g o ^ 2 ∂μ) = 1 at hgsecond
  change Measurable (fun z : Ω × Ω => r z.1 z.2) at hr
  change MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (μ.prod μ) at hr2
  change (∀ o y, r o y = r y o) at hrsymm
  change (∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0) at hrcan
  change 0 ≤ v at hv
  change (1 / 2 : ℝ) ≤ m at hmlo
  have original := Shao.OQ6.WeightedDeletionMoments.actual_quadratic_weighted_deletion_bounds
    μ h hh hh2 hhsymm hcenter hprojectionsecond n hn3 x hx hwindow
  rcases original with ⟨hsigned, hDI, hDold, hXI, hXold, hΛI, hΛold⟩
  change (∀ ξ i, Λsq ξ - Λdelsq ξ i = ψ ξ i ^ 2 + cross ξ i +
    ∑ j ∈ Finset.univ.erase i, r (ξ i) (ξ j) ^ 2) at hsigned
  change (∀ i : Fin n, Integrable
    (fun ξ => R ξ i * cap ξ i * |D₁ ξ - D₁del ξ i|) P₀) at hDI
  change (∀ i : Fin n, Integrable
    (fun ξ => R ξ i * cap ξ i * |cross ξ i|) P₀) at hXI
  change (∀ i : Fin n, Integrable
    (fun ξ => R ξ i * cap ξ i * |Λsq ξ - Λdelsq ξ i|) P₀) at hΛI
  let A_D : ℝ := ∑ i : Fin n,
    ∫ ξ, R ξ i * cap ξ i * |D₁ ξ - D₁del ξ i| ∂P₀
  let A_X : ℝ := ∑ i : Fin n, ∫ ξ, R ξ i * cap ξ i * |cross ξ i| ∂P₀
  let A_Λ : ℝ := ∑ i : Fin n,
    ∫ ξ, R ξ i * cap ξ i * |Λsq ξ - Λdelsq ξ i| ∂P₀
  let B_D : ℝ := 4 * Real.sqrt 2 * C * (1 + x) ^ 2 / Real.sqrt (n : ℝ)
  let B_X : ℝ := 16 * C ^ 2 * (n : ℝ) ^ 2 * x * (1 + x)
  let B_Λ : ℝ := 24 * C ^ 2 * (n : ℝ) ^ 2 * (1 + x) ^ 2
  have hscaled (t : ℝ) (ht : 0 < t) :
      t * A_D ≤ B_D * (1 + t * ρr) ∧
      t ^ 2 * A_X ≤ B_X * (1 + t * ρr) ^ 2 ∧
      t ^ 2 * A_Λ ≤ B_Λ * (1 + t * ρr) ^ 2 := by
    let kₜ : Ω → Ω → ℝ := fun o y => g o + g y + t * r o y
    let gₜ : Ω → ℝ := fun o => ∫ y, kₜ o y ∂μ
    let rₜ : Ω → Ω → ℝ := fun o y => kₜ o y - gₜ o - gₜ y
    let vₜ : ℝ := ∫ z : Ω × Ω, rₜ z.1 z.2 ^ 2 ∂(μ.prod μ)
    let φₜ : Ω → ℝ := fun o => a * gₜ o - (a * gₜ o) ^ 2 / 2
    let wₜ : Ω → ℝ := fun o => Real.exp (φₜ o)
    let mₜ : ℝ := ∫ o, wₜ o ∂μ
    let Lₜ : Ω → ℝ := fun o => wₜ o / mₜ
    let νₜ : Measure Ω := μ.withDensity (fun o => ENNReal.ofReal (Lₜ o))
    let Iₜ : ℝ := mₜ ^ n
    let Rₜ : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Real.exp (∑ j ∈ Finset.univ.erase i, φₜ (ξ j)) / Iₜ
    let capₜ : (Fin n → Ω) → Fin n → ℝ := fun ξ i => min |a * gₜ (ξ i)| 1
    let eₜ : (Fin n → Ω) → Fin n → Fin n → ℝ := fun ξ j k => rₜ (ξ j) (ξ k)
    let Fₜ : (Fin n → Ω) → ℝ := fun ξ => Shao.OQ5.P35.unorderedPairSum (eₜ ξ)
    let Fdelₜ : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Shao.OQ5.P35.unorderedPairSum
        (Shao.OQ6.ResidualDeletion.eraseIncident (eₜ ξ) i)
    let ψₜ : (Fin n → Ω) → Fin n → ℝ := fun ξ j =>
      Shao.OQ6.ResidualDeletion.rowSum (eₜ ξ) j
    let ψdelₜ : (Fin n → Ω) → Fin n → Fin n → ℝ := fun ξ i j =>
      Shao.OQ6.ResidualDeletion.rowSum
        (Shao.OQ6.ResidualDeletion.eraseIncident (eₜ ξ) i) j
    let Λsqₜ : (Fin n → Ω) → ℝ := fun ξ => ∑ j : Fin n, ψₜ ξ j ^ 2
    let Λdelsqₜ : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      ∑ j : Fin n, ψdelₜ ξ i j ^ 2
    let D₁ₜ : (Fin n → Ω) → ℝ := fun ξ =>
      Fₜ ξ / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
    let D₁delₜ : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Fdelₜ ξ i / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
    let crossₜ : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      ∑ j ∈ Finset.univ.erase i,
        2 * rₜ (ξ i) (ξ j) * (ψₜ ξ j - rₜ (ξ i) (ξ j))
    have aux := scaled_centered_kernel_model μ g hg hg2 hgmean hgsecond
      r hr hr2 hrsymm hrcan t ht.le
    rcases aux with ⟨hkM, hk2, hkSymm, hkMean, hkSecond,
      hProjectionAE, hrPoint, hrAE, hEnergy, hRootEnergy⟩
    change Measurable (fun z : Ω × Ω => kₜ z.1 z.2) at hkM
    change MemLp (fun z : Ω × Ω => kₜ z.1 z.2) 2 (μ.prod μ) at hk2
    change (∀ o y, kₜ o y = kₜ y o) at hkSymm
    change (∫ z : Ω × Ω, kₜ z.1 z.2 ∂(μ.prod μ)) = 0 at hkMean
    change (∫ o, (∫ y, kₜ o y ∂μ) ^ 2 ∂μ) = 1 at hkSecond
    change gₜ =ᵐ[μ] g at hProjectionAE
    change (∀ o y, gₜ o = g o → gₜ y = g y → rₜ o y = t * r o y) at hrPoint
    change Real.sqrt vₜ = t * ρr at hRootEnergy
    have hWeightAE : wₜ =ᵐ[μ] w := by
      filter_upwards [hProjectionAE] with o ho
      change Real.exp (a * gₜ o - (a * gₜ o) ^ 2 / 2) =
        Real.exp (a * g o - (a * g o) ^ 2 / 2)
      rw [ho]
    have hMassEq : mₜ = m := integral_congr_ae hWeightAE
    have hDensityAE : Lₜ =ᵐ[μ] L := by
      filter_upwards [hWeightAE] with o ho
      change wₜ o / mₜ = w o / m
      rw [ho, hMassEq]
    have hTiltEq : νₜ = ρ := by
      apply withDensity_congr_ae
      filter_upwards [hDensityAE] with o ho
      rw [ho]
    have hSampleAE : ∀ᵐ ξ ∂P₀, ∀ j : Fin n, gₜ (ξ j) = g (ξ j) := by
      rw [ae_all_iff]
      intro j
      exact (measurePreserving_eval (μ := fun _ : Fin n => μ) j).quasiMeasurePreserving.ae
        hProjectionAE
    have hstats (ξ : Fin n → Ω) (hξ : ∀ j : Fin n, gₜ (ξ j) = g (ξ j)) :
        (∀ i, Rₜ ξ i = R ξ i) ∧
        (∀ i, capₜ ξ i = cap ξ i) ∧
        Fₜ ξ = t * F ξ ∧
        (∀ i, Fdelₜ ξ i = t * Fdel ξ i) ∧
        (∀ j, ψₜ ξ j = t * ψ ξ j) ∧
        (∀ i j, ψdelₜ ξ i j = t * ψdel ξ i j) ∧
        Λsqₜ ξ = t ^ 2 * Λsq ξ ∧
        (∀ i, Λdelsqₜ ξ i = t ^ 2 * Λdelsq ξ i) ∧
        D₁ₜ ξ = t * D₁ ξ ∧
        (∀ i, D₁delₜ ξ i = t * D₁del ξ i) ∧
        (∀ i, crossₜ ξ i = t ^ 2 * cross ξ i) := by
      have hrij (j k : Fin n) : rₜ (ξ j) (ξ k) = t * r (ξ j) (ξ k) :=
        hrPoint (ξ j) (ξ k) (hξ j) (hξ k)
      have hEdge (j k : Fin n) : eₜ ξ j k = t * e ξ j k := hrij j k
      have hErase (i j k : Fin n) :
          Shao.OQ6.ResidualDeletion.eraseIncident (eₜ ξ) i j k =
            t * Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i j k := by
        dsimp only [Shao.OQ6.ResidualDeletion.eraseIncident]
        split_ifs with hij
        · simp only [mul_zero]
        · exact hEdge j k
      have hR (i : Fin n) : Rₜ ξ i = R ξ i := by
        have hSum : (∑ j ∈ Finset.univ.erase i, φₜ (ξ j)) =
            ∑ j ∈ Finset.univ.erase i, φ (ξ j) := by
          apply Finset.sum_congr rfl
          intro j hj
          dsimp only [φₜ, φ]
          rw [hξ j]
        change Real.exp (∑ j ∈ Finset.univ.erase i, φₜ (ξ j)) / mₜ ^ n =
          Real.exp (∑ j ∈ Finset.univ.erase i, φ (ξ j)) / m ^ n
        rw [hSum, hMassEq]
      have hCap (i : Fin n) : capₜ ξ i = cap ξ i := by
        change min |a * gₜ (ξ i)| 1 = min |a * g (ξ i)| 1
        rw [hξ i]
      have hF : Fₜ ξ = t * F ξ := by
        simp only [Fₜ, F, Shao.OQ5.P35.unorderedPairSum]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hjk : j < k
        · simp only [if_pos hjk, hEdge]
        · simp only [if_neg hjk, mul_zero]
      have hFd (i : Fin n) : Fdelₜ ξ i = t * Fdel ξ i := by
        simp only [Fdelₜ, Fdel, Shao.OQ5.P35.unorderedPairSum]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hjk : j < k
        · simp only [if_pos hjk, hErase]
        · simp only [if_neg hjk, mul_zero]
      have hψ (j : Fin n) : ψₜ ξ j = t * ψ ξ j := by
        simp only [ψₜ, ψ, Shao.OQ6.ResidualDeletion.rowSum]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        exact hEdge j k
      have hψd (i j : Fin n) : ψdelₜ ξ i j = t * ψdel ξ i j := by
        simp only [ψdelₜ, ψdel, Shao.OQ6.ResidualDeletion.rowSum]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        exact hErase i j k
      have hΛ : Λsqₜ ξ = t ^ 2 * Λsq ξ := by
        change (∑ j : Fin n, ψₜ ξ j ^ 2) = t ^ 2 * ∑ j : Fin n, ψ ξ j ^ 2
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [hψ j]
        ring
      have hΛd (i : Fin n) : Λdelsqₜ ξ i = t ^ 2 * Λdelsq ξ i := by
        change (∑ j : Fin n, ψdelₜ ξ i j ^ 2) = t ^ 2 * ∑ j : Fin n, ψdel ξ i j ^ 2
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [hψd i j]
        ring
      have hD : D₁ₜ ξ = t * D₁ ξ := by
        dsimp only [D₁ₜ, D₁]
        rw [hF]
        ring
      have hDd (i : Fin n) : D₁delₜ ξ i = t * D₁del ξ i := by
        dsimp only [D₁delₜ, D₁del]
        rw [hFd i]
        ring
      have hX (i : Fin n) : crossₜ ξ i = t ^ 2 * cross ξ i := by
        dsimp only [crossₜ, cross]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [hrij i j, hψ j]
        ring
      exact ⟨hR, hCap, hF, hFd, hψ, hψd, hΛ, hΛd, hD, hDd, hX⟩
    have hDScale (i : Fin n) :
        (∫ ξ, Rₜ ξ i * capₜ ξ i * |D₁ₜ ξ - D₁delₜ ξ i| ∂P₀) =
          t * (∫ ξ, R ξ i * cap ξ i * |D₁ ξ - D₁del ξ i| ∂P₀) := by
      calc
        _ = ∫ ξ, t * (R ξ i * cap ξ i * |D₁ ξ - D₁del ξ i|) ∂P₀ := by
          apply integral_congr_ae
          filter_upwards [hSampleAE] with ξ hξ
          rcases hstats ξ hξ with ⟨hR, hCap, hF, hFd, hψ, hψd, hΛ, hΛd, hD, hDd, hX⟩
          rw [hR i, hCap i, hD, hDd i, ← mul_sub, abs_mul, abs_of_pos ht]
          ring
        _ = _ := integral_const_mul _ _
    have hXScale (i : Fin n) :
        (∫ ξ, Rₜ ξ i * capₜ ξ i * |crossₜ ξ i| ∂P₀) =
          t ^ 2 * (∫ ξ, R ξ i * cap ξ i * |cross ξ i| ∂P₀) := by
      calc
        _ = ∫ ξ, t ^ 2 * (R ξ i * cap ξ i * |cross ξ i|) ∂P₀ := by
          apply integral_congr_ae
          filter_upwards [hSampleAE] with ξ hξ
          rcases hstats ξ hξ with ⟨hR, hCap, hF, hFd, hψ, hψd, hΛ, hΛd, hD, hDd, hX⟩
          rw [hR i, hCap i, hX i, abs_mul, abs_of_nonneg (sq_nonneg t)]
          ring
        _ = _ := integral_const_mul _ _
    have hΛScale (i : Fin n) :
        (∫ ξ, Rₜ ξ i * capₜ ξ i * |Λsqₜ ξ - Λdelsqₜ ξ i| ∂P₀) =
          t ^ 2 * (∫ ξ, R ξ i * cap ξ i * |Λsq ξ - Λdelsq ξ i| ∂P₀) := by
      calc
        _ = ∫ ξ, t ^ 2 * (R ξ i * cap ξ i * |Λsq ξ - Λdelsq ξ i|) ∂P₀ := by
          apply integral_congr_ae
          filter_upwards [hSampleAE] with ξ hξ
          rcases hstats ξ hξ with ⟨hR, hCap, hF, hFd, hψ, hψd, hΛ, hΛd, hD, hDd, hX⟩
          rw [hR i, hCap i, hΛ, hΛd i, ← mul_sub, abs_mul,
            abs_of_nonneg (sq_nonneg t)]
          ring
        _ = _ := integral_const_mul _ _
    have scaled := Shao.OQ6.WeightedDeletionMoments.actual_quadratic_weighted_deletion_bounds
      μ kₜ hkM hk2 hkSymm hkMean hkSecond n hn3 x hx hwindow
    rcases scaled with ⟨hsgn, hDti, hDtB, hXti, hXtB, hΛti, hΛtB⟩
    change (∑ i : Fin n,
      ∫ ξ, Rₜ ξ i * capₜ ξ i * |D₁ₜ ξ - D₁delₜ ξ i| ∂P₀) ≤
        4 * Real.sqrt 2 * C * (1 + Real.sqrt vₜ) * (1 + x) ^ 2 /
          Real.sqrt (n : ℝ) at hDtB
    change (∑ i : Fin n,
      ∫ ξ, Rₜ ξ i * capₜ ξ i * |crossₜ ξ i| ∂P₀) ≤
        16 * C ^ 2 * (1 + Real.sqrt vₜ) ^ 2 * (n : ℝ) ^ 2 * x * (1 + x) at hXtB
    change (∑ i : Fin n,
      ∫ ξ, Rₜ ξ i * capₜ ξ i * |Λsqₜ ξ - Λdelsqₜ ξ i| ∂P₀) ≤
        24 * C ^ 2 * (1 + Real.sqrt vₜ) ^ 2 * (n : ℝ) ^ 2 * (1 + x) ^ 2 at hΛtB
    refine ⟨?_, ?_, ?_⟩
    · calc
        t * A_D = ∑ i : Fin n,
            ∫ ξ, Rₜ ξ i * capₜ ξ i * |D₁ₜ ξ - D₁delₜ ξ i| ∂P₀ := by
          simp_rw [hDScale]
          exact Finset.mul_sum _ _ _
        _ ≤ _ := hDtB
        _ = B_D * (1 + t * ρr) := by
          rw [hRootEnergy]
          dsimp only [B_D]
          ring
    · calc
        t ^ 2 * A_X = ∑ i : Fin n,
            ∫ ξ, Rₜ ξ i * capₜ ξ i * |crossₜ ξ i| ∂P₀ := by
          simp_rw [hXScale]
          exact Finset.mul_sum _ _ _
        _ ≤ _ := hXtB
        _ = B_X * (1 + t * ρr) ^ 2 := by
          rw [hRootEnergy]
          dsimp only [B_X]
          ring
    · calc
        t ^ 2 * A_Λ = ∑ i : Fin n,
            ∫ ξ, Rₜ ξ i * capₜ ξ i * |Λsqₜ ξ - Λdelsqₜ ξ i| ∂P₀ := by
          simp_rw [hΛScale]
          exact Finset.mul_sum _ _ _
        _ ≤ _ := hΛtB
        _ = B_Λ * (1 + t * ρr) ^ 2 := by
          rw [hRootEnergy]
          dsimp only [B_Λ]
          ring
  have hDB : A_D ≤ B_D * ρr := by
    simpa only [pow_one] using remove_positive_scale_offset A_D B_D ρr 1
      (fun t ht => by simpa only [pow_one] using (hscaled t ht).1)
  have hXB : A_X ≤ B_X * ρr ^ 2 :=
    remove_positive_scale_offset A_X B_X ρr 2 (fun t ht => (hscaled t ht).2.1)
  have hΛB : A_Λ ≤ B_Λ * ρr ^ 2 :=
    remove_positive_scale_offset A_Λ B_Λ ρr 2 (fun t ht => (hscaled t ht).2.2)
  have hDfinal : (∑ i : Fin n,
      ∫ ξ, R ξ i * cap ξ i * |D₁ ξ - D₁del ξ i| ∂P₀) ≤
        4 * Real.sqrt 2 * C * ρr * (1 + x) ^ 2 / Real.sqrt (n : ℝ) := by
    calc
      _ ≤ B_D * ρr := hDB
      _ = _ := by dsimp only [B_D]; ring
  have hXfinal : (∑ i : Fin n,
      ∫ ξ, R ξ i * cap ξ i * |cross ξ i| ∂P₀) ≤
        16 * C ^ 2 * ρr ^ 2 * (n : ℝ) ^ 2 * x * (1 + x) := by
    calc
      _ ≤ B_X * ρr ^ 2 := hXB
      _ = _ := by dsimp only [B_X]; ring
  have hΛfinal : (∑ i : Fin n,
      ∫ ξ, R ξ i * cap ξ i * |Λsq ξ - Λdelsq ξ i| ∂P₀) ≤
        24 * C ^ 2 * ρr ^ 2 * (n : ℝ) ^ 2 * (1 + x) ^ 2 := by
    calc
      _ ≤ B_Λ * ρr ^ 2 := hΛB
      _ = _ := by dsimp only [B_Λ]; ring
  have hEdgeM (j k : Fin n) : Measurable (fun ξ : Fin n → Ω => e ξ j k) := by
    have hpair : Measurable (fun ξ : Fin n → Ω => (ξ j, ξ k)) :=
      (measurable_pi_apply j).prodMk (measurable_pi_apply k)
    simpa only [e, Function.comp_def] using hr.comp hpair
  have hEraseM (i j k : Fin n) : Measurable
      (fun ξ : Fin n → Ω => Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i j k) := by
    by_cases hjk : j = i ∨ k = i
    · simpa only [Shao.OQ6.ResidualDeletion.eraseIncident, if_pos hjk] using
        (measurable_const : Measurable (fun _ : Fin n → Ω => (0 : ℝ)))
    · simpa only [Shao.OQ6.ResidualDeletion.eraseIncident, if_neg hjk] using hEdgeM j k
  have hFM : Measurable F := by
    apply Finset.measurable_sum
    intro j hj
    apply Finset.measurable_sum
    intro k hk
    by_cases hjk : j < k
    · simpa only [if_pos hjk] using hEdgeM j k
    · simpa only [if_neg hjk] using
        (measurable_const : Measurable (fun _ : Fin n → Ω => (0 : ℝ)))
  have hFdelM (i : Fin n) : Measurable (fun ξ => Fdel ξ i) := by
    apply Finset.measurable_sum
    intro j hj
    apply Finset.measurable_sum
    intro k hk
    by_cases hjk : j < k
    · simpa only [if_pos hjk] using hEraseM i j k
    · simpa only [if_neg hjk] using
        (measurable_const : Measurable (fun _ : Fin n → Ω => (0 : ℝ)))
  have hDM : Measurable D₁ := hFM.div_const _
  have hDdelM (i : Fin n) : Measurable (fun ξ => D₁del ξ i) := (hFdelM i).div_const _
  have hφM : Measurable φ :=
    (hg.const_mul a).sub (((hg.const_mul a).pow_const (2 : ℕ)).div_const 2)
  have hRM (i : Fin n) : Measurable (fun ξ => R ξ i) := by
    have hSumM : Measurable (fun ξ : Fin n → Ω =>
        ∑ j ∈ Finset.univ.erase i, φ (ξ j)) :=
      Finset.measurable_sum _ (fun j hj => hφM.comp (measurable_pi_apply j))
    exact hSumM.exp.div_const I
  have hcapM (i : Fin n) : Measurable (fun ξ => cap ξ i) := by
    simpa only [cap, Real.norm_eq_abs, Function.comp_apply] using
      ((hg.comp (measurable_pi_apply i)).const_mul a).norm.min measurable_const
  have hmpos : 0 < m := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hmlo
  have hIpos : 0 < I := pow_pos hmpos n
  have hR0 (ξ : Fin n → Ω) (i : Fin n) : 0 ≤ R ξ i :=
    div_nonneg (Real.exp_pos _).le hIpos.le
  have hcap0 (ξ : Fin n → Ω) (i : Fin n) : 0 ≤ cap ξ i :=
    le_min (abs_nonneg _) (by norm_num)
  have hAbsPoint (ξ : Fin n → Ω) (i : Fin n) :
      R ξ i * cap ξ i * abs (abs (D₁ ξ) - abs (D₁del ξ i)) ≤
        R ξ i * cap ξ i * |D₁ ξ - D₁del ξ i| :=
    mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub (D₁ ξ) (D₁del ξ i))
      (mul_nonneg (hR0 ξ i) (hcap0 ξ i))
  have hAbsI (i : Fin n) : Integrable
      (fun ξ => R ξ i * cap ξ i * abs (abs (D₁ ξ) - abs (D₁del ξ i))) P₀ := by
    have hAbsM : Measurable (fun ξ => abs (abs (D₁ ξ) - abs (D₁del ξ i))) := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using
        ((hDM.norm).sub ((hDdelM i).norm)).norm
    apply (hDI i).mono' (((hRM i).mul (hcapM i)).mul hAbsM).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ξ => by
      change |R ξ i * cap ξ i * abs (abs (D₁ ξ) - abs (D₁del ξ i))| ≤ _
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg (hR0 ξ i) (hcap0 ξ i)) (abs_nonneg _))]
      exact hAbsPoint ξ i
  have hAbsB : (∑ i : Fin n,
      ∫ ξ, R ξ i * cap ξ i * abs (abs (D₁ ξ) - abs (D₁del ξ i)) ∂P₀) ≤
        4 * Real.sqrt 2 * C * ρr * (1 + x) ^ 2 / Real.sqrt (n : ℝ) := by
    exact (Finset.sum_le_sum (fun i hi =>
      integral_mono (hAbsI i) (hDI i) (fun ξ => hAbsPoint ξ i))).trans hDfinal
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hdpos : 0 < (n : ℝ) - 2 := by linarith only [hn4]
  have hJid (ξ : Fin n → Ω) : J ξ = Λsq ξ / ((n : ℝ) - 2) ^ 2 := by
    simp only [J, u, div_pow, ← Finset.sum_div, Λsq]
  have hJdelid (ξ : Fin n → Ω) (i : Fin n) :
      Jdel ξ i = Λdelsq ξ i / ((n : ℝ) - 2) ^ 2 := by
    simp only [Jdel, udel, div_pow, ← Finset.sum_div, Λdelsq]
  have hJdiff (ξ : Fin n → Ω) (i : Fin n) :
      J ξ - Jdel ξ i = (Λsq ξ - Λdelsq ξ i) / ((n : ℝ) - 2) ^ 2 := by
    rw [hJid, hJdelid, sub_div]
  have hJpoint (ξ : Fin n → Ω) (i : Fin n) :
      R ξ i * cap ξ i * |J ξ - Jdel ξ i| =
        (R ξ i * cap ξ i * |Λsq ξ - Λdelsq ξ i|) / ((n : ℝ) - 2) ^ 2 := by
    rw [hJdiff, abs_div, abs_of_nonneg (sq_nonneg ((n : ℝ) - 2))]
    ring
  have hJI (i : Fin n) : Integrable
      (fun ξ => R ξ i * cap ξ i * |J ξ - Jdel ξ i|) P₀ := by
    exact ((hΛI i).div_const (((n : ℝ) - 2) ^ 2)).congr
      (Filter.Eventually.of_forall fun ξ => (hJpoint ξ i).symm)
  have hJB : (∑ i : Fin n,
      ∫ ξ, R ξ i * cap ξ i * |J ξ - Jdel ξ i| ∂P₀) ≤
        96 * C ^ 2 * ρr ^ 2 * (1 + x) ^ 2 := by
    calc
      _ = (∑ i : Fin n,
          ∫ ξ, R ξ i * cap ξ i * |Λsq ξ - Λdelsq ξ i| ∂P₀) /
            ((n : ℝ) - 2) ^ 2 := by
        simp_rw [hJpoint, integral_div]
        rw [Finset.sum_div]
      _ ≤ (24 * C ^ 2 * ρr ^ 2 * (n : ℝ) ^ 2 * (1 + x) ^ 2) /
          ((n : ℝ) - 2) ^ 2 :=
        div_le_div_of_nonneg_right hΛfinal (sq_nonneg _)
      _ ≤ 96 * C ^ 2 * ρr ^ 2 * (1 + x) ^ 2 := by
        apply (div_le_iff₀ (sq_pos_of_pos hdpos)).mpr
        have hfour : (n : ℝ) ^ 2 ≤ 4 * ((n : ℝ) - 2) ^ 2 := by
          nlinarith only [hn4, sq_nonneg ((n : ℝ) - 4)]
        have hcommon0 : 0 ≤ 24 * C ^ 2 * ρr ^ 2 * (1 + x) ^ 2 := by positivity
        have hf := mul_le_mul_of_nonneg_left hfour hcommon0
        nlinarith only [hf]
  exact ⟨hsigned, hDI, hDfinal, hXI, hXfinal, hΛI, hΛfinal,
    hAbsI, hAbsB, hJI, hJB⟩

end

end Shao.OQ6.RhoWeightedDeletionMoments
