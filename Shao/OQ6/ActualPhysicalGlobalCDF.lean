import Shao.OQ6.ActualPhysicalCompactCDF

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Shao.OQ6.ActualPhysicalGlobalCDF

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

universe u
private theorem nonnegative_physical_threshold_gaussian_shift
    (n : ℕ) (hn : 3 ≤ n) :
    let N : ℝ := (n : ℝ)
    let c_n : ℝ := 4 * (N - 1) / (N - 2) ^ 2
    let τ : ℝ → ℝ := fun x => x / Real.sqrt (1 + c_n * x ^ 2)
    ∀ x : ℝ, 0 ≤ x →
      0 ≤ τ x ∧ τ x ≤ x ∧
        |Shao.OQ4.standardNormalCDF (τ x) - Shao.OQ4.standardNormalCDF x| ≤
          12 * x ^ 3 / N := by
  classical
  let N : ℝ := (n : ℝ)
  let c_n : ℝ := 4 * (N - 1) / (N - 2) ^ 2
  let τ : ℝ → ℝ := fun x => x / Real.sqrt (1 + c_n * x ^ 2)
  let H0 : Fin n → Fin n → ℝ := fun _ _ => 0
  change ∀ x : ℝ, 0 ≤ x →
    0 ≤ τ x ∧ τ x ≤ x ∧
      |Shao.OQ4.standardNormalCDF (τ x) - Shao.OQ4.standardNormalCDF x| ≤
        12 * x ^ 3 / N
  have hN3 : (3 : ℝ) ≤ N := by
    dsimp only [N]
    exact_mod_cast hn
  have hN : 0 < N := by linarith only [hN3]
  have hN2 : 0 < N - 2 := by linarith only [hN3]
  have hfinite :=
    Shao.OQ6.PhysicalCompact.finite_physical_studentizer_conversion
      H0 (by intro i j; rfl) hn
  dsimp only at hfinite
  rcases hfinite with ⟨hc_n, _, _, _, _, hτabs, _, _⟩
  change 0 < c_n at hc_n
  change (∀ x : ℝ,
    |τ x| ≤ |x| ∧ |τ x - x| ≤ c_n * |x| ^ 3 / 2) at hτabs
  have hcN : c_n ≤ 24 / N := by
    change 4 * (N - 1) / (N - 2) ^ 2 ≤ 24 / N
    apply (div_le_div_iff₀ (sq_pos_of_pos hN2) hN).2
    have hp := mul_nonneg (sub_nonneg.mpr hN3)
      (by linarith only [hN3] : 0 ≤ 5 * N - 8)
    nlinarith only [hp]
  intro x hx
  have hτ0 : 0 ≤ τ x := by
    dsimp only [τ]
    exact div_nonneg hx (Real.sqrt_nonneg _)
  have hτx : τ x ≤ x := by
    calc
      τ x ≤ |τ x| := le_abs_self _
      _ ≤ |x| := (hτabs x).1
      _ = x := abs_of_nonneg hx
  refine ⟨hτ0, hτx, ?_⟩
  calc
    |Shao.OQ4.standardNormalCDF (τ x) - Shao.OQ4.standardNormalCDF x|
        ≤ |τ x - x| := Shao.OQ4.standardNormalCDF_lipschitz _ _
    _ ≤ c_n * |x| ^ 3 / 2 := (hτabs x).2
    _ = c_n * x ^ 3 / 2 := by rw [abs_of_nonneg hx]
    _ ≤ (24 / N) * x ^ 3 / 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcN (pow_nonneg hx 3)) (by norm_num)
    _ = 12 * x ^ 3 / N := by ring

theorem actual_physical_global_cdf_tail_rpow_rate
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
          ∀ x : ℝ, 0 ≤ x →
            let error : ℝ := K *
              (β * Real.rpow (1 + x) p / Real.rpow N ((p - 2) / 2) +
                (1 + x) * s / q + x ^ 3 / N)
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
  obtain ⟨c169, hc169, h169⟩ := Shao.OQ6.ActualUncenteredCompactCDF.actual_uncentered_compact_cdf_tail_bounds_nonnegative C hSZ μ h hh hh2 hhsymm hcenter hprojectionsecond
  obtain ⟨c147, hc147, h147⟩ := Shao.OQ6.PhysicalCompact.actual_physical_zero_probability_and_compact_transport μ h hh hh2 hhsymm hcenter hprojectionsecond
  let c : ℝ := min c169 c147
  have hc : 0 < c := by
    dsimp only [c]
    exact lt_min hc169 hc147
  have hC : 0 < C := lt_trans (by norm_num : (0 : ℝ) < 1) hSZ.1
  have hdivc : 0 ≤ 2 / c := div_nonneg (by norm_num) hc.le
  let K : ℝ := 65553 * C + 33117 + 12 + 2 / c
  have hK : 0 < K := by
    dsimp only [K]
    nlinarith only [hC, hdivc]
  have hKA : C ≤ K := by
    dsimp only [K]
    nlinarith only [hC, hdivc]
  have hKB : 65552 * C + 33105 + 2 / c ≤ K := by
    dsimp only [K]
    nlinarith only [hC]
  have hKD : (12 : ℝ) ≤ K := by
    dsimp only [K]
    nlinarith only [hC, hdivc]
  have hdata :=
    Shao.OQ6.ActualQuadraticTiltMoments.actual_quadratic_source_moments
      μ h hh hh2 hhsymm hcenter hprojectionsecond 3 (by norm_num) 0
        (by norm_num) (by positivity)
  dsimp only at hdata
  rcases hdata with ⟨hg, hg2, _⟩
  change Measurable g at hg
  change MemLp g 2 μ at hg2
  change Integrable (fun o => Real.rpow |g o| p) μ at hgp
  have hs : 1 ≤ s := by
    change 1 ≤ 1 + Real.sqrt v
    exact le_add_of_nonneg_right (Real.sqrt_nonneg v)
  have hs0 : 0 ≤ s := by linarith only [hs]
  have hβ : 0 ≤ β := by
    apply integral_nonneg
    intro o
    change (0 : ℝ) ≤ Real.rpow |g o| p
    simpa only [Real.rpow_eq_pow] using
      Real.rpow_nonneg (abs_nonneg (g o)) p
  refine ⟨K, hK, ?_⟩
  intro n hn
  let N : ℝ := (n : ℝ)
  let q : ℝ := Real.sqrt N
  let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  let U : (Fin n → Ω) → ℝ := fun ξ => Shao.OQ6.FiniteRows.uStatistic (fun i j => h (ξ i) (ξ j))
  let R2 : (Fin n → Ω) → ℝ := fun ξ => Shao.OQ6.FiniteRows.jackknifeSq (fun i j => h (ξ i) (ξ j))
  let T : (Fin n → Ω) → ℝ := fun ξ => if 0 < R2 ξ then q * U ξ / Real.sqrt (R2 ξ) else 0
  let J : (Fin n → Ω) → ℝ := fun ξ => Shao.OQ6.FiniteRows.uncenteredSq (fun i j => h (ξ i) (ξ j))
  let Tstar : (Fin n → Ω) → ℝ := fun ξ => if 0 < J ξ then q * U ξ / (2 * Real.sqrt (J ξ)) else 0
  let Z : Set (Fin n → Ω) := {ξ | R2 ξ = 0}
  let c_n : ℝ := 4 * (N - 1) / (N - 2) ^ 2
  let τ : ℝ → ℝ := fun x => x / Real.sqrt (1 + c_n * x ^ 2)
  let zeroFee : ℝ := Real.exp (-c147 * N) + ((1 / 16 : ℝ) + 16720 * s) / q
  have hN3 : (3 : ℝ) ≤ N := by
    dsimp only [N]
    exact_mod_cast hn
  have hN : 0 < N := by linarith only [hN3]
  have hq : 0 < q := Real.sqrt_pos.mpr hN
  have hqsq : q ^ 2 = N := Real.sq_sqrt hN.le
  have hq1 : 1 ≤ q := by
    by_contra hnot
    have hlt : q < 1 := lt_of_not_ge hnot
    have hprod := mul_pos (sub_pos.mpr hlt)
      (by linarith only [hq] : 0 < 1 + q)
    nlinarith only [hprod, hqsq, hN3]
  have hqN : q ≤ N := by
    have hprod := mul_nonneg hq.le (sub_nonneg.mpr hq1)
    nlinarith only [hprod, hqsq]
  have hden : 0 < Real.rpow N ((p - 2) / 2) := Real.rpow_pos_of_pos hN _
  have hsq : 0 ≤ s / q := div_nonneg hs0 hq.le
  have hunit : 1 / q ≤ s / q := div_le_div_of_nonneg_right hs hq.le
  have hexp169 : Real.exp (-c169 * N) ≤ Real.exp (-c * N) := by
    apply Real.exp_le_exp.mpr
    have hprod := mul_le_mul_of_nonneg_right
      (show c ≤ c169 from min_le_left c169 c147) hN.le
    nlinarith only [hprod]
  have hexp147 : Real.exp (-c147 * N) ≤ Real.exp (-c * N) := by
    apply Real.exp_le_exp.mpr
    have hprod := mul_le_mul_of_nonneg_right
      (show c ≤ c147 from min_le_right c169 c147) hN.le
    nlinarith only [hprod]
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
  have h147n := h147 n hn
  dsimp only at h147n
  rcases h147n with
    ⟨_, _, _, hT, _, _, _, _, _, _, _, _, _, hZbound,
      _, _, _, _, hdiscclosed, hdiscopen, _, _⟩
  change Measurable T at hT
  change P₀.real Z ≤ zeroFee at hZbound
  change (∀ x : ℝ,
    |P₀.real {ξ | T ξ ≤ x} - P₀.real {ξ | Tstar ξ ≤ τ x}| ≤ P₀.real Z)
    at hdiscclosed
  change (∀ x : ℝ,
    |P₀.real {ξ | T ξ < x} - P₀.real {ξ | Tstar ξ < τ x}| ≤ P₀.real Z)
    at hdiscopen
  have h169n := h169 n hn
  dsimp only at h169n
  rcases h169n with ⟨_, h169bound⟩
  have hthreshold := nonnegative_physical_threshold_gaussian_shift n hn
  dsimp only at hthreshold
  change (∀ x : ℝ, 0 ≤ x →
    0 ≤ τ x ∧ τ x ≤ x ∧
      |Shao.OQ4.standardNormalCDF (τ x) - Shao.OQ4.standardNormalCDF x| ≤
        12 * x ^ 3 / N) at hthreshold
  refine ⟨hT, ?_⟩
  intro x hx
  let y : ℝ := τ x
  let Lcompact : ℝ := N * (∫ o, Shao.truncationF ((1 + y) * (g o / q)) ∂μ)
  let A : ℝ := β * Real.rpow (1 + x) p / Real.rpow N ((p - 2) / 2)
  let B : ℝ := (1 + x) * s / q
  let D : ℝ := x ^ 3 / N
  let E169 : ℝ := C * (Lcompact + 16 * (1 + 4096) * (1 + y) * s / q) + Real.exp (-c169 * N) + ((1 / 16 : ℝ) + 16384 * s) / q
  let fee : ℝ := C * (A + 16 * (1 + 4096) * B) + 2 * Real.exp (-c * N) + ((1 / 8 : ℝ) + 33104 * s) / q + 12 * D
  let error : ℝ := K * (β * Real.rpow (1 + x) p / Real.rpow N ((p - 2) / 2) + (1 + x) * s / q + x ^ 3 / N)
  change
    |P₀.real {ξ | T ξ ≤ x} - Shao.OQ4.standardNormalCDF x| ≤ error ∧
    |P₀.real {ξ | T ξ < x} - Shao.OQ4.standardNormalCDF x| ≤ error ∧
    |P₀.real {ξ | x < T ξ} - (1 - Shao.OQ4.standardNormalCDF x)| ≤ error ∧
    |P₀.real {ξ | x ≤ T ξ} - (1 - Shao.OQ4.standardNormalCDF x)| ≤ error
  have hthresholdx := hthreshold x hx
  have hy : 0 ≤ y := hthresholdx.1
  have hyx : y ≤ x := hthresholdx.2.1
  have hgauss0 := hthresholdx.2.2
  change |Shao.OQ4.standardNormalCDF y - Shao.OQ4.standardNormalCDF x| ≤
    12 * x ^ 3 / N at hgauss0
  have hgauss :
      |Shao.OQ4.standardNormalCDF y - Shao.OQ4.standardNormalCDF x| ≤
        12 * D := by
    calc
      |Shao.OQ4.standardNormalCDF y - Shao.OQ4.standardNormalCDF x|
          ≤ 12 * x ^ 3 / N := hgauss0
      _ = 12 * D := by dsimp only [D]; ring
  have hpower : Real.rpow (1 + y) p ≤ Real.rpow (1 + x) p :=
    Real.rpow_le_rpow (by linarith only [hy])
      (by linarith only [hyx]) (by linarith only [hp2])
  have hmoment :=
    Shao.OQ6.ActualPhysicalCompactCDF.normalized_observation_truncation_budget_le_rpow_moment
      μ g hg hg2 p hp2.le hp3 hgp n (le_trans (by norm_num : 1 ≤ 3) hn) y hy
  dsimp only at hmoment
  have hL := hmoment.2.2
  change Lcompact ≤ β * Real.rpow (1 + y) p /
    Real.rpow N ((p - 2) / 2) at hL
  have hLA : Lcompact ≤ A := by
    calc
      Lcompact ≤ β * Real.rpow (1 + y) p /
          Real.rpow N ((p - 2) / 2) := hL
      _ ≤ β * Real.rpow (1 + x) p / Real.rpow N ((p - 2) / 2) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpower hβ) hden.le
      _ = A := rfl
  have hpowx : 0 ≤ Real.rpow (1 + x) p := by
    simpa only [Real.rpow_eq_pow] using
      Real.rpow_nonneg (by linarith only [hx] : 0 ≤ 1 + x) p
  have hA : 0 ≤ A := div_nonneg (mul_nonneg hβ hpowx) hden.le
  have hB : 0 ≤ B :=
    div_nonneg (mul_nonneg (by linarith only [hx]) hs0) hq.le
  have hD : 0 ≤ D := div_nonneg (pow_nonneg hx 3) hN.le
  have hBbase : s / q ≤ B := by
    change s / q ≤ (1 + x) * s / q
    apply div_le_div_of_nonneg_right _ hq.le
    have hmul := mul_le_mul_of_nonneg_right
      (by linarith only [hx] : (1 : ℝ) ≤ 1 + x) hs0
    simpa only [one_mul] using hmul
  have hresy : (1 + y) * s / q ≤ B := by
    change (1 + y) * s / q ≤ (1 + x) * s / q
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith only [hyx]) hs0) hq.le
  have hinside :
      Lcompact + 16 * (1 + 4096) * (1 + y) * s / q ≤
        A + 16 * (1 + 4096) * B := by
    calc
      Lcompact + 16 * (1 + 4096) * (1 + y) * s / q =
          Lcompact + (16 * (1 + 4096)) * ((1 + y) * s / q) := by ring
      _ ≤ A + (16 * (1 + 4096)) * B :=
        add_le_add hLA
          (mul_le_mul_of_nonneg_left hresy (by norm_num))
  have hanalytic := mul_le_mul_of_nonneg_left hinside hC.le
  have h169y := h169bound y hy
  rcases h169y with ⟨hclosed169, hopen169, _, _⟩
  change |P₀.real {ξ | Tstar ξ ≤ y} - Shao.OQ4.standardNormalCDF y| ≤ E169
    at hclosed169
  change |P₀.real {ξ | Tstar ξ < y} - Shao.OQ4.standardNormalCDF y| ≤ E169
    at hopen169
  have hpay : E169 + zeroFee + 12 * D ≤ fee := by
    have hfractions :
        ((1 / 16 : ℝ) + 16384 * s) / q +
          ((1 / 16 : ℝ) + 16720 * s) / q =
            ((1 / 8 : ℝ) + 33104 * s) / q := by ring
    have hexps :
        Real.exp (-c169 * N) + Real.exp (-c147 * N) ≤
          2 * Real.exp (-c * N) := by
      linarith only [hexp169, hexp147]
    calc
      E169 + zeroFee + 12 * D =
          C * (Lcompact + 16 * (1 + 4096) * (1 + y) * s / q) +
            (Real.exp (-c169 * N) + Real.exp (-c147 * N)) +
            (((1 / 16 : ℝ) + 16384 * s) / q +
              ((1 / 16 : ℝ) + 16720 * s) / q) + 12 * D := by
        dsimp only [E169, zeroFee]
        ring
      _ = C * (Lcompact + 16 * (1 + 4096) * (1 + y) * s / q) +
          (Real.exp (-c169 * N) + Real.exp (-c147 * N)) +
          ((1 / 8 : ℝ) + 33104 * s) / q + 12 * D := by rw [hfractions]
      _ ≤ C * (A + 16 * (1 + 4096) * B) +
          2 * Real.exp (-c * N) +
          ((1 / 8 : ℝ) + 33104 * s) / q + 12 * D := by
        linarith only [hanalytic, hexps]
      _ = fee := rfl
  have hexpB : 2 * Real.exp (-c * N) ≤ (2 / c) * B :=
    hexp.trans (mul_le_mul_of_nonneg_left hBbase hdivc)
  have h18 : (1 / 8 : ℝ) / q ≤ (1 / 8 : ℝ) * (s / q) := by
    have hmul := mul_le_mul_of_nonneg_left hunit
      (by norm_num : (0 : ℝ) ≤ 1 / 8)
    convert hmul using 1 <;> ring
  have hpoly : ((1 / 8 : ℝ) + 33104 * s) / q ≤ 33105 * B := by
    calc
      ((1 / 8 : ℝ) + 33104 * s) / q =
          (1 / 8 : ℝ) / q + 33104 * (s / q) := by ring
      _ ≤ (1 / 8 : ℝ) * (s / q) + 33104 * (s / q) := by
        linarith only [h18]
      _ ≤ 33105 * (s / q) := by linarith only [hsq]
      _ ≤ 33105 * B := mul_le_mul_of_nonneg_left hBbase (by norm_num)
  have hfeecoef :
      fee ≤ C * A + (65552 * C + 33105 + 2 / c) * B + 12 * D := by
    calc
      fee = C * A + 65552 * C * B + 2 * Real.exp (-c * N) +
          ((1 / 8 : ℝ) + 33104 * s) / q + 12 * D := by
        dsimp only [fee]
        ring
      _ ≤ C * A + 65552 * C * B + (2 / c) * B + 33105 * B +
          12 * D := by linarith only [hexpB, hpoly]
      _ = C * A + (65552 * C + 33105 + 2 / c) * B + 12 * D := by ring
  have hfee : fee ≤ error := by
    have hAmul := mul_le_mul_of_nonneg_right hKA hA
    have hBmul := mul_le_mul_of_nonneg_right hKB hB
    have hDmul := mul_le_mul_of_nonneg_right hKD hD
    calc
      fee ≤ C * A + (65552 * C + 33105 + 2 / c) * B + 12 * D := hfeecoef
      _ ≤ K * A + K * B + K * D := by linarith only [hAmul, hBmul, hDmul]
      _ = error := by
        dsimp only [error, A, B, D]
        ring
  have hclosed :
      |P₀.real {ξ | T ξ ≤ x} - Shao.OQ4.standardNormalCDF x| ≤ error := by
    have hd := hdiscclosed x
    change |P₀.real {ξ | T ξ ≤ x} - P₀.real {ξ | Tstar ξ ≤ y}| ≤
      P₀.real Z at hd
    have hfirst := abs_sub_le (P₀.real {ξ | T ξ ≤ x})
      (P₀.real {ξ | Tstar ξ ≤ y}) (Shao.OQ4.standardNormalCDF x)
    have hsecond := abs_sub_le (P₀.real {ξ | Tstar ξ ≤ y})
      (Shao.OQ4.standardNormalCDF y) (Shao.OQ4.standardNormalCDF x)
    have htransport :
        |P₀.real {ξ | T ξ ≤ x} - Shao.OQ4.standardNormalCDF x| ≤
          E169 + zeroFee + 12 * D := by
      linarith only [hfirst, hsecond, hd, hZbound, hclosed169, hgauss]
    exact htransport.trans (hpay.trans hfee)
  have hopen :
      |P₀.real {ξ | T ξ < x} - Shao.OQ4.standardNormalCDF x| ≤ error := by
    have hd := hdiscopen x
    change |P₀.real {ξ | T ξ < x} - P₀.real {ξ | Tstar ξ < y}| ≤
      P₀.real Z at hd
    have hfirst := abs_sub_le (P₀.real {ξ | T ξ < x})
      (P₀.real {ξ | Tstar ξ < y}) (Shao.OQ4.standardNormalCDF x)
    have hsecond := abs_sub_le (P₀.real {ξ | Tstar ξ < y})
      (Shao.OQ4.standardNormalCDF y) (Shao.OQ4.standardNormalCDF x)
    have htransport :
        |P₀.real {ξ | T ξ < x} - Shao.OQ4.standardNormalCDF x| ≤
          E169 + zeroFee + 12 * D := by
      linarith only [hfirst, hsecond, hd, hZbound, hopen169, hgauss]
    exact htransport.trans (hpay.trans hfee)
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

end

end Shao.OQ6.ActualPhysicalGlobalCDF
