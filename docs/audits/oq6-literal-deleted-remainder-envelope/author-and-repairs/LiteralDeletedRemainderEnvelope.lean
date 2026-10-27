import Shao.OQ6.NormalizedRemainderEnvelope

set_option autoImplicit false

universe u

namespace Shao.OQ6.LiteralDeletedRemainderEnvelope

noncomputable section

open MeasureTheory
open scoped BigOperators Classical Topology

theorem literal_deleted_remainder_envelope_spec
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω) [hν : IsProbabilityMeasure ν]
    (n : ℕ) (hn : 1 ≤ n) (ξ : Fin n → Ω → ℝ)
    (hξ : ∀ i : Fin n, Measurable (ξ i))
    (hξ2 : ∀ i : Fin n, MemLp (ξ i) 2 ν)
    (hξenergy : (∑ i : Fin n, ∫ ω, (ξ i ω) ^ 2 ∂ν) = 1)
    (B : Ω → ℝ) (Bdelete : Fin n → Ω → ℝ)
    (hB : Measurable B)
    (hBdelete : ∀ i : Fin n, Measurable (Bdelete i))
    (hBnonneg : ∀ ω : Ω, 0 ≤ B ω)
    (hBdeletenonneg : ∀ (i : Fin n) (ω : Ω), 0 ≤ Bdelete i ω)
    (hBint : Integrable B ν)
    (hBdeleteint : ∀ i : Fin n, Integrable (Bdelete i) ν)
    (z : ℝ) (hz : 0 ≤ z) :
    let V : Ω → ℝ :=
      fun ω : Ω => Real.sqrt (∑ j : Fin n, (ξ j ω) ^ 2)
    let Vdelete : Fin n → Ω → ℝ :=
      fun (i : Fin n) (ω : Ω) =>
        Real.sqrt (∑ j ∈ Finset.univ.erase i, (ξ j ω) ^ 2)
    let C : Ω → ℝ := fun ω : Ω => Real.sqrt (1 + B ω)
    let Cdelete : Fin n → Ω → ℝ :=
      fun (i : Fin n) (ω : Ω) => Real.sqrt (1 + Bdelete i ω)
    let H : Ω → ℝ :=
      fun ω : Ω => (1 + V ω) * (Real.sqrt (n : ℝ) + z * C ω)
    let Hdelete : Fin n → Ω → ℝ :=
      fun (i : Fin n) (ω : Ω) =>
        (1 + Vdelete i ω) * (Real.sqrt (n : ℝ) + z * Cdelete i ω)
    let ρ : ℝ → ℝ := fun ε : ℝ => 4 * ε * Real.sqrt (n : ℝ)
    let M : ℝ → Ω → ℝ :=
      fun (ε : ℝ) (ω : Ω) => ρ ε * H ω
    let Mdelete : ℝ → Fin n → Ω → ℝ :=
      fun (ε : ℝ) (i : Fin n) (ω : Ω) => ρ ε * Hdelete i ω
    let κ : Fin n → ℝ :=
      fun i : Fin n => 4 * Real.sqrt (n : ℝ) *
        ((∫ ω, H ω ∂ν) + (∫ ω, Hdelete i ω ∂ν))
    let Δ : (Ω → ℝ) → (Fin n → Ω → ℝ) → ℝ → Fin n → Ω → ℝ :=
      fun (A : Ω → ℝ) (Adelete : Fin n → Ω → ℝ)
        (ε : ℝ) (i : Fin n) (ω : Ω) =>
          (A ω + M ε ω) - (Adelete i ω + Mdelete ε i ω) -
            (A ω - Adelete i ω)
    Measurable V ∧
    (∀ i : Fin n, Measurable (Vdelete i)) ∧
    (∀ (i : Fin n) (ω : Ω), 0 ≤ Vdelete i ω ∧ Vdelete i ω ≤ V ω) ∧
    Measurable C ∧
    (∀ i : Fin n, Measurable (Cdelete i)) ∧
    (∀ ω : Ω, 1 ≤ C ω) ∧
    (∀ (i : Fin n) (ω : Ω), 1 ≤ Cdelete i ω) ∧
    Measurable H ∧ Integrable H ν ∧
    (∀ i : Fin n, Measurable (Hdelete i) ∧ Integrable (Hdelete i) ν) ∧
    (∀ ω : Ω, 0 < H ω) ∧
    (∀ (i : Fin n) (ω : Ω), 0 < Hdelete i ω) ∧
    (∀ ε : ℝ, Measurable (M ε) ∧
      ∀ i : Fin n, Measurable (Mdelete ε i)) ∧
    (∀ ε : ℝ, Integrable (M ε) ν ∧
      ∀ i : Fin n, Integrable (Mdelete ε i) ν) ∧
    (∀ ε : ℝ, Integrable (fun ω : Ω => |M ε ω|) ν ∧
      ∀ i : Fin n, Integrable (fun ω : Ω => |Mdelete ε i ω|) ν) ∧
    (∀ ε : ℝ, 0 ≤ ε → ∀ ω : Ω,
      0 ≤ M ε ω ∧ ∀ i : Fin n, 0 ≤ Mdelete ε i ω) ∧
    (∀ ε : ℝ, (∫ ω, M ε ω ∂ν) = ρ ε * (∫ ω, H ω ∂ν)) ∧
    (∀ (ε : ℝ) (i : Fin n),
      (∫ ω, Mdelete ε i ω ∂ν) = ρ ε * (∫ ω, Hdelete i ω ∂ν)) ∧
    (∀ ε : ℝ,
      (∫ ω, |M ε ω| ∂ν) = |ρ ε| * (∫ ω, H ω ∂ν)) ∧
    (∀ (ε : ℝ) (i : Fin n),
      (∫ ω, |Mdelete ε i ω| ∂ν) = |ρ ε| * (∫ ω, Hdelete i ω ∂ν)) ∧
    (∀ i : Fin n, 0 ≤ κ i) ∧
    (∀ (ε : ℝ) (i : Fin n),
      (∫ ω, M ε ω ∂ν) + (∫ ω, Mdelete ε i ω ∂ν) = ε * κ i) ∧
    (∀ (ε : ℝ) (i : Fin n),
      (∫ ω, |M ε ω| ∂ν) + (∫ ω, |Mdelete ε i ω| ∂ν) = |ε| * κ i) ∧
    Filter.Tendsto (fun ε : ℝ => ∫ ω, M ε ω ∂ν)
      (nhds (0 : ℝ)) (nhds (0 : ℝ)) ∧
    Filter.Tendsto (fun ε : ℝ => ∫ ω, |M ε ω| ∂ν)
      (nhds (0 : ℝ)) (nhds (0 : ℝ)) ∧
    (∀ i : Fin n, Filter.Tendsto (fun ε : ℝ => ∫ ω, Mdelete ε i ω ∂ν)
      (nhds (0 : ℝ)) (nhds (0 : ℝ))) ∧
    (∀ i : Fin n, Filter.Tendsto (fun ε : ℝ => ∫ ω, |Mdelete ε i ω| ∂ν)
      (nhds (0 : ℝ)) (nhds (0 : ℝ))) ∧
    (∀ (A : Ω → ℝ) (Adelete : Fin n → Ω → ℝ)
        (ε : ℝ) (i : Fin n) (ω : Ω),
      Δ A Adelete ε i ω = M ε ω - Mdelete ε i ω) ∧
    (∀ (A : Ω → ℝ) (Adelete : Fin n → Ω → ℝ)
        (ε : ℝ) (i : Fin n) (ω : Ω),
      |Δ A Adelete ε i ω| ≤ |M ε ω| + |Mdelete ε i ω|) ∧
    (∀ (A : Ω → ℝ) (Adelete : Fin n → Ω → ℝ)
        (ε : ℝ), 0 ≤ ε → ∀ (i : Fin n) (ω : Ω),
      |Δ A Adelete ε i ω| ≤ M ε ω + Mdelete ε i ω) ∧
    (∀ (A : Ω → ℝ) (Adelete : Fin n → Ω → ℝ)
        (ε : ℝ) (i : Fin n),
      Measurable (Δ A Adelete ε i) ∧
      Integrable (Δ A Adelete ε i) ν ∧
      Integrable (fun ω : Ω => |Δ A Adelete ε i ω|) ν) ∧
    (∀ (A : Ω → ℝ) (Adelete : Fin n → Ω → ℝ)
        (ε : ℝ) (i : Fin n),
      (∫ ω, |Δ A Adelete ε i ω| ∂ν) ≤ |ε| * κ i) ∧
    (∀ (A : Ω → ℝ) (Adelete : Fin n → Ω → ℝ) (i : Fin n),
      Filter.Tendsto (fun ε : ℝ => ∫ ω, |Δ A Adelete ε i ω| ∂ν)
        (nhds (0 : ℝ)) (nhds (0 : ℝ))) := by
  let V : Ω → ℝ :=
    fun ω : Ω => Real.sqrt (∑ j : Fin n, (ξ j ω) ^ 2)
  let Vdelete : Fin n → Ω → ℝ :=
    fun (i : Fin n) (ω : Ω) =>
      Real.sqrt (∑ j ∈ Finset.univ.erase i, (ξ j ω) ^ 2)
  let C : Ω → ℝ := fun ω : Ω => Real.sqrt (1 + B ω)
  let Cdelete : Fin n → Ω → ℝ :=
    fun (i : Fin n) (ω : Ω) => Real.sqrt (1 + Bdelete i ω)
  let H : Ω → ℝ :=
    fun ω : Ω => (1 + V ω) * (Real.sqrt (n : ℝ) + z * C ω)
  let Hdelete : Fin n → Ω → ℝ :=
    fun (i : Fin n) (ω : Ω) =>
      (1 + Vdelete i ω) * (Real.sqrt (n : ℝ) + z * Cdelete i ω)
  let ρ : ℝ → ℝ := fun ε : ℝ => 4 * ε * Real.sqrt (n : ℝ)
  let M : ℝ → Ω → ℝ :=
    fun (ε : ℝ) (ω : Ω) => ρ ε * H ω
  let Mdelete : ℝ → Fin n → Ω → ℝ :=
    fun (ε : ℝ) (i : Fin n) (ω : Ω) => ρ ε * Hdelete i ω
  let κ : Fin n → ℝ :=
    fun i : Fin n => 4 * Real.sqrt (n : ℝ) *
      ((∫ ω, H ω ∂ν) + (∫ ω, Hdelete i ω ∂ν))
  let Δ : (Ω → ℝ) → (Fin n → Ω → ℝ) → ℝ → Fin n → Ω → ℝ :=
    fun (A : Ω → ℝ) (Adelete : Fin n → Ω → ℝ)
      (ε : ℝ) (i : Fin n) (ω : Ω) =>
        (A ω + M ε ω) - (Adelete i ω + Mdelete ε i ω) -
          (A ω - Adelete i ω)
  let Hdom : Fin n → Ω → ℝ :=
    fun (i : Fin n) (ω : Ω) =>
      (1 + V ω) * (Real.sqrt (n : ℝ) + z * Cdelete i ω)
  let E : Fin n → Ω → ℝ :=
    fun (i : Fin n) (ω : Ω) => H ω - Hdelete i ω
  rcases Shao.OQ6.NormalizedRemainderEnvelope.actual_energy_envelope_integrability
      ν n hn ξ hξ hξ2 hξenergy B hB hBnonneg hBint with
    ⟨hVm, hVnonneg, _, _, _, _, _, hCm, hCone, _, _, _, _, _, _, _,
      hHspec, hHpositive, _, hFullAbsIntegral, _⟩
  have hHm : Measurable H := (hHspec z).1
  have hHint : Integrable H ν := (hHspec z).2
  have hHpos : ∀ ω : Ω, 0 < H ω := hHpositive z hz
  have hCdeleteSpec : ∀ i : Fin n,
      Measurable (Cdelete i) ∧ (∀ ω : Ω, 1 ≤ Cdelete i ω) ∧
        Measurable (Hdom i) ∧ Integrable (Hdom i) ν := by
    intro i
    rcases Shao.OQ6.NormalizedRemainderEnvelope.actual_energy_envelope_integrability
        ν n hn ξ hξ hξ2 hξenergy (Bdelete i) (hBdelete i)
        (fun ω : Ω => hBdeletenonneg i ω) (hBdeleteint i) with
      ⟨_, _, _, _, _, _, _, hCiM, hCiOne, _, _, _, _, _, _, _,
        hHiSpec, _, _, _, _⟩
    exact ⟨hCiM, hCiOne, (hHiSpec z).1, (hHiSpec z).2⟩
  have hVdeleteM : ∀ i : Fin n, Measurable (Vdelete i) := by
    intro i
    exact (Finset.measurable_sum (Finset.univ.erase i)
      (fun (j : Fin n) (_hj : j ∈ Finset.univ.erase i) =>
        (hξ j).pow_const (2 : ℕ))).sqrt
  have hVdeleteBounds : ∀ (i : Fin n) (ω : Ω),
      0 ≤ Vdelete i ω ∧ Vdelete i ω ≤ V ω := by
    intro i ω
    refine ⟨Real.sqrt_nonneg _, ?_⟩
    apply Real.sqrt_le_sqrt
    have herase :
        (∑ j ∈ Finset.univ.erase i, (ξ j ω) ^ 2) + (ξ i ω) ^ 2 =
          ∑ j : Fin n, (ξ j ω) ^ 2 :=
      Finset.sum_erase_add Finset.univ
        (fun j : Fin n => (ξ j ω) ^ 2) (Finset.mem_univ i)
    linarith [sq_nonneg (ξ i ω)]
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hHdeleteM : ∀ i : Fin n, Measurable (Hdelete i) := by
    intro i
    exact (measurable_const.add (hVdeleteM i)).mul
      (measurable_const.add (measurable_const.mul (hCdeleteSpec i).1))
  have hHdeletePos : ∀ (i : Fin n) (ω : Ω), 0 < Hdelete i ω := by
    intro i ω
    have hOneVpos : 0 < 1 + Vdelete i ω := by
      linarith [(hVdeleteBounds i ω).1]
    have hzC : 0 ≤ z * Cdelete i ω :=
      mul_nonneg hz (by linarith [(hCdeleteSpec i).2.1 ω])
    exact mul_pos hOneVpos (add_pos_of_pos_of_nonneg hnsqrt hzC)
  have hHdeleteLe : ∀ (i : Fin n) (ω : Ω), Hdelete i ω ≤ Hdom i ω := by
    intro i ω
    change (1 + Vdelete i ω) * (Real.sqrt (n : ℝ) + z * Cdelete i ω) ≤
      (1 + V ω) * (Real.sqrt (n : ℝ) + z * Cdelete i ω)
    exact mul_le_mul_of_nonneg_right
      (add_le_add_left (hVdeleteBounds i ω).2 1)
      (add_nonneg (Real.sqrt_nonneg (n : ℝ))
        (mul_nonneg hz (by linarith [(hCdeleteSpec i).2.1 ω])))
  have hHdeleteInt : ∀ i : Fin n, Integrable (Hdelete i) ν := by
    intro i
    apply (hCdeleteSpec i).2.2.2.mono' (hHdeleteM i).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω : Ω => by
      change ‖Hdelete i ω‖ ≤ Hdom i ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hHdeletePos i ω).le]
      exact hHdeleteLe i ω)
  have hρnonneg : ∀ ε : ℝ, 0 ≤ ε → 0 ≤ ρ ε := by
    intro ε hε
    exact mul_nonneg (mul_nonneg (by norm_num) hε) (Real.sqrt_nonneg (n : ℝ))
  have hMMeas : ∀ ε : ℝ, Measurable (M ε) ∧
      ∀ i : Fin n, Measurable (Mdelete ε i) := by
    intro ε
    exact ⟨measurable_const.mul hHm,
      fun i : Fin n => measurable_const.mul (hHdeleteM i)⟩
  have hMInt : ∀ ε : ℝ, Integrable (M ε) ν ∧
      ∀ i : Fin n, Integrable (Mdelete ε i) ν := by
    intro ε
    exact ⟨hHint.const_mul (ρ ε),
      fun i : Fin n => (hHdeleteInt i).const_mul (ρ ε)⟩
  have hMAbsInt : ∀ ε : ℝ, Integrable (fun ω : Ω => |M ε ω|) ν ∧
      ∀ i : Fin n, Integrable (fun ω : Ω => |Mdelete ε i ω|) ν := by
    intro ε
    refine ⟨?_, ?_⟩
    · simpa only [Real.norm_eq_abs] using (hMInt ε).1.norm
    · intro i
      simpa only [Real.norm_eq_abs] using ((hMInt ε).2 i).norm
  have hMnonneg : ∀ ε : ℝ, 0 ≤ ε → ∀ ω : Ω,
      0 ≤ M ε ω ∧ ∀ i : Fin n, 0 ≤ Mdelete ε i ω := by
    intro ε hε ω
    exact ⟨mul_nonneg (hρnonneg ε hε) (hHpos ω).le,
      fun i : Fin n => mul_nonneg (hρnonneg ε hε) (hHdeletePos i ω).le⟩
  have hMIntegral : ∀ ε : ℝ,
      (∫ ω, M ε ω ∂ν) = ρ ε * (∫ ω, H ω ∂ν) := by
    intro ε
    exact integral_const_mul (ρ ε) H
  have hMdeleteIntegral : ∀ (ε : ℝ) (i : Fin n),
      (∫ ω, Mdelete ε i ω ∂ν) = ρ ε * (∫ ω, Hdelete i ω ∂ν) := by
    intro ε i
    exact integral_const_mul (ρ ε) (Hdelete i)
  have hMAbsIntegral : ∀ ε : ℝ,
      (∫ ω, |M ε ω| ∂ν) = |ρ ε| * (∫ ω, H ω ∂ν) := by
    intro ε
    exact hFullAbsIntegral z hz ε
  have hMdeleteAbsIntegral : ∀ (ε : ℝ) (i : Fin n),
      (∫ ω, |Mdelete ε i ω| ∂ν) = |ρ ε| * (∫ ω, Hdelete i ω ∂ν) := by
    intro ε i
    calc
      (∫ ω, |Mdelete ε i ω| ∂ν) = ∫ ω, |ρ ε| * Hdelete i ω ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun ω : Ω => by
          change |ρ ε * Hdelete i ω| = |ρ ε| * Hdelete i ω
          rw [abs_mul, abs_of_nonneg (hHdeletePos i ω).le])
      _ = |ρ ε| * (∫ ω, Hdelete i ω ∂ν) :=
        integral_const_mul (abs (ρ ε)) (Hdelete i)
  have hκnonneg : ∀ i : Fin n, 0 ≤ κ i := by
    intro i
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg (n : ℝ)))
      (add_nonneg (integral_nonneg (fun ω : Ω => (hHpos ω).le))
        (integral_nonneg (fun ω : Ω => (hHdeletePos i ω).le)))
  have hPairIntegral : ∀ (ε : ℝ) (i : Fin n),
      (∫ ω, M ε ω ∂ν) + (∫ ω, Mdelete ε i ω ∂ν) = ε * κ i := by
    intro ε i
    rw [hMIntegral ε, hMdeleteIntegral ε i]
    dsimp only [ρ, κ]
    ring
  have hAbsRho : ∀ ε : ℝ, |ρ ε| = 4 * |ε| * Real.sqrt (n : ℝ) := by
    intro ε
    dsimp only [ρ]
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
      abs_of_nonneg (Real.sqrt_nonneg (n : ℝ))]
  have hPairAbsIntegral : ∀ (ε : ℝ) (i : Fin n),
      (∫ ω, |M ε ω| ∂ν) + (∫ ω, |Mdelete ε i ω| ∂ν) = |ε| * κ i := by
    intro ε i
    rw [hMAbsIntegral ε, hMdeleteAbsIntegral ε i, hAbsRho ε]
    dsimp only [κ]
    ring
  have hρlimit : Filter.Tendsto ρ (nhds (0 : ℝ)) (nhds (0 : ℝ)) := by
    have hid : Filter.Tendsto (fun ε : ℝ => ε) (nhds (0 : ℝ)) (nhds (0 : ℝ)) :=
      Filter.tendsto_id
    simpa only [ρ, mul_zero, zero_mul] using
      (Filter.Tendsto.mul_const (Real.sqrt (n : ℝ))
        (Filter.Tendsto.const_mul (4 : ℝ) hid))
  have hMLimit : Filter.Tendsto (fun ε : ℝ => ∫ ω, M ε ω ∂ν)
      (nhds (0 : ℝ)) (nhds (0 : ℝ)) := by
    simpa only [hMIntegral, zero_mul] using
      (Filter.Tendsto.mul_const (∫ ω, H ω ∂ν) hρlimit)
  have hMAbsLimit : Filter.Tendsto (fun ε : ℝ => ∫ ω, |M ε ω| ∂ν)
      (nhds (0 : ℝ)) (nhds (0 : ℝ)) := by
    simpa only [hMAbsIntegral, abs_zero, zero_mul] using
      (Filter.Tendsto.mul_const (∫ ω, H ω ∂ν) hρlimit.abs)
  have hMdeleteLimit : ∀ i : Fin n,
      Filter.Tendsto (fun ε : ℝ => ∫ ω, Mdelete ε i ω ∂ν)
        (nhds (0 : ℝ)) (nhds (0 : ℝ)) := by
    intro i
    simpa only [hMdeleteIntegral, zero_mul] using
      (Filter.Tendsto.mul_const (∫ ω, Hdelete i ω ∂ν) hρlimit)
  have hMdeleteAbsLimit : ∀ i : Fin n,
      Filter.Tendsto (fun ε : ℝ => ∫ ω, |Mdelete ε i ω| ∂ν)
        (nhds (0 : ℝ)) (nhds (0 : ℝ)) := by
    intro i
    simpa only [hMdeleteAbsIntegral, abs_zero, zero_mul] using
      (Filter.Tendsto.mul_const (∫ ω, Hdelete i ω ∂ν) hρlimit.abs)
  have hΔeq : ∀ (A : Ω → ℝ) (Adelete : Fin n → Ω → ℝ)
      (ε : ℝ) (i : Fin n) (ω : Ω),
      Δ A Adelete ε i ω = M ε ω - Mdelete ε i ω := by
    intro A Adelete ε i ω
    dsimp only [Δ]
    ring
  have hΔabsbound : ∀ (A : Ω → ℝ) (Adelete : Fin n → Ω → ℝ)
      (ε : ℝ) (i : Fin n) (ω : Ω),
      |Δ A Adelete ε i ω| ≤ |M ε ω| + |Mdelete ε i ω| := by
    intro A Adelete ε i ω
    rw [hΔeq A Adelete ε i ω]
    simpa only [sub_eq_add_neg, abs_neg] using
      (abs_add_le (M ε ω) (-(Mdelete ε i ω)))
  have hΔsourcebound : ∀ (A : Ω → ℝ) (Adelete : Fin n → Ω → ℝ)
      (ε : ℝ), 0 ≤ ε → ∀ (i : Fin n) (ω : Ω),
      |Δ A Adelete ε i ω| ≤ M ε ω + Mdelete ε i ω := by
    intro A Adelete ε hε i ω
    simpa only [abs_of_nonneg (hMnonneg ε hε ω).1,
      abs_of_nonneg ((hMnonneg ε hε ω).2 i)] using
      (hΔabsbound A Adelete ε i ω)
  have hΔfunEq : ∀ (A : Ω → ℝ) (Adelete : Fin n → Ω → ℝ)
      (ε : ℝ) (i : Fin n),
      Δ A Adelete ε i = (fun ω : Ω => M ε ω - Mdelete ε i ω) := by
    intro A Adelete ε i
    exact funext (hΔeq A Adelete ε i)
  have hΔspec : ∀ (A : Ω → ℝ) (Adelete : Fin n → Ω → ℝ)
      (ε : ℝ) (i : Fin n),
      Measurable (Δ A Adelete ε i) ∧ Integrable (Δ A Adelete ε i) ν ∧
        Integrable (fun ω : Ω => |Δ A Adelete ε i ω|) ν := by
    intro A Adelete ε i
    have hδm : Measurable (Δ A Adelete ε i) := by
      rw [hΔfunEq A Adelete ε i]
      exact (hMMeas ε).1.sub ((hMMeas ε).2 i)
    have hδint : Integrable (Δ A Adelete ε i) ν := by
      rw [hΔfunEq A Adelete ε i]
      exact (hMInt ε).1.sub ((hMInt ε).2 i)
    refine ⟨hδm, hδint, ?_⟩
    simpa only [Real.norm_eq_abs] using hδint.norm
  have hΔintegral : ∀ (A : Ω → ℝ) (Adelete : Fin n → Ω → ℝ)
      (ε : ℝ) (i : Fin n),
      (∫ ω, |Δ A Adelete ε i ω| ∂ν) ≤ |ε| * κ i := by
    intro A Adelete ε i
    calc
      (∫ ω, |Δ A Adelete ε i ω| ∂ν) ≤
          ∫ ω, |M ε ω| + |Mdelete ε i ω| ∂ν :=
        integral_mono (hΔspec A Adelete ε i).2.2
          ((hMAbsInt ε).1.add ((hMAbsInt ε).2 i))
          (hΔabsbound A Adelete ε i)
      _ = (∫ ω, |M ε ω| ∂ν) + (∫ ω, |Mdelete ε i ω| ∂ν) :=
        integral_add (hMAbsInt ε).1 ((hMAbsInt ε).2 i)
      _ = |ε| * κ i := hPairAbsIntegral ε i
  have hΔEeq : ∀ (A : Ω → ℝ) (Adelete : Fin n → Ω → ℝ)
      (ε : ℝ) (i : Fin n) (ω : Ω),
      Δ A Adelete ε i ω = ρ ε * E i ω := by
    intro A Adelete ε i ω
    rw [hΔeq A Adelete ε i ω]
    dsimp only [M, Mdelete, E]
    ring
  have hΔAbsIntegralE : ∀ (A : Ω → ℝ) (Adelete : Fin n → Ω → ℝ)
      (ε : ℝ) (i : Fin n),
      (∫ ω, |Δ A Adelete ε i ω| ∂ν) =
        |ρ ε| * (∫ ω, |E i ω| ∂ν) := by
    intro A Adelete ε i
    calc
      (∫ ω, |Δ A Adelete ε i ω| ∂ν) = ∫ ω, |ρ ε| * |E i ω| ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun ω : Ω => by
          rw [hΔEeq A Adelete ε i ω, abs_mul])
      _ = |ρ ε| * (∫ ω, |E i ω| ∂ν) :=
        integral_const_mul (abs (ρ ε)) (fun ω : Ω => |E i ω|)
  have hΔlimit : ∀ (A : Ω → ℝ) (Adelete : Fin n → Ω → ℝ) (i : Fin n),
      Filter.Tendsto (fun ε : ℝ => ∫ ω, |Δ A Adelete ε i ω| ∂ν)
        (nhds (0 : ℝ)) (nhds (0 : ℝ)) := by
    intro A Adelete i
    simpa only [hΔAbsIntegralE, abs_zero, zero_mul] using
      (Filter.Tendsto.mul_const (∫ ω, |E i ω| ∂ν) hρlimit.abs)
  exact ⟨hVm, hVdeleteM, hVdeleteBounds, hCm,
    (fun i : Fin n => (hCdeleteSpec i).1), hCone,
    (fun (i : Fin n) (ω : Ω) => (hCdeleteSpec i).2.1 ω), hHm, hHint,
    (fun i : Fin n => ⟨hHdeleteM i, hHdeleteInt i⟩), hHpos, hHdeletePos,
    hMMeas, hMInt, hMAbsInt, hMnonneg, hMIntegral, hMdeleteIntegral,
    hMAbsIntegral, hMdeleteAbsIntegral, hκnonneg, hPairIntegral,
    hPairAbsIntegral, hMLimit, hMAbsLimit, hMdeleteLimit, hMdeleteAbsLimit,
    hΔeq, hΔabsbound, hΔsourcebound, hΔspec, hΔintegral, hΔlimit⟩

end

end Shao.OQ6.LiteralDeletedRemainderEnvelope
