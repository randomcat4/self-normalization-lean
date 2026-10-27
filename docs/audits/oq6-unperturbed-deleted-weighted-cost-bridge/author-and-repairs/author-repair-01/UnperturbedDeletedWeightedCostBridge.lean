import Shao.OQ6.LiteralDeletedWeightedCosts

set_option autoImplicit false
universe u

namespace Shao.OQ6.UnperturbedDeletedWeightedCostBridge
noncomputable section

open MeasureTheory
open scoped BigOperators Classical Topology

theorem actual_unperturbed_deleted_weighted_cost_bridge
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω) (n : ℕ) (z K : ℝ) (hK : 0 ≤ K)
    (η : ℕ → Fin n → Ω → ℝ)
    (hη : ∀ (k : ℕ) (i : Fin n), Measurable (η k i))
    (Anew : ℕ → Ω → ℝ) (Adelete : Fin n → Ω → ℝ)
    (B : Ω → ℝ) (Bdelete Hdelete : Fin n → Ω → ℝ)
    (hAnew : ∀ k : ℕ, Measurable (Anew k))
    (hAdelete : ∀ i : Fin n, Measurable (Adelete i))
    (hHdelete : ∀ i : Fin n,
      Measurable (Hdelete i) ∧ Integrable (Hdelete i) ν ∧
        ∀ ω : Ω, 0 ≤ Hdelete i ω)
    (ε : ℕ → ℝ)
    (hεlim : Filter.Tendsto ε Filter.atTop (nhds (0 : ℝ))) :
    let Mdelete : ℕ → Fin n → Ω → ℝ :=
      fun k i ω => K * ε k * Hdelete i ω
    let AdeleteNew : ℕ → Fin n → Ω → ℝ :=
      fun k i ω => Adelete i ω + Mdelete k i ω
    let ℓη : ℕ → Fin n → Ω → ℝ :=
      fun k i ω => z * η k i ω - (z * η k i ω) ^ 2 / 2
    let Sηminus : ℕ → Fin n → Ω → ℝ :=
      fun k i ω => ∑ j ∈ Finset.univ.erase i, ℓη k j ω
    let capη : ℕ → Fin n → Ω → ℝ :=
      fun k i ω => min |z * η k i ω| 1
    let deletedTestη : ℕ → Fin n → Ω → ℝ :=
      fun k i ω => capη k i ω *
        (|Anew k ω - AdeleteNew k i ω| + z * |B ω - Bdelete i ω|)
    let deletedTestUnperturbedη : ℕ → Fin n → Ω → ℝ :=
      fun k i ω => capη k i ω *
        (|Anew k ω - Adelete i ω| + z * |B ω - Bdelete i ω|)
    let weightedDeletedη : ℕ → Fin n → Ω → ℝ :=
      fun k i ω => deletedTestη k i ω * Real.exp (Sηminus k i ω)
    let weightedDeletedUnperturbedη : ℕ → Fin n → Ω → ℝ :=
      fun k i ω => deletedTestUnperturbedη k i ω * Real.exp (Sηminus k i ω)
    let Edel : ℝ := Real.exp ((n : ℝ) / 2)
    let Qdel : Fin n → Ω → ℝ := fun i ω => Edel * (K * Hdelete i ω)
    let mHdelete : Fin n → ℝ := fun i => ∫ ω, Hdelete i ω ∂ν
    let Cdel : Fin n → ℝ := fun i => Edel * (K * mHdelete i)
    (∀ (k : ℕ) (i : Fin n), Integrable (weightedDeletedη k i) ν) →
    (∀ (k : ℕ) (i : Fin n) (ω : Ω),
      0 ≤ capη k i ω ∧ capη k i ω ≤ 1 ∧
      0 < Real.exp (Sηminus k i ω) ∧
      Real.exp (Sηminus k i ω) ≤ Edel) ∧
    (∀ (k : ℕ) (i : Fin n) (ω : Ω),
      weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω =
        capη k i ω *
          (|Anew k ω - Adelete i ω| - |Anew k ω - AdeleteNew k i ω|) *
            Real.exp (Sηminus k i ω)) ∧
    (∀ (k : ℕ) (i : Fin n) (ω : Ω),
      |weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω| ≤
        capη k i ω * |Mdelete k i ω| * Real.exp (Sηminus k i ω) ∧
      |weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω| ≤
        |ε k| * Qdel i ω) ∧
    (∀ i : Fin n, Integrable (Qdel i) ν ∧
      (∫ ω, Qdel i ω ∂ν) = Cdel i ∧ 0 ≤ Cdel i) ∧
    (∀ (k : ℕ) (i : Fin n),
      Measurable (fun ω => weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω) ∧
      Integrable (fun ω => weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω) ν ∧
      Integrable (fun ω => |weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω|) ν ∧
      Integrable (weightedDeletedUnperturbedη k i) ν ∧
      (∫ ω, |weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω| ∂ν) ≤
        |ε k| * Cdel i ∧
      |(∫ ω, weightedDeletedUnperturbedη k i ω ∂ν) -
        (∫ ω, weightedDeletedη k i ω ∂ν)| ≤ |ε k| * Cdel i) ∧
    (∀ i : Fin n,
      Filter.Tendsto
        (fun k : ℕ => ∫ ω, |weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω| ∂ν)
        Filter.atTop (nhds (0 : ℝ)) ∧
      Filter.Tendsto
        (fun k : ℕ => (∫ ω, weightedDeletedUnperturbedη k i ω ∂ν) -
          (∫ ω, weightedDeletedη k i ω ∂ν))
        Filter.atTop (nhds (0 : ℝ))) ∧
    (∀ k : ℕ,
      |(∑ i : Fin n, ∫ ω, weightedDeletedUnperturbedη k i ω ∂ν) -
        (∑ i : Fin n, ∫ ω, weightedDeletedη k i ω ∂ν)| ≤
          |ε k| * ∑ i : Fin n, Cdel i) ∧
    Filter.Tendsto
      (fun k : ℕ => (∑ i : Fin n, ∫ ω, weightedDeletedUnperturbedη k i ω ∂ν) -
        (∑ i : Fin n, ∫ ω, weightedDeletedη k i ω ∂ν))
      Filter.atTop (nhds (0 : ℝ)) ∧
    (∀ (I0 sourceCost0 : ℝ) (Iη : ℕ → ℝ) (fullη : ℕ → Ω → ℝ),
      let sourceCostη : ℕ → ℝ := fun k =>
        ((∫ ω, fullη k ω ∂ν) +
          ∑ i : Fin n, ∫ ω, weightedDeletedη k i ω ∂ν) / Iη k
      let unperturbedSourceCostη : ℕ → ℝ := fun k =>
        ((∫ ω, fullη k ω ∂ν) +
          ∑ i : Fin n, ∫ ω, weightedDeletedUnperturbedη k i ω ∂ν) / Iη k
      0 < I0 →
      Filter.Tendsto Iη Filter.atTop (nhds I0) →
      Filter.Tendsto sourceCostη Filter.atTop (nhds sourceCost0) →
      Filter.Tendsto (fun k : ℕ => unperturbedSourceCostη k - sourceCostη k)
        Filter.atTop (nhds (0 : ℝ)) ∧
      Filter.Tendsto unperturbedSourceCostη Filter.atTop (nhds sourceCost0))    := by
  intro Mdelete AdeleteNew ℓη Sηminus capη deletedTestη deletedTestUnperturbedη
    weightedDeletedη weightedDeletedUnperturbedη Edel Qdel mHdelete Cdel hPerturbed
  have hHnonneg : ∀ (i : Fin n) (ω : Ω), 0 ≤ Hdelete i ω :=
    fun i ω => (hHdelete i).2.2 ω
  have hcap : ∀ (k : ℕ) (i : Fin n) (ω : Ω),
      0 ≤ capη k i ω ∧ capη k i ω ≤ 1 := by
    intro k i ω
    exact ⟨le_min (abs_nonneg _) (by norm_num), min_le_right _ _⟩
  have hSbound : ∀ (k : ℕ) (i : Fin n) (ω : Ω),
      Sηminus k i ω ≤ (n : ℝ) / 2 := by
    intro k i ω
    have hcard : (Finset.univ.erase i).card ≤ n := by
      calc
        (Finset.univ.erase i).card ≤ (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_card (Finset.erase_subset _ _)
        _ = n := by simp only [Finset.card_univ, Fintype.card_fin]
    have hcardR : ((Finset.univ.erase i).card : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hcard
    calc
      Sηminus k i ω ≤ ∑ _j ∈ Finset.univ.erase i, (1 / 2 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        change z * η k j ω - (z * η k j ω) ^ 2 / 2 ≤ (1 / 2 : ℝ)
        nlinarith [sq_nonneg (z * η k j ω - 1)]
      _ = ((Finset.univ.erase i).card : ℝ) / 2 := by
        simp [div_eq_mul_inv]
      _ ≤ (n : ℝ) / 2 := by linarith only [hcardR]
  have hexp : ∀ (k : ℕ) (i : Fin n) (ω : Ω),
      Real.exp (Sηminus k i ω) ≤ Edel := by
    intro k i ω
    exact Real.exp_le_exp.mpr (hSbound k i ω)
  have hPointwiseBounds : ∀ (k : ℕ) (i : Fin n) (ω : Ω),
      0 ≤ capη k i ω ∧ capη k i ω ≤ 1 ∧
      0 < Real.exp (Sηminus k i ω) ∧
      Real.exp (Sηminus k i ω) ≤ Edel :=
    fun k i ω => ⟨(hcap k i ω).1, (hcap k i ω).2,
      Real.exp_pos _, hexp k i ω⟩
  have hCancel : ∀ (k : ℕ) (i : Fin n) (ω : Ω),
      weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω =
        capη k i ω *
          (|Anew k ω - Adelete i ω| - |Anew k ω - AdeleteNew k i ω|) *
            Real.exp (Sηminus k i ω) := by
    intro k i ω
    dsimp only [weightedDeletedUnperturbedη, weightedDeletedη,
      deletedTestUnperturbedη, deletedTestη]
    ring
  have hMabs : ∀ (k : ℕ) (i : Fin n) (ω : Ω),
      |Mdelete k i ω| = |ε k| * (K * Hdelete i ω) := by
    intro k i ω
    dsimp only [Mdelete]
    rw [abs_mul, abs_mul, abs_of_nonneg hK, abs_of_nonneg (hHnonneg i ω)]
    ring
  have hReverse : ∀ (k : ℕ) (i : Fin n) (ω : Ω),
      |(|Anew k ω - Adelete i ω| - |Anew k ω - AdeleteNew k i ω|)| ≤
        |Mdelete k i ω| := by
    intro k i ω
    calc
      |(|Anew k ω - Adelete i ω| - |Anew k ω - AdeleteNew k i ω|)| ≤
          |(Anew k ω - Adelete i ω) - (Anew k ω - AdeleteNew k i ω)| :=
        abs_abs_sub_abs_le_abs_sub _ _
      _ = |Mdelete k i ω| := by
        congr 1
        dsimp only [AdeleteNew]
        ring
  have hCompare : ∀ (k : ℕ) (i : Fin n) (ω : Ω),
      |weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω| ≤
        capη k i ω * |Mdelete k i ω| * Real.exp (Sηminus k i ω) ∧
      |weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω| ≤
        |ε k| * Qdel i ω := by
    intro k i ω
    have hRaw : |weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω| ≤
        capη k i ω * |Mdelete k i ω| * Real.exp (Sηminus k i ω) := by
      calc
        |weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω| =
            capη k i ω *
              |(|Anew k ω - Adelete i ω| - |Anew k ω - AdeleteNew k i ω|)| *
                Real.exp (Sηminus k i ω) := by
          rw [hCancel k i ω, abs_mul, abs_mul,
            abs_of_nonneg (hcap k i ω).1, abs_of_pos (Real.exp_pos _)]
        _ ≤ capη k i ω * |Mdelete k i ω| * Real.exp (Sηminus k i ω) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hReverse k i ω) (hcap k i ω).1)
            (Real.exp_pos _).le
    refine ⟨hRaw, ?_⟩
    calc
      |weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω| ≤
          capη k i ω * |Mdelete k i ω| * Real.exp (Sηminus k i ω) := hRaw
      _ ≤ 1 * |Mdelete k i ω| * Real.exp (Sηminus k i ω) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hcap k i ω).2 (abs_nonneg _))
          (Real.exp_pos _).le
      _ ≤ 1 * |Mdelete k i ω| * Edel :=
        mul_le_mul_of_nonneg_left (hexp k i ω)
          (mul_nonneg (by norm_num) (abs_nonneg _))
      _ = |ε k| * Qdel i ω := by
        rw [hMabs k i ω]
        dsimp only [Qdel]
        ring
  have hQdel : ∀ i : Fin n, Integrable (Qdel i) ν ∧
      (∫ ω, Qdel i ω ∂ν) = Cdel i ∧ 0 ≤ Cdel i := by
    intro i
    refine ⟨((hHdelete i).2.1.const_mul K).const_mul Edel, ?_, ?_⟩
    · dsimp only [Qdel, Cdel, mHdelete]
      rw [integral_const_mul, integral_const_mul]
    · dsimp only [Cdel, mHdelete, Edel]
      exact mul_nonneg (Real.exp_pos _).le
        (mul_nonneg hK (integral_nonneg (hHnonneg i)))
  have hAdnewM : ∀ (k : ℕ) (i : Fin n), Measurable (AdeleteNew k i) := by
    intro k i
    exact (hAdelete i).add (measurable_const.mul (hHdelete i).1)
  have hCapM : ∀ (k : ℕ) (i : Fin n), Measurable (capη k i) := by
    intro k i
    change Measurable (fun ω : Ω => min |z * η k i ω| (1 : ℝ))
    simpa only [Real.norm_eq_abs] using
      ((show Measurable (fun ω : Ω => z * η k i ω) from
        measurable_const.mul (hη k i)).norm).min
        (measurable_const : Measurable (fun _ : Ω => (1 : ℝ)))
  have hSM : ∀ (k : ℕ) (i : Fin n), Measurable (Sηminus k i) := by
    intro k i
    exact Finset.measurable_sum (Finset.univ.erase i) (fun j _ =>
      (measurable_const.mul (hη k j)).sub
        (((measurable_const.mul (hη k j)).pow_const 2).div_const 2))
  have hDiffM : ∀ (k : ℕ) (i : Fin n),
      Measurable (fun ω => weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω) := by
    intro k i
    have hAbsA : Measurable (fun ω : Ω => |Anew k ω - Adelete i ω|) := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using
        ((hAnew k).sub (hAdelete i)).norm
    have hAbsAd : Measurable (fun ω : Ω => |Anew k ω - AdeleteNew k i ω|) := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using
        ((hAnew k).sub (hAdnewM k i)).norm
    simp_rw [hCancel k i]
    exact ((hCapM k i).mul (hAbsA.sub hAbsAd)).mul (hSM k i).exp
  have hDiffI : ∀ (k : ℕ) (i : Fin n),
      Integrable (fun ω => weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω) ν := by
    intro k i
    apply ((hQdel i).1.const_mul |ε k|).mono' (hDiffM k i).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs] using (hCompare k i ω).2
  have hDiffAbsI : ∀ (k : ℕ) (i : Fin n),
      Integrable (fun ω => |weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω|) ν :=
    fun k i => (hDiffI k i).abs
  have hUnperturbedI : ∀ (k : ℕ) (i : Fin n),
      Integrable (weightedDeletedUnperturbedη k i) ν := by
    intro k i
    have hsumI : Integrable
        (fun ω => (weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω) +
          weightedDeletedη k i ω) ν :=
      (hDiffI k i).add (hPerturbed k i)
    simpa only [sub_add_cancel] using hsumI
  have hL1Bound : ∀ (k : ℕ) (i : Fin n),
      (∫ ω, |weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω| ∂ν) ≤
        |ε k| * Cdel i := by
    intro k i
    calc
      (∫ ω, |weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω| ∂ν) ≤
          ∫ ω, |ε k| * Qdel i ω ∂ν :=
        integral_mono (hDiffAbsI k i) ((hQdel i).1.const_mul |ε k|)
          (fun ω => (hCompare k i ω).2)
      _ = |ε k| * Cdel i := by
        rw [integral_const_mul, (hQdel i).2.1]
  have hIntegralBound : ∀ (k : ℕ) (i : Fin n),
      |(∫ ω, weightedDeletedUnperturbedη k i ω ∂ν) -
        (∫ ω, weightedDeletedη k i ω ∂ν)| ≤ |ε k| * Cdel i := by
    intro k i
    rw [← integral_sub (hUnperturbedI k i) (hPerturbed k i)]
    have hnorm :
        |∫ ω, weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω ∂ν| ≤
          ∫ ω, |weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω| ∂ν := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ := ν)
          (fun ω : Ω => weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω))
    exact hnorm.trans (hL1Bound k i)
  have hAnalytic : ∀ (k : ℕ) (i : Fin n),
      Measurable (fun ω => weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω) ∧
      Integrable (fun ω => weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω) ν ∧
      Integrable (fun ω => |weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω|) ν ∧
      Integrable (weightedDeletedUnperturbedη k i) ν ∧
      (∫ ω, |weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω| ∂ν) ≤
        |ε k| * Cdel i ∧
      |(∫ ω, weightedDeletedUnperturbedη k i ω ∂ν) -
        (∫ ω, weightedDeletedη k i ω ∂ν)| ≤ |ε k| * Cdel i :=
    fun k i => ⟨hDiffM k i, hDiffI k i, hDiffAbsI k i,
      hUnperturbedI k i, hL1Bound k i, hIntegralBound k i⟩
  have hAbsEps : Filter.Tendsto (fun k : ℕ => |ε k|)
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa only [abs_zero] using hεlim.abs
  have hL1Lim : ∀ i : Fin n,
      Filter.Tendsto
        (fun k : ℕ => ∫ ω, |weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω| ∂ν)
        Filter.atTop (nhds (0 : ℝ)) := by
    intro i
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun k =>
        integral_nonneg (fun ω => abs_nonneg
          (weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω)))
      (Filter.Eventually.of_forall fun k => hL1Bound k i)
    simpa only [zero_mul] using hAbsEps.mul_const (Cdel i)
  have hIntegralLim : ∀ i : Fin n,
      Filter.Tendsto
        (fun k : ℕ => (∫ ω, weightedDeletedUnperturbedη k i ω ∂ν) -
          (∫ ω, weightedDeletedη k i ω ∂ν))
        Filter.atTop (nhds (0 : ℝ)) := by
    intro i
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero, Real.norm_eq_abs]
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun k => abs_nonneg
        ((∫ ω, weightedDeletedUnperturbedη k i ω ∂ν) -
          (∫ ω, weightedDeletedη k i ω ∂ν)))
      (Filter.Eventually.of_forall fun k => hIntegralBound k i)
    simpa only [zero_mul] using hAbsEps.mul_const (Cdel i)
  have hTotalBound : ∀ k : ℕ,
      |(∑ i : Fin n, ∫ ω, weightedDeletedUnperturbedη k i ω ∂ν) -
        (∑ i : Fin n, ∫ ω, weightedDeletedη k i ω ∂ν)| ≤
          |ε k| * ∑ i : Fin n, Cdel i := by
    intro k
    calc
      |(∑ i : Fin n, ∫ ω, weightedDeletedUnperturbedη k i ω ∂ν) -
          (∑ i : Fin n, ∫ ω, weightedDeletedη k i ω ∂ν)| =
          |∑ i : Fin n, ((∫ ω, weightedDeletedUnperturbedη k i ω ∂ν) -
            (∫ ω, weightedDeletedη k i ω ∂ν))| := by
        rw [Finset.sum_sub_distrib]
      _ ≤ ∑ i : Fin n, |(∫ ω, weightedDeletedUnperturbedη k i ω ∂ν) -
          (∫ ω, weightedDeletedη k i ω ∂ν)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, |ε k| * Cdel i :=
        Finset.sum_le_sum (fun i _ => hIntegralBound k i)
      _ = |ε k| * ∑ i : Fin n, Cdel i := by rw [Finset.mul_sum]
  have hTotalLim : Filter.Tendsto
      (fun k : ℕ => (∑ i : Fin n, ∫ ω, weightedDeletedUnperturbedη k i ω ∂ν) -
        (∑ i : Fin n, ∫ ω, weightedDeletedη k i ω ∂ν))
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa only [Finset.sum_const_zero, Finset.sum_sub_distrib] using
      tendsto_finsetSum Finset.univ (fun i _ => hIntegralLim i)
  refine ⟨hPointwiseBounds, hCancel, hCompare, hQdel, hAnalytic,
    (fun i => ⟨hL1Lim i, hIntegralLim i⟩), hTotalBound, hTotalLim, ?_⟩
  intro I0 sourceCost0 Iη fullη sourceCostη unperturbedSourceCostη
    hI0 hIηlim hCostlim
  have hRatioGap : Filter.Tendsto
      (fun k : ℕ => ((∑ i : Fin n, ∫ ω, weightedDeletedUnperturbedη k i ω ∂ν) -
        (∑ i : Fin n, ∫ ω, weightedDeletedη k i ω ∂ν)) / Iη k)
      Filter.atTop (nhds (0 : ℝ)) := by
    have hPiDiv :
        ((fun k : ℕ => (∑ i : Fin n, ∫ ω, weightedDeletedUnperturbedη k i ω ∂ν) -
          (∑ i : Fin n, ∫ ω, weightedDeletedη k i ω ∂ν)) / Iη) =
          (fun k : ℕ => ((∑ i : Fin n, ∫ ω, weightedDeletedUnperturbedη k i ω ∂ν) -
            (∑ i : Fin n, ∫ ω, weightedDeletedη k i ω ∂ν)) / Iη k) := by
      funext k
      simp only [Pi.div_apply]
    simpa only [zero_div, hPiDiv] using hTotalLim.div hIηlim hI0.ne'
  have hCostDiff : ∀ k : ℕ,
      unperturbedSourceCostη k - sourceCostη k =
        ((∑ i : Fin n, ∫ ω, weightedDeletedUnperturbedη k i ω ∂ν) -
          (∑ i : Fin n, ∫ ω, weightedDeletedη k i ω ∂ν)) / Iη k := by
    intro k
    dsimp only [sourceCostη, unperturbedSourceCostη]
    ring
  have hCostGap : Filter.Tendsto
      (fun k : ℕ => unperturbedSourceCostη k - sourceCostη k)
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa only [hCostDiff] using hRatioGap
  refine ⟨hCostGap, ?_⟩
  simpa only [sub_add_cancel, zero_add] using hCostGap.add hCostlim


end
end Shao.OQ6.UnperturbedDeletedWeightedCostBridge
