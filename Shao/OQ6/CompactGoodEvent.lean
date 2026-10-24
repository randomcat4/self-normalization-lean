import Shao.OQ6.ActualQuadraticTiltMoments
import Shao.OQ6.FiniteTiltedMoments
import Shao.OQ6.ActualRemainderEnvelope
import Shao.Probability.QuadraticEnergyLowerTail
import Shao.Probability.FiniteIIDMoments
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

namespace Shao.OQ6.CompactGoodEvent

noncomputable section

open MeasureTheory
open scoped BigOperators

private theorem projection_compact_good_event_of_clip_second
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgmean : (∫ o, g o ∂μ) = 0)
    (hgsecond : (∫ o, g o ^ 2 ∂μ) = 1)
    (K : ℝ) (hK : 1 ≤ K)
    (hclipsecond : (3 / 4 : ℝ) ≤
      (∫ o, (max (-K) (min (g o) K)) ^ 2 ∂μ)) :
    let c : ℝ := 1 / (512 * K ^ 2)
    0 < c ∧
      ∀ (n : ℕ), 0 < n →
        let P₀ : Measure (Fin n → Ω) :=
          Measure.pi (fun _ : Fin n => μ)
        let Vsq : (Fin n → Ω) → ℝ := fun ξ =>
          (∑ i : Fin n, g (ξ i) ^ 2) / (n : ℝ)
        let W : (Fin n → Ω) → ℝ := fun ξ =>
          (∑ i : Fin n, g (ξ i)) / Real.sqrt (n : ℝ)
        let G : Set (Fin n → Ω) := {ξ |
          (1 / 2 : ℝ) ≤ Vsq ξ ∧
          |W ξ| ≤ Real.sqrt (Real.sqrt (n : ℝ)) *
            (4 + Real.sqrt (Vsq ξ))}
        MeasurableSet G ∧
          Integrable (fun ξ => W ξ ^ 2) P₀ ∧
          (∫ ξ, W ξ ^ 2 ∂P₀) = 1 ∧
          P₀.real {ξ | Vsq ξ ≤ (1 / 2 : ℝ)} ≤
            Real.exp (-c * (n : ℝ)) ∧
          P₀.real Gᶜ ≤ Real.exp (-c * (n : ℝ)) +
            1 / (16 * Real.sqrt (n : ℝ)) := by
  classical
  have hKpos : 0 < K := by linarith
  let f : Ω → ℝ := fun o => max (-K) (min (g o) K)
  have hf : Measurable f := measurable_const.max (hg.min measurable_const)
  have hfb (o : Ω) : |f o| ≤ K ∧ |f o| ≤ |g o| := by
    have hfl : -K ≤ f o := le_max_left _ _
    have hfu : f o ≤ K := max_le (by linarith) (min_le_right _ _)
    refine ⟨abs_le.mpr ⟨hfl, hfu⟩, ?_⟩
    by_cases hlo : g o ≤ -K
    · have hmin : g o ≤ K := by linarith
      have heq : f o = -K := by simp [f, min_eq_left hmin, max_eq_left hlo]
      rw [heq, abs_neg, abs_of_pos hKpos]
      exact (by linarith [neg_le_abs (g o)])
    · by_cases hhi : K ≤ g o
      · have heq : f o = K := by
          simp [f, min_eq_right hhi, max_eq_right (by linarith : -K ≤ K)]
        rw [heq, abs_of_pos hKpos]
        exact hhi.trans (le_abs_self _)
      · have heq : f o = g o := by
          simp [f, min_eq_left (le_of_not_ge hhi),
            max_eq_right (le_of_not_ge hlo)]
        simpa only [heq] using (le_rfl : |g o| ≤ |g o|)
  have hfsq (o : Ω) : f o ^ 2 ≤ g o ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (f o)) (hfb o).2 2
  have hf2 : Integrable (fun o => f o ^ 2) μ := by
    apply hg2.integrable_sq.mono' (hf.pow_const 2).aestronglyMeasurable
    exact ae_of_all μ fun o => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hfsq o
  have hfcube (o : Ω) : |f o| ^ 3 ≤ K * f o ^ 2 := by
    calc
      |f o| ^ 3 = f o ^ 2 * |f o| := by rw [pow_succ, sq_abs]
      _ ≤ f o ^ 2 * K := mul_le_mul_of_nonneg_left (hfb o).1 (sq_nonneg _)
      _ = _ := mul_comm _ _
  have hf3 : Integrable (fun o => |f o| ^ 3) μ := by
    apply (hf2.const_mul K).mono' (by fun_prop)
    exact ae_of_all μ fun o => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) 3)]
      exact hfcube o
  let a : ℝ := ∫ o, f o ^ 2 ∂μ
  let b : ℝ := ∫ o, |f o| ^ 3 ∂μ
  have ha34 : (3 / 4 : ℝ) ≤ a := hclipsecond
  have hapos : 0 < a := by linarith
  have ha1 : a ≤ 1 := by
    calc
      a ≤ ∫ o, g o ^ 2 ∂μ := integral_mono hf2 hg2.integrable_sq hfsq
      _ = 1 := hgsecond
  have hb0 : 0 ≤ b := integral_nonneg fun o => pow_nonneg (abs_nonneg _) 3
  have hbK : b ≤ K * a := by
    calc
      b ≤ ∫ o, K * f o ^ 2 ∂μ := integral_mono hf3 (hf2.const_mul K) hfcube
      _ = K * a := integral_const_mul _ _
  refine ⟨by positivity, ?_⟩
  intro n hn
  dsimp only
  let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  let Vsq : (Fin n → Ω) → ℝ := fun ξ => (∑ i : Fin n, g (ξ i) ^ 2) / (n : ℝ)
  let W : (Fin n → Ω) → ℝ := fun ξ => (∑ i : Fin n, g (ξ i)) / Real.sqrt (n : ℝ)
  let G : Set (Fin n → Ω) := {ξ | (1 / 2 : ℝ) ≤ Vsq ξ ∧
    |W ξ| ≤ Real.sqrt (Real.sqrt (n : ℝ)) * (4 + Real.sqrt (Vsq ξ))}
  change MeasurableSet G ∧ Integrable (fun ξ => W ξ ^ 2) P₀ ∧
    (∫ ξ, W ξ ^ 2 ∂P₀) = 1 ∧
    P₀.real {ξ | Vsq ξ ≤ (1 / 2 : ℝ)} ≤
      Real.exp (-(1 / (512 * K ^ 2)) * (n : ℝ)) ∧
    P₀.real Gᶜ ≤ Real.exp (-(1 / (512 * K ^ 2)) * (n : ℝ)) +
      1 / (16 * Real.sqrt (n : ℝ))
  letI : IsProbabilityMeasure P₀ := inferInstance
  let N : ℝ := (n : ℝ)
  let q : ℝ := Real.sqrt N
  have hN : 0 < N := by
    change (0 : ℝ) < (n : ℝ)
    exact_mod_cast hn
  have hq : 0 < q := Real.sqrt_pos.mpr hN
  have hqsq : q ^ 2 = N := Real.sq_sqrt hN.le
  have hVm : Measurable Vsq := by dsimp [Vsq]; fun_prop
  have hWm : Measurable W := by dsimp [W]; fun_prop
  have hV0 (ξ : Fin n → Ω) : 0 ≤ Vsq ξ :=
    div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) hN.le
  have hGm : MeasurableSet G := by
    exact (measurableSet_le measurable_const hVm).inter
      (measurableSet_le (continuous_abs.measurable.comp hWm) (by fun_prop))
  let d : ℝ := Real.sqrt (N * a)
  have hd : 0 < d := Real.sqrt_pos.mpr (mul_pos hN hapos)
  have hdsq : d ^ 2 = N * a := Real.sq_sqrt (mul_pos hN hapos).le
  let Z : Ω → ℝ := fun o => f o / d
  have hZ : Measurable Z := hf.div_const d
  let ν : Measure ℝ := μ.map Z
  letI : IsProbabilityMeasure ν := by
    constructor
    change μ.map Z Set.univ = 1
    rw [Measure.map_apply hZ MeasurableSet.univ]
    simp
  have hZsq (o : Ω) : Z o ^ 2 = f o ^ 2 / d ^ 2 := div_pow _ _ _
  have hZcube (o : Ω) : |Z o| ^ 3 = |f o| ^ 3 / d ^ 3 := by
    dsimp only [Z]
    rw [abs_div, abs_of_pos hd, div_pow]
  have hν2 : Integrable (fun z : ℝ => z ^ 2) ν := by
    apply (integrable_map_measure (by fun_prop) hZ.aemeasurable).2
    exact (hf2.div_const (d ^ 2)).congr (ae_of_all μ fun o => (hZsq o).symm)
  have hν3 : Integrable (fun z : ℝ => |z| ^ 3) ν := by
    apply (integrable_map_measure (by fun_prop) hZ.aemeasurable).2
    exact (hf3.div_const (d ^ 3)).congr (ae_of_all μ fun o => (hZcube o).symm)
  have hνsecond : (∫ z : ℝ, z ^ 2 ∂ν) = a / d ^ 2 := by
    rw [show ν = μ.map Z from rfl, integral_map hZ.aemeasurable (by fun_prop)]
    simp_rw [hZsq]
    exact integral_div _ _
  have hνthird : (∫ z : ℝ, |z| ^ 3 ∂ν) = b / d ^ 3 := by
    rw [show ν = μ.map Z from rfl, integral_map hZ.aemeasurable (by fun_prop)]
    simp_rw [hZcube]
    exact integral_div _ _
  have hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) = 1 := by
    rw [hνsecond, hdsq]
    change N * (a / (N * a)) = 1
    field_simp [hN.ne', hapos.ne']
  let κ : ℝ := 1 - 1 / (2 * a)
  have hκlow : (1 / 3 : ℝ) ≤ κ := by
    dsimp only [κ]
    have hh : 1 / (2 * a) ≤ (2 / 3 : ℝ) :=
      (div_le_iff₀ (by positivity : 0 < 2 * a)).2 (by linarith)
    linarith
  have hκpos : 0 < κ := by linarith
  have hκone : κ ≤ 1 := by
    have hh : 0 ≤ 1 / (2 * a) := by positivity
    dsimp only [κ]
    linarith
  let β : ℝ := N * (b / d ^ 3)
  let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ν)
  have henergy := Shao.Probability.finite_iid_energy_lower_tail
    ν n hn hν2 hν3 hnorm κ hκpos hκone
  dsimp only at henergy
  rw [hνthird] at henergy
  change 0 < β ∧ Q.real {v : Shao.Path n | Shao.energy v ≤ 1 - κ} ≤
    Real.exp (-(κ ^ 3 / (8 * β ^ 2))) at henergy
  have hβ : 0 < β := henergy.1
  have hd6 : (d ^ 3) ^ 2 = N ^ 3 * a ^ 3 := by
    calc
      (d ^ 3) ^ 2 = (d ^ 2) ^ 3 := by ring
      _ = (N * a) ^ 3 := by rw [hdsq]
      _ = _ := mul_pow _ _ _
  have hβsq : β ^ 2 = b ^ 2 / (N * a ^ 3) := by
    dsimp only [β]
    rw [mul_pow, div_pow, hd6]
    field_simp [hN.ne', hapos.ne']
    <;> ring
  have hb2 : b ^ 2 ≤ K ^ 2 * a ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hb0 hbK 2
  have hβa : N * β ^ 2 * a ≤ K ^ 2 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hapos)).mp
    calc
      a ^ 2 * (N * β ^ 2 * a) = b ^ 2 := by
        rw [hβsq]
        field_simp [hN.ne', hapos.ne']
        <;> ring
      _ ≤ a ^ 2 * K ^ 2 := by simpa only [mul_comm] using hb2
  have hNβ : N * β ^ 2 ≤ 2 * K ^ 2 := by
    have hhalf : (N * β ^ 2) * (1 / 2 : ℝ) ≤ (N * β ^ 2) * a :=
      mul_le_mul_of_nonneg_left (by linarith : (1 / 2 : ℝ) ≤ a) (by positivity)
    linarith
  have hκcube : (1 / 27 : ℝ) ≤ κ ^ 3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 3) hκlow 3
    norm_num at hh
    exact hh
  have hexponent : N / (512 * K ^ 2) ≤ κ ^ 3 / (8 * β ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 8 * β ^ 2)).2
    calc
      N / (512 * K ^ 2) * (8 * β ^ 2) = (N * β ^ 2) / (64 * K ^ 2) := by
        field_simp [hKpos.ne']
        <;> ring
      _ ≤ (2 * K ^ 2) / (64 * K ^ 2) :=
        div_le_div_of_nonneg_right hNβ (by positivity)
      _ = (1 / 32 : ℝ) := by field_simp [hKpos.ne']; ring
      _ ≤ κ ^ 3 := (by norm_num : (1 / 32 : ℝ) ≤ 1 / 27).trans hκcube
  let T : (Fin n → Ω) → Shao.Path n := fun ξ i => Z (ξ i)
  have hT : Measurable T := Measurable.of_eval fun i => hZ.comp (measurable_pi_apply i)
  have hmap : P₀.map T = Q := Measure.pi_map_pi (fun _ : Fin n => hZ.aemeasurable)
  have hA : MeasurableSet {v : Shao.Path n | Shao.energy v ≤ 1 - κ} :=
    measurableSet_le Shao.measurable_energy measurable_const
  have hpull : P₀.real (T ⁻¹' {v : Shao.Path n | Shao.energy v ≤ 1 - κ}) =
      Q.real {v : Shao.Path n | Shao.energy v ≤ 1 - κ} := by
    rw [← hmap, Measure.real_def, Measure.real_def, Measure.map_apply hT hA]
  have hlow : P₀.real {ξ | Vsq ξ ≤ (1 / 2 : ℝ)} ≤
      Real.exp (-(1 / (512 * K ^ 2)) * (n : ℝ)) := by
    have hsub : {ξ | Vsq ξ ≤ (1 / 2 : ℝ)} ⊆
        T ⁻¹' {v : Shao.Path n | Shao.energy v ≤ 1 - κ} := by
      intro ξ hξ
      have hsum : (∑ i : Fin n, f (ξ i) ^ 2) ≤ N / 2 := by
        have hgSum : (∑ i : Fin n, g (ξ i) ^ 2) ≤ N / 2 := by
          have hh := (div_le_iff₀ hN).mp hξ
          linarith
        exact (Finset.sum_le_sum fun i _ => hfsq (ξ i)).trans hgSum
      change (∑ i : Fin n, (f (ξ i) / d) ^ 2) ≤ 1 - κ
      simp_rw [div_pow]
      rw [← Finset.sum_div, hdsq]
      calc
        (∑ i : Fin n, f (ξ i) ^ 2) / (N * a) ≤ (N / 2) / (N * a) :=
          div_le_div_of_nonneg_right hsum (by positivity)
        _ = 1 - κ := by dsimp [κ]; field_simp [hN.ne', hapos.ne']; ring
    calc
      P₀.real {ξ | Vsq ξ ≤ (1 / 2 : ℝ)} ≤
          P₀.real (T ⁻¹' {v : Shao.Path n | Shao.energy v ≤ 1 - κ}) :=
        measureReal_mono hsub
      _ = Q.real {v : Shao.Path n | Shao.energy v ≤ 1 - κ} := hpull
      _ ≤ Real.exp (-(κ ^ 3 / (8 * β ^ 2))) := henergy.2
      _ ≤ Real.exp (-(1 / (512 * K ^ 2)) * (n : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have heq : (1 / (512 * K ^ 2)) * (n : ℝ) = N / (512 * K ^ 2) := by
          dsimp only [N]
          ring
        rw [neg_mul, heq]
        exact neg_le_neg hexponent
  let η : Measure ℝ := μ.map g
  letI : IsProbabilityMeasure η := by
    constructor
    change μ.map g Set.univ = 1
    rw [Measure.map_apply hg MeasurableSet.univ]
    simp
  have hη2i : Integrable (fun z : ℝ => z ^ 2) η :=
    (integrable_map_measure (by fun_prop) hg.aemeasurable).2 hg2.integrable_sq
  have hη2 : MemLp (id : ℝ → ℝ) 2 η :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 hη2i
  have hηmean : (∫ z : ℝ, z ∂η) = 0 := by
    rw [show η = μ.map g from rfl, integral_map hg.aemeasurable (by fun_prop)]
    exact hgmean
  have hηsecond : (∫ z : ℝ, z ^ 2 ∂η) = 1 := by
    rw [show η = μ.map g from rfl, integral_map hg.aemeasurable (by fun_prop)]
    exact hgsecond
  have hI : ProbabilityTheory.iIndepFun (fun i (ξ : Fin n → Ω) => g (ξ i)) P₀ :=
    ProbabilityTheory.iIndepFun_pi (μ := fun _ : Fin n => μ)
      (X := fun _ (o : Ω) => g o) (fun _ => hg.aemeasurable)
  have hLaw (i : Fin n) : ProbabilityTheory.IdentDistrib
      (fun ξ : Fin n → Ω => g (ξ i)) (id : ℝ → ℝ) P₀ η := by
    refine ⟨(hg.comp (measurable_pi_apply i)).aemeasurable, measurable_id.aemeasurable, ?_⟩
    calc
      P₀.map (fun ξ : Fin n → Ω => g (ξ i)) =
          (P₀.map (fun ξ : Fin n → Ω => ξ i)).map g :=
        (Measure.map_map hg (measurable_pi_apply i)).symm
      _ = η := by rw [(measurePreserving_eval (fun _ : Fin n => μ) i).map_eq]
      _ = η.map id := Measure.map_id.symm
  have hS2 : MemLp (fun ξ : Fin n → Ω => ∑ i : Fin n, g (ξ i)) 2 P₀ :=
    memLp_finsetSum Finset.univ fun i _ =>
      hg2.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => μ) i)
  have hWi : Integrable (fun ξ => W ξ ^ 2) P₀ := by
    apply (hS2.integrable_sq.div_const (q ^ 2)).congr
    exact ae_of_all P₀ fun ξ => by dsimp [W, q, N]; rw [div_pow]
  have hSW := Shao.Probability.finite_iid_sumSquare_integral
    (Z := fun i (ξ : Fin n → Ω) => g (ξ i))
    (fun i => hg.comp (measurable_pi_apply i)) hI hLaw hη2
  have hWsecond : (∫ ξ, W ξ ^ 2 ∂P₀) = 1 := by
    have hsumInt : (∫ ξ : Fin n → Ω, (∑ i : Fin n, g (ξ i)) ^ 2 ∂P₀) = N := by
      simpa only [Shao.Probability.finiteFeatureSum, hηmean, hηsecond,
        zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, mul_one] using hSW
    simp_rw [show ∀ ξ, W ξ ^ 2 = (∑ i : Fin n, g (ξ i)) ^ 2 / q ^ 2 from
      fun ξ => div_pow _ _ _]
    rw [integral_div, hsumInt, hqsq, div_self hN.ne']
  let A : Set (Fin n → Ω) := {ξ | 16 * q < W ξ ^ 2}
  have hAm : MeasurableSet A := measurableSet_lt measurable_const (hWm.pow_const 2)
  have hmark : (16 * q) * P₀.real A ≤ 1 := by
    calc
      (16 * q) * P₀.real A = ∫ ξ, A.indicator (fun _ => 16 * q) ξ ∂P₀ := by
        rw [integral_indicator_const _ hAm, smul_eq_mul, mul_comm]
      _ ≤ ∫ ξ, W ξ ^ 2 ∂P₀ := by
        apply integral_mono ((integrable_const _).indicator hAm) hWi
        intro ξ
        by_cases hξ : ξ ∈ A
        · rw [Set.indicator_of_mem hξ]
          exact le_of_lt hξ
        · rw [Set.indicator_of_notMem hξ]
          exact sq_nonneg _
      _ = 1 := hWsecond
  have hAprob : P₀.real A ≤ 1 / (16 * q) :=
    (le_div_iff₀ (by positivity : 0 < 16 * q)).2 (by simpa only [mul_comm] using hmark)
  have hGsub : Gᶜ ⊆ {ξ | Vsq ξ ≤ (1 / 2 : ℝ)} ∪ A := by
    intro ξ hξ
    by_cases hV : (1 / 2 : ℝ) ≤ Vsq ξ
    · right
      have hbad : ¬ |W ξ| ≤ Real.sqrt q * (4 + Real.sqrt (Vsq ξ)) := by
        intro hh
        exact hξ ⟨hV, hh⟩
      have hlarge : 4 * Real.sqrt q < |W ξ| := by
        have hbase : 4 * Real.sqrt q ≤ Real.sqrt q * (4 + Real.sqrt (Vsq ξ)) := by
          nlinarith only [mul_nonneg (Real.sqrt_nonneg q) (Real.sqrt_nonneg (Vsq ξ))]
        exact hbase.trans_lt (lt_of_not_ge hbad)
      change 16 * q < W ξ ^ 2
      have hmul : 0 < (|W ξ| - 4 * Real.sqrt q) * (|W ξ| + 4 * Real.sqrt q) :=
        mul_pos (by linarith only [hlarge])
          (by linarith only [hlarge, Real.sqrt_nonneg q])
      nlinarith only [hmul, sq_abs (W ξ), Real.sq_sqrt hq.le]
    · exact Or.inl (le_of_lt (lt_of_not_ge hV))
  refine ⟨hGm, hWi, hWsecond, hlow, ?_⟩
  calc
    P₀.real Gᶜ ≤ P₀.real ({ξ | Vsq ξ ≤ (1 / 2 : ℝ)} ∪ A) := measureReal_mono hGsub
    _ ≤ P₀.real {ξ | Vsq ξ ≤ (1 / 2 : ℝ)} + P₀.real A := measureReal_union_le _ _
    _ ≤ Real.exp (-(1 / (512 * K ^ 2)) * (n : ℝ)) + 1 / (16 * q) :=
      add_le_add hlow hAprob

theorem original_projection_compact_good_event
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgmean : (∫ o, g o ∂μ) = 0)
    (hgsecond : (∫ o, g o ^ 2 ∂μ) = 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ), 0 < n →
        let P₀ : Measure (Fin n → Ω) :=
          Measure.pi (fun _ : Fin n => μ)
        let Vsq : (Fin n → Ω) → ℝ := fun ξ =>
          (∑ i : Fin n, g (ξ i) ^ 2) / (n : ℝ)
        let W : (Fin n → Ω) → ℝ := fun ξ =>
          (∑ i : Fin n, g (ξ i)) / Real.sqrt (n : ℝ)
        let G : Set (Fin n → Ω) := {ξ |
          (1 / 2 : ℝ) ≤ Vsq ξ ∧
          |W ξ| ≤ Real.sqrt (Real.sqrt (n : ℝ)) *
            (4 + Real.sqrt (Vsq ξ))}
        MeasurableSet G ∧
          Integrable (fun ξ => W ξ ^ 2) P₀ ∧
          (∫ ξ, W ξ ^ 2 ∂P₀) = 1 ∧
          P₀.real {ξ | Vsq ξ ≤ (1 / 2 : ℝ)} ≤
            Real.exp (-c * (n : ℝ)) ∧
          P₀.real Gᶜ ≤ Real.exp (-c * (n : ℝ)) +
            1 / (16 * Real.sqrt (n : ℝ)) := by
  classical
  let f : ℕ → Ω → ℝ := fun m o =>
    max (-((m : ℝ) + 1)) (min (g o) ((m : ℝ) + 1))
  have hclip (K : ℝ) (hK : 0 ≤ K) (o : Ω) :
      (max (-K) (min (g o) K)) ^ 2 ≤ g o ^ 2 := by
    by_cases hlo : g o ≤ -K
    · have hmin : g o ≤ K := by linarith
      rw [min_eq_left hmin, max_eq_left hlo]
      have hab : K ≤ |g o| := by linarith [neg_le_abs (g o)]
      have hh := pow_le_pow_left₀ hK hab 2
      simpa only [neg_sq, sq_abs] using hh
    · by_cases hhi : K ≤ g o
      · rw [min_eq_right hhi, max_eq_right (by linarith : -K ≤ K)]
        have hh := pow_le_pow_left₀ hK (hhi.trans (le_abs_self _)) 2
        simpa only [sq_abs] using hh
      · rw [min_eq_left (le_of_not_ge hhi), max_eq_right (le_of_not_ge hlo)]
  have hmeas (m : ℕ) : AEStronglyMeasurable (fun o => f m o ^ 2) μ := by
    dsimp only [f]
    exact (measurable_const.max (hg.min measurable_const) |>.pow_const 2).aestronglyMeasurable
  have hbound (m : ℕ) : ∀ᵐ o ∂μ, ‖f m o ^ 2‖ ≤ g o ^ 2 := by
    exact ae_of_all μ fun o => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hclip ((m : ℝ) + 1) (by positivity) o
  have hpoint : ∀ᵐ o ∂μ,
      Filter.Tendsto (fun m : ℕ => f m o ^ 2) Filter.atTop (nhds (g o ^ 2)) := by
    apply ae_of_all μ
    intro o
    obtain ⟨M, hM⟩ := exists_nat_gt |g o|
    have heq : Filter.EventuallyEq Filter.atTop
        (fun m : ℕ => f m o ^ 2) (fun _ : ℕ => g o ^ 2) := by
      filter_upwards [Filter.eventually_ge_atTop M] with m hm
      have hMm : (M : ℝ) ≤ m := by exact_mod_cast hm
      have hlarge : |g o| ≤ (m : ℝ) + 1 := by linarith
      rcases abs_le.mp hlarge with ⟨hlo, hhi⟩
      simp only [f, min_eq_left hhi, max_eq_right hlo]
    exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds
  have hlim := tendsto_integral_of_dominated_convergence
    (fun o => g o ^ 2) hmeas hg2.integrable_sq hbound hpoint
  rw [hgsecond] at hlim
  have hevent : ∀ᶠ m : ℕ in Filter.atTop, (3 / 4 : ℝ) < ∫ o, f m o ^ 2 ∂μ :=
    hlim.eventually (Ioi_mem_nhds (by norm_num : (3 / 4 : ℝ) < 1))
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hevent
  let K : ℝ := (M : ℝ) + 1
  have hK : 1 ≤ K := by
    dsimp only [K]
    have hh : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hsecond : (3 / 4 : ℝ) ≤ ∫ o, (max (-K) (min (g o) K)) ^ 2 ∂μ :=
    (hM M le_rfl).le
  have hs := projection_compact_good_event_of_clip_second μ g hg hg2 hgmean hgsecond K hK hsecond
  exact ⟨1 / (512 * K ^ 2), hs.1, hs.2⟩

theorem original_projection_compact_good_event_fixed_p
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgmean : (∫ o, g o ∂μ) = 0)
    (hgsecond : (∫ o, g o ^ 2 ∂μ) = 1)
    (p : ℝ) (hp2 : 2 < p) (hp3 : p ≤ 3)
    (hgp : Integrable (fun o => Real.rpow |g o| p) μ)
    (Bp : ℝ) (hBp : 1 ≤ Bp)
    (hgmoment : (∫ o, Real.rpow |g o| p ∂μ) ≤ Bp) :
    let K : ℝ := Real.rpow (4 * Bp) (1 / (p - 2))
    let c : ℝ := 1 / (512 * K ^ 2)
    0 < c ∧
      ∀ (n : ℕ), 0 < n →
        let P₀ : Measure (Fin n → Ω) :=
          Measure.pi (fun _ : Fin n => μ)
        let Vsq : (Fin n → Ω) → ℝ := fun ξ =>
          (∑ i : Fin n, g (ξ i) ^ 2) / (n : ℝ)
        let W : (Fin n → Ω) → ℝ := fun ξ =>
          (∑ i : Fin n, g (ξ i)) / Real.sqrt (n : ℝ)
        let G : Set (Fin n → Ω) := {ξ |
          (1 / 2 : ℝ) ≤ Vsq ξ ∧
          |W ξ| ≤ Real.sqrt (Real.sqrt (n : ℝ)) *
            (4 + Real.sqrt (Vsq ξ))}
        MeasurableSet G ∧
          P₀.real {ξ | Vsq ξ ≤ (1 / 2 : ℝ)} ≤
            Real.exp (-c * (n : ℝ)) ∧
          P₀.real Gᶜ ≤ Real.exp (-c * (n : ℝ)) +
            1 / (16 * Real.sqrt (n : ℝ)) := by
  classical
  let K : ℝ := Real.rpow (4 * Bp) (1 / (p - 2))
  have hp : 0 < p - 2 := by linarith
  have hbase : 0 < 4 * Bp := by linarith
  have hKpos : 0 < K := Real.rpow_pos_of_pos hbase _
  have hK : 1 ≤ K := by
    have hh := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith : (1 : ℝ) ≤ 4 * Bp) (by positivity : 0 ≤ 1 / (p - 2))
    simpa only [K, Real.rpow_eq_pow, Real.one_rpow] using hh
  have hKpow : Real.rpow K (p - 2) = 4 * Bp := by
    dsimp only [K]
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul hbase.le]
    have heq : 1 / (p - 2) * (p - 2) = 1 := by field_simp [hp.ne']
    rw [heq, Real.rpow_one]
  have hKrpos : 0 < Real.rpow K (p - 2) := Real.rpow_pos_of_pos hKpos _
  let f : Ω → ℝ := fun o => max (-K) (min (g o) K)
  have hf : Measurable f := measurable_const.max (hg.min measurable_const)
  have hfb (o : Ω) : |f o| ≤ K := by
    exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have hfi : Integrable (fun o => f o ^ 2) μ := by
    apply (integrable_const (K ^ 2)).mono' (hf.pow_const 2).aestronglyMeasurable
    exact ae_of_all μ fun o => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (f o)) (hfb o) 2
  have hpoint (o : Ω) : g o ^ 2 - f o ^ 2 ≤
      Real.rpow |g o| p / Real.rpow K (p - 2) := by
    by_cases hsmall : |g o| ≤ K
    · rcases abs_le.mp hsmall with ⟨hlo, hhi⟩
      have heq : f o = g o := by simp only [f, min_eq_left hhi, max_eq_right hlo]
      rw [heq, sub_self]
      exact div_nonneg (Real.rpow_nonneg (abs_nonneg _) _) hKrpos.le
    · have hlarge : K < |g o| := lt_of_not_ge hsmall
      have hu : 0 < |g o| := hKpos.trans hlarge
      have hmono : Real.rpow K (p - 2) ≤ Real.rpow |g o| (p - 2) :=
        Real.rpow_le_rpow hKpos.le hlarge.le hp.le
      have heq : |g o| ^ 2 * Real.rpow |g o| (p - 2) = Real.rpow |g o| p := by
        simp only [Real.rpow_eq_pow]
        rw [← Real.rpow_natCast |g o| 2, ← Real.rpow_add hu]
        congr 1
        ring
      have hmul : g o ^ 2 * Real.rpow K (p - 2) ≤ Real.rpow |g o| p := by
        have hh := mul_le_mul_of_nonneg_left hmono (sq_nonneg |g o|)
        rw [heq] at hh
        simpa only [sq_abs] using hh
      apply (le_div_iff₀ hKrpos).2
      nlinarith [mul_nonneg (sq_nonneg (f o)) hKrpos.le]
  have hdiff : (∫ o, g o ^ 2 ∂μ) - (∫ o, f o ^ 2 ∂μ) ≤
      (∫ o, Real.rpow |g o| p ∂μ) / Real.rpow K (p - 2) := by
    calc
      (∫ o, g o ^ 2 ∂μ) - (∫ o, f o ^ 2 ∂μ) =
          ∫ o, g o ^ 2 - f o ^ 2 ∂μ := (integral_sub hg2.integrable_sq hfi).symm
      _ ≤ ∫ o, Real.rpow |g o| p / Real.rpow K (p - 2) ∂μ :=
        integral_mono (hg2.integrable_sq.sub hfi) (hgp.div_const _) hpoint
      _ = _ := integral_div _ _
  have hcap : (∫ o, Real.rpow |g o| p ∂μ) / Real.rpow K (p - 2) ≤ (1 / 4 : ℝ) := by
    rw [hKpow]
    apply (div_le_iff₀ hbase).2
    nlinarith
  have hsecond : (3 / 4 : ℝ) ≤ ∫ o, (max (-K) (min (g o) K)) ^ 2 ∂μ := by
    rw [hgsecond] at hdiff
    change (3 / 4 : ℝ) ≤ ∫ o, f o ^ 2 ∂μ
    linarith
  have hs := projection_compact_good_event_of_clip_second μ g hg hg2 hgmean hgsecond K hK hsecond
  refine ⟨hs.1, ?_⟩
  intro n hn
  have hh := hs.2 n hn
  dsimp only at hh ⊢
  exact ⟨hh.1, hh.2.2.2.1, hh.2.2.2.2⟩

theorem actual_uncentered_compact_localization_events
    {Ω : Type*} [MeasurableSpace Ω]
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
        let P₀ : Measure (Fin n → Ω) :=
          Measure.pi (fun _ : Fin n => μ)
        let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
          Shao.OQ6.ResidualDeletion.rowSum
            (fun j k => r (ξ j) (ξ k)) i
        let Λsq : (Fin n → Ω) → ℝ := fun ξ =>
          ∑ i : Fin n, ψ ξ i ^ 2
        let B : (Fin n → Ω) → ℝ := fun ξ =>
          4096 * (s / Real.sqrt (n : ℝ) +
            Λsq ξ / (s * ((n : ℝ) ^ 2 * Real.sqrt (n : ℝ))))
        let Vsq : (Fin n → Ω) → ℝ := fun ξ =>
          (∑ i : Fin n, g (ξ i) ^ 2) / (n : ℝ)
        let W : (Fin n → Ω) → ℝ := fun ξ =>
          (∑ i : Fin n, g (ξ i)) / Real.sqrt (n : ℝ)
        let J : (Fin n → Ω) → ℝ := fun ξ =>
          Shao.OQ6.FiniteRows.uncenteredSq
            (fun i j => h (ξ i) (ξ j))
        let D₂ : (Fin n → Ω) → ℝ := fun ξ =>
          if 0 < Vsq ξ then J ξ / Vsq ξ - 1 else 0
        let G : Set (Fin n → Ω) := {ξ |
          (1 / 2 : ℝ) ≤ Vsq ξ ∧
          |W ξ| ≤ Real.sqrt (Real.sqrt (n : ℝ)) *
            (4 + Real.sqrt (Vsq ξ))}
        let Hcpt : Set (Fin n → Ω) := {ξ |
          ξ ∈ G ∧ -(1 / 2 : ℝ) ≤ D₂ ξ}
        MeasurableSet G ∧ MeasurableSet Hcpt ∧
          Integrable Λsq P₀ ∧ Integrable B P₀ ∧
          (∫ ξ, B ξ ∂P₀) ≤
            8192 * s / Real.sqrt (n : ℝ) ∧
          P₀.real Gᶜ ≤ Real.exp (-c * (n : ℝ)) +
            1 / (16 * Real.sqrt (n : ℝ)) ∧
          P₀.real {ξ | ξ ∈ G ∧ D₂ ξ < -(1 / 2 : ℝ)} ≤
            16384 * s / Real.sqrt (n : ℝ) ∧
          P₀.real Hcptᶜ ≤ Real.exp (-c * (n : ℝ)) +
            ((1 / 16 : ℝ) + 16384 * s) / Real.sqrt (n : ℝ) ∧
          (∀ ξ ∈ Hcpt, (1 / 2 : ℝ) ≤ Vsq ξ ∧
            (1 / 2 : ℝ) ≤ 1 + D₂ ξ ∧ (1 / 4 : ℝ) ≤ J ξ) := by
  classical
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
  let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
  let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
  let s : ℝ := 1 + Real.sqrt v
  have hdata := Shao.OQ6.ActualQuadraticTiltMoments.actual_quadratic_source_moments
    μ h hh hh2 hhsymm hcenter hprojectionsecond 3 (by omega) 0 (by norm_num) (by positivity)
  dsimp only at hdata
  rcases hdata with ⟨hg, hg2, hgmean, hgsecond, hr, hr2, hrsymm, hrcan, hv, hs, hvs, hrest⟩
  change Measurable g at hg
  change MemLp g 2 μ at hg2
  change (∫ o, g o ∂μ) = 0 at hgmean
  change (∫ o, g o ^ 2 ∂μ) = 1 at hgsecond
  change Measurable (fun t : Ω × Ω => r t.1 t.2) at hr
  change MemLp (fun t : Ω × Ω => r t.1 t.2) 2 (μ.prod μ) at hr2
  change (∀ o y, r o y = r y o) at hrsymm
  change (∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0) at hrcan
  change 1 ≤ s at hs
  change v ≤ s ^ 2 at hvs
  obtain ⟨c, hc, hproj⟩ := original_projection_compact_good_event μ g hg hg2 hgmean hgsecond
  refine ⟨c, hc, ?_⟩
  intro n hn
  dsimp only
  let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    Shao.OQ6.ResidualDeletion.rowSum (fun j k => r (ξ j) (ξ k)) i
  let Λsq : (Fin n → Ω) → ℝ := fun ξ => ∑ i : Fin n, ψ ξ i ^ 2
  let B : (Fin n → Ω) → ℝ := fun ξ =>
    4096 * (s / Real.sqrt (n : ℝ) +
      Λsq ξ / (s * ((n : ℝ) ^ 2 * Real.sqrt (n : ℝ))))
  let Vsq : (Fin n → Ω) → ℝ := fun ξ => (∑ i : Fin n, g (ξ i) ^ 2) / (n : ℝ)
  let W : (Fin n → Ω) → ℝ := fun ξ => (∑ i : Fin n, g (ξ i)) / Real.sqrt (n : ℝ)
  let J : (Fin n → Ω) → ℝ := fun ξ =>
    Shao.OQ6.FiniteRows.uncenteredSq (fun i j => h (ξ i) (ξ j))
  let D₂ : (Fin n → Ω) → ℝ := fun ξ => if 0 < Vsq ξ then J ξ / Vsq ξ - 1 else 0
  let G : Set (Fin n → Ω) := {ξ | (1 / 2 : ℝ) ≤ Vsq ξ ∧
    |W ξ| ≤ Real.sqrt (Real.sqrt (n : ℝ)) * (4 + Real.sqrt (Vsq ξ))}
  let Hcpt : Set (Fin n → Ω) := {ξ | ξ ∈ G ∧ -(1 / 2 : ℝ) ≤ D₂ ξ}
  change MeasurableSet G ∧ MeasurableSet Hcpt ∧
    Integrable Λsq P₀ ∧ Integrable B P₀ ∧
    (∫ ξ, B ξ ∂P₀) ≤ 8192 * s / Real.sqrt (n : ℝ) ∧
    P₀.real Gᶜ ≤ Real.exp (-c * (n : ℝ)) + 1 / (16 * Real.sqrt (n : ℝ)) ∧
    P₀.real {ξ | ξ ∈ G ∧ D₂ ξ < -(1 / 2 : ℝ)} ≤ 16384 * s / Real.sqrt (n : ℝ) ∧
    P₀.real Hcptᶜ ≤ Real.exp (-c * (n : ℝ)) +
      ((1 / 16 : ℝ) + 16384 * s) / Real.sqrt (n : ℝ) ∧
    (∀ ξ ∈ Hcpt, (1 / 2 : ℝ) ≤ Vsq ξ ∧ (1 / 2 : ℝ) ≤ 1 + D₂ ξ ∧ (1 / 4 : ℝ) ≤ J ξ)
  letI : IsProbabilityMeasure P₀ := inferInstance
  let N : ℝ := (n : ℝ)
  let q : ℝ := Real.sqrt N
  have hN3 : 3 ≤ N := by
    change (3 : ℝ) ≤ (n : ℝ)
    exact_mod_cast hn
  have hN : 0 < N := by linarith
  have hq : 0 < q := Real.sqrt_pos.mpr hN
  have hspos : 0 < s := by linarith
  have hden : 0 < s * (N ^ 2 * q) := by positivity
  have hp := hproj n (by omega)
  dsimp only at hp
  change MeasurableSet G ∧ Integrable (fun ξ => W ξ ^ 2) P₀ ∧
    (∫ ξ, W ξ ^ 2 ∂P₀) = 1 ∧
    P₀.real {ξ | Vsq ξ ≤ (1 / 2 : ℝ)} ≤ Real.exp (-c * (n : ℝ)) ∧
    P₀.real Gᶜ ≤ Real.exp (-c * (n : ℝ)) + 1 / (16 * q) at hp
  have hGm : MeasurableSet G := hp.1
  have hGprob := hp.2.2.2.2
  have hVm : Measurable Vsq := by dsimp [Vsq]; fun_prop
  have hJm : Measurable J := by
    dsimp [J, Shao.OQ6.FiniteRows.uncenteredSq, Shao.OQ6.FiniteRows.rowMean]
    fun_prop
  have hDm : Measurable D₂ :=
    Measurable.ite (measurableSet_lt measurable_const hVm)
      ((hJm.div hVm).sub_const 1) measurable_const
  have hHm : MeasurableSet Hcpt := hGm.inter (measurableSet_le measurable_const hDm)
  have hρeq : μ.withDensity (fun _ => ENNReal.ofReal (1 : ℝ)) = μ := by
    apply Measure.ext
    intro A hA
    rw [withDensity_apply _ hA]
    simp
  have hrow := Shao.OQ6.FiniteTiltedMoments.row_square_sum_moment μ r hr hr2 hrsymm hrcan
    s hspos.le hvs (fun _ => 1) measurable_const 1
    (fun _ => by norm_num) (fun _ => by norm_num) (by simp)
    0 (by norm_num) (by simp) n
  dsimp only at hrow
  rw [hρeq] at hrow
  simp only [one_pow, zero_pow (by decide : 2 ≠ 0),
    mul_zero, add_zero, mul_one] at hrow
  rcases hrow with ⟨hρ, hP, hψ2, hΛ, hΛeq, hΛbound⟩
  change Integrable Λsq P₀ at hΛ
  change (∫ ξ, Λsq ξ ∂P₀) ≤ (2 * (n.choose 2 : ℝ)) * s ^ 2 at hΛbound
  have hchoose : 2 * (n.choose 2 : ℝ) = N * (N - 1) := by
    have hh := Shao.OQ5.P35.pairCount_eq_choose n
    unfold Shao.OQ5.P35.pairCount at hh
    dsimp only [N]
    linarith
  have hcoeff : 2 * (n.choose 2 : ℝ) ≤ N ^ 2 := by rw [hchoose]; nlinarith
  have hΛN : (∫ ξ, Λsq ξ ∂P₀) ≤ N ^ 2 * s ^ 2 :=
    hΛbound.trans (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg s))
  have hBi : Integrable B P₀ :=
    ((integrable_const (s / q)).add (hΛ.div_const (s * (N ^ 2 * q)))).const_mul 4096
  have hΛnon (ξ : Fin n → Ω) : 0 ≤ Λsq ξ :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hBnon (ξ : Fin n → Ω) : 0 ≤ B ξ := by
    dsimp only [B]
    exact mul_nonneg (by norm_num)
      (add_nonneg (div_nonneg hspos.le hq.le) (div_nonneg (hΛnon ξ) hden.le))
  have hBint : (∫ ξ, B ξ ∂P₀) ≤ 8192 * s / q := by
    have hquot : (∫ ξ, Λsq ξ ∂P₀) / (s * (N ^ 2 * q)) ≤ s / q := by
      apply (div_le_iff₀ hden).2
      calc
        (∫ ξ, Λsq ξ ∂P₀) ≤ N ^ 2 * s ^ 2 := hΛN
        _ = s / q * (s * (N ^ 2 * q)) := by field_simp [hq.ne']
    have hBeq : (∫ ξ, B ξ ∂P₀) =
        4096 * (s / q + (∫ ξ, Λsq ξ ∂P₀) / (s * (N ^ 2 * q))) := by
      change (∫ ξ, 4096 * (s / q + Λsq ξ / (s * (N ^ 2 * q))) ∂P₀) = _
      rw [integral_const_mul, integral_add (integrable_const _) (hΛ.div_const _),
        integral_const, probReal_univ, one_smul, integral_div]
    rw [hBeq]
    calc
      4096 * (s / q + (∫ ξ, Λsq ξ ∂P₀) / (s * (N ^ 2 * q)))
          ≤ 4096 * (s / q + s / q) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hquot) (by norm_num)
      _ = 8192 * s / q := by ring
  let E : Set (Fin n → Ω) := {ξ | ξ ∈ G ∧ D₂ ξ < -(1 / 2 : ℝ)}
  have hEm : MeasurableSet E := hGm.inter (measurableSet_lt hDm measurable_const)
  have hEprob : P₀.real E ≤ 16384 * s / q := by
    by_cases hscale : s ≤ q
    · have henvelope (ξ : Fin n → Ω) (hξ : ξ ∈ G) : |D₂ ξ| ≤ B ξ := by
        have hV : (1 / 2 : ℝ) ≤ Vsq ξ := hξ.1
        have hVpos : 0 < Vsq ξ := by linarith
        have hW := hξ.2
        have hH : (fun i j : Fin n => g (ξ i) + g (ξ j) + r (ξ i) (ξ j)) =
            (fun i j : Fin n => h (ξ i) (ξ j)) := by
          funext i j
          dsimp only [r]
          ring
        have he := Shao.OQ6.ActualRemainderEnvelope.actual_uncentered_remainder_envelope
          (fun i => g (ξ i)) (fun i j => r (ξ i) (ξ j))
          (fun i j => hrsymm (ξ i) (ξ j)) hn 1 (by norm_num) s hs (by simpa using hscale)
        dsimp only at he
        simp only [Real.sqrt_one, one_mul, mul_one] at he
        rw [hH] at he
        have hbound := he hV hW
        change |J ξ / Vsq ξ - 1| ≤ B ξ at hbound
        simpa only [D₂, if_pos hVpos] using hbound
      have hmark : (1 / 2 : ℝ) * P₀.real E ≤ ∫ ξ, B ξ ∂P₀ := by
        calc
          (1 / 2 : ℝ) * P₀.real E = ∫ ξ, E.indicator (fun _ => (1 / 2 : ℝ)) ξ ∂P₀ := by
            rw [integral_indicator_const _ hEm, smul_eq_mul, mul_comm]
          _ ≤ ∫ ξ, B ξ ∂P₀ := by
            apply integral_mono ((integrable_const _).indicator hEm) hBi
            intro ξ
            by_cases hξ : ξ ∈ E
            · rw [Set.indicator_of_mem hξ]
              have hbound := henvelope ξ hξ.1
              have hneg := hξ.2
              have hh := (neg_le_abs (D₂ ξ)).trans hbound
              linarith
            · rw [Set.indicator_of_notMem hξ]
              exact hBnon ξ
      calc
        P₀.real E = 2 * ((1 / 2 : ℝ) * P₀.real E) := by ring
        _ ≤ 2 * (8192 * s / q) :=
          mul_le_mul_of_nonneg_left (hmark.trans hBint) (by norm_num)
        _ = 16384 * s / q := by ring
    · have hlarge : q < s := lt_of_not_ge hscale
      have hone : (1 : ℝ) ≤ 16384 * s / q := by
        apply (le_div_iff₀ hq).2
        nlinarith only [hlarge, hq]
      exact (measureReal_le_one (μ := P₀) (s := E)).trans hone
  have hHsub : Hcptᶜ ⊆ Gᶜ ∪ E := by
    intro ξ hξ
    by_cases hG : ξ ∈ G
    · right
      refine ⟨hG, ?_⟩
      by_contra hnot
      exact hξ ⟨hG, le_of_not_gt hnot⟩
    · exact Or.inl hG
  have hHprob : P₀.real Hcptᶜ ≤ Real.exp (-c * (n : ℝ)) +
      ((1 / 16 : ℝ) + 16384 * s) / q := by
    calc
      P₀.real Hcptᶜ ≤ P₀.real (Gᶜ ∪ E) := measureReal_mono hHsub
      _ ≤ P₀.real Gᶜ + P₀.real E := measureReal_union_le _ _
      _ ≤ (Real.exp (-c * (n : ℝ)) + 1 / (16 * q)) + 16384 * s / q :=
        add_le_add hGprob hEprob
      _ = _ := by field_simp [hq.ne']; ring
  refine ⟨hGm, hHm, hΛ, hBi, hBint, hGprob, hEprob, hHprob, ?_⟩
  intro ξ hξ
  have hV : (1 / 2 : ℝ) ≤ Vsq ξ := hξ.1.1
  have hVpos : 0 < Vsq ξ := by linarith only [hV]
  have hD : (1 / 2 : ℝ) ≤ 1 + D₂ ξ := by linarith only [hξ.2]
  have hratio : J ξ / Vsq ξ = 1 + D₂ ξ := by
    rw [show D₂ ξ = J ξ / Vsq ξ - 1 from if_pos hVpos]
    ring
  have hJ : J ξ = (1 + D₂ ξ) * Vsq ξ := by
    apply (div_eq_iff hVpos.ne').mp
    exact hratio
  refine ⟨hV, hD, ?_⟩
  rw [hJ]
  have hh := mul_le_mul hD hV (by norm_num : (0 : ℝ) ≤ 1 / 2) (by linarith only [hD] : 0 ≤ 1 + D₂ ξ)
  norm_num at hh
  exact hh

end

end Shao.OQ6.CompactGoodEvent
