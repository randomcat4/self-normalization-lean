import Shao.OQ3.StageLayerDecomposition
import Mathlib.Probability.Distributions.Gaussian.Real

namespace Shao.OQ3

open MeasureTheory Filter
open scoped BigOperators

noncomputable section

theorem stage_source_layer_conditional_factorization (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q d : ℝ) (hq : 0 < q)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (n : ℕ) (hn : 0 < n)
    (hmass : 0 < (Measure.pi (fun _ : Fin n => mu)).real
      {z : Shao.Path n | normalDeviation q z = d}) :
    (Measure.pi (fun _ : Fin n => mu)).real
        {z : Shao.Path n | normalDeviation q z = d ∧ z ∈ sourceTail q n} =
      (Measure.pi (fun _ : Fin n => mu)).real
          {z : Shao.Path n | normalDeviation q z = d} *
        (normalLayerConditionalLaw mu q (q / 4) d n).real
          {x : ℝ | -((q / 16) * d) ≤ x ^ 2 ∧
            -(Real.sqrt (n : ℝ) * q / 4) < x} := by
  classical
  let nu : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
  let A : Set (Shao.Path n) := {z | normalDeviation q z = d}
  let T : Shao.Path n → ℝ := fun z =>
    ((∑ i, z i) - (n : ℝ) * (q / 4)) / Real.sqrt (n : ℝ)
  let B : Set ℝ := {x | -((q / 16) * d) ≤ x ^ 2 ∧
    -(Real.sqrt (n : ℝ) * q / 4) < x}
  let r : ℝ := Real.sqrt (n : ℝ)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hr : 0 < r := Real.sqrt_pos.2 hnR
  have hrsq : r ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have hcoords : ∀ᵐ z ∂nu, ∀ i : Fin n,
      z i ∈ Set.range (fun j : Fin 4 ⊕ Fin J =>
        stageAtom (fun k : Fin J => addedAtom k.val) j) := by
    rw [ae_all_iff]
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => mu) (i := i)).eventually hrange
  have hE : ∀ᵐ z ∂nu, 0 < Shao.energy z := by
    filter_upwards [hcoords] with z hz
    have hsq (i : Fin n) : 1 ≤ (z i) ^ 2 := by
      obtain ⟨j, hj⟩ := hz i
      have habs : 1 ≤ |z i| := by
        rw [← hj]
        cases j with
        | inl j => exact (fixedAtom_bounds (Sum.inl j)).1
        | inr j => exact (fixedAtom_bounds (Sum.inr j.val)).1
      calc
        (1 : ℝ) = (1 : ℝ) ^ 2 := by norm_num
        _ ≤ |z i| ^ 2 := (sq_le_sq₀ (by norm_num) (abs_nonneg _)).mpr habs
        _ = (z i) ^ 2 := sq_abs _
    have hsum : (n : ℝ) ≤ Shao.energy z := by
      calc
        (n : ℝ) = ∑ _i : Fin n, (1 : ℝ) := by simp
        _ ≤ ∑ i : Fin n, (z i) ^ 2 := Finset.sum_le_sum (fun i _ => hsq i)
        _ = Shao.energy z := rfl
    exact hnR.trans_le hsum
  have hMc : Continuous (fun z : Shao.Path n => normalDeviation q z) := by
    unfold normalDeviation normalValue
    fun_prop
  have hA : MeasurableSet A := (isClosed_eq hMc continuous_const).measurableSet
  have hT : Measurable T := by dsimp [T]; fun_prop
  have hB : MeasurableSet B :=
    (measurableSet_le measurable_const (show Measurable (fun x : ℝ => x ^ 2) by fun_prop)).inter
      (measurableSet_lt measurable_const measurable_id)
  have hA0 : nu A ≠ 0 := ne_of_gt (ENNReal.toReal_pos_iff.mp hmass).1
  have hlaw : normalLayerConditionalLaw mu q (q / 4) d n =
      Measure.map T (ProbabilityTheory.cond nu A) := by
    change (if nu A = 0 then Measure.dirac 0 else
      Measure.map T (ProbabilityTheory.cond nu A)) = _
    rw [ite_eq_right hA0]
  have hset : {z : Shao.Path n | normalDeviation q z = d ∧ z ∈ sourceTail q n}
      =ᵐ[nu] A ∩ T ⁻¹' B := by
    filter_upwards [hE] with z hzE
    apply propext
    change (normalDeviation q z = d ∧ z ∈ sourceTail q n) ↔
      (normalDeviation q z = d ∧ -((q / 16) * d) ≤ T z ^ 2 ∧
        -(r * q / 4) < T z)
    by_cases hz : normalDeviation q z = d
    · have hR : r * T z = tangentDeviation q z := by
        change r * (((∑ i, z i) - (n : ℝ) * (q / 4)) / r) =
          (∑ i, z i) - (n : ℝ) * q / 4
        rw [mul_div_cancel₀ _ hr.ne']
        ring
      have hRsq : tangentDeviation q z ^ 2 = (n : ℝ) * T z ^ 2 := by
        rw [← hR, mul_pow, hrsq]
      have hsum : (∑ i, z i) = r * (T z + r * q / 4) := by
        calc
          _ = r * T z + (n : ℝ) * q / 4 := by
            dsimp [tangentDeviation] at hR
            linarith
          _ = _ := by rw [← hrsq]; ring
      have hsign : 0 < (∑ i, z i) ↔ -(r * q / 4) < T z := by
        rw [hsum, mul_pos_iff_of_pos_left hr]
        constructor <;> intro h <;> linarith
      have hcurve : -((n : ℝ) * q / 16 * d) ≤ tangentDeviation q z ^ 2 ↔
          -((q / 16) * d) ≤ T z ^ 2 := by
        rw [hRsq]
        constructor
        · intro hc
          apply (mul_le_mul_iff_of_pos_left hnR).mp
          convert hc using 1
          ring
        · intro hc
          have hc' := (mul_le_mul_iff_of_pos_left hnR).mpr hc
          convert hc' using 1
          ring
      rw [sourceTail_on_normal_layer q hq n hn z d hz]
      simp only [hz, true_and, hzE, hsign, hcurve]
      exact and_comm
    · simp only [hz, false_and]
  have hmul : normalLayerConditionalLaw mu q (q / 4) d n B * nu A =
      nu (A ∩ T ⁻¹' B) := by
    rw [hlaw, Measure.map_apply hT hB]
    exact ProbabilityTheory.cond_mul_eq_inter hA (T ⁻¹' B) nu
  have hreal := congrArg ENNReal.toReal hmul
  rw [ENNReal.toReal_mul] at hreal
  change nu.real {z : Shao.Path n | normalDeviation q z = d ∧ z ∈ sourceTail q n} =
    nu.real A * (normalLayerConditionalLaw mu q (q / 4) d n).real B
  calc
    _ = (nu (A ∩ T ⁻¹' B)).toReal := congrArg ENNReal.toReal (measure_congr hset)
    _ = (normalLayerConditionalLaw mu q (q / 4) d n B).toReal * (nu A).toReal := hreal.symm
    _ = _ := mul_comm _ _

private theorem square_level_null (G : Measure ℝ) [NullSingletonClass G] (a : ℝ) :
    G {x : ℝ | x ^ 2 = a} = 0 := by
  classical
  have hsub : {x : ℝ | x ^ 2 = a} ⊆ {Real.sqrt a, -Real.sqrt a} := by
    intro x hx
    have ha : 0 ≤ a := by change x ^ 2 = a at hx; nlinarith [sq_nonneg x]
    have hs := Real.sq_sqrt ha
    have hp : (x - Real.sqrt a) * (x + Real.sqrt a) = 0 := by
      change x ^ 2 = a at hx
      nlinarith
    rcases mul_eq_zero.mp hp with hp | hp
    · exact Set.mem_insert_iff.mpr (Or.inl (by linarith))
    · exact Set.mem_insert_of_mem _ (by simp only [Set.mem_singleton_iff]; linarith)
  have hz : G ({Real.sqrt a, -Real.sqrt a} : Set ℝ) = 0 := by
    simpa using (Finset.measure_zero ({Real.sqrt a, -Real.sqrt a} : Finset ℝ) G)
  exact measure_mono_null hsub hz

private theorem square_threshold_frontier_null (G : Measure ℝ) [NullSingletonClass G]
    (a : ℝ) : G (frontier {x : ℝ | a ≤ x ^ 2}) = 0 := by
  have hf : frontier {x : ℝ | a ≤ x ^ 2} ⊆ {x : ℝ | a = x ^ 2} :=
    frontier_le_subset_eq continuous_const (by fun_prop)
  exact measure_mono_null (fun x hx => (hf hx).symm) (square_level_null G a)

private theorem square_threshold_mass_limits (G : Measure ℝ) [IsProbabilityMeasure G]
    [NullSingletonClass G] (a : ℝ) :
    Tendsto (fun k : ℕ => G.real {x : ℝ | a + 1 / (k + 1 : ℝ) ≤ x ^ 2})
        atTop (nhds (G.real {x : ℝ | a ≤ x ^ 2})) ∧
      Tendsto (fun k : ℕ => G.real {x : ℝ | a - 1 / (k + 1 : ℝ) ≤ x ^ 2})
        atTop (nhds (G.real {x : ℝ | a ≤ x ^ 2})) := by
  let C : ℝ → Set ℝ := fun b => {x | b ≤ x ^ 2}
  let delta : ℕ → ℝ := fun k => 1 / (k + 1 : ℝ)
  have hdpos (k : ℕ) : 0 < delta k := by dsimp [delta]; positivity
  have hdanti : Antitone delta := by
    intro k l hkl
    dsimp [delta]
    exact one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hkl 1)
  have hCm (b : ℝ) : MeasurableSet (C b) :=
    measurableSet_le measurable_const (show Measurable (fun x : ℝ => x ^ 2) by fun_prop)
  have hmono : Monotone (fun k => C (a + delta k)) := by
    intro k l hkl x hx
    change a + delta l ≤ x ^ 2
    change a + delta k ≤ x ^ 2 at hx
    have hh := hdanti hkl
    linarith
  have hanti : Antitone (fun k => C (a - delta k)) := by
    intro k l hkl x hx
    change a - delta k ≤ x ^ 2
    change a - delta l ≤ x ^ 2 at hx
    have hh := hdanti hkl
    linarith
  have hu : (⋃ k, C (a + delta k)) = {x : ℝ | a < x ^ 2} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨k, hk⟩
      have hpos := hdpos k
      change a + delta k ≤ x ^ 2 at hk
      linarith
    · intro hx
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
      exact ⟨k, by change a + delta k ≤ x ^ 2; dsimp [delta]; linarith⟩
  have hi : (⋂ k, C (a - delta k)) = C a := by
    ext x
    simp only [Set.mem_iInter]
    constructor
    · intro hx
      change a ≤ x ^ 2
      by_contra h
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr (not_le.mp h))
      have hxk := hx k
      change a - delta k ≤ x ^ 2 at hxk
      dsimp [delta] at hxk
      linarith
    · intro hx k
      have hp := hdpos k
      change a ≤ x ^ 2 at hx
      change a - delta k ≤ x ^ 2
      linarith
  have heq : {x : ℝ | a < x ^ 2} =ᵐ[G] C a := by
    have hn := (measure_eq_zero_iff_ae_notMem).mp (square_level_null G a)
    filter_upwards [hn] with x hx
    apply propext
    change x ^ 2 ≠ a at hx
    change a < x ^ 2 ↔ a ≤ x ^ 2
    exact ⟨le_of_lt, fun h => lt_of_le_of_ne h (Ne.symm hx)⟩
  have hGeq : G {x : ℝ | a < x ^ 2} = G (C a) := measure_congr heq
  have hup : Tendsto (fun k => G (C (a + delta k))) atTop (nhds (G (C a))) := by
    simpa only [Function.comp_def, hu, hGeq] using
      (tendsto_measure_iUnion_atTop (μ := G) hmono)
  have hdown : Tendsto (fun k => G (C (a - delta k))) atTop (nhds (G (C a))) := by
    simpa only [Function.comp_def, hi] using
      (tendsto_measure_iInter_atTop (μ := G)
        (fun k => (hCm (a - delta k)).nullMeasurableSet) hanti
        ⟨0, measure_ne_top G _⟩)
  constructor
  · simpa only [Function.comp_def, measureReal_def] using
      (ENNReal.tendsto_toReal (measure_ne_top G (C a))).comp hup
  · simpa only [Function.comp_def, measureReal_def] using
      (ENNReal.tendsto_toReal (measure_ne_top G (C a))).comp hdown

private theorem moving_curved_probability_tendsto
    (rho : ℕ → Measure ℝ) (hprob : ∀ j, IsProbabilityMeasure (rho j))
    (G : Measure ℝ) [IsProbabilityMeasure G] [NullSingletonClass G]
    (hcont : ∀ A : Set ℝ, G (frontier A) = 0 →
      Tendsto (fun j => (rho j).real A) atTop (nhds (G.real A)))
    (a b : ℕ → ℝ) (a0 : ℝ) (ha : Tendsto a atTop (nhds a0))
    (hb : Tendsto b atTop atBot) :
    Tendsto (fun j => (rho j).real {x : ℝ | a j ≤ x ^ 2 ∧ b j < x})
      atTop (nhds (G.real {x : ℝ | a0 ≤ x ^ 2})) := by
  let C : ℝ → Set ℝ := fun c => {x | c ≤ x ^ 2}
  let E : ℕ → Set ℝ := fun j => {x | a j ≤ x ^ 2 ∧ b j < x}
  let L : ℝ := G.real (C a0)
  have htail : Tendsto (fun k : ℕ => G.real (Set.Iic (-(k : ℝ)))) atTop (nhds 0) := by
    have hanti : Antitone (fun k : ℕ => Set.Iic (-(k : ℝ))) := by
      intro k l hkl x hx
      change x ≤ -(k : ℝ)
      change x ≤ -(l : ℝ) at hx
      have hklR : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hkl
      linarith
    have hi : (⋂ k : ℕ, Set.Iic (-(k : ℝ))) = ∅ := by
      ext x
      constructor
      · intro hx
        obtain ⟨k, hk⟩ := exists_nat_gt (-x)
        have hxk := Set.mem_iInter.mp hx k
        change x ≤ -(k : ℝ) at hxk
        linarith
      · intro hx
        exact False.elim hx
    have ht : Tendsto (fun k : ℕ => G (Set.Iic (-(k : ℝ)))) atTop (nhds 0) := by
      simpa only [Function.comp_def, hi, measure_empty] using
        (tendsto_measure_iInter_atTop (μ := G)
          (fun k : ℕ => measurableSet_Iic.nullMeasurableSet) hanti
          ⟨0, measure_ne_top G _⟩)
    simpa only [Function.comp_def, measureReal_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp ht
  have htnull (k : ℕ) : G (frontier (Set.Iic (-(k : ℝ)))) = 0 :=
    measure_mono_null (frontier_Iic_subset _) (measure_singleton _)
  have hpos (k : ℕ) : 0 < 1 / (k + 1 : ℝ) := by positivity
  have hplus := (square_threshold_mass_limits G a0).1
  have hminus := (square_threshold_mass_limits G a0).2
  apply tendsto_order.2
  constructor
  · intro c hc
    let e : ℝ := (L - c) / 5
    have he : 0 < e := by dsimp [e]; linarith
    have hG : ∀ᶠ k : ℕ in atTop, L - e < G.real (C (a0 + 1 / (k + 1 : ℝ))) :=
      hplus.eventually (Ioi_mem_nhds (by change L - e < L; linarith))
    obtain ⟨k, hk⟩ := hG.exists
    obtain ⟨K, hK⟩ := (htail.eventually (Iio_mem_nhds he)).exists
    have hp := hcont (C (a0 + 1 / (k + 1 : ℝ)))
      (square_threshold_frontier_null G _)
    have hpe : ∀ᶠ j in atTop,
        G.real (C (a0 + 1 / (k + 1 : ℝ))) - e <
          (rho j).real (C (a0 + 1 / (k + 1 : ℝ))) :=
      hp.eventually (Ioi_mem_nhds (by linarith))
    have hte : ∀ᶠ j in atTop,
        (rho j).real (Set.Iic (-(K : ℝ))) < G.real (Set.Iic (-(K : ℝ))) + e :=
      (hcont _ (htnull K)).eventually (Iio_mem_nhds (by linarith))
    have hae : ∀ᶠ j in atTop, a j < a0 + 1 / (k + 1 : ℝ) :=
      ha.eventually (Iio_mem_nhds (by have hh := hpos k; linarith))
    have hbe : ∀ᶠ j in atTop, b j ≤ -(K : ℝ) := hb.eventually_le_atBot _
    filter_upwards [hpe, hte, hae, hbe] with j hjp hjt hja hjb
    let : IsProbabilityMeasure (rho j) := hprob j
    have hsub : C (a0 + 1 / (k + 1 : ℝ)) ⊆ E j ∪ Set.Iic (-(K : ℝ)) := by
      intro x hx
      by_cases hxt : x ≤ -(K : ℝ)
      · exact Or.inr hxt
      · exact Or.inl ⟨hja.le.trans hx, lt_of_le_of_lt hjb (lt_of_not_ge hxt)⟩
    have hle : (rho j).real (C (a0 + 1 / (k + 1 : ℝ))) ≤
        (rho j).real (E j) + (rho j).real (Set.Iic (-(K : ℝ))) :=
      (measureReal_mono (μ := rho j) hsub).trans
        (measureReal_union_le (μ := rho j) _ _)
    change c < (rho j).real (E j)
    dsimp [e] at hk hK hjp hjt
    linarith only [hk, hK, hjp, hjt, hle, hc]
  · intro c hc
    let e : ℝ := (c - L) / 3
    have he : 0 < e := by dsimp [e]; linarith
    have hG : ∀ᶠ k : ℕ in atTop, G.real (C (a0 - 1 / (k + 1 : ℝ))) < L + e :=
      hminus.eventually (Iio_mem_nhds (by change L < L + e; linarith))
    obtain ⟨k, hk⟩ := hG.exists
    have hp := hcont (C (a0 - 1 / (k + 1 : ℝ)))
      (square_threshold_frontier_null G _)
    have hpe : ∀ᶠ j in atTop,
        (rho j).real (C (a0 - 1 / (k + 1 : ℝ))) <
          G.real (C (a0 - 1 / (k + 1 : ℝ))) + e :=
      hp.eventually (Iio_mem_nhds (by linarith))
    have hae : ∀ᶠ j in atTop, a0 - 1 / (k + 1 : ℝ) < a j :=
      ha.eventually (Ioi_mem_nhds (by have hh := hpos k; linarith))
    filter_upwards [hpe, hae] with j hjp hja
    let : IsProbabilityMeasure (rho j) := hprob j
    have hsub : E j ⊆ C (a0 - 1 / (k + 1 : ℝ)) :=
      fun x hx => hja.le.trans hx.1
    have hle := measureReal_mono (μ := rho j) hsub
    change (rho j).real (E j) < c
    dsimp [e] at hk hjp
    linarith only [hk, hjp, hle, hc]

theorem stage_source_weighted_layer_subsequence_tendsto (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q ell : ℝ) (hq : 0 < q)
    (hmeanY : (∫ x : ℝ, normalValue x ∂mu) = q)
    (hmeanX : (∫ x : ℝ, x ∂mu) = q / 4)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (d : ℕ → ℝ) (hd : ∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M)
    (hlayer : ∀ᶠ n : ℕ in atTop, ∃ k : ℤ,
      d n + (n : ℝ) * q = dyadicMesh J * (k : ℝ))
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (d0 : ℝ)
    (hd0 : Tendsto (fun j : ℕ => d (m j)) atTop (nhds d0))
    (hcont : ∀ A : Set ℝ,
      (ProbabilityTheory.gaussianReal 0 (Real.toNNReal (transverseVariance mu)))
          (frontier A) = 0 →
      Tendsto (fun n : ℕ => (normalLayerConditionalLaw mu q (q / 4) (d n) n).real A)
        atTop (nhds ((ProbabilityTheory.gaussianReal 0
          (Real.toNNReal (transverseVariance mu))).real A))) :
    Tendsto (fun j : ℕ => Real.sqrt (m j : ℝ) * Real.exp (-ell * d (m j)) *
        (Measure.pi (fun _ : Fin (m j) => mu)).real
          {z : Shao.Path (m j) | normalDeviation q z = d (m j) ∧
            z ∈ sourceTail q (m j)})
      atTop (nhds (((dyadicMesh J / (2 * Real.pi)) *
          Real.sqrt (2 * Real.pi / normalVariance mu)) * Real.exp (-ell * d0) *
        (ProbabilityTheory.gaussianReal 0 (Real.toNNReal (transverseVariance mu))).real
          {x : ℝ | -((q / 16) * d0) ≤ x ^ 2})) := by
  have hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10 := by
    filter_upwards [hrange] with x hx
    obtain ⟨i, rfl⟩ := hx
    cases i with
    | inl i => exact (fixedAtom_bounds (Sum.inl i)).2
    | inr i => exact (fixedAtom_bounds (Sum.inr i.val)).2
  have hbase (i : Fin 4) : 0 < mu.real {baseAtom i} := by
    exact hpos (Sum.inl i)
  have hS := normalVariance_pos mu hb hbase
  have hD := parabolaCovariance_det_pos mu hb hbase
  have hT := transverseVariance_pos mu hb hbase
  let G : Measure ℝ := ProbabilityTheory.gaussianReal 0 (Real.toNNReal (transverseVariance mu))
  let rho : ℕ → Measure ℝ := fun j => normalLayerConditionalLaw mu q (q / 4) (d (m j)) (m j)
  have : IsProbabilityMeasure G := by dsimp [G]; infer_instance
  have : NullSingletonClass G :=
    ProbabilityTheory.nullSingletonClass_gaussianReal (ne_of_gt (Real.toNNReal_pos.mpr hT))
  have hprob (j : ℕ) : IsProbabilityMeasure (rho j) :=
    normalLayerConditionalLaw_isProbabilityMeasure mu q (q / 4) (d (m j)) (m j)
  have hcont' (A : Set ℝ) (hA : G (frontier A) = 0) :
      Tendsto (fun j => (rho j).real A) atTop (nhds (G.real A)) :=
    (hcont A hA).comp hm
  have ha : Tendsto (fun j => -((q / 16) * d (m j))) atTop
      (nhds (-((q / 16) * d0))) :=
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => q / 16) atTop (nhds (q / 16))).mul hd0).neg
  have hnat : Tendsto (fun j => (m j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hm
  have hroot := Real.tendsto_sqrt_atTop.comp hnat
  have hbot : Tendsto (fun j => -(Real.sqrt (m j : ℝ) * q / 4)) atTop atBot := by
    convert hroot.atTop_mul_const_of_neg (show -q / 4 < 0 by linarith) using 1
    ext j
    dsimp only [Function.comp_def]
    ring
  have hcurve := moving_curved_probability_tendsto rho hprob G hcont'
    (fun j => -((q / 16) * d (m j)))
    (fun j => -(Real.sqrt (m j : ℝ) * q / 4)) (-((q / 16) * d0)) ha hbot
  let C : ℝ := (dyadicMesh J / (2 * Real.pi)) * Real.sqrt (2 * Real.pi / normalVariance mu)
  have hrawC : Tendsto (fun n : ℕ => ((Real.sqrt (n : ℝ) : ℝ) : ℂ) *
      normalLayerCharacteristic mu q (q / 4) (d n) 0 n) atTop (nhds (C : ℂ)) := by
    simpa [C] using stage_normalLayerCharacteristic_scaled_tendsto mu J q (q / 4)
      hb hmeanY hmeanX hS hD hrange hpos 0 d hd hlayer
  have hmasslim : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) *
      (Measure.pi (fun _ : Fin n => mu)).real
        {z : Shao.Path n | normalDeviation q z = d n}) atTop (nhds C) := by
    have hre := (Complex.continuous_re.tendsto _).comp hrawC
    simpa only [Function.comp_def, normalLayerCharacteristic_zero_eq_mass,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using hre
  have hexp : Tendsto (fun j => Real.exp (-ell * d (m j))) atTop
      (nhds (Real.exp (-ell * d0))) :=
    (Real.continuous_exp.tendsto _).comp
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => -ell) atTop (nhds (-ell))).mul hd0)
  have hprod := ((hmasslim.comp hm).mul hexp).mul hcurve
  have hmass := eventually_stage_normalLayer_mass_pos mu J q (q / 4)
    hb hmeanY hmeanX hS hD hrange hpos d hd hlayer
  have heq : (fun j : ℕ =>
      (Real.sqrt (m j : ℝ) * (Measure.pi (fun _ : Fin (m j) => mu)).real
        {z : Shao.Path (m j) | normalDeviation q z = d (m j)}) *
      Real.exp (-ell * d (m j)) * (rho j).real
        {x : ℝ | -((q / 16) * d (m j)) ≤ x ^ 2 ∧
          -(Real.sqrt (m j : ℝ) * q / 4) < x}) =ᶠ[atTop]
      (fun j : ℕ => Real.sqrt (m j : ℝ) * Real.exp (-ell * d (m j)) *
        (Measure.pi (fun _ : Fin (m j) => mu)).real
          {z : Shao.Path (m j) | normalDeviation q z = d (m j) ∧
            z ∈ sourceTail q (m j)}) := by
    filter_upwards [hm.eventually hmass, hm.eventually (eventually_ge_atTop (1 : ℕ))]
      with j hj hjn
    have hn : 0 < m j := by omega
    dsimp [rho]
    rw [stage_source_layer_conditional_factorization mu J q (d (m j)) hq hrange (m j) hn hj]
    ring
  exact hprod.congr' heq

end
end Shao.OQ3
