import Shao.OQ4.BrownianPositiveCDF
import Shao.OQ4.PolygonalKilledFunctionalLimit
import Shao.OQ4.RandomDenominatorFarTail
import Shao.Probability.FiniteIID
import Shao.Probability.MeasurablePath
import Shao.Basic.ClosedSurvival
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

-- Complete local implementation of the parent-frozen proposal; no Lean check yet.
noncomputable section
namespace Shao.OQ4.PositiveBoundaryStudentized
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal Topology
set_option autoImplicit false
variable {Ω : Type*} [MeasurableSpace Ω]

private def infiniteLaw (ν : Measure ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => ν)

private def finiteProjection (n : ℕ) (ω : ℕ → ℝ) : Shao.Path n :=
  fun i => ω i.val

private def squareAverage (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, (ω i) ^ 2) / (n : ℝ)

def energyBad (n : ℕ) (δ : ℝ) : Set (Shao.Path n) :=
  {a | δ * (n : ℝ) < |Shao.energy a - (n : ℝ)|}

private theorem measurable_finiteProjection (n : ℕ) :
    Measurable (finiteProjection n) := by
  exact measurable_pi_iff.mpr fun i => measurable_pi_apply i.val

private theorem finiteProjection_map_eq_pi
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) :
    (infiniteLaw ν).map (finiteProjection n) = Measure.pi (fun _ : Fin n => ν) := by
  letI : IsProbabilityMeasure (infiniteLaw ν) := by
    dsimp only [infiniteLaw]
    infer_instance
  have hX (i : Fin n) : Measurable (fun ω : ℕ → ℝ => ω i.val) :=
    measurable_pi_apply i.val
  have hInd : iIndepFun (fun i : ℕ => fun ω : ℕ → ℝ => ω i) (infiniteLaw ν) := by
    exact iIndepFun_infinitePi (P := fun _ : ℕ => ν)
      (X := fun _ : ℕ => (id : ℝ → ℝ)) (fun _ => measurable_id)
  have hLaw (i : Fin n) :
      IdentDistrib (fun ω : ℕ → ℝ => ω i.val) (id : ℝ → ℝ) (infiniteLaw ν) ν := by
    refine ⟨(hX i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa only [infiniteLaw, Measure.map_id] using
      (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) i.val).map_eq
  have hFin : iIndepFun (fun i : Fin n => fun ω : ℕ → ℝ => ω i.val) (infiniteLaw ν) :=
    hInd.precomp Fin.val_injective
  exact Shao.Probability.iid_samplePath_map_eq_pi hX hFin hLaw

private theorem projection_energy (n : ℕ) (ω : ℕ → ℝ) :
    Shao.energy (finiteProjection n ω) = ∑ i ∈ Finset.range n, (ω i) ^ 2 := by
  simpa only [Shao.energy, finiteProjection] using
    Fin.sum_univ_eq_sum_range (fun i : ℕ => (ω i) ^ 2) n

private theorem measurable_squareAverage (n : ℕ) : Measurable (squareAverage n) := by
  classical
  unfold squareAverage
  fun_prop

private theorem squareAverage_ae_tendsto
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν)
    (hsecond : (∫ z : ℝ, z ^ 2 ∂ν) = 1) :
    ∀ᵐ ω ∂infiniteLaw ν,
      Tendsto (fun n : ℕ => squareAverage n ω) atTop (𝓝 (1 : ℝ)) := by
  letI : IsProbabilityMeasure (infiniteLaw ν) := by
    dsimp only [infiniteLaw]
    infer_instance
  have hLaw (i : ℕ) :
      IdentDistrib (fun ω : ℕ → ℝ => ω i) (id : ℝ → ℝ) (infiniteLaw ν) ν := by
    refine ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa only [infiniteLaw, Measure.map_id] using
      (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) i).map_eq
  have hSqLaw (i : ℕ) : IdentDistrib
      (fun ω : ℕ → ℝ => (ω i) ^ 2) (fun z : ℝ => z ^ 2) (infiniteLaw ν) ν :=
    (hLaw i).sq
  have hInt : Integrable (fun ω : ℕ → ℝ => (ω 0) ^ 2) (infiniteLaw ν) :=
    (hSqLaw 0).symm.integrable_snd hSq
  have hMean : (∫ ω : ℕ → ℝ, (ω 0) ^ 2 ∂infiniteLaw ν) = 1 :=
    (hSqLaw 0).integral_eq.trans hsecond
  have hInd : iIndepFun (fun i : ℕ => fun ω : ℕ → ℝ => (ω i) ^ 2) (infiniteLaw ν) := by
    simpa only [infiniteLaw] using
      (iIndepFun_infinitePi (P := fun _ : ℕ => ν)
        (X := fun _ : ℕ => fun z : ℝ => z ^ 2)
        (fun _ => measurable_id.pow_const 2))
  have hIdent (i : ℕ) : IdentDistrib
      (fun ω : ℕ → ℝ => (ω i) ^ 2) (fun ω : ℕ → ℝ => (ω 0) ^ 2)
      (infiniteLaw ν) (infiniteLaw ν) :=
    (hSqLaw i).trans (hSqLaw 0).symm
  have hs := strong_law_ae_real (fun i : ℕ => fun ω : ℕ → ℝ => (ω i) ^ 2)
    hInt (fun i j hij => hInd.indepFun hij) hIdent
  simpa only [squareAverage, hMean] using hs

private theorem measurableSet_energyBad (n : ℕ) (δ : ℝ) :
    MeasurableSet (energyBad n δ) := by
  exact measurableSet_lt measurable_const
    (continuous_abs.measurable.comp (Shao.measurable_energy.sub_const (n : ℝ)))

private theorem finite_energy_bad_eq_infinite
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) (δ : ℝ) :
    (Measure.pi (fun _ : Fin n => ν)).real (energyBad n δ) =
      (infiniteLaw ν).real {ω | δ * (n : ℝ) <
        |(∑ i ∈ Finset.range n, (ω i) ^ 2) - (n : ℝ)|} := by
  rw [← finiteProjection_map_eq_pi ν n,
    map_measureReal_apply (measurable_finiteProjection n) (measurableSet_energyBad n δ)]
  congr 1
  ext ω
  simp only [mem_preimage, energyBad, mem_setOf_eq, projection_energy]

theorem finite_energy_lln
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun z : ℝ => z ^ 2) ν)
    (hsecond : (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n => ν)).real
      (energyBad n δ)) atTop (𝓝 (0 : ℝ)) := by
  letI : IsProbabilityMeasure (infiniteLaw ν) := by
    dsimp only [infiniteLaw]
    infer_instance
  have hm := tendstoInMeasure_of_tendsto_ae
    (fun n => (measurable_squareAverage n).aestronglyMeasurable)
    (squareAverage_ae_tendsto ν hSq hsecond)
  have hw := (tendstoInMeasure_iff_measureReal_norm.mp hm) δ hδ
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ hw
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [finite_energy_bad_eq_infinite ν n δ]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hratio : squareAverage n ω - 1 =
      ((∑ i ∈ Finset.range n, (ω i) ^ 2) - (n : ℝ)) / (n : ℝ) := by
    dsimp only [squareAverage]
    field_simp [ne_of_gt hnR] <;> ring
  change δ ≤ ‖squareAverage n ω - 1‖
  rw [Real.norm_eq_abs, hratio, abs_div, abs_of_pos hnR]
  exact ((lt_div_iff₀ hnR).mpr hω).le

private theorem integrable_square_of_third
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) ν) :
    Integrable (fun z : ℝ => z ^ 2) ν := by
  have hb := (integrable_const (1 : ℝ)).add h3
  apply hb.mono' (by fun_prop)
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z)]
  change z ^ 2 ≤ 1 + |z| ^ 3
  have hz := abs_nonneg z
  have hz2 : |z| ^ 2 = z ^ 2 := sq_abs z
  by_cases h : |z| ≤ 1
  · nlinarith [mul_nonneg hz (sub_nonneg.mpr h), pow_nonneg hz 3]
  · have hh : 1 ≤ |z| := le_of_not_ge h
    nlinarith [sq_nonneg (|z| - 1),
      mul_nonneg (sub_nonneg.mpr hh) (sq_nonneg |z|)]

private theorem sqrt_nat_tendsto
    (nSeq : ℕ → ℕ) (hn : Tendsto nSeq atTop atTop) :
    Tendsto (fun j => Real.sqrt (nSeq j : ℝ)) atTop atTop := by
  exact Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hn)

private theorem horizon_exact (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (Real.toNNReal ((r ^ 2)⁻¹) : ℝ) * (r * Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) ∧
      PolygonalKilledFunctionalLimit.floorHorizon
        (Real.toNNReal ((r ^ 2)⁻¹)) (r * Real.sqrt (n : ℝ)) = n := by
  have he : (Real.toNNReal ((r ^ 2)⁻¹) : ℝ) *
      (r * Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := by
    rw [Real.coe_toNNReal _ (inv_nonneg.mpr (sq_nonneg r)), mul_pow,
      Real.sq_sqrt (Nat.cast_nonneg n)]
    field_simp [ne_of_gt hr]
  exact ⟨he, by simp only [PolygonalKilledFunctionalLimit.floorHorizon, he,
    Nat.floor_natCast]⟩

private theorem discrete_event_eq_closedStrip
    (n : ℕ) (h : ℝ) (hh : 0 < h) (b : ℝ≥0) :
    PolygonalKilledFunctionalLimit.discreteClosedSurvival n n h 0 b =
      (Shao.closedStrip ((b : ℝ) * h) : Set (Shao.Path n)) := by
  ext a
  change (∀ k : ℕ, k ≤ n → |0 + Shao.prefixSum a k / h| ≤ (b : ℝ)) ↔
    ∀ k : ℕ, k ≤ n → |Shao.prefixSum a k| ≤ (b : ℝ) * h
  simp only [zero_add, abs_div, abs_of_pos hh, div_le_iff₀ hh]

theorem deterministic_positive_boundary_tendsto
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) ν)
    (hmean : (∫ z : ℝ, z ∂ν) = 0)
    (hsecond : (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (nSeq : ℕ → ℕ) (hn : Tendsto nSeq atTop atTop)
    (rSeq : ℕ → ℝ) (r : ℝ) (hr : 0 < r)
    (hrSeq : Tendsto rSeq atTop (𝓝 r)) :
    Tendsto (fun j => (Measure.pi (fun _ : Fin (nSeq j) => ν)).real
      (Shao.closedStrip (rSeq j * Real.sqrt (nSeq j : ℝ)))) atTop
        (𝓝 (Shao.Probability.BrownianSup.probability B P hB r)) := by
  let N : ℕ → ℕ := fun j => max (nSeq j) 1
  let T : ℝ≥0 := Real.toNNReal ((r ^ 2)⁻¹)
  let h : ℕ → ℝ := fun j => r * Real.sqrt (N j : ℝ)
  let b : ℕ → ℝ≥0 := fun j => Real.toNNReal (rSeq j / r)
  have hNpos (j : ℕ) : 0 < N j :=
    lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hN : Tendsto N atTop atTop :=
    tendsto_atTop_mono (fun j => le_max_left (nSeq j) 1) hn
  have hNeq : N =ᶠ[atTop] nSeq := by
    filter_upwards [hn.eventually (eventually_ge_atTop (1 : ℕ))] with j hj
    exact max_eq_left hj
  have hT : 0 < T := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos hr))
  have hpos (j : ℕ) : 0 < h j :=
    mul_pos hr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (hNpos j)))
  have hhor (j : ℕ) : (T : ℝ) * h j ^ 2 ≤ (N j : ℝ) :=
    (horizon_exact r hr (N j)).1.le
  have hinfty : Tendsto h atTop atTop :=
    (sqrt_nat_tendsto N hN).const_mul_atTop hr
  have hb : Tendsto b atTop (𝓝 (1 : ℝ≥0)) := by
    have hd : Tendsto (fun j => rSeq j / r) atTop (𝓝 (1 : ℝ)) := by
      simpa only [div_self (ne_of_gt hr)] using hrSeq.div_const r
    simpa only [b, Real.toNNReal_one] using tendsto_real_toNNReal hd
  have hlim := PolygonalKilledFunctionalLimit.discrete_survival_tendsto_brownian
    B P hB T hT N h (fun _ => ν) (fun _ => inferInstance)
    hpos hhor (fun _ => h3) (fun _ => hmean) (fun _ => hsecond)
    (∫ z : ℝ, |z| ^ 3 ∂ν) (fun _ => le_rfl) hinfty
    b hb (fun _ => 0) 0 tendsto_const_nhds (by norm_num)
  have htime : P.real (BrownianSurvivalBoundary.closedSurvival B T 0) =
      Shao.Probability.BrownianSup.probability B P hB r := by
    rw [BrownianPositiveCDF.survival_time_eq_probability B P hB T hT]
    congr 1
    simp only [T, Real.coe_toNNReal _ (inv_nonneg.mpr (sq_nonneg r)),
      Real.sqrt_inv, Real.sqrt_sq_eq_abs, abs_of_pos hr, one_div, inv_inv]
  rw [htime] at hlim
  apply hlim.congr'
  filter_upwards [hNeq, hrSeq.eventually (eventually_gt_nhds hr)] with j hNj hrj
  rw [(horizon_exact r hr (N j)).2,
    discrete_event_eq_closedStrip (N j) (h j) (hpos j) (b j)]
  have hwall : (b j : ℝ) * h j = rSeq j * Real.sqrt (N j : ℝ) := by
    dsimp only [b, h]
    rw [Real.coe_toNNReal _ (div_nonneg hrj.le hr.le)]
    field_simp [ne_of_gt hr] <;> ring
  rw [hwall, hNj]

private theorem measurableSet_closedStrip (n : ℕ) (w : ℝ) :
    MeasurableSet (Shao.closedStrip w : Set (Shao.Path n)) := by
  simp only [Shao.closedStrip, Set.ofPred_forall]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    measurableSet_le (continuous_abs.measurable.comp (Shao.measurable_prefixSum k))
      measurable_const

private theorem measurableSet_randomDenominatorEvent (n : ℕ) (h : ℝ) :
    MeasurableSet (RandomDenominatorFarTail.randomDenominatorEvent n h) := by
  change MeasurableSet {a : Shao.Path n | ∀ k : ℕ, k ≤ n →
    |Shao.prefixSum a k| ≤ h / Real.sqrt (n : ℝ) * Real.sqrt (Shao.energy a)}
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun k : ℕ => MeasurableSet.iInter fun (_ : k ≤ n) =>
    measurableSet_le (continuous_abs.measurable.comp (Shao.measurable_prefixSum k))
      (measurable_const.mul Shao.measurable_sqrt_energy)

theorem randomDenominatorEvent_eq (n : ℕ) (x : ℝ) :
    RandomDenominatorFarTail.randomDenominatorEvent n (x * Real.sqrt (n : ℝ)) =
      {a : Shao.Path n | a ∈ Shao.closedStrip (x * Real.sqrt (Shao.energy a))} := by
  by_cases hn : n = 0
  · subst n
    ext a
    have he : Shao.energy a = 0 := by simp only [Shao.energy, Finset.univ_eq_empty,
      Finset.sum_empty]
    simp only [RandomDenominatorFarTail.randomDenominatorEvent, Set.mem_ofPred_eq, Nat.cast_zero,
      Real.sqrt_zero, mul_zero, zero_div, zero_mul, he]
  · have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hs : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnR)
    have hcancel : x * Real.sqrt (n : ℝ) / Real.sqrt (n : ℝ) = x := by
      field_simp [hs]
    simp only [RandomDenominatorFarTail.randomDenominatorEvent, hcancel]

private theorem sandwich_sets (n : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ((Shao.closedStrip (x * Real.sqrt (n : ℝ) * Real.sqrt (1 - δ)) :
      Set (Shao.Path n)) \ energyBad n δ) ⊆
        RandomDenominatorFarTail.randomDenominatorEvent n (x * Real.sqrt (n : ℝ)) ∧
    RandomDenominatorFarTail.randomDenominatorEvent n (x * Real.sqrt (n : ℝ)) ⊆
      (Shao.closedStrip (x * Real.sqrt (n : ℝ) * Real.sqrt (1 + δ)) ∪ energyBad n δ) := by
  have hgood (a : Shao.Path n) (ha : a ∉ energyBad n δ) :
      (1 - δ) * (n : ℝ) ≤ Shao.energy a ∧
        Shao.energy a ≤ (1 + δ) * (n : ℝ) := by
    have habs : |Shao.energy a - (n : ℝ)| ≤ δ * (n : ℝ) := le_of_not_gt ha
    have hh := abs_le.mp habs
    constructor <;> linarith
  have hlow (a : Shao.Path n) (ha : a ∉ energyBad n δ) :
      x * Real.sqrt (n : ℝ) * Real.sqrt (1 - δ) ≤ x * Real.sqrt (Shao.energy a) := by
    have hh := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hgood a ha).1) hx
    rw [Real.sqrt_mul (sub_nonneg.mpr hδ1.le)] at hh
    nlinarith
  have hupp (a : Shao.Path n) (ha : a ∉ energyBad n δ) :
      x * Real.sqrt (Shao.energy a) ≤ x * Real.sqrt (n : ℝ) * Real.sqrt (1 + δ) := by
    have hh := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hgood a ha).2) hx
    rw [Real.sqrt_mul (by linarith : 0 ≤ 1 + δ)] at hh
    nlinarith
  simp only [randomDenominatorEvent_eq n x]
  constructor
  · rintro a ⟨ha, hbad⟩ k hk
    exact (ha k hk).trans (hlow a hbad)
  · intro a ha
    by_cases hbad : a ∈ energyBad n δ
    · exact Or.inr hbad
    · exact Or.inl (fun k hk => (ha k hk).trans (hupp a hbad))

theorem sandwich_probability
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (x : ℝ) (hx : 0 ≤ x) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (Measure.pi (fun _ : Fin n => ν)).real
        (Shao.closedStrip (x * Real.sqrt (n : ℝ) * Real.sqrt (1 - δ))) -
      (Measure.pi (fun _ : Fin n => ν)).real (energyBad n δ) ≤
        (Measure.pi (fun _ : Fin n => ν)).real
          (RandomDenominatorFarTail.randomDenominatorEvent n (x * Real.sqrt (n : ℝ))) ∧
    (Measure.pi (fun _ : Fin n => ν)).real
        (RandomDenominatorFarTail.randomDenominatorEvent n (x * Real.sqrt (n : ℝ))) ≤
      (Measure.pi (fun _ : Fin n => ν)).real
        (Shao.closedStrip (x * Real.sqrt (n : ℝ) * Real.sqrt (1 + δ))) +
      (Measure.pi (fun _ : Fin n => ν)).real (energyBad n δ) := by
  classical
  let μ := Measure.pi (fun _ : Fin n => ν)
  let Aminus : Set (Shao.Path n) :=
    Shao.closedStrip (x * Real.sqrt (n : ℝ) * Real.sqrt (1 - δ))
  let Aplus : Set (Shao.Path n) :=
    Shao.closedStrip (x * Real.sqrt (n : ℝ) * Real.sqrt (1 + δ))
  let E := RandomDenominatorFarTail.randomDenominatorEvent n (x * Real.sqrt (n : ℝ))
  have hsets := sandwich_sets n x hx δ hδ hδ1
  have hsub : Aminus ⊆ E ∪ energyBad n δ := by
    intro a ha
    by_cases hbad : a ∈ energyBad n δ
    · exact Or.inr hbad
    · exact Or.inl (hsets.1 ⟨ha, hbad⟩)
  have hlo : μ.real Aminus ≤ μ.real E + μ.real (energyBad n δ) :=
    (measureReal_mono hsub).trans (measureReal_union_le _ _)
  have hup : μ.real E ≤ μ.real Aplus + μ.real (energyBad n δ) :=
    (measureReal_mono hsets.2).trans (measureReal_union_le _ _)
  exact ⟨by linarith, hup⟩

theorem studentized_positive_boundary_tendsto
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) ν)
    (hmean : (∫ z : ℝ, z ∂ν) = 0)
    (hsecond : (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (nSeq : ℕ → ℕ) (hn : Tendsto nSeq atTop atTop)
    (xSeq : ℕ → ℝ) (x : ℝ) (hx : 0 < x)
    (hxSeq : Tendsto xSeq atTop (𝓝 x)) :
    Tendsto (fun j => (Measure.pi (fun _ : Fin (nSeq j) => ν)).real
      (RandomDenominatorFarTail.randomDenominatorEvent (nSeq j)
        (xSeq j * Real.sqrt (nSeq j : ℝ)))) atTop
      (𝓝 (Shao.Probability.BrownianSup.probability B P hB x)) := by
  let F := Shao.Probability.BrownianSup.probability B P hB
  let p : ℕ → ℝ := fun j => (Measure.pi (fun _ : Fin (nSeq j) => ν)).real
    (RandomDenominatorFarTail.randomDenominatorEvent (nSeq j)
      (xSeq j * Real.sqrt (nSeq j : ℝ)))
  have hFc : ContinuousAt F x := BrownianPositiveCDF.probability_continuousAt B P hB x hx
  have hm : Tendsto (fun d : ℝ => F (x * Real.sqrt (1 - d))) (𝓝 (0 : ℝ)) (𝓝 (F x)) := by
    have ha : Tendsto (fun d : ℝ => x * Real.sqrt (1 - d)) (𝓝 (0 : ℝ)) (𝓝 x) := by
      simpa only [sub_zero, Real.sqrt_one, mul_one] using
        (show Continuous (fun d : ℝ => x * Real.sqrt (1 - d)) by fun_prop).tendsto 0
    exact hFc.tendsto.comp ha
  have hp : Tendsto (fun d : ℝ => F (x * Real.sqrt (1 + d))) (𝓝 (0 : ℝ)) (𝓝 (F x)) := by
    have ha : Tendsto (fun d : ℝ => x * Real.sqrt (1 + d)) (𝓝 (0 : ℝ)) (𝓝 x) := by
      simpa only [add_zero, Real.sqrt_one, mul_one] using
        (show Continuous (fun d : ℝ => x * Real.sqrt (1 + d)) by fun_prop).tendsto 0
    exact hFc.tendsto.comp ha
  change Tendsto p atTop (𝓝 (F x))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hquarter : 0 < ε / 4 := by linarith
  have hnear := ((Metric.tendsto_nhds.mp hm) (ε / 4) hquarter).and
    ((Metric.tendsto_nhds.mp hp) (ε / 4) hquarter)
  obtain ⟨η, hη, hηball⟩ := Metric.mem_nhds_iff.mp hnear
  let δ : ℝ := min η 1 / 2
  have hδ : 0 < δ := div_pos (lt_min hη zero_lt_one) (by norm_num)
  have hδ1 : δ < 1 := by
    have hh := min_le_right η (1 : ℝ)
    dsimp only [δ]
    linarith
  have hδη : δ < η := by
    have hh := min_le_left η (1 : ℝ)
    dsimp only [δ]
    linarith
  have hδball : δ ∈ Metric.ball (0 : ℝ) η := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hδ] using hδη
  obtain ⟨hFm, hFp⟩ := hηball hδball
  let qminus : ℕ → ℝ := fun j => (Measure.pi (fun _ : Fin (nSeq j) => ν)).real
    (Shao.closedStrip (xSeq j * Real.sqrt (nSeq j : ℝ) * Real.sqrt (1 - δ)))
  let qplus : ℕ → ℝ := fun j => (Measure.pi (fun _ : Fin (nSeq j) => ν)).real
    (Shao.closedStrip (xSeq j * Real.sqrt (nSeq j : ℝ) * Real.sqrt (1 + δ)))
  let err : ℕ → ℝ := fun j => (Measure.pi (fun _ : Fin (nSeq j) => ν)).real
    (energyBad (nSeq j) δ)
  have hqm : Tendsto qminus atTop (𝓝 (F (x * Real.sqrt (1 - δ)))) := by
    have hh := deterministic_positive_boundary_tendsto B P hB ν h3 hmean hsecond
      nSeq hn (fun j => xSeq j * Real.sqrt (1 - δ)) (x * Real.sqrt (1 - δ))
      (mul_pos hx (Real.sqrt_pos.mpr (sub_pos.mpr hδ1)))
      (hxSeq.mul_const (Real.sqrt (1 - δ)))
    simpa only [qminus, F, mul_assoc, mul_left_comm, mul_comm] using hh
  have hqp : Tendsto qplus atTop (𝓝 (F (x * Real.sqrt (1 + δ)))) := by
    have hh := deterministic_positive_boundary_tendsto B P hB ν h3 hmean hsecond
      nSeq hn (fun j => xSeq j * Real.sqrt (1 + δ)) (x * Real.sqrt (1 + δ))
      (mul_pos hx (Real.sqrt_pos.mpr (by linarith : 0 < 1 + δ)))
      (hxSeq.mul_const (Real.sqrt (1 + δ)))
    simpa only [qplus, F, mul_assoc, mul_left_comm, mul_comm] using hh
  have he : Tendsto err atTop (𝓝 (0 : ℝ)) :=
    (finite_energy_lln ν (integrable_square_of_third ν h3) hsecond δ hδ).comp hn
  filter_upwards [(Metric.tendsto_nhds.mp hqm) (ε / 4) hquarter,
    (Metric.tendsto_nhds.mp hqp) (ε / 4) hquarter,
    (Metric.tendsto_nhds.mp he) (ε / 4) hquarter,
    hxSeq.eventually (eventually_gt_nhds hx)] with j hjm hjp hje hxj
  have hs := sandwich_probability ν (nSeq j) (xSeq j) hxj.le δ hδ hδ1
  have hlo : qminus j - err j ≤ p j := hs.1
  have hup : p j ≤ qplus j + err j := hs.2
  have h1 : |qminus j - F (x * Real.sqrt (1 - δ))| < ε / 4 := by
    simpa only [Real.dist_eq] using hjm
  have h2 : |qplus j - F (x * Real.sqrt (1 + δ))| < ε / 4 := by
    simpa only [Real.dist_eq] using hjp
  have h3e : |err j| < ε / 4 := by simpa only [Real.dist_eq, sub_zero] using hje
  have h4 : |F (x * Real.sqrt (1 - δ)) - F x| < ε / 4 := by
    simpa only [Real.dist_eq] using hFm
  have h5 : |F (x * Real.sqrt (1 + δ)) - F x| < ε / 4 := by
    simpa only [Real.dist_eq] using hFp
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor
  · linarith [(abs_lt.mp h1).1, (abs_lt.mp h3e).2, (abs_lt.mp h4).1]
  · linarith [(abs_lt.mp h2).2, (abs_lt.mp h3e).2, (abs_lt.mp h5).2]

theorem studentized_positive_boundary_ratio_tendsto
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) ν)
    (hmean : (∫ z : ℝ, z ∂ν) = 0)
    (hsecond : (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (nSeq : ℕ → ℕ) (hn : Tendsto nSeq atTop atTop)
    (xSeq : ℕ → ℝ) (x : ℝ) (hx : 0 < x)
    (hxSeq : Tendsto xSeq atTop (𝓝 x)) :
    Tendsto (fun j =>
      (Measure.pi (fun _ : Fin (nSeq j) => ν)).real
        (RandomDenominatorFarTail.randomDenominatorEvent (nSeq j)
          (xSeq j * Real.sqrt (nSeq j : ℝ))) /
      Shao.Probability.BrownianSup.probability B P hB (xSeq j))
      atTop (𝓝 (1 : ℝ)) := by
  have hnum := studentized_positive_boundary_tendsto B P hB ν h3 hmean hsecond
    nSeq hn xSeq x hx hxSeq
  have hden := BrownianPositiveCDF.probability_tendsto B P hB xSeq x hx hxSeq
  have hne := ne_of_gt (BrownianPositiveCDF.probability_pos B P hB x hx)
  have hdiv := hnum.div hden hne
  rw [div_self hne] at hdiv
  exact hdiv

end Shao.OQ4.PositiveBoundaryStudentized
end
