-- Complete local implementation of the parent-frozen source B0 declarations.
-- Frozen formal SHA256: 558f522be7bc4a4cf8bac12f26b2028a214b1a00602347c85bb661a7174d1047.
-- All19 heads/all3 literal values retained. Unchecked: producer qualification and parent gate pending.
import Shao.OQ4.PolygonalKilledFunctionalLimit
import Shao.OQ4.BrownianSurvivalBoundary
import Shao.OQ4.BrownianKilledCosineIdentity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Sequences
import Mathlib.Topology.ContinuousOn
import Mathlib.Algebra.Order.Floor.Semiring

noncomputable section
namespace Shao.OQ4.BrownianUniformSurvival
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω]

-- PUBLIC actual probability, with no modification/completion of the given B/P.
def brownianSurvival (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (T : ℝ≥0) (u : ℝ) : ℝ :=
  P.real (BrownianSurvivalBoundary.closedSurvival B T u)

-- PUBLIC literal real supremum over ALL physical starting points in [-h,h].
def survivalError (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (T : ℝ≥0) (h : ℝ) : ℝ :=
  sSup ((fun z : ℝ =>
    |killedMass ν h (PolygonalKilledFunctionalLimit.floorHorizon T h) z -
      brownianSurvival B P T (z / h)|) '' Icc (-h) h)

private def rowLength (T : ℝ≥0) (h : ℝ) : ℕ :=
  ⌈(T : ℝ) * h ^ 2⌉₊

private theorem continuous_pathSup_characterization
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (u : ℝ) (ω : Ω)
    (hc : Continuous (B · ω)) :
    ω ∈ BrownianSurvivalBoundary.closedSurvival B T u ↔
      BrownianSurvivalBoundary.pathSup B T u ω ≤ 1 := by
  have hcont : Continuous (fun t : ℝ≥0 => |u + B t ω|) :=
    (continuous_const.add hc).abs
  have hb : BddAbove ((fun t : ℝ≥0 => |u + B t ω|) '' Icc 0 T) :=
    (isCompact_Icc.image hcont).bddAbove
  have hne : ((fun t : ℝ≥0 => |u + B t ω|) '' Icc 0 T).Nonempty :=
    ⟨|u + B 0 ω|, ⟨0, ⟨le_rfl, bot_le⟩, rfl⟩⟩
  change (∀ t : ℝ≥0, t ≤ T → |u + B t ω| ≤ 1) ↔
    sSup ((fun t : ℝ≥0 => |u + B t ω|) '' Icc 0 T) ≤ 1
  constructor
  · intro hs
    apply csSup_le hne
    rintro _ ⟨t, ht, rfl⟩
    exact hs t ht.2
  · intro hs t ht
    exact (le_csSup hb ⟨t, ⟨bot_le, ht⟩, rfl⟩).trans hs

private theorem pathSup_abs_sub_le
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω)
    (hc : Continuous (B · ω)) (u v : ℝ) :
    |BrownianSurvivalBoundary.pathSup B T u ω -
      BrownianSurvivalBoundary.pathSup B T v ω| ≤ |u - v| := by
  let q : ℝ → ℝ := fun w => BrownianSurvivalBoundary.pathSup B T w ω
  have hb (w : ℝ) :
      BddAbove ((fun t : ℝ≥0 => |w + B t ω|) '' Icc 0 T) :=
    (isCompact_Icc.image ((continuous_const.add hc).abs)).bddAbove
  have hne (w : ℝ) :
      ((fun t : ℝ≥0 => |w + B t ω|) '' Icc 0 T).Nonempty :=
    ⟨|w + B 0 ω|, ⟨0, ⟨le_rfl, bot_le⟩, rfl⟩⟩
  have hdom (a b : ℝ) : q a ≤ q b + |a - b| := by
    apply csSup_le (hne a)
    rintro _ ⟨t, ht, rfl⟩
    have htbound : |b + B t ω| ≤ q b := le_csSup (hb b) ⟨t, ht, rfl⟩
    calc
      |a + B t ω| = |(b + B t ω) + (a - b)| := by congr 1; ring
      _ ≤ |b + B t ω| + |a - b| := by
        apply abs_le.mpr
        constructor
        · linarith [neg_le_abs (b + B t ω), neg_le_abs (a - b)]
        · linarith [le_abs_self (b + B t ω), le_abs_self (a - b)]
      _ ≤ q b + |a - b| := by linarith
  have huv := hdom u v
  have hvu := hdom v u
  rw [abs_sub_comm v u] at hvu
  change |q u - q v| ≤ |u - v|
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem survival_indicator_tendsto
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω)
    (hc : Continuous (B · ω)) (uSeq : ℕ → ℝ) (u : ℝ)
    (huSeq : Tendsto uSeq atTop (𝓝 u))
    (hboundary : BrownianSurvivalBoundary.pathSup B T u ω ≠ 1) :
    Tendsto (fun j =>
      (BrownianSurvivalBoundary.closedSurvival B T (uSeq j)).indicator
        (fun _ : Ω => (1 : ℝ)) ω) atTop
      (𝓝 ((BrownianSurvivalBoundary.closedSurvival B T u).indicator
        (fun _ : Ω => (1 : ℝ)) ω)) := by
  let q : ℝ → ℝ := fun w => BrownianSurvivalBoundary.pathSup B T w ω
  have huabs : Tendsto (fun j => |uSeq j - u|) atTop (𝓝 (0 : ℝ)) := by
    have hd : Tendsto (fun j => uSeq j - u) atTop (𝓝 (u - u)) :=
      huSeq.sub tendsto_const_nhds
    simpa only [sub_self, abs_zero] using hd.abs
  have hq : Tendsto (fun j => q (uSeq j)) atTop (𝓝 (q u)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [Real.dist_eq]
    apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _)
      (Eventually.of_forall fun j => pathSup_abs_sub_le B T ω hc (uSeq j) u) huabs
  have heq : (fun j =>
      (BrownianSurvivalBoundary.closedSurvival B T (uSeq j)).indicator
        (fun _ : Ω => (1 : ℝ)) ω) =ᶠ[atTop]
      (fun _ : ℕ => (BrownianSurvivalBoundary.closedSurvival B T u).indicator
        (fun _ : Ω => (1 : ℝ)) ω) := by
    rcases lt_or_gt_of_ne hboundary with hlt | hgt
    · have hu : ω ∈ BrownianSurvivalBoundary.closedSurvival B T u :=
        (continuous_pathSup_characterization B T u ω hc).mpr hlt.le
      have hlt' : q u < 1 := hlt
      filter_upwards [(tendsto_order.1 hq).2 1 hlt'] with j hj
      have hju : ω ∈ BrownianSurvivalBoundary.closedSurvival B T (uSeq j) :=
        (continuous_pathSup_characterization B T (uSeq j) ω hc).mpr hj.le
      simp only [Set.indicator_of_mem hju, Set.indicator_of_mem hu]
    · have hu : ω ∉ BrownianSurvivalBoundary.closedSurvival B T u := by
        intro hs
        exact not_le_of_gt hgt
          ((continuous_pathSup_characterization B T u ω hc).mp hs)
      have hgt' : 1 < q u := hgt
      filter_upwards [(tendsto_order.1 hq).1 1 hgt'] with j hj
      have hju : ω ∉ BrownianSurvivalBoundary.closedSurvival B T (uSeq j) := by
        intro hs
        exact not_le_of_gt hj
          ((continuous_pathSup_characterization B T (uSeq j) ω hc).mp hs)
      simp only [Set.indicator_of_notMem hju, Set.indicator_of_notMem hu]
  exact (tendsto_congr' heq).mpr tendsto_const_nhds

private theorem integral_indicator_one_nullMeasurable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (s : Set α) (hs : NullMeasurableSet s μ) :
    (∫ a, s.indicator (fun _ : α => (1 : ℝ)) a ∂μ) = μ.real s := by
  rw [integral_indicator₀ hs, setIntegral_const]
  simp only [smul_eq_mul, mul_one]

-- The sequence need not stay in [-1,1]; only its limit is in that interval.
private theorem brownian_survival_tendsto
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) (hT : 0 < T)
    (uSeq : ℕ → ℝ) (u : ℝ) (huSeq : Tendsto uSeq atTop (𝓝 u))
    (hu : u ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun j => brownianSurvival B P T (uSeq j)) atTop
      (𝓝 (brownianSurvival B P T u)) := by
  have hne : ∀ᵐ ω ∂P, BrownianSurvivalBoundary.pathSup B T u ω ≠ 1 := by
    apply ae_iff.mpr
    simpa only [not_not] using
      BrownianSurvivalBoundary.measure_pathSup_eq_one_eq_zero B P hB T hT u hu
  have hpoint : ∀ᵐ ω ∂P, Tendsto (fun j =>
      (BrownianSurvivalBoundary.closedSurvival B T (uSeq j)).indicator
        (fun _ : Ω => (1 : ℝ)) ω) atTop
      (𝓝 ((BrownianSurvivalBoundary.closedSurvival B T u).indicator
        (fun _ : Ω => (1 : ℝ)) ω)) := by
    filter_upwards [hB.cont, hne] with ω hc hn
    exact survival_indicator_tendsto B T ω hc uSeq u huSeq hn
  have hmeas (j : ℕ) :
      AEStronglyMeasurable
        ((BrownianSurvivalBoundary.closedSurvival B T (uSeq j)).indicator
          (fun _ : Ω => (1 : ℝ))) P :=
    aestronglyMeasurable_const.indicator₀
      (BrownianSurvivalBoundary.closedSurvival_nullMeasurable B P hB T (uSeq j))
  have hbound (j : ℕ) : ∀ᵐ ω ∂P,
      ‖(BrownianSurvivalBoundary.closedSurvival B T (uSeq j)).indicator
        (fun _ : Ω => (1 : ℝ)) ω‖ ≤ 1 := by
    apply Eventually.of_forall
    intro ω
    by_cases hω : ω ∈ BrownianSurvivalBoundary.closedSurvival B T (uSeq j)
    · simp only [Set.indicator_of_mem hω, norm_one, le_refl]
    · simp only [Set.indicator_of_notMem hω, norm_zero, zero_le_one]
  have hlim := tendsto_integral_of_dominated_convergence
    (fun _ : Ω => (1 : ℝ)) hmeas (integrable_const _) hbound hpoint
  have hI (v : ℝ) :
      (∫ ω, (BrownianSurvivalBoundary.closedSurvival B T v).indicator
        (fun _ : Ω => (1 : ℝ)) ω ∂P) = brownianSurvival B P T v :=
    integral_indicator_one_nullMeasurable P _
      (BrownianSurvivalBoundary.closedSurvival_nullMeasurable B P hB T v)
  simpa only [hI] using hlim

theorem continuousOn_brownianSurvival
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) (hT : 0 < T) :
    ContinuousOn (brownianSurvival B P T) (Icc (-1 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply SeqContinuous.continuous
  intro uSeq u huSeq
  have hreal : Tendsto (fun j => (uSeq j : ℝ)) atTop (𝓝 (u : ℝ)) :=
    (continuous_subtype_val.tendsto u).comp huSeq
  exact brownian_survival_tendsto B P hB T hT
    (fun j => (uSeq j : ℝ)) (u : ℝ) hreal u.property

private theorem rowLength_horizon (T : ℝ≥0) (h : ℝ) :
    (T : ℝ) * h ^ 2 ≤ (rowLength T h : ℝ) := by
  exact Nat.le_ceil _

private theorem floorHorizon_le_rowLength (T : ℝ≥0) (h : ℝ) :
    PolygonalKilledFunctionalLimit.floorHorizon T h ≤ rowLength T h := by
  exact PolygonalKilledFunctionalLimit.floorHorizon_le T h (rowLength T h)
    (rowLength_horizon T h)

private theorem discrete_survival_probability_eq_killedMass
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (n l : ℕ) (hl : l ≤ n)
    (h : ℝ) (hh : 0 < h) (z : ℝ) (hz : |z| ≤ h) :
    (Measure.pi (fun _ : Fin n => ν)).real
      (PolygonalKilledFunctionalLimit.discreteClosedSurvival
        n l h (z / h) (1 : ℝ≥0)) =
      killedMass ν h l z := by
  have ht := BrownianKilledCosineIdentity.discrete_killed_test_integral
    ν n l hl h hh (1 : ℝ≥0) z (by simpa only [NNReal.coe_one, one_mul] using hz)
    (fun _ : ℝ => (1 : ℝ)) measurable_const ⟨1, fun _ => by norm_num⟩
  have hm := PolygonalKilledFunctionalLimit.measurableSet_discreteClosedSurvival
    n l h (z / h) (1 : ℝ≥0)
  calc
    _ = ∫ a : Shao.Path n,
        (PolygonalKilledFunctionalLimit.discreteClosedSurvival
          n l h (z / h) (1 : ℝ≥0)).indicator
          (fun _ : Shao.Path n => (1 : ℝ)) a
            ∂Measure.pi (fun _ : Fin n => ν) := (integral_indicator_one hm).symm
    _ = _ := by
      simpa only [NNReal.coe_one, one_mul, killedMass] using ht.2.2

private theorem scaledStart_mem (h z : ℝ) (hh : 0 < h) (hz : |z| ≤ h) :
    z / h ∈ Icc (-1 : ℝ) 1 := by
  have hb := abs_le.mp hz
  constructor
  · exact (le_div_iff₀ hh).mpr (by simpa only [neg_one_mul] using hb.1)
  · exact (div_le_iff₀ hh).mpr (by simpa only [one_mul] using hb.2)

-- Actual varying row law and physical starting point, on the original finite kernels.
-- @killedMass makes every varying probability instance explicit.
private theorem killedMass_tendsto_brownian
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) (hT : 0 < T)
    (hSeq : ℕ → ℝ) (νSeq : ℕ → Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (hpos : ∀ j, 0 < hSeq j)
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (hinfty : Tendsto hSeq atTop atTop)
    (zSeq : ℕ → ℝ) (hz : ∀ j, |zSeq j| ≤ hSeq j)
    (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1)
    (hstart : Tendsto (fun j => zSeq j / hSeq j) atTop (𝓝 u)) :
    Tendsto (fun j => @killedMass (νSeq j) (hprob j) (hSeq j)
      (PolygonalKilledFunctionalLimit.floorHorizon T (hSeq j)) (zSeq j))
      atTop (𝓝 (brownianSurvival B P T u)) := by
  have hs := PolygonalKilledFunctionalLimit.discrete_survival_tendsto_brownian
    B P hB T hT (fun j => rowLength T (hSeq j)) hSeq νSeq hprob hpos
    (fun j => rowLength_horizon T (hSeq j)) h3 hmean hsecond M hM hinfty
    (fun _ : ℕ => (1 : ℝ≥0)) tendsto_const_nhds
    (fun j => zSeq j / hSeq j) u hstart hu
  have hrow (j : ℕ) :
      (Measure.pi (fun _ : Fin (rowLength T (hSeq j)) => νSeq j)).real
        (PolygonalKilledFunctionalLimit.discreteClosedSurvival
          (rowLength T (hSeq j)) (PolygonalKilledFunctionalLimit.floorHorizon T (hSeq j))
          (hSeq j) (zSeq j / hSeq j) (1 : ℝ≥0)) =
      @killedMass (νSeq j) (hprob j) (hSeq j)
        (PolygonalKilledFunctionalLimit.floorHorizon T (hSeq j)) (zSeq j) := by
    letI : IsProbabilityMeasure (νSeq j) := hprob j
    exact discrete_survival_probability_eq_killedMass (νSeq j)
      (rowLength T (hSeq j)) (PolygonalKilledFunctionalLimit.floorHorizon T (hSeq j))
      (floorHorizon_le_rowLength T (hSeq j)) (hSeq j) (hpos j) (zSeq j) (hz j)
  simpa only [hrow, brownianSurvival] using hs

private theorem survivalError_bounds
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (T : ℝ≥0)
    (h : ℝ) (hh : 0 ≤ h) :
    0 ≤ survivalError B P ν T h ∧ survivalError B P ν T h ≤ 1 := by
  let E : ℝ → ℝ := fun z =>
    |killedMass ν h (PolygonalKilledFunctionalLimit.floorHorizon T h) z -
      brownianSurvival B P T (z / h)|
  have hE (z : ℝ) : 0 ≤ E z ∧ E z ≤ 1 := by
    have hk0 := killedMass_nonneg ν h (PolygonalKilledFunctionalLimit.floorHorizon T h) z
    have hk1 := killedMass_le_one ν h (PolygonalKilledFunctionalLimit.floorHorizon T h) z
    have hg0 : 0 ≤ brownianSurvival B P T (z / h) := measureReal_nonneg
    have hg1 : brownianSurvival B P T (z / h) ≤ 1 := measureReal_le_one
    exact ⟨abs_nonneg _, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have hz0 : (0 : ℝ) ∈ Icc (-h) h := ⟨neg_nonpos.mpr hh, hh⟩
  have hne : (E '' Icc (-h) h).Nonempty := ⟨E 0, ⟨0, hz0, rfl⟩⟩
  have hb : BddAbove (E '' Icc (-h) h) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨z, _, rfl⟩
    exact (hE z).2
  change 0 ≤ sSup (E '' Icc (-h) h) ∧ sSup (E '' Icc (-h) h) ≤ 1
  constructor
  · exact (hE 0).1.trans (le_csSup hb ⟨0, hz0, rfl⟩)
  · apply csSup_le hne
    rintro _ ⟨z, _, rfl⟩
    exact (hE z).2

private theorem survivalError_le_of_forall
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (T : ℝ≥0)
    (h : ℝ) (hh : 0 ≤ h) (ε : ℝ)
    (hbound : ∀ z : ℝ, |z| ≤ h →
      |killedMass ν h (PolygonalKilledFunctionalLimit.floorHorizon T h) z -
        brownianSurvival B P T (z / h)| ≤ ε) :
    survivalError B P ν T h ≤ ε := by
  unfold survivalError
  apply csSup_le
  · exact ⟨_, ⟨0, ⟨neg_nonpos.mpr hh, hh⟩, rfl⟩⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hbound z (abs_le.mpr hz)

-- Stronger than the fixed-law source: H is shared by every law in the moment class.
-- M is arbitrary; if the class is empty the universal conclusion is vacuous.
-- B/P/T are fixed outside H. No uniformity over different B/P is asserted here.
theorem uniform_brownian_survival_momentClass
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) (hT : 0 < T) (M : ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ H : ℝ, 0 < H ∧ ∀ h : ℝ, H ≤ h →
      ∀ (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν),
      Integrable (fun x : ℝ => |x| ^ 3) ν →
      (∫ x : ℝ, x ∂ν) = 0 →
      (∫ x : ℝ, x ^ 2 ∂ν) = 1 →
      (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ M →
      ∀ z : ℝ, |z| ≤ h →
        |@killedMass ν hprob h (PolygonalKilledFunctionalLimit.floorHorizon T h) z -
          brownianSurvival B P T (z / h)| < ε := by
  classical
  by_contra hnot
  have hbad (H : ℝ) (hH : 0 < H) :
      ∃ h : ℝ, H ≤ h ∧ ∃ (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν),
        Integrable (fun x : ℝ => |x| ^ 3) ν ∧
        (∫ x : ℝ, x ∂ν) = 0 ∧
        (∫ x : ℝ, x ^ 2 ∂ν) = 1 ∧
        (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ M ∧
        ∃ z : ℝ, |z| ≤ h ∧
          ε ≤ |@killedMass ν hprob h (PolygonalKilledFunctionalLimit.floorHorizon T h) z -
            brownianSurvival B P T (z / h)| := by
    by_contra hn
    apply hnot
    refine ⟨H, hH, ?_⟩
    intro h hh ν hprob h3 hmean hsecond hM z hz
    by_contra he
    exact hn ⟨h, hh, ν, hprob, h3, hmean, hsecond, hM, z, hz, le_of_not_gt he⟩
  choose hSeq hhSeq νSeq hprob h3 hmean hsecond hM zSeq hzSeq herr using
    (fun j : ℕ => hbad ((j : ℝ) + 1) (by positivity))
  have hpos (j : ℕ) : 0 < hSeq j := by
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith [hhSeq j]
  have hinfty : Tendsto hSeq atTop atTop := by
    apply tendsto_atTop_mono
      (fun j : ℕ => show (j : ℝ) ≤ hSeq j by linarith [hhSeq j])
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop)
  let uSeq : ℕ → ℝ := fun j => zSeq j / hSeq j
  have huSeq (j : ℕ) : uSeq j ∈ Icc (-1 : ℝ) 1 :=
    scaledStart_mem (hSeq j) (zSeq j) (hpos j) (hzSeq j)
  obtain ⟨u, hu, φ, hφ, hstart⟩ :=
    (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).tendsto_subseq huSeq
  have hK := killedMass_tendsto_brownian B P hB T hT
    (fun j => hSeq (φ j)) (fun j => νSeq (φ j)) (fun j => hprob (φ j))
    (fun j => hpos (φ j)) (fun j => h3 (φ j))
    (fun j => hmean (φ j)) (fun j => hsecond (φ j)) M (fun j => hM (φ j))
    (hinfty.comp hφ.tendsto_atTop) (fun j => zSeq (φ j)) (fun j => hzSeq (φ j))
    u hu (by simpa only [uSeq, Function.comp_def] using hstart)
  have hG := brownian_survival_tendsto B P hB T hT
    (fun j => uSeq (φ j)) u (by simpa only [Function.comp_def] using hstart) hu
  have he : Tendsto (fun j =>
      |@killedMass (νSeq (φ j)) (hprob (φ j)) (hSeq (φ j))
        (PolygonalKilledFunctionalLimit.floorHorizon T (hSeq (φ j))) (zSeq (φ j)) -
        brownianSurvival B P T (zSeq (φ j) / hSeq (φ j))|)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [uSeq, sub_self, abs_zero] using (hK.sub hG).abs
  have hev := (tendsto_order.1 he).2 ε hε
  obtain ⟨j, hj⟩ := hev.exists
  exact not_lt_of_ge (herr (φ j)) hj

-- Exact fixed-law source corollary: finite third moment supplies its own M.
theorem uniform_brownian_survival
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) (hT : 0 < T)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ H : ℝ, 0 < H ∧ ∀ h : ℝ, H ≤ h →
      ∀ z : ℝ, |z| ≤ h →
        |killedMass ν h (PolygonalKilledFunctionalLimit.floorHorizon T h) z -
          brownianSurvival B P T (z / h)| < ε := by
  obtain ⟨H, hH, hbound⟩ := uniform_brownian_survival_momentClass
    B P hB T hT (∫ x : ℝ, |x| ^ 3 ∂ν) ε hε
  refine ⟨H, hH, ?_⟩
  intro h hh z hz
  exact hbound h hh ν (inferInstance : IsProbabilityMeasure ν)
    h3 hmean hsecond le_rfl z hz

-- Exact source B0: the displayed real supremum tends to zero as real h -> +infinity.
theorem tendsto_survivalError
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) (hT : 0 < T)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    Tendsto (survivalError B P ν T) atTop (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨H, hH, hbound⟩ := uniform_brownian_survival
    B P hB T hT ν h3 hmean hsecond (ε / 2) (half_pos hε)
  refine ⟨H, ?_⟩
  intro h hh
  have hh0 : 0 ≤ h := hH.le.trans hh
  have hs0 := (survivalError_bounds B P ν T h hh0).1
  have hs1 : survivalError B P ν T h ≤ ε / 2 :=
    survivalError_le_of_forall B P ν T h hh0 (ε / 2)
      (fun z hz => (hbound h hh z hz).le)
  have hsmall : survivalError B P ν T h < ε :=
    hs1.trans_lt (half_lt_self hε)
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hs0] using hsmall

end Shao.OQ4.BrownianUniformSurvival
end
