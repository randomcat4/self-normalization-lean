/- Frozen by successor OQ4 lead before implementation, 2026-10-24.
   One definition, six theorems; no private heads or instances.
   Body-local have/let permitted. All public/private top-level amendments
   require the lead to freeze their complete types/values before writing.
   No proof credit is claimed by this interface-only artifact. -/
import Shao.OQ4.SparseOriginalIIDTransport
import Shao.OQ4.RademacherS5Assembly

set_option autoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
universe uX uB

namespace Shao.OQ4.RademacherOriginalIIDTransport

variable {ΩX : Type uX} [MeasurableSpace ΩX]
variable {ΩB : Type uB} [MeasurableSpace ΩB]

def sourceRatio
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (μ : Measure ΩX) (X : ℕ → ΩX → ℝ)
    (c : ℝ) (n : ℕ) : ℝ :=
  μ.real (OriginalIIDWindow.sourceEvent n X
    (c * Real.rpow (n : ℝ) (-((1 : ℝ) / 6)))) /
    Shao.Probability.BrownianSup.probability B P hB
      (c * Real.rpow (n : ℝ) (-((1 : ℝ) / 6)))

theorem sourcePath_identDistrib
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law) (n : ℕ) :
    IdentDistrib (OriginalIIDWindow.sourcePath n X)
      (id : Shao.Path n → Shao.Path n) μ (RademacherS5Assembly.pathLaw n) := by
  classical
  have hX (i : Fin n) : AEMeasurable (X (i.val + 1)) μ :=
    (hLaw i.val).aemeasurable_fst
  let Z : ΩX → Shao.Path n := fun ω i =>
    (hX i).mk (X (i.val + 1)) ω
  have hZ : Measurable Z :=
    Measurable.of_eval fun i => (hX i).measurable_mk
  have hcoords : ∀ᵐ ω ∂μ, ∀ i : Fin n,
      X (i.val + 1) ω = Z ω i :=
    ae_all_iff.mpr fun i => (hX i).ae_eq_mk
  have hFZ : OriginalIIDWindow.sourcePath n X =ᵐ[μ] Z := by
    filter_upwards [hcoords] with ω hω
    exact funext hω
  have hF : AEMeasurable (OriginalIIDWindow.sourcePath n X) μ :=
    ⟨Z, hZ, hFZ⟩
  have hfin : iIndepFun (fun i : Fin n => X (i.val + 1)) μ :=
    hIndep.precomp (show Function.Injective (fun i : Fin n => i.val) from
      fun i j hij => Fin.ext hij)
  have hmap : μ.map (OriginalIIDWindow.sourcePath n X) =
      RademacherS5Assembly.pathLaw n := by
    change μ.map (fun ω (i : Fin n) => X (i.val + 1) ω) =
      Measure.pi (fun _ : Fin n => RademacherCosine.law)
    rw [hfin.map_fun_eq_pi_map hX]
    congr 1
    funext i
    simpa only [Measure.map_id] using (hLaw i.val).map_eq
  refine ⟨hF, measurable_id.aemeasurable, ?_⟩
  simpa only [Measure.map_id] using hmap

theorem source_probability_eq_product
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law) (n : ℕ) (s : ℝ) :
    μ.real (OriginalIIDWindow.sourceEvent n X s) =
      (RademacherS5Assembly.pathLaw n).real
        (RademacherS5Assembly.selfNormalizedEvent n s) := by
  have hpath := sourcePath_identDistrib μ X hIndep hLaw n
  have hself : MeasurableSet
      (RademacherS5Assembly.selfNormalizedEvent n s) := by
    simp only [RademacherS5Assembly.selfNormalizedEvent, Set.setOf_forall]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_le (Shao.continuous_prefixSum k).abs.measurable
        (by simpa only [RademacherS5Assembly.V] using
          (Shao.measurable_energyWall s))
  have hpull : OriginalIIDWindow.sourceEvent n X s =
      OriginalIIDWindow.sourcePath n X ⁻¹'
        RademacherS5Assembly.selfNormalizedEvent n s := by
    simpa only [SparseCriticalDenominator.selfEvent,
      RademacherS5Assembly.selfNormalizedEvent, RademacherS5Assembly.V] using
      (SparseOriginalIIDTransport.source_event_pullbacks n X s).1
  rw [hpull]
  exact congrArg ENNReal.toReal (hpath.measure_mem_eq hself)

theorem source_ratio_eventually_eq
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law) (c : ℝ) (hc : 0 < c) :
    sourceRatio B P hB μ X c =ᶠ[atTop] RademacherS5Assembly.Q B P hB c := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [sourceRatio, source_probability_eq_product μ X hIndep hLaw]
  change RademacherS5Assembly.Qsource B P hB c n =
    RademacherS5Assembly.Q B P hB c n
  exact (RademacherS5Assembly.actual_source_event B P hB hc hn).2.2.2.2

theorem original_critical_phase
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.log (sourceRatio B P hB μ X c n) -
      RademacherCriticalPhase.exponent c n) atTop (𝓝 (0 : ℝ)) ∧
    Tendsto (fun n : ℕ => sourceRatio B P hB μ X c n /
      RademacherCriticalPhase.factor c n) atTop (𝓝 (1 : ℝ)) ∧
    Tendsto (fun n : ℕ => sourceRatio B P hB μ X c n -
      RademacherCriticalPhase.factor c n) atTop (𝓝 (0 : ℝ)) := by
  have heq := source_ratio_eventually_eq B P hB μ X hIndep hLaw c hc
  rcases (RademacherS5Assembly.S5_MAIN B P hB hc).1 with
    ⟨hlog, _, hratio, _, hdiff, _⟩
  have hlogeq : (fun n : ℕ =>
      Real.log (RademacherS5Assembly.Q B P hB c n) -
        RademacherS5Assembly.E c n) =ᶠ[atTop]
      (fun n : ℕ => Real.log (sourceRatio B P hB μ X c n) -
        RademacherCriticalPhase.exponent c n) := by
    filter_upwards [heq] with n hn
    simpa only [hn, RademacherS5Assembly.E]
  have hratioeq : (fun n : ℕ => RademacherS5Assembly.Q B P hB c n /
      RademacherS5Assembly.F c n) =ᶠ[atTop]
      (fun n : ℕ => sourceRatio B P hB μ X c n /
        RademacherCriticalPhase.factor c n) := by
    filter_upwards [heq] with n hn
    simpa only [hn, RademacherS5Assembly.F]
  have hdiffEq : (fun n : ℕ => RademacherS5Assembly.Q B P hB c n -
      RademacherS5Assembly.F c n) =ᶠ[atTop]
      (fun n : ℕ => sourceRatio B P hB μ X c n -
        RademacherCriticalPhase.factor c n) := by
    filter_upwards [heq] with n hn
    simpa only [hn, RademacherS5Assembly.F]
  exact ⟨hlog.congr' hlogeq, hratio.congr' hratioeq, hdiff.congr' hdiffEq⟩

theorem original_critical_cluster
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law) (c : ℝ) (hc : 0 < c) :
    RademacherCriticalPhase.Cluster (sourceRatio B P hB μ X c) =
      Set.Icc (1 : ℝ) (Real.exp (Real.pi ^ 2 / (4 * c ^ 3))) ∧
    (¬ ∃ L : ℝ, Tendsto (sourceRatio B P hB μ X c) atTop (𝓝 L)) := by
  have heq := source_ratio_eventually_eq B P hB μ X hIndep hLaw c hc
  have hcluster : RademacherCriticalPhase.Cluster (sourceRatio B P hB μ X c) =
      RademacherS5Assembly.Cluster (RademacherS5Assembly.Q B P hB c) := by
    apply Set.ext
    intro L
    constructor
    · rintro ⟨σ, hσ, hL⟩
      refine ⟨σ, hσ, hL.congr' ?_⟩
      exact heq.comp_tendsto hσ.tendsto_atTop
    · rintro ⟨σ, hσ, hL⟩
      refine ⟨σ, hσ, hL.congr' ?_⟩
      exact heq.symm.comp_tendsto hσ.tendsto_atTop
  constructor
  · calc
      RademacherCriticalPhase.Cluster (sourceRatio B P hB μ X c) =
          RademacherS5Assembly.Cluster (RademacherS5Assembly.Q B P hB c) := hcluster
      _ = Set.Icc (1 : ℝ) (Real.exp (Real.pi ^ 2 / (4 * c ^ 3))) := by
        simpa only [RademacherS5Assembly.coeff, RademacherCriticalPhase.q] using
          (RademacherS5Assembly.S5_CLUSTER B P hB hc).2.1
  · rintro ⟨L, hL⟩
    exact (RademacherS5Assembly.S5_NOT_CONVERGENT B P hB hc).2.2.1
      ⟨L, hL.congr' heq⟩

theorem original_cube_limits
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law) :
    Tendsto (fun j : ℕ => sourceRatio B P hB μ X 1 ((j + 1) ^ 3))
      atTop (𝓝 (Real.exp (Real.pi ^ 2 / 4))) ∧
    Tendsto (fun j : ℕ => sourceRatio B P hB μ X 1 ((j + 2) ^ 3 - 1))
      atTop (𝓝 (1 : ℝ)) := by
  have heq := source_ratio_eventually_eq B P hB μ X hIndep hLaw 1
    (by norm_num : (0 : ℝ) < 1)
  rcases RademacherS5Assembly.S5_CUBE B P hB with
    ⟨hcoeff, hcube, hbelow, _⟩
  rcases hcube.1 with ⟨hCPcube, _, _, _, hQcube, _, _⟩
  rcases hbelow.1 with ⟨hCPbelow, _, _, _, hQbelow, _, _⟩
  have heqCube : (fun j : ℕ => RademacherS5Assembly.Q B P hB 1
      (RademacherS5Assembly.cubeSeq j)) =ᶠ[atTop]
      (fun j : ℕ => sourceRatio B P hB μ X 1
        (RademacherS5Assembly.cubeSeq j)) :=
    heq.symm.comp_tendsto hCPcube.1.tendsto_atTop
  have heqBelow : (fun j : ℕ => RademacherS5Assembly.Q B P hB 1
      (RademacherS5Assembly.cubeMinusOneSeq j)) =ᶠ[atTop]
      (fun j : ℕ => sourceRatio B P hB μ X 1
        (RademacherS5Assembly.cubeMinusOneSeq j)) :=
    heq.symm.comp_tendsto hCPbelow.1.tendsto_atTop
  constructor
  · simpa only [hcoeff, mul_one, RademacherS5Assembly.cubeSeq,
      RademacherCriticalPhase.cubeIndex] using hQcube.congr' heqCube
  · simpa only [mul_zero, Real.exp_zero, RademacherS5Assembly.cubeMinusOneSeq,
      RademacherCriticalPhase.belowCubeIndex] using hQbelow.congr' heqBelow

end Shao.OQ4.RademacherOriginalIIDTransport
