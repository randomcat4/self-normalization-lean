import Shao.OQ4.EnergyPathLaw
import Shao.OQ4.EnergyLinearTiltLaw

/-! Actual finite linear path change of measure, including empty paths. -/

namespace Shao.OQ4

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

noncomputable def energyLinearPathIntegrand {n : ℕ} (h t : ℝ) (a : Shao.Path n) : ℝ := by
  classical
  exact if a ∈ Shao.closedStrip h then Real.exp (-t * Shao.prefixSum a n) else 0

theorem energyLinearPathIntegrand_nonneg {n : ℕ} (h t : ℝ) (a : Shao.Path n) :
    0 ≤ energyLinearPathIntegrand h t a := by
  unfold energyLinearPathIntegrand
  split_ifs <;> positivity

theorem energyLinearPathIntegrand_measurable {n : ℕ} (h t : ℝ) (hh : 0 ≤ h) :
    Measurable (energyLinearPathIntegrand (n := n) h t) := by
  have hA : MeasurableSet (Shao.closedStrip (n := n) h) := by
    rw [← shiftedClosedSurvival_eq_closedStrip n h hh]
    exact measurableSet_shiftedClosedSurvival n h 0
  exact Measurable.ite hA ((Shao.measurable_prefixSum n).const_mul (-t)).exp measurable_const

theorem energyLinearPathIntegrand_closed_bounds {n : ℕ} (h t : ℝ) (a : Shao.Path n)
    (ha : a ∈ Shao.closedStrip h) :
    Real.exp (-|t| * h) ≤ energyLinearPathIntegrand h t a ∧
      energyLinearPathIntegrand h t a ≤ Real.exp (|t| * h) := by
  have hb : |t * Shao.prefixSum a n| ≤ |t| * h := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (ha n le_rfl) (abs_nonneg t)
  have hp := abs_le.mp hb
  rw [energyLinearPathIntegrand, ite_eq_left ha]
  constructor <;> apply Real.exp_le_exp.mpr <;> linarith [hp.1, hp.2]

theorem energyLinearPathIntegrand_le {n : ℕ} (h t : ℝ) (a : Shao.Path n) :
    energyLinearPathIntegrand h t a ≤ Real.exp (|t| * h) := by
  by_cases ha : a ∈ Shao.closedStrip h
  · exact (energyLinearPathIntegrand_closed_bounds h t a ha).2
  · simp only [energyLinearPathIntegrand, ite_eq_right ha]
    exact Real.exp_nonneg _

theorem energyLinearPathIntegrand_integrable (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (n : ℕ) (h t : ℝ) (hh : 0 ≤ h) :
    Integrable (energyLinearPathIntegrand (n := n) h t) (Measure.pi (fun _ : Fin n => ρ)) := by
  apply Integrable.of_bound (energyLinearPathIntegrand_measurable h t hh).aestronglyMeasurable
    (Real.exp (|t| * h))
  exact Filter.Eventually.of_forall fun a => by
    rw [Real.norm_eq_abs, abs_of_nonneg (energyLinearPathIntegrand_nonneg h t a)]
    exact energyLinearPathIntegrand_le h t a

theorem energyLinearPathLaw_withDensity (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (T h s t : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s t) =
      (Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s)).withDensity
        (fun a => ENNReal.ofReal (Real.exp (t * Shao.prefixSum a n) /
          (energyLinearNormalizer ν h s t) ^ n)) := by
  have : IsProbabilityMeasure (energyTiltedLaw ν h s) :=
    energyTiltedLaw_isProbabilityMeasure ν T h s hT hh hs hSq hsecond
  have : IsProbabilityMeasure (energyLinearTiltLaw ν h s t) :=
    energyLinearTiltLaw_isProbabilityMeasure ν T h s hT hh hs hSq hsecond t
  have hL := energyLinearNormalizer_pos ν T h s hT hh hs hSq hsecond t
  have : IsProbabilityMeasure ((energyTiltedLaw ν h s).withDensity
      (fun x => ENNReal.ofReal (Real.exp (t * x) / energyLinearNormalizer ν h s t))) :=
    energyLinearTiltLaw_isProbabilityMeasure ν T h s hT hh hs hSq hsecond t
  change Measure.pi (fun _ : Fin n => (energyTiltedLaw ν h s).withDensity
    (fun x => ENNReal.ofReal (Real.exp (t * x) / energyLinearNormalizer ν h s t))) = _
  rw [finitePi_withDensity (energyTiltedLaw ν h s) _ (energyLinear_density_measurable ν h s t) n]
  congr 1
  funext a
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ =>
    div_nonneg (Real.exp_nonneg (t * a i)) hL.le)]
  congr 1
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [← Real.exp_sum, Shao.prefixSum_length, Finset.mul_sum]

private theorem energyLinearPath_density_mul {n : ℕ} (h t L : ℝ) (a : Shao.Path n) :
    (Real.exp (t * Shao.prefixSum a n) / L ^ n) * energyLinearPathIntegrand h t a =
      (1 / L ^ n) * (Shao.closedStrip h).indicator (fun _ => (1 : ℝ)) a := by
  classical
  by_cases ha : a ∈ Shao.closedStrip h
  · rw [energyLinearPathIntegrand, ite_eq_left ha, Set.indicator_of_mem ha, mul_one]
    calc
      _ = (Real.exp (t * Shao.prefixSum a n) * Real.exp (-t * Shao.prefixSum a n)) / L ^ n := by ring
      _ = _ := by
        rw [← Real.exp_add]
        have he : t * Shao.prefixSum a n + -t * Shao.prefixSum a n = 0 := by ring
        rw [he, Real.exp_zero]
  · simp [energyLinearPathIntegrand, ha]

theorem energyLinearPathLaw_integral (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (T h s t : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    Integrable (energyLinearPathIntegrand (n := n) h t)
        (Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s t)) ∧
      (Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s)).real (Shao.closedStrip h) =
        (energyLinearNormalizer ν h s t) ^ n *
          ∫ a, energyLinearPathIntegrand h t a
            ∂Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s t) := by
  have : IsProbabilityMeasure (energyTiltedLaw ν h s) :=
    energyTiltedLaw_isProbabilityMeasure ν T h s hT hh hs hSq hsecond
  have : IsProbabilityMeasure (energyLinearTiltLaw ν h s t) :=
    energyLinearTiltLaw_isProbabilityMeasure ν T h s hT hh hs hSq hsecond t
  have hL := energyLinearNormalizer_pos ν T h s hT hh hs hSq hsecond t
  have hn : 0 < (energyLinearNormalizer ν h s t) ^ n := pow_pos hL n
  have hA : MeasurableSet (Shao.closedStrip (n := n) h) := by
    rw [← shiftedClosedSurvival_eq_closedStrip n h (by linarith : 0 ≤ h)]
    exact measurableSet_shiftedClosedSurvival n h 0
  have hD : Measurable (fun a : Shao.Path n => ENNReal.ofReal
      (Real.exp (t * Shao.prefixSum a n) / (energyLinearNormalizer ν h s t) ^ n)) := by
    exact (((Shao.measurable_prefixSum n).const_mul t).exp.div_const _).ennreal_ofReal
  have htop : ∀ᵐ a ∂Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s),
      ENNReal.ofReal (Real.exp (t * Shao.prefixSum a n) /
        (energyLinearNormalizer ν h s t) ^ n) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hp (a : Shao.Path n) :
      0 ≤ Real.exp (t * Shao.prefixSum a n) / (energyLinearNormalizer ν h s t) ^ n :=
    div_nonneg (Real.exp_nonneg _) hn.le
  have hweighted : Integrable (fun a : Shao.Path n =>
      (Real.exp (t * Shao.prefixSum a n) / (energyLinearNormalizer ν h s t) ^ n) *
        energyLinearPathIntegrand h t a)
      (Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s)) := by
    simp_rw [energyLinearPath_density_mul]
    exact ((integrable_const (1 : ℝ)).indicator hA).const_mul _
  refine ⟨energyLinearPathIntegrand_integrable _ n h t (by linarith), ?_⟩
  have hI : (∫ a, energyLinearPathIntegrand h t a
      ∂Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s t)) =
      (1 / (energyLinearNormalizer ν h s t) ^ n) *
        (Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s)).real (Shao.closedStrip h) := by
    rw [energyLinearPathLaw_withDensity ν n T h s t hT hh hs hSq hsecond,
      integral_withDensity_eq_integral_toReal_smul hD htop]
    simp_rw [ENNReal.toReal_ofReal (hp _), smul_eq_mul, energyLinearPath_density_mul]
    rw [integral_const_mul, integral_indicator hA]
    simp
  rw [hI]
  field_simp

theorem energyLinearPathLaw_sandwich (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (T h s t : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    (energyLinearNormalizer ν h s t) ^ n * Real.exp (-|t| * h) *
        (Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s t)).real (Shao.closedStrip h) ≤
      (Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s)).real (Shao.closedStrip h) ∧
    (Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s)).real (Shao.closedStrip h) ≤
      (energyLinearNormalizer ν h s t) ^ n * Real.exp (|t| * h) *
        (Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s t)).real (Shao.closedStrip h) := by
  classical
  have : IsProbabilityMeasure (energyLinearTiltLaw ν h s t) :=
    energyLinearTiltLaw_isProbabilityMeasure ν T h s hT hh hs hSq hsecond t
  obtain ⟨hFi, hidentity⟩ := energyLinearPathLaw_integral ν n T h s t hT hh hs hSq hsecond
  have hn : 0 ≤ (energyLinearNormalizer ν h s t) ^ n :=
    (pow_pos (energyLinearNormalizer_pos ν T h s hT hh hs hSq hsecond t) n).le
  have hA : MeasurableSet (Shao.closedStrip (n := n) h) := by
    rw [← shiftedClosedSurvival_eq_closedStrip n h (by linarith : 0 ≤ h)]
    exact measurableSet_shiftedClosedSurvival n h 0
  have hI : Integrable ((Shao.closedStrip (n := n) h).indicator (fun _ => (1 : ℝ)))
      (Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s t)) :=
    (integrable_const (1 : ℝ)).indicator hA
  have hmass : (∫ a, (Shao.closedStrip h).indicator (fun _ => (1 : ℝ)) a
      ∂Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s t)) =
      (Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s t)).real (Shao.closedStrip h) := by
    rw [integral_indicator hA]
    simp
  have hlo : ∀ a : Shao.Path n, Real.exp (-|t| * h) *
      (Shao.closedStrip h).indicator (fun _ => (1 : ℝ)) a ≤ energyLinearPathIntegrand h t a := by
    intro a
    by_cases ha : a ∈ Shao.closedStrip h
    · simpa only [Set.indicator_of_mem ha, mul_one] using
        (energyLinearPathIntegrand_closed_bounds h t a ha).1
    · simp [energyLinearPathIntegrand, ha]
  have hhi : ∀ a : Shao.Path n, energyLinearPathIntegrand h t a ≤ Real.exp (|t| * h) *
      (Shao.closedStrip h).indicator (fun _ => (1 : ℝ)) a := by
    intro a
    by_cases ha : a ∈ Shao.closedStrip h
    · simpa only [Set.indicator_of_mem ha, mul_one] using
        (energyLinearPathIntegrand_closed_bounds h t a ha).2
    · simp [energyLinearPathIntegrand, ha]
  have hlower := integral_mono_ae (hI.const_mul (Real.exp (-|t| * h))) hFi
    (Filter.Eventually.of_forall hlo)
  have hupper := integral_mono_ae hFi (hI.const_mul (Real.exp (|t| * h)))
    (Filter.Eventually.of_forall hhi)
  rw [integral_const_mul, hmass] at hlower hupper
  rw [hidentity]
  exact ⟨by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hlower hn,
    by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hupper hn⟩

private theorem energyLinearPath_iid_real_apply {Ω : Type*} [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X p)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) p ρ)
    (A : Set (Shao.Path n)) (hA : MeasurableSet A) :
    (Measure.pi (fun _ : Fin n => ρ)).real A =
      p.real {ω | Shao.Probability.samplePath X ω ∈ A} := by
  have hY := Shao.Probability.measurable_samplePath hX
  have hmap := Shao.Probability.iid_samplePath_map_eq_pi hX hIndep hLaw
  rw [← hmap, measureReal_def, Measure.map_apply hY hA]
  rfl

theorem energyLinearPathLaw_integral_iid {Ω : Type*} [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (T h s t : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X p)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) p (energyLinearTiltLaw ν h s t)) :
    Integrable (fun ω => energyLinearPathIntegrand h t (Shao.Probability.samplePath X ω)) p ∧
      (∫ ω, energyLinearPathIntegrand h t (Shao.Probability.samplePath X ω) ∂p) =
        (∫ a, energyLinearPathIntegrand h t a
          ∂Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s t)) ∧
      (Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s)).real (Shao.closedStrip h) =
        (energyLinearNormalizer ν h s t) ^ n *
          ∫ ω, energyLinearPathIntegrand h t (Shao.Probability.samplePath X ω) ∂p := by
  have : IsProbabilityMeasure (energyLinearTiltLaw ν h s t) :=
    energyLinearTiltLaw_isProbabilityMeasure ν T h s hT hh hs hSq hsecond t
  have hY := Shao.Probability.measurable_samplePath hX
  have hmap := Shao.Probability.iid_samplePath_map_eq_pi hX hIndep hLaw
  have hF := energyLinearPathIntegrand_measurable (n := n) h t (by linarith : 0 ≤ h)
  obtain ⟨hFi, hidentity⟩ := energyLinearPathLaw_integral ν n T h s t hT hh hs hSq hsecond
  have hmi : Integrable (energyLinearPathIntegrand (n := n) h t)
      (Measure.map (Shao.Probability.samplePath X) p) := by
    rwa [hmap]
  have hsample := (integrable_map_measure hF.aestronglyMeasurable hY.aemeasurable).1 hmi
  have hJ : (∫ ω, energyLinearPathIntegrand h t (Shao.Probability.samplePath X ω) ∂p) =
      (∫ a, energyLinearPathIntegrand h t a
        ∂Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s t)) := by
    calc
      _ = ∫ a, energyLinearPathIntegrand h t a
          ∂Measure.map (Shao.Probability.samplePath X) p :=
        (integral_map hY.aemeasurable hF.aestronglyMeasurable).symm
      _ = _ := by rw [hmap]
  exact ⟨hsample, hJ, by rw [hJ]; exact hidentity⟩

theorem energyLinearPathLaw_probability_iid {Ω : Type*} [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (T h s t : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X p)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) p (energyLinearTiltLaw ν h s t)) :
    (Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s t)).real (Shao.closedStrip h) =
      p.real {ω | Shao.Probability.samplePath X ω ∈ Shao.closedStrip h} := by
  have : IsProbabilityMeasure (energyLinearTiltLaw ν h s t) :=
    energyLinearTiltLaw_isProbabilityMeasure ν T h s hT hh hs hSq hsecond t
  have hA : MeasurableSet (Shao.closedStrip (n := n) h) := by
    rw [← shiftedClosedSurvival_eq_closedStrip n h (by linarith : 0 ≤ h)]
    exact measurableSet_shiftedClosedSurvival n h 0
  exact energyLinearPath_iid_real_apply p _ X hX hIndep hLaw _ hA

theorem energyLinearPathLaw_base_probability_iid {Ω : Type*} [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X p)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) p (energyTiltedLaw ν h s)) :
    (Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s)).real (Shao.closedStrip h) =
      p.real {ω | Shao.Probability.samplePath X ω ∈ Shao.closedStrip h} := by
  have : IsProbabilityMeasure (energyTiltedLaw ν h s) :=
    energyTiltedLaw_isProbabilityMeasure ν T h s hT hh hs hSq hsecond
  have hA : MeasurableSet (Shao.closedStrip (n := n) h) := by
    rw [← shiftedClosedSurvival_eq_closedStrip n h (by linarith : 0 ≤ h)]
    exact measurableSet_shiftedClosedSurvival n h 0
  exact energyLinearPath_iid_real_apply p _ X hX hIndep hLaw _ hA

theorem energyLinearPathLaw_iid {Ω₀ Ω : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω]
    (p₀ : Measure Ω₀) [IsProbabilityMeasure p₀] (p : Measure Ω) [IsProbabilityMeasure p]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (T h s t : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (X₀ : Fin n → Ω₀ → ℝ) (hX₀ : ∀ i, Measurable (X₀ i)) (hIndep₀ : iIndepFun X₀ p₀)
    (hLaw₀ : ∀ i, IdentDistrib (X₀ i) (id : ℝ → ℝ) p₀ (energyTiltedLaw ν h s))
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X p)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) p (energyLinearTiltLaw ν h s t)) :
    Integrable (fun ω => energyLinearPathIntegrand h t (Shao.Probability.samplePath X ω)) p ∧
      p₀.real {ω | Shao.Probability.samplePath X₀ ω ∈ Shao.closedStrip h} =
        (energyLinearNormalizer ν h s t) ^ n *
          ∫ ω, energyLinearPathIntegrand h t (Shao.Probability.samplePath X ω) ∂p ∧
      ((energyLinearNormalizer ν h s t) ^ n * Real.exp (-|t| * h) *
          p.real {ω | Shao.Probability.samplePath X ω ∈ Shao.closedStrip h} ≤
        p₀.real {ω | Shao.Probability.samplePath X₀ ω ∈ Shao.closedStrip h} ∧
       p₀.real {ω | Shao.Probability.samplePath X₀ ω ∈ Shao.closedStrip h} ≤
        (energyLinearNormalizer ν h s t) ^ n * Real.exp (|t| * h) *
          p.real {ω | Shao.Probability.samplePath X ω ∈ Shao.closedStrip h}) := by
  obtain ⟨hFi, _hJ, hidentity⟩ :=
    energyLinearPathLaw_integral_iid p ν n T h s t hT hh hs hSq hsecond X hX hIndep hLaw
  have hbase := energyLinearPathLaw_base_probability_iid p₀ ν n T h s hT hh hs hSq hsecond
    X₀ hX₀ hIndep₀ hLaw₀
  have htilt := energyLinearPathLaw_probability_iid p ν n T h s t hT hh hs hSq hsecond
    X hX hIndep hLaw
  have hbounds := energyLinearPathLaw_sandwich ν n T h s t hT hh hs hSq hsecond
  rw [hbase] at hidentity
  rw [hbase, htilt] at hbounds
  exact ⟨hFi, hidentity, hbounds⟩

end Shao.OQ4
