import Shao.OQ4.EnergyRelativePathBounds

/-! Joint limits of the actual energy and centered path laws for one fixed original law. -/

namespace Shao.OQ4

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

universe u v w

noncomputable def energyJointBaseProbability (ν : Measure ℝ) (n : ℕ) (h s : ℝ) : ℝ :=
  (Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s)).real (Shao.closedStrip h)

noncomputable def energyJointCenteredProbability (ν : Measure ℝ) (n : ℕ) (h s θ : ℝ) : ℝ :=
  (Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s θ)).real (Shao.closedStrip h)

noncomputable def energyJointIntegral (ν : Measure ℝ) (n : ℕ) (h s : ℝ) : ℝ :=
  ∫ a, energyPathIntegrand h s a ∂Measure.pi (fun _ : Fin n => ν)

def energyJointErrorLimits (M T : ℝ) (h : ℕ → ℝ) (n : ℕ → ℕ) : Prop :=
  Tendsto (fun j => energyRelativePathError2 M T (n j) (h j)) atTop (𝓝 0) ∧
  Tendsto (fun j => energyRelativePathError M T (n j) (h j)) atTop (𝓝 0) ∧
  Tendsto (fun j => Real.exp (energyRelativePathError2 M T (n j) (h j)) - 1) atTop (𝓝 0) ∧
  Tendsto (fun j => Real.exp (energyRelativePathError M T (n j) (h j)) - 1) atTop (𝓝 0) ∧
  Tendsto (fun j => Real.exp (-energyRelativePathError2 M T (n j) (h j))) atTop (𝓝 1) ∧
  Tendsto (fun j => Real.exp (energyRelativePathError2 M T (n j) (h j))) atTop (𝓝 1) ∧
  Tendsto (fun j => Real.exp (-energyRelativePathError M T (n j) (h j))) atTop (𝓝 1) ∧
  Tendsto (fun j => Real.exp (energyRelativePathError M T (n j) (h j))) atTop (𝓝 1)

def energyJointNormalizationLimits (ν : Measure ℝ) (h s θ : ℕ → ℝ) (n : ℕ → ℕ) : Prop :=
  Tendsto (fun j => (n j : ℝ) * Real.log (energyLinearNormalizer ν (h j) (s j) (θ j)))
    atTop (𝓝 0) ∧
  Tendsto (fun j => |θ j| * h j) atTop (𝓝 0) ∧
  Tendsto (fun j => (energyLinearNormalizer ν (h j) (s j) (θ j)) ^ n j) atTop (𝓝 1) ∧
  Tendsto (fun j => (n j : ℝ) * (Real.log (energyNormalizer ν (h j) (s j)) - s j / h j ^ 2))
    atTop (𝓝 0) ∧
  Tendsto (fun j => Real.exp (-s j * (n j : ℝ) / h j ^ 2) *
    (energyNormalizer ν (h j) (s j)) ^ n j) atTop (𝓝 1)

def energyJointFiniteConclusion (ν : Measure ℝ) (M T h s θ : ℝ) (n : ℕ) : Prop :=
  energyE1Conclusion ν T h s ∧ energyE2Conclusion ν M T h s θ ∧
  0 < energyLinearNormalizer ν h s θ ∧ 0 < energyNormalizer ν h s ∧
  energyRelativePathConclusion ν M T h s θ n ∧
  0 ≤ Real.exp (energyRelativePathError2 M T n h) - 1 ∧
  0 ≤ Real.exp (energyRelativePathError M T n h) - 1 ∧
  |energyJointBaseProbability ν n h s - energyJointCenteredProbability ν n h s θ| ≤
    (Real.exp (energyRelativePathError2 M T n h) - 1) *
      energyJointCenteredProbability ν n h s θ ∧
  |energyJointIntegral ν n h s - energyJointCenteredProbability ν n h s θ| ≤
    (Real.exp (energyRelativePathError M T n h) - 1) *
      energyJointCenteredProbability ν n h s θ

def energyJointSequenceConclusion (ν : Measure ℝ) (M T : ℝ)
    (h s θ : ℕ → ℝ) (n : ℕ → ℕ) : Prop :=
  energyJointErrorLimits M T h n ∧ energyJointNormalizationLimits ν h s θ n ∧
  (∀ᶠ j in atTop, energyJointFiniteConclusion ν M T (h j) (s j) (θ j) (n j)) ∧
  ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop,
    |energyJointBaseProbability ν (n j) (h j) (s j) -
        energyJointCenteredProbability ν (n j) (h j) (s j) (θ j)| ≤
      η * energyJointCenteredProbability ν (n j) (h j) (s j) (θ j) ∧
    |energyJointIntegral ν (n j) (h j) (s j) -
        energyJointCenteredProbability ν (n j) (h j) (s j) (θ j)| ≤
      η * energyJointCenteredProbability ν (n j) (h j) (s j) (θ j)

def energyJointIIDConclusion {Ων : Type u} {Ωμ : Type v} {Ωθ : Type w}
    [MeasurableSpace Ων] [MeasurableSpace Ωμ] [MeasurableSpace Ωθ]
    (pν : Measure Ων) (pμ : Measure Ωμ) (pθ : Measure Ωθ)
    (ν : Measure ℝ) (M T h s θ : ℝ) {n : ℕ}
    (X : Fin n → Ων → ℝ) (Y : Fin n → Ωμ → ℝ) (W : Fin n → Ωθ → ℝ) : Prop :=
  energyRelativePathIIDConclusion pν pμ pθ ν M T h s θ X Y W ∧
  pμ.real {ω | Shao.Probability.samplePath Y ω ∈ Shao.closedStrip h} =
    energyJointBaseProbability ν n h s ∧
  pθ.real {ω | Shao.Probability.samplePath W ω ∈ Shao.closedStrip h} =
    energyJointCenteredProbability ν n h s θ ∧
  |pμ.real {ω | Shao.Probability.samplePath Y ω ∈ Shao.closedStrip h} -
      pθ.real {ω | Shao.Probability.samplePath W ω ∈ Shao.closedStrip h}| ≤
    (Real.exp (energyRelativePathError2 M T n h) - 1) *
      pθ.real {ω | Shao.Probability.samplePath W ω ∈ Shao.closedStrip h} ∧
  |(∫ ω, energyPathIntegrand h s (Shao.Probability.samplePath X ω) ∂pν) -
      pθ.real {ω | Shao.Probability.samplePath W ω ∈ Shao.closedStrip h}| ≤
    (Real.exp (energyRelativePathError M T n h) - 1) *
      pθ.real {ω | Shao.Probability.samplePath W ω ∈ Shao.closedStrip h}

def energyJointIIDTail (ν : Measure ℝ) (M T : ℝ) (h s θ : ℕ → ℝ) : Prop :=
  ∀ᶠ j in atTop, ∀ (m : ℕ) (Ων : Type u) (Ωμ : Type v) (Ωθ : Type w)
    [MeasurableSpace Ων] [MeasurableSpace Ωμ] [MeasurableSpace Ωθ]
    (pν : Measure Ων) [IsProbabilityMeasure pν]
    (pμ : Measure Ωμ) [IsProbabilityMeasure pμ]
    (pθ : Measure Ωθ) [IsProbabilityMeasure pθ]
    (X : Fin m → Ων → ℝ) (Y : Fin m → Ωμ → ℝ) (W : Fin m → Ωθ → ℝ),
    (∀ i, Measurable (X i)) → iIndepFun X pν →
    (∀ i, IdentDistrib (X i) (id : ℝ → ℝ) pν ν) →
    (∀ i, Measurable (Y i)) → iIndepFun Y pμ →
    (∀ i, IdentDistrib (Y i) (id : ℝ → ℝ) pμ (energyTiltedLaw ν (h j) (s j))) →
    (∀ i, Measurable (W i)) → iIndepFun W pθ →
    (∀ i, IdentDistrib (W i) (id : ℝ → ℝ) pθ
      (energyLinearTiltLaw ν (h j) (s j) (θ j))) →
    energyJointIIDConclusion pν pμ pθ ν M T (h j) (s j) (θ j) X Y W

private theorem joint_relative_abs {a x r : ℝ} (hr : 0 ≤ r)
    (hlo : Real.exp (-a) * r ≤ x) (hup : x ≤ Real.exp a * r) :
    |x - r| ≤ (Real.exp a - 1) * r := by
  have he : 1 - Real.exp (-a) ≤ Real.exp a - 1 := by
    linarith [Real.add_one_le_exp a, Real.add_one_le_exp (-a)]
  have hm := mul_le_mul_of_nonneg_right he hr
  apply abs_le.mpr
  constructor <;> nlinarith

private theorem joint_pow_eq_exp_log (x : ℝ) (hx : 0 < x) (n : ℕ) :
    x ^ n = Real.exp ((n : ℝ) * Real.log x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_succ, add_mul, Real.exp_add, one_mul, Real.exp_log hx]

private theorem joint_zero_of_abs_le {f g : ℕ → ℝ}
    (hg : Tendsto g atTop (𝓝 0)) (hb : ∀ᶠ j in atTop, |f j| ≤ g j) :
    Tendsto f atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero f).2
  exact squeeze_zero' (Eventually.of_forall (fun j => abs_nonneg (f j))) hb hg

/-- Deterministic errors for any length scale n/h³ → 0, including zero lengths. -/
theorem energyJointTransport_error_limits (M T : ℝ) (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hh : Tendsto h atTop atTop)
    (hn : Tendsto (fun j => (n j : ℝ) / h j ^ 3) atTop (𝓝 0)) :
    energyJointErrorLimits M T h n := by
  have hi : Tendsto (fun j => (h j)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hh
  have h4 : Tendsto (fun j => (n j : ℝ) / h j ^ 4) atTop (𝓝 (0 : ℝ)) := by
    have hm := hn.mul hi
    simp only [mul_zero] at hm
    apply hm.congr'
    filter_upwards [hh.eventually_ge_atTop 2] with j hj
    have hz : h j ≠ 0 := by linarith
    field_simp
  have h2 : Tendsto (fun j => energyRelativePathError2 M T (n j) (h j)) atTop (𝓝 0) := by
    have hl := (hi.const_mul (energyE2Constant M T)).add
      (h4.const_mul (energyE2Constant M T))
    simpa [energyRelativePathError2, div_eq_mul_inv, mul_assoc] using hl
  have he : Tendsto (fun j => energyRelativePathError M T (n j) (h j)) atTop (𝓝 0) := by
    have hl := (hn.const_mul (energyE1Constant T * M)).add h2
    simpa [energyRelativePathError, div_eq_mul_inv, mul_assoc] using hl
  have hp2 : Tendsto (fun j => Real.exp (energyRelativePathError2 M T (n j) (h j)))
      atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp h2
  have hp : Tendsto (fun j => Real.exp (energyRelativePathError M T (n j) (h j)))
      atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp he
  have hm2 : Tendsto (fun j => Real.exp (-energyRelativePathError2 M T (n j) (h j)))
      atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp (by simpa using h2.neg)
  have hm : Tendsto (fun j => Real.exp (-energyRelativePathError M T (n j) (h j)))
      atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp (by simpa using he.neg)
  exact ⟨h2, he, by simpa using hp2.sub_const 1, by simpa using hp.sub_const 1,
    hm2, hp2, hm, hp⟩

/-- Actual finite laws, positive normalizers, integrability and zero-mass-safe relative errors. -/
theorem energyJointTransport_finite_of_e2 (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (M T h s θ : ℝ) (n : ℕ) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hh : energyE2Threshold M T ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hβM : (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ M) (hE2 : energyE2Conclusion ν M T h s θ) :
    energyJointFiniteConclusion ν M T h s θ n := by
  have hheight := energyLinearCentering_height_bounds M T h hM hT hh
  have hh1 : 1 ≤ h := le_trans (by norm_num) hheight.2.2.1
  have hE1 := energyE1_common_bounds ν M T h s hM hT hheight.2.1 hs
    hSq hCube hsecond hmean hβM
  have hZ : 0 < energyNormalizer ν h s :=
    energyTiltedLaw_normalizer_pos ν T h s hT hh1 hs hSq hsecond
  have hL := energyLinearNormalizer_pos ν T h s hT hh1 hs hSq hsecond θ
  have hrel := energyRelativePath_bounds_of_e2 ν M T h s θ n hM hT hh hs
    hSq hCube hsecond hmean hβM hE2
  have hd := hrel
  rcases hd with ⟨he2, he, hpow, hp, hint, hI⟩
  have hr : 0 ≤ energyJointCenteredProbability ν n h s θ := ENNReal.toReal_nonneg
  refine ⟨hE1, hE2, hL, hZ, hrel, ?_, ?_, ?_, ?_⟩
  · have hc := Real.exp_le_exp.mpr he2
    simpa using sub_nonneg.mpr hc
  · have hc := Real.exp_le_exp.mpr he
    simpa using sub_nonneg.mpr hc
  · exact joint_relative_abs hr hp.1 hp.2
  · exact joint_relative_abs hr hI.1 hI.2

/-- Normalizer and endpoint limits for an arbitrary already centered parameter sequence. -/
theorem energyJointTransport_normalization_limits (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (M T : ℝ) (h s θ : ℕ → ℝ) (n : ℕ → ℕ) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hh : Tendsto h atTop atTop) (hs : ∀ j, |s j| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hβM : (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ M)
    (hE2 : ∀ᶠ j in atTop, energyE2Conclusion ν M T (h j) (s j) (θ j))
    (hn : Tendsto (fun j => (n j : ℝ) / h j ^ 3) atTop (𝓝 0)) :
    energyJointNormalizationLimits ν h s θ n := by
  have hH := hh.eventually_ge_atTop (energyE2Threshold M T)
  have hi : Tendsto (fun j => (h j)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hh
  have h4 : Tendsto (fun j => (n j : ℝ) / h j ^ 4) atTop (𝓝 (0 : ℝ)) := by
    have hm := hn.mul hi
    simp only [mul_zero] at hm
    apply hm.congr'
    filter_upwards [hH] with j hj
    have hh2 := (energyLinearCentering_height_bounds M T (h j) hM hT hj).2.2.1
    have hz : h j ≠ 0 := by linarith
    field_simp
  have hlogL : Tendsto (fun j => (n j : ℝ) *
      Real.log (energyLinearNormalizer ν (h j) (s j) (θ j))) atTop (𝓝 0) := by
    apply joint_zero_of_abs_le (by simpa using h4.const_mul (energyE2Constant M T))
    filter_upwards [hE2] with j hj
    rcases hj with ⟨_, _, _, _, _, _, _, _, hlog, _, _⟩
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (n j))]
    calc
      _ ≤ (n j : ℝ) * (energyE2Constant M T / h j ^ 4) :=
        mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
      _ = energyE2Constant M T * ((n j : ℝ) / h j ^ 4) := by ring
  have htheta : Tendsto (fun j => |θ j| * h j) atTop (𝓝 0) := by
    apply joint_zero_of_abs_le (by simpa [div_eq_mul_inv] using hi.const_mul (energyE2Constant M T))
    filter_upwards [hH, hE2] with j hj hE
    have hh2 := (energyLinearCentering_height_bounds M T (h j) hM hT hj).2.2.1
    have hp : 0 < h j := by linarith
    rcases hE with ⟨_, _, _, _, _, _, _, ht, _, _, _⟩
    rw [abs_mul, abs_abs, abs_of_pos hp]
    calc
      _ ≤ (energyE2Constant M T / h j ^ 2) * h j :=
        mul_le_mul_of_nonneg_right ht hp.le
      _ = energyE2Constant M T / h j := by field_simp
  have hpowL : Tendsto (fun j => (energyLinearNormalizer ν (h j) (s j) (θ j)) ^ n j)
      atTop (𝓝 1) := by
    have hl : Tendsto (fun j => Real.exp ((n j : ℝ) *
        Real.log (energyLinearNormalizer ν (h j) (s j) (θ j)))) atTop (𝓝 1) := by
      simpa only [Function.comp_def, Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp hlogL
    apply hl.congr'
    filter_upwards [hH] with j hj
    have hh2 := (energyLinearCentering_height_bounds M T (h j) hM hT hj).2.2.1
    have hL := energyLinearNormalizer_pos ν T (h j) (s j) hT
      (le_trans (by norm_num) hh2) (hs j) hSq hsecond (θ j)
    exact (joint_pow_eq_exp_log _ hL _).symm
  have hlogZ : Tendsto (fun j => (n j : ℝ) *
      (Real.log (energyNormalizer ν (h j) (s j)) - s j / h j ^ 2)) atTop (𝓝 0) := by
    apply joint_zero_of_abs_le (by simpa using hn.const_mul (energyE1Constant T * M))
    filter_upwards [hH] with j hj
    have hheight := energyLinearCentering_height_bounds M T (h j) hM hT hj
    have hp : 0 ≤ h j := le_trans (by norm_num) hheight.2.2.1
    have hE1 := energyE1_common_bounds ν M T (h j) (s j) hM hT hheight.2.1
      (hs j) hSq hCube hsecond hmean hβM
    rcases hE1 with ⟨_, _, _, _, _, _, _, hlog, _, _, _⟩
    have hP : 0 ≤ energyE1Constant T := le_trans (by norm_num)
      (energyE1Constant_dominates T hT).1
    have hq : 0 ≤ (n j : ℝ) / h j ^ 3 := div_nonneg (Nat.cast_nonneg _) (pow_nonneg hp _)
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (n j))]
    calc
      _ ≤ (n j : ℝ) * (energyE1Constant T * (∫ x : ℝ, |x| ^ 3 ∂ν) / h j ^ 3) :=
        mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
      _ = (∫ x : ℝ, |x| ^ 3 ∂ν) * (energyE1Constant T * ((n j : ℝ) / h j ^ 3)) := by ring
      _ ≤ M * (energyE1Constant T * ((n j : ℝ) / h j ^ 3)) :=
        mul_le_mul_of_nonneg_right hβM (mul_nonneg hP hq)
      _ = energyE1Constant T * M * ((n j : ℝ) / h j ^ 3) := by ring
  have henergy : Tendsto (fun j => Real.exp (-s j * (n j : ℝ) / h j ^ 2) *
      (energyNormalizer ν (h j) (s j)) ^ n j) atTop (𝓝 1) := by
    have hl : Tendsto (fun j => Real.exp ((n j : ℝ) *
        (Real.log (energyNormalizer ν (h j) (s j)) - s j / h j ^ 2))) atTop (𝓝 1) := by
      simpa only [Function.comp_def, Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp hlogZ
    apply hl.congr'
    filter_upwards [hH] with j hj
    have hh2 := (energyLinearCentering_height_bounds M T (h j) hM hT hj).2.2.1
    have hZ := energyTiltedLaw_normalizer_pos ν T (h j) (s j) hT
      (le_trans (by norm_num) hh2) (hs j) hSq hsecond
    rw [joint_pow_eq_exp_log _ hZ _, ← Real.exp_add]
    congr 1
    ring
  exact ⟨hlogL, htheta, hpowL, hlogZ, henergy⟩

/-- The true iid realization on three independent choices of probability space. -/
theorem energyJointTransport_iid_of_e2 {Ων : Type u} {Ωμ : Type v} {Ωθ : Type w}
    [MeasurableSpace Ων] [MeasurableSpace Ωμ] [MeasurableSpace Ωθ]
    (pν : Measure Ων) [IsProbabilityMeasure pν]
    (pμ : Measure Ωμ) [IsProbabilityMeasure pμ]
    (pθ : Measure Ωθ) [IsProbabilityMeasure pθ]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (M T h s θ : ℝ) (n : ℕ)
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hh : energyE2Threshold M T ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hβM : (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ M) (hE2 : energyE2Conclusion ν M T h s θ)
    (X : Fin n → Ων → ℝ) (hX : ∀ i, Measurable (X i)) (hIndepX : iIndepFun X pν)
    (hLawX : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) pν ν)
    (Y : Fin n → Ωμ → ℝ) (hY : ∀ i, Measurable (Y i)) (hIndepY : iIndepFun Y pμ)
    (hLawY : ∀ i, IdentDistrib (Y i) (id : ℝ → ℝ) pμ (energyTiltedLaw ν h s))
    (W : Fin n → Ωθ → ℝ) (hW : ∀ i, Measurable (W i)) (hIndepW : iIndepFun W pθ)
    (hLawW : ∀ i, IdentDistrib (W i) (id : ℝ → ℝ) pθ (energyLinearTiltLaw ν h s θ)) :
    energyJointIIDConclusion pν pμ pθ ν M T h s θ X Y W := by
  have hdata := energyRelativePath_iid_of_e2 pν pμ pθ ν M T h s θ n hM hT hh hs
    hSq hCube hsecond hmean hβM hE2 X hX hIndepX hLawX Y hY hIndepY hLawY W hW hIndepW hLawW
  have hh2 := (energyLinearCentering_height_bounds M T h hM hT hh).2.2.1
  have hh1 : 1 ≤ h := le_trans (by norm_num) hh2
  have hp := (energyLinearPathLaw_base_probability_iid pμ ν n T h s hT hh1 hs
    hSq hsecond Y hY hIndepY hLawY).symm
  have hr := (energyLinearPathLaw_probability_iid pθ ν n T h s θ hT hh1 hs
    hSq hsecond W hW hIndepW hLawW).symm
  have hfin := energyJointTransport_finite_of_e2 ν M T h s θ n hM hT hh hs
    hSq hCube hsecond hmean hβM hE2
  rcases hfin with ⟨_, _, _, _, _, _, _, habs2, habs⟩
  have hi := hdata.2.1
  refine ⟨hdata, hp, hr, ?_, ?_⟩
  · simpa only [hp, hr, energyJointBaseProbability, energyJointCenteredProbability] using habs2
  · simpa only [hi, hr, energyJointIntegral, energyJointCenteredProbability] using habs

/-- Full joint conclusion for any eventually valid common centering sequence. -/
theorem energyJointTransport_sequence_of_e2 (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (M T : ℝ) (h s θ : ℕ → ℝ) (n : ℕ → ℕ) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hh : Tendsto h atTop atTop) (hs : ∀ j, |s j| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hβM : (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ M)
    (hE2 : ∀ᶠ j in atTop, energyE2Conclusion ν M T (h j) (s j) (θ j))
    (hn : Tendsto (fun j => (n j : ℝ) / h j ^ 3) atTop (𝓝 0)) :
    energyJointSequenceConclusion ν M T h s θ n := by
  have he := energyJointTransport_error_limits M T h n hh hn
  have hnorm := energyJointTransport_normalization_limits ν M T h s θ n hM hT hh hs
    hSq hCube hsecond hmean hβM hE2 hn
  have hfin : ∀ᶠ j in atTop, energyJointFiniteConclusion ν M T (h j) (s j) (θ j) (n j) := by
    filter_upwards [hh.eventually_ge_atTop (energyE2Threshold M T), hE2] with j hj hEj
    exact energyJointTransport_finite_of_e2 ν M T (h j) (s j) (θ j) (n j) hM hT hj (hs j)
      hSq hCube hsecond hmean hβM hEj
  refine ⟨he, hnorm, hfin, ?_⟩
  intro η hη
  have hd2 := he.2.2.1.eventually (gt_mem_nhds hη)
  have hd := he.2.2.2.1.eventually (gt_mem_nhds hη)
  filter_upwards [hfin, hd2, hd] with j hj hδ2 hδ
  rcases hj with ⟨_, _, _, _, _, _, _, habs2, habs⟩
  have hr : 0 ≤ energyJointCenteredProbability ν (n j) (h j) (s j) (θ j) :=
    ENNReal.toReal_nonneg
  exact ⟨habs2.trans (mul_le_mul_of_nonneg_right hδ2.le hr),
    habs.trans (mul_le_mul_of_nonneg_right hδ.le hr)⟩

/-- One centering sequence is selected before every length sequence and every iid realization.
Early heights may be zero or negative; all actual law conclusions are supplied on the cofinal tail. -/
theorem energyJointTransport_common_bounds (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (M T : ℝ) (h s : ℕ → ℝ) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hh : Tendsto h atTop atTop) (hs : ∀ j, |s j| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hβM : (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ M) :
    ∃ θ : ℕ → ℝ,
      (∀ j, h j < energyE2Threshold M T → θ j = 0) ∧
      (∀ᶠ j in atTop, energyE2Conclusion ν M T (h j) (s j) (θ j) ∧
        ∀ m : ℕ, energyRelativePathConclusion ν M T (h j) (s j) (θ j) m) ∧
      energyJointIIDTail.{u,v,w} ν M T h s θ ∧
      ∀ n : ℕ → ℕ, Tendsto (fun j => (n j : ℝ) / h j ^ 3) atTop (𝓝 0) →
        energyJointSequenceConclusion ν M T h s θ n := by
  classical
  have hselect : ∀ (a b : ℝ), energyE2Threshold M T ≤ a → |b| ≤ T →
      ∃ t : ℝ, energyE2Conclusion ν M T a b t ∧
        ∀ m : ℕ, energyRelativePathConclusion ν M T a b t m := by
    intro a b ha hb
    exact energyRelativePath_common_bounds ν M T a b hM hT ha hb
      hSq hCube hsecond hmean hβM
  let Θ : ℝ → ℝ → ℝ := fun a b => if ha : energyE2Threshold M T ≤ a then
    if hb : |b| ≤ T then Classical.choose (hselect a b ha hb) else 0 else 0
  let θ : ℕ → ℝ := fun j => Θ (h j) (s j)
  have htail : ∀ᶠ j in atTop, energyE2Conclusion ν M T (h j) (s j) (θ j) ∧
      ∀ m : ℕ, energyRelativePathConclusion ν M T (h j) (s j) (θ j) m := by
    filter_upwards [hh.eventually_ge_atTop (energyE2Threshold M T)] with j hj
    simpa only [θ, Θ, dite_eq_left hj, dite_eq_left (hs j)] using
      Classical.choose_spec (hselect (h j) (s j) hj (hs j))
  have hE2 := htail.mono (fun j hj => hj.1)
  refine ⟨θ, ?_, htail, ?_, ?_⟩
  · intro j hj
    simp [θ, Θ, not_le.mpr hj]
  · filter_upwards [hh.eventually_ge_atTop (energyE2Threshold M T), hE2] with j hj hEj
    intro m Ων Ωμ Ωθ _ _ _ pν _ pμ _ pθ _ X Y W hX hIndepX hLawX hY hIndepY hLawY hW hIndepW hLawW
    exact energyJointTransport_iid_of_e2 pν pμ pθ ν M T (h j) (s j) (θ j) m hM hT hj
      (hs j) hSq hCube hsecond hmean hβM hEj X hX hIndepX hLawX Y hY hIndepY hLawY W hW hIndepW hLawW
  · intro n hn
    exact energyJointTransport_sequence_of_e2 ν M T h s θ n hM hT hh hs
      hSq hCube hsecond hmean hβM hE2 hn

end Shao.OQ4
