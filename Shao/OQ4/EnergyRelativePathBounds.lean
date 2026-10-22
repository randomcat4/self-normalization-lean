import Shao.OQ4.EnergyE2Bounds
import Shao.OQ4.EnergyLinearPathLaw

/-! Finite multiplicative path bounds for the same actual E2 centering parameter. -/

namespace Shao.OQ4

open MeasureTheory ProbabilityTheory

noncomputable def energyRelativePathError2 (M T : ℝ) (n : ℕ) (h : ℝ) : ℝ :=
  energyE2Constant M T / h + energyE2Constant M T * (n : ℝ) / h ^ 4

noncomputable def energyRelativePathError (M T : ℝ) (n : ℕ) (h : ℝ) : ℝ :=
  energyE1Constant T * M * (n : ℝ) / h ^ 3 + energyRelativePathError2 M T n h

/-- All finite conclusions concern the same actual product laws and closed event. -/
def energyRelativePathConclusion (ν : Measure ℝ) (M T h s θ : ℝ) (n : ℕ) : Prop :=
  0 ≤ energyRelativePathError2 M T n h ∧
  0 ≤ energyRelativePathError M T n h ∧
  (Real.exp (-energyE2Constant M T / h) * (energyLinearNormalizer ν h s θ) ^ n *
      (Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s θ)).real (Shao.closedStrip h) ≤
      (Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s)).real (Shao.closedStrip h) ∧
    (Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s)).real (Shao.closedStrip h) ≤
      Real.exp (energyE2Constant M T / h) * (energyLinearNormalizer ν h s θ) ^ n *
        (Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s θ)).real (Shao.closedStrip h)) ∧
  (Real.exp (-energyRelativePathError2 M T n h) *
      (Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s θ)).real (Shao.closedStrip h) ≤
      (Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s)).real (Shao.closedStrip h) ∧
    (Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s)).real (Shao.closedStrip h) ≤
      Real.exp (energyRelativePathError2 M T n h) *
        (Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s θ)).real (Shao.closedStrip h)) ∧
  Integrable (energyPathIntegrand (n := n) h s) (Measure.pi (fun _ : Fin n => ν)) ∧
  (Real.exp (-energyRelativePathError M T n h) *
      (Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s θ)).real (Shao.closedStrip h) ≤
      (∫ a, energyPathIntegrand h s a ∂Measure.pi (fun _ : Fin n => ν)) ∧
    (∫ a, energyPathIntegrand h s a ∂Measure.pi (fun _ : Fin n => ν)) ≤
      Real.exp (energyRelativePathError M T n h) *
        (Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s θ)).real (Shao.closedStrip h))

theorem energyRelativePath_errors_nonneg (M T h : ℝ) (n : ℕ)
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hh : 0 ≤ h) :
    0 ≤ energyRelativePathError2 M T n h ∧ 0 ≤ energyRelativePathError M T n h := by
  have hP : 0 ≤ energyE1Constant T := le_trans (by norm_num) (energyE1Constant_dominates T hT).1
  have hC : 0 ≤ energyE2Constant M T := le_trans (by norm_num) (energyE2Constant_dominates M T hM hT).1
  unfold energyRelativePathError energyRelativePathError2
  constructor <;> positivity

private theorem relativePath_pow_eq_exp_log (x : ℝ) (hx : 0 < x) (n : ℕ) :
    x ^ n = Real.exp ((n : ℝ) * Real.log x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_succ, add_mul, one_mul, Real.exp_add, Real.exp_log hx]

/-- Any parameter satisfying the actual E2 conclusion obeys the finite path bounds. -/
theorem energyRelativePath_bounds_of_e2 (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (M T h s θ : ℝ) (n : ℕ) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hh : energyE2Threshold M T ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hβM : (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ M)
    (hE2 : energyE2Conclusion ν M T h s θ) :
    energyRelativePathConclusion ν M T h s θ n := by
  have hheight := energyLinearCentering_height_bounds M T h hM hT hh
  have hh2 : 2 ≤ h := hheight.2.2.1
  have hh1 : 1 ≤ h := by linarith
  have hh0 : 0 < h := by linarith
  have hP : 0 ≤ energyE1Constant T := le_trans (by norm_num) (energyE1Constant_dominates T hT).1
  obtain ⟨_hμprob, _hμi, _hμq, _hμc, _hμsupport, _hh2, hZbounds, hlogZ,
    _hμmean, _hμsecond, _hμthird⟩ :=
    energyE1_common_bounds ν M T h s hM hT hheight.2.1 hs hSq hCube hsecond hmean hβM
  obtain ⟨_hMean, _hprob, _hsupport, _hi, _hq, _hc, _hmeanInt, hθ, hlogL, _hqerr, _hcbd⟩ := hE2
  let p := (Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s)).real (Shao.closedStrip h)
  let r := (Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s θ)).real (Shao.closedStrip h)
  let L := energyLinearNormalizer ν h s θ
  let Z := energyNormalizer ν h s
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hL0 : 0 < L := energyLinearNormalizer_pos ν T h s hT hh1 hs hSq hsecond θ
  have hZ0 : 0 < Z := by dsimp [Z]; linarith [hZbounds.1]
  have hendpoint : |θ| * h ≤ energyE2Constant M T / h := by
    calc
      _ ≤ (energyE2Constant M T / h ^ 2) * h := mul_le_mul_of_nonneg_right hθ hh0.le
      _ = _ := by field_simp
  have hraw := energyLinearPathLaw_sandwich ν n T h s θ hT hh1 hs hSq hsecond
  change L ^ n * Real.exp (-|θ| * h) * r ≤ p ∧ p ≤ L ^ n * Real.exp (|θ| * h) * r at hraw
  have hpow0 := (pow_pos hL0 n).le
  have hendpointBounds : Real.exp (-energyE2Constant M T / h) * L ^ n * r ≤ p ∧
      p ≤ Real.exp (energyE2Constant M T / h) * L ^ n * r := by
    constructor
    · calc
        _ = L ^ n * Real.exp (-energyE2Constant M T / h) * r := by ring
        _ ≤ L ^ n * Real.exp (-|θ| * h) * r :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (by simpa only [neg_div, neg_mul] using neg_le_neg hendpoint)) hpow0) hr0
        _ ≤ p := hraw.1
    · calc
        p ≤ L ^ n * Real.exp (|θ| * h) * r := hraw.2
        _ ≤ L ^ n * Real.exp (energyE2Constant M T / h) * r :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr hendpoint) hpow0) hr0
        _ = _ := by ring
  have hLogPow : |(n : ℝ) * Real.log L| ≤ energyE2Constant M T * (n : ℝ) / h ^ 4 := by
    calc
      _ = (n : ℝ) * |Real.log L| := by rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
      _ ≤ (n : ℝ) * (energyE2Constant M T / h ^ 4) :=
        mul_le_mul_of_nonneg_left hlogL (Nat.cast_nonneg n)
      _ = _ := by ring
  have hLogPowBounds := abs_le.mp hLogPow
  have hLpow := relativePath_pow_eq_exp_log L hL0 n
  have hloFactor : Real.exp (-energyRelativePathError2 M T n h) ≤
      Real.exp (-energyE2Constant M T / h) * L ^ n := by
    rw [hLpow, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    unfold energyRelativePathError2
    simp only [neg_div]
    linarith [hLogPowBounds.1]
  have hhiFactor : Real.exp (energyE2Constant M T / h) * L ^ n ≤
      Real.exp (energyRelativePathError2 M T n h) := by
    rw [hLpow, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    unfold energyRelativePathError2
    linarith [hLogPowBounds.2]
  have habsorbed : Real.exp (-energyRelativePathError2 M T n h) * r ≤ p ∧
      p ≤ Real.exp (energyRelativePathError2 M T n h) * r :=
    ⟨(mul_le_mul_of_nonneg_right hloFactor hr0).trans hendpointBounds.1,
      hendpointBounds.2.trans (mul_le_mul_of_nonneg_right hhiFactor hr0)⟩
  obtain ⟨hFi, hidentity⟩ := energyPathLaw_integral ν n T h s hT hh1 hs hSq hsecond
  let B := Real.exp (-s * (n : ℝ) / h ^ 2) * Z ^ n
  change (∫ a, energyPathIntegrand h s a ∂Measure.pi (fun _ : Fin n => ν)) = B * p at hidentity
  have hBexp : B = Real.exp ((n : ℝ) * (Real.log Z - s / h ^ 2)) := by
    dsimp [B]
    rw [relativePath_pow_eq_exp_log Z hZ0 n, ← Real.exp_add]
    congr 1
    ring
  have hδ : |(n : ℝ) * (Real.log Z - s / h ^ 2)| ≤
      energyE1Constant T * M * (n : ℝ) / h ^ 3 := by
    calc
      _ = (n : ℝ) * |Real.log Z - s / h ^ 2| := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
      _ ≤ (n : ℝ) * (energyE1Constant T * (∫ x : ℝ, |x| ^ 3 ∂ν) / h ^ 3) :=
        mul_le_mul_of_nonneg_left hlogZ (Nat.cast_nonneg n)
      _ ≤ (n : ℝ) * (energyE1Constant T * M / h ^ 3) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hβM hP) (pow_nonneg hh0.le 3)) (Nat.cast_nonneg n)
      _ = _ := by ring
  have hδbounds := abs_le.mp hδ
  have hBlo : Real.exp (-(energyE1Constant T * M * (n : ℝ) / h ^ 3)) ≤ B := by
    rw [hBexp]
    exact Real.exp_le_exp.mpr hδbounds.1
  have hBhi : B ≤ Real.exp (energyE1Constant T * M * (n : ℝ) / h ^ 3) := by
    rw [hBexp]
    exact Real.exp_le_exp.mpr hδbounds.2
  have hweighted : Real.exp (-energyRelativePathError M T n h) * r ≤
      (∫ a, energyPathIntegrand h s a ∂Measure.pi (fun _ : Fin n => ν)) ∧
      (∫ a, energyPathIntegrand h s a ∂Measure.pi (fun _ : Fin n => ν)) ≤
        Real.exp (energyRelativePathError M T n h) * r := by
    constructor
    · calc
        _ = Real.exp (-(energyE1Constant T * M * (n : ℝ) / h ^ 3)) *
            (Real.exp (-energyRelativePathError2 M T n h) * r) := by
          rw [energyRelativePathError, neg_add, Real.exp_add]
          ring
        _ ≤ Real.exp (-(energyE1Constant T * M * (n : ℝ) / h ^ 3)) * p :=
          mul_le_mul_of_nonneg_left habsorbed.1 (Real.exp_nonneg _)
        _ ≤ B * p := mul_le_mul_of_nonneg_right hBlo hp0
        _ = _ := hidentity.symm
    · calc
        _ = B * p := hidentity
        _ ≤ Real.exp (energyE1Constant T * M * (n : ℝ) / h ^ 3) * p :=
          mul_le_mul_of_nonneg_right hBhi hp0
        _ ≤ Real.exp (energyE1Constant T * M * (n : ℝ) / h ^ 3) *
            (Real.exp (energyRelativePathError2 M T n h) * r) :=
          mul_le_mul_of_nonneg_left habsorbed.2 (Real.exp_nonneg _)
        _ = _ := by rw [energyRelativePathError, Real.exp_add]; ring
  obtain ⟨he2, he⟩ := energyRelativePath_errors_nonneg M T h n hM hT hh0.le
  exact ⟨he2, he, hendpointBounds, habsorbed, hFi, hweighted⟩

/-- E2 is called once, before n, and its complete actual-law conclusion is retained. -/
theorem energyRelativePath_common_bounds (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (M T h s : ℝ) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hh : energyE2Threshold M T ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hβM : (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ M) :
    ∃ θ : ℝ, energyE2Conclusion ν M T h s θ ∧
      ∀ n : ℕ, energyRelativePathConclusion ν M T h s θ n := by
  obtain ⟨θ, hE2⟩ := energyE2_common_bounds ν M T h s hM hT hh hs hSq hCube hsecond hmean hβM
  exact ⟨θ, hE2, fun n => energyRelativePath_bounds_of_e2 ν M T h s θ n hM hT hh hs
    hSq hCube hsecond hmean hβM hE2⟩

/-- An original-law iid realization needs no realization of either tilted law. -/
theorem energyRelativePath_integral_iid {Ω : Type*} [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (M T h s θ : ℝ) (n : ℕ)
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hh : energyE2Threshold M T ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hβM : (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ M) (hE2 : energyE2Conclusion ν M T h s θ)
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hIndepX : iIndepFun X p)
    (hLawX : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) p ν) :
    Integrable (fun ω => energyPathIntegrand h s (Shao.Probability.samplePath X ω)) p ∧
    (∫ ω, energyPathIntegrand h s (Shao.Probability.samplePath X ω) ∂p) =
      (∫ a, energyPathIntegrand h s a ∂Measure.pi (fun _ : Fin n => ν)) ∧
    (Real.exp (-energyRelativePathError M T n h) *
        (Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s θ)).real (Shao.closedStrip h) ≤
        (∫ ω, energyPathIntegrand h s (Shao.Probability.samplePath X ω) ∂p) ∧
      (∫ ω, energyPathIntegrand h s (Shao.Probability.samplePath X ω) ∂p) ≤
        Real.exp (energyRelativePathError M T n h) *
          (Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s θ)).real (Shao.closedStrip h)) := by
  have hheight := energyLinearCentering_height_bounds M T h hM hT hh
  have hh1 : 1 ≤ h := by linarith [hheight.2.2.1]
  obtain ⟨hFi, hsample⟩ := energyPathLaw_integral_iid p ν n T h s hT hh1 hs hSq hsecond
    X hX hIndepX hLawX
  have hcanonical := (energyPathLaw_integral ν n T h s hT hh1 hs hSq hsecond).2
  have hI : (∫ ω, energyPathIntegrand h s (Shao.Probability.samplePath X ω) ∂p) =
      (∫ a, energyPathIntegrand h s a ∂Measure.pi (fun _ : Fin n => ν)) :=
    hsample.trans hcanonical.symm
  have hweighted := (energyRelativePath_bounds_of_e2 ν M T h s θ n hM hT hh hs
    hSq hCube hsecond hmean hβM hE2).2.2.2.2.2
  rw [← hI] at hweighted
  exact ⟨hFi, hI, hweighted⟩
/-- Sample versions may use three unrelated probability spaces. -/
def energyRelativePathIIDConclusion {Ων Ωμ Ωθ : Type*}
    [MeasurableSpace Ων] [MeasurableSpace Ωμ] [MeasurableSpace Ωθ]
    (pν : Measure Ων) (pμ : Measure Ωμ) (pθ : Measure Ωθ)
    (ν : Measure ℝ) (M T h s θ : ℝ) {n : ℕ}
    (X : Fin n → Ων → ℝ) (Y : Fin n → Ωμ → ℝ) (W : Fin n → Ωθ → ℝ) : Prop :=
  Integrable (fun ω => energyPathIntegrand h s (Shao.Probability.samplePath X ω)) pν ∧
  (∫ ω, energyPathIntegrand h s (Shao.Probability.samplePath X ω) ∂pν) =
    (∫ a, energyPathIntegrand h s a ∂Measure.pi (fun _ : Fin n => ν)) ∧
  (Real.exp (-energyE2Constant M T / h) * (energyLinearNormalizer ν h s θ) ^ n *
      pθ.real {ω | Shao.Probability.samplePath W ω ∈ Shao.closedStrip h} ≤
      pμ.real {ω | Shao.Probability.samplePath Y ω ∈ Shao.closedStrip h} ∧
    pμ.real {ω | Shao.Probability.samplePath Y ω ∈ Shao.closedStrip h} ≤
      Real.exp (energyE2Constant M T / h) * (energyLinearNormalizer ν h s θ) ^ n *
        pθ.real {ω | Shao.Probability.samplePath W ω ∈ Shao.closedStrip h}) ∧
  (Real.exp (-energyRelativePathError2 M T n h) *
      pθ.real {ω | Shao.Probability.samplePath W ω ∈ Shao.closedStrip h} ≤
      pμ.real {ω | Shao.Probability.samplePath Y ω ∈ Shao.closedStrip h} ∧
    pμ.real {ω | Shao.Probability.samplePath Y ω ∈ Shao.closedStrip h} ≤
      Real.exp (energyRelativePathError2 M T n h) *
        pθ.real {ω | Shao.Probability.samplePath W ω ∈ Shao.closedStrip h}) ∧
  (Real.exp (-energyRelativePathError M T n h) *
      pθ.real {ω | Shao.Probability.samplePath W ω ∈ Shao.closedStrip h} ≤
      (∫ ω, energyPathIntegrand h s (Shao.Probability.samplePath X ω) ∂pν) ∧
    (∫ ω, energyPathIntegrand h s (Shao.Probability.samplePath X ω) ∂pν) ≤
      Real.exp (energyRelativePathError M T n h) *
        pθ.real {ω | Shao.Probability.samplePath W ω ∈ Shao.closedStrip h})

/-- The true iid map bridges transport every finite conclusion for this same θ. -/
theorem energyRelativePath_iid_of_e2 {Ων Ωμ Ωθ : Type*}
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
    energyRelativePathIIDConclusion pν pμ pθ ν M T h s θ X Y W := by
  have hheight := energyLinearCentering_height_bounds M T h hM hT hh
  have hh1 : 1 ≤ h := by linarith [hheight.2.2.1]
  obtain ⟨hFi, hsample⟩ := energyPathLaw_integral_iid pν ν n T h s hT hh1 hs hSq hsecond
    X hX hIndepX hLawX
  have hcanonical := (energyPathLaw_integral ν n T h s hT hh1 hs hSq hsecond).2
  have hI : (∫ ω, energyPathIntegrand h s (Shao.Probability.samplePath X ω) ∂pν) =
      (∫ a, energyPathIntegrand h s a ∂Measure.pi (fun _ : Fin n => ν)) :=
    hsample.trans hcanonical.symm
  have hbase := energyLinearPathLaw_base_probability_iid pμ ν n T h s hT hh1 hs hSq hsecond
    Y hY hIndepY hLawY
  have htilt := energyLinearPathLaw_probability_iid pθ ν n T h s θ hT hh1 hs hSq hsecond
    W hW hIndepW hLawW
  obtain ⟨_he2, _he, hendpoint, habsorbed, _hcanonicalFi, hweighted⟩ :=
    energyRelativePath_bounds_of_e2 ν M T h s θ n hM hT hh hs hSq hCube hsecond hmean hβM hE2
  rw [hbase, htilt] at hendpoint habsorbed
  rw [htilt, ← hI] at hweighted
  exact ⟨hFi, hI, hendpoint, habsorbed, hweighted⟩

/-- One internally chosen θ works for all lengths and all three-space iid realizations. -/
theorem energyRelativePath_common_bounds_iid {Ων Ωμ Ωθ : Type*}
    [MeasurableSpace Ων] [MeasurableSpace Ωμ] [MeasurableSpace Ωθ]
    (pν : Measure Ων) [IsProbabilityMeasure pν]
    (pμ : Measure Ωμ) [IsProbabilityMeasure pμ]
    (pθ : Measure Ωθ) [IsProbabilityMeasure pθ]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (M T h s : ℝ)
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hh : energyE2Threshold M T ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hβM : (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ M) :
    ∃ θ : ℝ, energyE2Conclusion ν M T h s θ ∧
      (∀ n : ℕ, energyRelativePathConclusion ν M T h s θ n) ∧
      ∀ (n : ℕ) (X : Fin n → Ων → ℝ) (Y : Fin n → Ωμ → ℝ) (W : Fin n → Ωθ → ℝ),
        (∀ i, Measurable (X i)) → iIndepFun X pν →
        (∀ i, IdentDistrib (X i) (id : ℝ → ℝ) pν ν) →
        (∀ i, Measurable (Y i)) → iIndepFun Y pμ →
        (∀ i, IdentDistrib (Y i) (id : ℝ → ℝ) pμ (energyTiltedLaw ν h s)) →
        (∀ i, Measurable (W i)) → iIndepFun W pθ →
        (∀ i, IdentDistrib (W i) (id : ℝ → ℝ) pθ (energyLinearTiltLaw ν h s θ)) →
        energyRelativePathIIDConclusion pν pμ pθ ν M T h s θ X Y W := by
  obtain ⟨θ, hE2, hfinite⟩ := energyRelativePath_common_bounds ν M T h s hM hT hh hs
    hSq hCube hsecond hmean hβM
  refine ⟨θ, hE2, hfinite, ?_⟩
  intro n X Y W hX hIndepX hLawX hY hIndepY hLawY hW hIndepW hLawW
  exact energyRelativePath_iid_of_e2 pν pμ pθ ν M T h s θ n hM hT hh hs
    hSq hCube hsecond hmean hβM hE2 X hX hIndepX hLawX Y hY hIndepY hLawY W hW hIndepW hLawW

end Shao.OQ4
