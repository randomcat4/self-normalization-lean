import Shao.Probability.RademacherGrid
import Shao.Probability.BrownianSup
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Finite grids for the actual Brownian motion

The definitions here are the frozen B2 node G objects.  The dense-grid
argument works on the single a.e. set of continuous sample paths.
-/

namespace Shao.Probability.BrownianSup

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BigOperators

noncomputable def gridTime (d j : ℕ) : ℝ≥0 :=
  ⟨(j : ℝ) / (d : ℝ), div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω)

def brownianGridEvent (d : ℕ) (x : ℝ) : Set Ω :=
  {ω | ∀ j : ℕ, j ≤ d → |B (gridTime d j) ω| ≤ x}

noncomputable def brownianGridProbability (d : ℕ) (x : ℝ) : ℝ :=
  P.real (brownianGridEvent B d x)

private instance radMeasure_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (radMeasure n) := by
  unfold radMeasure
  infer_instance

private def blockSum (d m : ℕ) (a : Shao.Path (d * m)) (i : Fin d) : ℝ :=
  ∑ k : Fin m, a (finProdFinEquiv (i, k))

private noncomputable def radBlockVector (d m : ℕ) (a : Shao.Path (d * m)) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => (Real.sqrt (d : ℝ))⁻¹ *
    ((Real.sqrt (m : ℝ))⁻¹ * blockSum d m a i))

private theorem radBlockVector_measurable (d m : ℕ) :
    Measurable (radBlockVector d m) := by
  unfold radBlockVector blockSum
  fun_prop

private theorem rad_law_integral (f : ℝ → ℝ) :
    (∫ y, f y ∂Shao.OQ4.RademacherCosine.law) =
      (1 / 2 : ℝ) * f 1 + (1 / 2 : ℝ) * f (-1) := by
  let h := Shao.OQ4.RademacherCosine.halfENNReal
  have hh : h ≠ ⊤ := by norm_num [h, Shao.OQ4.RademacherCosine.halfENNReal]
  have hp : Integrable f (h • Measure.dirac (1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure hh
  have hn : Integrable f (h • Measure.dirac (-1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure hh
  rw [Shao.OQ4.RademacherCosine.law, integral_add_measure hp hn,
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  norm_num [h, Shao.OQ4.RademacherCosine.halfENNReal, ENNReal.toReal_div]

private theorem rad_law_mean :
    (∫ y : ℝ, y ∂Shao.OQ4.RademacherCosine.law) = 0 := by
  rw [rad_law_integral]
  norm_num

private theorem rad_law_second :
    (∫ y : ℝ, y ^ 2 ∂Shao.OQ4.RademacherCosine.law) = 1 := by
  rw [rad_law_integral]
  norm_num

private theorem radBlockVector_charFun (d m : ℕ) (t : EuclideanSpace ℝ (Fin d)) :
    charFun ((radMeasure (d * m)).map (radBlockVector d m)) t =
      ∏ i : Fin d, (charFun Shao.OQ4.RademacherCosine.law
        ((Real.sqrt (m : ℝ))⁻¹ * ((Real.sqrt (d : ℝ))⁻¹ * t i))) ^ m := by
  classical
  let c : Fin (d * m) → ℝ := fun k =>
    (Real.sqrt (m : ℝ))⁻¹ * ((Real.sqrt (d : ℝ))⁻¹ * t (finProdFinEquiv.symm k).1)
  have hinner (a : Shao.Path (d * m)) :
      inner ℝ (radBlockVector d m a) t = ∑ k : Fin (d * m), c k * a k := by
    rw [← finProdFinEquiv.sum_comp]
    simp only [Fintype.sum_prod_type, c, Equiv.symm_apply_apply, radBlockVector,
      PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      blockSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [charFun_map_eq_charFun_map_inner_one (radBlockVector_measurable d m).aemeasurable]
  simp_rw [hinner]
  have hi : iIndepFun (fun k : Fin (d * m) => fun a : Shao.Path (d * m) => c k * a k)
      (radMeasure (d * m)) := by
    exact (iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)).comp
      (fun k y => c k * y) (by fun_prop)
  rw [hi.charFun_map_fun_sum_eq_prod
    (fun k => ((measurable_pi_apply k).const_mul (c k)).aemeasurable)]
  simp only [Finset.prod_apply]
  have heval (k : Fin (d * m)) :
      (radMeasure (d * m)).map (fun a : Shao.Path (d * m) => a k) =
        Shao.OQ4.RademacherCosine.law :=
    (measurePreserving_eval (fun _ : Fin (d * m) => Shao.OQ4.RademacherCosine.law) k).map_eq
  have hfactor (k : Fin (d * m)) :
      charFun ((radMeasure (d * m)).map
        (fun a : Shao.Path (d * m) => c k * a k)) (1 : ℝ) =
          charFun Shao.OQ4.RademacherCosine.law (c k) := by
    rw [charFun_map_mul_comp (measurable_pi_apply k).aemeasurable, heval, mul_one]
  simp_rw [hfactor]
  rw [← finProdFinEquiv.prod_comp]
  have he (i : Fin d) (k : Fin m) : (finProdFinEquiv (i, k)).divNat = i := by
    exact congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (i, k))
  simp [Fintype.prod_prod_type, c, he]

private noncomputable def brownianBlockVector (d : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => B (gridTime d (i.val + 1)) ω - B (gridTime d i.val) ω)

private theorem gridTime_monotone (d : ℕ) : Monotone (gridTime d) := by
  intro i j hij
  change (i : ℝ) / (d : ℝ) ≤ (j : ℝ) / (d : ℝ)
  exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (Nat.cast_nonneg d)

private theorem brownianBlockVector_aemeasurable (hB : IsBrownianReal B P) (d : ℕ) :
    AEMeasurable (brownianBlockVector B d) P := by
  apply (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp_aemeasurable
  exact AEMeasurable.of_eval fun i =>
    (hB.toIsPreBrownianReal.aemeasurable _).sub (hB.toIsPreBrownianReal.aemeasurable _)

private theorem brownian_blocks_independent (hB : IsBrownianReal B P) (d : ℕ) :
    iIndepFun (fun i : Fin d => fun ω =>
      B (gridTime d (i.val + 1)) ω - B (gridTime d i.val) ω) P := by
  exact hB.toIsPreBrownianReal.hasIndepIncrements d (fun i => gridTime d i.val)
    ((gridTime_monotone d).comp (fun _ _ h => h))

private theorem gridTime_mem {d j : ℕ} (hd : 0 < d) (hj : j ≤ d) :
    gridTime d j ∈ Icc (0 : ℝ≥0) 1 := by
  constructor
  · exact bot_le
  · change (j : ℝ) / (d : ℝ) ≤ 1
    exact (div_le_one (by exact_mod_cast hd)).2 (by exact_mod_cast hj)

private theorem gridTime_double (d j : ℕ) (hd : 0 < d) :
    gridTime (2 * d) (2 * j) = gridTime d j := by
  apply Subtype.ext
  change ((2 * j : ℕ) : ℝ) / ((2 * d : ℕ) : ℝ) = (j : ℝ) / (d : ℝ)
  push_cast
  field_simp

omit [MeasurableSpace Ω] in
private theorem brownianGridEvent_dyadic_antitone (x : ℝ) :
    Antitone (fun r : ℕ => brownianGridEvent B (2 ^ r) x) := by
  apply antitone_nat_of_succ_le
  intro r ω hω j hj
  have hpow : 0 < 2 ^ r := pow_pos (by norm_num) _
  have hj' : 2 * j ≤ 2 ^ (r + 1) := by
    rw [pow_succ]
    omega
  have h := hω (2 * j) hj'
  rw [show 2 ^ (r + 1) = 2 * 2 ^ r by rw [pow_succ]; omega,
    gridTime_double (2 ^ r) j hpow] at h
  exact h

variable [IsProbabilityMeasure P]

private theorem brownian_block_variance (d : ℕ) (hd : 0 < d) (i : Fin d) :
    nndist (gridTime d (i.val + 1)).1
      (gridTime d i.val).1 =
        (⟨1 / (d : ℝ), by positivity⟩ : ℝ≥0) := by
  apply Subtype.ext
  change |((i.val + 1 : ℕ) : ℝ) / (d : ℝ) - (i.val : ℝ) / (d : ℝ)| = 1 / (d : ℝ)
  rw [abs_of_nonneg]
  · push_cast
    ring
  · apply sub_nonneg.2
    exact div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg d)

omit [IsProbabilityMeasure P] in
private theorem brownian_block_charFun (hB : IsBrownianReal B P)
    (d : ℕ) (hd : 0 < d) (i : Fin d) (t : ℝ) :
    charFun (P.map (fun ω =>
      B (gridTime d (i.val + 1)) ω - B (gridTime d i.val) ω)) t =
        Complex.exp (-((((Real.sqrt (d : ℝ))⁻¹ * t) : ℂ) ^ 2) / 2) := by
  change charFun (P.map (B (gridTime d (i.val + 1)) - B (gridTime d i.val))) t = _
  rw [(hB.toIsPreBrownianReal.hasLaw_sub
    (gridTime d (i.val + 1)) (gridTime d i.val)).map_eq]
  rw! [brownian_block_variance d hd i]
  trans Complex.exp ((t : ℂ) * 0 * Complex.I -
    ((1 / (d : ℝ) : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2)
  · exact charFun_gaussianReal (μ := 0)
      (v := (⟨1 / (d : ℝ), by positivity⟩ : ℝ≥0)) t
  have hs : ((Real.sqrt (d : ℝ))⁻¹ * t) ^ 2 = (1 / (d : ℝ)) * t ^ 2 := by
    rw [mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    ring
  have hsc := congrArg (fun y : ℝ => (y : ℂ)) hs
  push_cast at hsc
  simp only [mul_zero, zero_mul, zero_sub]
  push_cast
  rw [hsc]
  ring_nf

private theorem rad_blocks_tendsto (hB : IsBrownianReal B P) (d : ℕ) (hd : 0 < d) :
    TendstoInDistribution (fun m => radBlockVector d m) atTop
      (brownianBlockVector B d) (fun m => radMeasure (d * m)) P := by
  apply TendstoInDistribution.of_tendsto_charFun
    (fun m => (radBlockVector_measurable d m).aemeasurable)
    (brownianBlockVector_aemeasurable B P hB d)
  intro t
  have hjoint := (iIndepFun_iff_charFun_pi (fun i : Fin d =>
    (hB.toIsPreBrownianReal.aemeasurable (gridTime d (i.val + 1))).sub
      (hB.toIsPreBrownianReal.aemeasurable (gridTime d i.val)))).1
        (brownian_blocks_independent B P hB d) t
  change Tendsto _ _ (𝓝 (charFun (P.map (brownianBlockVector B d)) t))
  rw [show charFun (P.map (brownianBlockVector B d)) t =
      ∏ i : Fin d, Complex.exp (-((((Real.sqrt (d : ℝ))⁻¹ * t i) : ℂ) ^ 2) / 2) by
        exact hjoint.trans (Finset.prod_congr rfl fun i _ => brownian_block_charFun B P hB d hd i (t i))]
  simp_rw [radBlockVector_charFun]
  apply tendsto_finsetProd
  intro i _
  simpa only [Measure.map_id, Complex.ofReal_mul] using
    (tendsto_charFun_inv_sqrt_mul_pow (P := Shao.OQ4.RademacherCosine.law)
      (X := id) aemeasurable_id rad_law_mean rad_law_second
      ((Real.sqrt (d : ℝ))⁻¹ * t i))

private noncomputable def cumulative (d : ℕ) (v : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => Shao.prefixSum (WithLp.ofLp v) (i.val + 1))

private theorem cumulative_continuous (d : ℕ) : Continuous (cumulative d) := by
  unfold cumulative Shao.prefixSum
  fun_prop

private noncomputable def radEndpointVector (d m : ℕ) (a : Shao.Path (d * m)) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => (Real.sqrt (d * m : ℝ))⁻¹ *
    Shao.prefixSum a ((i.val + 1) * m))

private noncomputable def brownianEndpointVector (d : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => B (gridTime d (i.val + 1)) ω)

private theorem cumulative_radBlockVector (d m : ℕ) (a : Shao.Path (d * m)) :
    cumulative d (radBlockVector d m a) = radEndpointVector d m a := by
  classical
  apply PiLp.ext
  intro j
  change (∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j.val + 1),
    (Real.sqrt (d : ℝ))⁻¹ * ((Real.sqrt (m : ℝ))⁻¹ *
      ∑ k : Fin m, a (finProdFinEquiv (i, k)))) =
    (Real.sqrt (d * m : ℝ))⁻¹ * Shao.prefixSum a ((j.val + 1) * m)
  have hc : (Real.sqrt (d * m : ℝ))⁻¹ =
      (Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt (m : ℝ))⁻¹ := by
    rw [Real.sqrt_mul (Nat.cast_nonneg d), mul_inv]
  rw [hc, Shao.prefixSum]
  simp only [Finset.sum_filter]
  rw [← finProdFinEquiv.sum_comp]
  simp only [Fintype.sum_prod_type]
  change (∑ i : Fin d, if i.val < j.val + 1 then
    (Real.sqrt (d : ℝ))⁻¹ * ((Real.sqrt (m : ℝ))⁻¹ *
      ∑ k : Fin m, a (finProdFinEquiv (i, k))) else 0) =
    (Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt (m : ℝ))⁻¹ *
      ∑ i : Fin d, ∑ k : Fin m,
        if k.val + m * i.val < (j.val + 1) * m then a (finProdFinEquiv (i, k)) else 0
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  have hh (k : Fin m) : k.val + m * i.val < (j.val + 1) * m ↔ i.val < j.val + 1 := by
    constructor
    · intro h
      by_contra hi
      have hmul := Nat.mul_le_mul_right m (Nat.le_of_not_gt hi)
      nlinarith
    · intro hi
      have hmul := Nat.mul_le_mul_right m hi
      nlinarith [k.is_lt]
  simp_rw [hh]
  split_ifs <;> simp [Finset.mul_sum, mul_assoc]

private theorem prefixSum_succ {n : ℕ} (a : Shao.Path n) (k : ℕ) (hk : k < n) :
    Shao.prefixSum a (k + 1) = Shao.prefixSum a k + a ⟨k, hk⟩ := by
  classical
  have heq : Finset.univ.filter (fun i : Fin n => i.val < k + 1) =
      insert ⟨k, hk⟩ (Finset.univ.filter (fun i : Fin n => i.val < k)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hi
      by_cases h : i.val = k
      · left
        exact Fin.ext h
      · right
        omega
    · rintro (rfl | hi)
      · simp
      · omega
  rw [Shao.prefixSum, heq, Finset.sum_insert]
  · rw [add_comm]
    rfl
  · simp

omit [MeasurableSpace Ω] in
private theorem brownian_prefix_telescope (d k : ℕ) (hk : k ≤ d) (ω : Ω) :
    Shao.prefixSum (WithLp.ofLp (brownianBlockVector B d ω)) k =
      B (gridTime d k) ω - B 0 ω := by
  induction k with
  | zero =>
    have hz : gridTime d 0 = 0 := by apply Subtype.ext; simp [gridTime]
    simp [hz]
  | succ k ih =>
    rw [prefixSum_succ _ k (by omega), ih (by omega)]
    change (B (gridTime d k) ω - B 0 ω) +
      (B (gridTime d (k + 1)) ω - B (gridTime d k) ω) = _
    ring

private theorem rad_endpoints_tendsto (hB : IsBrownianReal B P) (d : ℕ) (hd : 0 < d) :
    TendstoInDistribution (fun m => radEndpointVector d m) atTop
      (brownianEndpointVector B d) (fun m => radMeasure (d * m)) P := by
  have h := (rad_blocks_tendsto B P hB d hd).continuous_comp (cumulative_continuous d)
  apply h.congr
  · intro m
    exact Eventually.of_forall fun a => cumulative_radBlockVector d m a
  · filter_upwards [hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω
    apply PiLp.ext
    intro i
    change Shao.prefixSum (WithLp.ofLp (brownianBlockVector B d ω)) (i.val + 1) = _
    rw [brownian_prefix_telescope B d (i.val + 1) (by omega) ω, hω, sub_zero]
    rfl

private def gridCube (d : ℕ) (x : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {v | ∀ i, |v i| ≤ x}

private theorem gridCube_closed (d : ℕ) (x : ℝ) : IsClosed (gridCube d x) := by
  simp only [gridCube, ofPred_forall]
  exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const

private theorem gridCube_frontier_subset (d : ℕ) (x : ℝ) :
    frontier (gridCube d x) ⊆
      ⋃ i : Fin d, {v : EuclideanSpace ℝ (Fin d) | v i = x ∨ v i = -x} := by
  intro v hv
  have hweak : ∀ i, |v i| ≤ x := by
    have hcl := frontier_subset_closure hv
    rwa [(gridCube_closed d x).closure_eq] at hcl
  by_contra h
  have hstrict : ∀ i, |v i| < x := by
    intro i
    apply lt_of_le_of_ne (hweak i)
    intro heq
    apply h
    apply mem_iUnion.2 ⟨i, ?_⟩
    rcases le_total 0 (v i) with hi | hi
    · left
      simpa only [abs_of_nonneg hi] using heq
    · right
      have hh : -(v i) = x := by simpa only [abs_of_nonpos hi] using heq
      linarith
  have hopen : IsOpen {w : EuclideanSpace ℝ (Fin d) | ∀ i, |w i| < x} := by
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (by fun_prop) continuous_const
  have hinterior : {w : EuclideanSpace ℝ (Fin d) | ∀ i, |w i| < x} ⊆
      interior (gridCube d x) :=
    interior_maximal (fun _ hw i => (hw i).le) hopen
  exact hv.2 (hinterior hstrict)

omit [IsProbabilityMeasure P] in
private theorem brownian_positive_time_level_null (hB : IsBrownianReal B P)
    (t : ℝ≥0) (ht : t ≠ 0) (y : ℝ) : P {ω | B t ω = y} = 0 := by
  have : NullSingletonClass (gaussianReal 0 t) := nullSingletonClass_gaussianReal ht
  have h := (hB.toIsPreBrownianReal.hasLaw_eval t).measure_eq (measurableSet_singleton y)
  have hs : {z : ℝ | z = y} = {y} := by ext z; rfl
  rw [hs, measure_singleton] at h
  exact h

omit [IsProbabilityMeasure P] in
private theorem brownianEndpointVector_aemeasurable (hB : IsBrownianReal B P) (d : ℕ) :
    AEMeasurable (brownianEndpointVector B d) P := by
  apply (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp_aemeasurable
  exact AEMeasurable.of_eval fun _ => hB.toIsPreBrownianReal.aemeasurable _

omit [IsProbabilityMeasure P] in
private theorem brownian_grid_cube_null_frontier (hB : IsBrownianReal B P)
    (d : ℕ) (hd : 0 < d) (x : ℝ) :
    (P.map (brownianEndpointVector B d)) (frontier (gridCube d x)) = 0 := by
  rw [Measure.map_apply_of_aemeasurable
    (brownianEndpointVector_aemeasurable B P hB d) isClosed_frontier.measurableSet]
  apply measure_mono_null (preimage_mono (gridCube_frontier_subset d x))
  rw [preimage_iUnion]
  apply measure_iUnion_null
  intro i
  have ht : gridTime d (i.val + 1) ≠ 0 := by
    intro hz
    have hz' : (((i.val + 1 : ℕ) : ℝ) / (d : ℝ)) = 0 :=
      congrArg (fun z : ℝ≥0 => (z : ℝ)) hz
    exact (div_pos (by positivity) (by exact_mod_cast hd)).ne' hz'
  change P ({ω | B (gridTime d (i.val + 1)) ω = x} ∪
    {ω | B (gridTime d (i.val + 1)) ω = -x}) = 0
  exact measure_union_null
    (brownian_positive_time_level_null B P hB _ ht x)
    (brownian_positive_time_level_null B P hB _ ht (-x))

private theorem rad_cube_event (d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (x : ℝ) (hx : 0 < x) :
    (radEndpointVector d m) ⁻¹' gridCube d x = coarseStrip d m x := by
  ext a
  have hs : 0 < Real.sqrt (d * m : ℝ) := by positivity
  have hbound (y : ℝ) : |(Real.sqrt (d * m : ℝ))⁻¹ * y| ≤ x ↔
      |y| ≤ x * Real.sqrt (d * m : ℝ) := by
    rw [abs_mul, abs_inv, abs_of_pos hs, ← div_eq_inv_mul, div_le_iff₀ hs]
  change (∀ i : Fin d, |(Real.sqrt (d * m : ℝ))⁻¹ *
      Shao.prefixSum a ((i.val + 1) * m)| ≤ x) ↔
    ∀ j : ℕ, j ≤ d → |Shao.prefixSum a (j * m)| ≤ x * Real.sqrt (d * m : ℝ)
  simp_rw [hbound]
  constructor
  · intro h j hj
    rcases j with _ | j
    · simp only [zero_mul, Shao.prefixSum_zero, abs_zero]
      positivity
    · exact h ⟨j, by omega⟩
  · intro h i
    exact h (i.val + 1) (by omega)

omit [IsProbabilityMeasure P] in
private theorem brownian_cube_event_ae (hB : IsBrownianReal B P)
    (d : ℕ) (x : ℝ) (hx : 0 < x) :
    (brownianEndpointVector B d) ⁻¹' gridCube d x =ᵐ[P] brownianGridEvent B d x := by
  filter_upwards [hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hzero
  apply propext
  change (∀ i : Fin d, |B (gridTime d (i.val + 1)) ω| ≤ x) ↔
    ∀ j : ℕ, j ≤ d → |B (gridTime d j) ω| ≤ x
  constructor
  · intro h j hj
    rcases j with _ | j
    · have hz : gridTime d 0 = 0 := by apply Subtype.ext; simp [gridTime]
      simpa only [hz, hzero, abs_zero] using hx.le
    · exact h ⟨j, by omega⟩
  · intro h i
    exact h (i.val + 1) (by omega)

theorem rademacher_coarse_tendsto_brownian_grid (hB : IsBrownianReal B P)
    (d : ℕ) (hd : 0 < d) (x : ℝ) (hx : 0 < x) :
    Tendsto (fun m : ℕ => coarseProbability d m x) atTop
      (𝓝 (brownianGridProbability B P d x)) := by
  have hconv := rad_endpoints_tendsto B P hB d hd
  have hlim := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    hconv.tendsto (brownian_grid_cube_null_frontier B P hB d hd x)
  simp only [ProbabilityMeasure.coe_mk] at hlim
  have htarget : (P.map (brownianEndpointVector B d)) (gridCube d x) =
      P (brownianGridEvent B d x) := by
    rw [Measure.map_apply_of_aemeasurable
      (brownianEndpointVector_aemeasurable B P hB d) (gridCube_closed d x).measurableSet]
    exact measure_congr (brownian_cube_event_ae B P hB d x hx)
  rw [htarget] at hlim
  have hreal := (ENNReal.continuousAt_toReal
    (measure_ne_top P (brownianGridEvent B d x))).tendsto.comp hlim
  apply hreal.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  change (((radMeasure (d * m)).map (radEndpointVector d m)) (gridCube d x)).toReal =
    coarseProbability d m x
  rw [Measure.map_apply_of_aemeasurable (hconv.forall_aemeasurable m)
    (gridCube_closed d x).measurableSet, rad_cube_event d m hd (by omega) x hx]
  rfl

omit [IsProbabilityMeasure P] in
private theorem brownianGridEvent_nullMeasurable (hB : IsBrownianReal B P)
    (d : ℕ) (x : ℝ) : NullMeasurableSet (brownianGridEvent B d x) P := by
  have heq : brownianGridEvent B d x =
      ⋂ j ∈ Finset.range (d + 1), {ω | |B (gridTime d j) ω| ≤ x} := by
    ext ω
    simp only [brownianGridEvent, mem_ofPred_eq, mem_iInter, Finset.mem_range]
    constructor
    · intro h j hj
      exact h j (by omega)
    · intro h j hj
      exact h j (by omega)
  rw [heq]
  apply Finset.nullMeasurableSet_biInter
  intro j _
  exact (continuous_abs.measurable.comp_aemeasurable
    (hB.toIsPreBrownianReal.aemeasurable (gridTime d j))).nullMeasurableSet_preimage
      measurableSet_Iic

private theorem dyadic_floor_tendsto (t : ℝ≥0) :
    Tendsto (fun r : ℕ => gridTime (2 ^ r) ⌊(t : ℝ) * ((2 ^ r : ℕ) : ℝ)⌋₊)
      atTop (𝓝 t) := by
  apply NNReal.tendsto_coe.1
  have hp : Tendsto (fun r : ℕ => ((2 ^ r : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  exact (tendsto_nat_floor_mul_div_atTop t.2).comp hp

omit [IsProbabilityMeasure P] in
private theorem fullStrip_ae_eq_dyadic_iInter (hB : IsBrownianReal B P) (x : ℝ) :
    fullStrip B x =ᵐ[P] ⋂ r : ℕ, brownianGridEvent B (2 ^ r) x := by
  filter_upwards [hB.cont] with ω hc
  apply propext
  constructor
  · intro h
    simp only [mem_iInter]
    intro r j hj
    exact h _ (gridTime_mem (pow_pos (by norm_num) r) hj)
  · intro h t ht
    have hbound : ∀ r : ℕ,
        |B (gridTime (2 ^ r) ⌊(t : ℝ) * ((2 ^ r : ℕ) : ℝ)⌋₊) ω| ≤ x := by
      intro r
      have hj : ⌊(t : ℝ) * ((2 ^ r : ℕ) : ℝ)⌋₊ ≤ 2 ^ r := by
        have ht' : (t : ℝ) ≤ 1 := ht.2
        have hmul : (t : ℝ) * ((2 ^ r : ℕ) : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) :=
          by nlinarith [(Nat.cast_nonneg (2 ^ r : ℕ) : (0 : ℝ) ≤ _)]
        exact (Nat.floor_mono hmul).trans_eq (Nat.floor_natCast (R := ℝ) (2 ^ r))
      exact (mem_iInter.mp h r) _ hj
    exact le_of_tendsto ((hc.abs.tendsto t).comp (dyadic_floor_tendsto t))
      (Eventually.of_forall hbound)

theorem brownian_dyadic_grid_tendsto_probability (hB : IsBrownianReal B P) (x : ℝ) :
    Tendsto (fun r : ℕ => brownianGridProbability B P (2 ^ r) x) atTop
      (𝓝 (probability B P hB x)) := by
  have hlim := tendsto_measure_iInter_atTop
    (fun r => brownianGridEvent_nullMeasurable B P hB (2 ^ r) x)
    (brownianGridEvent_dyadic_antitone B x) ⟨0, measure_ne_top P _⟩
  have heq : P (⋂ r : ℕ, brownianGridEvent B (2 ^ r) x) = P (fullStrip B x) :=
    measure_congr (fullStrip_ae_eq_dyadic_iInter B P hB x).symm
  rw [heq] at hlim
  have hreal :=
    (ENNReal.continuousAt_toReal (measure_ne_top P (fullStrip B x))).tendsto.comp hlim
  simpa only [brownianGridProbability, Function.comp_def, ← measureReal_def,
    ← probability_eq_fullStrip B P hB x] using hreal

end Shao.Probability.BrownianSup
