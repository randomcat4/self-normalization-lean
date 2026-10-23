-- Lane-lead exact formal freeze: all54 heads and17 transparent values (16defs+1abbrev).
-- Complete implementation draft under frozen heads/values; no Lean gate yet.
-- Parent fully read proof, all exact heads/literal values and pinned API evidence before freeze.
-- Namespace is lane-owned; no shared Probability/common-definition edit is needed.
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Algebra.Order.Floor.Semiring

noncomputable section
namespace Shao.OQ4.CanonicalBrownian
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

-- PUBLIC concrete sample space, probability measure, and literal process.
abbrev Sample := (ℕ × ℕ) → ℝ

def law : Measure Sample :=
  Measure.infinitePi (fun _ : ℕ × ℕ => gaussianReal 0 1)

instance instIsProbabilityMeasureLaw : IsProbabilityMeasure law := by
  unfold law
  infer_instance

private def coord (i : ℕ × ℕ) (ω : Sample) : ℝ := ω i

private def clip (u : ℝ) : ℝ := max 0 (min 1 u)

private def tent (u : ℝ) : ℝ := max 0 (1 - |2 * u - 1|)

private def amplitude (n : ℕ) : ℝ := (2 * (Real.sqrt 2) ^ n)⁻¹

private def hat (n k : ℕ) (u : ℝ) : ℝ :=
  amplitude n * tent ((2 : ℝ) ^ n * u - (k : ℝ))

private def level (m n : ℕ) (u : ℝ) (ω : Sample) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ n), coord (m, 2 ^ n + k) ω * hat n k u

private def unitPartial (m N : ℕ) (u : ℝ) (ω : Sample) : ℝ :=
  u * coord (m, 0) ω + ∑ n ∈ Finset.range N, level m n u ω

private def unit (m : ℕ) (u : ℝ) (ω : Sample) : ℝ :=
  u * coord (m, 0) ω + ∑' n : ℕ, level m n u ω

private def Bpartial (N : ℕ) (t : ℝ≥0) (ω : Sample) : ℝ :=
  ∑ m ∈ Finset.range (⌊(t : ℝ)⌋₊ + 1),
    unitPartial m N (clip ((t : ℝ) - (m : ℝ))) ω

def B (t : ℝ≥0) (ω : Sample) : ℝ :=
  ∑ m ∈ Finset.range (⌊(t : ℝ)⌋₊ + 1),
    unit m (clip ((t : ℝ) - (m : ℝ))) ω

private def fourthMoment : ℝ :=
  ∫ x : ℝ, |x| ^ 4 ∂gaussianReal 0 1

private def bad (m n : ℕ) : Set Sample :=
  {ω | ∃ k ∈ Finset.range (2 ^ n),
    (4 / 3 : ℝ) ^ n < |coord (m, 2 ^ n + k) ω|}

private def Good (ω : Sample) : Prop :=
  ∀ m : ℕ, ∀ᶠ n : ℕ in atTop, ω ∉ bad m n

private def unitCov (N : ℕ) (u v : ℝ) : ℝ :=
  u * v + ∑ n ∈ Finset.range N,
    ∑ k ∈ Finset.range (2 ^ n), hat n k u * hat n k v

private def fullCov (N : ℕ) (s t : ℝ≥0) : ℝ :=
  ∑ m ∈ Finset.range (⌊((max s t : ℝ≥0) : ℝ)⌋₊ + 1),
    unitCov N (clip ((s : ℝ) - (m : ℝ)))
      (clip ((t : ℝ) - (m : ℝ)))

-- PRIVATE probability/convergence obligation inventory.
private theorem measurable_coord (i : ℕ × ℕ) : Measurable (coord i) := by
  exact measurable_pi_apply i

private theorem hasLaw_coord (i : ℕ × ℕ) :
    HasLaw (coord i) (gaussianReal 0 1) law := by
  exact (measurePreserving_eval_infinitePi
    (fun _ : ℕ × ℕ => gaussianReal 0 1) i).hasLaw

private theorem iIndepFun_coord : iIndepFun coord law := by
  exact iIndepFun_infinitePi (X := fun _ : ℕ × ℕ => (id : ℝ → ℝ))
    (fun _ => measurable_id)

private theorem integrable_fourthMoment :
    Integrable (fun x : ℝ => |x| ^ 4) (gaussianReal 0 1) := by
  have h : MemLp (id : ℝ → ℝ) (4 : ℝ≥0∞) (gaussianReal 0 1) := by
    simpa using (memLp_id_gaussianReal (μ := 0) (v := 1) (4 : ℝ≥0))
  simpa only [id_eq, Real.norm_eq_abs] using
    h.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)

private theorem measurableSet_bad (m n : ℕ) : MeasurableSet (bad m n) := by
  classical
  have heq : bad m n = ⋃ k ∈ Finset.range (2 ^ n),
      {ω | (4 / 3 : ℝ) ^ n < |coord (m, 2 ^ n + k) ω|} := by
    ext ω
    simp [bad]
  rw [heq]
  exact Finset.measurableSet_biUnion _ fun k _ =>
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (measurable_coord _))

private theorem bad_measure_le (m n : ℕ) :
    law (bad m n) ≤ ENNReal.ofReal (fourthMoment * (81 / 128 : ℝ) ^ n) := by
  classical
  have hC : 0 ≤ fourthMoment := integral_nonneg (fun _ => by positivity)
  have hr : 0 < (4 / 3 : ℝ) ^ n := pow_pos (by norm_num) _
  have hmom (i : ℕ × ℕ) :
      (∫⁻ ω, ENNReal.ofReal (|coord i ω| ^ 4) ∂law) =
        ENNReal.ofReal fourthMoment := by
    calc
      _ = ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ 4) ∂law.map (coord i) :=
        (lintegral_map (by fun_prop) (measurable_coord i)).symm
      _ = ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ 4) ∂gaussianReal 0 1 := by
        rw [(hasLaw_coord i).map_eq]
      _ = ENNReal.ofReal fourthMoment :=
        (ofReal_integral_eq_lintegral_ofReal integrable_fourthMoment
          (ae_of_all _ fun _ => by positivity)).symm
  have htail (k : ℕ) :
      law {ω | (4 / 3 : ℝ) ^ n < |coord (m, 2 ^ n + k) ω|} ≤
        ENNReal.ofReal (fourthMoment / (((4 / 3 : ℝ) ^ n) ^ 4)) := by
    calc
      _ ≤ law {ω | ENNReal.ofReal (((4 / 3 : ℝ) ^ n) ^ 4) ≤
          ENNReal.ofReal (|coord (m, 2 ^ n + k) ω| ^ 4)} := by
        apply measure_mono
        intro ω hω
        apply ENNReal.ofReal_le_ofReal
        exact pow_le_pow_left₀ hr.le hω.le _
      _ ≤ (∫⁻ ω, ENNReal.ofReal (|coord (m, 2 ^ n + k) ω| ^ 4) ∂law) /
          ENNReal.ofReal (((4 / 3 : ℝ) ^ n) ^ 4) :=
        meas_ge_le_lintegral_div
          (ENNReal.measurable_ofReal.comp
            ((continuous_abs.measurable.comp (measurable_coord _)).pow_const 4)).aemeasurable
          (by positivity) (by simp)
      _ = ENNReal.ofReal (fourthMoment / (((4 / 3 : ℝ) ^ n) ^ 4)) := by
        rw [hmom, ENNReal.ofReal_div_of_pos (pow_pos hr _)]
  have heq : bad m n = ⋃ k ∈ Finset.range (2 ^ n),
      {ω | (4 / 3 : ℝ) ^ n < |coord (m, 2 ^ n + k) ω|} := by
    ext ω
    simp [bad]
  calc
    law (bad m n) ≤ ∑ k ∈ Finset.range (2 ^ n),
        law {ω | (4 / 3 : ℝ) ^ n < |coord (m, 2 ^ n + k) ω|} := by
      rw [heq]
      exact measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range (2 ^ n),
        ENNReal.ofReal (fourthMoment / (((4 / 3 : ℝ) ^ n) ^ 4)) :=
      Finset.sum_le_sum fun k _ => htail k
    _ = ENNReal.ofReal (fourthMoment * (81 / 128 : ℝ) ^ n) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      push_cast
      have hp : ((4 / 3 : ℝ) ^ n) ^ 4 = ((4 / 3 : ℝ) ^ 4) ^ n := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm n 4]
      calc
        (2 : ℝ) ^ n * (fourthMoment / (((4 / 3 : ℝ) ^ n) ^ 4)) =
            fourthMoment * ((2 : ℝ) ^ n / (((4 / 3 : ℝ) ^ 4) ^ n)) := by
          rw [hp]
          ring
        _ = fourthMoment * ((2 : ℝ) / ((4 / 3 : ℝ) ^ 4)) ^ n := by rw [← div_pow]
        _ = fourthMoment * (81 / 128 : ℝ) ^ n := by norm_num

private theorem good_ae : ∀ᵐ ω ∂law, Good ω := by
  have hs : Summable (fun n : ℕ => fourthMoment * (81 / 128 : ℝ) ^ n) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(81 / 128 : ℝ)‖ < 1)).mul_left _
  apply ae_all_iff.2
  intro m
  apply ae_eventually_notMem
  exact ne_top_of_le_ne_top hs.tsum_ofReal_ne_top
    (ENNReal.tsum_le_tsum (fun n => bad_measure_le m n))

private theorem hat_zero (n k : ℕ) : hat n k 0 = 0 := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  simp only [hat, tent, mul_zero, zero_sub]
  rw [abs_of_nonpos (by linarith), max_eq_left (by linarith), mul_zero]

private theorem hat_one (n k : ℕ) (hk : k < 2 ^ n) : hat n k 1 = 0 := by
  have hk' : (k : ℝ) + 1 ≤ (2 : ℝ) ^ n := by exact_mod_cast hk
  simp only [hat, tent, mul_one]
  rw [abs_of_nonneg (by linarith), max_eq_left (by linarith), mul_zero]

private theorem level_bound (m n : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (ω : Sample) (hω : ∀ k ∈ Finset.range (2 ^ n),
      |coord (m, 2 ^ n + k) ω| ≤ R) (u : ℝ) :
    |level m n u ω| ≤ amplitude n * R := by
  classical
  have ha : 0 ≤ amplitude n := by unfold amplitude; positivity
  have hnonneg (k : ℕ) : 0 ≤ tent ((2 : ℝ) ^ n * u - k) := le_max_left _ _
  have hle (k : ℕ) : tent ((2 : ℝ) ^ n * u - k) ≤ 1 := by
    unfold tent
    exact max_le (by norm_num) (by linarith [abs_nonneg (2 * ((2 : ℝ) ^ n * u - k) - 1)])
  have hdisj (k l : ℕ) (hkl : k ≠ l)
      (hk : tent ((2 : ℝ) ^ n * u - k) ≠ 0) :
      tent ((2 : ℝ) ^ n * u - l) = 0 := by
    by_contra hl
    have hkp := lt_of_le_of_ne (hnonneg k) (Ne.symm hk)
    have hlp := lt_of_le_of_ne (hnonneg l) (Ne.symm hl)
    have hkabs : |2 * ((2 : ℝ) ^ n * u - k) - 1| < 1 := by
      have hh := (lt_max_iff.mp hkp).resolve_left (lt_irrefl (0 : ℝ))
      linarith
    have hlabs : |2 * ((2 : ℝ) ^ n * u - l) - 1| < 1 := by
      have hh := (lt_max_iff.mp hlp).resolve_left (lt_irrefl (0 : ℝ))
      linarith
    obtain ⟨hklo, hkhi⟩ := abs_lt.mp hkabs
    obtain ⟨hllo, hlhi⟩ := abs_lt.mp hlabs
    have hdist : |(k : ℝ) - l| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
    have : k = l := by
      rcases lt_or_gt_of_ne hkl with h | h
      · have : (k : ℝ) + 1 ≤ l := by exact_mod_cast h
        rw [abs_of_nonpos (by linarith)] at hdist
        linarith
      · have : (l : ℝ) + 1 ≤ k := by exact_mod_cast h
        rw [abs_of_nonneg (by linarith)] at hdist
        linarith
    exact hkl this
  by_cases hz : ∀ k ∈ Finset.range (2 ^ n), tent ((2 : ℝ) ^ n * u - k) = 0
  · have heq : level m n u ω = 0 := by
      unfold level hat
      apply Finset.sum_eq_zero
      intro k hk
      simp [hz k hk]
    rw [heq, abs_zero]
    positivity
  · push_neg at hz
    obtain ⟨k, hk, hkt⟩ := hz
    have heq : level m n u ω = coord (m, 2 ^ n + k) ω * hat n k u := by
      unfold level
      apply Finset.sum_eq_single k
      · intro l _ hlk
        simp [hat, hdisj k l (Ne.symm hlk) hkt]
      · exact fun h => (h hk).elim
    rw [heq, abs_mul, hat, abs_mul, abs_of_nonneg ha,
      abs_of_nonneg (hnonneg k)]
    calc
      _ ≤ R * (amplitude n * 1) := mul_le_mul (hω k hk)
        (mul_le_mul_of_nonneg_left (hle k) ha) (mul_nonneg ha (hnonneg k)) hR
      _ = amplitude n * R := by ring

private theorem unitPartial_zero (m N : ℕ) (ω : Sample) :
    unitPartial m N 0 ω = 0 := by
  simp [unitPartial, level, hat_zero]

private theorem unit_zero (m : ℕ) (ω : Sample) : unit m 0 ω = 0 := by
  simp [unit, level, hat_zero]

private theorem unitPartial_one (m N : ℕ) (ω : Sample) :
    unitPartial m N 1 ω = coord (m, 0) ω := by
  have hz (n : ℕ) : level m n 1 ω = 0 := by
    unfold level
    apply Finset.sum_eq_zero
    intro k hk
    simp [hat_one n k (Finset.mem_range.mp hk)]
  simp [unitPartial, hz]

private theorem unit_one (m : ℕ) (ω : Sample) :
    unit m 1 ω = coord (m, 0) ω := by
  have hz (n : ℕ) : level m n 1 ω = 0 := by
    unfold level
    apply Finset.sum_eq_zero
    intro k hk
    simp [hat_one n k (Finset.mem_range.mp hk)]
  simp [unit, hz]

private theorem continuous_unitPartial (m N : ℕ) (ω : Sample) :
    Continuous (fun u : ℝ => unitPartial m N u ω) := by
  unfold unitPartial level hat tent
  fun_prop

private theorem unitPartial_tendstoUniformlyOn (ω : Sample) (hω : Good ω) (m : ℕ) :
    TendstoUniformlyOn (fun N u => unitPartial m N u ω)
      (fun u => unit m u ω) atTop Set.univ := by
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hr : ‖(4 : ℝ) / (3 * Real.sqrt 2)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    apply (div_lt_one (by positivity)).2
    nlinarith
  have hs : Summable (fun n : ℕ => (1 / 2 : ℝ) *
      ((4 : ℝ) / (3 * Real.sqrt 2)) ^ n) :=
    (summable_geometric_of_norm_lt_one hr).mul_left _
  have hb : ∀ᶠ n : ℕ in atTop, ∀ u ∈ (Set.univ : Set ℝ),
      ‖level m n u ω‖ ≤ (1 / 2 : ℝ) *
        ((4 : ℝ) / (3 * Real.sqrt 2)) ^ n := by
    filter_upwards [hω m] with n hn u _
    have hc : ∀ k ∈ Finset.range (2 ^ n),
        |coord (m, 2 ^ n + k) ω| ≤ (4 / 3 : ℝ) ^ n := by
      intro k hk
      exact le_of_not_gt (fun h => hn ⟨k, hk, h⟩)
    have hl := level_bound m n ((4 / 3 : ℝ) ^ n) (by positivity) ω hc u
    rw [Real.norm_eq_abs]
    convert hl using 1 <;> unfold amplitude
    simp only [mul_inv_rev, mul_pow, div_pow]
    ring
  have ht := tendstoUniformlyOn_tsum_nat_eventually hs hb
  rw [Metric.tendstoUniformlyOn_iff] at ht ⊢
  intro ε hε
  filter_upwards [ht ε hε] with N hN u hu
  simpa only [unit, unitPartial, Real.dist_eq, add_sub_add_left_eq_sub] using hN u hu

private theorem continuous_unit_of_good (ω : Sample) (hω : Good ω) (m : ℕ) :
    Continuous (fun u : ℝ => unit m u ω) := by
  exact continuousOn_univ.mp
    ((unitPartial_tendstoUniformlyOn ω hω m).continuousOn
      (Filter.Eventually.of_forall fun N =>
        (continuous_unitPartial m N ω).continuousOn).frequently)

private theorem B_eq_sum_of_le (ω : Sample) (M : ℕ) (t : ℝ≥0)
    (ht : (t : ℝ) ≤ (M : ℝ)) :
    B t ω = ∑ m ∈ Finset.range M,
      unit m (clip ((t : ℝ) - (m : ℝ))) ω := by
  classical
  have hfloor : (⌊(t : ℝ)⌋₊ : ℝ) ≤ t := Nat.floor_le t.2
  have hfloorM : ⌊(t : ℝ)⌋₊ ≤ M := by exact_mod_cast hfloor.trans ht
  unfold B
  by_cases hlt : ⌊(t : ℝ)⌋₊ < M
  · apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt hlt))
    intro m _ hm
    have hm' : ⌊(t : ℝ)⌋₊ + 1 ≤ m := by simpa only [Finset.mem_range, not_lt] using hm
    have htm : (t : ℝ) - m ≤ 0 := by
      have hf := Nat.lt_floor_add_one (t : ℝ)
      have hm'' : ((⌊(t : ℝ)⌋₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm'
      push_cast at hm''
      linarith
    have hc : clip ((t : ℝ) - m) = 0 := by
      unfold clip
      rw [min_eq_right (by linarith), max_eq_left htm]
    simp [hc, unit_zero]
  · have heq : ⌊(t : ℝ)⌋₊ = M := by omega
    have htM : (t : ℝ) = M := by rw [heq] at hfloor; linarith
    rw [heq, Finset.sum_range_succ]
    simp [htM, clip, unit_zero]

private theorem continuous_B_of_good (ω : Sample) (hω : Good ω) :
    Continuous (fun t : ℝ≥0 => B t ω) := by
  classical
  apply continuous_iff_continuousAt.2
  intro t
  obtain ⟨M, hM⟩ := exists_nat_gt (t : ℝ)
  have heq : (fun s : ℝ≥0 => B s ω) =ᶠ[𝓝 t]
      (fun s => ∑ m ∈ Finset.range M,
        unit m (clip ((s : ℝ) - (m : ℝ))) ω) := by
    filter_upwards [(isOpen_lt continuous_subtype_val continuous_const).mem_nhds hM]
      with s hs
    exact B_eq_sum_of_le ω M s hs.le
  have hc : Continuous (fun s : ℝ≥0 => ∑ m ∈ Finset.range M,
      unit m (clip ((s : ℝ) - (m : ℝ))) ω) := by
    apply continuous_finsetSum
    intro m _
    exact (continuous_unit_of_good ω hω m).comp (by unfold clip; fun_prop)
  exact hc.continuousAt.congr_of_eventuallyEq heq

private theorem measurable_Bpartial (N : ℕ) (t : ℝ≥0) :
    Measurable (Bpartial N t) := by
  unfold Bpartial unitPartial level coord
  fun_prop

private theorem Bpartial_tendsto_of_good (ω : Sample) (hω : Good ω) (t : ℝ≥0) :
    Tendsto (fun N => Bpartial N t ω) atTop (𝓝 (B t ω)) := by
  classical
  unfold Bpartial B
  exact tendsto_finsetSum _ fun m _ =>
    (unitPartial_tendstoUniformlyOn ω hω m).tendsto_at (Set.mem_univ _)

-- PRIVATE deterministic covariance and characteristic-function obligations.
-- No desired Brownian/FDD/continuity property occurs as an assumption here.
private theorem coordinate_index_injective (n p k l : ℕ)
    (hk : k < 2 ^ n) (hl : l < 2 ^ p)
    (h : 2 ^ n + k = 2 ^ p + l) : n = p ∧ k = l := by
  have hnp : n = p := by
    rcases lt_trichotomy n p with hnp | hnp | hpn
    · have hp : 2 ^ (n + 1) ≤ 2 ^ p := by gcongr; omega
      rw [pow_succ] at hp
      omega
    · exact hnp
    · have hn : 2 ^ (p + 1) ≤ 2 ^ n := by gcongr; omega
      rw [pow_succ] at hn
      omega
  subst p
  exact ⟨rfl, by omega⟩

private theorem unitCov_dyadic (N j k : ℕ) (hj : j ≤ 2 ^ N) (hk : k ≤ 2 ^ N) :
    unitCov N ((j : ℝ) / (2 : ℝ) ^ N) ((k : ℝ) / (2 : ℝ) ^ N) =
      min ((j : ℝ) / (2 : ℝ) ^ N) ((k : ℝ) / (2 : ℝ) ^ N) := by
  classical
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt0 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hpow (n : ℕ) : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  -- Every older tent is affine on each cell of the current dyadic mesh.
  have haff (N n k q : ℕ) (hn : n < N) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      hat n k (((q : ℝ) + x) / (2 : ℝ) ^ N) =
        (1 - x) * hat n k ((q : ℝ) / (2 : ℝ) ^ N) +
          x * hat n k (((q : ℝ) + 1) / (2 : ℝ) ^ N) := by
    let d : ℕ := 2 ^ (N - (n + 1))
    have hd : 0 < d := by dsimp [d]; positivity
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hp : (2 : ℝ) ^ N = 2 * (2 : ℝ) ^ n * (d : ℝ) := by
      have hN : N = n + 1 + (N - (n + 1)) := by omega
      conv_lhs => rw [hN, pow_add, pow_succ]
      dsimp [d]
      push_cast
      ring
    have harg (y : ℝ) :
        2 * ((2 : ℝ) ^ n * (((q : ℝ) + y) / (2 : ℝ) ^ N) - k) - 1 =
          (((q : ℝ) + y) - ((2 * k + 1) * d : ℕ)) / (d : ℝ) := by
      rw [hp]
      push_cast
      field_simp
      ring
    push_cast at harg
    have hcell : q + 1 ≤ 2 * k * d ∨ (2 * k + 2) * d ≤ q ∨
        (2 * k * d ≤ q ∧ q + 1 ≤ (2 * k + 1) * d) ∨
        ((2 * k + 1) * d ≤ q ∧ q + 1 ≤ (2 * k + 2) * d) := by
      have he1 : (2 * k + 1) * d = 2 * k * d + d := by ring
      have he2 : (2 * k + 2) * d = 2 * k * d + 2 * d := by ring
      rw [he1, he2]
      omega
    rcases hcell with hleft | hright | hrise | hfall
    · have hz (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
          tent ((2 : ℝ) ^ n * (((q : ℝ) + y) / (2 : ℝ) ^ N) - k) = 0 := by
        have hleftR : (q : ℝ) + 1 ≤ 2 * k * d := by exact_mod_cast hleft
        have hb : (((q : ℝ) + y) - (2 * k + 1 : ℝ) * d) / d ≤ -1 :=
          (div_le_iff₀ hdR).2 (by nlinarith [hy.2])
        unfold tent
        rw [harg, abs_of_nonpos (by linarith), max_eq_left (by linarith)]
      simp only [hat]
      rw [show (q : ℝ) / 2 ^ N = ((q : ℝ) + 0) / 2 ^ N by ring,
        hz x hx, hz 0 (by norm_num), hz 1 (by norm_num)]
      ring
    · have hz (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
          tent ((2 : ℝ) ^ n * (((q : ℝ) + y) / (2 : ℝ) ^ N) - k) = 0 := by
        have hrightR : (2 * k + 2 : ℝ) * d ≤ q := by exact_mod_cast hright
        have hb : 1 ≤ (((q : ℝ) + y) - (2 * k + 1 : ℝ) * d) / d :=
          (le_div_iff₀ hdR).2 (by nlinarith [hy.1])
        unfold tent
        rw [harg, abs_of_nonneg (by linarith), max_eq_left (by linarith)]
      simp only [hat]
      rw [show (q : ℝ) / 2 ^ N = ((q : ℝ) + 0) / 2 ^ N by ring,
        hz x hx, hz 0 (by norm_num), hz 1 (by norm_num)]
      ring
    · have hlo : (2 * k : ℝ) * d ≤ q := by exact_mod_cast hrise.1
      have hhi : (q : ℝ) + 1 ≤ (2 * k + 1 : ℝ) * d := by exact_mod_cast hrise.2
      have he (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
          tent ((2 : ℝ) ^ n * (((q : ℝ) + y) / (2 : ℝ) ^ N) - k) =
            (((q : ℝ) + y) - (2 * k : ℝ) * d) / d := by
        have hlo' : -1 ≤ (((q : ℝ) + y) - (2 * k + 1 : ℝ) * d) / d :=
          (le_div_iff₀ hdR).2 (by nlinarith [hy.1])
        have hhi' : (((q : ℝ) + y) - (2 * k + 1 : ℝ) * d) / d ≤ 0 :=
          (div_le_iff₀ hdR).2 (by nlinarith [hy.2])
        unfold tent
        rw [harg, abs_of_nonpos hhi', max_eq_right (by linarith)]
        field_simp
        ring
      simp only [hat]
      rw [show (q : ℝ) / 2 ^ N = ((q : ℝ) + 0) / 2 ^ N by ring,
        he x hx, he 0 (by norm_num), he 1 (by norm_num)]
      ring
    · have hlo : (2 * k + 1 : ℝ) * d ≤ q := by exact_mod_cast hfall.1
      have hhi : (q : ℝ) + 1 ≤ (2 * k + 2 : ℝ) * d := by exact_mod_cast hfall.2
      have he (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
          tent ((2 : ℝ) ^ n * (((q : ℝ) + y) / (2 : ℝ) ^ N) - k) =
            ((2 * k + 2 : ℝ) * d - ((q : ℝ) + y)) / d := by
        have hlo' : 0 ≤ (((q : ℝ) + y) - (2 * k + 1 : ℝ) * d) / d :=
          (le_div_iff₀ hdR).2 (by nlinarith [hy.1])
        have hhi' : (((q : ℝ) + y) - (2 * k + 1 : ℝ) * d) / d ≤ 1 :=
          (div_le_iff₀ hdR).2 (by nlinarith [hy.2])
        unfold tent
        rw [harg, abs_of_nonneg hlo', max_eq_right (by linarith)]
        field_simp
        ring
      simp only [hat]
      rw [show (q : ℝ) / 2 ^ N = ((q : ℝ) + 0) / 2 ^ N by ring,
        he x hx, he 0 (by norm_num), he 1 (by norm_num)]
      ring
  have hlin (N q : ℕ) (x v : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      unitCov N (((q : ℝ) + x) / (2 : ℝ) ^ N) v =
        (1 - x) * unitCov N ((q : ℝ) / (2 : ℝ) ^ N) v +
          x * unitCov N (((q : ℝ) + 1) / (2 : ℝ) ^ N) v := by
    have hs : (∑ n ∈ Finset.range N, ∑ k ∈ Finset.range (2 ^ n),
        hat n k (((q : ℝ) + x) / 2 ^ N) * hat n k v) =
        ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range (2 ^ n),
          ((1 - x) * hat n k ((q : ℝ) / 2 ^ N) +
            x * hat n k (((q : ℝ) + 1) / 2 ^ N)) * hat n k v := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro k _
      rw [haff N n k q (Finset.mem_range.mp hn) x hx]
    unfold unitCov
    rw [hs]
    simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]
    ring
  have hsym (N : ℕ) (u v : ℝ) : unitCov N u v = unitCov N v u := by
    unfold unitCov
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro n _
      apply Finset.sum_congr rfl
      intro k _
      ring
  have hold (N q l : ℕ) : hat N l ((q : ℝ) / (2 : ℝ) ^ N) = 0 := by
    unfold hat tent
    rw [show (2 : ℝ) ^ N * ((q : ℝ) / (2 : ℝ) ^ N) = q by field_simp]
    rcases le_or_gt q l with h | h
    · have h' : (q : ℝ) ≤ l := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith), max_eq_left (by linarith), mul_zero]
    · have h' : (l : ℝ) + 1 ≤ q := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith), max_eq_left (by linarith), mul_zero]
  have hmid (N q l : ℕ) :
      hat N l (((q : ℝ) + 1 / 2) / (2 : ℝ) ^ N) =
        if l = q then amplitude N else 0 := by
    unfold hat tent
    rw [show (2 : ℝ) ^ N * (((q : ℝ) + 1 / 2) / (2 : ℝ) ^ N) =
      (q : ℝ) + 1 / 2 by field_simp]
    split_ifs with h
    · subst l
      norm_num
    · rcases lt_or_gt_of_ne (Ne.symm h) with hlt | hgt
      · have hh : (q : ℝ) + 1 ≤ l := by exact_mod_cast hlt
        rw [abs_of_nonpos (by linarith), max_eq_left (by linarith), mul_zero]
      · have hh : (l : ℝ) + 1 ≤ q := by exact_mod_cast hgt
        rw [abs_of_nonneg (by linarith), max_eq_left (by linarith), mul_zero]
  have ha2 (N : ℕ) : amplitude N ^ 2 = ((2 : ℝ) ^ N)⁻¹ / 4 := by
    unfold amplitude
    rw [inv_pow, mul_pow, ← pow_mul, Nat.mul_comm N 2, pow_mul, hsqrt]
    field_simp
    ring
  induction N generalizing j k with
  | zero =>
      have hj' : j = 0 ∨ j = 1 := by norm_num at hj; omega
      have hk' : k = 0 ∨ k = 1 := by norm_num at hk; omega
      rcases hj' with rfl | rfl <;> rcases hk' with rfl | rfl <;>
        norm_num [unitCov]
  | succ N ih =>
      have hpN : 2 ^ (N + 1) = 2 * 2 ^ N := by rw [pow_succ]; omega
      have hpR : (2 : ℝ) ^ (N + 1) = 2 * (2 : ℝ) ^ N := by rw [pow_succ]; ring
      have heven (q : ℕ) : ((2 * q : ℕ) : ℝ) / (2 : ℝ) ^ (N + 1) =
          (q : ℝ) / (2 : ℝ) ^ N := by rw [hpR]; push_cast; ring
      have hodd (q : ℕ) : ((2 * q + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (N + 1) =
          ((q : ℝ) + 1 / 2) / (2 : ℝ) ^ N := by rw [hpR]; push_cast; ring
      have hstep (u v : ℝ) : unitCov (N + 1) u v = unitCov N u v +
          ∑ l ∈ Finset.range (2 ^ N), hat N l u * hat N l v := by
        simp only [unitCov, Finset.sum_range_succ]
        ring
      have hE (q p : ℕ) (hq : q ≤ 2 ^ N) (hp : p ≤ 2 ^ N) :
          unitCov (N + 1) ((q : ℝ) / 2 ^ N) ((p : ℝ) / 2 ^ N) =
            min ((q : ℝ) / 2 ^ N) ((p : ℝ) / 2 ^ N) := by
        rw [hstep]
        simpa [hold] using ih q p hq hp
      have hME (q p : ℕ) (hq : q < 2 ^ N) (hp : p ≤ 2 ^ N) :
          unitCov (N + 1) (((q : ℝ) + 1 / 2) / 2 ^ N) ((p : ℝ) / 2 ^ N) =
            min (((q : ℝ) + 1 / 2) / 2 ^ N) ((p : ℝ) / 2 ^ N) := by
        rw [hstep]
        simp only [hold, mul_zero, Finset.sum_const_zero, add_zero]
        rw [hlin N q (1 / 2) _ (by norm_num)]
        rw [ih q p hq.le hp]
        have hq1 : q + 1 ≤ 2 ^ N := hq
        have hi := ih (q + 1) p hq1 hp
        push_cast at hi
        rw [hi]
        rcases le_or_gt p q with h | h
        · have h' : (p : ℝ) ≤ q := by exact_mod_cast h
          rw [min_eq_right (by gcongr <;> linarith),
            min_eq_right (by gcongr <;> linarith), min_eq_right (by gcongr <;> linarith)]
          ring
        · have h' : (q : ℝ) + 1 ≤ p := by exact_mod_cast h
          rw [min_eq_left (by gcongr <;> linarith),
            min_eq_left (by gcongr <;> linarith), min_eq_left (by gcongr <;> linarith)]
          ring
      have hMM (q p : ℕ) (hq : q < 2 ^ N) (hp : p < 2 ^ N) :
          unitCov (N + 1) (((q : ℝ) + 1 / 2) / 2 ^ N)
              (((p : ℝ) + 1 / 2) / 2 ^ N) =
            min (((q : ℝ) + 1 / 2) / 2 ^ N) (((p : ℝ) + 1 / 2) / 2 ^ N) := by
        rw [hstep]
        have hsum : (∑ l ∈ Finset.range (2 ^ N),
            hat N l (((q : ℝ) + 1 / 2) / 2 ^ N) *
            hat N l (((p : ℝ) + 1 / 2) / 2 ^ N)) =
              if q = p then amplitude N ^ 2 else 0 := by
          simp_rw [hmid]
          simp [Finset.mem_range.mpr hq, Finset.mem_range.mpr hp, sq,
            eq_comm, and_left_comm, and_assoc]
        rw [hsum, hlin N q (1 / 2) _ (by norm_num)]
        rw [hsym N ((q : ℝ) / 2 ^ N), hsym N (((q : ℝ) + 1) / 2 ^ N),
          hlin N p (1 / 2) _ (by norm_num), hlin N p (1 / 2) _ (by norm_num)]
        have h00 := ih p q hp.le hq.le
        have h01 := ih (p + 1) q hp hq.le
        have h10 := ih p (q + 1) hp.le hq
        have h11 := ih (p + 1) (q + 1) hp hq
        push_cast at h01 h10 h11
        rw [h00, h01, h10, h11]
        have hdmono (a b : ℝ) (hab : a ≤ b) : a / (2 : ℝ) ^ N ≤ b / (2 : ℝ) ^ N :=
          div_le_div_of_nonneg_right hab (hpow N).le
        rcases lt_trichotomy q p with h | rfl | h
        · have h' : (q : ℝ) + 1 ≤ p := by exact_mod_cast h
          rw [if_neg (ne_of_lt h),
            min_eq_right (hdmono _ _ (by linarith : (q : ℝ) ≤ p)),
            min_eq_right (hdmono _ _ (by linarith : (q : ℝ) ≤ (p : ℝ) + 1)),
            min_eq_right (hdmono _ _ h'),
            min_eq_right (hdmono _ _ (by linarith : (q : ℝ) + 1 ≤ (p : ℝ) + 1)),
            min_eq_left (hdmono _ _ (by linarith : (q : ℝ) + 1 / 2 ≤ (p : ℝ) + 1 / 2))]
          ring
        · rw [if_pos rfl, min_self, min_self, min_self,
            min_eq_right (hdmono _ _ (by linarith : (q : ℝ) ≤ (q : ℝ) + 1)),
            min_eq_left (hdmono _ _ (by linarith : (q : ℝ) ≤ (q : ℝ) + 1)), ha2]
          field_simp
          ring
        · have h' : (p : ℝ) + 1 ≤ q := by exact_mod_cast h
          rw [if_neg (ne_of_gt h),
            min_eq_left (hdmono _ _ (by linarith : (p : ℝ) ≤ q)),
            min_eq_left (hdmono _ _ h'),
            min_eq_left (hdmono _ _ (by linarith : (p : ℝ) ≤ (q : ℝ) + 1)),
            min_eq_left (hdmono _ _ (by linarith : (p : ℝ) + 1 ≤ (q : ℝ) + 1)),
            min_eq_right (hdmono _ _ (by linarith : (p : ℝ) + 1 / 2 ≤ (q : ℝ) + 1 / 2))]
          ring
      have hjpar : j = 2 * (j / 2) ∨ j = 2 * (j / 2) + 1 := by omega
      have hkpar : k = 2 * (k / 2) ∨ k = 2 * (k / 2) + 1 := by omega
      rcases hjpar with hjp | hjp <;> rcases hkpar with hkp | hkp
      · rw [hjp, hkp, heven, heven]
        exact hE _ _ (by rw [hpN] at hj; omega) (by rw [hpN] at hk; omega)
      · rw [hjp, hkp, heven, hodd, hsym, min_comm]
        exact hME _ _ (by rw [hpN] at hk; omega) (by rw [hpN] at hj; omega)
      · rw [hjp, hkp, hodd, heven]
        exact hME _ _ (by rw [hpN] at hj; omega) (by rw [hpN] at hk; omega)
      · rw [hjp, hkp, hodd, hodd]
        exact hMM _ _ (by rw [hpN] at hj; omega) (by rw [hpN] at hk; omega)

private theorem unitCov_approx (N : ℕ) (u v : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    |unitCov N u v - min u v| ≤ ((2 : ℝ) ^ N)⁻¹ := by
  classical
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ha (n : ℕ) : 0 ≤ amplitude n := by unfold amplitude; positivity
  have ha2 (n : ℕ) : amplitude n ^ 2 = (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n := by
    unfold amplitude
    rw [inv_pow, mul_pow, ← pow_mul, Nat.mul_comm n 2, pow_mul, hsqrt]
    simp only [mul_inv_rev, inv_pow, one_div]
    ring
  have hh (n k : ℕ) (x : ℝ) : |hat n k x| ≤ amplitude n := by
    have hn : 0 ≤ tent ((2 : ℝ) ^ n * x - k) := le_max_left _ _
    have ht : tent ((2 : ℝ) ^ n * x - k) ≤ 1 := by
      unfold tent
      exact max_le (by norm_num) (by linarith [abs_nonneg (2 * ((2 : ℝ) ^ n * x - k) - 1)])
    simpa [hat, abs_mul, abs_of_nonneg (ha n), abs_of_nonneg hn] using
      mul_le_mul_of_nonneg_left ht (ha n)
  have hlevel (n : ℕ) (x y : ℝ) :
      |∑ k ∈ Finset.range (2 ^ n), hat n k x * hat n k y| ≤ amplitude n ^ 2 := by
    let ω : Sample := fun i => if 2 ^ n ≤ i.2 then hat n (i.2 - 2 ^ n) x else 0
    have hω : ∀ k ∈ Finset.range (2 ^ n), |coord (0, 2 ^ n + k) ω| ≤ amplitude n := by
      intro k _
      simpa [ω, coord] using hh n k x
    simpa [level, coord, ω, sq] using level_bound 0 n (amplitude n) (ha n) ω hω y
  have hs : Summable (fun l : ℕ => (1 / 2 : ℝ) ^ l) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have ht : (∑' l : ℕ, (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ (N + l)) =
      ((2 : ℝ) ^ N)⁻¹ / 2 := by
    simp_rw [pow_add, ← mul_assoc]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
    norm_num only [one_div]
    norm_num
    simp only [one_div, inv_pow]
    ring
  have htail (L : ℕ) (x y : ℝ) :
      |unitCov (N + L) x y - unitCov N x y| ≤ ((2 : ℝ) ^ N)⁻¹ := by
    have heq : unitCov (N + L) x y - unitCov N x y =
        ∑ l ∈ Finset.range L, ∑ k ∈ Finset.range (2 ^ (N + l)),
          hat (N + l) k x * hat (N + l) k y := by
      simp only [unitCov, Finset.sum_range_add]
      ring
    rw [heq]
    calc
      _ ≤ ∑ l ∈ Finset.range L,
          |∑ k ∈ Finset.range (2 ^ (N + l)), hat (N + l) k x * hat (N + l) k y| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l ∈ Finset.range L, amplitude (N + l) ^ 2 :=
        Finset.sum_le_sum fun l _ => hlevel (N + l) x y
      _ = ∑ l ∈ Finset.range L, (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ (N + l) := by
        simp_rw [ha2]
      _ ≤ ∑' l : ℕ, (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ (N + l) := by
        have hs' : Summable (fun l : ℕ => (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ (N + l)) := by
          simpa only [pow_add, ← mul_assoc] using
            hs.mul_left ((1 / 4 : ℝ) * (1 / 2 : ℝ) ^ N)
        exact hs'.sum_le_tsum _ (fun _ _ => by positivity)
      _ ≤ ((2 : ℝ) ^ N)⁻¹ := by
        rw [ht]
        have : 0 ≤ ((2 : ℝ) ^ N)⁻¹ := by positivity
        linarith
  let grid : ℕ → ℝ → ℝ := fun L x =>
    (⌊(2 : ℝ) ^ (N + L) * x⌋₊ : ℝ) / (2 : ℝ) ^ (N + L)
  have hden (L : ℕ) : (0 : ℝ) < (2 : ℝ) ^ (N + L) := by positivity
  have hglim (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      Tendsto (fun L => grid L x) atTop (𝓝 x) := by
    have hp : Tendsto (fun L : ℕ => ((2 : ℝ) ^ (N + L))⁻¹) atTop (𝓝 0) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
        (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).const_mul ((2 : ℝ) ^ N)⁻¹
      simpa [pow_add, mul_inv_rev, inv_pow, mul_comm] using h
    have hlo : Tendsto (fun L : ℕ => x - ((2 : ℝ) ^ (N + L))⁻¹) atTop (𝓝 x) := by
      simpa using (tendsto_const_nhds.sub hp)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
    · intro L
      have hf := Nat.lt_floor_add_one ((2 : ℝ) ^ (N + L) * x)
      dsimp [grid]
      apply (le_div_iff₀ (hden L)).2
      calc
        (x - ((2 : ℝ) ^ (N + L))⁻¹) * (2 : ℝ) ^ (N + L) =
            (2 : ℝ) ^ (N + L) * x - 1 := by field_simp <;> ring
        _ ≤ ⌊(2 : ℝ) ^ (N + L) * x⌋₊ := by linarith
    · intro L
      dsimp [grid]
      apply (div_le_iff₀ (hden L)).2
      simpa only [mul_comm] using Nat.floor_le (mul_nonneg (hden L).le hx.1)
  have hgrid (L : ℕ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      ⌊(2 : ℝ) ^ (N + L) * x⌋₊ ≤ 2 ^ (N + L) := by
    apply Nat.floor_le_of_le
    exact_mod_cast (mul_le_of_le_one_right (hden L).le hx.2)
  have heq (L : ℕ) : unitCov (N + L) (grid L u) (grid L v) =
      min (grid L u) (grid L v) :=
    unitCov_dyadic _ _ _ (hgrid L u hu) (hgrid L v hv)
  have hc : Continuous (fun p : ℝ × ℝ => unitCov N p.1 p.2) := by
    unfold unitCov hat tent
    fun_prop
  have hlim := ((hglim u hu).min (hglim v hv)).sub
    (hc.continuousAt.tendsto.comp ((hglim u hu).prodMk_nhds (hglim v hv)))
  have hlim' : Tendsto (fun L =>
      |unitCov (N + L) (grid L u) (grid L v) - unitCov N (grid L u) (grid L v)|)
      atTop (𝓝 |min u v - unitCov N u v|) := by
    simpa only [heq, Function.comp_def] using hlim.abs
  have hbound := le_of_tendsto hlim' (Eventually.of_forall fun L =>
    htail L (grid L u) (grid L v))
  simpa only [abs_sub_comm] using hbound

private theorem fullCov_tendsto (s t : ℝ≥0) :
    Tendsto (fun N => fullCov N s t) atTop
      (𝓝 (min (s : ℝ) (t : ℝ))) := by
  classical
  have hc (x : ℝ) : clip x ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_left _ _)
  have hcmono : Monotone clip := by
    intro x y h
    exact max_le_max le_rfl (min_le_min le_rfl h)
  have hp : Tendsto (fun N : ℕ => ((2 : ℝ) ^ N)⁻¹) atTop (𝓝 0) := by
    simpa [inv_pow] using tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (by norm_num : ‖(2 : ℝ)⁻¹‖ < 1)
  have hunit (x y : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
      Tendsto (fun N => unitCov N x y) atTop (𝓝 (min x y)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun N => by
      simpa only [Real.norm_eq_abs] using unitCov_approx N x y hx hy) hp
  have hlim := tendsto_finsetSum (Finset.range (⌊((max s t : ℝ≥0) : ℝ)⌋₊ + 1))
    (fun m _ => hunit (clip ((s : ℝ) - m)) (clip ((t : ℝ) - m)) (hc _) (hc _))
  have hsum (x : ℝ≥0) (M : ℕ) (hM : ⌊(x : ℝ)⌋₊ + 1 ≤ M) :
      (∑ m ∈ Finset.range M, clip ((x : ℝ) - m)) = x := by
    have hf : (⌊(x : ℝ)⌋₊ : ℝ) ≤ x := Nat.floor_le x.2
    have hf' := Nat.lt_floor_add_one (x : ℝ)
    have hshort : (∑ m ∈ Finset.range (⌊(x : ℝ)⌋₊ + 1), clip ((x : ℝ) - m)) = x := by
      rw [Finset.sum_range_succ]
      have hones : (∑ m ∈ Finset.range ⌊(x : ℝ)⌋₊, clip ((x : ℝ) - m)) =
          (⌊(x : ℝ)⌋₊ : ℝ) := by
        calc
          _ = ∑ _m ∈ Finset.range ⌊(x : ℝ)⌋₊, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro m hm
            have hm' : (m : ℝ) + 1 ≤ ⌊(x : ℝ)⌋₊ := by
              exact_mod_cast Finset.mem_range.mp hm
            unfold clip
            rw [min_eq_left (by linarith), max_eq_right (by norm_num)]
          _ = _ := by simp
      rw [hones]
      have hlast : clip ((x : ℝ) - ⌊(x : ℝ)⌋₊) = (x : ℝ) - ⌊(x : ℝ)⌋₊ := by
        unfold clip
        rw [min_eq_right (by linarith), max_eq_right (by linarith)]
      rw [hlast]
      ring
    calc
      _ = ∑ m ∈ Finset.range (⌊(x : ℝ)⌋₊ + 1), clip ((x : ℝ) - m) := by
        symm
        apply Finset.sum_subset (Finset.range_mono hM)
        intro m _ hm
        have hm' : ⌊(x : ℝ)⌋₊ + 1 ≤ m := by simpa only [Finset.mem_range, not_lt] using hm
        have hmR : (⌊(x : ℝ)⌋₊ : ℝ) + 1 ≤ m := by exact_mod_cast hm'
        unfold clip
        rw [min_eq_right (by linarith), max_eq_left (by linarith)]
      _ = x := hshort
  have hmin (m : ℕ) : min (clip ((s : ℝ) - m)) (clip ((t : ℝ) - m)) =
      clip (((min s t : ℝ≥0) : ℝ) - m) := by
    rcases le_total s t with hst | hts
    · have hstR : (s : ℝ) ≤ t := hst
      rw [min_eq_left hst, min_eq_left (hcmono (sub_le_sub_right hstR _))]
    · have htsR : (t : ℝ) ≤ s := hts
      rw [min_eq_right hts, min_eq_right (hcmono (sub_le_sub_right htsR _))]
  have hM : ⌊((min s t : ℝ≥0) : ℝ)⌋₊ + 1 ≤
      ⌊((max s t : ℝ≥0) : ℝ)⌋₊ + 1 := by
    gcongr
    exact min_le_max
  have heq : (∑ m ∈ Finset.range (⌊((max s t : ℝ≥0) : ℝ)⌋₊ + 1),
      min (clip ((s : ℝ) - m)) (clip ((t : ℝ) - m))) = min (s : ℝ) (t : ℝ) := by
    simp_rw [hmin]
    simpa only [NNReal.coe_min] using hsum (min s t) _ hM
  simpa only [fullCov, heq] using hlim

private theorem partial_finite_characteristic (N : ℕ)
    (I : Finset ℝ≥0) (a : I → ℝ) :
    (∫ ω, Complex.exp
      (((∑ i : I, a i * Bpartial N i.1 ω : ℝ) : ℂ) * Complex.I) ∂law) =
      Complex.exp (-((∑ i : I, ∑ j : I,
        a i * a j * fullCov N i.1 j.1 : ℝ) : ℂ) / 2) := by
  classical
  -- Finitely supported coefficient vectors keep repeated Gaussian coordinates
  -- combined before independence is used.
  let ev (ω : Sample) : ((ℕ × ℕ) →₀ ℝ) →ₗ[ℝ] ℝ :=
    Finsupp.linearCombination ℝ (fun p => coord p ω)
  let dot (f g : ((ℕ × ℕ) →₀ ℝ)) : ℝ := (Finsupp.linearCombination ℝ g) f
  have dev (ω : Sample) (f : ((ℕ × ℕ) →₀ ℝ)) : ev ω f =
      ∑ p ∈ f.support, f p * coord p ω := by
    change f.sum (fun p c => c • coord p ω) = _
    rfl
  have ddot (f g : ((ℕ × ℕ) →₀ ℝ)) : dot f g = ∑ p ∈ f.support, f p * g p := by
    simp [dot, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul]
  have dadd₁ (f g h : ((ℕ × ℕ) →₀ ℝ)) : dot (f + g) h = dot f h + dot g h := by
    exact map_add (Finsupp.linearCombination ℝ h) f g
  have dadd₂ (f g h : ((ℕ × ℕ) →₀ ℝ)) : dot f (g + h) = dot f g + dot f h := by
    simp [ddot, Finsupp.add_apply, mul_add, Finset.sum_add_distrib]
  have dsum₁ {α : Type} (s : Finset α) (f : α → ((ℕ × ℕ) →₀ ℝ)) (g : ((ℕ × ℕ) →₀ ℝ)) :
      dot (∑ i ∈ s, f i) g = ∑ i ∈ s, dot (f i) g := by
    exact map_sum (Finsupp.linearCombination ℝ g) f s
  have dsum₂ {α : Type} (s : Finset α) (f : ((ℕ × ℕ) →₀ ℝ)) (g : α → ((ℕ × ℕ) →₀ ℝ)) :
      dot f (∑ i ∈ s, g i) = ∑ i ∈ s, dot f (g i) := by
    simp only [ddot, Finset.sum_apply', Finset.mul_sum]
    exact Finset.sum_comm
  have dsmul₁ (c : ℝ) (f g : ((ℕ × ℕ) →₀ ℝ)) : dot (c • f) g = c * dot f g := by
    exact map_smul (Finsupp.linearCombination ℝ g) c f
  have dsmul₂ (c : ℝ) (f g : ((ℕ × ℕ) →₀ ℝ)) : dot f (c • g) = c * dot f g := by
    simp [ddot, Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm, mul_assoc]
  have dsingle (p : ℕ × ℕ) (c : ℝ) (g : ((ℕ × ℕ) →₀ ℝ)) :
      dot (Finsupp.single p c) g = c * g p := by
    simp [dot, Finsupp.linearCombination_single, smul_eq_mul]
  let bu (m : ℕ) (u : ℝ) : ((ℕ × ℕ) →₀ ℝ) := Finsupp.single (m, 0) u +
    ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range (2 ^ n),
      Finsupp.single (m, 2 ^ n + k) (hat n k u)
  have bz (p m : ℕ) (u : ℝ) : bu p u (m, 0) = if p = m then u else 0 := by
    dsimp [bu]
    simp only [Finsupp.add_apply, Finset.sum_apply']
    have hz (n : ℕ) : (∑ k ∈ Finset.range (2 ^ n),
        (Finsupp.single (p, 2 ^ n + k) (hat n k u) : ((ℕ × ℕ) →₀ ℝ)) (m, 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      have hn : 2 ^ n + k ≠ 0 := by positivity
      simp [Finsupp.single_apply, Prod.mk.injEq, hn]
    simp [hz, Finsupp.single_apply, Prod.mk.injEq]
  have bl (p m n k : ℕ) (hn : n < N) (hk : k < 2 ^ n) (u : ℝ) :
      bu p u (m, 2 ^ n + k) = if p = m then hat n k u else 0 := by
    have hn0 : 2 ^ n + k ≠ 0 := by positivity
    dsimp [bu]
    simp only [Finsupp.add_apply, Finset.sum_apply']
    have hbase : (Finsupp.single (p, 0) u : ((ℕ × ℕ) →₀ ℝ)) (m, 2 ^ n + k) = 0 := by
      simp [Finsupp.single_apply, Prod.mk.injEq, hn0, Ne.symm hn0]
    rw [hbase, zero_add]
    by_cases hpm : p = m
    · subst p
      rw [Finset.sum_eq_single n]
      · rw [Finset.sum_eq_single k]
        · simp
        · intro l hl hlk
          have hneq : 2 ^ n + l ≠ 2 ^ n + k := by omega
          simp [Finsupp.single_apply, hneq, Prod.mk.injEq, hlk]
        · exact fun h => (h (Finset.mem_range.mpr hk)).elim
      · intro r hr hrn
        apply Finset.sum_eq_zero
        intro l hl
        have hneq : 2 ^ r + l ≠ 2 ^ n + k := by
          intro he
          exact hrn (coordinate_index_injective r n l k (Finset.mem_range.mp hl) hk he).1
        simp [Finsupp.single_apply, Prod.mk.injEq, hneq]
      · exact fun h => (h (Finset.mem_range.mpr hn)).elim
    · rw [if_neg hpm]
      apply Finset.sum_eq_zero
      intro r _
      apply Finset.sum_eq_zero
      intro l _
      simp [Finsupp.single_apply, Prod.mk.injEq, hpm]
  have dbu (m p : ℕ) (u v : ℝ) : dot (bu m u) (bu p v) =
      if m = p then unitCov N u v else 0 := by
    change dot (Finsupp.single (m, 0) u +
      ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range (2 ^ n),
        Finsupp.single (m, 2 ^ n + k) (hat n k u)) (bu p v) = _
    rw [dadd₁, dsingle, bz, dsum₁]
    have hs : (∑ n ∈ Finset.range N,
        dot (∑ k ∈ Finset.range (2 ^ n),
          Finsupp.single (m, 2 ^ n + k) (hat n k u)) (bu p v)) =
        ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range (2 ^ n),
          hat n k u * (if p = m then hat n k v else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [dsum₁]
      apply Finset.sum_congr rfl
      intro k hk
      rw [dsingle, bl p m n k (Finset.mem_range.mp hn) (Finset.mem_range.mp hk)]
    rw [hs]
    by_cases h : m = p
    · subst p
      simp [unitCov]
    · simp [h, Ne.symm h]
  let M : ℕ := ∑ i : I, (⌊(i.1 : ℝ)⌋₊ + 1)
  have hiM (i : I) : ⌊(i.1 : ℝ)⌋₊ + 1 ≤ M := by
    exact Finset.single_le_sum (f := fun j : I => ⌊(j.1 : ℝ)⌋₊ + 1)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  let b (i : I) : ((ℕ × ℕ) →₀ ℝ) := ∑ m ∈ Finset.range M, bu m (clip ((i.1 : ℝ) - m))
  have evbu (ω : Sample) (m : ℕ) (u : ℝ) : ev ω (bu m u) = unitPartial m N u ω := by
    dsimp [ev, bu]
    simp only [map_add, map_sum, Finsupp.linearCombination_single,
      smul_eq_mul, unitPartial, level]
    simp [mul_comm]
  have evb (ω : Sample) (i : I) : ev ω (b i) = Bpartial N i.1 ω := by
    dsimp [b]
    rw [map_sum]
    simp only [evbu]
    symm
    unfold Bpartial
    apply Finset.sum_subset (Finset.range_mono (hiM i))
    intro m _ hm
    have hm' : ⌊(i.1 : ℝ)⌋₊ + 1 ≤ m := by simpa only [Finset.mem_range, not_lt] using hm
    have hmR : (⌊(i.1 : ℝ)⌋₊ : ℝ) + 1 ≤ m := by exact_mod_cast hm'
    have hfl := Nat.lt_floor_add_one (i.1 : ℝ)
    have hc : clip ((i.1 : ℝ) - m) = 0 := by
      unfold clip
      rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    simp [hc, unitPartial_zero]
  have db (i j : I) : dot (b i) (b j) = fullCov N i.1 j.1 := by
    dsimp [b]
    rw [dsum₁]
    have heq : (∑ m ∈ Finset.range M,
        dot (bu m (clip ((i.1 : ℝ) - m)))
          (∑ p ∈ Finset.range M, bu p (clip ((j.1 : ℝ) - p)))) =
        ∑ m ∈ Finset.range M,
          unitCov N (clip ((i.1 : ℝ) - m)) (clip ((j.1 : ℝ) - m)) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [dsum₂]
      simp_rw [dbu]
      simp [Finset.mem_range.mp hm]
    rw [heq]
    unfold fullCov
    have hmax : ⌊((max i.1 j.1 : ℝ≥0) : ℝ)⌋₊ + 1 ≤ M := by
      rcases le_total i.1 j.1 with h | h
      · simpa only [max_eq_right h] using hiM j
      · simpa only [max_eq_left h] using hiM i
    symm
    apply Finset.sum_subset (Finset.range_mono hmax)
    intro m _ hm
    have hm' : ⌊((max i.1 j.1 : ℝ≥0) : ℝ)⌋₊ + 1 ≤ m := by
      simpa only [Finset.mem_range, not_lt] using hm
    have hmR : (⌊((max i.1 j.1 : ℝ≥0) : ℝ)⌋₊ : ℝ) + 1 ≤ m := by exact_mod_cast hm'
    have hf := Nat.lt_floor_add_one ((max i.1 j.1 : ℝ≥0) : ℝ)
    have hci : clip ((i.1 : ℝ) - m) = 0 := by
      have hle : (i.1 : ℝ) ≤ ((max i.1 j.1 : ℝ≥0) : ℝ) := le_max_left _ _
      unfold clip
      rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    simp [hci, unitCov, hat_zero]
  let d : ((ℕ × ℕ) →₀ ℝ) := ∑ i : I, a i • b i
  have evd (ω : Sample) : ev ω d = ∑ i : I, a i * Bpartial N i.1 ω := by
    dsimp [d]
    simp only [map_sum, map_smul, smul_eq_mul, evb]
  have dnorm : (∑ p ∈ d.support, d p ^ 2) =
      ∑ i : I, ∑ j : I, a i * a j * fullCov N i.1 j.1 := by
    have heq : (∑ p ∈ d.support, d p ^ 2) = dot d d := by simp [ddot, sq]
    rw [heq]
    dsimp [d]
    rw [dsum₁]
    apply Finset.sum_congr rfl
    intro i _
    rw [dsmul₁, dsum₂, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [dsmul₂, db]
    ring
  have hm (p : ℕ × ℕ) : AEMeasurable (fun ω => d p * coord p ω) law := by
    exact (measurable_coord p).aemeasurable.const_mul _
  have hind : iIndepFun (fun p ω => d p * coord p ω) law :=
    iIndepFun_coord.comp (fun p x => d p * x) (fun _ => by fun_prop)
  have hchar := congrFun
    ((hind.restrict d.support).charFun_map_finsetSum_eq_prod (fun p _ => hm p)) (1 : ℝ)
  have hscalar (p : ℕ × ℕ) :
      charFun (law.map (fun ω => d p * coord p ω)) (1 : ℝ) =
        Complex.exp (-((d p ^ 2 : ℝ) : ℂ) / 2) := by
    rw [charFun_apply_real, integral_map (hm p) (by fun_prop)]
    have he : (∫ ω, Complex.exp (((d p * coord p ω : ℝ) : ℂ) * Complex.I) ∂law) =
        charFun (gaussianReal 0 1) (d p) := by
      rw [charFun_apply_real, ← (hasLaw_coord p).map_eq,
        integral_map (hasLaw_coord p).aemeasurable (by fun_prop)]
      congr 1
      ext ω
      simp
    simp only [Complex.ofReal_one, one_mul]
    rw [he, charFun_gaussianReal]
    congr 1
    push_cast
    ring
  have hleft : charFun (law.map (∑ p ∈ d.support, fun ω => d p * coord p ω)) (1 : ℝ) =
      ∫ ω, Complex.exp (((ev ω d : ℝ) : ℂ) * Complex.I) ∂law := by
    rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
    apply integral_congr_ae
    exact ae_of_all _ fun ω => by simp [dev, Finset.sum_apply]
  have hright : (∏ p ∈ d.support,
      charFun (law.map (fun ω => d p * coord p ω)) (1 : ℝ)) =
      Complex.exp (-((∑ p ∈ d.support, d p ^ 2 : ℝ) : ℂ) / 2) := by
    simp_rw [hscalar]
    rw [← Complex.exp_sum]
    congr 1
    simp only [Complex.ofReal_sum, Complex.ofReal_pow]
    rw [← Finset.sum_div, Finset.sum_neg_distrib]
  simp only [Finset.prod_apply] at hchar
  rw [hleft, hright, dnorm] at hchar
  simpa only [evd] using hchar

private theorem finite_characteristic (I : Finset ℝ≥0) (a : I → ℝ) :
    (∫ ω, Complex.exp
      (((∑ i : I, a i * B i.1 ω : ℝ) : ℂ) * Complex.I) ∂law) =
      Complex.exp (-((∑ i : I, ∑ j : I,
        a i * a j * min (i.1 : ℝ) (j.1 : ℝ) : ℝ) : ℂ) / 2) := by
  classical
  have hm (N : ℕ) : Measurable (fun ω => Complex.exp
      (((∑ i : I, a i * Bpartial N i.1 ω : ℝ) : ℂ) * Complex.I)) := by
    have hcoord (i : I) := measurable_Bpartial N i.1
    fun_prop
  have hn (N : ℕ) (ω : Sample) : ‖Complex.exp
      (((∑ i : I, a i * Bpartial N i.1 ω : ℝ) : ℂ) * Complex.I)‖ ≤ (1 : ℝ) := by
    simp [Complex.norm_exp]
  have hl : ∀ᵐ ω ∂law, Tendsto (fun N => Complex.exp
      (((∑ i : I, a i * Bpartial N i.1 ω : ℝ) : ℂ) * Complex.I)) atTop
        (𝓝 (Complex.exp (((∑ i : I, a i * B i.1 ω : ℝ) : ℂ) * Complex.I))) := by
    filter_upwards [good_ae] with ω hω
    have hsum : Tendsto (fun N => ∑ i : I, a i * Bpartial N i.1 ω)
        atTop (𝓝 (∑ i : I, a i * B i.1 ω)) :=
      tendsto_finsetSum Finset.univ fun i _ =>
        (Bpartial_tendsto_of_good ω hω i.1).const_mul _
    exact Complex.continuous_exp.continuousAt.tendsto.comp
      (((Complex.continuous_ofReal.continuousAt.tendsto.comp hsum).mul_const Complex.I))
  have hleft := tendsto_integral_of_dominated_convergence (fun _ : Sample => (1 : ℝ))
    (fun N => (hm N).aestronglyMeasurable) (integrable_const 1)
    (fun N => ae_of_all _ (hn N)) hl
  have hquad : Tendsto (fun N => ∑ i : I, ∑ j : I,
      a i * a j * fullCov N i.1 j.1) atTop
      (𝓝 (∑ i : I, ∑ j : I, a i * a j * min (i.1 : ℝ) (j.1 : ℝ))) :=
    tendsto_finsetSum Finset.univ fun i _ =>
      tendsto_finsetSum Finset.univ fun j _ =>
        (fullCov_tendsto i.1 j.1).const_mul _
  have hright := Complex.continuous_exp.continuousAt.tendsto.comp
    ((Complex.continuous_ofReal.continuousAt.tendsto.comp hquad).neg.div_const (2 : ℂ))
  apply tendsto_nhds_unique hleft
  simpa only [partial_finite_characteristic, Function.comp_def] using hright

-- PUBLIC final interfaces. Each is unconditional in Sample/law/B.
theorem B_zero (ω : Sample) : B 0 ω = 0 := by
  simp [B, clip, unit_zero]

theorem B_continuous_ae : ∀ᵐ ω ∂law, Continuous (fun t : ℝ≥0 => B t ω) := by
  filter_upwards [good_ae] with ω hω
  exact continuous_B_of_good ω hω

theorem B_aemeasurable (t : ℝ≥0) : AEMeasurable (B t) law := by
  apply aemeasurable_of_tendsto_metrizable_ae'
    (fun N => (measurable_Bpartial N t).aemeasurable)
  filter_upwards [good_ae] with ω hω
  exact Bpartial_tendsto_of_good ω hω t

theorem B_hasLaw_finite (I : Finset ℝ≥0) :
    HasLaw (fun ω => I.restrict (B · ω))
      (ProbabilityTheory.BrownianReal.projectiveFamily I) law := by
  classical
  let e := MeasurableEquiv.toLp 2 (I → ℝ)
  have hF : AEMeasurable (fun ω => I.restrict (B · ω)) law :=
    AEMeasurable.of_eval fun i => B_aemeasurable i.1
  have heF : AEMeasurable (fun ω => e (I.restrict (B · ω))) law :=
    e.measurable.comp_aemeasurable hF
  have hmap : law.map (fun ω => e (I.restrict (B · ω))) =
      multivariateGaussian 0 (ProbabilityTheory.BrownianReal.covMatrix I) := by
    apply Measure.ext_of_charFun
    funext x
    rw [charFun_apply, integral_map heF (by fun_prop)]
    rw [charFun_multivariateGaussian
      (ProbabilityTheory.BrownianReal.posSemidef_covMatrix I)]
    have h := finite_characteristic I (fun i => x i)
    convert h using 1
    · apply integral_congr_ae
      exact ae_of_all _ fun ω => by
        congr 1 <;> simp [e, MeasurableEquiv.coe_toLp, PiLp.inner_apply,
          RCLike.inner_apply, Finset.restrict_def, mul_comm]
    · congr 1
      simp [ProbabilityTheory.BrownianReal.covMatrix, dotProduct,
        Matrix.mulVec, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm, neg_div]
  refine ⟨hF, ?_⟩
  apply e.map_measurableEquiv_injective
  rw [AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable hF]
  change law.map (fun ω => e (I.restrict (B · ω))) =
    (ProbabilityTheory.BrownianReal.projectiveFamily I).map e
  rw [hmap]
  exact (ProbabilityTheory.BrownianReal.measurePreserving_toLp_projectiveFamily I).map_eq.symm

theorem isBrownianReal : IsBrownianReal B law where
  toIsPreBrownianReal := ⟨B_hasLaw_finite⟩
  cont := B_continuous_ae

theorem B_hasLaw_eval (t : ℝ≥0) : HasLaw (B t) (gaussianReal 0 t) law :=
  isBrownianReal.toIsPreBrownianReal.hasLaw_eval t

theorem B_integral (t : ℝ≥0) : (∫ ω, B t ω ∂law) = 0 :=
  isBrownianReal.toIsPreBrownianReal.integral_eval t

theorem B_covariance (s t : ℝ≥0) :
    cov[B s, B t; law] = min (s : ℝ) (t : ℝ) := by
  simpa only [NNReal.coe_min] using isBrownianReal.toIsPreBrownianReal.covariance_eval s t

theorem B_hasLaw_sub (s t : ℝ≥0) :
    HasLaw (B s - B t) (gaussianReal 0 (nndist s.1 t.1)) law :=
  isBrownianReal.toIsPreBrownianReal.hasLaw_sub s t

end Shao.OQ4.CanonicalBrownian
