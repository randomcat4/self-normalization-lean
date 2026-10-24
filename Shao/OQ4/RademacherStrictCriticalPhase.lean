import Shao.OQ4.RademacherGeneralStrictS4
import Shao.OQ4.RademacherCriticalPhase
import Shao.OQ4.RademacherS5Assembly
import Shao.OQ4.RademacherStrictCube

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
universe uB

namespace Shao.OQ4.RademacherStrictCriticalPhase

def delta (c : ℝ) (n : ℕ) : ℝ :=
  RademacherGeneralStrictS4.delta (RademacherCriticalPhase.height c n)

def exponent (c : ℝ) (n : ℕ) : ℝ :=
  RademacherCriticalPhase.q c * delta c n

def factor (c : ℝ) (n : ℕ) : ℝ := Real.exp (exponent c n)

-- The denominator is the literal c * n^(-1/6) Brownian probability.
def Q {ΩB : Type uB} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (c : ℝ) (n : ℕ) : ℝ :=
  RademacherStrictCube.strictP n (RademacherCriticalPhase.height c n) /
    Shao.Probability.BrownianSup.probability B P hB
      (RademacherS5Assembly.x c n)

-- The upper endpoint differs materially from the old weak phaseIndex.
def phaseIndex (c d : ℝ) (k : ℕ) : ℕ :=
  letI : DecidableEq ℝ := Classical.decEq ℝ
  if d = 0 then RademacherCriticalPhase.downIndex c k
  else if d = 1 then RademacherCriticalPhase.upIndex c k + 1
  else RademacherCriticalPhase.nearestIndex c (1 - d) k

-- Frozen private mathematical helper.
-- This is the one genuinely new root-perturbation estimate for route one.
private theorem above_height_error {c : ℝ} (hc : 0 < c)
    {k : ℕ} (hk : 1 ≤ k) :
    0 < RademacherCriticalPhase.height c
      (RademacherCriticalPhase.upIndex c k + 1) - (k : ℝ) ∧
    RademacherCriticalPhase.height c
      (RademacherCriticalPhase.upIndex c k + 1) - (k : ℝ) <
      2 * c ^ 3 / (k : ℝ) ^ 2 := by
  let y := RademacherCriticalPhase.height c (RademacherCriticalPhase.upIndex c k + 1)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkp : (0 : ℝ) < k := by linarith
  have hy : 0 ≤ y := (RademacherCriticalPhase.finite_phase hc _).1
  have hc3 : 0 < c ^ 3 := pow_pos hc _
  have hy3 : y ^ 3 = c ^ 3 * ((RademacherCriticalPhase.upIndex c k + 1 : ℕ) : ℝ) :=
    (RademacherCriticalPhase.positive_time hc (n := RademacherCriticalPhase.upIndex c k + 1)
      (by omega)).2.2.1
  have ht3 : c ^ 3 * RademacherCriticalPhase.target c 0 k = (k : ℝ) ^ 3 := by
    dsimp [RademacherCriticalPhase.target]
    field_simp [hc.ne'] <;> ring
  have hr := (RademacherCriticalPhase.up_rounding hc).2 k
  have hr1 : 0 < ((RademacherCriticalPhase.upIndex c k + 1 : ℕ) : ℝ) -
      RademacherCriticalPhase.target c 0 k := by push_cast; linarith
  have hr2 : ((RademacherCriticalPhase.upIndex c k + 1 : ℕ) : ℝ) -
      RademacherCriticalPhase.target c 0 k < 2 := by push_cast; linarith
  have hfac : (y - (k : ℝ)) * (y ^ 2 + y * (k : ℝ) + (k : ℝ) ^ 2) =
      c ^ 3 * (((RademacherCriticalPhase.upIndex c k + 1 : ℕ) : ℝ) -
        RademacherCriticalPhase.target c 0 k) := by nlinarith [hy3, ht3]
  have hyk : (k : ℝ) < y := by
    by_contra h
    have hle : y ^ 3 ≤ (k : ℝ) ^ 3 := by gcongr; exact le_of_not_gt h
    have hp := mul_pos hc3 hr1
    nlinarith [hy3, ht3]
  have hQ : (k : ℝ) ^ 2 ≤ y ^ 2 + y * (k : ℝ) + (k : ℝ) ^ 2 := by
    nlinarith [sq_nonneg y, mul_nonneg hy hkp.le]
  refine ⟨sub_pos.mpr hyk, ?_⟩
  apply (lt_div_iff₀ (pow_pos hkp 2)).mpr
  have hp := mul_le_mul_of_nonneg_left hQ (sub_pos.mpr hyk).le
  have hu := mul_lt_mul_of_pos_left hr2 hc3
  nlinarith [hfac]

-- Public head 1: actual self-normalized event, all n with n=0 separate.
theorem canonical_probability {c : ℝ} (hc : 0 < c) (n : ℕ) :
    (RademacherS5Assembly.pathLaw n).real
      (RademacherStrictCube.strictSelfNormalizedEvent n
        (RademacherS5Assembly.x c n)) =
      RademacherStrictCube.strictP n (RademacherCriticalPhase.height c n) := by
  by_cases hn : n = 0
  · subst n
    rw [(RademacherStrictCube.zero_time (RademacherCriticalPhase.height c 0) (RademacherS5Assembly.x c 0)).2.2.2,
      (RademacherStrictCube.zero_time (RademacherCriticalPhase.height c 0) (RademacherS5Assembly.x c 0)).2.1]
  have hn1 : 1 ≤ n := by omega
  have hx : RademacherS5Assembly.x c n * Real.sqrt (n : ℝ) =
      RademacherCriticalPhase.height c n :=
    (RademacherS5Assembly.positive_time hc hn1).2.2.2.2.2.2.2.2.2.2.2
  change ((RademacherS5Assembly.pathLaw n)
    (RademacherStrictCube.strictSelfNormalizedEvent n (RademacherS5Assembly.x c n))).toReal = _
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [(RademacherStrictCube.actual_path_support n).2.2] with v hv
  apply propext
  change (∀ r : ℕ, 1 ≤ r → r ≤ n → |Shao.prefixSum v r| <
    RademacherS5Assembly.x c n * RademacherS5Assembly.V v) ↔ _
  rw [hv.2.2.2, hx]
  rfl

-- Public head 2: strict range; integers give zero, never the old weak value 1.
theorem phase_bounds {c : ℝ} (hc : 0 < c) (n : ℕ) :
    0 ≤ delta c n ∧ delta c n < 1 ∧
    0 < RademacherCriticalPhase.q c ∧
    0 ≤ exponent c n ∧ exponent c n < RademacherCriticalPhase.q c ∧
    1 ≤ factor c n ∧ factor c n < Real.exp (RademacherCriticalPhase.q c) ∧
    (∀ z : ℤ, RademacherCriticalPhase.height c n = (z : ℝ) → delta c n = 0) := by
  have hh := (RademacherCriticalPhase.finite_phase hc n).1
  have hq : 0 < RademacherCriticalPhase.q c := by
    dsimp [RademacherCriticalPhase.q]
    positivity
  have hd0 : 0 ≤ delta c n := by
    dsimp [delta, RademacherGeneralStrictS4.delta]
    exact sub_nonneg.mpr (Nat.le_ceil _)
  have hd1 : delta c n < 1 := by
    dsimp [delta, RademacherGeneralStrictS4.delta]
    linarith [Nat.ceil_lt_add_one hh]
  have he0 : 0 ≤ exponent c n := mul_nonneg hq.le hd0
  have he1 : exponent c n < RademacherCriticalPhase.q c := by
    dsimp [exponent]
    nlinarith [mul_lt_mul_of_pos_left hd1 hq]
  refine ⟨hd0, hd1, hq, he0, he1, ?_, ?_, ?_⟩
  · simpa only [factor, Real.exp_zero] using Real.exp_le_exp.mpr he0
  · exact Real.exp_lt_exp.mpr he1
  · intro z hz
    have hz0 : 0 ≤ z := by exact_mod_cast (hz ▸ hh)
    have hcast : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hz0
    dsimp [delta, RademacherGeneralStrictS4.delta]
    rw [hz, Nat.ceil_intCast, hcast, sub_self]

-- Public head 3: actual closed-interval realization by a StrictMono map.
-- The cutoff concerns the existing deterministic geometry, not positivity
-- of the new probability ratio at every prefix; that is a tail output below.
theorem phase_realization {c d : ℝ} (hc : 0 < c)
    (hd : d ∈ Set.Icc (0 : ℝ) 1) :
    ∃ K : ℕ, 2 ≤ K ∧
      StrictMono (fun j : ℕ => phaseIndex c d (j + K)) ∧
      (∀ j : ℕ, RademacherCriticalPhase.cutoff c ≤ phaseIndex c d (j + K)) ∧
      Tendsto (fun j : ℕ => delta c (phaseIndex c d (j + K)))
        atTop (𝓝 d) ∧
      Tendsto (fun j : ℕ => exponent c (phaseIndex c d (j + K)))
        atTop (𝓝 (RademacherCriticalPhase.q c * d)) ∧
      Tendsto (fun j : ℕ => factor c (phaseIndex c d (j + K)))
        atTop (𝓝 (Real.exp (RademacherCriticalPhase.q c * d))) := by
  classical
  have finish (w : ℕ → ℕ) (hw : ∀ k, phaseIndex c d k = w k)
      (K : ℕ) (hs : StrictMono (fun j : ℕ => w (j + K)))
      (hcut : ∀ j, RademacherCriticalPhase.cutoff c ≤ w (j + K))
      (ht : Tendsto (fun k => delta c (w k)) atTop (𝓝 d)) :
      ∃ K : ℕ, 2 ≤ K ∧ StrictMono (fun j : ℕ => phaseIndex c d (j + K)) ∧
        (∀ j, RademacherCriticalPhase.cutoff c ≤ phaseIndex c d (j + K)) ∧
        Tendsto (fun j => delta c (phaseIndex c d (j + K))) atTop (𝓝 d) ∧
        Tendsto (fun j => exponent c (phaseIndex c d (j + K))) atTop
          (𝓝 (RademacherCriticalPhase.q c * d)) ∧
        Tendsto (fun j => factor c (phaseIndex c d (j + K))) atTop
          (𝓝 (Real.exp (RademacherCriticalPhase.q c * d))) := by
    have hshift : StrictMono (fun j : ℕ => j + (K + 2)) :=
      fun _ _ hij => Nat.add_lt_add_right hij _
    have hδ : Tendsto (fun j => delta c (phaseIndex c d (j + (K + 2))))
        atTop (𝓝 d) := by simpa only [hw, Function.comp_def] using ht.comp hshift.tendsto_atTop
    have hE : Tendsto (fun j => exponent c (phaseIndex c d (j + (K + 2)))) atTop
        (𝓝 (RademacherCriticalPhase.q c * d)) := tendsto_const_nhds.mul hδ
    refine ⟨K + 2, by omega, ?_, ?_, hδ, hE, ?_⟩
    · intro i j hij
      simpa only [hw, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hs (Nat.add_lt_add_right hij 2)
    · intro j
      simpa only [hw, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcut (j + 2)
    · exact Real.continuous_exp.continuousAt.tendsto.comp hE
  by_cases hd0 : d = 0
  · subst d
    have ht := (RademacherCriticalPhase.down_phase hc).2.2
    have heq : (fun k => RademacherCriticalPhase.delta c (RademacherCriticalPhase.downIndex c k))
        =ᶠ[atTop] (fun k => delta c (RademacherCriticalPhase.downIndex c k)) := by
      filter_upwards [(RademacherCriticalPhase.down_phase hc).2.1] with k hk
      have hceil : Nat.ceil (RademacherCriticalPhase.height c (RademacherCriticalPhase.downIndex c k)) = k :=
        (Nat.ceil_eq_iff (by omega : k ≠ 0)).mpr ⟨by rw [hk.2.2.1]; exact hk.2.2.2.1, hk.2.2.2.2.1.le⟩
      dsimp [delta, RademacherGeneralStrictS4.delta, RademacherCriticalPhase.delta,
        RademacherCriticalPhase.upperHeight]
      rw [hceil, hk.2.2.2.2.2, hk.2.2.1]
      ring
    obtain ⟨K, hK, hs, hcut, _⟩ := RademacherCriticalPhase.down_subsequence hc
    exact finish (RademacherCriticalPhase.downIndex c) (by intro k; simp [phaseIndex])
      K hs (fun j => (hcut j).1) (ht.congr' heq)
  by_cases hd1 : d = 1
  · subst d
    let w := fun k => RademacherCriticalPhase.upIndex c k + 1
    have herr : Tendsto (fun k => RademacherCriticalPhase.height c (w k) - (k : ℝ))
        atTop (𝓝 (0 : ℝ)) := by
      apply Metric.tendsto_atTop.mpr
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (2 * c ^ 3 / ε))
      have hN1 : 1 ≤ N := by exact_mod_cast (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hN))
      refine ⟨N, ?_⟩
      intro k hk
      have hk1 : 1 ≤ k := le_trans hN1 hk
      have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      have hquot : 2 * c ^ 3 / ε < (k : ℝ) :=
        lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hN) (by exact_mod_cast hk)
      have hprod := (div_lt_iff₀ hε).mp hquot
      have hb := above_height_error hc hk1
      have hs : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
      have hu : 2 * c ^ 3 / (k : ℝ) ^ 2 < ε := by
        apply (div_lt_iff₀ (by positivity : 0 < (k : ℝ) ^ 2)).mpr
        nlinarith [mul_le_mul_of_nonneg_left hs hε.le]
      simpa only [w, Real.dist_eq, sub_zero, abs_of_pos hb.1] using hb.2.trans hu
    have hcell : ∀ᶠ k : ℕ in atTop, (k : ℝ) < RademacherCriticalPhase.height c (w k) ∧
        RademacherCriticalPhase.height c (w k) < (k : ℝ) + 1 := by
      filter_upwards [eventually_ge_atTop 1, (tendsto_order.1 herr).2 1 (by norm_num)] with k hk he
      exact ⟨by linarith [(above_height_error hc hk).1], by linarith⟩
    have ht : Tendsto (fun k => delta c (w k)) atTop (𝓝 (1 : ℝ)) := by
      have hu : Tendsto (fun k : ℕ => (1 : ℝ) -
          (RademacherCriticalPhase.height c (w k) - (k : ℝ))) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub herr
      have heq : (fun k : ℕ => (1 : ℝ) -
          (RademacherCriticalPhase.height c (w k) - (k : ℝ))) =ᶠ[atTop]
          (fun k => delta c (w k)) := by
        filter_upwards [hcell] with k hk
        have hceil : Nat.ceil (RademacherCriticalPhase.height c (w k)) = k + 1 :=
          (Nat.ceil_eq_iff (by omega : k + 1 ≠ 0)).mpr
            ⟨by simpa using hk.1, by simpa only [Nat.cast_add, Nat.cast_one] using hk.2.le⟩
        dsimp [delta, RademacherGeneralStrictS4.delta]
        rw [hceil, Nat.cast_add, Nat.cast_one]
        ring
      have hu' : Tendsto (fun k : ℕ => (1 : ℝ) -
          (RademacherCriticalPhase.height c (w k) - (k : ℝ))) atTop (𝓝 (1 : ℝ)) := by
        simpa only [sub_zero] using hu
      exact hu'.congr' heq
    obtain ⟨K, hK, hs, hcut, _⟩ := RademacherCriticalPhase.up_subsequence hc
    apply finish w (by intro k; simp [phaseIndex, w]) K
    · intro i j hij
      exact Nat.add_lt_add_right (hs hij) 1
    · intro j
      exact le_trans (hcut j).1 (Nat.le_add_right _ _)
    · exact ht
  · have hdpos : 0 < d := lt_of_le_of_ne hd.1 (Ne.symm hd0)
    have hdlt : d < 1 := lt_of_le_of_ne hd.2 hd1
    have hα0 : 0 < 1 - d := by linarith
    have hα1 : 1 - d < 1 := by linarith
    have ht := (RademacherCriticalPhase.nearest_phase hc hα0 hα1).2.2
    have heq : (fun k => RademacherCriticalPhase.delta c (RademacherCriticalPhase.nearestIndex c (1 - d) k))
        =ᶠ[atTop] (fun k => delta c (RademacherCriticalPhase.nearestIndex c (1 - d) k)) := by
      filter_upwards [(RademacherCriticalPhase.nearest_phase hc hα0 hα1).2.1] with k hk
      have hceil : Nat.ceil (RademacherCriticalPhase.height c (RademacherCriticalPhase.nearestIndex c (1 - d) k)) = k + 1 :=
        (Nat.ceil_eq_iff (by omega : k + 1 ≠ 0)).mpr
          ⟨by simpa using hk.1, by simpa only [Nat.cast_add, Nat.cast_one] using hk.2.1.le⟩
      dsimp [delta, RademacherGeneralStrictS4.delta, RademacherCriticalPhase.delta,
        RademacherCriticalPhase.upperHeight]
      rw [hceil, hk.2.2, Nat.cast_add, Nat.cast_one]
    obtain ⟨K, hK, hs, hcut, _⟩ := RademacherCriticalPhase.nearest_subsequence hc hα0 hα1
    apply finish (RademacherCriticalPhase.nearestIndex c (1 - d))
      (by intro k; simp [phaseIndex, hd0, hd1]) K hs (fun j => (hcut j).1)
    convert ht.congr' heq using 1 <;> ring

-- Public head 4: whole-sequence critical correction, literal x in Q/b.
-- Third scale and h/sqrt(n)=x are proved using existing positive-time APIs.
theorem critical_main {ΩB : Type uB} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c : ℝ} (hc : 0 < c) :
    (∀ᶠ n : ℕ in atTop,
      0 < RademacherStrictCube.strictP n (RademacherCriticalPhase.height c n) ∧
      0 < Shao.Probability.BrownianSup.probability B P hB
        (RademacherS5Assembly.x c n) ∧
      0 < Q B P hB c n) ∧
    Tendsto (fun n : ℕ => Real.log (Q B P hB c n) - exponent c n)
      atTop (𝓝 (0 : ℝ)) ∧
    Tendsto (fun n : ℕ => Q B P hB c n / factor c n)
      atTop (𝓝 (1 : ℝ)) ∧
    Tendsto (fun n : ℕ => Q B P hB c n - factor c n)
      atTop (𝓝 (0 : ℝ)) := by
  have hsc := RademacherCriticalPhase.scales hc
  have hs3 : ∃ M : ℝ, 0 < M ∧ ∃ K : ℕ, ∀ n : ℕ, K ≤ n →
      (n : ℝ) / RademacherCriticalPhase.height c n ^ 3 ≤ M := by
    refine ⟨1 / c ^ 3, by positivity, 1, ?_⟩
    intro n hn
    exact ((RademacherCriticalPhase.positive_time hc hn).2.2.2.1).le
  have h := RademacherGeneralStrictS4.strict_S4_EVENTUAL B P hB (fun n => n)
    (RademacherCriticalPhase.height c) hsc.1 hsc.2 hs3
  have hx : ∀ᶠ n : ℕ in atTop,
      RademacherCriticalPhase.height c n / Real.sqrt (n : ℝ) = RademacherS5Assembly.x c n ∧
      RademacherGeneralStrictS4.correction n (RademacherCriticalPhase.height c n) = exponent c n ∧
      RademacherGeneralStrictS4.Q B P hB n (RademacherCriticalPhase.height c n) = Q B P hB c n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hxt : RademacherCriticalPhase.height c n / Real.sqrt (n : ℝ) = RademacherS5Assembly.x c n :=
      (RademacherS5Assembly.positive_time hc hn).2.2.2.2.2.2.2.2.2.2.1.symm
    refine ⟨hxt, ?_, ?_⟩
    · dsimp [RademacherGeneralStrictS4.correction, exponent, delta, RademacherCriticalPhase.q]
      rw [(RademacherCriticalPhase.positive_time hc hn).2.2.2.1]
      ring
    · dsimp [RademacherGeneralStrictS4.Q, Q]
      rw [hxt]
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < RademacherStrictCube.strictP n (RademacherCriticalPhase.height c n) ∧
      0 < Shao.Probability.BrownianSup.probability B P hB (RademacherS5Assembly.x c n) ∧
      0 < Q B P hB c n := by
    filter_upwards [h.1, hx] with n hn he
    simpa only [he.1, he.2.2] using hn
  have hlog : Tendsto (fun n => Real.log (Q B P hB c n) - exponent c n) atTop (𝓝 (0 : ℝ)) :=
    h.2.1.congr' (hx.mono (fun n hn => by rw [hn.2.1, hn.2.2]))
  have hrat : Tendsto (fun n => Q B P hB c n / factor c n) atTop (𝓝 (1 : ℝ)) :=
    h.2.2.congr' (hx.mono (fun n hn => by rw [hn.2.1, hn.2.2]; rfl))
  refine ⟨hpos, hlog, hrat, ?_⟩
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hBpos : 0 < Real.exp (RademacherCriticalPhase.q c) := Real.exp_pos _
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.1 hrat
    (ε / Real.exp (RademacherCriticalPhase.q c)) (div_pos hε hBpos)
  refine ⟨J, ?_⟩
  intro n hn
  have hF : 0 < factor c n := Real.exp_pos _
  have hFb : factor c n ≤ Real.exp (RademacherCriticalPhase.q c) := (phase_bounds hc n).2.2.2.2.2.2.1.le
  have hratn : |Q B P hB c n / factor c n - 1| < ε / Real.exp (RademacherCriticalPhase.q c) := by
    simpa only [Real.dist_eq] using hJ n hn
  have hid : Q B P hB c n - factor c n = factor c n * (Q B P hB c n / factor c n - 1) := by
    field_simp [hF.ne']
  rw [Real.dist_eq, sub_zero, hid, abs_mul, abs_of_pos hF]
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right hFb (abs_nonneg _))
  simpa only [mul_comm] using (lt_div_iff₀ hBpos).1 hratn

-- Public head 5: exact CP.Cluster definition, including both directions.
theorem cluster_sets {ΩB : Type uB} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c : ℝ} (hc : 0 < c) :
    RademacherCriticalPhase.Cluster (delta c) = Set.Icc (0 : ℝ) 1 ∧
    RademacherCriticalPhase.Cluster (exponent c) =
      Set.Icc (0 : ℝ) (RademacherCriticalPhase.q c) ∧
    RademacherCriticalPhase.Cluster (factor c) =
      Set.Icc (1 : ℝ) (Real.exp (RademacherCriticalPhase.q c)) ∧
    RademacherCriticalPhase.Cluster (Q B P hB c) =
      Set.Icc (1 : ℝ) (Real.exp (RademacherCriticalPhase.q c)) := by
  have hq : 0 < RademacherCriticalPhase.q c := (phase_bounds hc 0).2.2.1
  have hδset : RademacherCriticalPhase.Cluster (delta c) = Set.Icc (0 : ℝ) 1 := by
    ext L
    constructor
    · rintro ⟨σ, hs, hL⟩
      exact ⟨le_of_tendsto_of_tendsto' tendsto_const_nhds hL (fun j => (phase_bounds hc (σ j)).1),
        le_of_tendsto' hL (fun j => (phase_bounds hc (σ j)).2.1.le)⟩
    · intro hL
      obtain ⟨K, hK, hs, hcut, ht, _⟩ := phase_realization hc hL
      exact ⟨_, hs, ht⟩
  have hEset : RademacherCriticalPhase.Cluster (exponent c) = Set.Icc (0 : ℝ) (RademacherCriticalPhase.q c) := by
    ext L
    constructor
    · rintro ⟨σ, hs, hL⟩
      exact ⟨le_of_tendsto_of_tendsto' tendsto_const_nhds hL (fun j => (phase_bounds hc (σ j)).2.2.2.1),
        le_of_tendsto' hL (fun j => (phase_bounds hc (σ j)).2.2.2.2.1.le)⟩
    · intro hL
      have hd : L / RademacherCriticalPhase.q c ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨div_nonneg hL.1 hq.le, (div_le_iff₀ hq).mpr (by simpa using hL.2)⟩
      obtain ⟨K, hK, hs, hcut, hδ, hE, hF⟩ := phase_realization hc hd
      have heq : RademacherCriticalPhase.q c * (L / RademacherCriticalPhase.q c) = L := by field_simp [hq.ne']
      exact ⟨_, hs, by simpa only [heq] using hE⟩
  have hFset : RademacherCriticalPhase.Cluster (factor c) = Set.Icc (1 : ℝ) (Real.exp (RademacherCriticalPhase.q c)) := by
    ext L
    constructor
    · rintro ⟨σ, hs, hL⟩
      exact ⟨le_of_tendsto_of_tendsto' tendsto_const_nhds hL (fun j => (phase_bounds hc (σ j)).2.2.2.2.2.1),
        le_of_tendsto' hL (fun j => (phase_bounds hc (σ j)).2.2.2.2.2.2.1.le)⟩
    · intro hL
      have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL.1
      have hl0 : 0 ≤ Real.log L := by simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 1) hL.1
      have hlq : Real.log L ≤ RademacherCriticalPhase.q c := by
        simpa only [Real.log_exp] using Real.log_le_log hLp hL.2
      have hd : Real.log L / RademacherCriticalPhase.q c ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨div_nonneg hl0 hq.le, (div_le_iff₀ hq).mpr (by simpa using hlq)⟩
      obtain ⟨K, hK, hs, hcut, hδ, hE, hF⟩ := phase_realization hc hd
      have heq : RademacherCriticalPhase.q c * (Real.log L / RademacherCriticalPhase.q c) = Real.log L := by field_simp [hq.ne']
      exact ⟨_, hs, by simpa only [heq, Real.exp_log hLp] using hF⟩
  have hdiff := (critical_main B P hB hc).2.2.2
  have hQF : RademacherCriticalPhase.Cluster (Q B P hB c) = RademacherCriticalPhase.Cluster (factor c) := by
    ext L
    constructor
    · rintro ⟨σ, hs, hL⟩
      refine ⟨σ, hs, ?_⟩
      have ht := hL.sub (hdiff.comp hs.tendsto_atTop)
      have ht' : Tendsto (fun j => Q B P hB c (σ j) - (Q B P hB c (σ j) - factor c (σ j))) atTop (𝓝 L) := by
        simpa only [Function.comp_def, sub_zero] using ht
      exact ht'.congr' (Filter.Eventually.of_forall fun j => by ring)
    · rintro ⟨σ, hs, hL⟩
      refine ⟨σ, hs, ?_⟩
      have ht := hL.add (hdiff.comp hs.tendsto_atTop)
      have ht' : Tendsto (fun j => factor c (σ j) + (Q B P hB c (σ j) - factor c (σ j))) atTop (𝓝 L) := by
        simpa only [Function.comp_def, add_zero] using ht
      exact ht'.congr' (Filter.Eventually.of_forall fun j => by ring)
  exact ⟨hδset, hEset, hFset, hQF.trans hFset⟩

-- Public head 6: each sequence has two distinct actual subsequential limits.
theorem not_convergent {ΩB : Type uB} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c : ℝ} (hc : 0 < c) :
    (¬ ∃ L : ℝ, Tendsto (delta c) atTop (𝓝 L)) ∧
    (¬ ∃ L : ℝ, Tendsto (exponent c) atTop (𝓝 L)) ∧
    (¬ ∃ L : ℝ, Tendsto (factor c) atTop (𝓝 L)) ∧
    (¬ ∃ L : ℝ, Tendsto (Q B P hB c) atTop (𝓝 L)) := by
  have hsets := cluster_sets B P hB hc
  have hq : 0 < RademacherCriticalPhase.q c := (phase_bounds hc 0).2.2.1
  have hexp : 1 < Real.exp (RademacherCriticalPhase.q c) := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hq
  have separate (z : ℕ → ℝ) (a b : ℝ) (hab : a < b)
      (ha : a ∈ RademacherCriticalPhase.Cluster z) (hb : b ∈ RademacherCriticalPhase.Cluster z) :
      ¬ ∃ L : ℝ, Tendsto z atTop (𝓝 L) := by
    rintro ⟨L, hL⟩
    obtain ⟨σa, hsa, hta⟩ := ha
    obtain ⟨σb, hsb, htb⟩ := hb
    have heqa := tendsto_nhds_unique (hL.comp hsa.tendsto_atTop) hta
    have heqb := tendsto_nhds_unique (hL.comp hsb.tendsto_atTop) htb
    linarith
  refine ⟨separate _ 0 1 (by norm_num) ?_ ?_,
    separate _ 0 (RademacherCriticalPhase.q c) hq ?_ ?_,
    separate _ 1 (Real.exp (RademacherCriticalPhase.q c)) hexp ?_ ?_,
    separate _ 1 (Real.exp (RademacherCriticalPhase.q c)) hexp ?_ ?_⟩
  · rw [hsets.1]; exact ⟨le_rfl, by norm_num⟩
  · rw [hsets.1]; exact ⟨by norm_num, le_rfl⟩
  · rw [hsets.2.1]; exact ⟨le_rfl, hq.le⟩
  · rw [hsets.2.1]; exact ⟨hq.le, le_rfl⟩
  · rw [hsets.2.2.1]; exact ⟨le_rfl, hexp.le⟩
  · rw [hsets.2.2.1]; exact ⟨hexp.le, le_rfl⟩
  · rw [hsets.2.2.2]; exact ⟨le_rfl, hexp.le⟩
  · rw [hsets.2.2.2]; exact ⟨hexp.le, le_rfl⟩

end Shao.OQ4.RademacherStrictCriticalPhase

end
