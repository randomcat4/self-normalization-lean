import Shao.OQ4.RademacherStrictWeakBoundary
import Shao.OQ4.RademacherCriticalPhase
import Shao.OQ4.RademacherRealThresholdBridge

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Shao.OQ4.RademacherStrictWeakBoundary

def criticalRatio (c : ℝ) (n : ℕ) : ℝ :=
  ratio n (RademacherCriticalPhase.height c n)

-- n=0 is only a prefix: criticalRatio c 0=1 but the displayed factor
-- there equals exp(q c), because integerIndicator (height c 0)=1.
theorem critical_main {c : ℝ} (hc : 0 < c) :
    (∀ᶠ n : ℕ in atTop,
      0 < RademacherS5Assembly.p n (RademacherCriticalPhase.height c n) ∧
      0 < RademacherStrictCube.strictP n
        (RademacherCriticalPhase.height c n) ∧
      0 < criticalRatio c n) ∧
    Tendsto (fun n : ℕ =>
      Real.log (criticalRatio c n) -
        RademacherCriticalPhase.q c *
          integerIndicator (RademacherCriticalPhase.height c n))
      atTop (𝓝 (0 : ℝ)) ∧
    Tendsto (fun n : ℕ =>
      criticalRatio c n /
        Real.exp (RademacherCriticalPhase.q c *
          integerIndicator (RademacherCriticalPhase.height c n)))
      atTop (𝓝 (1 : ℝ)) ∧
    Tendsto (fun n : ℕ =>
      criticalRatio c n -
        Real.exp (RademacherCriticalPhase.q c *
          integerIndicator (RademacherCriticalPhase.height c n)))
      atTop (𝓝 (0 : ℝ)) := by
  have hscale3 : ∃ M : ℝ, 0 < M ∧ ∃ K : ℕ, ∀ n : ℕ, K ≤ n →
      (n : ℝ) / RademacherCriticalPhase.height c n ^ 3 ≤ M := by
    refine ⟨1 / c ^ 3, by positivity, 1, ?_⟩
    intro n hn
    exact (RademacherCriticalPhase.positive_time hc hn).2.2.2.1.le
  have hm := boundary_main (fun n => n) (RademacherCriticalPhase.height c)
    (RademacherCriticalPhase.scales hc).1
    (RademacherCriticalPhase.scales hc).2 hscale3
  have hcoef : (Real.pi ^ 2 / 4) * (1 / c ^ 3) = RademacherCriticalPhase.q c := by
    dsimp [RademacherCriticalPhase.q]
    field_simp
  have heq : ∀ᶠ n : ℕ in atTop,
      (Real.pi ^ 2 / 4) * ((n : ℝ) / RademacherCriticalPhase.height c n ^ 3) =
        RademacherCriticalPhase.q c := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    rw [(RademacherCriticalPhase.positive_time hc hn).2.2.2.1, hcoef]
  refine ⟨?_, hm.2.1.congr' ?_, hm.2.2.1.congr' ?_, hm.2.2.2.congr' ?_⟩
  · filter_upwards [hm.1] with n hn
    exact ⟨hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1⟩
  · filter_upwards [heq] with n hn
    simp only [criticalRatio, hn]
  · filter_upwards [heq] with n hn
    simp only [criticalRatio, hn]
  · filter_upwards [heq] with n hn
    simp only [criticalRatio, hn]

-- The +1 is essential. Every displayed tail probability is actual and
-- positive. Exact equality of the quotient follows only on that tail.
theorem noninteger_subsequence {c : ℝ} (hc : 0 < c) :
    ∃ K : ℕ, 2 ≤ K ∧
      StrictMono (fun j : ℕ => RademacherCriticalPhase.upIndex c (j + K) + 1) ∧
      (∀ j : ℕ,
        let n := RademacherCriticalPhase.upIndex c (j + K) + 1
        RademacherCriticalPhase.cutoff c ≤ n ∧
        ((j + K : ℕ) : ℝ) < RademacherCriticalPhase.height c n ∧
        RademacherCriticalPhase.height c n < ((j + K : ℕ) : ℝ) + 1 ∧
        0 < RademacherS5Assembly.p n (RademacherCriticalPhase.height c n) ∧
        0 < RademacherStrictCube.strictP n
          (RademacherCriticalPhase.height c n) ∧
        criticalRatio c n = 1) := by
  classical
  have herror {k : ℕ} (hk : 1 ≤ k) :
      0 < RademacherCriticalPhase.height c (RademacherCriticalPhase.upIndex c k + 1) - (k : ℝ) ∧
      RademacherCriticalPhase.height c (RademacherCriticalPhase.upIndex c k + 1) - (k : ℝ) <
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
  obtain ⟨K0, hK0, hs, hl, _⟩ := RademacherCriticalPhase.up_subsequence hc
  have hs1 : StrictMono (fun j : ℕ => RademacherCriticalPhase.upIndex c (j + K0) + 1) :=
    fun _ _ hij => Nat.add_lt_add_right (hs hij) 1
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hs1.tendsto_atTop.eventually (critical_main hc).1)
  obtain ⟨D, hD⟩ := exists_nat_gt (max 1 (2 * c ^ 3))
  let K := K0 + (T + D + 2)
  have hK : 2 ≤ K := by dsimp [K]; omega
  have hmono : StrictMono (fun j : ℕ => RademacherCriticalPhase.upIndex c (j + K) + 1) := by
    intro i j hij
    simpa only [K, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs1 (Nat.add_lt_add_right hij (T + D + 2))
  refine ⟨K, hK, hmono, ?_⟩
  intro j
  let k := j + K
  let n := RademacherCriticalPhase.upIndex c k + 1
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hDk : (D : ℝ) ≤ k := by exact_mod_cast (show D ≤ k by dsimp [k, K]; omega)
  have hbig : 2 * c ^ 3 < (k : ℝ) :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hD) hDk
  have hsquare : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hsmall : 2 * c ^ 3 / (k : ℝ) ^ 2 < 1 := by
    apply (div_lt_one (by positivity : 0 < (k : ℝ) ^ 2)).2
    linarith
  have he := herror (show 1 ≤ k by omega)
  have hlo : (k : ℝ) < RademacherCriticalPhase.height c n := by dsimp [n]; linarith [he.1]
  have hhi : RademacherCriticalPhase.height c n < (k : ℝ) + 1 := by dsimp [n]; linarith [he.2]
  have hnonint : ¬ ∃ z : ℤ, RademacherCriticalPhase.height c n = (z : ℝ) := by
    rintro ⟨z, hz⟩
    have h1 : (k : ℤ) < z := by exact_mod_cast (hz ▸ hlo)
    have h2 : z < (k : ℤ) + 1 := by exact_mod_cast (hz ▸ hhi)
    omega
  have hpos : 0 < RademacherS5Assembly.p n (RademacherCriticalPhase.height c n) ∧
      0 < RademacherStrictCube.strictP n (RademacherCriticalPhase.height c n) ∧
      0 < criticalRatio c n := by
    simpa only [n, k, K, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hT (j + (T + D + 2)) (by omega)
  have hcut : RademacherCriticalPhase.cutoff c ≤ n := by
    have hh := (hl (j + (T + D + 2))).1
    dsimp [n, k, K]
    simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at hh ⊢
    omega
  have hequal : RademacherS5Assembly.p n (RademacherCriticalPhase.height c n) =
      RademacherStrictCube.strictP n (RademacherCriticalPhase.height c n) := by
    change ((RademacherS5Assembly.pathLaw n) (@Shao.closedStrip n _)).toReal =
      ((RademacherS5Assembly.pathLaw n) (RademacherStrictCube.strictEvent n _)).toReal
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [(RademacherStrictCube.actual_path_support n).2.2] with v hv
    apply propext
    constructor
    · intro hw r hr hrn
      have hle := hw r hrn
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact hlt
      · obtain ⟨z, hz⟩ := hv.2.1 r hrn
        exact (hnonint ⟨|z|, by rw [Int.cast_abs, ← hz]; exact heq.symm⟩).elim
    · intro ht r hrn
      by_cases hr0 : r = 0
      · subst r
        simpa only [Shao.prefixSum_zero, abs_zero] using (lt_trans (by positivity : (0 : ℝ) < k) hlo).le
      · exact (ht r (by omega) hrn).le
  refine ⟨hcut, hlo, hhi, hpos.1, hpos.2.1, ?_⟩
  change RademacherS5Assembly.p n _ / RademacherStrictCube.strictP n _ = 1
  rw [hequal, div_self hpos.2.1.ne']

-- d is a positive integer rational denominator; q c is the spectral
-- coefficient. No coprimality premise or cancellation in Nat is needed.
theorem rational_integer_subsequence {c : ℝ} (hc : 0 < c)
    (p d : ℕ) (hp : 1 ≤ p) (hd : 1 ≤ d)
    (hRat : c ^ 3 = (p : ℝ) / (d : ℝ)) :
    ∃ K : ℕ, 2 ≤ K ∧
      StrictMono (fun j : ℕ => d * p ^ 2 * (j + K) ^ 3) ∧
      (∀ j : ℕ,
        let n := d * p ^ 2 * (j + K) ^ 3
        RademacherCriticalPhase.cutoff c ≤ n ∧
        RademacherCriticalPhase.height c n = ((p * (j + K) : ℕ) : ℝ) ∧
        0 < RademacherS5Assembly.p n (RademacherCriticalPhase.height c n) ∧
        0 < RademacherStrictCube.strictP n
          (RademacherCriticalPhase.height c n)) ∧
      Tendsto (fun j : ℕ =>
        criticalRatio c (d * p ^ 2 * (j + K) ^ 3))
        atTop (𝓝 (Real.exp (RademacherCriticalPhase.q c))) := by
  classical
  have hp0 : 0 < p := by omega
  have hd0 : 0 < d := by omega
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
  have hheight (k : ℕ) : RademacherCriticalPhase.height c (d * p ^ 2 * k ^ 3) =
      ((p * k : ℕ) : ℝ) := by
    have hx3 : (((p * k : ℕ) : ℝ) / c) ^ 3 = ((d * p ^ 2 * k ^ 3 : ℕ) : ℝ) := by
      rw [div_pow, hRat]
      push_cast
      field_simp [hdR]
      <;> ring
    have hx := (RademacherCriticalPhase.root_spec (d * p ^ 2 * k ^ 3)).2.2
      (((p * k : ℕ) : ℝ) / c) (by positivity) hx3
    rw [RademacherCriticalPhase.height, ← hx]
    field_simp [hc.ne']
  have ha : 0 < d * p ^ 2 := Nat.mul_pos hd0 (pow_pos hp0 2)
  have hmono : StrictMono (fun k : ℕ => d * p ^ 2 * k ^ 3) := by
    intro i j hij
    exact Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left hij (by norm_num : (3 : ℕ) ≠ 0)) ha
  have htail := hmono.tendsto_atTop.eventually ((critical_main hc).1.and
    (eventually_ge_atTop (RademacherCriticalPhase.cutoff c)))
  obtain ⟨T, hT⟩ := eventually_atTop.1 htail
  let K := max 2 T
  have hK : 2 ≤ K := le_max_left _ _
  have hσ : StrictMono (fun j : ℕ => d * p ^ 2 * (j + K) ^ 3) :=
    hmono.comp (fun _ _ hij => Nat.add_lt_add_right hij K)
  have hJ (j : ℕ) : integerIndicator
      (RademacherCriticalPhase.height c (d * p ^ 2 * (j + K) ^ 3)) = 1 := by
    have hh : ∃ z : ℤ, RademacherCriticalPhase.height c (d * p ^ 2 * (j + K) ^ 3) = (z : ℝ) :=
      ⟨(p * (j + K) : ℕ), by simpa only [Int.cast_natCast] using hheight (j + K)⟩
    simp only [integerIndicator, if_pos hh]
  refine ⟨K, hK, hσ, ?_, ?_⟩
  · intro j
    have ht := hT (j + K) (by dsimp [K]; omega)
    exact ⟨ht.2, hheight (j + K), ht.1.1, ht.1.2.1⟩
  · have he : Tendsto (fun j : ℕ => criticalRatio c (d * p ^ 2 * (j + K) ^ 3) -
        Real.exp (RademacherCriticalPhase.q c)) atTop (𝓝 (0 : ℝ)) := by
      simpa only [Function.comp_def, hJ, mul_one] using (critical_main hc).2.2.2.comp hσ.tendsto_atTop
    simpa only [sub_add_cancel, zero_add] using he.add_const (Real.exp (RademacherCriticalPhase.q c))

-- Both set inclusions are required; outer inclusion is the finite-two-set
-- distance argument in proof.md, not an appeal to generic cluster closure.
theorem critical_rational {c : ℝ} (hc : 0 < c)
    (hRat : ∃ r : ℚ, (r : ℝ) = c ^ 3) :
    RademacherCriticalPhase.Cluster (criticalRatio c) =
      ({(1 : ℝ), Real.exp (RademacherCriticalPhase.q c)} : Set ℝ) ∧
    (¬ ∃ L : ℝ, Tendsto (criticalRatio c) atTop (𝓝 L)) := by
  classical
  obtain ⟨r, hr⟩ := hRat
  have hrpos : (0 : ℚ) < r := by
    exact_mod_cast (show (0 : ℝ) < (r : ℝ) by rw [hr]; positivity)
  have hnum : (0 : ℤ) < r.num := Rat.num_pos.mpr hrpos
  have hp : 1 ≤ r.num.toNat := by
    have hto : (r.num.toNat : ℤ) = r.num := Int.toNat_of_nonneg hnum.le
    omega
  have hd : 1 ≤ r.den := r.den_pos
  have hncast : ((r.num.toNat : ℕ) : ℝ) = (r.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum.le
  have hrep : c ^ 3 = (r.num.toNat : ℝ) / (r.den : ℝ) := by
    calc
      c ^ 3 = (r : ℝ) := hr.symm
      _ = (r.num : ℝ) / (r.den : ℝ) := Rat.cast_def r
      _ = (r.num.toNat : ℝ) / (r.den : ℝ) := by rw [hncast]
  obtain ⟨K0, hK0, hσ0, hP0⟩ := noninteger_subsequence hc
  obtain ⟨K1, hK1, hσ1, hP1, hL1⟩ := rational_integer_subsequence hc r.num.toNat r.den hp hd hrep
  have hL0 : Tendsto (fun j : ℕ => criticalRatio c (RademacherCriticalPhase.upIndex c (j + K0) + 1))
      atTop (𝓝 (1 : ℝ)) := by
    have he : (fun j : ℕ => criticalRatio c (RademacherCriticalPhase.upIndex c (j + K0) + 1)) =
        (fun _ : ℕ => (1 : ℝ)) := funext fun j => (hP0 j).2.2.2.2.2
    rw [he]
    exact tendsto_const_nhds
  have hmem0 : (1 : ℝ) ∈ RademacherCriticalPhase.Cluster (criticalRatio c) := ⟨_, hσ0, hL0⟩
  have hmem1 : Real.exp (RademacherCriticalPhase.q c) ∈ RademacherCriticalPhase.Cluster (criticalRatio c) :=
    ⟨_, hσ1, hL1⟩
  have htwo (n : ℕ) : Real.exp (RademacherCriticalPhase.q c *
      integerIndicator (RademacherCriticalPhase.height c n)) = 1 ∨
      Real.exp (RademacherCriticalPhase.q c *
        integerIndicator (RademacherCriticalPhase.height c n)) = Real.exp (RademacherCriticalPhase.q c) := by
    rcases (boundary_gap (RademacherCriticalPhase.height c n)
      (RademacherCriticalPhase.finite_phase hc n).1).2 with h | h
    · exact Or.inl (by rw [h, mul_zero, Real.exp_zero])
    · exact Or.inr (by rw [h, mul_one])
  have hcluster : RademacherCriticalPhase.Cluster (criticalRatio c) =
      ({(1 : ℝ), Real.exp (RademacherCriticalPhase.q c)} : Set ℝ) := by
    ext L
    constructor
    · rintro ⟨σ, hσ, hL⟩
      have herr := (critical_main hc).2.2.2.comp hσ.tendsto_atTop
      have hF : Tendsto (fun j => Real.exp (RademacherCriticalPhase.q c *
          integerIndicator (RademacherCriticalPhase.height c (σ j)))) atTop (𝓝 L) := by
        simpa only [Function.comp_def, sub_sub_cancel, sub_zero] using hL.sub herr
      by_contra hnot
      have hne0 : L ≠ 1 := by intro h; apply hnot; simp [h]
      have hne1 : L ≠ Real.exp (RademacherCriticalPhase.q c) := by intro h; apply hnot; simp [h]
      let ε := min |(1 : ℝ) - L| |Real.exp (RademacherCriticalPhase.q c) - L| / 2
      have hε : 0 < ε := by
        dsimp [ε]
        exact div_pos (lt_min (abs_pos.mpr (sub_ne_zero.mpr hne0.symm))
          (abs_pos.mpr (sub_ne_zero.mpr hne1.symm))) (by norm_num)
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hF ε hε
      have hdist := hN N le_rfl
      rcases htwo (σ N) with h | h
      · rw [h, Real.dist_eq] at hdist
        have hεle : ε ≤ |(1 : ℝ) - L| / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
        linarith [abs_nonneg ((1 : ℝ) - L)]
      · rw [h, Real.dist_eq] at hdist
        have hεle : ε ≤ |Real.exp (RademacherCriticalPhase.q c) - L| / 2 :=
          div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
        linarith [abs_nonneg (Real.exp (RademacherCriticalPhase.q c) - L)]
    · intro hL
      rcases Set.mem_insert_iff.1 hL with h | h
      · simpa only [h] using hmem0
      · have h : L = Real.exp (RademacherCriticalPhase.q c) := Set.mem_singleton_iff.1 h
        simpa only [h] using hmem1
  refine ⟨hcluster, ?_⟩
  rintro ⟨L, hL⟩
  have h0 : (1 : ℝ) = L := tendsto_nhds_unique hL0 (hL.comp hσ0.tendsto_atTop)
  have h1 : Real.exp (RademacherCriticalPhase.q c) = L := tendsto_nhds_unique hL1 (hL.comp hσ1.tendsto_atTop)
  have hq : 0 < RademacherCriticalPhase.q c := by dsimp [RademacherCriticalPhase.q]; positivity
  have hgt : 1 < Real.exp (RademacherCriticalPhase.q c) := Real.one_lt_exp_iff.mpr hq
  linarith

-- Do not strengthen the eventual quotient equality to all positive n:
-- at a low threshold the equal probabilities can both be zero.
theorem critical_irrational {c : ℝ} (hc : 0 < c)
    (hIrr : ¬ ∃ r : ℚ, (r : ℝ) = c ^ 3) :
    (∀ n : ℕ, 1 ≤ n →
      (∀ z : ℤ, RademacherCriticalPhase.height c n ≠ (z : ℝ)) ∧
      RademacherS5Assembly.p n (RademacherCriticalPhase.height c n) =
        RademacherStrictCube.strictP n
          (RademacherCriticalPhase.height c n)) ∧
    (∀ᶠ n : ℕ in atTop, criticalRatio c n = 1) ∧
    Tendsto (criticalRatio c) atTop (𝓝 (1 : ℝ)) ∧
    RademacherCriticalPhase.Cluster (criticalRatio c) = ({(1 : ℝ)} : Set ℝ) := by
  classical
  have hall (n : ℕ) (hn : 1 ≤ n) :
      (∀ z : ℤ, RademacherCriticalPhase.height c n ≠ (z : ℝ)) ∧
      RademacherS5Assembly.p n (RademacherCriticalPhase.height c n) =
        RademacherStrictCube.strictP n (RademacherCriticalPhase.height c n) := by
    have ht := RademacherCriticalPhase.positive_time hc hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hnon (z : ℤ) : RademacherCriticalPhase.height c n ≠ (z : ℝ) := by
      intro hz
      apply hIrr
      refine ⟨(z : ℚ) ^ 3 / (n : ℚ), ?_⟩
      push_cast
      apply (div_eq_iff hnR).2
      rw [← hz]
      exact ht.2.2.1
    refine ⟨hnon, ?_⟩
    change ((RademacherS5Assembly.pathLaw n) (@Shao.closedStrip n _)).toReal =
      ((RademacherS5Assembly.pathLaw n) (RademacherStrictCube.strictEvent n _)).toReal
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [(RademacherStrictCube.actual_path_support n).2.2] with v hv
    apply propext
    constructor
    · intro hw r hr hrn
      have hle := hw r hrn
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact hlt
      · obtain ⟨z, hz⟩ := hv.2.1 r hrn
        exact (hnon |z| (by rw [Int.cast_abs, ← hz]; exact heq.symm)).elim
    · intro hs r hrn
      by_cases hr0 : r = 0
      · subst r
        simpa only [Shao.prefixSum_zero, abs_zero] using ht.2.1.le
      · exact (hs r (by omega) hrn).le
  have hevent : ∀ᶠ n : ℕ in atTop, criticalRatio c n = 1 := by
    filter_upwards [(critical_main hc).1, eventually_ge_atTop (1 : ℕ)] with n hp hn
    change RademacherS5Assembly.p n _ / RademacherStrictCube.strictP n _ = 1
    rw [(hall n hn).2, div_self hp.2.1.ne']
  have hlim : Tendsto (criticalRatio c) atTop (𝓝 (1 : ℝ)) := by
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) := tendsto_const_nhds
    apply hconst.congr'
    filter_upwards [hevent] with n hn
    exact hn.symm
  refine ⟨hall, hevent, hlim, ?_⟩
  ext L
  constructor
  · rintro ⟨σ, hσ, hL⟩
    exact Set.mem_singleton_iff.2 (tendsto_nhds_unique hL (hlim.comp hσ.tendsto_atTop))
  · intro hL
    have hL : L = 1 := Set.mem_singleton_iff.1 hL
    subst L
    exact ⟨id, strictMono_id, by simpa only [id_eq] using hlim⟩

end Shao.OQ4.RademacherStrictWeakBoundary
end
