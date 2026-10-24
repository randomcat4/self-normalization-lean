import Shao.OQ4.RademacherGeneralStrictS4
import Shao.OQ4.CanonicalBrownian

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Shao.OQ4.RademacherStrictWeakBoundary

def integerIndicator (h : ℝ) : ℝ :=
  letI : Decidable (∃ z : ℤ, h = (z : ℝ)) := Classical.propDecidable _
  if ∃ z : ℤ, h = (z : ℝ) then 1 else 0

def ratio (n : ℕ) (h : ℝ) : ℝ :=
  RademacherS5Assembly.p n h / RademacherStrictCube.strictP n h

-- Nat.floor/Nat.ceil are used only on the explicitly nonnegative domain.
theorem boundary_gap (h : ℝ) (hh : 0 ≤ h) :
    ((Nat.floor h : ℝ) + 1 - h) -
        RademacherGeneralStrictS4.delta h = integerIndicator h ∧
    (integerIndicator h = 0 ∨ integerIndicator h = 1) := by
  classical
  by_cases hi : ∃ z : ℤ, h = (z : ℝ)
  · have hJ : integerIndicator h = 1 := by simp [integerIndicator, hi]
    rcases hi with ⟨z, rfl⟩
    have hz : 0 ≤ z := by exact_mod_cast hh
    have he : (z : ℝ) = (z.toNat : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hz).symm
    rw [he] at hJ ⊢
    simp only [Nat.floor_natCast, Nat.ceil_natCast,
      RademacherGeneralStrictS4.delta, hJ]
    constructor
    · ring
    · simp
  · have hJ : integerIndicator h = 0 := by simp [integerIndicator, hi]
    have hlt : (Nat.floor h : ℝ) < h := by
      refine lt_of_le_of_ne (Nat.floor_le hh) ?_
      intro he
      exact hi ⟨(Nat.floor h : ℤ), by exact_mod_cast he.symm⟩
    have hc : Nat.ceil h = Nat.floor h + 1 := by
      apply (Nat.ceil_eq_iff (by omega : Nat.floor h + 1 ≠ 0)).2
      simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using
        And.intro hlt (Nat.lt_floor_add_one h).le
    rw [RademacherGeneralStrictS4.delta, hc, Nat.cast_add, Nat.cast_one, hJ]
    exact ⟨by ring, Or.inl rfl⟩

-- One common positive tail gives the ordinary interpretation of log/div.
-- No limit of the third scale is assumed.
theorem boundary_main (n_ : ℕ → ℕ) (h_ : ℕ → ℝ)
    (hh : Tendsto h_ atTop atTop)
    (hscale2 : Tendsto
      (fun k : ℕ => (n_ k : ℝ) / (h_ k) ^ 2) atTop atTop)
    (hscale3 : ∃ M : ℝ, 0 < M ∧
      ∃ K_M : ℕ, ∀ k : ℕ, K_M ≤ k →
        (n_ k : ℝ) / (h_ k) ^ 3 ≤ M) :
    (∀ᶠ k : ℕ in atTop,
      2 ≤ h_ k ∧ 1 ≤ n_ k ∧
      0 < RademacherS5Assembly.p (n_ k) (h_ k) ∧
      0 < RademacherStrictCube.strictP (n_ k) (h_ k) ∧
      0 < ratio (n_ k) (h_ k) ∧
      Real.log (ratio (n_ k) (h_ k)) =
        Real.log (RademacherS5Assembly.p (n_ k) (h_ k)) -
          Real.log (RademacherStrictCube.strictP (n_ k) (h_ k))) ∧
    Tendsto (fun k : ℕ =>
      Real.log (ratio (n_ k) (h_ k)) -
        (Real.pi ^ 2 / 4) * ((n_ k : ℝ) / (h_ k) ^ 3) *
          integerIndicator (h_ k)) atTop (𝓝 (0 : ℝ)) ∧
    Tendsto (fun k : ℕ =>
      ratio (n_ k) (h_ k) /
        Real.exp ((Real.pi ^ 2 / 4) * ((n_ k : ℝ) / (h_ k) ^ 3) *
          integerIndicator (h_ k))) atTop (𝓝 (1 : ℝ)) ∧
    Tendsto (fun k : ℕ =>
      ratio (n_ k) (h_ k) -
        Real.exp ((Real.pi ^ 2 / 4) * ((n_ k : ℝ) / (h_ k) ^ 3) *
          integerIndicator (h_ k))) atTop (𝓝 (0 : ℝ)) := by
  classical
  let m : ℕ → ℕ := fun k => Nat.floor (h_ k)
  let B := CanonicalBrownian.B
  let P := CanonicalBrownian.law
  let hB : IsBrownianReal B P := CanonicalBrownian.isBrownianReal
  let b : ℕ → ℝ := fun k => Shao.Probability.BrownianSup.probability B P hB
    (h_ k / Real.sqrt (n_ k : ℝ))
  let A : ℕ → ℝ := fun k => (Real.pi ^ 2 / 4) *
    ((n_ k : ℝ) / (h_ k) ^ 3) * integerIndicator (h_ k)
  have hcell : ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      1 ≤ m k ∧ (m k : ℝ) ≤ h_ k ∧ h_ k < (m k : ℝ) + 1 := by
    obtain ⟨K, hK⟩ := eventually_atTop.1 (hh.eventually_ge_atTop (2 : ℝ))
    refine ⟨K, fun k hk => ?_⟩
    have hhk : 0 ≤ h_ k := by linarith [hK k hk]
    exact ⟨(Nat.le_floor_iff hhk).2 (by norm_num; linarith [hK k hk]),
      Nat.floor_le hhk, Nat.lt_floor_add_one _⟩
  have hw := RademacherS4Assembly.S4_EVENTUAL B P hB m n_ h_ hcell hh
    hscale2 hscale3
  have hs := RademacherGeneralStrictS4.strict_S4_EVENTUAL B P hB n_ h_
    hh hscale2 hscale3
  have hwlog := hw.2.2.2.2.2.2.2.1
  obtain ⟨Kt, Kp, hKtp, htime, hpos, _⟩ := hw.2.2.2.2.2.2.2.2.2
  have hlegal : ∀ᶠ k : ℕ in atTop,
      2 ≤ h_ k ∧ 1 ≤ n_ k ∧
      0 < RademacherS5Assembly.p (n_ k) (h_ k) ∧
      0 < RademacherStrictCube.strictP (n_ k) (h_ k) ∧ 0 < b k := by
    filter_upwards [hh.eventually_ge_atTop (2 : ℝ), eventually_ge_atTop Kp,
      hs.1] with k hk hkp hsk
    have ht := htime k (hKtp.trans hkp)
    rcases (hpos k hkp).1 with ⟨_, _, _, _, _, _, _, _, _, hp, _, _, hb, _⟩
    exact ⟨hk, ht.2.2.2.1, hp, hsk.1, hb⟩
  have htail : ∀ᶠ k : ℕ in atTop,
      2 ≤ h_ k ∧ 1 ≤ n_ k ∧
      0 < RademacherS5Assembly.p (n_ k) (h_ k) ∧
      0 < RademacherStrictCube.strictP (n_ k) (h_ k) ∧
      0 < ratio (n_ k) (h_ k) ∧
      Real.log (ratio (n_ k) (h_ k)) =
        Real.log (RademacherS5Assembly.p (n_ k) (h_ k)) -
          Real.log (RademacherStrictCube.strictP (n_ k) (h_ k)) := by
    filter_upwards [hlegal] with k hk
    exact ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1,
      div_pos hk.2.2.1 hk.2.2.2.1,
      Real.log_div hk.2.2.1.ne' hk.2.2.2.1.ne'⟩
  have hlog : Tendsto (fun k => Real.log (ratio (n_ k) (h_ k)) - A k)
      atTop (𝓝 (0 : ℝ)) := by
    have hd := hwlog.sub hs.2.1
    have heq : (fun k =>
        (Real.log (RademacherS4Assembly.Q B P hB (n_ k) (h_ k)) -
          RademacherS4Assembly.w (m k) (n_ k) (h_ k)) -
        (Real.log (RademacherGeneralStrictS4.Q B P hB (n_ k) (h_ k)) -
          RademacherGeneralStrictS4.correction (n_ k) (h_ k))) =ᶠ[atTop]
        (fun k => Real.log (ratio (n_ k) (h_ k)) - A k) := by
      filter_upwards [hlegal, htail] with k hk ht
      have hg := (boundary_gap (h_ k) (by linarith [hk.1])).1
      change (Real.log (RademacherS5Assembly.p (n_ k) (h_ k) / b k) -
          (Real.pi ^ 2 / 4) * ((n_ k : ℝ) / (h_ k) ^ 3) *
            ((Nat.floor (h_ k) : ℝ) + 1 - h_ k)) -
        (Real.log (RademacherStrictCube.strictP (n_ k) (h_ k) / b k) -
          (Real.pi ^ 2 / 4) * ((n_ k : ℝ) / (h_ k) ^ 3) *
            RademacherGeneralStrictS4.delta (h_ k)) = _
      rw [Real.log_div hk.2.2.1.ne' hk.2.2.2.2.ne',
        Real.log_div hk.2.2.2.1.ne' hk.2.2.2.2.ne', ht.2.2.2.2.2]
      dsimp only [A]
      rw [← hg]
      ring
    simpa only [sub_self] using hd.congr' heq
  have hquot : Tendsto (fun k => ratio (n_ k) (h_ k) / Real.exp (A k))
      atTop (𝓝 (1 : ℝ)) := by
    have he := (Real.continuous_exp.tendsto (0 : ℝ)).comp hlog
    have heq : (fun k => Real.exp (Real.log (ratio (n_ k) (h_ k)) - A k))
        =ᶠ[atTop] (fun k => ratio (n_ k) (h_ k) / Real.exp (A k)) := by
      filter_upwards [htail] with k hk
      rw [Real.exp_sub, Real.exp_log hk.2.2.2.2.1]
    simpa only [Real.exp_zero, Function.comp_def] using he.congr' heq
  obtain ⟨M, hM, KM, hKM⟩ := hscale3
  have hbound : ∀ᶠ k : ℕ in atTop,
      |ratio (n_ k) (h_ k) - Real.exp (A k)| ≤
        Real.exp ((Real.pi ^ 2 / 4) * M) *
          |ratio (n_ k) (h_ k) / Real.exp (A k) - 1| := by
    filter_upwards [hlegal, eventually_ge_atTop KM] with k hk hkm
    have hJ := (boundary_gap (h_ k) (by linarith [hk.1])).2
    have hA : A k ≤ (Real.pi ^ 2 / 4) * M := by
      rcases hJ with hj | hj
      · simp only [A, hj, mul_zero]; positivity
      · simp only [A, hj, mul_one]
        exact mul_le_mul_of_nonneg_left (hKM k hkm) (by positivity)
    have heq : ratio (n_ k) (h_ k) - Real.exp (A k) =
        Real.exp (A k) * (ratio (n_ k) (h_ k) / Real.exp (A k) - 1) := by
      field_simp [Real.exp_ne_zero (A k)]
    rw [heq, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hA) (abs_nonneg _)
  have hadd : Tendsto (fun k => ratio (n_ k) (h_ k) - Real.exp (A k))
      atTop (𝓝 (0 : ℝ)) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).2
    apply squeeze_zero' (Eventually.of_forall fun k => abs_nonneg _) hbound
    simpa using ((hquot.sub (tendsto_const_nhds (x := (1 : ℝ)))).abs).const_mul
      (Real.exp ((Real.pi ^ 2 / 4) * M))
  exact ⟨htail, hlog, hquot, hadd⟩

-- Exact whole-sequence limit criterion, including exclusion of L≤0.
theorem boundary_tendsto_iff (n_ : ℕ → ℕ) (h_ : ℕ → ℝ)
    (hh : Tendsto h_ atTop atTop)
    (hscale2 : Tendsto
      (fun k : ℕ => (n_ k : ℝ) / (h_ k) ^ 2) atTop atTop)
    (hscale3 : ∃ M : ℝ, 0 < M ∧
      ∃ K_M : ℕ, ∀ k : ℕ, K_M ≤ k →
        (n_ k : ℝ) / (h_ k) ^ 3 ≤ M) (L : ℝ) :
    Tendsto (fun k : ℕ => ratio (n_ k) (h_ k)) atTop (𝓝 L) ↔
      1 ≤ L ∧
      Tendsto (fun k : ℕ =>
        ((n_ k : ℝ) / (h_ k) ^ 3) * integerIndicator (h_ k))
        atTop (𝓝 ((4 / Real.pi ^ 2) * Real.log L)) := by
  classical
  have hm := boundary_main n_ h_ hh hscale2 hscale3
  let t : ℕ → ℝ := fun k => ((n_ k : ℝ) / (h_ k) ^ 3) * integerIndicator (h_ k)
  let a : ℝ := Real.pi ^ 2 / 4
  have ha : 0 < a := by dsimp [a]; positivity
  have hp : Real.pi ^ 2 ≠ 0 := by positivity
  have herr : Tendsto (fun k => ratio (n_ k) (h_ k) - Real.exp (a * t k))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [a, t, mul_assoc] using hm.2.2.2
  have htpos : ∀ᶠ k : ℕ in atTop, 0 ≤ t k := by
    filter_upwards [hh.eventually_ge_atTop (2 : ℝ)] with k hk
    have hj := (boundary_gap (h_ k) (by linarith)).2
    rcases hj with hj | hj <;> simp only [t, hj, mul_zero, mul_one] <;> positivity
  constructor
  · intro hR
    have hF : Tendsto (fun k => Real.exp (a * t k)) atTop (𝓝 L) := by
      have hx := hR.sub herr
      simpa only [sub_sub_cancel, sub_zero] using hx
    have hL : 1 ≤ L := by
      apply ge_of_tendsto hF
      filter_upwards [htpos] with k hk
      exact Real.one_le_exp (mul_nonneg ha.le hk)
    have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
    have hlog := (Real.continuousAt_log hLp.ne').tendsto.comp hF
    have ht := hlog.const_mul (4 / Real.pi ^ 2)
    refine ⟨hL, ?_⟩
    convert ht using 1
    ext k
    simp only [Function.comp_def, Real.log_exp]
    dsimp only [a, t]
    field_simp
  · rintro ⟨hL, ht⟩
    have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
    have hA : Tendsto (fun k => a * t k) atTop (𝓝 (Real.log L)) := by
      have hx := ht.const_mul a
      convert hx using 1 <;> dsimp only [a] <;> field_simp
    have hF := (Real.continuous_exp.tendsto (Real.log L)).comp hA
    have hx := herr.add hF
    simpa only [sub_add_cancel, Real.exp_log hLp, zero_add,
      Function.comp_def] using hx

end Shao.OQ4.RademacherStrictWeakBoundary
end
