import Shao.OQ3.PositiveBoxSimultaneousDiophantine
import Shao.OQ3.RealParameterDiophantine
import Shao.OQ3.SymmetricEightAtomDiophantine

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem exists_symmetric_eight_atom_weak_cramer :
    ∃ a : Fin 8 → ℝ, a 0 = 1 ∧ StrictMono a ∧ (∀ i, 0 < a i) ∧
      let A : Fin (8 + 8) → ℝ := Fin.append a (fun i => -a i)
      let mu : Measure ℝ := Measure.sum fun k : Fin (8 + 8) =>
        ENNReal.ofReal ((1 : ℝ) / 16) • Measure.dirac (A k)
      IsProbabilityMeasure mu ∧ Integrable (fun x : ℝ => x) mu ∧
        (∫ x : ℝ, x ∂mu) = 0 ∧ (∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ x ∂mu, |x| ≤ B) ∧
        ∃ c : ℝ, 0 < c ∧ ∃ R : ℝ, 0 ≤ R ∧ ∀ xi eta : ℝ,
          R < Real.sqrt (xi ^ 2 + eta ^ 2) →
          ‖jointCharacteristic mu xi eta‖ ≤
            1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-(3 : ℝ) / 8) := by
  classical
  obtain ⟨r, hr, hLi, hQi⟩ := exists_positive_box_simultaneous_diophantine
  let a : Fin 8 → ℝ := Fin.cons 1 r
  have ha0 : a 0 = 1 := rfl
  have hasucc (j : Fin 7) : a j.succ = r j := rfl
  have hr0 : 2 < r 0 := by simpa using (hr 0).1
  have hpos : ∀ i, 0 < a i := by
    intro i
    refine Fin.cases (by rw [ha0]; norm_num) (fun j => ?_) i
    rw [hasucc]
    have hn : (0 : ℝ) ≤ j.val := by positivity
    linarith [(hr j).1]
  have hmono : StrictMono a := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => omega
      | succ j =>
        rw [ha0, hasucc]
        have hn : (0 : ℝ) ≤ j.val := by positivity
        linarith [(hr j).1]
    | succ i =>
      cases j using Fin.cases with
      | zero => omega
      | succ j =>
        rw [hasucc, hasucc]
        have hval : i.val + 1 ≤ j.val := by omega
        have hvalR : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast hval
        linarith [(hr i).2, (hr j).1]
  let alphaL : Fin 8 → ℝ := fun i => 2 * a i
  let alphaQ : Fin 7 → ℝ := fun j => 2 * ((a j.succ) ^ 2 - (a 0) ^ 2)
  have hL0 : 0 < alphaL 0 := by dsimp [alphaL]; rw [ha0]; norm_num
  have hQ0 : 0 < alphaQ 0 := by dsimp [alphaQ]; rw [hasucc, ha0]; nlinarith
  have hden : r 0 ^ 2 - 1 ≠ 0 := by nlinarith
  have hLratio (j : Fin 7) : alphaL j.succ / alphaL 0 = r j := by
    dsimp [alphaL]
    rw [hasucc, ha0]
    ring
  have hQratio (j : Fin 6) : alphaQ j.succ / alphaQ 0 =
      (r j.succ ^ 2 - 1) / (r 0 ^ 2 - 1) := by
    dsimp [alphaQ]
    simp only [hasucc, ha0, one_pow]
    field_simp [hden] <;> ring
  obtain ⟨QL, hQL, hLi⟩ := hLi
  obtain ⟨QQ, hQQ, hQi⟩ := hQi
  have hLInteger : ∀ q : ℤ, QL < |(q : ℝ)| → ∃ j : Fin 7, ∀ p : ℤ,
      (1 : ℝ) * Real.rpow |(q : ℝ)| (-(3 : ℝ) / 16) ≤
        |(q : ℝ) * (alphaL j.succ / alphaL 0) - (p : ℝ)| := by
    intro q hq
    obtain ⟨j, hj⟩ := hLi q hq
    refine ⟨j, ?_⟩
    intro p
    simpa only [hLratio, one_mul] using hj p
  have hQInteger : ∀ q : ℤ, QQ < |(q : ℝ)| → ∃ j : Fin 6, ∀ p : ℤ,
      (1 : ℝ) * Real.rpow |(q : ℝ)| (-(3 : ℝ) / 16) ≤
        |(q : ℝ) * (alphaQ j.succ / alphaQ 0) - (p : ℝ)| := by
    intro q hq
    obtain ⟨j, hj⟩ := hQi q hq
    refine ⟨j, ?_⟩
    intro p
    simpa only [hQratio, one_mul] using hj p
  obtain ⟨cL, hcL, TL, hTL, hL⟩ :=
    real_parameter_diophantine_of_integer_ratios 7 alphaL hL0 1 QL (by norm_num) hQL hLInteger
  obtain ⟨cQ, hcQ, TQ, hTQ, hQ⟩ :=
    real_parameter_diophantine_of_integer_ratios 6 alphaQ hQ0 1 QQ (by norm_num) hQQ hQInteger
  have hLinear : ∀ t : ℝ, TL < |t| → ∃ i : Fin 8, ∀ k : ℤ,
      cL * Real.rpow |t| (-(3 : ℝ) / 16) ≤
        |2 * t * a i - 2 * Real.pi * (k : ℝ)| := by
    intro t ht
    obtain ⟨i, hi⟩ := hL t ht
    refine ⟨i, ?_⟩
    intro k
    have hid : t * alphaL i = 2 * t * a i := by dsimp [alphaL]; ring
    simpa only [hid] using hi k
  have hQuadratic : ∀ t : ℝ, TQ < |t| → ∃ j : Fin 7, ∀ k : ℤ,
      cQ * Real.rpow |t| (-(3 : ℝ) / 16) ≤
        |2 * t * (a j.succ) ^ 2 - 2 * t * (a 0) ^ 2 - 2 * Real.pi * (k : ℝ)| := by
    intro t ht
    obtain ⟨j, hj⟩ := hQ t ht
    refine ⟨j, ?_⟩
    intro k
    have hid : t * alphaQ j - 2 * Real.pi * (k : ℝ) =
        2 * t * (a j.succ) ^ 2 - 2 * t * (a 0) ^ 2 - 2 * Real.pi * (k : ℝ) := by
      dsimp [alphaQ]
      ring
    simpa only [hid] using hj k
  have hlaw := symmetric_eight_atom_law_and_phase_gap a
  dsimp only at hlaw
  refine ⟨a, ha0, hmono, hpos, ?_⟩
  dsimp only
  refine ⟨hlaw.1, hlaw.2.1, hlaw.2.2.1, ?_, ?_⟩
  · exact ⟨∑ i : Fin 8, |a i|, hlaw.2.2.2.1, hlaw.2.2.2.2.1⟩
  · exact symmetric_eight_atom_weak_cramer_of_diophantine_bounds
      a cL cQ TL TQ hcL hcQ hTL hTQ hLinear hQuadratic

end
end Shao.OQ3
