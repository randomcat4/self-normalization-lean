/- Context196 finite-unit source candidate, V2 freeze.
All 13 frozen private helpers and both exact finite public bridges have candidate bodies.
The full module remains incomplete: binomial_payments, binomial_halves,
uniform_log_pair and critical_limits are absent, preserved in remaining-frozen-declarations.
No Lean or native gate has been run. No formal credit is claimed.
-/

import Shao.OQ4.RademacherS4Assembly
import Shao.Probability.BerryEsseen
import Shao.Probability.BrownianFirstTerm
import Shao.Probability.MeasurablePath
import Shao.Basic.ClosedSurvival
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Order.Floor

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology

universe u

namespace Shao.OQ4.SparseCriticalDenominator

def law : Measure ℝ :=
  (3 / 4 : ℝ≥0∞) • Measure.dirac (0 : ℝ) +
    (1 / 8 : ℝ≥0∞) • Measure.dirac (2 : ℝ) +
    (1 / 8 : ℝ≥0∞) • Measure.dirac (-2 : ℝ)

instance law_isProbabilityMeasure : IsProbabilityMeasure law := by
  constructor
  norm_num [law]
  all_goals
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    repeat' rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num [ENNReal.toReal_div, ENNReal.toReal_inv]

def pathLaw (n : ℕ) : Measure (Shao.Path n) :=
  Measure.pi (fun _ : Fin n => law)

def count {n : ℕ} (a : Shao.Path n) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => a i ≠ 0)).card

def weight (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * (1 / 4 : ℝ) ^ k * (3 / 4 : ℝ) ^ (n - k)

def selfEvent (n : ℕ) (s : ℝ) : Set (Shao.Path n) :=
  {a | ∀ j : ℕ, j ≤ n →
    |Shao.prefixSum a j| ≤ s * Real.sqrt (Shao.energy a)}

def detEvent (n : ℕ) (s : ℝ) : Set (Shao.Path n) :=
  @Shao.closedStrip n (s * Real.sqrt (n : ℝ))

def time (m : ℕ) : ℕ := (2 * m) ^ 3

def meanIndex (m : ℕ) : ℕ := 2 * m ^ 3

def criticalX (m : ℕ) : ℝ :=
  Real.rpow (time m : ℝ) (-((1 : ℝ) / 6))

def randomHeight (m k : ℕ) : ℝ :=
  criticalX m * Real.sqrt (k : ℝ)

def phaseExponent (m k : ℕ) : ℝ :=
  (Real.pi ^ 2 / 4) * ((k : ℝ) / randomHeight m k ^ 3) *
    ((⌊randomHeight m k⌋₊ : ℝ) + 1 - randomHeight m k)

def baseline {Ω : Type u} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (m : ℕ) : ℝ :=
  Shao.Probability.BrownianSup.probability B P hB (criticalX m)

def randomRatio {Ω : Type u} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (m : ℕ) : ℝ :=
  (pathLaw (time m)).real (selfEvent (time m) (criticalX m)) /
    baseline B P hB m

def detRatio {Ω : Type u} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (m : ℕ) : ℝ :=
  (pathLaw (time m)).real (detEvent (time m) (criticalX m)) /
    baseline B P hB m

/- Context196: frozen V2 finite helpers. Unexecuted Lean source candidate. -/

private def jointEvent (n k : ℕ) (h x : ℝ) : Set (Shao.Path n) :=
  {a | count a = k ∧ |x| ≤ h ∧
    a ∈ Shao.OQ4.shiftedClosedSurvival (n := n) (2 * h) (2 * x)}

private def jointMass (n k : ℕ) (h x : ℝ) : ℝ :=
  (pathLaw n).real (jointEvent n k h x)

private def closedRadMass (h : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  if |x| ≤ h then
    Shao.OQ4.killedMass Shao.OQ4.RademacherCosine.law h k x
  else 0

private theorem measurable_count (n : ℕ) :
    Measurable (@count n) := by
  classical
  have hsum (a : Shao.Path n) :
      count a = ∑ i : Fin n, if a i ≠ 0 then (1 : ℕ) else 0 := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, smul_eq_mul, mul_one, count]
  have hi (i : Fin n) : Measurable
      (fun a : Shao.Path n => if a i ≠ 0 then (1 : ℕ) else 0) := by
    exact Measurable.ite
      (isClosed_eq (continuous_apply i) continuous_const).measurableSet.compl
      measurable_const measurable_const
  convert Finset.measurable_sum (Finset.univ : Finset (Fin n)) (fun i _ => hi i) using 1
  funext a
  exact hsum a

private theorem count_cons (n : ℕ) (y : ℝ) (a : Shao.Path n) :
    count (Fin.cons y a) = count a + (if y ≠ 0 then 1 else 0) := by
  classical
  have hsum (r : ℕ) (b : Shao.Path r) :
      count b = ∑ i : Fin r, if b i ≠ 0 then (1 : ℕ) else 0 := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, smul_eq_mul, mul_one, count]
  rw [hsum, Fin.sum_univ_succ, hsum]
  simp only [Fin.cons_zero, Fin.cons_succ]
  omega

private theorem pathLaw_real_cons (n : ℕ) (A : Set (Shao.Path (n + 1)))
    (hA : MeasurableSet A) :
    (pathLaw (n + 1)).real A =
      (3 / 4 : ℝ) * (pathLaw n).real
        ((fun a : Shao.Path n => Fin.cons (0 : ℝ) a) ⁻¹' A) +
      (1 / 8 : ℝ) * (pathLaw n).real
        ((fun a : Shao.Path n => Fin.cons (2 : ℝ) a) ⁻¹' A) +
      (1 / 8 : ℝ) * (pathLaw n).real
        ((fun a : Shao.Path n => Fin.cons (-2 : ℝ) a) ⁻¹' A) := by
  classical
  letI : IsProbabilityMeasure (pathLaw n) := by
    dsimp only [pathLaw]
    infer_instance
  have hmcons (y : ℝ) : Measurable (fun a : Shao.Path n => (Fin.cons y a : Shao.Path (n + 1))) := by
    apply measurable_pi_iff.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.cons_zero] using
        (measurable_const : Measurable (fun _ : Shao.Path n => y))
    · simpa only [Fin.cons_succ] using
        (measurable_pi_apply j : Measurable (fun a : Shao.Path n => a j))
  let F : Shao.Path (n + 1) → ℝ≥0∞ := A.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hA
  have hsection (y : ℝ) :
      (∫⁻ a : Shao.Path n, F (Fin.cons y a) ∂pathLaw n) =
        pathLaw n ((fun a : Shao.Path n => Fin.cons y a) ⁻¹' A) := by
    change (∫⁻ a : Shao.Path n,
      ((fun b : Shao.Path n => Fin.cons y b) ⁻¹' A).indicator (fun _ => 1) a
        ∂pathLaw n) = _
    rw [lintegral_indicator (hA.preimage (hmcons y))]
    simp
  have hrec :
      pathLaw (n + 1) A =
        (3 / 4 : ℝ≥0∞) * pathLaw n
          ((fun a : Shao.Path n => Fin.cons (0 : ℝ) a) ⁻¹' A) +
        (1 / 8 : ℝ≥0∞) * pathLaw n
          ((fun a : Shao.Path n => Fin.cons (2 : ℝ) a) ⁻¹' A) +
        (1 / 8 : ℝ≥0∞) * pathLaw n
          ((fun a : Shao.Path n => Fin.cons (-2 : ℝ) a) ⁻¹' A) := by
    calc
      pathLaw (n + 1) A = ∫⁻ a, F a ∂pathLaw (n + 1) := by
        dsimp only [F]
        rw [lintegral_indicator hA]
        simp
      _ = ∫⁻ y, ∫⁻ a : Shao.Path n, F (Fin.cons y a) ∂pathLaw n ∂law :=
        Shao.OQ4.path_pi_lintegral_cons law n F hF
      _ = _ := by
        rw [law, lintegral_add_measure, lintegral_add_measure,
          lintegral_smul_measure, lintegral_smul_measure, lintegral_smul_measure]
        simp only [lintegral_dirac, smul_eq_mul, hsection]
  change (pathLaw (n + 1) A).toReal = _
  rw [hrec, ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_div, measureReal_def]

private theorem measurableSet_jointEvent (n k : ℕ) (h x : ℝ) :
    MeasurableSet (jointEvent n k h x) := by
  have hc : MeasurableSet {a : Shao.Path n | count a = k} :=
    (measurable_count n) (measurableSet_singleton k)
  have hx : MeasurableSet {a : Shao.Path n | |x| ≤ h} := by
    by_cases hx : |x| ≤ h <;> simp [hx]
  change MeasurableSet
    ({a : Shao.Path n | count a = k} ∩
      ({a : Shao.Path n | |x| ≤ h} ∩
        Shao.OQ4.shiftedClosedSurvival (n := n) (2 * h) (2 * x)))
  exact hc.inter (hx.inter (Shao.OQ4.measurableSet_shiftedClosedSurvival n _ _))

private theorem jointEvent_cons (n k : ℕ) (y h x : ℝ) (a : Shao.Path n) :
    Fin.cons y a ∈ jointEvent (n + 1) (k + (if y ≠ 0 then 1 else 0)) h x ↔
      |x| ≤ h ∧ a ∈ jointEvent n k h (x + y / 2) := by
  have hz : 2 * (x + y / 2) = 2 * x + y := by ring
  change
    (count (Fin.cons y a) = k + (if y ≠ 0 then 1 else 0) ∧
      |x| ≤ h ∧ Fin.cons y a ∈
        Shao.OQ4.shiftedClosedSurvival (2 * h) (2 * x)) ↔
    (|x| ≤ h ∧ count a = k ∧ |x + y / 2| ≤ h ∧
      a ∈ Shao.OQ4.shiftedClosedSurvival (2 * h) (2 * (x + y / 2)))
  rw [count_cons, Nat.add_right_cancel_iff, Shao.OQ4.shiftedClosedSurvival_cons]
  simp only [← hz, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  constructor
  · rintro ⟨hc, hx, hy, ha⟩
    exact ⟨hx, hc, by linarith, ha⟩
  · rintro ⟨hx, hc, hy, ha⟩
    exact ⟨hc, hx, by linarith, ha⟩

private theorem jointMass_succ_zero (n : ℕ) (h x : ℝ) :
    jointMass (n + 1) 0 h x = (3 / 4 : ℝ) * jointMass n 0 h x := by
  have hz :
      (fun a : Shao.Path n => Fin.cons (0 : ℝ) a) ⁻¹'
        jointEvent (n + 1) 0 h x = jointEvent n 0 h x := by
    ext a
    simpa [jointEvent, and_assoc, and_left_comm, and_comm] using
      (jointEvent_cons n 0 0 h x a)
  have hp :
      (fun a : Shao.Path n => Fin.cons (2 : ℝ) a) ⁻¹'
        jointEvent (n + 1) 0 h x = ∅ := by
    ext a
    simp [jointEvent, count_cons]
  have hn :
      (fun a : Shao.Path n => Fin.cons (-2 : ℝ) a) ⁻¹'
        jointEvent (n + 1) 0 h x = ∅ := by
    ext a
    simp [jointEvent, count_cons]
  unfold jointMass
  rw [pathLaw_real_cons n _ (measurableSet_jointEvent (n + 1) 0 h x), hz, hp, hn]
  simp

private theorem jointMass_succ (n k : ℕ) (h x : ℝ) :
    jointMass (n + 1) (k + 1) h x =
      if |x| ≤ h then
        (3 / 4 : ℝ) * jointMass n (k + 1) h x +
        (1 / 8 : ℝ) * jointMass n k h (x + 1) +
        (1 / 8 : ℝ) * jointMass n k h (x - 1)
      else 0 := by
  by_cases hx : |x| ≤ h
  · have hz :
        (fun a : Shao.Path n => Fin.cons (0 : ℝ) a) ⁻¹'
          jointEvent (n + 1) (k + 1) h x = jointEvent n (k + 1) h x := by
      ext a
      simpa [hx] using (jointEvent_cons n (k + 1) 0 h x a)
    have hp :
        (fun a : Shao.Path n => Fin.cons (2 : ℝ) a) ⁻¹'
          jointEvent (n + 1) (k + 1) h x = jointEvent n k h (x + 1) := by
      ext a
      simpa [hx] using (jointEvent_cons n k 2 h x a)
    have hn :
        (fun a : Shao.Path n => Fin.cons (-2 : ℝ) a) ⁻¹'
          jointEvent (n + 1) (k + 1) h x = jointEvent n k h (x - 1) := by
      ext a
      simpa [hx, sub_eq_add_neg] using (jointEvent_cons n k (-2) h x a)
    unfold jointMass
    rw [if_pos hx, pathLaw_real_cons n _
      (measurableSet_jointEvent (n + 1) (k + 1) h x), hz, hp, hn]
  · have he : jointEvent (n + 1) (k + 1) h x = ∅ := by
      ext a
      simp [jointEvent, hx]
    simp only [jointMass, he, measureReal_empty, if_neg hx]

private theorem closedRadMass_succ (h : ℝ) (k : ℕ) (x : ℝ) :
    closedRadMass h (k + 1) x =
      if |x| ≤ h then
        (closedRadMass h k (x + 1) + closedRadMass h k (x - 1)) / 2
      else 0 := by
  have hhalf : Shao.OQ4.RademacherCosine.halfENNReal ≠ ⊤ := by
    norm_num [Shao.OQ4.RademacherCosine.halfENNReal]
  have hreal : Shao.OQ4.RademacherCosine.halfENNReal.toReal = (1 / 2 : ℝ) := by
    norm_num [Shao.OQ4.RademacherCosine.halfENNReal, ENNReal.toReal_div]
  have hp (f : ℝ → ℝ) : Integrable f
      (Shao.OQ4.RademacherCosine.halfENNReal • Measure.dirac (1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure hhalf
  have hn (f : ℝ → ℝ) : Integrable f
      (Shao.OQ4.RademacherCosine.halfENNReal • Measure.dirac (-1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure hhalf
  have hformula (f : ℝ → ℝ) :
      (∫ y : ℝ, f y ∂Shao.OQ4.RademacherCosine.law) =
        (1 / 2 : ℝ) * f 1 + (1 / 2 : ℝ) * f (-1) := by
    rw [Shao.OQ4.RademacherCosine.law, integral_add_measure (hp f) (hn f),
      integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac, hreal]
    rfl
  have hm : Measurable (Shao.OQ4.killedMass Shao.OQ4.RademacherCosine.law h k) :=
    Shao.OQ4.killedAction_measurable _ h k (fun _ => 1) measurable_const
  have hb : ∃ M : ℝ, ∀ w : ℝ,
      |Shao.OQ4.killedMass Shao.OQ4.RademacherCosine.law h k w| ≤ M := by
    refine ⟨1, fun w => ?_⟩
    rw [abs_of_nonneg (Shao.OQ4.killedMass_nonneg _ h k w)]
    exact Shao.OQ4.killedMass_le_one _ h k w
  have hkernel : Shao.OQ4.killedMass Shao.OQ4.RademacherCosine.law h (k + 1) x =
      ∫ y : ℝ, if |x + y| ≤ h then
        Shao.OQ4.killedMass Shao.OQ4.RademacherCosine.law h k (x + y) else 0
          ∂Shao.OQ4.RademacherCosine.law := by
    calc
      _ = Shao.OQ4.killedAction Shao.OQ4.RademacherCosine.law h 1
          (Shao.OQ4.killedMass Shao.OQ4.RademacherCosine.law h k) x := by
        change Shao.OQ4.killedAction Shao.OQ4.RademacherCosine.law h (k + 1) (fun _ => 1) x =
          Shao.OQ4.killedAction Shao.OQ4.RademacherCosine.law h 1
            (fun z => Shao.OQ4.killedAction Shao.OQ4.RademacherCosine.law h k (fun _ => 1) z) x
        simpa only [Nat.add_comm] using
          (Shao.OQ4.killedAction_semigroup Shao.OQ4.RademacherCosine.law h
            1 k x (fun _ => 1) measurable_const ⟨1, by simp⟩)
      _ = _ := (Shao.OQ4.killedAction_one Shao.OQ4.RademacherCosine.law h
        x _ hm hb).2
  have hrec : Shao.OQ4.killedMass Shao.OQ4.RademacherCosine.law h (k + 1) x =
      (closedRadMass h k (x + 1) + closedRadMass h k (x - 1)) / 2 := by
    rw [hkernel, hformula]
    simp only [closedRadMass, sub_eq_add_neg]
    ring
  by_cases hx : |x| ≤ h
  · simpa only [closedRadMass, if_pos hx] using hrec
  · simp only [closedRadMass, if_neg hx]

private theorem weight_succ (n k : ℕ) :
    weight (n + 1) (k + 1) =
      (3 / 4 : ℝ) * weight n (k + 1) + (1 / 4 : ℝ) * weight n k := by
  rcases lt_trichotomy k n with hkn | hkn | hkn
  · have hsub : n + 1 - (k + 1) = n - k := by omega
    have hexp : n - k = (n - (k + 1)) + 1 := by omega
    simp only [weight, Nat.choose_succ_succ, Nat.cast_add]
    rw [hsub, hexp]
    simp only [pow_succ]
    ring
  · subst k
    simp only [weight, Nat.choose_self, Nat.cast_one, Nat.sub_self,
      Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n), Nat.cast_zero,
      zero_mul, mul_zero, zero_add, pow_zero, mul_one, pow_succ]
    ring
  · have h1 : n < k + 1 := by omega
    have h2 : n + 1 < k + 1 := by omega
    simp only [weight, Nat.choose_eq_zero_of_lt hkn,
      Nat.choose_eq_zero_of_lt h1, Nat.choose_eq_zero_of_lt h2,
      Nat.cast_zero, zero_mul, mul_zero, zero_add]

private theorem jointMass_factorization (n k : ℕ) (h x : ℝ) :
    jointMass n k h x = weight n k * closedRadMass h k x := by
  induction n generalizing k h x with
  | zero =>
    cases k with
    | zero =>
      by_cases hx : |x| ≤ h <;>
        simp [jointMass, jointEvent, count, weight, closedRadMass, pathLaw,
          Shao.OQ4.shiftedClosedSurvival_zero, Shao.OQ4.killedMass,
          Shao.OQ4.killedAction_zero, hx]
    | succ k =>
      have he : jointEvent 0 (k + 1) h x = ∅ := by
        ext a
        simp [jointEvent, count]
      simp [jointMass, he, weight]
  | succ n ih =>
    cases k with
    | zero =>
      have hw : weight (n + 1) 0 = (3 / 4 : ℝ) * weight n 0 := by
        simp only [weight, Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one,
          Nat.sub_zero, pow_succ]
        ring
      rw [jointMass_succ_zero, ih, hw]
      ring
    | succ k =>
      rw [jointMass_succ, ih, ih, ih, weight_succ]
      by_cases hx : |x| ≤ h
      · rw [if_pos hx]
        have hr := closedRadMass_succ h k x
        rw [if_pos hx] at hr
        simp only [hr]
        ring
      · simp only [if_neg hx, closedRadMass, if_neg hx, mul_zero]


theorem law_moments :
    Integrable (fun z : ℝ => |z| ^ 3) law ∧
    (∫ z : ℝ, z ∂law) = 0 ∧
    (∫ z : ℝ, z ^ 2 ∂law) = 1 ∧
    (∫ z : ℝ, |z| ^ 3 ∂law) = 2 ∧
    variance (id : ℝ → ℝ) law = 1 := by
  have h0 (f : ℝ → ℝ) :
      Integrable f ((3 / 4 : ℝ≥0∞) • Measure.dirac (0 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by finiteness)
  have hp (f : ℝ → ℝ) :
      Integrable f ((1 / 8 : ℝ≥0∞) • Measure.dirac (2 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by finiteness)
  have hn (f : ℝ → ℝ) :
      Integrable f ((1 / 8 : ℝ≥0∞) • Measure.dirac (-2 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by finiteness)
  have hi (f : ℝ → ℝ) : Integrable f law := by
    rw [law]
    exact ((h0 f).add_measure (hp f)).add_measure (hn f)
  have hf (f : ℝ → ℝ) :
      (∫ z : ℝ, f z ∂law) =
        (3 / 4 : ℝ) * f 0 + (1 / 8 : ℝ) * f 2 + (1 / 8 : ℝ) * f (-2) := by
    rw [law, integral_add_measure ((h0 f).add_measure (hp f)) (hn f),
      integral_add_measure (h0 f) (hp f),
      integral_smul_measure, integral_smul_measure, integral_smul_measure,
      integral_dirac, integral_dirac, integral_dirac]
    norm_num [ENNReal.toReal_div]
  have hmean : (∫ z : ℝ, z ∂law) = 0 := by
    rw [hf]
    norm_num
  have hsecond : (∫ z : ℝ, z ^ 2 ∂law) = 1 := by
    rw [hf]
    norm_num
  have hthird : (∫ z : ℝ, |z| ^ 3 ∂law) = 2 := by
    rw [hf]
    norm_num
  have hvariance : variance (id : ℝ → ℝ) law = 1 := by
    rw [variance_eq_integral measurable_id.aemeasurable]
    change (∫ z : ℝ, (z - ∫ y : ℝ, y ∂law) ^ 2 ∂law) = 1
    simpa only [hmean, sub_zero] using hsecond
  exact ⟨hi _, hmean, hsecond, hthird, hvariance⟩

theorem critical_scale (m : ℕ) (hm : 1 ≤ m) :
    time m = 8 * m ^ 3 ∧
    time m = 4 * meanIndex m ∧
    0 < criticalX m ∧
    criticalX m = 1 / Real.sqrt (2 * (m : ℝ)) ∧
    criticalX m * Real.sqrt (time m : ℝ) / 2 = (m : ℝ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hb : (0 : ℝ) < 2 * (m : ℝ) := by positivity
  have ht : time m = 8 * m ^ 3 := by
    dsimp only [time]
    ring
  have htmean : time m = 4 * meanIndex m := by
    rw [ht, meanIndex]
    ring
  have htR : (time m : ℝ) = (2 * (m : ℝ)) ^ 3 := by
    simp only [time, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
  have hx : criticalX m = 1 / Real.sqrt (2 * (m : ℝ)) := by
    unfold criticalX
    rw [htR]
    change (((2 * (m : ℝ)) ^ 3 : ℝ) ^ (-((1 : ℝ) / 6))) = _
    rw [← Real.rpow_natCast_mul hb.le 3 (-((1 : ℝ) / 6))]
    norm_num only [show (3 : ℝ) * (-((1 : ℝ) / 6)) = -((1 : ℝ) / 2) by norm_num]
    rw [Real.rpow_neg hb.le, ← Real.sqrt_eq_rpow, one_div]
  have hs : 0 < Real.sqrt (2 * (m : ℝ)) := Real.sqrt_pos.2 hb
  have hroot : Real.sqrt (time m : ℝ) =
      2 * (m : ℝ) * Real.sqrt (2 * (m : ℝ)) := by
    have hsq : (time m : ℝ) = (2 * (m : ℝ)) ^ 2 * (2 * (m : ℝ)) := by
      rw [htR]
      ring
    rw [hsq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hb.le]
  refine ⟨ht, htmean, ?_, hx, ?_⟩
  · rw [hx]
    positivity
  · rw [hx, hroot]
    field_simp [hs.ne'] <;> ring

theorem actual_event_bridges (n : ℕ) (hn : 0 < n)
    (s : ℝ) (hs : 0 ≤ s) (a : Shao.Path n) :
    (a ∈ selfEvent n s ↔
      Shao.absMax a hn ≤ s * Real.sqrt (Shao.energy a)) ∧
    (a ∈ detEvent n s ↔
      Shao.absMax a hn ≤ s * Real.sqrt (n : ℝ)) ∧
    (Shao.energy a = 0 → a ∈ selfEvent n s ∧ a ∈ detEvent n s) := by
  have hself : a ∈ selfEvent n s ↔
      Shao.absMax a hn ≤ s * Real.sqrt (Shao.energy a) :=
    Shao.mem_closedStrip_iff_absMax_le a hn _
      (mul_nonneg hs (Real.sqrt_nonneg _))
  have hdet : a ∈ detEvent n s ↔
      Shao.absMax a hn ≤ s * Real.sqrt (n : ℝ) :=
    Shao.mem_closedStrip_iff_absMax_le a hn _
      (mul_nonneg hs (Real.sqrt_nonneg _))
  refine ⟨hself, hdet, ?_⟩
  intro hzero
  constructor
  · intro j _
    simp only [Shao.prefixSum_eq_zero_of_energy_eq_zero a hzero j,
      abs_zero, hzero, Real.sqrt_zero, mul_zero, le_refl]
  · intro j _
    simpa only [Shao.prefixSum_eq_zero_of_energy_eq_zero a hzero j, abs_zero] using
      mul_nonneg hs (Real.sqrt_nonneg (n : ℝ))

/- Context196: finite public proof bodies, preserving frozen V2 types. -/

theorem count_law (n : ℕ) :
    (∀ k : ℕ, (pathLaw n).real {a : Shao.Path n | count a = k} =
      weight n k) ∧
    (∀ᵐ a : Shao.Path n ∂pathLaw n,
      Shao.energy a = 4 * (count a : ℝ)) := by
  classical
  have hmset (r k : ℕ) : MeasurableSet {a : Shao.Path r | count a = k} :=
    (measurable_count r) (measurableSet_singleton k)
  have hwzero (r : ℕ) : weight (r + 1) 0 = (3 / 4 : ℝ) * weight r 0 := by
    simp only [weight, Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one,
      Nat.sub_zero, pow_succ]
    ring
  have hdist (r : ℕ) : ∀ k : ℕ,
      (pathLaw r).real {a : Shao.Path r | count a = k} = weight r k := by
    induction r with
    | zero =>
      intro k
      cases k with
      | zero => simp [count, weight, pathLaw]
      | succ k =>
        have he : {a : Shao.Path 0 | count a = k + 1} = ∅ := by
          ext a
          simp [count]
        rw [he]
        simp [weight]
    | succ r ih =>
      intro k
      have hz : (fun a : Shao.Path r => Fin.cons (0 : ℝ) a) ⁻¹'
          {a : Shao.Path (r + 1) | count a = k} =
            {a : Shao.Path r | count a = k} := by
        ext a
        simp [count_cons]
      cases k with
      | zero =>
        have hp : (fun a : Shao.Path r => Fin.cons (2 : ℝ) a) ⁻¹'
            {a : Shao.Path (r + 1) | count a = 0} = ∅ := by
          ext a
          simp [count_cons]
        have hn : (fun a : Shao.Path r => Fin.cons (-2 : ℝ) a) ⁻¹'
            {a : Shao.Path (r + 1) | count a = 0} = ∅ := by
          ext a
          simp [count_cons]
        rw [pathLaw_real_cons r _ (hmset (r + 1) 0), hz, hp, hn, ih 0, hwzero]
        simp
      | succ k =>
        have hp : (fun a : Shao.Path r => Fin.cons (2 : ℝ) a) ⁻¹'
            {a : Shao.Path (r + 1) | count a = k + 1} =
              {a : Shao.Path r | count a = k} := by
          ext a
          simp [count_cons]
        have hn : (fun a : Shao.Path r => Fin.cons (-2 : ℝ) a) ⁻¹'
            {a : Shao.Path (r + 1) | count a = k + 1} =
              {a : Shao.Path r | count a = k} := by
          ext a
          simp [count_cons]
        rw [pathLaw_real_cons r _ (hmset (r + 1) (k + 1)), hz, hp, hn,
          ih (k + 1), ih k, weight_succ]
        ring
  have hsingle : ∀ᵐ z : ℝ ∂law, z = 0 ∨ z = 2 ∨ z = -2 := by
    rw [ae_iff]
    simp [law, Measure.add_apply, Measure.smul_apply]
  have hcoord (i : Fin n) :
      ∀ᵐ a : Shao.Path n ∂pathLaw n, a i = 0 ∨ a i = 2 ∨ a i = -2 := by
    rw [ae_iff] at hsingle ⊢
    exact Measure.pi_eval_preimage_null (fun _ : Fin n => law) (i := i) hsingle
  have hall : ∀ᵐ a : Shao.Path n ∂pathLaw n,
      ∀ i : Fin n, a i = 0 ∨ a i = 2 ∨ a i = -2 :=
    ae_all_iff.2 hcoord
  refine ⟨hdist n, ?_⟩
  filter_upwards [hall] with a ha
  have hsq (i : Fin n) : (a i) ^ 2 = if a i ≠ 0 then (4 : ℝ) else 0 := by
    rcases ha i with h | h | h <;> norm_num [h]
  calc
    Shao.energy a =
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => a i ≠ 0), (4 : ℝ) := by
      simp only [Shao.energy, hsq, Finset.sum_filter]
    _ = 4 * (count a : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul, count]
      ring

theorem conditional_strip_mass (n k : ℕ) (hk : k ≤ n)
    (h : ℝ) (hh : 0 ≤ h) :
    (pathLaw n).real
      ({a : Shao.Path n | count a = k} ∩ @Shao.closedStrip n (2 * h)) =
    weight n k * RademacherS4Assembly.p k h := by
  have he : jointEvent n k h 0 =
      {a : Shao.Path n | count a = k} ∩ @Shao.closedStrip n (2 * h) := by
    ext a
    simp only [jointEvent, Set.mem_setOf_eq, Set.mem_inter_iff, abs_zero,
      hh, true_and, mul_zero,
      Shao.OQ4.shiftedClosedSurvival_eq_closedStrip n (2 * h) (by linarith)]
  have hr : closedRadMass h k 0 = RademacherS4Assembly.p k h := by
    rw [closedRadMass, if_pos (by simpa only [abs_zero] using hh),
      Shao.OQ4.killedMass_eq_closedStrip_probability
        Shao.OQ4.RademacherCosine.law k h hh]
    rfl
  simpa only [jointMass, he, hr] using (jointMass_factorization n k h 0)

theorem exact_mixtures (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    (pathLaw n).real (selfEvent n s) =
      (∑ k ∈ Finset.range (n + 1),
        weight n k * RademacherS4Assembly.p k (s * Real.sqrt (k : ℝ))) ∧
    (pathLaw n).real (detEvent n s) =
      (∑ k ∈ Finset.range (n + 1),
        weight n k * RademacherS4Assembly.p k
          (s * Real.sqrt (n : ℝ) / 2)) := by
  classical
  letI : IsProbabilityMeasure (pathLaw n) := by
    dsimp only [pathLaw]
    infer_instance
  let C (k : ℕ) : Set (Shao.Path n) := {a | count a = k}
  have hmC (k : ℕ) : MeasurableSet (C k) :=
    (measurable_count n) (measurableSet_singleton k)
  have hmself : MeasurableSet (selfEvent n s) := by
    simp only [selfEvent, Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_le (Shao.continuous_prefixSum j).abs.measurable
        (Shao.continuous_energyWall s).measurable
  have hmdet : MeasurableSet (detEvent n s) := by
    simp only [detEvent, Shao.closedStrip, Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_le (Shao.continuous_prefixSum j).abs.measurable measurable_const
  have hcountle (a : Shao.Path n) : count a ≤ n := by
    simpa only [count, Finset.card_univ, Fintype.card_fin] using
      Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => a i ≠ 0)
  have hpart (E : Set (Shao.Path n)) (hE : MeasurableSet E) :
      (pathLaw n).real E =
        ∑ k ∈ Finset.range (n + 1), (pathLaw n).real (C k ∩ E) := by
    have hEeq : E = ⋃ k ∈ Finset.range (n + 1), C k ∩ E := by
      ext a
      constructor
      · intro ha
        refine Set.mem_iUnion.mpr ⟨count a, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
        · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hcountle a))
        · exact ⟨rfl, ha⟩
      · intro ha
        rcases Set.mem_iUnion.mp ha with ⟨k, ha⟩
        rcases Set.mem_iUnion.mp ha with ⟨_, ha⟩
        exact ha.2
    calc
      (pathLaw n).real E =
          (pathLaw n).real (⋃ k ∈ Finset.range (n + 1), C k ∩ E) :=
        congrArg (pathLaw n).real hEeq
      _ = _ := by
        apply measureReal_biUnion_finset
        · intro i _ j _ hij
          apply Set.disjoint_left.2
          rintro a ⟨hai, _⟩ ⟨haj, _⟩
          exact hij (hai.symm.trans haj)
        · intro k _
          exact (hmC k).inter hE
        · intro k hk
          exact measure_ne_top _ _
  constructor
  · rw [hpart (selfEvent n s) hmself]
    apply Finset.sum_congr rfl
    intro k hk
    have hkN : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hae : C k ∩ selfEvent n s =ᵐ[pathLaw n]
        C k ∩ @Shao.closedStrip n (2 * (s * Real.sqrt (k : ℝ))) := by
      filter_upwards [(count_law n).2] with a ha
      by_cases hak : count a = k
      · have he : Shao.energy a = 4 * (k : ℝ) := by simpa only [hak] using ha
        have hroot : Real.sqrt (4 * (k : ℝ)) = 2 * Real.sqrt (k : ℝ) := by
          rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
            Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
        apply propext
        simp only [C, Set.mem_inter_iff, Set.mem_setOf_eq, hak, true_and,
          selfEvent, Shao.closedStrip, he, hroot,
          show s * (2 * Real.sqrt (k : ℝ)) = 2 * (s * Real.sqrt (k : ℝ)) by ring]
      · apply propext
        simp only [C, Set.mem_inter_iff, Set.mem_setOf_eq, hak, false_and]
    rw [measureReal_congr hae]
    exact conditional_strip_mass n k hkN _ (mul_nonneg hs (Real.sqrt_nonneg _))
  · rw [hpart (detEvent n s) hmdet]
    apply Finset.sum_congr rfl
    intro k hk
    have hkN : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hwall : 2 * (s * Real.sqrt (n : ℝ) / 2) = s * Real.sqrt (n : ℝ) := by ring
    have hmass := conditional_strip_mass n k hkN
      (s * Real.sqrt (n : ℝ) / 2) (by positivity)
    simpa only [C, detEvent, hwall] using hmass


/- Context199: the Context196 header above is preserved historical status. All four frozen analytic bodies below are now present as unexecuted source candidates. The released Context200 uniform-log and Context201 critical-limit bodies are incorporated byte-for-byte. Parent full-source review and explicit execution activation remain pending. -/

theorem binomial_payments (m : ℕ) (hm : 1 ≤ m) :
    (∀ k : ℕ, 0 ≤ weight (time m) k) ∧
    (∑ k ∈ Finset.range (time m + 1), weight (time m) k) = 1 ∧
    (∑ k ∈ Finset.range (time m + 1),
      weight (time m) k * ((k : ℝ) - (meanIndex m : ℝ)) ^ 2) =
        (3 / 2 : ℝ) * (m : ℝ) ^ 3 ∧
    (∑ k ∈ (Finset.range (time m + 1)).filter (fun k : ℕ => k < m ^ 3),
      weight (time m) k) ≤
        Real.exp (-(1 - 2 / Real.exp 1) * (m : ℝ) ^ 3) ∧
    (∀ t : ℝ, |t| ≤ 1 →
      (∑ k ∈ Finset.range (time m + 1),
        weight (time m) k * Real.exp (t * ((k : ℝ) - (meanIndex m : ℝ)))) ≤
          Real.exp (2 * (time m : ℝ) * t ^ 2)) := by
  classical
  have hG (n : ℕ) (s : ℝ) :
      (∑ k ∈ Finset.range (n + 1), weight n k * s ^ k) =
        (3 / 4 + s / 4) ^ n := by
    calc
      _ = ∑ k ∈ Finset.range (n + 1),
          (s / 4) ^ k * (3 / 4 : ℝ) ^ (n - k) * (n.choose k : ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        simp only [weight, div_eq_mul_inv, mul_pow, one_pow, one_mul]
        ring
      _ = (s / 4 + 3 / 4) ^ n := (add_pow (s / 4) (3 / 4 : ℝ) n).symm
      _ = _ := by rw [add_comm (s / 4) (3 / 4 : ℝ)]
  have hNonneg (n k : ℕ) : 0 ≤ weight n k := by
    unfold weight
    positivity
  have hOut (n k : ℕ) (hnk : n < k) : weight n k = 0 := by
    simp [weight, Nat.choose_eq_zero_of_lt hnk]
  have hTotal (n : ℕ) :
      (∑ k ∈ Finset.range (n + 1), weight n k) = 1 := by
    simpa only [one_pow, mul_one,
      show (3 / 4 : ℝ) + 1 / 4 = 1 by norm_num] using hG n 1
  have hWeightZero (n : ℕ) :
      weight (n + 1) 0 = (3 / 4 : ℝ) * weight n 0 := by
    simp only [weight, Nat.choose_zero_right, Nat.cast_one, one_mul,
      pow_zero, mul_one, Nat.sub_zero, pow_succ]
    ring
  have hShift (n : ℕ) (f : ℕ → ℝ) :
      (∑ k ∈ Finset.range (n + 1), weight n (k + 1) * f (k + 1)) +
          weight n 0 * f 0 =
        ∑ k ∈ Finset.range (n + 1), weight n k * f k := by
    rw [Finset.sum_range_succ (fun k => weight n (k + 1) * f (k + 1)) n]
    rw [hOut n (n + 1) (Nat.lt_succ_self n)]
    simp only [zero_mul, add_zero]
    exact (Finset.sum_range_succ' (fun k => weight n k * f k) n).symm
  have hOperator (n : ℕ) (f : ℕ → ℝ) :
      (∑ k ∈ Finset.range (n + 2), weight (n + 1) k * f k) =
        (3 / 4 : ℝ) * (∑ k ∈ Finset.range (n + 1), weight n k * f k) +
        (1 / 4 : ℝ) *
          (∑ k ∈ Finset.range (n + 1), weight n k * f (k + 1)) := by
    rw [Finset.sum_range_succ' (fun k => weight (n + 1) k * f k) (n + 1)]
    simp_rw [weight_succ, add_mul, mul_assoc]
    rw [hWeightZero n, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
    nlinarith only [hShift n f]
  have hFirst (n : ℕ) :
      (∑ k ∈ Finset.range (n + 1), weight n k * (k : ℝ)) = (n : ℝ) / 4 := by
    induction n with
    | zero => simp [weight]
    | succ n ih =>
      have hs :
          (∑ k ∈ Finset.range (n + 1), weight n k * ((k + 1 : ℕ) : ℝ)) =
            (∑ k ∈ Finset.range (n + 1), weight n k * (k : ℝ)) + 1 := by
        simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one,
          Finset.sum_add_distrib, hTotal]
      rw [hOperator n (fun k => (k : ℝ)), hs]
      simp only [ih, Nat.cast_succ]
      ring
  have hSecond (n : ℕ) :
      (∑ k ∈ Finset.range (n + 1), weight n k * (k : ℝ) ^ 2) =
        ((n : ℝ) ^ 2 + 3 * (n : ℝ)) / 16 := by
    induction n with
    | zero => simp [weight]
    | succ n ih =>
      have hs :
          (∑ k ∈ Finset.range (n + 1), weight n k * ((k + 1 : ℕ) : ℝ) ^ 2) =
            (∑ k ∈ Finset.range (n + 1), weight n k * (k : ℝ) ^ 2) +
              2 * (∑ k ∈ Finset.range (n + 1), weight n k * (k : ℝ)) + 1 := by
        calc
          _ = ∑ k ∈ Finset.range (n + 1),
              ((weight n k * (k : ℝ) ^ 2 + 2 * (weight n k * (k : ℝ))) +
                weight n k) := by
            apply Finset.sum_congr rfl
            intro k hk
            push_cast
            ring
          _ = _ := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
              ← Finset.mul_sum, hTotal]
      rw [hOperator n (fun k => (k : ℝ) ^ 2), hs]
      simp only [ih, hFirst, Nat.cast_succ]
      ring
  have hCenteredSecond (n : ℕ) (c : ℝ) :
      (∑ k ∈ Finset.range (n + 1), weight n k * ((k : ℝ) - c) ^ 2) =
        ((n : ℝ) ^ 2 + 3 * (n : ℝ)) / 16 -
          2 * c * ((n : ℝ) / 4) + c ^ 2 := by
    calc
      _ = ∑ k ∈ Finset.range (n + 1),
          ((weight n k * (k : ℝ) ^ 2 - (2 * c) * (weight n k * (k : ℝ))) +
            c ^ 2 * weight n k) := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, hSecond, hFirst, hTotal]
        ring
  have hExpG (n : ℕ) (a : ℝ) :
      (∑ k ∈ Finset.range (n + 1), weight n k * Real.exp (a * (k : ℝ))) =
        (3 / 4 + Real.exp a / 4) ^ n := by
    simpa only [mul_comm a, Real.exp_nat_mul] using hG n (Real.exp a)
  have hExpQuadratic (x : ℝ) (hx : |x| ≤ 1) :
      Real.exp x ≤ 1 + x + x ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le (x := x)
      (by simpa only [Real.norm_eq_abs] using hx)
    have hh : |Real.exp x - 1 - x| ≤ x ^ 2 := by
      simpa only [Real.norm_eq_abs, sq_abs] using h
    linarith [(abs_le.mp hh).2]
  have hSingle (t : ℝ) (ht : |t| ≤ 1) :
      (3 / 4 : ℝ) * Real.exp (-t / 4) +
        (1 / 4 : ℝ) * Real.exp (3 * t / 4) ≤ Real.exp (2 * t ^ 2) := by
    have ht1 : |-t / 4| ≤ 1 := by
      rw [abs_div, abs_neg]
      norm_num
      linarith
    have ht2 : |3 * t / 4| ≤ 1 := by
      rw [abs_div, abs_mul]
      norm_num
      linarith
    have h1 := hExpQuadratic (-t / 4) ht1
    have h2 := hExpQuadratic (3 * t / 4) ht2
    have he := Real.add_one_le_exp (2 * t ^ 2)
    nlinarith [sq_nonneg t]
  have hCenteredG (t : ℝ) :
      (∑ k ∈ Finset.range (time m + 1), weight (time m) k *
        Real.exp (t * ((k : ℝ) - (meanIndex m : ℝ)))) =
        ((3 / 4 : ℝ) * Real.exp (-t / 4) +
          (1 / 4 : ℝ) * Real.exp (3 * t / 4)) ^ time m := by
    have hn : (time m : ℝ) / 4 = (meanIndex m : ℝ) := by
      rw [(critical_scale m hm).2.1]
      push_cast
      ring
    calc
      _ = Real.exp (-t * (meanIndex m : ℝ)) *
          (∑ k ∈ Finset.range (time m + 1),
            weight (time m) k * Real.exp (t * (k : ℝ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [show t * ((k : ℝ) - (meanIndex m : ℝ)) =
          -t * (meanIndex m : ℝ) + t * (k : ℝ) by ring, Real.exp_add]
        ring
      _ = Real.exp (-t * (meanIndex m : ℝ)) *
          (3 / 4 + Real.exp t / 4) ^ time m := by rw [hExpG]
      _ = (Real.exp (-t / 4) * (3 / 4 + Real.exp t / 4)) ^ time m := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 1
        congr 1
        rw [← hn]
        ring
      _ = _ := by
        congr 1
        have hexp : Real.exp (-t / 4) * Real.exp t = Real.exp (3 * t / 4) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc
          Real.exp (-t / 4) * (3 / 4 + Real.exp t / 4) =
              (3 / 4 : ℝ) * Real.exp (-t / 4) +
                (Real.exp (-t / 4) * Real.exp t) / 4 := by ring
          _ = _ := by rw [hexp]; ring
  let r : ℝ := (m : ℝ) ^ 3
  let u : ℝ := (1 - Real.exp (-1)) / 4
  have hLowFirst :
      (∑ k ∈ (Finset.range (time m + 1)).filter (fun k : ℕ => k < m ^ 3),
        weight (time m) k) ≤
          Real.exp r * (3 / 4 + Real.exp (-1) / 4) ^ time m := by
    have hpoint (k : ℕ) (hk : k < m ^ 3) :
        weight (time m) k ≤
          Real.exp r * (weight (time m) k * Real.exp (-(k : ℝ))) := by
      have hkr : (k : ℝ) ≤ r := by
        dsimp only [r]
        exact_mod_cast (Nat.le_of_lt hk)
      have he : 1 ≤ Real.exp (r - (k : ℝ)) := by
        simpa only [Real.exp_zero] using
          (Real.exp_le_exp.mpr (sub_nonneg.mpr hkr))
      have hw := mul_le_mul_of_nonneg_left he (hNonneg (time m) k)
      rw [sub_eq_add_neg, Real.exp_add] at hw
      nlinarith only [hw]
    calc
      _ ≤ ∑ k ∈ (Finset.range (time m + 1)).filter (fun k : ℕ => k < m ^ 3),
          Real.exp r * (weight (time m) k * Real.exp (-(k : ℝ))) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hpoint k (Finset.mem_filter.mp hk).2
      _ ≤ ∑ k ∈ Finset.range (time m + 1),
          Real.exp r * (weight (time m) k * Real.exp (-(k : ℝ))) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro k hk hnot
        exact mul_nonneg (Real.exp_pos _).le
          (mul_nonneg (hNonneg (time m) k) (Real.exp_pos _).le)
      _ = _ := by
        rw [← Finset.mul_sum]
        congr 1
        simpa only [neg_one_mul] using hExpG (time m) (-1)
  have hLowSecond :
      Real.exp r * (3 / 4 + Real.exp (-1) / 4) ^ time m ≤
        Real.exp (-(1 - 2 / Real.exp 1) * (m : ℝ) ^ 3) := by
    have hb : (3 / 4 : ℝ) + Real.exp (-1) / 4 = 1 - u := by
      dsimp only [u]
      ring
    have hbase : 0 ≤ (3 / 4 : ℝ) + Real.exp (-1) / 4 := by positivity
    have hbound : (3 / 4 : ℝ) + Real.exp (-1) / 4 ≤ Real.exp (-u) := by
      rw [hb]
      exact Real.one_sub_le_exp_neg u
    calc
      _ ≤ Real.exp r * Real.exp (-u) ^ time m := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos r).le
        exact pow_le_pow_left₀ hbase hbound (time m)
      _ = Real.exp (r + (time m : ℝ) * (-u)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
      _ = _ := by
        congr 1
        dsimp only [r, u]
        rw [(critical_scale m hm).1]
        push_cast
        rw [Real.exp_neg]
        ring
  refine ⟨hNonneg (time m), hTotal (time m), ?_,
    hLowFirst.trans hLowSecond, ?_⟩
  · rw [hCenteredSecond, (critical_scale m hm).1]
    simp only [(critical_scale m hm).1, meanIndex,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  · intro t ht
    rw [hCenteredG]
    calc
      _ ≤ Real.exp (2 * t ^ 2) ^ time m := by
        apply pow_le_pow_left₀ _ (hSingle t ht) (time m)
        positivity
      _ = Real.exp (2 * (time m : ℝ) * t ^ 2) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring


theorem binomial_halves :
    Tendsto (fun m : ℕ =>
      ∑ k ∈ (Finset.range (time m + 1)).filter
        (fun k : ℕ => k < meanIndex m), weight (time m) k)
      atTop (𝓝 (1 / 2 : ℝ)) ∧
    Tendsto (fun m : ℕ =>
      ∑ k ∈ (Finset.range (time m + 1)).filter
        (fun k : ℕ => meanIndex m ≤ k), weight (time m) k)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  classical
  let b : ℝ → ℝ := fun z => if z ≠ 0 then 1 else 0
  have hb : Measurable b := by
    exact Measurable.ite
      (isClosed_eq continuous_id continuous_const).measurableSet.compl
      measurable_const measurable_const
  let eta : Measure ℝ := law.map b
  have hEtaProbability : IsProbabilityMeasure eta := by
    constructor
    change (law.map b) Set.univ = 1
    rw [Measure.map_apply hb MeasurableSet.univ]
    simp
  letI : IsProbabilityMeasure eta := hEtaProbability
  have hEta : eta =
      (3 / 4 : ℝ≥0∞) • Measure.dirac (0 : ℝ) +
        (1 / 4 : ℝ≥0∞) • Measure.dirac (1 : ℝ) := by
    ext A hA
    change (law.map b) A = _
    rw [Measure.map_apply hb hA]
    by_cases h0 : (0 : ℝ) ∈ A <;> by_cases h1 : (1 : ℝ) ∈ A <;>
      norm_num [law, Measure.add_apply, Measure.smul_apply,
        Measure.dirac_apply', hA, hA.preimage hb, b, h0, h1]
    all_goals
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      repeat' rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
      norm_num [ENNReal.toReal_div, ENNReal.toReal_inv]
  have hEtaFinite (f : ℝ → ℝ) : Integrable f eta ∧
      (∫ z : ℝ, f z ∂eta) = (3 / 4 : ℝ) * f 0 + (1 / 4 : ℝ) * f 1 := by
    have h0 : Integrable f ((3 / 4 : ℝ≥0∞) • Measure.dirac (0 : ℝ)) :=
      (integrable_dirac (by simp)).smul_measure (by finiteness)
    have h1 : Integrable f ((1 / 4 : ℝ≥0∞) • Measure.dirac (1 : ℝ)) :=
      (integrable_dirac (by simp)).smul_measure (by finiteness)
    constructor
    · rw [hEta]
      exact h0.add_measure h1
    · rw [hEta, integral_add_measure h0 h1,
        integral_smul_measure, integral_smul_measure,
        integral_dirac, integral_dirac]
      norm_num [ENNReal.toReal_div]
  have hMean : (∫ z : ℝ, z ∂eta) = (1 / 4 : ℝ) := by
    rw [(hEtaFinite (fun z => z)).2]
    norm_num
  have hVariance : variance (id : ℝ → ℝ) eta = (3 / 16 : ℝ) := by
    rw [variance_eq_integral measurable_id.aemeasurable]
    change (∫ z : ℝ, (z - ∫ y : ℝ, y ∂eta) ^ 2 ∂eta) = 3 / 16
    rw [hMean, (hEtaFinite (fun z => (z - 1 / 4) ^ 2)).2]
    norm_num
  have hThird : (∫ z : ℝ, |z - 1 / 4| ^ 3 ∂eta) = (15 / 128 : ℝ) := by
    rw [(hEtaFinite (fun z => |z - 1 / 4| ^ 3)).2]
    norm_num
  let F : (n : ℕ) → Shao.Path n → Shao.Path n := fun _ a i => b (a i)
  have hF (n : ℕ) : Measurable (F n) := by
    apply measurable_pi_iff.mpr
    intro i
    exact hb.comp (measurable_pi_apply i)
  have hProductMap (n : ℕ) :
      (pathLaw n).map (F n) = Measure.pi (fun _ : Fin n => eta) := by
    simpa only [pathLaw, eta, F] using
      (Measure.pi_map_pi (fun _ : Fin n => hb.aemeasurable))
  have hFinalCount (n : ℕ) (a : Shao.Path n) :
      Shao.prefixSum (F n a) n = (count a : ℝ) := by
    have hfull : (Finset.univ.filter (fun i : Fin n => i.val < n)) = Finset.univ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, i.isLt]
    have hnat : count a = ∑ i : Fin n, if a i ≠ 0 then (1 : ℕ) else 0 := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, smul_eq_mul, mul_one, count]
    rw [Shao.prefixSum, hfull, hnat, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hi0 : a i ≠ 0 <;> simp [F, b, hi0]
  have hPredicateMass (n : ℕ) (P : ℕ → Prop) :
      (pathLaw n).real {a : Shao.Path n | P (count a)} =
        ∑ k ∈ (Finset.range (n + 1)).filter P, weight n k := by
    letI : IsProbabilityMeasure (pathLaw n) := by
      dsimp only [pathLaw]
      infer_instance
    let S : Finset ℕ := (Finset.range (n + 1)).filter P
    let C (k : ℕ) : Set (Shao.Path n) := {a | count a = k}
    have hCountLe (a : Shao.Path n) : count a ≤ n := by
      simpa only [count, Finset.card_univ, Fintype.card_fin] using
        Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => a i ≠ 0)
    have hSet : {a : Shao.Path n | P (count a)} = ⋃ k ∈ S, C k := by
      ext a
      constructor
      · intro ha
        exact Set.mem_iUnion.mpr ⟨count a, Set.mem_iUnion.mpr
          ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hCountLe a)), ha⟩, rfl⟩⟩
      · intro ha
        rcases Set.mem_iUnion.mp ha with ⟨k, ha⟩
        rcases Set.mem_iUnion.mp ha with ⟨hk, hak⟩
        have hPk : P k := (Finset.mem_filter.mp hk).2
        change count a = k at hak
        change P (count a)
        simpa only [hak] using hPk
    have hDisjoint : Set.PairwiseDisjoint (↑S) C := by
      intro i hi j hj hij
      apply Set.disjoint_left.2
      intro a hai haj
      change count a = i at hai
      change count a = j at haj
      exact hij (hai.symm.trans haj)
    have hMeasurable (k : ℕ) (_hk : k ∈ S) : MeasurableSet (C k) :=
      measurable_count n (measurableSet_singleton k)
    rw [hSet, measureReal_biUnion_finset hDisjoint hMeasurable (by intro k hk; finiteness)]
    apply Finset.sum_congr rfl
    intro k hk
    exact (count_law n).1 k
  have hGaussianZero : Shao.OQ4.standardNormalCDF 0 = (1 / 2 : ℝ) := by
    let γ : Measure ℝ := gaussianReal 0 1
    letI : NullSingletonClass γ :=
      nullSingletonClass_gaussianReal (by norm_num : (1 : ℝ≥0) ≠ 0)
    have hReflect : γ.real (Set.Ioi 0) = γ.real (Set.Iio 0) := by
      have hMap : γ.map (fun x : ℝ => -x) = γ := by
        simpa only [γ, neg_zero] using (gaussianReal_map_neg (μ := 0) (v := 1))
      calc
        γ.real (Set.Ioi 0) = (γ.map (fun x : ℝ => -x)).real (Set.Ioi 0) := by
          rw [hMap]
        _ = γ.real (Set.Iio 0) := by
          apply congrArg ENNReal.toReal
          rw [Measure.map_apply (by fun_prop) measurableSet_Ioi]
          congr 1
          ext x
          simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio, neg_pos]
    have hNotZero : ∀ᵐ x : ℝ ∂γ, x ≠ 0 := by
      simp only [ae_iff]
      simp
    have hClosed : γ.real (Set.Iic 0) = γ.real (Set.Iio 0) := by
      apply measureReal_congr
      filter_upwards [hNotZero] with x hx
      simp only [Set.mem_Iic, Set.mem_Iio]
      simp only [le_iff_lt_or_eq, hx, or_false]
    have hTotal := measureReal_add_measureReal_compl
      (μ := γ) (s := Set.Iic 0) measurableSet_Iic
    simp only [Set.compl_Iic, probReal_univ] at hTotal
    rw [Shao.OQ4.standardNormalCDF_eq_real]
    change γ.real (Set.Iic 0) = (1 / 2 : ℝ)
    linarith
  let sigma : ℝ := Real.sqrt (3 / 16 : ℝ)
  let v : ℕ → ℝ := fun m => Real.sqrt (time m : ℝ)
  let d : ℕ → ℝ := fun m => sigma * v m
  let E : ℕ → ℝ := fun m => 120 / (sigma ^ 3 * v m)
  let lower : ℕ → ℝ := fun m =>
    ∑ k ∈ (Finset.range (time m + 1)).filter (fun k : ℕ => k < meanIndex m),
      weight (time m) k
  let closedLower : ℕ → ℝ := fun m =>
    ∑ k ∈ (Finset.range (time m + 1)).filter (fun k : ℕ => k ≤ meanIndex m),
      weight (time m) k
  let upper : ℕ → ℝ := fun m =>
    ∑ k ∈ (Finset.range (time m + 1)).filter (fun k : ℕ => meanIndex m ≤ k),
      weight (time m) k
  have hSigma : 0 < sigma := by
    dsimp only [sigma]
    exact Real.sqrt_pos.2 (by norm_num)
  have hPositive (m : ℕ) (hm : 1 ≤ m) : 0 < v m ∧ 0 < d m := by
    have ht : 0 < time m := by
      unfold time
      have hm0 : 0 < m := by omega
      positivity
    have hv : 0 < v m := Real.sqrt_pos.2 (by exact_mod_cast ht)
    exact ⟨hv, mul_pos hSigma hv⟩
  have hBECount (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
      |(pathLaw (time m)).real {a : Shao.Path (time m) |
          ((count a : ℝ) - (meanIndex m : ℝ)) / d m ≤ x} -
        Shao.OQ4.standardNormalCDF x| ≤ E m := by
    have hn : 1 ≤ time m := by
      have ht : 0 < time m := by
        unfold time
        have hm0 : 0 < m := by omega
        positivity
      omega
    have hnmean : (time m : ℝ) * (1 / 4) = (meanIndex m : ℝ) := by
      rw [(critical_scale m hm).2.1]
      push_cast
      ring
    have hbe := Shao.Probability.iid_centered_berryEsseen eta
      (hEtaFinite (fun z => |z| ^ 3)).1
      (by rw [hVariance]; norm_num) (time m) hn x
    dsimp only at hbe
    simp only [hMean, hVariance, hThird, hnmean] at hbe
    norm_num only [show (1024 : ℝ) * (15 / 128) = 120 by norm_num] at hbe
    have hMass :
        (Measure.pi (fun _ : Fin (time m) => eta)).real
            {a : Shao.Path (time m) |
              (Shao.prefixSum a (time m) - (meanIndex m : ℝ)) / d m ≤ x} =
          (pathLaw (time m)).real {a : Shao.Path (time m) |
            ((count a : ℝ) - (meanIndex m : ℝ)) / d m ≤ x} := by
      rw [← hProductMap (time m)]
      apply congrArg ENNReal.toReal
      rw [Measure.map_apply (hF (time m))
        (measurableSet_le
          (((Shao.measurable_prefixSum (time m)).sub_const _).div_const _) measurable_const)]
      congr 1
      ext a
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hFinalCount]
    change |(Measure.pi (fun _ : Fin (time m) => eta)).real
        {a : Shao.Path (time m) |
          (Shao.prefixSum a (time m) - (meanIndex m : ℝ)) / d m ≤ x} -
        Shao.OQ4.standardNormalCDF x| ≤ E m at hbe
    rw [hMass] at hbe
    exact hbe
  have hStrictCDF (m : ℕ) (hm : 1 ≤ m) :
      |lower m - Shao.OQ4.standardNormalCDF (-1 / d m)| ≤ E m := by
    have hp (k : ℕ) :
        ((k : ℝ) - (meanIndex m : ℝ)) / d m ≤ -1 / d m ↔
          k < meanIndex m := by
      rw [div_le_div_iff_of_pos_right (hPositive m hm).2]
      constructor
      · intro hk
        have hr : (k + 1 : ℕ) ≤ meanIndex m := by
          exact_mod_cast (show (k : ℝ) + 1 ≤ (meanIndex m : ℝ) by linarith)
        omega
      · intro hk
        have hr : (k : ℝ) + 1 ≤ (meanIndex m : ℝ) := by
          exact_mod_cast (show k + 1 ≤ meanIndex m by omega)
        linarith
    have he : (pathLaw (time m)).real {a : Shao.Path (time m) |
        ((count a : ℝ) - (meanIndex m : ℝ)) / d m ≤ -1 / d m} = lower m := by
      rw [hPredicateMass (time m) (fun k : ℕ => ((k : ℝ) - (meanIndex m : ℝ)) / d m ≤ -1 / d m)]
      simp only [lower]
      simp_rw [hp]
    have hbe := hBECount m hm (-1 / d m)
    rw [he] at hbe
    exact hbe
  have hClosedCDF (m : ℕ) (hm : 1 ≤ m) :
      |closedLower m - (1 / 2 : ℝ)| ≤ E m := by
    have hp (k : ℕ) :
        ((k : ℝ) - (meanIndex m : ℝ)) / d m ≤ 0 ↔ k ≤ meanIndex m := by
      rw [div_le_iff₀ (hPositive m hm).2]
      simp only [zero_mul, sub_nonpos]
      exact_mod_cast (Iff.rfl : k ≤ meanIndex m ↔ k ≤ meanIndex m)
    have he : (pathLaw (time m)).real {a : Shao.Path (time m) |
        ((count a : ℝ) - (meanIndex m : ℝ)) / d m ≤ 0} = closedLower m := by
      rw [hPredicateMass (time m) (fun k : ℕ => ((k : ℝ) - (meanIndex m : ℝ)) / d m ≤ 0)]
      simp only [closedLower]
      simp_rw [hp]
    have hbe := hBECount m hm 0
    rw [he, hGaussianZero] at hbe
    exact hbe
  have hSplit (m : ℕ) (hm : 1 ≤ m) :
      closedLower m = lower m + weight (time m) (meanIndex m) ∧
        lower m + upper m = 1 := by
    have hmean : meanIndex m ∈ Finset.range (time m + 1) := by
      apply Finset.mem_range.mpr
      rw [(critical_scale m hm).2.1]
      omega
    constructor
    · calc
        closedLower m = ∑ k ∈ Finset.range (time m + 1),
            ((if k < meanIndex m then weight (time m) k else 0) +
              if k = meanIndex m then weight (time m) k else 0) := by
          dsimp only [closedLower]
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro k hk
          by_cases hlt : k < meanIndex m
          · simp [hlt, Nat.le_of_lt hlt, Nat.ne_of_lt hlt]
          · by_cases heq : k = meanIndex m
            · simp [heq]
            · have hgt : meanIndex m < k := by omega
              simp [hlt, heq, Nat.not_le_of_gt hgt]
        _ = lower m + weight (time m) (meanIndex m) := by
          rw [Finset.sum_add_distrib]
          simp only [lower, Finset.sum_filter]
          simp [hmean]
    · calc
        lower m + upper m =
            ∑ k ∈ Finset.range (time m + 1), weight (time m) k := by
          dsimp only [lower, upper]
          rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k hk
          by_cases hlt : k < meanIndex m
          · simp [hlt, Nat.not_le_of_gt hlt]
          · simp [hlt, Nat.le_of_not_gt hlt]
        _ = 1 := (binomial_payments m hm).2.1
  have hLowerError (m : ℕ) (hm : 1 ≤ m) :
      |lower m - (1 / 2 : ℝ)| ≤ E m + 1 / d m := by
    have hPhi : |Shao.OQ4.standardNormalCDF (-1 / d m) - (1 / 2 : ℝ)| ≤
        1 / d m := by
      have hl := Shao.OQ4.standardNormalCDF_lipschitz (-1 / d m) 0
      simpa only [hGaussianZero, sub_zero, abs_div,
        abs_neg, abs_one, abs_of_pos (hPositive m hm).2] using hl
    calc
      _ = |(lower m - Shao.OQ4.standardNormalCDF (-1 / d m)) +
          (Shao.OQ4.standardNormalCDF (-1 / d m) - 1 / 2)| := by
        congr 1
        ring
      _ ≤ |lower m - Shao.OQ4.standardNormalCDF (-1 / d m)| +
          |Shao.OQ4.standardNormalCDF (-1 / d m) - 1 / 2| := abs_add_le _ _
      _ ≤ _ := add_le_add (hStrictCDF m hm) hPhi
  have hBoundaryAtom (m : ℕ) (hm : 1 ≤ m) :
      0 ≤ weight (time m) (meanIndex m) ∧
        weight (time m) (meanIndex m) ≤ 2 * E m + 1 / d m := by
    refine ⟨(binomial_payments m hm).1 _, ?_⟩
    have hF := (abs_le.mp (hClosedCDF m hm)).2
    have hL := (abs_le.mp (hLowerError m hm)).1
    linarith [(hSplit m hm).1]
  let D : ℝ := 120 / sigma ^ 3 + 1 / sigma
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hRate (m : ℕ) (hm : 1 ≤ m) :
      |lower m - (1 / 2 : ℝ)| ≤ D / (m : ℝ) ∧
        |upper m - (1 / 2 : ℝ)| ≤ D / (m : ℝ) := by
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
    have hcube : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg (m : ℝ))
        (show 0 ≤ (m : ℝ) - 1 by linarith)]
    have ht : (time m : ℝ) = 8 * (m : ℝ) ^ 3 := by
      exact_mod_cast (critical_scale m hm).1
    have hvSq : (v m) ^ 2 = (time m : ℝ) := Real.sq_sqrt (by positivity)
    have hvm : (m : ℝ) ≤ v m := by
      have hv0 := (hPositive m hm).1
      rw [ht] at hvSq
      by_contra hnot
      have hvlt : v m < (m : ℝ) := lt_of_not_ge hnot
      have hprod : 0 < ((m : ℝ) - v m) * ((m : ℝ) + v m) :=
        mul_pos (sub_pos.mpr hvlt) (add_pos hm0 hv0)
      nlinarith [pow_nonneg hm0.le 3]
    have hE : E m ≤ (120 / sigma ^ 3) / (m : ℝ) := by
      dsimp only [E]
      rw [div_div]
      apply div_le_div_of_nonneg_left (by norm_num) (mul_pos (pow_pos hSigma 3) hm0)
      exact mul_le_mul_of_nonneg_left hvm (pow_nonneg hSigma.le 3)
    have hd : 1 / d m ≤ (1 / sigma) / (m : ℝ) := by
      dsimp only [d]
      rw [div_div]
      apply div_le_div_of_nonneg_left (by norm_num) (mul_pos hSigma hm0)
      exact mul_le_mul_of_nonneg_left hvm hSigma.le
    have herr : |lower m - (1 / 2 : ℝ)| ≤ D / (m : ℝ) := by
      calc
        _ ≤ E m + 1 / d m := hLowerError m hm
        _ ≤ (120 / sigma ^ 3) / (m : ℝ) + (1 / sigma) / (m : ℝ) := add_le_add hE hd
        _ = _ := by dsimp only [D]; ring
    have hAtomRate : weight (time m) (meanIndex m) ≤
        (240 / sigma ^ 3 + 1 / sigma) / (m : ℝ) := by
      calc
        _ ≤ 2 * E m + 1 / d m := (hBoundaryAtom m hm).2
        _ ≤ 2 * ((120 / sigma ^ 3) / (m : ℝ)) +
            (1 / sigma) / (m : ℝ) := by linarith [hE, hd]
        _ = _ := by ring
    have hu : upper m - (1 / 2 : ℝ) = -(lower m - (1 / 2 : ℝ)) := by
      linarith [(hSplit m hm).2]
    refine ⟨herr, ?_⟩
    rw [hu, abs_neg]
    exact herr
  have hLimit (f : ℕ → ℝ)
      (hf : ∀ m : ℕ, 1 ≤ m → |f m - (1 / 2 : ℝ)| ≤ D / (m : ℝ)) :
      Tendsto f atTop (𝓝 (1 / 2 : ℝ)) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨J, hJ⟩ := exists_nat_gt (D / ε + 1)
    refine ⟨max J 1, ?_⟩
    intro m hm
    have hm1 : 1 ≤ m := (le_max_right J 1).trans hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    have hJm : (J : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast ((le_max_left J 1).trans hm)
    have hlarge : D / ε < (m : ℝ) := by linarith
    have hcross : D < ε * (m : ℝ) := by
      have h := (div_lt_iff₀ hε).mp hlarge
      nlinarith only [h]
    have hsmall : D / (m : ℝ) < ε := (div_lt_iff₀ hm0).mpr hcross
    simpa only [Real.dist_eq] using (hf m hm1).trans_lt hsmall
  exact ⟨hLimit lower (fun m hm => (hRate m hm).1),
    hLimit upper (fun m hm => (hRate m hm).2)⟩


theorem uniform_log_pair {Ω : Type u} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, 1 ≤ J ∧
      ∀ m : ℕ, J ≤ m → ∀ k : ℕ, m ^ 3 ≤ k → k ≤ time m →
        0 < baseline B P hB m ∧
        0 < RademacherS4Assembly.p k (randomHeight m k) ∧
        0 < RademacherS4Assembly.p k (m : ℝ) ∧
        |Real.log (RademacherS4Assembly.p k (randomHeight m k) /
          baseline B P hB m) - phaseExponent m k| < ε ∧
        |Real.log (RademacherS4Assembly.p k (m : ℝ) / baseline B P hB m) +
          (Real.pi ^ 2 / 8) * ((k : ℝ) - (meanIndex m : ℝ)) / (m : ℝ) ^ 2 -
          (Real.pi ^ 2 / 4) * ((k : ℝ) / (m : ℝ) ^ 3)| < ε := by
  classical
  let F : ℝ → ℝ := Shao.Probability.BrownianSup.probability B P hB
  let g : ℝ → ℝ := Shao.Probability.BrownianSup.firstTerm
  have g_pos (z : ℝ) : 0 < g z := by
    dsimp [g, Shao.Probability.BrownianSup.firstTerm]
    positivity
  have g_log (z : ℝ) :
      Real.log (g z) = Real.log (4 / Real.pi) - (Real.pi ^ 2 / 8) / z ^ 2 := by
    dsimp [g, Shao.Probability.BrownianSup.firstTerm]
    rw [Real.log_mul (by positivity : (4 / Real.pi : ℝ) ≠ 0)
      (Real.exp_ne_zero _), Real.log_exp]
    ring
  have log_bound {q c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hcq : c ≤ q) :
      |Real.log q| ≤ c⁻¹ * |q - 1| := by
    have hderiv : ∀ z ∈ Set.Ici c,
        HasDerivWithinAt Real.log z⁻¹ (Set.Ici c) z := by
      intro z hz
      exact (Real.hasDerivAt_log
        (ne_of_gt (lt_of_lt_of_le hc hz))).hasDerivWithinAt
    have hbound : ∀ z ∈ Set.Ici c, ‖z⁻¹‖ ≤ c⁻¹ := by
      intro z hz
      have hzpos : 0 < z := lt_of_lt_of_le hc hz
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hzpos)]
      simpa only [one_div] using one_div_le_one_div_of_le hc hz
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := Real.log) (f' := fun z : ℝ => z⁻¹) (s := Set.Ici c)
      (x := (1 : ℝ)) (y := q) hderiv hbound (convex_Ici c) hc1 hcq
    simpa only [Real.norm_eq_abs, Real.log_one, sub_zero] using h
  have brownian_log_seq (z : ℕ → ℝ)
      (hsmall : ∀ d : ℝ, 0 < d → ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
        0 < z j ∧ z j < d) :
      Tendsto (fun j : ℕ => Real.log (F (z j) / g (z j))) atTop
        (𝓝 (0 : ℝ)) := by
    apply Metric.tendsto_atTop.mpr
    intro e he
    have heta : 0 < min (1 / 4 : ℝ) (e / 4) :=
      lt_min (by norm_num) (by positivity)
    obtain ⟨d, hd, hfirst⟩ :=
      Shao.Probability.BrownianSup.actual_brownian_firstTerm B P hB
        (min (1 / 4 : ℝ) (e / 4)) heta
    obtain ⟨J, hJ⟩ := hsmall d hd
    refine ⟨J, ?_⟩
    intro j hj
    have hq : |F (z j) / g (z j) - 1| < min (1 / 4 : ℝ) (e / 4) :=
      hfirst (z j) (hJ j hj).1 (hJ j hj).2
    have hq4 : |F (z j) / g (z j) - 1| < 1 / 4 :=
      lt_of_lt_of_le hq (min_le_left _ _)
    have hhalf : (1 / 2 : ℝ) ≤ F (z j) / g (z j) := by
      have hlow := (abs_lt.mp hq4).1
      linarith
    have hlog := log_bound (q := F (z j) / g (z j))
      (c := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hhalf
    norm_num at hlog
    have hqe : |F (z j) / g (z j) - 1| < e / 4 :=
      lt_of_lt_of_le hq (min_le_right _ _)
    have hfinal : |Real.log (F (z j) / g (z j))| < e := by
      linarith
    simpa only [Real.dist_eq, sub_zero] using hfinal
  have geometry (m k : ℕ) (hm : 1 ≤ m) (hl : m ^ 3 ≤ k) (hu : k ≤ time m) :
      0 < (m : ℝ) ∧ 0 < (k : ℝ) ∧ 0 < randomHeight m k ∧
      (m : ℝ) / 2 ≤ randomHeight m k ∧
      (k : ℝ) / randomHeight m k ^ 2 = 2 * (m : ℝ) ∧
      (k : ℝ) / randomHeight m k ^ 3 ≤ 4 ∧
      (m : ℝ) ≤ (k : ℝ) / (m : ℝ) ^ 2 ∧
      (k : ℝ) / (m : ℝ) ^ 3 ≤ 8 ∧
      randomHeight m k / Real.sqrt (k : ℝ) = criticalX m ∧
      1 / criticalX m ^ 2 = 2 * (m : ℝ) := by
    rcases critical_scale m hm with ⟨htime, hmean, hxpos, hxvalue, hwall⟩
    have hmN : 0 < m := by omega
    have hkN : 0 < k := lt_of_lt_of_le (pow_pos hmN 3) hl
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast hmN
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast hkN
    have hlR : (m : ℝ) ^ 3 ≤ (k : ℝ) := by exact_mod_cast hl
    have huN : k ≤ 8 * m ^ 3 := by simpa only [htime] using hu
    have huR : (k : ℝ) ≤ 8 * (m : ℝ) ^ 3 := by exact_mod_cast huN
    have hroot : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkpos
    have hHpos : 0 < randomHeight m k := by
      exact mul_pos hxpos hroot
    have hHsq : randomHeight m k ^ 2 = (k : ℝ) / (2 * (m : ℝ)) := by
      rw [randomHeight, hxvalue, mul_pow, div_pow, one_pow,
        Real.sq_sqrt (by positivity : 0 ≤ 2 * (m : ℝ)),
        Real.sq_sqrt (Nat.cast_nonneg k)]
      ring
    have hquad : 2 * (m : ℝ) * randomHeight m k ^ 2 = (k : ℝ) := by
      have h := (eq_div_iff (by positivity : (2 * (m : ℝ)) ≠ 0)).mp hHsq
      nlinarith [h]
    have hHlower : (m : ℝ) / 2 ≤ randomHeight m k := by
      by_contra hn
      have hlt : randomHeight m k < (m : ℝ) / 2 := lt_of_not_ge hn
      have hsq : randomHeight m k ^ 2 < ((m : ℝ) / 2) ^ 2 := by
        have hp := mul_pos (sub_pos.mpr hlt)
          (show 0 < (m : ℝ) / 2 + randomHeight m k by positivity)
        nlinarith [hp]
      have hmul := mul_lt_mul_of_pos_left hsq
        (show 0 < 2 * (m : ℝ) by positivity)
      nlinarith [pow_pos hmpos 3]
    have hscale2 : (k : ℝ) / randomHeight m k ^ 2 = 2 * (m : ℝ) := by
      apply (div_eq_iff (pow_ne_zero 2 hHpos.ne')).2
      nlinarith [hquad]
    have hscale3 : (k : ℝ) / randomHeight m k ^ 3 ≤ 4 := by
      have hid : (k : ℝ) / randomHeight m k ^ 3 =
          (2 * (m : ℝ)) / randomHeight m k := by
        rw [← hquad]
        field_simp [hHpos.ne']
        <;> ring
      rw [hid]
      apply (div_le_iff₀ hHpos).2
      linarith
    have hdet2 : (m : ℝ) ≤ (k : ℝ) / (m : ℝ) ^ 2 := by
      apply (le_div_iff₀ (pow_pos hmpos 2)).2
      nlinarith [hlR]
    have hdet3 : (k : ℝ) / (m : ℝ) ^ 3 ≤ 8 := by
      exact (div_le_iff₀ (pow_pos hmpos 3)).2 huR
    have hxarg : randomHeight m k / Real.sqrt (k : ℝ) = criticalX m := by
      dsimp [randomHeight]
      field_simp [hroot.ne']
    have hxinv : 1 / criticalX m ^ 2 = 2 * (m : ℝ) := by
      rw [hxvalue, div_pow, one_pow,
        Real.sq_sqrt (by positivity : 0 ≤ 2 * (m : ℝ))]
      field_simp [hmpos.ne']
    exact ⟨hmpos, hkpos, hHpos, hHlower, hscale2, hscale3,
      hdet2, hdet3, hxarg, hxinv⟩
  have uniform_extract
      (G : ℕ → ℕ → Prop)
      (hseq : ∀ (M K : ℕ → ℕ),
        (∀ j : ℕ, j ≤ M j) →
        (∀ j : ℕ, (M j) ^ 3 ≤ K j) →
        (∀ j : ℕ, K j ≤ time (M j)) →
        ∀ᶠ j : ℕ in atTop, G (M j) (K j)) :
      ∃ J : ℕ, ∀ m : ℕ, J ≤ m → ∀ k : ℕ,
        m ^ 3 ≤ k → k ≤ time m → G m k := by
    by_contra hnone
    push_neg at hnone
    let M : ℕ → ℕ := fun j => Classical.choose (hnone j)
    have hM (j : ℕ) := Classical.choose_spec (hnone j)
    let K : ℕ → ℕ := fun j => Classical.choose (hM j).2
    have hK (j : ℕ) := Classical.choose_spec (hM j).2
    have hgood : ∀ᶠ j : ℕ in atTop, G (M j) (K j) :=
      hseq M K (fun j => (hM j).1)
        (fun j => (hK j).1) (fun j => (hK j).2.1)
    obtain ⟨j, hj⟩ := hgood.exists
    exact (hK j).2.2 hj
  intro ε hε
  let G : ℕ → ℕ → Prop := fun m k =>
    0 < baseline B P hB m ∧
    0 < RademacherS4Assembly.p k (randomHeight m k) ∧
    0 < RademacherS4Assembly.p k (m : ℝ) ∧
    |Real.log (RademacherS4Assembly.p k (randomHeight m k) /
      baseline B P hB m) - phaseExponent m k| < ε ∧
    |Real.log (RademacherS4Assembly.p k (m : ℝ) / baseline B P hB m) +
      (Real.pi ^ 2 / 8) * ((k : ℝ) - (meanIndex m : ℝ)) / (m : ℝ) ^ 2 -
      (Real.pi ^ 2 / 4) * ((k : ℝ) / (m : ℝ) ^ 3)| < ε
  have hseq : ∀ (M K : ℕ → ℕ),
      (∀ j : ℕ, j ≤ M j) →
      (∀ j : ℕ, (M j) ^ 3 ≤ K j) →
      (∀ j : ℕ, K j ≤ time (M j)) →
      ∀ᶠ j : ℕ in atTop, G (M j) (K j) := by
    intro M K hM hlow hupp
    let HR : ℕ → ℝ := fun j => randomHeight (M j) (K j)
    let cell : ℕ → ℕ := fun j => ⌊HR j⌋₊
    let xr : ℕ → ℝ := fun j => RademacherS4Assembly.x (K j) (HR j)
    let yd : ℕ → ℝ := fun j => RademacherS4Assembly.x (K j) (M j : ℝ)
    have hMnat : Tendsto M atTop atTop :=
      tendsto_atTop_mono hM tendsto_id
    have hMr : Tendsto (fun j : ℕ => (M j : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hMnat
    have hgeom (j : ℕ) (hj : 1 ≤ j) :=
      geometry (M j) (K j) (le_trans hj (hM j)) (hlow j) (hupp j)
    have hcellR : ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
        1 ≤ cell j ∧ (cell j : ℝ) ≤ HR j ∧ HR j < (cell j : ℝ) + 1 := by
      refine ⟨2, ?_⟩
      intro j hj
      rcases hgeom j (by omega) with
        ⟨hmpos, hkpos, hHpos, hHlower, hs2, hs3, hd2, hd3, hx, hxi⟩
      have hm2 : (2 : ℝ) ≤ (M j : ℝ) := by exact_mod_cast le_trans hj (hM j)
      have hH1 : (1 : ℝ) ≤ HR j := by dsimp [HR]; linarith
      exact ⟨Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ HR j by simpa only [Nat.cast_one] using hH1), Nat.floor_le (by dsimp [HR]; positivity),
        Nat.lt_floor_add_one _⟩
    have hHR : Tendsto HR atTop atTop := by
      apply tendsto_atTop.2
      intro b
      filter_upwards [hMr.eventually (eventually_ge_atTop (2 * b)),
        eventually_ge_atTop (1 : ℕ)] with j hj hj1
      have h := (hgeom j hj1).2.2.2.1
      change b ≤ randomHeight (M j) (K j)
      linarith
    have hRs2 : Tendsto
        (fun j : ℕ => RademacherS4Assembly.N (K j) / HR j ^ 2) atTop atTop := by
      apply tendsto_atTop.2
      intro b
      filter_upwards [hMr.eventually (eventually_ge_atTop (b / 2)),
        eventually_ge_atTop (1 : ℕ)] with j hj hj1
      have hs := (hgeom j hj1).2.2.2.2.1
      change b ≤ (K j : ℝ) / randomHeight (M j) (K j) ^ 2
      rw [hs]
      linarith
    have hRs3 : ∃ A : ℝ, 0 < A ∧ ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
        RademacherS4Assembly.scale3 (K j) (HR j) ≤ A := by
      refine ⟨4, by norm_num, 1, ?_⟩
      intro j hj
      exact (hgeom j hj).2.2.2.2.2.1
    have hsR := RademacherS4Assembly.S4_EVENTUAL B P hB cell K HR
      hcellR hHR hRs2 hRs3
    rcases hsR with
      ⟨hRH, hRNH, hR4, hRHinv, hRx, hRsmall, hReta, hRres, hRKres,
        JRtime, JRpos, hRJorder, hRtime, hRpositive, hReps⟩
    have hcellD : ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
        1 ≤ M j ∧ (M j : ℝ) ≤ (M j : ℝ) ∧ (M j : ℝ) < (M j : ℝ) + 1 := by
      exact ⟨1, fun j hj => ⟨le_trans hj (hM j), le_rfl, by linarith⟩⟩
    have hDs2 : Tendsto
        (fun j : ℕ => RademacherS4Assembly.N (K j) / (M j : ℝ) ^ 2)
        atTop atTop := by
      apply tendsto_atTop.2
      intro b
      filter_upwards [hMr.eventually (eventually_ge_atTop b),
        eventually_ge_atTop (1 : ℕ)] with j hj hj1
      exact hj.trans (hgeom j hj1).2.2.2.2.2.2.1
    have hDs3 : ∃ A : ℝ, 0 < A ∧ ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
        RademacherS4Assembly.scale3 (K j) (M j : ℝ) ≤ A := by
      refine ⟨8, by norm_num, 1, ?_⟩
      intro j hj
      exact (hgeom j hj).2.2.2.2.2.2.2.1
    have hsD := RademacherS4Assembly.S4_EVENTUAL B P hB M K
      (fun j : ℕ => (M j : ℝ)) hcellD hMr hDs2 hDs3
    rcases hsD with
      ⟨hDH, hDNH, hD4, hDHinv, hDy, hDsmall, hDeta, hDres, hDKres,
        JDtime, JDpos, hDJorder, hDtime, hDpositive, hDeps⟩
    have hlogR : Tendsto (fun j : ℕ => Real.log (F (xr j) / g (xr j)))
        atTop (𝓝 (0 : ℝ)) := brownian_log_seq xr hRsmall
    have hlogD : Tendsto (fun j : ℕ => Real.log (F (yd j) / g (yd j)))
        atTop (𝓝 (0 : ℝ)) := brownian_log_seq yd hDsmall
    have htotal : Tendsto (fun j : ℕ =>
        (Real.log (RademacherS4Assembly.Q B P hB (K j) (M j : ℝ)) -
          RademacherS4Assembly.w (M j) (K j) (M j : ℝ)) +
        Real.log (F (yd j) / g (yd j)) - Real.log (F (xr j) / g (xr j)))
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [add_zero, sub_zero] using (hDres.add hlogD).sub hlogR
    obtain ⟨JRe, hJRe⟩ := (Metric.tendsto_atTop.mp hRres) ε hε
    obtain ⟨JDe, hJDe⟩ := (Metric.tendsto_atTop.mp htotal) ε hε
    filter_upwards [eventually_ge_atTop (1 : ℕ),
      eventually_ge_atTop JRpos, eventually_ge_atTop JDpos,
      eventually_ge_atTop JRe, eventually_ge_atTop JDe] with j hj1 hjR hjD hjeR hjeD
    rcases hgeom j hj1 with
      ⟨hmpos, hkpos, hHpos, hHlower, hRs2j, hRs3j, hDs2j, hDs3j, hxarg, hxinv⟩
    rcases (hRpositive j hjR).1 with
      ⟨hR1, hRpos, hRHpos, hRapos, hRrho, hRrholt, hRarho, hRpia,
        hRpK, hpR, hRKpos, hRDpos, hbR, hRgpos, hRTpos, hRQQK, hRQpos, hRQKpos⟩
    rcases (hDpositive j hjD).1 with
      ⟨hD1, hDpos, hDHpos, hDapos, hDrho, hDrholt, hDarho, hDpia,
        hDpK, hpD, hDKpos, hDDpos, hbD, hDgpos, hDTpos, hDQQK, hDQpos, hDQKpos⟩
    have hxr : xr j = criticalX (M j) := by
      change randomHeight (M j) (K j) / Real.sqrt (K j : ℝ) = criticalX (M j)
      exact hxarg
    have hbase : baseline B P hB (M j) = F (xr j) := by
      rw [hxr]
      rfl
    have hb : 0 < baseline B P hB (M j) := by
      rw [hbase]
      exact hbR
    have hxF : 0 < F (xr j) := hbR
    have hyF : 0 < F (yd j) := hbD
    have hQR : RademacherS4Assembly.Q B P hB (K j) (HR j) =
        RademacherS4Assembly.p (K j) (randomHeight (M j) (K j)) /
          baseline B P hB (M j) := by
      change RademacherS4Assembly.p (K j) (HR j) / F (xr j) = _
      rw [← hbase]
    have hwR : RademacherS4Assembly.w (cell j) (K j) (HR j) =
        phaseExponent (M j) (K j) := by
      rcases RademacherS4Assembly.definition_bridges (cell j) (K j) (HR j) with
        ⟨hH, hH', hN, ht, hu, ha, ha', ha'', hrho, hrho', hrho'', hlambda,
          hdelta, hthird, hA, hx, hCdet, hw, hCDA⟩
      rw [hw, hH, hN]
      rfl
    have hQD : RademacherS4Assembly.Q B P hB (K j) (M j : ℝ) =
        RademacherS4Assembly.p (K j) (M j : ℝ) / F (yd j) := rfl
    have hwD : RademacherS4Assembly.w (M j) (K j) (M j : ℝ) =
        (Real.pi ^ 2 / 4) * ((K j : ℝ) / (M j : ℝ) ^ 3) := by
      rcases RademacherS4Assembly.definition_bridges (M j) (K j) (M j : ℝ) with
        ⟨hH, hH', hN, ht, hu, ha, ha', ha'', hrho, hrho', hrho'', hlambda,
          hdelta, hthird, hA, hx, hCdet, hw, hCDA⟩
      rw [hw, hH, hN]
      ring
    have hiy : 1 / yd j ^ 2 = (K j : ℝ) / (M j : ℝ) ^ 2 := by
      change (1 : ℝ) / ((M j : ℝ) / Real.sqrt (K j : ℝ)) ^ 2 = _
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg (K j))]
      field_simp [hmpos.ne', hkpos.ne']
      <;> ring
    have hix : 1 / xr j ^ 2 = 2 * (M j : ℝ) := by
      rw [hxr]
      exact hxinv
    have hly : (Real.pi ^ 2 / 8) / yd j ^ 2 =
        (Real.pi ^ 2 / 8) * ((K j : ℝ) / (M j : ℝ) ^ 2) := by
      rw [div_eq_mul_one_div, hiy]
    have hlx : (Real.pi ^ 2 / 8) / xr j ^ 2 =
        (Real.pi ^ 2 / 8) * (2 * (M j : ℝ)) := by
      rw [div_eq_mul_one_div, hix]
    have hcancel : Real.log (g (yd j)) - Real.log (g (xr j)) +
        (Real.pi ^ 2 / 8) * ((K j : ℝ) - (meanIndex (M j) : ℝ)) /
          (M j : ℝ) ^ 2 = 0 := by
      rw [g_log, g_log, hly, hlx]
      simp only [meanIndex, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
      field_simp [hmpos.ne']
      <;> ring
    have hdet_identity :
        Real.log (RademacherS4Assembly.p (K j) (M j : ℝ) /
          baseline B P hB (M j)) +
          (Real.pi ^ 2 / 8) * ((K j : ℝ) - (meanIndex (M j) : ℝ)) /
            (M j : ℝ) ^ 2 -
          (Real.pi ^ 2 / 4) * ((K j : ℝ) / (M j : ℝ) ^ 3) =
        (Real.log (RademacherS4Assembly.Q B P hB (K j) (M j : ℝ)) -
          RademacherS4Assembly.w (M j) (K j) (M j : ℝ)) +
          Real.log (F (yd j) / g (yd j)) - Real.log (F (xr j) / g (xr j)) := by
      rw [hbase, hQD, hwD,
        Real.log_div hpD.ne' hxF.ne', Real.log_div hpD.ne' hyF.ne',
        Real.log_div hyF.ne' (g_pos (yd j)).ne',
        Real.log_div hxF.ne' (g_pos (xr j)).ne']
      linarith [hcancel]
    have hrandom_error :
        |Real.log (RademacherS4Assembly.p (K j) (randomHeight (M j) (K j)) /
          baseline B P hB (M j)) - phaseExponent (M j) (K j)| < ε := by
      have h := hJRe j hjeR
      simpa only [Real.dist_eq, sub_zero, hQR, hwR] using h
    have hdet_error :
        |Real.log (RademacherS4Assembly.p (K j) (M j : ℝ) /
          baseline B P hB (M j)) +
          (Real.pi ^ 2 / 8) * ((K j : ℝ) - (meanIndex (M j) : ℝ)) /
            (M j : ℝ) ^ 2 -
          (Real.pi ^ 2 / 4) * ((K j : ℝ) / (M j : ℝ) ^ 3)| < ε := by
      rw [hdet_identity]
      simpa only [Real.dist_eq, sub_zero] using hJDe j hjeD
    exact ⟨hb, hpR, hpD, hrandom_error, hdet_error⟩
  obtain ⟨J, hJ⟩ := uniform_extract G hseq
  refine ⟨max 1 J, le_max_left _ _, ?_⟩
  intro m hm k hl hu
  exact hJ m (le_trans (le_max_right _ _) hm) k hl hu


theorem critical_limits {Ω : Type u} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    Tendsto (randomRatio B P hB) atTop
      (𝓝 ((1 + Real.exp (Real.pi ^ 2 / 2)) / 2)) ∧
    Tendsto (detRatio B P hB) atTop
      (𝓝 (Real.exp (Real.pi ^ 2 / 2))) := by
  classical
  have mixture_ratios (m : ℕ) (hm : 1 ≤ m) :
      randomRatio B P hB m =
        (∑ k ∈ Finset.range (time m + 1),
          weight (time m) k *
            (RademacherS4Assembly.p k (randomHeight m k) /
              baseline B P hB m)) ∧
      detRatio B P hB m =
        (∑ k ∈ Finset.range (time m + 1),
          weight (time m) k *
            (RademacherS4Assembly.p k (m : ℝ) /
              baseline B P hB m)) := by
    rcases critical_scale m hm with ⟨htime, hmean, hxpos, hxvalue, hwall⟩
    rcases exact_mixtures (time m) (criticalX m) hxpos.le with ⟨hrandom, hdet⟩
    constructor
    · unfold randomRatio
      rw [hrandom, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [randomHeight]
      ring
    · unfold detRatio
      rw [hdet, hwall, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      ring

  have p_bounds (k : ℕ) (h : ℝ) :
      0 ≤ RademacherS4Assembly.p k h ∧ RademacherS4Assembly.p k h ≤ 1 := by
    change 0 ≤ (Measure.pi (fun _ : Fin k => RademacherCosine.law)).real
        (@Shao.closedStrip k h) ∧
      (Measure.pi (fun _ : Fin k => RademacherCosine.law)).real
        (@Shao.closedStrip k h) ≤ 1
    exact ⟨measureReal_nonneg, measureReal_le_one⟩

  have weighted_square (S : Finset ℕ) (w z : ℕ → ℝ)
      (hw : ∀ k ∈ S, 0 ≤ w k) :
      (∑ k ∈ S, w k * z k) ^ 2 ≤
        (∑ k ∈ S, w k) * (∑ k ∈ S, w k * (z k) ^ 2) := by
    let q : ℝ := ∑ k ∈ S, w k
    let s : ℝ := ∑ k ∈ S, w k * z k
    let a : ℝ := ∑ k ∈ S, w k * (z k) ^ 2
    have hq : 0 ≤ q := Finset.sum_nonneg hw
    have ha : 0 ≤ a := Finset.sum_nonneg fun k hk =>
      mul_nonneg (hw k hk) (sq_nonneg _)
    change s ^ 2 ≤ q * a
    by_cases hq0 : q = 0
    · have hz (k : ℕ) (hk : k ∈ S) : w k = 0 := by
        have hsingle : w k ≤ ∑ j ∈ S, w j :=
          Finset.single_le_sum hw hk
        change w k ≤ q at hsingle
        exact le_antisymm (hq0 ▸ hsingle) (hw k hk)
      have hs : s = 0 := Finset.sum_eq_zero fun k hk => by rw [hz k hk, zero_mul]
      rw [hs, hq0]
      norm_num
    · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
      have hnonneg : 0 ≤ ∑ k ∈ S, w k * (z k - s / q) ^ 2 :=
        Finset.sum_nonneg fun k hk => mul_nonneg (hw k hk) (sq_nonneg _)
      have hexpand :
          (∑ k ∈ S, w k * (z k - s / q) ^ 2) =
            a - 2 * (s / q) * s + (s / q) ^ 2 * q := by
        calc
          _ = ∑ k ∈ S,
              (w k * (z k) ^ 2 - (2 * (s / q)) * (w k * z k) +
                (s / q) ^ 2 * w k) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
          _ = _ := by
            simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              Finset.mul_sum, q, s, a]
      rw [hexpand] at hnonneg
      have hmult := mul_nonneg hq hnonneg
      have halg : q * (a - 2 * (s / q) * s + (s / q) ^ 2 * q) =
          q * a - s ^ 2 := by
        field_simp [hq0]
        <;> ring
      rw [halg] at hmult
      linarith

  have finite_chebyshev (I : Finset ℕ) (w Z : ℕ → ℝ) (D : ℝ)
      (hD : 0 < D) (hw : ∀ k ∈ I, 0 ≤ w k) :
      (∑ k ∈ I.filter (fun k => D < |Z k|), w k) ≤
        (∑ k ∈ I, w k * (Z k) ^ 2) / D ^ 2 := by
    have hD2 : 0 < D ^ 2 := sq_pos_of_pos hD
    apply (le_div_iff₀ hD2).2
    calc
      (∑ k ∈ I.filter (fun k => D < |Z k|), w k) * D ^ 2 =
          ∑ k ∈ I.filter (fun k => D < |Z k|), w k * D ^ 2 :=
        Finset.sum_mul _ _ _
      _ ≤ ∑ k ∈ I.filter (fun k => D < |Z k|), w k * (Z k) ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        rcases Finset.mem_filter.mp hk with ⟨hkI, hkD⟩
        apply mul_le_mul_of_nonneg_left _ (hw k hkI)
        have hprod := mul_pos (sub_pos.mpr hkD)
          (show 0 < |Z k| + D by positivity)
        nlinarith [sq_abs (Z k)]
      _ ≤ ∑ k ∈ I, w k * (Z k) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun k hkI hkT => mul_nonneg (hw k hkI) (sq_nonneg _))

  have finite_tilted_tail (I T : Finset ℕ) (w Z : ℕ → ℝ) (t M : ℝ)
      (hTI : T ⊆ I) (hw : ∀ k ∈ I, 0 ≤ w k)
      (hM : (∑ k ∈ I, w k * Real.exp ((-2 * t) * Z k)) ≤ M) :
      (∑ k ∈ T, w k * Real.exp (-t * Z k)) ≤
        Real.sqrt M * Real.sqrt (∑ k ∈ T, w k) := by
    have hwp (k : ℕ) (hk : k ∈ T) : 0 ≤ w k := hw k (hTI hk)
    have hq : 0 ≤ ∑ k ∈ T, w k := Finset.sum_nonneg hwp
    have hS : 0 ≤ ∑ k ∈ T, w k * Real.exp (-t * Z k) :=
      Finset.sum_nonneg fun k hk => mul_nonneg (hwp k hk) (Real.exp_nonneg _)
    have hM0 : 0 ≤ M := le_trans
      (Finset.sum_nonneg fun k hk => mul_nonneg (hw k hk) (Real.exp_nonneg _)) hM
    have hM' : (∑ k ∈ T, w k * (Real.exp (-t * Z k)) ^ 2) ≤ M := by
      calc
        _ = ∑ k ∈ T, w k * Real.exp ((-2 * t) * Z k) := by
          apply Finset.sum_congr rfl
          intro k hk
          congr 1
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
        _ ≤ ∑ k ∈ I, w k * Real.exp ((-2 * t) * Z k) :=
          Finset.sum_le_sum_of_subset_of_nonneg hTI
            (fun k hk _ => mul_nonneg (hw k hk) (Real.exp_nonneg _))
        _ ≤ M := hM
    have hsq := weighted_square T w (fun k => Real.exp (-t * Z k)) hwp
    have hsq' : (∑ k ∈ T, w k * Real.exp (-t * Z k)) ^ 2 ≤
        M * (∑ k ∈ T, w k) :=
      hsq.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hM' hq)
    have hroot : 0 ≤ Real.sqrt M * Real.sqrt (∑ k ∈ T, w k) := by positivity
    have hroot2 : (Real.sqrt M * Real.sqrt (∑ k ∈ T, w k)) ^ 2 =
        M * (∑ k ∈ T, w k) := by
      rw [mul_pow, Real.sq_sqrt hM0, Real.sq_sqrt hq]
    nlinarith

  have exp_error (r a d : ℝ) (hr : 0 < r) (hd : 0 ≤ d)
      (hlog : |Real.log r - a| ≤ d) :
      |r - Real.exp a| ≤ Real.exp a * (Real.exp d - 1) := by
    have he : 0 < Real.exp d := Real.exp_pos _
    have he1 : 1 ≤ Real.exp d := Real.one_le_exp hd
    have hu : r ≤ Real.exp a * Real.exp d := by
      rw [← Real.exp_add, ← Real.exp_log hr]
      exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp hlog).2])
    have hl : Real.exp a / Real.exp d ≤ r := by
      rw [← Real.exp_sub, ← Real.exp_log hr]
      exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp hlog).1])
    have hinv : 2 - Real.exp d ≤ 1 / Real.exp d := by
      apply (le_div_iff₀ he).2
      nlinarith [sq_nonneg (Real.exp d - 1)]
    have hl' : Real.exp a * (2 - Real.exp d) ≤ r := by
      calc
        _ ≤ Real.exp a * (1 / Real.exp d) :=
          mul_le_mul_of_nonneg_left hinv (Real.exp_nonneg _)
        _ = Real.exp a / Real.exp d := by ring
        _ ≤ r := hl
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

  have finite_compare (I : Finset ℕ) (w f v z : ℕ → ℝ)
      (G L : ℕ → Prop) [DecidablePred G] [DecidablePred L]
      (e E C b : ℝ)
      (hw : ∀ k ∈ I, 0 ≤ w k) (hw1 : (∑ k ∈ I, w k) = 1)
      (he : 0 ≤ e) (hE : 0 ≤ E) (hC : 0 ≤ C) (hb : 0 ≤ b)
      (hf : ∀ k ∈ I, 0 ≤ f k)
      (hv : ∀ k ∈ I, 0 ≤ v k ∧ v k ≤ E)
      (hz : ∀ k ∈ I, 0 ≤ z k)
      (hcentral : ∀ k ∈ I, G k → |f k - v k| ≤ e)
      (hlow : ∀ k ∈ I, L k → f k ≤ b)
      (hhigh : ∀ k ∈ I, ¬ L k → f k ≤ C * z k) :
      |(∑ k ∈ I, w k * f k) - (∑ k ∈ I, w k * v k)| ≤
        e + b * (∑ k ∈ I.filter L, w k) +
          C * (∑ k ∈ I.filter (fun k => ¬ G k), w k * z k) +
          E * (∑ k ∈ I.filter (fun k => ¬ G k), w k) := by
    have hp (k : ℕ) (hk : k ∈ I) :
        w k * |f k - v k| ≤
          e * w k + (if L k then b * w k else 0) +
            (if ¬ G k then C * (w k * z k) + E * w k else 0) := by
      by_cases hg : G k
      · have hmain := mul_le_mul_of_nonneg_left (hcentral k hk hg) (hw k hk)
        by_cases hl : L k <;> simp only [hg, not_true_eq_false, hl, if_true, if_false]
        · nlinarith [mul_nonneg hb (hw k hk)]
        · nlinarith
      · have ha : |f k - v k| ≤ f k + E := by
          exact abs_le.mpr ⟨by linarith [(hf k hk), (hv k hk).2],
            by linarith [(hv k hk).1]⟩
        have hmul := mul_le_mul_of_nonneg_left ha (hw k hk)
        have hew := mul_nonneg he (hw k hk)
        have hcz := mul_nonneg hC (mul_nonneg (hw k hk) (hz k hk))
        by_cases hl : L k
        · have hbound := mul_le_mul_of_nonneg_left (hlow k hk hl) (hw k hk)
          simp only [hg, not_false_eq_true, hl, if_true]
          nlinarith
        · have hbound := mul_le_mul_of_nonneg_left (hhigh k hk hl) (hw k hk)
          simp only [hg, not_false_eq_true, hl, if_false, if_true]
          nlinarith
    calc
      _ = |∑ k ∈ I, w k * (f k - v k)| := by
        congr 1
        simp only [mul_sub, Finset.sum_sub_distrib]
      _ ≤ ∑ k ∈ I, |w k * (f k - v k)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k ∈ I, w k * |f k - v k| := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [abs_mul, abs_of_nonneg (hw k hk)]
      _ ≤ ∑ k ∈ I,
          (e * w k + (if L k then b * w k else 0) +
            (if ¬ G k then C * (w k * z k) + E * w k else 0)) :=
        Finset.sum_le_sum hp
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.mul_sum,
          hw1, mul_one] <;> ring

  have height_algebra (m k : ℕ) (hm : 1 ≤ m) :
      0 ≤ randomHeight m k ∧
      2 * (m : ℝ) * randomHeight m k ^ 2 = (k : ℝ) := by
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
    have hs : 0 < Real.sqrt (2 * (m : ℝ)) := Real.sqrt_pos.mpr (by positivity)
    rcases critical_scale m hm with ⟨_, _, hx, hxvalue, _⟩
    constructor
    · exact mul_nonneg hx.le (Real.sqrt_nonneg _)
    · rw [randomHeight, hxvalue, mul_pow, one_div_pow,
        Real.sq_sqrt (by positivity : 0 ≤ 2 * (m : ℝ)),
        Real.sq_sqrt (Nat.cast_nonneg k)]
      field_simp [hmpos.ne']
      <;> ring

  have height_nonlow (m k : ℕ) (hm : 1 ≤ m) (hk : m ^ 3 ≤ k) :
      0 < randomHeight m k ∧ (m : ℝ) / 2 ≤ randomHeight m k ∧
      (k : ℝ) / randomHeight m k ^ 3 =
        2 * (m : ℝ) / randomHeight m k ∧
      0 ≤ (k : ℝ) / randomHeight m k ^ 3 ∧
      (k : ℝ) / randomHeight m k ^ 3 ≤ 4 := by
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
    have hkR : (m : ℝ) ^ 3 ≤ (k : ℝ) := by exact_mod_cast hk
    rcases height_algebra m k hm with ⟨hh0, hh2⟩
    have hh : 0 < randomHeight m k := by
      by_contra h
      have heq := le_antisymm (le_of_not_gt h) hh0
      rw [heq] at hh2
      nlinarith [pow_pos hmpos 3]
    have hhhalf : (m : ℝ) / 2 ≤ randomHeight m k := by
      by_contra h
      have hsmall : randomHeight m k < (m : ℝ) / 2 := lt_of_not_ge h
      have hsqsmall : randomHeight m k ^ 2 < ((m : ℝ) / 2) ^ 2 := by
        have hprod := mul_pos (sub_pos.mpr hsmall)
          (show 0 < (m : ℝ) / 2 + randomHeight m k by positivity)
        nlinarith
      have hprod := mul_lt_mul_of_pos_left hsqsmall (by positivity : 0 < 2 * (m : ℝ))
      nlinarith [pow_pos hmpos 3]
    have hU : (k : ℝ) / randomHeight m k ^ 3 =
        2 * (m : ℝ) / randomHeight m k := by
      rw [← hh2]
      field_simp [hh.ne']
      <;> ring
    refine ⟨hh, hhhalf, hU, by positivity, ?_⟩
    rw [hU]
    exact (div_le_iff₀ hh).mpr (by linarith)

  have phase_bounds (m k : ℕ) (hm : 1 ≤ m) (hk : m ^ 3 ≤ k) :
      0 ≤ phaseExponent m k ∧ phaseExponent m k ≤ Real.pi ^ 2 := by
    rcases height_nonlow m k hm hk with ⟨hh, hhhalf, hU, hU0, hU4⟩
    have hd0 : 0 ≤ (⌊randomHeight m k⌋₊ : ℝ) + 1 - randomHeight m k :=
      le_of_lt (by linarith [Nat.lt_floor_add_one (randomHeight m k)])
    have hd1 : (⌊randomHeight m k⌋₊ : ℝ) + 1 - randomHeight m k ≤ 1 := by
      linarith [Nat.floor_le hh.le]
    change 0 ≤ (Real.pi ^ 2 / 4) * ((k : ℝ) / randomHeight m k ^ 3) *
        ((⌊randomHeight m k⌋₊ : ℝ) + 1 - randomHeight m k) ∧
      (Real.pi ^ 2 / 4) * ((k : ℝ) / randomHeight m k ^ 3) *
        ((⌊randomHeight m k⌋₊ : ℝ) + 1 - randomHeight m k) ≤ Real.pi ^ 2
    constructor
    · positivity
    · have hmul := mul_le_mul hU4 hd1 hd0 (by norm_num : (0 : ℝ) ≤ 4)
      have hc := mul_le_mul_of_nonneg_left hmul (by positivity : 0 ≤ Real.pi ^ 2 / 4)
      nlinarith

  have central_height (m k : ℕ) (hm : 1 ≤ m) (d : ℝ)
      (hd : 0 < d) (hd1 : d ≤ 1 / 2)
      (hband : |(k : ℝ) - (meanIndex m : ℝ)| ≤ d * (m : ℝ) ^ 2) :
      m ^ 3 ≤ k ∧ |randomHeight m k - (m : ℝ)| ≤ d / 2 := by
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hmpos : 0 < (m : ℝ) := by linarith
    have hmean : (meanIndex m : ℝ) = 2 * (m : ℝ) ^ 3 := by
      simp only [meanIndex, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    rw [hmean] at hband
    rcases abs_le.mp hband with ⟨hbandlo, hbandhi⟩
    rcases height_algebra m k hm with ⟨hh0, hh2⟩
    have hm2 : 0 < (m : ℝ) ^ 2 := sq_pos_of_pos hmpos
    have hm3 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 3 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hmR) (sq_nonneg (m : ℝ))]
    have hkR : (m : ℝ) ^ 3 ≤ (k : ℝ) := by
      have hdM : d * (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 :=
        mul_le_of_le_one_left hm2.le (by linarith)
      linarith
    have habsId : |(k : ℝ) - 2 * (m : ℝ) ^ 3| =
        2 * (m : ℝ) *
          (|randomHeight m k - (m : ℝ)| * (randomHeight m k + (m : ℝ))) := by
      calc
        _ = |(2 * (m : ℝ)) *
            ((randomHeight m k - (m : ℝ)) * (randomHeight m k + (m : ℝ)))| := by
          congr 1
          nlinarith [hh2]
        _ = _ := by
          rw [abs_mul, abs_of_pos (show 0 < 2 * (m : ℝ) by positivity), abs_mul,
            abs_of_nonneg (show 0 ≤ randomHeight m k + (m : ℝ) by positivity)]
    have hband' : |(k : ℝ) - 2 * (m : ℝ) ^ 3| ≤ d * (m : ℝ) ^ 2 :=
      abs_le.mpr ⟨hbandlo, hbandhi⟩
    have hmin : |randomHeight m k - (m : ℝ)| * (m : ℝ) ≤
        |randomHeight m k - (m : ℝ)| * (randomHeight m k + (m : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    have hmin' := mul_le_mul_of_nonneg_left hmin (by positivity : 0 ≤ 2 * (m : ℝ))
    rw [habsId] at hband'
    constructor
    · exact_mod_cast hkR
    · have hcancel : (2 * |randomHeight m k - (m : ℝ)|) * (m : ℝ) ^ 2 ≤
          d * (m : ℝ) ^ 2 := by nlinarith only [hmin', hband']
      have hsmall := (mul_le_mul_iff_of_pos_right hm2).mp hcancel
      linarith

  have central_phase (m k : ℕ) (hm : 1 ≤ m) (d : ℝ)
      (hd : 0 < d) (hd1 : d ≤ 1 / 2)
      (hband : |(k : ℝ) - (meanIndex m : ℝ)| ≤ d * (m : ℝ) ^ 2) :
      |phaseExponent m k -
        (if k < meanIndex m then 0 else Real.pi ^ 2 / 2)| ≤ Real.pi ^ 2 * d := by
    rcases central_height m k hm d hd hd1 hband with ⟨hknonlow, hhclose⟩
    rcases height_nonlow m k hm hknonlow with ⟨hhpos, hhhalf, hU, hU0, hU4⟩
    rcases height_algebra m k hm with ⟨hh0, hh2⟩
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hmean : (meanIndex m : ℝ) = 2 * (m : ℝ) ^ 3 := by
      simp only [meanIndex, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    have hc0 : 0 ≤ Real.pi ^ 2 / 4 := by positivity
    let H : ℝ := randomHeight m k
    let U : ℝ := (k : ℝ) / H ^ 3
    let c : ℝ := Real.pi ^ 2 / 4
    have hHclose : |H - (m : ℝ)| ≤ d / 2 := hhclose
    have hHpos : 0 < H := hhpos
    have hHhalf : (1 / 2 : ℝ) ≤ H := le_trans (by linarith) hhhalf
    have hUeq : U * H = 2 * (m : ℝ) := by
      change ((k : ℝ) / randomHeight m k ^ 3) * randomHeight m k = _
      rw [hU]
      exact div_mul_cancel₀ _ hhpos.ne'
    have hUclose : |U - 2| ≤ 2 * d := by
      have habs : |U - 2| * H = 2 * |H - (m : ℝ)| := by
        calc
          _ = |(U - 2) * H| := by rw [abs_mul, abs_of_pos hHpos]
          _ = |(-2) * (H - (m : ℝ))| := by congr 1; nlinarith [hUeq]
          _ = _ := by rw [abs_mul]; norm_num
      have hsmall := mul_le_mul_of_nonneg_left hHhalf (abs_nonneg (U - 2))
      nlinarith
    have hc : 0 ≤ c := hc0
    have hcId : 2 * c = Real.pi ^ 2 / 2 := by dsimp [c]; ring
    by_cases hk : k < meanIndex m
    · have hkR : (k : ℝ) < 2 * (m : ℝ) ^ 3 := by
        rw [← hmean]
        exact_mod_cast hk
      have hHlt : H < (m : ℝ) := by
        change 2 * (m : ℝ) * H ^ 2 = (k : ℝ) at hh2
        by_contra h
        have hle : (m : ℝ) ≤ H := le_of_not_gt h
        have hsq : (m : ℝ) ^ 2 ≤ H ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hle)
            (show 0 ≤ H + (m : ℝ) by positivity)]
        have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 2 * (m : ℝ))
        nlinarith
      have hHm1 : ((m - 1 : ℕ) : ℝ) ≤ H := by
        rw [Nat.cast_sub hm]
        norm_num
        linarith [(abs_le.mp hHclose).1]
      have hfloor : ⌊H⌋₊ = m - 1 := (Nat.floor_eq_iff hh0).mpr
        ⟨hHm1, by rw [Nat.cast_sub hm]; norm_num; exact hHlt⟩
      have hdelta : (⌊H⌋₊ : ℝ) + 1 - H = (m : ℝ) - H := by
        rw [hfloor, Nat.cast_sub hm]
        norm_num
      have hdelta0 : 0 ≤ (m : ℝ) - H := by linarith
      have hdeltaD : (m : ℝ) - H ≤ d / 2 := by
        linarith [(abs_le.mp hHclose).1]
      have hup : c * U * ((m : ℝ) - H) ≤ c * (4 * (d / 2)) := by
        have hU4local : U ≤ 4 := hU4
        simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left
          (mul_le_mul hU4local hdeltaD hdelta0 (by norm_num)) hc)
      rw [if_pos hk]
      change |c * U * ((⌊H⌋₊ : ℝ) + 1 - H) - 0| ≤ _
      rw [hdelta, sub_zero, abs_of_nonneg (by positivity)]
      dsimp only [c] at hup ⊢
      nlinarith only [hup, mul_nonneg (sq_nonneg Real.pi) hd.le]
    · have hkR : 2 * (m : ℝ) ^ 3 ≤ (k : ℝ) := by
        rw [← hmean]
        exact_mod_cast (Nat.le_of_not_gt hk)
      have hmH : (m : ℝ) ≤ H := by
        change 2 * (m : ℝ) * H ^ 2 = (k : ℝ) at hh2
        by_contra h
        have hlt : H < (m : ℝ) := lt_of_not_ge h
        have hsq : H ^ 2 < (m : ℝ) ^ 2 := by
          nlinarith [mul_pos (sub_pos.mpr hlt)
            (show 0 < (m : ℝ) + H by positivity)]
        have hmul := mul_lt_mul_of_pos_left hsq (by positivity : 0 < 2 * (m : ℝ))
        nlinarith
      have hHlt : H < (m : ℝ) + 1 := by linarith [(abs_le.mp hHclose).2]
      have hfloor : ⌊H⌋₊ = m := (Nat.floor_eq_iff hh0).mpr ⟨hmH, hHlt⟩
      let δ : ℝ := (m : ℝ) + 1 - H
      have hδ0 : 0 ≤ δ := by dsimp [δ]; linarith
      have hδ1 : δ ≤ 1 := by dsimp [δ]; linarith
      have hδclose : |δ - 1| ≤ d / 2 := by
        have heq : δ - 1 = -(H - (m : ℝ)) := by dsimp [δ]; ring
        rw [heq, abs_neg]
        exact hHclose
      rw [if_neg hk]
      change |c * U * ((⌊H⌋₊ : ℝ) + 1 - H) - Real.pi ^ 2 / 2| ≤ _
      rw [hfloor, ← hcId]
      change |c * U * δ - 2 * c| ≤ _
      calc
        _ = c * |(U - 2) * δ + 2 * (δ - 1)| := by
          calc
            _ = |c * ((U - 2) * δ + 2 * (δ - 1))| := by congr 1; ring
            _ = _ := by rw [abs_mul, abs_of_nonneg hc]
        _ ≤ c * (|(U - 2) * δ| + |2 * (δ - 1)|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) hc
        _ = c * (|U - 2| * δ + 2 * |δ - 1|) := by
          rw [abs_mul, abs_of_nonneg hδ0, abs_mul]
          norm_num
        _ ≤ c * ((2 * d) * 1 + 2 * (d / 2)) := by
          apply mul_le_mul_of_nonneg_left _ hc
          have hu := mul_le_mul hUclose hδ1 hδ0 (by positivity : 0 ≤ 2 * d)
          nlinarith
        _ ≤ Real.pi ^ 2 * d := by dsimp [c]; nlinarith [mul_nonneg (sq_nonneg Real.pi) hd.le]

  have central_det_algebra (m k : ℕ) (hm : 1 ≤ m) (d : ℝ)
      (hd : 0 ≤ d)
      (hband : |(k : ℝ) - (meanIndex m : ℝ)| ≤ d * (m : ℝ) ^ 2) :
      |-(Real.pi ^ 2 / 8) * ((k : ℝ) - (meanIndex m : ℝ)) / (m : ℝ) ^ 2 +
          (Real.pi ^ 2 / 4) * ((k : ℝ) / (m : ℝ) ^ 3) - Real.pi ^ 2 / 2| ≤
        (3 * (Real.pi ^ 2 / 8)) * d := by
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hmpos : 0 < (m : ℝ) := by linarith
    have hm2 : 0 < (m : ℝ) ^ 2 := sq_pos_of_pos hmpos
    have hm3 : 0 < (m : ℝ) ^ 3 := pow_pos hmpos 3
    have hm23 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 3 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hmR) (sq_nonneg (m : ℝ))]
    have hmean : (meanIndex m : ℝ) = 2 * (m : ℝ) ^ 3 := by
      simp only [meanIndex, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    have hdiv2 : |((k : ℝ) - (meanIndex m : ℝ)) / (m : ℝ) ^ 2| ≤ d := by
      rw [abs_div, abs_of_pos hm2]
      exact (div_le_iff₀ hm2).mpr hband
    have hdiv3 : |((k : ℝ) - (meanIndex m : ℝ)) / (m : ℝ) ^ 3| ≤ d := by
      rw [abs_div, abs_of_pos hm3]
      apply (div_le_iff₀ hm3).mpr
      exact hband.trans (mul_le_mul_of_nonneg_left hm23 hd)
    have halg :
        -(Real.pi ^ 2 / 8) * ((k : ℝ) - (meanIndex m : ℝ)) / (m : ℝ) ^ 2 +
            (Real.pi ^ 2 / 4) * ((k : ℝ) / (m : ℝ) ^ 3) - Real.pi ^ 2 / 2 =
          -(Real.pi ^ 2 / 8) * (((k : ℝ) - (meanIndex m : ℝ)) / (m : ℝ) ^ 2) +
            (Real.pi ^ 2 / 4) * (((k : ℝ) - (meanIndex m : ℝ)) / (m : ℝ) ^ 3) := by
      rw [hmean]
      field_simp [hmpos.ne']
      <;> ring
    rw [halg]
    calc
      _ ≤ |-(Real.pi ^ 2 / 8) * (((k : ℝ) - (meanIndex m : ℝ)) / (m : ℝ) ^ 2)| +
          |(Real.pi ^ 2 / 4) * (((k : ℝ) - (meanIndex m : ℝ)) / (m : ℝ) ^ 3)| := abs_add_le _ _
      _ ≤ (Real.pi ^ 2 / 8) * d + (Real.pi ^ 2 / 4) * d := by
        simp only [abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ Real.pi ^ 2 / 8),
          abs_of_nonneg (by positivity : 0 ≤ Real.pi ^ 2 / 4)]
        exact add_le_add
          (mul_le_mul_of_nonneg_left hdiv2 (by positivity))
          (mul_le_mul_of_nonneg_left hdiv3 (by positivity))
      _ = _ := by ring

  let I (m : ℕ) : Finset ℕ := Finset.range (time m + 1)
  let W (m k : ℕ) : ℝ := weight (time m) k
  let Z (m k : ℕ) : ℝ := (k : ℝ) - (meanIndex m : ℝ)
  let R (m k : ℕ) : ℝ :=
    RademacherS4Assembly.p k (randomHeight m k) / baseline B P hB m
  let A (m k : ℕ) : ℝ :=
    RademacherS4Assembly.p k (m : ℝ) / baseline B P hB m
  let lam : ℝ := Real.pi ^ 2 / 8
  let a : ℝ := Real.pi ^ 2 / 2
  let E : ℝ := Real.exp a
  let C : ℝ := Real.exp (1 + 2 * Real.pi ^ 2)
  let V (m k : ℕ) : ℝ := if k < meanIndex m then 1 else E
  let tilt (m k : ℕ) : ℝ := Real.exp (-(lam / (m : ℝ) ^ 2) * Z m k)
  have hEpos : 0 < E := Real.exp_pos _
  have hE1 : 1 ≤ E := Real.one_le_exp (by dsimp [a]; positivity)
  have hCpos : 0 < C := Real.exp_pos _
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have wpos (m : ℕ) (hm : 1 ≤ m) (k : ℕ) : 0 ≤ W m k :=
    (binomial_payments m hm).1 k
  have wsum (m : ℕ) (hm : 1 ≤ m) : (∑ k ∈ I m, W m k) = 1 :=
    (binomial_payments m hm).2.1
  have v_bounds (m k : ℕ) : 0 ≤ V m k ∧ V m k ≤ E := by
    dsimp [V]
    split_ifs <;> constructor <;> linarith

  have global_bounds : ∃ J : ℕ, 1 ≤ J ∧ ∀ m : ℕ, J ≤ m →
      0 < baseline B P hB m ∧
      ∀ k ∈ I m, m ^ 3 ≤ k →
        R m k ≤ C ∧ A m k ≤ C * tilt m k := by
    obtain ⟨J, hJ, hu⟩ := uniform_log_pair B P hB 1 (by norm_num)
    refine ⟨J, hJ, ?_⟩
    intro m hm
    have hm1 : 1 ≤ m := hJ.trans hm
    have htime : time m = 8 * m ^ 3 := (critical_scale m hm1).1
    have hkn : m ^ 3 ≤ time m := by rw [htime]; omega
    have hb := (hu m hm (m ^ 3) le_rfl hkn).1
    refine ⟨hb, ?_⟩
    intro k hkI hklo
    have hkhi : k ≤ time m := Nat.le_of_lt_succ (Finset.mem_range.mp hkI)
    rcases hu m hm k hklo hkhi with ⟨hb, hpR, hpA, hlogR, hlogA⟩
    have hr : 0 < R m k := div_pos hpR hb
    have hd : 0 < A m k := div_pos hpA hb
    have hphase := (phase_bounds m k hm1 hklo).2
    have hlogR' : Real.log (R m k) ≤ 1 + 2 * Real.pi ^ 2 := by
      change |Real.log (R m k) - phaseExponent m k| < 1 at hlogR
      have hs := (abs_lt.mp hlogR).2
      nlinarith [sq_nonneg Real.pi]
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm1)
    have hkR : (k : ℝ) ≤ 8 * (m : ℝ) ^ 3 := by
      have hk' : k ≤ 8 * m ^ 3 := hkhi.trans_eq htime
      exact_mod_cast hk'
    have hfrac : (k : ℝ) / (m : ℝ) ^ 3 ≤ 8 :=
      (div_le_iff₀ (pow_pos hmpos 3)).mpr (by nlinarith)
    have hlogA' : Real.log (A m k) ≤
        (1 + 2 * Real.pi ^ 2) + (-(lam / (m : ℝ) ^ 2) * Z m k) := by
      have hs := (abs_lt.mp hlogA).2
      have hcoef := mul_le_mul_of_nonneg_left hfrac
        (by positivity : 0 ≤ Real.pi ^ 2 / 4)
      change Real.log (A m k) + (Real.pi ^ 2 / 8) * Z m k / (m : ℝ) ^ 2 -
        (Real.pi ^ 2 / 4) * ((k : ℝ) / (m : ℝ) ^ 3) < 1 at hs
      dsimp [lam]
      have halg : -((Real.pi ^ 2 / 8) / (m : ℝ) ^ 2) * Z m k =
          -((Real.pi ^ 2 / 8) * Z m k / (m : ℝ) ^ 2) := by ring
      rw [halg]
      linarith
    constructor
    · change R m k ≤ Real.exp (1 + 2 * Real.pi ^ 2)
      rw [← Real.exp_log hr]
      exact Real.exp_le_exp.mpr hlogR'
    · change A m k ≤ Real.exp (1 + 2 * Real.pi ^ 2) *
        Real.exp (-(lam / (m : ℝ) ^ 2) * Z m k)
      rw [← Real.exp_add, ← Real.exp_log hd]
      exact Real.exp_le_exp.mpr hlogA'

  have central_errors (theta d : ℝ) (htheta : 0 < theta)
      (hd : 0 < d) (hd1 : d ≤ 1 / 2) :
      ∃ J : ℕ, 1 ≤ J ∧ ∀ m : ℕ, J ≤ m → ∀ k ∈ I m,
        |Z m k| ≤ d * (m : ℝ) ^ 2 →
          |R m k - V m k| ≤ E * (Real.exp (theta + Real.pi ^ 2 * d) - 1) ∧
          |A m k - E| ≤ E * (Real.exp (theta + Real.pi ^ 2 * d) - 1) := by
    obtain ⟨J, hJ, hu⟩ := uniform_log_pair B P hB theta htheta
    refine ⟨J, hJ, ?_⟩
    intro m hm k hkI hband
    have hm1 : 1 ≤ m := hJ.trans hm
    have hklo : m ^ 3 ≤ k := (central_height m k hm1 d hd hd1 hband).1
    have hkhi : k ≤ time m := Nat.le_of_lt_succ (Finset.mem_range.mp hkI)
    rcases hu m hm k hklo hkhi with ⟨hb, hpR, hpA, hlogR, hlogA⟩
    have hr : 0 < R m k := div_pos hpR hb
    have ha : 0 < A m k := div_pos hpA hb
    let target : ℝ := if k < meanIndex m then 0 else a
    have htarget : Real.exp target = V m k := by
      dsimp [target, V, E]
      split_ifs <;> simp
    have hphase : |phaseExponent m k - target| ≤ Real.pi ^ 2 * d :=
      central_phase m k hm1 d hd hd1 hband
    have hlogcentralR : |Real.log (R m k) - target| ≤ theta + Real.pi ^ 2 * d := by
      calc
        _ = |(Real.log (R m k) - phaseExponent m k) +
            (phaseExponent m k - target)| := by congr 1; ring
        _ ≤ |Real.log (R m k) - phaseExponent m k| +
            |phaseExponent m k - target| := abs_add_le _ _
        _ ≤ _ := add_le_add hlogR.le hphase
    have hlogcentralA : |Real.log (A m k) - a| ≤ theta + Real.pi ^ 2 * d := by
      have halg := central_det_algebra m k hm1 d hd.le hband
      have hpart :
          |-(Real.pi ^ 2 / 8) * Z m k / (m : ℝ) ^ 2 +
              (Real.pi ^ 2 / 4) * ((k : ℝ) / (m : ℝ) ^ 3) - a| ≤
            Real.pi ^ 2 * d := by
        have hc : 3 * (Real.pi ^ 2 / 8) * d ≤ Real.pi ^ 2 * d := by
          nlinarith [mul_nonneg (sq_nonneg Real.pi) hd.le]
        exact halg.trans hc
      calc
        _ = |(Real.log (A m k) + (Real.pi ^ 2 / 8) * Z m k / (m : ℝ) ^ 2 -
              (Real.pi ^ 2 / 4) * ((k : ℝ) / (m : ℝ) ^ 3)) +
            (-(Real.pi ^ 2 / 8) * Z m k / (m : ℝ) ^ 2 +
              (Real.pi ^ 2 / 4) * ((k : ℝ) / (m : ℝ) ^ 3) - a)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
        _ ≤ _ := add_le_add hlogA.le hpart
    have hgap0 : 0 ≤ theta + Real.pi ^ 2 * d := by positivity
    have hexp0 : 0 ≤ Real.exp (theta + Real.pi ^ 2 * d) - 1 := by
      linarith [Real.one_le_exp hgap0]
    constructor
    · have h := exp_error (R m k) target (theta + Real.pi ^ 2 * d) hr hgap0 hlogcentralR
      rw [htarget] at h
      exact h.trans (mul_le_mul_of_nonneg_right (v_bounds m k).2 hexp0)
    · exact exp_error (A m k) a (theta + Real.pi ^ 2 * d) ha hgap0 hlogcentralA

  let Low (m : ℕ) : ℝ :=
    (∑ k ∈ (I m).filter (fun k => k < m ^ 3), W m k) / baseline B P hB m
  let T (d : ℝ) (m : ℕ) : Finset ℕ :=
    (I m).filter (fun k => d * (m : ℝ) ^ 2 < |Z m k|)
  let Tail (d : ℝ) (m : ℕ) : ℝ := ∑ k ∈ T d m, W m k
  let TiltTail (d : ℝ) (m : ℕ) : ℝ := ∑ k ∈ T d m, W m k * tilt m k
  have hnat : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hnat
  have hpositive : ∀ᶠ m : ℕ in atTop, 1 ≤ m := eventually_ge_atTop 1

  have baseline_lower : ∀ᶠ m : ℕ in atTop,
      0 < baseline B P hB m ∧
      (2 / Real.pi) * Real.exp (-2 * lam * (m : ℝ)) ≤ baseline B P hB m := by
    have hxlim : Tendsto criticalX atTop (𝓝 (0 : ℝ)) := by
      have hs : Tendsto (fun m : ℕ => Real.sqrt (2 * (m : ℝ))) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp (hnat.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
      have h := tendsto_inv_atTop_zero.comp hs
      apply h.congr'
      filter_upwards [hpositive] with m hm
      simpa only [Function.comp_def, one_div] using (critical_scale m hm).2.2.2.1.symm
    obtain ⟨δ, hδ, hsmall⟩ := Shao.Probability.BrownianSup.actual_brownian_firstTerm
      B P hB (1 / 2) (by norm_num)
    filter_upwards [hpositive, hxlim.eventually (eventually_lt_nhds hδ)] with m hm hxδ
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
    rcases critical_scale m hm with ⟨_, _, hx, hxval, _⟩
    have hg : 0 < Shao.Probability.BrownianSup.firstTerm (criticalX m) := by
      dsimp [Shao.Probability.BrownianSup.firstTerm]
      exact mul_pos (div_pos (by norm_num) Real.pi_pos) (Real.exp_pos _)
    have hratio := (abs_lt.mp (hsmall (criticalX m) hx hxδ)).1
    have hbhalf : Shao.Probability.BrownianSup.firstTerm (criticalX m) / 2 <
        baseline B P hB m := by
      have hratio' : (1 / 2 : ℝ) < baseline B P hB m /
          Shao.Probability.BrownianSup.firstTerm (criticalX m) := by
        change -(1 / 2 : ℝ) < baseline B P hB m /
          Shao.Probability.BrownianSup.firstTerm (criticalX m) - 1 at hratio
        linarith
      have hmul := (lt_div_iff₀ hg).mp hratio'
      linarith
    have hgformula : Shao.Probability.BrownianSup.firstTerm (criticalX m) / 2 =
        (2 / Real.pi) * Real.exp (-2 * lam * (m : ℝ)) := by
      have hs : 0 ≤ 2 * (m : ℝ) := by positivity
      have hx2 : criticalX m ^ 2 = 1 / (2 * (m : ℝ)) := by
        rw [hxval, one_div_pow, Real.sq_sqrt hs]
      dsimp [Shao.Probability.BrownianSup.firstTerm]
      rw [hx2]
      have hexp : -(Real.pi ^ 2 / 8) / (1 / (2 * (m : ℝ))) =
          -2 * lam * (m : ℝ) := by
        dsimp [lam]
        field_simp [hmpos.ne']
        <;> ring
      rw [hexp]
      ring
    refine ⟨lt_trans (by positivity : 0 < Shao.Probability.BrownianSup.firstTerm (criticalX m) / 2)
      hbhalf, ?_⟩
    rw [← hgformula]
    exact hbhalf.le

  have low_limit : Tendsto Low atTop (𝓝 (0 : ℝ)) := by
    let c0 : ℝ := 1 - 2 / Real.exp 1
    have hc0 : 0 < c0 := by
      have h2 : (2 : ℝ) < Real.exp 1 := by
        have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
        linarith
      have he : 0 < Real.exp 1 := Real.exp_pos _
      dsimp [c0]
      have hd : 2 / Real.exp 1 < 1 := (div_lt_one he).mpr h2
      linarith
    let U (m : ℕ) : ℝ := (Real.pi / 2) *
      Real.exp (-c0 * (m : ℝ) ^ 3 + 2 * lam * (m : ℝ))
    have hcubic : Tendsto (fun m : ℕ => (m : ℝ) ^ 3) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp hnat
    have hneg : Tendsto (fun m : ℕ => -(c0 / 2) * (m : ℝ) ^ 3) atTop atBot := by
      simpa only [Function.comp_def, neg_mul] using tendsto_neg_atTop_atBot.comp
        (hcubic.const_mul_atTop (by positivity : 0 < c0 / 2))
    have hsq : Tendsto (fun m : ℕ => (m : ℝ) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hnat
    have hdom : ∀ᶠ m : ℕ in atTop,
        -c0 * (m : ℝ) ^ 3 + 2 * lam * (m : ℝ) ≤ -(c0 / 2) * (m : ℝ) ^ 3 := by
      filter_upwards [hpositive, hsq.eventually (eventually_ge_atTop (4 * lam / c0))]
        with m hm hm2
      have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      have hmul : 4 * lam ≤ (m : ℝ) ^ 2 * c0 := (div_le_iff₀ hc0).mp hm2
      have hmul' := mul_le_mul_of_nonneg_right hmul hm0
      nlinarith
    have hpoly : Tendsto (fun m : ℕ => -c0 * (m : ℝ) ^ 3 + 2 * lam * (m : ℝ))
        atTop atBot := by
      apply tendsto_atBot.mpr
      intro x
      filter_upwards [hdom, hneg.eventually (eventually_le_atBot x)] with m hm hx
      exact le_trans hm hx
    have hU : Tendsto U atTop (𝓝 (0 : ℝ)) := by
      simpa only [Function.comp_def, U, mul_zero] using (Real.tendsto_exp_atBot.comp hpoly).const_mul (Real.pi / 2)
    have hlower : ∀ᶠ m : ℕ in atTop, 0 ≤ Low m := by
      filter_upwards [hpositive, baseline_lower] with m hm hb
      exact div_nonneg (Finset.sum_nonneg fun k hk => wpos m hm k) hb.1.le
    have hupper : ∀ᶠ m : ℕ in atTop, Low m ≤ U m := by
      filter_upwards [hpositive, baseline_lower] with m hm hb
      have hL := (binomial_payments m hm).2.2.2.1
      have hbasepos : 0 < (2 / Real.pi) * Real.exp (-2 * lam * (m : ℝ)) := by positivity
      calc
        Low m ≤ Real.exp (-c0 * (m : ℝ) ^ 3) / baseline B P hB m := by
          exact div_le_div_of_nonneg_right hL hb.1.le
        _ ≤ Real.exp (-c0 * (m : ℝ) ^ 3) /
            ((2 / Real.pi) * Real.exp (-2 * lam * (m : ℝ))) :=
          div_le_div_of_nonneg_left (Real.exp_nonneg _) hbasepos hb.2
        _ = U m := by
          dsimp [U]
          rw [Real.exp_add, show -2 * lam * (m : ℝ) = -(2 * lam * (m : ℝ)) by ring,
            Real.exp_neg]
          field_simp [Real.pi_ne_zero, (Real.exp_pos (2 * lam * (m : ℝ))).ne']
          <;> ring
    exact squeeze_zero' hlower hupper hU

  have tail_limit (d : ℝ) (hd : 0 < d) : Tendsto (Tail d) atTop (𝓝 (0 : ℝ)) := by
    have hmajor : Tendsto (fun m : ℕ => ((3 / 2 : ℝ) / d ^ 2) * (m : ℝ)⁻¹)
        atTop (𝓝 (0 : ℝ)) := by simpa using hinv.const_mul ((3 / 2 : ℝ) / d ^ 2)
    have hlow : ∀ᶠ m : ℕ in atTop, 0 ≤ Tail d m := by
      filter_upwards [hpositive] with m hm
      exact Finset.sum_nonneg fun k hk => wpos m hm k
    have hup : ∀ᶠ m : ℕ in atTop,
        Tail d m ≤ ((3 / 2 : ℝ) / d ^ 2) * (m : ℝ)⁻¹ := by
      filter_upwards [hpositive] with m hm
      have hmpos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
      have hcheb := finite_chebyshev (I m) (W m) (Z m) (d * (m : ℝ) ^ 2)
        (by positivity) (fun k hk => wpos m hm k)
      have hvar : (∑ k ∈ I m, W m k * (Z m k) ^ 2) = (3 / 2 : ℝ) * (m : ℝ) ^ 3 :=
        (binomial_payments m hm).2.2.1
      change Tail d m ≤ _ at hcheb
      rw [hvar] at hcheb
      have heq : ((3 / 2 : ℝ) * (m : ℝ) ^ 3) / (d * (m : ℝ) ^ 2) ^ 2 =
          ((3 / 2 : ℝ) / d ^ 2) * (m : ℝ)⁻¹ := by
        field_simp [hd.ne', hmpos.ne']
        <;> ring
      exact hcheb.trans_eq heq
    exact squeeze_zero' hlow hup hmajor

  have tilted_tail_limit (d : ℝ) (hd : 0 < d) :
      Tendsto (TiltTail d) atTop (𝓝 (0 : ℝ)) := by
    let t (m : ℕ) : ℝ := lam / (m : ℝ) ^ 2
    let M (m : ℕ) : ℝ := Real.exp (8 * (time m : ℝ) * t m ^ 2)
    have ht : Tendsto t atTop (𝓝 (0 : ℝ)) := by
      simpa only [t, div_eq_mul_inv, inv_pow, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
        using (hinv.pow 2).const_mul lam
    have htbound : ∀ᶠ m : ℕ in atTop, |-2 * t m| ≤ 1 := by
      have hh : Tendsto (fun m : ℕ => |-2 * t m|) atTop (𝓝 (0 : ℝ)) := by
        simpa only [mul_zero, abs_zero] using (ht.const_mul (-2)).abs
      exact (hh.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).mono
        (fun m hm => hm.le)
    have hM : Tendsto M atTop (𝓝 (1 : ℝ)) := by
      have he : Tendsto (fun m : ℕ => 8 * (time m : ℝ) * t m ^ 2)
          atTop (𝓝 (0 : ℝ)) := by
        have h : Tendsto (fun m : ℕ => (64 * lam ^ 2) * (m : ℝ)⁻¹)
            atTop (𝓝 (0 : ℝ)) := by
          simpa only [mul_zero] using hinv.const_mul (64 * lam ^ 2)
        apply h.congr'
        filter_upwards [hpositive] with m hm
        have hmpos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
        dsimp [t]
        rw [(critical_scale m hm).1]
        push_cast
        field_simp [hmpos.ne']
        <;> ring
      simpa only [Function.comp_def, M, Real.exp_zero] using Real.continuous_exp.continuousAt.tendsto.comp he
    have hroot : Tendsto (fun m : ℕ => Real.sqrt (M m) * Real.sqrt (Tail d m))
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [Function.comp_def, Real.sqrt_one, Real.sqrt_zero, mul_zero] using
        (Real.continuous_sqrt.continuousAt.tendsto.comp hM).mul
          (Real.continuous_sqrt.continuousAt.tendsto.comp (tail_limit d hd))
    have hlow : ∀ᶠ m : ℕ in atTop, 0 ≤ TiltTail d m := by
      filter_upwards [hpositive] with m hm
      exact Finset.sum_nonneg fun k hk =>
        mul_nonneg (wpos m hm k) (Real.exp_nonneg _)
    have hup : ∀ᶠ m : ℕ in atTop,
        TiltTail d m ≤ Real.sqrt (M m) * Real.sqrt (Tail d m) := by
      filter_upwards [hpositive, htbound] with m hm htm
      have hmgf := (binomial_payments m hm).2.2.2.2 (-2 * t m) htm
      have hmgf' : (∑ k ∈ I m, W m k * Real.exp ((-2 * t m) * Z m k)) ≤ M m := by
        have heq : 2 * (time m : ℝ) * (-2 * t m) ^ 2 = 8 * (time m : ℝ) * t m ^ 2 := by ring
        simpa only [M, heq] using hmgf
      exact finite_tilted_tail (I m) (T d m) (W m) (Z m) (t m) (M m)
        (Finset.filter_subset _ _) (fun k hk => wpos m hm k) hmgf'
    exact squeeze_zero' hlow hup hroot

  have average_eq (m : ℕ) : (∑ k ∈ I m, W m k * V m k) =
      (∑ k ∈ (I m).filter (fun k => k < meanIndex m), W m k) +
        E * (∑ k ∈ (I m).filter (fun k => meanIndex m ≤ k), W m k) := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases h : k < meanIndex m
    · have hn : ¬ meanIndex m ≤ k := Nat.not_le.mpr h
      simp only [V, h, hn, if_true, if_false, mul_one, mul_zero, add_zero]
    · have hn : meanIndex m ≤ k := Nat.le_of_not_gt h
      simp only [V, h, hn, if_true, if_false, zero_add]
      ring

  have average_limit : Tendsto (fun m : ℕ => ∑ k ∈ I m, W m k * V m k)
      atTop (𝓝 ((1 + E) / 2)) := by
    have hh := binomial_halves.1.add (binomial_halves.2.const_mul E)
    convert hh using 1
    · funext m
      exact average_eq m
    · ring

  have total_errors (theta d : ℝ) (htheta : 0 < theta)
      (hd : 0 < d) (hd1 : d ≤ 1 / 2) :
      ∃ J : ℕ, 1 ≤ J ∧ ∀ m : ℕ, J ≤ m →
        |randomRatio B P hB m - (∑ k ∈ I m, W m k * V m k)| ≤
          E * (Real.exp (theta + Real.pi ^ 2 * d) - 1) + Low m +
            C * Tail d m + E * Tail d m ∧
        |detRatio B P hB m - E| ≤
          E * (Real.exp (theta + Real.pi ^ 2 * d) - 1) + Low m +
            C * TiltTail d m + E * Tail d m := by
    obtain ⟨Jg, hJg, hg⟩ := global_bounds
    obtain ⟨Jc, hJc, hc⟩ := central_errors theta d htheta hd hd1
    refine ⟨max Jg Jc, hJg.trans (le_max_left _ _), ?_⟩
    intro m hm
    have hmg : Jg ≤ m := (le_max_left _ _).trans hm
    have hmc : Jc ≤ m := (le_max_right _ _).trans hm
    have hm1 : 1 ≤ m := hJg.trans hmg
    have hb : 0 < baseline B P hB m := (hg m hmg).1
    have hglob := (hg m hmg).2
    let err : ℝ := E * (Real.exp (theta + Real.pi ^ 2 * d) - 1)
    have herr : 0 ≤ err := by
      have h : 1 ≤ Real.exp (theta + Real.pi ^ 2 * d) :=
        Real.one_le_exp (by positivity)
      dsimp [err]
      positivity
    have hbinv : 0 ≤ 1 / baseline B P hB m := by positivity
    have hR0 (k : ℕ) (hk : k ∈ I m) : 0 ≤ R m k :=
      div_nonneg (p_bounds _ _).1 hb.le
    have hA0 (k : ℕ) (hk : k ∈ I m) : 0 ≤ A m k :=
      div_nonneg (p_bounds _ _).1 hb.le
    have hRlow (k : ℕ) (hk : k ∈ I m) (hklow : k < m ^ 3) :
        R m k ≤ 1 / baseline B P hB m :=
      div_le_div_of_nonneg_right (p_bounds _ _).2 hb.le
    have hAlow (k : ℕ) (hk : k ∈ I m) (hklow : k < m ^ 3) :
        A m k ≤ 1 / baseline B P hB m :=
      div_le_div_of_nonneg_right (p_bounds _ _).2 hb.le
    have hRhigh (k : ℕ) (hk : k ∈ I m) (hklo : ¬ k < m ^ 3) :
        R m k ≤ C * (1 : ℝ) := by
      simpa only [mul_one] using (hglob k hk (Nat.le_of_not_gt hklo)).1
    have hAhigh (k : ℕ) (hk : k ∈ I m) (hklo : ¬ k < m ^ 3) :
        A m k ≤ C * tilt m k := (hglob k hk (Nat.le_of_not_gt hklo)).2
    have hR := finite_compare (I m) (W m) (R m) (V m) (fun _ => (1 : ℝ))
      (fun k => |Z m k| ≤ d * (m : ℝ) ^ 2) (fun k => k < m ^ 3)
      err E C (1 / baseline B P hB m)
      (fun k hk => wpos m hm1 k) (wsum m hm1) herr hEpos.le hCpos.le hbinv
      hR0 (fun k hk => v_bounds m k) (fun k hk => by norm_num)
      (fun k hk hg => (hc m hmc k hk hg).1) hRlow hRhigh
    have hA := finite_compare (I m) (W m) (A m) (fun _ => E) (tilt m)
      (fun k => |Z m k| ≤ d * (m : ℝ) ^ 2) (fun k => k < m ^ 3)
      err E C (1 / baseline B P hB m)
      (fun k hk => wpos m hm1 k) (wsum m hm1) herr hEpos.le hCpos.le hbinv
      hA0 (fun k hk => ⟨hEpos.le, le_rfl⟩) (fun k hk => Real.exp_nonneg _)
      (fun k hk hg => (hc m hmc k hk hg).2) hAlow hAhigh
    have hloweq : (1 / baseline B P hB m) *
        (∑ k ∈ (I m).filter (fun k => k < m ^ 3), W m k) = Low m := by
      dsimp [Low]
      ring
    rw [hloweq] at hR hA
    simp only [not_le, mul_one] at hR hA
    have hsumE : (∑ k ∈ I m, W m k * E) = E := by
      rw [← Finset.sum_mul, wsum m hm1, one_mul]
    rw [hsumE] at hA
    rcases mixture_ratios m hm1 with ⟨hmixR, hmixA⟩
    change randomRatio B P hB m = ∑ k ∈ I m, W m k * R m k at hmixR
    change detRatio B P hB m = ∑ k ∈ I m, W m k * A m k at hmixA
    rw [hmixR, hmixA]
    exact ⟨hR, hA⟩

  have epsilon_closure (F : ℕ → ℝ) (Rest : ℝ → ℕ → ℝ)
      (hrest : ∀ d : ℝ, 0 < d → Tendsto (Rest d) atTop (𝓝 (0 : ℝ)))
      (hbound : ∀ theta d : ℝ, 0 < theta → 0 < d → d ≤ 1 / 2 →
        ∀ᶠ m : ℕ in atTop,
          |F m| ≤ E * (Real.exp (theta + Real.pi ^ 2 * d) - 1) + Rest d m) :
      Tendsto F atTop (𝓝 (0 : ℝ)) := by
    apply Metric.tendsto_nhds.mpr
    intro eps heps
    have hshift : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
      tendsto_atTop_mono (fun j : ℕ => by linarith) hnat
    have hsmall : Tendsto (fun j : ℕ => E *
        (Real.exp (2 * ((j : ℝ) + 1)⁻¹) - 1)) atTop (𝓝 (0 : ℝ)) := by
      have hi := tendsto_inv_atTop_zero.comp hshift
      have he := Real.continuous_exp.continuousAt.tendsto.comp (hi.const_mul 2)
      simpa only [Function.comp_def, mul_zero, Real.exp_zero, sub_self, mul_zero] using
        (he.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
          atTop (𝓝 (1 : ℝ)))).const_mul E
    obtain ⟨j, hj⟩ :=
      (hsmall.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < eps / 2))).exists
    let theta : ℝ := ((j : ℝ) + 1)⁻¹
    have htheta : 0 < theta := by dsimp [theta]; positivity
    let d : ℝ := min (1 / 2) (theta / (Real.pi ^ 2 + 1))
    have hd : 0 < d := by dsimp [d]; exact lt_min (by norm_num) (by positivity)
    have hd1 : d ≤ 1 / 2 := min_le_left _ _
    have hdtheta : Real.pi ^ 2 * d ≤ theta := by
      have h := (le_div_iff₀ (show 0 < Real.pi ^ 2 + 1 by positivity)).mp
        (min_le_right (1 / 2 : ℝ) (theta / (Real.pi ^ 2 + 1)))
      change d * (Real.pi ^ 2 + 1) ≤ theta at h
      nlinarith
    have he : E * (Real.exp (theta + Real.pi ^ 2 * d) - 1) < eps / 2 := by
      have hexp := Real.exp_le_exp.mpr (show theta + Real.pi ^ 2 * d ≤ 2 * theta by linarith)
      have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_right hexp 1) hEpos.le
      exact lt_of_le_of_lt hmul hj
    filter_upwards [hbound theta d htheta hd hd1,
      (hrest d hd).eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < eps / 2))]
      with m hm hrestm
    have hfinal : |F m| < eps := by linarith
    simpa only [Real.dist_eq, sub_zero] using hfinal

  have random_difference : Tendsto
      (fun m : ℕ => randomRatio B P hB m - (∑ k ∈ I m, W m k * V m k))
      atTop (𝓝 (0 : ℝ)) := by
    refine epsilon_closure _
      (fun d m => Low m + C * Tail d m + E * Tail d m) ?_ ?_
    · intro d hd
      simpa only [add_zero, mul_zero] using
        (low_limit.add ((tail_limit d hd).const_mul C)).add ((tail_limit d hd).const_mul E)
    · intro theta d htheta hd hd1
      obtain ⟨J, hJ, h⟩ := total_errors theta d htheta hd hd1
      filter_upwards [eventually_ge_atTop J] with m hm
      have hr := (h m hm).1
      linarith
  have det_difference : Tendsto (fun m : ℕ => detRatio B P hB m - E)
      atTop (𝓝 (0 : ℝ)) := by
    refine epsilon_closure _
      (fun d m => Low m + C * TiltTail d m + E * Tail d m) ?_ ?_
    · intro d hd
      simpa only [add_zero, mul_zero] using
        (low_limit.add ((tilted_tail_limit d hd).const_mul C)).add ((tail_limit d hd).const_mul E)
    · intro theta d htheta hd hd1
      obtain ⟨J, hJ, h⟩ := total_errors theta d htheta hd hd1
      filter_upwards [eventually_ge_atTop J] with m hm
      have hr := (h m hm).2
      linarith
  constructor
  · have h := random_difference.add average_limit
    simpa only [sub_add_cancel, zero_add, E, a] using h
  · have h := det_difference.add_const E
    simpa only [sub_add_cancel, zero_add, E, a] using h


end Shao.OQ4.SparseCriticalDenominator
