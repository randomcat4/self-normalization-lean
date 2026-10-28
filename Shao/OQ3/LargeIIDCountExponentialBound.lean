import Shao.OQ3.IIDMeasurableSetCountExponentialBound
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Algebra.Order.Archimedean.Basic

namespace Shao.OQ3
open Classical MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section

theorem exists_large_iid_count_arbitrary_exponential_bound
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (alpha R : ℝ) (halpha : 0 < alpha) (hR : 0 < R) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ,
      let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
      let LargeCount : Shao.Path n → ℕ := fun z =>
        (Finset.univ.filter (fun i : Fin n => B < |z i|)).card
      P.real {z | alpha * (n : ℝ) ≤ (LargeCount z : ℝ)} ≤
        Real.exp (-R * (n : ℝ)) := by
  classical
  let H : ℕ → Set ℝ := fun k => {x | (k : ℝ) + 1 < |x|}
  have hH (k : ℕ) : MeasurableSet (H k) :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hAnti : Antitone H := by
    intro i j hij x hx
    have hijR : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    change (i : ℝ) + 1 < |x|
    change (j : ℝ) + 1 < |x| at hx
    linarith only [hijR, hx]
  have hInter : (⋂ k : ℕ, H k) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨k, hk⟩ := exists_nat_gt |x|
    have hh := Set.mem_iInter.mp hx k
    change (k : ℝ) + 1 < |x| at hh
    linarith only [hk, hh]
  have hLimE := tendsto_measure_iInter_atTop (μ := mu)
    (fun k => (hH k).nullMeasurableSet) hAnti ⟨0, measure_ne_top mu _⟩
  rw [hInter, measure_empty] at hLimE
  have hLimR : Tendsto (fun k : ℕ => mu.real (H k)) atTop (𝓝 (0 : ℝ)) := by
    have hh := (ENNReal.continuousAt_toReal (show (0 : ENNReal) ≠ ⊤ by simp)).tendsto.comp hLimE
    simpa only [Function.comp_def, measureReal_def, ENNReal.toReal_zero] using hh
  let t : ℝ := (R + 1) / alpha
  have ht : 0 < t := div_pos (by linarith) halpha
  have hExp : 1 < Real.exp t := by
    simpa only [Real.exp_zero] using (Real.exp_lt_exp.mpr ht)
  have hCoef : 0 < Real.exp t - 1 := sub_pos.mpr hExp
  have hq : 0 < 1 / (Real.exp t - 1) := one_div_pos.mpr hCoef
  have hEvent : ∀ᶠ k in atTop, mu.real (H k) < 1 / (Real.exp t - 1) :=
    (tendsto_order.1 hLimR).2 _ hq
  obtain ⟨k, hk⟩ := hEvent.exists
  let B : ℝ := (k : ℝ) + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro n P LargeCount
  have hMass : (Real.exp t - 1) * mu.real (H k) ≤ 1 := by
    have hh := (lt_div_iff₀ hCoef).mp hk
    nlinarith only [hh]
  have hBaseNN : 0 ≤ 1 + (Real.exp t - 1) * mu.real (H k) := by positivity
  have hBase : 1 + (Real.exp t - 1) * mu.real (H k) ≤ Real.exp 1 := by
    have hh : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    linarith only [hMass, hh]
  have hCount : P.real {z | alpha * (n : ℝ) ≤ (LargeCount z : ℝ)} ≤
      Real.exp (-(t * alpha) * (n : ℝ)) *
        (1 + (Real.exp t - 1) * mu.real (H k)) ^ n := by
    have hh := iid_measurable_set_count_exponential_bound mu (H k) (hH k) t alpha ht n
    convert hh using 1
  have htalpha : t * alpha = R + 1 := by
    dsimp only [t]
    field_simp
  calc
    P.real {z | alpha * (n : ℝ) ≤ (LargeCount z : ℝ)} ≤
        Real.exp (-(t * alpha) * (n : ℝ)) *
          (1 + (Real.exp t - 1) * mu.real (H k)) ^ n := hCount
    _ ≤ Real.exp (-(t * alpha) * (n : ℝ)) * (Real.exp 1) ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hBaseNN hBase n) (Real.exp_nonneg _)
    _ = Real.exp (-R * (n : ℝ)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, htalpha]
      congr 1
      ring

end
end Shao.OQ3
