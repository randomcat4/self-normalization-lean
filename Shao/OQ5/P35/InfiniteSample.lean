import Shao.OQ5.P35.RealLaw
import Mathlib.Probability.Independence.InfinitePi

/-!
# One fixed infinite iid observation sequence for p35

Source: `current/oq56/inputs02/p35.md`, §1 and §3, and contract C0.
Every finite sample is taken from this single probability measure and the
same fixed real law. Distinct-coordinate pairs have the actual product law.
-/

set_option autoImplicit false

namespace Shao.OQ5.P35

noncomputable section

open MeasureTheory

/-- The probability law of the entire infinite sequence, fixed before any sample size. -/
def sampleLaw : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => realLaw)

/-- Coordinate observations on the fixed sequence space. -/
def sampleCoordinate (i : ℕ) (ω : ℕ → ℝ) : ℝ := ω i

instance sampleLaw_isProbabilityMeasure : IsProbabilityMeasure sampleLaw := by
  unfold sampleLaw
  infer_instance

theorem measurable_sampleCoordinate (i : ℕ) : Measurable (sampleCoordinate i) :=
  measurable_pi_apply i

theorem map_sampleCoordinate (i : ℕ) :
    Measure.map (sampleCoordinate i) sampleLaw = realLaw := by
  exact Measure.infinitePi_map_eval (fun _ : ℕ => realLaw) i

/-- Full mutual independence of all coordinates, not only pairwise independence. -/
theorem iIndepFun_sampleCoordinate :
    ProbabilityTheory.iIndepFun sampleCoordinate sampleLaw := by
  exact ProbabilityTheory.iIndepFun_infinitePi
    (P := fun _ : ℕ => realLaw) (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)

/-- The pair law uses distinct coordinates; it asserts no same-coordinate fourth moment. -/
theorem map_sampleCoordinate_pair (i j : ℕ) (hij : i ≠ j) :
    Measure.map (fun ω => (sampleCoordinate i ω, sampleCoordinate j ω)) sampleLaw =
      realLaw.prod realLaw := by
  exact Measure.infinitePi_map_eval_prod (P := fun _ : ℕ => realLaw) hij

end

end Shao.OQ5.P35
