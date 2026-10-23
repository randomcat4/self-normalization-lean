import Shao.OQ3.QuadraticSampleChangeOfMeasure
import Shao.OQ3.BoundaryLaplacePhysicalDomain

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem sample_self_normalized_tail_iff
    (level : ℝ) (hlevel : 0 < level) (n : ℕ) (hn : 1 ≤ n) (z : Shao.Path n) :
    let M : ℝ × ℝ :=
      ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
    level * Real.sqrt (n : ℝ) ≤
        (if Shao.energy z = 0 then 0 else (∑ i : Fin n, z i) / Real.sqrt (Shao.energy z)) ↔
      0 < M.2 ∧ level * Real.sqrt M.2 ≤ M.1 := by
  have hN : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) hn)
  have hsN : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hN
  have hE : 0 ≤ Shao.energy z := Shao.energy_nonneg z
  dsimp only
  by_cases hz : Shao.energy z = 0
  · have hthreshold : ¬ level * Real.sqrt (n : ℝ) ≤ (0 : ℝ) :=
      not_le.mpr (mul_pos hlevel hsN)
    simp [hz, hthreshold]
  · have hEpos : 0 < Shao.energy z := lt_of_le_of_ne hE (Ne.symm hz)
    have hsE : 0 < Real.sqrt (Shao.energy z) := Real.sqrt_pos.mpr hEpos
    have hscale : Real.sqrt (Shao.energy z / (n : ℝ)) * (n : ℝ) =
        Real.sqrt (n : ℝ) * Real.sqrt (Shao.energy z) := by
      calc
        _ = (Real.sqrt (Shao.energy z) / Real.sqrt (n : ℝ)) *
            (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by
          rw [Real.sqrt_div hE, Real.mul_self_sqrt hN.le]
        _ = _ := by field_simp [hsN.ne']
    simp only [ite_eq_right hz]
    constructor
    · intro h
      refine ⟨div_pos hEpos hN, (le_div_iff₀ hN).mpr ?_⟩
      calc
        (level * Real.sqrt (Shao.energy z / (n : ℝ))) * (n : ℝ) =
            (level * Real.sqrt (n : ℝ)) * Real.sqrt (Shao.energy z) := by
          rw [mul_assoc, hscale]
          ring
        _ ≤ ∑ i : Fin n, z i := (le_div_iff₀ hsE).mp h
    · rintro ⟨_, h⟩
      apply (le_div_iff₀ hsE).mpr
      have hh := (le_div_iff₀ hN).mp h
      calc
        (level * Real.sqrt (n : ℝ)) * Real.sqrt (Shao.energy z) =
            (level * Real.sqrt (Shao.energy z / (n : ℝ))) * (n : ℝ) := by
          rw [mul_assoc, ← hscale, ← mul_assoc]
        _ ≤ ∑ i : Fin n, z i := hh

theorem iid_self_normalized_tail_map_and_split
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (level : ℝ) (hlevel : 0 < level) (n : ℕ) (hn : 1 ≤ n)
    (U : Set (ℝ × ℝ)) (hU : MeasurableSet U) :
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
    let M : Shao.Path n → (ℝ × ℝ) := fun z =>
      ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
    let Tail : Set (ℝ × ℝ) := {w | 0 < w.2 ∧ level * Real.sqrt w.2 ≤ w.1}
    let T : Set (Shao.Path n) := {z | level * Real.sqrt (n : ℝ) ≤
      (if Shao.energy z = 0 then 0 else (∑ i : Fin n, z i) / Real.sqrt (Shao.energy z))}
    MeasurableSet Tail ∧ MeasurableSet T ∧
      P.real T = (Measure.map M P).real Tail ∧
      P.real T = (Measure.map M P).real (U ∩ Tail) +
        (Measure.map M P).real (Tail \ U) := by
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
  let M : Shao.Path n → (ℝ × ℝ) := fun z =>
    ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
  let Tail : Set (ℝ × ℝ) := {w | 0 < w.2 ∧ level * Real.sqrt w.2 ≤ w.1}
  let T : Set (Shao.Path n) := {z | level * Real.sqrt (n : ℝ) ≤
    (if Shao.energy z = 0 then 0 else (∑ i : Fin n, z i) / Real.sqrt (Shao.energy z))}
  have hM : Continuous M := by dsimp [M, Shao.energy]; fun_prop
  have hcurve : Continuous (fun w : ℝ × ℝ => level * Real.sqrt w.2) :=
    continuous_const.mul continuous_snd.sqrt
  have hTail : MeasurableSet Tail :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le hcurve.measurable measurable_fst)
  have hset : T = M ⁻¹' Tail := by
    ext z
    exact sample_self_normalized_tail_iff level hlevel n hn z
  have hT : MeasurableSet T := by
    rw [hset]
    exact hTail.preimage hM.measurable
  have hmap : P.real T = (Measure.map M P).real Tail := by
    change (P T).toReal = ((Measure.map M P) Tail).toReal
    rw [Measure.map_apply hM.measurable hTail, hset]
  refine ⟨hTail, hT, hmap, ?_⟩
  rw [hmap]
  simpa only [Set.inter_comm] using
    (measureReal_inter_add_sdiff (μ := Measure.map M P) (s := Tail) hU).symm

end
end Shao.OQ3
