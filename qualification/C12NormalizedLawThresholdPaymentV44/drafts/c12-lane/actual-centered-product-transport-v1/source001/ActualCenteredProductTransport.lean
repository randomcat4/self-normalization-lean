import Shao.C2.AuxiliaryCenteredProductLaw
import Shao.C2.TwoSided
import Shao.Probability.MeasurablePath

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
noncomputable section
namespace Shao.C2.ActualCenteredProductTransport
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

theorem double_crossing_smul_iff
    {n : ℕ} (hn : 0 < n) (v : Shao.Path n) (t : ℝ) (ht : 0 < t) (x : ℝ) :
    t • v ∈ Shao.C2.doubleCrossing hn x ↔ v ∈ Shao.C2.doubleCrossing hn x := by
  have hRoot : Real.sqrt (Shao.energy (t • v)) = t * Real.sqrt (Shao.energy v) := by
    rw [Shao.energy_smul, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]
  change (x * Real.sqrt (Shao.energy (t • v)) ≤ Shao.upperMax (t • v) hn ∧
    x * Real.sqrt (Shao.energy (t • v)) ≤ Shao.lowerMax (t • v) hn) ↔
    (x * Real.sqrt (Shao.energy v) ≤ Shao.upperMax v hn ∧
      x * Real.sqrt (Shao.energy v) ≤ Shao.lowerMax v hn)
  rw [hRoot, Shao.upperMax_smul_of_nonneg t ht.le,
    Shao.lowerMax_smul_of_nonneg t ht.le]
  rw [show x * (t * Real.sqrt (Shao.energy v)) =
    t * (x * Real.sqrt (Shao.energy v)) by ring]
  simp only [mul_le_mul_iff_left₀ ht]

theorem iid_centered_scaled_product_transport
    (rho : Measure ℝ) [IsProbabilityMeasure rho] (n : ℕ) (hn : 0 < n)
    (mu t : ℝ) (ht : 0 < t) :
    let chi : Measure ℝ := Measure.map (fun z : ℝ => (z - mu) / t) rho
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
    let Pc : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => chi)
    IsProbabilityMeasure chi ∧
      Measure.map (fun v : Shao.Path n => (fun i => (v i - mu) / t)) P = Pc ∧
      (∀ x : ℝ,
        P.real {v : Shao.Path n | (fun i => v i - mu) ∈ Shao.C2.doubleCrossing hn x} =
          Pc.real (Shao.C2.doubleCrossing hn x)) ∧
      ∀ q : ℝ,
        P.real {v : Shao.Path n | Shao.energy (fun i => v i - mu) ≤ q} =
          Pc.real {w : Shao.Path n | t ^ 2 * Shao.energy w ≤ q} := by
  intro chi P Pc
  have hF : Measurable (fun z : ℝ => (z - mu) / t) := by fun_prop
  have hChi : IsProbabilityMeasure chi := by
    dsimp only [chi]
    exact (Measure.isProbabilityMeasure_map_iff hF.aemeasurable).mpr inferInstance
  letI : IsProbabilityMeasure chi := hChi
  letI : IsProbabilityMeasure P := by dsimp only [P]; infer_instance
  let X : Fin n → Shao.Path n → ℝ := fun i v => (v i - mu) / t
  let T : Shao.Path n → Shao.Path n := fun v i => (v i - mu) / t
  have hX (i : Fin n) : Measurable (X i) := hF.comp (measurable_pi_apply i)
  have hIndep : iIndepFun X P :=
    iIndepFun_pi (X := fun _ : Fin n => (fun z : ℝ => (z - mu) / t))
      (fun _ => hF.aemeasurable)
  have hLaw (i : Fin n) : IdentDistrib (X i) (id : ℝ → ℝ) P chi := by
    refine ⟨(hX i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    rw [Measure.map_id]
    calc
      Measure.map (X i) P =
          Measure.map (fun z : ℝ => (z - mu) / t) (Measure.map (Function.eval i) P) :=
        (Measure.map_map hF (measurable_pi_apply i)).symm
      _ = chi := by
        rw [(measurePreserving_eval (fun _ : Fin n => rho) i).map_eq]
  have hMap : Measure.map T P = Pc :=
    Shao.Probability.iid_samplePath_map_eq_pi hX hIndep hLaw
  have hT : Measurable T := Measurable.of_eval hX
  have hRestore (v : Shao.Path n) : (fun i => v i - mu) = t • T v := by
    funext i
    change v i - mu = t * ((v i - mu) / t)
    field_simp [ht.ne'] <;> ring
  refine ⟨hChi, hMap, ?_, ?_⟩
  · intro x
    let D : Set (Shao.Path n) := Shao.C2.doubleCrossing hn x
    have hD : MeasurableSet D := Shao.C2.measurableSet_doubleCrossing hn x
    have hPre : T ⁻¹' D =
        {v : Shao.Path n | (fun i => v i - mu) ∈ Shao.C2.doubleCrossing hn x} := by
      ext v
      change T v ∈ Shao.C2.doubleCrossing hn x ↔
        (fun i => v i - mu) ∈ Shao.C2.doubleCrossing hn x
      rw [hRestore v]
      exact (double_crossing_smul_iff hn (T v) t ht x).symm
    have hh := congrArg (fun m : Measure (Shao.Path n) => m D) hMap
    rw [Measure.map_apply hT hD, hPre] at hh
    exact congrArg ENNReal.toReal hh
  · intro q
    let A : Set (Shao.Path n) := {w | t ^ 2 * Shao.energy w ≤ q}
    have hA : MeasurableSet A :=
      measurableSet_le (measurable_const.mul Shao.measurable_energy) measurable_const
    have hPre : T ⁻¹' A =
        {v : Shao.Path n | Shao.energy (fun i => v i - mu) ≤ q} := by
      ext v
      change t ^ 2 * Shao.energy (T v) ≤ q ↔
        Shao.energy (fun i => v i - mu) ≤ q
      rw [hRestore v, Shao.energy_smul]
    have hh := congrArg (fun m : Measure (Shao.Path n) => m A) hMap
    rw [Measure.map_apply hT hA, hPre] at hh
    exact congrArg ENNReal.toReal hh

end Shao.C2.ActualCenteredProductTransport
