import Shao.C2.AuxiliaryOwnC1Budget
import Shao.Probability.FiniteIID

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.C2.AuxiliaryCenteredProductLaw
open MeasureTheory ProbabilityTheory

theorem auxiliary_centered_product_law_and_endpoint
    (rho : Measure ℝ) [IsProbabilityMeasure rho] (n : ℕ) (mu : ℝ) :
    let chi : Measure ℝ := Measure.map (fun z : ℝ => z - mu) rho
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
    let Pc : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => chi)
    Measure.map (fun v : Shao.Path n => (fun i => v i - mu)) P = Pc ∧
      ∀ y : ℝ,
        P.real {v : Shao.Path n |
          y * Real.sqrt (Shao.energy (fun i => v i - mu)) ≤
            |Shao.prefixSum (fun i => v i - mu) n|} =
        Pc.real {w : Shao.Path n | y * Real.sqrt (Shao.energy w) ≤
          |Shao.prefixSum w n|} := by
  intro chi P Pc
  letI : IsProbabilityMeasure chi := by dsimp [chi]; infer_instance
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  let X : Fin n → Shao.Path n → ℝ := fun i v => v i - mu
  have hShift : Measurable (fun z : ℝ => z - mu) := by fun_prop
  have hX (i : Fin n) : Measurable (X i) := hShift.comp (measurable_pi_apply i)
  have hIndep : iIndepFun X P :=
    iIndepFun_pi (X := fun _ : Fin n => (fun z : ℝ => z - mu))
      (fun _ => hShift.aemeasurable)
  have hLaw (i : Fin n) : IdentDistrib (X i) (id : ℝ → ℝ) P chi := by
    refine ⟨(hX i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    rw [Measure.map_id]
    calc
      Measure.map (X i) P =
          Measure.map (fun z : ℝ => z - mu) (Measure.map (Function.eval i) P) :=
        (Measure.map_map hShift (measurable_pi_apply i)).symm
      _ = chi := by
        rw [(measurePreserving_eval (fun _ : Fin n => rho) i).map_eq]
  have hMap : Measure.map (fun v : Shao.Path n => (fun i => v i - mu)) P = Pc :=
    Shao.Probability.iid_samplePath_map_eq_pi hX hIndep hLaw
  refine ⟨hMap, ?_⟩
  intro y
  let A : Set (Shao.Path n) := {w | y * Real.sqrt (Shao.energy w) ≤
    |Shao.prefixSum w n|}
  have hA : MeasurableSet A :=
    measurableSet_le (Shao.measurable_energyWall y) (Shao.continuous_prefixSum n).abs.measurable
  have hCenter : Measurable (fun v : Shao.Path n => (fun i => v i - mu)) :=
    Measurable.of_eval hX
  have hh := congrArg (fun q : Measure (Shao.Path n) => q A) hMap
  rw [Measure.map_apply hCenter hA] at hh
  exact congrArg ENNReal.toReal hh

end Shao.C2.AuxiliaryCenteredProductLaw
