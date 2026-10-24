import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

set_option autoImplicit false

namespace Shao.OQ6.CoordinateBorelFactorization

noncomputable section

open MeasureTheory

def coordinateCodeTuple
    {I : Type*} {X : I → Type*}
    (c : ∀ i : I, X i → ℝ) (x : ∀ i : I, X i) : I → ℝ :=
  fun i : I => c i (x i)

def deleteCoordinateTuple
    {I : Type*} {X : I → Type*}
    (i : I) (x : ∀ j : I, X j) :
    ∀ j : {j : I // j ≠ i}, X j.1 :=
  fun j : {j : I // j ≠ i} => x j.1

theorem real_borel_factorization_of_comap
    {X S : Type*} [mX : MeasurableSpace X] [mS : MeasurableSpace S]
    (t : X → S)
    (hcomap : MeasurableSpace.comap t mS = mX)
    (h : X → ℝ) (hh : Measurable h) :
    ∃ F : S → ℝ, Measurable F ∧ ∀ x : X, h x = F (t x) := by
  have hh' : Measurable[MeasurableSpace.comap t mS] h := by
    apply measurable_iff_comap_le.mpr
    rw [hcomap]
    exact measurable_iff_comap_le.mp hh
  obtain ⟨F, hF, hEq⟩ := hh'.exists_eq_measurable_comp
  refine ⟨F, hF, ?_⟩
  intro x
  exact congrFun hEq x

theorem finite_coordinate_code_tuple_spec
    {I : Type*} [Fintype I] {X : I → Type*}
    [mX : ∀ i : I, MeasurableSpace (X i)]
    (c : ∀ i : I, X i → ℝ)
    (hcomap : ∀ i : I,
      MeasurableSpace.comap (c i) (borel ℝ) = mX i) :
    let C : (∀ i : I, X i) → (I → ℝ) := coordinateCodeTuple c
    Measurable[(inferInstance : MeasurableSpace (∀ i : I, X i)),
      borel (I → ℝ)] C ∧
    MeasurableSpace.comap C (borel (I → ℝ)) =
      (inferInstance : MeasurableSpace (∀ i : I, X i)) ∧
    (∀ (h : (∀ i : I, X i) → ℝ), Measurable h →
      ∃ F : (I → ℝ) → ℝ,
        Measurable[borel (I → ℝ), borel ℝ] F ∧
        ∀ x : (∀ i : I, X i), h x = F (C x)) := by
  dsimp only
  have hB : (inferInstance : MeasurableSpace (I → ℝ)) = borel (I → ℝ) :=
    BorelSpace.measurable_eq
  have hR : (inferInstance : MeasurableSpace ℝ) = borel ℝ :=
    BorelSpace.measurable_eq
  have hfull : MeasurableSpace.comap (coordinateCodeTuple c) (borel (I → ℝ)) =
      (inferInstance : MeasurableSpace (∀ i : I, X i)) := by
    rw [← hB]
    calc
      MeasurableSpace.comap (coordinateCodeTuple c)
          (inferInstance : MeasurableSpace (I → ℝ)) =
          ⨆ i : I, MeasurableSpace.comap
            (fun x : (∀ i : I, X i) => c i (x i))
            (inferInstance : MeasurableSpace ℝ) :=
        MeasurableSpace.comap_process_pi
          (fun (i : I) (x : (∀ i : I, X i)) => c i (x i))
      _ = ⨆ i : I, MeasurableSpace.comap
            (fun x : (∀ i : I, X i) => x i) (mX i) := by
        apply iSup_congr
        intro i
        rw [hR]
        change MeasurableSpace.comap
          (c i ∘ (fun x : (∀ i : I, X i) => x i)) (borel ℝ) = _
        rw [← MeasurableSpace.comap_comp, hcomap i]
      _ = (inferInstance : MeasurableSpace (∀ i : I, X i)) := rfl
  refine ⟨?_, hfull, ?_⟩
  · exact measurable_iff_comap_le.mpr hfull.le
  · intro h hh
    obtain ⟨F, hF, hEq⟩ := real_borel_factorization_of_comap
      (mS := borel (I → ℝ)) (coordinateCodeTuple c) hfull h hh
    refine ⟨F, ?_, hEq⟩
    simpa only [hR] using hF

theorem finite_deleted_code_factorization
    {n : ℕ} {X : Fin n → Type*}
    [mX : ∀ j : Fin n, MeasurableSpace (X j)]
    (c : ∀ j : Fin n, X j → ℝ)
    (hcomap : ∀ j : Fin n,
      MeasurableSpace.comap (c j) (borel ℝ) = mX j)
    (i : Fin n) :
    let J : Type := {j : Fin n // j ≠ i}
    let C : (∀ j : Fin n, X j) → (Fin n → ℝ) := coordinateCodeTuple c
    let Cdel : (∀ j : J, X j.1) → (J → ℝ) :=
      coordinateCodeTuple (fun j : J => c j.1)
    let pX : (∀ j : Fin n, X j) → (∀ j : J, X j.1) :=
      deleteCoordinateTuple (X := X) i
    let pR : (Fin n → ℝ) → (J → ℝ) :=
      deleteCoordinateTuple (X := fun _ : Fin n => ℝ) i
    Measurable pX ∧
    Measurable[borel (Fin n → ℝ), borel (J → ℝ)] pR ∧
    Measurable[(inferInstance : MeasurableSpace (∀ j : J, X j.1)),
      borel (J → ℝ)] Cdel ∧
    MeasurableSpace.comap Cdel (borel (J → ℝ)) =
      (inferInstance : MeasurableSpace (∀ j : J, X j.1)) ∧
    (∀ x : (∀ j : Fin n, X j), pR (C x) = Cdel (pX x)) ∧
    MeasurableSpace.comap (fun x : (∀ j : Fin n, X j) => pR (C x))
        (borel (J → ℝ)) =
      MeasurableSpace.comap pX
        (inferInstance : MeasurableSpace (∀ j : J, X j.1)) ∧
    (∀ (d : (∀ j : J, X j.1) → ℝ), Measurable d →
      ∃ F : (J → ℝ) → ℝ,
        Measurable[borel (J → ℝ), borel ℝ] F ∧
        (∀ y : (∀ j : J, X j.1), d y = F (Cdel y)) ∧
        Measurable[borel (Fin n → ℝ), borel ℝ]
          (fun z : Fin n → ℝ => F (pR z)) ∧
        ∀ x : (∀ j : Fin n, X j), d (pX x) = F (pR (C x))) := by
  classical
  dsimp only
  let J : Type := {j : Fin n // j ≠ i}
  let C : (∀ j : Fin n, X j) → (Fin n → ℝ) := coordinateCodeTuple c
  let Cdel : (∀ j : J, X j.1) → (J → ℝ) :=
    coordinateCodeTuple (fun j : J => c j.1)
  let pX : (∀ j : Fin n, X j) → (∀ j : J, X j.1) :=
    deleteCoordinateTuple (X := X) i
  let pR : (Fin n → ℝ) → (J → ℝ) :=
    deleteCoordinateTuple (X := fun _ : Fin n => ℝ) i
  have hdel := finite_coordinate_code_tuple_spec
    (I := J) (X := fun j : J => X j.1)
    (fun j : J => c j.1) (fun j : J => hcomap j.1)
  have hpX : Measurable pX := by
    apply Measurable.of_eval
    intro j
    exact measurable_pi_apply j.1
  have hBFull : (inferInstance : MeasurableSpace (Fin n → ℝ)) =
      borel (Fin n → ℝ) := BorelSpace.measurable_eq
  have hBDel : (inferInstance : MeasurableSpace (J → ℝ)) =
      borel (J → ℝ) := BorelSpace.measurable_eq
  have hpR' : Measurable pR := by
    apply Measurable.of_eval
    intro j
    exact measurable_pi_apply j.1
  have hpR : Measurable[borel (Fin n → ℝ), borel (J → ℝ)] pR := by
    apply measurable_iff_comap_le.mpr
    rw [← hBFull, ← hBDel]
    exact measurable_iff_comap_le.mp hpR'
  have hcomm : ∀ x : (∀ j : Fin n, X j), pR (C x) = Cdel (pX x) := by
    intro x
    rfl
  have hlift : MeasurableSpace.comap
      (fun x : (∀ j : Fin n, X j) => pR (C x)) (borel (J → ℝ)) =
      MeasurableSpace.comap pX
        (inferInstance : MeasurableSpace (∀ j : J, X j.1)) := by
    calc
      MeasurableSpace.comap
          (fun x : (∀ j : Fin n, X j) => pR (C x)) (borel (J → ℝ)) =
          MeasurableSpace.comap
            (fun x : (∀ j : Fin n, X j) => Cdel (pX x))
            (borel (J → ℝ)) := rfl
      _ = MeasurableSpace.comap pX
          (MeasurableSpace.comap Cdel (borel (J → ℝ))) :=
        (MeasurableSpace.comap_comp
          (m := borel (J → ℝ)) (f := Cdel) (g := pX)).symm
      _ = MeasurableSpace.comap pX
          (inferInstance : MeasurableSpace (∀ j : J, X j.1)) := by
        rw [hdel.2.1]
  refine ⟨hpX, hpR, hdel.1, hdel.2.1, hcomm, hlift, ?_⟩
  intro d hd
  obtain ⟨F, hF, hEq⟩ := hdel.2.2 d hd
  refine ⟨F, hF, hEq, ?_, ?_⟩
  · exact hF.comp hpR
  · intro x
    exact (hEq (pX x)).trans (congrArg F (hcomm x).symm)

end

end Shao.OQ6.CoordinateBorelFactorization
