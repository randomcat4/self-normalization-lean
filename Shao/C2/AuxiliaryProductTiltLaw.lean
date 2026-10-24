import Shao.C2.AuxiliaryEnergyTilt
import Shao.OQ4.EnergyPathLaw
import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Shao.C2.AuxiliaryProductTiltLaw
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem auxiliary_actual_product_tilt_law
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (s : ℝ) (hs : 0 ≤ s) (n : ℕ) :
    let Z : ℝ := ∫ z : ℝ, Real.exp (-s * z ^ 2) ∂nu
    let rho : Measure ℝ := nu.tilted (fun z => -s * z ^ 2)
    let Praw : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    let Ptilt : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
    let W : Shao.Path n → ℝ := fun v => Real.exp (-s * Shao.energy v)
    0 < Z ∧ IsProbabilityMeasure Ptilt ∧ Integrable W Praw ∧
      (∫ v : Shao.Path n, W v ∂Praw) = Z ^ n ∧
      Ptilt = Praw.tilted (fun v => -s * Shao.energy v) := by
  intro Z rho Praw Ptilt W
  rcases Shao.C2.AuxiliaryEnergyTilt.auxiliary_energy_tilt_normalizer_and_drift
      nu h2 h3 hmean hnorm s hs with ⟨hV, hZ, _hZL, _hZU, hRho, _hId, _hDrift⟩
  letI : IsProbabilityMeasure rho := hRho
  have hPtilt : IsProbabilityMeasure Ptilt := by dsimp [Ptilt]; infer_instance
  have hProd (v : Shao.Path n) : W v = ∏ i : Fin n, Real.exp (-s * (v i) ^ 2) := by
    change Real.exp (-s * (∑ i : Fin n, (v i) ^ 2)) = _
    rw [Finset.mul_sum, Real.exp_sum]
  have hWfunc : W = (fun v : Shao.Path n => ∏ i : Fin n, Real.exp (-s * (v i) ^ 2)) :=
    funext hProd
  have hW : Integrable W Praw := by
    rw [hWfunc]
    exact Integrable.fintype_prod (fun _ : Fin n => hV)
  have hZprod : (∫ v : Shao.Path n, W v ∂Praw) = Z ^ n := by
    calc
      (∫ v : Shao.Path n, W v ∂Praw) = ∏ _ : Fin n, Z := by
        simp_rw [hProd]
        exact integral_fintype_prod_eq_prod (fun _ : Fin n =>
          fun z : ℝ => Real.exp (-s * z ^ 2))
      _ = Z ^ n := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  let d : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp (-s * z ^ 2) / Z)
  have hd : Measurable d := by dsimp [d]; fun_prop
  letI : IsProbabilityMeasure (nu.withDensity d) := hRho
  have hPi := Shao.OQ4.finitePi_withDensity nu d hd n
  have hDensity (v : Shao.Path n) : (∏ i : Fin n, d (v i)) =
      ENNReal.ofReal (W v / Z ^ n) := by
    calc
      (∏ i : Fin n, d (v i)) = ENNReal.ofReal
          (∏ i : Fin n, Real.exp (-s * (v i) ^ 2) / Z) :=
        (ENNReal.ofReal_prod_of_nonneg (fun i _ =>
          div_nonneg (Real.exp_pos _).le hZ.le)).symm
      _ = ENNReal.ofReal ((∏ i : Fin n, Real.exp (-s * (v i) ^ 2)) /
          (∏ _ : Fin n, Z)) := by rw [Finset.prod_div_distrib]
      _ = ENNReal.ofReal (W v / Z ^ n) := by
        rw [← hProd]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hLaw : Ptilt = Praw.tilted (fun v => -s * Shao.energy v) := by
    change Measure.pi (fun _ : Fin n => nu.withDensity d) = _
    rw [hPi, Measure.tilted, hZprod]
    congr 1
    funext v
    exact hDensity v
  exact ⟨hZ, hPtilt, hW, hZprod, hLaw⟩

theorem auxiliary_actual_event_laplace_identity
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (s : ℝ) (hs : 0 ≤ s) (n : ℕ)
    (A : Set (Shao.Path n)) (hA : MeasurableSet A) :
    let Z : ℝ := ∫ z : ℝ, Real.exp (-s * z ^ 2) ∂nu
    let rho : Measure ℝ := nu.tilted (fun z => -s * z ^ 2)
    let Praw : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    let Ptilt : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
    let W : Shao.Path n → ℝ := fun v => Real.exp (-s * Shao.energy v)
    Integrable (A.indicator W) Praw ∧
      (∫ v : Shao.Path n, A.indicator W v ∂Praw) = Z ^ n * Ptilt.real A := by
  intro Z rho Praw Ptilt W
  rcases auxiliary_actual_product_tilt_law nu h2 h3 hmean hnorm s hs n with
    ⟨hZ, hPtilt, hW, hZprod, hLaw⟩
  letI : IsProbabilityMeasure Ptilt := hPtilt
  change Ptilt = Praw.tilted (fun v => -s * Shao.energy v) at hLaw
  have hIndicator : Integrable (A.indicator W) Praw := hW.indicator hA
  have hProbability : Ptilt.real A =
      (∫ v : Shao.Path n, A.indicator W v ∂Praw) / Z ^ n := by
    calc
      Ptilt.real A = ∫ v : Shao.Path n, A.indicator (fun _ => (1 : ℝ)) v ∂Ptilt := by
        rw [integral_indicator_const _ hA]
        simp only [smul_eq_mul, mul_one]
      _ = ∫ v : Shao.Path n, (W v / Z ^ n) *
          A.indicator (fun _ => (1 : ℝ)) v ∂Praw := by
        rw [hLaw, integral_tilted, hZprod]
        rfl
      _ = ∫ v : Shao.Path n, A.indicator W v / Z ^ n ∂Praw := by
        apply integral_congr_ae
        exact ae_of_all _ (fun v => by
          by_cases hv : v ∈ A
          · simp only [Set.indicator_of_mem hv, mul_one]
          · simp only [Set.indicator_of_notMem hv, mul_zero, zero_div])
      _ = _ := integral_div _ _
  have hNonzero : Z ^ n ≠ 0 := pow_ne_zero n hZ.ne'
  have hEq := (eq_div_iff hNonzero).1 hProbability
  exact ⟨hIndicator, by nlinarith⟩

end Shao.C2.AuxiliaryProductTiltLaw
