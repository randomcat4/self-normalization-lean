import Shao.OQ3.BoundedActualChartWindowProbabilityLaplace
import Shao.OQ3.BoundedActualQuadraticExteriorExponentialBound
import Shao.OQ3.SampleParabolaTailDomain

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators Matrix Topology
noncomputable section

set_option maxHeartbeats 1000000 in
theorem bounded_actual_self_normalized_tail_laplace_of_closure_gap
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (hdet : 0 < (parabolaCovariance
      (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))).det)
    (level a0 : ℝ) (hlevel : 0 < level) (ha0 : 0 < a0) (hnegative : theta.2 < 0)
    (hmean : (∫ x : ℝ, x ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2),
      ∫ x : ℝ, x ^ 2 ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)) =
        (a0, a0 ^ 2 / level ^ 2))
    (hsaddle : theta.1 = -2 * a0 * theta.2 / level ^ 2)
    (e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ))
    (he : (e : (ℝ × ℝ) → (ℝ × ℝ)) = fun p =>
      (∫ x : ℝ, x ∂mu.tilted (fun x => p.1 * x + p.2 * x ^ 2),
        ∫ x : ℝ, x ^ 2 ∂mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)))
    (hte : theta ∈ e.source)
    (hsource : e.source ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (rmax : ℝ) (hrmax : 0 < rmax)
    (supportRadius : ℝ) (hSupport : 0 ≤ supportRadius)
    (hbounded : ∀ᵐ x ∂mu, |x| ≤ supportRadius)
    (beta c R : ℝ) (hbeta : 0 < beta) (hbetaUpper : beta < (2 : ℝ) / 5)
    (hc : 0 < c) (hR : 0 ≤ R)
    (hWC : ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)) xi eta‖ ≤
        1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) :
    let Omega : Set (ℝ × ℝ) := interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
    let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    let means : (ℝ × ℝ) → (ℝ × ℝ) := fun p =>
      (∫ x : ℝ, x ∂nu p, ∫ x : ℝ, x ^ 2 ∂nu p)
    let K : (ℝ × ℝ) → ℝ := fun p => Real.log
      (∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu)
    let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (nu theta)
    let pr0 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
    let pr1 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
    let row0 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 0 • pr0 + D 0 1 • pr1
    let row1 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 1 • pr0 + D 1 1 • pr1
    ∀ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = row0.prod row1 →
      let J : (ℝ × ℝ) → ℝ := fun w =>
        (e.symm w).1 * w.1 + (e.symm w).2 * w.2 - K (e.symm w)
      let v : ℝ × ℝ := (1, 2 * a0 / level ^ 2)
      let Lambda1 : ℝ := 2 * theta.2 / level ^ 2 +
        (L.symm v).1 + (2 * a0 / level ^ 2) * (L.symm v).2
      let J0 : ℝ := J (a0, a0 ^ 2 / level ^ 2)
      0 < -theta.2 ∧ (0 < Lambda1 →
        ∃ cap : ℝ, 0 < cap ∧ cap ≤ rmax ∧
          ∀ rho : ℝ, 0 < rho → rho ≤ cap →
            let U : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
              |w.1 ^ 2 / level ^ 2 - w.2| ≤ rho}
            let Tail : Set (ℝ × ℝ) := {w | 0 < w.2 ∧ level * Real.sqrt w.2 ≤ w.1}
            let V : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
              0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
            let Carrier : Set (ℝ × ℝ) :=
              Set.Icc (-supportRadius) supportRadius ×ˢ Set.Icc 0 (supportRadius ^ 2)
            V = U ∩ Tail ∧
              ((∃ delta : ℝ, 0 < delta ∧
                  ∀ w ∈ Carrier ∩ closure (Tail \ U),
                    ((J0 + delta : ℝ) : EReal) <
                      Shao.Probability.bivariateLegendreRate mu
                        (fun x : ℝ => (x, x ^ 2)) w) →
                ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
                  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
                  let T : Set (Shao.Path n) := {z |
                    level * Real.sqrt (n : ℝ) ≤
                      (if Shao.energy z = 0 then 0 else
                        (∑ i : Fin n, z i) / Real.sqrt (Shao.energy z))}
                  let main : ℝ := 1 /
                    (Real.sqrt (2 * Real.pi * (n : ℝ)) * (-theta.2) * Real.sqrt D.det *
                      Real.sqrt Lambda1)
                  0 < main ∧
                    |(Real.exp ((n : ℝ) * J0) * P.real T) / main - 1| ≤
                      C / Real.sqrt (n : ℝ))) := by
  classical
  intro Omega nu means K D pr0 pr1 row0 row1 L hL J v Lambda1 J0
  obtain ⟨hlambda, H⟩ := bounded_actual_chart_window_probability_laplace
    mu theta htheta hdet level a0 hlevel ha0 hnegative hmean hsaddle
      e he hte hsource rmax hrmax supportRadius hSupport hbounded
      beta c R hbeta hbetaUpper hc hR hWC L hL
  refine ⟨hlambda, ?_⟩
  intro hcurvature
  obtain ⟨cap, hcap, hcapMax, hAll⟩ := H hcurvature
  refine ⟨cap, hcap, hcapMax, ?_⟩
  intro rho hrho hrhocap U Tail V Carrier
  obtain ⟨hVeq, hVCompact, _hPoints, _hFloor, CL, hCL, NL, hNL, hLocal⟩ :=
    hAll rho hrho hrhocap
  refine ⟨hVeq, ?_⟩
  rintro ⟨delta, hdelta, hgap⟩
  obtain ⟨CE, hCE, hExterior⟩ := bounded_actual_quadratic_exterior_exponential_bound
    mu supportRadius hSupport hbounded (Tail \ U) (J0 + delta) hgap
  let kDen : ℝ := Real.sqrt (2 * Real.pi) * (-theta.2) * Real.sqrt D.det *
    Real.sqrt Lambda1
  have hD : 0 < D.det := hdet
  have hkDen : 0 < kDen := by dsimp only [kDen]; positivity
  let Cfinal : ℝ := CL + CE * kDen / delta
  have hCfinal : 0 < Cfinal := by dsimp only [Cfinal]; positivity
  refine ⟨Cfinal, hCfinal, NL, hNL, ?_⟩
  intro n hn P T main
  have hn1 : 1 ≤ n := le_trans (by omega) (le_trans hNL hn)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  let M : Shao.Path n → (ℝ × ℝ) := fun z =>
    ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
  have hLocalN : 0 < main ∧
      |(Real.exp ((n : ℝ) * J0) * P.real (M ⁻¹' V)) / main - 1| ≤
        CL / Real.sqrt (n : ℝ) := hLocal n hn
  have hExt : P.real (M ⁻¹' (Tail \ U)) ≤ CE * Real.exp (-(n : ℝ) * (J0 + delta)) :=
    hExterior n hn1
  have hUClosed : IsClosed U := by
    change IsClosed ({w : ℝ × ℝ | |w.1 - a0| ≤ rho} ∩
      {w : ℝ × ℝ | |w.1 ^ 2 / level ^ 2 - w.2| ≤ rho})
    exact (isClosed_le (by fun_prop) continuous_const).inter
      (isClosed_le (by fun_prop) continuous_const)
  have hU : MeasurableSet U := hUClosed.measurableSet
  obtain ⟨hTail, _hT, _hMap, hSplit0⟩ :=
    iid_self_normalized_tail_map_and_split mu level hlevel n hn1 U hU
  have hM : Continuous M := by dsimp [M, Shao.energy]; fun_prop
  have hMap (A : Set (ℝ × ℝ)) (hA : MeasurableSet A) :
      (Measure.map M P).real A = P.real (M ⁻¹' A) := by
    change ((Measure.map M P) A).toReal = (P (M ⁻¹' A)).toReal
    rw [Measure.map_apply hM.measurable hA]
  have hSplit : P.real T = P.real (M ⁻¹' V) + P.real (M ⁻¹' (Tail \ U)) := by
    calc
      _ = (Measure.map M P).real (U ∩ Tail) +
          (Measure.map M P).real (Tail \ U) := hSplit0
      _ = _ := by rw [hMap _ (hU.inter hTail), hMap _ (hTail.diff hU), ← hVeq]
  let s : ℝ := Real.sqrt (n : ℝ)
  have hs : 0 < s := Real.sqrt_pos.mpr hnpos
  have hsq : s ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hmain : main = 1 / (s * kDen) := by
    dsimp only [main, s, kDen]
    rw [Real.sqrt_mul (show 0 ≤ 2 * Real.pi by positivity)]
    congr 1
    ring
  have hExpCancel : Real.exp (delta * (n : ℝ)) * Real.exp (-(n : ℝ) * delta) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  have hTest : delta * (n : ℝ) ≤ Real.exp (delta * (n : ℝ)) := by
    linarith [Real.add_one_le_exp (delta * (n : ℝ))]
  have hDecay : delta * (n : ℝ) * Real.exp (-(n : ℝ) * delta) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hTest (Real.exp_nonneg (-(n : ℝ) * delta))
    rwa [hExpCancel] at hh
  have hSDecay : s * Real.exp (-(n : ℝ) * delta) ≤ (1 / delta) / s := by
    apply (le_div_iff₀ hs).mpr
    apply (le_div_iff₀ hdelta).mpr
    calc
      _ = delta * (n : ℝ) * Real.exp (-(n : ℝ) * delta) := by rw [← hsq]; ring
      _ ≤ 1 := hDecay
  have hScaledExt : Real.exp ((n : ℝ) * J0) * P.real (M ⁻¹' (Tail \ U)) ≤
      CE * Real.exp (-(n : ℝ) * delta) := by
    calc
      _ ≤ Real.exp ((n : ℝ) * J0) * (CE * Real.exp (-(n : ℝ) * (J0 + delta))) :=
        mul_le_mul_of_nonneg_left hExt (Real.exp_nonneg _)
      _ = CE * (Real.exp ((n : ℝ) * J0) * Real.exp (-(n : ℝ) * (J0 + delta))) := by ring
      _ = CE * Real.exp (-(n : ℝ) * delta) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hOut : (Real.exp ((n : ℝ) * J0) * P.real (M ⁻¹' (Tail \ U))) / main ≤
      (CE * kDen / delta) / s := by
    calc
      _ ≤ (CE * Real.exp (-(n : ℝ) * delta)) / main :=
        div_le_div_of_nonneg_right hScaledExt hLocalN.1.le
      _ = (CE * kDen) * (s * Real.exp (-(n : ℝ) * delta)) := by rw [hmain]; field_simp
      _ ≤ (CE * kDen) * ((1 / delta) / s) :=
        mul_le_mul_of_nonneg_left hSDecay (mul_pos hCE hkDen).le
      _ = (CE * kDen / delta) / s := by ring
  have hOutNonneg : 0 ≤
      (Real.exp ((n : ℝ) * J0) * P.real (M ⁻¹' (Tail \ U))) / main :=
    div_nonneg (mul_nonneg (Real.exp_nonneg _) measureReal_nonneg) hLocalN.1.le
  refine ⟨hLocalN.1, ?_⟩
  change |(Real.exp ((n : ℝ) * J0) * P.real T) / main - 1| ≤ Cfinal / s
  calc
    _ = |((Real.exp ((n : ℝ) * J0) * P.real (M ⁻¹' V)) / main - 1) +
        (Real.exp ((n : ℝ) * J0) * P.real (M ⁻¹' (Tail \ U))) / main| := by
      rw [hSplit]
      congr 1
      ring
    _ ≤ |(Real.exp ((n : ℝ) * J0) * P.real (M ⁻¹' V)) / main - 1| +
        |(Real.exp ((n : ℝ) * J0) * P.real (M ⁻¹' (Tail \ U))) / main| := abs_add_le _ _
    _ = |(Real.exp ((n : ℝ) * J0) * P.real (M ⁻¹' V)) / main - 1| +
        (Real.exp ((n : ℝ) * J0) * P.real (M ⁻¹' (Tail \ U))) / main := by
      rw [abs_of_nonneg hOutNonneg]
    _ ≤ CL / s + (CE * kDen / delta) / s := add_le_add hLocalN.2 hOut
    _ = Cfinal / s := by dsimp only [Cfinal]; ring

end
end Shao.OQ3
