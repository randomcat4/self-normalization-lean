import Shao.C2.ActualCenteredOrdinaryEnergy
import Shao.C2.AuxiliaryCenteredDoubleSandwich
import Shao.C2.ActualCenteredProductTransport
import Shao.C2.ActualBrownianThresholdPayment
import Shao.C2.UnitSecondEnergyLowerTailPayment

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
noncomputable section
namespace Shao.C2.CenteredConditionalComparison
open MeasureTheory ProbabilityTheory Set
open Shao.C2.BridgeDomination
open scoped BigOperators NNReal Topology Classical

theorem iid_centered_scaled_law_double_comparison :
    ∃ eta epsilon C : ℝ, 0 < eta ∧ 0 < epsilon ∧ 0 < C ∧
      ∀ {ΩB : Type*} [MeasurableSpace ΩB]
        (Bm : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
        IsBrownianReal Bm PB →
        ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
          (n : ℕ) (hn : 0 < n) (mu t x : ℝ), 0 < t → 1 ≤ x →
          x / Real.sqrt (n : ℝ) ≤ 1 / 2 →
          let chi : Measure ℝ := Measure.map (fun z : ℝ => (z - mu) / t) rho
          let delta : ℝ := (∫ z : ℝ, |z| ^ 3 ∂chi) / Real.sqrt (n : ℝ)
          let h : ℝ := 3 * ((n : ℝ) * |mu|)
          Integrable (fun z : ℝ => z ^ 2) chi →
          Integrable (fun z : ℝ => |z| ^ 3) chi →
          (∫ z : ℝ, z ∂chi) = 0 → (∫ z : ℝ, z ^ 2 ∂chi) = 1 →
          (∀ᵐ z : ℝ ∂chi, |z| ≤ eta * Real.sqrt (n : ℝ) / (x + h)) →
          1 / 2 ≤ (n : ℝ) * t ^ 2 → h ≤ 1 / 2 → (1 + x) * h ≤ 1 →
          delta * (1 + x) ^ 3 ≤ epsilon →
          |(Measure.pi (fun _ : Fin n => rho)).real (Shao.C2.doubleCrossing hn x) -
              PB.real {omega |
                (∃ s : BridgeTime, x ≤ Bm ⟨(s : ℝ), s.property.1⟩ omega) ∧
                ∃ s : BridgeTime, Bm ⟨(s : ℝ), s.property.1⟩ omega ≤ -x}| ≤
            C * (delta * (1 + x) ^ 3 + (1 + x) * h) * Shao.standardNormalTail x := by
  obtain ⟨eta, eps, Cg, heta, heps, hCg, hCompare⟩ :=
    Shao.C2.ActualCenteredOrdinaryEnergy.iid_actual_centered_ordinary_energy_relative_comparison
  refine ⟨eta, min eps (1 / 16), 8 * Cg * Real.exp 2 + 32 + 8 * Real.exp 2,
    heta, lt_min heps (by norm_num), by positivity, ?_⟩
  intro ΩB _ Bm PB _ hBrownian rho _ n hn mu t x ht hx hxScale
    chi delta h h2 h3 hmean hsecond hbound hScale hHalf hShift hsmall
  have hTransport :=
    Shao.C2.ActualCenteredProductTransport.iid_centered_scaled_product_transport
      rho n hn mu t ht
  letI : IsProbabilityMeasure chi := hTransport.1
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
  let Pc : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => chi)
  letI : IsProbabilityMeasure P := by dsimp only [P]; infer_instance
  let a : ℝ := 1 + x
  let A : ℝ := 8 * Cg * Real.exp 2
  let B : ℝ := 8 * Real.exp 2
  let u : ℝ := delta * a ^ 3
  let v : ℝ := a * h
  let DB : ℝ → Set ΩB := fun y => {omega |
    (∃ s : BridgeTime, y ≤ Bm ⟨(s : ℝ), s.property.1⟩ omega) ∧
      ∃ s : BridgeTime, Bm ⟨(s : ℝ), s.property.1⟩ omega ≤ -y}
  let E : ℝ := A * u * Shao.standardNormalTail x + B * v * Shao.standardNormalTail x
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hxpos : 0 < x := by linarith only [hx]
  have ha : 0 < a := by dsimp only [a]; linarith only [hx]
  have hh : 0 ≤ h := by dsimp only [h]; positivity
  have hdelta : 0 ≤ delta := by
    dsimp only [delta]
    exact div_nonneg (integral_nonneg (fun z => pow_nonneg (abs_nonneg z) 3))
      (Real.sqrt_nonneg _)
  have hPsi : 0 ≤ Shao.standardNormalTail x :=
    (Shao.standardNormalTail_basic.2.2.1 x).1.le
  have hu : 0 ≤ u := mul_nonneg hdelta (pow_nonneg ha.le 3)
  have hv : 0 ≤ v := mul_nonneg ha.le hh
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hNeigh : h ≤ 1 / a := by
    apply (le_div_iff₀ ha).mpr
    simpa only [a, mul_comm] using hShift
  have hsmallCmp : delta * a ^ 3 ≤ eps := hsmall.trans (min_le_left _ _)
  have hsmallEnergy : delta * a ^ 3 ≤ 1 / 16 := hsmall.trans (min_le_right _ _)
  have hPaid :=
    Shao.C2.UnitSecondEnergyLowerTailPayment.iid_unit_second_energy_lower_tail_gaussian_payment
      chi n hn h2 h3 hsecond x hx0 hsmallEnergy
  change 0 < delta ∧
    Pc.real {w : Shao.Path n | Shao.energy w ≤ (n : ℝ) / 2} ≤
      32 * u * Shao.standardNormalTail x at hPaid
  let bad : Set (Shao.Path n) :=
    {w | Shao.energy (fun i => w i - mu) < 1 / 4}
  have hEnergySet :
      {w : Shao.Path n | t ^ 2 * Shao.energy w ≤ (n : ℝ) * t ^ 2 / 2} =
        {w : Shao.Path n | Shao.energy w ≤ (n : ℝ) / 2} := by
    ext w
    change t ^ 2 * Shao.energy w ≤ (n : ℝ) * t ^ 2 / 2 ↔
      Shao.energy w ≤ (n : ℝ) / 2
    rw [show (n : ℝ) * t ^ 2 / 2 = t ^ 2 * ((n : ℝ) / 2) by ring]
    exact mul_le_mul_iff_right₀ (sq_pos_of_pos ht)
  have hBad : P.real bad ≤ 32 * u * Shao.standardNormalTail x := by
    have hQuarter : (1 / 4 : ℝ) ≤ (n : ℝ) * t ^ 2 / 2 := by
      linarith only [hScale]
    have hSub : bad ⊆
        {w : Shao.Path n | Shao.energy (fun i => w i - mu) ≤ (n : ℝ) * t ^ 2 / 2} := by
      intro w hw
      exact (le_of_lt hw).trans hQuarter
    calc
      P.real bad ≤ P.real
          {w : Shao.Path n | Shao.energy (fun i => w i - mu) ≤ (n : ℝ) * t ^ 2 / 2} :=
        measureReal_mono hSub
      _ = Pc.real
          {w : Shao.Path n | t ^ 2 * Shao.energy w ≤ (n : ℝ) * t ^ 2 / 2} :=
        hTransport.2.2.2 ((n : ℝ) * t ^ 2 / 2)
      _ = Pc.real {w : Shao.Path n | Shao.energy w ≤ (n : ℝ) / 2} := by
        rw [hEnergySet]
      _ ≤ 32 * u * Shao.standardNormalTail x := hPaid.2
  have hEnd (y : ℝ) (hy : 1 / 2 ≤ y) (hymax : y ≤ x + h)
      (hyDist : |y - x| ≤ h) :
      |P.real {w : Shao.Path n | (fun i => w i - mu) ∈ Shao.C2.doubleCrossing hn y} -
        PB.real (DB x)| ≤ E := by
    have hypos : 0 < y := by linarith only [hy]
    have hya : y ≤ a := by dsimp only [a]; linarith only [hymax, hHalf]
    have hsupport : ∀ᵐ z : ℝ ∂chi,
        |z| ≤ eta * Real.sqrt (n : ℝ) / y := by
      filter_upwards [hbound] with z hz
      exact hz.trans (div_le_div_of_nonneg_left
        (mul_nonneg heta.le (Real.sqrt_nonneg _)) hypos hymax)
    have hsmallY : delta * y ^ 3 ≤ eps := by
      exact (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hypos.le hya 3) hdelta).trans hsmallCmp
    have hCmp := hCompare Bm PB hBrownian chi n hn y hy hsupport hmean hsecond hsmallY
    change |Pc.real (Shao.C2.doubleCrossing hn y) - PB.real (DB y)| ≤
      Cg * delta * (1 + y) ^ 3 * Shao.standardNormalTail y at hCmp
    have hMove :=
      Shao.C2.ActualBrownianThresholdPayment.brownian_double_local_threshold_payment
        Bm PB hBrownian x y hxpos hypos (hyDist.trans hNeigh)
    change Shao.standardNormalTail y ≤ Real.exp 2 * Shao.standardNormalTail x ∧
      |PB.real (DB y) - PB.real (DB x)| ≤
        (8 * Real.exp 2) * a * |y - x| * Shao.standardNormalTail x at hMove
    have hOnePlus : 1 + y ≤ 2 * a := by
      dsimp only [a]
      linarith only [hymax, hHalf, hx]
    have hCube : (1 + y) ^ 3 ≤ 8 * a ^ 3 := by
      calc
        (1 + y) ^ 3 ≤ (2 * a) ^ 3 :=
          pow_le_pow_left₀ (by linarith only [hy]) hOnePlus 3
        _ = 8 * a ^ 3 := by ring
    have hGaussian : Cg * delta * (1 + y) ^ 3 * Shao.standardNormalTail y ≤
        A * u * Shao.standardNormalTail x := by
      calc
        Cg * delta * (1 + y) ^ 3 * Shao.standardNormalTail y ≤
            Cg * delta * (1 + y) ^ 3 * (Real.exp 2 * Shao.standardNormalTail x) :=
          mul_le_mul_of_nonneg_left hMove.1
            (mul_nonneg (mul_nonneg hCg.le hdelta) (pow_nonneg (by linarith only [hy]) 3))
        _ ≤ Cg * delta * (8 * a ^ 3) * (Real.exp 2 * Shao.standardNormalTail x) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hCube (mul_nonneg hCg.le hdelta))
            (mul_nonneg (Real.exp_pos 2).le hPsi)
        _ = A * u * Shao.standardNormalTail x := by dsimp only [A, u]; ring
    have hThreshold : (8 * Real.exp 2) * a * |y - x| * Shao.standardNormalTail x ≤
        B * v * Shao.standardNormalTail x := by
      calc
        (8 * Real.exp 2) * a * |y - x| * Shao.standardNormalTail x ≤
            (8 * Real.exp 2) * a * h * Shao.standardNormalTail x :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hyDist (by positivity)) hPsi
        _ = B * v * Shao.standardNormalTail x := by dsimp only [B, v]; ring
    calc
      |P.real {w : Shao.Path n | (fun i => w i - mu) ∈ Shao.C2.doubleCrossing hn y} -
          PB.real (DB x)| = |Pc.real (Shao.C2.doubleCrossing hn y) - PB.real (DB x)| := by
        rw [hTransport.2.2.1 y]
      _ ≤ |Pc.real (Shao.C2.doubleCrossing hn y) - PB.real (DB y)| +
          |PB.real (DB y) - PB.real (DB x)| := abs_sub_le _ _ _
      _ ≤ Cg * delta * (1 + y) ^ 3 * Shao.standardNormalTail y +
          (8 * Real.exp 2) * a * |y - x| * Shao.standardNormalTail x :=
        add_le_add hCmp hMove.2
      _ ≤ E := add_le_add hGaussian hThreshold
  have hPlusDist : |x + h - x| ≤ h := by
    rw [show x + h - x = h by ring, abs_of_nonneg hh]
  have hMinusDist : |x - h - x| ≤ h := by
    rw [show x - h - x = -h by ring, abs_neg, abs_of_nonneg hh]
  have hPlus := hEnd (x + h) (by linarith only [hx, hh]) le_rfl hPlusDist
  have hMinus := hEnd (x - h) (by linarith only [hx, hHalf])
    (by linarith only [hh]) hMinusDist
  have hSand :=
    Shao.C2.AuxiliaryCenteredDoubleSandwich.auxiliary_centered_double_probability_sandwich
      hn P mu x hx0 hxScale
  change P.real {w : Shao.Path n | (fun i => w i - mu) ∈
      Shao.C2.doubleCrossing hn (x + h)} - P.real bad ≤
        P.real (Shao.C2.doubleCrossing hn x) ∧
    P.real (Shao.C2.doubleCrossing hn x) ≤
      P.real {w : Shao.Path n | (fun i => w i - mu) ∈
        Shao.C2.doubleCrossing hn (x - h)} + P.real bad at hSand
  have hTotal : |P.real (Shao.C2.doubleCrossing hn x) - PB.real (DB x)| ≤
      E + 32 * u * Shao.standardNormalTail x := by
    apply abs_le.mpr
    constructor
    · linarith only [(abs_le.mp hPlus).1, hSand.1, hBad]
    · linarith only [(abs_le.mp hMinus).2, hSand.2, hBad]
  change |P.real (Shao.C2.doubleCrossing hn x) - PB.real (DB x)| ≤
    (A + 32 + B) * (u + v) * Shao.standardNormalTail x
  calc
    |P.real (Shao.C2.doubleCrossing hn x) - PB.real (DB x)| ≤
        E + 32 * u * Shao.standardNormalTail x := hTotal
    _ ≤ E + 32 * u * Shao.standardNormalTail x +
        ((A + 32) * (v * Shao.standardNormalTail x) + B * (u * Shao.standardNormalTail x)) :=
      le_add_of_nonneg_right (add_nonneg
        (mul_nonneg (add_nonneg hA (by norm_num)) (mul_nonneg hv hPsi))
        (mul_nonneg hB (mul_nonneg hu hPsi)))
    _ = (A + 32 + B) * (u + v) * Shao.standardNormalTail x := by
      dsimp only [E]
      ring

end Shao.C2.CenteredConditionalComparison
