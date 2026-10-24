/- Mathematical candidate only: no production bodies or Lean/AX execution.
   PR333 exact source is a pending independent-review dependency.
   One public head; no new definitions, instances, global or private helpers. -/
import Shao.Probability.SourceNonresidualBrownian
import Shao.Probability.SourceTruncationBridge
import Shao.Probability.OriginalCDFPullback
import Shao.Probability.SourceMomentDomain
import Shao.Probability.QuadraticEnergyLowerTail

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
noncomputable section
namespace Shao.Probability.SourceOriginalLawNonresidualReturn
open MeasureTheory ProbabilityTheory
open Shao.C2.BridgeDomination
open scoped BigOperators NNReal

private theorem olr_normalized_nonresidual_return :
    ∀ cstar : ℝ, 0 < cstar → ∃ C : ℝ, 0 < C ∧
      ∀ {ΩB : Type*} [MeasurableSpace ΩB]
        (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
        IsBrownianReal B PB →
        ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu]
          (n : ℕ) (hn : 0 < n),
          Integrable (fun z : ℝ => z ^ 2) nu →
          (∫ z : ℝ, z ∂nu) = 0 →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
          ∀ x : ℝ, 1 ≤ x → x ^ 6 ≤ (n : ℝ) →
            (n : ℝ) * (∫ z : ℝ, Shao.truncationF (x * z) ∂nu) ≤ 1 →
            let R : ℝ := Shao.truncationBudget nu n x
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
            let DB : Set ΩB := {omega |
              (∃ t : BridgeTime, x ≤ B ⟨(t : ℝ), t.property.1⟩ omega) ∧
              ∃ t : BridgeTime, B ⟨(t : ℝ), t.property.1⟩ omega ≤ -x}
            cstar * Real.exp (-3 * x ^ 2) ≤ R →
            |P.real (Shao.C2.doubleCrossing hn x) - PB.real DB| ≤
              C * R * Shao.standardNormalTail x := by
  classical
  intro cstar hcs
  let K : ℝ := Real.sqrt (2 * Real.pi)
  let C0 : ℝ := 2 * K + 2 * Real.exp 1 + 2
  let eps : ℝ := 1 / 1024
  let eta : ℝ := eps ^ 3 / 2 ^ 20
  obtain ⟨Cc, hCc, hCoarse⟩ := original_coarse_gaussian_upper
  obtain ⟨Cb, hCb, hBad⟩ := sourceTruncation_original_two_signs_bad_crossing
  let A0 : ℝ := 512 * C0 * Real.exp 2 + 512 * K + Cb / eps ^ 3
  let B0 : ℝ := Real.exp 1 * (C0 + 2) + 2
  let Ccompact : ℝ := Real.exp 12 / (cstar * Shao.standardNormalTail 2)
  let Clarge : ℝ := (Cc + 2) / eta
  let Csmall : ℝ := A0 + 2 * K * B0 / cstar
  let C : ℝ := 1 + Ccompact + Clarge + Csmall
  have hK : 0 < K := by dsimp [K]; positivity
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  have heps : 0 < eps := by norm_num [eps]
  have heta : 0 < eta := by norm_num [eta, eps]
  have hA0 : 0 ≤ A0 := by dsimp [A0]; positivity
  have hB0 : 0 ≤ B0 := by dsimp [B0]; positivity
  have ht2 : 0 < Shao.standardNormalTail 2 := (Shao.standardNormalTail_basic.2.2.1 2).1
  have hCcompact : 0 ≤ Ccompact := by dsimp [Ccompact]; positivity
  have hClarge : 0 ≤ Clarge := by dsimp [Clarge]; positivity
  have hCsmall : 0 ≤ Csmall := by dsimp [Csmall]; positivity
  have hCcompactC : Ccompact ≤ C := by dsimp [C]; linarith only [hCcompact, hClarge, hCsmall]
  have hClargeC : Clarge ≤ C := by dsimp [C]; linarith only [hCcompact, hClarge, hCsmall]
  have hCsmallC : Csmall ≤ C := by dsimp [C]; linarith only [hCcompact, hClarge, hCsmall]
  refine ⟨C, by dsimp [C]; linarith only [hCcompact, hClarge, hCsmall], ?_⟩
  intro ΩB hΩB B PB hPB hB nu hNu n hn h2 hmean hnorm x hx hsize hcut R P DB hnon
  letI : IsProbabilityMeasure PB := hPB
  letI : IsProbabilityMeasure nu := hNu
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hN : 0 < (n : ℝ) := by exact_mod_cast hn
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hR : 0 < R := (mul_pos hcs (Real.exp_pos _)).trans_le hnon
  have ht : 0 < Shao.standardNormalTail x := (Shao.standardNormalTail_basic.2.2.1 x).1
  let d : ℝ := PB.real DB
  obtain ⟨hU, hL, hDB, hUL, hId, hd0, hdCoarse, hdExp⟩ :=
    SourceNonresidualBrownian.actual_brownian_weak_double_crossing B PB hB x (by linarith only [hx])
  change 0 ≤ d at hd0
  change d ≤ 2 * Shao.standardNormalTail x at hdCoarse
  change d ≤ 2 * Real.exp (-9 * x ^ 2 / 2) at hdExp
  have hdPaid : d ≤ 2 * Real.exp (-4 * x ^ 2) := by
    apply hdExp.trans
    gcongr
    nlinarith only [sq_nonneg x]
  have hP0 : 0 ≤ P.real (Shao.C2.doubleCrossing hn x) := measureReal_nonneg
  have hErr : |P.real (Shao.C2.doubleCrossing hn x) - d| ≤
      P.real (Shao.C2.doubleCrossing hn x) + d := by
    apply abs_le.mpr
    constructor <;> linarith only [hP0, hd0]
  by_cases hx2 : x ≤ 2
  · have hP1 : P.real (Shao.C2.doubleCrossing hn x) ≤ 1 := measureReal_le_one
    have hd1 : d ≤ 1 := measureReal_le_one
    have herr1 : |P.real (Shao.C2.doubleCrossing hn x) - d| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> linarith only [hP0, hP1, hd0, hd1]
    have hRlo : cstar * Real.exp (-12) ≤ R := by
      apply le_trans _ hnon
      apply mul_le_mul_of_nonneg_left _ hcs.le
      apply Real.exp_le_exp.mpr
      have hs := pow_le_pow_left₀ hx0 hx2 2
      norm_num at hs
      nlinarith only [hs]
    have htail2 : Shao.standardNormalTail 2 ≤ Shao.standardNormalTail x :=
      Shao.standardNormalTail_basic.1 hx2
    have hprod : cstar * Real.exp (-12) * Shao.standardNormalTail 2 ≤
        R * Shao.standardNormalTail x :=
      mul_le_mul hRlo htail2 ht2.le hR.le
    have hPaid : 1 ≤ Ccompact * (R * Shao.standardNormalTail x) := by
      have hh := mul_le_mul_of_nonneg_left hprod hCcompact
      have hid : Ccompact * (cstar * Real.exp (-12) * Shao.standardNormalTail 2) = 1 := by
        dsimp [Ccompact]
        field_simp
        rw [← Real.exp_add]
        norm_num
      rwa [hid] at hh
    calc
      _ ≤ 1 := herr1
      _ ≤ Ccompact * (R * Shao.standardNormalTail x) := hPaid
      _ ≤ C * (R * Shao.standardNormalTail x) :=
        mul_le_mul_of_nonneg_right hCcompactC (by positivity)
      _ = _ := by ring
  have hx2p : 2 < x := lt_of_not_ge hx2
  by_cases hLarge : eta ≤ R
  · have hCrs := hCoarse nu hNu n hn h2 hmean hnorm x (by linarith only [hx]) hsize hcut
    have hDP : P.real (Shao.C2.doubleCrossing hn x) ≤ Cc * Shao.standardNormalTail x :=
      (measureReal_mono (μ := P) Set.inter_subset_left).trans hCrs
    have hCoeff : Cc + 2 ≤ Clarge * R := by
      calc
        _ = Clarge * eta := by dsimp [Clarge]; field_simp
        _ ≤ Clarge * R := mul_le_mul_of_nonneg_left hLarge hClarge
    calc
      _ ≤ P.real (Shao.C2.doubleCrossing hn x) + d := hErr
      _ ≤ (Cc + 2) * Shao.standardNormalTail x := by linarith only [hDP, hdCoarse]
      _ ≤ (Clarge * R) * Shao.standardNormalTail x :=
        mul_le_mul_of_nonneg_right hCoeff ht.le
      _ ≤ (C * R) * Shao.standardNormalTail x := by gcongr
  have hSmall : R < eta := lt_of_not_ge hLarge
  have hRcut : R ≤ eps ^ 3 / 8 := by
    have he : eta ≤ eps ^ 3 / 8 := by norm_num [eta, eps]
    exact hSmall.le.trans he
  let a : ℝ := 1 + x
  have ha : 0 < a := by dsimp [a]; linarith only [hx, hx0, hx2p]
  have ha1 : 1 ≤ a := by dsimp [a]; linarith only [hx, hx0, hx2p]
  have ha3 : 3 ≤ a := by dsimp [a]; linarith only [hx, hx0, hx2p]
  let rhoA : Measure ℝ := ProbabilityTheory.cond nu {z | |z| ≤ eps / a}
  obtain ⟨hMass, hMass1, hAprob, hAsp, hA1, hA2, hA3, hA4⟩ :=
    Shao.sourceTruncation_law_data nu n h2 hnorm x eps hx0 heps (by norm_num [eps]) hRcut
  letI : IsProbabilityMeasure rhoA := hAprob
  let m : ℝ := ∫ z : ℝ, z ∂rhoA
  let d0 : ℝ := (n : ℝ) * |m|
  let g : ℝ := (n : ℝ) * ∫ z : ℝ, |z| ^ 3 ∂rhoA
  let V : ℝ := (n : ℝ) * ∫ z : ℝ, (z - m) ^ 2 ∂rhoA
  obtain ⟨hm, hg, h4, hC3, hC3le⟩ :=
    Shao.sourceTruncation_paid_moments nu n h2 hnorm hmean x eps hx0 heps
      (by norm_num [eps]) hRcut
  change d0 ≤ 2 * R / (eps ^ 2 * a) at hm
  change g ≤ 2 * R / a ^ 3 at hg
  obtain ⟨hA2lo, hA2hi, hmu2, hvDef, hvInt, hvPos, hvLo, hvHi⟩ :=
    Shao.sourceTruncation_variance_bounds nu n h2 hnorm hmean x eps hx0 heps
      (by norm_num [eps]) hRcut
  have hVeq : V = (n : ℝ) * variance (id : ℝ → ℝ) rhoA := by
    dsimp only [V]
    rw [← hvInt]
  have hVlo : (1 / 2 : ℝ) ≤ V := by rw [hVeq]; exact hvLo
  have hVhi : V ≤ (4 / 3 : ℝ) := by rw [hVeq]; exact hvHi
  have hV : 0 < V := by linarith only [hVlo]
  have hC1 : Integrable (fun z : ℝ => z - m) rhoA := hA1.sub (integrable_const m)
  have hC2 : Integrable (fun z : ℝ => (z - m) ^ 2) rhoA := by
    convert (hA2.sub (hA1.const_mul (2 * m))).add (integrable_const (m ^ 2)) using 1
    funext z
    change (z - m) ^ 2 = z ^ 2 - (2 * m) * z + m ^ 2
    ring
  have hCMean : (∫ z : ℝ, z - m ∂rhoA) = 0 := by
    rw [integral_sub hA1 (integrable_const m)]
    simp only [integral_const, probReal_univ, one_smul]
    change m - m = 0
    ring
  let sV : ℝ := Real.sqrt V
  have hsV : 0 < sV := Real.sqrt_pos.2 hV
  have hsV2 : sV ^ 2 = V := Real.sq_sqrt hV.le
  have hsVhalf : (1 / 2 : ℝ) ≤ sV := by
    apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hsV.le).mp
    rw [hsV2]
    nlinarith only [hVlo]
  let f : ℝ → ℝ := fun z => (z - m) / sV
  let zeta : Measure ℝ := Measure.map f rhoA
  have hfm : Measurable f := by fun_prop
  letI : IsProbabilityMeasure zeta := by dsimp [zeta]; infer_instance
  have hf2 : Integrable (fun z : ℝ => (f z) ^ 2) rhoA := by
    simpa only [f, div_pow] using hC2.div_const (sV ^ 2)
  have hfcube (z : ℝ) : |f z| ^ 3 = |z - m| ^ 3 / sV ^ 3 := by
    change |(z - m) / sV| ^ 3 = |z - m| ^ 3 / sV ^ 3
    rw [abs_div, abs_of_pos hsV, div_pow]
  have hf3 : Integrable (fun z : ℝ => |f z| ^ 3) rhoA :=
    (hC3.div_const (sV ^ 3)).congr (ae_of_all rhoA (fun z => (hfcube z).symm))
  have hz2 : Integrable (fun z : ℝ => z ^ 2) zeta :=
    (integrable_map_measure (continuous_id.pow 2).aestronglyMeasurable hfm.aemeasurable).2 hf2
  have hz3 : Integrable (fun z : ℝ => |z| ^ 3) zeta :=
    (integrable_map_measure (continuous_abs.pow 3).aestronglyMeasurable hfm.aemeasurable).2 hf3
  have hzMean : (∫ z : ℝ, z ∂zeta) = 0 := by
    rw [show zeta = Measure.map f rhoA from rfl,
      integral_map (μ := rhoA) (φ := f) (f := fun z : ℝ => z) hfm.aemeasurable
        continuous_id.aestronglyMeasurable]
    change (∫ z : ℝ, (z - m) / sV ∂rhoA) = 0
    rw [integral_div, hCMean, zero_div]
  have hzNorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂zeta) = 1 := by
    rw [show zeta = Measure.map f rhoA from rfl,
      integral_map (μ := rhoA) (φ := f) (f := fun z : ℝ => z ^ 2) hfm.aemeasurable
        (continuous_id.pow 2).aestronglyMeasurable]
    simp_rw [f, div_pow]
    rw [integral_div, ← mul_div_assoc, hsV2]
    change V / V = 1
    exact div_self hV.ne'
  let delta : ℝ := (n : ℝ) * ∫ z : ℝ, |z| ^ 3 ∂zeta
  have hDeltaEq : delta = ((n : ℝ) * ∫ z : ℝ, |z - m| ^ 3 ∂rhoA) / sV ^ 3 := by
    dsimp only [delta, zeta]
    rw [integral_map (μ := rhoA) (φ := f) (f := fun z : ℝ => |z| ^ 3) hfm.aemeasurable
      (continuous_abs.pow 3).aestronglyMeasurable]
    simp_rw [hfcube]
    rw [integral_div, mul_div_assoc]
  have hDeltaBound : delta ≤ 64 * R / a ^ 3 := by
    rw [hDeltaEq]
    apply (div_le_iff₀ (pow_pos hsV 3)).2
    have hc : (n : ℝ) * (∫ z : ℝ, |z - m| ^ 3 ∂rhoA) ≤ 8 * g := by
      have hh := mul_le_mul_of_nonneg_left hC3le hN.le
      convert hh using 1 <;> dsimp [g] <;> ring
    have hsCube : (1 / 4 : ℝ) ≤ sV ^ 3 := by
      calc
        _ = (1 / 2 : ℝ) * (1 / 2 : ℝ) := by norm_num
        _ ≤ V * sV := mul_le_mul hVlo hsVhalf (by norm_num) hV.le
        _ = sV ^ 3 := by rw [← hsV2]; ring
    have hRdiv : 0 ≤ R / a ^ 3 := by positivity
    have hHG : g ≤ 2 * (R / a ^ 3) := by simpa only [mul_div_assoc] using hg
    calc
      _ ≤ 8 * g := hc
      _ ≤ 8 * (2 * (R / a ^ 3)) := mul_le_mul_of_nonneg_left hHG (by norm_num)
      _ = (64 * (R / a ^ 3)) * (1 / 4) := by ring
      _ ≤ (64 * (R / a ^ 3)) * sV ^ 3 :=
        mul_le_mul_of_nonneg_left hsCube (by positivity)
      _ = _ := by ring
  have hmAbs : |m| ≤ eps / a := by
    calc
      _ = |∫ z : ℝ, z ∂rhoA| := rfl
      _ ≤ ∫ z : ℝ, |z| ∂rhoA := abs_integral_le_integral_abs
      _ ≤ ∫ _z : ℝ, eps / a ∂rhoA := integral_mono_ae hA1.abs (integrable_const _) hAsp
      _ = eps / a := by simp
  have hzSupport : ∀ᵐ z : ℝ ∂zeta, |z| ≤ 4 * eps / a := by
    apply (ae_map_iff hfm.aemeasurable (measurableSet_le continuous_abs.measurable measurable_const)).2
    filter_upwards [hAsp] with z hz
    change |z| ≤ eps / a at hz
    change |(z - m) / sV| ≤ 4 * eps / a
    rw [abs_div, abs_of_pos hsV]
    apply (div_le_iff₀ hsV).2
    have hzm : |z - m| ≤ 2 * eps / a :=
      (abs_sub z m).trans (by
        calc
          _ ≤ eps / a + eps / a := add_le_add hz hmAbs
          _ = _ := by ring)
    calc
      _ ≤ 2 * eps / a := hzm
      _ = (4 * (eps / a)) * (1 / 2) := by ring
      _ ≤ (4 * (eps / a)) * sV :=
        mul_le_mul_of_nonneg_left hsVhalf (by positivity)
      _ = _ := by ring
  let PA : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rhoA)
  let PZ : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => zeta)
  letI : IsProbabilityMeasure PA := by dsimp [PA]; infer_instance
  letI : IsProbabilityMeasure PZ := by dsimp [PZ]; infer_instance
  let T : Shao.Path n → Shao.Path n := fun A i => f (A i)
  have hTm : Measurable T := Measurable.of_eval (fun i => hfm.comp (measurable_pi_apply i))
  have hTmap : Measure.map T PA = PZ := Measure.pi_map_pi (fun _ : Fin n => hfm.aemeasurable)
  let Cpath : Shao.Path n → Shao.Path n := fun A i => A i - m
  have hCm : Measurable Cpath := by
    dsimp only [Cpath]
    fun_prop
  let E : Set (Shao.Path n) := {A | V / 2 ≤ Shao.energy (Cpath A)}
  have hEm : MeasurableSet E := measurableSet_le measurable_const
    (Shao.measurable_energy.comp hCm)
  let hs : ℝ := 3 * d0
  let y : ℝ := x - hs
  have hd0 : 0 ≤ d0 := by dsimp [d0]; positivity
  have hhs : 0 ≤ hs := by dsimp [hs]; positivity
  have hahs : a * hs ≤ 6 * R / eps ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ 3 * a by positivity)
    have heq : 3 * a * (2 * R / (eps ^ 2 * a)) = 6 * R / eps ^ 2 := by field_simp; ring
    dsimp only [hs]
    nlinarith only [hh, heq]
  have hahsSmall : a * hs ≤ 1 / 8 := by
    have hnum : 6 * eta / eps ^ 2 ≤ (1 / 8 : ℝ) := by norm_num [eta, eps]
    exact hahs.trans ((div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hSmall.le (by norm_num)) (sq_nonneg eps)).trans hnum)
  have hhsNear : hs ≤ 1 / a := (le_div_iff₀ ha).2 (by nlinarith only [hahsSmall])
  have hy : 1 ≤ y := by
    have hdiv : 1 / a ≤ (1 : ℝ) := (div_le_one ha).2 ha1
    dsimp [y]
    linarith only [hx2p, hhsNear, hdiv]
  have hy0 : 0 ≤ y := by linarith only [hy]
  have hyx : y ≤ x := by dsimp [y]; linarith only [hhs]
  have hya : y ≤ a := hyx.trans (by dsimp [a]; linarith only [hx, hx0, hx2p])
  have hNear : |y - x| ≤ 1 / (1 + x) := by
    dsimp only [y]
    rw [show x - hs - x = -hs by ring, abs_neg, abs_of_nonneg hhs]
    exact hhsNear
  have hShiftExp : 8 * x * hs ≤ 1 := by
    have hnum : 48 * eta / eps ^ 2 ≤ (1 : ℝ) := by norm_num [eta, eps]
    have hraw : 8 * (a * hs) ≤ 48 * R / eps ^ 2 := by
      calc
        _ ≤ 8 * (6 * R / eps ^ 2) := mul_le_mul_of_nonneg_left hahs (by norm_num)
        _ = _ := by ring
    have hxhs : 8 * x * hs ≤ 8 * (a * hs) := by
      dsimp [a]
      nlinarith only [hhs]
    apply hxhs.trans (hraw.trans _)
    apply le_trans _ hnum
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hSmall.le (by norm_num)) (sq_nonneg eps)
  have hASquare : (∫ z : ℝ, z ^ 2 ∂rhoA) ≤ (eps / a) ^ 2 := by
    calc
      _ ≤ ∫ _z : ℝ, (eps / a) ^ 2 ∂rhoA := by
        apply integral_mono_ae hA2 (integrable_const _)
        filter_upwards [hAsp] with z hz
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg z) (by positivity)).2 hz
      _ = (eps / a) ^ 2 := by simp
  have hSample : x ≤ Real.sqrt (n : ℝ) / 2 := by
    have hh : (3 / 4 : ℝ) ≤ (n : ℝ) * (eps / a) ^ 2 :=
      hA2lo.trans (mul_le_mul_of_nonneg_left hASquare hN.le)
    have hh' : (3 / 4 : ℝ) * a ^ 2 ≤ (n : ℝ) * eps ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos ha)).mp
      simpa only [div_pow, mul_div_assoc] using hh
    have hxa2 : x ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hx0 (by dsimp [a]; linarith only [hx, hx0, hx2p]) 2
    have hns := Real.sq_sqrt hN.le
    have hns0 := Real.sqrt_nonneg (n : ℝ)
    norm_num [eps] at hh'
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    apply (sq_le_sq₀ (by positivity : 0 ≤ x * 2) hns0).mp
    rw [mul_pow, hns]
    nlinarith only [hh', hxa2, hN.le]
  have hGeometry (A : Shao.Path n) :
      Real.sqrt (Shao.energy (Cpath A)) ≤
        Real.sqrt (Shao.energy A) + Real.sqrt (n : ℝ) * |m| := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i : Fin n => A i) (fun _ : Fin n => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at hcs
    have hSum : |∑ i : Fin n, A i| ≤
        Real.sqrt (n : ℝ) * Real.sqrt (Shao.energy A) := by
      apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
      rw [sq_abs, mul_pow, Real.sq_sqrt hN.le,
        Real.sq_sqrt (Shao.energy_nonneg A)]
      simpa only [Shao.energy, mul_comm] using hcs
    have hQC : Shao.energy (Cpath A) = Shao.energy A -
        2 * m * (∑ i : Fin n, A i) + (n : ℝ) * m ^ 2 := by
      change (∑ i : Fin n, (A i - m) ^ 2) = _
      calc
        _ = ∑ i : Fin n, ((A i) ^ 2 - 2 * m * A i + m ^ 2) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by
          simp only [Shao.energy, Finset.sum_add_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
    have hCross : -2 * m * (∑ i : Fin n, A i) ≤
        2 * |m| * (Real.sqrt (n : ℝ) * Real.sqrt (Shao.energy A)) := by
      calc
        _ ≤ 2 * |m * (∑ i : Fin n, A i)| := by
          have hh := neg_le_abs (m * (∑ i : Fin n, A i))
          linarith only [hh]
        _ = 2 * |m| * |∑ i : Fin n, A i| := by rw [abs_mul]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hSum (by positivity)
    have hRhs : (Real.sqrt (Shao.energy A) + Real.sqrt (n : ℝ) * |m|) ^ 2 =
        Shao.energy A + 2 * |m| * (Real.sqrt (n : ℝ) * Real.sqrt (Shao.energy A)) +
          (n : ℝ) * m ^ 2 := by
      calc
        _ = (Real.sqrt (Shao.energy A)) ^ 2 +
          2 * |m| * (Real.sqrt (n : ℝ) * Real.sqrt (Shao.energy A)) +
          (Real.sqrt (n : ℝ)) ^ 2 * |m| ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt (Shao.energy_nonneg A), Real.sq_sqrt hN.le, sq_abs]
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (Shao.energy_nonneg (Cpath A)), hRhs]
    rw [hQC]
    linarith only [hCross]
  have hPrefix (A : Shao.Path n) (k : ℕ) :
      |Shao.prefixSum A k - Shao.prefixSum (Cpath A) k| ≤ d0 := by
    let U : Finset (Fin n) := Finset.univ.filter (fun i => i.val < k)
    have hcard : U.card ≤ n := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        (Finset.card_le_card (Finset.filter_subset (fun i : Fin n => i.val < k) Finset.univ))
    have hcardR : (U.card : ℝ) ≤ n := by exact_mod_cast hcard
    change |(∑ i ∈ U, A i) - ∑ i ∈ U, (A i - m)| ≤ d0
    rw [← Finset.sum_sub_distrib]
    simp only [sub_sub_cancel, Finset.sum_const, nsmul_eq_mul, abs_mul]
    rw [abs_of_nonneg (show (0 : ℝ) ≤ (U.card : ℝ) from Nat.cast_nonneg U.card)]
    exact mul_le_mul_of_nonneg_right hcardR (abs_nonneg m)
  have hContain : Shao.C2.doubleCrossing hn x ∩ E ⊆
      {A : Shao.Path n | Cpath A ∈ Shao.C2.doubleCrossing hn y} := by
    intro A hA
    rcases hA with ⟨hD, hE⟩
    have hQC : (1 / 2 : ℝ) ≤ Real.sqrt (Shao.energy (Cpath A)) := by
      have he : V / 2 ≤ Shao.energy (Cpath A) := hE
      apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (Real.sqrt_nonneg (Shao.energy (Cpath A)))).mp
      rw [Real.sq_sqrt (Shao.energy_nonneg (Cpath A))]
      linarith only [he, hVlo]
    have hDrift : x * (Real.sqrt (n : ℝ) * |m|) ≤ d0 / 2 := by
      calc
        _ ≤ (Real.sqrt (n : ℝ) / 2) * (Real.sqrt (n : ℝ) * |m|) :=
          mul_le_mul_of_nonneg_right hSample (by positivity)
        _ = d0 / 2 := by
          dsimp [d0]
          rw [show Real.sqrt (n : ℝ) / 2 * (Real.sqrt (n : ℝ) * |m|) =
            (Real.sqrt (n : ℝ)) ^ 2 * |m| / 2 by ring, Real.sq_sqrt hN.le]
    have hShift : d0 + x * (Real.sqrt (n : ℝ) * |m|) ≤
        hs * Real.sqrt (Shao.energy (Cpath A)) := by
      have hh := mul_le_mul_of_nonneg_left hQC (show 0 ≤ hs by exact hhs)
      dsimp only [hs] at hh ⊢
      linarith only [hh, hDrift]
    have hWall : y * Real.sqrt (Shao.energy (Cpath A)) ≤
        x * Real.sqrt (Shao.energy A) - d0 := by
      have hh := mul_le_mul_of_nonneg_left (hGeometry A) hx0
      dsimp only [y]
      nlinarith only [hh, hShift]
    change (y * Real.sqrt (Shao.energy (Cpath A)) ≤ Shao.upperMax (Cpath A) hn) ∧
      (y * Real.sqrt (Shao.energy (Cpath A)) ≤ Shao.lowerMax (Cpath A) hn)
    constructor
    · obtain ⟨k, hk, hkn, hw⟩ := (Shao.upperMax_ge_iff A hn _).mp hD.1
      have hp := (le_abs_self (Shao.prefixSum A k - Shao.prefixSum (Cpath A) k)).trans
        (hPrefix A k)
      exact (show y * Real.sqrt (Shao.energy (Cpath A)) ≤ Shao.prefixSum (Cpath A) k by
        linarith only [hWall, hw, hp]).trans (Shao.le_upperMax (Cpath A) hn k hk hkn)
    · obtain ⟨k, hk, hkn, hw⟩ := (Shao.upperMax_ge_iff (-A) hn _).mp hD.2
      have hp := (neg_le_abs (Shao.prefixSum A k - Shao.prefixSum (Cpath A) k)).trans
        (hPrefix A k)
      rw [Shao.prefixSum_neg] at hw
      change y * Real.sqrt (Shao.energy (Cpath A)) ≤ Shao.upperMax (-(Cpath A)) hn
      have hw' := Shao.le_upperMax (-(Cpath A)) hn k hk hkn
      rw [Shao.prefixSum_neg] at hw'
      linarith only [hWall, hw, hp, hw']
  have hScaleC (A : Shao.Path n) : T A = sV⁻¹ • Cpath A := by
    funext i
    change (A i - m) / sV = sV⁻¹ * (A i - m)
    rw [div_eq_mul_inv, mul_comm]
  have hEventC : {A : Shao.Path n | Cpath A ∈ Shao.C2.doubleCrossing hn y} =
      T ⁻¹' Shao.C2.doubleCrossing hn y := by
    ext A
    change (y * Real.sqrt (Shao.energy (Cpath A)) ≤ Shao.upperMax (Cpath A) hn ∧
      y * Real.sqrt (Shao.energy (Cpath A)) ≤ Shao.lowerMax (Cpath A) hn) ↔
      (y * Real.sqrt (Shao.energy (T A)) ≤ Shao.upperMax (T A) hn ∧
      y * Real.sqrt (Shao.energy (T A)) ≤ Shao.lowerMax (T A) hn)
    rw [hScaleC, Shao.energy_smul, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (inv_pos.2 hsV).le,
      Shao.upperMax_smul_of_nonneg _ (inv_pos.2 hsV).le,
      Shao.lowerMax_smul_of_nonneg _ (inv_pos.2 hsV).le]
    rw [show y * (sV⁻¹ * Real.sqrt (Shao.energy (Cpath A))) =
      sV⁻¹ * (y * Real.sqrt (Shao.energy (Cpath A))) by ring]
    simp only [mul_le_mul_iff_right₀ (inv_pos.2 hsV)]
  have hCProb : PA.real {A : Shao.Path n | Cpath A ∈ Shao.C2.doubleCrossing hn y} =
      PZ.real (Shao.C2.doubleCrossing hn y) := by
    rw [hEventC, ← hTmap]
    simp only [Measure.real_def]
    rw [Measure.map_apply hTm (Shao.C2.measurableSet_doubleCrossing hn y)]
  obtain ⟨hDelta, hLow⟩ := finite_iid_energy_lower_tail zeta n hn hz2 hz3 hzNorm
    (1 / 2) (by norm_num) (by norm_num)
  change 0 < delta at hDelta
  change PZ.real {v : Shao.Path n | Shao.energy v ≤ 1 - (1 / 2 : ℝ)} ≤
    Real.exp (-((1 / 2 : ℝ) ^ 3 / (8 * delta ^ 2))) at hLow
  norm_num at hLow
  have hEnergyT (A : Shao.Path n) : Shao.energy (T A) = Shao.energy (Cpath A) / V := by
    rw [hScaleC, Shao.energy_smul, inv_pow, hsV2]
    ring
  have hLowContain : Eᶜ ⊆ T ⁻¹' {v : Shao.Path n | Shao.energy v ≤ 1 / 2} := by
    intro A hA
    have hh : Shao.energy (Cpath A) < V / 2 := lt_of_not_ge hA
    change Shao.energy (T A) ≤ (1 / 2 : ℝ)
    rw [hEnergyT]
    exact (div_le_iff₀ hV).2 (by linarith only [hh])
  have hELow : PA.real Eᶜ ≤ Real.exp (-(1 / (64 * delta ^ 2))) := by
    calc
      _ ≤ PA.real (T ⁻¹' {v : Shao.Path n | Shao.energy v ≤ 1 / 2}) :=
        measureReal_mono hLowContain
      _ = PZ.real {v : Shao.Path n | Shao.energy v ≤ 1 / 2} := by
        rw [← hTmap]
        simp only [Measure.real_def]
        rw [Measure.map_apply hTm (measurableSet_le Shao.measurable_energy measurable_const)]
      _ ≤ _ := by convert hLow using 1 <;> congr 1 <;> field_simp <;> ring
  let q : ℝ := 512 * R
  have hq : 0 < q := by dsimp [q]; positivity
  have hqsmall : q ≤ 1 / 32 := by
    have hh : 512 * eta ≤ (1 / 32 : ℝ) := by norm_num [eta, eps]
    exact (mul_le_mul_of_nonneg_left hSmall.le (by norm_num)).trans hh
  have hLowExponent : a ^ 6 / (16 * q ^ 2) ≤ 1 / (64 * delta ^ 2) := by
    have hd : delta * a ^ 3 ≤ 64 * R := (le_div_iff₀ (pow_pos ha 3)).mp hDeltaBound
    have hs := pow_le_pow_left₀ (show 0 ≤ delta * a ^ 3 by positivity) hd 2
    apply (div_le_div_iff₀ (by positivity : 0 < 16 * q ^ 2)
      (by positivity : 0 < 64 * delta ^ 2)).2
    dsimp only [q]
    nlinarith only [hs, sq_nonneg R]
  have hNumericExponent : x ^ 2 / 2 + a / q ≤ a ^ 6 / (16 * q ^ 2) := by
    have ha6 : a ^ 2 ≤ a ^ 6 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) ha1 4
      norm_num at hh
      nlinarith only [mul_le_mul_of_nonneg_left hh (sq_nonneg a)]
    have h32 : 32 * q ≤ a := by linarith only [hqsmall, ha1]
    have hq2 : q ^ 2 ≤ 1 / 16 := by
      have hh := pow_le_pow_left₀ hq.le hqsmall 2
      norm_num at hh
      linarith only [hh]
    apply (le_div_iff₀ (by positivity : 0 < 16 * q ^ 2)).2
    have hid : a / q * (16 * q ^ 2) = 16 * a * q := by field_simp
    rw [add_mul, hid]
    have hxa : x ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hx0 (by dsimp [a]; linarith only [hx, hx0, hx2p]) 2
    have hpart : 8 * x ^ 2 * q ^ 2 ≤ a ^ 2 / 2 := by
      have hh := mul_le_mul_of_nonneg_left hq2 (sq_nonneg x)
      nlinarith only [hh, hxa]
    have hpart2 : 16 * a * q ≤ a ^ 2 / 2 := by
      nlinarith only [mul_le_mul_of_nonneg_left h32 ha.le]
    nlinarith only [hpart, hpart2, ha6]
  have hExpSmall : Real.exp (-(a / q)) ≤ q / a := by
    have hh : a / q ≤ Real.exp (a / q) := by linarith only [Real.add_one_le_exp (a / q)]
    have hm := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-(a / q))).le
    rw [show Real.exp (a / q) * Real.exp (-(a / q)) = 1 by
      rw [← Real.exp_add]; simp] at hm
    apply (le_div_iff₀ ha).2
    have hm' := mul_le_mul_of_nonneg_right hm hq.le
    convert hm' using 1 <;> field_simp <;> ring
  have hDensity : Real.exp (-x ^ 2 / 2) = K * Shao.standardNormalDensity x := by
    dsimp [K]
    simp only [Shao.standardNormalDensity, gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
    field_simp
  have hMills : Real.exp (-x ^ 2 / 2) / a ≤ K * Shao.standardNormalTail x := by
    rw [hDensity, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (Shao.standardNormal_mills_bounds x hx0).1 hK.le
  have hEPaid : PA.real Eᶜ ≤ 512 * K * R * Shao.standardNormalTail x := by
    calc
      _ ≤ Real.exp (-(1 / (64 * delta ^ 2))) := hELow
      _ ≤ Real.exp (-(a ^ 6 / (16 * q ^ 2))) := Real.exp_le_exp.2 (neg_le_neg hLowExponent)
      _ ≤ Real.exp (-(x ^ 2 / 2 + a / q)) := Real.exp_le_exp.2 (neg_le_neg hNumericExponent)
      _ = Real.exp (-x ^ 2 / 2) * Real.exp (-(a / q)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-x ^ 2 / 2) * (q / a) :=
        mul_le_mul_of_nonneg_left hExpSmall (Real.exp_pos _).le
      _ = q * (Real.exp (-x ^ 2 / 2) / a) := by ring
      _ ≤ q * (K * Shao.standardNormalTail x) := mul_le_mul_of_nonneg_left hMills hq.le
      _ = _ := by dsimp [q]; ring
  have hPASand : PA.real (Shao.C2.doubleCrossing hn x) ≤
      PZ.real (Shao.C2.doubleCrossing hn y) + PA.real Eᶜ := by
    have hSub : Shao.C2.doubleCrossing hn x ⊆
        {A : Shao.Path n | Cpath A ∈ Shao.C2.doubleCrossing hn y} ∪ Eᶜ := by
      intro A hA
      by_cases hAE : A ∈ E
      · exact Or.inl (hContain ⟨hA, hAE⟩)
      · exact Or.inr hAE
    exact (measureReal_mono (μ := PA) hSub).trans
      ((measureReal_union_le _ _).trans_eq (by rw [hCProb]))
  let uY : ℝ := delta * (1 + y) ^ 3
  have hUy : uY ≤ 512 * R := by
    have hdelta := (le_div_iff₀ (pow_pos ha 3)).mp hDeltaBound
    have hxa : 1 + y ≤ 2 * a := by dsimp [a]; linarith only [hyx, hx0]
    calc
      _ ≤ delta * (2 * a) ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith only [hy0]) hxa 3) hDelta.le
      _ = 8 * (delta * a ^ 3) := by ring
      _ ≤ _ := by linarith only [hdelta]
  have hUySmall : uY ≤ 1 / 20000 := by
    have hh : 512 * eta ≤ (1 / 20000 : ℝ) := by norm_num [eta, eps]
    exact hUy.trans ((mul_le_mul_of_nonneg_left hSmall.le (by norm_num)).trans hh)
  have hzY : ∀ᵐ z : ℝ ∂zeta, |z| ≤ 1 / (4 * y) := by
    have hbound : 4 * eps / a ≤ 1 / (4 * y) := by
      apply (div_le_div_iff₀ ha (by linarith only [hy] : 0 < 4 * y)).2
      norm_num [eps]
      nlinarith only [hya, hy0]
    filter_upwards [hzSupport] with z hz
    exact hz.trans hbound
  have hCentered :=
    (SourceNonresidualBrownian.source_centered_bounded_nonresidual_brownian_comparison
      1 (by norm_num)).2.2 B PB hB zeta n hn y hy hzY hzMean hzNorm
  obtain ⟨_, _, _, _, _, _, _, hComp⟩ := hCentered
  have hTwo := (hComp hUySmall).1
  let DBY : Set ΩB := {omega |
    (∃ t : BridgeTime, y ≤ B ⟨(t : ℝ), t.property.1⟩ omega) ∧
    ∃ t : BridgeTime, B ⟨(t : ℝ), t.property.1⟩ omega ≤ -y}
  change |PZ.real (Shao.C2.doubleCrossing hn y) - PB.real DBY| ≤
    C0 * uY * Shao.standardNormalTail y + C0 * Real.exp (-4 * y ^ 2) at hTwo
  have hDY := (SourceNonresidualBrownian.actual_brownian_weak_double_crossing B PB hB y
    (by linarith only [hy])).2.2.2.2.2.2.2
  change PB.real DBY ≤ 2 * Real.exp (-9 * y ^ 2 / 2) at hDY
  have hDY4 : PB.real DBY ≤ 2 * Real.exp (-4 * y ^ 2) := by
    apply hDY.trans
    gcongr
    nlinarith only [sq_nonneg y]
  have hPZY : PZ.real (Shao.C2.doubleCrossing hn y) ≤
      C0 * uY * Shao.standardNormalTail y + (C0 + 2) * Real.exp (-4 * y ^ 2) := by
    have hh := le_abs_self (PZ.real (Shao.C2.doubleCrossing hn y) - PB.real DBY)
    nlinarith only [hh, hTwo, hDY4]
  have hTailY : Shao.standardNormalTail y ≤ Real.exp 2 * Shao.standardNormalTail x :=
    (Shao.standardNormalTail_local_comparison x y hx0 hy0 hNear).2
  have hExpY : Real.exp (-4 * y ^ 2) ≤ Real.exp 1 * Real.exp (-4 * x ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp only [y]
    nlinarith only [hShiftExp, sq_nonneg hs]
  have hPZPaid : PZ.real (Shao.C2.doubleCrossing hn y) ≤
      (512 * C0 * Real.exp 2) * R * Shao.standardNormalTail x +
        (Real.exp 1 * (C0 + 2)) * Real.exp (-4 * x ^ 2) := by
    apply hPZY.trans
    calc
      _ ≤ C0 * (512 * R) * (Real.exp 2 * Shao.standardNormalTail x) +
          (C0 + 2) * (Real.exp 1 * Real.exp (-4 * x ^ 2)) := by
        apply add_le_add
        · apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hUy hC0.le
          · exact hTailY
          · exact (Shao.standardNormalTail_basic.2.2.1 y).1.le
          · positivity
        · exact mul_le_mul_of_nonneg_left hExpY (by positivity)
      _ = _ := by ring
  have hPAPaid : PA.real (Shao.C2.doubleCrossing hn x) ≤
      (512 * C0 * Real.exp 2 + 512 * K) * R * Shao.standardNormalTail x +
        (Real.exp 1 * (C0 + 2)) * Real.exp (-4 * x ^ 2) := by
    nlinarith only [hPASand, hPZPaid, hEPaid]
  let N : Set (Shao.Path n) := {v | ∀ i : Fin n, |v i| ≤ eps / a}
  have hNm : MeasurableSet N := by
    have hrepr : N = ⋂ i : Fin n, {v : Shao.Path n | |v i| ≤ eps / a} := by
      ext v
      simp only [N, Set.mem_setOf_eq, Set.mem_iInter]
    rw [hrepr]
    exact MeasurableSet.iInter (fun i => measurableSet_le
      (continuous_abs.measurable.comp (measurable_pi_apply i)) measurable_const)
  have hNrepr : (⋂ i : Fin n, (Function.eval i) ⁻¹' {z : ℝ | |z| ≤ eps / a}) = N := by
    ext v
    simp only [N, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq, Function.eval]
  have hIndep : iIndepFun (fun i : Fin n => Function.eval i) P :=
    iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable)
  have hLaw (i : Fin n) : IdentDistrib (Function.eval i) (id : ℝ → ℝ) P nu := by
    refine ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    exact (measurePreserving_eval (fun _ : Fin n => nu) i).map_eq.trans Measure.map_id.symm
  have hData := sourceTruncation_conditioned_sample (fun i : Fin n => measurable_pi_apply i)
    hIndep hLaw h2 x eps hx0 heps (by norm_num [eps]) hRcut
  dsimp only at hData
  change P.real ((⋂ i : Fin n, (Function.eval i) ⁻¹' {z : ℝ | |z| ≤ eps / a})ᶜ) ≤
    R / eps ^ 3 ∧ _ at hData
  rw [hNrepr] at hData
  have hCond : ProbabilityTheory.cond P N = PA := by
    have hh := hData.2.2.2.1
    change Measure.map (id : Shao.Path n → Shao.Path n) (ProbabilityTheory.cond P N) = PA at hh
    simpa only [Measure.map_id] using hh
  let px : ℝ := P.real N
  have hpx1 : px ≤ 1 := measureReal_le_one
  have hMultiply : PA.real (Shao.C2.doubleCrossing hn x) * px =
      P.real (N ∩ Shao.C2.doubleCrossing hn x) := by
    simpa only [hCond, px, Measure.real_def, ENNReal.toReal_mul] using
      congrArg ENNReal.toReal (cond_mul_eq_inter hNm (Shao.C2.doubleCrossing hn x) P)
  have hSplit := measureReal_inter_add_sdiff (μ := P)
    (s := Shao.C2.doubleCrossing hn x) hNm
  change P.real (Shao.C2.doubleCrossing hn x ∩ N) +
    P.real (Shao.C2.doubleCrossing hn x ∩ Nᶜ) = P.real (Shao.C2.doubleCrossing hn x) at hSplit
  rw [Set.inter_comm (Shao.C2.doubleCrossing hn x) N, ← hMultiply] at hSplit
  have hMarked := (hBad nu n hn h2 hmean hnorm x eps hx0 heps (by norm_num [eps])
    hRcut x (by linarith only [hx]) (by simp; positivity)).1 1 (Or.inl rfl)
  have hBadD : P.real (Shao.C2.doubleCrossing hn x ∩ Nᶜ) ≤
      (Cb / eps ^ 3) * R * Shao.standardNormalTail x := by
    have hsub : Shao.C2.doubleCrossing hn x ∩ Nᶜ ⊆ Shao.upperCrossing hn x ∩ Nᶜ := by
      intro v hv
      exact ⟨hv.1.1, hv.2⟩
    apply (measureReal_mono (μ := P) hsub).trans
    simpa only [P, R, N, a, Shao.upperCrossing, one_smul, mul_assoc] using hMarked
  have hMix : P.real (Shao.C2.doubleCrossing hn x) ≤
      PA.real (Shao.C2.doubleCrossing hn x) + (Cb / eps ^ 3) * R * Shao.standardNormalTail x := by
    have hh := mul_le_of_le_one_right
      (measureReal_nonneg (μ := PA) (s := Shao.C2.doubleCrossing hn x)) hpx1
    linarith only [hh, hSplit, hBadD]
  have hOriginal : P.real (Shao.C2.doubleCrossing hn x) ≤
      A0 * R * Shao.standardNormalTail x +
        (Real.exp 1 * (C0 + 2)) * Real.exp (-4 * x ^ 2) := by
    dsimp only [A0]
    nlinarith only [hMix, hPAPaid]
  have hTwoOriginal : |P.real (Shao.C2.doubleCrossing hn x) - d| ≤
      A0 * R * Shao.standardNormalTail x + B0 * Real.exp (-4 * x ^ 2) := by
    dsimp only [B0]
    nlinarith only [hErr, hOriginal, hdPaid]
  have hGauss : Real.exp (-x ^ 2) ≤ 2 * K * Shao.standardNormalTail x := by
    have hm := (div_le_iff₀ ha).mp (Shao.standardNormal_mills_bounds x hx0).1
    have hd : Shao.standardNormalDensity x = K⁻¹ * Real.exp (-x ^ 2 / 2) := by
      simp [K, Shao.standardNormalDensity, ProbabilityTheory.gaussianPDFReal]
    rw [hd] at hm
    have hm' : Real.exp (-x ^ 2 / 2) ≤ K * (Shao.standardNormalTail x * a) := by
      have hh := mul_le_mul_of_nonneg_left hm hK.le
      simpa only [← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul] using hh
    have hexp : x ≤ Real.exp (x ^ 2 / 2) := by
      nlinarith only [Real.add_one_le_exp (x ^ 2 / 2), sq_nonneg (x - 1)]
    have hweight : a * Real.exp (-x ^ 2 / 2) ≤ 2 := by
      have hh : a ≤ 2 * Real.exp (x ^ 2 / 2) := by dsimp [a]; linarith only [hexp, hx]
      have hp := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-x ^ 2 / 2)).le
      have he : Real.exp (x ^ 2 / 2) * Real.exp (-x ^ 2 / 2) = 1 := by
        rw [← Real.exp_add]
        convert Real.exp_zero using 1 <;> congr 1 <;> ring
      nlinarith only [hp, he]
    calc
      _ = Real.exp (-x ^ 2 / 2) * Real.exp (-x ^ 2 / 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ (K * (Shao.standardNormalTail x * a)) * Real.exp (-x ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right hm' (Real.exp_pos _).le
      _ = (K * Shao.standardNormalTail x) * (a * Real.exp (-x ^ 2 / 2)) := by ring
      _ ≤ (K * Shao.standardNormalTail x) * 2 :=
        mul_le_mul_of_nonneg_left hweight (by positivity)
      _ = _ := by ring
  have hRare : Real.exp (-4 * x ^ 2) ≤ (R / cstar) * Real.exp (-x ^ 2) := by
    have hh := mul_le_mul_of_nonneg_right hnon (Real.exp_pos (-x ^ 2)).le
    have hid : Real.exp (-3 * x ^ 2) * Real.exp (-x ^ 2) = Real.exp (-4 * x ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [mul_assoc, hid] at hh
    have hd := (le_div_iff₀ hcs).mpr (by simpa only [mul_comm] using hh)
    convert hd using 1 <;> ring
  calc
    _ ≤ A0 * R * Shao.standardNormalTail x + B0 * Real.exp (-4 * x ^ 2) := hTwoOriginal
    _ ≤ A0 * R * Shao.standardNormalTail x + B0 * ((R / cstar) * (2 * K * Shao.standardNormalTail x)) := by
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_left
        (hRare.trans (mul_le_mul_of_nonneg_left hGauss (by positivity))) hB0
    _ = Csmall * R * Shao.standardNormalTail x := by dsimp [Csmall]; ring
    _ ≤ C * R * Shao.standardNormalTail x := by gcongr

theorem original_iid_nonresidual_double_crossing_comparison :
    ∀ cstar : ℝ, 0 < cstar → ∃ C : ℝ, 0 < C ∧
      ∀ rhoStar : ℝ, 0 < rhoStar → rhoStar ≤ 1 / 16 →
        ∀ p : ℝ, 2 < p → p ≤ 3 →
          ∀ {Ω ΩB : Type*} [MeasurableSpace Ω] [MeasurableSpace ΩB]
            (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
            IsBrownianReal B PB →
            ∀ (mu : Measure Ω) (rho : Measure ℝ)
              [IsProbabilityMeasure mu] [IsProbabilityMeasure rho]
              (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ),
              (∀ i, AEMeasurable (X i) mu) →
              iIndepFun X mu →
              (∀ i, IdentDistrib (X i) (id : ℝ → ℝ) mu rho) →
              Integrable (fun z : ℝ => z ^ 2) rho →
              (∫ z : ℝ, z ∂rho) = 0 →
              0 < (∫ z : ℝ, z ^ 2 ∂rho) →
              Integrable (fun z : ℝ => Real.rpow |z| p) rho →
              let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂rho
              let sigma : ℝ := Real.sqrt sigmaSq
              let scale : ℝ := sigma * Real.sqrt (n : ℝ)
              let nu : Measure ℝ := Measure.map (fun z : ℝ => z / scale) rho
              let Ln : ℝ := (∫ z : ℝ, Real.rpow |z| p ∂rho) /
                (Real.rpow sigma p * Real.rpow (n : ℝ) ((p - 2) / 2))
              let Rn : ℝ → ℝ := fun t => Shao.truncationBudget nu n t
              let I : Set ℝ := {t | 0 ≤ t ∧
                (t ≤ Real.rpow Ln (-1 / p) ∨ Rn t ≤ rhoStar)}
              let population : Ω → Shao.Path n := Shao.Probability.samplePath X
              let rawEnergy : Ω → ℝ := fun omega => ∑ i : Fin n, (X i omega) ^ 2
              ∀ x : ℝ, 1 ≤ x → x ∈ I →
                cstar * Real.exp (-3 * x ^ 2) ≤ Rn x →
                let D : Set Ω := {omega |
                  x * Real.sqrt (rawEnergy omega) ≤ Shao.upperMax (population omega) hn ∧
                  x * Real.sqrt (rawEnergy omega) ≤ Shao.lowerMax (population omega) hn}
                let DB : Set ΩB := {omega |
                  (∃ t : BridgeTime, x ≤ B ⟨(t : ℝ), t.property.1⟩ omega) ∧
                  ∃ t : BridgeTime, B ⟨(t : ℝ), t.property.1⟩ omega ≤ -x}
                Rn x = (n : ℝ) * (∫ z : ℝ,
                  Shao.truncationF ((1 + x) * z / scale) ∂rho) ∧
                NullMeasurableSet D mu ∧
                Integrable (D.indicator (fun _ : Ω => (1 : ℝ))) mu ∧
                NullMeasurableSet DB PB ∧
                |mu.real D - PB.real DB| ≤ C * Rn x * Shao.standardNormalTail x := by
  classical
  intro cstar hcs
  obtain ⟨C, hC, hCore⟩ := olr_normalized_nonresidual_return cstar hcs
  refine ⟨C, hC, ?_⟩
  intro rhoStar hrho hrho16 p hp2 hp3 Ω ΩB hΩ hΩB B PB hPB hB
    mu rho hmu hRho n hn X hX hIndep hLaw h2 hmean hsecond hp
    sigmaSq sigma scale nu Ln Rn I population rawEnergy x hx hIx hnon D DB
  letI : IsProbabilityMeasure PB := hPB
  letI : IsProbabilityMeasure mu := hmu
  letI : IsProbabilityMeasure rho := hRho
  obtain ⟨hSigma, hNuProb, hNu2, hNuMean, hNorm, hNuP, hNuPEq,
    hLnPos, hLnEq, hNormMap, hSigned⟩ :=
    original_raw_normalization_data p hp2 hp3 rho n hn h2 hmean hsecond hp
  letI : IsProbabilityMeasure nu := hNuProb
  change Ln = (n : ℝ) * (∫ z : ℝ, Real.rpow |z| p ∂nu) at hLnEq
  have hX0 : 0 ≤ x := by linarith only [hx]
  have hN : 0 < (n : ℝ) := by exact_mod_cast hn
  have hScale : 0 < scale := mul_pos hSigma (Real.sqrt_pos.2 hN)
  have hGuards : x ^ 6 ≤ (n : ℝ) ∧
      (n : ℝ) * (∫ z : ℝ, Shao.truncationF (x * z) ∂nu) ≤ 1 := by
    rcases hIx.2 with hMoment | hBudget
    · have hm := (original_moment_domain_coarse_guards p hp2 hp3 nu n hn
        hNu2 hNorm hNuP).2.2.2.2 x hX0
      apply hm
      rw [← hLnEq]
      exact hMoment
    · have hs := Shao.truncationBudget_sample_size_lower nu n hNu2 hNorm
        x rhoStar hX0 hBudget hrho16
      have hmono : (∫ z : ℝ, Shao.truncationF (x * z) ∂nu) ≤
          ∫ z : ℝ, Shao.truncationF ((1 + x) * z) ∂nu :=
        integral_mono (Shao.integrable_truncationF_mul nu hNu2 x)
          (Shao.integrable_truncationF_mul nu hNu2 (1 + x))
          (fun z => Shao.truncationF_mono_scale x (1 + x) z hX0 (by linarith))
      refine ⟨(pow_le_pow_left₀ hX0 (by linarith : x ≤ 1 + x) 6).trans
        (hs.1.trans hs.2), ?_⟩
      have hh := mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      exact hh.trans (hBudget.trans (hrho16.trans (by norm_num)))
  have hCoreBound := hCore B PB hB nu n hn hNu2 hNuMean hNorm x hx
    hGuards.1 hGuards.2 hnon
  let Praw : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
  let Pnorm : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  letI : IsProbabilityMeasure Praw := by dsimp [Praw]; infer_instance
  letI : IsProbabilityMeasure Pnorm := by dsimp [Pnorm]; infer_instance
  have hPop : AEMeasurable population mu := AEMeasurable.of_eval hX
  have hPopMap : Measure.map population mu = Praw := by
    change Measure.map (fun omega i => X i omega) mu = _
    rw [hIndep.map_fun_eq_pi_map hX]
    congr 1
    funext i
    simpa only [Measure.map_id] using (hLaw i).map_eq
  have hPopPair : IdentDistrib population (id : Shao.Path n → Shao.Path n) mu Praw :=
    ⟨hPop, measurable_id.aemeasurable, by simpa only [Measure.map_id] using hPopMap⟩
  let E : Set (Shao.Path n) := Shao.C2.doubleCrossing hn x
  have hEm : MeasurableSet E := Shao.C2.measurableSet_doubleCrossing hn x
  have hPre : population ⁻¹' E = D := by rfl
  have hDn : NullMeasurableSet D mu := by
    rw [← hPre]
    exact hPop.nullMeasurableSet_preimage hEm
  let f : Shao.Path n → ℝ := E.indicator (fun _ => (1 : ℝ))
  have hfm : Measurable f := measurable_const.indicator hEm
  have hfi : Integrable f Praw := (integrable_const (1 : ℝ)).indicator hEm
  have hDI : Integrable (D.indicator (fun _ : Ω => (1 : ℝ))) mu := by
    have hi := (hPopPair.comp hfm).integrable_iff.mpr hfi
    change Integrable (fun omega => f (population omega)) mu at hi
    convert hi using 1
    rfl
  have hDraw : mu.real D = Praw.real E := by
    have hh := congrArg ENNReal.toReal (hPopPair.measure_mem_eq hEm)
    simpa only [Measure.real, hPre, Set.preimage_id] using hh
  let T : Shao.Path n → Shao.Path n := fun a i => a i / scale
  have hTm : Measurable T := by
    dsimp only [T]
    fun_prop
  have hTmap : Measure.map T Praw = Pnorm := hNormMap
  have hc : 0 < scale⁻¹ := inv_pos.2 hScale
  have hTpre : T ⁻¹' E = E := by
    ext a
    have hTa : T a = scale⁻¹ • a := by
      funext i
      change a i / scale = scale⁻¹ * a i
      rw [div_eq_mul_inv, mul_comm]
    change (x * Real.sqrt (Shao.energy (T a)) ≤ Shao.upperMax (T a) hn ∧
      x * Real.sqrt (Shao.energy (T a)) ≤ Shao.lowerMax (T a) hn) ↔
      (x * Real.sqrt (Shao.energy a) ≤ Shao.upperMax a hn ∧
      x * Real.sqrt (Shao.energy a) ≤ Shao.lowerMax a hn)
    rw [hTa, Shao.energy_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc.le,
      Shao.upperMax_smul_of_nonneg _ hc.le, Shao.lowerMax_smul_of_nonneg _ hc.le]
    rw [show x * (scale⁻¹ * Real.sqrt (Shao.energy a)) =
      scale⁻¹ * (x * Real.sqrt (Shao.energy a)) by ring]
    simp only [mul_le_mul_iff_right₀ hc]
  have hNormProb : Pnorm.real E = Praw.real E := by
    rw [← hTmap]
    simp only [Measure.real_def]
    rw [Measure.map_apply hTm hEm, hTpre]
  have hRraw : Rn x = (n : ℝ) * (∫ z : ℝ,
      Shao.truncationF ((1 + x) * z / scale) ∂rho) := by
    change (n : ℝ) * (∫ z : ℝ, Shao.truncationF ((1 + x) * z)
      ∂Measure.map (fun z : ℝ => z / scale) rho) = _
    rw [integral_map (show AEMeasurable (fun z : ℝ => z / scale) rho from by fun_prop)
      (show AEStronglyMeasurable (fun z : ℝ => Shao.truncationF ((1 + x) * z))
        (Measure.map (fun z : ℝ => z / scale) rho) from
        (Shao.continuous_truncationF.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)]
    simp only [div_eq_mul_inv, mul_assoc]
  have hDBn : NullMeasurableSet DB PB :=
    (SourceNonresidualBrownian.actual_brownian_weak_double_crossing B PB hB x
      (by linarith only [hx])).2.2.1
  refine ⟨hRraw, hDn, hDI, hDBn, ?_⟩
  rw [hDraw, ← hNormProb]
  exact hCoreBound

end Shao.Probability.SourceOriginalLawNonresidualReturn
