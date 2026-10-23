import Shao.OQ3.CompactTiltWeakCramer
import Shao.OQ3.RegularCovariance

/-!
# Uniform actual covariance spectra for compact quadratic tilts

Source: current/oq3/proofs/r2/report.md 38-60,74-76,83-92,343-369.
Source SHA256: 572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55.
Frozen scope80: b30cd580532e687dc5bc385a06965281e93ea55cc8160363824c5ed70d655b83.
-/

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix ENNReal NNReal
noncomputable section

private theorem bounded_parabola_memLp (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (M : ℝ) (hb : ∀ᵐ x ∂mu, |x| ≤ M) :
    MemLp (fun x : ℝ => x) 2 mu ∧ MemLp (fun x : ℝ => x ^ 2) 2 mu := by
  have h1 : MemLp (fun x : ℝ => x) 2 mu :=
    MemLp.of_bound continuous_id.aestronglyMeasurable M
      (by simpa only [Real.norm_eq_abs] using hb)
  have h2b : ∀ᵐ x ∂mu, |x ^ 2| ≤ M ^ 2 := hb.mono fun x hx => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hx 2
  exact ⟨h1, MemLp.of_bound (by fun_prop) (M ^ 2)
    (by simpa only [Real.norm_eq_abs] using h2b)⟩

private theorem quadratic_variance_eq (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (h1 : MemLp (fun x : ℝ => x) 2 mu)
    (h2 : MemLp (fun x : ℝ => x ^ 2) 2 mu) (xi eta : ℝ) :
    ProbabilityTheory.variance (fun x : ℝ => xi * x + eta * x ^ 2) mu =
      xi ^ 2 * parabolaCovariance mu 0 0 +
        2 * xi * eta * parabolaCovariance mu 0 1 +
        eta ^ 2 * parabolaCovariance mu 1 1 := by
  change ProbabilityTheory.variance (fun x : ℝ => xi * x + eta * x ^ 2) mu =
    xi ^ 2 * ProbabilityTheory.variance (fun x : ℝ => x) mu +
      2 * xi * eta * ProbabilityTheory.covariance (fun x : ℝ => x)
        (fun x : ℝ => x ^ 2) mu +
      eta ^ 2 * ProbabilityTheory.variance (fun x : ℝ => x ^ 2) mu
  rw [ProbabilityTheory.variance_fun_add (h1.const_mul xi) (h2.const_mul eta),
    ProbabilityTheory.variance_const_mul, ProbabilityTheory.variance_const_mul,
    ProbabilityTheory.covariance_const_mul_left,
    ProbabilityTheory.covariance_const_mul_right]
  ring

private theorem variance_lower_of_measure_lower (mu nu : Measure ℝ)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (f : ℝ → ℝ) (hmu : MemLp f 2 mu) (hnu : MemLp f 2 nu)
    (m : ℝ) (hm : 0 ≤ m) (hdom : ENNReal.ofReal m • mu ≤ nu) :
    m * ProbabilityTheory.variance f mu ≤ ProbabilityTheory.variance f nu := by
  let z : ℝ := ∫ x, f x ∂nu
  have hgmu : MemLp (fun x => f x - z) 2 mu := hmu.sub (memLp_const z)
  have hgnu : MemLp (fun x => f x - z) 2 nu := hnu.sub (memLp_const z)
  have hcenter : ProbabilityTheory.variance f mu ≤ ∫ x, (f x - z) ^ 2 ∂mu := by
    have hv := ProbabilityTheory.variance_eq_sub hgmu
    change ProbabilityTheory.variance (fun x => f x - z) mu =
      (∫ x, (f x - z) ^ 2 ∂mu) - (∫ x, f x - z ∂mu) ^ 2 at hv
    rw [ProbabilityTheory.variance_sub_const hmu.aestronglyMeasurable z] at hv
    linarith only [hv, sq_nonneg (∫ x, f x - z ∂mu)]
  have hmono := integral_mono_measure hdom
    (Filter.Eventually.of_forall fun x : ℝ => sq_nonneg (f x - z)) hgnu.integrable_sq
  rw [integral_smul_measure, ENNReal.toReal_ofReal hm, smul_eq_mul] at hmono
  rw [ProbabilityTheory.variance_eq_integral hnu.aemeasurable]
  exact (mul_le_mul_of_nonneg_left hcenter hm).trans hmono

private theorem quadratic_variance_upper (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ᵐ x ∂mu, |x| ≤ M)
    (xi eta : ℝ) :
    ProbabilityTheory.variance (fun x : ℝ => xi * x + eta * x ^ 2) mu ≤
      (M ^ 2 + M ^ 4) * (xi ^ 2 + eta ^ 2) := by
  obtain ⟨h1, h2⟩ := bounded_parabola_memLp mu M hb
  have hf : MemLp (fun x : ℝ => xi * x + eta * x ^ 2) 2 mu :=
    (h1.const_mul xi).add (h2.const_mul eta)
  have hbound : ∀ᵐ x ∂mu, (xi * x + eta * x ^ 2) ^ 2 ≤
      (M ^ 2 + M ^ 4) * (xi ^ 2 + eta ^ 2) := hb.mono fun x hx => by
    have hx2 : x ^ 2 ≤ M ^ 2 := by
      have hh := pow_le_pow_left₀ (abs_nonneg x) hx 2
      simpa only [sq_abs] using hh
    have hx4 : x ^ 4 ≤ M ^ 4 := by
      have hh := pow_le_pow_left₀ (sq_nonneg x) hx2 2
      simpa only [← pow_mul] using hh
    have hcs : (xi * x + eta * x ^ 2) ^ 2 ≤
        (xi ^ 2 + eta ^ 2) * (x ^ 2 + x ^ 4) := by
      nlinarith only [sq_nonneg (xi * x ^ 2 - eta * x)]
    have hprod := mul_le_mul_of_nonneg_left (add_le_add hx2 hx4)
      (add_nonneg (sq_nonneg xi) (sq_nonneg eta))
    exact hcs.trans (by simpa only [mul_comm] using hprod)
  have hint := integral_mono_ae hf.integrable_sq
    (integrable_const ((M ^ 2 + M ^ 4) * (xi ^ 2 + eta ^ 2))) hbound
  have hmoment : (∫ x, (xi * x + eta * x ^ 2) ^ 2 ∂mu) ≤
      (M ^ 2 + M ^ 4) * (xi ^ 2 + eta ^ 2) := by simpa using hint
  have hv := ProbabilityTheory.variance_eq_sub hf
  change ProbabilityTheory.variance (fun x : ℝ => xi * x + eta * x ^ 2) mu =
    (∫ x, (xi * x + eta * x ^ 2) ^ 2 ∂mu) -
      (∫ x, xi * x + eta * x ^ 2 ∂mu) ^ 2 at hv
  linarith only [hv, hmoment, sq_nonneg (∫ x, xi * x + eta * x ^ 2 ∂mu)]

theorem parabolaCovariance_pos_of_weakCramer
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ᵐ x ∂mu, |x| ≤ M)
    (beta c R : ℝ) (hc : 0 < c)
    (hWC : ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic mu xi eta‖ ≤
        1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) :
    0 < parabolaCovariance mu 0 0 ∧
      0 < parabolaCovariance mu 1 1 ∧
      0 < (parabolaCovariance mu).det ∧
      ∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 →
        0 < xi ^ 2 * parabolaCovariance mu 0 0 +
          2 * xi * eta * parabolaCovariance mu 0 1 +
          eta ^ 2 * parabolaCovariance mu 1 1 := by
  obtain ⟨h1, h2⟩ := bounded_parabola_memLp mu M hb
  have hpos (xi eta : ℝ) (hne : xi ≠ 0 ∨ eta ≠ 0) :
      0 < xi ^ 2 * parabolaCovariance mu 0 0 +
        2 * xi * eta * parabolaCovariance mu 0 1 +
        eta ^ 2 * parabolaCovariance mu 1 1 := by
    let f : ℝ → ℝ := fun x => xi * x + eta * x ^ 2
    have hf : MemLp f 2 mu := (h1.const_mul xi).add (h2.const_mul eta)
    have hvpos : 0 < ProbabilityTheory.variance f mu := by
      by_contra hn
      have hvzero : ProbabilityTheory.variance f mu = 0 :=
        le_antisymm (not_lt.mp hn) (ProbabilityTheory.variance_nonneg f mu)
      have hconstant := ProbabilityTheory.ae_eq_integral_of_variance_eq_zero hf hvzero
      let rho : ℝ := Real.sqrt (xi ^ 2 + eta ^ 2)
      have hrho : 0 < rho := Real.sqrt_pos.2 (by
        rcases hne with hx | hy
        · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg eta)
        · exact add_pos_of_nonneg_of_pos (sq_nonneg xi) (sq_pos_of_ne_zero hy))
      let T : ℝ := (|R| + 1) / rho
      have hT : 0 < T := div_pos (by positivity) hrho
      have hscale : Real.sqrt ((T * xi) ^ 2 + (T * eta) ^ 2) = T * rho := by
        calc
          _ = Real.sqrt (T ^ 2 * (xi ^ 2 + eta ^ 2)) := congrArg Real.sqrt (by ring)
          _ = T * rho := by rw [Real.sqrt_mul (sq_nonneg T), Real.sqrt_sq hT.le]
      have hradius : Real.sqrt ((T * xi) ^ 2 + (T * eta) ^ 2) = |R| + 1 := by
        rw [hscale]
        exact div_mul_cancel₀ _ (ne_of_gt hrho)
      have hphase : ∀ᵐ x ∂mu, jointPhase (T * xi) (T * eta) x =
          Complex.exp (((T * (∫ y, f y ∂mu) : ℝ) : ℂ) * Complex.I) := by
        filter_upwards [hconstant] with x hx
        unfold jointPhase
        rw [show T * xi * x + T * eta * x ^ 2 = T * f x by dsimp [f]; ring, hx]
      have hchar : jointCharacteristic mu (T * xi) (T * eta) =
          Complex.exp (((T * (∫ y, f y ∂mu) : ℝ) : ℂ) * Complex.I) := by
        unfold jointCharacteristic
        calc
          _ = ∫ _ : ℝ,
              Complex.exp (((T * (∫ y, f y ∂mu) : ℝ) : ℂ) * Complex.I) ∂mu :=
            integral_congr_ae hphase
          _ = _ := by simp
      have hnorm : ‖jointCharacteristic mu (T * xi) (T * eta)‖ = 1 := by
        rw [hchar]
        exact Complex.norm_exp_ofReal_mul_I _
      have hfreq : R < Real.sqrt ((T * xi) ^ 2 + (T * eta) ^ 2) := by
        rw [hradius]
        linarith only [le_abs_self R]
      have hp : 0 < c * Real.rpow
          (Real.sqrt ((T * xi) ^ 2 + (T * eta) ^ 2)) (-beta) :=
        mul_pos hc (Real.rpow_pos_of_pos (by rw [hradius]; positivity) _)
      have hw := hWC (T * xi) (T * eta) hfreq
      rw [hnorm] at hw
      linarith only [hw, hp]
    simpa only [f, quadratic_variance_eq mu h1 h2 xi eta] using hvpos
  let a : ℝ := parabolaCovariance mu 0 0
  let b : ℝ := parabolaCovariance mu 0 1
  let d : ℝ := parabolaCovariance mu 1 1
  have ha : 0 < a := by simpa [a] using hpos 1 0 (Or.inl one_ne_zero)
  have hd : 0 < d := by simpa [d] using hpos 0 1 (Or.inr one_ne_zero)
  have hp := hpos (-b) a (Or.inr (ne_of_gt ha))
  change 0 < (-b) ^ 2 * a + 2 * (-b) * a * b + a ^ 2 * d at hp
  have hprod : 0 < a * (a * d - b ^ 2) := by nlinarith only [hp]
  have hdet : 0 < a * d - b ^ 2 := by
    rcases mul_pos_iff.mp hprod with ⟨_, hh⟩ | ⟨hh, _⟩
    · exact hh
    · linarith only [ha, hh]
  refine ⟨ha, hd, ?_, hpos⟩
  rw [Matrix.det_fin_two, show parabolaCovariance mu 1 0 = parabolaCovariance mu 0 1 from rfl]
  change 0 < a * d - b * b
  nlinarith only [hdet]

theorem exists_compact_tilted_covariance_spectral_bounds
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ᵐ x ∂mu, |x| ≤ M)
    (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (u0 v0 beta c R : ℝ) (hc : 0 < c)
    (hWC : ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic (mu.tilted (fun x => u0 * x + v0 * x ^ 2)) xi eta‖ ≤
        1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) :
    let mu0 : Measure ℝ := mu.tilted (fun x => u0 * x + v0 * x ^ 2)
    let D0 : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance mu0
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧
      let lambdaMin : ℝ := m * D0.det / (D0 0 0 + D0 1 1)
      let lambdaMax : ℝ := 2 * (M ^ 2 + M ^ 4) + 1 + lambdaMin
      0 < lambdaMin ∧ lambdaMin < lambdaMax ∧ 0 < m ^ 2 * c / 2 ∧
        ∀ p ∈ K,
          let mup : Measure ℝ := mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
          IsProbabilityMeasure mup ∧ (∀ᵐ x ∂mup, |x| ≤ M) ∧
            MemLp (fun x : ℝ => x) 2 mup ∧
            MemLp (fun x : ℝ => x ^ 2) 2 mup ∧
            (ENNReal.ofReal m • mu0 ≤ mup) ∧
            (∀ xi eta : ℝ,
              lambdaMin * (xi ^ 2 + eta ^ 2) ≤
                  xi ^ 2 * parabolaCovariance mup 0 0 +
                    2 * xi * eta * parabolaCovariance mup 0 1 +
                    eta ^ 2 * parabolaCovariance mup 1 1 ∧
                xi ^ 2 * parabolaCovariance mup 0 0 +
                    2 * xi * eta * parabolaCovariance mup 0 1 +
                    eta ^ 2 * parabolaCovariance mup 1 1 ≤
                  lambdaMax * (xi ^ 2 + eta ^ 2)) ∧
            ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
              ‖jointCharacteristic mup xi eta‖ ≤
                1 - (m ^ 2 * c / 2) *
                  Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta) := by
  let mu0 : Measure ℝ := mu.tilted (fun x => u0 * x + v0 * x ^ 2)
  let D0 : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance mu0
  letI : IsProbabilityMeasure mu0 := isProbabilityMeasure_tilted
    (quadratic_exp_integrable_of_ae_abs_le mu M hM hb u0 v0)
  have hb0 : ∀ᵐ x ∂mu0, |x| ≤ M :=
    (tilted_absolutelyContinuous mu (fun x => u0 * x + v0 * x ^ 2)).ae_le hb
  obtain ⟨h01, h02⟩ := bounded_parabola_memLp mu0 M hb0
  obtain ⟨ha, hd, hdet, _hpositive⟩ :=
    parabolaCovariance_pos_of_weakCramer mu0 M hM hb0 beta c R hc hWC
  have htrace : 0 < D0 0 0 + D0 1 1 := add_pos ha hd
  have hdetformula : D0.det = D0 0 0 * D0 1 1 - (D0 0 1) ^ 2 := by
    rw [Matrix.det_fin_two, show D0 1 0 = D0 0 1 from rfl]
    ring
  obtain ⟨m, hm, hm1, hnewc, hfamily⟩ :=
    exists_compact_tilted_weakCramer_bound mu M hM hb K hK u0 v0 beta c R hc hWC
  let lo : ℝ := m * D0.det / (D0 0 0 + D0 1 1)
  let B : ℝ := M ^ 2 + M ^ 4
  let hi : ℝ := 2 * B + 1 + lo
  have hlo : 0 < lo := div_pos (mul_pos hm hdet) htrace
  have hB : 0 ≤ B := add_nonneg (sq_nonneg M) (by positivity)
  have hhi : lo < hi := by dsimp [hi]; linarith only [hB]
  refine ⟨m, hm, hm1, hlo, hhi, hnewc, ?_⟩
  intro p hp
  let mup : Measure ℝ := mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
  letI : IsProbabilityMeasure mup := isProbabilityMeasure_tilted
    (quadratic_exp_integrable_of_ae_abs_le mu M hM hb p.1 p.2)
  have hbp : ∀ᵐ x ∂mup, |x| ≤ M :=
    (tilted_absolutelyContinuous mu (fun x => p.1 * x + p.2 * x ^ 2)).ae_le hb
  obtain ⟨h1, h2⟩ := bounded_parabola_memLp mup M hbp
  obtain ⟨hdom, _hgap, hwc⟩ := hfamily p hp
  refine ⟨inferInstance, hbp, h1, h2, hdom, ?_, hwc⟩
  intro xi eta
  let rr : ℝ := xi ^ 2 + eta ^ 2
  let q0 : ℝ := xi ^ 2 * D0 0 0 + 2 * xi * eta * D0 0 1 + eta ^ 2 * D0 1 1
  let qp : ℝ := xi ^ 2 * parabolaCovariance mup 0 0 +
    2 * xi * eta * parabolaCovariance mup 0 1 + eta ^ 2 * parabolaCovariance mup 1 1
  have hrr : 0 ≤ rr := add_nonneg (sq_nonneg xi) (sq_nonneg eta)
  have hidentity : (D0 0 0 + D0 1 1) * q0 - D0.det * rr =
      (D0 0 0 * xi + D0 0 1 * eta) ^ 2 +
        (D0 0 1 * xi + D0 1 1 * eta) ^ 2 := by
    rw [hdetformula]
    dsimp [q0, rr]
    ring
  have hbase : (D0.det / (D0 0 0 + D0 1 1)) * rr ≤ q0 := by
    calc
      _ = (D0.det * rr) / (D0 0 0 + D0 1 1) := by ring
      _ ≤ q0 := (div_le_iff₀ htrace).2 (by
        linarith only [hidentity, sq_nonneg (D0 0 0 * xi + D0 0 1 * eta),
          sq_nonneg (D0 0 1 * xi + D0 1 1 * eta)])
  have hf0 : MemLp (fun x : ℝ => xi * x + eta * x ^ 2) 2 mu0 :=
    (h01.const_mul xi).add (h02.const_mul eta)
  have hfp : MemLp (fun x : ℝ => xi * x + eta * x ^ 2) 2 mup :=
    (h1.const_mul xi).add (h2.const_mul eta)
  have hvar := variance_lower_of_measure_lower mu0 mup _ hf0 hfp m hm.le hdom
  rw [quadratic_variance_eq mu0 h01 h02 xi eta,
    quadratic_variance_eq mup h1 h2 xi eta] at hvar
  change m * q0 ≤ qp at hvar
  change lo * rr ≤ qp ∧ qp ≤ hi * rr
  constructor
  · calc
      lo * rr = m * ((D0.det / (D0 0 0 + D0 1 1)) * rr) := by dsimp [lo]; ring
      _ ≤ m * q0 := mul_le_mul_of_nonneg_left hbase hm.le
      _ ≤ qp := hvar
  · have hu := quadratic_variance_upper mup M hM hbp xi eta
    rw [quadratic_variance_eq mup h1 h2 xi eta] at hu
    change qp ≤ B * rr at hu
    have hBhi : B ≤ hi := by dsimp [hi]; linarith only [hB, hlo]
    exact hu.trans (mul_le_mul_of_nonneg_right hBhi hrr)

end
end Shao.OQ3
