/-
Actual source P0: all-start killed Brownian spectrum and terminal remainder.
Classical attribution: C:/game/shao/current/oq4/b01/proof01.md316–343.
This implements the finite-spectrum alternative, not a supplied killed-heat semigroup.
Parent route: brownian-terminal-spectral-next-math-notes-v1.md; author149 rederivation.
Exact frozen heads/values/imports: frozen-brownian-terminal-spectral-formal-v1.
LOCAL UNCHECKED implementation; upstream139/143/145 qualification remains pending.
-/
import Shao.OQ4.BrownianKilledCosineIdentity
import Shao.OQ4.RademacherSpectralPairing
import Shao.OQ4.RademacherScalarBounds
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option autoImplicit false
noncomputable section
namespace Shao.OQ4.BrownianTerminalSpectral
open MeasureTheory ProbabilityTheory Filter Set
open RademacherFiniteBasis
open RademacherScalarBounds (H lambda C_rho)
open RademacherSpectralPairing (alpha beta lowerModes reflect)
open scoped BigOperators NNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω]

-- Public literal values: the actual Brownian probability appears in the remainder.
def spectralTerm (T : ℝ≥0) (u : ℝ) (ell : ℕ) : ℝ :=
  (4 * (-1 : ℝ) ^ ell / (Real.pi * ((2 * ell + 1 : ℕ) : ℝ))) *
    Real.exp (-lambda * ((2 * ell + 1 : ℕ) : ℝ) ^ 2 * (T : ℝ)) *
    Real.cos (((2 * ell + 1 : ℕ) : ℝ) * Real.pi * u / 2)

def spectralSeries (T : ℝ≥0) (u : ℝ) : ℝ :=
  ∑' ell : ℕ, spectralTerm T u ell

def remainderC : ℝ :=
  4 / (3 * Real.pi * (1 - Real.exp (-2 * Real.pi ^ 2)))

def terminalRemainder (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (T : ℝ≥0) (u : ℝ) : ℝ :=
  P.real (BrownianSurvivalBoundary.closedSurvival B T u) -
    (4 / Real.pi) * Real.exp (-lambda * (T : ℝ)) * Real.cos (Real.pi * u / 2)

-- Private literal values. Same scale/clamp as 145, whose private constants are inaccessible.
private def stripRadius (m : ℕ) : ℝ≥0 :=
  (m : ℝ≥0) / ((m : ℝ≥0) + 1)

private def latticeStart (m : ℕ) (u : ℝ) : ℤ :=
  max (-(m : ℤ)) (min (m : ℤ) ⌊H m * u⌋)

private def rowLength (T : ℝ≥0) (m : ℕ) : ℕ :=
  ⌈(T : ℝ) * H m ^ 2⌉₊

private def rawStartTerm (m n : ℕ) (r : ℤ) (ell : ℕ) : ℝ :=
  (1 / H m) * (-1 : ℝ) ^ ell * RademacherFiniteS1.cotangent (alpha m ell) *
    Real.cos (beta m ell) ^ n * Real.cos (beta m ell * (r : ℝ))

private def lowTerm (T : ℝ≥0) (u : ℝ) (j ell : ℕ) : ℝ :=
  if ell ∈ lowerModes (j + 1) then
    rawStartTerm (j + 1)
      (PolygonalKilledFunctionalLimit.floorHorizon T (H (j + 1)))
      (latticeStart (j + 1) u) ell
  else 0

private def majorant (T : ℝ≥0) (ell : ℕ) : ℝ :=
  (4 / Real.pi) *
    Real.exp (-lambda * (T : ℝ) / 2 * ((2 * ell + 1 : ℕ) : ℝ))

-- Finite all-start algebra: even COEFFICIENTS, rather than zero-start vectors, vanish.
private theorem survivalCoefficient_even_zero (m k : ℕ) :
    RademacherAllModes.survivalCoefficient m (2 * k) = 0 := by
  classical
  have hv (s : ℤ) : vector m (2 * k) (-s) = -vector m (2 * k) s := by
    let v : ℝ := (k : ℝ) * Real.pi * (s : ℝ) / H m
    have hp : theta m (2 * k) * ((s : ℝ) + ((m : ℝ) + 1)) =
        (k : ℝ) * Real.pi + v := by
      dsimp [theta, RademacherCosine.angle, v, H]
      push_cast
      field_simp
      <;> ring
    have hn : theta m (2 * k) * (-(s : ℝ) + ((m : ℝ) + 1)) =
        (k : ℝ) * Real.pi - v := by
      dsimp [theta, RademacherCosine.angle, v, H]
      push_cast
      field_simp
      <;> ring
    unfold vector phi
    push_cast
    rw [hp, hn, Real.sin_add, Real.sin_sub, Real.sin_nat_mul_pi]
    ring
  have hs : (∑ s ∈ states m, vector m (2 * k) s) =
      ∑ s ∈ states m, vector m (2 * k) (-s) := by
    refine Finset.sum_bij (fun s _ => -s) ?_ ?_ ?_ ?_
    · intro s hs
      simp only [states, Finset.mem_Icc] at hs ⊢
      omega
    · intro s hs t ht he
      omega
    · intro t ht
      refine ⟨-t, ?_, by simp⟩
      simp only [states, Finset.mem_Icc] at ht ⊢
      omega
    · intro s hs
      simp
  simp_rw [hv] at hs
  rw [Finset.sum_neg_distrib] at hs
  rw [RademacherAllModes.survivalCoefficient_eq]
  have hz : (∑ s ∈ states m, vector m (2 * k) s) = 0 := by linarith
  rw [hz, mul_zero]

private theorem vector_odd_start (m ell : ℕ) (r : ℤ) :
    vector m (2 * ell + 1) r =
      (-1 : ℝ) ^ ell * Real.cos (beta m ell * (r : ℝ)) := by
  have ha : theta m (2 * ell + 1) * ((r : ℝ) + ((m : ℝ) + 1)) =
      (ell : ℝ) * Real.pi + (beta m ell * (r : ℝ) + Real.pi / 2) := by
    dsimp [theta, RademacherCosine.angle, beta]
    push_cast
    field_simp
    <;> ring
  unfold vector phi
  rw [ha, Real.sin_add, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi,
    Real.sin_add_pi_div_two]
  ring

private theorem killedMass_odd_start (m : ℕ) (hm : 1 ≤ m) (n : ℕ)
    (r : ℤ) (hr : r ∈ states m) :
    killedMass RademacherCosine.law (m : ℝ) n (r : ℝ) =
      ∑ ell ∈ Finset.range (m + 1), rawStartTerm m n r ell := by
  classical
  let F : ℕ → ℝ := fun j =>
    RademacherAllModes.survivalCoefficient m j * mu m j ^ n * vector m j r
  have hs : (∑ j ∈ modes m, F j) =
      ∑ ell ∈ Finset.range (m + 1), F (2 * ell + 1) := by
    let odds := (Finset.range (m + 1)).image (fun ell => 2 * ell + 1)
    have hsub : odds ⊆ modes m := by
      intro j hj
      obtain ⟨ell, hell, rfl⟩ := Finset.mem_image.mp hj
      exact (RademacherFiniteS1.odd_mode_mem_iff m ell).2 hell
    calc
      _ = ∑ j ∈ odds, F j := by
        symm
        apply Finset.sum_subset hsub
        intro j hj hjnot
        rcases RademacherFiniteS1.mode_parity_partition m j hj with
          ⟨k, hk, rfl⟩ | ⟨ell, hell, rfl⟩
        · dsimp [F]
          rw [survivalCoefficient_even_zero]
          ring
        · exact False.elim (hjnot (Finset.mem_image.mpr ⟨ell, hell, rfl⟩))
      _ = _ := by
        dsimp [odds]
        apply Finset.sum_image
        intro a ha b hb hab
        exact RademacherFiniteS1.odd_mode_injective hab
  rw [RademacherAllModes.killedMass_spectrum m hm (m : ℝ) le_rfl
    (by linarith) r hr n]
  change (∑ j ∈ modes m, F j) = _
  rw [hs]
  apply Finset.sum_congr rfl
  intro ell hell
  dsimp [F]
  rw [RademacherFiniteS1.survivalCoefficient_odd m hm ell hell, vector_odd_start]
  have hmu : mu m (2 * ell + 1) = Real.cos (beta m ell) := by
    unfold mu
    congr 1
    unfold theta RademacherCosine.angle beta
    ring
  rw [hmu]
  change (1 / H m) * RademacherFiniteS1.cotangent (alpha m ell) *
    Real.cos (beta m ell) ^ n *
      ((-1 : ℝ) ^ ell * Real.cos (beta m ell * (r : ℝ))) = _
  unfold rawStartTerm
  ring

private theorem finite_mass_split (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (hn : 1 ≤ n)
    (r : ℤ) (hr : r ∈ states m) :
    killedMass RademacherCosine.law (m : ℝ) n (r : ℝ) =
      (∑ ell ∈ lowerModes m, rawStartTerm m n r ell) +
        ∑ ell ∈ lowerModes m, rawStartTerm m n r (reflect m ell) := by
  rw [killedMass_odd_start m hm n r hr,
    RademacherSpectralPairing.sum_reflection_partition]
  rw [Finset.sum_add_distrib]
  by_cases he : Even m
  · have hc : rawStartTerm m n r (m / 2) = 0 := by
      unfold rawStartTerm
      rw [RademacherSpectralPairing.beta_center he, Real.cos_pi_div_two,
        zero_pow (by omega : n ≠ 0)]
      ring
    simp only [he, if_true, hc, add_zero]
  · simp only [he, if_false, add_zero]

-- Actual finite-product attachment and the given-model Brownian limit.
private theorem latticeStart_bounds (m : ℕ) (u : ℝ) :
    -(m : ℤ) ≤ latticeStart m u ∧ latticeStart m u ≤ (m : ℤ) := by
  unfold latticeStart
  constructor
  · exact le_max_left _ _
  · exact max_le_iff.mpr ⟨by omega, min_le_left _ _⟩


private theorem scaledStart_error (m : ℕ) (hm : 1 ≤ m)
    (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    |(latticeStart m u : ℝ) / H m - u| ≤ 1 / H m := by
  have hH : 0 < H m := RademacherScalarBounds.H_pos hm
  let p : ℤ := ⌊H m * u⌋
  have hp0 : (p : ℝ) ≤ H m * u := Int.floor_le _
  have hp1 : H m * u < (p : ℝ) + 1 := Int.lt_floor_add_one _
  have hxlo : -H m ≤ H m * u := by
    simpa using mul_le_mul_of_nonneg_left hu.1 hH.le
  have hxhi : H m * u ≤ H m := by
    simpa using mul_le_mul_of_nonneg_left hu.2 hH.le
  have hraw : |(latticeStart m u : ℝ) - H m * u| ≤ 1 := by
    by_cases hlo : p < -(m : ℤ)
    · have hpm : p ≤ (m : ℤ) := by omega
      have hr : latticeStart m u = -(m : ℤ) := by
        change max (-(m : ℤ)) (min (m : ℤ) p) = -(m : ℤ)
        rw [min_eq_right hpm, max_eq_left hlo.le]
      have hpupper : (p : ℝ) + 1 ≤ -(m : ℝ) := by
        exact_mod_cast (show p + 1 ≤ -(m : ℤ) by omega)
      rw [hr]
      push_cast
      apply abs_le.mpr
      dsimp [H] at hxlo hxhi hp0 hp1 ⊢
      constructor <;> linarith
    · have hplo : -(m : ℤ) ≤ p := le_of_not_gt hlo
      by_cases hhi : (m : ℤ) < p
      · have hr : latticeStart m u = (m : ℤ) := by
          change max (-(m : ℤ)) (min (m : ℤ) p) = (m : ℤ)
          rw [min_eq_left hhi.le, max_eq_right (by omega)]
        have hplower : (m : ℝ) + 1 ≤ (p : ℝ) := by
          exact_mod_cast (show (m : ℤ) + 1 ≤ p by omega)
        rw [hr]
        push_cast
        apply abs_le.mpr
        dsimp [H] at hxlo hxhi hp0 hp1 ⊢
        constructor <;> linarith
      · have hphi : p ≤ (m : ℤ) := le_of_not_gt hhi
        have hr : latticeStart m u = p := by
          change max (-(m : ℤ)) (min (m : ℤ) p) = p
          rw [min_eq_right hphi, max_eq_right hplo]
        rw [hr]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    |(latticeStart m u : ℝ) / H m - u| =
        |((latticeStart m u : ℝ) - H m * u) / H m| := by
      congr 1
      field_simp [hH.ne'] <;> ring
    _ = |(latticeStart m u : ℝ) - H m * u| / H m := by
      rw [abs_div, abs_of_pos hH]
    _ ≤ 1 / H m := div_le_div_of_nonneg_right hraw hH.le


private theorem scale_tendsto :
    Tendsto (fun j : ℕ => H (j + 1)) atTop atTop := by
  apply tendsto_atTop_mono (fun j : ℕ => ?_)
    (tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop)
  simp only [H, Nat.cast_add, Nat.cast_one]
  linarith


private theorem radius_tendsto :
    Tendsto (fun j : ℕ => stripRadius (j + 1)) atTop (𝓝 (1 : ℝ≥0)) := by
  apply NNReal.tendsto_coe.1
  have hi : Tendsto (fun j : ℕ => 1 / H (j + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp scale_tendsto
  have heq (j : ℕ) : (stripRadius (j + 1) : ℝ) = 1 - 1 / H (j + 1) := by
    change ((j + 1 : ℕ) : ℝ) / (((j + 1 : ℕ) : ℝ) + 1) =
      1 - 1 / H (j + 1)
    dsimp [H]
    field_simp [show (((j + 1 : ℕ) : ℝ) + 1) ≠ 0 by positivity] <;> ring
  simp_rw [heq]
  simpa only [sub_zero, NNReal.coe_one] using
    (tendsto_const_nhds.sub hi :
      Tendsto (fun j : ℕ => (1 : ℝ) - 1 / H (j + 1)) atTop (𝓝 (1 - 0)))


private theorem start_tendsto (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun j : ℕ => (latticeStart (j + 1) u : ℝ) / H (j + 1))
      atTop (𝓝 u) := by
  have hi : Tendsto (fun j : ℕ => 1 / H (j + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp scale_tendsto
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _))
    (Eventually.of_forall (fun j => scaledStart_error (j + 1) (by omega) u hu)) hi


private theorem rowLength_horizon (T : ℝ≥0) (m : ℕ) :
    (T : ℝ) * H m ^ 2 ≤ (rowLength T m : ℝ) := by
  exact Nat.le_ceil _


private theorem rademacher_moments :
    Integrable (fun x : ℝ => |x| ^ 3) RademacherCosine.law ∧
      (∫ x : ℝ, x ∂RademacherCosine.law) = 0 ∧
      (∫ x : ℝ, x ^ 2 ∂RademacherCosine.law) = 1 ∧
      (∫ x : ℝ, |x| ^ 3 ∂RademacherCosine.law) = 1 := by
  have hhalf : RademacherCosine.halfENNReal ≠ ⊤ := by
    norm_num [RademacherCosine.halfENNReal]
  have hreal : RademacherCosine.halfENNReal.toReal = (1 / 2 : ℝ) := by
    norm_num [RademacherCosine.halfENNReal, ENNReal.toReal_div]
  have hp (f : ℝ → ℝ) :
      Integrable f (RademacherCosine.halfENNReal • Measure.dirac (1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure hhalf
  have hn (f : ℝ → ℝ) :
      Integrable f (RademacherCosine.halfENNReal • Measure.dirac (-1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure hhalf
  have hi (f : ℝ → ℝ) : Integrable f RademacherCosine.law := by
    rw [RademacherCosine.law]
    exact (hp f).add_measure (hn f)
  have hformula (f : ℝ → ℝ) :
      (∫ x : ℝ, f x ∂RademacherCosine.law) =
        (1 / 2 : ℝ) * f 1 + (1 / 2 : ℝ) * f (-1) := by
    rw [RademacherCosine.law, integral_add_measure (hp f) (hn f),
      integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac, hreal]
    rfl
  refine ⟨hi _, ?_, ?_, ?_⟩
  · norm_num [hformula]
  · norm_num [hformula]
  · norm_num [hformula]


private theorem discrete_row_mass (T : ℝ≥0) (m : ℕ) (hm : 1 ≤ m) (r : ℤ)
    (hr : r ∈ states m) :
    (Measure.pi (fun _ : Fin (rowLength T m) => RademacherCosine.law)).real
      (PolygonalKilledFunctionalLimit.discreteClosedSurvival (rowLength T m)
        (PolygonalKilledFunctionalLimit.floorHorizon T (H m))
        (H m) ((r : ℝ) / H m) (stripRadius m)) =
      killedMass RademacherCosine.law (m : ℝ)
        (PolygonalKilledFunctionalLimit.floorHorizon T (H m)) (r : ℝ) := by
  have hH := RademacherScalarBounds.H_pos hm
  have hl := PolygonalKilledFunctionalLimit.floorHorizon_le T (H m)
    (rowLength T m) (rowLength_horizon T m)
  have hrad : (stripRadius m : ℝ) * H m = (m : ℝ) := by
    change ((m : ℝ) / ((m : ℝ) + 1)) * ((m : ℝ) + 1) = (m : ℝ)
    field_simp
  have habs' : |(r : ℝ)| ≤ (stripRadius m : ℝ) * H m := by
    rw [hrad]
    have hr' := Finset.mem_Icc.mp hr
    exact abs_le.mpr ⟨by exact_mod_cast hr'.1, by exact_mod_cast hr'.2⟩
  have ht := BrownianKilledCosineIdentity.discrete_killed_test_integral
    RademacherCosine.law (rowLength T m)
    (PolygonalKilledFunctionalLimit.floorHorizon T (H m)) hl
    (H m) hH (stripRadius m) (r : ℝ) habs'
    (fun _ : ℝ => (1 : ℝ)) measurable_const ⟨1, by intro w; norm_num⟩
  have hprob : (∫ a : Shao.Path (rowLength T m),
      (PolygonalKilledFunctionalLimit.discreteClosedSurvival (rowLength T m)
        (PolygonalKilledFunctionalLimit.floorHorizon T (H m))
        (H m) ((r : ℝ) / H m) (stripRadius m)).indicator
          (fun _ => (1 : ℝ)) a
        ∂Measure.pi (fun _ : Fin (rowLength T m) => RademacherCosine.law)) =
      (Measure.pi (fun _ : Fin (rowLength T m) => RademacherCosine.law)).real
        (PolygonalKilledFunctionalLimit.discreteClosedSurvival (rowLength T m)
          (PolygonalKilledFunctionalLimit.floorHorizon T (H m))
          (H m) ((r : ℝ) / H m) (stripRadius m)) := by
    rw [integral_indicator
      (PolygonalKilledFunctionalLimit.measurableSet_discreteClosedSurvival _ _ _ _ _)]
    simp
  rw [← hprob]
  simpa only [hrad, killedMass] using ht.2.2

private theorem finite_mass_tendsto_brownian
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) (hT : 0 < T)
    (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun j : ℕ => killedMass RademacherCosine.law (j + 1 : ℝ)
      (PolygonalKilledFunctionalLimit.floorHorizon T (H (j + 1)))
      (latticeStart (j + 1) u : ℝ)) atTop
      (𝓝 (P.real (BrownianSurvivalBoundary.closedSurvival B T u))) := by
  rcases rademacher_moments with ⟨h3, hmean, hsecond, hthird⟩
  have ht := PolygonalKilledFunctionalLimit.discrete_survival_tendsto_brownian
    B P hB T hT (fun j => rowLength T (j + 1)) (fun j => H (j + 1))
    (fun _ => RademacherCosine.law) (fun _ => inferInstance)
    (fun j => RademacherScalarBounds.H_pos (by omega))
    (fun j => rowLength_horizon T (j + 1))
    (fun _ => h3) (fun _ => hmean) (fun _ => hsecond) 1
    (fun _ => hthird.le) scale_tendsto (fun j => stripRadius (j + 1))
    radius_tendsto (fun j => (latticeStart (j + 1) u : ℝ) / H (j + 1)) u
    (start_tendsto u hu) hu
  convert ht using 1
  funext j
  have hr : latticeStart (j + 1) u ∈ states (j + 1) :=
    Finset.mem_Icc.mpr (latticeStart_bounds _ _)
  simpa only [Nat.cast_add, Nat.cast_one] using
    (discrete_row_mass T (j + 1) (by omega) _ hr).symm

-- Scalar estimates are proved here from derivatives, not imported private facts.
private theorem tan_lower (x : ℝ) (hx : 0 ≤ x) (hxpi : x < Real.pi / 2) :
    x ≤ Real.tan x := by
  have hc (t : ℝ) (ht : t ∈ Icc (0 : ℝ) x) : 0 < Real.cos t := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [ht.1, ht.2, Real.pi_pos]
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) x) :
      HasDerivAt (fun s : ℝ => Real.tan s - s) (Real.tan t ^ 2) t := by
    convert (Real.hasDerivAt_tan (hc t ht).ne').fun_sub (hasDerivAt_id t) using 1
    · rfl
    · rw [Real.tan_eq_sin_div_cos]
      field_simp [(hc t ht).ne']
      nlinarith [Real.sin_sq_add_cos_sq t]
  have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) x)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    (fun t _ => sq_nonneg (Real.tan t))
  have hh := hmono ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
  have hf : 0 ≤ Real.tan x - x := by simpa using hh
  linarith

private theorem tan_upper_quarter (x : ℝ) (hx : x ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    Real.tan x ≤ 2 * x := by
  have hc (t : ℝ) (ht : t ∈ Icc (0 : ℝ) x) : 0 < Real.cos t := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [ht.1, ht.2, hx.2, Real.pi_pos]
  have hsq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) x) : (1 / 2 : ℝ) ≤ Real.cos t ^ 2 := by
    have hp : 0 ≤ Real.cos (2 * t) := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor <;> linarith [ht.1, ht.2, hx.2, Real.pi_pos]
    rw [Real.cos_two_mul] at hp
    linarith
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) x) :
      HasDerivAt (fun s : ℝ => 2 * s - Real.tan s) (2 - 1 / Real.cos t ^ 2) t := by
    convert ((hasDerivAt_id t).const_mul 2).fun_sub
      (Real.hasDerivAt_tan (hc t ht).ne') using 1
    · rfl
    · ring
  have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) x)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    (by
      intro t ht
      have hs := hsq t (interior_subset ht)
      have hp : 0 < Real.cos t ^ 2 := by linarith
      have hdiv : 1 / Real.cos t ^ 2 ≤ (2 : ℝ) := (div_le_iff₀ hp).2 (by linarith)
      linarith)
  have hh := hmono ⟨le_rfl, hx.1⟩ ⟨hx.1, le_rfl⟩ hx.1
  have hf : 0 ≤ 2 * x - Real.tan x := by simpa using hh
  linarith

private theorem log_cos_bounds (x : ℝ) (hx : x ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    0 ≤ -Real.log (Real.cos x) - x ^ 2 / 2 ∧
      -Real.log (Real.cos x) - x ^ 2 / 2 ≤ x ^ 4 / 3 := by
  have eval {f f' : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) (hz : f 0 = 0)
      (hd : ∀ s ∈ Icc 0 t, HasDerivAt f (f' s) s)
      (hn : ∀ s ∈ Icc 0 t, 0 ≤ f' s) : 0 ≤ f t := by
    have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t)
      (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hd s (interior_subset hs)).hasDerivWithinAt)
      (fun s hs => hn s (interior_subset hs))
    have hh := hmono ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
    simpa only [hz] using hh
  have hc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Real.pi / 4)) : 0 < Real.cos t := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [ht.1, ht.2, Real.pi_pos]
  have htanDeriv {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Real.pi / 4)) :
      HasDerivAt (fun s : ℝ => Real.tan s - s) (Real.tan t ^ 2) t := by
    convert (Real.hasDerivAt_tan (hc ht).ne').fun_sub (hasDerivAt_id t) using 1
    · rfl
    · rw [Real.tan_eq_sin_div_cos]
      field_simp [(hc ht).ne']
      nlinarith [Real.sin_sq_add_cos_sq t]
  have htanRem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Real.pi / 4)) :
      0 ≤ Real.tan t - t ∧ Real.tan t - t ≤ (4 / 3 : ℝ) * t ^ 3 := by
    refine ⟨sub_nonneg.mpr (tan_lower t ht.1 (by linarith [ht.2, Real.pi_pos])), ?_⟩
    have hh := eval (f := fun s : ℝ => (4 / 3 : ℝ) * s ^ 3 - (Real.tan s - s))
      (f' := fun s => 4 * s ^ 2 - Real.tan s ^ 2) ht.1 (by simp)
      (by
        intro s hs
        convert (((hasDerivAt_id s).pow 3).const_mul (4 / 3 : ℝ)).fun_sub
          (htanDeriv ⟨hs.1, hs.2.trans ht.2⟩) using 1
        · rfl
        · dsimp only [id]
          ring)
      (by
        intro s hs
        have hlo := tan_lower s hs.1 (by linarith [hs.2, ht.2, Real.pi_pos])
        have hhi := tan_upper_quarter s ⟨hs.1, hs.2.trans ht.2⟩
        nlinarith [hs.1])
    linarith
  have hlogDeriv {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Real.pi / 4)) :
      HasDerivAt (fun s : ℝ => -Real.log (Real.cos s) - s ^ 2 / 2)
        (Real.tan t - t) t := by
    convert (((Real.hasDerivAt_cos t).log (hc ht).ne').neg).fun_sub
      (((hasDerivAt_id t).pow 2).div_const 2) using 1
    · rfl
    · rw [Real.tan_eq_sin_div_cos]
      simp only [id_eq]
      ring
  constructor
  · exact eval (f := fun t : ℝ => -Real.log (Real.cos t) - t ^ 2 / 2)
      (f' := fun t : ℝ => Real.tan t - t) (t := x) hx.1 (by simp)
      (fun t ht => hlogDeriv ⟨ht.1, ht.2.trans hx.2⟩)
      (fun t ht => (htanRem ⟨ht.1, ht.2.trans hx.2⟩).1)
  · have hh := eval
      (f := fun t : ℝ => t ^ 4 / 3 - (-Real.log (Real.cos t) - t ^ 2 / 2))
      (f' := fun t => (4 / 3 : ℝ) * t ^ 3 - (Real.tan t - t)) hx.1 (by simp)
      (by
        intro t ht
        convert (((hasDerivAt_id t).pow 4).div_const 3).fun_sub
          (hlogDeriv ⟨ht.1, ht.2.trans hx.2⟩) using 1
        · rfl
        · dsimp only [id]
          ring)
      (fun t ht => sub_nonneg.mpr (htanRem ⟨ht.1, ht.2.trans hx.2⟩).2)
    linarith

private theorem cotangent_bound (x : ℝ) (hx : 0 < x) (hxpi : x ≤ Real.pi / 4) :
    0 ≤ RademacherFiniteS1.cotangent x ∧
      RademacherFiniteS1.cotangent x ≤ 1 / x := by
  have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx
    (by linarith [hxpi, Real.pi_pos])
  have hc : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], by linarith [hxpi, Real.pi_pos]⟩
  have ht := tan_lower x hx.le (by linarith [hxpi, Real.pi_pos])
  have htan : 0 < Real.tan x := hx.trans_le ht
  have he : RademacherFiniteS1.cotangent x = 1 / Real.tan x := by
    unfold RademacherFiniteS1.cotangent
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hs.ne', hc.ne']
  rw [he]
  exact ⟨by positivity, one_div_le_one_div_of_le hx ht⟩

private theorem cosine_power_bound (x : ℝ) (hx : 0 ≤ x)
    (hxpi : x < Real.pi / 2) (n : ℕ) :
    |Real.cos x ^ n| ≤ Real.exp (-(n : ℝ) * x ^ 2 / 2) := by
  have hc (t : ℝ) (ht : t ∈ Icc (0 : ℝ) x) : 0 < Real.cos t := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [ht.1, ht.2, Real.pi_pos]
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) x) :
      HasDerivAt (fun s : ℝ => Real.log (Real.cos s) + s ^ 2 / 2)
        (-Real.tan t + t) t := by
    convert ((Real.hasDerivAt_cos t).log (hc t ht).ne').add
      (((hasDerivAt_id t).pow 2).div_const 2) using 1
    · rfl
    · rw [Real.tan_eq_sin_div_cos]
      simp only [id_eq]
      ring
  have ha : AntitoneOn (fun t : ℝ => Real.log (Real.cos t) + t ^ 2 / 2)
      (Icc (0 : ℝ) x) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) x)
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t (interior_subset ht)).deriv]
      have hh := tan_lower t (interior_subset ht).1
        (lt_of_le_of_lt (interior_subset ht).2 hxpi)
      linarith
  have hh := ha ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
  have hzero : Real.log (Real.cos x) + x ^ 2 / 2 ≤ 0 := by simpa using hh
  have hlog : Real.log (Real.cos x) ≤ -x ^ 2 / 2 := by linarith
  have hcx := hc x ⟨hx, le_rfl⟩
  calc
    _ = Real.exp ((n : ℝ) * Real.log (Real.cos x)) := by
      rw [← Real.log_pow, Real.exp_log (pow_pos hcx n), abs_of_pos (pow_pos hcx n)]
    _ ≤ _ := Real.exp_le_exp.mpr
      (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))])

private theorem floor_time_error (T : ℝ≥0) (m : ℕ) (hm : 1 ≤ m) :
    0 ≤ (T : ℝ) -
      (PolygonalKilledFunctionalLimit.floorHorizon T (H m) : ℝ) / H m ^ 2 ∧
    (T : ℝ) - (PolygonalKilledFunctionalLimit.floorHorizon T (H m) : ℝ) / H m ^ 2 <
      1 / H m ^ 2 := by
  have hH := RademacherScalarBounds.H_pos hm
  have hH2 := pow_pos hH 2
  have hlo : (PolygonalKilledFunctionalLimit.floorHorizon T (H m) : ℝ) ≤
      (T : ℝ) * H m ^ 2 := Nat.floor_le (mul_nonneg T.2 (sq_nonneg _))
  have hhi : (T : ℝ) * H m ^ 2 <
      (PolygonalKilledFunctionalLimit.floorHorizon T (H m) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  constructor
  · exact sub_nonneg.mpr ((div_le_iff₀ hH2).2 hlo)
  · apply (lt_div_iff₀ hH2).2
    have he : ((T : ℝ) -
        (PolygonalKilledFunctionalLimit.floorHorizon T (H m) : ℝ) / H m ^ 2) * H m ^ 2 =
        (T : ℝ) * H m ^ 2 - (PolygonalKilledFunctionalLimit.floorHorizon T (H m) : ℝ) := by
      field_simp [hH.ne']
      <;> ring
    rw [he]
    linarith

private theorem floor_time_tendsto (T : ℝ≥0) :
    Tendsto (fun j : ℕ =>
      (PolygonalKilledFunctionalLimit.floorHorizon T (H (j + 1)) : ℝ) / H (j + 1) ^ 2)
      atTop (𝓝 (T : ℝ)) := by
  have hi : Tendsto (fun j : ℕ => 1 / H (j + 1) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa [one_div, inv_pow] using (tendsto_inv_atTop_zero.comp scale_tendsto).pow 2
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) ?_ hi
  exact Eventually.of_forall fun j => by
    have he := floor_time_error T (j + 1) (by omega)
    rw [abs_sub_comm, abs_of_nonneg he.1]
    exact he.2.le

private theorem scaled_time_eventually (T : ℝ≥0) (hT : 0 < T) :
    ∀ᶠ j : ℕ in atTop,
      1 ≤ PolygonalKilledFunctionalLimit.floorHorizon T (H (j + 1)) ∧
      (T : ℝ) / 2 ≤
        (PolygonalKilledFunctionalLimit.floorHorizon T (H (j + 1)) : ℝ) / H (j + 1) ^ 2 := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have ht : ∀ᶠ j : ℕ in atTop, (T : ℝ) / 2 <
      (PolygonalKilledFunctionalLimit.floorHorizon T (H (j + 1)) : ℝ) / H (j + 1) ^ 2 :=
    (floor_time_tendsto T).eventually (lt_mem_nhds (by linarith))
  filter_upwards [ht] with j hj
  refine ⟨?_, hj.le⟩
  have hp : (0 : ℝ) <
      (PolygonalKilledFunctionalLimit.floorHorizon T (H (j + 1)) : ℝ) / H (j + 1) ^ 2 :=
    (by positivity : (0 : ℝ) < (T : ℝ) / 2).trans hj
  have hn : (0 : ℝ) < (PolygonalKilledFunctionalLimit.floorHorizon T (H (j + 1)) : ℝ) :=
    (div_pos_iff_of_pos_right
      (pow_pos (RademacherScalarBounds.H_pos (by omega : 1 ≤ j + 1)) 2)).mp hp
  have hnNat : 0 < PolygonalKilledFunctionalLimit.floorHorizon T (H (j + 1)) := by
    exact_mod_cast hn
  omega

private theorem coefficient_tendsto (ell : ℕ) :
    Tendsto (fun j : ℕ => (1 / H (j + 1)) *
      RademacherFiniteS1.cotangent (alpha (j + 1) ell)) atTop
      (𝓝 (4 / (Real.pi * ((2 * ell + 1 : ℕ) : ℝ)))) := by
  let q : ℝ := ((2 * ell + 1 : ℕ) : ℝ)
  let a : ℕ → ℝ := fun j => alpha (j + 1) ell
  have hq : 0 < q := by dsimp [q]; positivity
  have ha : Tendsto a atTop (𝓝 (0 : ℝ)) := by
    have hi := (tendsto_inv_atTop_zero.comp scale_tendsto).const_mul (q * Real.pi / 4)
    simpa [a, alpha, H, q, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hi
  have hap (j : ℕ) : 0 < a j := by dsimp [a, alpha]; positivity
  have hane : Tendsto a atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ha,
      Eventually.of_forall (fun j => by simpa using (hap j).ne')⟩
  have hs := Real.tendsto_sin_div_nhdsNE_zero.comp hane
  have hc := (Real.continuous_cos.tendsto 0).comp ha
  have ht : Tendsto (fun j => (4 / (Real.pi * q)) *
      (Real.cos (a j) / (Real.sin (a j) / a j))) atTop
      (𝓝 (4 / (Real.pi * q))) := by
    simpa using (hc.div hs (by norm_num : (1 : ℝ) ≠ 0)).const_mul (4 / (Real.pi * q))
  have hal : ∀ᶠ j : ℕ in atTop, a j < Real.pi / 2 :=
    ha.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < Real.pi / 2))
  apply ht.congr'
  filter_upwards [hal] with j hj
  have hsin : Real.sin (a j) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi (hap j)
    (by linarith [Real.pi_pos])).ne'
  dsimp [a, alpha, H, q, RademacherFiniteS1.cotangent] at *
  field_simp [hsin, (hap j).ne', Real.pi_ne_zero]
  <;> ring

private theorem power_log_error (T : ℝ≥0) (m : ℕ) (hm : 1 ≤ m)
    (ell : ℕ) (hbeta : beta m ell ≤ Real.pi / 4) :
    |(PolygonalKilledFunctionalLimit.floorHorizon T (H m) : ℝ) *
        Real.log (Real.cos (beta m ell)) +
        lambda * ((2 * ell + 1 : ℕ) : ℝ) ^ 2 * (T : ℝ)| ≤
      (lambda * ((2 * ell + 1 : ℕ) : ℝ) ^ 2 +
        (T : ℝ) * C_rho * ((2 * ell + 1 : ℕ) : ℝ) ^ 4) / H m ^ 2 := by
  let q : ℝ := ((2 * ell + 1 : ℕ) : ℝ)
  let L : ℕ := PolygonalKilledFunctionalLimit.floorHorizon T (H m)
  have hH := RademacherScalarBounds.H_pos hm
  have hH2 := pow_pos hH 2
  have hbpos : 0 < beta m ell := by unfold beta; positivity
  have hb := log_cos_bounds (beta m ell) ⟨hbpos.le, hbeta⟩
  have hlead : beta m ell ^ 2 / 2 = lambda * q ^ 2 / H m ^ 2 := by
    dsimp [beta, lambda, H, q]
    field_simp
    <;> ring
  have hrem : beta m ell ^ 4 / 3 = C_rho * q ^ 4 / H m ^ 4 := by
    dsimp [beta, C_rho, H, q]
    field_simp
    <;> ring
  have he : |Real.log (Real.cos (beta m ell)) + lambda * q ^ 2 / H m ^ 2| ≤
      C_rho * q ^ 4 / H m ^ 4 := by
    rw [← hlead, abs_of_nonpos (by linarith [hb.1])]
    rw [← hrem]
    linarith [hb.2]
  have hL0 : 0 ≤ (L : ℝ) := Nat.cast_nonneg _
  have hLle : (L : ℝ) ≤ (T : ℝ) * H m ^ 2 :=
    Nat.floor_le (mul_nonneg T.2 (sq_nonneg _))
  have hratio : (L : ℝ) / H m ^ 2 ≤ (T : ℝ) := (div_le_iff₀ hH2).2 hLle
  have hgap := floor_time_error T m hm
  have hlam : 0 ≤ lambda * q ^ 2 := by dsimp [lambda]; positivity
  have hC : 0 ≤ C_rho * q ^ 4 := by dsimp [C_rho]; positivity
  have hscale : (L : ℝ) * (C_rho * q ^ 4 / H m ^ 4) ≤
      (T : ℝ) * C_rho * q ^ 4 / H m ^ 2 := by
    calc
      _ = ((L : ℝ) / H m ^ 2) * (C_rho * q ^ 4 / H m ^ 2) := by
        field_simp [hH.ne']
        <;> ring
      _ ≤ (T : ℝ) * (C_rho * q ^ 4 / H m ^ 2) :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = _ := by ring
  change |(L : ℝ) * Real.log (Real.cos (beta m ell)) + lambda * q ^ 2 * (T : ℝ)| ≤ _
  calc
    _ = |(L : ℝ) * (Real.log (Real.cos (beta m ell)) + lambda * q ^ 2 / H m ^ 2) +
        (lambda * q ^ 2) * ((T : ℝ) - (L : ℝ) / H m ^ 2)| := by congr 1; ring
    _ ≤ |(L : ℝ) * (Real.log (Real.cos (beta m ell)) + lambda * q ^ 2 / H m ^ 2)| +
        |(lambda * q ^ 2) * ((T : ℝ) - (L : ℝ) / H m ^ 2)| := by
      simpa only [Real.norm_eq_abs] using norm_add_le
        ((L : ℝ) * (Real.log (Real.cos (beta m ell)) + lambda * q ^ 2 / H m ^ 2))
        ((lambda * q ^ 2) * ((T : ℝ) - (L : ℝ) / H m ^ 2))
    _ = (L : ℝ) * |Real.log (Real.cos (beta m ell)) + lambda * q ^ 2 / H m ^ 2| +
        (lambda * q ^ 2) * ((T : ℝ) - (L : ℝ) / H m ^ 2) := by
      rw [abs_mul, abs_of_nonneg hL0, abs_mul, abs_of_nonneg hlam,
        abs_of_nonneg hgap.1]
    _ ≤ (L : ℝ) * (C_rho * q ^ 4 / H m ^ 4) +
        (lambda * q ^ 2) * (1 / H m ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left he hL0)
        (mul_le_mul_of_nonneg_left hgap.2.le hlam)
    _ ≤ (T : ℝ) * C_rho * q ^ 4 / H m ^ 2 +
        (lambda * q ^ 2) * (1 / H m ^ 2) := add_le_add hscale le_rfl
    _ = _ := by ring

private theorem mode_power_tendsto (T : ℝ≥0) (ell : ℕ) :
    Tendsto (fun j : ℕ => Real.cos (beta (j + 1) ell) ^
      PolygonalKilledFunctionalLimit.floorHorizon T (H (j + 1))) atTop
      (𝓝 (Real.exp (-lambda * ((2 * ell + 1 : ℕ) : ℝ) ^ 2 * (T : ℝ)))) := by
  let q : ℝ := ((2 * ell + 1 : ℕ) : ℝ)
  have hi : Tendsto (fun j : ℕ => 1 / H (j + 1) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa [one_div, inv_pow] using (tendsto_inv_atTop_zero.comp scale_tendsto).pow 2
  have hb : Tendsto (fun j : ℕ => (lambda * q ^ 2 + (T : ℝ) * C_rho * q ^ 4) /
      H (j + 1) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa [div_eq_mul_inv] using hi.const_mul (lambda * q ^ 2 + (T : ℝ) * C_rho * q ^ 4)
  have hbeta : Tendsto (fun j : ℕ => beta (j + 1) ell) atTop (𝓝 (0 : ℝ)) := by
    have hi' := (tendsto_inv_atTop_zero.comp scale_tendsto).const_mul (q * Real.pi / 2)
    simpa [beta, H, q, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hi'
  have hsmall : ∀ᶠ j : ℕ in atTop, beta (j + 1) ell ≤ Real.pi / 4 :=
    (hbeta.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < Real.pi / 4))).mono
      (fun _ h => h.le)
  have hlog : Tendsto (fun j : ℕ =>
      (PolygonalKilledFunctionalLimit.floorHorizon T (H (j + 1)) : ℝ) *
        Real.log (Real.cos (beta (j + 1) ell))) atTop
      (𝓝 (-lambda * q ^ 2 * (T : ℝ))) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [Real.dist_eq]
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) ?_ hb
    filter_upwards [hsmall] with j hj
    simpa only [sub_neg_eq_add, neg_mul, q] using power_log_error T (j + 1) (by omega) ell hj
  have hexp := (Real.continuous_exp.tendsto _).comp hlog
  apply hexp.congr'
  filter_upwards [hsmall] with j hj
  have hc : 0 < Real.cos (beta (j + 1) ell) := by
    apply Real.cos_pos_of_mem_Ioo
    have hp : 0 < beta (j + 1) ell := by unfold beta; positivity
    constructor <;> linarith [hp, hj, Real.pi_pos]
  simp only [Function.comp_apply]
  rw [Real.exp_nat_mul, Real.exp_log hc]

private theorem majorant_summable (T : ℝ≥0) (hT : 0 < T) :
    Summable (majorant T) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hlam : 0 < lambda := by unfold lambda; positivity
  have hq0 : 0 ≤ Real.exp (-lambda * (T : ℝ)) := (Real.exp_pos _).le
  have hq1 : Real.exp (-lambda * (T : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hs := (summable_geometric_of_lt_one hq0 hq1).mul_left
    ((4 / Real.pi) * Real.exp (-lambda * (T : ℝ) / 2))
  have he (ell : ℕ) : majorant T ell =
      ((4 / Real.pi) * Real.exp (-lambda * (T : ℝ) / 2)) *
        Real.exp (-lambda * (T : ℝ)) ^ ell := by
    unfold majorant
    rw [← Real.exp_nat_mul]
    have ha : -lambda * (T : ℝ) / 2 * ((2 * ell + 1 : ℕ) : ℝ) =
        -lambda * (T : ℝ) / 2 + (ell : ℝ) * (-lambda * (T : ℝ)) := by
      push_cast
      ring
    rw [ha, Real.exp_add]
    ring
  simpa only [← he] using hs

private theorem spectralTerm_bound (T : ℝ≥0) (hT : 0 < T) (u : ℝ) (ell : ℕ) :
    |spectralTerm T u ell| ≤ majorant T ell := by
  let q : ℝ := ((2 * ell + 1 : ℕ) : ℝ)
  have hq : 1 ≤ q := by dsimp [q]; exact_mod_cast (by omega : 1 ≤ 2 * ell + 1)
  have hqp : 0 < q := by linarith
  have hlam : 0 ≤ lambda := by unfold lambda; positivity
  have hc : 4 / (Real.pi * q) ≤ 4 / Real.pi := by
    apply div_le_div_of_nonneg_left (by norm_num) Real.pi_pos
    nlinarith [Real.pi_pos]
  have he : Real.exp (-lambda * q ^ 2 * (T : ℝ)) ≤
      Real.exp (-lambda * (T : ℝ) / 2 * q) := by
    apply Real.exp_le_exp.mpr
    have hqq : q / 2 ≤ q ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hqq (mul_nonneg hlam T.2)
    calc
      -lambda * q ^ 2 * (T : ℝ) = -(lambda * (T : ℝ) * q ^ 2) := by ring
      _ ≤ -(lambda * (T : ℝ) * (q / 2)) := neg_le_neg hh
      _ = -lambda * (T : ℝ) / 2 * q := by ring
  have habs : |spectralTerm T u ell| = (4 / (Real.pi * q)) *
      Real.exp (-lambda * q ^ 2 * (T : ℝ)) *
        |Real.cos (q * Real.pi * u / 2)| := by
    change |(4 * (-1 : ℝ) ^ ell / (Real.pi * q)) *
      Real.exp (-lambda * q ^ 2 * (T : ℝ)) * Real.cos (q * Real.pi * u / 2)| = _
    simp only [abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_pos Real.pi_pos, abs_of_pos hqp, abs_of_pos (Real.exp_pos _)]
    norm_num
  rw [habs]
  calc
    _ ≤ (4 / (Real.pi * q)) * Real.exp (-lambda * q ^ 2 * (T : ℝ)) * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)
    _ ≤ (4 / Real.pi) * Real.exp (-lambda * (T : ℝ) / 2 * q) := by
      rw [mul_one]
      exact mul_le_mul hc he (Real.exp_pos _).le (by positivity)
    _ = majorant T ell := rfl

private theorem lowTerm_tendsto (T : ℝ≥0) (hT : 0 < T)
    (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) (ell : ℕ) :
    Tendsto (fun j : ℕ => lowTerm T u j ell) atTop (𝓝 (spectralTerm T u ell)) := by
  let q : ℝ := ((2 * ell + 1 : ℕ) : ℝ)
  have hc : Tendsto (fun j : ℕ =>
      Real.cos (beta (j + 1) ell * (latticeStart (j + 1) u : ℝ))) atTop
      (𝓝 (Real.cos (q * Real.pi * u / 2))) := by
    have ht := (Real.continuous_cos.tendsto _).comp
      ((start_tendsto u hu).const_mul (q * Real.pi / 2))
    convert ht using 1
    · funext j
      congr 1
      dsimp [beta, H, q]
      field_simp
      <;> ring
    · congr 1
      ring
  have hr : Tendsto (fun j : ℕ => rawStartTerm (j + 1)
      (PolygonalKilledFunctionalLimit.floorHorizon T (H (j + 1)))
      (latticeStart (j + 1) u) ell) atTop (𝓝 (spectralTerm T u ell)) := by
    have ht := (((coefficient_tendsto ell).mul_const ((-1 : ℝ) ^ ell)).mul
      (mode_power_tendsto T ell)).mul hc
    convert ht using 1
    · funext j
      unfold rawStartTerm
      ring
    · unfold spectralTerm
      dsimp [q]
      ring
  apply hr.congr'
  filter_upwards [eventually_ge_atTop (2 * ell)] with j hj
  have hell : ell ∈ lowerModes (j + 1) :=
    (RademacherSpectralPairing.mem_lowerModes _ _).2 (by omega)
  simp only [lowTerm, if_pos hell]

private theorem lowTerm_eventually_bound (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    ∀ᶠ j : ℕ in atTop, ∀ ell : ℕ, |lowTerm T u j ell| ≤ majorant T ell := by
  filter_upwards [scaled_time_eventually T hT] with j hj
  intro ell
  by_cases hell : ell ∈ lowerModes (j + 1)
  · rw [lowTerm, if_pos hell]
    let m : ℕ := j + 1
    let n : ℕ := PolygonalKilledFunctionalLimit.floorHorizon T (H m)
    let q : ℝ := ((2 * ell + 1 : ℕ) : ℝ)
    let c : ℝ := (1 / H m) * RademacherFiniteS1.cotangent (alpha m ell)
    have hH : 0 < H m := RademacherScalarBounds.H_pos (by dsimp [m]; omega)
    have hq : 1 ≤ q := by dsimp [q]; exact_mod_cast (by omega : 1 ≤ 2 * ell + 1)
    have hqp : 0 < q := by linarith
    have hal := RademacherSpectralPairing.lower_alpha_bounds hell
    have hbe := RademacherSpectralPairing.lower_beta_bounds hell
    have hcot := cotangent_bound (alpha m ell) hal.1 hal.2.le
    have hc0 : 0 ≤ c := mul_nonneg (by positivity) hcot.1
    have hc1 : c ≤ 4 / (Real.pi * q) := by
      calc
        _ ≤ (1 / H m) * (1 / alpha m ell) :=
          mul_le_mul_of_nonneg_left hcot.2 (by positivity)
        _ = _ := by
          dsimp [alpha, H, q]
          field_simp
          <;> ring
    have hp := cosine_power_bound (beta m ell) hbe.1.le hbe.2 n
    have hp' : |Real.cos (beta m ell) ^ n| ≤
        Real.exp (-lambda * ((n : ℝ) / H m ^ 2) * q ^ 2) := by
      convert hp using 1
      congr 1
      dsimp [beta, lambda, H, q]
      field_simp
      <;> ring
    have htime : (T : ℝ) / 2 ≤ (n : ℝ) / H m ^ 2 := hj.2
    have hqq : q ≤ q ^ 2 := by nlinarith
    have hmult : (T : ℝ) / 2 * q ≤ ((n : ℝ) / H m ^ 2) * q ^ 2 :=
      (mul_le_mul_of_nonneg_left hqq (by positivity)).trans
        (mul_le_mul_of_nonneg_right htime (sq_nonneg _))
    have he : Real.exp (-lambda * ((n : ℝ) / H m ^ 2) * q ^ 2) ≤
        Real.exp (-lambda * (T : ℝ) / 2 * q) := by
      apply Real.exp_le_exp.mpr
      have hlam : 0 ≤ lambda := by unfold lambda; positivity
      nlinarith [mul_le_mul_of_nonneg_left hmult hlam]
    have hcoef : 4 / (Real.pi * q) ≤ 4 / Real.pi := by
      apply div_le_div_of_nonneg_left (by norm_num) Real.pi_pos
      nlinarith [Real.pi_pos]
    have hraw : |rawStartTerm m n (latticeStart m u) ell| =
        c * |Real.cos (beta m ell) ^ n| *
          |Real.cos (beta m ell * (latticeStart m u : ℝ))| := by
      have heq : rawStartTerm m n (latticeStart m u) ell =
          c * (-1 : ℝ) ^ ell * Real.cos (beta m ell) ^ n *
            Real.cos (beta m ell * (latticeStart m u : ℝ)) := by
        dsimp [rawStartTerm, c]
        ring
      rw [heq]
      simp only [abs_mul, abs_of_nonneg hc0, abs_pow, abs_neg, abs_one, one_pow, mul_one]
    change |rawStartTerm m n (latticeStart m u) ell| ≤ majorant T ell
    rw [hraw]
    calc
      _ ≤ (4 / (Real.pi * q)) *
          Real.exp (-lambda * ((n : ℝ) / H m ^ 2) * q ^ 2) * 1 :=
        mul_le_mul (mul_le_mul hc1 hp' (abs_nonneg _) (by positivity))
          (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity)
      _ ≤ (4 / Real.pi) * Real.exp (-lambda * (T : ℝ) / 2 * q) := by
        rw [mul_one]
        exact mul_le_mul hcoef he (Real.exp_pos _).le (by positivity)
      _ = _ := rfl
  · simp only [lowTerm, if_neg hell, abs_zero]
    unfold majorant
    positivity

private theorem low_sum_tendsto (T : ℝ≥0) (hT : 0 < T)
    (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun j : ℕ => ∑ ell ∈ lowerModes (j + 1),
      rawStartTerm (j + 1)
        (PolygonalKilledFunctionalLimit.floorHorizon T (H (j + 1)))
        (latticeStart (j + 1) u) ell) atTop (𝓝 (spectralSeries T u)) := by
  have ht := tendsto_tsum_of_dominated_convergence (majorant_summable T hT)
    (fun ell => lowTerm_tendsto T hT u hu ell)
    (by simpa only [Real.norm_eq_abs] using lowTerm_eventually_bound T hT u)
  have heq (j : ℕ) : (∑' ell : ℕ, lowTerm T u j ell) =
      ∑ ell ∈ lowerModes (j + 1), rawStartTerm (j + 1)
        (PolygonalKilledFunctionalLimit.floorHorizon T (H (j + 1)))
        (latticeStart (j + 1) u) ell := by
    rw [tsum_eq_sum (s := lowerModes (j + 1))
      (fun ell hell => by simp only [lowTerm, if_neg hell])]
    apply Finset.sum_congr rfl
    intro ell hell
    simp only [lowTerm, if_pos hell]
  simp_rw [heq] at ht
  exact ht

private theorem high_sum_abs_le (T : ℝ≥0) (hT : 0 < T)
    (m : ℕ) (hm : 1 ≤ m) (n : ℕ)
    (htime : (T : ℝ) / 2 ≤ (n : ℝ) / H m ^ 2) (r : ℤ) :
    |∑ ell ∈ lowerModes m, rawStartTerm m n r (reflect m ell)| ≤
      (Real.pi / (4 * H m)) * (∑' ell : ℕ, majorant T ell) := by
  have hH := RademacherScalarBounds.H_pos hm
  have hterm (ell : ℕ) (hell : ell ∈ lowerModes m) :
      |rawStartTerm m n r (reflect m ell)| ≤ (Real.pi / (4 * H m)) * majorant T ell := by
    let q : ℝ := ((2 * ell + 1 : ℕ) : ℝ)
    let c : ℝ := (1 / H m) * Real.tan (alpha m ell)
    have hq : 1 ≤ q := by dsimp [q]; exact_mod_cast (by omega : 1 ≤ 2 * ell + 1)
    have hal := RademacherSpectralPairing.lower_alpha_bounds hell
    have hbe := RademacherSpectralPairing.lower_beta_bounds hell
    have hellem := RademacherSpectralPairing.lowerModes_le hell
    have hcosp : 0 < Real.cos (alpha m ell) :=
      (RademacherSpectralPairing.lower_trig_denominators hell).2
    have hsinp : 0 ≤ Real.sin (alpha m ell) :=
      (RademacherSpectralPairing.lower_trig_denominators hell).1.le
    have hsinle : Real.sin (alpha m ell) ≤ Real.cos (alpha m ell) := by
      have htwo : 0 ≤ Real.cos (2 * alpha m ell) := by
        apply Real.cos_nonneg_of_mem_Icc
        constructor <;> linarith [hal.1, hal.2, Real.pi_pos]
      rw [Real.cos_two_mul] at htwo
      nlinarith [Real.sin_sq_add_cos_sq (alpha m ell)]
    have htan0 : 0 ≤ Real.tan (alpha m ell) := by
      rw [Real.tan_eq_sin_div_cos]
      exact div_nonneg hsinp hcosp.le
    have htan1 : Real.tan (alpha m ell) ≤ 1 := by
      rw [Real.tan_eq_sin_div_cos]
      exact (div_le_one hcosp).2 hsinle
    have hc0 : 0 ≤ c := mul_nonneg (by positivity) htan0
    have hc1 : c ≤ 1 / H m := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left htan1
        (by positivity : 0 ≤ 1 / H m)
    have hp := cosine_power_bound (beta m ell) hbe.1.le hbe.2 n
    have hp' : |(-Real.cos (beta m ell)) ^ n| ≤
        Real.exp (-lambda * ((n : ℝ) / H m ^ 2) * q ^ 2) := by
      simp only [abs_pow, abs_neg] at hp ⊢
      convert hp using 1
      congr 1
      dsimp [beta, lambda, H, q]
      field_simp
      <;> ring
    have hqq : q ≤ q ^ 2 := by nlinarith
    have hmult : (T : ℝ) / 2 * q ≤ ((n : ℝ) / H m ^ 2) * q ^ 2 :=
      (mul_le_mul_of_nonneg_left hqq (by positivity)).trans
        (mul_le_mul_of_nonneg_right htime (sq_nonneg _))
    have he : Real.exp (-lambda * ((n : ℝ) / H m ^ 2) * q ^ 2) ≤
        Real.exp (-lambda * (T : ℝ) / 2 * q) := by
      apply Real.exp_le_exp.mpr
      have hlam : 0 ≤ lambda := by unfold lambda; positivity
      nlinarith [mul_le_mul_of_nonneg_left hmult hlam]
    have hraw : |rawStartTerm m n r (reflect m ell)| =
        c * |(-Real.cos (beta m ell)) ^ n| *
          |Real.cos (beta m (reflect m ell) * (r : ℝ))| := by
      have heq : rawStartTerm m n r (reflect m ell) =
          c * (-1 : ℝ) ^ reflect m ell * (-Real.cos (beta m ell)) ^ n *
            Real.cos (beta m (reflect m ell) * (r : ℝ)) := by
        unfold rawStartTerm
        rw [RademacherSpectralPairing.cotangent_reflect hellem,
          RademacherSpectralPairing.cos_beta_reflect hellem]
        dsimp [c]
        ring
      rw [heq]
      simp only [abs_mul, abs_of_nonneg hc0, abs_pow, abs_neg, abs_one, one_pow, mul_one]
    rw [hraw]
    calc
      _ ≤ (1 / H m) * Real.exp (-lambda * ((n : ℝ) / H m ^ 2) * q ^ 2) * 1 :=
        mul_le_mul (mul_le_mul hc1 hp' (abs_nonneg _) (by positivity))
          (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity)
      _ ≤ (1 / H m) * Real.exp (-lambda * (T : ℝ) / 2 * q) := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by
        dsimp [majorant, q]
        field_simp [Real.pi_ne_zero, hH.ne']
        <;> ring
  calc
    _ ≤ ∑ ell ∈ lowerModes m, |rawStartTerm m n r (reflect m ell)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ell ∈ lowerModes m, (Real.pi / (4 * H m)) * majorant T ell :=
      Finset.sum_le_sum hterm
    _ = (Real.pi / (4 * H m)) * ∑ ell ∈ lowerModes m, majorant T ell := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((majorant_summable T hT).sum_le_tsum (lowerModes m)
        (fun ell _ => by unfold majorant; positivity)) (by positivity)

private theorem high_sum_tendsto_zero (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    Tendsto (fun j : ℕ => ∑ ell ∈ lowerModes (j + 1),
      rawStartTerm (j + 1)
        (PolygonalKilledFunctionalLimit.floorHorizon T (H (j + 1)))
        (latticeStart (j + 1) u) (reflect (j + 1) ell)) atTop (𝓝 (0 : ℝ)) := by
  have hi : Tendsto (fun j : ℕ => 1 / H (j + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp scale_tendsto
  have hb : Tendsto (fun j : ℕ =>
      (Real.pi / (4 * H (j + 1))) * (∑' ell : ℕ, majorant T ell)) atTop (𝓝 (0 : ℝ)) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      hi.const_mul ((Real.pi / 4) * ∑' ell : ℕ, majorant T ell)
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq, sub_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) ?_ hb
  filter_upwards [scaled_time_eventually T hT] with j hj
  exact high_sum_abs_le T hT (j + 1) (by omega) _ hj.2 _

private theorem finite_mass_tendsto_series (T : ℝ≥0) (hT : 0 < T)
    (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun j : ℕ => killedMass RademacherCosine.law (j + 1 : ℝ)
      (PolygonalKilledFunctionalLimit.floorHorizon T (H (j + 1)))
      (latticeStart (j + 1) u : ℝ)) atTop (𝓝 (spectralSeries T u)) := by
  have ht := (low_sum_tendsto T hT u hu).add (high_sum_tendsto_zero T hT u)
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [scaled_time_eventually T hT] with j hj
  have hr : latticeStart (j + 1) u ∈ states (j + 1) :=
    Finset.mem_Icc.mpr (latticeStart_bounds _ _)
  simpa only [Nat.cast_add, Nat.cast_one] using
    (finite_mass_split (j + 1) (by omega) _ hj.1 _ hr).symm

-- Public convergence and actual all-start expansion, at every positive time.
theorem spectralTerm_abs_summable (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    Summable (fun ell : ℕ => |spectralTerm T u ell|) := by
  apply (majorant_summable T hT).of_norm_bounded
  intro ell
  simpa only [Real.norm_eq_abs, abs_abs] using spectralTerm_bound T hT u ell

theorem spectral_uniform_absolute_convergence (T : ℝ≥0) (hT : 0 < T) :
    TendstoUniformly
      (fun N : ℕ => fun u : ℝ => ∑ ell ∈ Finset.range N, |spectralTerm T u ell|)
      (fun u : ℝ => ∑' ell : ℕ, |spectralTerm T u ell|) atTop := by
  apply tendstoUniformly_tsum_nat (majorant_summable T hT)
  intro ell u
  simpa only [Real.norm_eq_abs, abs_abs] using spectralTerm_bound T hT u ell

theorem spectral_uniform_convergence (T : ℝ≥0) (hT : 0 < T) :
    TendstoUniformly
      (fun N : ℕ => fun u : ℝ => ∑ ell ∈ Finset.range N, spectralTerm T u ell)
      (spectralSeries T) atTop := by
  apply tendstoUniformly_tsum_nat (majorant_summable T hT)
  intro ell u
  simpa only [Real.norm_eq_abs] using spectralTerm_bound T hT u ell

theorem brownian_survival_spectral
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) (hT : 0 < T)
    (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    P.real (BrownianSurvivalBoundary.closedSurvival B T u) = spectralSeries T u := by
  exact tendsto_nhds_unique (finite_mass_tendsto_brownian B P hB T hT u hu)
    (finite_mass_tendsto_series T hT u hu)

-- Tail algebra, with the explicit same constant for every model, time and start.
private theorem shifted_tail_identity (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    spectralSeries T u -
      (4 / Real.pi) * Real.exp (-lambda * (T : ℝ)) * Real.cos (Real.pi * u / 2) =
        ∑' k : ℕ, spectralTerm T u (k + 1) := by
  have hs : Summable (spectralTerm T u) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using spectralTerm_abs_summable T hT u
  have hzero : spectralTerm T u 0 =
      (4 / Real.pi) * Real.exp (-lambda * (T : ℝ)) * Real.cos (Real.pi * u / 2) := by
    simp [spectralTerm]
  rw [spectralSeries, hs.tsum_eq_zero_add, hzero]
  ring

private theorem tail_term_bound (T : ℝ≥0) (hT : 1 ≤ T) (u : ℝ) (k : ℕ) :
    |spectralTerm T u (k + 1)| ≤
      (4 / (3 * Real.pi)) * Real.exp (-9 * lambda * (T : ℝ)) *
        (Real.exp (-2 * Real.pi ^ 2)) ^ k := by
  let q : ℝ := ((2 * (k + 1) + 1 : ℕ) : ℝ)
  have hq : 3 ≤ q := by
    dsimp [q]
    push_cast
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
  have hqp : 0 < q := by linarith
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hlam : 0 ≤ lambda := by unfold lambda; positivity
  have hfreq : (9 : ℝ) + 16 * (k : ℝ) ≤ q ^ 2 := by
    rcases k with _ | k
    · norm_num [q]
    · dsimp [q]
      push_cast
      nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ)), sq_nonneg (k : ℝ)]
  have hcoef : 4 / (Real.pi * q) ≤ 4 / (3 * Real.pi) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity : (0 : ℝ) < 3 * Real.pi)
    nlinarith [Real.pi_pos]
  have hexp : Real.exp (-lambda * q ^ 2 * (T : ℝ)) ≤
      Real.exp (-9 * lambda * (T : ℝ)) * (Real.exp (-2 * Real.pi ^ 2)) ^ k := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hscaled := mul_le_mul_of_nonneg_left hfreq (mul_nonneg hlam T.2)
    have htime := mul_le_mul_of_nonneg_left hTr
      (show 0 ≤ 16 * lambda * (k : ℝ) by positivity)
    have hid : 16 * lambda = 2 * Real.pi ^ 2 := by unfold lambda; ring
    have htime' : 16 * lambda * (k : ℝ) ≤ 16 * lambda * (k : ℝ) * (T : ℝ) := by
      simpa only [mul_one] using htime
    have hsum : 9 * lambda * (T : ℝ) + 2 * Real.pi ^ 2 * (k : ℝ) ≤
        lambda * q ^ 2 * (T : ℝ) := by
      calc
        _ = 9 * lambda * (T : ℝ) + 16 * lambda * (k : ℝ) := by rw [hid]
        _ ≤ 9 * lambda * (T : ℝ) + 16 * lambda * (k : ℝ) * (T : ℝ) :=
          add_le_add le_rfl htime'
        _ = lambda * (T : ℝ) * (9 + 16 * (k : ℝ)) := by ring
        _ ≤ lambda * (T : ℝ) * q ^ 2 := hscaled
        _ = lambda * q ^ 2 * (T : ℝ) := by ring
    calc
      -lambda * q ^ 2 * (T : ℝ) = -(lambda * q ^ 2 * (T : ℝ)) := by ring
      _ ≤ -(9 * lambda * (T : ℝ) + 2 * Real.pi ^ 2 * (k : ℝ)) := neg_le_neg hsum
      _ = -9 * lambda * (T : ℝ) + (k : ℝ) * (-2 * Real.pi ^ 2) := by ring
  have habs : |spectralTerm T u (k + 1)| = (4 / (Real.pi * q)) *
      Real.exp (-lambda * q ^ 2 * (T : ℝ)) *
        |Real.cos (q * Real.pi * u / 2)| := by
    change |(4 * (-1 : ℝ) ^ (k + 1) / (Real.pi * q)) *
      Real.exp (-lambda * q ^ 2 * (T : ℝ)) * Real.cos (q * Real.pi * u / 2)| = _
    simp only [abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_pos Real.pi_pos, abs_of_pos hqp, abs_of_pos (Real.exp_pos _)]
    norm_num
  rw [habs]
  calc
    _ ≤ (4 / (Real.pi * q)) * Real.exp (-lambda * q ^ 2 * (T : ℝ)) * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)
    _ ≤ (4 / (3 * Real.pi)) *
        (Real.exp (-9 * lambda * (T : ℝ)) * (Real.exp (-2 * Real.pi ^ 2)) ^ k) := by
      rw [mul_one]
      exact mul_le_mul hcoef hexp (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

private theorem series_remainder_bound (T : ℝ≥0) (hT : 1 ≤ T) (u : ℝ) :
    |spectralSeries T u -
      (4 / Real.pi) * Real.exp (-lambda * (T : ℝ)) * Real.cos (Real.pi * u / 2)| ≤
        remainderC * Real.exp (-9 * lambda * (T : ℝ)) := by
  have htpos : 0 < T := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hT
  let Q : ℝ := Real.exp (-2 * Real.pi ^ 2)
  let A : ℝ := (4 / (3 * Real.pi)) * Real.exp (-9 * lambda * (T : ℝ))
  have hq0 : 0 ≤ Q := (Real.exp_pos _).le
  have hq1 : Q < 1 := by
    dsimp [Q]
    apply Real.exp_lt_one_iff.mpr
    nlinarith [sq_pos_of_pos Real.pi_pos]
  have hs : Summable (fun k : ℕ => |spectralTerm T u (k + 1)|) :=
    (summable_nat_add_iff 1).mpr (spectralTerm_abs_summable T htpos u)
  have hgeom : Summable (fun k : ℕ => A * Q ^ k) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left A
  rw [shifted_tail_identity T htpos u]
  calc
    _ ≤ ∑' k : ℕ, |spectralTerm T u (k + 1)| := by
      simpa only [Real.norm_eq_abs] using
        norm_tsum_le_tsum_norm (show Summable (fun k : ℕ => ‖spectralTerm T u (k + 1)‖) by
          simpa only [Real.norm_eq_abs] using hs)
    _ ≤ ∑' k : ℕ, A * Q ^ k :=
      Summable.tsum_le_tsum (fun k => tail_term_bound T hT u k) hs hgeom
    _ = A * (1 - Q)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
    _ = remainderC * Real.exp (-9 * lambda * (T : ℝ)) := by
      dsimp [A, Q, remainderC]
      field_simp [Real.pi_ne_zero, sub_ne_zero.mpr (ne_of_gt hq1)]
      <;> ring

theorem remainderC_pos : 0 < remainderC := by
  unfold remainderC
  apply div_pos (by norm_num)
  apply mul_pos (mul_pos (by norm_num) Real.pi_pos)
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  nlinarith [sq_pos_of_pos Real.pi_pos]

theorem brownian_terminal_block
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) (hT : 1 ≤ T)
    (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    P.real (BrownianSurvivalBoundary.closedSurvival B T u) =
      (4 / Real.pi) * Real.exp (-lambda * (T : ℝ)) * Real.cos (Real.pi * u / 2) +
        terminalRemainder B P T u ∧
    |terminalRemainder B P T u| ≤ remainderC * Real.exp (-9 * lambda * (T : ℝ)) := by
  constructor
  · unfold terminalRemainder
    ring
  · unfold terminalRemainder
    have htpos : 0 < T := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hT
    rw [brownian_survival_spectral B P hB T htpos u hu]
    exact series_remainder_bound T hT u

end Shao.OQ4.BrownianTerminalSpectral
end
