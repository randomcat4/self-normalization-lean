import Shao.OQ3.EuclideanGaussianPolynomialIntegrability
import Shao.OQ3.NormalizedIIDPairSuperpolynomialDecay
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem euclidean_gaussian_weighted_tail_bound
    (k : ℕ) (a R : ℝ) (ha : 0 < a) (hR : 0 ≤ R) :
    let tail : Set (ℝ × ℝ) := {z | R ≤ Real.sqrt (z.1 ^ 2 + z.2 ^ 2)}
    let f : (ℝ × ℝ) → ℝ := fun z =>
      (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ k *
        Real.exp (-a * (z.1 ^ 2 + z.2 ^ 2))
    let envelope : (ℝ × ℝ) → ℝ := fun z =>
      (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ k *
        Real.exp (-(a / 2) * (z.1 ^ 2 + z.2 ^ 2))
    Integrable f ∧ Integrable envelope ∧ IntegrableOn f tail ∧
      0 ≤ (∫ z in tail, f z) ∧
      (∫ z in tail, f z) ≤
        Real.exp (-a * R ^ 2 / 2) * (∫ z : ℝ × ℝ, envelope z) := by
  dsimp only
  let tail : Set (ℝ × ℝ) := {z | R ≤ Real.sqrt (z.1 ^ 2 + z.2 ^ 2)}
  let f : (ℝ × ℝ) → ℝ := fun z =>
    (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ k * Real.exp (-a * (z.1 ^ 2 + z.2 ^ 2))
  let envelope : (ℝ × ℝ) → ℝ := fun z =>
    (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ k *
      Real.exp (-(a / 2) * (z.1 ^ 2 + z.2 ^ 2))
  let c : ℝ := Real.exp (-a * R ^ 2 / 2)
  have hf : Integrable f := integrable_euclidean_radius_power_gaussian k a ha
  have hen : Integrable envelope :=
    integrable_euclidean_radius_power_gaussian k (a / 2) (by positivity)
  have henvnonneg : ∀ z, 0 ≤ envelope z := fun z =>
    mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) k) (Real.exp_pos _).le
  have hc : 0 ≤ c := (Real.exp_pos _).le
  have hcenv : Integrable (fun z => c * envelope z) := hen.const_mul c
  have hrcont : Continuous (fun z : ℝ × ℝ => Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) := by
    fun_prop
  have htail : MeasurableSet tail := (isClosed_le continuous_const hrcont).measurableSet
  have hbound : ∀ z ∈ tail, f z ≤ c * envelope z := by
    intro z hz
    have hr2 : R ^ 2 ≤ z.1 ^ 2 + z.2 ^ 2 := by
      calc
        R ^ 2 ≤ (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ 2 :=
          pow_le_pow_left₀ hR hz 2
        _ = z.1 ^ 2 + z.2 ^ 2 := Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
    have hm : a * R ^ 2 ≤ a * (z.1 ^ 2 + z.2 ^ 2) :=
      mul_le_mul_of_nonneg_left hr2 ha.le
    have he : Real.exp (-a * (z.1 ^ 2 + z.2 ^ 2)) =
        Real.exp (-a * (z.1 ^ 2 + z.2 ^ 2) / 2) *
          Real.exp (-(a / 2) * (z.1 ^ 2 + z.2 ^ 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      f z = Real.exp (-a * (z.1 ^ 2 + z.2 ^ 2) / 2) * envelope z := by
        dsimp [f, envelope]
        rw [he]
        ring
      _ ≤ c * envelope z :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith))
          (henvnonneg z)
  have hfirst : (∫ z in tail, f z) ≤ ∫ z in tail, c * envelope z :=
    setIntegral_mono_on hf.integrableOn hcenv.integrableOn htail hbound
  have hsecond : (∫ z in tail, c * envelope z) ≤ ∫ z : ℝ × ℝ, c * envelope z := by
    calc
      _ ≤ ∫ z : ℝ × ℝ in Set.univ, c * envelope z :=
        setIntegral_mono_set hcenv.integrableOn
          (Filter.Eventually.of_forall (fun z => mul_nonneg hc (henvnonneg z)))
          (Filter.Eventually.of_forall (fun _ _ => Set.mem_univ _))
      _ = ∫ z : ℝ × ℝ, c * envelope z := by simp only [Measure.restrict_univ]
  have hlast : (∫ z in tail, f z) ≤ c * (∫ z : ℝ × ℝ, envelope z) := by
    simpa only [integral_const_mul] using hfirst.trans hsecond
  exact ⟨hf, hen, hf.integrableOn,
    integral_nonneg (fun z =>
      mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) k) (Real.exp_pos _).le),
    hlast⟩

theorem eventually_scaled_euclidean_gaussian_weighted_tail
    (k : ℕ) (delta q epsilon : ℝ) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      let tail : Set (ℝ × ℝ) := {z |
        delta * Real.sqrt (n : ℝ) ≤ Real.sqrt (z.1 ^ 2 + z.2 ^ 2)}
      let f : (ℝ × ℝ) → ℝ := fun z =>
        (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ k *
          Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2)
      IntegrableOn f tail ∧ 0 ≤ (∫ z in tail, f z) ∧
        Real.rpow (n : ℝ) q * (∫ z in tail, f z) < epsilon := by
  let envelope : (ℝ × ℝ) → ℝ := fun z =>
    (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ k *
      Real.exp (-((1 / 2 : ℝ) / 2) * (z.1 ^ 2 + z.2 ^ 2))
  have hen : Integrable envelope :=
    integrable_euclidean_radius_power_gaussian k ((1 / 2 : ℝ) / 2) (by norm_num)
  let I : ℝ := ∫ z : ℝ × ℝ, envelope z
  have hI : 0 ≤ I := integral_nonneg (fun z =>
    mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) k) (Real.exp_pos _).le)
  let C : ℝ := 1 + I
  have hC : 0 < C := by dsimp [C]; linarith
  let c : ℝ := delta ^ 2 / 4
  have hc : 0 < c := by dsimp [c]; positivity
  have hev := eventually_real_power_mul_stretched_exponential_lt
    1 c q (epsilon / C) (by norm_num) hc (div_pos hepsilon hC)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max M 1, le_max_right _ _, ?_⟩
  intro n hn
  dsimp only
  let tail : Set (ℝ × ℝ) := {z |
    delta * Real.sqrt (n : ℝ) ≤ Real.sqrt (z.1 ^ 2 + z.2 ^ 2)}
  let f : (ℝ × ℝ) → ℝ := fun z =>
    (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ k * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2)
  have hn1 : 1 ≤ n := (le_max_right M 1).trans hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hstep : Real.rpow (n : ℝ) q * Real.exp (-c * (n : ℝ)) < epsilon / C := by
    have hp := hM n ((le_max_left M 1).trans hn)
    change Real.rpow (n : ℝ) q * Real.exp (-c * Real.rpow (n : ℝ) (1 : ℝ)) < epsilon / C at hp
    rw [Real.rpow_eq_pow (n : ℝ) 1, Real.rpow_one] at hp
    exact hp
  have ht := euclidean_gaussian_weighted_tail_bound k (1 / 2)
    (delta * Real.sqrt (n : ℝ)) (by norm_num)
      (mul_nonneg hdelta.le (Real.sqrt_nonneg _))
  dsimp only at ht
  have hexp (z : ℝ × ℝ) :
      Real.exp (-(1 / 2 : ℝ) * (z.1 ^ 2 + z.2 ^ 2)) =
        Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) := by
    congr 1
    ring
  simp only [hexp] at ht
  have hcoef : Real.exp (-(1 / 2 : ℝ) * (delta * Real.sqrt (n : ℝ)) ^ 2 / 2) =
      Real.exp (-c * (n : ℝ)) := by
    congr 1
    rw [mul_pow, Real.sq_sqrt hnR.le]
    dsimp [c]
    ring
  have hupper : (∫ z in tail, f z) ≤ Real.exp (-c * (n : ℝ)) * I := by
    simpa only [hcoef] using ht.2.2.2.2
  have ha : 0 ≤ Real.rpow (n : ℝ) q := (Real.rpow_pos_of_pos hnR q).le
  have hIC : I ≤ C := by dsimp [C]; linarith
  refine ⟨ht.2.2.1, ht.2.2.2.1, ?_⟩
  calc
    Real.rpow (n : ℝ) q * (∫ z in tail, f z) ≤
        Real.rpow (n : ℝ) q * (Real.exp (-c * (n : ℝ)) * I) :=
      mul_le_mul_of_nonneg_left hupper ha
    _ = (Real.rpow (n : ℝ) q * Real.exp (-c * (n : ℝ))) * I := by ring
    _ ≤ (Real.rpow (n : ℝ) q * Real.exp (-c * (n : ℝ))) * C :=
      mul_le_mul_of_nonneg_left hIC (mul_nonneg ha (Real.exp_pos _).le)
    _ < (epsilon / C) * C := mul_lt_mul_of_pos_right hstep hC
    _ = epsilon := div_mul_cancel₀ epsilon (ne_of_gt hC)

end
end Shao.OQ3
