import Shao.OQ5.P35.ConditionalBackground
import Shao.OQ5.P35.ConditionalMixture
import Shao.OQ5.P35.SampleStatistics
import Shao.OQ5.P35.TargetCancellation
import Shao.OQ5.P35.FiniteIIDMoments

/-!
# Uniform conditional bound for the actual p35 jackknife square

Source: original p35 §5, (11)–(13). All four adjusted-row vectors,
including both target/background interactions, are retained. Background
moments are transported from the actual fixed-position conditional law.
-/

set_option autoImplicit false

namespace Shao.OQ5.P35

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

private theorem center_energy_le {n : ℕ} (b : Fin n → ℝ) (hn : 0 < n) :
    (∑ i, center b i ^ 2) ≤ ∑ i, b i ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm : (n : ℝ) * mean b = ∑ i, b i := by
    unfold mean
    field_simp
  have he : (∑ i, center b i ^ 2) =
      (∑ i, b i ^ 2) - 2 * mean b * (∑ i, b i) + (n : ℝ) * mean b ^ 2 := by
    simp only [center, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hc : (∑ i : Fin n, 2 * b i * mean b) =
        (2 * mean b) * ∑ i : Fin n, b i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hc]
  rw [he, ← hm]
  nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (sq_nonneg (mean b))]

private theorem four_square (a b c d : ℝ) :
    (a - b - c - d)^2 ≤ 4 * (a^2+b^2+c^2+d^2) := by
  nlinarith [sq_nonneg (a+b), sq_nonneg (a+c), sq_nonneg (a+d),
    sq_nonneg (b-c), sq_nonneg (b-d), sq_nonneg (c-d)]

private theorem complement_sum {n : ℕ} (J : Finset (Fin n)) (f : Fin n → ℝ) :
    (∑ i : Fin n, if i ∈ J then 0 else f i) =
      ∑ r : Fin (Finset.univ \ J).card, f (Shao.retainedIndex (Finset.univ \ J) r) := by
  classical
  have he : (Finset.univ.filter (fun i : Fin n => i ∉ J)) = Finset.univ \ J := by
    ext i
    simp
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, he]
  conv_lhs => rw [← Finset.image_orderEmbOfFin_univ (Finset.univ \ J) rfl]
  rw [Finset.sum_image]
  · rfl
  · intro i _ j _ hij
    exact (Shao.retainedIndex (Finset.univ \ J)).injective hij

private theorem background_square_sum {n : ℕ} (J : Finset (Fin n)) (f : Fin n → ℝ) :
    (∑ i, backgroundFeature J f i ^ 2) =
      ∑ r : Fin (Finset.univ \ J).card, f (Shao.retainedIndex (Finset.univ \ J) r)^2 := by
  classical
  rw [← complement_sum J (fun i => f i ^ 2)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ J <;> simp [backgroundFeature, hi]

private theorem background_sum_compressed {n : ℕ} (J : Finset (Fin n)) (f : Fin n → ℝ) :
    backgroundSum J f =
      ∑ r : Fin (Finset.univ \ J).card, f (Shao.retainedIndex (Finset.univ \ J) r) :=
  complement_sum J f

private theorem background_leave_sum {n : ℕ} (J : Finset (Fin n)) (f : Fin n → ℝ) :
    (∑ i, backgroundFeature J f i ^ 2 *
      (backgroundSum J f - backgroundFeature J f i)^2) =
      ∑ r : Fin (Finset.univ \ J).card,
        f (Shao.retainedIndex (Finset.univ \ J) r)^2 *
          ((∑ s : Fin (Finset.univ \ J).card,
            f (Shao.retainedIndex (Finset.univ \ J) s)) -
              f (Shao.retainedIndex (Finset.univ \ J) r))^2 := by
  classical
  rw [← background_sum_compressed J f, ← complement_sum J
    (fun i => f i ^ 2 * (backgroundSum J f - f i)^2)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ J <;> simp [backgroundFeature, hi]

private theorem studentizer_four_energy {n : ℕ} (A d Z : Fin n → ℝ)
    (hn : 3 ≤ n) (J : Finset (Fin n)) (t δ : ℝ)
    (hZ : ∀ i ∈ J, Z i = t) (hd : ∀ i ∈ J, d i = δ)
    (hδ : δ = ((J.card : ℝ)-1)*t^2/((n : ℝ)-2)) :
    studentizerSq A d Z ≤ (16 / ((n : ℝ)-1)) *
      (2 * (∑ i, A i ^ 2) + 2 * (∑ i, backgroundOffset J d i ^ 2) +
        (((J.card : ℝ)*t^2*backgroundSum J Z ^ 2 +
          (J.card : ℝ)^2*t^2*(∑ i, backgroundFeature J Z i ^ 2) +
          (∑ i, backgroundFeature J Z i ^ 2 *
            (backgroundSum J Z-backgroundFeature J Z i)^2)) / ((n : ℝ)-2)^2)) := by
  classical
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hpoint (i : Fin n) :
      adjustedRow A d Z i ^ 2 ≤ 4 *
        (2*A i^2+2*backgroundOffset J d i^2+
          (t^2*backgroundSum J Z^2*targetIndicator J i +
            (J.card : ℝ)^2*t^2*backgroundFeature J Z i^2 +
            backgroundFeature J Z i^2*(backgroundSum J Z-backgroundFeature J Z i)^2) /
            ((n : ℝ)-2)^2) := by
    rw [adjustedRow_eq_targetCancellation A d Z hn J t δ hZ hd hδ]
    have hb : (A i+backgroundOffset J d i)^2 ≤ 2*A i^2+2*backgroundOffset J d i^2 := by
      nlinarith [sq_nonneg (A i-backgroundOffset J d i)]
    have hp := four_square (A i+backgroundOffset J d i)
      (t*backgroundSum J Z*targetIndicator J i/((n : ℝ)-2))
      ((J.card : ℝ)*t*backgroundFeature J Z i/((n : ℝ)-2))
      (backgroundFeature J Z i*(backgroundSum J Z-backgroundFeature J Z i)/((n : ℝ)-2))
    have hi : targetIndicator J i ^ 2 = targetIndicator J i := by
      unfold targetIndicator
      split_ifs <;> norm_num
    have he :
        (A i+backgroundOffset J d i -
          (t*backgroundSum J Z*targetIndicator J i+
            (J.card : ℝ)*t*backgroundFeature J Z i+
            backgroundFeature J Z i*(backgroundSum J Z-backgroundFeature J Z i))/((n : ℝ)-2))^2 ≤
        4*((A i+backgroundOffset J d i)^2+
          (t^2*backgroundSum J Z^2*targetIndicator J i+
            (J.card : ℝ)^2*t^2*backgroundFeature J Z i^2+
            backgroundFeature J Z i^2*(backgroundSum J Z-backgroundFeature J Z i)^2)/
            ((n : ℝ)-2)^2) := by
      convert hp using 1
      · congr 1
        ring
      · simp only [div_pow, mul_pow, hi]
        ring
    linarith
  have hI : (∑ i : Fin n, targetIndicator J i) = (J.card : ℝ) := by
    unfold targetIndicator
    rw [Finset.sum_ite_mem_eq]
    simp
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hpoint i)
  have hsum : (∑ i, adjustedRow A d Z i^2) ≤ 4 *
      (2 * (∑ i, A i ^ 2) + 2 * (∑ i, backgroundOffset J d i ^ 2) +
        (((J.card : ℝ)*t^2*backgroundSum J Z ^ 2 +
          (J.card : ℝ)^2*t^2*(∑ i, backgroundFeature J Z i ^ 2) +
          (∑ i, backgroundFeature J Z i ^ 2 *
            (backgroundSum J Z-backgroundFeature J Z i)^2)) / ((n : ℝ)-2)^2)) := by
    have he : (∑ i : Fin n, 4 *
        (2*A i^2+2*backgroundOffset J d i^2+
          (t^2*backgroundSum J Z^2*targetIndicator J i +
            (J.card : ℝ)^2*t^2*backgroundFeature J Z i^2 +
            backgroundFeature J Z i^2*(backgroundSum J Z-backgroundFeature J Z i)^2) /
            ((n : ℝ)-2)^2)) = 4 *
      (2 * (∑ i, A i ^ 2) + 2 * (∑ i, backgroundOffset J d i ^ 2) +
        (((J.card : ℝ)*t^2*backgroundSum J Z ^ 2 +
          (J.card : ℝ)^2*t^2*(∑ i, backgroundFeature J Z i ^ 2) +
          (∑ i, backgroundFeature J Z i ^ 2 *
            (backgroundSum J Z-backgroundFeature J Z i)^2)) / ((n : ℝ)-2)^2)) := by
      rw [← Finset.mul_sum]
      simp only [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, hI]
      ring
    rw [he] at hs
    exact hs
  rw [studentizerSq_eq_centeredRow A d Z hn]
  have hc := center_energy_le (adjustedRow A d Z) (by omega)
  calc
    _ ≤ (4/((n : ℝ)-1)) * (∑ i, adjustedRow A d Z i^2) :=
      mul_le_mul_of_nonneg_left hc (div_nonneg (by norm_num) (by linarith))
    _ ≤ (4/((n : ℝ)-1)) * (4 * _) :=
      mul_le_mul_of_nonneg_left hsum (div_nonneg (by norm_num) (by linarith))
    _ = _ := by ring

private theorem scale_coefficients (j : ℕ) (hj : 1 ≤ j) :
    let k := categoryScale j
    let n := (rareSampleSize j : ℝ)
    let t := categoryFeature j
    (4 ≤ k) ∧ (n = k^4) ∧ (4 ≤ n) ∧
      (t^2 ≤ k^5) ∧
      (categoryOffset j = ((targetCategoryCount j : ℝ)-1)*t^2/(n-2)) ∧
      ((targetCategoryCount j : ℝ) = k) ∧
      (k^2*(1/512 : ℝ)^(2*j) ≤ 1) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  dsimp only
  have hk := categoryScale_succ_ge l
  have hv := categoryValue_succ_ge l
  have ht : categoryFeature (l+1)^2 ≤ categoryScale (l+1)^5 := by
    rw [← categoryValue_sq_succ]
    dsimp [categoryFeature, featureMean]
    nlinarith
  have hn : (rareSampleSize (l+1) : ℝ) = categoryScale (l+1)^4 := by
    simp [rareSampleSize, targetCategoryCount, categoryScale]
  refine ⟨hk, hn, ?_, ht, ?_, ?_, ?_⟩
  · rw [hn]
    nlinarith [sq_nonneg (categoryScale (l+1)^2-4)]
  · simp [categoryOffset, rareSampleSize, targetCategoryCount, categoryScale]
  · simp [targetCategoryCount, categoryScale]
  · have he : categoryScale (l+1)^2 * (1/512 : ℝ)^(2*(l+1)) =
        (1/16384 : ℝ)^(l+1) := by
      unfold categoryScale
      rw [← pow_mul, Nat.mul_comm (l+1) 2, pow_mul, pow_mul, ← mul_pow]
      norm_num
    rw [he]
    exact pow_le_one₀ (by norm_num) (by norm_num)

private theorem noise_cond_square (n j : ℕ) (hj : 1 ≤ j)
    (J : Finset (Fin n)) (i : Fin n) :
    Integrable (fun ω => decodeNoise (sampleCoordinate i.val ω)^2)
      (cond sampleLaw (fixedCategoryEvent n j J)) ∧
    (∫ ω, decodeNoise (sampleCoordinate i.val ω)^2
      ∂cond sampleLaw (fixedCategoryEvent n j J)) = (1/3 : ℝ) := by
  have := categoryPatternLaw_isProbability j hj J i
  have hm : Measure.map (fun ω => decodeNoise (sampleCoordinate i.val ω))
      (cond sampleLaw (fixedCategoryEvent n j J)) = noiseLaw := by
    calc
      _ = Measure.map Prod.snd (Measure.map (sampleDecoded i.val)
          (cond sampleLaw (fixedCategoryEvent n j J))) := by
        rw [Measure.map_map measurable_snd (measurable_sampleDecoded i.val)]
        rfl
      _ = _ := by
        rw [map_sampleDecoded_cond_fixed n j hj J i, Measure.map_snd_prod,
          measure_univ, one_smul]
  have hi : IdentDistrib (fun ω => decodeNoise (sampleCoordinate i.val ω)) id
      (cond sampleLaw (fixedCategoryEvent n j J)) noiseLaw :=
    ⟨(measurable_decodeNoise.comp (measurable_sampleCoordinate i.val)).aemeasurable,
      measurable_id.aemeasurable, by simpa only [Measure.map_id] using hm⟩
  have hs := hi.comp (measurable_id.pow_const 2)
  exact ⟨hs.integrable_iff.mpr integrable_noiseLaw_sq,
    hs.integral_eq.trans integral_noiseLaw_sq⟩

private theorem feature_map_mean (j : ℕ) :
    (∫ z : ℝ, z ∂Measure.map categoryFeature (backgroundCategoryLaw j)) =
      ∫ c, categoryFeature c ∂backgroundCategoryLaw j := by
  exact integral_map (measurable_of_countable categoryFeature).aemeasurable
    measurable_id.aestronglyMeasurable

private theorem feature_map_square (j : ℕ) :
    (∫ z : ℝ, z^2 ∂Measure.map categoryFeature (backgroundCategoryLaw j)) =
      ∫ c, categoryFeature c^2 ∂backgroundCategoryLaw j := by
  exact integral_map (measurable_of_countable categoryFeature).aemeasurable
    (measurable_id.pow_const 2).aestronglyMeasurable

private theorem offset_map_square (j : ℕ) :
    (∫ z : ℝ, z^2 ∂Measure.map categoryOffset (backgroundCategoryLaw j)) =
      ∫ c, categoryOffset c^2 ∂backgroundCategoryLaw j := by
  exact integral_map (measurable_of_countable categoryOffset).aemeasurable
    (measurable_id.pow_const 2).aestronglyMeasurable

private theorem numeric_energy_bound
    (n k t C u M D m p q : ℝ)
    (hn : 4 ≤ n) (hC : 1 ≤ C)
    (hm : 0 ≤ m) (hmn : m ≤ n) (hp : 0 ≤ p) (hpn : p ≤ n)
    (hq : 0 ≤ q) (hqn : q ≤ n)
    (hM : 0 ≤ M) (hMC : M ≤ C) (hDC : D ≤ C)
    (hku : k*t^2*u^2 ≤ n*C^2)
    (hk : 0 ≤ k) (hkt : k*t^2 ≤ n^2) (hkt2 : k^2*t^2 ≤ n^2)
    (hu : u^2 ≤ C^2) :
    (16/(n-1)) * (2*n/3 + 2*m*D +
      (k*t^2*(m*M+m*p*u^2) + k^2*t^2*(m*M) +
        m*M*(p*M+p*q*u^2))/(n-2)^2) ≤ 1024*C^3 := by
  have hn0 : 0 < n := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hC2 : C ≤ C^2 := by nlinarith
  have hC3 : C^2 ≤ C^3 := by nlinarith [mul_nonneg (sq_nonneg C) (by linarith : 0 ≤ C-1)]
  have hmM : m*M ≤ n*C :=
    mul_le_mul hmn hMC hM (le_of_lt hn0)
  have hpM : p*M ≤ n*C :=
    mul_le_mul hpn hMC hM (le_of_lt hn0)
  have hmp : m*p ≤ n^2 := by
    calc m*p ≤ n*n := mul_le_mul hmn hpn hp (le_of_lt hn0)
         _ = n^2 := by ring
  have hpq : p*q ≤ n^2 := by
    calc p*q ≤ n*n := mul_le_mul hpn hqn hq (le_of_lt hn0)
         _ = n^2 := by ring
  have hterm1 : k*t^2*(m*M+m*p*u^2) ≤ 2*n^3*C^3 := by
    have ha : k*t^2*(m*M) ≤ n^3*C := by
      calc
        _ ≤ n^2*(n*C) := mul_le_mul hkt hmM
          (mul_nonneg hm hM) (sq_nonneg n)
        _ = _ := by ring
    have hb : k*t^2*(m*p*u^2) ≤ n^3*C^2 := by
      calc
        _ = (m*p)*(k*t^2*u^2) := by ring
        _ ≤ n^2*(n*C^2) := mul_le_mul hmp hku
          (mul_nonneg (mul_nonneg hk (sq_nonneg t)) (sq_nonneg u)) (sq_nonneg n)
        _ = _ := by ring
    have hCC3 : C ≤ C^3 := hC2.trans hC3
    have hna := mul_le_mul_of_nonneg_left hCC3 (pow_nonneg hn0.le 3)
    have hnb := mul_le_mul_of_nonneg_left hC3 (pow_nonneg hn0.le 3)
    nlinarith
  have hterm2 : k^2*t^2*(m*M) ≤ n^3*C^3 := by
    calc
      _ ≤ n^2*(n*C) := mul_le_mul hkt2 hmM
        (mul_nonneg hm hM) (sq_nonneg n)
      _ = n^3*C := by ring
      _ ≤ n^3*C^3 := mul_le_mul_of_nonneg_left (hC2.trans hC3) (pow_nonneg hn0.le 3)
  have hterm3 : m*M*(p*M+p*q*u^2) ≤ 2*n^3*C^3 := by
    have ha : m*M*(p*M) ≤ n^2*C^2 := by
      calc
        _ ≤ (n*C)*(n*C) := mul_le_mul hmM hpM
          (mul_nonneg hp hM) (mul_nonneg hn0.le hC0)
        _ = _ := by ring
    have hb : m*M*(p*q*u^2) ≤ n^3*C^3 := by
      calc
        _ ≤ (n*C)*(n^2*C^2) := mul_le_mul hmM
          (mul_le_mul hpq hu (sq_nonneg u) (sq_nonneg n))
          (mul_nonneg (mul_nonneg hp hq) (sq_nonneg u)) (mul_nonneg hn0.le hC0)
        _ = _ := by ring
    have hnn : n^2 ≤ n^3 := by nlinarith [mul_nonneg (sq_nonneg n) (by linarith : 0 ≤ n-1)]
    have hc : n^2*C^2 ≤ n^3*C^3 :=
      mul_le_mul hnn hC3 (sq_nonneg C) (pow_nonneg hn0.le 3)
    nlinarith
  have hs : k*t^2*(m*M+m*p*u^2) + k^2*t^2*(m*M) +
      m*M*(p*M+p*q*u^2) ≤ 5*n^3*C^3 := by linarith
  have hden : n^2 ≤ 4*(n-2)^2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ n-4) (by linarith : 0 ≤ 3*n-4)]
  have hquot : (5*n^3*C^3)/(n-2)^2 ≤ 20*n*C^3 := by
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < n-2))).mpr
    have hh := mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ 5*n*C^3)
    nlinarith
  have hbase : 2*n/3+2*m*D ≤ 4*n*C^3 := by
    have hmd : m*D ≤ n*C := by
      calc
        m*D ≤ m*C := mul_le_mul_of_nonneg_left hDC hm
        _ ≤ n*C := mul_le_mul_of_nonneg_right hmn hC0
    have hc := mul_le_mul_of_nonneg_left (hC2.trans hC3) hn0.le
    have h1 : 1 ≤ C^3 := le_trans hC (hC2.trans hC3)
    have hc1 := mul_le_mul_of_nonneg_left h1 hn0.le
    nlinarith
  have hall : 2*n/3+2*m*D +
      (k*t^2*(m*M+m*p*u^2) + k^2*t^2*(m*M) +
        m*M*(p*M+p*q*u^2))/(n-2)^2 ≤ 24*n*C^3 := by
    have hdiv := div_le_div_of_nonneg_right hs (sq_nonneg (n-2))
    linarith
  have hratio : n/(n-1) ≤ 2 := by
    apply (div_le_iff₀ (by linarith : 0 < n-1)).mpr
    linarith
  calc
    _ ≤ (16/(n-1))*(24*n*C^3) :=
      mul_le_mul_of_nonneg_left hall (div_nonneg (by norm_num) (by linarith))
    _ = 384*(n/(n-1))*C^3 := by ring
    _ ≤ 384*2*C^3 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio (by norm_num)) (by positivity)
    _ ≤ _ := by nlinarith [pow_nonneg hC0 3]

private theorem fixed_scalar_bound (j : ℕ) (hj : 1 ≤ j)
    (J : Finset (Fin (rareSampleSize j))) (hJ : J.card = targetCategoryCount j)
    (C : ℝ) (hC : 1 ≤ C)
    (hM : (∫ c, categoryFeature c^2 ∂backgroundCategoryLaw j) ≤ C)
    (hD : (∫ c, categoryOffset c^2 ∂backgroundCategoryLaw j) ≤ C)
    (hu : |∫ c, categoryFeature c ∂backgroundCategoryLaw j| ≤ C*(1/512 : ℝ)^j) :
    Integrable (jackknifeSq (rareSampleSize j))
      (cond sampleLaw (fixedCategoryEvent (rareSampleSize j) j J)) ∧
    (∫ ω, jackknifeSq (rareSampleSize j) ω
      ∂cond sampleLaw (fixedCategoryEvent (rareSampleSize j) j J)) ≤ 1024*C^3 := by
  classical
  let n := rareSampleSize j
  let μ := cond sampleLaw (fixedCategoryEvent n j J)
  let B : Finset (Fin n) := Finset.univ \ J
  let e : Fin B.card → Fin n := fun r => Shao.retainedIndex B r
  have he : Function.Injective e := (Shao.retainedIndex B).injective
  have hback (r : Fin B.card) : e r ∉ J :=
    (Finset.mem_sdiff.mp (Shao.retainedIndex_mem B r)).2
  have := fixedCategoryEvent_cond_isProbability n j hj J
  have := backgroundCategoryLaw_isProbability j hj
  let W : Fin B.card → (ℕ → ℝ) → ℝ :=
    fun r ω => categoryFeature (sampleCategory (e r).val ω)
  let D : Fin B.card → (ℕ → ℝ) → ℝ :=
    fun r ω => categoryOffset (sampleCategory (e r).val ω)
  let A : Fin n → (ℕ → ℝ) → ℝ := fun i ω => decodeNoise (sampleCoordinate i.val ω)
  let ν := Measure.map categoryFeature (backgroundCategoryLaw j)
  let M : ℝ := ∫ c, categoryFeature c^2 ∂backgroundCategoryLaw j
  let u : ℝ := ∫ c, categoryFeature c ∂backgroundCategoryLaw j
  let V : ℝ := ∫ c, categoryOffset c^2 ∂backgroundCategoryLaw j
  have hWm (r : Fin B.card) : Measurable (W r) :=
    (measurable_of_countable categoryFeature).comp (measurable_sampleCategory (e r).val)
  have hWi : iIndepFun W μ :=
    iIndepFun_selectedBackgroundFeature B.card n j hj J e he hback
  have hWlaw (r : Fin B.card) : IdentDistrib (W r) id μ ν :=
    identDistrib_selectedBackgroundFeature B.card n j hj J e he hback r
  have hW2 (r : Fin B.card) : MemLp (W r) 2 μ :=
    (hWlaw r).symm.memLp_snd (memLp_backgroundFeature j hj)
  have hWsq (r : Fin B.card) : Integrable (fun ω => W r ω^2) μ :=
    (hW2 r).integrable_sq
  have hWint (r : Fin B.card) : (∫ ω, W r ω^2 ∂μ) = M :=
    ((hWlaw r).comp (measurable_id.pow_const 2)).integral_eq.trans (feature_map_square j)
  have hDsq (r : Fin B.card) : Integrable (fun ω => D r ω^2) μ :=
    (((identDistrib_selectedBackgroundOffset B.card n j hj J e he hback r).symm.memLp_snd
      (memLp_backgroundOffset j hj))).integrable_sq
  have hDint (r : Fin B.card) : (∫ ω, D r ω^2 ∂μ) = V :=
    ((identDistrib_selectedBackgroundOffset B.card n j hj J e he hback r).comp
      (measurable_id.pow_const 2)).integral_eq.trans (offset_map_square j)
  have hAsq (i : Fin n) : Integrable (fun ω => A i ω^2) μ :=
    (noise_cond_square n j hj J i).1
  have hAint (i : Fin n) : (∫ ω, A i ω^2 ∂μ) = (1/3 : ℝ) :=
    (noise_cond_square n j hj J i).2
  have hS2 : MemLp (finiteFeatureSum W) 2 μ :=
    memLp_finsetSum Finset.univ (fun r _ => hW2 r)
  have hL : Integrable (finiteLeaveOwnSquareSum W) μ :=
    finite_iid_leaveOwnSquare_integrable hWm hWi hWlaw (memLp_backgroundFeature j hj)
  have hSint : (∫ ω, finiteFeatureSum W ω^2 ∂μ) =
      (B.card : ℝ)*M+(B.card : ℝ)*((B.card-1 : ℕ) : ℝ)*u^2 := by
    simpa only [ν, feature_map_mean, feature_map_square] using
      finite_iid_sumSquare_integral hWm hWi hWlaw (memLp_backgroundFeature j hj)
  have hLint : (∫ ω, finiteLeaveOwnSquareSum W ω ∂μ) =
      (B.card : ℝ)*M*(((B.card-1 : ℕ) : ℝ)*M+
        ((B.card-1 : ℕ) : ℝ)*((B.card-2 : ℕ) : ℝ)*u^2) := by
    simpa only [ν, feature_map_mean, feature_map_square] using
      finite_iid_leaveOwnSquare_integral hWm hWi hWlaw (memLp_backgroundFeature j hj)
  let G : (ℕ → ℝ) → ℝ := fun ω =>
    (16/((n : ℝ)-1)) * (2*(∑ i, A i ω^2)+2*(∑ r, D r ω^2)+
      (((targetCategoryCount j : ℝ)*categoryFeature j^2*finiteFeatureSum W ω^2+
        (targetCategoryCount j : ℝ)^2*categoryFeature j^2*(∑ r, W r ω^2)+
        finiteLeaveOwnSquareSum W ω)/((n : ℝ)-2)^2))
  have hG : Integrable G μ :=
    ((((integrable_finsetSum _ (fun i _ => hAsq i)).const_mul 2).add
      ((integrable_finsetSum _ (fun r _ => hDsq r)).const_mul 2)).add
      ((((hS2.integrable_sq.const_mul _).add
        ((integrable_finsetSum _ (fun r _ => hWsq r)).const_mul _)).add hL).div_const _)).const_mul _
  have hGint : (∫ ω, G ω ∂μ) =
      (16/((n : ℝ)-1))*(2*(n : ℝ)/3+2*(B.card : ℝ)*V+
        (((targetCategoryCount j : ℝ)*categoryFeature j^2*
          ((B.card : ℝ)*M+(B.card : ℝ)*((B.card-1 : ℕ) : ℝ)*u^2)+
          (targetCategoryCount j : ℝ)^2*categoryFeature j^2*((B.card : ℝ)*M)+
          (B.card : ℝ)*M*(((B.card-1 : ℕ) : ℝ)*M+
            ((B.card-1 : ℕ) : ℝ)*((B.card-2 : ℕ) : ℝ)*u^2))/((n : ℝ)-2)^2)) := by
    have hA0 := (integrable_finsetSum Finset.univ (fun i _ => hAsq i)).const_mul 2
    have hD0 := (integrable_finsetSum Finset.univ (fun r _ => hDsq r)).const_mul 2
    have hT := hS2.integrable_sq.const_mul ((targetCategoryCount j : ℝ)*categoryFeature j^2)
    have hZ0 := (integrable_finsetSum Finset.univ (fun r _ => hWsq r)).const_mul
      ((targetCategoryCount j : ℝ)^2*categoryFeature j^2)
    unfold G
    rw [integral_const_mul, integral_add, integral_add,
      integral_const_mul, integral_const_mul, integral_div,
      integral_add, integral_add, integral_const_mul, integral_const_mul,
      hSint, hLint, integral_finsetSum _ (fun i _ => hAsq i),
      integral_finsetSum _ (fun r _ => hDsq r),
      integral_finsetSum _ (fun r _ => hWsq r)]
    · simp only [hAint, hDint, hWint, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    all_goals first
      | exact hA0
      | exact hD0
      | exact hT
      | exact hZ0
      | exact hL
      | exact hA0.add hD0
      | exact hT.add hZ0
      | exact ((hT.add hZ0).add hL).div_const (((n : ℝ)-2)^2)
  rcases scale_coefficients j hj with ⟨hk4, hnk, hn4, ht, hδ, hcast, hrate⟩
  have hn3 : 3 ≤ n := by
    have : (3 : ℝ) ≤ n := by exact le_trans (by norm_num) hn4
    exact_mod_cast this
  have hdom : ∀ᵐ ω ∂μ, jackknifeSq n ω ≤ G ω := by
    filter_upwards [ae_cond_mem (μ := sampleLaw)
      (measurableSet_fixedCategoryEvent n j J)] with ω hω
    let a : Fin n → ℝ := fun i => decodeNoise (finiteSample n ω i)
    let d : Fin n → ℝ := fun i => observationOffset (finiteSample n ω i)
    let z : Fin n → ℝ := fun i => observationFeature (finiteSample n ω i)
    have hzt (i : Fin n) (hi : i ∈ J) : z i = categoryFeature j := by
      have hc : sampleCategory i.val ω = j := by
        simpa only [fixedCategoryEvent, Set.mem_ofPred_eq, hi, ite_true] using hω i
      change categoryFeature (sampleCategory i.val ω) = categoryFeature j
      rw [hc]
    have hdt (i : Fin n) (hi : i ∈ J) : d i = categoryOffset j := by
      have hc : sampleCategory i.val ω = j := by
        simpa only [fixedCategoryEvent, Set.mem_ofPred_eq, hi, ite_true] using hω i
      change categoryOffset (sampleCategory i.val ω) = categoryOffset j
      rw [hc]
    have hhδ : categoryOffset j =
        ((J.card : ℝ)-1)*categoryFeature j^2/((n : ℝ)-2) := by
      rw [hJ]
      exact hδ
    have hb := studentizer_four_energy a d z hn3 J (categoryFeature j)
      (categoryOffset j) hzt hdt hhδ
    have heD : (∑ i, backgroundOffset J d i^2) = ∑ r, D r ω^2 :=
      background_square_sum J d
    have heZ : (∑ i, backgroundFeature J z i^2) = ∑ r, W r ω^2 :=
      background_square_sum J z
    have heS : backgroundSum J z = finiteFeatureSum W ω :=
      background_sum_compressed J z
    have heL : (∑ i, backgroundFeature J z i^2 *
        (backgroundSum J z-backgroundFeature J z i)^2) =
        finiteLeaveOwnSquareSum W ω :=
      background_leave_sum J z
    rw [heD, heZ, heL, heS, hJ] at hb
    exact hb
  have hI : Integrable (jackknifeSq n) μ :=
    hG.mono' (measurable_jackknifeSq n).aestronglyMeasurable
      (hdom.mono (fun ω hω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (jackknifeSq_nonneg n hn3 ω)]
        exact hω))
  refine ⟨hI, (integral_mono_ae hI hG hdom).trans ?_⟩
  rw [hGint]
  let k := categoryScale j
  let t := categoryFeature j
  let ρ := (1/512 : ℝ)^j
  have hk0 : 0 ≤ k := by dsimp [k]; linarith
  have hk1 : 1 ≤ k := by dsimp [k]; linarith
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hC0 : 0 ≤ C := by linarith
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hu2 : u^2 ≤ C^2*ρ^2 := by
    calc
      u^2 = |u|^2 := (sq_abs u).symm
      _ ≤ (C*ρ)^2 := pow_le_pow_left₀ (abs_nonneg u) hu 2
      _ = _ := by ring
  have huC : u^2 ≤ C^2 := by
    calc
      _ ≤ C^2*ρ^2 := hu2
      _ ≤ C^2*1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ hρ0 hρ1) (sq_nonneg C)
      _ = _ := by ring
  have hr : k^2*ρ^2 ≤ 1 := by
    simpa only [k, ρ, ← pow_mul, Nat.mul_comm j 2] using hrate
  have hkt : k*t^2 ≤ (n : ℝ)^2 := by
    calc
      _ ≤ k*k^5 := mul_le_mul_of_nonneg_left ht hk0
      _ = k^6 := by ring
      _ ≤ k^8 := pow_le_pow_right₀ hk1 (by norm_num)
      _ = _ := by rw [hnk]; ring
  have hkt2 : k^2*t^2 ≤ (n : ℝ)^2 := by
    calc
      _ ≤ k^2*k^5 := mul_le_mul_of_nonneg_left ht (sq_nonneg k)
      _ = k^7 := by ring
      _ ≤ k^8 := pow_le_pow_right₀ hk1 (by norm_num)
      _ = _ := by rw [hnk]; ring
  have hku : k*t^2*u^2 ≤ (n : ℝ)*C^2 := by
    calc
      _ ≤ (k*k^5)*(C^2*ρ^2) := mul_le_mul
        (mul_le_mul_of_nonneg_left ht hk0) hu2 (sq_nonneg u)
        (mul_nonneg hk0 (pow_nonneg hk0 5))
      _ = (n : ℝ)*C^2*(k^2*ρ^2) := by rw [hnk]; ring
      _ ≤ (n : ℝ)*C^2*1 :=
        mul_le_mul_of_nonneg_left hr (mul_nonneg hn0 (sq_nonneg C))
      _ = _ := by ring
  have hbcard : B.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ B
  have hmN : (B.card : ℝ) ≤ n := by exact_mod_cast hbcard
  have hpN : ((B.card-1 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast (Nat.sub_le B.card 1).trans hbcard
  have hqN : ((B.card-2 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast (Nat.sub_le B.card 2).trans hbcard
  have hnum := numeric_energy_bound (n : ℝ) k t C u M V
    (B.card : ℝ) ((B.card-1 : ℕ) : ℝ) ((B.card-2 : ℕ) : ℝ)
    hn4 hC (Nat.cast_nonneg _) hmN (Nat.cast_nonneg _) hpN (Nat.cast_nonneg _) hqN
    (integral_nonneg (fun c => sq_nonneg (categoryFeature c))) hM hD
    hku hk0 hkt hkt2 huC
  simpa only [hcast, k, t] using hnum

private theorem all_fixed_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 1 ≤ j →
      ∀ J : Finset (Fin (rareSampleSize j)), J.card = targetCategoryCount j →
        Integrable (jackknifeSq (rareSampleSize j))
          (cond sampleLaw (fixedCategoryEvent (rareSampleSize j) j J)) ∧
        (∫ ω, jackknifeSq (rareSampleSize j) ω
          ∂cond sampleLaw (fixedCategoryEvent (rareSampleSize j) j J)) ≤ C := by
  obtain ⟨D, hD0, hb⟩ := backgroundCategoryMoments_uniform
  let C := D+1
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨1024*C^3, by dsimp [C]; positivity, ?_⟩
  intro j hj J hJ
  have hm := hb j hj
  apply fixed_scalar_bound j hj J hJ C hC
  · exact hm.1.trans (by dsimp [C]; linarith)
  · exact hm.2.1.trans (by dsimp [C]; linarith)
  · exact hm.2.2.1.trans (mul_le_mul_of_nonneg_right
      (by dsimp [C]; linarith : D ≤ C) (by positivity))

theorem integrable_jackknifeSq_cond_fixed (j : ℕ) (hj : 1 ≤ j)
    (J : Finset (Fin (rareSampleSize j))) (hJ : J.card = targetCategoryCount j) :
    Integrable (jackknifeSq (rareSampleSize j))
      (cond sampleLaw (fixedCategoryEvent (rareSampleSize j) j J)) := by
  obtain ⟨C, _, h⟩ := all_fixed_bounds
  exact (h j hj J hJ).1

theorem integrable_jackknifeSq_cond_rare (j : ℕ) (hj : 1 ≤ j) :
    Integrable (jackknifeSq (rareSampleSize j))
      (cond sampleLaw (rareCategoryEvent j)) := by
  classical
  apply integrable_cond_exactCategoryEvent (rareSampleSize j) (targetCategoryCount j) j hj
    (targetCategoryCount_le_rareSampleSize j) (jackknifeSq (rareSampleSize j))
  intro J hJ
  exact integrable_jackknifeSq_cond_fixed j hj J (Finset.mem_powersetCard.mp hJ).2

theorem jackknifeSq_cond_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 1 ≤ j →
      (∀ J : Finset (Fin (rareSampleSize j)), J.card = targetCategoryCount j →
        (∫ ω, jackknifeSq (rareSampleSize j) ω
          ∂cond sampleLaw (fixedCategoryEvent (rareSampleSize j) j J)) ≤ C) ∧
      (∫ ω, jackknifeSq (rareSampleSize j) ω
        ∂cond sampleLaw (rareCategoryEvent j)) ≤ C := by
  classical
  obtain ⟨C, hC, h⟩ := all_fixed_bounds
  refine ⟨C, hC, ?_⟩
  intro j hj
  refine ⟨fun J hJ => (h j hj J hJ).2, ?_⟩
  apply integral_cond_exactCategoryEvent_le (rareSampleSize j) (targetCategoryCount j) j hj
    (targetCategoryCount_le_rareSampleSize j) (jackknifeSq (rareSampleSize j)) C
  · intro J hJ
    exact (h j hj J (Finset.mem_powersetCard.mp hJ).2).1
  · intro J hJ
    exact (h j hj J (Finset.mem_powersetCard.mp hJ).2).2

end

end Shao.OQ5.P35
