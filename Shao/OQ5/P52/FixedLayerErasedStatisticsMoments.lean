import Shao.OQ5.P52.FixedLayerErasedNoiseEdges
import Shao.OQ5.P52.FixedLayerSampleStatistics

/-!
# Honest moments of the original statistics under the actual erased product

Finite L2 closure establishes integrability before every integral expansion.
Noise and residual cross terms vanish for all indices. Random sample
centering is retained in the original jackknife identity.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped BigOperators

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

attribute [local instance] fixedErasedLaw_isProbabilityMeasure

private theorem sum_memLp_two {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (n : ℕ) (f : Fin n → α → ℝ) (hf : ∀ i, MemLp (f i) 2 μ) :
    MemLp (fun x => ∑ i : Fin n, f i x) 2 μ :=
  memLp_finsetSum Finset.univ (fun i _ => hf i)

private theorem center_memLp_two {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (n : ℕ) (f : Fin n → α → ℝ) (hf : ∀ i, MemLp (f i) 2 μ) (i : Fin n) :
    MemLp (fun x => Shao.OQ5.P35.center (fun k => f k x) i) 2 μ := by
  change MemLp (fun x => f i x - (n : ℝ)⁻¹ * ∑ k : Fin n, f k x) 2 μ
  exact (hf i).sub ((sum_memLp_two μ n f hf).const_mul (n : ℝ)⁻¹)

private theorem integral_sum_mul_sum {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (n m : ℕ) (f : Fin n → α → ℝ) (g : Fin m → α → ℝ)
    (hf : ∀ i, MemLp (f i) 2 μ) (hg : ∀ k, MemLp (g k) 2 μ) :
    (∫ x, (∑ i : Fin n, f i x) * (∑ k : Fin m, g k x) ∂μ) =
      ∑ i : Fin n, ∑ k : Fin m, ∫ x, f i x * g k x ∂μ := by
  have _hproduct := (sum_memLp_two μ n f hf).integrable_mul (sum_memLp_two μ m g hg)
  have hI (i : Fin n) (k : Fin m) : Integrable (fun x => f i x * g k x) μ :=
    (hf i).integrable_mul (hg k)
  calc
    _ = ∫ x, ∑ i : Fin n, ∑ k : Fin m, f i x * g k x ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => Fintype.sum_mul_sum _ _
    _ = _ := by
      rw [integral_finsetSum Finset.univ (fun i _ =>
        integrable_finsetSum Finset.univ (fun k _ => hI i k))]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum Finset.univ (fun k _ => hI i k)

private theorem integral_linear_sq {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f g : α → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (a b : ℝ) :
    (∫ x, (a * f x + b * g x) ^ 2 ∂μ) =
      a ^ 2 * (∫ x, (f x) ^ 2 ∂μ) +
        (2 * a * b) * (∫ x, f x * g x ∂μ) + b ^ 2 * (∫ x, (g x) ^ 2 ∂μ) := by
  have hff := hf.integrable_sq
  have hfg : Integrable (fun x => f x * g x) μ := hf.integrable_mul hg
  have hgg := hg.integrable_sq
  have _hsq := ((hf.const_mul a).add (hg.const_mul b)).integrable_sq
  calc
    _ = ∫ x, a ^ 2 * (f x) ^ 2 + (2 * a * b) * (f x * g x) +
        b ^ 2 * (g x) ^ 2 ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only; ring
    _ = _ := by
      have hA : Integrable (fun x => a ^ 2 * (f x) ^ 2) μ := hff.const_mul _
      have hB : Integrable (fun x => (2 * a * b) * (f x * g x)) μ := hfg.const_mul _
      have hC : Integrable (fun x => b ^ 2 * (g x) ^ 2) μ := hgg.const_mul _
      have hAB : Integrable (fun x => a ^ 2 * (f x) ^ 2 + (2 * a * b) * (f x * g x)) μ :=
        hA.add hB
      rw [integral_add hAB hC, integral_add hA hB, integral_const_mul,
        integral_const_mul, integral_const_mul]

private theorem center_inner_identity (n : ℕ) (hn0 : (n : ℝ) ≠ 0)
    (f g : Fin n → ℝ) :
    (∑ i : Fin n, Shao.OQ5.P35.center f i * Shao.OQ5.P35.center g i) =
      (∑ i : Fin n, f i * g i) -
        (n : ℝ)⁻¹ * (∑ i : Fin n, f i) * (∑ i : Fin n, g i) := by
  simp only [Shao.OQ5.P35.center, Shao.OQ5.P35.mean, sub_mul, mul_sub,
    Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hn0]
  ring

private theorem integral_center_cross_zero {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (n : ℕ) (hn0 : (n : ℝ) ≠ 0)
    (f g : Fin n → α → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (hg : ∀ k, MemLp (g k) 2 μ)
    (hzero : ∀ i k, (∫ x, f i x * g k x ∂μ) = 0) :
    (∫ x, ∑ i : Fin n,
      Shao.OQ5.P35.center (fun k => f k x) i *
        Shao.OQ5.P35.center (fun k => g k x) i ∂μ) = 0 := by
  have hI (i k : Fin n) : Integrable (fun x => f i x * g k x) μ :=
    (hf i).integrable_mul (hg k)
  have hdiag : Integrable (fun x => ∑ i : Fin n, f i x * g i x) μ :=
    integrable_finsetSum Finset.univ (fun i _ => hI i i)
  have htotal : Integrable (fun x => (∑ i : Fin n, f i x) * (∑ k : Fin n, g k x)) μ :=
    (sum_memLp_two μ n f hf).integrable_mul (sum_memLp_two μ n g hg)
  have _hcenter : Integrable (fun x => ∑ i : Fin n,
      Shao.OQ5.P35.center (fun k => f k x) i *
        Shao.OQ5.P35.center (fun k => g k x) i) μ :=
    integrable_finsetSum Finset.univ (fun i _ =>
      (center_memLp_two μ n f hf i).integrable_mul (center_memLp_two μ n g hg i))
  have hd0 : (∫ x, ∑ i : Fin n, f i x * g i x ∂μ) = 0 := by
    rw [integral_finsetSum Finset.univ (fun i _ => hI i i)]
    simp only [hzero, Finset.sum_const_zero]
  have ht0 : (∫ x, (∑ i : Fin n, f i x) * (∑ k : Fin n, g k x) ∂μ) = 0 := by
    rw [integral_sum_mul_sum μ n n f g hf hg]
    simp only [hzero, Finset.sum_const_zero]
  calc
    _ = ∫ x, (∑ i : Fin n, f i x * g i x) -
        (n : ℝ)⁻¹ * ((∑ i : Fin n, f i x) * (∑ k : Fin n, g k x)) ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        simpa only [mul_assoc] using center_inner_identity n hn0 (fun i => f i x) (fun k => g k x)
    _ = 0 := by
      rw [integral_sub hdiag (htotal.const_mul _), integral_const_mul, hd0, ht0]
      ring

private theorem center_add_mul (n : ℕ) (f g : Fin n → ℝ) (c : ℝ) (i : Fin n) :
    Shao.OQ5.P35.center (fun k => f k + g k * c) i =
      Shao.OQ5.P35.center f i + Shao.OQ5.P35.center g i * c := by
  simp only [Shao.OQ5.P35.center, Shao.OQ5.P35.mean, Finset.sum_add_distrib,
    ← Finset.sum_mul]
  ring

private theorem integral_center_energy_add_mul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (n : ℕ) (f g : Fin n → α → ℝ)
    (hf : ∀ i, MemLp (f i) 2 μ) (hg : ∀ i, MemLp (g i) 2 μ) (c : ℝ) :
    (∫ x, ∑ i : Fin n,
      (Shao.OQ5.P35.center (fun k => f k x + g k x * c) i) ^ 2 ∂μ) =
      (∫ x, ∑ i : Fin n, (Shao.OQ5.P35.center (fun k => f k x) i) ^ 2 ∂μ) +
        (2 * c) * (∫ x, ∑ i : Fin n,
          Shao.OQ5.P35.center (fun k => f k x) i *
            Shao.OQ5.P35.center (fun k => g k x) i ∂μ) +
        c ^ 2 * (∫ x, ∑ i : Fin n, (Shao.OQ5.P35.center (fun k => g k x) i) ^ 2 ∂μ) := by
  have hff := integrable_finsetSum Finset.univ (fun i _ =>
    (center_memLp_two μ n f hf i).integrable_sq)
  have hcross (i : Fin n) : Integrable (fun x =>
      Shao.OQ5.P35.center (fun k => f k x) i *
        Shao.OQ5.P35.center (fun k => g k x) i) μ :=
    (center_memLp_two μ n f hf i).integrable_mul (center_memLp_two μ n g hg i)
  have hfg : Integrable (fun x => ∑ i : Fin n,
      Shao.OQ5.P35.center (fun k => f k x) i *
        Shao.OQ5.P35.center (fun k => g k x) i) μ :=
    integrable_finsetSum Finset.univ (fun i _ => hcross i)
  have hgg := integrable_finsetSum Finset.univ (fun i _ =>
    (center_memLp_two μ n g hg i).integrable_sq)
  have _hsq := integrable_finsetSum Finset.univ (fun i _ =>
    (center_memLp_two μ n (fun k x => f k x + g k x * c)
      (fun k => (hf k).add ((hg k).mul_const c)) i).integrable_sq)
  calc
    _ = ∫ x,
        (∑ i : Fin n, (Shao.OQ5.P35.center (fun k => f k x) i) ^ 2) +
          (2 * c) * (∑ i : Fin n,
            Shao.OQ5.P35.center (fun k => f k x) i *
              Shao.OQ5.P35.center (fun k => g k x) i) +
          c ^ 2 * (∑ i : Fin n, (Shao.OQ5.P35.center (fun k => g k x) i) ^ 2) ∂μ := by
      apply integral_congr_ae
      refine Eventually.of_forall fun x => ?_
      dsimp only
      simp_rw [center_add_mul]
      calc
        _ = ∑ i : Fin n,
            ((Shao.OQ5.P35.center (fun k => f k x) i) ^ 2 +
              (2 * c) * (Shao.OQ5.P35.center (fun k => f k x) i *
                Shao.OQ5.P35.center (fun k => g k x) i) +
              c ^ 2 * (Shao.OQ5.P35.center (fun k => g k x) i) ^ 2) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by
      have hB : Integrable (fun x => (2 * c) * (∑ i : Fin n,
          Shao.OQ5.P35.center (fun k => f k x) i *
            Shao.OQ5.P35.center (fun k => g k x) i)) μ := hfg.const_mul _
      have hC : Integrable (fun x => c ^ 2 * (∑ i : Fin n,
          (Shao.OQ5.P35.center (fun k => g k x) i) ^ 2)) μ := hgg.const_mul _
      have hAB : Integrable (fun x =>
          (∑ i : Fin n, (Shao.OQ5.P35.center (fun k => f k x) i) ^ 2) +
            (2 * c) * (∑ i : Fin n,
              Shao.OQ5.P35.center (fun k => f k x) i *
                Shao.OQ5.P35.center (fun k => g k x) i)) μ := hff.add hB
      rw [integral_add hAB hC, integral_add hff hB, integral_const_mul, integral_const_mul]

private theorem noise_sum_memLp_two (j n : ℕ) :
    MemLp (fun x : Fin n → LayerObs => ∑ i : Fin n, (x i).1) 2
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) :=
  sum_memLp_two (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) n (fun i (x : Fin n → LayerObs) => (x i).1) (fixedErasedSampleNoise_memLp_two j n)

theorem fixedSampleU_memLp_two_fixedErasedLaw
    (j n : ℕ) (hn : 3 ≤ n) :
    MemLp (fun x : Fin n → LayerObs => fixedSampleU x) 2
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) := by
  apply (memLp_congr_ae (Eventually.of_forall (fixedSampleU_eq_noise_add_residual n hn))).mpr
  exact ((noise_sum_memLp_two j n).const_mul (2 / (n : ℝ))).add
    ((fixedErasedResidualPairSum_memLp_two j n).const_mul (n.choose 2 : ℝ)⁻¹)

theorem integrable_fixedSampleStudentizerSq_fixedErasedLaw
    (j n : ℕ) (hn : 3 ≤ n) :
    Integrable (fun x : Fin n → LayerObs => fixedSampleStudentizerSq x)
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) := by
  let f : Fin n → (Fin n → LayerObs) → ℝ :=
    fun i x => (x i).1 + fixedErasedResidualRow i x / ((n : ℝ) - 2)
  have hf (i : Fin n) : MemLp (f i) 2 (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) := by
    change MemLp ((fun x : Fin n → LayerObs => (x i).1) +
      (fun x : Fin n → LayerObs => fixedErasedResidualRow i x / ((n : ℝ) - 2))) 2
        (Measure.pi (fun _ : Fin n => fixedErasedLaw j))
    exact (fixedErasedSampleNoise_memLp_two j n i).add
      ((fixedErasedResidualRow_memLp_two j n i).mul_const (((n : ℝ) - 2)⁻¹))
  have hI := (integrable_finsetSum Finset.univ (fun i _ =>
    (center_memLp_two _ n f hf i).integrable_sq)).const_mul (4 / ((n : ℝ) - 1))
  exact hI.congr (Eventually.of_forall fun x =>
    (fixedSampleStudentizerSq_eq_centered_residual_rows n hn x).symm)

private theorem integral_noise_sum_zero (j n : ℕ) :
    (∫ x : Fin n → LayerObs, ∑ i : Fin n, (x i).1
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) = 0 := by
  rw [integral_finsetSum Finset.univ (fun i _ =>
    (fixedErasedSampleNoise_memLp_two j n i).integrable (by norm_num))]
  simp only [integral_fixedErasedSampleNoise_eq_zero, Finset.sum_const_zero]

theorem integral_fixedSampleU_fixedErasedLaw_eq_zero
    (j n : ℕ) (hn : 3 ≤ n) :
    (∫ x : Fin n → LayerObs, fixedSampleU x
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) = 0 := by
  have _hU := (fixedSampleU_memLp_two_fixedErasedLaw j n hn).integrable (by norm_num)
  calc
    _ = ∫ x : Fin n → LayerObs,
        (2 / (n : ℝ)) * (∑ i : Fin n, (x i).1) +
          (n.choose 2 : ℝ)⁻¹ * fixedErasedResidualPairSum x
        ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j) :=
      integral_congr_ae (Eventually.of_forall (fixedSampleU_eq_noise_add_residual n hn))
    _ = 0 := by
      rw [integral_add
        (((noise_sum_memLp_two j n).integrable (by norm_num)).const_mul _)
        (((fixedErasedResidualPairSum_memLp_two j n).integrable (by norm_num)).const_mul _),
        integral_const_mul, integral_const_mul, integral_noise_sum_zero,
        integral_fixedErasedResidualPairSum_eq_zero]
      ring

private theorem integral_noise_sum_sq (j n : ℕ) :
    (∫ x : Fin n → LayerObs, (∑ i : Fin n, (x i).1) ^ 2
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) = (n : ℝ) / 3 := by
  have _hI := (noise_sum_memLp_two j n).integrable_sq
  simp only [pow_two]
  rw [integral_sum_mul_sum _ n n (fun i (x : Fin n → LayerObs) => (x i).1) (fun i (x : Fin n → LayerObs) => (x i).1)
    (fixedErasedSampleNoise_memLp_two j n) (fixedErasedSampleNoise_memLp_two j n)]
  simp [integral_fixedErasedSampleNoise_mul, nsmul_eq_mul, div_eq_mul_inv]

private theorem integral_noise_mul_pair (j n : ℕ) (i : Fin n) :
    (∫ x : Fin n → LayerObs, (x i).1 * fixedErasedResidualPairSum x
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) = 0 := by
  have _hI := (fixedErasedSampleNoise_memLp_two j n i).integrable_mul
    (fixedErasedResidualPairSum_memLp_two j n)
  have hI (a b : Fin n) : Integrable (fun x : Fin n → LayerObs =>
      (x i).1 * (if a < b then fixedResidualKernel (x a, x b) else 0))
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) := by
    by_cases hab : a < b
    · simpa only [hab, ite_true] using
        integrable_fixedErasedSampleNoise_mul_residualEdge j n i a b hab.ne
    · simpa only [hab, ite_false, mul_zero] using
        (integrable_const (0 : ℝ) : Integrable (fun _ : Fin n → LayerObs => (0 : ℝ))
          (Measure.pi (fun _ : Fin n => fixedErasedLaw j)))
  change (∫ x : Fin n → LayerObs, (x i).1 *
    (∑ a : Fin n, ∑ b : Fin n, if a < b then fixedResidualKernel (x a, x b) else 0)
    ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) = 0
  simp only [Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun a _ =>
    integrable_finsetSum Finset.univ (fun b _ => hI a b))]
  apply Finset.sum_eq_zero
  intro a _
  rw [integral_finsetSum Finset.univ (fun b _ => hI a b)]
  apply Finset.sum_eq_zero
  intro b _
  by_cases hab : a < b
  · simpa only [hab, ite_true] using
      integral_fixedErasedSampleNoise_mul_residualEdge j n i a b hab.ne
  · simp only [hab, ite_false, mul_zero, integral_zero]

private theorem integral_noise_sum_mul_pair (j n : ℕ) :
    (∫ x : Fin n → LayerObs, (∑ i : Fin n, (x i).1) * fixedErasedResidualPairSum x
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) = 0 := by
  have _hI := (noise_sum_memLp_two j n).integrable_mul
    (fixedErasedResidualPairSum_memLp_two j n)
  simp only [Finset.sum_mul]
  have hI (i : Fin n) : Integrable (fun x : Fin n → LayerObs =>
      (x i).1 * fixedErasedResidualPairSum x)
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) :=
    (fixedErasedSampleNoise_memLp_two j n i).integrable_mul
      (fixedErasedResidualPairSum_memLp_two j n)
  rw [integral_finsetSum Finset.univ (fun i _ => hI i)]
  simp only [integral_noise_mul_pair, Finset.sum_const_zero]

theorem integral_fixedSampleU_scaled_sq_fixedErasedLaw
    (j n : ℕ) (hn : 3 ≤ n) :
    (∫ x : Fin n → LayerObs, (n : ℝ) * (fixedSampleU x) ^ 2
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) =
      (4 / 3 : ℝ) + (2 / ((n : ℝ) - 1)) *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂(fixedErasedLaw j).prod (fixedErasedLaw j)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have h1 : (n : ℝ) - 1 ≠ 0 := by
    have h : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    exact sub_ne_zero.mpr (ne_of_gt h)
  have _hI := ((fixedSampleU_memLp_two_fixedErasedLaw j n hn).integrable_sq).const_mul (n : ℝ)
  calc
    _ = (n : ℝ) * (∫ x : Fin n → LayerObs,
        ((2 / (n : ℝ)) * (∑ i : Fin n, (x i).1) +
          (n.choose 2 : ℝ)⁻¹ * fixedErasedResidualPairSum x) ^ 2
        ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) := by
      rw [integral_const_mul]
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun x => congrArg (fun t : ℝ => t ^ 2)
        (fixedSampleU_eq_noise_add_residual n hn x)
    _ = (n : ℝ) *
        ((2 / (n : ℝ)) ^ 2 * ((n : ℝ) / 3) +
          (2 * (2 / (n : ℝ)) * (n.choose 2 : ℝ)⁻¹) * 0 +
          ((n.choose 2 : ℝ)⁻¹) ^ 2 * ((n.choose 2 : ℝ) *
            (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
              ∂(fixedErasedLaw j).prod (fixedErasedLaw j)))) := by
      rw [integral_linear_sq _ _ _ (noise_sum_memLp_two j n)
        (fixedErasedResidualPairSum_memLp_two j n), integral_noise_sum_sq,
        integral_noise_sum_mul_pair, integral_fixedErasedResidualPairSum_sq]
    _ = _ := by
      rw [← Shao.OQ5.P35.pairCount_eq_choose n]
      unfold Shao.OQ5.P35.pairCount
      field_simp [hn0, h1]
      ring

private theorem integral_noise_mul_row (j n : ℕ) (i k : Fin n) :
    (∫ x : Fin n → LayerObs, (x i).1 * fixedErasedResidualRow k x
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) = 0 := by
  classical
  have _hI := (fixedErasedSampleNoise_memLp_two j n i).integrable_mul
    (fixedErasedResidualRow_memLp_two j n k)
  change (∫ x : Fin n → LayerObs,
    (x i).1 * ∑ a ∈ Finset.univ.erase k, fixedResidualKernel (x k, x a)
    ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) = 0
  simp only [Finset.mul_sum]
  rw [integral_finsetSum _ (fun a ha =>
    integrable_fixedErasedSampleNoise_mul_residualEdge j n i k a (Finset.mem_erase.mp ha).1.symm)]
  exact Finset.sum_eq_zero fun a ha =>
    integral_fixedErasedSampleNoise_mul_residualEdge j n i k a (Finset.mem_erase.mp ha).1.symm

private theorem integral_noise_center_energy (j n : ℕ) (hn : 3 ≤ n) :
    (∫ x : Fin n → LayerObs, ∑ i : Fin n,
      (Shao.OQ5.P35.center (fun k => (x k).1) i) ^ 2
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) = ((n : ℝ) - 1) / 3 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hsquares : Integrable (fun x : Fin n → LayerObs => ∑ i : Fin n, (x i).1 ^ 2)
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) :=
    integrable_finsetSum Finset.univ (fun i _ => (fixedErasedSampleNoise_memLp_two j n i).integrable_sq)
  have htotal := (noise_sum_memLp_two j n).integrable_sq
  have _hcenter := integrable_finsetSum Finset.univ (fun i _ =>
    (center_memLp_two _ n (fun k (x : Fin n → LayerObs) => (x k).1) (fixedErasedSampleNoise_memLp_two j n) i).integrable_sq)
  have hdiag : (∫ x : Fin n → LayerObs, ∑ i : Fin n, (x i).1 ^ 2
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) = (n : ℝ) / 3 := by
    rw [integral_finsetSum Finset.univ (fun i _ => (fixedErasedSampleNoise_memLp_two j n i).integrable_sq)]
    calc
      _ = ∑ _i : Fin n, (1 / 3 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        have h := integral_fixedErasedSampleNoise_mul j n i i
        rw [ite_eq_left rfl] at h
        simpa only [pow_two] using h
      _ = _ := by simp [nsmul_eq_mul, div_eq_mul_inv]
  calc
    _ = ∫ x : Fin n → LayerObs, (∑ i : Fin n, (x i).1 ^ 2) -
        (n : ℝ)⁻¹ * (∑ i : Fin n, (x i).1) ^ 2
        ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        simpa only [pow_two, mul_assoc] using
          center_inner_identity n hn0 (fun i => (x i).1) (fun i => (x i).1)
    _ = ((n : ℝ) - 1) / 3 := by
      rw [integral_sub hsquares (htotal.const_mul _), integral_const_mul,
        hdiag, integral_noise_sum_sq]
      field_simp [hn0]

private theorem integral_row_center_energy (j n : ℕ) (hn : 3 ≤ n) :
    (∫ x : Fin n → LayerObs, ∑ i : Fin n,
      (Shao.OQ5.P35.center (fun k => fixedErasedResidualRow k x) i) ^ 2
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) =
      ((n : ℝ) - 1) * ((n : ℝ) - 2) *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂(fixedErasedLaw j).prod (fixedErasedLaw j)) := by
  have h := integral_fixedErasedResidualCenteredRows_sq j n hn
  rw [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega)] at h
  norm_num only [Nat.cast_one, Nat.cast_ofNat] at h
  simpa only [Shao.OQ5.P35.center, Shao.OQ5.P35.mean] using h

theorem integral_fixedSampleStudentizerSq_fixedErasedLaw
    (j n : ℕ) (hn : 3 ≤ n) :
    (∫ x : Fin n → LayerObs, fixedSampleStudentizerSq x
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) =
      (4 / 3 : ℝ) + (4 / ((n : ℝ) - 2)) *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂(fixedErasedLaw j).prod (fixedErasedLaw j)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have h1 : (n : ℝ) - 1 ≠ 0 := by
    have h : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    exact sub_ne_zero.mpr (ne_of_gt h)
  have h2 : (n : ℝ) - 2 ≠ 0 := by
    have h : (2 : ℝ) < n := by exact_mod_cast (show 2 < n by omega)
    exact sub_ne_zero.mpr (ne_of_gt h)
  have _hI := integrable_fixedSampleStudentizerSq_fixedErasedLaw j n hn
  have hz := integral_center_cross_zero
    (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) n hn0
    (fun i (x : Fin n → LayerObs) => (x i).1) (fun i (x : Fin n → LayerObs) => fixedErasedResidualRow i x)
    (fixedErasedSampleNoise_memLp_two j n) (fixedErasedResidualRow_memLp_two j n)
    (integral_noise_mul_row j n)
  calc
    _ = (4 / ((n : ℝ) - 1)) * (∫ x : Fin n → LayerObs, ∑ i : Fin n,
        (Shao.OQ5.P35.center
          (fun k => (x k).1 + fixedErasedResidualRow k x * (((n : ℝ) - 2)⁻¹)) i) ^ 2
        ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simpa only [div_eq_mul_inv] using fixedSampleStudentizerSq_eq_centered_residual_rows n hn x
    _ = (4 / ((n : ℝ) - 1)) *
        (((n : ℝ) - 1) / 3 + (2 * (((n : ℝ) - 2)⁻¹)) * 0 +
          ((((n : ℝ) - 2)⁻¹) ^ 2) * (((n : ℝ) - 1) * ((n : ℝ) - 2) *
            (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
              ∂(fixedErasedLaw j).prod (fixedErasedLaw j)))) := by
      rw [integral_center_energy_add_mul _ n (fun i (x : Fin n → LayerObs) => (x i).1)
        (fun i (x : Fin n → LayerObs) => fixedErasedResidualRow i x)
        (fixedErasedSampleNoise_memLp_two j n) (fixedErasedResidualRow_memLp_two j n),
        integral_noise_center_energy j n hn, hz, integral_row_center_energy j n hn]
    _ = _ := by
      field_simp [h1, h2]
      ring

end
end Shao.OQ5.P52
