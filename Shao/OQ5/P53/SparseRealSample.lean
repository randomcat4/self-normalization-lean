import Shao.OQ5.P53.SparseRealEncoding
import Mathlib.Probability.Independence.InfinitePi

/-!
# The actual fixed infinite real iid sample for p53

Source: current/oq56/inputs02/p53.md, especially sections 1 and 3.
Both entire sample laws are fixed once alpha, x and N are fixed, before any
actual sample size. Coordinatewise encoding and decoding transport the full
sample laws. Reconstruction is only almost everywhere on these actual laws.

The true studentizer, balanced events, conditional estimates and original
tail conclusions remain separate obligations.
-/

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace Shao.OQ5.P53

def sparsePopulationSampleMeasure (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) :
    Measure (ℕ → ((ℝ × (ℕ × Bool)) × (ℕ × Bool))) :=
  Measure.infinitePi (fun _ : ℕ => sparsePopulationMeasure α x N)

def sparseRealSampleMeasure (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) :
    Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => sparseRealMeasure α x N)

def sparseRealSampleCoordinate (i : ℕ) (ω : ℕ → ℝ) : ℝ := ω i

theorem sparsePopulationSampleMeasure_probability :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  IsProbabilityMeasure (sparsePopulationSampleMeasure α x N) := by
  intro α x N
  let : IsProbabilityMeasure (sparsePopulationMeasure α x N) :=
    sparsePopulationMeasure_probability α x N
  unfold sparsePopulationSampleMeasure
  infer_instance

theorem sparseRealSampleMeasure_probability :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  IsProbabilityMeasure (sparseRealSampleMeasure α x N) := by
  intro α x N
  let : IsProbabilityMeasure (sparseRealMeasure α x N) :=
    sparseRealMeasure_probability α x N
  unfold sparseRealSampleMeasure
  infer_instance

theorem measurable_sparseRealSampleCoordinate :
  ∀ (i : ℕ), Measurable (sparseRealSampleCoordinate i) := by
  intro i
  exact measurable_pi_apply i

theorem sparseRealSampleCoordinate_law :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  ∀ (i : ℕ),
  (sparseRealSampleMeasure α x N).map (sparseRealSampleCoordinate i) =
    sparseRealMeasure α x N := by
  intro α x N i
  let : IsProbabilityMeasure (sparseRealMeasure α x N) :=
    sparseRealMeasure_probability α x N
  exact Measure.infinitePi_map_eval (fun _ : ℕ => sparseRealMeasure α x N) i

theorem iIndepFun_sparseRealSampleCoordinate :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  ProbabilityTheory.iIndepFun sparseRealSampleCoordinate (sparseRealSampleMeasure α x N) := by
  intro α x N
  let : IsProbabilityMeasure (sparseRealMeasure α x N) :=
    sparseRealMeasure_probability α x N
  exact ProbabilityTheory.iIndepFun_infinitePi
    (P := fun _ : ℕ => sparseRealMeasure α x N)
    (X := fun _ (y : ℝ) => y) (fun _ => measurable_id)

theorem sparseRealSampleCoordinate_pair_law :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  ∀ (i j : ℕ), i ≠ j →
  (sparseRealSampleMeasure α x N).map
    (fun ω => (sparseRealSampleCoordinate i ω, sparseRealSampleCoordinate j ω)) =
    (sparseRealMeasure α x N).prod (sparseRealMeasure α x N) := by
  intro α x N i j hij
  let : IsProbabilityMeasure (sparseRealMeasure α x N) :=
    sparseRealMeasure_probability α x N
  exact Measure.infinitePi_map_eval_prod
    (P := fun _ : ℕ => sparseRealMeasure α x N) hij

theorem sparseRealSample_prefix_law :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  ∀ (n : ℕ),
  (sparseRealSampleMeasure α x N).map
    (fun ω (i : Fin n) => sparseRealSampleCoordinate i.val ω) =
    Measure.pi (fun _ : Fin n => sparseRealMeasure α x N) := by
  intro α x N n
  have hi : ProbabilityTheory.iIndepFun
      (fun i : Fin n => sparseRealSampleCoordinate i.val)
      (sparseRealSampleMeasure α x N) :=
    ProbabilityTheory.iIndepFun.precomp Fin.val_injective
      (iIndepFun_sparseRealSampleCoordinate α x N)
  simpa only [sparseRealSampleCoordinate_law] using
    ProbabilityTheory.iIndepFun.map_fun_eq_pi_map
      (fun i : Fin n => (measurable_sparseRealSampleCoordinate i.val).aemeasurable) hi

theorem sparsePopulationSample_prefix_law :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  ∀ (n : ℕ),
  (sparsePopulationSampleMeasure α x N).map
    (fun ω (i : Fin n) => ω i.val) =
    Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N) := by
  intro α x N n
  let : IsProbabilityMeasure (sparsePopulationMeasure α x N) :=
    sparsePopulationMeasure_probability α x N
  have hind : ProbabilityTheory.iIndepFun
      (fun i : ℕ => fun ω : ℕ → ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) => ω i)
      (sparsePopulationSampleMeasure α x N) :=
    ProbabilityTheory.iIndepFun_infinitePi
      (P := fun _ : ℕ => sparsePopulationMeasure α x N)
      (X := fun _ (z : (ℝ × (ℕ × Bool)) × (ℕ × Bool)) => z)
      (fun _ => measurable_id)
  have hi : ProbabilityTheory.iIndepFun
      (fun i : Fin n => fun ω : ℕ → ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) => ω i.val)
      (sparsePopulationSampleMeasure α x N) :=
    ProbabilityTheory.iIndepFun.precomp Fin.val_injective hind
  have hcoord (i : ℕ) :
      (sparsePopulationSampleMeasure α x N).map (fun ω => ω i) =
        sparsePopulationMeasure α x N :=
    Measure.infinitePi_map_eval (fun _ : ℕ => sparsePopulationMeasure α x N) i
  simpa only [hcoord] using ProbabilityTheory.iIndepFun.map_fun_eq_pi_map
    (fun i : Fin n => (measurable_pi_apply i.val).aemeasurable) hi

theorem sparsePopulationSample_encode_law :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  (sparsePopulationSampleMeasure α x N).map
    (fun ω : ℕ → ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) =>
      fun i : ℕ => sparsePopulationEncode (ω i)) =
    sparseRealSampleMeasure α x N := by
  intro α x N
  let : IsProbabilityMeasure (sparsePopulationMeasure α x N) :=
    sparsePopulationMeasure_probability α x N
  exact Measure.infinitePi_map_pi (fun _ : ℕ => sparsePopulationMeasure α x N)
    (fun _ => measurable_sparsePopulationEncode)

theorem sparseRealSample_decode_law :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  (sparseRealSampleMeasure α x N).map
    (fun ω : ℕ → ℝ => fun i : ℕ => sparsePopulationDecode (ω i)) =
    sparsePopulationSampleMeasure α x N := by
  intro α x N
  let : IsProbabilityMeasure (sparseRealMeasure α x N) :=
    sparseRealMeasure_probability α x N
  change (Measure.infinitePi (fun _ : ℕ => sparseRealMeasure α x N)).map
    (fun ω : ℕ → ℝ => fun i : ℕ => sparsePopulationDecode (ω i)) =
      Measure.infinitePi (fun _ : ℕ => sparsePopulationMeasure α x N)
  simpa only [sparsePopulationDecode_realMeasure_law] using
    Measure.infinitePi_map_pi (fun _ : ℕ => sparseRealMeasure α x N)
      (fun _ => measurable_sparsePopulationDecode)

theorem sparsePopulationSample_noise_mem_Icc_ae :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  ∀ᵐ ω ∂sparsePopulationSampleMeasure α x N,
    ∀ (i : ℕ), (ω i).1.1 ∈ Set.Icc (-1 : ℝ) 1 := by
  intro α x N
  let : IsProbabilityMeasure (sparsePopulationMeasure α x N) :=
    sparsePopulationMeasure_probability α x N
  rw [ae_all_iff]
  intro i
  have h : ∀ᵐ z ∂(sparsePopulationSampleMeasure α x N).map (fun ω => ω i),
      z.1.1 ∈ Set.Icc (-1 : ℝ) 1 := by
    change ∀ᵐ z ∂(Measure.infinitePi (fun _ : ℕ => sparsePopulationMeasure α x N)).map
      (fun ω => ω i), z.1.1 ∈ Set.Icc (-1 : ℝ) 1
    rw [Measure.infinitePi_map_eval]
    exact sparsePopulation_noise_mem_Icc_ae α x N
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable h

theorem sparsePopulationSample_decode_encode_ae :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  ∀ᵐ ω ∂sparsePopulationSampleMeasure α x N,
    (fun i : ℕ => sparsePopulationDecode (sparsePopulationEncode (ω i))) = ω := by
  intro α x N
  filter_upwards [sparsePopulationSample_noise_mem_Icc_ae α x N] with ω hω
  funext i
  exact sparsePopulationDecode_encode (ω i) (hω i)

theorem sparseRealSample_encode_decode_ae :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  ∀ᵐ ω ∂sparseRealSampleMeasure α x N,
    (fun i : ℕ => sparsePopulationEncode (sparsePopulationDecode (ω i))) = ω := by
  intro α x N
  have h : ∀ᵐ ω ∂sparseRealSampleMeasure α x N,
      ∀ i : ℕ, sparsePopulationEncode (sparsePopulationDecode (ω i)) = ω i := by
    rw [ae_all_iff]
    intro i
    have hi : ∀ᵐ y ∂(sparseRealSampleMeasure α x N).map (sparseRealSampleCoordinate i),
        sparsePopulationEncode (sparsePopulationDecode y) = y := by
      rw [sparseRealSampleCoordinate_law]
      exact sparsePopulationEncode_decode_ae α x N
    exact ae_of_ae_map (measurable_sparseRealSampleCoordinate i).aemeasurable hi
  filter_upwards [h] with ω hω
  exact funext hω

end Shao.OQ5.P53
