import Shao.Probability.QuadraticChordMoments
import Shao.Probability.SourceScalarNoise
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Moments.Variance

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable def quadraticChordFamilyLaw (ν : Measure ℝ) :
    Measure (Fin 8 → ℝ × ℝ) := Measure.pi (fun _ => quadraticChordLaw ν)

noncomputable def quadraticNoiseInputLaw (ν : Measure ℝ) :
    Measure (((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) × ℝ) :=
  ((quadraticChordFamilyLaw ν).prod (quadraticChordFamilyLaw ν)).prod sourceScalarLaw

noncomputable def quadraticFullNoiseMap (ν : Measure ℝ)
    (p : ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) × ℝ) : ℝ × ℝ :=
  let gamma := (∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν
  ((∑ j : Fin 8, (p.1.1 j).1) - (∑ j : Fin 8, (p.1.2 j).1) + gamma * p.2,
   (∑ j : Fin 8, (p.1.1 j).2) + (∑ j : Fin 8, (p.1.2 j).2))

noncomputable def quadraticFullNoiseLaw (ν : Measure ℝ) : Measure (ℝ × ℝ) :=
  Measure.map (quadraticFullNoiseMap ν) (quadraticNoiseInputLaw ν)

noncomputable def quadraticFullNoiseChar (ν : Measure ℝ) (u v : ℝ) : ℂ :=
  ∫ z : ℝ × ℝ, Complex.exp
    (((u * z.1 + v * z.2 : ℝ) : ℂ) * Complex.I) ∂quadraticFullNoiseLaw ν

private lemma full_map_measurable (ν : Measure ℝ) : Measurable (quadraticFullNoiseMap ν) := by
  unfold quadraticFullNoiseMap
  fun_prop

theorem quadraticFullNoise_law_data (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) :
    IsProbabilityMeasure (quadraticChordFamilyLaw ν) ∧
    IsProbabilityMeasure (quadraticNoiseInputLaw ν) ∧
    IsProbabilityMeasure (quadraticFullNoiseLaw ν) ∧
    Measure.map (fun z : ℝ × ℝ => (-z.1, z.2)) (quadraticFullNoiseLaw ν) =
      quadraticFullNoiseLaw ν := by
  obtain ⟨_, hc, _, _⟩ := quadraticChord_law_data ν h3 hV h hh hs
  let := hc
  let := sourceScalarLaw_data.1
  have hf : IsProbabilityMeasure (quadraticChordFamilyLaw ν) := by
    unfold quadraticChordFamilyLaw
    infer_instance
  let := hf
  have hi : IsProbabilityMeasure (quadraticNoiseInputLaw ν) := by
    unfold quadraticNoiseInputLaw
    infer_instance
  let := hi
  have hl : IsProbabilityMeasure (quadraticFullNoiseLaw ν) := by
    unfold quadraticFullNoiseLaw
    exact (Measure.isProbabilityMeasure_map_iff (full_map_measurable ν).aemeasurable).mpr inferInstance
  refine ⟨hf, hi, hl, ?_⟩
  let R : ℝ × ℝ → ℝ × ℝ := fun z => (-z.1, z.2)
  let T : ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) × ℝ →
      ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) × ℝ :=
    fun p => ((p.1.2, p.1.1), -p.2)
  have ht : MeasurePreserving T (quadraticNoiseInputLaw ν) (quadraticNoiseInputLaw ν) := by
    exact (Measure.measurePreserving_swap (μ := quadraticChordFamilyLaw ν)
      (ν := quadraticChordFamilyLaw ν)).prod
      (⟨measurable_neg, sourceScalarLaw_data.2.1⟩ :
        MeasurePreserving (fun t : ℝ => -t) sourceScalarLaw sourceScalarLaw)
  have he : R ∘ quadraticFullNoiseMap ν = quadraticFullNoiseMap ν ∘ T := by
    funext p
    dsimp [R, T, quadraticFullNoiseMap, Function.comp_def]
    apply Prod.ext <;> ring
  change Measure.map R (Measure.map (quadraticFullNoiseMap ν) (quadraticNoiseInputLaw ν)) =
    Measure.map (quadraticFullNoiseMap ν) (quadraticNoiseInputLaw ν)
  rw [Measure.map_map (by fun_prop) (full_map_measurable ν), he,
    ← Measure.map_map (full_map_measurable ν) ht.measurable, ht.map_eq]

private noncomputable def familyPhase (u v : ℝ) (p : Fin 8 → ℝ × ℝ) : ℂ :=
  Complex.exp (((u * (∑ j : Fin 8, (p j).1) + v * (∑ j : Fin 8, (p j).2) : ℝ) : ℂ) * Complex.I)

private lemma family_phase_product (u v : ℝ) (p : Fin 8 → ℝ × ℝ) :
    familyPhase u v p = ∏ j : Fin 8,
      Complex.exp (((u * (p j).1 + v * (p j).2 : ℝ) : ℂ) * Complex.I) := by
  unfold familyPhase
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  ring_nf
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma family_phase_integral (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) (u v : ℝ) :
    (∫ p : Fin 8 → ℝ × ℝ, familyPhase u v p ∂quadraticChordFamilyLaw ν) =
      quadraticChordChar ν u v ^ 8 := by
  obtain ⟨_, hc, _, _⟩ := quadraticChord_law_data ν h3 hV h hh hs
  let := hc
  simp_rw [family_phase_product]
  unfold quadraticChordFamilyLaw quadraticChordChar
  simpa only [Fintype.card_fin] using
    (integral_fintype_prod_eq_pow (ι := Fin 8) (μ := quadraticChordLaw ν)
      (fun z : ℝ × ℝ => Complex.exp (((u * z.1 + v * z.2 : ℝ) : ℂ) * Complex.I)))

private lemma full_phase_product (ν : Measure ℝ) (u v : ℝ)
    (p : ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) × ℝ) :
    Complex.exp (((u * (quadraticFullNoiseMap ν p).1 + v * (quadraticFullNoiseMap ν p).2 : ℝ) : ℂ) * Complex.I) =
      (familyPhase u v p.1.1 * familyPhase (-u) v p.1.2) *
        Complex.exp (((((∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν) * u * p.2 : ℝ) : ℂ) * Complex.I) := by
  unfold familyPhase quadraticFullNoiseMap
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem quadraticFullNoiseChar_product (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) (u v : ℝ) :
    let gamma := (∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν
    quadraticFullNoiseChar ν u v =
      quadraticChordChar ν u v ^ 8 * quadraticChordChar ν (-u) v ^ 8 *
        sourceScalarChar (gamma * u) ∧
    quadraticFullNoiseChar ν (-u) v = quadraticFullNoiseChar ν u v ∧
    (quadraticFullNoiseChar ν u v).im = 0 ∧
    ‖quadraticFullNoiseChar ν u v‖ ≤ 1 := by
  let gamma := (∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν
  obtain ⟨hf, hi, hl, hr⟩ := quadraticFullNoise_law_data ν h3 hV h hh hs
  let := hf
  let := hi
  let := hl
  let := sourceScalarLaw_data.1
  have hprod : quadraticFullNoiseChar ν u v =
      quadraticChordChar ν u v ^ 8 * quadraticChordChar ν (-u) v ^ 8 *
        sourceScalarChar (gamma * u) := by
    unfold quadraticFullNoiseChar quadraticFullNoiseLaw
    rw [integral_map (full_map_measurable ν).aemeasurable (by fun_prop)]
    simp_rw [full_phase_product]
    unfold quadraticNoiseInputLaw
    rw [integral_prod_mul
      (fun p : (Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ) => familyPhase u v p.1 * familyPhase (-u) v p.2)
      (fun t : ℝ => Complex.exp ((((gamma * u * t : ℝ) : ℂ)) * Complex.I)),
      integral_prod_mul (familyPhase u v) (familyPhase (-u) v),
      family_phase_integral ν h3 hV h hh hs u v,
      family_phase_integral ν h3 hV h hh hs (-u) v]
    rfl
  have heven : quadraticFullNoiseChar ν (-u) v = quadraticFullNoiseChar ν u v := by
    unfold quadraticFullNoiseChar
    calc
      _ = ∫ z : ℝ × ℝ, Complex.exp
          (((u * (-z.1) + v * z.2 : ℝ) : ℂ) * Complex.I) ∂quadraticFullNoiseLaw ν := by
        apply integral_congr_ae
        filter_upwards [] with z
        congr 2
        push_cast
        ring
      _ = ∫ z : ℝ × ℝ, Complex.exp
          (((u * z.1 + v * z.2 : ℝ) : ℂ) * Complex.I)
          ∂Measure.map (fun z : ℝ × ℝ => (-z.1, z.2)) (quadraticFullNoiseLaw ν) :=
        (integral_map (φ := fun z : ℝ × ℝ => (-z.1, z.2))
          (f := fun z : ℝ × ℝ => Complex.exp (((u * z.1 + v * z.2 : ℝ) : ℂ) * Complex.I))
          (by fun_prop) (by fun_prop)).symm
      _ = _ := by rw [hr]
  have hkim := (quadraticChordChar_exact ν h3 hV u v).2.2.1
  have hkmim := (quadraticChordChar_exact ν h3 hV (-u) v).2.2.1
  have hsim := (sourceScalarChar_even_bound (gamma * u)).2.1
  have hk : quadraticChordChar ν u v = ((quadraticChordChar ν u v).re : ℂ) := by
    apply Complex.ext <;> simp [hkim]
  have hkm : quadraticChordChar ν (-u) v = ((quadraticChordChar ν (-u) v).re : ℂ) := by
    apply Complex.ext <;> simp [hkmim]
  have hsc : sourceScalarChar (gamma * u) = ((sourceScalarChar (gamma * u)).re : ℂ) := by
    apply Complex.ext <;> simp [hsim]
  refine ⟨hprod, heven, ?_, ?_⟩
  · rw [hprod, hk, hkm, hsc]
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_im]
  · unfold quadraticFullNoiseChar
    simpa using norm_integral_le_of_norm_le
      (integrable_const (μ := quadraticFullNoiseLaw ν) (1 : ℝ))
      (Filter.Eventually.of_forall fun z : ℝ × ℝ => by simp [Complex.norm_exp, Complex.mul_re])

private noncomputable def familyZ (p : Fin 8 → ℝ × ℝ) : ℝ := ∑ j : Fin 8, (p j).1

private noncomputable def familyAbsZ (p : Fin 8 → ℝ × ℝ) : ℝ := ∑ j : Fin 8, |(p j).1|

private noncomputable def familyAbsY (p : Fin 8 → ℝ × ℝ) : ℝ := ∑ j : Fin 8, |(p j).2|

private lemma integral_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α → ℝ) (hf : Integrable f μ) :
    (∫ p : α × β, f p.1 ∂μ.prod ν) = ∫ x, f x ∂μ := by
  rw [integral_prod _ (hf.comp_fst ν)]
  simp

private lemma integral_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : β → ℝ) (hf : Integrable f ν) :
    (∫ p : α × β, f p.2 ∂μ.prod ν) = ∫ x, f x ∂ν := by
  rw [integral_prod _ (hf.comp_snd μ)]
  simp

private lemma family_sum_data (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (f : ℝ × ℝ → ℝ) (hf : Integrable f μ) :
    Integrable (fun p : Fin 8 → ℝ × ℝ => ∑ j : Fin 8, f (p j)) (Measure.pi (fun _ => μ)) ∧
    (∫ p : Fin 8 → ℝ × ℝ, ∑ j : Fin 8, f (p j) ∂Measure.pi (fun _ => μ)) =
      8 * (∫ z : ℝ × ℝ, f z ∂μ) := by
  have hi (j : Fin 8) : Integrable (fun p : Fin 8 → ℝ × ℝ => f (p j)) (Measure.pi (fun _ => μ)) :=
    (measurePreserving_eval (fun _ : Fin 8 => μ) j).integrable_comp_of_integrable hf
  have he (j : Fin 8) :
      (∫ p : Fin 8 → ℝ × ℝ, f (p j) ∂Measure.pi (fun _ => μ)) = ∫ z, f z ∂μ := by
    have hm := (measurePreserving_eval (fun _ : Fin 8 => μ) j).map_eq
    calc
      _ = ∫ z, f z ∂Measure.map (fun p : Fin 8 → ℝ × ℝ => p j) (Measure.pi (fun _ => μ)) :=
        (integral_map (φ := fun p : Fin 8 → ℝ × ℝ => p j) (f := f)
          (measurable_pi_apply j).aemeasurable (by rw [hm]; exact hf.aestronglyMeasurable)).symm
      _ = _ := by rw [hm]
  refine ⟨integrable_finsetSum _ (fun j _ => hi j), ?_⟩
  rw [integral_finsetSum _ (fun j _ => hi j)]
  norm_num [he]

private lemma family_centered_second (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hi : Integrable (fun z : ℝ × ℝ => z.1) μ)
    (hsq : Integrable (fun z : ℝ × ℝ => z.1 ^ 2) μ)
    (hm : (∫ z : ℝ × ℝ, z.1 ∂μ) = 0) :
    MemLp familyZ 2 (Measure.pi (fun _ : Fin 8 => μ)) ∧
    (∫ p : Fin 8 → ℝ × ℝ, familyZ p ∂Measure.pi (fun _ => μ)) = 0 ∧
    (∫ p : Fin 8 → ℝ × ℝ, familyZ p ^ 2 ∂Measure.pi (fun _ => μ)) =
      8 * (∫ z : ℝ × ℝ, z.1 ^ 2 ∂μ) := by
  have h2 : MemLp (fun z : ℝ × ℝ => z.1) 2 μ :=
    (memLp_two_iff_integrable_sq measurable_fst.aestronglyMeasurable).mpr hsq
  have hsum : MemLp familyZ 2 (Measure.pi (fun _ : Fin 8 => μ)) := by
    exact memLp_finsetSum Finset.univ
      (fun j _ => h2.comp_measurePreserving (measurePreserving_eval (fun _ : Fin 8 => μ) j))
  have hmean : (∫ p : Fin 8 → ℝ × ℝ, familyZ p ∂Measure.pi (fun _ => μ)) = 0 := by
    simpa only [familyZ, hm, mul_zero] using (family_sum_data μ (fun z => z.1) hi).2
  have hv : variance familyZ (Measure.pi (fun _ : Fin 8 => μ)) =
      8 * variance (fun z : ℝ × ℝ => z.1) μ := by
    have he : (∑ j : Fin 8, fun p : Fin 8 → ℝ × ℝ => (p j).1) = familyZ := by
      funext p
      simp [familyZ]
    have hv := variance_sum_pi (X := fun _ : Fin 8 => fun z : ℝ × ℝ => z.1) (fun _ => h2)
    rw [he] at hv
    simpa using hv
  rw [variance_eq_sub hsum, variance_eq_sub h2] at hv
  simp only [Pi.pow_apply, hmean, hm, zero_pow (by norm_num : 2 ≠ 0), sub_zero] at hv
  exact ⟨hsum, hmean, hv⟩

private lemma centered_product_sum {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α → ℝ) (g : β → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 ν)
    (hfm : (∫ x, f x ∂μ) = 0) (hgm : (∫ y, g y ∂ν) = 0) :
    MemLp (fun p : α × β => f p.1 + g p.2) 2 (μ.prod ν) ∧
    (∫ p : α × β, f p.1 + g p.2 ∂μ.prod ν) = 0 ∧
    (∫ p : α × β, (f p.1 + g p.2) ^ 2 ∂μ.prod ν) =
      (∫ x, f x ^ 2 ∂μ) + (∫ y, g y ^ 2 ∂ν) := by
  have hi := hf.integrable (by norm_num)
  have hj := hg.integrable (by norm_num)
  have hsum : MemLp (fun p : α × β => f p.1 + g p.2) 2 (μ.prod ν) :=
    (hf.comp_fst ν).add (hg.comp_snd μ)
  have hm : (∫ p : α × β, f p.1 + g p.2 ∂μ.prod ν) = 0 := by
    rw [integral_add (hi.comp_fst ν) (hj.comp_snd μ), integral_fst μ ν f hi,
      integral_snd μ ν g hj, hfm, hgm, add_zero]
  have hv := variance_add_prod hf hg
  rw [variance_eq_sub hsum, variance_eq_sub hf, variance_eq_sub hg] at hv
  simp only [Pi.pow_apply, hm, hfm, hgm, zero_pow (by norm_num : 2 ≠ 0), sub_zero] at hv
  exact ⟨hsum, hm, hv⟩

private lemma sum_abs_first (p : Fin 8 → ℝ × ℝ) : |familyZ p| ≤ familyAbsZ p := by
  simpa only [familyZ, familyAbsZ, Real.norm_eq_abs] using
    (norm_sum_le (s := Finset.univ) (f := fun j : Fin 8 => (p j).1))

theorem quadraticFullNoise_support_moments (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (hgamma : (∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν ≤ 2 * h) :
    let gamma := (∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν
    let law := quadraticFullNoiseLaw ν
    (∀ᵐ z : ℝ × ℝ ∂law, |z.1| ≤ 34 * h ∧ |z.2| ≤ 64 * h ^ 2) ∧
    Integrable (fun z : ℝ × ℝ => |z.1|) law ∧
    Integrable (fun z : ℝ × ℝ => |z.2|) law ∧
    Integrable (fun z : ℝ × ℝ => z.1 ^ 2) law ∧
    (∫ z : ℝ × ℝ, |z.1| ∂law) ≤ (67 / 3 : ℝ) * gamma ∧
    (∫ z : ℝ × ℝ, |z.2| ∂law) ≤ (128 / 3 : ℝ) * h * gamma ∧
    (∫ z : ℝ × ℝ, z.1 ^ 2 ∂law) =
      16 * (∫ z : ℝ × ℝ, z.1 ^ 2 ∂quadraticChordLaw ν) +
        gamma ^ 2 * (∫ t : ℝ, t ^ 2 ∂sourceScalarLaw) ∧
    (∫ z : ℝ × ℝ, z.1 ^ 2 ∂law) ≤ (70 / 3 : ℝ) * h * gamma := by
  let gamma := (∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν
  let M := quadraticChordFamilyLaw ν
  let P := M.prod M
  let L := quadraticNoiseInputLaw ν
  let law := quadraticFullNoiseLaw ν
  have hg0 : 0 ≤ gamma := div_nonneg (integral_nonneg (fun a => by positivity)) hV.le
  obtain ⟨hf, hi, hl, _⟩ := quadraticFullNoise_law_data ν h3 hV h hh hs
  let := hf
  let := hi
  let := hl
  obtain ⟨_, hc, hcs, _⟩ := quadraticChord_law_data ν h3 hV h hh hs
  let := hc
  obtain ⟨hsp, _, hss, hsi, hsia, hsisq, hsm, hsma, hsmsq⟩ := sourceScalarLaw_data
  let := hsp
  obtain ⟨hci, hcia, hcisq, hciya, hcm, _, _, hcma, hcmya, hcmsq⟩ :=
    quadraticChord_moments ν h3 hV h hh hs
  have hsumZ : ∀ p : Fin 8 → ℝ × ℝ, |familyZ p| ≤ familyAbsZ p := sum_abs_first
  have hsumY (p : Fin 8 → ℝ × ℝ) : |∑ j : Fin 8, (p j).2| ≤ familyAbsY p := by
    simpa only [familyAbsY, Real.norm_eq_abs] using
      (norm_sum_le (s := Finset.univ) (f := fun j : Fin 8 => (p j).2))
  have hfamily : ∀ᵐ p : Fin 8 → ℝ × ℝ ∂M,
      ∀ j : Fin 8, |(p j).1| ≤ 2 * h ∧ |(p j).2| ≤ 2 * h * |(p j).1| := by
    rw [ae_all_iff]
    intro j
    exact (measurePreserving_eval (fun _ : Fin 8 => quadraticChordLaw ν) j).quasiMeasurePreserving.ae hcs
  have hfamilyB (p : Fin 8 → ℝ × ℝ)
      (hp : ∀ j : Fin 8, |(p j).1| ≤ 2 * h ∧ |(p j).2| ≤ 2 * h * |(p j).1|) :
      familyAbsZ p ≤ 16 * h ∧ familyAbsY p ≤ 32 * h ^ 2 := by
    constructor
    · calc
        _ ≤ ∑ j : Fin 8, 2 * h := Finset.sum_le_sum (fun j _ => (hp j).1)
        _ = _ := by simp; ring
    · have hy (j : Fin 8) : |(p j).2| ≤ 4 * h ^ 2 := by
        have hm := mul_le_mul_of_nonneg_left (hp j).1 (show 0 ≤ 2 * h by positivity)
        nlinarith only [hm, (hp j).2]
      calc
        _ ≤ ∑ _j : Fin 8, 4 * h ^ 2 := Finset.sum_le_sum (fun j _ => hy j)
        _ = _ := by simp; ring
  have hp : ∀ᵐ p : (Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ) ∂P,
      (∀ j, |(p.1 j).1| ≤ 2 * h ∧ |(p.1 j).2| ≤ 2 * h * |(p.1 j).1|) ∧
      (∀ j, |(p.2 j).1| ≤ 2 * h ∧ |(p.2 j).2| ≤ 2 * h * |(p.2 j).1|) :=
    (measurePreserving_fst.quasiMeasurePreserving.ae hfamily).and
      (measurePreserving_snd.quasiMeasurePreserving.ae hfamily)
  have hinput : ∀ᵐ p : ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) × ℝ ∂L,
      ((∀ j, |(p.1.1 j).1| ≤ 2 * h ∧ |(p.1.1 j).2| ≤ 2 * h * |(p.1.1 j).1|) ∧
       (∀ j, |(p.1.2 j).1| ≤ 2 * h ∧ |(p.1.2 j).2| ≤ 2 * h * |(p.1.2 j).1|)) ∧ |p.2| ≤ 1 :=
    (measurePreserving_fst.quasiMeasurePreserving.ae hp).and
      (measurePreserving_snd.quasiMeasurePreserving.ae hss)
  have hzpoint (p : ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) × ℝ) :
      |(quadraticFullNoiseMap ν p).1| ≤
        (familyAbsZ p.1.1 + familyAbsZ p.1.2) + gamma * |p.2| := by
    change |familyZ p.1.1 - familyZ p.1.2 + gamma * p.2| ≤ _
    calc
      _ ≤ |familyZ p.1.1 - familyZ p.1.2| + |gamma * p.2| := abs_add_le _ _
      _ ≤ |familyZ p.1.1| + |familyZ p.1.2| + gamma * |p.2| := by
        rw [abs_mul, abs_of_nonneg hg0]
        linarith only [abs_sub (familyZ p.1.1) (familyZ p.1.2)]
      _ ≤ _ := by linarith only [hsumZ p.1.1, hsumZ p.1.2]
  have hypoint (p : ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) × ℝ) :
      |(quadraticFullNoiseMap ν p).2| ≤ familyAbsY p.1.1 + familyAbsY p.1.2 := by
    change |(∑ j : Fin 8, (p.1.1 j).2) + (∑ j : Fin 8, (p.1.2 j).2)| ≤ _
    exact (abs_add_le _ _).trans (add_le_add (hsumY p.1.1) (hsumY p.1.2))
  have hsupport : ∀ᵐ z : ℝ × ℝ ∂law, |z.1| ≤ 34 * h ∧ |z.2| ≤ 64 * h ^ 2 := by
    apply (ae_map_iff (full_map_measurable ν).aemeasurable (by measurability)).mpr
    filter_upwards [hinput] with p hp
    obtain ⟨hz1, hy1⟩ := hfamilyB p.1.1 hp.1.1
    obtain ⟨hz2, hy2⟩ := hfamilyB p.1.2 hp.1.2
    have ht := mul_le_mul_of_nonneg_left hp.2 hg0
    constructor
    · nlinarith only [hzpoint p, hz1, hz2, ht, hgamma]
    · linarith only [hypoint p, hy1, hy2]
  have hza : Integrable (fun z : ℝ × ℝ => |z.1|) law := by
    refine (integrable_const (34 * h)).mono' (by fun_prop) ?_
    simpa only [Real.norm_eq_abs, abs_abs] using hsupport.mono (fun _ hz => hz.1)
  have hya : Integrable (fun z : ℝ × ℝ => |z.2|) law := by
    refine (integrable_const (64 * h ^ 2)).mono' (by fun_prop) ?_
    simpa only [Real.norm_eq_abs, abs_abs] using hsupport.mono (fun _ hz => hz.2)
  have hzs : Integrable (fun z : ℝ × ℝ => z.1 ^ 2) law := by
    refine (integrable_const ((34 * h) ^ 2)).mono' (by fun_prop) ?_
    filter_upwards [hsupport] with z hz
    simpa only [Real.norm_eq_abs, abs_pow] using pow_le_pow_left₀ (abs_nonneg z.1) hz.1 2
  have hGA := (family_sum_data (quadraticChordLaw ν) (fun z => |z.1|) hcia).1
  have hHA := (family_sum_data (quadraticChordLaw ν) (fun z => |z.2|) hciya).1
  have eGA := (family_sum_data (quadraticChordLaw ν) (fun z => |z.1|) hcia).2
  have eHA := (family_sum_data (quadraticChordLaw ν) (fun z => |z.2|) hciya).2
  change Integrable familyAbsZ M at hGA
  change Integrable familyAbsY M at hHA
  change (∫ p, familyAbsZ p ∂M) = _ at eGA
  change (∫ p, familyAbsY p ∂M) = _ at eHA
  have hGAb : Integrable (fun p : (Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ) =>
      familyAbsZ p.1 + familyAbsZ p.2) P := (hGA.comp_fst M).add (hGA.comp_snd M)
  have hHAb : Integrable (fun p : (Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ) =>
      familyAbsY p.1 + familyAbsY p.2) P := (hHA.comp_fst M).add (hHA.comp_snd M)
  have hdomZ : Integrable (fun p : ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) × ℝ =>
      (familyAbsZ p.1.1 + familyAbsZ p.1.2) + gamma * |p.2|) L :=
    (hGAb.comp_fst sourceScalarLaw).add ((hsia.const_mul gamma).comp_snd P)
  have hdomY : Integrable (fun p : ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) × ℝ =>
      familyAbsY p.1.1 + familyAbsY p.1.2) L := hHAb.comp_fst sourceScalarLaw
  have mp : MeasurePreserving (quadraticFullNoiseMap ν) L law := ⟨full_map_measurable ν, rfl⟩
  have hzbound : (∫ z : ℝ × ℝ, |z.1| ∂law) ≤ (67 / 3 : ℝ) * gamma := by
    have hm := integral_mono (mp.integrable_comp_of_integrable hza) hdomZ hzpoint
    have he : (∫ p : ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) × ℝ,
        |(quadraticFullNoiseMap ν p).1| ∂L) = ∫ z : ℝ × ℝ, |z.1| ∂law := by
      exact (integral_map (μ := L) (φ := quadraticFullNoiseMap ν)
        (f := fun z : ℝ × ℝ => |z.1|) (full_map_measurable ν).aemeasurable (by fun_prop)).symm
    dsimp only [Function.comp_def] at hm
    rw [he] at hm
    change _ ≤ (∫ p : ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) × ℝ,
      (familyAbsZ p.1.1 + familyAbsZ p.1.2) + gamma * |p.2| ∂P.prod sourceScalarLaw) at hm
    rw [integral_add (hGAb.comp_fst sourceScalarLaw) ((hsia.const_mul gamma).comp_snd P),
      integral_fst P sourceScalarLaw _ hGAb, integral_snd P sourceScalarLaw _ (hsia.const_mul gamma),
      integral_const_mul] at hm
    change _ ≤ (∫ p : (Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ),
      familyAbsZ p.1 + familyAbsZ p.2 ∂M.prod M) + gamma * (∫ t : ℝ, |t| ∂sourceScalarLaw) at hm
    rw [integral_add (hGA.comp_fst M) (hGA.comp_snd M), integral_fst M M _ hGA,
      integral_snd M M _ hGA, eGA] at hm
    have ht := mul_le_mul_of_nonneg_left hsma hg0
    nlinarith only [hm, ht, hcma]
  have hybound : (∫ z : ℝ × ℝ, |z.2| ∂law) ≤ (128 / 3 : ℝ) * h * gamma := by
    have hm := integral_mono (mp.integrable_comp_of_integrable hya) hdomY hypoint
    have he : (∫ p : ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) × ℝ,
        |(quadraticFullNoiseMap ν p).2| ∂L) = ∫ z : ℝ × ℝ, |z.2| ∂law := by
      exact (integral_map (μ := L) (φ := quadraticFullNoiseMap ν)
        (f := fun z : ℝ × ℝ => |z.2|) (full_map_measurable ν).aemeasurable (by fun_prop)).symm
    dsimp only [Function.comp_def] at hm
    rw [he] at hm
    change _ ≤ (∫ p : ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) × ℝ,
      familyAbsY p.1.1 + familyAbsY p.1.2 ∂P.prod sourceScalarLaw) at hm
    rw [integral_fst P sourceScalarLaw _ hHAb] at hm
    change _ ≤ (∫ p : (Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ),
      familyAbsY p.1 + familyAbsY p.2 ∂M.prod M) at hm
    rw [integral_add (hHA.comp_fst M) (hHA.comp_snd M), integral_fst M M _ hHA,
      integral_snd M M _ hHA, eHA] at hm
    nlinarith only [hm, hcmya]
  obtain ⟨hG2, hGm, hGs⟩ := family_centered_second (quadraticChordLaw ν) hci hcisq hcm
  change MemLp familyZ 2 M at hG2
  change (∫ p, familyZ p ∂M) = 0 at hGm
  change (∫ p, familyZ p ^ 2 ∂M) = _ at hGs
  let F : (Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ) → ℝ :=
    fun p => familyZ p.1 + (-familyZ p.2)
  obtain ⟨hF2, hFm, hFs⟩ := centered_product_sum M M familyZ (fun p => -familyZ p)
    hG2 hG2.neg hGm (by rw [integral_neg, hGm, neg_zero])
  have hS2 : MemLp (fun t : ℝ => t) 2 sourceScalarLaw :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr hsisq
  have hSm : (∫ t : ℝ, gamma * t ∂sourceScalarLaw) = 0 := by
    rw [integral_const_mul, hsm, mul_zero]
  obtain ⟨_, _, hfullsq⟩ := centered_product_sum P sourceScalarLaw F (fun t => gamma * t)
    hF2 (hS2.const_mul gamma) hFm hSm
  have heSecond : (∫ z : ℝ × ℝ, z.1 ^ 2 ∂law) =
      16 * (∫ z : ℝ × ℝ, z.1 ^ 2 ∂quadraticChordLaw ν) +
        gamma ^ 2 * (∫ t : ℝ, t ^ 2 ∂sourceScalarLaw) := by
    have he : (∫ z : ℝ × ℝ, z.1 ^ 2 ∂law) =
        ∫ p : ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) × ℝ,
          (F p.1 + gamma * p.2) ^ 2 ∂L := by
      unfold law quadraticFullNoiseLaw
      rw [integral_map (full_map_measurable ν).aemeasurable (by fun_prop)]
      rfl
    rw [he]
    change (∫ p : ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) × ℝ,
      (F p.1 + gamma * p.2) ^ 2 ∂P.prod sourceScalarLaw) = _
    rw [hfullsq]
    change (∫ p : (Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ), F p ^ 2 ∂M.prod M) +
      (∫ t : ℝ, (gamma * t) ^ 2 ∂sourceScalarLaw) = _
    rw [hFs]
    simp only [neg_sq, hGs, mul_pow, integral_const_mul]
    ring
  have hsecondbound : (∫ z : ℝ × ℝ, z.1 ^ 2 ∂law) ≤ (70 / 3 : ℝ) * h * gamma := by
    rw [heSecond]
    have ht := mul_le_mul_of_nonneg_left hsmsq (sq_nonneg gamma)
    have hg := mul_le_mul_of_nonneg_right hgamma hg0
    nlinarith only [ht, hg, hcmsq]
  exact ⟨hsupport, hza, hya, hzs, hzbound, hybound, heSecond, hsecondbound⟩

theorem quadraticFullNoise_independent_sample (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    IndepFun (fun p : Ω × (ℝ × ℝ) => p.1) (fun p => p.2)
      (μ.prod (quadraticFullNoiseLaw ν)) ∧
    Measure.map (fun p : Ω × (ℝ × ℝ) => p.1) (μ.prod (quadraticFullNoiseLaw ν)) = μ ∧
    Measure.map (fun p : Ω × (ℝ × ℝ) => p.2) (μ.prod (quadraticFullNoiseLaw ν)) =
      quadraticFullNoiseLaw ν := by
  let := (quadraticFullNoise_law_data ν h3 hV h hh hs).2.2.1
  refine ⟨indepFun_prod measurable_id measurable_id, ?_, ?_⟩
  · simp only [Measure.map_fst_prod, measure_univ, one_smul]
  · simp only [Measure.map_snd_prod, measure_univ, one_smul]

end Shao.Probability
