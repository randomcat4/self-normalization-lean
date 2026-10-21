import Shao.OQ5.P35.ConditionalBackground
import Shao.OQ5.P35.ConditionalMixture
import Shao.OQ5.P35.SampleStatistics
import Shao.OQ5.P35.TargetCancellation
import Shao.OQ5.P35.FiniteIIDMoments
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Actual conditional numerator signal and variance

Source: original p35 §6, formulas (14)–(17). The sample remains under its
normalized fixed-position or rare-event restriction. The mean retains the
background offset bias, target/background interaction, and background pair
mean. The pair moment calculation uses only the actual marginal L2 bound.
-/

set_option autoImplicit false
set_option maxRecDepth 1600

namespace Shao.OQ5.P35

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

def sampleCenteredNumerator (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  Real.sqrt (n : ℝ) * (sampleU n ω - populationMean)

def conditionalNumeratorMean (j : ℕ) : ℝ :=
  let n : ℝ := rareSampleSize j
  let K : ℝ := targetCategoryCount j
  let m : ℝ := (rareSampleSize j - targetCategoryCount j : ℕ)
  let u : ℝ := ∫ c, categoryFeature c ∂backgroundCategoryLaw j
  let dB : ℝ := ∫ c, categoryOffset c ∂backgroundCategoryLaw j
  Real.sqrt n *
    (K * categoryOffset j / (n - 1) + 2 * m * dB / n -
      2 * K * categoryFeature j * m * u / (n * (n - 1)) -
      m * (m - 1) * u ^ 2 / (n * (n - 1)) - populationMean)

private theorem numerator_measurable (n : ℕ) : Measurable (sampleCenteredNumerator n) :=
  measurable_const.mul ((measurable_sampleU n).sub measurable_const)

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

private theorem pair_square_identity {m : ℕ} (z : Fin m → ℝ) :
    (∑ i, z i)^2 - ∑ i, z i^2 =
      2 * unorderedPairSum (fun i k => z i * z k) := by
  classical
  rw [← offDiagonalSum_eq_two_unordered _ (fun i k => mul_comm (z i) (z k))]
  have hr (i : Fin m) :
      (∑ k ∈ Finset.univ.erase i, z i * z k) = z i * (∑ k, z k) - z i^2 := by
    rw [← Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    ring
  simp_rw [hr]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

private theorem background_pair_compressed {n : ℕ} (J : Finset (Fin n)) (z : Fin n → ℝ) :
    backgroundSum J z ^ 2 - backgroundSqSum J z =
      2 * unorderedPairSum (fun r s : Fin (Finset.univ \ J).card =>
        z (Shao.retainedIndex (Finset.univ \ J) r) *
          z (Shao.retainedIndex (Finset.univ \ J) s)) := by
  classical
  have hq : backgroundSqSum J z =
      ∑ r : Fin (Finset.univ \ J).card, z (Shao.retainedIndex (Finset.univ \ J) r)^2 := by
    rw [← complement_sum J (fun i => z i^2)]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ J <;> simp [backgroundFeature, hi]
  rw [hq, show backgroundSum J z = _ from complement_sum J z]
  exact pair_square_identity _

private theorem scale_data (j : ℕ) (hj : 1 ≤ j) :
    4 ≤ categoryScale j ∧
    (rareSampleSize j : ℝ) = categoryScale j^4 ∧
    4 ≤ (rareSampleSize j : ℝ) ∧
    categoryFeature j^2 ≤ categoryScale j^5 ∧
    categoryOffset j = ((targetCategoryCount j : ℝ)-1)*categoryFeature j^2/
      ((rareSampleSize j : ℝ)-2) ∧
    (targetCategoryCount j : ℝ) = categoryScale j := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hk := categoryScale_succ_ge l
  have hv := categoryValue_succ_ge l
  have ht : categoryFeature (l+1)^2 ≤ categoryScale (l+1)^5 := by
    rw [← categoryValue_sq_succ]
    dsimp [categoryFeature, featureMean]
    nlinarith
  have hn : (rareSampleSize (l+1) : ℝ) = categoryScale (l+1)^4 := by
    simp [rareSampleSize, targetCategoryCount, categoryScale]
  refine ⟨hk, hn, ?_, ht, ?_, ?_⟩
  · rw [hn]
    nlinarith [sq_nonneg (categoryScale (l+1)^2-4)]
  · simp [categoryOffset, rareSampleSize, targetCategoryCount, categoryScale]
  · simp [targetCategoryCount, categoryScale]

private theorem iid_sum_statistics {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {m : ℕ} (Z : Fin m → Ω → ℝ) (hi : iIndepFun Z μ)
    (hl : ∀ i, IdentDistrib (Z i) (id : ℝ → ℝ) μ ν)
    (h2 : MemLp (id : ℝ → ℝ) 2 ν) :
    MemLp (finiteFeatureSum Z) 2 μ ∧
    (∫ ω, finiteFeatureSum Z ω ∂μ) = (m : ℝ) * ∫ z, z ∂ν ∧
    variance (finiteFeatureSum Z) μ = (m : ℝ) * variance (id : ℝ → ℝ) ν := by
  classical
  have hz (i : Fin m) : MemLp (Z i) 2 μ := (hl i).symm.memLp_snd h2
  refine ⟨memLp_finsetSum _ (fun i _ => hz i), ?_, ?_⟩
  · change (∫ ω, ∑ i : Fin m, Z i ω ∂μ) = _
    rw [integral_finsetSum _ (fun i _ => (hz i).integrable (by norm_num))]
    simp only [(hl _).integral_eq, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, id_eq]
  · have h := IndepFun.variance_sum (s := Finset.univ) (fun i _ => hz i)
      (fun i _ k _ hik => hi.indepFun hik)
    change variance (fun ω => ∑ i : Fin m, Z i ω) μ = _
    convert h using 1
    · congr 1
      funext ω
      simp
    · simp only [(hl _).variance_eq, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]

private theorem noise_law_fixed (n j : ℕ) (hj : 1 ≤ j)
    (J : Finset (Fin n)) (i : Fin n) :
    IdentDistrib (fun ω => decodeNoise (sampleCoordinate i.val ω)) (id : ℝ → ℝ)
      (cond sampleLaw (fixedCategoryEvent n j J)) noiseLaw := by
  have := categoryPatternLaw_isProbability j hj J i
  refine ⟨(measurable_decodeNoise.comp (measurable_sampleCoordinate i.val)).aemeasurable,
    measurable_id.aemeasurable, ?_⟩
  rw [Measure.map_id]
  calc
    Measure.map (fun ω => decodeNoise (sampleCoordinate i.val ω))
        (cond sampleLaw (fixedCategoryEvent n j J)) =
      Measure.map Prod.snd (Measure.map (sampleDecoded i.val)
        (cond sampleLaw (fixedCategoryEvent n j J))) := by
        rw [Measure.map_map measurable_snd (measurable_sampleDecoded i.val)]
        rfl
    _ = noiseLaw := by
      rw [map_sampleDecoded_cond_fixed n j hj J i, Measure.map_snd_prod,
        measure_univ, one_smul]

private theorem noise_indep_fixed (n j : ℕ) (hj : 1 ≤ j) (J : Finset (Fin n)) :
    iIndepFun (fun i : Fin n => fun ω => decodeNoise (sampleCoordinate i.val ω))
      (cond sampleLaw (fixedCategoryEvent n j J)) :=
  (iIndepFun_sampleDecoded_cond_fixed n j hj J).comp (fun _ => Prod.snd)
    (fun _ => measurable_snd)

/-- A fixed-multiple variance estimate requires no independence between the four summands. -/
private theorem variance_four {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (A B C D : Ω → ℝ)
    (ha : MemLp A 2 μ) (hb : MemLp B 2 μ) (hc : MemLp C 2 μ) (hd : MemLp D 2 μ) :
    variance (fun ω => A ω+B ω+C ω+D ω) μ ≤
      4*(variance A μ+variance B μ+variance C μ+variance D μ) := by
  have he : (∫ ω, A ω+B ω+C ω+D ω ∂μ) =
      (∫ ω,A ω ∂μ)+(∫ ω,B ω ∂μ)+(∫ ω,C ω ∂μ)+(∫ ω,D ω ∂μ) := by
    calc
      _ = (∫ ω, A ω+B ω+C ω ∂μ)+(∫ ω,D ω ∂μ) :=
        integral_add (((ha.add hb).add hc).integrable (by norm_num)) (hd.integrable (by norm_num))
      _ = _ := by
        rw [integral_add (f := fun ω => A ω+B ω) (g := C)
          ((ha.add hb).integrable (by norm_num)) (hc.integrable (by norm_num)),
          integral_add (f := A) (g := B) (ha.integrable (by norm_num)) (hb.integrable (by norm_num))]
  rw [variance_eq_integral (X := fun ω => A ω+B ω+C ω+D ω)
    (by exact ((ha.add hb).add hc |>.add hd).aemeasurable),
    he, variance_eq_integral ha.aemeasurable, variance_eq_integral hb.aemeasurable,
    variance_eq_integral hc.aemeasurable, variance_eq_integral hd.aemeasurable]
  have hia : Integrable (fun ω => (A ω-∫ x,A x ∂μ)^2) μ := (ha.sub (memLp_const (∫ x,A x ∂μ))).integrable_sq
  have hib : Integrable (fun ω => (B ω-∫ x,B x ∂μ)^2) μ := (hb.sub (memLp_const (∫ x,B x ∂μ))).integrable_sq
  have hic : Integrable (fun ω => (C ω-∫ x,C x ∂μ)^2) μ := (hc.sub (memLp_const (∫ x,C x ∂μ))).integrable_sq
  have hid : Integrable (fun ω => (D ω-∫ x,D x ∂μ)^2) μ := (hd.sub (memLp_const (∫ x,D x ∂μ))).integrable_sq
  rw [← integral_add hia hib,
    ← integral_add (f := fun ω => (A ω-∫ x,A x ∂μ)^2+(B ω-∫ x,B x ∂μ)^2)
      (g := fun ω => (C ω-∫ x,C x ∂μ)^2) (hia.add hib) hic,
    ← integral_add (f := fun ω => (A ω-∫ x,A x ∂μ)^2+(B ω-∫ x,B x ∂μ)^2+(C ω-∫ x,C x ∂μ)^2)
      (g := fun ω => (D ω-∫ x,D x ∂μ)^2) ((hia.add hib).add hic) hid,
    ← integral_const_mul]
  apply integral_mono ((ha.add hb |>.add hc |>.add hd).sub (memLp_const ((∫ x,A x ∂μ)+(∫ x,B x ∂μ)+(∫ x,C x ∂μ)+(∫ x,D x ∂μ)))).integrable_sq
    (((hia.add hib).add hic |>.add hid).const_mul 4)
  intro ω
  have h (a b c d : ℝ) : (a+b+c+d)^2 ≤ 4*(a^2+b^2+c^2+d^2) := by
    nlinarith [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (a-d),
      sq_nonneg (b-c), sq_nonneg (b-d), sq_nonneg (c-d)]
  convert h (A ω-∫ x,A x ∂μ) (B ω-∫ x,B x ∂μ)
    (C ω-∫ x,C x ∂μ) (D ω-∫ x,D x ∂μ) using 1
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

private theorem fixed_decomposition (j : ℕ) (hj : 1 ≤ j)
    (J : Finset (Fin (rareSampleSize j))) (hJ : J.card = targetCategoryCount j) :
    let n := rareSampleSize j
    let B : Finset (Fin n) := Finset.univ \ J
    let e := Shao.retainedIndex B
    let A := fun i : Fin n => fun ω => decodeNoise (sampleCoordinate i.val ω)
    let W := fun r : Fin B.card => fun ω => categoryFeature (sampleCategory (e r).val ω)
    let D := fun r : Fin B.card => fun ω => categoryOffset (sampleCategory (e r).val ω)
    sampleCenteredNumerator n =ᵐ[cond sampleLaw (fixedCategoryEvent n j J)]
      fun ω => Real.sqrt (n : ℝ) *
        ((J.card : ℝ)*categoryOffset j/((n : ℝ)-1) +
          2/(n : ℝ)*finiteFeatureSum A ω + 2/(n : ℝ)*finiteFeatureSum D ω -
          (2*(J.card : ℝ)*categoryFeature j/((n : ℝ)*((n : ℝ)-1)))*finiteFeatureSum W ω -
          (2/((n : ℝ)*((n : ℝ)-1)))*finitePairProductSum W ω - populationMean) := by
  classical
  dsimp only
  have hs := scale_data j hj
  have hn : 3 ≤ rareSampleSize j := by exact_mod_cast (by linarith [hs.2.2.1] : (3 : ℝ) ≤ rareSampleSize j)
  filter_upwards [ae_cond_mem (μ := sampleLaw)
    (measurableSet_fixedCategoryEvent (rareSampleSize j) j J)] with ω hω
  let A := fun i : Fin (rareSampleSize j) => decodeNoise (finiteSample (rareSampleSize j) ω i)
  let d := fun i : Fin (rareSampleSize j) => observationOffset (finiteSample (rareSampleSize j) ω i)
  let z := fun i : Fin (rareSampleSize j) => observationFeature (finiteSample (rareSampleSize j) ω i)
  have hz (i : Fin (rareSampleSize j)) (hi : i ∈ J) : z i = categoryFeature j := by
    have hc : sampleCategory i.val ω = j := by
      simpa only [fixedCategoryEvent, Set.mem_ofPred_eq, hi, ite_true] using hω i
    change categoryFeature (sampleCategory i.val ω) = _
    rw [hc]
  have hd (i : Fin (rareSampleSize j)) (hi : i ∈ J) : d i = categoryOffset j := by
    have hc : sampleCategory i.val ω = j := by
      simpa only [fixedCategoryEvent, Set.mem_ofPred_eq, hi, ite_true] using hω i
    change categoryOffset (sampleCategory i.val ω) = _
    rw [hc]
  have ht := uStatistic_eq_targetCancellation A d z hn J (categoryFeature j) (categoryOffset j)
    hz hd (by rw [hJ]; exact hs.2.2.2.2.1)
  have hb := background_pair_compressed J z
  have hds := complement_sum J d
  have hws := complement_sum J z
  unfold sampleCenteredNumerator
  rw [sampleU_eq_uStatistic, ht]
  change Real.sqrt (rareSampleSize j : ℝ) * _ = _
  change backgroundSum J z = _ at hws
  change (∑ i, backgroundOffset J d i) = _ at hds
  rw [hb, hws, hds]
  dsimp only [finiteFeatureSum, finitePairProductSum, A, d, z, finiteSample,
    observationFeature, observationOffset, sampleCategory]
  ring

private theorem fixed_moments (j : ℕ) (hj : 1 ≤ j)
    (J : Finset (Fin (rareSampleSize j))) (hJ : J.card = targetCategoryCount j) :
    MemLp (sampleCenteredNumerator (rareSampleSize j)) 2
      (cond sampleLaw (fixedCategoryEvent (rareSampleSize j) j J)) ∧
    (∫ ω, sampleCenteredNumerator (rareSampleSize j) ω
      ∂cond sampleLaw (fixedCategoryEvent (rareSampleSize j) j J)) = conditionalNumeratorMean j := by
  classical
  let n := rareSampleSize j
  let μ := cond sampleLaw (fixedCategoryEvent n j J)
  have := fixedCategoryEvent_cond_isProbability n j hj J
  have := backgroundCategoryLaw_isProbability j hj
  let B : Finset (Fin n) := Finset.univ \ J
  let e := Shao.retainedIndex B
  have he : Function.Injective e := e.injective
  have hback (r : Fin B.card) : e r ∉ J := (Finset.mem_sdiff.mp (Shao.retainedIndex_mem B r)).2
  let A := fun i : Fin n => fun ω => decodeNoise (sampleCoordinate i.val ω)
  let W := fun r : Fin B.card => fun ω => categoryFeature (sampleCategory (e r).val ω)
  let D := fun r : Fin B.card => fun ω => categoryOffset (sampleCategory (e r).val ω)
  let ν := Measure.map categoryFeature (backgroundCategoryLaw j)
  let ξ := Measure.map categoryOffset (backgroundCategoryLaw j)
  have hν : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable).mpr inferInstance
  have hξ : IsProbabilityMeasure ξ := (Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable).mpr inferInstance
  have hA2 : MemLp (id : ℝ → ℝ) 2 noiseLaw :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr integrable_noiseLaw_sq
  have hAs := iid_sum_statistics A (noise_indep_fixed n j hj J) (noise_law_fixed n j hj J) hA2
  have hWl := identDistrib_selectedBackgroundFeature B.card n j hj J e he hback
  have hDl := identDistrib_selectedBackgroundOffset B.card n j hj J e he hback
  have hWi := iIndepFun_selectedBackgroundFeature B.card n j hj J e he hback
  have hDi := iIndepFun_selectedBackgroundOffset B.card n j hj J e he hback
  have hWm (r : Fin B.card) : Measurable (W r) :=
    (measurable_of_countable categoryFeature).comp (measurable_sampleCategory (e r).val)
  have hWs := iid_sum_statistics W hWi hWl (memLp_backgroundFeature j hj)
  have hDs := iid_sum_statistics D hDi hDl (memLp_backgroundOffset j hj)
  have hF2 := finite_iid_pairProduct_memLp_two hWm hWi hWl (memLp_backgroundFeature j hj)
  have hFm := finite_iid_pairProduct_integral hWm hWi hWl (memLp_backgroundFeature j hj)
  have hmeanW : (∫ z : ℝ,z ∂ν) = ∫ c,categoryFeature c ∂backgroundCategoryLaw j := by
    exact integral_map (measurable_of_countable categoryFeature).aemeasurable measurable_id.aestronglyMeasurable
  have hmeanD : (∫ z : ℝ,z ∂ξ) = ∫ c,categoryOffset c ∂backgroundCategoryLaw j := by
    exact integral_map (measurable_of_countable categoryOffset).aemeasurable measurable_id.aestronglyMeasurable
  dsimp only [ν] at hmeanW
  dsimp only [ξ] at hmeanD
  let g := fun ω => (J.card : ℝ)*categoryOffset j/((n : ℝ)-1) +
    2/(n : ℝ)*finiteFeatureSum A ω + 2/(n : ℝ)*finiteFeatureSum D ω -
    (2*(J.card : ℝ)*categoryFeature j/((n : ℝ)*((n : ℝ)-1)))*finiteFeatureSum W ω -
    (2/((n : ℝ)*((n : ℝ)-1)))*finitePairProductSum W ω - populationMean
  have hg2 : MemLp g 2 μ :=
    (((((memLp_const _).add (hAs.1.const_mul _)).add (hDs.1.const_mul _)).sub
      (hWs.1.const_mul _)).sub (hF2.const_mul _)).sub (memLp_const _)
  have hdec := fixed_decomposition j hj J hJ
  have hN2 : MemLp (sampleCenteredNumerator n) 2 μ :=
    MemLp.ae_eq hdec.symm (hg2.const_mul (Real.sqrt (n : ℝ)))
  refine ⟨hN2, ?_⟩
  have hgint := hg2.integrable (by norm_num)
  rw [integral_congr_ae hdec, integral_const_mul]
  have hei : (∫ ω,g ω ∂μ) =
      (J.card : ℝ)*categoryOffset j/((n : ℝ)-1) +
      2/(n : ℝ)*((n : ℝ)*0) +
      2/(n : ℝ)*((B.card : ℝ)*(∫ c,categoryOffset c ∂backgroundCategoryLaw j)) -
      (2*(J.card : ℝ)*categoryFeature j/((n : ℝ)*((n : ℝ)-1)))*
        ((B.card : ℝ)*(∫ c,categoryFeature c ∂backgroundCategoryLaw j)) -
      (2/((n : ℝ)*((n : ℝ)-1)))*
        (B.card.choose 2 : ℝ)*(∫ c,categoryFeature c ∂backgroundCategoryLaw j)^2 - populationMean := by
    dsimp only [g]
    rw [integral_sub (f := fun ω => _ - _ - _) (g := fun _ => populationMean)
      (((((memLp_const _).add (hAs.1.const_mul _)).add (hDs.1.const_mul _)).sub
      (hWs.1.const_mul _)).sub (hF2.const_mul _) |>.integrable (by norm_num)) (integrable_const _),
      integral_sub (f := fun ω => _ + _ + _ - _) (g := fun ω => _*finitePairProductSum W ω)
      (((((memLp_const _).add (hAs.1.const_mul _)).add (hDs.1.const_mul _)).sub
      (hWs.1.const_mul _)).integrable (by norm_num)) ((hF2.const_mul _).integrable (by norm_num)),
      integral_sub (f := fun ω => _ + _ + _) (g := fun ω => _*finiteFeatureSum W ω)
      ((((memLp_const _).add (hAs.1.const_mul _)).add (hDs.1.const_mul _)).integrable (by norm_num))
      ((hWs.1.const_mul _).integrable (by norm_num)),
      integral_add (f := fun ω => _ + _) (g := fun ω => _*finiteFeatureSum D ω)
      (((memLp_const _).add (hAs.1.const_mul _)).integrable (by norm_num))
      ((hDs.1.const_mul _).integrable (by norm_num)),
      integral_add (f := fun _ => _) (g := fun ω => _*finiteFeatureSum A ω)
      (integrable_const _) ((hAs.1.const_mul _).integrable (by norm_num))]
    simp only [integral_const_mul, integral_const, probReal_univ, one_smul,
      hAs.2.1, hDs.2.1, hWs.2.1, hFm, integral_noiseLaw_id, hmeanW, hmeanD]
    ring
  change Real.sqrt (n : ℝ)*(∫ ω,g ω ∂μ) = _
  rw [hei]
  have hc : B.card = n-J.card := by simp [B, Finset.card_sdiff]
  have hchoose : 2*(B.card.choose 2 : ℝ) = (B.card : ℝ)*((B.card : ℝ)-1) := by
    rw [← pairCount_eq_choose]
    unfold pairCount
    ring
  unfold conditionalNumeratorMean
  dsimp only
  rw [← hJ, ← hc]
  congr 1
  dsimp only [n]
  linear_combination -((∫ c,categoryFeature c ∂backgroundCategoryLaw j)^2 /
    ((rareSampleSize j : ℝ)*((rareSampleSize j : ℝ)-1))) * hchoose

theorem memLp_sampleCenteredNumerator_cond_fixed (j : ℕ) (hj : 1 ≤ j)
    (J : Finset (Fin (rareSampleSize j))) (hJ : J.card = targetCategoryCount j) :
    MemLp (sampleCenteredNumerator (rareSampleSize j)) 2
      (cond sampleLaw (fixedCategoryEvent (rareSampleSize j) j J)) :=
  (fixed_moments j hj J hJ).1

theorem memLp_sampleCenteredNumerator_cond_rare (j : ℕ) (hj : 1 ≤ j) :
    MemLp (sampleCenteredNumerator (rareSampleSize j)) 2
      (cond sampleLaw (rareCategoryEvent j)) := by
  apply (memLp_two_iff_integrable_sq (numerator_measurable _).aestronglyMeasurable).mpr
  apply integrable_cond_exactCategoryEvent _ _ j hj (targetCategoryCount_le_rareSampleSize j)
  intro J hJ
  exact (memLp_sampleCenteredNumerator_cond_fixed j hj J (Finset.mem_powersetCard.mp hJ).2).integrable_sq

theorem integral_sampleCenteredNumerator_cond_fixed (j : ℕ) (hj : 1 ≤ j)
    (J : Finset (Fin (rareSampleSize j))) (hJ : J.card = targetCategoryCount j) :
    (∫ ω, sampleCenteredNumerator (rareSampleSize j) ω
      ∂cond sampleLaw (fixedCategoryEvent (rareSampleSize j) j J)) = conditionalNumeratorMean j :=
  (fixed_moments j hj J hJ).2

theorem integral_sampleCenteredNumerator_cond_rare (j : ℕ) (hj : 1 ≤ j) :
    (∫ ω, sampleCenteredNumerator (rareSampleSize j) ω
      ∂cond sampleLaw (rareCategoryEvent j)) = conditionalNumeratorMean j := by
  classical
  rw [rareCategoryEvent, integral_cond_exactCategoryEvent _ _ j hj
    (targetCategoryCount_le_rareSampleSize j) _
    (fun J hJ => (memLp_sampleCenteredNumerator_cond_fixed j hj J
      (Finset.mem_powersetCard.mp hJ).2).integrable (by norm_num))]
  have hconst : (∑ J ∈ (Finset.univ : Finset (Fin (rareSampleSize j))).powersetCard
      (targetCategoryCount j), ∫ ω, sampleCenteredNumerator (rareSampleSize j) ω
        ∂cond sampleLaw (fixedCategoryEvent (rareSampleSize j) j J)) =
      ∑ _J ∈ (Finset.univ : Finset (Fin (rareSampleSize j))).powersetCard
        (targetCategoryCount j), conditionalNumeratorMean j := by
    apply Finset.sum_congr rfl
    intro J hJ
    exact integral_sampleCenteredNumerator_cond_fixed j hj J (Finset.mem_powersetCard.mp hJ).2
  rw [hconst, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hc : (rareSampleSize j |>.choose (targetCategoryCount j) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (targetCategoryCount_le_rareSampleSize j)).ne'
  field_simp


private theorem scalar_variance_bound (n k t m C a b c f : ℝ)
    (hn : 4 ≤ n) (hC : 1 ≤ C) (_hm0 : 0 ≤ m) (hm : m ≤ n)
    (hkt : k^2*t^2 ≤ n^2)
    (ha : a ≤ n) (hb : b ≤ m*C) (hc : c ≤ m*C)
    (hf : f ≤ n^2*C^2+n^3*C^3) :
    n * (4*((2/n)^2*a+(2/n)^2*b+
      (-(2*k*t/(n*(n-1))))^2*c+(-(2/(n*(n-1))))^2*f)) ≤ 1024*C^3 := by
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n-1 := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hden : n^2 ≤ 4*(n-1)^2 := by nlinarith
  have hn2 : n ≤ n^2 := by nlinarith
  have h1 : n*(2/n)^2*a ≤ 4 := by
    calc
      _ ≤ n*(2/n)^2*n := mul_le_mul_of_nonneg_left ha (by positivity)
      _ = 4 := by field_simp; ring
  have h2 (x : ℝ) (hx : x ≤ m*C) : n*(2/n)^2*x ≤ 4*C := by
    calc
      _ ≤ n*(2/n)^2*(n*C) := mul_le_mul_of_nonneg_left
        (hx.trans (mul_le_mul_of_nonneg_right hm hC0)) (by positivity)
      _ = 4*C := by field_simp; ring
  have h3 : n*(-(2*k*t/(n*(n-1))))^2*c ≤ 16*C := by
    calc
      _ ≤ n*(-(2*k*t/(n*(n-1))))^2*(n*C) := mul_le_mul_of_nonneg_left
        (hc.trans (mul_le_mul_of_nonneg_right hm hC0)) (by positivity)
      _ = 4*(k^2*t^2)*C/(n-1)^2 := by field_simp; ring
      _ ≤ 4*n^2*C/(n-1)^2 := by gcongr
      _ ≤ 16*C := by
        apply (div_le_iff₀ (sq_pos_of_pos hn1)).mpr
        nlinarith [mul_le_mul_of_nonneg_right hden hC0]
  have h4 : n*(-(2/(n*(n-1))))^2*f ≤ 16*(C^2+C^3) := by
    calc
      _ ≤ n*(-(2/(n*(n-1))))^2*(n^2*C^2+n^3*C^3) :=
        mul_le_mul_of_nonneg_left hf (by positivity)
      _ = 4*(n*C^2+n^2*C^3)/(n-1)^2 := by field_simp; ring
      _ ≤ 16*(C^2+C^3) := by
        apply (div_le_iff₀ (sq_pos_of_pos hn1)).mpr
        have hA := mul_le_mul_of_nonneg_right (hn2.trans hden) (sq_nonneg C)
        have hB := mul_le_mul_of_nonneg_right hden (pow_nonneg hC0 3)
        nlinarith
  have hC2 : C ≤ C^2 := by nlinarith
  have hC3 : C^2 ≤ C^3 := by nlinarith [mul_nonneg hC0 (sub_nonneg.mpr hC2)]
  nlinarith [h2 b hb]

private theorem fixed_variance_bound (C : ℝ) (hC : 1 ≤ C)
    (j : ℕ) (hj : 1 ≤ j) (J : Finset (Fin (rareSampleSize j)))
    (hJ : J.card = targetCategoryCount j)
    (hM : (∫ c,categoryFeature c^2 ∂backgroundCategoryLaw j) ≤ C)
    (hD : (∫ c,categoryOffset c^2 ∂backgroundCategoryLaw j) ≤ C)
    (hu : (∫ c,categoryFeature c ∂backgroundCategoryLaw j)^2 ≤ C^2) :
    variance (sampleCenteredNumerator (rareSampleSize j))
      (cond sampleLaw (fixedCategoryEvent (rareSampleSize j) j J)) ≤ 1024*C^3 := by
  classical
  let n := rareSampleSize j
  let μ := cond sampleLaw (fixedCategoryEvent n j J)
  have := fixedCategoryEvent_cond_isProbability n j hj J
  have := backgroundCategoryLaw_isProbability j hj
  let B : Finset (Fin n) := Finset.univ \ J
  let e := Shao.retainedIndex B
  have he : Function.Injective e := e.injective
  have hback (r : Fin B.card) : e r ∉ J := (Finset.mem_sdiff.mp (Shao.retainedIndex_mem B r)).2
  let A := fun i : Fin n => fun ω => decodeNoise (sampleCoordinate i.val ω)
  let W := fun r : Fin B.card => fun ω => categoryFeature (sampleCategory (e r).val ω)
  let D := fun r : Fin B.card => fun ω => categoryOffset (sampleCategory (e r).val ω)
  let ν := Measure.map categoryFeature (backgroundCategoryLaw j)
  let ξ := Measure.map categoryOffset (backgroundCategoryLaw j)
  have hν : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff
    (measurable_of_countable _).aemeasurable).mpr inferInstance
  have hξ : IsProbabilityMeasure ξ := (Measure.isProbabilityMeasure_map_iff
    (measurable_of_countable _).aemeasurable).mpr inferInstance
  have hA2 : MemLp (id : ℝ → ℝ) 2 noiseLaw :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr integrable_noiseLaw_sq
  have hAs := iid_sum_statistics A (noise_indep_fixed n j hj J) (noise_law_fixed n j hj J) hA2
  have hWl := identDistrib_selectedBackgroundFeature B.card n j hj J e he hback
  have hDl := identDistrib_selectedBackgroundOffset B.card n j hj J e he hback
  have hWi := iIndepFun_selectedBackgroundFeature B.card n j hj J e he hback
  have hDi := iIndepFun_selectedBackgroundOffset B.card n j hj J e he hback
  have hWm (r : Fin B.card) : Measurable (W r) :=
    (measurable_of_countable categoryFeature).comp (measurable_sampleCategory (e r).val)
  have hWs := iid_sum_statistics W hWi hWl (memLp_backgroundFeature j hj)
  have hDs := iid_sum_statistics D hDi hDl (memLp_backgroundOffset j hj)
  have hF2 := finite_iid_pairProduct_memLp_two hWm hWi hWl (memLp_backgroundFeature j hj)
  have hFv := finite_iid_pairProduct_variance hWm hWi hWl (memLp_backgroundFeature j hj)
  have hmeanW : (∫ z : ℝ,z ∂ν) = ∫ c,categoryFeature c ∂backgroundCategoryLaw j :=
    integral_map (measurable_of_countable categoryFeature).aemeasurable measurable_id.aestronglyMeasurable
  have hνv : variance (id : ℝ → ℝ) ν ≤ C := by
    calc
      _ ≤ ∫ z : ℝ,z^2 ∂ν := variance_le_expectation_sq measurable_id.aestronglyMeasurable
      _ = ∫ c,categoryFeature c^2 ∂backgroundCategoryLaw j :=
        integral_map (measurable_of_countable categoryFeature).aemeasurable
          (measurable_id.pow_const 2).aestronglyMeasurable
      _ ≤ C := hM
  have hξv : variance (id : ℝ → ℝ) ξ ≤ C := by
    calc
      _ ≤ ∫ z : ℝ,z^2 ∂ξ := variance_le_expectation_sq measurable_id.aestronglyMeasurable
      _ = ∫ c,categoryOffset c^2 ∂backgroundCategoryLaw j :=
        integral_map (measurable_of_countable categoryOffset).aemeasurable
          (measurable_id.pow_const 2).aestronglyMeasurable
      _ ≤ C := hD
  have hAv : variance (finiteFeatureSum A) μ ≤ (n : ℝ) := by
    rw [hAs.2.2]
    have hv : variance (id : ℝ → ℝ) noiseLaw ≤ 1 := by
      calc
        _ ≤ ∫ z : ℝ,z^2 ∂noiseLaw := variance_le_expectation_sq measurable_id.aestronglyMeasurable
        _ ≤ 1 := by rw [integral_noiseLaw_sq]; norm_num
    simpa using mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hWv : variance (finiteFeatureSum W) μ ≤ (B.card : ℝ)*C := by
    rw [hWs.2.2]
    exact mul_le_mul_of_nonneg_left hνv (Nat.cast_nonneg _)
  have hDv : variance (finiteFeatureSum D) μ ≤ (B.card : ℝ)*C := by
    rw [hDs.2.2]
    exact mul_le_mul_of_nonneg_left hξv (Nat.cast_nonneg _)
  have hm : (B.card : ℝ) ≤ n := by exact_mod_cast (show B.card ≤ n by simp [B, Finset.card_sdiff])
  have hm1 : ((B.card-1 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast (Nat.sub_le B.card 1 |>.trans (by exact_mod_cast hm))
  have hchoose : (B.card.choose 2 : ℝ) ≤ (n : ℝ)^2 := by
    rw [← pairCount_eq_choose, pairCount]
    have hm0 : (0 : ℝ) ≤ B.card := Nat.cast_nonneg _
    nlinarith
  have hFbound : variance (finitePairProductSum W) μ ≤ (n : ℝ)^2*C^2+(n : ℝ)^3*C^3 := by
    rw [hFv]
    change (B.card.choose 2 : ℝ)*variance (id : ℝ → ℝ) ν ^2+
      (B.card : ℝ)*((B.card-1 : ℕ) : ℝ)^2*(∫ z : ℝ,z ∂ν)^2*variance (id : ℝ → ℝ) ν ≤ _
    have hv0 : 0 ≤ variance (id : ℝ → ℝ) ν := variance_nonneg _ _
    have hC0 : 0 ≤ C := by linarith
    have hv2 : variance (id : ℝ → ℝ) ν ^2 ≤ C^2 := by nlinarith
    have hu' : (∫ z : ℝ,z ∂ν)^2 ≤ C^2 := by rw [hmeanW]; exact hu
    have hp : (B.card.choose 2 : ℝ)*variance (id : ℝ → ℝ) ν ^2 ≤ (n : ℝ)^2*C^2 := by gcongr
    have hq : (B.card : ℝ)*((B.card-1 : ℕ) : ℝ)^2*(∫ z : ℝ,z ∂ν)^2*variance (id : ℝ → ℝ) ν ≤
        (n : ℝ)*(n : ℝ)^2*C^2*C := by gcongr
    nlinarith
  have hs := scale_data j hj
  have hk : (targetCategoryCount j : ℝ)^2*categoryFeature j^2 ≤ (n : ℝ)^2 := by
    rw [hs.2.2.2.2.2, show (n : ℝ) = categoryScale j^4 from hs.2.1]
    calc
      _ ≤ categoryScale j^2*categoryScale j^5 :=
        mul_le_mul_of_nonneg_left hs.2.2.2.1 (sq_nonneg _)
      _ ≤ (categoryScale j^4)^2 := by
        have hk0 : 0 ≤ categoryScale j := by linarith [hs.1]
        have hpow : 0 ≤ categoryScale j^7 := pow_nonneg hk0 _
        nlinarith [mul_nonneg (sub_nonneg.mpr (show 1 ≤ categoryScale j by linarith [hs.1])) hpow]
  let a := fun ω => 2/(n : ℝ)*finiteFeatureSum A ω
  let b := fun ω => 2/(n : ℝ)*finiteFeatureSum D ω
  let c := fun ω => -(2*(targetCategoryCount j : ℝ)*categoryFeature j/((n : ℝ)*((n : ℝ)-1)))*finiteFeatureSum W ω
  let f := fun ω => -(2/((n : ℝ)*((n : ℝ)-1)))*finitePairProductSum W ω
  have ha2 : MemLp a 2 μ := hAs.1.const_mul _
  have hb2 : MemLp b 2 μ := hDs.1.const_mul _
  have hc2 : MemLp c 2 μ := hWs.1.const_mul _
  have hf2 : MemLp f 2 μ := hF2.const_mul _
  let G := fun ω => a ω+b ω+c ω+f ω
  have hG2 : MemLp G 2 μ := ((ha2.add hb2).add hc2).add hf2
  have heq : sampleCenteredNumerator n =ᵐ[μ] fun ω =>
      Real.sqrt (n : ℝ)*(G ω+((targetCategoryCount j : ℝ)*categoryOffset j/((n : ℝ)-1)-populationMean)) := by
    filter_upwards [fixed_decomposition j hj J hJ] with ω hω
    rw [hω, hJ]
    dsimp only [G,a,b,c,f]
    ring
  rw [variance_congr heq, variance_const_mul,
    variance_add_const hG2.aestronglyMeasurable, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hv := variance_four a b c f ha2 hb2 hc2 hf2
  calc
    _ ≤ (n : ℝ)*(4*(variance a μ+variance b μ+variance c μ+variance f μ)) :=
      mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg n)
    _ = _ := by
      dsimp only [a,b,c,f]
      rw [variance_const_mul, variance_const_mul, variance_const_mul, variance_const_mul]
    _ ≤ 1024*C^3 := scalar_variance_bound (n : ℝ) (targetCategoryCount j) (categoryFeature j)
      B.card C _ _ _ _ hs.2.2.1 hC (Nat.cast_nonneg _) hm hk hAv hDv hWv hFbound

theorem variance_sampleCenteredNumerator_cond_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 1 ≤ j →
      (∀ J : Finset (Fin (rareSampleSize j)), J.card = targetCategoryCount j →
        variance (sampleCenteredNumerator (rareSampleSize j))
          (cond sampleLaw (fixedCategoryEvent (rareSampleSize j) j J)) ≤ C) ∧
      variance (sampleCenteredNumerator (rareSampleSize j))
        (cond sampleLaw (rareCategoryEvent j)) ≤ C := by
  classical
  obtain ⟨D,hD,hbounds⟩ := backgroundCategoryMoments_uniform
  let C := D+1
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hC0 : 0 < C := by linarith
  refine ⟨1024*C^3, by positivity, ?_⟩
  intro j hj
  have hs := hbounds j hj
  have hu : (∫ c,categoryFeature c ∂backgroundCategoryLaw j)^2 ≤ C^2 := by
    have hpow : (1/512 : ℝ)^j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have ha : |∫ c,categoryFeature c ∂backgroundCategoryLaw j| ≤ C := by
      have := mul_le_mul_of_nonneg_left hpow hD.le
      dsimp [C]
      linarith [hs.2.2.1]
    have hsq := (sq_le_sq₀ (abs_nonneg (∫ c,categoryFeature c ∂backgroundCategoryLaw j)) hC0.le).mpr ha
    simpa only [sq_abs] using hsq
  have hfix (J : Finset (Fin (rareSampleSize j))) (hJ : J.card = targetCategoryCount j) :
      variance (sampleCenteredNumerator (rareSampleSize j))
        (cond sampleLaw (fixedCategoryEvent (rareSampleSize j) j J)) ≤ 1024*C^3 :=
    fixed_variance_bound C hC j hj J hJ (by dsimp [C]; linarith [hs.1])
      (by dsimp [C]; linarith [hs.2.1]) hu
  refine ⟨hfix, ?_⟩
  rw [variance_eq_integral (numerator_measurable _).aemeasurable,
    integral_sampleCenteredNumerator_cond_rare j hj]
  apply integral_cond_exactCategoryEvent_le _ _ j hj (targetCategoryCount_le_rareSampleSize j)
  · intro J hJ
    exact ((memLp_sampleCenteredNumerator_cond_fixed j hj J
      (Finset.mem_powersetCard.mp hJ).2).sub (memLp_const _)).integrable_sq
  · intro J hJ
    have hm := integral_sampleCenteredNumerator_cond_fixed j hj J (Finset.mem_powersetCard.mp hJ).2
    have hv := hfix J (Finset.mem_powersetCard.mp hJ).2
    rwa [variance_eq_integral (numerator_measurable _).aemeasurable, hm] at hv


private theorem geometric_error_limit (f : ℕ → ℝ) (C r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ᶠ j in atTop, |f j| ≤ C*r^j) : Tendsto f atTop (nhds 0) := by
  have hg : Tendsto (fun j : ℕ => C*r^j) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hg.neg) hg
  · filter_upwards [h] with j hj
    exact (abs_le.mp hj).1
  · filter_upwards [h] with j hj
    exact (abs_le.mp hj).2

/-- Exact scalar rearrangement preserving all four terms of the conditional mean. -/
private theorem mean_normal_form (j : ℕ) (hj : 1 ≤ j) :
    let k := categoryScale j
    let r := k⁻¹
    let u := ∫ c,categoryFeature c ∂backgroundCategoryLaw j
    let d := ∫ c,categoryOffset c ∂backgroundCategoryLaw j
    conditionalNumeratorMean j / k =
      (1-r)*((categoryFeature j)^2/k^5)/((1-2*r^4)*(1-r^4)) +
      (2*(k*(d-offsetMean))-2*d*r^2) -
      (2*(categoryFeature j*u)*r^2*(1-r^3)/(1-r^4)) -
      ((k*u)*u*(1-r^3)*(1-r^3-r^4)/(1-r^4)) := by
  dsimp only
  obtain ⟨hk,hn,hn4,ht,hd,hK⟩ := scale_data j hj
  have hk0 : categoryScale j ≠ 0 := by linarith
  have hn1 : categoryScale j^4-1 ≠ 0 := by rw [← hn]; linarith
  have hn2 : categoryScale j^4-2 ≠ 0 := by rw [← hn]; linarith
  have hsqrt : Real.sqrt (rareSampleSize j : ℝ) = categoryScale j^2 := by
    rw [hn, show categoryScale j^4=(categoryScale j^2)^2 by ring,
      Real.sqrt_sq (sq_nonneg _)]
  have hm : ((rareSampleSize j-targetCategoryCount j : ℕ) : ℝ) =
      categoryScale j^4-categoryScale j := by
    rw [Nat.cast_sub (targetCategoryCount_le_rareSampleSize j), hn, hK]
  unfold conditionalNumeratorMean
  dsimp only
  rw [hsqrt, hn, hK, hm, hd, hK, hn, populationMean]
  field_simp [hk0, hn1, hn2]
  ring

private theorem normalized_target_limit :
    Tendsto (fun j : ℕ =>
      (1-(categoryScale j)⁻¹)*(categoryFeature j^2/categoryScale j^5) /
        ((1-2*((categoryScale j)⁻¹)^4)*(1-((categoryScale j)⁻¹)^4))) atTop (nhds 1) := by
  have hr : Tendsto (fun j : ℕ => (categoryScale j)⁻¹) atTop (nhds 0) := by
    simpa only [categoryScale, ← inv_pow, show (4:ℝ)⁻¹=1/4 by norm_num] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4)
        (by norm_num : (1/4:ℝ) < 1)
  have hv : Tendsto (fun j : ℕ => (1/32 : ℝ)^j) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have ht : Tendsto (fun j : ℕ => categoryFeature j^2/categoryScale j^5) atTop (nhds 1) := by
    have hlim : Tendsto (fun j : ℕ => (1-featureMean*(1/32 : ℝ)^j)^2) atTop (nhds 1) := by
      simpa using ((tendsto_const_nhds (x := (1:ℝ))).sub
        ((tendsto_const_nhds (x := featureMean)).mul hv)).pow 2
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 1] with j hj
    obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rw [← categoryValue_sq_succ]
    have hv0 : categoryValue (l+1) ≠ 0 := by linarith [categoryValue_succ_ge l]
    have he : (1/32 : ℝ)^(l+1) = (categoryValue (l+1))⁻¹ := by
      simp [categoryValue, inv_pow]
    rw [he]
    unfold categoryFeature
    field_simp
  have hd1 : Tendsto (fun j : ℕ => 1-2*((categoryScale j)⁻¹)^4) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul (hr.pow 4))
  have hd2 : Tendsto (fun j : ℕ => 1-((categoryScale j)⁻¹)^4) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub (hr.pow 4)
  have hlim : Tendsto
      ((fun j : ℕ => (1-(categoryScale j)⁻¹)*(categoryFeature j^2/categoryScale j^5)) /
        (fun j : ℕ => (1-2*((categoryScale j)⁻¹)^4)*(1-((categoryScale j)⁻¹)^4))) atTop (nhds (1:ℝ)) := by
    simpa using ((tendsto_const_nhds.sub hr).mul ht).div (hd1.mul hd2) (by norm_num : (1:ℝ)*1≠0)
  exact hlim.congr (fun j => by simp)

theorem conditionalNumeratorMean_div_scale_tendsto_one :
    Tendsto (fun j : ℕ => conditionalNumeratorMean j / categoryScale j) atTop (nhds 1) := by
  obtain ⟨C,hC,hbounds⟩ := backgroundCategoryMoments_uniform
  let u := fun j => ∫ c,categoryFeature c ∂backgroundCategoryLaw j
  let d := fun j => ∫ c,categoryOffset c ∂backgroundCategoryLaw j
  have hr : Tendsto (fun j : ℕ => (categoryScale j)⁻¹) atTop (nhds 0) := by
    simpa only [categoryScale, ← inv_pow, show (4:ℝ)⁻¹=1/4 by norm_num] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4)
        (by norm_num : (1/4:ℝ) < 1)
  have hu : Tendsto u atTop (nhds 0) := by
    apply geometric_error_limit u C (1/512) (by norm_num) (by norm_num)
    filter_upwards [eventually_ge_atTop 1] with j hj
    exact (hbounds j hj).2.2.1
  have hku : Tendsto (fun j => categoryScale j*u j) atTop (nhds 0) := by
    apply geometric_error_limit _ C (1/128) (by norm_num) (by norm_num)
    filter_upwards [eventually_ge_atTop 1] with j hj
    calc
      _ = categoryScale j*|u j| := by rw [abs_mul, abs_of_nonneg (categoryScale_one_le j |>.trans' (by norm_num))]
      _ ≤ categoryScale j*(C*(1/512:ℝ)^j) :=
        mul_le_mul_of_nonneg_left (hbounds j hj).2.2.1 (by linarith [categoryScale_one_le j])
      _ = C*(1/128:ℝ)^j := by unfold categoryScale; rw [← mul_assoc, mul_comm _ C, mul_assoc, ← mul_pow]; norm_num
  have hdb : Tendsto (fun j => d j-offsetMean) atTop (nhds 0) := by
    apply geometric_error_limit _ C (1/1024) (by norm_num) (by norm_num)
    filter_upwards [eventually_ge_atTop 1] with j hj
    exact (hbounds j hj).2.2.2
  have hd : Tendsto d atTop (nhds offsetMean) := by
    simpa using hdb.add_const offsetMean
  have hkdb : Tendsto (fun j => categoryScale j*(d j-offsetMean)) atTop (nhds 0) := by
    apply geometric_error_limit _ C (1/256) (by norm_num) (by norm_num)
    filter_upwards [eventually_ge_atTop 1] with j hj
    calc
      _ = categoryScale j*|d j-offsetMean| := by
        rw [abs_mul, abs_of_nonneg (by linarith [categoryScale_one_le j])]
      _ ≤ categoryScale j*(C*(1/1024:ℝ)^j) :=
        mul_le_mul_of_nonneg_left (hbounds j hj).2.2.2 (by linarith [categoryScale_one_le j])
      _ = C*(1/256:ℝ)^j := by unfold categoryScale; rw [← mul_assoc, mul_comm _ C, mul_assoc, ← mul_pow]; norm_num
  have htu : Tendsto (fun j => categoryFeature j*u j) atTop (nhds 0) := by
    apply geometric_error_limit _ C (1/16) (by norm_num) (by norm_num)
    filter_upwards [eventually_ge_atTop 1] with j hj
    have ht : |categoryFeature j| ≤ (32:ℝ)^j := by
      obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      have hv := categoryValue_succ_ge l
      rw [abs_of_nonneg (by dsimp [categoryFeature,featureMean]; linarith)]
      change categoryValue (l+1)-featureMean ≤ _
      simp only [categoryValue, Nat.succ_ne_zero, ite_false]
      norm_num [featureMean]
    calc
      _ = |categoryFeature j| * |u j| := abs_mul _ _
      _ ≤ (32:ℝ)^j*(C*(1/512:ℝ)^j) :=
        mul_le_mul ht (hbounds j hj).2.2.1 (abs_nonneg _) (by positivity)
      _ = C*(1/16:ℝ)^j := by rw [← mul_assoc, mul_comm _ C, mul_assoc, ← mul_pow]; norm_num
  have hden : Tendsto (fun j : ℕ => 1-((categoryScale j)⁻¹)^4) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub (hr.pow 4)
  have hB : Tendsto (fun j => 2*(categoryScale j*(d j-offsetMean))-2*d j*((categoryScale j)⁻¹)^2)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hkdb).sub
      ((tendsto_const_nhds.mul hd).mul (hr.pow 2))
  have hcross : Tendsto (fun j => 2*(categoryFeature j*u j)*((categoryScale j)⁻¹)^2*
      (1-((categoryScale j)⁻¹)^3)/(1-((categoryScale j)⁻¹)^4)) atTop (nhds 0) := by
    have hl : Tendsto
        ((fun j => 2*(categoryFeature j*u j)*((categoryScale j)⁻¹)^2*(1-((categoryScale j)⁻¹)^3)) /
          (fun j => 1-((categoryScale j)⁻¹)^4)) atTop (nhds (0:ℝ)) := by
      simpa using (((tendsto_const_nhds.mul htu).mul (hr.pow 2)).mul
        (tendsto_const_nhds.sub (hr.pow 3))).div hden (by norm_num : (1:ℝ) ≠ 0)
    exact hl.congr (fun j => by simp)
  have hpair : Tendsto (fun j => (categoryScale j*u j)*u j*(1-((categoryScale j)⁻¹)^3)*
      (1-((categoryScale j)⁻¹)^3-((categoryScale j)⁻¹)^4)/(1-((categoryScale j)⁻¹)^4))
      atTop (nhds 0) := by
    have hl : Tendsto
        ((fun j => (categoryScale j*u j)*u j*(1-((categoryScale j)⁻¹)^3)*
          (1-((categoryScale j)⁻¹)^3-((categoryScale j)⁻¹)^4)) /
          (fun j => 1-((categoryScale j)⁻¹)^4)) atTop (nhds (0:ℝ)) := by
      simpa using (((hku.mul hu).mul (tendsto_const_nhds.sub (hr.pow 3))).mul
        ((tendsto_const_nhds.sub (hr.pow 3)).sub (hr.pow 4))).div hden (by norm_num : (1:ℝ) ≠ 0)
    exact hl.congr (fun j => by simp)
  have hlim := ((normalized_target_limit.add hB).sub hcross).sub hpair
  apply (by simpa using hlim : Tendsto _ atTop (nhds (1:ℝ))).congr'
  filter_upwards [eventually_ge_atTop 1] with j hj
  simpa only [u,d,inv_pow] using (mean_normal_form j hj).symm

theorem integral_sampleCenteredNumerator_cond_rare_div_scale_tendsto_one :
    Tendsto (fun j : ℕ =>
      (∫ ω,sampleCenteredNumerator (rareSampleSize j) ω
        ∂cond sampleLaw (rareCategoryEvent j))/categoryScale j) atTop (nhds 1) := by
  apply conditionalNumeratorMean_div_scale_tendsto_one.congr'
  filter_upwards [eventually_ge_atTop 1] with j hj
  rw [integral_sampleCenteredNumerator_cond_rare j hj]


end

end Shao.OQ5.P35
