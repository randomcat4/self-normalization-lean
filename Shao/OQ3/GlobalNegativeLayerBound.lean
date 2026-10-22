import Shao.OQ3.SourceFarWeightedTail
import Shao.OQ3.LocalNegativeLayerControl

namespace Shao.OQ3
open MeasureTheory Filter
open scoped BigOperators
noncomputable section

private theorem stage_normal_lower_ae (mu : Measure ℝ) (J : ℕ)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i)) :
    ∀ᵐ x ∂mu, -9 ≤ normalValue x := by
  filter_upwards [hrange] with x hx
  obtain ⟨i, rfl⟩ := hx
  cases i with
  | inl i => exact fixedAtom_normalValue_lower (Sum.inl i)
  | inr j => exact fixedAtom_normalValue_lower (Sum.inr j.val)

private theorem sqrt_mul_exp_neg_bound (N a : ℝ) (hN : 1 ≤ N) (ha : 0 < a) :
    Real.sqrt N * Real.exp (-a * N) ≤ 1 / a + 1 := by
  have hroot : Real.sqrt N ≤ N := Real.sqrt_le_self_iff.mpr (Or.inr hN)
  have hexp : a * N ≤ Real.exp (a * N) := by
    linarith only [Real.add_one_le_exp (a * N)]
  have hcancel : Real.exp (a * N) * Real.exp (-a * N) = 1 := by
    rw [← Real.exp_add]
    have hzero : a * N + -a * N = 0 := by ring
    rw [hzero, Real.exp_zero]
  have hscaled := mul_le_mul_of_nonneg_right hexp (Real.exp_nonneg (-a * N))
  rw [hcancel] at hscaled
  have hlinear : N * Real.exp (-a * N) ≤ 1 / a :=
    (le_div_iff₀ ha).mpr (by nlinarith only [hscaled])
  calc
    _ ≤ N * Real.exp (-a * N) :=
      mul_le_mul_of_nonneg_right hroot (Real.exp_nonneg _)
    _ ≤ 1 / a := hlinear
    _ ≤ 1 / a + 1 := by linarith

theorem exists_global_source_negative_layer_bound (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q H ell : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq0 : 1 < q) (hq1 : q < 103 / 100) (hH0 : 50 < H) (hH1 : H < 51)
    (hell : 0 ≤ ell) (hellq : ell * q < 7 / 200)
    (henergy : ∀ᵐ x ∂mu, 1 ≤ x ^ 2 ∧ x ^ 2 ≤ 1 + H)
    (hmeanY : (∫ x : ℝ, normalValue x ∂mu) = q)
    (hmeanX : (∫ x : ℝ, x ∂mu) = q / 4)
    (hS : 0 < normalVariance mu) (hD : 0 < (parabolaCovariance mu).det)
    (hgap : ell < q / (32 * transverseVariance mu))
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    ∃ gamma C : ℝ, 0 < gamma ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop, ∀ k : ℝ, 0 ≤ k →
        Real.sqrt (n : ℝ) * Real.exp (ell * k) *
          (Measure.pi (fun _ : Fin n => mu)).real
            {z : Shao.Path n | normalDeviation q z = -k ∧ z ∈ sourceTail q n} ≤
          C * Real.exp (-gamma * k) := by
  classical
  have hq : 0 < q := lt_trans zero_lt_one hq0
  have hX : Integrable (fun x : ℝ => x) mu :=
    integrable_continuous_of_fixed_bounds mu hb _ continuous_id
  have hX2 : Integrable (fun x : ℝ => x ^ 2) mu :=
    integrable_continuous_of_fixed_bounds mu hb _ (by fun_prop)
  have hmoment : (∫ x : ℝ, normalValue x ∂mu) =
      8 * (∫ x : ℝ, x ∂mu) - (∫ x : ℝ, x ^ 2 ∂mu) := by
    change (∫ x : ℝ, 8 * x - x ^ 2 ∂mu) = _
    rw [integral_sub (hX.const_mul 8) hX2, integral_const_mul]
  have hsecond : (∫ x : ℝ, x ^ 2 ∂mu) = q := by
    rw [hmeanY, hmeanX] at hmoment
    linarith only [hmoment]
  have hYlower := stage_normal_lower_ae mu J hrange
  obtain ⟨delta, gamma0, C0, hdelta, hgamma0, hC0, hlocal⟩ :=
    exists_local_source_negative_layer_bound mu J q ell hb hq hell
      hmeanY hmeanX hS hD hgap hrange hpos
  obtain ⟨Cfar, cfar, hCfar, hcfar, hfar⟩ :=
    exists_source_far_weighted_tail_bound mu hb q H ell delta
      hq0 hq1 hH0 hH1 hell hellq hdelta henergy hsecond
  let a : ℝ := cfar / 2
  let gammaFar : ℝ := cfar / 22
  let gamma : ℝ := min gamma0 gammaFar
  let C : ℝ := max C0 (Cfar * (1 / a + 1))
  have ha : 0 < a := div_pos hcfar (by norm_num)
  have hgammaFar : 0 < gammaFar := div_pos hcfar (by norm_num)
  have hgamma : 0 < gamma := lt_min hgamma0 hgammaFar
  have hC : 0 < C := lt_of_lt_of_le hC0 (le_max_left _ _)
  have hgg0 : gamma ≤ gamma0 := min_le_left _ _
  have hggf : gamma ≤ gammaFar := min_le_right _ _
  refine ⟨gamma, C, hgamma, hC, ?_⟩
  filter_upwards [hlocal, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  intro k hk
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hn1R : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  let nu : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
  let A : Set (Shao.Path n) :=
    {z | normalDeviation q z = -k ∧ z ∈ sourceTail q n}
  change Real.sqrt (n : ℝ) * Real.exp (ell * k) * nu.real A ≤ C * Real.exp (-gamma * k)
  by_cases hsmall : k / (n : ℝ) ≤ delta
  · have hexp : Real.exp (-gamma0 * k) ≤ Real.exp (-gamma * k) :=
      Real.exp_le_exp.mpr (by nlinarith only [hgg0, hk])
    calc
      _ ≤ C0 * Real.exp (-gamma0 * k) := hn k hk hsmall
      _ ≤ C0 * Real.exp (-gamma * k) := mul_le_mul_of_nonneg_left hexp hC0.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
  · have hcoords : ∀ᵐ z ∂nu, ∀ i : Fin n, -9 ≤ normalValue (z i) := by
      apply ae_all_iff.mpr
      intro i
      exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => mu) (i := i)).eventually hYlower
    have hMlower : ∀ᵐ z ∂nu, -(11 : ℝ) * (n : ℝ) ≤ normalDeviation q z := by
      filter_upwards [hcoords] with z hz
      have hsum : -(9 : ℝ) * (n : ℝ) ≤ ∑ i : Fin n, normalValue (z i) := by
        calc
          _ = ∑ _ : Fin n, (-9 : ℝ) := by simp [mul_comm]
          _ ≤ _ := Finset.sum_le_sum (fun i _ => hz i)
      have hq2 : q ≤ 2 := by linarith only [hq1]
      have hqN := mul_le_mul_of_nonneg_left hq2 hnR.le
      dsimp only [normalDeviation]
      linarith only [hsum, hqN]
    by_cases hlarge : 11 * (n : ℝ) < k
    · have hnull : nu A = 0 := by
        apply measure_eq_zero_iff_ae_notMem.mpr
        filter_upwards [hMlower] with z hz
        intro hzA
        have hMk : normalDeviation q z = -k := hzA.1
        linarith only [hz, hMk, hlarge]
      have hreal : nu.real A = 0 := by simp [measureReal_def, hnull]
      rw [hreal, mul_zero]
      exact mul_nonneg hC.le (Real.exp_nonneg _)
    · obtain ⟨hw, hfarN⟩ := hfar n hnpos
      let F : Set (Shao.Path n) :=
        {z | z ∈ sourceTail q n ∧ normalDeviation q z ≤ -delta * (n : ℝ)}
      have hM : Continuous (fun z : Shao.Path n => normalDeviation q z) := by
        unfold normalDeviation normalValue
        fun_prop
      have hA : MeasurableSet A :=
        (measurableSet_eq_fun hM.measurable measurable_const).inter (sourceTail_measurable q n)
      have hsubset : A ⊆ F := by
        intro z hz
        have hdk : delta * (n : ℝ) < k := (lt_div_iff₀ hnR).mp (lt_of_not_ge hsmall)
        exact ⟨hz.2, by linarith only [hdk, hz.1]⟩
      have hint : (∫ z : Shao.Path n in A, Real.exp (-ell * normalDeviation q z) ∂nu) =
          Real.exp (ell * k) * nu.real A := by
        calc
          _ = ∫ _z : Shao.Path n in A, Real.exp (ell * k) ∂nu :=
            setIntegral_congr_fun hA (fun z hz => by rw [hz.1]; congr 1; ring)
          _ = _ := by simp [smul_eq_mul, mul_comm, measureReal_def]
      have hweighted : Real.exp (ell * k) * nu.real A ≤ Cfar * Real.exp (-cfar * (n : ℝ)) := by
        calc
          _ = ∫ z : Shao.Path n in A, Real.exp (-ell * normalDeviation q z) ∂nu := hint.symm
          _ ≤ ∫ z : Shao.Path n in F, Real.exp (-ell * normalDeviation q z) ∂nu :=
            setIntegral_mono_set hw.integrableOn
              (Filter.Eventually.of_forall fun z => Real.exp_nonneg _)
              (Filter.Eventually.of_forall fun z hz => hsubset hz)
          _ ≤ _ := hfarN
      have hkN : k ≤ 11 * (n : ℝ) := le_of_not_gt hlarge
      have hexp : Real.exp (-cfar * (n : ℝ)) ≤
          Real.exp (-a * (n : ℝ)) * Real.exp (-gammaFar * k) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hm := mul_le_mul_of_nonneg_left hkN hcfar.le
        dsimp only [a, gammaFar]
        nlinarith only [hm]
      have hpre := sqrt_mul_exp_neg_bound (n : ℝ) a hn1R ha
      have hgammaExp : Real.exp (-gammaFar * k) ≤ Real.exp (-gamma * k) :=
        Real.exp_le_exp.mpr (by nlinarith only [hggf, hk])
      calc
        _ = Real.sqrt (n : ℝ) * (Real.exp (ell * k) * nu.real A) := by ring
        _ ≤ Real.sqrt (n : ℝ) * (Cfar * Real.exp (-cfar * (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hweighted (Real.sqrt_nonneg _)
        _ ≤ Real.sqrt (n : ℝ) *
            (Cfar * (Real.exp (-a * (n : ℝ)) * Real.exp (-gammaFar * k))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hCfar.le)
            (Real.sqrt_nonneg _)
        _ = (Cfar * (Real.sqrt (n : ℝ) * Real.exp (-a * (n : ℝ)))) *
            Real.exp (-gammaFar * k) := by ring
        _ ≤ (Cfar * (1 / a + 1)) * Real.exp (-gammaFar * k) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpre hCfar.le)
            (Real.exp_nonneg _)
        _ ≤ C * Real.exp (-gammaFar * k) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left hgammaExp hC.le

end
end Shao.OQ3
