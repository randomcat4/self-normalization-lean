import Shao.OQ3.NormalTrialCost
import Shao.OQ3.CompactTiltLayerMassBound
import Shao.OQ3.CenteredSampleTilt

namespace Shao.OQ3
open MeasureTheory Filter
open scoped BigOperators
noncomputable section

private theorem sample_projection_eq (q a v s : ℝ) (n : ℕ) (z : Shao.Path n) :
    centeredSampleProjection q a v s n z =
      v * normalDeviation q z + s * ((∑ i : Fin n, z i) - (n : ℝ) * a) := by
  unfold centeredSampleProjection centeredNormalProjection normalDeviation
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private theorem trial_tangent_sign (T b N k r sigma : ℝ)
    (hT : 0 < T) (hN : 0 < N) (hk : 0 ≤ k) (_hr : 0 ≤ r)
    (hbr : |b| * k ≤ r) (hsigma : sigma = 1 ∨ sigma = -1) :
    0 ≤ ((sigma * r / N - b * (-k / N)) / T) * sigma := by
  have hlo := mul_le_mul_of_nonneg_right (neg_abs_le b) hk
  have hhi := mul_le_mul_of_nonneg_right (le_abs_self b) hk
  rcases hsigma with rfl | rfl
  · simp only [one_mul, mul_one]
    rw [show r / N - b * (-k / N) = (r + b * k) / N by ring]
    exact div_nonneg (div_nonneg (by nlinarith only [hbr, hlo]) hN.le) hT.le
  · simp only [neg_one_mul, mul_neg, mul_one]
    apply neg_nonneg.mpr
    rw [show -r / N - b * (-k / N) = (-r + b * k) / N by ring]
    exact div_nonpos_of_nonpos_of_nonneg
      (div_nonpos_of_nonpos_of_nonneg (by nlinarith only [hbr, hhi]) hN.le) hT.le

theorem exists_local_negative_layer_tail_bound (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q a ell : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : 0 < q) (hell : 0 ≤ ell)
    (hmeanY : (∫ x : ℝ, normalValue x ∂mu) = q)
    (hmeanX : (∫ x : ℝ, x ∂mu) = a)
    (hS : 0 < normalVariance mu) (hD : 0 < (parabolaCovariance mu).det)
    (hgap : ell < q / (32 * transverseVariance mu))
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    ∃ delta gamma c C : ℝ, 0 < delta ∧ 0 < gamma ∧ 0 < c ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop, ∀ k r : ℝ, 0 ≤ k → 0 ≤ r →
        k / (n : ℝ) ≤ delta → r / (n : ℝ) ≤ delta →
          (n : ℝ) * q * k / 16 ≤ r ^ 2 →
            Real.sqrt (n : ℝ) * Real.exp (ell * k) *
              (Measure.pi (fun _ : Fin n => mu)).real
                {z : Shao.Path n | normalDeviation q z = -k ∧
                  r ≤ |(∑ i : Fin n, z i) - (n : ℝ) * a|} ≤
              C * Real.exp (-gamma * k - c * r ^ 2 / (n : ℝ)) := by
  let b : ℝ := ProbabilityTheory.covariance normalValue (fun x : ℝ => x) mu / normalVariance mu
  have hT : 0 < transverseVariance mu := div_pos hD hS
  obtain ⟨delta0, gamma, c, hdelta0, hgamma, hc, hweight⟩ :=
    exists_normalTrialCost_weight_margin mu hb q a ell hq hell hmeanY hmeanX hS hD hgap
  let delta : ℝ := min delta0 (min 1 (q / (64 * (b ^ 2 + 1))))
  have hden : 0 < 64 * (b ^ 2 + 1) := by positivity
  have hdelta : 0 < delta := lt_min hdelta0 (lt_min (by norm_num) (div_pos hq hden))
  have hd0 : delta ≤ delta0 := min_le_left _ _
  have hd1 : delta ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hdq : delta ≤ q / (64 * (b ^ 2 + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  let Q : Set (ℝ × ℝ) := Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1
  let psi : (ℝ × ℝ) → (ℝ × ℝ) := fun yz =>
    (8 * (normalTrialTilt mu yz.1 yz.2).1 + (normalTrialTilt mu yz.1 yz.2).2,
      -(normalTrialTilt mu yz.1 yz.2).1)
  have hpsi : Continuous psi := by dsimp [psi, normalTrialTilt]; fun_prop
  let K : Set (ℝ × ℝ) := psi '' Q
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image hpsi
  obtain ⟨C0, hC0, hfamily⟩ := exists_compact_tilted_normal_layer_mass_bound
    mu J q a hb hmeanY hmeanX hS hD hrange hpos K hK
  refine ⟨delta, gamma, c, 2 * C0, hdelta, hgamma, hc, by positivity, ?_⟩
  filter_upwards [hfamily, eventually_ge_atTop (1 : ℕ)] with n hnfamily hn1
  intro k r hk hr hkdelta hrdelta hcurve
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hkq : k / (n : ℝ) ≤ q / (64 * (b ^ 2 + 1)) := hkdelta.trans hdq
  have hlinear : (b ^ 2 + 1) * k ≤ (n : ℝ) * q / 64 := by
    have hh := (div_le_div_iff₀ hnpos hden).mp hkq
    nlinarith only [hh]
  have hmult := mul_le_mul_of_nonneg_right hlinear hk
  have hsq : (b * k) ^ 2 ≤ (r / 2) ^ 2 := by
    nlinarith only [hmult, hcurve, sq_nonneg k]
  have habssq : (|b| * k) ^ 2 ≤ (r / 2) ^ 2 := by
    simpa only [mul_pow, sq_abs] using hsq
  have hbrhalf : |b| * k ≤ r / 2 :=
    (sq_le_sq₀ (mul_nonneg (abs_nonneg b) hk) (by positivity)).mp habssq
  have hbr : |b| * k ≤ r := by linarith
  have hR : Continuous (fun z : Shao.Path n => (∑ i : Fin n, z i) - (n : ℝ) * a) := by fun_prop
  have hM : Continuous (fun z : Shao.Path n => normalDeviation q z) := by
    unfold normalDeviation normalValue
    fun_prop
  let E (sigma : ℝ) : Set (Shao.Path n) :=
    {z | normalDeviation q z = -k ∧ r ≤ sigma * ((∑ i : Fin n, z i) - (n : ℝ) * a)}
  have hbranch : ∀ sigma : ℝ, sigma = 1 ∨ sigma = -1 →
      Real.sqrt (n : ℝ) * Real.exp (ell * k) * (Measure.pi (fun _ : Fin n => mu)).real (E sigma) ≤
        C0 * Real.exp (-gamma * k - c * r ^ 2 / (n : ℝ)) := by
    intro sigma hsigma
    have hsigma2 : sigma ^ 2 = 1 := by rcases hsigma with rfl | rfl <;> norm_num
    have habsr : |sigma * r| = r := by
      rcases hsigma with rfl | rfl <;> simp [abs_of_nonneg hr]
    have hsqrs : (sigma * r) ^ 2 = r ^ 2 := by rw [mul_pow, hsigma2, one_mul]
    let y : ℝ := -k / (n : ℝ)
    let z0 : ℝ := sigma * r / (n : ℝ)
    let v : ℝ := (normalTrialTilt mu y z0).1
    let s : ℝ := (normalTrialTilt mu y z0).2
    have hssigma : 0 ≤ s * sigma := by
      exact trial_tangent_sign (transverseVariance mu) b (n : ℝ) k r sigma hT hnpos hk hr hbr hsigma
    have hy : -1 ≤ y ∧ y ≤ 1 := by
      have hkn : 0 ≤ k / (n : ℝ) := div_nonneg hk hnpos.le
      have hk1 := hkdelta.trans hd1
      dsimp only [y]
      rw [neg_div]
      constructor <;> linarith
    have hzabs : |z0| ≤ 1 := by
      dsimp only [z0]
      rw [abs_div, habsr, abs_of_pos hnpos]
      exact hrdelta.trans hd1
    have hpK : psi (y, z0) ∈ K := ⟨(y, z0), ⟨hy, abs_le.mp hzabs⟩, rfl⟩
    have hE : MeasurableSet (E sigma) :=
      (isClosed_eq hM continuous_const).measurableSet.inter
        (measurableSet_le measurable_const (continuous_const.mul hR).measurable)
    have hlower : ∀ path ∈ E sigma,
        v * (-k) + s * (sigma * r) ≤ centeredSampleProjection q a v s n path := by
      intro path hpath
      have hlin : s * (sigma * r) ≤ s * ((∑ i : Fin n, path i) - (n : ℝ) * a) := by
        calc
          _ = (s * sigma) * r := by ring
          _ ≤ (s * sigma) * (sigma * ((∑ i : Fin n, path i) - (n : ℝ) * a)) :=
            mul_le_mul_of_nonneg_left hpath.2 hssigma
          _ = s * ((∑ i : Fin n, path i) - (n : ℝ) * a) := by
            calc
              _ = s * sigma ^ 2 * ((∑ i : Fin n, path i) - (n : ℝ) * a) := by ring
              _ = _ := by rw [hsigma2, mul_one]
      rw [sample_projection_eq, hpath.1]
      exact add_le_add (le_refl _) hlin
    have hf : Integrable (fun x : ℝ => Real.exp (centeredNormalProjection q a v s x)) mu := by
      apply integrable_continuous_of_fixed_bounds mu hb
      unfold centeredNormalProjection normalValue
      fun_prop
    have _hZ : 0 < (∫ x : ℝ, Real.exp (centeredNormalProjection q a v s x) ∂mu) := integral_exp_pos hf
    let : IsProbabilityMeasure (mu.tilted (centeredNormalProjection q a v s)) :=
      isProbabilityMeasure_tilted hf
    have hchange := iid_centeredSample_event_bound mu hb q a v s n (E sigma) hE
      (v * (-k) + s * (sigma * r)) hlower
    have hfactor : (n : ℝ) * centeredNormalLogMGF mu q a v s - (v * (-k) + s * (sigma * r)) =
        -(n : ℝ) * normalTrialCost mu q a y z0 := by
      change (n : ℝ) * centeredNormalLogMGF mu q a v s - (v * (-k) + s * (sigma * r)) =
        -(n : ℝ) * (v * (-k / (n : ℝ)) + s * (sigma * r / (n : ℝ)) -
          centeredNormalLogMGF mu q a v s)
      field_simp [hnpos.ne']
      ring
    rw [hfactor] at hchange
    have hmass : Real.sqrt (n : ℝ) *
        (Measure.pi (fun _ : Fin n => mu.tilted (centeredNormalProjection q a v s))).real (E sigma) ≤ C0 := by
      calc
        _ ≤ Real.sqrt (n : ℝ) *
            (Measure.pi (fun _ : Fin n => mu.tilted (centeredNormalProjection q a v s))).real
              {path : Shao.Path n | normalDeviation q path = -k} :=
          mul_le_mul_of_nonneg_left (measureReal_mono (show E sigma ⊆
            {path : Shao.Path n | normalDeviation q path = -k} from fun path hpath => hpath.1)) (Real.sqrt_nonneg _)
        _ = Real.sqrt (n : ℝ) *
            (Measure.pi (fun _ : Fin n => mu.tilted
              (fun x : ℝ => (psi (y, z0)).1 * x + (psi (y, z0)).2 * x ^ 2))).real
              {path : Shao.Path n | normalDeviation q path = -k} := by
          rw [centeredProjection_tilt_eq_quadratic mu hb q a v s]
        _ ≤ C0 := hnfamily (psi (y, z0)) hpK (-k)
    have hmargin := hweight n hn1 k (sigma * r) hk (hkdelta.trans hd0)
      (by rw [habsr]; exact hrdelta.trans hd0) (by rw [hsqrs]; exact hcurve)
    rw [hsqrs] at hmargin
    let A : ℝ := ell * k - (n : ℝ) * normalTrialCost mu q a y z0
    have hA : A ≤ -gamma * k - c * r ^ 2 / (n : ℝ) := by
      dsimp only [A, y, z0]
      linarith only [hmargin]
    have hexp : Real.exp A = Real.exp (ell * k) *
        Real.exp (-(n : ℝ) * normalTrialCost mu q a y z0) := by
      dsimp only [A]
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ (Real.sqrt (n : ℝ) * Real.exp (ell * k)) *
          (Real.exp (-(n : ℝ) * normalTrialCost mu q a y z0) *
            (Measure.pi (fun _ : Fin n => mu.tilted (centeredNormalProjection q a v s))).real (E sigma)) :=
        mul_le_mul_of_nonneg_left hchange (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)
      _ = Real.exp A * (Real.sqrt (n : ℝ) *
          (Measure.pi (fun _ : Fin n => mu.tilted (centeredNormalProjection q a v s))).real (E sigma)) := by
        rw [hexp]
        ring
      _ ≤ Real.exp A * C0 := mul_le_mul_of_nonneg_left hmass (Real.exp_pos _).le
      _ ≤ Real.exp (-gamma * k - c * r ^ 2 / (n : ℝ)) * C0 :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hA) hC0.le
      _ = _ := mul_comm _ _
  have hcover : {path : Shao.Path n | normalDeviation q path = -k ∧
      r ≤ |(∑ i : Fin n, path i) - (n : ℝ) * a|} ⊆ E 1 ∪ E (-1) := by
    intro path hpath
    by_cases hz : 0 ≤ (∑ i : Fin n, path i) - (n : ℝ) * a
    · exact Or.inl ⟨hpath.1, by simpa only [abs_of_nonneg hz, one_mul] using hpath.2⟩
    · exact Or.inr ⟨hpath.1, by simpa only [abs_of_neg (lt_of_not_ge hz), neg_one_mul] using hpath.2⟩
  have hmassunion : (Measure.pi (fun _ : Fin n => mu)).real
      {path : Shao.Path n | normalDeviation q path = -k ∧
        r ≤ |(∑ i : Fin n, path i) - (n : ℝ) * a|} ≤
      (Measure.pi (fun _ : Fin n => mu)).real (E 1) +
        (Measure.pi (fun _ : Fin n => mu)).real (E (-1)) :=
    (measureReal_mono hcover).trans (measureReal_union_le _ _)
  calc
    _ ≤ (Real.sqrt (n : ℝ) * Real.exp (ell * k)) *
        ((Measure.pi (fun _ : Fin n => mu)).real (E 1) +
          (Measure.pi (fun _ : Fin n => mu)).real (E (-1))) :=
      mul_le_mul_of_nonneg_left hmassunion (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)
    _ = (Real.sqrt (n : ℝ) * Real.exp (ell * k)) * (Measure.pi (fun _ : Fin n => mu)).real (E 1) +
        (Real.sqrt (n : ℝ) * Real.exp (ell * k)) * (Measure.pi (fun _ : Fin n => mu)).real (E (-1)) := by ring
    _ ≤ C0 * Real.exp (-gamma * k - c * r ^ 2 / (n : ℝ)) +
        C0 * Real.exp (-gamma * k - c * r ^ 2 / (n : ℝ)) :=
      add_le_add (hbranch 1 (Or.inl rfl)) (hbranch (-1) (Or.inr rfl))
    _ = _ := by ring


end
end Shao.OQ3
