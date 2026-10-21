import Shao.Probability.RetainedVariance
import Shao.Probability.RetentionEvent
import Shao.Probability.MeasurablePath
import Shao.Basic.Deletion

/-!
# The genuine fixed-fiber retained comparison

The normalized law is the actual affine pushforward of the existing cutoff
law. The crossing comparison retains the original weak event and its actual
energy: the standardized product event first restores every raw coordinate.
No Gaussian tail comparison is assumed or asserted.
-/

set_option autoImplicit false

namespace Shao

open MeasureTheory ProbabilityTheory

noncomputable def retainedStandardize (ν : Measure ℝ) (x z : ℝ) : ℝ :=
  let μx : ℝ := ∫ u : ℝ, u ∂retainedCutoffLaw ν x
  let Vx : ℝ := ∫ u : ℝ, (u - μx) ^ 2 ∂retainedCutoffLaw ν x
  (z - μx) / Real.sqrt Vx

noncomputable def retainedStandardLaw (ν : Measure ℝ) (x : ℝ) : Measure ℝ :=
  Measure.map (retainedStandardize ν x) (retainedCutoffLaw ν x)

private theorem measurable_retainedStandardize (ν : Measure ℝ) (x : ℝ) :
    Measurable (retainedStandardize ν x) :=
  (measurable_id.sub measurable_const).div measurable_const

namespace Probability

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem retained_cond_transform_path_map_eq_pi
    {μ : Measure Ω} {ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (s : Finset (Fin n)) (hs : 0 < s.card)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hA : μ {ω | retentionSet X B ω = s} ≠ 0)
    (g : ℝ → ℝ) (hg : Measurable g) :
    Measure.map
        (fun ω (r : Fin s.card) => g (X (Shao.retainedIndex s r) ω))
        (cond μ {ω | retentionSet X B ω = s}) =
      Measure.pi (fun _ : Fin s.card => Measure.map g (cond ν B)) := by
  obtain ⟨hBpos, hI, hL⟩ := iid_retained_cond_retentionSet_eq hX hIndep hLaw s hs B hB hA
  have : IsProbabilityMeasure (cond μ {ω | retentionSet X B ω = s}) :=
    cond_isProbabilityMeasure hA
  have : IsProbabilityMeasure (cond ν B) := cond_isProbabilityMeasure hBpos
  let Y : Ω → Path s.card := fun ω r => X (retainedIndex s r) ω
  let G : Path s.card → Path s.card := fun a r => g (a r)
  have hY : Measurable Y := Measurable.of_eval (fun r => hX (retainedIndex s r))
  have hG : Measurable G := Measurable.of_eval (fun r => hg.comp (measurable_pi_apply r))
  have hraw : Measure.map Y (cond μ {ω | retentionSet X B ω = s}) =
      Measure.pi (fun _ : Fin s.card => cond ν B) :=
    iid_samplePath_map_eq_pi (fun r => hX (retainedIndex s r)) hI hL
  calc
    _ = Measure.map G (Measure.map Y (cond μ {ω | retentionSet X B ω = s})) :=
      (Measure.map_map hG hY).symm
    _ = Measure.map G (Measure.pi (fun _ : Fin s.card => cond ν B)) := by rw [hraw]
    _ = _ := Measure.pi_map_pi (fun _ : Fin s.card => hg.aemeasurable)

end Probability

theorem retainedStandardLaw_moments
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n j : ℕ) (x : ℝ)
    (hx : 2 ≤ x) (hsize : x ^ 6 ≤ (n : ℝ))
    (hj : (j : ℝ) ≤ x ^ 2 / 2)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hmean : (∫ z : ℝ, z ∂ν) = 0)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (hcut : (n : ℝ) * (∫ z : ℝ, truncationF (x * z) ∂ν) ≤ 1) :
    IsProbabilityMeasure (retainedStandardLaw ν x) ∧
      Integrable (fun z : ℝ => z) (retainedStandardLaw ν x) ∧
      Integrable (fun z : ℝ => z ^ 2) (retainedStandardLaw ν x) ∧
      Integrable (fun z : ℝ => |z| ^ 3) (retainedStandardLaw ν x) ∧
      (∫ z : ℝ, z ∂retainedStandardLaw ν x) = 0 ∧
      (∫ z : ℝ, z ^ 2 ∂retainedStandardLaw ν x) = 1 ∧
      (∫ z : ℝ, |z| ^ 3 ∂retainedStandardLaw ν x) /
          Real.sqrt ((n - j : ℕ) : ℝ) ≤
        64 / (Real.sqrt (x ^ 2 - (j : ℝ))) ^ 3 := by
  let η : Measure ℝ := retainedCutoffLaw ν x
  let μx : ℝ := ∫ z : ℝ, z ∂η
  let Vx : ℝ := ∫ z : ℝ, (z - μx) ^ 2 ∂η
  let τx : ℝ := Real.sqrt Vx
  let Z : ℝ → ℝ := retainedStandardize ν x
  let ζ : Measure ℝ := retainedStandardLaw ν x
  obtain ⟨hn64, _, _, _, _⟩ := retainedSample_size_bounds n j x hx hsize hj
  have hn2 : 2 ≤ n := by omega
  have hxpos : 0 < x := by linarith
  obtain ⟨_, hqhalf, _⟩ := retainedCutoffMass_bounds ν n hn2 x hxpos h2 hcut
  have hq : 0 < retainedCutoffMass ν x := by linarith
  have : IsProbabilityMeasure η := retainedCutoffLaw_isProbabilityMeasure ν x hq
  have hζprob : IsProbabilityMeasure ζ := by dsimp only [ζ, retainedStandardLaw]; infer_instance
  obtain ⟨hc1, hc2, hc3, hcmean, _, _⟩ := retainedCutoffLaw_centered_moments ν x hxpos hq h2
  change Integrable (fun z : ℝ => z - μx) η at hc1
  change Integrable (fun z : ℝ => (z - μx) ^ 2) η at hc2
  change Integrable (fun z : ℝ => |z - μx| ^ 3) η at hc3
  change (∫ z : ℝ, z - μx ∂η) = 0 at hcmean
  obtain ⟨_, hVpos, _, _⟩ :=
    retainedSample_variance_third_moment_bounds ν n j x hx hsize hj h2 hmean hnorm hcut
  change 0 < Vx at hVpos
  have hτpos : 0 < τx := Real.sqrt_pos.mpr hVpos
  have hτ2 : τx ^ 2 = Vx := Real.sq_sqrt hVpos.le
  have hZ (z : ℝ) : Z z = (z - μx) / τx := rfl
  have hZmeas : Measurable Z := measurable_retainedStandardize ν x
  have hZ1 : Integrable Z η := hc1.div_const τx
  have hZ2 : Integrable (fun z : ℝ => (Z z) ^ 2) η := by
    apply (hc2.div_const (τx ^ 2)).congr
    exact ae_of_all η (fun z => by
      change (z - μx) ^ 2 / τx ^ 2 = (Z z) ^ 2
      rw [hZ, div_pow])
  have hZcube (z : ℝ) : |Z z| ^ 3 = |z - μx| ^ 3 / τx ^ 3 := by
    rw [hZ, abs_div, abs_of_pos hτpos, div_pow]
  have hZ3 : Integrable (fun z : ℝ => |Z z| ^ 3) η :=
    (hc3.div_const (τx ^ 3)).congr (ae_of_all η (fun z => (hZcube z).symm))
  have h1 : Integrable (fun z : ℝ => z) ζ :=
    (integrable_map_measure continuous_id.aestronglyMeasurable hZmeas.aemeasurable).mpr hZ1
  have h2ζ : Integrable (fun z : ℝ => z ^ 2) ζ :=
    (integrable_map_measure (continuous_id.pow 2).aestronglyMeasurable hZmeas.aemeasurable).mpr hZ2
  have h3 : Integrable (fun z : ℝ => |z| ^ 3) ζ :=
    (integrable_map_measure (continuous_abs.pow 3).aestronglyMeasurable hZmeas.aemeasurable).mpr hZ3
  have hmeanζ : (∫ z : ℝ, z ∂ζ) = 0 := by
    change (∫ z : ℝ, z ∂Measure.map Z η) = 0
    rw [integral_map (μ := η) (φ := Z) (f := fun z : ℝ => z)
      hZmeas.aemeasurable continuous_id.aestronglyMeasurable]
    change (∫ z : ℝ, (z - μx) / τx ∂η) = 0
    rw [integral_div, hcmean, zero_div]
  have hsecondζ : (∫ z : ℝ, z ^ 2 ∂ζ) = 1 := by
    change (∫ z : ℝ, z ^ 2 ∂Measure.map Z η) = 1
    rw [integral_map (μ := η) (φ := Z) (f := fun z : ℝ => z ^ 2)
      hZmeas.aemeasurable (continuous_id.pow 2).aestronglyMeasurable]
    simp_rw [hZ, div_pow]
    rw [integral_div]
    change Vx / τx ^ 2 = 1
    rw [hτ2, div_self hVpos.ne']
  have hcubeζ : (∫ z : ℝ, |z| ^ 3 ∂ζ) =
      (∫ z : ℝ, |z - μx| ^ 3 ∂η) / τx ^ 3 := by
    change (∫ z : ℝ, |z| ^ 3 ∂Measure.map Z η) = _
    rw [integral_map (μ := η) (φ := Z) (f := fun z : ℝ => |z| ^ 3)
      hZmeas.aemeasurable (continuous_abs.pow 3).aestronglyMeasurable]
    simp_rw [hZcube]
    rw [integral_div]
  refine ⟨hζprob, h1, h2ζ, h3, hmeanζ, hsecondζ, ?_⟩
  change (∫ z : ℝ, |z| ^ 3 ∂ζ) / Real.sqrt ((n - j : ℕ) : ℝ) ≤ _
  rw [hcubeζ, div_div, mul_comm (τx ^ 3)]
  exact retainedSample_lyapunov_bound ν n j x hx hsize hj h2 hmean hnorm hcut

namespace Probability

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem retained_cond_upperCrossing_comparison
    {μ : Measure Ω} {ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (s : Finset (Fin n)) (x : ℝ)
    (hx : 2 ≤ x) (hsize : x ^ 6 ≤ (n : ℝ))
    (hj : ((n - s.card : ℕ) : ℝ) ≤ x ^ 2 / 2)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hmean : (∫ z : ℝ, z ∂ν) = 0)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (hcut : (n : ℝ) * (∫ z : ℝ, Shao.truncationF (x * z) ∂ν) ≤ 1)
    (hA : μ {ω | retentionSet X (Shao.retainedCutoffSet x) ω = s} ≠ 0) :
    let A : Set Ω := {ω | retentionSet X (Shao.retainedCutoffSet x) ω = s}
    let j : ℕ := n - s.card
    let η : Measure ℝ := Shao.retainedCutoffLaw ν x
    let ζ : Measure ℝ := Shao.retainedStandardLaw ν x
    let μx : ℝ := ∫ z : ℝ, z ∂η
    let τx : ℝ := Real.sqrt (∫ z : ℝ, (z - μx) ^ 2 ∂η)
    let y : ℝ := Real.sqrt (x ^ 2 - (j : ℝ))
    ∃ hn : 0 < n, ∃ hs : 0 < s.card,
      (cond μ A) {ω | samplePath X ω ∈ Shao.upperCrossing hn x} ≤
        (Measure.pi (fun _ : Fin s.card => η)) (Shao.upperCrossing hs y) ∧
      (Measure.pi (fun _ : Fin s.card => η)) (Shao.upperCrossing hs y) =
        (Measure.pi (fun _ : Fin s.card => ζ))
          {a : Shao.Path s.card |
            (fun r : Fin s.card => μx + τx * a r) ∈ Shao.upperCrossing hs y} := by
  classical
  let A : Set Ω := {ω | retentionSet X (retainedCutoffSet x) ω = s}
  let j : ℕ := n - s.card
  let η : Measure ℝ := retainedCutoffLaw ν x
  let ζ : Measure ℝ := retainedStandardLaw ν x
  let μx : ℝ := ∫ z : ℝ, z ∂η
  let τx : ℝ := Real.sqrt (∫ z : ℝ, (z - μx) ^ 2 ∂η)
  let y : ℝ := Real.sqrt (x ^ 2 - (j : ℝ))
  have hcard : s.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ s
  have hret : n - j = s.card := Nat.sub_sub_self hcard
  obtain ⟨hn64, hjn, hm1, _, _⟩ := retainedSample_size_bounds n j x hx hsize hj
  have hn : 0 < n := by omega
  have hs : 0 < s.card := by omega
  have hxpos : 0 < x := by linarith
  have hxx : (j : ℝ) < x ^ 2 := by nlinarith only [hj, sq_pos_of_pos hxpos]
  have hIcard : sᶜ.card = j := by simp only [Finset.card_compl, Fintype.card_fin, j]
  have hIlt : sᶜ.card < n := by rw [hIcard]; exact hjn
  have hcomp : Finset.univ \ sᶜ = s := by ext i; simp
  let Y : Ω → Path s.card := fun ω => retainedPath (samplePath X ω) s
  have hYmeas : Measurable Y := Measurable.of_eval (fun r => hX (retainedIndex s r))
  have hraw : Measure.map Y (cond μ A) = Measure.pi (fun _ : Fin s.card => η) := by
    change Measure.map (fun ω (r : Fin s.card) => X (retainedIndex s r) ω)
      (cond μ {ω | retentionSet X (retainedCutoffSet x) ω = s}) =
      Measure.pi (fun _ : Fin s.card => cond ν (retainedCutoffSet x))
    simpa only [Measure.map_id, id_eq] using
      retained_cond_transform_path_map_eq_pi hX hIndep hLaw s hs (retainedCutoffSet x)
        (measurableSet_retainedCutoffSet x) hA id measurable_id
  have hrawprob : (Measure.pi (fun _ : Fin s.card => η)) (upperCrossing hs y) =
      (cond μ A) {ω | Y ω ∈ upperCrossing hs y} := by
    rw [← hraw, Measure.map_apply hYmeas (measurableSet_upperCrossing hs y)]
    rfl
  have hsub : {ω | samplePath X ω ∈ upperCrossing hn x} ⊆
      {ω | Y ω ∈ upperCrossing hs y} := by
    intro ω hω
    have hdel := upperCrossing_retainedPath_of_deletion (samplePath X ω) sᶜ hn hIlt x hxpos
      (by rw [hIcard]; exact hxx) hω
    have hdel' : ∀ ht : 0 < (Finset.univ \ sᶜ).card,
        retainedPath (samplePath X ω) (Finset.univ \ sᶜ) ∈
          upperCrossing ht (Real.sqrt (x ^ 2 - (sᶜ.card : ℝ))) := fun _ => hdel
    rw [hcomp, hIcard] at hdel'
    exact hdel' hs
  have hineq : (cond μ A) {ω | samplePath X ω ∈ upperCrossing hn x} ≤
      (Measure.pi (fun _ : Fin s.card => η)) (upperCrossing hs y) := by
    rw [hrawprob]
    exact measure_mono hsub
  obtain ⟨_, hVpos, _, _⟩ :=
    retainedSample_variance_third_moment_bounds ν n j x hx hsize hj h2 hmean hnorm hcut
  have hτpos : 0 < τx := Real.sqrt_pos.mpr hVpos
  let G : Ω → Path s.card := fun ω r => retainedStandardize ν x (X (retainedIndex s r) ω)
  let R : Path s.card → Path s.card := fun a r => μx + τx * a r
  have hGmeas : Measurable G := Measurable.of_eval
    (fun r => (measurable_retainedStandardize ν x).comp (hX (retainedIndex s r)))
  have hRmeas : Measurable R := Measurable.of_eval
    (fun r => measurable_const.add (measurable_const.mul (measurable_pi_apply r)))
  have hstd : Measure.map G (cond μ A) = Measure.pi (fun _ : Fin s.card => ζ) :=
    retained_cond_transform_path_map_eq_pi hX hIndep hLaw s hs (retainedCutoffSet x)
      (measurableSet_retainedCutoffSet x) hA (retainedStandardize ν x)
      (measurable_retainedStandardize ν x)
  have hrestore (ω : Ω) : R (G ω) = Y ω := by
    funext r
    change μx + τx * retainedStandardize ν x (X (retainedIndex s r) ω) =
      X (retainedIndex s r) ω
    change μx + τx * ((X (retainedIndex s r) ω - μx) / τx) = _
    field_simp [hτpos.ne']
    ring
  have hEstd : MeasurableSet {a : Path s.card | R a ∈ upperCrossing hs y} :=
    (measurableSet_upperCrossing hs y).preimage hRmeas
  have hstdprob : (Measure.pi (fun _ : Fin s.card => ζ))
        {a : Path s.card | R a ∈ upperCrossing hs y} =
      (cond μ A) {ω | R (G ω) ∈ upperCrossing hs y} := by
    rw [← hstd, Measure.map_apply hGmeas hEstd]
    rfl
  refine ⟨hn, hs, hineq, ?_⟩
  change (Measure.pi (fun _ : Fin s.card => η)) (upperCrossing hs y) =
    (Measure.pi (fun _ : Fin s.card => ζ)) {a : Path s.card | R a ∈ upperCrossing hs y}
  rw [hrawprob, hstdprob]
  congr 1
  ext ω
  change Y ω ∈ upperCrossing hs y ↔ R (G ω) ∈ upperCrossing hs y
  rw [hrestore]

end Probability

end Shao
