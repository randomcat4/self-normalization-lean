import Shao.OQ6.QuadraticTilt
import Shao.OQ6.ObservationProductTilt
import Shao.OQ6.ActualQuadraticTiltMoments
import Shao.OQ6.ResidualDeletion
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.L2Space

/-!
Literal partial observation tilts from original p37(17) and p39.
The omitted exponent retains the full denominator.  The resulting measure
has mass m_i inverse.  Genuine absolute integrability is established before
signed transport.  The source probability engine remains due to Shao--Zhou.
No weighted-rate, concentration or original-root conclusion is asserted.
-/

set_option autoImplicit false

namespace Shao.OQ6.PartialObservationTilt

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

private theorem pt_prod_split
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) (i : ι) (hi : i ∈ s) :
    (∏ j ∈ s, f j) = f i * ∏ j ∈ s.erase i, f j := by
  calc
    (∏ j ∈ s, f j) = ∏ j ∈ insert i (s.erase i), f j := by
      rw [Finset.insert_erase hi]
    _ = f i * ∏ j ∈ s.erase i, f j := by
      rw [Finset.prod_insert (by simp : i ∉ s.erase i)]

private theorem pt_measurable_prod
    {α ι : Type*} [MeasurableSpace α]
    (s : Finset ι) (f : ι → α → ℝ)
    (hf : ∀ j ∈ s, Measurable (f j)) :
    Measurable (fun z => ∏ j ∈ s, f j z) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
      intro hf
      simpa using (measurable_const : Measurable (fun _ : α => (1 : ℝ)))
  | @insert j s hj ih =>
      intro hf
      have hfj : Measurable (f j) := hf j (Finset.mem_insert_self j s)
      have hfs : Measurable (fun z => ∏ k ∈ s, f k z) :=
        ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))
      simpa only [Finset.prod_insert hj, Pi.mul_def] using hfj.mul hfs

private theorem pt_bounded_density_integrable
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (d : α → ℝ) (hd : Measurable d) (B : ℝ)
    (hd0 : ∀ z, 0 ≤ d z) (hdB : ∀ z, d z ≤ B)
    {f : α → ℝ} (hf : Integrable f μ) :
    Integrable f (μ.withDensity (fun z => ENNReal.ofReal (d z))) := by
  apply (integrable_withDensity_iff hd.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).2
  have hp : Integrable (fun z => f z * d z) μ :=
    hf.mul_bdd hd.aestronglyMeasurable (c := B)
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hd0 z)] using hdB z)
  simpa only [ENNReal.toReal_ofReal (hd0 _)] using hp

private theorem pt_bounded_density_L2
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (d : α → ℝ) (hd : Measurable d) (B : ℝ)
    (hd0 : ∀ z, 0 ≤ d z) (hdB : ∀ z, d z ≤ B)
    {f : α → ℝ} (hfm : Measurable f) (hf : MemLp f 2 μ) :
    MemLp f 2 (μ.withDensity (fun z => ENNReal.ofReal (d z))) := by
  apply (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).2
  exact pt_bounded_density_integrable μ d hd B hd0 hdB hf.integrable_sq

private theorem pt_pair_selection
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (j k : Fin n) (hjk : j ≠ k) :
    MeasurePreserving (fun ξ : Fin n → Ω => (ξ j, ξ k))
      (Measure.pi (fun _ : Fin n => μ)) (μ.prod μ) := by
  have hind : iIndepFun (fun l (ξ : Fin n → Ω) => ξ l)
      (Measure.pi (fun _ : Fin n => μ)) :=
    iIndepFun_pi (μ := fun _ : Fin n => μ)
      (X := fun _ (o : Ω) => o) (fun _ => measurable_id.aemeasurable)
  have hmap (l : Fin n) :
      (Measure.pi (fun _ : Fin n => μ)).map
        (fun ξ : Fin n → Ω => ξ l) = μ :=
    (measurePreserving_eval (μ := fun _ : Fin n => μ) l).map_eq
  refine ⟨(measurable_pi_apply j).prodMk (measurable_pi_apply k), ?_⟩
  simpa only [hmap] using (hind.indepFun hjk).map_prod_eq_prod_map_map
    (measurable_pi_apply j).aemeasurable (measurable_pi_apply k).aemeasurable

private theorem pt_row_L2
    {X : Type*} [MeasurableSpace X] (ν : Measure X) (n : ℕ)
    (E : X → Fin n → Fin n → ℝ)
    (hE : ∀ j k : Fin n, j ≠ k → MemLp (fun ξ => E ξ j k) 2 ν)
    (j : Fin n) :
    MemLp (fun ξ => Shao.OQ6.ResidualDeletion.rowSum (E ξ) j) 2 ν := by
  classical
  unfold Shao.OQ6.ResidualDeletion.rowSum
  exact memLp_finsetSum _ (fun k hk =>
    hE j k (Finset.mem_erase.mp hk).1.symm)

private theorem pt_pair_sum_L2
    {X : Type*} [MeasurableSpace X] (ν : Measure X) (n : ℕ)
    (E : X → Fin n → Fin n → ℝ)
    (hE : ∀ j k : Fin n, j ≠ k → MemLp (fun ξ => E ξ j k) 2 ν) :
    MemLp (fun ξ => Shao.OQ5.P35.unorderedPairSum (E ξ)) 2 ν := by
  classical
  unfold Shao.OQ5.P35.unorderedPairSum
  apply memLp_finsetSum
  intro j hj
  apply memLp_finsetSum
  intro k hk
  by_cases hjk : j < k
  · simpa only [if_pos hjk] using hE j k (ne_of_lt hjk)
  · simp only [if_neg hjk]
    simp

theorem finite_observation_partial_tilt_transport
    {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (mu : Fin n → Measure Ω)
    [∀ j : Fin n, IsProbabilityMeasure (mu j)]
    (phi : Fin n → Ω → ℝ)
    (hExp : ∀ j : Fin n,
      Integrable (fun o : Ω => Real.exp (phi j o)) (mu j))
    (i : Fin n) :
    let m : Fin n → ℝ := fun j =>
      ∫ o : Ω, Real.exp (phi j o) ∂(mu j)
    let I : ℝ := ∏ j : Fin n, m j
    let P : Measure (Fin n → Ω) := Measure.pi mu
    let S : (Fin n → Ω) → ℝ := fun xi =>
      ∑ j : Fin n, phi j (xi j)
    let Sminus : (Fin n → Ω) → ℝ := fun xi =>
      ∑ j ∈ Finset.univ.erase i, phi j (xi j)
    let H : Measure (Fin n → Ω) := Measure.pi
      (fun j : Fin n => if j = i then mu j else (mu j).tilted (phi j))
    let R : (Fin n → Ω) → ℝ := fun xi => Real.exp (Sminus xi) / I
    let Q : Measure (Fin n → Ω) :=
      P.withDensity (fun xi => ENNReal.ofReal (R xi))
    (∀ j : Fin n, 0 < m j) ∧ 0 < I ∧
      Integrable (fun xi => Real.exp (S xi)) P ∧
      (∫ xi, Real.exp (S xi) ∂P) = I ∧
      Integrable (fun xi => Real.exp (Sminus xi)) P ∧
      (∫ xi, Real.exp (Sminus xi) ∂P) =
        (∏ j ∈ Finset.univ.erase i, m j) ∧
      I = m i * (∏ j ∈ Finset.univ.erase i, m j) ∧
      (∀ xi, R xi = (m i)⁻¹ *
        (∏ j ∈ Finset.univ.erase i, Real.exp (phi j (xi j)) / m j)) ∧
      P.tilted Sminus = H ∧ IsProbabilityMeasure H ∧
      Q = ENNReal.ofReal ((m i)⁻¹) • H ∧
      IsFiniteMeasure Q ∧ Q Set.univ = ENNReal.ofReal ((m i)⁻¹) ∧
      Integrable R P ∧ (∫ xi, R xi ∂P) = (m i)⁻¹ ∧
      (∀ f : (Fin n → Ω) → ℝ, Integrable f H →
        Integrable (fun xi => R xi * |f xi|) P ∧
        (∫ xi, R xi * |f xi| ∂P) =
          (m i)⁻¹ * (∫ xi, |f xi| ∂H) ∧
        Integrable (fun xi => R xi * f xi) P ∧
        Integrable f Q ∧
        (∫ xi, R xi * f xi ∂P) =
          (m i)⁻¹ * (∫ xi, f xi ∂H) ∧
        (∫ xi, f xi ∂Q) = (m i)⁻¹ * (∫ xi, f xi ∂H)) := by
  classical
  let m : Fin n → ℝ := fun j => ∫ o : Ω, Real.exp (phi j o) ∂(mu j)
  let I : ℝ := ∏ j : Fin n, m j
  let P : Measure (Fin n → Ω) := Measure.pi mu
  let S : (Fin n → Ω) → ℝ := fun xi => ∑ j : Fin n, phi j (xi j)
  let Sminus : (Fin n → Ω) → ℝ := fun xi =>
    ∑ j ∈ Finset.univ.erase i, phi j (xi j)
  let H : Measure (Fin n → Ω) := Measure.pi
    (fun j : Fin n => if j = i then mu j else (mu j).tilted (phi j))
  let R : (Fin n → Ω) → ℝ := fun xi => Real.exp (Sminus xi) / I
  let Q : Measure (Fin n → Ω) :=
    P.withDensity (fun xi => ENNReal.ofReal (R xi))
  let J : ℝ := ∏ j ∈ Finset.univ.erase i, m j
  let psi : Fin n → Ω → ℝ := fun j o => if j = i then 0 else phi j o
  letI : IsProbabilityMeasure P := by
    dsimp only [P]
    infer_instance
  have hm (j : Fin n) : 0 < m j := integral_exp_pos (hExp j)
  have hI : 0 < I := Finset.prod_pos (fun j _ => hm j)
  have hJ : 0 < J := Finset.prod_pos (fun j _ => hm j)
  have hsplit : I = m i * J :=
    pt_prod_split Finset.univ m i (Finset.mem_univ i)
  rcases Shao.OQ6.finite_observation_product_tilt n mu phi hExp with
    ⟨hFull, hFullNorm, hFullPos, hFullTilt⟩
  have hpsiExp (j : Fin n) :
      Integrable (fun o : Ω => Real.exp (psi j o)) (mu j) := by
    by_cases hji : j = i
    · simpa [psi, hji] using
        (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) (mu j))
    · simpa [psi, hji] using hExp j
  have hpsiSum (xi : Fin n → Ω) :
      (∑ j : Fin n, psi j (xi j)) = Sminus xi := by
    have herase :
        (∑ j ∈ Finset.univ.erase i, psi j (xi j)) =
          ∑ j : Fin n, psi j (xi j) := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
      simp [psi]
    calc
      _ = ∑ j ∈ Finset.univ.erase i, psi j (xi j) := herase.symm
      _ = Sminus xi := by
        apply Finset.sum_congr rfl
        intro j hj
        exact if_neg (Finset.mem_erase.mp hj).1
  have hpsiMean (j : Fin n) :
      (∫ o : Ω, Real.exp (psi j o) ∂(mu j)) =
        if j = i then 1 else m j := by
    by_cases hji : j = i
    · simp [psi, hji]
    · simp [psi, hji, m]
  have hpsiNorm :
      (∏ j : Fin n, ∫ o : Ω, Real.exp (psi j o) ∂(mu j)) = J := by
    calc
      _ = ∏ j : Fin n, if j = i then 1 else m j := by
        apply Finset.prod_congr rfl
        intro j hj
        exact hpsiMean j
      _ = (if i = i then (1 : ℝ) else m i) *
          ∏ j ∈ Finset.univ.erase i, if j = i then 1 else m j :=
        pt_prod_split Finset.univ (fun j => if j = i then 1 else m j)
          i (Finset.mem_univ i)
      _ = J := by
        simp only [ite_true, one_mul]
        apply Finset.prod_congr rfl
        intro j hj
        exact if_neg (Finset.mem_erase.mp hj).1
  have hpsiTilt (j : Fin n) :
      (mu j).tilted (psi j) =
        if j = i then mu j else (mu j).tilted (phi j) := by
    by_cases hji : j = i
    · simpa [psi, hji] using (tilted_zero (mu j))
    · simp [psi, hji]
  rcases Shao.OQ6.finite_observation_product_tilt n mu psi hpsiExp with
    ⟨hPartial, hPartialNorm, hPartialPos, hPartialTilt⟩
  have hMinus : Integrable (fun xi => Real.exp (Sminus xi)) P := by
    simpa only [hpsiSum] using hPartial
  have hMinusNorm : (∫ xi, Real.exp (Sminus xi) ∂P) = J := by
    simpa only [hpsiSum, hpsiNorm] using hPartialNorm
  have hTilt : P.tilted Sminus = H := by
    simpa only [hpsiSum, hpsiTilt] using hPartialTilt
  have hHprob : IsProbabilityMeasure H := by
    rw [← hTilt]
    exact isProbabilityMeasure_tilted hMinus
  letI : IsProbabilityMeasure H := hHprob
  have hfactor (xi : Fin n → Ω) :
      R xi = (m i)⁻¹ * (Real.exp (Sminus xi) / J) := by
    dsimp only [R]
    rw [hsplit]
    field_simp [(hm i).ne', hJ.ne'] <;> ring
  have hpoint (xi : Fin n → Ω) :
      R xi = (m i)⁻¹ *
        (∏ j ∈ Finset.univ.erase i, Real.exp (phi j (xi j)) / m j) := by
    rw [Finset.prod_div_distrib, ← Real.exp_sum]
    exact hfactor xi
  have hHdensity :
      H = P.withDensity (fun xi =>
        ENNReal.ofReal (Real.exp (Sminus xi) / J)) := by
    rw [← hTilt, Measure.tilted, hMinusNorm]
  have hRdensity :
      (fun xi => ENNReal.ofReal (R xi)) =
        ENNReal.ofReal ((m i)⁻¹) •
          (fun xi => ENNReal.ofReal (Real.exp (Sminus xi) / J)) := by
    funext xi
    rw [Pi.smul_apply, smul_eq_mul, hfactor,
      ENNReal.ofReal_mul (inv_nonneg.mpr (hm i).le)]
  have hQ : Q = ENNReal.ofReal ((m i)⁻¹) • H := by
    change P.withDensity (fun xi => ENNReal.ofReal (R xi)) =
      ENNReal.ofReal ((m i)⁻¹) • H
    rw [hHdensity, hRdensity,
      withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  have hQmass : Q Set.univ = ENNReal.ofReal ((m i)⁻¹) := by
    rw [hQ, Measure.smul_apply, measure_univ]
    simp
  have hQfinite : IsFiniteMeasure Q :=
    ⟨by rw [hQmass]; exact ENNReal.ofReal_lt_top⟩
  have hR : Integrable R P := hMinus.div_const I
  have hRnorm : (∫ xi, R xi ∂P) = (m i)⁻¹ := by
    change (∫ xi, Real.exp (Sminus xi) / I ∂P) = (m i)⁻¹
    simp_rw [div_eq_mul_inv]
    rw [integral_mul_const, hMinusNorm, hsplit]
    field_simp [(hm i).ne', hJ.ne'] <;> ring
  refine ⟨hm, hI, hFull, hFullNorm, hMinus, hMinusNorm, hsplit,
    hpoint, hTilt, hHprob, hQ, hQfinite, hQmass, hR, hRnorm, ?_⟩
  intro f hf
  -- Absolute L1 is obtained first, including the generic AE-measurable case.
  have hAbsTilt : Integrable (fun xi => |f xi|) (P.tilted Sminus) := by
    rw [hTilt]
    exact hf.abs
  have hAbsWeighted :
      Integrable (fun xi => Real.exp (Sminus xi) * |f xi|) P := by
    simpa only [smul_eq_mul] using
      (integrable_tilted_iff hMinus (fun xi => |f xi|)).1 hAbsTilt
  have hAbsR : Integrable (fun xi => R xi * |f xi|) P := by
    simpa only [R, div_mul_eq_mul_div] using hAbsWeighted.div_const I
  have hAbsEq :
      (∫ xi, R xi * |f xi| ∂P) = (m i)⁻¹ * (∫ xi, |f xi| ∂H) := by
    rw [← hTilt, integral_tilted, hMinusNorm]
    simp only [smul_eq_mul]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun xi => by
      change R xi * |f xi| =
        (m i)⁻¹ * (Real.exp (Sminus xi) / J * |f xi|)
      rw [hfactor]
      ring
  -- Only after the absolute integral is finite do we transport the signed test.
  have hfTilt : Integrable f (P.tilted Sminus) := by
    rw [hTilt]
    exact hf
  have hfWeighted : Integrable (fun xi => Real.exp (Sminus xi) * f xi) P := by
    simpa only [smul_eq_mul] using (integrable_tilted_iff hMinus f).1 hfTilt
  have hfR : Integrable (fun xi => R xi * f xi) P := by
    simpa only [R, div_mul_eq_mul_div] using hfWeighted.div_const I
  have hfQ : Integrable f Q := by
    rw [hQ]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  have hSigned :
      (∫ xi, R xi * f xi ∂P) = (m i)⁻¹ * (∫ xi, f xi ∂H) := by
    rw [← hTilt, integral_tilted, hMinusNorm]
    simp only [smul_eq_mul]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun xi => by
      change R xi * f xi =
        (m i)⁻¹ * (Real.exp (Sminus xi) / J * f xi)
      rw [hfactor]
      ring
  have hSignedQ :
      (∫ xi, f xi ∂Q) = (m i)⁻¹ * (∫ xi, f xi ∂H) := by
    rw [hQ, integral_smul_measure,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (hm i).le), smul_eq_mul]
  exact ⟨hAbsR, hAbsEq, hfR, hfQ, hSigned, hSignedQ⟩


theorem actual_quadratic_partial_source_transport
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun z : Ω × Ω => h z.1 z.2))
    (hh2 : MemLp (fun z : Ω × Ω => h z.1 z.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ z : Ω × Ω, h z.1 z.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (n : ℕ) (hn : 3 ≤ n) (i : Fin n)
    (x : ℝ) (hx : 0 ≤ x)
    (hwindow : x ≤ Real.sqrt (n : ℝ) /
      (2 * Real.exp (1 / 2 : ℝ))) :
    let C : ℝ := Real.exp (1 / 2 : ℝ)
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let a : ℝ := x / Real.sqrt (n : ℝ)
    let φ : Ω → ℝ := fun o => a * g o - (a * g o) ^ 2 / 2
    let w : Ω → ℝ := fun o => Real.exp (φ o)
    let m : ℝ := ∫ o, w o ∂μ
    let L : Ω → ℝ := fun o => w o / m
    let ρ : Measure Ω :=
      μ.withDensity (fun o => ENNReal.ofReal (L o))
    let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
    let Sminus : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ j ∈ Finset.univ.erase i, φ (ξ j)
    let I : ℝ := m ^ n
    let R : (Fin n → Ω) → ℝ := fun ξ => Real.exp (Sminus ξ) / I
    let H : Measure (Fin n → Ω) := Measure.pi
      (fun j : Fin n => if j = i then μ else ρ)
    let Q : Measure (Fin n → Ω) :=
      P₀.withDensity (fun ξ => ENNReal.ofReal (R ξ))
    let cap : (Fin n → Ω) → ℝ := fun ξ => min |a * g (ξ i)| 1
    let e : (Fin n → Ω) → Fin n → Fin n → ℝ :=
      fun ξ j k => r (ξ j) (ξ k)
    let F : (Fin n → Ω) → ℝ := fun ξ =>
      Shao.OQ5.P35.unorderedPairSum (e ξ)
    let Fdel : (Fin n → Ω) → ℝ := fun ξ =>
      Shao.OQ5.P35.unorderedPairSum
        (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i)
    let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ j =>
      Shao.OQ6.ResidualDeletion.rowSum (e ξ) j
    let ψdel : (Fin n → Ω) → Fin n → ℝ := fun ξ j =>
      Shao.OQ6.ResidualDeletion.rowSum
        (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i) j
    let Λsq : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ j : Fin n, ψ ξ j ^ 2
    let Λdelsq : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ j : Fin n, ψdel ξ j ^ 2
    let D₁ : (Fin n → Ω) → ℝ := fun ξ =>
      F ξ / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
    let D₁del : (Fin n → Ω) → ℝ := fun ξ =>
      Fdel ξ / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
    let cross : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ j ∈ Finset.univ.erase i,
        2 * r (ξ i) (ξ j) * (ψ ξ j - r (ξ i) (ξ j))
    Integrable w μ ∧ (1 / 2 : ℝ) ≤ m ∧ m ≤ (3 / 2 : ℝ) ∧
      0 < m ∧ 0 < I ∧ 0 < m⁻¹ ∧ m⁻¹ ≤ 2 ∧
      μ.tilted φ = ρ ∧ IsProbabilityMeasure ρ ∧
      (∫ ξ, Real.exp (∑ j : Fin n, φ (ξ j)) ∂P₀) = I ∧
      Integrable (fun ξ => Real.exp (Sminus ξ)) P₀ ∧
      (∫ ξ, Real.exp (Sminus ξ) ∂P₀) = m ^ (n - 1) ∧
      (∀ ξ, R ξ = m⁻¹ *
        (∏ j ∈ Finset.univ.erase i, L (ξ j))) ∧
      P₀.tilted Sminus = H ∧ IsProbabilityMeasure H ∧
      H = P₀.withDensity
        (fun ξ => ENNReal.ofReal
          (∏ j ∈ Finset.univ.erase i, L (ξ j))) ∧
      Q = ENNReal.ofReal (m⁻¹) • H ∧
      IsFiniteMeasure Q ∧ Q Set.univ = ENNReal.ofReal (m⁻¹) ∧
      (∀ ξ, 0 < R ξ ∧ R ξ ≤ 2 * (2 * C) ^ (n - 1)) ∧
      (∀ j k : Fin n, j ≠ k →
        MemLp (fun ξ => r (ξ j) (ξ k)) 2 H) ∧
      Integrable (fun ξ => D₁ ξ - D₁del ξ) H ∧
      Integrable (fun ξ => Λsq ξ - Λdelsq ξ) H ∧
      Integrable cross H ∧
      (∀ f : (Fin n → Ω) → ℝ, Integrable f H →
        Integrable (fun ξ => R ξ * cap ξ * |f ξ|) P₀ ∧
        (∫ ξ, R ξ * cap ξ * |f ξ| ∂P₀) =
          m⁻¹ * (∫ ξ, cap ξ * |f ξ| ∂H) ∧
        (∫ ξ, R ξ * cap ξ * |f ξ| ∂P₀) ≤
          2 * (∫ ξ, |f ξ| ∂H) ∧
        Integrable (fun ξ => R ξ * cap ξ * f ξ) P₀ ∧
        Integrable (fun ξ => cap ξ * f ξ) Q ∧
        (∫ ξ, R ξ * cap ξ * f ξ ∂P₀) =
          m⁻¹ * (∫ ξ, cap ξ * f ξ ∂H) ∧
        (∫ ξ, cap ξ * f ξ ∂Q) =
          m⁻¹ * (∫ ξ, cap ξ * f ξ ∂H)) := by
  classical
  let C : ℝ := Real.exp (1 / 2 : ℝ)
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
  let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
  let a : ℝ := x / Real.sqrt (n : ℝ)
  let φ : Ω → ℝ := fun o => a * g o - (a * g o) ^ 2 / 2
  let w : Ω → ℝ := fun o => Real.exp (φ o)
  let m : ℝ := ∫ o, w o ∂μ
  let L : Ω → ℝ := fun o => w o / m
  let ρ : Measure Ω := μ.withDensity (fun o => ENNReal.ofReal (L o))
  let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  let Sminus : (Fin n → Ω) → ℝ := fun ξ =>
    ∑ j ∈ Finset.univ.erase i, φ (ξ j)
  let I : ℝ := m ^ n
  let R : (Fin n → Ω) → ℝ := fun ξ => Real.exp (Sminus ξ) / I
  let H : Measure (Fin n → Ω) := Measure.pi
    (fun j : Fin n => if j = i then μ else ρ)
  let Q : Measure (Fin n → Ω) :=
    P₀.withDensity (fun ξ => ENNReal.ofReal (R ξ))
  let cap : (Fin n → Ω) → ℝ := fun ξ => min |a * g (ξ i)| 1
  let e : (Fin n → Ω) → Fin n → Fin n → ℝ :=
    fun ξ j k => r (ξ j) (ξ k)
  let F : (Fin n → Ω) → ℝ := fun ξ =>
    Shao.OQ5.P35.unorderedPairSum (e ξ)
  let Fdel : (Fin n → Ω) → ℝ := fun ξ =>
    Shao.OQ5.P35.unorderedPairSum
      (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i)
  let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ j =>
    Shao.OQ6.ResidualDeletion.rowSum (e ξ) j
  let ψdel : (Fin n → Ω) → Fin n → ℝ := fun ξ j =>
    Shao.OQ6.ResidualDeletion.rowSum
      (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i) j
  let Λsq : (Fin n → Ω) → ℝ := fun ξ => ∑ j : Fin n, ψ ξ j ^ 2
  let Λdelsq : (Fin n → Ω) → ℝ := fun ξ => ∑ j : Fin n, ψdel ξ j ^ 2
  let D₁ : (Fin n → Ω) → ℝ := fun ξ =>
    F ξ / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
  let D₁del : (Fin n → Ω) → ℝ := fun ξ =>
    Fdel ξ / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
  let cross : (Fin n → Ω) → ℝ := fun ξ =>
    ∑ j ∈ Finset.univ.erase i,
      2 * r (ξ i) (ξ j) * (ψ ξ j - r (ξ i) (ξ j))
  -- This public interface is frozen140; no private140 name is called.
  have source := ActualQuadraticTiltMoments.actual_quadratic_source_moments
    μ h hh hh2 hhsymm hcenter hprojectionsecond n hn x hx hwindow
  rcases source with
    ⟨hg, hg2, hgmean, hgsecond, hr, hr2, hrsymm, hrcan,
      hv, hs1, hvs, hw, hmlo, hmhi, hL, hL1, hLb, hLmass,
      hδint, hδbd, htilt, hρprob, hFullExp, hFullNorm, hFullPos,
      hFullPoint, hFullDensity, hFullProduct, hFullProb,
      hFullF2, hFullFsq, hFullRows, hFullΛ,
      hFullFid, hFullΛid, hFullFbin, hFullΛbin,
      hFullFpoly, hFullΛpoly, hFullFfinal, hFullΛfinal⟩
  change Measurable g at hg
  change Measurable (fun z : Ω × Ω => r z.1 z.2) at hr
  change MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (μ.prod μ) at hr2
  change Integrable w μ at hw
  change (1 / 2 : ℝ) ≤ m at hmlo
  change m ≤ (3 / 2 : ℝ) at hmhi
  change Measurable L at hL
  change (∀ o, 0 < L o ∧ L o ≤ 2 * C) at hLb
  change μ.tilted φ = ρ at htilt
  change IsProbabilityMeasure ρ at hρprob
  letI : IsProbabilityMeasure ρ := hρprob
  have hmpos : 0 < m := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hmlo
  have hmInvPos : 0 < m⁻¹ := inv_pos.mpr hmpos
  have hmInvLe : m⁻¹ ≤ 2 := by
    have hscaled : 0 ≤ (m - (1 / 2 : ℝ)) * m⁻¹ :=
      mul_nonneg (sub_nonneg.mpr hmlo) hmInvPos.le
    have hcancel : m⁻¹ * m = 1 := inv_mul_cancel₀ hmpos.ne'
    nlinarith only [hscaled, hcancel]
  have part := finite_observation_partial_tilt_transport n
    (fun _ : Fin n => μ) (fun _ : Fin n => φ) (fun _ => hw) i
  dsimp only at part
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.card_erase_of_mem (Finset.mem_univ i), htilt] at part
  rcases part with
    ⟨hFamilyPos, hIpos, hExpAll, hNormAll, hExpMinus, hNormMinus, hSplit,
      hPoint, hMinusTilt, hHprob, hQscale, hQfinite, hQmass,
      hRintegrable, hRnorm, hTransport⟩
  change 0 < I at hIpos
  change (∫ ξ, Real.exp (∑ j : Fin n, φ (ξ j)) ∂P₀) = I at hNormAll
  change Integrable (fun ξ => Real.exp (Sminus ξ)) P₀ at hExpMinus
  change (∫ ξ, Real.exp (Sminus ξ) ∂P₀) = m ^ (n - 1) at hNormMinus
  change (∀ ξ, R ξ = m⁻¹ *
    (∏ j ∈ Finset.univ.erase i, L (ξ j))) at hPoint
  change P₀.tilted Sminus = H at hMinusTilt
  change IsProbabilityMeasure H at hHprob
  change Q = ENNReal.ofReal (m⁻¹) • H at hQscale
  change IsFiniteMeasure Q at hQfinite
  change Q Set.univ = ENNReal.ofReal (m⁻¹) at hQmass
  letI : IsProbabilityMeasure H := hHprob
  let d : (Fin n → Ω) → ℝ := fun ξ =>
    ∏ j ∈ Finset.univ.erase i, L (ξ j)
  let B : ℝ := (2 * C) ^ (n - 1)
  have hdMeas : Measurable d :=
    pt_measurable_prod (Finset.univ.erase i)
      (fun j (ξ : Fin n → Ω) => L (ξ j))
      (fun j hj => hL.comp (measurable_pi_apply j))
  have hdPos (ξ : Fin n → Ω) : 0 < d ξ :=
    Finset.prod_pos (fun j hj => (hLb (ξ j)).1)
  have hdNonneg (ξ : Fin n → Ω) : 0 ≤ d ξ := (hdPos ξ).le
  have hdBound (ξ : Fin n → Ω) : d ξ ≤ B := by
    calc
      _ ≤ ∏ j ∈ Finset.univ.erase i, (2 * C) :=
        Finset.prod_le_prod₀ (fun j hj => (hLb (ξ j)).1.le)
          (fun j hj => (hLb (ξ j)).2)
      _ = B := by
        dsimp only [B]
        simp only [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Fintype.card_fin]
  have hdNormPoint (ξ : Fin n → Ω) :
      Real.exp (Sminus ξ) / m ^ (n - 1) = d ξ := by
    dsimp only [d, L, w, Sminus]
    rw [Finset.prod_div_distrib, ← Real.exp_sum]
    simp only [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin]
  have hHdensity :
      H = P₀.withDensity (fun ξ => ENNReal.ofReal (d ξ)) := by
    rw [← hMinusTilt, Measure.tilted, hNormMinus]
    simp_rw [hdNormPoint]
  have hBnonneg : 0 ≤ B := by
    dsimp only [B, C]
    positivity
  have hRbound (ξ : Fin n → Ω) :
      0 < R ξ ∧ R ξ ≤ 2 * (2 * C) ^ (n - 1) := by
    have hRfactor : R ξ = m⁻¹ * d ξ := hPoint ξ
    rw [hRfactor]
    refine ⟨mul_pos hmInvPos (hdPos ξ), ?_⟩
    exact le_trans
      (mul_le_mul_of_nonneg_left (hdBound ξ) hmInvPos.le)
      (mul_le_mul_of_nonneg_right hmInvLe hBnonneg)
  -- Off-diagonal L2 comes from the untilted pair law and a bounded density.
  -- This bound is qualitative at fixed n, not a uniform deletion-rate claim.
  have hEdges (j k : Fin n) (hjk : j ≠ k) :
      MemLp (fun ξ : Fin n → Ω => r (ξ j) (ξ k)) 2 H := by
    have hBase : MemLp (fun ξ : Fin n → Ω => r (ξ j) (ξ k)) 2 P₀ :=
      hr2.comp_measurePreserving (pt_pair_selection μ n j k hjk)
    have hMeas : Measurable (fun ξ : Fin n → Ω => r (ξ j) (ξ k)) := by
      have hsel : Measurable (fun ξ : Fin n → Ω => (ξ j, ξ k)) :=
        (measurable_pi_apply j).prodMk (measurable_pi_apply k)
      change Measurable ((fun z : Ω × Ω => r z.1 z.2) ∘
        (fun ξ : Fin n → Ω => (ξ j, ξ k)))
      exact hr.comp hsel
    rw [hHdensity]
    exact pt_bounded_density_L2 P₀ d hdMeas B hdNonneg hdBound hMeas hBase
  have hE : ∀ j k : Fin n, j ≠ k →
      MemLp (fun ξ => e ξ j k) 2 H := hEdges
  let edel : (Fin n → Ω) → Fin n → Fin n → ℝ := fun ξ =>
    Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i
  have hEdel (j k : Fin n) (hjk : j ≠ k) :
      MemLp (fun ξ => edel ξ j k) 2 H := by
    by_cases hzero : j = i ∨ k = i
    · simp only [edel, Shao.OQ6.ResidualDeletion.eraseIncident, if_pos hzero]
      simp
    · simpa only [edel, Shao.OQ6.ResidualDeletion.eraseIncident, if_neg hzero]
        using hE j k hjk
  have hF2H : MemLp F 2 H := pt_pair_sum_L2 H n e hE
  have hFd2H : MemLp Fdel 2 H := pt_pair_sum_L2 H n edel hEdel
  have hRowsH (j : Fin n) : MemLp (fun ξ => ψ ξ j) 2 H :=
    pt_row_L2 H n e hE j
  have hRowsDelH (j : Fin n) : MemLp (fun ξ => ψdel ξ j) 2 H :=
    pt_row_L2 H n edel hEdel j
  have hD1H : Integrable D₁ H :=
    (hF2H.integrable (by norm_num)).div_const
      (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
  have hD1delH : Integrable D₁del H :=
    (hFd2H.integrable (by norm_num)).div_const
      (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
  have hDdifference : Integrable (fun ξ => D₁ ξ - D₁del ξ) H :=
    hD1H.sub hD1delH
  have hΛH : Integrable Λsq H :=
    integrable_finsetSum Finset.univ (fun j hj => (hRowsH j).integrable_sq)
  have hΛdelH : Integrable Λdelsq H :=
    integrable_finsetSum Finset.univ (fun j hj => (hRowsDelH j).integrable_sq)
  have hΛdifference : Integrable (fun ξ => Λsq ξ - Λdelsq ξ) H :=
    hΛH.sub hΛdelH
  have hCrossH : Integrable cross H := by
    apply integrable_finsetSum
    intro j hj
    have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    have hprod : Integrable
        (fun ξ => r (ξ i) (ξ j) * (ψ ξ j - r (ξ i) (ξ j))) H :=
      (hEdges i j hij).integrable_mul ((hRowsH j).sub (hEdges i j hij))
    simpa only [mul_assoc] using hprod.const_mul (2 : ℝ)
  have hcapMeas : Measurable cap := by
    have hEval : Measurable (fun ξ : Fin n → Ω => g (ξ i)) := by
      change Measurable (g ∘ (fun ξ : Fin n → Ω => ξ i))
      exact hg.comp (measurable_pi_apply i)
    have hReal : Continuous (fun z : ℝ => min |a * z| (1 : ℝ)) := by
      fun_prop
    change Measurable ((fun z : ℝ => min |a * z| (1 : ℝ)) ∘
      (fun ξ : Fin n → Ω => g (ξ i)))
    exact hReal.measurable.comp hEval
  have hcapNonneg (ξ : Fin n → Ω) : 0 ≤ cap ξ :=
    le_min (abs_nonneg _) (by norm_num)
  have hcapLe (ξ : Fin n → Ω) : cap ξ ≤ 1 := min_le_right _ _
  have hcapNorm : ∀ᵐ ξ ∂H, ‖cap ξ‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall fun ξ => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hcapNonneg ξ)] using hcapLe ξ
  refine ⟨hw, hmlo, hmhi, hmpos, hIpos, hmInvPos, hmInvLe,
    htilt, hρprob, hNormAll, hExpMinus, hNormMinus, hPoint, hMinusTilt,
    hHprob, hHdensity, hQscale, hQfinite, hQmass, hRbound, hEdges,
    hDdifference, hΛdifference, hCrossH, ?_⟩
  intro f hf
  have hcf : Integrable (fun ξ => cap ξ * f ξ) H := by
    have hfc : Integrable (fun ξ => f ξ * cap ξ) H :=
      hf.mul_bdd hcapMeas.aestronglyMeasurable (c := (1 : ℝ)) hcapNorm
    exact hfc.congr (Filter.Eventually.of_forall fun ξ => mul_comm (f ξ) (cap ξ))
  rcases hTransport (fun ξ => cap ξ * f ξ) hcf with
    ⟨hAbs, hAbsEq, hSigned, hSignedQ, hSignedEq, hSignedQEq⟩
  have habs (ξ : Fin n → Ω) :
      |cap ξ * f ξ| = cap ξ * |f ξ| := by
    rw [abs_mul, abs_of_nonneg (hcapNonneg ξ)]
  have hAbs' : Integrable (fun ξ => R ξ * cap ξ * |f ξ|) P₀ := by
    simpa only [habs, mul_assoc] using hAbs
  have hAbsEq' :
      (∫ ξ, R ξ * cap ξ * |f ξ| ∂P₀) =
        m⁻¹ * (∫ ξ, cap ξ * |f ξ| ∂H) := by
    simpa only [habs, mul_assoc] using hAbsEq
  have hcfAbs : Integrable (fun ξ => cap ξ * |f ξ|) H := by
    simpa only [habs] using hcf.abs
  have hAbsMono :
      (∫ ξ, cap ξ * |f ξ| ∂H) ≤ ∫ ξ, |f ξ| ∂H :=
    integral_mono hcfAbs hf.abs (fun ξ => by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (hcapLe ξ) (abs_nonneg (f ξ)))
  have hAbsBound :
      (∫ ξ, R ξ * cap ξ * |f ξ| ∂P₀) ≤
        2 * (∫ ξ, |f ξ| ∂H) := by
    rw [hAbsEq']
    exact le_trans (mul_le_mul_of_nonneg_left hAbsMono hmInvPos.le)
      (mul_le_mul_of_nonneg_right hmInvLe (integral_nonneg fun ξ => abs_nonneg (f ξ)))
  have hSigned' : Integrable (fun ξ => R ξ * cap ξ * f ξ) P₀ := by
    simpa only [mul_assoc] using hSigned
  have hSignedEq' :
      (∫ ξ, R ξ * cap ξ * f ξ ∂P₀) =
        m⁻¹ * (∫ ξ, cap ξ * f ξ ∂H) := by
    simpa only [mul_assoc] using hSignedEq
  exact ⟨hAbs', hAbsEq', hAbsBound, hSigned', hSignedQ,
    hSignedEq', hSignedQEq⟩

end

end Shao.OQ6.PartialObservationTilt
